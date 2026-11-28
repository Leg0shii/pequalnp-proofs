import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37417.Model
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


end PEqualNP.Outside.L_meta_37417.Model

namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
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

def SBf (j : Nat) : Nat := [4, 4, 4, 8, 5, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 33]

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

end PEqualNP.Outside.L_meta_37417

namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
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
  | 3 => 0xffffdfe0ffffff803fffffffff00ffffffe1ff
  | 4 => 0x6bff07c1ffffc00ffc01ffff00ff007e38
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffff8022108825924992c5245b4b4b4b6caedb
  | 2 => 0xffff804421104aa492a54a48ad959595b5576d
  | 3 => 0x209e422093762349939136c0e6e6da61b6
  | 4 => 0x1508f43b1c473b8e231dc7e6c0f81c7a38
  | 5 => 0xe1087bde0783c0fc3e1f8f8f8c0e07dc0
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000c0c0c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
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
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf80fe01fe01fffc07c0fe07e07e0fff016327c
  | 3 => 0xfffffffe03ffffff0007fffff03fff83f8f
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8202142224204880851648a48a1451542d4b5
  | 2 => 0x556554ce51d4a91abe0aac56c568eba0d6325c
  | 3 => 0x468992949491b23256a81065965a22ca982b0a
  | 4 => 0x64cd1b19191923a3673cd941079cb0831d43e0
  | 5 => 0x870e1c1e1e1e3c3c7bcf1e79e410c30c1fbc00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xf80fe01fe01fffc07c0fe07e07e0fff016327c
  | 3 => 0xfffffffe03ffffff0007fffff03fff83f8f
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8202142224204880851648a48a1451542d4b5
  | 1 => 0x556554ce51d4a91abe0aac56c568eba0d6325c
  | 3 => 0x468992949491b23256a81065965a22ca982b0a
  | 4 => 0x64cd1b19191923a3673cd941079cb0831d43e0
  | 5 => 0x870e1c1e1e1e3c3c7bcf1e79e410c30c1fbc00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00aaaaaa00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x200000000d003a84129000c228000080000006133094c8b2e28e2322003001e7c4a41c013160a00a0d021cd922a80f27440000001802170c4202006ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x281bd42502fea2a07dd4540bba8a817c51503e8a2a05d14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206f90c40de218817e52102faa4206f90840de210817e51102faa2206f90440de208817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc37c87986f10f30bf296617d52cc2fca3985f54730bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c61df438c37c87186f10e30ee21c619c438c2fca5185f54a30ef19461dc328c2fca3185f54630ef18c61dc318c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261be434c37886985fd4930f7a92616f524c2f8a4987b14930b6292617f514c3eea2985dd4530be28a61f4514c2e8a2987ecc130ef182617f540c2fca8185f55030be2a0617e530c3be86186f90c30de21861dc430c33886185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20df21e41bc43c82fca3905f54720fd98641f830c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837c87106f10e20bea9441ef42883d885107bcca20f6194417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20df21a41bc43482fea2907dd4520bba8a417c51483e8a2905d14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c530837c86106f10c20bf29041ef42083d884107bcc820f6190417e51082faa2107b88420f6108417e50083f660107e0c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10df21e21bc43c42fea5885f94b10bea96217c52c43f661887e0c310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10df21c21bc43842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f731843e863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10df21a21bc43442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53042faa6085f14c10df21821bc43042fea4085f94810bea90217c52042fca2087dd0410fa20821f731043e862087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd548caf8a9195f54e32df21c65bc438cafca51977cca32f7994657e518cafaa3195f94232bea84657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265be434cb7886997bcc932ef192657f514cbeea2995dd4532be28a65f4514cae8a2995fd4132fda82657b504caf8a0997e14132bc282657f540cafca8195f55032be2a0657e530cb7c86196f10c32bf29065df320cbdc6419774c832f6990657e510cafaa2195f94032bea80657e53d06faa7a0ef90f41de21e837e52d07dca5a0db94b41bea9683ed52d06daa5a0ef90b41de216837e50d06faa1a0df55241bf29c837d539077c8720ef10e41bf294837d529077e8520ef50a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0ef90d41de21a837f52506f8a4a0ef90941de21283f7415077c82a0dfd4141be282837e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998df55331be2a663be43cc7788798df94b31bea96637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31df21c63bc438c6fca518df54a31bf28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a263be434c7788698dfd4931f7a92636f524c6f8a498fb14931b629263f7314c7bc6298dfd4131fda82637b504c6f8a098fe14131bc282637f540c6fca818df55031be2a0637e530c77c8618ef10c31bf290637d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43be43c87788790fd90721faa0e43f731c87e86390df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710df54e21be29c43be43887788710df54a21f721443ed42887de6510fb0ca21bf28c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53486fca690df54d21be29a43be43487788690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610ef90c21de218437e52087dc8410fb50821f799043ec32086fca210fd90421faa0843f731087e86210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a05f54f40df21e81bc43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a077d4d40afa9a817c53503b8a6a05714d40df21a81bc43502fea4a07bd4940b7a92817c52503d8a4a05b14940dfa1
  | 2 => 0xc6b52da0146e848a9aba59405c241064ea7547a16109a940a191d5543b00d80049041c6c8f24ba5fccfa2b0d4190840255960dc219a056e3cd662d6586255432152e41ed259484da5c0228fa07831d57284196000890340ca07400081000060348850007b104a954140e45aa3100034cab9560003800013b40c000002222da240ee8ad28264d5fa0b0b209108a0c1e0010478354485745c0b20ce860bb0c45680e8eb96c1b68641099818a6bd319f32fc09d0f2102d6b1cd60e51721c8e88c61cc994e01113c45f5098071b85188b2603048f40006c0506a866a970005f0002d2028188cd08000038d322880000010b14c0000000007f00000145ada00057cca0b402ca44ac9245468747704014227820a9350e184c808d11c62c618000120b000000001a80000004000000381c100041a0660f80c008000e82200010018000b00e0300a00808040000d06c06802000000002e00834038082580601816020000f822038360100600810008100600210800038000081801800168100000410800100100d044010080001c01010000080400e018000a8040003400838010000780601802030160001e0001602030000000003c0100a19000000100782c00000000220180201002020240001204016000000382c000000080e07000030000100204014058000582200000018000103c0100c0000200800000060e830010160200400800050ae03836050081580009002010000703e08004050460080c0b806000280100e18006010060180c0085601804000060005c00816018160b08000004008240380200000040040404606854000017e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea84873e5390f7ea521ef94a43dea9487bc5290f7ea321ef94643dea8c87bc5190f7ea121ef94243dea8487bc5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010f7ca621cf94c43cf29887bf5210f7ca421ef54843de29087bf5110f7ca221ef54443de28887bf5010f7ca021ef54043de280877e53d0afaa7a16f90f42de21e857e51d0beca3a15d94742bea8e85f551d0aeaa3a15f94342bea86857d5490afca7215f54e42df21c85bc4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310b7c86216f10c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665be43ccb7887995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653
  | 3 => 0x4d4a880041e88c661540001f4b30f10009b0a90ac4b894859a684e25886f122312000491450349347d9b2000b04002c229a66d5d8834eea3418036000b40238930a0484e29004280ec3e20e2a0000a71174a27400009f46c37c001581d09308482e46a0155a854000001018ea000501299db30c038daa050008d02200059a00085800580001151a90001280aaac2de7056704b1ee4f80021b45a2640023e3c87800017754e000b50f94087e16f11e2789c8548ce260610559c736c388b98a83e40000005e4f429c152575404a0e10fe5148b02e9133940ac0011c1a417c00001564000438000007eccb1440000000011b53e0015890a5b6950288e740400000127194000d318c00028c4c07324a148f2a5508c000c0a7c0003f01f0552c6af93982f4823f4001ea5667fc000003c61086010e0d6590da11a440524950d148e56c0780057aa30001da5b27f955a982cab14058d71125282e000470000b4a4e2b8000189ef0001812c2c80000f50fa702ce4bcfe00000000000000000000000bb44a0894b1be3c20015c0b00003d4d993d5ae00147a760646e9312af1361d09c19d56090d4ea7b19e2f43a9b10a62a8681013b0001378003060016225f0dca68000000ee9f800000492a389b9de21e4d87c2690460711f85749458027a44476b746080d000000000000008b83c9313bea083d00035c739350d80004ad1d1974660013c12900093cc01d43704fcaf279092af0379fa2f68995c9f14426e40480832474cc51e93ec0a4451a25b89ac640f65a81388f9e75a64cc4203f1a8250bc12036e7355b21a3426551790c0000000fa460cc000d38e952463c8114222072057acf592268001e842e7d0f588b0009083c000386000bc923550000e5a854382b88680016c498ec8000006fcba1851104b8c39bd25a89c4b8d537899d4099c1da8a0d58b73f20784300c3225e852103144294092d153c3fc09a08184749548c92080014027d000798368195449d0faa9c5360009c97154a8a4000003ee18d180bc000b54cf0001c2000cc9c631a6ec080001b4000001192aa0e04618e3481d903aa63ac000000bf0008c88a80034a915568001040000023c0002f82b09128e000002c60000002c02c0006c14a000000900002893920087200012c1a1069181384c8588eb5427b4f8011296000198004cc000fe9c43dc0288292c000a90e780013a730c4261520000d182d2685b8102390000006e9684ac9788a00029e298130d65065693fa991de5d42d04c0e04e8ee05b0069b80007e4b46a12cad81401c45d20000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x553482746154d209ed81534825e6514d20c7d50534831c5414d20c7d90534831c6414d208f996434823c6590d20c7d4e434831c5390d208f994434823c6510d20c7d4c434831c5310d20cdd53514833454d4520d5d4f514835453d4520cd90f514833443d4520cdd5051483345414520d5d4c51483545314520cd90c51483344314520d614f204832c5488120d314e204836451881208f596540823e63950208f18d540832c62550208f990540823e64d4c208f593530823f6454c208f19153082776154c209d185530823e6414c208f59053082766114c209d584530823f6590c208f596430823f6510c208f594430832d54d0820b9987420826d65108209b59432082ae6488420cb552210832d5408420d95442108279650c020e610c30083c8320c0209bd9520082ac6448020b318d20082e461480209ed9520082d863480209798f54c425d63d53109b98b54c426d62d53108f99353c423d64d4f109b98b53c426d62d4f108fd9153c423c6454f10c794c43c431d5310f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b10e610c30c426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423f6454e108f191538423f6454a108f191528423e6414a108f59052842e662d0610ad993218436752086108f98f544423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109dd85544423e65151108f98c544423e64d4d108f593534431f54d4d10c7153534431e64d4d10c7593534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534427b6054d1097994534431f5414d10c7150534431f6414d10c7190534423e6590d108f196434431f5390d10c714e434423e6510d108f194434431f5310d10c714c434432f54d4910cb153524434f53d4910d314f524432e43d4910cb10f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910cb90c524432c4314910d614f10443345484110d514e104436452841108f596540423e63950108f18d540433461550108f990540423e64d4c108f593530423f6454c108f191530426f6254c109b189530423e6414c108f590530426e6214c109b588530423f6590c108f596430423f6510c108f594430423e64d48108f593520423e64148108f590520425e63148109758c520433554d0410b998b410427565104109d59431042b664c8410cd55321042756508410cd550210436552084109e5943004398430c010f40c4300427965840109dd9510042b46444010b518d10042e462440109ed9510042d86344010
  | 1 => 0x866f65484219dd9521086e76548421d9d9521086e76448421b959121086e66348421b918d21087a64348421e910d21086e460484218fd91500863c645402197d8d500865c6354021c794c43d031d5310f40ad58742d02ad62d0740c794e43902776154a409d185529026f62546409b189519031f6414d40c714e435031f5310d40d3d4f525034c53d4940cb90f525032c43d4940d3d4c525034c5314940cb90c525032c43149408f997425031c53d0940cb14b42502b561d0940c714d425032c5250940d5d4f515035453d4540d9d4b515036452d4540cd90f515033443d4540d5d4c51503545314540d9d4851503645214540cd90c51503344314540cdd08515033542145408f997415031c53d0540ab58b415032c52d0540cd147415031c5350540cb14941503345150540c714e405032c5290140cd146405031e5310c408f596421023d65904408fd95401029c6350040ab18940102b461500409ed95401026e62d53309b58b54cc27661d53309d58754cc23e6494b308f59252cc23e64947308f59251cc31f6355230c7550438c29d6510e30c7594438c29e648ca30a7992318c23e64951309b98a544c26d62951309d986544c275619513097d8d544c26f62551309b189544c27761551309d185544c23e65151308f98c544c23c63151308f996434c23e6510d30cbd53524c32c54d4930cb90f524c32c43d4930cbd50524c32c5414930cb90c524c32c4314930cdd53514c33454d4530d9d4b514c36452d4530cd90f514c33443d4530cdd50514c3345414530d9d48514c3645214530cd90c514c3344314530da14b304c37051cc130c7152304c34c528c130d5146304c26e62150309b588540c27661150309d584540c29e6390c3097594430c2d96010c30c7994430c31d6510c30e6980430c3996010c308fd91520c23c64548309dd85520c2746154830a7992320c23f64544308f191510c26f62544309b189510c29e648c4308f992500c23d6494030c710e500c398438c03097d95300c29c644c030b3189300c2d4614c0309ed95300c39a434c030ba189300c2f0614c0309798f54c825d63d53209d98754c827561d53208f99353c823d64d4f209d98753c827561d4f208fd9153c823c6454f20c794c43c831d5310f208f99251c823d6494720e610c30c827661152209d584548823e64d4e208f593538827661d4e209d587538823f6454e208f19153882e661d0a208fd91518823c6454620ab992218823e63d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e63151208f993534823d64d4d20c7d53534831c54d4d20c7993534831d64d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8
  | 2 => 0x64943328f992544ca7661951329d586544ca7a60951329e582544ca7761551329d185544ca7b60551329e181544ca3e65151328f996434ca3e6510d32cdd53514cb3454d4532cd90f514cb3443d4532cdd50514cb345414532cd90c514cb344314532d9cc8514cb3b54d4132ce153504cb7351d4132dc147504cb3a43d4132ce10f504cb3b5414132ce150504cb735114132dc144504cb3a4314132ce10c504cb6b3214132d68c8504ca7661d50329d587540ca3e64948328f592520ca5f654c832b6181320ca6f654c832e310d320cae4614c832ba181320ca3e64944328f592510ca3f64540328f191500ca7761540329d185500cb1e5310f41cb90e52d072c4394b41cb90d52d072c4354b41cb54a42d072d5210b41c794e43906b561d0a41ab58b41906e662d0641c714e43506b66190d418f99442506e662d0541c794c43106b56110c41ad587421063f6550841ab58b411063f65504419dd95411065f63540419718d501066f62540419b189501066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c63e6590d318f994434c72f54d4931cb153524c72e43d4931cb10f524c72f5414931cb150524c72e4314931cb10c524c76452cc531ced53504c73854d4131dad4b504c76852d4131ce90f504c73843d4131ced50504c7385414131dad48504c7685214131ce90c504c7384314131dccc4504c75a31141319b98b540c66d62d50318f992520c63d64948318f992510c63d649443197d95310c6d8604c4319dd95310c794434c431b9189310c6f0604c4318fd91500c63c64540319bd89500c66c62540318f98e54c873561953218f18d54c863e64d4f218f59353c867a60d4f219e58353c863f6454f218f19153c863e6414f218f59053c863f6590f218f59643c863f6510f218f59443c873654907218f98e548872d62952218f18d548863e64d4e218f593538867a60d4e219e583538863f6454e218f191538863e6414e218f590538863f6590e218f596438863f6510e218f594438872e5490a21ab593218873554c86219b58a5448675619512197d8d544865c63551219ed81544867860551218f993534863d64d4d218fd91534863c6454d219bd8953486776154d219ed8153486786054d21c7d4c434871c5310d218f990504863d64141219798f540865d63d50218f993530863d64d4c218fd91530863c6454c219ed8153086786054c21c794c430871d5310c218f992520863d64948219b59642086e561908219b594320874d530c821b9584320863e64944218f59251086756590421b958a41087a54290421e99094108675650c421d554c31086e5620c421ab59321086b56488421b958a210
  | 3 => 0x542000000630002440a98f000000000000005580c97d2483d02303b4a007c310284b04b5191380a4000a42782060000021b000000000000000f8710000a0808000380588585a0000281b51480055e6b400000536000000000005043000029462c738000004d00011f00080c002170000000002e1ea848f794d19a7a9588002e402ceb183286754f6874000a180019f556000f0a47000714000ac0005a4e8129396a380022e000b1d1508f00e0000000000036cd507300000099800000000198b035c3e8000321381d40000000000000000000238ce000000000f384500016d030000c27604d0000d8400d79083923b0289b54e40000027d00000000000474001540d50000003f9270000000006b40a3d80000055200000000000000002c32240dcd1a25000000ea2c236e0006ba3132a000cc80054058c000000145d40000007e6292d9732e214d1303614c9982e00022c930002be18c99d119e300034cce8001905640c1a14b20006f1a6146acc512b42c28d00d96c1d0404ec8000009fc0026c001002010000020020100000100200804800000020008000000040080000002c01002000008038020000080000101000000000002000010000000040080600a0000080000200000801004008000000000080200500402c0001000000001002000000018010000000000000801000000000018010050000040100201a0340000000a03c008020040140600200002003000002034018010000040080300a0000180c00600c018080000000280400c00400005002004000000080040100600000c030000100380000000a0040080000000c008010000000000100202405801008000010030040180080000000002003000004000000020000080000404800000002004000080020180200700400800001004000018010020000180000403c00007002018028020000140180300000c01002000008018070060080000102400001008004014000089dd855290e746154a439bd895190e6c6254643cbd4a5290eb76154a43ad1855290eb66114a43ad5845290f375194643abd895190eac6254643ab9885190ead6214643ab98b5090ead62d4243ad9875090eb561d42438fd954310e5f6550c439bd895010e6c62540439dd855010e746154043c798e5310e9e6094c43ad9875210eb561d4843cb5485210eae62d4443ab58b5110f355114443abd895010eac6254043add855010eb46154043ab9885010ead6214043ad9845010eb56114043c794c43d0b364394742cd10e51d0b364354742cd10d51d0b1e5390e42ad5874290ae661d0a42c714e4350aae6290d42b99874250b1e5310c42ab5884310ab561d08428fd954210a6f655084297d8d5010a5c63540429dd855010a7461540429d98454cca7561153328fd9151cca3c64547328f99250cca3d
  | 4 => 0x588db0000007340013b0002340021d000000000000fa13d0a1dd000000fb05d2c01ec1e2b94bc000000005764b80013f1fe0000029e43000000000000000880171021bc2c800258a5832a9530871c38209358000830b903c000000eb37e768d20000940747900000000000000000738000000004a00022047200000000000add47800000000001fe3a2a34b680000089c001c10000000024f00000000097526771071420625f08e1f354c018d00022ec03c0011a0000000016600000000000000788001930000000000010a0244e8ed0003e4000003c87940200051225000000000500000004a2001201f70000007881100000000000000000000000f4294649ec1c63f000000000000001e80240001525f000b14c11f1458688dc80e4500014e1db5742e12997f544000a58004c64d40000000022cef800000000da1b358c0000000000084ca60000bc3e0a709b04c3ec0027e4004e4b28890008dd060d62180005b00000000000000000000001052e85693e000000000000000002589e8000002cca822d54a000000000004ac0025d0000009911330a434001c32be2655e9be0008287b9d32083bc270dd4aa00093020000158850005069cc5a8c5582000002610000011a80012a00119a6542a04c0000043c0000025a0000000015c000a6077114000000fc000000000000d200017c001a50000012b000000000000793e4000000694ea9ac000004a461c0011b00000000254000124000000000000000018e4a9080c20003ccab8cc000890ff8001be27800000000478000001d40001582100052449abf0001040007e0001200000000011c0000000055400000000a2c000002e0a04000000000000000021c91874aa723a000a98d9434030c6000152000501eb1e0820340000000006724300000008000212001620001b4a90430001b05bc5700026e1dd17a11504778578820000011802d000001441221800006513c0006440e1d730c639312ac2d600000000000000aa1a700a5a11e00000000000276000000000000002a1259943dc3909000047e0001c867000001058bd000a68001ca04e73d2200027c000001232f64c0490000008d800000000514b50005789a548800000000000002f295cfa93a1ca1c4000000a81106e0000000000000008600000000492460a3ac000002134000508001228004de000988001480008388405e000d80000008ad209cc3f4ab94e8764426f0b70003742f8008884c85dc001814dc27c000001a20001295e0dc0002d0005540000011700000111000000001461670000010fab20000004510b00032ca92193888348123e00081cdd8d040267800000484000000000004453d800000928000cf49c03400000000000180001424d8fd8ad000001518000007008c800000000000000003500025c0000000029400000
  | 5 => 0x2400000000000000000000000009b40026a0000000010f1faac0000001860014383d0000000015d0b078014835000a155c19824a71945280000934000000002fcc40420987f1382970ae12c0000000000000292390000018003a456000000000000000003fa810cb083046000000002a2634482b6320000000000d40015a880000000f4989000000d900002c0000d00055a5180000000000000000188000000000000000029f3e8000461e61782dc000c12f4000330000aa0003c0001c0a653a000000648cd00017465cd595b29e134b21444ee100000fe35283d240aa520398dc03a0e44853d0bb336000558001641901a0001c21f05380022a000000000008f40000010e0011c1f03849c4000000004bcbf23b3f2000110002f06c44c0000008713c9803506f4002600002c400000000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xb1c690c0002ad3a79830a1805888365381264809000288ae0320803810400043c20071742218c299065a210c604c832d08863126218e9043181310c60e39ac828243461c15310c21a90e0a986410d507054c3108652ba6ca90843311cd64484219c0e0b224210e846310d2108652ba0c0908438514d61d0940c48a4b0e84a060c5358b4150312b10a3a0a81321c96010c309a0e2b00861858872580430c2c838ac021861269da434c030d1486312601869243185300c312aa4c3a10410bdd95488420a32ea21860106255498b410421bbb2a990821465d4430c010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8884835d36548421884835d06048421
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 735
  | 4 => 712
  | 3 => 30
  | 2 => 2
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
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (756+((h/14+packedAt s3K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s3K5 (22295+((h/245+packedAt s3K5 (19845+(h % 245)*10) 10) % 883)*11) 11
  | 4 => packedAt s3K4 (29663+((h/237+packedAt s3K4 (27056+(h % 237)*11) 11) % 1250)*11) 11
  | 3 => packedAt s3K3 (1530+((h/10+packedAt s3K3 (1470+(h % 10)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (122+((h/1+packedAt s3K2 (120+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3ffffffffffffffff03ffffffffffff0fffff
  | 1 => 0xfc03fc07fff80ffffffc0fc07ff81ffff31e3f
  | 2 => 0xfffc0007fffff01ffffff0007fffe07ffc1fc7
  | 4 => 0xfffffff80fffffe03fffffff81ffff80ffe3f8
  | 5 => 0xfffffffff00000003ffffffffe000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc0848430118922448600b2cc965a28b1056cdb
  | 1 => 0x47a12952a690e4891b2c05542aa91d5a73162d
  | 2 => 0x892ba2a4cb2241d22d5550284d37446cbc1b46
  | 4 => 0x123230c68c448903b19a69b101c59608daa3b0
  | 5 => 0xe3c3c3070f870e1c3ee38e3e70061870efdc00
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaea8080a8a88080eaea8080a8a88080eaea8080a8a88080eaea8080a8a88080eaea8080a8a88080eaea8080a8a88080eaea8080a8a88080eaea8080a8a88080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
def s4K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x200000400130007721dc43b087a10e421
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2990621
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 5
  | 2 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*4) 4
  | 3 => packedAt s4K3 (i*15) 15
  | 2 => packedAt s4K2 (i*26) 26
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (5+((h/1+packedAt s4K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s4K3 (79+((h/1+packedAt s4K3 (75+(h % 1)*4) 4) % 13)*4) 4
  | 2 => packedAt s4K2 (27+((h/1+packedAt s4K2 (26+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffffffffffffffffffffbfc7fffe3fff1ff
  | 1 => 0xfffffffffffffffffffffffd7f879ffc707e67
  | 2 => 0xfffffffffffffffffffffffe7ff81fff807f87
  | 3 => 0xfbfffe3ffff8ff8
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xfffffffffffffffffffffff4071100609310ab
  | 1 => 0xfffffffffffffffffffffff2897229a4252665
  | 2 => 0x1922752c90a4b86
  | 3 => 0x60441b124c0d50
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 15 s4Pos s4Neg, 0xea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80ea80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0xe7852a3098003023800c0058017267c89c342c1064a149281e10a29485400036010904e215a312011000074c8d4004001708000b05f04f082ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330dfa1e61bd43cc2fca5985f54b30bf28e617d51cc37c81986f10330bfaa461bf548c27ea9185f95230beaa4617c548c378a9184f15230bea9c61bf438c37a87185f94a30bea9461de328c3b865185f94630bea8c61de318c3b863185f94230df20461bc408c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130dfa1a61bd434c2fea4987bd4930b7a92617c524c3d8a4985b14930bfa8a61f7514c2eea2985f14530fa28a6174514c37c80986f10130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa418778c830ee190617e510c3eca2185d94430bea8861f5510c2eaa218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc65907b4cb20bf28e417d51c837c81906f10320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20dfa1c41bd43882faa5107bcca20f6194417e51882faa3107b88620f610c417e508837c81106f10220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c534837e86906f50d20f719241ed32482fea2907dd4520bba8a417c51483e8a2905d14520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20dfa1841bd43082fca4107bcc820f6190417e51082faa2107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10dfa1e21bd43c42fea5885f94b10bea96217c52c43ec63887d4c710df20621bc40c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c538437e87086f50e10bfa94217e52842faa5085f14a10bea8c21f731843e863087dc8610fa10c217e508437c81086f10210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c534437e86886f50d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f5314437c80886f10110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c530437e86086f50c10bfa90217e52042faa4085f14810bf28821f731043e862087dc8410fa108217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xd529077c8520ef10a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41dea1a837f52507dea4a0dbd4941be29283ec52506d8a4a0efd0941dea1283f7415077c82a0dfd4141be282837e54106fca620df54c41dfa1883bd43106fca420df54841df21083bc42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc77a8798df94b31f7296636e52cc6faa598fb54b31b6a96637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31dfa1c63bd438c6fca518df54a31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263bf434c77a8698dfd4931be29263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf290637d520c6fca218f7cc431fb18863dd310c7ea6218df94031bea80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fdd0721fa20e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21f7a1443ec42887dc6510fb4ca21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf298437d53086f8a610efd0c21dea18437e52087de8410fb10821f719043ed32086fca210fdd0421fa20843f631087ea6210fbc8421fb10843ed21087ea4210f948421bf280437d50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7204f54e40de29c81bf529037ca5206f54a40de29481bf329037c65206f4ca40de19481bf519037ca3206f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6204f54c40de29881bf521037ca4206f54840de29081bf321037c64206f4c840de19081bf511037ca2206f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10
  | 2 => 0x2008000070060040600000c0100000000806401001002014000010000080580f000044008040040000000000200000002008000038040180000080200c0000080e00e004000100080000180c008014008000020040000401e00c0080000202c0000c0000000280100001c0000d0000000080300400c00802002008000080320140a00200200800800002004000000060040000000c0000000000000004805000000000210160000000400400c0300300000c0380000200c000020100040000500200c0100200000802806000010000000300000300900c0080080101601002001008010000000140100580400a03c0200000004c020070060040d0070000000000a008070008010040040080f00205c0180300001c0100001e00000000006000000010000040000000001401806004004030000000000200400201c010000020080000100200003002000000040000120040080000000004800000074028000040000100600400004000022014015f94b43bea96877e51d0efaa3a1df94343bea8687bf52d0f7ca5a1ef54b43de29687bf51d0f7ca3a1ef54743de28e87bf50d0f7ca1a1cf94343dea8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd4943df29287bd5250f78a4a1efd4543df28a87bd5150f78a2a1efd4143df28287bd5050f78a0a1cf14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542fba8a85775150af8a2a17d14542ba28a857f5050af8a0a15f95042bf298857d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccb7a87995f94732fb28e657651ccafaa3997d54732baa8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32dfa1c65bd438cafca51977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265bf434cb7a86997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cb7e86196f50c32bf29065df320cbdc6419774c832f6990657e510cafaa2195f94032bea80657e53d06faa7a0efd0f41dea1e837e52d06faa5a0efd0b41dea16837e50d06faa1a0df55241bf29c837d539077e8720ef50e41bf294837
  | 3 => 0x9c4562ac001f457200087042000000000770001792f8740002491ba8400000000000000000000004fa9300003f5bca80ba2140000011c2220000000031b000154000002dc0006fa7152a1e0b30003009080e82d26465c0e22a000000208001d40009280054604d409272105013f8c06080ac00000000000000004b0000da99957e5218f2ae4b66845e8d5240000001725740009b0bf27e000001db000000000004a20000015a000000000000006b85d96b0000009797d49a000ca00056200000000000530a526018c955220460ca87cef2e52d85cc639a20205bc96930604be4961c1266618b50c458c8bd8ca084126dc0000040e6ecfb91e63e000cf8000000a80005b0000e1371c953c0f8df27b074b5c1b0e537a0000026a47a2988f8e3000000000005909d8ba80d000001482a90006f0dd143000000d7ac521413d8721137ec440000000000000000000000002cd0000004188200000045000196255100000fa000090000009c0e20d20000007e818000000000002d030800000000ad178000000000cc099000000000002501e5878002540dc1c80000028d3c93c0005e0001514d61640000036cb6c00000360bf037a870000000000060a5885700048a000b3ad80003800a8004ac6940024655808c0031500090d14abc17c0010d00311698c0000000000000000000a951f8000600000000005c000001220001440029f00000000159000434000000000012f000524120eb1a34f47d8301791e8a9c0013d1c2000c9ada166940c781b000001299e832c000ae0060d0a882a00047c85c000f710000165000000000908002aa1a58c2470000000010000004560a64000008dc80000060ce000000095c00000000595308000005194e8000005fc0002f194000000ed5f03b12e9644de284738a000015c362d90ac000e198d42654d8086d0ce37000000000000000000001e80029151c0003fb000c258c318004240011d80000079d748003380008880057600000000000000ac2af4b86800729b000000408000000000019d000000000003c2000001420000000000050433800000076885542aa5da000001c25f6750c8800044b500020a0000000000019e000000000009b0002dc000368481ed0504dc0000000042d7600016c62c00000000b40588b80863158e9b20ba2d45a0005800015a92b0004c40000028a8b5079f22e27e0f88003b05b49aac2158a98000db0d4000ab800000000001e427248c00000000000d98005325a4c293a3ae52c0000000000024ab6404b88000530f8148001e0000000aa000000001891c53a6ab5402544009d0c72ab5ec4048182757ac347a800618648a38004e43c56ab070009f9328b94f80000000015a065509181f0000ee0000b000082a1b44a000001d9000000eaa8c21e788f520551e07c4b2061308e502259
  | 4 => 0x350000931dc000ff1fa000a904f22c000000000002ee4ed850874e6170c09043e0b3042218000864460e212227cc630800000000000354830000000d62903919a22477ce7160626000668cc08a000d380013a26c548001b0524c39da0e0854a6897000000001ef00045c0000000093c000945123908d0440000001a9fb000000000005be00000000000000000000002f13387111079442b14000a605b9ee450000000000000a53a800398acc0000014a32400000394000e892e000bb9671b13a47404e2cb5c2734880003960000000062e344000000000000ba6d3e60140000045c00002000218690000001fe7ac000000006251394f52cb980000036800108000000320002f10000017d0a7000ac0002f3000b74330640e60017a2d20000b185aeb4969213ba4015e718812fd0008054d0005d488d622ef00000125170438128dc23c268bf8000000000015b800356890c11f50000007d28b164a348d8aa1e4000001190c400000124000130748085701d8000f32bc000009260007200028300044c9c0000007983700044c000108000002886800060c000c81095a25404d00038e3bcc508d0bec58001560000000000001400000000000000000000000000000000000000000000000000003d25d87b23a00e3587804b11c0788aa5a160000bd25256447407a941cca209f0c3066a28000c11f237542a4e2fc0248e0891d021972000000000002f500083800000462c0c0003d1740f1718002c2af90b000000030c400043c00000000586080ee94e11e058d49fc3d8b243aaff3500011b0000000000000004c0003f000000000000000007e42380033c6b46b80059e378fe80039e1699015d468050a22304929040015f4068c94ba935d0548ff8340646116382409c0018d20b0005ecd626241a0000000000002c6ca68000874000004d2b4cca95b1f83f8202862820c46981a5eeb5894800000000f1ae74ccb803da354663acd30fb612c708b114620094541074f05f08319b5e414026a
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xf434831c53d0d208f995434823c6550d20c7d4d434831c5350d209b996324834c538c9209b195324834c534c920cdd53514833454d4520d5d4f514835453d4520cdd0f514833543d4520cdd5051483345414520d5d4c51483545314520cdd0c51483354314520d98c8514836532145208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd4440483345110120d314e204836451881209798c540825d63150209d984540827561150208f992530823d6494c208f990530823d6414c209b98853082766114c209d584530831e5350c20c754d43082b86050c208f992520823d64948209b59732082e661cc8209b594320823f64544208f191510836551084209bd9520082cc6348020b9185200827b65480208f58e54c423f63553108f99353c423d64d4f109b98b53c426d62d4f108f99253c423d6494f109b98a53c426d6294f108f99053c423d6414f108fd9743c423d65d0f108fd9543c423d6550f10ae18143c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c426e62d52109b58b548423e6494e108f592538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f59252842e662cc610d9d48218423d63d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58c544423e60151108f180544431f54d4d10c7153534431f64d4d10c7193534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534423e6414d108f590534425e6514d10c7d50534431c5414d10c7990534431d6414d10d5584534423e65d0d108f197434431f53d0d10c714f434423e6550d108f195434431f5350d10c714d434432f54d4910cb153524434f53d4910d314f524432f43d4910cb50f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910cbd0c524432d43149109d9963144354538c510d914a3144274654c510d514d3144364524c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c5210110d514e104436452841109798c540425d63150109b988540426d62150108f992530423d6494c108f990530423d6414c109b988530426d6214c109d984530431e5350c10c754d43042b86050c108fd91520423c64548108f990520423d64148109798c520425d63148108f992510423d64944109d59731042e662cc4109d59431042756508410d9548210427965840109dd9510042d46344010b9189100427b6544010
  | 1 => 0x23e650c8408f59432102ba60d4440abd8951102ac6254440a798c511029d6314440ab98851102ad6214440cd54451102ba60144408f997311023d65cc440c754f31102ae62cc440ab58b311031d534c440aed8131102b8604c4408f994311023d650c4408fd95211023c65484408f994211023d6508440e9484211033a6094040c758f548c33a60d5230c758c548c33a6015230ae983438c2b86050e308f992528c23d6494a308fd91528c23c6454a309dd85528c2746154a308f992518c23d64946308fd91518c23c64546309bd89518c26c6254630a758e408c29d63102308f992544c26e62951309b58a544c27661951309d586544c26f62551309b189544c27761551309d185544c23e65151308f997434c2ba60d0d308f195434c2b86050d30cbd53524c32c54d4930cbd0f524c32d43d4930cbd50524c32c5414930cbd0c524c32d4314930cdd53514c33454d4530d9d4b514c36452d4530cdd0f514c33543d4530cdd50514c3345414530d9d48514c3645214530cdd0c514c33543145308f996404c32f5290130cb14a404c3375190130cd146404c23e6510130cbd48404c32c5210130cdd44404c3345110130d314a304c354518c1309b98b540c26d62d50309d987540c27561d50308f596540c23f63550308f58d540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30cb952520c32d5494830cbd0e520c32d4394830cb951520c32d5454830cbd0d520c32d4354830d354a320c3365494430cd552510c3665294430d954a510c3374394430cd50e510c3365454430cd551510c3665254430d9549510c3374354430cd50d510c355518c4308fd96400c23d6590030a758e400c32e5290030cb54a400c3365190030cd546400c23f65100308f594400c29d6310030cb948400c32d5210030cd944400c335511003097d95300c2cc624c030b5185300c398404c0309ed95300c39b434c0308f58e54c823f63553208f99353c823d64d4f209d98753c827561d4f208f99253c823d6494f209d98653c82756194f208f99053c823d6414f208fd9743c823d65d0f208fd9543c823d6550f20ae18143c827661d52209d587548823e6494e208f592538823e6414e208f59053882766114e209d58453882e661cca208f992518823d64946208f58f544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6315120c7d53534831c54d4d20c7d93534831c64d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d208f990534823d6414d2097994534831f5414d20c7150534831e6414d20c7590534834d6214d208f997434823c65d0d20c7d4
  | 2 => 0x64543318f19150cc66e62152319b588548c63f6454a318f191528c6e662cc6318fd91508c63c64542319bd89544c66c62551319ed81544c67860551318f990524c63d6414931b998b314c63e64d41318f593504c63d65950318f982540c63c60550318f990540c63e6494c318f592530c63d65d0c318fd95430c65f654c4319dd95310c795434c4318fd91500c63c64540319bd89500c66c62540319798c54c865d63153218f99253c863d6494f218f99053c863d6414f21c794d43c871d5350f21d594d31c863f64543218f19150c865e63152219758c548863e6494e218f592538863e6414e218f590538871e5350e21c754d438874e534ca218fd91508863c64542218f58f544863e60d51218f992544866f62551219dd85544863e65151218f58c544863e60151218f992534863d6494d219b58a53486756194d218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f997434863c65d0d218f995434863c6550d21cd153214872c54885218f993504863d64d41218f596540863d63950218f982540863f6355021cb189540873461550218f181540863e64150218f993530863d64d4c218f992530863d6494c218f990530863d6414c219e98053086796014c218fd97430863d65d0c218fd95430863d6550c21cb553420866d6510821b9584420866d658c821b9586320873554d0421e9d0b41086756510421b958841087a442104219d59631086e5628c421b958a210866f6548421ab19121086776548421ad19121086e76548421d9d9521087a76448421b999121086e46448421e919121086a46448421e995121087a55448421b9d8d21086e56348421e9d0d21087a54348421b9181210863f64540218f191500865f63540219718d500871d53d0f40c754d439032e5250a40add8542902b46150a40abd8941902ac6250640cd94541902ba60d4e40ab98853902ad6214e40ad98453902b56114e40ae98053902b661d4a40ad58752902ba60d4a40cbd4a52902ba6014a408f997329023d65cca40ad98732902b561cca408f994329023d650ca40ab98b51902ad62d4640ae98351903375194640ae980519023e65cc6408f59731902ae62cc640ab58b319023e650c6408f594319023f65486408f195219023e65086408f59421903a521086408f997435031f5350d40c754f431023d6590c409dd8552102746154840add8542102b46150840cb548421026f62544409b18951102af6250440ab189411033551104408fd95401027b6550040ae98353102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae98352102b76154840ad185521029e6314840a758c521032d5214840ad98452102b56114840ae980521023e65cc8408f597321031d53cc840ad98732102b561cc840c754d32102bb604c840ae181321
  | 3 => 0xfa6c1a86e48302e3b2240001aa03cbd01d17832c8c021884112998ea00018c370571980005050600020824c870d100083cb790b0b6395611ed1100009382200c000600005810004060100200c0900000000010040e01c1a1280000802024300440002c3d02c010180001c000281207c000040104001000030000201c070040000026020000000000c0102003018040140101001038000140700400000300a4060000c06c05060030000007807040050e00309400000050080004c150000b0001a0000d0402e010190080301c27010010540301400024020480108c040080000004004050080404c020001e00008004000042d05c07034040401200000010020700100800004060000700c0900c07000110180208416008000d80b02c030000001c0500c1e00400138020040100803000080481d020060240300400010270581b0000e000040002b014000081d0000001c01008060042c0201c05c0100005000050381500408048030080c08c2e00006064000001906c060201c000100140501c11002776154b439d18552d0e6f62547439b18951d0eb76154b43ad18552d0f2d5214b43ad98452d0eb56114b43abd8951d0eac6254743ab98851d0ead6214743cd54451d0eae62d4343ab58b50d0eb661d4343ad58750d0eb76154943ad1855250ebb6054943ae1815250f2d5214943abd895150eac6254543aed815150eb86054543cd5445150eaf6254143ab1895050eb76154143ad1855050e3f6550c4397d954310f1e5450c43c754f43d0b1d5350e42c7d4d4350aac6250d42cdd0f5150b3543d4542cdd0c5150b354314542d9d085150b364214542c754f4310aad62d0c428fd954210ab461508429bd954210ae461508429d98754cca7561d53328f98254cca3c60553329d98454cca756115332cd95251ccb355494732cdd0e51ccb354394732cd95151ccb355454732cdd0d51ccb3543547328fd9150cca3c64543329d984548ca756115232b9987328ca3f64546328f191518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544cae661cc9328f990514ca3d64145328f993504ca3d64d41328f596540ca3e60950328f181540ca3e64150328f992530ca3d6494c328f597430ca3f6550c3297d95320ca6f654c832e350d320ca3f64540328f191500ca7761540329d185500cb1d53d0f41ad18542d071d5350e41c7d4d43506b46150d41cbd0f525072d43d4941cbd0c525072d43149418f997425072c52d0941cb14942506b46150941d914b415072c5290541c754f43106b561d0c418f596421063f6550441ab18941106776550441b9189411066e62d53319b58b54cc63e60953318f18154cc66e62153319b58854cc72e5494b31cb55252cc72f4394b31cb50e52cc72e5454b31cb55152cc72f4354b31cb50d52cc63f
  | 4 => 0x8280f129caf8be9185a88485e87545e28d512064fc9317a822014b4d1e2ab1e6a614f0f54d2b60d4aa1160c107598f14c2e048980140378dd9ff0fc8785f16208a000001eb5f2bc00012e42a2e454a2c00001091a230785a563a58262b48b92861360000000022c0012780002a0005a00e000000000e800000134000000000a205e3d2064000960003bccf9dd00014c8aacb0000f90a00053e11cef84e1e83a86aaee2ec5a14a1b347494c9690f3c2a6d810001d26ad488000002c9750000c2000000000006bcd20003f63fc000002f8000f52720000000f800000be800000000228fa000000000bf8df20497c001cf14e57c252ba0002f181a6e2500004687d5ec001858002420000021d0f81ac058000009680d1ac1f44905b8411288dccb8ed11e7b0001d705a000bb93b42e9d12290c3b6001760f7278595069cc450540108005ae90c6695e34466838afe52c1c0bc91c0a89517e8000000f4011f50005916f8000c61fc0011d08ca41650dd4201e0e32b04962640001854a00000000000ba0882c04f04349d0f8264b6cd3a320f46fc2128c3debc4a600015682d029c351c0e4142cf324ad9380725d2add4914d5349e8818ee26c934322514101880280038250d1ab0c2682a8c42bb3b4449020000a24dc092a422e714002c50f2898002ce3aa120651603c40580000006608d16800312a2c001b700052cfd06e4f60004b9511ac0013295b51e32cc620a3d0ab8600fd0009b4e3a835f8698f20e6266739839ae2908240007445c8f86c2ff5b25580ea49364000a10d74bc958f700043699d10a421c69a8958324ec330a30093a4ac55415c026000b08c13049ad2ead11a413c081bd3887940022227a1953e00c0704144c2790603ed452622cc8cd500290aaa20ab98b0a4001148d331c2780004042200040ac93cc071008243f022d0c88e4342ec07ae5000940e02714aaa1d0b2441348ec5b0774489056b2c60b059c8884c1d828546b060009bcae9ba16a000002ed138b408514a490324431f1292740d093e27e000001f337c2e800000392a9977800056000d1a4057e31cba1291c8500002dc3324e0950000000000025c3ceaa5560604e6be0b6953494b90e69f041c3c0c8a13384018c83080b8a08000691ce288c291b3ee16800003564a157091443860c89a254305ec410c833a46400125106bc8000fe000000c517120e8f4e88870ec5b12bb00000881290343684213b91a350488c381b3b07f4ca0734fa05c0406c1b24791f94f3a6001758a52e0000402b825eb041daa75e62488081452ea243d97a55a000848c428e00000284054000000314c83d8000004c6080002273c0110802af4040d95c9f6000b350382c0cc094009450000011c9931c22b0c6a9c5cc5ac62ac360a001408000ba000ac9dc5c6000001fe2b06d9640fc2a80fd0
  | 5 => 0x2145400056a000069e317e00025a2b3380017100046c158902cc0000012cae74ea00000261000568000000005d4001d61620018496a33c555498000007f0b704d0006b44a9bc13eb69621f95783894c8f2568000619b152aa00379a5336339852fb5667c9230355ee728341c83bc01d518e04fe15d018000008d00002637072cc0ade4b66d52392c340164ca86d00019c248cf0d4618d802747049980a0015a3e518add308af46d22a1a0a742f97305e3084e93006e0445208c23eb54b193915e5497013555436d3017e16693
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1b2b5c0080c2400000268c2800e94c8000004844c088b036bc00d4400f3710000002c856a028d41815200bac4e00000002c01a4800e803054f866629a00643988000700001ea94000002043080200282022c1000a00084a48e2a90a5a1e255258452d0e92392a228e87895895114743a48e2a90a4a1d28705485250e92392a228a874c1c15114543a48e4a18a2a14a47158b4310a9238a8629283291c961d0c41c48c430aa810c387059543086523a2c319043291d1628c42194ce93224210ca5731912108653380c890843291da5448421948ecaa24210ca47458d2108670382c690843291db4348421a4aeba1a4210ca47650d2108713290c2a14818918a5150640a4ce3a94a52052672d465190293baa4210c81491c55210840a48e4a88822060d63548521029238aa429081895496114840c2aa6b0e6420615635445110292392a228881895895114440c1aa6b16622041d7319521102923aa4210881895952108440c32c7306a9185287050c524c2983828628a618358d5210030c2ac6a88801868862101300c34830880980618654c6050c20a48e8a88421052674d48218430ca98c0a1821491d15208410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa81810238885831da5448421824865d74348421c05631c55214840c05631c95114440905831d52108440824875952108440
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 5 => packedAt s5K5 (24564+((h/267+packedAt s5K5 (21627+(h % 267)*11) 11) % 1279)*11) 11
  | 4 => packedAt s5K4 (32278+((h/260+packedAt s5K4 (29678+(h % 260)*10) 10) % 938)*11) 11
  | 3 => packedAt s5K3 (2870+((h/18+packedAt s5K3 (2744+(h % 18)*7) 7) % 81)*7) 7
  | 2 => packedAt s5K2 (366+((h/2+packedAt s5K2 (360+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 1 => 0xfc0ffffe03f83fff83e0fc1fffe1e03fa47e67
  | 2 => 0xfff03ffffc003ffffc00ffe0fffe003fc78f87
  | 3 => 0x3fffffffc0ffffff0000ffffffc3f80ff8
  | 4 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x420808c4890080014a12c211802298409b0ab
  | 1 => 0x49631914392252658168551a6b2142a9a45665
  | 2 => 0x90c5aa289074a4aaac109b48b5540532c68b86
  | 3 => 0xc28a3441224606d34a5a0210c6999603700d50
  | 4 => 0xe30c3871c38738fc739ce39c07111823ff6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80eaa8ea80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1a4f4000084400464a2005a7c00e146a0053d0449320b0adb85000002400cdd38535950794000003cd00000c01e0e62ee40050022401801780005aa00000006000c00220605cd200b9b0000c80000062f0009396005a000000002e4c0000104000000300001080c000030000080080405ff54017f950017e54017f55005fc54015f15003ff5300dfd4c03fe5300ff54c037d5300ff14c03ff4300efd0c03fe4300ff50c03bd4300ff10c05ff51017f94405fd51017f14401ff41007f90401fd41007f10403ff3100ff8c403fd3100ff0c401fe21007f48401fc21017fd4005fe50017f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a20009fd9510047fcca8800afe6544011feb2a2008bf59510047f8ca8800afc6544011be32a20029f19510007fec888002ff6444001dfb222000afd9110007fcc888002fe6444001feb222000bf59110007f8c888002fc6444001de3222000af19110047fea888023fe5444001bf2a22008ff55110047f8a8880237c544400fffb1a2007bfd8d10007bec688002df634400fff31a2001bf98d1003ffac68801efd634400ffe31a2001bf18d1003fb8c688006dc634400fffa9a2007dfd4d1003ffca68801ffd534400fbea9a2007ff14d1003ffe868801fbf434400fff21a2007ff50d1003f7a868801ffc4344001ffb122000bfd8910007dec488002ef6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910007d8c488002ec6244011ffa922008ff94910047faa488023fc5244001ffa122000ff90910007fa8488003fc424400fff9922007ff8c91003ffa648801ffc3244011ffa8a2008ff94510047faa288023fc5144001ffa0a2000ff90510007fa8288003fc414400fff98a2007ff8c51003fec628801ffd314400ffa98a2007ff0c510007fe4288003fe2144001fe90a2000ff08510047fea088023fe5044011fea822008ff14110007fe8088003fe4044001fea022000ff1011003ffe608801ffe304400ffe9822007ff0c110007fe4088003fe2044001fe9022000ffc4110007f62088003fe1044001fb0822004ffd9410025feca08013fe65040057f3282004df99410014fcca08013fd65040097eb282000df59410004faca08013fc65040057e3282000ffd9010005fec808003fe64040017f3202000ff59010005fac808003fc64040017e3202004ffd5010027fca8080037e5404009feaa02004ff15010026f8a80800fff63040077fb182003ff98c1000dfcc60800ffd63040077eb182003ff18c1000df8c60800fff5304007bfa982003ff94c1001ffaa60800f7d5304007fe2982003ffd0c1001f7e860800ffe4304007fea182003ef50c1001ff88608003ff62040017fb102000ff98810005fcc408003fd62040017eb102000ff18810005f8c408013ff5204009ff2902004ff54810027f8a408003ff4204001ff2102000ff50810007f8840800fff3204007ff1902003ff4c81001ff8640801afe6104009ffa882004ff94410027faa208013fc5104001ffa082000ff90410007fa8208003fc4104007ff9882003ff8c41001ffa620800ffc3104001ff9082000fdc8410007fc4208003fd2104001fe1082000fd0841002dfcc008013ff5004009ff2802004ff54010027f8a008003ff4004001ff2002000ff50010007f8800800fff3004007ff1802003ff4c01001ff86008003ff2004001ff1002000ff48010007f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x3ff4110001ff2088000ef90440007fa8220033fc4110001de208800bffcc44005ffc622002ffd3110017fe1888000ff88440007fa4220003fc211001d7f300800dffd404006ffca020037fd501001bfe280800cffd00400077e8020003fe4010001fd2008000ff500400077a8020003f94010017ff980800bff8c04005ffa602002ffc3010015ffb2e200abfd9710057fccb8800afe65c4015feb2e200abf59710057f8cb8800afc65c4001ffb262000bfd9310007fcc988002fe64c4001feb262000bf59310007f8c988002fc64c4015ffaa6200aff95310006fca98802bfd54c4015fe2a6200adf15310037fec78801aff63c400dff31e2001bf98f10037fac78801afd63c400dfe31e2001bf18f10037fea78801b7f53c400dff29e2006ff54f10036faa78801bfc53c400dffa1e2006efd0f10037fc878801bfd43c400ddea1e2006ff10f10007fec588003fe62c40017f3162000ff58b10005fac588003fc62c40017e316200affd4b10057fca58802bfd52c4015fe2962000ffd0b10007fc8588003fd42c4001fe2162006ffccb10037fc658801bfd32c400dfe196200affd4710057fca38802bfd51c4015fe28e2000ffd0710007fc8388003fd41c4001fe20e2006ffcc710037fc638801bf631c400dfe98e2006fd4c710037f86388003ff21c4001ff10e2000ff48710007f8438802bff50c4015ff286200aff54310057f8a188003ff40c4001ff2062000ff50310007f8818801bff30c400dff1862006ff4c310037f86188003ff20c4013ffb2c2009bfd961004ffccb0800afe6584013feb2c2009bf5961004ff8cb0800afc6584001ffb242000bfd9210007fcc908002fe6484001feb242000bf59210007f8c908002fc6484013ffaa42009ff95210006fca908027fd5484013fe2a42009df1521002ffec708016ff638400bff31c2001bf98e1002ffac708016fd638400bfe31c2001bf18e1002ffea7080177f538400bff29c2005ff54e1002efaa708017fc538400bffa1c2005efd0e1002ffc8708017fd438400bdea1c2005ff10e10007fec508002ff6284001ff3142000bf98a10007fac508002fd6284001fe3142009ffd4a1004ffca508027fd5284013fe2942000ffd0a10007fc8508003fd4284001fe2142005ffcca1002ffc6508017fd328400bfe1942007bf5861004ffea308027fe5184013fea8c2009ff14610007fe8308003fe4184001fea0c2000ff1061002ffe6308017fe318400bfe98c2005ff0c610007fe4308003f72184001ff10c2000ff48610007f84308003f421840077f3042009ffd421004ffca108027fd5084013fe2842000ffd0210007fc8108003fd4084001fe2042005ffcc21002ffc6108017fd308400bfe1842000ffc8210007fc4108003ff1084001fb8842000fec4210047feca88022ff6544001bfb
  | 2 => 0x40005fac3a0033fc61d0027ffa8e8013ff9474009ffaa3a004ffc51d0019ffa0e8000ff90740007fa83a0033fc41d001fff98e800fff8c74007ffa63a003ffc31d0001ff10e8000ff48740007f843a004fff50d0027ff2868013ff5434009ff8a1a003fff30d001fff186800fff4c34007ff861a004bff65900257fb2c8012ff99640015fccb2004b7e65900053f32c8012ff59640095facb200037d65900013eb2c8012ff19640015f8cb20042fd6490025ffaa48012efd5240097fca9200037e5490025feaa48012ff15240096f8a92004bbc54900259e2a4800effd8e40075fec72003bfe63900037f31c800eff58e40075fac72003bfc63900037e31c800effd4e40076fea72003bfe539001dfea9c800edf54e40077f8a72003bff439001ddfa1c800eff90e40077fa872003bbd439001dfe21c8000ffd8640007fcc320002fe6190001feb0c8000bf58640007f8c32004bff5190025ff28c8012ff54640097f8a320003ff4190001ff20c8000ef90640007fa8320003fc4190001de20c800effcc640077fc632003bfd319001dfe18c8000ff88640007fa4320003fc21900177f3048012ffd4240097fca12004bfd5090025fe2848000ffd02400077e8120003fb409001dff984800eff8c240077fa612003bfc3090023ffb2a8011bfd9540006fecaa00027f6550023ff32a8002bf9954008ffacaa0046fd6550023fe32a8002bf1954008ef8caa000a7c6550023ffaa28011ff95140006fca8a0047fd5450023fe2a28011df15140087fec6a0042ff6350021ff31a8001bf98d40087fac6a0042fd6350021fe31a8001bf18d40087fea6a00437f5350021ff29a8010ff54d40086faa6a0043fc5350021ffa1a8010efd0d40087fc86a0043fd4350021dea1a8010ff10d40007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150023ffa8a8011ff9454008ffaa2a0047fc5150001ffa0a8000ff90540007fa82a0003fc4150021ff98a8010ff8c540087fa62a0043fc3150001ff10a8000ff48540007f842a0047ff5050023ff2828011ff5414008ff8a0a0003ff4050001fda028000ff901400077c80a0043ff3050021ff1828010ff4c140087f860a0033ff651001b7fb28800dff99440015fcca20037fd651001b7eb28800cff19440015f8ca2003efe641001bffaa0800defd5040067fca8200337e541001bfeaa0800cff15040066f8a820037bc541001b9e2a0800cffd8c4005dfec62002ffe63100037f318800bff58c4005dfac620033fc63100037e318800bffd4c4005efea62002ffe5310017fea98800bdf54c4005ff8a620033ff4310017dfa18800bff90c4005ffa862002fbd4310019fe218800cffd8440007fcc220002fe6110001feb088000bf58440067f8c220037ff511001bff288800dff5444006ff8a22003
  | 3 => 0xf1944216fb8ca210b7fa651085bed328842dfe1944214bf986210cffea310867fe5188433fea8c4219ff14621007fe8310803fe4188401fea0c4200ff106210b7fe631085bfe318842dfe98c4216ff0c621007fe4310803f72188401ffb044200ff98221005fcc110803fd60884017eb044200ff182210cffea110867fe5088433fea844219ff142210b7fe611085bfe308842dfe9844216ff0c2210c7feca90862ff6548431ff32a4202bf995210c7faca90862fd6548431fe32a4202bf19521007fec890802ff6448401ff3224200bf99121007fac890802fd6448401fe3224200bf191210c7fea890863fe5448401bf2a24218ff551210c7f8a8908637c544842fffb1a4217bfd8d210bffcc690806fe634842ffeb1a4217bf58d210bff8c690806fc634842fffa9a4217dfd4d210bffca69085ffd534842fbea9a4217ff14d210bffe869085fbf434842fff21a4217ff50d210bf7a869085ffc4348431ffa8a4218ff945210c7faa290863fc5148401ffa0a4200ff90521007fa8290803fc414842fff98a4217ff8c5210bffa629085ffc3148401ff10a4200fb88521007fec090802ff6048401ff3024200ff58121007f8c090802fc6048431ffa824218ff941210c7faa090863fc504842fff9824217ff8c1210bffa609085ffc304842bffb284215bfd94210affcca1080afe650842bfeb284215bf594210aff8ca1080afc6508401ffb204200bfd9021007fcc810802fe6408401feb204200bf59021007f8c810802fc640842bffaa04215ff95021006fca810857fd540842bfe2a04215df150210a7fec610852ff6308429ff3184201bf98c210a7fac610852fd6308429fe3184201bf18c210a7fea6108537f5308429ff2984214ff54c210a6faa610853fc5308429ffa184214efd0c210a7fc8610853fd4308429dea184214ff10c210b5fcc210857ff510842bff2884215fd944210affaa210857f5510842bfe2884200ffd0421007ee8210803fe4108401fea084200ff10421007e88210853ff3108429ff1884214fd8c4210a7fa6210853f53108429fe1884200ff88421007ec4210803fd2108401fa9084200f948421007fec010803fe60084017f3004200ff58021005fac010803fc600842bffa804215ff940210affaa010857fc5008429ff9804214ff8c0210a7fa6010853fc3008419ffb2e8013bfd974009ffccba000afe65d0027feb2e8013bf59740067f8cba000afc65d0027ffaa6800cff95340066fca9a004ffd54d0019fe2a6800cdf15340067fec7a003eff63d001fff31e8001bf98f4007ffac7a003efd63d0019fe31e8001bf18f4007ffea7a003f7f53d001fff29e800fff54f4007efaa7a003ffc53d0019ffa1e800fefd0f4007ffc87a003ffd43d001fdea1e800cff10f40067fec3a0003fe61d00017f30e8000ff587
  | 4 => 0x87efd655043ffe32a8202bf195410fef8caa080a7c655043fffaa2821fff95141006fca8a087ffd545043ffe2a2821fdf151410f7fec6a087aff635043dff31a8201bf98d410f7fac6a087afd635043dfe31a8201bf18d410f7fea6a087b7f535043dff29a821eff54d410f6faa6a087bfc535043dffa1a821eefd0d410f7fc86a087bfd435043ddea1a821eff10d41007fec4a0802ff6250401f7b128200bbd8941007fcc4a0803fd6250401fe3128200bf18941007d8c4a0802ec625043fffa92821fff949410fffaa4a087ffc5250401ffa128200ff90941007fa84a087bff325043dff192821eff4c9410f7f864a087fff515043fff28a821fff545410fff8a2a0803ff4150401fba0a8200ff905410077c82a087bff315043dff18a821eff4c5410f7f862a0803ff60504017fb028200ff98141007fac0a0803fc60504017e302821fffd41410fffca0a087ffd505043ffe282821effcc1410f7fc60a087bfd305043dfe182820cffd94410ddfeca2086ffe65104057f328821bff594410ddfaca20833fc65104057e328821dbf990410dffea820833fe5410419bf2a0821bff55041067f8a8208337c5410419ffb18821abfd8c410d7fcc620806fe6310435feb18821abf58c41067f8c620806fc6310435ffa98821adfd4c410d7fca62086bfd5310435bea98821aff14c41067fe862086bbf4310435ff218821aff50c410d77a8620833fc4310419ffb108200ff98841005fcc420803fd62104017eb10820cff188410dffea42086ffe5210437fea90821bff14841067fe8420803fe4210401fea10820cff108410d7fe642086bfe3210435fe990821aff0c8410e5fcc22086fff5110437ff288821bff544410dff8a220833ff4110401dfa088200ff90441007ec8220803fd4110401dea088200fd504410d7fe622086bfe3110435fe988821aff0c441067fec020803fe60104017f3008200ff58041005fac020833fc6010437ffa80821bff940410dffaa02086ffc5010435ff980821aff8c0410d7fa602086bfc3010433ffb2c4219bfd96210cffccb1080afe6588433bf32c42029f996210cffacb10866fd6588401beb2c42009f596210cff8cb1080afc6588401ffb244200bfd9221007fcc910802fe6488401feb244200bf59221007f8c910802fc6488433ffaa44219ff95221006fca910867fd5488433fe2a44219df152210b7fec71085aff638842dff31c4201bf98e210b7fac71085afd638842dfe31c4201bf18e210b7fea71085b7f538842dff29c4216ff54e210b6faa71085bfc538842dffa1c4216efd0e210b7fc871085bfd438842ddea1c4216ff10e210bdfac510867ff5288433ff2944219fb94a210cffaa510867ed5288433fe2944200ffd0a21007de8510803fe4288401fea144200ff10a21007d8851085bff328842df
  | 5 => 0x30000041a8250000340f0080260000780100400000003002010008080080000003d0080000380b00004c01009000004010000140040300f00e0000081e000014028060400040b0010720c8138020140000800502e0000480003c0180380102e1441400102201400800014000008080200080980105c00c0d00101800c000020080100100e0000000380b00a000078100860cdf99254014fcc92a00b3e6495019bfb1ca8229fd8e54116fcc72a08b7d63950453eb1ca80cdf18e54066fe872a08b3f4395045bf21ca822df50e541167a872a0337c4395019bfb0ca800df98654006fac32a0337c6195045bf98ca822df8c654116fa632a08b7c3195019bfb04a800df98254006fac12a0337c6095045bf984a822df8c254116fa612a08b7c3095019ffb2e8221bfd974110ffccba080afe65d0443feb2e8221bf59741067f8cba080afc65d0443ffaa6820cff95341066fca9a0887fd54d0419fe2a6820cdf15341067fec7a0876ff63d043bff31e8201bf98f410effac7a0876fd63d0419fe31e8201bf18f410effea7a08777f53d043bff29e821dff54f410eefaa7a0877fc53d0419ffa1e821defd0f410effc87a0877fd43d043bdea1e820cff10f41067fec5a0803fe62d04017f3168200ff58b41005fac5a0833fc62d0443ffa968221ff94b4110ffaa5a0887fc52d0419ffa16821dffccb410effc65a0877fd32d043bfe1968221ffd474110ffca3a0887fd51d0443fe28e821dffcc7410effc63a0877fd31d043bfe18e820cffd8341007fcc1a0802fe60d0401feb068200bf58341067f8c1a0887ff50d0443ff2868221ff5434110ff8a1a0877ff30d043bff186821dff4c3410eff861a0883ff65904417fb2c8220ff99641015fccb208837e65904053f32c8220ff59641105facb208037d65904013eb2c8220ff19641015f8cb2087afd6490441ffaa48220ff95241006fca920883fd5490441fe2a48220df152410e7fec720872ff6390439ff31c8201bf98e410e7fac720872fd6390439fe31c8201bf18e410e7fea7208737f5390439ff29c821cff54e410e6faa720873fc5390439ffa1c821cefd0e410e7fc8720873fd4390439dea1c821cff10e41007fec520803fe62904017f3148200ff58a41005fac520803fc6290441ffa948220ff94a41107faa520883fc5290401ffa148200ff90a410e7fe6520873fe3290439fe994821cff0ca410d5fcc320883ff5190441ff28c8220ff54641107f8a320803ff4190401dfa0c8200fdd06410e7fe6320873fe3190439fe98c821cff0c641007fec120803fe60904017f3048200ff58241005fac120803fc6090441ffa848220ff94241107faa120883fc5090439ff984821cff8c2410e7fa6120873fc309043fffb2a821fbfd9541006fecaa08027f655043fff32a8202bf995410fffacaa0
  | 6 => 0x600014d0a5981000136800000235a241244000878021f29868c919e06402c9ae15d123d495182778b2c678000001639d3a1692645302b64e8000a2a6488e85e15921e0550428395e619fa51a41a4685206b9b58df4d811a83ea3f0eb9714b21290b79210f61109ad149c001041d8a32883250147c99987924cad0ff5916049d402cd5c1411c79792719c4183968058070800065072a3a0001ba88f80012f8196849e3800145a4901b00028100007f2088441058c9807dc086612c18ed484a4c0da660000c70f1a110001010000000fcdd794b80cd532038451932760000000000ea80000000000025c0b800026f800041d261b094f9c48000e28000000a54360039a18fe8001282681909f797a00000020095e1498981f989385f9fca7e171e581e48271b98000001050000d50001bd8001128002318f88da8001690c49999aa10aa3e8420001c59720000a200026b1fa8000000e58000001619b500000009d00003f8c78db0002270b280000025d80008c83d00026700027f8718000d980017500001f91693e8001d200000a0c742e86a0508fd5e504ca80d8f58227d08116a87a02283d818ddc0000e0c750001bf1802530a92221a896f1f69d11ce0ae93213ca4f96c03420306d9f305b84d13700022491600020780008d0000ac0000010000020b4008010000000000d0000040000301e000050020380040180408c020008010040fc1180001a0100000600202c0d02600a02001817014000000010000100400701e0001b0020000140081c0000e400006000034058000060600301a02404002004058004000000000000000301a000128040000000a8030480180080103204c000000160280080600e0000080001a0001300200003c0000f0140880a80000e0240c0020020000c830000000000140020040080000808c040070080d80a8090000000680c0060080503100000800003004048080000000000080c00201001011010024108080040b028803000128018080120a804806066000090000000240380f0460080080000e0600100004c0040200900a09c0380203e00000001010048020020020000600000400c0001302002c0000000400009000002028058000100000000000a02c0400002204c008060000780d8090040000180600a018020020000000580701801c0500b0040440300200a0400000000a00c0400d01400c000010000280b00203c0100380000e0640100900a0bc010000020000080400800c0100000003c0f80a00001c000040120140200401c01c0900401204c0001b01a0140101e0020380f000016014000520140540a02d00000000000000004008040100001600a0080140080700a09c07007000064018060060380200f022004000050000000580d018004008060060000300a00002c0080000c00002000008014030
  | 7 => 0x931a1f06802b94b1588e31401f71f59288001475c88f413828600005922d24594c079e0e17290092058a00ecb348f0001fa192a178000e39258000289131a58fa8d78000d21550048ec8fb83819722a83e19aa7b0001d312207d10ba2c8200001081e815e8dea6916707e02d944e6014901e9d0a548000000691fe0fe40013f0001d81904df1a524e00817091e8b9138a199710001731b800010240d11b19440002f9c2146a7206f12f0c00000000001ac83b0000000260f514b4ed8c584a97f814197a5789c840dc502080003cd5a8cb9bde4290887884580001497c00026c05400180013d1529b31098959d70fdd0003699200018fce6a4007c000120c780e0085c002201988525ed8299340ce0ae0758001871761af27a0f58860649a38601b4000238939a7eca6984903cd48a39454760538bc05285e800000201889a5122580e0000bf9a48c08000a78238001610000991b225aa840001bb80014bde7a488b59120000da4b1a56817c4f2430b9a620868d02391035a30000000a080983080306589700003a8db80028720d1a416c9200001a124127089fa0589964c0870ce88512756006198c12a5ad80017895706683296b514839e1f80005c1b144b0bca1c00000010e8001f41cf4001660910791be0068742108000df94adf12460000170b118187c97b9db893144906a2f0510e8a1412941193b1959140a188587a4bd9640ed075408d0e0ad8419fce8827989296a5178dac470000001330001be80015b17040008d8fc20b928dff04bcdfdcd27282d1ca1ebc09620a1ca100721ffa7c12a9e125089a8000000448000001170ec1bc9021941bf9cb94d979a56080922a3f9cdcf390290714e19499627c9dc8639df22e1ab8cf8c60ee1392029b28001c1967a3ba1d95420c05991d1bd06a9696171efa768db4001f88f21cf00013e17c91027e95f92d8eb00019f24800016c685825800000000000000000000043a261421c702a17f2181be50a1e018d9c3a5e8000f00ba81784918e4060724949991218000a94d84000dd951037000287a5e00017a8000f48000c100012316e9686520002408001460000000f99159d68d29eb9b68001890000a42160a80000da00000006c9a2a2da6c80000000000027494723300000016b00e80010f80001327d4af9841208f08bb09791b80018d0001ec0f68854e713086761a8b011519b80012a07017e9fc01524998804ea4c9a21ea98281080007957680010f0000c40fec0011e190c0e5eb6608000000000d8dec8410ff9808c19ef13c19182c24f07f96b82f25a125d6a00460e80019b0000001450240778001dd8002851255431da8749eb168c00166c8e11c118a188be1e0a1b09182fdbd60f09e079a378000000000000f319e8000001782701b0000148c0023200017b0000000838001cd8000159f
  | 8 => 0x78a5b839a731830cd1718ddd6500027d9cc21e80000010600000026e8ee9cfa228190000dc4dbd4a524263a4dc478b627117d03d4090de612c0013a92d1a90001c800000016d83587e93a12865707383de0fa529e2019a829215329fd08409ea5d1b116fcc5c268d096581816cdc61508ea02a98c919189995124a65a3cd630d91ac00012e2342308fa104400000160867145e2817701a0dce6d0e416980024b99805d8a88cda0726f26994c5d00e7a3c90906b104d3f96d4000001519f18071378b44000fe00008b000233800200084d4800f80c2540000a3c1c1900000001738001ab0d1000157a3d01880565f2158351f002499c8a7d3d8ff068929d911bb0de0338664000ca61480000002824d1fe82115a00016f80006280000023d8f79e68001b49aea668000378000000050001f212b00024a0002361e719c000075e126398e047309695b8001ee1ba0000000000c300001e22e8138000aa0849f80002290001f08184ba1de9038a6069846a348ef1fb00003c0fb03f192d8a8fd23c00c58f0001c027f47640014ea2b0bd0f805a900ccc185a4711f9bbc6f93484005f0001269f50570e11d489c22880010487b8000800c209500010304a14a2438ab97d80000001d0000000b3d440f912ba7fc0024b2738549270ac9b900104e21a0d69aa8891db15487d86d1e293b9cca050ca1e9a381016231934e149d94a91125883214f14c90c935a830c39bc1a00988388608500f10e805793121d000193e7e6538908ffd2e8829de275164988800101c0005b0cc82b10c1da19da0a991c498b68588dd0a015827826e0d70d9c3a0d58a70f7029283a6a26d84609f16e1b19b61e304f97425b0c28fd8a998f8e496699255216219d062c00229a640a4a6191ca7f10040000002e10b00001f22b9701778348128a85b3970ddd0ca99a0b404ce6a807a7dd9689b8a500a9ee8e98dee098dc05c96adce941a7911a10781b9cb025236a080a448a8218e08631c69d280c8168c807b64d85194dc3c4000e50000b489208886e122427927d93a062211019d18c5000247a611b89d99238000b7030040574a2381a800000000146d408d94002128b508818e0dca5589a0e226b8b30cf169e5500022a147a371d26869df87a8e61d60558001fb804022230175a598a326780000013503901d9ea16dc0015f0aa9a6a2c00000021300000000000015d96d040a8196f4161d5a442118b38e24c8a2503c800122c97e19023000004c0023b1850058bf0028480001a6265129a011a785d2741e5a1381220c9bc41ca3e2310940310820bb98ba804560a10488ef80000014cc001f90000001360e920a2040001c115c8001a084c4af11197e0331a70d19e18000001235198002449c998b000074e219afa3aa1b861212031a82113a5f8b8a6895608c0771fd88b8cb08667b
  | 9 => 0x1eae090001568101e90620818000001d5273cdd40000000b9338112069ed0001a804d800105e809558d3959a5c84b8f29ca90d92522f96bd94e420c694d5c2a590e189615009b27a86c07bc3b8d898604b443102cbe8d6126df3a629bcc8a20d91d94651f12c8d30ab168856a450e1cfca4a89016287b20201ed05567d5398e84c121d3020b1e89488d405a1c921527580f1b707686ea7728009c625d42800a632351d90b09f480b16ed6e62780d4089a99c300847110d1439279b7a269e42
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x562084101bfe652084101bfe55208410007e74208410007e442084101b7e632084101b7e53208410007f27008410005f57008410007f170084101aef66008410004fd76d001009e7e65d00100067d65d0010004ff7690010004fd76900100257e75900100057d75900100967e65900100067d6590010006be6490010006bd64900101a73c5490010005f67190010005f57190010004ff76500100057f75500100257c755001008e7e65500100067d6550010064ff7610010004fe7610010004fd7610010064fc761001006e7e65100100067d6510010066be6410010006bd641001019f3c5410010005f67110010005f57110010004fd76c80101967e65c80100067d65c8010004ff7688010004fd768801018e7e65880100067d6588010006ee6288010006ed6288010005f67188010005f57188010007e42188010004ff76480100057f75480100257c75480101867e65480100067d6548010005bf7448010005bc7448010005df734801001ddc7348010005f77148010005f47148010004fe7608010004fd7608010004fc760801017e7e65080100067d6508010005f67108010005f57108010007e421080100567e65c40100067d65c4010036f576c40101777665c40100077565c40100077654c40101777454c401016ef763c401016ef563c401016f7753c401016f7553c401016fb743c401016fb543c4010005f672c4010005f472c401004e7e65840100067d6584010155f5718401014ef6618401001df9768401002ef9768401000cf976840101677a65840100077965840100077a548401016778548401015f7b538401015f79538401015fbb438401015fb94384010155f9718401014efa6184010007f26184010007f32184010007f02184010004ff76440100057f75440100257c75440100467e65440100067d6544010005bf7444010005bc7444010005df734401001ddc7344010005ef7244010005ec7244010005f77644010006f77644010004f7764401000777754401011f74754401011f766544010007756544010007b77444010007b4744401000776544401011f745444010007d77344010137d47344010136f76344010136f56344010137775344010137755344010137b74344010137b54344010007e77244010005f67244010005f47244010007e47244010005e47244010145f7704401013ef6604401011ff2504401011ff15044010005fb7644010006fb7644010004fb76440100077b754401011f78754401011f7a6544010007796544010007bb7444010007b874440100077a544401011f785444010007db7344010137d873440101377b5344010137795344010137bb4344010137b94344010007eb7244010007e8724401012dfb7144010007f37144010126fa6144010007f2614401011ff2514401011ff15144010
  | 1 => 0x8810004fd75188100067d75188100047d7518810014fc7518810064fe7418810006be7418810004be7418810004fd7418810006bd7418810004bd74188100067e54188100067c5418810004ff731881000cfe7318810006de731881000cde7318810004fd7318810006dd7318810004dd731881000cfc73188100067f53188100067d5318810006bf4318810006bd4318810004fe7118810006f67118810004fe7018810006fa7018810064ff76d0810004fe76d0810004fd76d0810064fc76d081020e7e65d08100067d65d0810066be64d0810006bd64d0810005f671d0810005f571d0810004ff7690810004fe7690810004fd7690810004fc76908100257e75908100057d75908102067e65908100067d6590810006ee6290810006ed6290810004ff7650810004fe7650810004fd7650810004fc76508100057f75508100257c75508101fe7e65508100067d6550810006be6450810006bd6450810006ee6250810006ed6250810005f77150810005f47150810064ff7610810004fe7610810004fd7610810064fc76108101f67e65108100067d6510810004fd76d041010e7e65d04100067d65d0410004ff7690410004fd76904100257e75904100057d75904101067e65904100067d6590410006be6490410006bd6490410005fa7090410005f97090410004ff76504100057f75504100257c75504100fe7e65504100067d6550410005ef7250410005ec7250410064ff7610410004fd76104100de7e65104100067d6510410066be6410410006bd6410410005fa7010410005f97010410004fd76c84100257e75c84100057d75c84101ee7e65c84100067d65c8410005f576c8410006f576c84101e77675c84100077575c84101e6f765c84101e77665c84101e6f565c84100077565c84100067565c8410006f664c8410006f464c84100077654c84101e77454c84101def763c84101def563c84101df7753c84101df7553c84101dfb743c84101dfb543c8410006f762c8410006f562c8410005f570c84101d6f660c8410004ff7688410004fd76884100257e75884100057d75884100ce7e65884100067d6588410006ee6288410006ed62884101cdf67188410005fa7088410005f97088410004ff76484100c67e65484100067d6548410004ff7608410004fd76084100ae7e65084100067d6508410006ee6208410006ed6208410007e52108410005fa7008410005f97008410006f57608410004f576084101bef765084101bf7665084101bef56508410007756508410006756508410006f66408410006f464084100077654084101bf7454084101b6f763084101b6f563084101b77753084101b77553084101b7b743084101b7b543084101c5f67208410007e67208410006f76208410007e66208410006f56208410007e56208410006e
  | 2 => 0x67c75590100147c7559010006bf74590100067c5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d5359010006bf4359010006bd4359010004ff7259010004fc7259010064ff71590100f4fd7159010064ff7059010084fd70590100257e75190100057d75190100067e65190100067d6519010006bd641901001dde7319010005dd7319010005ee7219010005ed7219010064ff7519010014fe75190100667e75190100147e7519010004fd75190100667d75190100047d7519010064fc7519010064fe7419010066be74190100667c5419010064ff731901000cfe7319010066de731901000cde7319010004fd7319010066dd7319010004dd731901000cfc73190100067f53190100067d5319010066bf4319010006bd4319010004fe7219010066ee7219010004ee7219010004fd7219010066ed7219010004ed7219010004fe7119010066f67119010004fe7019010066fa70190100057f76950100667f76950100647f76950100067e76950100057d76950100067d76950100047d76950100667c76950100257e74950100273e74950100067f64950100667e64950100067d64950100667c649501022d7f739501022d7d73950102267f63950101167e63950102267d63950101167c63950102273f43950102273d43950100567e619501004e7e60950100257e75d88100057d75d88100067e65d88100067d65d8810004ff75d8810014fe75d88100067e75d88100147e75d8810004fd75d88100067d75d88100047d75d8810014fc75d8810064fe74d8810004fd74d88100067e54d88100067c54d8810004ff73d881000cfe73d8810004fd73d881000cfc73d88100067f53d88100067d53d8810006bf43d8810006bd43d8810004fe71d8810006f671d8810006fa70d8810004fd76988100067e65988100067d6598810006ef6298810004ff7598810014fe7598810004fd7598810014fc7598810064fe7498810004fd74988100067e54988100067c5498810004ff739881000cfe7398810004fd739881000cfc73988100067f53988100067d5398810006bf4398810006bd4398810006ee3298810006ed32988100067e65588100067d6558810004ff7558810014fe7558810004fd7558810014fc7558810004ff7458810064fc74588100067e54588100067c5458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810006bf4358810006bd4358810006ef7258810006ee3258810006ed325881021cff71588100bcfd7158810006f47158810214fd70588100257e75188100057d75188100067e65188100067d6518810005be7418810005bd741881001dde7318810005dd7318810006ed6218810004ff7518810014fe75188100067e75188100147e751
  | 3 => 0xc6448110006df6348110216dc6348110005f77148110005f471481100067f65c41100567c65c4110006bf64c4110006bc64c4110006df63c4110036dc63c4110006ef62c4110006ec62c41100077b65c411024f7865c4110007bb64c4110007b864c41100077a54c411024f7854c4110007db63c4110247d863c41102477b53c41102477953c4110247bb43c4110247b943c4110007eb62c4110007e862c4110247f231c4110247f131c41100067f658411004e7c6584110006bf6484110006bc6484110006df638411002edc6384110006ef6284110006ec628411000777658411023f746584110007b76484110007b4648411000776548411023f74548411013df7738411013df57384110007d76384110237d46384110237775384110237755384110237b74384110237b54384110007e76284110006f66284110006f46284110007e46284110006e46284110007f360841100257f76594100267f76594100147f76594100057c74594100057f73594100057d73594100067f63594100067e63594100067d63594100067c63594100073f43594100073d43594100067f74594100067e74594100067d74594100067c74594100647c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100063f43594100067e43594100067d43594100063d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c32594100267f71594100067e71594100267d71594100267c71594100067f31594100067e31594100067d31594100067c31594100267f70594100067e70594100267d70594100267c70594100067f30594100067e30594100067d30594100067c30594100267c10594100257e75d90100057d75d90100067e65d90100067d65d9010004ff75d9010014fe75d90100067e75d90100147e75d9010004fd75d90100067d75d90100047d75d9010014fc75d90100067c54d9010004ff73d901000cfe73d9010004fd73d901000cfc73d90100067f53d90100067d53d9010006bf43d9010006bd43d9010004fe72d9010004fd72d9010004fe71d9010006f671d9010004fe70d9010006fa70d9010004fd76990100257c75990100067e65990100067d6599010006bf6499010064ff75990100667f7599010014fe7599010004fd7599010064fc75990100667c75990100647c75990100667c5499010064ff739901000cfe7399010004fd739901000cfc73990100067f53990100067d5399010066bf4399010006bd4399010004fe7299010004fd72990100057f75590100257c75590100067e65590100067d6559010004ff75590100067f75590100047f7559010014fe7559010004fd7559010014fc7559010
  | 4 => 0x910006bf6410910066bc6410910006df6310910276dc6310910006ef6210910006ec6210910005f67110910005f57110910004fe76d05100067f65d051010e7c65d0510006bf64d0510066bc64d0510006df63d05100eedc63d0510006ef62d0510006ec62d0510005fa70d0510005f970d0510004fe76905100457e75905100057d75905100067f65905101067c6590510006bf6490510006bc6490510006df63905100e6dc6390510006ef6290510006ec6290510004fc76505100057f75505100457c75505100067f65505100fe7c6550510006bf6450510006bc6450510006df63505100f6dc6350510005ef7250510005ec7250510006ef6250510006ec6250510005fb7050510005f87050510004fe76105100067f65105100de7c6510510006bf6410510066bc6410510006df63105100d6dc6310510006ef6210510006ec6210510007b54110510004fe76c85100457e75c85100057d75c85100067f65c85101ee7c65c8510006bf64c8510006bc64c8510006df63c851021edc63c8510006ef62c8510006ec62c8510005fa70c8510005f970c8510004fe76885100457e75885100057d75885100067f65885100ce7c6588510006bf6488510006bc6488510006df63885100b6dc6388510006ef6288510006ec62885100067f65485100c67c6548510006bf6448510006bc6448510006df63485100bedc6348510006ef6248510006ec6248510005fb7048510005f87048510004fe76085100067f65085100ae7c6508510006bf6408510006bc6408510006df63085100a6dc6308510006ef6208510007e52108510004fe76d01100067f65d011009e7c65d0110006bf64d0110066bc64d0110006df63d011007edc63d0110006ef62d0110006ec62d0110005f671d0110005f571d0110004fe76901100457e75901100057d75901100067f65901100967c6590110006bf6490110006bc649011026f3c5490110006df6390110076dc6390110006ef6290110006ec6290110064ff7650110004fd7650110004fc76501100057f75501100457c75501100067f655011008e7c6550110006bf6450110006bc6450110006df6350110086dc6350110006ef6250110006ec6250110005f77150110005f47150110004fe76101100067f651011006e7c6510110006bf6410110066bc64101102673c5410110006df631011005edc6310110006ef6210110006ec6210110004fe76c81100067f65c81101967c65c8110006bf64c8110006bc64c8110006df63c811025edc63c8110006ef62c8110006ec62c8110005f671c8110005f571c81100067f658811018e7c6588110006bf6488110006bc6488110006df6388110256dc6388110006ef6288110006ec6288110004fd7648110004fc76481100067f65481101867c6548110006bf6448110006b
  | 5 => 0x4fe76189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed6218910004ff7518910014fe7518910004fd7518910014fc7518910064fe7418910004fd74189100067e54189100067c5418910004ff731891000cfe7318910004fd731891000cfc73189100067f53189100067d5318910006bf4318910006bd4318910006ee7218910006ef5218910006ee5218910006ed5218910006ec5218910006ef3218910006ee3218910006ed3218910006ec32189100a4fc7118910006f63118910006f53118910005ee7618910006ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac64189100076e54189100076c5418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d5318910007af4318910007ad4318910007e63118910007e53118910006ef7518910006ee7518910006ed7518910006ec7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef5418910006ee54189100066e5418910006ed5418910006ec54189100066c5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef53189100066f5318910006ee5318910006ed53189100066d5318910006ec5318910006ef4318910006af4318910006ee4318910006ed4318910006ad4318910006ec4318910006ef7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef3118910006ee3118910006e63118910006ed3118910006e53118910006ec3118910006ef7018910006ed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef3018910006ee3018910006ed3018910006ec3018910006ed1018910064ff76d0910004fe76d0910004fd76d0910064fc76d09100067f65d091020e7c65d0910006bf64d0910066bc64d0910006df63d091028edc63d0910006ef62d0910006ec62d0910004ff7690910004fe7690910004fd7690910004fc76909100457e75909100057d75909100067f65909102067c6590910006bf6490910006bc6490910006df6390910286dc6390910006ef6290910006ec6290910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100457c75509100067f65509101fe7c6550910006bf6450910006bc6450910006df635091027edc6350910006ef6250910006ec6250910005f77150910005f47150910064ff7610910004fe7610910004fd7610910064fc76109100067f65109101f67c651
  | 6 => 0xf65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076e54d89100076c54d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910007af43d8910007ad43d8910007e631d8910007e531d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d89100066e54d8910006ed54d8910006ec54d89100066c54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006af43d8910006ee43d8910006ed43d8910006ad43d8910006ec43d8910006ef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef30d8910006ee30d8910006ed30d8910006ec30d89100457e75989100057d75989100067f65989100067c6598910005be7498910005bd7498910006bf6498910006bc649891003dde7398910005dd7398910006df6398910006dc6398910006ef6298910004ff7598910014fe75989100067e75989100147e7598910004fd75989100067d75989100047d7598910014fc7598910064fe7498910006be7498910004be7498910004fd7498910006bd7498910004bd74989100067e54989100067c5498910004ff739891000cfe7398910006de739891000cde7398910004fd7398910006dd7398910004dd739891000cfc73989100067f53989100067d5398910006bf4398910006bd4398910004fd7198910006f57198910006f63198910006f53198910006f970989100057f75589100457c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891003ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf7458910064fc7458910006bc7458910004bc74589100067e54589100067c5458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006bf4358910006bd4358910006f77158910004ff7058910006fb7058910
  | 7 => 0x9110066bc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc5319110066bf7219110006be7219110006bd7219110066bc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc3219110066bf7119110006bd7119110006bf5119110006be5119110006bd5119110006bc5119110006bf3119110006be3119110006bd3119110006bc3119110066bf7019110006bd7019110006bf5019110006be5019110006bd5019110006bc5019110006bf3019110006be3019110006bd3019110006bc3019110006bd10191100667f76951100057e76951100067e76951100047e76951100067d76951100057c76951100667c76951100647c76951100457e74951100473e74951100067f64951100073f64951100063f64951100667e64951100067d64951100667c64951100073c64951100663c649511029d7f739511029d7d73951102967f63951101167e63951102967d63951101167c63951102975c63951101165c63951102973f43951102973d439511029776319511029775319511003dde76d8d1003ede76d8d1000cde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d100079f74d8d100079c74d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075e54d8d100075c54d8d10007d771d8d1003fd471d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d100069f74d8d10006de74d8d10006dd74d8d10006dc74d8d100069c74d8d10006df54d8d10006de54d8d100065e54d8d10006dd54d8d10006dc54d8d100065c54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df71d8d1003ede71d8d1003edd71d8d1003edc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df70d8d1003ede70d8d1003edd70d8d1003edc70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d1003edd10d8d100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910004ff75d8910014fe75d8910004fd75d8910014fc75d8910064fe74d8910004fd74d89100067e54d89100067c54d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006bf43d8910006bd43d8910006ef52d8910006ee52d8910006ed52d8910006ec52d8910006ef32d8910006ee32d8910006ed32d8910006ec32d8910006e
  | 8 => 0x6bf31d9110006be31d9110006bd31d9110006bc31d9110006bf70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d91100457e75991100057d75991100067f65991100067c6599110006bf649911003dde7399110005dd7399110006dc6399110005ee7299110005ed7299110064ff7599110014fe75991100667e75991100147e7599110004fd75991100667d75991100047d7599110064fc7599110064fe7499110004be74991100667c5499110064ff739911000cfe7399110066de739911000cde7399110004fd7399110066dd7399110004dd739911000cfc73991100067f53991100067d5399110066bf4399110006bd4399110004fe7299110066ee7299110004ee7299110004fd7299110066ed7299110004ed7299110004fd7199110066f57199110004fd7099110066f970991100057f75591100457c75591100067f65591100067c6559110005df735911003ddc7359110006dc6359110005ef7259110005ec7259110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf74591100067c5459110004ff7359110006df7359110004df735911000cfe7359110004fd735911000cfc7359110006dc735911000cdc73591100067f53591100067d5359110006bf4359110006bd4359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100457c75191100067f65191100067c6519110006bd64191100073c5419110006dc6319110064ff75191100667f7519110014fe7519110004fd7519110064fc75191100667c75191100647c7519110066be7419110006bf5419110066be5419110006bd54191100667c5419110066bc54191100663c5419110064ff731911000cfe7319110004fd731911000cfc73191100067f53191100067d5319110066bf4319110006be4319110006bd4319110066bc4319110004fe7219110004fd72191100e4fe7119110064fc7119110074fe7019110064fc7019110005be7619110006be7619110004be76191100073f75191100073c7519110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110005bf7319110005bd7319110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d5319110007b63119110007b53119110066bf75191100663f7519110006be7519110006bd7519110066bc75191100663c7519110066bf7319110004bf7319110006be7319110006bd7319110004bd731
  | 9 => 0x67188210005f57188210007e42188210005f576c4210006f576c42100077654c42102af7454c42102a6f763c42102a6f563c42102a77753c42102a77553c42102a7b743c42102a7b543c4210005f672c4210005f472c4210005f976c4210006f976c42100077a54c42102af7854c42102a77b53c42102a77953c42102a7bb43c42102a7b943c42100457e76d95100467e76d95100147e76d95100057e74d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100073f43d95100073d43d95100077631d95100077531d95100067f74d95100067e74d95100647e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100063f43d95100067e43d95100067d43d95100063d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95100467e71d95100467d71d95100467c71d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d95100467e70d95100467d70d95100467c70d95100067f30d95100067e30d95100067d30d95100067c30d95100467d10d95100457e75d91100057d75d91100067f65d91100067c65d91100073c54d9110006dc63d9110004ff75d9110014fe75d91100067e75d91100147e75d9110004fd75d91100067d75d91100047d75d9110014fc75d9110006bf54d9110006be54d9110006bd54d91100067c54d9110006bc54d91100063c54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d9110004fe72d9110004fd72d91100073e75d91100073d75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110005bf73d9110005bd73d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110007b631d9110007b531d9110006bf75d9110006be75d91100063e75d9110006bd75d91100063d75d9110006bc75d9110006bf73d9110004bf73d9110006be73d9110006bd73d9110004bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110
  | 10 => 0x8a10006ef6298a10004ff7598a10014fe7598a10004fd7598a10014fc7598a10064fe7498a10004fd7498a100067e5498a100067c5498a10004ff7398a1000cfe7398a10004fd7398a1000cfc7398a100067f5398a100067d5398a10006bf4398a10006bd4398a10006ee5298a10006ed5298a10006ee3298a10006ed3298a100057f7558a1004d7c7558a10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7458a10064fc7458a100067e5458a100067c5458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a100067f5358a100067d5358a10006bf4358a10006bd4358a10006ef7258a10006ee5258a10006ed5258a10006ee3258a10006ed3258a1004d7e7518a100057d7518a10006ed6218a10064ff76d0a10004fe76d0a10004fd76d0a10064fc76d0a10006ee62d0a10006ed62d0a10005f671d0a10005f571d0a10004ff7690a10004fe7690a10004fd7690a1004d7e7590a100057d7590a10004ff7650a10004fe7650a10004fd7650a10004fc7650a100057f7550a1004d7c7550a10005f77150a10005f47150a10064ff7610a10004fe7610a10004fd7610a10006ee6210a10006ed6210a10066be64d0610006bd64d0610005fa70d0610005f970d061004d7e75906100057d7590610006bf6490610006bc64906100057f755061004d7c7550610006be6450610006bd6450610005ef7250610005ec7250610005fb7050610005f87050610006bf6410610066bc641061004d7e75c86100057d75c8610006ee62c8610006ed62c8610005fa70c8610005f970c86102cf7675c86100077575c86102cef765c86102cef565c8610006f664c8610006f464c86100077654c86102cf7454c86101d6f763c86101d6f563c86101d77753c86101d77553c86101d7b743c86101d7b543c8610007e662c8610006f562c8610007e562c8610007f270c8610005f570c8610007f170c861004d7e75886100057d7588610006ef6288610006ee6248610006ed6248610005fb7048610005f87048610007e52108610005f57608610006f576086102c6f765086102c6f56508610006f66408610006f464086100077654086102c77454086101aef763086101aef563086101af7753086101af7553086101afb743086101afb54308610007e67208610006f76208610007e76208610006e76208610006f56208610007e462086102c7e652086102c7e55208610007e74208610007e442086101afe632086101afe53208610005f5700861004d7e75902100057d7590210006be6490210006bd64902102bf3c5490210005f67190210005f571902100057f755021004d7c7550210066be6410210006bd64102102b73c5410210005f67110210005f57110210005f
  | 11 => 0x6be6490710006bd6490710005fa7090710005f970907100057f75507100557c7550710005ef7250710005ec7250710066be6410710006bd6410710007b54110710005fa7010710005f970107100557e75c87100057d75c87100557e75887100057d7588710006ee6288710006ed6288710005fa7088710005f97088710006ee6208710006ed6208710007e52108710005fa7008710005f97008710066be64d0310006bd64d0310005f671d0310005f571d03100557e75903100057d7590310006bf6490310006bc64903102ef3c54903100057f75503100557c7550310006be6450310006bd6450310005f77150310005f47150310006bf6410310066bc64103102e73c5410310005f671c8310005f571c831004d7e75d92100057d75d9210005ee72d9210005ed72d9210004ff75d9210014fe75d92100067e75d92100147e75d9210004fd75d92100067d75d92100047d75d9210014fc75d92100067c54d9210004ff73d921000cfe73d9210004fd73d921000cfc73d92100067f53d92100067d53d9210006bf43d9210006bd43d9210004fe72d9210006ee72d9210004ee72d9210004fd72d9210006ed72d9210004ed72d9210006f571d9210006fa70d9210004fd7699210006bf6499210064ff7599210014fe7599210004fd7599210064fc75992100667c5499210064ff739921000cfe7399210004fd739921000cfc73992100067f53992100067d5399210066bf4399210006bd4399210004fe7299210004fd72992100057f755921004d7c7559210004ff75592100067f75592100047f7559210014fe7559210004fd7559210014fc75592100067c75592100147c7559210006bf74592100067c5459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210006bf4359210006bd4359210004ff7259210004fc7259210006bd6419210064ff7519210014fe7519210004fd7519210064fc7519210064fe7419210066be74192100667c5419210064ff731921000cfe7319210004fd731921000cfc73192100067f53192100067d5319210066bf4319210006bd4319210004fe7219210004fd7219210066f57119210066fa70192100667f76952100067e76952100067d76952100667c769521004d7e749521004f3e74952100067f64952100667e64952100067d64952100667c64952102dd7f73952102dd7d73952102d67f63952101167e63952102d67d63952101167c63952102d73f43952102d73d43952100467d61952100267e6095210004ff75d8a10014fe75d8a10004fd75d8a10014fc75d8a10064fe74d8a10004fd74d8a100067e54d8a100067c54d8a10004ff73d8a1000cfe73d8a10004fd73d8a1000cfc73d8a100067f53d8a100067d53d8a10006bf43d8a10006bd43d8a10006fa70d
  | 12 => 0xe7399310004fd739931000cfc73993100067f53993100067d5399310066bf4399310006bd4399310004fe7299310004fd72993100057f75593100557c75593100073c5459310004ff75593100067f75593100047f7559310014fe7559310004fd7559310014fc75593100067c75593100147c7559310006bf7459310006bf54593100067c5459310006bc54593100063c5459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d5359310006bf4359310006bd4359310004ff7259310004fc7259310006bd6419310064ff7519310014fe7519310004fd7519310064fc7519310064fe7419310066be74193100667c5419310064ff731931000cfe7319310004fd731931000cfc73193100067f53193100067d5319310066bf4319310006bd4319310004fe7219310004fd7219310066f67119310066f970193100667f76953100067e76953100067d76953100667c76953100557e74953100573e74953100067f64953100667e64953100067d64953100667c64953102fd7f73953102fd7d73953102f67f63953101167e63953102f67d63953101167c63953102f73f43953102f73d43953102f77631953102f77531953100557e75d8b100057d75d8b10005be74d8b10005bd74d8b10035de73d8b10005dd73d8b100557e7598b100057d7598b10006ef6298b10004ff7598b10014fe7598b100067e7598b100147e7598b10004fd7598b100067d7598b100047d7598b10014fc7598b10064fe7498b10004fd7498b100067e5498b100067c5498b10004ff7398b1000cfe7398b10004fd7398b1000cfc7398b100067f5398b100067d5398b10006bf4398b10006bd4398b10006f63198b10006f53198b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b10064fc7458b100067e5458b100067c5458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10006bf4358b10006bd4358b10006ed6218b10004ff7518b10014fe7518b10004fd7518b10014fc7518b10064fe7418b10004fd7418b100067e5418b100067c5418b10004ff7318b1000cfe7318b10004fd7318b1000cfc7318b100067f5318b100067d5318b10006bf4318b10006bd4318b10006f67118b10006f63118b10006f53118b10006f97018b10064ff76d0b10004fe76d0b10004fd76d0b10004ff7690b10004fe7690b10004fd7690b10004fc7690b100557e7590b100057d7590b10006be6490b10006bd6490b10004ff7650b10004fd7650b10004fc7650b100057f7550b100557c7550b10005f77150b10005f47150b10064ff7610b10004fe7610b10004fd7610b10064fc7610b10066be6410b10006bd6410b10005f67110b10005f57110b100557e75907100057d7590710
  | 13 => 0x4400073d759044006dbc759044036dbf739044036dbd739044038ebf639044038ebd639044038f3f539044038f3d5390440005be7290440065be7190440006bd6190440005bd7090440386be6090440004ff76504400057f755044006d7c75504400673c5450440005ef7250440005ec725044006dbe7510440065bc7510440065bf731044037dbd7310440066bf6310440376bd63104403773f53104403773d5310440005be721044036dbe7110440067b67110440067b66110440006bd6110440067b56110440006b56110440067ba7010440005bd7010440067b97010440366be6010440004ff7688440064fe7688440004fd768844006d7e75884400057d7588440065be7488440005bd748844035f3c5488440007ac4288440006f66188440006f56188440004ff7648440004fd7648440064fc7648440005bf7448440065bc74484403573c5448440006f66148440006f56148440004ff7608440064fe7608440004fd7608440005bf7408440065bc740844034f3c5408440007b44108440007e5210844006dbe75d0040065bc75d0040065bf73d0040345bd73d0040066bf63d004033ebd63d004033f3f53d004033f3d53d0040005be71d004006d7e75900400057d759004031dbd7490040336be64900400673c549004032f7a7590040007797590040065f97490040066fa6490040067ba649004032fbb54900400677a5490040067785490040067b854900400673854900403277b5390040327795390040067bb4390040327b94390040007ba4190040067b84190040004ff76500400057f755004006d7c75500400673e54500400673c5450040005bf7650040006bf7650040004bf76500400073f755004006dbe755004006dbc755004030f3c755004006d3c755004031dbf735004031dbd7350040306bf6350040306bd63500403073f53500403073d5350040005bc7150040065bf7050040316be605004030fba505004030fb95050040065fb7650040006fb7650040004fb76500400077b755004030f787550040065fb7450040007bb7450040066fa6450040067ba64500400677a5450040067ba54500400673a545004030fb954500400677854500403077b53500403077953500400557e75d93100057d75d9310004ff75d9310014fe75d93100067e75d93100147e75d9310004fd75d93100067d75d93100047d75d9310014fc75d93100067c54d9310004ff73d931000cfe73d9310004fd73d931000cfc73d93100067f53d93100067d53d9310006bf43d9310006bd43d9310004fe72d9310004fd72d9310006f671d9310006f970d9310004fd7699310006bf64993100073c5499310064ff7599310014fe7599310004fd7599310064fc7599310006bf54993100667c5499310066bc54993100663c5499310064ff739931000cf
  | 14 => 0x67f65185400067c6518540006f56118540004ff7518540014fe7518540004fd7518540014fc75185400067e54185400067c5418540004ff731854000cfe7318540004fd731854000cfc73185400067f53185400067d5318540006bf4318540006bd4318540004fe7218540004fd7218540006f73118540006f43118540004fe76d05400067f65d054010e7c65d054008d7e75905400057d75905400067f65905401067c6590540006f76190540006f46190540005fa7090540005f970905400057f755054008d7c75505400067f65505400fe7c6550540005ef7250540005ec7250540006f76150540006f46150540005fb7050540005f87050540004fe76105400067f65105400de7c6510540007b54110540004fe7688540004fd7688540004fc768854008d7e75885400057d75885400067f65885400ce7c6588540006ef6288540006ec6288540004ff7648540004fe7648540004fc76485400067f65485400c67c6548540004fe7608540004fd7608540004fc76085400067f65085400ae7c6508540005be7408540005bd7408540006f76108540006f46108540007e521085400067f65d014009e7c65d01400077b65d01403b77865d01400677a54d01400677854d01403af7b53d01403af7953d0140067bb43d01403afb943d014008d7e75901400057d75901400067f65901400967c65901400073e54901403a73c54901403a73e75901400073d75901400073f6590140096be6590140096bc65901403a73c65901400963c6590140315bf7390140315bd739014039ebf639014039ebd639014039f3f539014039f3d5390140006bc6190140007bb60901400673c5498440066f76198440004ff7598440014fe7598440004fd7598440014fc75984400667e54984400667c5498440004ff739844000cfe7398440004fd739844000cfc73984400067f53984400067d5398440006bf4398440006bd4398440004fe7298440004fd7298440006f65198440006f55198440066f74198440066f44198440006f63198440006f531984400057f755844006d7c75584400673c5458440005ef7258440005ec7258440066f46158440004ff75584400067f75584400047f7558440014fe7558440004fd7558440014fc75584400067c75584400147c75584400667e54584400667c5458440004ff735844000cfe7358440004fd735844000cfc73584400067f53584400067d5358440006bf4358440006bd4358440004ff7258440006ef7258440004ef7258440004fc7258440006ec7258440004ec7258440006f65158440006f55158440066f74158440066f44158440006f63158440006f53158440004fd769044006d7e75904400057d75904400673e54904400673c5490440005bd7690440006bd769044006dbe75904403973e759044006d3e759
  | 15 => 0xc75106403ff3e65106400073d65106403f5bf73106403f5bd7310640366bf6310640366bd63106403673f53106403673d5310640005be7210640007b67110640006bd6110640005bd7010640004ff7688640004fe7688640004fd76886400957e75886400057d75886400ce7e65886400067d6588640005be7488640005bd74886403ef3c5488640006ee6288640006ed6288640007ac4288640004ff7648640004fd7648640004fc76486400c67e65486400067d6548640005bf7448640005bc74486403e73c5448640004ff7608640004fe7608640004fd76086400ae7e65086400067d6508640005bf7408640005bc74086403df3c5408640006f66108640006f56108640007b44108640007e5210864009e7e65d02400067d65d02400673e54d02400673c54d0240005bd76d0240006bd76d0240095be75d0240095bc75d02403d73e65d02400073d65d0240335bf73d0240335bd73d02403cebf63d02403cebd63d02403cf3f53d02403cf3d53d0240005be71d02403d7ba50d02403d7b950d0240005f976d0240066f976d02403d77a65d02400077965d02400677a54d0240067ba54d02400673a54d02403d7b954d02400677854d02403cf7b53d02403cf7953d024008d7e76d954008e7e76d95400147e76d95400657c74d95400057f73d95400057d73d95400067f63d95400067e63d95400067d63d95400067c63d95400073f43d95400073d43d95400067f74d954008e7e74d95400647e74d954008e7d74d954008e7c74d95400647c74d95400067f73d95400047f73d95400067e73d95400067d73d95400047d73d95400067c73d95400067f43d95400063f43d95400067e43d95400067d43d95400063d43d95400067c43d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067e31d95400067d31d95400067c31d95400067f70d954008e7e70d954008e7d70d954008e7c70d954008e7d40d95400067f30d95400067e30d95400067d30d95400067c30d95400057e76951400667e76951400947e76951400657e74951400673e74951400667f64951400657f73951403c57d73951403be7f63951401167e63951403be7d63951401167c63951400673f43951403bf3d43951400667f60951400067f65d85400067c65d8540004ff75d8540014fe75d8540004fd75d8540014fc75d85400067e54d85400067c54d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540006bf43d8540006bd43d8540004fe72d8540004fd72d8540006f731d8540006f431d854008d7e75985400057d75985400067f65985400067c6598540006f761985400057f755854008d7c75585400067f65585400067c6558540005df7358540085dc7358540005ef7258540005ec7258540
  | 16 => 0x87400957f76596400967f76596400147f76596400973f74596400973c74596400057f73596400057d73596400067f63596400067e63596400067d63596400067c63596400073f43596400073d43596400967f74596400963f74596400967e74596400067d74596400967c74596400963c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596400067f43596400063f43596400067e43596400067d43596400063d43596400067c43596400067f71596400067e71596400067d71596400067c71596400067f31596400067e31596400067d31596400067c31596400967f70596400067e70596400967d70596400967c70596400967e40596400067f30596400067e30596400067d30596400067c30596400057d76952400667d769524008c7d76952400657e74952400673e74952400953e74952400657f73952404257d739524041e7f63952401167e639524041e7d63952401167c63952400673f439524041f3d43952400667e60952400957e75d86400057d75d86400067e65d86400067d65d86400073c54d8640005ee72d8640005ed72d86400067e65986400067d65986400073c5498640006f76198640004ff7598640014fe7598640004fd7598640014fc75986400067e54986400067c5498640004ff739864000cfe7398640004fd739864000cfc73986400067f53986400067d5398640006bf4398640006bd4398640004fe7298640004fd7298640006f63198640006f531986400067e65586400067d65586400073c5458640004ff7558640014fe7558640004fd7558640014fc75586400067e54586400067c5458640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640006bf4358640006bd4358640004ff7258640004fc7258640006f63158640006f531586400957e75186400057d75186400067e65186400067d65186400073c5418640006f5611864010e7e65d06400067d65d06400673c54d06400957e75906400057d75906401067e65906400067d65906400073e54906404173c5490640006f66190640006f56190640005fa7090640005f97090640095be75906404173e75906400953e75906400073d7590640095bc75906404173e65906400073d659064040dbf739064040dbd7390640386bf6390640386bd63906403873f53906403873d5390640005be7290640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b970906400057f75506400957c75506400fe7e65506400067d65506404073c5450640005ef7250640005ec7250640006f66150640006f56150640005fb7050640005f870506400de7e65106400067d65106400673e54106400673c5410640005bd7610640006bd7610640095be7510640095b
  | 17 => 0x43de7734842142fe6734842143fe5734842143de5734842142fe4734842142fe7634842142fe6634842142fe5634842142fe4634842142fe7534842142f67534842142fe6534842142fe5534842142f65534842142fe4534842142fe7434842142fa7434842142fe6434842142fe5434842142fa5434842142fe44348421007e77048421007e67048421007e57048421007e47048421005e47048421437e75048421437e65048421437e55048421437e4504842142fe7304842142fe6304842142fe5304842142fe43048421007e521d8021007e52198021006fb6098021004ff7598021014fe7598021004fd7598021014fc7598021064fe7498021004fd74980210067e54980210067c5498021004ff739802100cfe7398021004fd739802100cfc73980210067f53980210067d5398021006bf4398021006bd4398021006fa3098021006f930980210057f75580210ad7c7558021005bf7458021005bc7458021005df73580210a5dc7358021007e52158021004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff7458021006bf7458021004bf7458021064fc7458021006bc7458021004bc74580210067e54580210067c5458021004ff7358021006df7358021004df735802100cfe7358021004fd735802100cfc7358021006dc735802100cdc73580210067f53580210067d5358021006bf4358021006bd4358021006f63158021006f53158021006fa3058021006f930580210ad7e75180210057d7518021005be7418021005bd74180210a5de7318021005dd7318021007e52118021006f9601802109d7e75987400057d7598740066f76198740004ff7598740014fe75987400067e75987400147e7598740004fd75987400067d75987400047d7598740014fc75987400667e54987400667c5498740004ff739874000cfe7398740004fd739874000cfc73987400067f53987400067d5398740006bf4398740006bd4398740004fe7298740004fd7298740066f74198740066f44198740066f46158740004ff7558740014fe7558740004fd7558740014fc75587400667e54587400667c5458740004ff735874000cfe7358740004fd735874000cfc73587400067f53587400067d5358740006bf4358740006bd4358740004ff7258740004fc7258740066f74158740066f4415874009d7e75907400057d75907400057f755074009d7c7550740005ef7250740005ec7250740067b44150740004ff7688740064fe7688740004fd768874009d7e75887400057d7588740006ee6288740006ed6288740004ff7648740004fd7648740064fc7648740004ff7608740064fe7608740004fd7608740065be7408740005bd7408740006f66108740006f56108740007e5210
  | 18 => 0xe61950214d77631950214d7753195021004fd76d0421005f576d0421006f576d04214cdf775d04214cdf575d0421006f764d0421006f564d04214877654d04214877454d04214a5f773d04214a5f573d04214b77753d04214b77553d04214b7b743d04214b7b543d0421487e772d0421005f572d0421487e472d04214c6f662d04214bfe652d04214bfe552d0421487e742d04214b7e632d04214b7e532d0421005f670d0421004ff7690421004fd76904210ad7e75904210057d7590421006be6490421006bd6490421005ee7290421005ed729042149df67190421004ff76504210057f75504210ad7c7550421005ef7250421064ff7610421004fe7610421004fd7610421064fc7610421066be6410421006bd6410421005ee7210421005ed7210421007b54110421005f57610421006f57610421004f576104214adf775104214adf575104214a5f67410421007b67410421006f76410421007b66410421006f56410421007b5641042148776541042148774541042149df7731042149df5731042147f77531042147f75531042147fb7431042147fb54310421007e67210421005f57210421007e57210421005e57210421496f6621042148fe6521042148fe55210421487e74210421487e4421042147fe6321042147fe53210421005f670104210ad7e75884210057d7588421475f77588421467767588421475f57588421007757588421005757588421005f67488421005f47488421007765488421467745488421455f77388421455f5738842145f77538842145f75538842145fb7438842145fb5438842143df5728842143de5728842146ef66288421007e66288421467e65288421467e55288421007e74288421007e4428842145fe6328842145fe53288421005f67088421004ff7648421005f77648421006f77648421004f77648421445f77548421445f57548421005f67448421005f4744842100776544842143774544842143df7734842143df5734842142f77534842142f75534842142fb7434842142fb54348421455f7724842144ef66248421007e66248421437e75248421437e65248421437e55248421437e45248421007e74248421007e64248421007e54248421007e4424842142fe7324842142fe6324842142fe5324842142fe43248421005f47048421007e77648421005e77648421006e77648421447e77548421445e77548421437e67548421447e57548421445e57548421437e47548421437e76548421437e66548421437e56548421437e46548421007e77448421007e67448421005e67448421007e57448421007e47448421005e47448421007e76448421007e66448421007e56448421007e46448421437e75448421437e65448421007665448421437e55448421437e4544842143764544842143fe77348421
  | 19 => 0x85214eeed6588521006ee6488521006ec64885210076e54885214ef6c54885214e6ef63885214e6ed63885214e76f53885214e76d53885214e7af43885214e7ad4388521007e76188521004ff75d8121014fe75d8121004fd75d8121014fc75d8121064fe74d8121004fd74d81210067e54d81210067c54d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006bf43d8121006bd43d8121006fb60981210057f75581210c57c7558121005bf7458121005bc7458121005df73581210bddc73581210c57e75181210057d7518121006f96018121004ff7518121014fe75181210067e75181210147e7518121004fd75181210067d75181210047d7518121014fc7518121064fe7418121004fd74181210067e54181210067c5418121004ff731812100cfe7318121004fd731812100cfc73181210067f53181210067d5318121006bf4318121006bd4318121006ee21181210ad7e75d90210057d75d9021004ff75d9021014fe75d90210067e75d90210147e75d9021004fd75d90210067d75d90210047d75d9021014fc75d90210067c54d9021004ff73d902100cfe73d9021004fd73d902100cfc73d90210067f53d90210067d53d9021006bf43d9021006bd43d9021004fe71d9021006f671d9021004fe70d9021004fd70d9021004fd7699021006bf64990210073c5499021064ff7599021014fe7599021004fd7599021064fc7599021006bf54990210667c5499021066bc54990210663c5499021064ff739902100cfe7399021004fd739902100cfc73990210067f53990210067d5399021066bf4399021006bd4399021004fe7099021004fd70990210057f75590210ad7c75590210073c5459021004ff75590210067f75590210047f7559021014fe7559021004fd7559021014fc75590210067c75590210147c7559021006bf7459021006bf54590210067c5459021006bc54590210063c5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021006bf4359021006bd4359021006f47159021004ff7059021004fc7059021006bd6419021064ff7519021014fe7519021004fd7519021064fc7519021064fe7419021066be74190210667c5419021064ff731902100cfe7319021004fd731902100cfc73190210067f53190210067d5319021066bf4319021006bd4319021004fe7119021066f67119021004fe7019021004fd70190210667f76950210067e76950210067d76950210667c76950210ad7e74950210af3e74950210067f64950210667e64950210067d64950210667c64950214dd7f73950214dd7d73950214d67f63950211167e63950214d67d63950211167c63950214d73f43950214d73d43950214877771950214877471950210ce7
  | 20 => 0x14fc7598221064fe7498221004fd74982210067e54982210067c5498221004ff739822100cfe7398221004fd739822100cfc73982210067f53982210067d5398221006bf4398221006bd4398221006f721982210067e65582210067d6558221004ff7558221014fe7558221004fd7558221014fc7558221004ff7458221064fc74582210067e54582210067c5458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221006bf4358221006bd4358221006ee3258221006ed32582210cd7e75182210057d75182210067e65182210067d6518221006f960182210c57e75d91210057d75d91210073c54d9121004ff75d9121014fe75d91210067e75d91210147e75d9121004fd75d91210067d75d91210047d75d9121014fc75d9121006bf54d91210067c54d9121006bc54d91210063c54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d9121006bf43d9121006bd43d9121004fe70d9121004fd70d9121006bf6499121064ff7599121014fe7599121004fd7599121064fc7599121064fe74991210667c5499121064ff739912100cfe7399121004fd739912100cfc73991210067f53991210067d5399121066bf4399121006bd4399121004fd7199121066f57199121004fe7099121004fd70991210057f75591210c57c7559121004ff75591210067f75591210047f7559121014fe7559121004fd7559121014fc75591210067c75591210147c7559121006bf74591210067c5459121004ff735912100cfe7359121004fd735912100cfc73591210067f53591210067d5359121006bf4359121006bd4359121004ff7159121006f77159121004f77159121004ff7059121004fc7059121004fe7619121006bd64191210073c5419121064ff7519121014fe7519121004fd7519121064fc7519121066be7419121006bf54191210667c5419121066bc54191210663c5419121064ff731912100cfe7319121004fd731912100cfc73191210067f53191210067d5319121066bf4319121006bd4319121004fe7019121004fd70191210667f76951210067e76951210067d76951210667c76951210c57e74951210c73e74951210067f64951210667e64951210067d64951210667c64951214fd7f73951214fd7d73951214f67f63951211167e63951214f67d63951211167c63951214f73f43951214f73d4395121004fe76d0521006bf64d0521066bc64d0521005ee72d0521005ed72d0521004fe76905210c57e75905210057d7590521064ff7650521004fd7650521004fc76505210057f75505210c57c7550521006bf6450521006bc6450521005ef7250521005ec7250521004fe76105210c57e75885210057d75885214ef6e75885210076d75885214eeef658
  | 21 => 0xe75192210147e7519221004fd75192210667d75192210047d7519221064fc7519221064fe7419221066be74192210667c5419221064ff731922100cfe7319221066de731922100cde7319221004fd7319221066dd7319221004dd731922100cfc73192210067f53192210067d5319221066bf4319221006bd4319221066ed7219221066f67119221004fe7019221004fd70192210057f76952210667f76952210647f76952210067e76952210057d76952210067d76952210047d76952210667c76952210cd7e74952210cf3e74952210067f64952210667e64952210067d64952210667c64952215657f73952215657d739522155e7f63952211167e639522155e7d63952211167c639522155f3f439522155f3d43952215276f72952215276c72952210c67d629522155f6e329522155f6d32952210ae7e619522120e7e65d0a210067d65d0a21066be64d0a21006bd64d0a21005f671d0a21005f571d0a21006ed76d0a21555ef75d0a21555ed75d0a2154f6e65d0a210076d65d0a21006ef64d0a21007ae64d0a21006ed64d0a21007ad64d0a215276e54d0a215276c54d0a21545ef73d0a21545ed73d0a2153f6f53d0a2153f6d53d0a2153faf43d0a2153fad43d0a21007e671d0a21005ed71d0a21007e571d0a21005ee70d0a210cd7e7590a210057d7590a212067e6590a210067d6590a210057f7550a210cd7c7550a211fe7e6550a210067d6550a21006be6450a21006bd6450a21005f77150a21005f47150a211f67e6510a210067d6510a21007ad4210a21005ed7610a21006ed7610a21535ef7510a21535ed7510a2152f6e6510a210076d6510a21007ae7410a21006ef6410a21006ed6410a215276e5410a215276c5410a2151def7310a2151ded7310a215176f5310a215176d5310a21517af4310a21517ad4310a21005ed7110a21005ee7010a2110e7e65d06210067d65d06210cd7e75906210057d75906211067e65906210067d6590621006be6490621006bd6490621005ee7290621005ed72906210057f75506210cd7c75506210fe7e65506210067d6550621005ef7250621005ec72506210de7e65106210067d6510621066be6410621006bd6410621005ee7210621005ed72106211ee7e65c86210067d65c8621005f576c8621006f576c862150f7675c86210077575c862150ef765c862150f7665c862150ef565c86210077565c86210067565c8621006f664c8621006f464c86210077654c862150f7454c8621506f763c8621506f563c86215077753c86215077553c8621507b743c8621507b543c86210cd7e75d82210057d75d82210067e65d82210067d65d8221005be74d8221005bd74d82210b5de73d8221005dd73d82210067e65982210067d6598221006fb6098221004ff7598221014fe7598221004fd7598221
  | 22 => 0x8041006bd4398041004fe7298041004fd7298041066fb4098041066f840980410057f75580410dd7c7558041066f86058041004ff75580410067f75580410047f7558041014fe7558041004fd7558041014fc75580410067c75580410147c75580410667e54580410667c5458041004ff735804100cfe7358041004fd735804100cfc73580410067f53580410067d5358041006bf4358041006bd4358041004ff7258041004fc7258041066fb4058041066f840580410cd7f76596210ce7f76596210147f76596210057c74596210057f73596210057d73596210067f63596210067e63596210067d63596210067c63596210073f43596210073d43596210cf6e72596210076d72596210076e32596210076d32596210067f74596210067e74596210067d74596210067c74596210647c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210063f43596210067e43596210067d43596210063d43596210067c43596210ce7f72596210ce7e72596210067d72596210ce7c72596210067f32596210067e32596210067d32596210067c32596210ce7f71596210067e71596210ce7d71596210ce7c71596210067f31596210067e31596210067d31596210067c31596210ce7e21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596210cd7e75d92210057d75d92210067e65d92210067d65d9221004ff75d9221014fe75d92210067e75d92210147e75d9221004fd75d92210067d75d92210047d75d9221014fc75d92210067c54d9221004ff73d922100cfe73d9221004fd73d922100cfc73d92210067f53d92210067d53d9221006bf43d9221006bd43d9221006ed72d9221006f671d9221004fe70d9221004fd70d9221004fd76992210cd7c75992210067e65992210067d6599221006bf6499221064ff75992210667f7599221014fe7599221004fd7599221064fc75992210667c75992210647c75992210667c5499221064ff739922100cfe7399221004fd739922100cfc73992210067f53992210067d5399221066bf4399221006bd4399221004fe7099221004fd70992210057f75592210cd7c75592210067e65592210067d6559221004ff75592210067f75592210047f7559221014fe7559221004fd7559221014fc75592210067c75592210147c7559221006bf74592210067c5459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d5359221006bf4359221006bd4359221006ef7259221004ff7059221004fc70592210cd7e75192210057d75192210067e65192210067d6519221006bd64192210b5de7319221005dd7319221064ff7519221014fe75192210667
  | 23 => 0x5df73581410f5dc7358141005ef7258141005ec7258141006ef6258141006ec62581410067f65181410067c6518141006ef6218141006ec6218141006f96018141004ff7518141014fe7518141004fd7518141014fc75181410067e54181410067c5418141004ff731814100cfe7318141004fd731814100cfc73181410067f53181410067d5318141006bf4318141006bd4318141004fe7218141004fd7218141006be4118141006fb3018141006f830181410dd7e75988410057d7598841066ef6298841004ff7598841014fe75988410067e75988410147e7598841004fd75988410067d75988410047d7598841014fc75988410667e54988410667c5498841004ff739884100cfe7398841004fd739884100cfc73988410067f53988410067d5398841006bf4398841006bd4398841066ef4298841066ec4298841004fe7098841004fd7098841066ec6258841004ff7558841014fe7558841004fd7558841014fc75588410667e54588410667c5458841004ff735884100cfe7358841004fd735884100cfc73588410067f53588410067d5358841006bf4358841006bd4358841066ef4258841066ec4258841006f47158841004ff7058841004fc7058841004fd76908410dd7e75908410057d75908410673c5490841004ff76508410057f75508410dd7c7550841005f77150841065bf73d04415adbd73d0441066bf63d04415a6bd63d04415a73f53d04415a73d53d0441005be70d04410dd7e75904410057d7590441585bd749044159ebe6490441597767590441007757590441065f57490441066f66490441067b6649044106776549044106774549044158f77539044158f755390441067b7439044158fb54390441005f67290441004ff76504410057f75504410dd7c75504410673e54504410673c5450441005ef7250441005ec7250441005bf7650441006bf7650441004bf76504410073f75504415773c7550441585bf7350441585bd735044156ebf635044156ebd635044156f3f535044156f3d5350441007af7250441007ac7250441065bf715044157ebe6150441577b65150441577b5515044156fb7315044156fb43150441005bc7050441065f77650441006f77650441004f77650441007777550441577747550441065f77450441007b77450441066f66450441067b66450441067765450441067b65450441067365450441577b5545044106774545044156f77535044156f75535044156fb64350441067b44350441007e77250441005f47250441007e47250441005e47250441007b64250441067b44250441066fb6098041004ff7598041014fe7598041004fd7598041014fc75980410667e54980410667c5498041004ff739804100cfe7398041004fd739804100cfc73980410067f53980410067d5398041006bf439
  | 24 => 0xd5318941006bf4318941006bd4318941006ef5218941006ee5218941006ed5218941006ec5218941006ef3218941006ee3218941006ed3218941006ec3218941004fe7018941004fd7018941005ee7618941006ee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c65189410076e54189410076c5418941006ef6318941006ee6318941006ed6318941006ec63189410076f53189410076d5318941007af4318941007ad4318941006ef7518941006ee7518941006ed7518941006ec7518941006ef7418941006ef5418941006ee54189410066e5418941006ed5418941006ec54189410066c5418941006ef7318941006ee7318941006ed7318941006ec7318941006ef53189410066f5318941006ee5318941006ed53189410066d5318941006ec5318941006ef4318941006af4318941006ee4318941006ed4318941006ad4318941006ec4318941006ef7118941006ef5118941006ee5118941006ed5118941006ec5118941006ed4118941006ef3118941006ee3118941006ed3118941006ec3118941006ef7018941006ee7018941006ed7018941006ec7018941006ef5018941006ee5018941006ed5018941006ec5018941006ef3018941006ee3018941006ed3018941006ec30189410067f65d094120e7c65d09410673c54d0941006ec62d09410fd7e75909410057d75909410067f65909412067c6590941006ef6290941006ec6290941005f67190941005f571909410067f65509411fe7c65509415d73c5450941005f77150941005f471509410067f65d054110e7c65d0541006ef62d0541006ec62d05410077765d05415cf7465d05410677654d05410677454d05415c77753d05415c77553d0541067b743d05415c7b543d0541007e762d0541006f462d0541007e462d0541006e462d05410fd7e75905410057d75905410067f65905411067c65905410073e54905415bf3c5490541006ef6290541006ec62905415bf3e75905410073d75905410073f65905415bf3c659054157dbf739054157dbd73905415b6bf63905415b6bd63905415b73f53905415b73d5390541007af6290541007ac6290541007b761905410067f65d81410067c65d8141006ef62d8141006ec62d8141004ff75d8141014fe75d8141004fd75d8141014fc75d81410067e54d81410067c54d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d8141006bf43d8141006bd43d8141004fe72d8141004fd72d8141006fb30d8141006f830d81410fd7e75981410057d75981410067f65981410067c6598141005ee7298141005ed7298141006ef6298141006ec6298141006fb60981410057f75581410fd7c75581410067f65581410067c6558141
  | 25 => 0x95410fe7d74d95410fe7c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d95410067f43d95410063f43d95410067e43d95410067d43d95410063d43d95410067c43d95410067f72d95410067e72d95410067d72d95410067c72d95410067f32d95410067e32d95410067d32d95410067c32d95410067f71d95410fe7e71d95410fe7d71d95410fe7c71d95410fe7d41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f70d95410067e70d95410067d70d95410067c70d95410067f30d95410067e30d95410067d30d95410067c30d95410057e76951410667e76951411047e76951410657e74951410673e74951410667f64951410657f73951415e57d73951415de7f63951411167e63951415de7d63951411167c63951410673f43951415df3d43951410667f61951410067f65d89410067c65d8941004ff75d8941014fe75d8941004fd75d8941014fc75d89410067e54d89410067c54d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941006bf43d8941006bd43d8941006ef52d8941006ee52d8941006ed52d8941006ec52d8941006ef32d8941006ee32d8941006ed32d8941006ec32d8941004fe70d8941004fd70d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066c65d89410076e54d89410076c54d8941006ef63d8941006ee63d8941006ed63d8941006ec63d89410076f53d89410076d53d8941007af43d8941007ad43d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941006ef74d8941006ef54d8941006ee54d89410066e54d8941006ed54d8941006ec54d89410066c54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d89410066f53d8941006ee53d8941006ed53d89410066d53d8941006ec53d8941006ef43d8941006af43d8941006ee43d8941006ed43d8941006ad43d8941006ec43d8941006ef71d8941006ed71d8941006ef51d8941006ee51d8941006ed51d8941006ec51d8941006ef31d8941006ee31d8941006ed31d8941006ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ee50d8941006ed50d8941006ec50d8941006ef30d8941006ee30d8941006ed30d8941006ec30d89410fd7e75989410057d75989410067f65989410067c6598941006ef62989410057f75589410fd7c75589410067f65589410067c65589410067f65189410067c6518941006ed6218941004ff7518941014fe7518941004fd7518941014fc75189410067e54189410067c5418941004ff731894100cfe7318941004fd731894100cfc73189410067f53189410067
  | 26 => 0x1067d71596411067c71596411067e41596410067f31596410067e31596410067d31596410067c31596410067f70596410067e70596410067d70596410067c70596410067f30596410067e30596410067d30596410067c30596410057d76952410667d76952410fc7d76952410657e74952410673e74952410657f739524160d7d73952416067f63952411167e63952416067d63952411167c63952410673f43952416073d43952410667e61952411057e75d8a410057d75d8a410067e65d8a410067d65d8a410067e6598a410067d6598a41006ef6298a41004ff7598a41014fe7598a41004fd7598a41014fc7598a410067e5498a410067c5498a41004ff7398a4100cfe7398a41004fd7398a4100cfc7398a410067f5398a410067d5398a41006bf4398a41006bd4398a41004fe7098a41004fd7098a410067e6558a410067d6558a41004ff7558a41014fe7558a41004fd7558a41014fc7558a410067e5458a410067c5458a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a41006bf4358a41006bd4358a41004ff7058a41004fc7058a411057e7518a410057d7518a410067e6518a410067d6518a41006ed6218a4120e7e65d0a410067d65d0a412067e6590a410067d6590a415ff3c5490a41005f67190a41005f57190a4110e7e65d06410067d65d06410673e54d06410673c54d0641005bd76d0641006bd76d06415f73e65d06410073d65d064159dbf73d064159dbd73d06415eebf63d06415eebd63d06415ef3f53d06415ef3d53d06415f7b651d06415f7b551d0641005be70d0641005f576d0641066f576d06415f77665d06410077565d06410677654d0641067b654d06410673654d06415f7b554d06410677454d06415ef7753d06415ef7553d0641006f662d06411057e75d82410057d75d82410067e65d82410067d65d82410067e65982410067d6598241006fb6098241004ff7598241014fe7598241004fd7598241014fc75982410067e54982410067c5498241004ff739824100cfe7398241004fd739824100cfc73982410067f53982410067d5398241006bf4398241006bd4398241004fe7298241004fd72982410067e65582410067d6558241004ff7558241014fe7558241004fd7558241014fc75582410067e54582410067c5458241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d5358241006bf4358241006bd4358241004ff7258241004fc72582411057e75182410057d75182410067e65182410067d6518241006f960182410fd7e76d95410fe7e76d95410147e76d95410657c74d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95410073f43d95410073d43d95410067f74d95410fe7e74d
  | 27 => 0xd63982540673f43982540073d43982540057e71982540057d71982540067e61982540667c61982540657e70982540667f60982540677b60982540677860982540677b40982540677840982540657f76582540657e74582540657c74582540667e64582540673e64582540057f73582541157e73582540057d73582541157c73582540667f63582540067d63582540673f43582540073d43582540057f71582540057c71582540667f61582540067d61582540657f70582540677b60582540067e60582540667c60582540677860582540667860582540677b4058254067784058254066ef6298b41004ff7598b41014fe7598b41004fd7598b41014fc7598b410667e5498b410667c5498b41004ff7398b4100cfe7398b41004fd7398b4100cfc7398b410067f5398b410067d5398b41006bf4398b41006bd4398b41006ee5298b41006ed5298b41066ef4298b41066ec4298b41006ee3298b41006ed3298b41004fe7098b41004fd7098b410057f7558b4110d7c7558b41066ec6258b41004ff7558b410067f7558b410047f7558b41014fe7558b41004fd7558b41014fc7558b410067c7558b410147c7558b410667e5458b410667c5458b41004ff7358b4100cfe7358b41004fd7358b4100cfc7358b410067f5358b410067d5358b41006bf4358b41006bd4358b41006ee5258b41006ed5258b41066ef4258b41066ec4258b41006ee3258b41006ed3258b41004ff7058b41004fc7058b4110d7e75983410057d7598341066fb6098341004ff7598341014fe75983410067e75983410147e7598341004fd75983410067d75983410047d7598341014fc75983410667e54983410667c5498341004ff739834100cfe7398341004fd739834100cfc73983410067f53983410067d5398341006bf4398341006bd4398341004fe7298341004fd7298341066fb4098341066f84098341066f86058341004ff7558341014fe7558341004fd7558341014fc75583410667e54583410667c5458341004ff735834100cfe7358341004fd735834100cfc73583410067f53583410067d5358341006bf4358341006bd4358341004ff7258341004fc7258341066fb4058341066f840583411057f76596411067f76596410147f76596410057f73596410057d73596410067f63596410067e63596410067d63596410067c63596410073f43596410073d43596411067f74596411067e74596410067d74596411067c74596410067f73596410047f73596410067e73596410067d73596410047d73596410067c73596410067f43596410063f43596410067e43596410067d43596410063d43596410067c43596410067f72596410067e72596410067d72596410067c72596410067f32596410067e32596410067d32596410067c32596411067f71596410067e7159641
  | 28 => 0x202d002000000a00201d8004000014019000800a00a000800c020001006001001e00f002803402e0000050008002001017800000600600a007c00000200200780040020018044016002000800401e0060138004006003003801000c029001800404600a005803400e00600b8024010000014801c01400a0010004074007005803c016001006800400a001000802c00000301500040120180000000008057002802c00e001002000004800800b802c01200000600200000010000008020009000803801200400d801401e04c02b803c00200b0078018002011001003c004008000804c006003004800000a00d00580140000060030010056000000801400001b00a8000002006001001c016005004000001c002006000402000d0008008000011003000c0060010000088000001000800002a00900000b40040050010040002000004002c020008001000000200100b800000c000000000000400d01980580020040090000000008000000c000000000004c05e004007000001e003003004001a00900800000080100040024014005006000c00200200a8020000004011000000c013035800011200000000080180080010004000000001004c010005002800c00800f011001401e01202c002800c00200400080000190008014014003008001000200000d000c01e00f00f805c006000001800c0380050040028004044000800400a00e004801401200100a8000004002000004000001a000800c00c00400400000000040098014014004002005001e013004000c000007007001400000f000001801800c007800000c00c00000e401200e0048108000007011003800000200700000020000657d76986540657e74986540657c74986540667e64986540673e64986540057f73986541157e73986540057d73986541157c73986540667f63986540067d63986540673f43986540073d43986540057e72986540057d72986540667f62986540657e71986540667f61986540677761986540677461986540677741986540677441986540057e70986540057d70986540667c60986540657f76586540657e74586540657c74586540667e64586540673e64586540057f73586541157e73586540057d73586541157c73586540667f63586540067d63586540673f43586540073d43586540057f72586540076f72586540056f72586540057c72586540076c72586540056c72586540067e62586540667c62586540657f71586540677761586540067e61586540667c61586540677461586540667461586540677741586540677441586540057f70586540057c70586540667f60586540657d76982540657e74982540657c74982540667e64982540673e64982540963e64982540057f73982541157e73982540057d73982541157c73982540667f63982540067
  | 29 => 0x2a004000000800000600180500000000030000000006001001001600d0010008014003001801c00400c001801000c00000280000020000048004000003003802006000600000080000000000008000004008000000000c002001803a00e000004800200400d825c0100040040018006023006000c002002002805400600000b001000600a0018004006000001003401001e001801800800b0058020010006000001c00000c021806005e001005002c00400b0008004000045006800001e01f0178000008005001800001000201100100020250000008008000000005001c005006800404a00b00c80040b2017003800c02401400b8018004001001800003400c0008030000007005800c00600c0000000000003005008c00a01b00700100440010028000006001005000000c001002002000200b001000c0340040000004000011000003c002008002000c0600020038008004011000000401400600000000040110090054000001005008c00200100180180240000020000030000000001c0000140078050014005000000001c004002002400000700300ac00a000001801000000100200040140040028000002007002801400000000000040120000018038006009005800c00000000400dc03a0030048020002001005801001a0050078000020004005809c00000200180180000010000004022013004802c02400000d824800001c0080000006000000000c012013002000c00001100480600bc003000005401e006000000c006000001800800e000001804c00600f018003c020000001003400000000000080020030000018000000000000000800300a000000a005000005c0080270108004000003001003000000b008805000402a0000054016000000008c0080050020014004004003800000c032002800800000300980080020130010040002000001000800000f005800800200700f00000000030000020092008009000000400700200fc0080000050000000004001000c002000003000000c01700c009800a0060000010006018005007c002016010800000200d003800c048004006800003400700b800400000e00280100000050000008000004000800004c0110020028000000001803000000000380240180000000000004026002804400c01b0170020010037005800000a00d0000000006005000000800800a004000c05c01200d00580040000038000014007004800400001a00280000040010018024008002000000c006005000000000a00f000000c016006008800c00000100080d801a0050028024014001000006c04600101000b004a005009000c00202f003000402a000000000000000000000340060040030040004002000007400000a03d00000060000108000018009001000805400101680b40000000000000
  | 30 => 0x80240000110004014000001800400a0010008018018000009800800001b000002002a009000000000400e000800402600100000040000050058010002000001800001000000000000240020018018010003001800000a0080000000000005001800c00000700000100000000048000000001000002000400b0058000008004001002000000c001002400201f003004000c00001900000100000018000012005001001c00000d000002c01003900c00100000010018018002002000000c00c009001002401000f022807800000f000002001a001002804c02200100a805402c0000000000022010000000c006015000004800000700000180000010000088004003000000004e00c000800002400000d8008000001008800000c00b0000024000000003006c0060010038000006009019000800200f000001801a010004000000000400e800400000001200ac008000005001c074000002800000c000002800000001d000000003c0000048014024004029002c004000005001c000001001000400600a0040004006000000000002c000003800c01c010005801c00000500080480000080008044004007000800400000b008801c0080050000008000017000002c01000c0000028008054000000c0120060068014000006000000c01600800100300040030018004000002005800801c00d00580000060020000040004000000805000c005002800401a003000800000000000680cc02200d001803c010005003000401602500b001001000000000640260050028000046007001005c000006002003c00a0010138038000002001003802000b003000000000c0020010002002001000800200300300200260000038034008006004800004e0370028090008002001002002000800080040080020108000018002004800805a005003803c002047001804000e0060018000002006001002c0000110018000010013004004800c0060020094012000009801802400100000c4000003001000c0860130008004000005007002800a004000002c00000700180c000200700300400080000030000000006001000c07e00101c80200000000100010018005001001403a00600000700f000c0018054068010004800000a001004000c0000010010090008024004001400201c0000010000001000000000600100b800c0040050050000006000004000801a00e001000402e00a000001c002004008000003800900b8050002006000005c00000c001000400600400f800c0000130040038022005011801802e0100040024000029001800403000400100bc00001c002000c004001002000009a002002001000001a000001801200c004000c00200d00080140000010050000000000001000001000800b008c00400101080080040050038008032005000800c004012
  | 31 => 0x4979e6800020c83ef0eea09300003cd800018480007e180005f3058a00000002bf8df83ec09e42a012d4153c0000000044503071c000105e0001ff861c11840000000000071600004cc347845a31d12f4842866c30020b262b18df93213726c88f5424e84f458365168490cdc4f4e3e619d05c432200000000df051da5b836c8d8e6f60d63000155f0c850ee6ef8db3728871806f904e947518c005076289203e438c80926db800008900004d9800000013f06110000111000030c00003f55552771cc4204280008ba9edc0000de793813b878884880578d5604189cc05e1ce14d000f3107900a000000040210a619580aa10b82f200022588ee8a512ae11dc66b0c9682a00008ea831c0001996000000017fdbf08438000728c518773117e49923726718b8c1500fea388800065e9b4824193922c9849a2f0057600022a88a28cd029f820a3af82427d08848125a46043f0d0638c048a6f419428fe13266a30b4c33a17e8000024638811ed94a800000023ea225a09a425800000000000001c2b1f097d8044967c000060005a8aac61521c62581eb82e6850c43e0338000000000f80705ae10a0000000000019ee0000cc878b84be1b380006aa00000002002275a548427a5502c307c66a280768f809b863483734891a1e4cf22e4690a4fe4fc50e670da093925162e2291e0e3a38a646fd1d927ad06ea00016638b31d4903656dc87f978496484020000dc6743940e4099700013a2767451d7451213fc629a0915b294ec00004d6599e23a43f875c11788fa1f80f5639887588f792b064ae34e1dd80008bd800069187667f117c60f4000000009e2000000003c1de226215a281b800095d11940000024445000007415a812d1148889169295e8eec3908cbe60799128ec1efc65191bc40311865d59d7c93a8b5080d9a0c5d4a188312800000019aa00000003d88abc00017f429180000000000604800000017c80468ed21aa1d7a6da140a4d421ee3d48000000144223618ca84b216e0001342187a1fc02b15b6000166e46f8000285800047c02960d380000d08a4a6799f407ca005600012ea00020b643b17fc2e49502510133e6cb8c542a28d4037c9246535142246b038407083cc663a4682ad9da0920a15659784dc11d20f42aa07a68df140b5ad89461fe870c7410b4a1b9d89133917080cf8020000000008c008001001000400200000200200360000018000008009000002801400f003000001e01a00b00280060050000010034000003002c0280010050030012000001802800c0000010000002000002001800800000c800400000c0038040000000006800400201d001801000400a000005800200f0070038000004005800001c00b0048000000013000800c002026007000c00000300180040040000020034012001000001801a001000001
  | 32 => 0x1c482941320227846c66e007c85f1694705a1cc30a1c10000000016c5f6475b0e662de17760808cb81f7101b48394c85c5a19e17c000000000002f51fb423c9018000018848d069256ba0f000000006b39c7a6fe01aa8eba5c28b28000000213c0001e28960242c5ef985237606b02db0000000214e0000732000087446a1dfc2f08cde4150de0838000056080008cd8d941af0532433089c60715c495a90f4863947d4e80000000000086b80004da168a8c709907dbc00094fa2a07dc095453ba4566a895246b4cfad88e08a67eb13ba81c0a9e0daa15c83304a47b9906010a05c07c2226462b87081b80a527a208708e0219038c40000905aa32a18c800000e503a094ca5068cc0000000000001d91da0d3e22d9525000000000000002f117ee53a055500022b623c168e62e21385da0fb9411061416602cb31f071425b1dac90809e879295e833989c282f1a9e3e998db0a71920000237a3c987061a9014302f08328e420be04c99fa6c7164667200681671f746259e8200015460a180000000000154d5e30000cfa000000000000008bc00008f88f7e8db1e2c19d8ba65f58000373164c73d16e63bf9a7a8d48000656843822380008c919c200000000ee98e85789a1c0000af864f000005f93d400000004d518d86bf9eb0286800284491928848f944b7000046c8e985d2c00063213de18c000004852ac0000df600017fa8b20b1a1539ef8000254c3f902b47c000006b89e6e14881449550fa091ea216737e2fe4ff80b400000004f6a43e75f8000000000067c8aca58e95309039d4c2331b8652911089358b769659c005540fd88c68130000149e7ce2090000194007c8f9600010340000e402249376034000028724c600024e40000e41000222e20ea1d2000000070e15484831f6a8510eac1f1000018f23127a915b00000000875976437d25be4e780000001e1a0000f6e90d800083f19980000000757000059b0ed60001b546dc9db47220000000007200010ac852000000000008d28f5c28e800067d00003f3c3a22a41d2e79496d613e162044a966a059932a0279c204928a5e93b21002d21c4c647644c3620cc200612be33da4c068212200001c8e4589f6e0e50f70457a4b60b58fe6622a1f07320b8a4731bfa4901ec70bfa1601d219283caa104377000000023bc41913ff69d17c496ba0b08ff235607584a82f81c50205898a062932216887cc711a2708af9dd008e07fe1b987380631a021d9000071d58f91fb824352a93a40000e2137762ac7358fba23580007799db6000018754980004aa00004802466000000000007240000ac45ca80000585951000152287d9cc4829d79a0002412228218400000002959ef604d211e000000092300000000eb60fa80000928f6800000000001fa60000000917a17876f00004e4c0000001512
  | 33 => 0x1dd471cdb7c1668000611861863dd7f800010aa06e0bce000102e000225200000007268e461010afa65a822b89820421ae19ca4b8074434511d029e07c009880000001e421709e806dd1c580001cac7f293770331ebc000224600013280558000000114404509148ac9b0e767067a0911cce0df815a57698a16fc8cf283782a62bd10366f49d8c57e860c358037668d13bb3248228000095a38b0d10426062c959a0288a21eba17e0858143a43a36be47478f230e6170baa3841a3532890a46b580000ce80005110b1c902a5858b98c8400000009040b400000ca02d81970257886e7af854628b89fc19b83be47a8c6686aa27c00000487e29c1e92616120002572308885d0a080000b0041005900005400086519014108609dc92d0d4421182d492412f0639d0e893382fc6d5a2725aa13c06ae99623458cea62a886a0d21cc649b07e223f097655849008ca8e3c7d4075e47224223951a4800006061578372000194e35e8efa0411ac42468f3080a80006d3947c5f6955c0000000489a39c000218c5621f9639b80c84368dec1e000008f4a0da3d814416f99ea04169ce378c1cfa01e800000010e4209241600000000001382644c8a200000008c899b096c179800011b478f8d502e000006d7800053725603f89a941490000000000000023843608abe000254b563887c8fd12e60000240000145e8f281b126c9f4c58f92ee00000000381e66230a5840d1987c82e946c7c48000659806a2cb133838186ca336215a0ba80006eb0000103a08408784c48c21f9a1f29dea2639efe252947865213f20408c021c3950e473800000012361868b4e06417e400000006d8122c8d79daa3fe04f26daa3a86c41c3c24a8ac213b18405e788b23f5a5aa431207e79d97aa1dc25887879c5a65f9622549c9c06b6001206f0e0a2db86a625d000070315ad615c572946ddbe8cf0fe80920fae5e51c3495e0b2a04e84c85690af7017167078295de5731e961ed1a6252d169e099867c12394e640582473681d1a720029a49ea21403d82502cf98bd61aa0680ed249e881077a75594de4090e747c392b65740e34190a2ee2b31df416f9118612c9a47199b8e1b3502200004b61ecc00058e0e4a5048000000000045300000001d060002058000000000012326ae5b7a94080000d80000583035e2d504d24e5000000018e08f5a18000024087ec9f8c1cd980a18e25060000dc06950ac871809ce3448bea4ce40000131ffa32a1324286037873994fe7cb8e0477a1a2247bc0b0870a04e3d080fa0aaa146469a1c864c83c20b1dd185cd9be447d06d00000e70597cf1e32ca1324be94265ce8000732a5215b181ee3a5221c7c08000000186673a92103be0dac89d04e086ca36e32601e250d42802851e9800022f254b8e2800022440880b0007689346a48ace210
  | 34 => 0x899a23859c960000602000000031c23ce2f683708791f7c5670cee3a0069000007604c38571050a35087980003ae80005b34a326e50ef08c622aa15e000001e05ee6eb9f3216164765660e7c085220a64d83e222e84405f780004ac987a5fc0dbe79a8e920a8802e5d8058e78d20e200007bc71d254a39107f08f920c454be55294494778590f4681da5100000982000049086f88aa00003440000d620000000884000040199787b100000002032655d9b6801000074f9749965055b0001f5a58c0de356e800000000008ad06de84500005961a5600013562c180268a781d49171dc00501abb36ea0fa71520a6269a348312257c1de12762be58da68199140228f981f383f66b4000051411222c0871d0001da4000114a0001b3c3a69c0a4db1116000225c6a9a0725598dd65db1c06047202e5289b2c2d498d46a9dd0a83b150a74a82a089aa0628c7826f3e94bf294c91e275400008d00000850800066180000000fb21aa8b7a0000ed855d8fb48a90cd279c00007fc1dec257000017200009368000000000000000809329c5202ba398638d5f881296745a5a4140ea98fe47c958654c9766303129e3c2a2303168ec44c59dce6270e188760f7253e9ba06ab99a61dd00da9371bc018b8bf85091af46bb00004c3011000000008181fd451ed08600014f246b8e1a6ad469e0002316630208097603285bc8ee47aa1c1a7ef00000b2800095590c88b518857d89c786590e860e989fa60619567da5cb61c10c20676a3ec8dd1a0e7de01922441994841a01870ea1627d8566651683b26ca196e70100008122598529938e603163c2bc108e000041423b1b061e0826e21415420f61b8c518096434b98f469b934807f000003884fc06c88dc651217a9118f641f418b493e93e20ed815c6b540d543c9ae085c971059520063c597d0540477e945221a606844e68d9a52900953c35f2186000000000000003b9df5c00014fd0001980141800091510d00001cb800000008e18e9c6ce13f69469d122030c6810b00c42322168343a1f80088c7e00000005bf068e594a00e00008ac74a517600002785b31a1602080cd3ca000060f1b4c6bd8d3417b0fa85258ec233fa0501e101fa0d61bbc4f985a8505063611a875270992e249309e603b654f77341fe6b90412048921e06620b48530eb03381042686088486b48bc000000000023da000000000024f44be0faa1b7123c93e18941ce96ce176129693d9d488261c9021980505ae978c36261261bd8e9e342a2e05be0dd583083643df00fe973056495a17b26d0037c22f8fcc000085e00013e878a93ea3d2251f81916482e9179000006ac3f7154002500005b812487df81d800004248b095e63111a3286c033093c000028893d640f059257380000000a960001a86740903e0a4800000000000000d86637800
  | 35 => 0x5619c000036d80006f7000000000002d600000001f650e900004d79f761b59b8a00002b0235d6280001cbe000143c000062500000006058000277800000019f651b800000013140001cda000147025e0000876834c20a8000507000008d873c80700ca240897a07243829700b1800007ec7480c6a4161fec5c8961639d89b055b195e80c0d394518ee2621235c7581f2c000155e83503508b4892418ca2840f288386a700e644f93e032f11680000000000195c50195ec450047a27c8d8b2b79f8848501e8000054459adbaa74c9eec1bb81f455300000000de13e0800092022de38917d46cbcc2c31899115f09ed8264800014b1ea21899360000129a78000000301dae0000fec2800fee44387da5cb1c6c4ba00001b4800041b80000479102842000000017f6000000041a04706f68c3e3ab86046de000001b136e4e11a784b9000057f9142095069600011c41061242215d21a5f9a08c9121be285b09621e782c822d04de8c298607761ade7be995213e81ca61345f4028038000007348a400000001b120b98a0c47b1504000002c0069c6e90618ba51e400064193c233f00007250b6a6ed903500000006b5c00000000000000e127b0157a69a000000018b049a256489ba4ee817888077b9c7e3f083ee36ac00005d00002a09fbe046000086b00002e51c863dd00001b54c041690d927f780001bb64bc5909ce063ec69c96917860b783f41b91e1400018cc39600845af9cdc774a48e760983a6be073e29ea23c247951a594036c88220a2000000040c814e00000006fa8fbd0000000612a3a065a1f5b0000cec0000e6a3dd9cae4de64ac03b0e3555c00f43a2150609b20f80a39b1455f103803c9484000156442a000046717dc4d39e32901843e54ee22c04d8d30807800000008da1c99d6e14a000000019101631b268c8233e0002040675934668982160000cd485c171a6778b720839c6a20425186d082ae4ec828a77215b822c0c240f1a5ac733064884d94745be844a8a1800000000000100b826a615083a598ef08e881e39a14be109974c8879f9e0118dd34715592599400018d1e5c53480000001abc0001ef44b4923a5b00f6c42884ce8fe85c6388c4d00e4a2e23c485503efa35f63d830e8a09b6238222063d325ce79e800067398566d189c880f99e031b1c7279f93f800019020001c4205f101e3fe96c20730b2e5ce25d49769d1c0bd192c90c19030c78b70000146a298a05c2bb1f3a37b88547b2872c747400056bd16421e08d40000bc616e215011f9e06794025e37f9ca428280004fe8dbc00005425750d0061b9f3e0c11ef000019ae36788020000000313885f0000f08000000059c800086d11c2000000053fd36a0000dca501133200023ee3790c0a4bf213472a115681d255c197186b64e800000018b621380004de8aa071
  | 36 => 0x969ef2182191533c13ae15f853c40b14816e607a83958cb07cf05b6897875056d091c8b3986f6e0a17e28d05ce34e17e05a90bb260e0afc117165d67905ac71021305270314136027a56f8a2683b89f613d82ee7b79be84e413bc78da41c3058ef60a4165c0cc93746dd8016811a08807006208da80008280db84791d4017f000026a158400000002d98000149840890e1d42000091893400000001f52843139a00021b64b19ec2000097e01996f041e800000000000000e2a2b000e18e6a5424c298833799626000000012b0bb400005961728b6209608f86a59d4487a905c1a68a2c0001d3c650c7d87e7209e95100000000da61a812ec7b6800084f89723231a7c53d0e530001c9e00000008a391600001452000000048a256c123128a017812050b906c504125a6388a6a348013c79e25d04cda2404a6110c51fc83441c826867410c6518851e6a092547a41a2405d8dc2000188c91a80f883905f94999cd50000fc85df01b4827cfca1cb83252499d5a88a01a059da4cc0001ca111d812c2b49b6194b0a848460320948258619114d909e559095c1202189d5b28249ada1210a700001bd42599fc600000004478f20621800082084605a00000000104c02395d252e8d761fc969c4ec135c8998430248800048ec0000fe025b49c99544751806762a1586880f4027c0fa2000054a2841974105960459a1f8027f80cf4308000468820600000a93b21d949428c607e48000000000000c948266292621c14274727dfe658c8a5a3fd015f31d9d8842d027248ac9d0776a2567f68fd06f3161800000000000b5a00000007cc19343f7800000012d689409f8531141e0b1531a00d1712182892853f0ad60000d9893483b057284a2484800014123006af88de20508006f1108a5d01e045db8fd41e717ac86e1b9e6190ae03e7022c826c22e0fea2f80001c8a7710d9d212952a81983fe7ab12c400000006af5ab08b607120cb000000800000000b046f380365df90d2000234638501860eb0000000000012781ce68a15ea0000d42000000095f8694000246c68480a400000000000088560179205800002f6000000005f20000a2800002940000e2e844258e1698000585097c000000000005cc6469cb917780d69211ae600007d449b8dae839a37e2dd01500f71d90555049200008e87a9805a1bf100411487462ff0d6c000056a92b8d4c11880004cb89580021a3a1350688000102a0bc039c4b286be3bb8fc000019905819d0f8f713963c081835ba86e23b31b18825c0967ac98f838d8ed4785983d18384a60e59b3e5a80b5c16410b845e9d7609d800072d03348fc04c24f200c600000000000b844a500003ba00007488caa097c00086915230324eaa7fb8000329236502f80cb5461820000099a224138690a81727a480002bc956e374247e00008
  | 37 => 0x74e30d1c8c43294f800019187910c2e7c9a4e871380002fa02d04a110941dc9d0c68102606620c323c5062850c115071f046e0e800006ec1df05f8a044000000036c000043d80000000ae20000000310000049f160e14000000dd0650796800032b9ffc6f08000000156a0985f1469a800011600002508ff24c60000466071a0719120673001c7668be2482030837a81ac000108800025c4000166400024586be97588b023647958000565899e0000000802032a0001db27aa8a58281188e2b69aa46a94aa48409f0a00014580000c821e304aa730888200014a8000253a00007be14d9ab803922d63fc0f0e68413a9745a3e896d17ba349a0226c29b0c2ab87207f800007dc94544b791305d518980d01fe23de0bde48b96c322218d650ea0121fa18a89770c9c2ff9fa49560b0e41182264c2079460d9d861e2249220c13ac32680001b308e21f4a55e2cc8000421000066700006ff84500001a385580000155c0001421a4e0002292866a3443e00e3e8ed10fa415870a0001ba600000000001b7e0001ae87578f5e6ad82ec45b11042ea10be00a000000023588c999168931c0e8800d32000153e3ead1780801bee16d1b70000000000019bc4d2800046e00008ab8d084d921ce208171c86999d248c0a7c44e92884a4849847681de8a3240c17680006ee05aa01484e86504d6876e806426b0d9b1328d6a1ea93581ee803810706f80f516ad6ba81008dd91b0302056600321f40000a02223000047480001d0000066d20860a20000000169800018e44bd957e00000000000b424a91a1a000000084ba362000147e8a002568040000793800040e800013196af6d49b4a0000a245f28000000059e08c9486340832200004da835962408d252246e9c5c09c1cba48e49ec00004824cb241a0a1059443783028651ece000000000000003eb08ce00016441ffc87a29305ba70c800000018c32a7000084886462838a6e0338d1a3359f1c6bc920a331a1827599fdc6990fcd000000081a8cc40a61e6415599580d29c2255a183e5430d48524816878714942bda0784ce98d0910a4e692e01f83a8065254e89a27d182d80c00e8c0000e371618c5c2d908367b40ae40000b9028813d8449090457f115886285638830aee7830000000000075c912e383972872ce05a51d4cb456823888e797b82ef185e7351b9672f22a66d6a08a5119f182cea2226411cd28551344870031688097505e382b87920ab02170a0644191f819a0354664a0dc0269df685d88058e9939806152a61428f0c1890f341799e6215212aa2b1861c79505105e71c185bd076e80d1a4c926956222a06620651138208875a722d85a73618f148e1ecc5daa0b828aa1964c4043a2ed90302a623c27ea165a0810f506d996b02c795f44f284a0226101a777111c9221f58188c02a1e281386
  | 38 => 0x7ed800057d8c8e8d8d9d41c0982e91c14183688ea48028a401d29399626967e3f18000000241e44b00c10b0916a7898a8e7a7006e72080007c400001da83da35d00000001ee264a80002e196c417888d037a0700727000000010740188dc43d6a3041888cca6a112c87a28000000103d2e700df5b5056e05ea5d264988125aaa0ae4400c3a553a192962a3b86b714368c41ac355d197646a8c384f32462060800036f5ce8400809f000250c6200da97841e9a57040008cb00a85a407982950b1266e9f22972204c2e78de912b898678215bc05509bc8729fe8633804a70fa23e20392f244d9b30000026a0de80003241a00043069b5480000000036e3190ed04a89aca46094a0053dcec09f92174b08e8a07d9fae41420c600000001cc055100010123389ffe4ae00007051d705c61e5e5228bf44c49d643870c586d7c25250b220e0a7872238e0be44e3158a39200000000000000219c00001cb604239608f084c6278d53000000000000000000f2c376800000000000000e788881d9e89e9ff26770d9a0b80f8a830064a000252e2f21c2455e22788e0894066c87f80a923287b4855203f049c2ee818d6e88eca1bb13a25d396ee5af242485014f646d919a41d88b83658f6a2b60e0c54e1eb627d02ba8a716601969b6436a9f5e0ff188d67b122a56e578200001a668b25387f3000032b0f4e35bcf845d69acf629000000001d22fd863e832925d7e6000040fc00085d0d221d0a0f645523b200000006b317ea40149d20000ef40000000494148e4fb19e2646c00000000008a8814a000199e40000002f2916635f821075a1fce4f421525650b3c23aa1ba25a9cfe0be24a80b3879263741b9197800025c07ae4b397725630f245d29d584df068a19607a04d681470002232000137e64719550001ce2000225a0001bb255100000605d8e000000017a039a4b69ac844293b62e20f1874404662f717b024480009291c980f1000015e9afc00025266c0071e6ca94168c096b48000d284a00d5e5d1a1e800002bc290800079b1c12552877c70a0cce73c15c6719000000006b5930911a05b86b1951914e8e509b60b88894139970a000000037480002d585dc92e80008f60a74696030a0161c681e686d883a06fa0ced1ca967880615a0ef26cc8e1e4e7dc2e5a88c5e276134c61b0dce0f786c4668194a04f928606b93b42f4a2fc0289a4420691f649343e35c1183405c40000f488e000000dd000101010d809d90b8d7b11e00b2845904831b8000649038100016ae00016340000e7a0001cbd00022c68ff8b300c1800000009c411f0000000000000014285e9800002319fe88d8000210883c0000000000184700008600001f5f7f20000653000000000004af01b05569b6c29223cc45c19604a40e26000064c000107e8d6800087525760c6916e3b68
  | 39 => 0x80a33d00000f216e435998260000f587b187562319de0321a30c000000087e9bba3cb80006608000927044c75a85e725a1f482cd8e177cd0388000193824e19ab5b79a90761119000018762e6092c1fd15ef18dd0c0513000082700003c88c9e91e000000005ae68aa314000000021c8e7e5871014000000036721c4304800003ec63b0c919f85ab07b621900006e11f5400000000001d26199961e1ba000058b000000015ee000142066fa4400001eee75500002ee1a0d2c21bfc5000534221a128000226200001dc4818db90000fce5720f86712800095018492c822c400024340150f06647973c80e8000697094e59e84ee001812e398000000011d629d9db807990db4b622fa00020f266915280001dc20000ab400006f071591880ea000030a800e242800016085757fd800000008e41e880000001d2c8d09a6c82b1fd63f44c464c79ab49098f8c306985896d8a6c661547a8cca1a83b7019e139120400000a652f208e4600d5c13005d256aa56e590000000016c83800fe300005a059e1832172c000000000094d9df834d990835696e2893a5626701c5e27b990d16c8bfa000152c4189850000035a21d9a728098ad400018a21bc400000000001a080001a752c05198dbb00003569439ff453394d000025a25a99f8e3c1000003a594594005e08ce846439c80603e7a4008f111e65840d4a54d068040806fe8149f5602619c44f18dd47249cf29631f7a000056c5b046c082918fa6e9018935e24a22fba0d807945884568698539039e000000007a800060087de28491260fa06d4393800042b868655c8446582202000009ea57611322f4000000f0728351a50400022948e291c61751f2086f243c18e93d22fc11347d380001bc9cb720a000000013e4000061055592fe15817746d601284e0115c3590ee0000090800000005bda51e3f051fa3e91a7e968099c5a10d1c41a9cf65a20f6667a80ea7baa1986398f384ab9f0626f8d524a800ef15517204cd08fe36317d257c1cc049e0000401c0de0ef2370000255a44f000054523064f39b2d1e394da0d4a48a5c7867253c118a7c79f6c83aa2e80b11ee86ce912800024044f2c0003e38fb672b561b88d14d8803092e3ac9c3b14fa24a253168245ca3f2000000003700002ef8b6870b1028088a54d5c19c2d2431d382ac9f1a80b1f2a61e18226bb9f0412e8aba1ad013352214e05544c1075e052e09ad08014583f01fa9ee07f08b100000ea20ab13884aea38c47f0b2802e1b163c687ac17f847230500001980e5240399e80000fda3e4031063b4000000067e7fa9cb293c9f4481f1432935000017e820c0360406000102f654136200008265e203e0000000000000000000ae80001b242a6800077c8000000000000000000002296000000077598f015f00002ce1d081e91c89613041a
  | 40 => 0x600000740000eb45009f601480a443061e023979f3657006b252b08d22d7a2980028be612007b87c3149a7e890b049614980c6239249f99f0000045605cc0000000d7093623c864f901572800001ca943e0001636000000000002da41485b008c53be4a3826405158a0538800067f08441939d460f5944e1b217a48ac23f60001e463aa21d04c0a14a06bc00000001e463f21f232296d80000ee682595163e6a36626b8e2b6221d247299db06d40dad13c098c28f9b900aa1848912a3302f3086c8b70b167600996103021c97293a675885844f1129c9524f326c79669580126a004038e566818e06e8c4c4074b443d286404548fc42b70d8408bcc7892984004a31e721fd9f66577258242d8a5c3720eb8547014832e8ad00e425245dc1da6035038a523212026602cc80f08e683f816c000151e5f00d8a30781460bd9b9a5bfa2548d51e4c6f59a4a17925ba96f04345fb186235619003b009d41d5019c254978034e946815cc24e30d81a20cd9cbb0575a4021f81a477f893606da59c000253000000000000000000000025100008275ac052e15950001ce40d705585c980008e91cee72a819316f1b4481e8a1e0b187b2045a1dc60904b074d18b207b00003969c08586800000014ae65c80d21535dca2f5a3d02cd236071c1d1e08c24960000ccc41f0d80412853a0c4800051725081ad9953082216655ccff620118dc62f04ea87789205a69702916977a70a9f8449d10ea47a021a8e3817043822ba1219a8800012d01448d7960b1da2642a4c40b910e224f88526fb23a238e9510407043c0c31480000000035560561e589b40000d04000000046795f28af052a00010e528c02b2199012a7341cb0000027730194150c99e1207801035ac9f90000083e15308ae1db00005708fa70001f4a52c822a6ab03ce00013ee000000059380005128a380001730000175c7e5042a0000000661209900016d294a01c46a6a46e1601fa027289c67e09ad20001a3e0000d54000025c53000004760aaa73797a8868019a0000654465921c387400035ccc1c0000000426982a0000fb83b3a4e2937890e96a111209f000000001b57f48bec9111e7c054889a00019d825b80003af00005cb800092c21e275285740fc99a823d89da245800000010bc0000000000000094706c200000006980ae600012700000000000000027814ea4045b0834f0000000000080e03e141c16d0000000071100000d9a0aa766050269984b271160ce1f2138a2301b04112051c90c80005758000386c00000e842096c80006d7000000781c82e598008de166292822b896684fe7f6233458a8d2c00014cc5bb0000000000093f0b7c61b44225c393f42821890000229a00000003bf023e00006a229805f652d8aa65c5093007c00d76f289a06cd80002558559156844215c224278e
  | 41 => 0x6a1a8e17edf16314197c000038c0000786535810e0ee00002c90cda424124e84722d00001a5e6108dde00000001468000740087b56b000000025d690a08f46b51e7461c9c764de0dfc643a5a600021a2515a3d431c9656049a1ec5ba0f004cc00002c28212378996c36a1e2054d800070c17480001fe4789000012e139c36d1d520d898e12e38c3c00024524ad23b6000205461390f07900ffe3ff0386000142a2a8800081b234c000000062089804ea1fd06a01d966e70b2284a90ce494a01400017ae2a491ee26aa22691f068c21a1a5020715e48d74d0c8250c5696422f476a160a643124450e13707a79acd6011b884690c7a3298ede5e802be8340f1c01f8e4c61a1dde3e218084b31b1a4701ba8846973226507e449590276b08d2a6c0922203083271758a7258946f468c13aa00000423cf88ca7b90ec64100818779009088a974239b05ea00005627981778000195963c800077191de60397fe78e80003539be03990f7a5c303e662480b67a500004c100006cd201a0da198c0001fb85985a0a7f00932065982811a03ae6e49724303a45052c000456984e292f9d30299810809683c02021e1835b9eae2e8918e6cc4d240ba08c46aa86c653180301e40c266f197a21b697342a5055c4d486168f010d6094d0d86c813954970cb628f0d185d8968c6fda3ac4371ed63e49ec84c706b96e01ac6628d0661740a684980f10218a44e3efd21869d91a055618747b500e845d253c48f99304a09bb442311e03f8082c42e860f14c06ae3f498ee94d18143bc64aa35c97bc1ae8bb07ec09508780dfa66698ff69c16864f7032e77e87b02ba80ba1ff11fe0e61216524014c0a31e8c6a81af05808cf8061067868b9faa102975e1251a1450d1d4e2938a3d8b698c236914c25fca27e5b698c685a862a2eb174489b1ab200017b40fb18ec0001a3c700800000007d68da18ea0b71c435f3a3381c40e5c3a1043260c0b7e1d31bde2d19fba1a1033c25201241adde8672648ee2a211105cf98be74e84543a40c945e2816284e898442720169719c1c0001e8400005146f2198342c9c840be959e21682b6796103b91c8e0220b82d292c8f3a8bb254e03b80004c1866a3149a0b42480000000a8c4c0187e5ed814d12f009c74d8ea6364053889a0bae921917c648a3c6222901780915e0857907842090d4060000000000002e8000073f0f44000000000009ba24f000003c54080000000000221851cc000000164a91923be00000000000a367a3a32e00018c47c91f6873e0f3c00020d22c507e664b81580001d280001472000179
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xea664d0821040015cb0c21042080039959442084100047bc32e0108200287e85dda40040010fb0bbb480080023ba0b769001000476c16ed200200287e855da40040010ff0cbac80080021fe1d65900100043ec3acb200200ca3c8459640040194790b324800804a8f21564900100065ab24e3200200287c85dd940040230fb0dbaa80080021fa1d65500100243e43acaa00200287e859d840040010fb0b3b080080328f211651001006d1e42ac82002000c75659c440040018eacab8880080027920971100100063ab2ce31002000ce5629c620040018eacab8c400800339dd8218801000732b2843100200287c85dd920040011ef03bb240080c21f61b75480100043f43aca900200487c8759520040018b8e6b2a40080030f99774480100061eb2ee89002000c3e651d1200400187aca3a240080031799773480100062eb2ee69002000c7665dc520040018eacbb8a40080031d99471480100063ab28e2900200287e859d820040010fb0b3b0400800a1fa1576080100143f428ec100200087d851d8200401917d083b040080022f610760801000c6f418ec10020008dd831d820040010ff0eb2840080021f61d650801000c7ac34e21002000ce5760842004001ccaca1084008002f860021080100047ac30e58802004c797659610040198f2ed2a4200800a1f21776440100443ec36ea880200087e8759510040090f90eb2a2008003171cd65440100061f32ee88802000c3d65dd1100400187cca3a220080030f59474440100062f32ee68802000c5d65dcd10040018dccbb9220080031b597724401000637328e48802000c6d651c910040018eccbbb220080031d1d776440100066a39eec8802000c7785dd910040018e90bbb220080031d15376440100063ba9eec8802000c7553dd9100400196e87bb220080032d50f76440100063bbb6ea8802000c7776595100400196eedba220080032ddd87444010006ca398e88802000c777695110040019aeedb9a200800339ddb72440100047ac34e488020009e6829c910040019ceec392200800359dd47244010006b23a8e48802000da7741c91004001b48e8392200800371dcc7244010006e2398e48802000d66651c91004001acaca3922008003599507244010006b22a0e48802000ce7631c910040019cac6392200800359d4c7244010006b2a98e48802000da7431c91004001b4a8639220080033998072440100063d32eec8802000c7875dd910040019b0e7bb220080031ee1776440100063c42eec8802000c7854dd910040018f6a7bb220080031e54f76440100065da1eec8802000cb943dd910040018f6edbaa20080031edd965440100065dbb6e88802000cbb761d11004001b30e63a220080031edda54440100066dbb6e68802000ceb76dc910040019d6ec3922008003781cb7144010
  | 1 => 0xd0b3b684080021f61676d08100647ac34e3a102000c75659c742040018eacab8e840800a1fa1776908100043ec2eed210200287e859da42040010fb0b3b4840800a1fa1576908100143f428ed210200087d851da42040031bd063b484080023760c76908100043fc32eb210200087f8759642040010fb0eb2c84080328f211659081006476c3cc5210200287c85dd942040050fd0b3b284080021f61676508100043fc2aeca10200287c855d942040011ef02bb2840800a1fa1476508100043ec28eca1020018de831d942040011bb063b284080021f61b75508100043f43acaa10200087c8759542040191d90eb1284080031d99771508100063ab2ee2a1020008f5861c542040018ecca38a84080031d59471508100065b320e2a102000cb5641c542040019ccc438a84080033958871508100143f42cec210200087d859d8420401947908b2884080328f21165d04100143f42eed208200087d85dda41040050fd0abb482080021fe1975904100043fc3acb208200087d8759641040050f90bbb2820807e1f61b75504100043f43acaa08200487c87595410401947908b2a82080031b997725041000636b2ee4a082000c6e651c941040018daca392820800a1fa1576c84101ec3fc32eb908200487f8759721040010fb0eb2e42080f29de1d65c84100053ac3acb90820c4a748459721040014ef06b2e42080029d60d65c84100071ba1acb9082000e354359721040011eb0e32642080029d61464c84100056ac18c99082000ae58219321041894ef0d2a642080029d61762c84100143f42eed108200087d85dda210401917d09bb442080022f613768841000c6f41eed10820008dd83dda21040050fd0abb442080021fe1975884100043fc3acb108200087d8759621041878ece2b2c420821eb960562084104373332a421082000e656548421040018e8a8bb042080031dd4d76084100063aa9aec1082000cb7435d8210400196a86bb04208003398c9760841000672992ec1082090a748459421040014ef06b2842080029d60d65084100071ba1aca1082000e35435942104001ccd04b2842080039960965084106163b392ca1082000e66325942104001cca64b2842080023d61c64084100053ac28c81082000ad58319021040015cb0432042082429de1a54084100063abb4a81082000ae5869c821040016cb0b39042080039959672084100053ac2ec41082000ae5869882104001ccacb31042080023de1d62084100073332ac41082000e656558821040015cf0eb10420800339e1d620841000573c2ac41082000ae58558821041215c908b104208003999516208410007322a2c41082000ae78358821040015cb06b10420800399d4d620841000732a9ac41082000ea7435882104001d4a86b104208242b9e1b420841000732b2e841082090
  | 2 => 0xe76950100643fc32ed2a0200c87e845da54040190f908bb4a8080021fe0d76950100043ec1aed2a02000c3f435da540400187a86bb4a8080021f61f64950100043fc3ac92a0200c87c845d762040010ff06baec4080021fe1574d88100143e42ae9b10200c87f8795362040010fb0f2a6c4080321fe1c54d88100043ec38a9b102000a5d8315362040050fd0bb9ec4080021f61773d88100143fc3ea7b10200087d87d4f62040010ff0ea9ec4080021f61d53d88106361f3ae87b102000c3d75d0f620418b87ceaa1ec4080030f5d543d881000e4f39a87b102000c9d7350f6204001c3aa6a1ec4080031d5d671d88100043fc2ae9310200287c855d262040014bb062a4c4080038754d439881000c76c3c6531020008bf845d5620401917908baac4080023d20575588100143f42ee8b10200087d85dd1620400187ee82a2c4080330f1d054588100052ec18a8b1020008f4815cd6204001c3aa6a1ac4080063b21d32588100057240a64b10200287f865d462040010fb0f328c408003179ce65188100043fc3aca3102000c5e73594620400187ccb3a0c4080030f59674188100061f32ae83102000c3d655d062040018bccab98c40800317595731881000477c3ac43102000cad74588620400199ae6b10c4080322fa1375188100045ec26ea31020018de83dd462040011bb07ba8c4080321f21175188100043fc1aea3102000c3e759d0620400187aeb3a0c4080330fe1674188100661e42ce831020008bd839d062040010ff0aba0c40800a1f21574188100061f3aae83102000c3d755d0620400187f0aba0c4080030f21574188100045fc1ae8310200c87f8795062040010fb0f2a0c4080330f9d254188100061eba4a83102022c5e7395062040190ff0e2a0c4080021f61c54188100661f3a0a83102000c3d7415062040014bb062a0c40831f179cc54188100143f42ee6310200087d85dcc620401917d09b98c4080022f61373188100062f3ace63102000c5d759cc620400193ce9398c408003275d273188100062f3aae63102000c5d755cc620400193ce8b98c408003275d173188100062f42ae63102000c5d855cc620400193d08b98c4080032761173188100062f2a2e63102000c5c545cc62040050ff0fa98c4080021f61f53188100061f3a6a63102000c3d74d4c62040038bce7a98c408003175cf53188100043fc3aa6310200087d8754c620400187ce8a98c4080030f5d1531881000e2f39aa63102000c5d7354c620401917f0fa18c4080022f61f43188106361f3ae863102000c3d75d0c620400393ce7a18c408003275cf43188100045fc3a8631020008bd8750c620418b87ceaa18c4080030f5d5431881000e4f39a863102000c9d7350c6204001c3aa6a18c4080032d5d271188100066ab9ce23102000cd9739c062040050f
  | 3 => 0x2b2820c8a79809c565040090fd0f98aca080021f61f31594100051f42662b282000a3d84cc565040014dd0598aca080029b60b31594100043f43862b28200087d870c5650400147d0818aca080028f61031594100072a98862b2820c8a75819c165040090fd0f982ca080021f61f30594100051f42660b282000a3d84cc165040010fd0e182ca080021f61c30594100051f42060b282000a3d840c165040014dd04182ca080029b60830594100053b40860b282000a75810c165040010ff06baec8080029760c54d90100143f42ee7b20200087d85dcf64040050ff0fa9ec8080021f61f53d90100043fc3aa7b20200087d8754f640418d87ceba1ec8080030f5d743d901000c5fc3a87b2020c5c3e7550f640400187aeaa1ec808007279cd43d90100064eb9a87b202000e1d5350f640401947d0932cc8080328f21165990100043fc2ae7320200287c855ce640401993e86b9cc8080321fa1f53990100643e43ea7320200c87e8754e64040190f90ea9cc808007179cd53990100062eb9aa7320200cc3f7550e6404019878eaa1cc80803327dcd43990100070ea9a87320200287e859ca64040010fb0b394c8080021fe1572990100143e42ae53202000a3e8499564040090f90eb2ac8080028f21165590100143f43eeab20200c87e84dd564040010fb07baac8080021fa1c75590100052ec18a8b2020018bc84dcd64040010ff0ab9ac80800a1f215735901000477c12e6b2020008ec825cd64040011e902b9ac8080023e20173590100043f43ea6b20200287c87d4d64040010fd0ea9ac8080021f21d53590100061fbae86b2020c6c3c75d0d64040031790ea1ac8080030fdd5435901062e1e3aa86b202000c9f7350d6404001c3aa6a1ac808002ad20543590100043ec3cca3202000c5e7399464040010ff0eb28c808003179cd65190100045fc3ac83202000c5e655cc64040018bacab98c8080332799173190100064eb22e63202000c6e659c864040018dacb390c8080031b995721901000636b2ae4320200ccae645c8640400195ac8b90c8080321f21175190100043fc1aea320200cc3f435d4640400317b08b98c80803327d0d73190100062f42ae63202000c5d855cc640401993d08b98c8080331795173190100662e2a2e6320200287f87d4c64040010fb0fa98c808007179cf53190100062eb9ea6320200087f8754c64040010fb0ea98c808007179cd53190100062eb9aa632020c5c3e7550c640400187aeaa18c808007279cd43190100064eb9a863202000e1d5350c64040198dca9390c8080331b152721901000637a9ce43202000c6d539c8640401995e87390c8080032b50e7219010066372a2e4320200cc6c545c864040018dea6b90c8080031b54d721901006657a1ae43202000cad435c864040019c902b90c8080021f61
  | 4 => 0x440031b906bb2408800a1f214764811000c6e418ec902200087e87d9520440010f90fb2a4088003171cf65481100045f43ec890220008bc87d91204400187eebb2240880030f1d764481100064e39ec890220008be8719120440191790e32240880030fdd464481100061e3a8c89022000c9c7319120440011bd0fb1a40880023721f63481100062fbaec69022000c5c75d8d204400193ee9b1a4088003271d363481100063bb2ee29022000c7465dc5204400196ec9b8a40880032d19371481100066bb1ee29022000cd463dc520440018eeca38a40880031d19471481100065bb20e29022000cb4641c520440019aec638a40880033518c714811000673b10e29022000ce4621c52044001d30c632620880231d9db65841100065b3b6c9082200ccb6761921044001d28c6324208801f359db638411000733b28c50822000e646518a1044001d4ec83142088003a9190628411000763b18c50822000ec46318a1044001ccca8314208800399150628411000673b98c50822000ce57318a1044001ccea631420880039954c628411000753a18c50822000ea54318a10440012bb063a2ca080021fe1973594100043f43ec6b28200487e8798d650400147d0931aca080028f61263594100062fb9cc6b28200287e8758d65040018bee6b1aca080021fa1c63594100051f420c6b282000a3d8418d65040014dd0431aca080029b60863594106361fbb686b2820c5c3f7650d6504001a3ae6a1aca080038798d43594100070eb1a86b282000c3f749d1650401987ce83a2ca0800297a0c74594100052ec18e8b28200c87e84dcd65040010fb0f39aca080028fa1273594100051ec24e6b2820cba77815cd65040014e902b9aca080321f21173594100062fc1ae6b282000c77815cd65040018e902b9aca080021fa1c73594100051f420e6b282000a3d841cd65040190f90fa1aca080330f9d343594100661e3a686b28200cc3f87d0d65040198790fa1aca080030fdcf43594100061eb9e86b28200087e8790d65040010fb0f21aca0832a8f61243594100062eb9c86b28200087f8750d65040010f90ea1aca080330f1d143594100062eb9a86b282000c3f8750d65040018790ea1aca0800387e0d43594100061fb9a86b282000e1e7350d650400187ae6a1aca08003875cd43594100060eb9a86b28200087e8710d65040010fb0e21aca083268fa1043594100053b40ee4b282004a7581dc965040018dee5392ca080028fe1172594100051e422e4b2820c2a77815c965040014e902b92ca080021fa1f32594100043ec3e64b282000a3e84cc9650400147b09992ca080029da0732594100053ac0e64b282000a77814c965040014e902992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca080028fa1271594100051ec24e
  | 5 => 0x80021fa1b75505100062e31eeaa0a200087e87d9541440010f90fb2a82880030fdd764505100061e3aec8a0a2000c3f751914144001878ea322828800317dd763505100062e3aec6a0a20008ee86dc941440018decbb9282880031b197725051000657b26e4a0a2000cac64dc9414400199ec7b9282880033318f725051000477430e4a0a2000c6f651c941440018d8ca39282880032bd90725051000656320e4a0a2000ccf631c94144001998c639282880023ba1f62505100047643ec4a0a2000c6f75d8941440018d8ebb1282880023ba1c625051000637ba8c4a0a2000c6c7518941440019b0c7b8282880032ed9070505100066c318e0a0a200cab4865044144001c6ecaa0882882b7a518d4110510007523128220a200287c859db21440010f90cbae42880031718d75c85100043fc3ecb90a200087d87d97214400187cebb2642880030f5d764c85100061f3a8c990a2000c3d7519321440018bcebb1e4288003175d763c8510006373aec590a2000c6d75d8b21440018dcea31642880031b5d462c851000674314e190a200287c859da21440330f90cbac42880031718d75885100043fc3ecb10a200887d87d96214400187cebb2442880030f5d764885100061f3a8c910a2000c3d7519221440018bcebb1c4288003175d76388510006373aec510a2000c6d75d8a21440018dcea31442880031b5d4628851000675b10e090a2000e6765484214410dcc8ca9084288003a9d912108510007523224210a2000ec763484214410bd88c690842880332d19271d011000672314e3a022000ce4625c740440050f90b3b480880030f15276901100943e432eb2022000c5c635d640440010ff0fb2c80880221f61f65901100651f426cb2022012a3e85d92404400187cebb2480880030f5d764901100651e428c92022000c3e75192404400187aea3248088003179d763901100062ebaec72022000e1c54d8e40440018dcebb1480880031b5d76290110007162a6c52022000c6e7518a40440018daea31480880038b15062901100043fc2aeca02200287c855d940440011bf06bb280880063720d765011000477c12eca02200287c851d940440010fd0dbaa80880031718f75501100043f43ecaa02200087c87d95404400187eebb2280880030f1d764501100061fba8c8a022000c3c7519140440018beebb1a8088003171d7635011000637baec4a022000c6c75d8940440018deea31280880031b1d462501100066a31ee2a022000ce462dc5404400196ec838a80880033518c715011000672310e2a022000c3c549d8404401947d09b2880880368fa1764101100070e2a6c62022000e2c54d884044001c58a831080880033918a71c811000672312e3902200087f855d920440050f90abb240880022fe1176481100645e422ec90220008df835d92
  | 6 => 0x732a9a623122000ea7434c46244001d4a86988c488002b9201311891000537428623122000a6d850c4624400155d08188c488002ab610311891000537c2ae03122000a6c855c0624400155f08b80c488002ab211701891000567c1ae03122000acc835c062440015cd03a80c488002b9607501891000557c22a03122000aac8454062440015cf02a80c488002b920550189100053742e603122000a6d85cc0624400155d09980c488002ab61330189100057340e603122000ae581cc06244001d8c63180c488002b9e0530189100057240a6031220008ee870c062440011db0e180c4880029ba14301891000536c28603122000aae840c0624400155b08180c488002b9a04301891000572c08603122000ec6310c062440014df0a880c4880029b215101891000557c22203122000aac84440624400159f06880c488002b320d10189100043fc2aeda12200287c855db42440011bf06bb684880063720d76d09100143f42eed212200087d85dda42440031bd07bb484880023760f76909100143e42ced212200087f855da42440050f90abb4848800237e0d769091000c6e41aed212200287e851da42440010fb0a3b484880021f21975909100062e31aeb212200087f87d9642440010fb0fb2c84880030f9d764909100061ebaec92122000c3e75192424400187aea3248488003179d763909100062ebaec72122000c6e75d8a42440018daebb1484880031b9d4629091000636ba8c5212200287e85dd942440010fb0bbb2848800637a0f76509100046ec1eeca12200287e859d942440010fb0b3b284880021fe1576509100143e42aeca1220008df835d942440031b906bb2848800a1f21476509100047a408eca12200087e86dd542440018b8c7baa84880021fa1f65509100043e43ecaa122000c3f75d914244001878ebb2284880030fdd464509100061e3a8c8a122000c5f75d8d42440018b8ebb1a84880323ba1f625091000637baec4a122000c6c75d8942440018deea31284880031b1d462509100063bb2ee2a122000c7465dc5424400196ec9b8a84880032d19371509100066bb1ee2a122000cd463dc542440019c8c5b8a84880031dd9471509100063a328e2a122000cb7641c54244001968c838a848800335d8c71509100066a318e2a122000ce7621c542440019c8c438a84880021fe1576109100143e42aec21220008df835d842440031b906bb084880332d192711091000672314e22122000ce4625c44244019970c9386828800a1f21676905101043e432eb20a2000c5c635d641440010ff0fb2c82880221f61f65905100061f3aec920a2000c3d75d92414400187cea32482880030f5d464905100062f3aec720a2000c5d75d8e41440018dcebb1482880031b5d76290510006373a8c520a2000c6d7518a41440050f90a3b2828
  | 7 => 0x6e86d4c62440014d90da98c4880031b9db531891000717b26a63122000e2c64d4c6244001c9ec7a98c4880039318f531891000537432a63122000a6c8654c62440018dceca98c4880038bd91531891000716322a63122000e4f6354c6244001c98c6a98c488002aba1b431891000556436863122000cae76d0c6244001c5ecba18c4880038b197431891000747b1e863122000e8c63d0c624400155d0ca18c488002ab2194318910006573b2863122000e2f6550c6244001c58caa18c488003a3d8d43189100074631a863122000f0d5350c62440015cd0d188c48800399d9631189100073232c623122000ea7648c46244001d48c9188c488003b1d8e31189100076231c623122000e67654c46244001cc8ca988c488003a9d91311891000752322623122000ec7634c46244001d88c6988c488002b9a06751891000572c0cea3122000a6e85dd062440014db0bba0c4880029be1574189100053642ae83122000ae7815d062440015cb023a0c4880038bd52541891000536c1ca83122000ace83150624400159b062a0c488002b9a04541891000572c08a83122000e2e841506244001c9d062a0c4880029b60c541891000726c18a83122000a4d831506244001ccd022a0c4880039960454189100053742ce63122000a6d859cc624400155d09398c488002ab61273189100057340ce63122000ae5819cc62440014dd0a398c4880029b614731891000557420e63122000aad841cc62440015cd02398c488002b9604731891000575400e63122000ae9801cc62440014dd09a98c488002aba12531891000556c24a63122000ae68194c62440015cb03298c4880029b211531891000727c1aa63122000aae8414c624400155b08298c488002b9a04531891000572c08a63122000a6f85d0c62440014d90ba18c4880038b9534318910007162a6863122000e2f85d0c6244001c590ba18c4880038bd4f431891000716a9e863122000a6e8590c62440014db0b218c4880039354e43189100057340c863122000ae58190c62440014df0aa18c4880029b2154318910007172a2863122000e2c5450c6244001c9aa6a18c4880038be1543189100071642a863122000e8f8350c6244001c5ea6a18c488003a394d431891000716a9a863122000e8d5350c6244001c1aa6a18c4880029ba14431891000536c28863122000ae68110c62440015cb02218c4880029ba17711891000536c2ee231220008ee87d4462440011db0fa88c4880023ba1f311891000476c3e623122000a6e85cc462440014db0b988c488002aba13311891000556c26623122000e66548c46244001cc8a9188c48800399d4e311891000732a9c623122000ea7438c46244001d4a87188c488002b9a023118910007332a2623122000e64544c46244001d8f06988c48800399d4d31189100
  | 8 => 0xe6a9ac4880022fa1f43589100645e43e86b122000c3f75d0d624418d878eba1ac48800327dcf435891000e4e39e86b1220008be8750d62440011790ea1ac4880030fdd5435891062e1e3aa86b122000c9f7350d6244003938e6a1ac4880038754d43589100063bbaee2b122000c7475dc5624400196ee9b8ac4880032d1d371589100066bb9ee2b122000cd473dc562440011df0eb10c4880029be1562189100053642ac43122000aaf84588624400155908b10c488002b3e0d62189100056641ac4312200087f855d062440050f90aba0c4880029760c54189100070ea9a863122000a6e859c862440014db0b390c488002aba12721891000556c24e43122000ace839c8624400159b07390c488002b9607521891001476c3ca43122000a6e85cc862440014db0b990c488002aba13321891000556c26643122000ae581cc862440031db0f190c4880029ba14321891000536c28643122000aae840c8624400155b08190c488002b96043218910006373b6ca3122000a6e84d9462440014db07b28c4880023b61e651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000c6e7619462440014dd08328c4880029b60c65189100053742ec83122000a6d85d90624400195cedb20c4880038bd9764189100071632ec83122000e2e85d906244001c5b0bb20c488002ab60f641891000476c3cc83122000a6e8599062440014db0b320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400195cec320c4880038bd94641891000716328c83122000e2f851906244001c590a320c488002ab60c641891000537434a83122000a6c8695062440018dced2a0c4880038bd92541891000716324a83122000a6e8615062440014d90c2a0c4880031b9d8541891000717b20a83122000e2c64150624400169b062a0c488003339db631891000727b2ec63122000e4c65d8c6244001d1ec9b18c488003a3193631891000727c2ec63122000e4c85d8c6244001d1f09b18c488003a32136318910007272a6c63122000e4c54d8c6244001d8f03b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab612631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000a6e8518c62440014db0a318c488002aba10631891000556c20c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001c9d0a318c48800393614631891000747420c63122000e8d8418c6244001c9ca8318c48800393150631891000762c08c63122000a
  | 9 => 0x54989100143f42ee7312200087d85dce624401917d09b9cc4880022f61373989100062f3ace73122000c5d759ce624400193ce939cc488003275d273989100062f3aae73122000c5d755ce624400193ce8b9cc488003275d173989100062f42ae73122000c5d855ce624400193d08b9cc4880032761173989100062f2a2e73122000c5c545ce62440050ff0fa9cc4880021f61f53989100061f3a6a73122000c3d74d4e62440038bce7a9cc488003175cf53989100043fc3aa7312200087d8754e624400187ce8a9cc4880030f5d1539891000e2f39aa73122000c5d7354e624401917f0fa1cc4880022f61f43989106361f3ae873122000c3d75d0e624400393ce7a1cc488003275cf43989100045fc3a8731220008bd8750e624418b87ceaa1cc4880030f5d5439891000e4f39a873122000c9d7350e6244001c3aa6a1cc488007359ce319891000c7bc3a633122001cd6734c662440050fd0dbaac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800637a1b73589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100046f43ec6b122000c5f75d8d62440018b8ebb1ac48800327dd363589100064e3a6c6b1220008de8718d62440018beea31ac488003171d463589100064fba0c6b122000c9c7418d62440190fd09baac4880021f60f75589100045fc22eab12200c8bc845d562440011bf06baac4880063720d75589100047bc0aeab12200287e85dd162440010fb0bba2c4880030fdd774589100061e3aee8b122000c3e85dd1624400187b0bba2c4880022f60f74589100061fba8e8b122000c3c751d1624401987f0a3a2c4880330f21474589100045ec18e8b12200087e8795162440190f90f2a2c4880030fdd254589100661e3a4a8b122022c5c7395162440010fd0e2a2c4880321f21c54589100061fba0a8b12200cc3c7415162440014bb062a2c48831f171cc54589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fc2ee6b122000c5c85dcd624400193f09b9ac4880032721373589100062f2a6e6b122000c5c54dcd62440010ff0ab9ac48800a1f21573589100045fc22e6b12200c8bc845cd62440011ef02b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f53589100143e43ea6b122000c3f74d4d6244001878e9a9ac48800317dcf535891000e2e39ea6b12200087e8754d62440010f90ea9ac4880030fdd153589100061e3a2a6b122000c5f7354d62440038b8
  | 10 => 0xb122000a6d831536244001c9b062a6c4880029360c54d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537428e7b122000a6d851cf624400155d0839ec488002ab61073d891000573408e7b122000ae5811cf62440014dd09a9ec488002aba1253d891000556c24a7b122000a6c8454f6244001c9f06a9ec488002aba1053d891000556c20a7b122000a6f85d0f62440014d90ba1ec4880038b95343d8910007162a687b122000e2f85d0f6244001c590ba1ec4880038bd4f43d891000716a9e87b122000a6e8590f62440014db0b21ec4880039354e43d891000537c2a87b122000a6c8550f6244001c5ca8a1ec4880038b15143d891000726a9a87b122000e2f8550f6244001c590aa1ec488003a3e0d43d891000717a9a87b122000e8e5350f6244001c5aa6a1ec488003a354d43d891000706a9a87b122000a6e8510f62440014db0a21ec4880029be1571d89100053642ae3b1220008ee87d4762440011db0fa8ec4880023ba1f31d891000476c3e63b122000a6e85cc762440014db0b98ec488002aba1331d891000556c2663b122000a6e850c762440014db0a18ec488002aba1031d891000556c2063b122000a6e85dc362440014db0bb86c488002aba1370d891000556c26e1b122000ace83dc3624400159b07b86c488002abe1150d891000556422a1b122000a6e85cc362440014db0b986c488002aba1330d891000556c2661b1220008ee870c362440011db0e186c4880029ba1430d891000536c2861b122000aae840c3624400155b08186c488002b9a0430d891000572c0861b122000c5e73d9662440018bce632cc4880030fd9674989100061e32ce93122000c3f655d26244001878caba4c4880030f9d764989100061ebaec93122000c9e73d92624400187cea324c4880030f5d464989100064f398c93122000c5f655ce62440018b8cab9cc48800327d9173989100064e322e73122000c5e75d8e62440018baebb1cc488003279d363989100064eba6c73122000c5e7518e62440018baea31cc488003279d063989100064eba0c73122000c6e75d8a62440018daebb14c4880032b9d3629891000656ba6c53122000cce73d8a624400199ae7b14c4880322fa1375989100045ec26eb31220018de83dd662440011bb07bacc4880321f21175989100043fc1aeb3122000c3e759d2624400187aeb3a4c4880330fe1674989100661e42ce931220008bd839d262440010ff0aba4c48800a1f21574989100061f3aae93122000c3d755d2624400187f0aba4c4880030f21574989100045fc1ae9312200c87f8795262440010fb0f2a4c4880330f9d254989100061eba4a93122022c5e7395262440190ff0e2a4c4880021f61c54989100661f3a0a93122000c3d7415262440014bb062a4c48831f179cc
  | 11 => 0x440015af02b96c68801eb520572d8d100056b40ea5b1a2000ad581d4b634404d5b501b8ec688002b3a0b51d8d1000566c16a3b1a2026ad681dc3634400153f08a86c688002a721150d8d100043fc2ae9b12200287c855d362440014bb062a6c4880038754d43d891000572c0ea5b1220028ef8754b62440014dd0b996c4880029b61732d89100055742665b122000aad84ccb62440031df0e996c4880029ba1432d891000536c2865b122000aae840cb624400155b08196c4880029ba1365d891000536c1ecbb122000aae84997624400155b0932ec488002b3a0e65d891000566c1ccbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000a6e8419762440014db0632ec4880029ba1764d891000536c2ec9b122000e2f65d936244001c58cbb26c4880038ba1764d891000716c2ec9b122000aad83d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d891000717c28c9b122000e2c85193624400155b06326c4880029ba1a54d891000536434a9b122000e2f649536244001c58c92a6c4880029ba1854d891000536430a9b122000e2f641536244001c58c82a6c488002d360c54d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000727c2ec7b122000e4c85d8f6244001d1f09b1ec488003a321363d8910007272a6c7b122000e4c54d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f62440014dd0a31ec4880029b61463d891000557420c7b122000aad8418f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c9d0a31ec4880039361463d891000747420c7b122000e8d8418f6244001c9ca831ec4880039315063d891000762c08c7b122000a6e86d4f62440014d90da9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000aae86d0f62440015590da1ec4880038bd9743d89100071632e87b122000e8f63d0f6244001d18c7a1ec488002aba1943d89100055643287b122000e2f6550f6244001c58caa1ec488003a3d8d43d89100074631a87b122000f0d5350f6244001d88c718ec488003b118d31d891000573408ebb122000ae5811d762440014dd0bba6c4880029b61774d891000572c0ee9b122000a6f855d362440014d90aba6c4880038bd5254d891000536c1ca9b122000ace83153624400159b062a6c4880038ba1054d891000727418a9
  | 12 => 0x30f61f64951100051fc1ec92a22000a3d83d92544400187ee7b24a8880030f5cf64951100043fc3ac92a22000a5f8359254440454b906b24a8880029be09649511000536412c92a22000a3e86192544400187cec324a8880330f1d864951100070e318c92a22000a5e86dd763440018bcedbaec68800297a1875d8d100062f3b0ebb1a2000c5e76d9763440014bd09b2ec6880023761e65d8d100052f42ccbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a20008df87597634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc8259763440014bd0c32ec688003179d865d8d100052f420cbb1a2000a9e86dd3634400193cedba6c68800347dd774d8d100070fb2ee9b1a2000e1c65dd3634400153d0c3a6c688003279d874d8d100070fb28e9b1a2000e1c651d363440014bd0bb26c6880029761764d8d100064f3b6c9b1a2000e1f65d936344001c38cbb26c68800387a1764d8d100070ec2ec9b1a2000e1f75d936344001c38ebb26c6880023761e64d8d100052f42cc9b1a2000a5d85993634400153d09326c688002b3a0a64d8d1000566c14c9b1a20008df8759363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc82593634400153d0c326c688003279d864d8d100070fb28c9b1a2000e1c651936344001c3f0a326c6880038721464d8d100070fba8c9b1a2000e1c7519363440014bd0d2a6c6880029721a54d8d101162f3b4a9b1a2000e1f649536344001c38c92a6c68800257a1c54d8d100052f430a9b1a2000a5c86153634418f8bcec2a6c68800387d9054d8d100070e320a9b1a2007ad686dc763440014bd09baec68800297a1675d8d100054f424ebb1a2000a9d849d7634400153f08baec688002a721175d8d100052f438ebb1a2000c5e871d763440014bd083aec68800297a1774d8d100052ec2ee9b1a2000c5f75dd36344001c3d0bba6c6880038761774d8d100064fbaee9b1a2000e1f75dd3634400183eebba6c688003275d774d8d100070e3aee9b1a2000a5e859d363440014bb0b3a6c688002a7a1274d8d100052fc2ae9b1a2000a5c855d363440018beeaba6c688002a7a1c74d8d100064f438e9b1a2000e1f851d36344001c390a3a6c68800387dd474d8d100070e3a8e9b1a2000e1f5495363440014bd0f2a6c6880029721e54d8d106652f424a9b1a2000e1f749536344001c38e92a6c68800237a1c54d8d100046ec38a9b1a2000a5e8715363440018bd0e2a6c68800217a1c54d8d100062ec38a9b1a2000a5c8715363440a74bd082a6c68800387a1054d8d100070fba0a9b1a2000e1c7415363440014bd0b396c6880029761672d8d100054f424e5b1a2000a9d849cb63440014bf0ab96c6880029721572d8d100054fc22e5b1a2000a9c845cb63
  | 13 => 0x51ec28c63222000c9d7318c6444001c3eca318c8880038719463191100064ec38c63222000e1e8518c6444001c3b0a318c88800387dd463191100070e3a8c63222000e958118c644400147d0da98c8880028f21b53191100061f3b6a63222000e1f63d4c6444001c38c7a98c8880028fa1953191100051e432a63222000c3e7654c6444001a3ae6a98c88800387d8d53191100070e31aa63222000ab6868c46444001d28c7188c888003a518d31191100651f42cea322200cc3f759d4644401987f0bb98c8880330f21773191100045ec3ce63222000a3e859cc644400147b0b398c8880028fe1573191100051e42ae6322200cc3f755cc6444019878eab98c8880030fe1573191100061e42ae6322200c8bf835cc644401993f06b98c8880328fa1f53191100651e43ea63222000c3f73d4c644400187ae7a98c8880322fa1e53191100045ec3ca63222000a3d8594c644400193ae7298c888003275cd53191100651f43aa6322200ca3c8754c6444001c3f06a98c8880030fdcd53191100070f39aa63222000c3d7354c6444001c3ae6a98c888003075cd53191100645f438a632220008bd8714c644400147d0a298c8880028fa1672191100051ec2ce43222000a3f855c864440014790ab90c888002ade0572191100055b40ea43222000ab581d48644401917d0f990c8880022f61f32191100051f42e643222000a3d85cc8644400156d03990c888002ad60732191100645f4386432220008bd870c8644400147d0a190c8880028f61432191100051fc2ae23222000a3c855c4644400155f04b88c888002ab209711911000557416a23222000aad82d44644401917d0f988c8880022f61f31191100051f42e623222000a3d85cc4644400155d05988c888002ab60b31191100055dc02623222000ab8804c4644401917d0e188c8880022f61c31191100051f428623222000a3d850c4644400147f0ab80c8880028f21570191100945fc3aa0322200c8bc87540644401917d0f980c8880022f61f30191100051f42e603222000a3d85cc0644400156f02980c888002ad20530191100645f4386032220008bd870c0644400147d0a180c8880028f614301911000557410603222000aad820c0644400156d02180c888002ad60430191100051fc2a203222000a3c8544064440190fd0d3b4a8880031718e76951100651e424ed2a22000c3e749da54440190fd093b4a8880321f21276951100061e424ed2a2200087f839da54440010fb073b4a8880030fd0e76951100061ea1ced2a2200ca3c845da54440014bf06bb4a88808a9720d769511000537c12ed2a22000a6c825da54440010fd0c3b4a8880031718c76951100043ec3ec92a22000c3e74d92544401947d0db24a8880030f9db64951100061e3b6c92a22000e1c63d92544400147b0fb24a888
  | 14 => 0xc855cd644400117f08b9ac8880023be09735911000476412e6b2220008f7815cd64440011f700b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440010fd0fa9ac88800a1f21f53591100062fb9ea6b222001c5c73d4d64440010fd0ea9ac8880021f21d53591100062fb9aa6b222001c5c7354d644400117d0fa1ac8880030fdd743591106361e3ae86b222000c9f73d0d6444003938e7a1ac8880062f21d43591100061fbaa86b2220c5c3c7550d644400193ee6a1ac888007271cd43591100070ea9a86b222000c6f75dc964440018d8ebb92c8880032bdd3725911000667b9ee4b222000ccc73dc964440018d8a9b92c8880031bd4f725911000636a9ee4b222000caf43dc9644400195a87b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc7259110006362a0e4b222000c6f531c964440018daa6392c8880032bd0c725911000656a18e4b222000cd473dc564440019c8e5b8ac888003361cf70591100143f42cec322200087d859d8644401947d09b28c8880328fa1065191100045fc3ac83222000a3f8559064440014790ab20c888002a7e0d64191100054e41ac83222000aaf82590644400155904b20c888002c760c54191100062e3a8c63222000e1c5418c644401917908ba8c8880328fa1754191100661fbaea8322200087f855cc64440050f90ab98c8880322f21173191100661f2a2e6322200cc3c545cc644401993e86b98c8880321fa1f53191100643e43ea6322200ca3e84d4c644401947909a98c8880321fa1d53191100643e43aa6322200ca3e8454c644401947908a98c888007179cd53191100062eb9aa632220008bd8790c644400147d0b218c8880028f61643191100070ea9c863222000a3f8550c64440014790aa18c8880330fdd543191100661e3aa86322200cc9f7350c6444001c3aa6a18c88800a1fa1672191100043ec2ce4322200087f855c864440050f90ab90c8880028fa1676191100051ec2cec3222000c3e859d8644400187b0b3b0c8880022f60e76191100051f430ea3222000c3e761d4644400163b063a8c8880030f9db65191100051ec1eca32220008bd87994644400153d07328c888002a760e651911000557414ca3222000aad82994644400117f0eb28c888002a7e0d65191100054e41aca3222000aaf82594644400155904b28c8880030f9d865191100051ec18ca32220008be86dcc644400187ecbb98c8880030f19773191100061fb2ae63222000c3c655cc644400117f0fb18c888003275cf63191100045ec3cc63222000a3e8598c644400147b0b318c888002aba0a631911000556c14c632220008bf8758c644400147f0ab18c8880028f215631911000557c12c63222000aac8258c644400117b0e318c8880028fa14631911000
  | 15 => 0xe29ec8880022f61c53d91100051f42ee5b222000a3d85dcb644400156b03b96c8880028fa1472d91100051ec28e5b222000ab681d4b644400156b03a96c8880022fa1f32d91100045ec3e65b222000a3e85ccb644400147b0b996c888002ada0732d91100055ac0e65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000a3e85dc7644400147b0bb8ec888002aba0b71d911000556c16e3b222000aae82d47644400155b05a8ec8880022fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec888002aba0b31d911000556c1663b2220008be870c7644400117b0e18ec8880028fa1431d91100051ec2863b222000a3e85dc3644400147b0bb86c8880362fe1d50d91100945e43aa1b2220008be87cc3644400117b0f986c8880028fa1730d91100051ec2e61b2220008be870c3644400117b0e186c8880028fa1430d91100051ec2861b222000aae820c3644400155b04186c888002ada0430d91100055ac0861b22200cc3c645d664440018bce7b2cc888003179cc65991100061f3aec93222000c3d75d92644400193ce7b24c88800317d9573991100062e32ae73222000c9f645ce6444019938c8b9cc888003179d463991100062eba8c73222000c6f659ca64440018d8cb394c8880032bd92729911006656324e53222000ccc639ca64440018decab94c8880031b195729911000657b22e5322200ccac645ca6444001998c6b94c8880321f21175991100043fc1aeb322200cc3f435d6644401993e86b9cc88800317a1573991100062ec2ae7322200cc9e845ce64440198bca8b9cc8880331715173991100143fc3ea7322200087d87d4e64440038bce7a9cc888003175cf53991100043fc3aa7322200087d8754e64440038bce6a9cc888003175cd539911062e1f3aa873222000c3d7550e644400393ce6a1cc888003275cd43991100070ea9a87322200cc6e549ca64440198d8a9394c8880031bd4e729911000636a9ce5322200ccaf439ca644400195a87394c8880331b9517299110066362a2e53222000c6f535ca64440018daa6b94c8880332bd0d729911000656a1ae5322200087e87d9564440018b8e7b2ac8880021fa1c65591100062e398cab222000c5f65dcd64440018b8cbb9ac88800317dd463591100062e3a8c6b222000c6f65dc964440018d8cbb92c8880033318f725911000637b28e4b222000c6c651c96444001998c6392c8880021f60f75591100045fc22eab2220008df835d564440031b906baac8880023be09755911000476412eab222000c3f75dd16444001878ebba2c8880029760c545911063e2e398a8b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fc2ee6b222000c5c85dcd644400193f09b9ac8880031715373591100043fc2ae6b22200287
  | 16 => 0x3d91100062eba8c7b222000e1c5418f64440014bb073aec8880030fe1175d91100043fc1aebb222000c3d75d53644400587ceb2a6c88800b0f1d654d91100145fc3aa9b222000a5d83153644400187aea2a6c888002a7a0c54d91100054ec18a9b222000a3d87153644400187b0e2a6c88800387a0c54d91100051ec18a9b222000e1d83153644400143b062a6c8880330f9c054d91100661e380a9b22200287e85dcf64440010fb0bb9ec8880030f15373d91100061e2a2e7b22200287f87d4f64440010fb0fa9ec8880028fa1353d91100043fc3aa7b22200087d8754f644400147908a9ec88800317dcd53d911000e2e39aa7b222000a3c85d0f644418d87ceba1ec8880030f5d743d91100064fb9e87b222000a3e8590f644400147b0b21ec8880038754e43d911000c5fc3a87b222000a3f8550f64440014790aa1ec8883170f9d543d91100061ebaa87b222000c9d7350f6444001c3aa6a1ec8880028fa1443d91100051ec2887b222000b1d839d7644400147b0fb2ec8880028f60f65d91100054f41ccbb222000a9d83997644400155d0532ec888002ab60a65d91100054fc1acbb222000a9c83597644400155f04b2ec888002ab20965d91100051ec18cbb222000c3f65dcf6444001878cbb9ec8880030fd9573d91100061e32ae7b222000c9d73d8f644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100064eb98c7b222000e1f6518f6444001c38ca31ec8880032761c63d91100070f428c7b222000e1d8518f6444001c3cea31ec888003875d463d91100074ac08c7b222000a3e86d4f64440014790da9ec88800387d8f53d91100070e31ea7b222000a3e8654f64440014790ca9ec88800347dcd53d91100070fb1aa7b222000e1c6354f6444001d28c718ec888003a518d31d91100054f41cebb222000a9d839d76444001c3d073aec8880028f60e75d91100070ec1cebb222000a1d839d7644400187f0ebaec8880028fe0d75d91100061eba8ebb222000a3e85dcf644400147b0bb9ec8880030f9d773d91100061ebaee7b222000c3e85dcf644400187b0bb9ec8880028fa1673d91100051ec2ce7b222000c3e755cf644400187aeab9ec8880030fa1573d91100061ec2ae7b222000c9f835cf644400147d0a39ec8880028f61473d91100055b408e7b222000ab5811cf644400147f0fa9ec8880028f61f53d91100061fb9ea7b222000c3d73d4f644400117d0f29ec8880022f61e53d91100064fb9ca7b222000c9f7354f644400147f0ea9ec8880028f61d53d91100070fc1aa7b222000c3f7354f6444001c3ee6a9ec88800307dcd53d91100061eb9aa7b222000e1c7354f644400117d0
  | 17 => 0xc2000ae785d8821840015cb0bb104308242b9a136208610007332a6c410c2000e6454d8821840015cf07b104308002b960f620861000733a9ec410c2000e6553d882184001d4e87b104308003a950f620861000771406c410c2000a778558821840016cb0a3104308002f8a006208610485724368410c2000ae68610821840254790ab2481080368f21564102100665b322e220420009e4825c440840012bb073a6ca880021fa1b73d95100143fc3ec7b2a2000c5d73d8f65440010fb0f31eca880028fa1263d95100051ec24c7b2a2000a6e8298f65440014db0531eca880021fe1d63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d95100443ec38c7b2a2000a3e8418f654400147b0831eca88003175cc63d95100062ec38c7b2a2000e1e8418f6544001c3b0831eca88003179d063d95100072ac08c7b2a2000a3e86d0f654418d87ceda1eca8800387d8f43d95100070e31e87b2a2000a3c8650f654418b87ceca1eca8800347dcd43d95100070fb1a87b2a2000e1c6350f6544001ca8c718eca880039518d31d95100052f41ce9b2a2000a5d839d3654401987ce83a6ca880030f5d074d95100643f426e7b2a200087d879cf654400147d0939eca880028f61273d95100643e422e7b2a2000c5f835cf65440010fd0e39eca880028fa1073d95100051ec20e7b2a20cfa76811cf65440014eb0239eca880321fe1f43d95100661f3a687b2a200cc3c74d0f654401987f0fa1eca880330f21f43d95100061fb9e87b2a2000c3d73d0f65440010fd0f21eca880021f61e43d95106751ec2487b2a2000c5f7390f65440010ff0ea1eca880021f21d43d95100661f3a287b2a2000c5f7350f654400187f0ea1eca880030f21d43d95100070fc1a87b2a2000c3f7350f6544001c3ee6a1eca8800307dcd43d95100061eb9a87b2a2000e1c7350f65440010fd0e21eca880021f61c43d951066d1f42087b2a2000a77815cb65440114e902b96ca880021fa1f32d95100043ec3e65b2a2000a3e84ccb654400147b09996ca880029da0732d95100053ac0e65b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a2023a7a80dc765440010fd0f98eca880021f61f31d95100051f42663b2a2000a3d84cc765440014dd0598eca880029b60b31d95100043f43863b2a200887d870c7654400147d0818eca880028f61031d95100051f426e1b2a2000a3d84dc365440474ed03b86ca880021fa1f30d95100043ec3e61b2a2000a3e84cc3654400147b09986ca880021fa1c30d95100443ec3861b2a2000a3e840c3654400147b08186ca880029ba0830d951000536c1061b2a2000a76810c365440014eb02186ca880221f61f65d91100051f426cbb222000a3e84197644400163b062a6c888003179d46
  | 18 => 0x40010ff06baec9080029760c54d92100143f42ee7b24200087d85dcf64840011dd05b9ec9080023b60b73d92100143fc3ea7b24200087d87d4f64840010ff0ea9ec9080021f61d53d92106361f3ae87b242000c3d75d0f648400317f0ea1ec9083170f9d543d92100061ebaa87b242000c9d7350f6484001c3aa6a1ec908002ad20543d9210006373ace5b242000c6d759cb64840018d8a9396c9080031bd4e72d921000636a9ce5b242000caf439cb648400195a87396c9080031b9d572d921000636baae5b242000c6c545cb64840018dea6b96c9080031b54d72d921000657a1ae5b242000cad435cb64840019cce4b8ec90803327d0d739921000e2f39aa73242000c5d7354e6484001c3aa6a1cc90800a1fa1672992100043ec2ce5324200287e87dd564840010fb07baac9080021fa1c75592100052ec18a8b24200087f855cd64840050f90ab9ac9080021fa1f53592100143e43ea6b24200087e8754d64840010f90ea9ac9080030fdd743592106361e3ae86b2420018bc8750d648400187eeaa1ac9083170f1d543592100064fb9a86b242000e1d5350d648400117f0eb20c90803327d0d731921000e2f39aa63242000c5d7354c6484001c3aa6a18c9080021fe1572192100143e42ae43242000a6e829da54840014db053b4a9080021f61f649521000537416c92a42000a6d82d9254840010ff0eb24a9080322fa1375d8a100045ec26ebb14200087f855d362840050f90aba6c5080330f9d054d8a100061eba0a9b142000a5d831536284001c3aa6a1ec5080322fa137598a100045ec26eb314200087f855d262840050f90aba4c5080330f9d05498a100061eba0a93142000a5d831526284001c3aa6a1cc50800a3b61e5298a1000c76c3c65314200c87e84dd562840010fb07baac50800a1fa177458a100043ec2ee8b14200087e8795162840190f90f2a2c5080021fa1c5458a100643e438a8b142000a5d8315162840010ff0ab9ac50800a1f2157358a100043f43ea6b14200287c87d4d62840010fd0ea9ac5080021f21d5358a100061fbae86b1420c6c3c75d0d628400187eeaa1ac5083170f1d54358a100064fb9a86b142001c9c7350d6284001c3aa6a1ac50800b1b1d65258a100147643aa4b1420018ec874c96284003998e6992c5080023be1d6218a1000636baac4314200287e859db42840010fb0b3b6850800a1fa177690a100043ec2eed214200287e859d942840010fb0b3b285080021fe157650a100143e42aeca14200087f855d842840050f90abb085080022fa1e64506100045ec3ec820c2000c6d7598b21840018daeab1643080029de1562c86100053bc2aec10c2000ae58299021840011eb0e3204308002d961672086100047ac3ec410c20009e587d8821840017c501b104308002b961f620861000672c3ec41
  | 19 => 0x21fe0d75d93100052ec18a9b26200287e85dcf64c40010fb0bb9ec9880023ba0b73d931000476c16e7b26200287f87d4f64c40010fb0fa9ec9880021fe1d53d93100043ec3aa7b2620c6c3e75d0f64c400187aeba1ec9880062fe1d43d931062e1f3aa87b262000c3d7550f64c400193ae6a1ec9880038754d43d93100051f42ec93262000b1d8315264c401917908bacc9880330f15173993100664fa1ae7326200ca3c84d4e64c401947908a9cc988007179cd53993100062eb9aa73262000a3c8550e64c4001c3aa6a1cc9880021fe1572993100143e42ae5326200ccac425ca64c401987eec2a2c988002c760c54593100143f43eeab262000c3d84dd564c40010fb07baac9880021fa1c75593100051f42ee8b2620008be87d5164c400187eebaa2c9880029760c54593100061fba8a8b262000a9d8315164c400147d0e2a2c9880030fa1c54593100070f418a8b262000a3d8315164c4001c3b062a2c9880028760c54593100061e2a6e6b26200087f855cd64c40050f90ab9ac9880030f15173593100043f43ea6b26200287c87d4d64c40010fd0ea9ac9880021f21d53593100051e422a6b262000a3c85d0d64c400187eeba1ac98831b0f1d7435931000c5e43a86b262000a3c8550d64c400187eeaa1ac9883170f1d543593100064fb9a86b262000e1d5350d64c400117f0eb20c98803327d0d731931000e2f39aa63262000c5d7354c64c4001c3aa6a18c98800a1fa1672193100043ec2ce43262000c3e745da54c40010fb0fb24a9880021fe1d64953100061f3a2c92a6200c87c845d662c40010ff06bacc5880021fe157498b100143e42ae9316200c87f8795262c40010fb0f2a4c5880321fe1c5498b100043ec38a93162000a5d8315262c40050fd0bb9cc5880021f6177398b100143fc3ea7316200087d87d4e62c40010ff0ea9cc5880021f61d5398b106361f3ae873162000c3d75d0e62c418b87ceaa1cc5880030f5d54398b1000e4f39a873162000c9d7350e62c4001c3aa6a1cc588007359cd3198b100143f42ee8b16200087d85dd162c40014bb062a2c5880038754d4358b1000477c3ac4316200c8be84dd462c400117b09ba8c5880021fe157418b100143e42ae8316200cc3e7415062c400187ae82a0c5880029760c5418b100070ea9a8631620018f5878c462c40010ff0abb6858800a1f21576d0b100143f42eed216200087d85dda42c40050fd0a3b485880021f6147690b100061f3acc92162000c3e7559242c40010ff0abb2858800a1f2157650b100143f42cec216200087d859d842c400187ceb32483880030f9d5649071000536c2cc510e2000a6d8598821c402547d0bb2481880022fa1e64503100061e3acc8a062000c3c7559140c400117b0fb2081880368fa17641031000477416ebb2420008ed82dd7648
  | 20 => 0x6e41aec10a80008be869d02150001878cb3a042a00030f195740854000572c10c210a8000ae68648421500015c90c90842a000399d9521085404373232a4210a800c87c865d640500190fb0fb2c80a00338ed8254901400951e432eb2028012a3e86d96405002387cedb2c80a00038ed9760901400070ea9a87308800287e859ca61100010fb0b394c2200323d61e519844000c7ac3c6330880a4d2c54dc96110121a58a8392c220243391847258440486d2208e4b08800087d83dd561100011df04baac2200023b20975584400043fc2ae6b08800287c855cd61100011df04b9ac2200023b20973584400043f43ea6b08800287c87d4d61100010fd0ea9ac2200021f21d53584400061fbae86b0880c6c3c75d0d611000187eeaa1ac2203170f1d543584400064fb9a86b088000e1d5350d611000156902a1ac2200031bdd77258440006363aee4b0880a4c6e54dc961101498d8a9b92c2200031bd4f725844000636a9ee4b088000caf43dc9611000195a87b92c2200031bdd47258440006363a8e4b088090ce7711c961101218dca8392c2202431b150725844000637a98e4b088000c6d531c9611000195e86392c2200032b50c725844048673a08e4b088090ce4411c961100058e8eb28ac220003391ca51584400647a43aa2b08800cab48454561100019c8e4a8ac220003391ca315844000c7a43a62b08800cab4844c561100019c8e498ac2200332d9c5769044006c9fc3aeb20880a4d2c54dc94110121a58a839282200364fa1672104400655bc3ac22088000cb7875844110001c6f0ab0882200038d21561104400665bb9ac22088000cb5735844110001c6ea6b0882200038d54d611044000753c12c22088000ea482584411001b2790ab80822000a1fa1776884400043ec2eed108800c93c845d6211001b2790aba442200031d5d661884400063abaac31088000ae4825862110001878a9bb242200021fe1576484400143e42aec908800d93e85dd12110019968e8b0a4220002b920961484400043fc2aec108800287c855d82110001878a8bb042200022f61b740844006c9f42ee81088000cb57610421101215c90c908422000339dd9210844000672bb2421088090ba48448421101a1e48a890842200364fa1671d00400963cbb2eb200800cb38845d640100cb6750b20c80200330f95376500400661e2a6eca008000c3c75dd9401000117f07bb280200022f60f76500400061fa9eeca008000c3d53dd94010001974a1bb280200032e543765004006c9f43eeaa008000c3f76dd540100018f0ebbb280200338e95376500400663d2a6eca00800ccba54dd94010019874a9bb280200032e55376500400663c2a6eca008000c7b53dd940100018f2a7bb280200031eddb75500400659c426eaa008000b3985dd140100cba70ebba280200
  | 21 => 0x8648421900015cb0c908432021b99995210864000732b2a4210c8000ba48448421901a7e48a890843200030f99576d02400061ebb2cba04801293e859c740900018f4cabb681200334e95176d02400063cbb2cba04800087e86dcf65500050ff0fb1ecaa0003175cf63d95400043ec3cc7b2a800087f8758f65500014ef02b1ecaa00029d20563d954008c3ec38c7b2a8000c5d7318f655018d87ceda1ecaa03170f9d943d95400068fb9a87b2a8000e1f6350f6550001c38c6a1ecaa01869ea0374d95400643f426e7b2a800087d879cf655002347d0939ecaa00028f61273d95400643e422e7b2a8000c5f835cf65500010fd0e39ecaa03468fa1073d95400051ec20e7b2a800c87f87d0f65500190f90fa1ecaa00330f9d343d95400661e3a687b2a800cc3f87d0f65500198790fa1ecaa00030fdcf43d95400061eb9e87b2a800087e8790f65500010fb0f21ecaa034a8f61243d95400062fb9c87b2a80c787f8750f65500450f90ea1ecaa00330f9d143d95400661e3a287b2a8000c5f7350f655018f87f0ea1ecaa008b0f21d43d95400070fc1a87b2a8000c3f7350f6550001c3ee6a1ecaa000307dcd43d95400061eb9a87b2a8000e1c7350f65500010fd0e21ecaa00461f61c43d954068d1f42087b2a8000a6f825c765500014d904b8ecaa00021fa1f31d95400043ec3e63b2a8000a3e84cc7655000147b0998ecaa00029ba0b31d954000536c1663b2a800087e870c765500010fb0e18ecaa00028fa1031d95400051ec2063b2a8061a3e84dc365500010fd0f986caa00021f61f30d95400051f42661b2a8000a3d84cc365500010fd0e186caa00461f61c30d95400051f42061b2a8000a3d840c365500014ed02186caa00029d60430d95400663db04ed2a2800cd38409da54500014bb062a6c2a00038754d43d85400043fc2ae5b0a800287c855cb61500015cd0598ec2a0002ad61031d85400143f436eab0a800087e87d9561500018b8e7b2ac2a00021fa1c65585400062e398cab0a8000c5f65dcd61500018b8cbb9ac2a00031bd9772585400063632ee4b0a8000c6f651c961500018d8ca392c2a00023de1d61185400056a41ac230a8000ae48258461500014bb062a0c2a00038754d43185400143f42ce430a800087d859c8615000156b09988c2a0002b9a0b31185400043e432eb20a800087d87d9641500010fd0dbaa82a00021fa1f655054000637b2ee4a0a8000c6c65dc941500018deca39282a00031b194725054000672396c2a0a8000ce4721854150001c6ecaa0882a000a1f21676885400043fc2aed10a800287c855da21500050fd0a3b442a00021f61476885400043e432eb10a800087f87d9621500010fb0fb2c42a000a1fa1776485400043ec2eec90a800087f855d821500050f90abb042a000237e0d760854000c
  | 22 => 0x39acb2004a8fa1f43596400951e43e86b2c8000c3f73d0d659000187ae7a1acb200021fa1e43596400043ec3c86b2c80d9a3d8490d65900018bae721acb2008a1fe1d435964063c3e43a86b2c8000c5d7350d659004587f0ea1acb200028fa1d43596400051e43a86b2c80c7c3c8750d6590001c3f06a1acb200030fdcd43596400070f39a86b2c8000c3d7350d6590001c3ae6a1acb20003075cd43596400943f43886b2c800087d8710d65901b147d0821acb200029ba0b715964000536c16e2b2c80d7a3e849c5659000147b0938acb200031ddc671596400051fc22e2b2c80d6a3c845c565900010fd0f98acb200021f61f31596400051f42662b2c8000a3d84cc565900014dd0598acb200029b60b31596400043f43862b2c800087d870c5659000147d0818acb200028f61031596406ad1f424e0b2c800cc3c749c165900250fd0f982cb200021f61f30596400051f42660b2c8000a3d84cc165900010fd0e182cb200021f61c30596400051f42060b2c8000a3d840c165900014ed02182cb200029d60430596400663d302ed2a4800cd3b405da549000127b0e2a6c320002c760c54d86400063732ce5b0c8000c6d659cb6190001a58a9396c3200031b99572d864000636b2ae5b0c8000d2c545cb619000163b062a4c3200038d153619864000573416c330c8000a5d831526190001c3aa6a1cc32000a1fa1672986400043ec2ce530c80018f5878c6619000163b062a2c3200029760c54586400062fb9aa6b0c8001c5c7354d619000193ee7a1ac3200038754d43586400143f42ee4b0c800087d85dc961900031e90e98ac320007351cd31586400143fc32ea30c800087d8799461900010ff0eb28c3200024f61c54186400058ec18a830c80008f78758461900010ff0cbac83200021fe1d65906406a49ec3ca920c8000e36545864190001a70a938483200034e95170906400949fc3aeb20c800093f875964190001c6acab0c83200034e9d670906400069cbaae120c800087d86dd541900010f90eb2a83200031b997725064000636b2ee4a0c8000d2c54dc941900018dcca39283200031b5947250640006962a0e4a0c8000e345498541900019c8e530a8320003391c961506400069c2a0e0a0c801293e859c841900252790ab80832000a1fa1776886400043ec2eed10c80018de83dda21900011bb07bb4432000a1fa1676886400043ec2ced10c800287e855da21900010ff0cbac43200324f21175886400043fc3acb10c800087d8759621900192790b3a4432004a4f21574886400061e2a6ec90c800287e851d921900010fb0a3b243200030f15076486400949f42ee890c8000c3e65dd1219000187cca3a2432000a1fa1676086400043ec2cec10c8000c3c549d82190001878a8bb0432004a4fa17740864000572c14c210c8000ae7
  | 23 => 0x580210061fba8e8b004200c3c751d1600841987f0a3a2c0108330f21474580210045ec18e8b00420087e8795160084190f90f2a2c0108030fdd254580210661e3a4a8b004222c5c7395160084010fd0e2a2c0108321f21c54580210061fba0a8b00420cc3c7415160084014bb062a2c010b1f171cc54580210062fbaee6b004200c5c75dcd600840193ee9b9ac010803271d373580210062fc2ee6b004200c5c85dcd600840193f09b9ac0108032721373580210062f2a6e6b004200c5c54dcd60084010ff0ab9ac01080a1f21573580210045fc22e6b00420c8bc845cd60084018beea39ac010803171d473580210064fba0e6b004200c9c741cd60084010fd0fa9ac01080a1f21f53580210061fba6a6b004200c3c74d4d60084018bee7a9ac010807171cf53580210043f43aa6b00420087c8754d600840187ee8a9ac0108030f1d153580210062fb9aa6b004201c5c7354d600840117d0fa1ac0108322f21f43580210061fbae86b0042c6c3c75d0d600840193ee7a1ac010807271cf43580210045f43a86b0042008bc8750d600840187eeaa1ac010b170f1d543580210064fb9a86b004201c9c7350d6008401c3aa6a1ac010807351ce315802100e6a39a62b004201cd8738c16008401da463182c0108063e21d3058021004f3c3a423004286d66754846008401acaea908c010803699d12118021006d2ba2423004285dc6734846008401b8ae6908c0108023ee1d60180210066cb9ac0300420087f835d661d00050fd0bb9cc3a00021f61773987400143fc3ea730e800087d87d4e61d00010ff0ea9cc3a00021f61d53987406361f3ae8730e8000c3d75d0e61d018b87ceaa1cc3a00030f5d543987400064eb9a8730e8000e1d5350e61d0001c3aa6a1ac3a000a1fa1772587400043ec2ee4b0e800287e85dda21d00010fb0bbb443a00029b61662887400143f42eec90e800087d85dd921d00050fd0bbb043a00021f61776087400053ac2cc210e8000ae58298421d00015cf0c90843a0002b961921087400043fc32e6b2c800c93c845cd65900010fd0fb1acb2036f0f1d363596400943f43cc6b2c8000c5f7398d65900050fd0eb1acb2036f0f1d163596400062fb9ac6b2c800087e8718d65900014ed0231acb200029d60463596400649e43e86b2c80c6c3f76d0d65901b72790ea1acb203170fdd943596400068eb9a86b2c8000e1e6350d6590001c3ac6a1acb2004a8fe1174596406ad3dc02e8b2c8000c3f74dcd6590001878e9b9acb200030fe1373596400061e426e6b2c800087d879cd65901b147d0939acb200028f61273596400062fb9ce6b2c8000a3f845cd65901b547908b9acb200030fdd173596400061e3a2e6b2c8000c3f845cd659000187908b9acb2000317e0d73596400043f438e6b2c8012a3e841cd659000147b08
  | 24 => 0x842009e585dd92108401acb0bbb24210802596177648421484f3426ec9084200d6454dd921084013cf07bb242108027960f7648421006b3a9eec9084200d6553dd92108401b4e87bb242108036950f7648421004f3406ec9084200ce687dd92108401ccd0bbb24210803996177648421007322a6ec9084200e6753dd92108401ccaa7bb24210803a9d0f764842100752a1eec9084286b6685dd121084016cb0bba24210803c9153744842100572c34e890842009e5869d121085219cb0d3a24210a4279e167448421004f2c2ce890842909e6849d12108521ac8a93a24210a4279e0e7448421004f2c1ce89084200d67539d12108401acaa73a24210a4369d0e7448421006d2a1ce890842009e6809d121084015cf0cba24210802d9e157448421435b242ae89084200da5741d12108401e48a83a24210a4279e147448421004f2c28e89084290da6841d12108401b4ea83a24210a43591507448421486d22a0e89084290d24541d121085213cf063a242108027960c7448421006b3a98e89084200d65531d12108521b4e863a242108036950c7448421004f3400e890842009e687d91210850d6cd0bb224210802d96176448421484f243cc89084290da4749912108401e48a93224210a4279e1d6448421004f243ac89084200b6785591210850d6c90ab224210803691d16448421007922a2c890842009e6871912108521acf0f2a24210a435921e5448421006b3bb4a89084200e6776951210850d6cd092a24210a1bc9a125448421486b33a4a89084290d647495121085bd6cf072a24210b7ad960e54484216eeb3b9ca890842ddd657395121085b9e4e872a24210b73c950e544842100572c34e09084200ae7865c121084016cf0ab824210a1ad92157048421005d3c22e09084200ba4845c1210840178f06b824210a16f120d7048421435b3428e09084200b65851c121084013cf0a382421080359a147048421004f2c28e09084200d65851c121084012cb0a3824210a4279a107048421006b32a0e09084200d64541c121084013cf0638242108027960c7048421006b3a98e09084200d65531c12108401b4e8638242108036950c7048421004f3c3a43b0042009e48748660084017c10090cc0108022fe1175980210645e422eb300420087f855d260084050f90aba4c0108330f1d054980210052ec18a93004200e1d5350e60084031f30f184c0108027921d2158021006b3baa42b004286d64754856008401b4ee890ac010803691d12158021006e3b9a42b004285dc47348560084017c10090ac0108321fa1375580210043ec1eeab0042008bf845d5600841917908baac01080237e0d755802100c6e41aeab00420287e85dd160084010fb0bba2c0108030fdd774580210061e3aee8b004200c3e85dd1600840187b0bba2c0108022f60f74
  | 25 => 0x4014bb062a2c8108030fdd454590210054ec18a8b204200a3e87151640840187d0e2a2c81080387a0c54590210051ec18a8b204200e1d83151640840143b062a2c8108030f15373590210043fc2ae6b20420287c855cd6408401878a8b9ac8108023d20573590210047dc02e6b2042008f8805cd64084010fd0fa9ac81080a1f21f53590210043f43aa6b20420087c8754d640840147908a9ac8108028f21743590210061fbae86b2042c6c3c75d0d64084031790ea1ac8108028f21543590210061fbaa86b2042c5c3c7550d640840193ee6a1ac8108038754d43590210055a40a86b204200c77751c564084018e8ea38ac8108038d150715902100672390e2b204200c3c541c1640840117f0eb20c81083327d0d731902100e2f39aa63204200c5d7354c6408401c3aa6a18c81080a1fa1671190210043ec2ce2320420087f855c064084050f90ab80c8108030f9d176950214853a40aed2a04290c74715da54084010fb0fb24a8108021fe1d64950210061f3a2c92a0420087f855db41084050f90abb682108025de1576d04214871a2a2c9a084200977855cb41084012eb0b38682108027960a70d04210143f42eed208420087d85dda410840187ceb32482108030f9d564904210143f42cec208420087d859d841084012db0b3908210a431d95176104214863a2a2ec2084200c77535d841084018eaa6bb082108032dd0d76104210065aa1aec2084290ce7425d841084011ef0eb208210a438d951641042148572412c82084290ea44259041084016cb0b39082108023de197210421004f3c32e42084200ce7865c841084013cf0ab908210802796157210421486b32a2e42084290d64545c841084013cf06b9082108027960d7210421006b3a9ae42084200d65535c84108401b4e86b9082108036950d7210421004f2402e42084219c75765d621085212e908bac42108025de0d7588421004bac1aeb1084200d37435d62108401a6a86bac4210a3359a097588421006b2c12eb10842dfc76625d62108401acc64bac4210803594c97588421004bac28e910842009d5831d221085212ef0f2a44210a23595ca5488421006b2bacc51084200d6575d0a2108521b4ce9a144210803595d442884210143f42eec908420087d85dd921084012eb0bbb242108031da1776484210063ac2eec9084200c7454dd921084018eea7bb242108031d54f76484210065ba1eec9084200cb543dd921084011eb0d3a24210a434d15074484210063bbb4a89084286b668598921084016cb0b3124210a43691d34248421004f343c849084286b668590921084016cb0b21242108027921d4248421005b3c2a849084286b64855092108401b48e8a1242108025d6147048421435b342eec9084200b6585dd921084019cb0dbb2421080279e177648421006b342eec90
  | 26 => 0x23de0575591210061e3aee8b224200a5d8315164484010ff0ab9ac89080a1f21573591210047bc0ae6b2242008fb805cd64484011f100b9ac8908021fa1f53591210143e43ea6b22420087e8754d64484010f90ea9ac8908030fdd743591216361e3ae86b2242018bc8750d644840187eeaa1ac890b170f1d543591210064fb9a86b224200e1d5350d64484018eeebb8ac8908031d1d771591216263a2a6e2b224200c7753dc564484018eaa7b8ac8908032dd0f71591210065aa1ee2b22420287e859d864484010fb0b3b0c8908022fe1d64191210051e42ac83224200b1d83150644841917908ba8c8908328fa1754191210661e2a2e6322420cc9f435cc644841947909a98c8908328f211531912100e2f39aa63224200c5d7354c64484014790aa18c8908038754d43191210661e2a4e0322420087f855c064484050f90ab80c8908030f9d276951216253bc0aed2a2420087d87d92544840187ce9b24a8908021fe1d64951216253bc0ac92a2420ccac645cb41484010ff0abb2829080a1f21576505210061e3aec8a0a4200c3c751914148401958c9b92829080a1fa1676105210043ec2cec20a42a4e2c54192214841917d09baec0908022f61375d81210043fc2ae9b02420287c855d3604841987ce82a6c0908030f5d054d81210052ec18a9b024200e1d5350f604840127908ba8c0908023ee1d60181210045fc22ea302420c8bc845d4604840147908ba8c0908030fe1175181210643e422ea3024200c3c845d4604841907908ba8c0908021fe0d75181210043fc2ae8302420287c855d060484190ff0f2a0c0908021f61e54181210643fc38a8302420087d871506048419878e82a0c0908029760c54181210143f42ee6302420087d85dcc60484050ff0fa98c0908021f61f53181210043fc3aa6302420087d8754c604858d87ceba18c0908030f5d7431812162e1f3aa863024200c3d7550c604840393ce6a18c090803275cd43181210070ea9a863024200c6d7588460484010ff06baec8108029760c54d90210143f42ee7b20420087d85dcf64084050ff0fa9ec8108021f61f53d90210043fc3aa7b20420087d8754f640858d87ceba1ec8108030f5d743d902100c5fc3a87b2042c5c3e7550f640840187aeaa1ec810803275cd43d90210070ea9a87b204200a3e85d92640840163b062a4c8108322f21175990210661e2a2e7320420cc9f435ce640841947909a9cc8108328f211539902100e2f39aa73204200c5d7354e64084014790aa1cc8108038754d43990210143f42ce1320420087d859c26408419878a9384c8108330fdd854590210058ec18a8b20420287e87dd5640840187b09baac8108021f60f75590210047a40aeab20420087e871d5640840147d0bba2c8108022fa1f54590210061fbaea8b204200ab681d516408
  | 27 => 0xeb9ea6324420087f8754c64884010fb0ea98c910807179cd53192210062eb9aa632442c5c3e7550c648840187aeaa18c910807279cd43192210064eb9a863244200e1d5350c64884010fb0f3b4a9108321fe1976952210643f422ed2a4420c87c845da54884010ff06bb4a9108021f60d76952210061fa1aed2a44200c3d435da54884018df04bb4a910a931b209769522152637a12ed2a442a4c6c425da54884010fb0fb24a9108021fe1d64952210063ab2ce3a144200c75655c74288549c5ca8b2685108038b59564d0a21004b7c2ae3a144290ae7865c742884012db0b38685109021fe197590a210cc3fc3acb214420ca3c8459642884010fb0dbaa85108021f21d6550a210063b32ee2a144200c7565dc542884018ecca38a85108031d5947150a210065b320e2a144200cb5641c5428841947908b2885108038b5954210a2152596422ca21442008ed87d90428841947908b2e83108021fe1975906210043fc3acb20c421f87d86dd541884330f90eb2a83108328f21165506210063732ee4a0c4200c6d65dc941884018dcca39283108031b5947250621004b6c2ce420c421987f8759721884018eccabb643108031d9d576c86210063abb2eb90c4200c757659721885434ef0eb2e43108029d61d65c86216253a422cb90c4200a778359721884014eb06b2e43108038dd0d65c86210071aa1acb90c428cc767259721884014eb0a3264310802b560c64c86216253bc34a990c4200c5e7399760884018bce6b2ec1108030f99674d82210061eb2ce9b044200c3e655d3608840187acaba6c1108031799573d82210062eb2ae7b04420087f855d260884050f90aba4c1108029760c54982210070ea9a8730442008bf845d5608841917908baac11080a1fa1774582210043ec2ee8b044200c3f741516088419878e82a2c1108029760c54582210070ea9a86b04420287f865d460884010fb0f328c1108021fe1d65182210047dc3ac03044200b1d83153644840187f08baec8908021fe0d75d91210061ebaea9b224200a5d83153644840187aea2a6c890802a760c54d91210051ec38a9b224200c3d871536448401c3d062a6c8908028f60c54d91210070ec18a9b224200a1d8315364484050fd0bb9ec8908021f61773d91210061e2a6e7b224200c3c545cf64484050ff0fa9ec8908021f61f53d91210043fc3aa7b22420087d8754f644840147908a9ec8908028f21743d91216361f3ae87b224200c3d75d0f644840317f0ea1ec8908028f21543d912162e1f3aa87b224200c3d7550f644840193ae6a1ec8908038754d43d91210061e2a4e1b22420cc9f435ce64484038bce6a9cc890803175cd53991210070ea9a87322420087f855c664484050f90ab8cc89080a1fa1670991210043ec2ce1322420087d83dd5644840117f08baac89080
  | 28 => 0x750d65884018790ea1acb1080387e0d43596210061fb9a86b2c4200e1e7350d658840187ae6a1acb10803875cd43596210060eb9a86b2c420087e8710d65884010fb0e21acb10b868fa1043596210051fc22e4b2c4200a3c845c965885bf4ef02b92cb108021fa1f32596210043ec3e64b2c4200a3e84cc9658840147b09992cb108029da0732596210053ac0e64b2c4200a77814c965884014e902992cb108661fa1c32596210043ec3864b2c4200a3e840c9658840147b08192cb108028fa1271596210051ec24e2b2c42dfa6e829c565884330fd0f98acb108021f61f31596210051f42662b2c4200a3d84cc565884014dd0598acb108029b60b31596210043f43862b2c420087d870c5658840147d0818acb108028f61031596210072a98862b2c4200a3f845c1658840147908b82cb108029be09705962170536412e0b2c420087e87cc165884010fb0f982cb108028fa1330596210051ec2660b2c420087e870c165884010fb0e182cb108028fa1030596210051ec2060b2c4200a6e820c165884014db04182cb108029da0430596210053ac0860b2c420087f835d764884014bb062a6c91080a1fa1773d92210043ec2ee7b2442008fa80dcf64884011f301b9ec91080a1fe1f53d92210043ec3ea7b24420087f8754f64884010fb0ea9ec910b1b0f9d743d92210061ebae87b2442018bf8750f648858b87ceaa1ec9108030f5d543d922100e4f39a87b244200c9d7350f6488401c3aa6a1ec9108031d9d671d92210063abace3b244200ce5729c7648841947d0932cc9108328f21165992210043fc2ae7324420287c855ce648841993e86b9cc9108321fa1f53992210643e43ea7324420c87e8754e64884190f90ea9cc910807179cd53992210062eb9aa7324420cc3f7550e6488419878eaa1cc91083327dcd43992210070ea9a87324420287e859c264884010fb0b384c9108021fe1570992210143e42ae13244200a3e8499564884330f90eb2ac9108028f21165592210143f43eeab24420087d83dd564884010fd0e3aac9108029760c54592210043fc2ae6b24420287c855cd64884010fd0fa9ac91080a1f21f53592210043f43aa6b24420087c8754d648840187eeba1ac910b1b0f1d7435922100c5e43a86b244200c3f7550d648858b878eaa1ac91080327dcd43592210070ea9a86b244200c6f75dc964884018d8ebb92c9108021f61e65192210062f39cca324420087f8759464884018bce6b28c9108022fe1d64192210062f32ae63244200c5d655cc648841993cc8b98c9108032759173192210643e422ea324420087f835d4648841987e86ba8c91083327d0d73192210062f42ae63244200c5d855cc648841993d08b98c9108331795173192210662e2a2e6324420287f87d4c64884010fb0fa98c910807179cf53192210062
  | 29 => 0x12c0a08023ee1d60181410056c41ac0302820c8bc845d460504014bb062a0c0a08038754d43181410055a40a86302820087f855c860504050f90ab90c0a0802ae61330181410043fc1aeb310820287e85dce62104010fb0bb9cc42080a1fe1f53988410043ec3ea7310820087f8754e62104010fb0ea9cc420b1b0f9d743988410061ebae8731082c5c3e7550e621040187aeaa1cc420803275cd43988410070ea9a873108200e1d5350d62104050fd0a382c4208021f61470588410661e2a2ed2108220c75765d6411041987ca9bb282208330f1537650441486962a0e4a088200c3c75dd9411040117f07bb282208022f60f76504410061fa9eeca088200c3d53dd9411040196ca3bb282208032d54776504410061fbb6eaa088200caf76dc9411040195eec39282208034b1d472504410063a3aeeca08820ce3654dd941104198eca9bb282208332d95376504410661b2a6eca088200cb554dd941104198e8a9bb282208031dd4f76504410063aa9eeca088200c7776dd5411041966909baa8220802cd617745044100673bb6e4a0882a4f2654dc941104019ceec392822080359dd47250441006b23a8e4a088290f26541c94110521b4cc83928220a43599507250441486b22a0e4a088200d67531c94110401acaa63928220802cd61642504410070ea9a87300820087f855ca60104050f90ab94c02080237e0d729804100c6e41ae5300820087d83dd5601042517f08baac0208021fe1573580410143e42ae6b0082008ef825cd60104011d904b9ac0208021fa1f53580410143e43ea6b00820087e8754d60104010f90ea9ac0208030fdd743580416361e3ae86b008200c3f7550d601058b878eaa1ac02080327dcd43580410070ea9a86b00820095d831d165884010ff0cb9acb108021fa1f63596210cc3f43cc6b2c4200a3e8498d658840147b0931acb1080317dce63596210143f43ac6b2c4200c5f7358d65884010fd0e31acb108028fa1063596210051ec20c6b2c42c6c3f76d0d658858b87eeca1acb10803475cd43596210070f31a86b2c4200e1d6350d65884334df0cb92cb10802cb21172596210072731a64b2c4200c3f749d165884014df04ba2cb10a9a9b20974596210661f3a0e8b2c4200a5e831d165884014bb063a2cb108321fa1373596210043ec3ce6b2c4200a3e849cd658840147b0939acb10b8e9ba0a735962100536c14e6b2c420c87c845cd65884018bf06b9acb108021fa1c73596210051f420e6b2c4200a3d841cd65884190f90fa1acb108330f9d343596210661e3a686b2c420cc3f87d0d65884198790fa1acb108030fdcf43596210061eb9e86b2c420087e8790d65884010fb0f21acb10b8a8f61243596210062eb9c86b2c420087f8750d65884010f90ea1acb108330f1d143596210062eb9a86b2c4200c3f8
  | 30 => 0x89410057340c863128200ae58190c62504014df0aa18c4a08029b2154318941007172a2863128200e2c5450c6250401c9aa6a18c4a0802b9e0543189410057240a863128200e2f8550c6250401c590aa18c4a0803a3e0d431894100717a9a863128200e8e5350c6250401c5aa6a18c4a0803a354d431894100706a9a863128200ea78150c6250401d4902a18c4a08029ba14431894100536c28863128200a6e85dc462504014db0bb88c4a0802b3a0f711894100566c1ee231282008ee87d4462504011db0fa88c4a080399d46511894100557c22a23128200aac8454462504014df0aa08c4a08029b21541189410047743e6231282008ed87cc462504014dd0b988c4a08029b617311894100557426623128200aad84cc462504014dd0a188c4a08029b614311894100557420623128200aad840c462504014df0ab80c4a08029b215701894100557c22e03128200acf835c0625040159906b80c4a0802b9e05701894100537428e03128200a6d851c0625040155b08380c4a0802b3a0c701894100566c18e03128200ae5811c0625040155f08a80c4a0802ab211501894100573408a03128200ae58114062504014dd0b980c4a08029b617301894100557426603128200aad84cc062504011dd0e180c4a08023b61c301894100537428603128200a6d850c0625040155d08180c4a0802ab610301894100573408603128200ae5810c06250521c58a831684a08021f21975909410043ec3ecb2128200c6e75d8a42504018daebb1484a08031b9d4629094100636ba8c52128200ce4629c642504010fd0fb2a84a08031dd9771509410063a32ee2a128200c77651c542504018e8ca38a84a08034d150715094100673b10e2a128200e676518b4150401cc8ca31682a0a439995062d0541487322a0c5a0a8200e675318b4150401ccaa631682a0a43a9d0c62d054100752a18c5a0a820c87c865d641504190fb0fb2c82a08338dd865490541006373aec520a8200c6d75d8a41504018dcea31482a08031b5d46290541007162a0c520a8200e2c6518a4150401c6ecbb0c82a08029760c54d81410070ea9a87b02820287e859cb60504010fb0b396c0a0802ae61030d814100578c0861b028200c6f659ca60504018d8cb394c0a08031bd9572981410063632ae53028200c6e75d8a60504018daebb14c0a08031b9d4629814100636ba8c5302820287e86dd5605043f0f90dbaac0a08021fa1f65581410062e39ecab02820087e8719560504018b8e632ac0a080317d9773581410062e32ee6b028200c6f65dc960504018d8cbb92c0a08031bd94725814100636328e4b0282008ee87d8960504018deebb12c0a08031b1d7625814100667b9ec4b028200ccc73d8960504011dd0e312c0a08031bdd46258141006363a8c4b028200ccf731896050401998e63
  | 31 => 0x8200a6c855c762504011dd0fa8ec4a08023b61f51d89410047743e63b1282008ed87cc762504014dd0b98ec4a08029b61731d89410055742663b128200aad84cc762504014dd0a18ec4a08029b61431d89410055742063b128200aad840c76250401d8a6218ec4a08029ba1770d894100536c2ee1b128200aad84dc3625040159d07b86c4a0802b360f70d894100572c0ee1b128200a6e859c362504014db0b386c4a0802abe1150d894100556422a1b128200a6e85cc362504014db0b986c4a0802aba1330d894100556c2661b1282008ee870c362504011db0e186c4a08029ba1430d894100536c2861b128200aae840c3625040155b08186c4a0802b9a0430d894100572c0861b128200c6e75d8a62504018daebb14c4a08021fa1f65589410043f438cab1282008ef8758862504014df0ab10c4a08029b21562189410052ec18a83128200e1d5350c62504015cb03a90c4a080a3b61e521894100556c24a43128200a6e85cc862504014db0b990c4a0802ab613321894100572c0e6431282018ed878c862504014dd0a190c4a08029b614321894100556c20643128200ccd730c862504010ff0ab80c4a080a1f21570189410046fc1ae031282018dc835c062504018dcedb28c4a08029b60f651894100476c3cca31282008ef8759462504018dcec328c4a08029b60c651894100537434a83128200a6e86150625040169b062a0c4a08023b61e63189410053742cc63128200a6d8598c62504011df0eb18c4a08029be1563189410053642ac63128200aeb8058c62504015d100b18c4a08029ba14631894100536c28c63128200a6e86d4c62504014d90da98c4a08029ba19531894100536432a63128200e2f65d0c6250401c58cba18c4a08038bd9543189410071632a863128200e8f6350c6250401e1aa6a18c4a0802e9205431894100557426ea3128200aad84dd462504015cd033a8c4a0802b960675189410053742ee83128200a6d85dd062504015cd03aa0c4a0802b9607541894100717aa4a83128200a6d8395062504015cf02aa0c4a0802b9205541894100567418a83128200acd831506250521c5d082a0c4a0a4393a0c541894100536c18a83128290e4d83150625040149b062a0c4a08029ba16731894100536c2ce63128200aae849cc625040155b09398c4a0802b9a06731894100572c0ce63128200a6e851cc62504014db0a398c4a0802aba10731894100556c20e63128200ccd731cc62505214dd09a98c4a0802aba12531894100556c24a63128290a6c8454c6250401c9f06a98c4a0802aba10531894100556c20a63128290a6f85d0c62505214d90ba18c4a0a438b9534318941487162a6863128290e2f85d0c6250521c590ba18c4a08038bd4f431894100716a9e863128200a6e8590c62504014db0b218c4a08039354e431
  | 32 => 0xcd47d0821ecaa08029de0572d95410fd3a40ae5b2a82e5a3e841cb655040147b08396caa08021fa1f32d95410043ec3e65b2a8200a3e84ccb655040147b09996caa08029da0732d95410053ac0e65b2a820087e870cb65504010fb0e196caa08028fa1032d95410051ec2065b2a82aea3e84dc765504010fd0f98ecaa08021f61f31d95410051f42663b2a8200a3d84cc765504014dd0598ecaa08029b60b31d95410043f43863b2a821f87d870c7655040147d0818ecaa08028f61031d95410072a98863b2a82e4a3e84dc3655040147b09b86caa08021fa1f30d95410043ec3e61b2a8200a3e84cc3655040147b09986caa08021fa1c30d95410043ec3861b2a8200a3e840c3655040147b08186caa08029ba0830d954100536c1061b2a8200a76810c365504014eb02186caa08331dd8676951410669a20ced2a28200a5d831536250401c3aa6a1ec4a080a3be1d52d89410053742e65b128200a6d85ccb625040155b09996c4a08063be1d32d894100e6739a65b128200a6e850cb62504014db0a196c4a0802ab61032d89410143f42ce1b12820087d859c362504014db07b2ec4a08029b60c65d894100537434a9b128200a6e86153625040169b062a6c4a08029ba1663d894100536c2cc7b128200a6f8558f62504014d90ab1ec4a0802bae0163d894100574402c7b128200a6e8518f62504014db0a31ec4a08029ba1b53d894100536436a7b128200a6e8654f62504014d90ca9ec4a08038bd9743d89410071632e87b128200e2f6550f6250401c58caa1ec4a0803a3d8d43d89410074631a87b128200f0d5350f625040174902a1ec4a0802b9a0475d894100572c08ebb128200a6e85dd362504014db0bba6c4a08038bd5254d894100536c1ca9b128200ace83153625040159b062a6c4a0a938ba1054d894152727418a9b128200a6d831536250549c9b062a6c4a08029360c54d89410053742ce7b128200a6d859cf625040155d0939ec4a0802ab61273d894100667b9ce7b128200a6e851cf62504014db0a39ec4a0802aba1073d894100556c20e7b128200ae6811cf62504015cb0239ec4a0a929ba1353d894100557424a7b128200aad8494f62505494d908a9ec4a080393e0d53d894100557420a7b128200aad8414f62505494df0ba1ec4a0a929b21743d8941527172a687b1282a4e2c54d0f6250549c5f0ba1ec4a0a938b21743d894100717a9e87b128200e2d53d0f62504014dd0b21ec4a08029b61643d894100726a9c87b128200a6f8550f62504014d90aa1ec4a08038b95143d8941007162a287b128200e4d5350f6250401c5f0aa1ec4a08038b21543d894100747c1a87b128200e2f5350f6250401d1ca6a1ec4a08038b54d43d894100746a9a87b128200e0d5350f62504014dd0a21ec4a08029b61443d894100537c2ae3b12
  | 33 => 0x8f61243596410062eb9c86b2c822287f8750d659058f0f90ea1acb20803175cd43596411161fc3a86b2c82c7c3c8750d6590401c3f06a1acb208030fdcd43596410070f39a86b2c8200c3d7350d6590401c3ae6a1acb20803075cd43596411043f43886b2c820087d8710d65905d547d0821acb208029da0772596411053ac0ee4b2c8200c6f729c9659040147f08b92cb20ba68f21172596410043f43e64b2c820087d87cc9659040147d09992cb208028f61332596410053b40e64b2c8200a7581cc965904010fd0e192cb208021f61c32596410051f42064b2c8200a3d840c965905d147d0938acb208821fa1f31596410043ec3e62b2c8200a3e84cc5659040147b0998acb208029ba0b315964100536c1662b2c820087e870c565904010fb0e18acb208028fa1031596410051ec2062b2c8200e55310c565904018f6e1382cb208028fe1170596413951e422e0b2c820087e87cc165904010fb0f982cb208028fa1330596410051ec2660b2c820087e870c165904010fb0e182cb208028fa1030596410051ec2060b2c8200a6e820c165904014db04182cb208029da0430596410053ac0860b2c820cc76615da5490419a6e82bb4a9208029760c5498a410070ea9a87314820087f855c262904050f90ab84c5208029760c5458a410070ea9a86b14820287e851c162904010fb0a382c5208021f61e6518a410043fc3aca31482008ef8758862904010ff0eb2c85208030f99576d06410061ebb2cba0c8200c76655db4190419a6ca8bb683208031d5d965d06410052ec18a93048200e1d5350e60904010ff0ab94c12080a1f21572982410052ec18a8b048200c5f7354d60904038b8e6a9ac12080327dcf43582410070ea9a86b04820287e851c960904010fb0a392c12080a1fe1975182410043ec3cca304820087f8759460904011f70eb00c1208021fa1b73d95410143fc3ec7b2a8200c5d73d8f65504010fb0f31ecaa08029ba0a63d954100536c14c7b2a820087f8758f65504014df04b1ecaa08029b20963d95410053dc02c7b2a8200a788058f655043f0fb0e31ecaa0803175cc63d95416361f3b687b2a82c5c3e7650f6550401a3ee6a1ecaa080387d8d43d95410070e31a87b2a8200b348150f655055d4ed03ba6caa08021f61e73d95410fd1f424e7b2a8200a3d849cf65504018bf06b9ecaa08021fa1c73d95417351f420e7b2a8200a3d841cf65504018bae639ecaa08030fdcf43d95410061eb9e87b2a820087e8790f65504010fb0f21ecaa0b9e8f61243d95410062fb9c87b2a82c787f8750f65504450f90ea1ecaa080317dcd43d954163e1fc3a87b2a8222c3c8750f6550401c3f06a1ecaa08030fdcd43d95410070fb9a87b2a8200c1f7350f655040187ae6a1ecaa0803871cd43d95410043f43887b2a821f87d8710f65505
  | 34 => 0x1a0060008000004018000801c450ff0eb1cc32a08b179cd63986540062eb9ac730ca80ce1f4358e61950014ef02b1cc32a08b479cd43986540068eb9a8730ca80ce1f6350e619501927908b84c32a0025be097358654004b6412e6b0ca82287c8758d61950018bee6b1ac32a08b171cd63586540670fa1ac6b0ca800a748158d6195001a3ee6a1ac32a08b471cd43586540670fb1a86b0ca8a4e6461dc961951498dd0db92c32a2931b993725865452697326e4b0ca8a4c6f63dc961950018dac7b92c32a2934bd0f725865400696a1ee4b0ca8a4c6c61dc961951498dec1b92c32a24399184725865448637320e4b0ca890d2e641c961951218dec6392c32a0031b58c725865448697a18e4b0ca800d2d431c96195121acec2392c32a243591847258654486b3a08e4b0ca890d64411c961950018dee5312c32a0029da06625865400637b94c2b0ca80ca7681985619500187cc9b9cc12a0030f99173982541143fc3ac7304a80ca3e8458e60950458bce6b1cc12a003175cd63982540670fa1ac7304a8eca3f8650e6095045a3ce6a1cc12a003475cd43982540670fb1a87304a80c93c845c660950018eae330cc12a08a1f21d63582540062fb9ac6b04a822c5c7358d6095019c3e86b1ac12a0029e20163582540068fb9a86b04a822d1c7350d6095019c3ec6a1ac12a0029be0961582540063a38ac2b04a800a788058560950194f501302c12a0038754d4398b4106476c3ca531682018ed878ca62d04010ff0ab84c5a080a1f2157098b410046fc1ae131682018dc835c262d04010fb07baac5a08021fe157358b410143e42ae6b16820087e87d4d62d04050f90fa9ac5a08021fa1d5358b410043e43aa6b168200c3f75d0d62d058d878eba1ac5a08030fdd54358b4162e1e3aa86b168200c9f7350d62d0401c3aa6a1ac5a080b1b1d65258b410647643aa4b1682018ec874c962d041947908bacc1a08030fe1175983410061e422eb306820087f835d660d04050fd0bb9cc1a08021f61773983410143fc3ea7306820087d87d4e60d04010ff0ea9cc1a08021f61d53983416361f3ae873068200c3d75d0e60d058b87ceaa1cc1a08030f5d543983410064eb9a873068200e1d5350e60d0401c3aa6a1ac1a080a1fa1472583410043ec28e4b06820087f865cd65904010fd0fb1acb208821fa1e63596410062fb9cc6b2c820287e8758d65904018bee6b1acb208021fa1c63596416361fbb686b2c82c5c3f7650d6590401a3ae6a1acb208038798d43596410070eb1a86b2c8200a6f825d165904014d904ba2cb20ba29de0574596410043ec3ce6b2c82eaa3e849cd659040147b0939acb2080317e0d73596410043f438e6b2c8220a3e841cd659040147b0839acb208030fdcf43596410061eb9e86b2c820087e8790d65904010fb0f21acb20bae
  | 35 => 0x8800000c006000001800a0000008028000003008004400c004000001c0020010018068020004000000000400c000000401c009000001000c009009800400600200201f8022000000027400000000f801801000001f0004000001000000800000000080180020000110038000021016000001c012003800000c00000d001c0000020100008006021000803c000005002801800200500a0000070007000001400600a003800000600001a000800200d00180040220020018004000008000000400000b01a804400c0020200000018009001000000200d006000000600000000a0016000000800c00e00000a8004008000001002400a039000005c00200202e001c01c00600900f800c0030010000012000003000400800d001802001a002005002400000a000000c00600000100000160140018014002035002003001000500e002c000005000001802a0050018008002013001000400000100580b00020000050010002004011801400403f0108000000002007000400200900d8004008012002002801e0080000008022017004000400000b00500080240190000000004007002000000201c001800000003500700b400800700300c800a00000000140040070008000000000000802800400a0050070002009000005400c001002002c00200202d800000400f00c002000604c0028000006010002001c008005005000000e001000000800000000f8018000007000002c00c011000803801a01e00000640000060008000000005004000804600400000fc00800000600100060080068008000002006005c0120010028108004004000001c0d000100100a801c0060000004046016000003800000302280cc00202200000300000040000008034000002004400a00a0000000002009001801001c0260008028008000005803c000007001007004000200b80400320070000030000006002800000200500880b800200500100cc042001015804c0020070030268000004009000000000300200000000000010000000007006000001a00401d00180020270018024012007003808c00600600580000060160050008006011000012400a003002800002200000180b000600500a001000001800a002c016001000002000e00f000800800600700500d0004001006800002a0180138044006001007001800a003005008800000900700100240090080028000000005000000a000001800000a0000008014038001000001801e0010168004000007001800c0040040000028024004002002007c0060000004016004002800000a002000003c010035002800c00000000780080000040040000000000002000c02402f0018010078002000000000c00100780000060420000000026004000000803c0040000000064005000800000400b000000406c00100080080
  | 36 => 0x180020048004040016001000000a000003000c002001000004800400000c802800800400500040020200000034014002003000000201e00d80180320020050018000003000000c016002006000000000b00a800000001300000180000000090010004005001000000800500b800000000100b80380e6004000804c00000a00280280100000350004002000001000c00a0020010008008005000802c04c007000000408600100600e801a00800000a004200006c00180000020028074008003001002c0100010158010004001000800c026001000011c16e005003000400000c00680000080080008010000004003001c00801600b806801a01a000002402a00300280280060050020114006045001802c00a009000002000201d0000000012006017800c018004000803c0080000048094010000000000001601a00380040040030070028018000000000c00403d0000038014001001802c00c002001800400201e000002c000000005001000401301b805000a01a00000000000220030000004005000000400000a0020008004043002004c002001009802002201600180040b201b00580480180000068000002001000801000c017001801c00000c000802800206c023000401000800980700000070080008006007001000000404100180040ac00700c003401e00a00380040000050000018002000001001c0000230038014002073003800800a00200e8024002014000000800200f00b000002200500000180120000008000000000000802400a000000801c0120000068018000000000009c01c006000003c012001000005404200b0000000004000000001400002100080000000000000184000002000000001600600200bc00a051003000400400500480000220080118060000009002001c01200201d00140460020188028000000001803000000600a800400000e001005800c0090370000006002000000002a000001000001a000012002400600003600e801a0060000090006002000001000000000700b4008011000000800800000b800000200200700b4002009001000400400e000800000601d014800c00000000a000800800d005800801800400000000620050030000000000000817007e000003800403801100080bc02601b00a000000a00b005009003e016000000000c01100200000260000010004000002007000c00600000000000080000038000002014002000c04800c002804800000000080e800401a0028004006000004801400000500080ac00c000002800403c002003005000e002000806800200e00400000040020008000008001068001c01a00200d802400000600000040680020000000112006016802001a00f00a802c01e003001000c00400000180040180100008000004000000006800c00000280000020020
  | 37 => 0x202255815323948eb000000001559bc094d0aa43918dea4569b40508a01e90d9bf341e1e051e99e5e7b20caa89c8aa0488845a5fb1ab64551416832800021fcfa2221a0664618dae67183c80a40e3c570a598116030038da5f24c81386960a1d000b17a64ada1866fe0e5e000032a44f00007f225a429ea1ec12d00004d59d1401c00006f501ec8b387f88d480006f91ba984a15821a0000092c94f03931d46000109a8bc185a92f9c7a3c619a62df000000000000391ba43a90cca9078000000184c51f90160000fc6000000000020de7bc00000000f1e00008243c18000000001227722748e38ea038c99240001889000205000f80000c05f7287709e0541800096d0000882948e47294767cd0cec000000022c80f46019684000029262506528a70000454133e000000000000001b2400044c000004c9118000253e3fa000000024fa94d80003f901fe3e3822a003000033480004cb02a21351ae247b0000000179a56209920000024004003808001a003006802804600101c800400e000000000400e0000098014002002003800000a0060010000008001000802800400000300f402e00700680c006e00000a803c010025000800c006001001003002800c000005000801400c800000202900180b402c01100e002c05c002001008804e0000058024008002004001000c00d0038000002015003002800200600c000800000000080140020040008000008001010800000200d007000400c08b001803c054000000001000001100000000ca01c00e000001e00000580c80020050010014002008003800402200600680300280000020070000008003000801805a00380280060350070020000001000000000e037000000401e001004003000001d00c0038004006000800c032000000001c0020000008000018023011800008c000000000400c005001000001c027002004803c00101400a4018017004000000600500b800400000600a8004062001007003c00600a00600f801600000702e400800f00000b4000010003001c02400d0010020006030002805c000003001802c010001000000000200100581040000030078034006000007800000a0040118000000003001805800c0030080004000000004800000e00301b800801c0040000008006009008000400400d000001c00000000200200000030008124022049001802000a00000c8000006035000000401e000007800004003e000800000c00300b000802e004000001800200f004007c00400500000380b801c01e004c00802900180480b6000005800402400500b000800e003011006401a001002000000602c0068054004000001802402800400480040000010000008002001004803400e006004000801e001004000001e0070028010030003000000401400100380000020000038030
  | 38 => 0x23b70c1a04f84026e713583c506ee04e15a20c682d223806ba6c6a51e414a370667007a3d28a72661846a8df100e9740bb094c213040b01e80000000000025a5e71b1846b1e2c0001ef81b9975621591007ef00000001a48000244c8a38000000015248d1b561719b24837231691781cc02e150a00003f284d0b3c00000007ff0bbc50325ac05d198b967a22c82ea34628f0636715a0fa84a9de40e2043a46d871061c078e5149cd750e8b7e90b08540219a345b092206cdd68c734025e864252204f5ed822a15e8750220c4450efa7301cb6255206a6141d1c30d8d6a8ab1a8e1088d8e0f798f05e5961a27b84a66d520082690d66914809417b03600148410463005c376a52e05c1b8c42082268ed997c7ce92e4170033c679165824b009b675808050d0d96081880a3b910647b99a2c6be16e25808d305d89b6071ba20851614261f4198050d94824c925283c58c2c3371c109640c0e4369a38150c5043f3827c2e3c26a15a04923e10d6e091a454654499f902851825888309350c300ac8c9a3ad06fc29f11dc2b7a5520810afe0e11d0236a85b00ee042025380a682687da7b1a5de1c3169c17407c801523888799d8a7c7895e971800010f966e13622da024a34a8f502fc21c993693c9dea3888aa86aa0c6889606ce4ec99bc1dfd04c585066e27a9f90884253873684e833a82605011f006d3157692b85326bc811c0618af83cc8a5208ca1ee4d1060c42280aa862a0aa727a41a5378b0a42000d3014140871a23ce97b8110122900c24c211c1c601db28185f08dfa1b246f040a746c91a722a4c23dc01fa6faa38a76f8b4a00022c6685858c4580fb8754c3b203285501b2133c47a1e1800022b600016d253d9af613f9600025800000000000001bfa5ea1430000052c1928be0587810c90813f000000008038da07c517b84f8800074496467d609762cd051e3d7805a22e000034880005750f666079a28000153a54599e086fa2d483f958c7e2a22069816408898f6a40d8ffe29e00000000000622800000014a01a700009612158000000000000008c910848b918284ea00001432426000000019d836222b9bb4000088d000099a18b000063d9b28000238c7fd141000000007b100000690e3800014c000021a881c8000000158600000000616318259127c0001de00098ae053d22162a619565308b2e67386162821f96328251a000000008e9c8659c05525c20c0c7701c2000017d0521000028017bb00000003559d3c57f9c7e40824e07bd03ee13f02b0000111c3a3015659080002ec838a1341d216f8236404694f2924000077f000014d0a2883180008f30c00944149e03e0e483a180000001ba10ff055e0000a540000a1440a0fdc00000008c400000000000285800004017e669d1af4056864f3df85f20000000006905a631a3c073b
  | 39 => 0x1c9088790b200ca1a40c59698411097c000000083f0aec7a20ee263694aa4e75266000000038c22427b7400091200005a48a10000247622500005a9000000000002ad02da221000001d90e0000103e8d711de0000f4e00b904e67b00001fa1b3c6e651a86d0c84002c201000018865fa9d3a7168d5890ba0709071e741231bab65e87e43fe03207d3a4dc2ae004d4a98b984b207f45eb985e268d46a000138a33e000036b15bc8622404269db5c1c0812c000000043a0acc0b380008d00a68000065e00013c60000bba3bd8d2032a1b161eb95d00001102000166400025be61b0c440db02742b086264298000068817143c82c064d17c606598980002478641a19a8b9a456390a3fe000248e229039e00000005d718a84b48a664970fd80290000931150258e95b672318e85ca90c07e88fea608922e7ea16223aa0a0c16e80003f790e279f1d0e0001f1c57a981096a000056a81f80000f80000175212f11d6097123a8a51c1e22623f4700192a86b93d621d86429659fdc25ba47a163800053f21e289821d655c099068525ce5179d5e115902e0000000000226c7f4177454802e67911d247348e942278000000070892183a81a094d419c077e4a80a1c53e9f0a44b0e98783d170267485082b80006de924817f40000001f1643b074a31a9eaa843992e2da8e9c83a9e020e884ba8928c5a3b98918298114e75d000089108dc5f71354078a026662997e00009888a600000000ed6000000090c9662000000053115a46cc8000000130a0000da8000201a65200007ec8b460001be10000e807fb804a743254000020067769ed6025c01c13e211892e9e7e88f8a622f4000057f064c79996b88b4107c1d1250c643137447a834800011da00007962eb000079b945c84018640a9163e31900007c61a940ed109c622000018f0000000000000000005dc20525c19ac05b21a9c8be064433383c66eb09e402a19fc0ba82181c491767aca3060000000000075c88aa1941d900003ec072c836949829b8000000000000000004b0942c54b90223b804466f1c5b207106780634fd060621ba00016aa0001c380490ec087686bb5eb0b384868000525059e000000000000000e51e4c7d7127a0000000000000007c81be74d1c3c69280000001700846a3020000000000120806002808dba1fe54f9bf76a1800062f8a20000250e0000d3e0eb90d800025ae829a14c2b91f3c3cba1f63ab800019ea372626807e113000092216c496f092029f816821d0e9691a80008501b2647d17820b624fe7a7194a94495460000b1415e06171b01db80000c0464107ea84c80001bc1c022d616fe9498ee863d1b1e6570e500d599aa5538a0a9581d36185058a02f9ebc544114600000003d4951a0000f0e0001f8c060982e12c9e225ac8bd85fe06f4000000081f8c2835c9a3
  | 40 => 0x58700007f81b0a0000c3a7050f7200020a248d8000137000039b0000460800056a0f12000053072f1a80000159626e259210a00004f40008662123282612b84bc04880000df26688bfa0ab8f583be13fc5df9f9c18c92c61cf9a088b6087003c043492a9e681770dca6f212ee8659ff86a680002af05a434911c22d11ea48708d1c82c1682499000000011427828e726a1000046d0cd00e7247c2c08b9a6249e1200102447064d5a0cb9a925a8219e44f8b3275489947111e961f31cde30f0e641d9a18e40284600c309985980ea22a682f080d17e839803cc911086a01898b256b01690a2845e789de5a00017c20625e8a92d85ea53984b637d07f24b81e9064e9d0437e800063924ea22d04863541bae4429afa10d800060c135c309202e06498a2077d2403ca836e76c02a885b14544a406000001a82003a3a62e91ede92a000000000005371b0800000000bc51c48fb1c5e24a9cf60001b5a6ee83aa000000090380ec000000000009ac0000d980000f5a3e3006e4a18a58665927600022a22d7a254000187a85a00005bf08520001ce86a58522000000000020d400000000000000000000079192d44b9848428b1c64772800000000000000000000000000000000000000000129a0001d10000000000000005e49f62000000003d85fc5400000263823843e800066e000066c8fa479e800089723f22dea49823317cc0c21e148d805f62378f3880e193804506a0000183272900607a81bce27d07b635b038228bda7c40783586049a501865fca8731e500138b603d7206e56023a03a79fb8000139c00000000001518688214697aa2cc047800012e0602640905e8ae80008361ed06b0962e9348c801820d2e14009ca58110568415a100c11ca0086881001b1dd290323ea023111619187e071d061275588d68780d7604e96260a206a495a012a7e916b6924984a7e6a4022362400000000012b00006d41dcc532210241d80000001a2400000005568ebe5d61180088826e25689d600012bc7f780008b097987a616188cc05fe000255a91d0000000000000000003bd1b8e00002ca80480e04de00240a39272226d57e89e8f9c00000006d380000001b782ca1d067858c62686243e53a965a24020a85c78a2e733955c956073053a02f68f0859c0001d9e3208eac72d1fba4db056674799f27ae061b529858687c25d6000146c00014884f110147ff80001528c663b68ae88869590092017270c974c000000000019446f1a502000041493d85820001d6000000001208fc24e3c60a8f19f0861d0000000237a57b000082019709701800478a3aa0001fa6000125409607600000e241d61d22000095811490b071f063800016ba7a480000000b1862b9b3e292000082da09070fda6600005e67db0a4c7a8a42a000182a5230ad664b00008c28ebc00
  | 41 => 0xcc87480000d482891ffa43111880d69ac84e9987e3da24ca245a5a07ab0f022249e2e18b897290ea2462f20df04958dbc4f39fc022a9630000136a00015520b41b4476610de31d9168346800067a1c345c8896c31f898a7758c3801e095c783827a3609a444639f367320e0a4449a5e13906fe41e9e8e079829453323668aba0848ee156e44389b689e23b260114e08449d6866d21929061666630235e7bd98a68c10312444217826c22d602d915e3089d44300800265988f86ba980c46597d4375026c96885d64ef8c9c0dc84ea2e1944036d0c7822b01eb53399f067481c81f3946642f86c66da9ce64ee823e02112b21519d4a74e01b84520e66242800062d93f252b029832289243669c184e0047a8810d427f9981a959245a861003414aa3ca00023b47bf8000133933a00003e4552000076f1f6e00001de2db112842924380001c0e5b9800000008900ed836a1e1659a37a22e228d108c12713ca3c90146455a5e41f60c1620c90344bb0000607000045ca2b24f78000506a2a4000146097c1ed45dc800032d000084d9d1d20000003ed00000001018788e2b54be0c5c8f40e045bca35606500cc5cf154a1da067c97510945fca5b819f8400315852669c1a406af89aa2c006be51687a032f9da6609962447c997866419626f6964495f9f304a4993069d82ba29398d8739093a5118fe21e30cc861e09fc8fe19f617e0d0e41990b8529186277e1338099035c6198342575a1f842d09f05ef9f4c8da8ab61b2a5325cc5bb210990d44ed855a4ba818f7129c7640017027c68cf60001a6268117aa81e0b3a55321c8838800081723e87f8a588843076a14b97ce10610d28d217b98e68b125f492da02d25e600003b044d1c0a6b624c047f248a7554dc016212061a9866a0cf8de47e80d525e51f8e48080e8757000068292ce396000023e8a920be18dc1ce18f851597de2b200de8761f3e3eaa37400005722d7103c00018086bb9e4083200001b6158441003e8297000088500006d9000034c84de022959c7bb092e43309a000000005a89e4938b000078e173e4248b8407ed22679705a677a13ac8a580001e055be11992463d4066426f8000000212c389905841d08fc17e8b3018d48d45978cb67170dee68f01160001a4c4afa32e5a69554000066c41f80008248b503652518547164c05cce8450484c644a9d964eb9c6035c1f061781fd86c8000086c0107000000088c8d8c0a08aac918239e2eda4b84e7a33a1ea1a300041eca00011245b5a3bc2d69a227ec08da16b8000000000000000002f51e0092080003929daa3f3229a5ad19c26b58bcc0da0f7a00000001ac1da20a317207840e0050a98de68d800043e082e63080009189f787750ce0251000046b9b065108a8600009c6260125237e0c986a614ec000104800186cc0000c2600000
  | 42 => 0x349817d00006ae0000000674251c000225642e933633b9946324844864ac9c44a885b6679904a8c899de663982006806d918784a295f0000000010a201000003e800000013f64cc221c545124e3f51fac2e00cbc577a2507188f9a848a52a09c8cb806280000f39f507de857e6fd12d67f1800023d88ee63f11d08978ca47d800743fb2450748c1442299af032980004b40000000033400010020120e8211902be0050000000000008025e00001e800c905af0000e7a773891c0bd21088e51cfc5db065c0190e40859062a4c59a2e622d9b606618f2223a05679395c64b79cdc796018c49d17d83aa8d0a1d099283bf8ed40b30cd600017a25d99bdf6ac17244f817c000008f0008061075507840130d06439115c28995ce6b81fea3df110c000184615f1acc0e40000051c0420000000241800000006ef808123c56c07c273a90ea1c391784aa969e544865683b1ea60461a88000072620618e2000222e848000080a023c158800000000008af80003bc80000d28f94000128041b9bbe05f1ac609e153c44d94ee28c256c2201f742f9971a4f500009578b2a61382960000000000059a82180001369c9c7c802d600006e81730000623220e24e216052d1ace1b0a1107f1184003116bc1e600005760e0c0cc87321aa97902b71f80000042406c01641ea85243f29f2a4d1a2e07bb81e539588ce050c1d06d4870a6149cba6e425cc4fb9f5a4dda06c9339cac33f911e2519b8200000006a9843c0000746000141c7b683dc835a5b638f92823d5a4a42548d5454109de522822c32799500f68dce39f1ce05a40b1a0782170594859605e8d7423200000000e9a000000000018ce000018e42ba04a4d9a09e11c188e35e8d0c8689d3056b80003d31042823962c95c19da133000061a071670b8fc481398a00001e3e7b90c589728000765215c000000037f00000000000000147425e9ba582080002191fc230186b896500000000000551172c4140d40190000000013c000010e65b692ca2cf85a21e00be26e4999e7c4800000000006ec000064725ec5a29d9264600002d380292e2171c70319086d1a53c7d519125818e1643c03be00020f25139f8404e528403c9aaa88e91d85de11a407a87b48bd9dd86ce8ff62c80580000000093b9b8065a2104059d14c80d9ee88b487504a6093c26f1b2e51b83928f8885e1940c3430b8ac40df855194b06b403606a257924308f780000000c1800000dc3b280fe78194481a4800084e037634e0dc600010f659400005a201f41761c4e64f14b211507ee4c68bf23eca4d8756a4a601f25428548e6a1d317ee74a80000000af26ed800078f0e680000d3c6dc172e7dd80000b50000189051d8290a3e7ad80000000000202000046e86bc0001c361b8125a3dd91c02b39cf87e2191a00023266458a4280f12785
  | 43 => 0x8d39d802f59faa37213f4377217c2e793aa2d8a2dc0b08ed24d9654a9139e4b85980562fd9a6c61c8a6c7355aae0d305d40830af01ec18e6223061a1e714ba86a8b16041091063ba58a7199b2c4c79cc41418fbe12819547d29d1846797e23618c520fa980a95a9a3e0d4137c7e0844238b9a7802689c20aa9a4637f89429251f2e8bc90d04ed016c397047460080008e8808e65d14867b311400002058074a16e6328bea15b96b01ab092638406680001f5e3779d6c06200006e2893e76a00003c9a36c21b138844188c41c725aa88d039a936a14228d9fd424a0c4c46e149c15e90108108000666023673e98ec47502c61b1103269600004cd081609c00006dd9c163050000345177600010c64ff9c7081201360bf80001ce89660cb000041c85287ed243c0000bc45d50bdc126a3da49317fc70d46de2ae99be000000078a1d6247e0c601be25ba5e78ac06f78a904e4829a7fb169667e9efa00004e200000006050dbe81f0fac13c8b785b0047c858a49a8d1087e8701d1611b1e2458a1b2968492b447822c00de0bc696998d6000244a0ef019e86614060001e080f8000000004ca921254642596f86bb13697799b3675e96f405a94f803a82c404802fa1660e1202f1d720000c6c088050267d0cfc65b87be0001d825d69480617144c5c59b2259c922857000000000000664a04492c069a6f71dba8b2960e4c60ea667893826ae01d604891fa5d380000d0d88072e01bc5fd00006b4983c9619a2a8e00aee82807066b11d646721d7c446800056e0000000000000019840000000378126e11f800093782e4795155089f80000c40a825b914b08f80a8480e8da471a98d022a4d781ef0ce603b9ada105891e70989821649b339720f00000059463f9d5821b9ae613e96dc7df8b9275b91980000b4238e89d8089132a7f49e4855a8a9e6a79e343378720000197215703023bf0000469800077d00003cf00001458000732a26a02b80008479d326f488ca8a800000001eb07c100001df638283d1c5078802f206720242160cc20561a5c000000048c1c3073f914a3210000267813c8a0003c1302054968570400005a0076173a7f31f405c506908521e322079c5478e920e48581831d3a4bc034013011381b400a0dd858a8f28000000000000005a016d00000b0610221a014402c83d80df600001d4710a48c0001242000138414f81543d200161039f92000185655a160c0000b8a1ac94fe107116e0001c3e62a95fa22721ce42f24461889d50817a50a5e20d440a788a279c21ac8671e6c00c08826cad7c437593224bf17866ac92f685508422e58fb67259c1a0e603c02c10d462fb000066ba384759908e03f060e5cc040657200d26349bad4e519c477d8e2a8f1000026a00000000dc27070538536a3983589d1f1538e024681b0c55602660088
  | 44 => 0x7240001174000237600015c46b501080000000130819a0001dc60000126532800000020f664508260001a6464f925e59a050800000007cc8e761f488461d78b6440c09da000152881a1288361038c42892ae4e4618c0000000336856473bc76c05b497e5ed08c281d02347f39296000231a4d21b6e00000e24280dcc65493da05400004e2cc4a95882102cb20c248621248ca8fbc34418b03cf9a1a0001b4263a8d4e5eda4b462e0ef00001abc7dc0c7a0281c8200000000000901000168e9198a74702110820d9edc5fe92fe3479dfe78a8c54000167800000007bf0afc378946277b086200023e63230d345628a9400007400369df08bba15047c1d9a40704504e419643e29e944ec19d87b7caf45d788bc0321aca78102a0710000050800000f0957a06d9876000164821f070000011ce044800000000002fd1e0b7019b66000000077200000000000000000000021261c79cf297691a2292a4a21ff0000000163636980000000f0418f9838234a0cc3de08022c702ec52d9a003c2967e28e1ca217117428190cc459d07c4193800044e995e00025e816a1d082c8816b8990dc457d86620ee9f0c3a48000735a45839b90460001090764078a825012e66a000076300002e8800000000002fe00006330000000000034d8000147d6f62f08b56000132e739d6a8496000000015568adc00000009a500004aa00008e4000000000018c4000024a1d6df2c95d8f226e12424000192900d977a5240b404049df200000006fc9ba875e16d400012b040109a25950d922ac80006580d9e4ef01062a21baf26994444981cae362178062105be1bc95e00001d765ab01a65728f1c6e5000036d9748000000015503a42ac00002f3837a43f851a382122c6ff8c7c7c380005d00aa21e68b8206e80009100a64000055b0000ac65669a4e00006c30000c74433800016404ae0000000000000000007c625e1e8482f1cf082f967a83e53281ada2621df00000000970374894a00000002ee1418888942854306663420000721400011a00003fb90686ae800000004f41ee1b4872f8bfe32394ae4020d3a2e465e232c80003860cae36e800018d07901cf0000325a33e1201268000037023f82e0834912200000004ba09d2286a4f463e9a7a0d4847264404440fc16382720db20001cb25c49f100f5936e3409bf0340101a000218090494d605f934c6e9a2fa050899c7ca115233d01e472a196c30c9e1c730939a5388e1e00024e43b09de27aa1f9e6b7886809091583d920608029c242c999a43e7a2aa33915ee44982ac89c006a84b94d80858162000258e83b92c002400881a616cc55b0c206f5e002749a02a84f978e3459db21eb1afc4fe138c2b9800056507ca70495f8053096a20e186e1261da05e812444c189f877b91be3d0009c78994d045aa0ac905201c
  | 45 => 0xa00000000b79aa2736e5b24891e1a91c131c0949e9e41711324c392c41cba32c10a9bfc226a5446ec47a232198b42dc80666771dac85e968679820c430a956217212ba325174416100004b61d1a712183a212876e4f91d7e69a81f600001ac150655626c9cd468984a8770814a0bb8a5695d228a32c1ec0448016e87c8f348af0d188c50000579800000000000001b343fc04322ba8d9c729800000020f717285f400000002eb8380842549a0000f0c10323ee00000000001bc26c100000000f744c4000036c000022e86b323c99c000020b80000e0666083a633e976a145130215b00003d18a506d7903a08b85c25001a5467a80447b0842c4d7a3ae45e85480ce159e92b078707c0f1001781781c5098c4d4a49e2420000231983e76d065874b000025822a6148071a2fc05ee487072a2a700000000bbe5ec94920000e4e000000000000006e694be65680007480eec82700ac3ea152a2b699a07f58f4291b22121f019b00e38cba90a1bb80870ece02c9dde45f0844582961683922664c485d287d053c8fe95f4548930419c848e7710cd883c0109939809e61501c61472032279831c42d80587088a047e18c5e34b098425304e62dd04969021ef259d8c408ea192610b9b105d90ff407f077043f23622121d886ab00005d8191e37b1eba21700001f5a43458d041e0d78000129044008291f611b81ee681a3d215e47567a31f487fd80c270e916c82d068e7efa15a0d387fa2d49138740141e31ca572000000046a8e341e78000000000000013e826593c26732472000000000000000000000000000000000000000620000137e91f80000000000940211690420c08f2000049b0000158222400020ce00005400001c920000ba880517b0000031e33306dc16e082a6df821200012ac8698aa60af0230000000086f199493f185862080000001b9f203800033c88f49600bca13594700350d7e84280002fa068a0001bec6ce00461eca0046f407fe7b8800000008ec93317ba6bfa3b016d00002d500000000d12196943c56c8a0206a143e34a9a903f48000736054c6cc587c13ba378825a2521fc0b763e61f6a208861c648829c302a480000090c0000000245086028798163ee96ee00006fa09010c233c0330492916631c09321188eee49881661b581dc893a3583e816ae2da0d801a58cc648a8000000256e00000180000ec63220000000000000000002e40f2c18e800000016c6278a5dc7958000000000000000001921b9672603f413105f7000118463823285731eae713062817690065c408a041b144a57c00006ad093689b9c8e27019ee00008148ac000031b92046f1000049c17844e383d806a96be5da15741b9218259f00000000b6671481488861e78935a54e7a695a6000000046c8000222934a547920a919019061203063db1a5a000
  | 46 => 0xf80001ee95ba6c00000000000017385745028c1089215b400000000001d42000207a00017c82c30000441000057480000000a5e3f595242a59ccc58ca3a400023f0841c2289420afa0ca0a4405bce1c2bd905455080006e7890260b00002ea89121b5030e000254c593a2fc127889634a000097125507b487d48221f4200022c45d41dfa0000000000162069a177c000129e00018a44da18341250bd20c9893400004b046495267e60c4e851178c000078687a09b4000108864290f429d8430632213a0941a8c00009ba8bf8c465f2a55c6e20b241c8a0161f88e8e8c4a23c0001e62690862f841917e0df161079dc6e240980008ee97f08c7965c1d6884c70b1b2f8a098ba746509893b03ac0a1109e51c9c580e585bc11d9f465baa2b42860dd000009405dba58c48e2416650856a85c96fa4e593cc0958e1a4ee1a523ff1f3833880e672681340a19c288118a5a82319f875a818420f03e22901e3084f238688c07f68eb0a3a95e21fc6f892140438f44432a3d889a0a8a0f4963c3cc0e7817923364d399fe5009a0e5cccce813c14500000000838227c1a31bf514281ca09f8ff25ef194c19823d64a50404000033a4f6180e7fc80009520c084bd21fa0c289686b7031462705ac14389ae418114482c8783000121e15d9d4e4b883ec3078e706dd1ba219d157c1d89ece3e48a8e0f41a026438d5e79c90dc22c13a02340aaa04a22ea02e800055917f69018000459170c4c321144219baa6f540000ad21c600000005b78e8a36280005c600009670f6e000001e0000a6a00008ea0001d1700010701d4800000022ec6870e288c391b07d102271a218900300bee8169aa4783229e0fea396472000000005363c810d68e713c88ff123e6e614a22c405443141bee3301fe8000183620d0000000194e1f7166a00000008a415787da0000040a1e480b000035316ec000090b3b409f6458873410e09569761d865d2881c88014244c9844a8cc88061b4925036897347b81ddc28aa35a035868651e13980029c043fe869440e01c21e90b4c4c21d8e5b28c9062b102a3e421ca14497e0061e5166a8047806b83f81d520f805d9464033881a30491d227411fe398835479a9ba05500b366351b72357049065a95926fa25b081306181e20d7c396a4e279d919a4aa1e5200ea1b872017e48748ec82731b0e7eb934039f989e85d02628ae1cb0418877617a1bd873180402ff16e089001b21048ed8177a2368c009504a90f8823a090401c88660000ca27d90f080b70eb82ed1024364142e2c7824e1321c84087853a66e8000073a07602095dc7c880007f917363ae86ec51f0b703880f9615619002138000000152c36e0fa6284935a151ddae000257a5c380006c497466c7158e2398ecc000077419524f072a80004d8178a2e81e360b9639000e00005f5a08
  | 47 => 0x818a28800021b4000022f2e980001de0fda00024f843b88782e50f1a106928e8060bda7fc1d2e2b615f2057927e479002a3850ad04320fe07d483223e097a486d9d8400000000001ae44fe966c6ba0d6895507e61b4128a6fc51901f79ba76258eb23d51d3f5a995a0853833641a8fae20a1c460001d4c0d980004c51b3b6da0ede83a2286000186a66680a232b00000b880000001cee8a30000204a0302e7077254d13a47ba9f241171212000000085a88be00012103951fda1bd972864808b66ca82070001d9c5769b865660000000184400024220c60000881800000004be2b29f7c8a1249c00000000850be409d960888e07944f723387909b7c5051d494d882547af8a224a311944b715363f99e8272203468930c4852e034042b19ac03195f5931800000016d813818421de93642b524e83e180001811a0c00000000000974000225a83413729418e748000eb6000000097496126c5020e4f99d48949143873d21c40001be674a16e80000000000186085d965605700000000c3e8fd800000012cc00000004be800000021d4000000000003ca1509538000000013d885a88a24c871c920c0f11bcc7c0823167289862a01e1e4731c7827b00003350aae0001f265318000070082c8c7000051a00003f220e67d999d46a2800022200001aa198c02600000f9993200000000000000000000068e912e0001a561e0800052a1ad088080008100000000147a47186ea8e48e0e28c8606592970a2520b0892599586d294320ff94e44d40de634103f60dd23548cf253a5348b8e18c05aa542118a6d621ea2d225140d11da474282b60ba0f3a8cd068420e8d607a1a4d01e4836455993ec72500688ef93008b203d4852a2e879923208f703a04a71a7e13b09d42af88c03ba8fc09171370941134289d800085f8ae227a02a66ef252087795720000ec400000006cc000080f800000018bc7740c1c2388d640001c2a503937a0000160080838600011ee8f924a00544000000000080307283a423085ffa5660001ce22b49c6c000150e278cbc079293d252598240930a8c8a4870400000008c30f3642a15e20769a6e000087a20fa35000016f000022f4291818b8da00005c989fa149c0005b3a34c00010aa24380000000e880820000855814027f99766f29200134a5c200022a80000000000069e910800076d88206fd80003d880000000d4a4fa97da7ed880c29c0a0e69c80005578bde00012f27d5969409a09221fb1a1e6c0a2de00011e6000000000000002e30c42000014e91a073617886da49a800039113a25ce119c00000006d8a46e6db153027393326d7c2b88d08b0e000000000009f27ad09a18578b6e7e51bd652f194075c057074
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x181f85e13735891000417a6054dcd624400141d931d1535891000507a5d5350d624400141c9754d435891000607a1d5350d624400181c8754d43589100049364e84d94624400124d93a1764189100058364e85d90624400160d9321464189100049364c86150624400124c9660c5418910006139d9831506244001a0f6460c541891000683191831506244001a0f85e13631891000493a6054d8c6244001a0d856106318910004936605418c624400160d931915318910005836506354c624400160d931954318910005836546350c624400160e9654d4318910005832595350c6244001a0e8654d4318910006832195350c6244001c0e7654d431891000683a11831506244001a0e9460c541891000691a45831506244001a459160c54189100069160e811506244001a458360454189100058364f85d0c624400160d93217431891000583a615350c624400160c9854d43189100059164c548c46244001e055350e31189100059164c544c46244001e055350d31189100050764c549da404400121e9815363901100058364c54d8a404400160d9315062901100050764c549d8404400121e9815363101100058364c54d88404400160d9315062101100059164c5418a1044001e055350c628411006607991831d1650400141f965cd4359410066079d1831d1650400146692e057359410064172617350d650400141d979cd4359410065072617350d6504001c17915cd4359410007052457350d650400141f9754d43d90100050765d5350f640401905c985cd539901006507a5d5350e640400121d93211655901000507a5d5350d640400341d945cd531901000507e5d5350c640400141d9754d43190100070354d439c86404001c0d5350d721901000607e0d435da540400141f9754d43d88100050765d5350f620400181f7460c5458810066071d183151620400141d93215741881000417e5d83150620401981e7460c5418810006075d183150620400181d85611731881000417660545cc620400141d939d1531881000507e5d5350c620400141d9754d431881000607e1d5350c620400181d8754d43188104850b251651c9410401903c9461d65c84106248d2518759721040010779760d65c84100068560d4359721040014559315176084100070554d435d82104001a158350d650841000589251825942104001265985967208410004996578758821041212a4946156208410486892105458821040016459315162084100078154d4358821041216249459442084100650d251655c440040018656520971100100640f2518759420040014659759421080100051564c54dd91004001c155350f764401000519658541c910040015459315072440100072158d431c91004001d055350c72440100051664c54dd91004001c195350f7644010
  | 1 => 0x66071c183153644400141d9315373d91100050764c545cf644400505e98dcd53d911000507e4d75d0f644400141d9754d43d911000487259839d7644400141d9319773d9110004876627518f644400181d9760e75d911006e079c1839d7644402581c7060e75d91100050764f875d7644400141d93a1573d911000507e4d855cf644400181e98dcd53d9110006076637354f644400141f9754d43991100050765d5350e6444001c0d5350e72991100070354d435ca644418f05c9760c545911000607e1784dcd644400141e9754d43591100050725d5350d644400381c8754d43591100051364c54dc96444001c0d5350f72591100051364c541c96444001c0d5350c7259110004876605418c644401905c985cd531911006607a117354c644400181d8754e4319110064872615350c644401941e9754d43191100048764e859d8644400141d93a167619110006079d9831d4644400141d931957319110006076157318c644400181d876146319110004876607518c644400181e865cd5319110006072197354c644400141f97d8d53191100050765c6354c644400141d979cd5319110064872617354c644401981f985cd5319110066072617354c644400141d939d276951100050764c849da544400181f83d0e76951100060760d439da544400105f9361f64951100050764e74d92544400121f9361f649511000507e4d87d92544400181f83dcf64951100060760d73d92544400141d949db75d8d100050765676dd3634400141e96dd774d8d1000607a1b75dd3634400105e96a1c54d8d1000607a1f64153634400181e8719054d8d1000607a1f751d3634400181c87dd254d8d1000607a1c74953634400181c94a1c54d8d1000417a5c87153634400181e87a1054d8d1000607a1f74153634400181e871d054d8d100049364e84d97624400124d93a1764d89100058364e85d93624400160d9321464d89100049364c86153624400124c9660c54d891000683d91831536244001a0c6460c54d891000683e1784d8f624400124e9815363d8910006836158418f624400124d9815063d89100058364c6454f624400160d9418d53d89100058364c6550f624400160d9518d43d891000583a595350f624400160c9654d43d891000683a195350f6244001a0c8654d43d891000683a11831536244001a0e9460c54d89100058364f85d0f624400160d9321743d891000583a615350f624400160c9854d43d89100050764c855d2624400105f9760c5498910066079d183152624400181d7460c549891000607615845ce624400105d9815173989100050764e7454e624400141f9754d43989100050765d5350e624400181f8754d43989100060761d5350e624400141d93a1774589100041725d83151624400181f7460c5458910066071d1831516244
  | 2 => 0x852112494614704842100459e4d851c1210852116798950704842100459660541c121085219248415070484210055164c541c1210840116595e0c704842100459663531c121084011659854c704842100649617431c121084019258550c70484210066160d431c12108401d055350c7048421004596578748760084011659521d2198021066071d183152600840141d93a1774580210041725d83151600840181f7460c5458021066071d183151600840181f85e13735802100417a6054dcd600840141d931d1535802100507a5d5350d600840141c9754d435802100607a1d5350d600840181c8754d43580210050765d5350e61d000126595e1921087400050764f84dcd659000141d9321373596400050765e7350d659002521c985cd435964000607e617350d659000181c985cd43596400054364c549cb619000150d9315172d86400058564c54d866190001a2454a0b61986400054664c549c2419000150d9315372506400054364c541c94190001615931526150640007091507298541900015199315070506400050764c54dd9219000141d9315076486400050764c549d8219000141d93151760864000689153864842190001a2665211210864006417a637350f655001941e98dcd43d9540065072637350f655000141e971cd43d954000507a5d5350d6110001c0d5350f72584400070354d431c961101218a4841c95158440007055cd535844110001a248520961104400650d2517558621100018657520961884400050764c54dd9211000141d931517608440484392617648421101218a4845d921084400070915176484211001943a94d4f76500400660e21376dd540100191389761774500400050765d5350f64c401981f7660c545931000607dd58315164c400181e8760c545931000607a5d8315164c400141d9315373593100050764c545cd64c400141e9754d43593100050764e745da54c400141d939d1649531000507e5d5350e62c400141d9754d4398b10066079d18315062c400181d7460c5418b100050765d5350f648400144d9315272d92100070354d439cb648400144d9315172d92100070354d435cb648400141e9754d4359210066079d183153628400181d7460c54d8a10066079d183152628400181d7460c5498a1000507a5d5350d628400141c9754d4358a1000499e5587d8821841212a694e17620861048689a1054d8821840016459315362086100078154d43d8821840018e187a03620861006607191839d3654400105d989d063d951000507a5b7350f654401981c7460e74d951006417a637350f654401941e98dcd43d951000507a5c7350f654400121d93a1365d9110004176627518f644400121d9815063d9110006075d583153644400181d8760c54d91100060765d83153644401981e7060c54d911
  | 3 => 0x2100607e0d435da548852142c9459472506216248d251875972188401a158350d65c862100607dd183151608841981c7460c5458221006075d583153644840181d8760c54d91210060765d83153644840141d9315373d91210050764c545cf644840141d9754d43d91210050764c549c364485898577160c545912100507a5d5350d6448401c155350f715912162685d8583150644841921c9854d43191210050764e749da544840141d939d36495121066079d183153604840181d7460c54d81210044764c845d4604840121d9321175181210050764c845d4604841981c7460c54181210640f25185dcc604841903c9461f53181210640f2518754c604841903c985d743181210040f2617550c604840141f9754d43181210050765d5350c604854942c945d621181210050765d5350f640841981f7660c5459021486151c583151640840181f7560c545902100607a1d83151640840181e9760c545902148685dc583151640840141d9315373590210050764c545cd640840183854201735902100507a5d5350d640840161593150715902148709150721c5640840141d9315070590210050764e745da540840141d939d164950210070554d435d8410840116595e1972104210074154d435c841084011659520172104210064560d435d62108401524946097588421485492517510a210841903c9461776484214844d25185dd921084014349461776484210051564c54dd92108401c155350f764842100649214745092108521134946147048421004c925185dd921085211a49461776484210054925185dd921084019279461776484214845925185dd921084019249461776484214844925185dd921084011679361776484210045966054dd921084015459315376484210045965783dd9210840116598d4f76484210045966153dd9210840192585d0f76484210064961543dd921084019858350f76484210074154d43dd921084018668761776484210058925185dd921084016459315376484210078154d43dd92108401705931537448421486291d1869d121084011679561a744842148661d0d839d121084019458354e74484210074154d439d1210840116595a02744842100549255741d1210840170593150744842148469251851d1210852152695d50744842148649151831d121085219874360c744842148549253531d121085215249454c74484210065160d531d121084015249550c74484210074154d431d1210852192454a0074484214864921c54991210840170593152644842100649214745912108521924871516448421005c164c54591210840116595a1c644842148459a6376951210840132494614704842148469251851c1210840152494614704842100649e51851c1210852116494614704842100649251851c1210
  | 4 => 0xe67986399e2ca15c4794f1b6180a51ad2bc104e4136000524ea9cc02a81c830b422c328e209c1d0775019a4000620799af100238d59f801682cd48002a4000719e71be138cf8a1238668239a22480bc3e0de10e0ccdb18c22473c919ea098294219ca25c7e40397a0544e0c01110004890890a0001710680000000000177288504000000004ec1d12802c000ba1432987a4f619837a810048653847d8e30001a45a40002c0001a4d0c002e25e4000be0007c04b87903456400000004228501bf000450369f31e42203783d0000149480015a018090cc04000000000900c000081501400008020280f00c0002800010120000203c01000000a800000060240100c020000200c0f01c04044240101500c07010020000a000090000804001004020041506000000000000b0141600000014070080603804010010000200003014000080000403000020200b028000500d00001004010140e008020040d0080600405004000400001c0601c2e00c0001001040090000202c000140d00800004030000001000010020000b020000080200001000020480300c0505400000040281000401004050d003000090300a00015004000140100c0001549c0f4358f725865452703d8d43dc96195121c0f4358c725865448703d8d431c9619500141d9399373982540050764e645ce609500141e9754d4358b410050764c845d660d040141d9754d43983410050765e7350d659040141e971cd43d95410058364c6550f625040160d9518d43d894100583a595350f625040160c9654d43d894152683d0d839536250549a0e5460c54d894152683d0d831536250549a0e9460c54d89415268310183153625054960e9854d43d8941005832615350f6250521a2441a1a54189410058364c6550c625040160e9654d4318941006891948150c6250521a0f4360e541894148683951831506250521a0f4360c541894148683a51831506250521a0e7460c541894148691d05831506250521a0c4160c541894148691105831506250521a0c4060c5418941006891508150c625052160e9854d4318941005832615350c6250401e0553e054318941006892148150c6250401e055320543189410054564c541c54250401e055350c62d05410058364c5418a415040141d9754d43988410650da5353dd9411041983484ddb75504415270995376dc94110521c2654dd8725044148549251531c9411040141e9754d435804106607991831d1658854990c4260c745962148615985831d1658840141f965cd4359621066079d1831d1658841905c985cd43596210050765e7350d658841941c985cd435962100507e5d5350f648840141d9754d43d9221064172617354e648841941e9754d43992210048764c84595648840141e9754d435922100507e5d5350c648840141d9754d43192
  | 5 => 0xdc84d1ca1846200c062000000643895f0e29da4260000001f218000001730c6370641db33714c0020a048000908003b25e05c9f72a0674698582b83d4e58dd0926e0c88753586be310003be0000011a0fa0007b91f000000a28cb3ac1d10420c23c2980212f0002a000000000664000ae0000000013c3f40982a1c6a0e1ac9b8c91a00000016a2d83000000009e760d31d43ca0004f8e13d6000391bb3047ecca0340dc6cc5980a08a8480a0b732051c412051cc0dc15867154044098d10521ec1708b3570003c0000004008982134e1a8e018e00016cc30000007c40019b00081800181000780000001f068c430ea000000840000003a4001700000003411b4020008100027c2885e8002e4000488000000003b00036843c0000011217c000003d0614110e4064350ce1663bc49cf18003ae8500018b2dc50000000000000000e01c4000559e242a2106b0d53db6b80f0f9202000b10bf2647b4b59750d81783f0bb41e3b0f78b109400077877000424001c100069a2e967000234ee0000380000000006c39c0d80008c000c980004a7402895b000309000420006a0da90d000364769a012c0006081205a2d88c8fd2b4330628991460c08b9ba000000a11481582bc001640005d8758fa13a71ce8800000000a58001240f00004b0003680180000000108000000000f20002680000000032c0044a9f212816433000106000f09b28000000b9c301a61c1d93a39c0002b00006a0000016f18c5604991d0000003881913c3f8ab8cd1f8120cac524046a80412b00000000000000000ab0bc000584961a53a6110e916d324734d881d3ea43904815b06610d800041c7f8e499722a5547d89b07c35c429031866f87b18f2f64f4fe87a2c07b80716301e6542c4002603c0c4827208338771b20aa2e8a32160702c8548000e05a0af83900070e000000000009009a14e6dca88001180005a8a42160a000040000000a69530004a8000f400005aaa0000000003f8000b44e4bf0200000004c0003424cc7f90529c57400110314060000d81025f49f8cf0cf6345c1350a02c07889025a7f000000020000fa1bc2624941f80000c08c93000000460ff97f0
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x90014f00006d7830001000000000804007a74a000230c0058000000240000007440000000000001c0000042000000000900000001500a96c40001680000162622415802800c295c7cd130070b0018014000004b99000000a00740000000000000000d0000000000000000040818100001000400080000011000540b4632902a18c4a0802a04a854c8150c625058980bb0b26422ea302420c8072a19754d4318121005033462a100b9ac810a434047264c541c5640840120ad1928c2eec90842008c168c946177648421004a0b464a30bbb24210802905a325185dd921085210925232bc1eec908429084929198d4f764842148424948cc2a7bb24210a42124a961743dd9210840109254b0aa1eec9084200a416a15350f7648421004c0b464a30bbb24210a42504a954d431d1210852188243b262a4c89084290c4121d93151644842148424948cad0e3224210802305a3251851c12108401282d1928c28e09084200a4168c94614704842148620908c98a83824210a42124a4657831c1210852109252331a98e090842908492919854c704842148424952c2e863824210802124a9615431c12108401482d42a6a18e0908429084929195e1d21d802148424948ca90e90cc010802a05a315282d866190001602d18a8394c2a0c8000a8168c54e19210864048504948ba904b0c422024302498151764842110001602d18a8bb2421088090889a939561f620861048640d08c98a9b104308002c06a2e457350d650400140bd3b06a1acb908209088929198596720841048444948caf0eb1042082432048464c545882104121412522ca412e22002090909291975942108010
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2804860068768c946177648421484104b96a15350c70484214860049868c545d92108440
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x4c
  | 4 => 0x4e
  | 5 => 0x124c
  | 6 => 0x138c
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x124e
  | 10 => 0x138e
  | 11 => 0x10c
  | 12 => 0x5
  | 13 => 0x10e
  | 14 => 0x130c
  | 15 => 0x180c
  | 16 => 0xa0c
  | 17 => 0xa0e
  | 18 => 0x130e
  | 19 => 0x180e
  | 20 => 0x20c
  | 21 => 0x20e
  | 22 => 0x140c
  | 23 => 0xb0c
  | 24 => 0xb0e
  | 25 => 0x140e
  | 26 => 0x28c
  | 27 => 0x28e
  | 28 => 0x148c
  | 29 => 0x184c
  | 30 => 0xb8c
  | 31 => 0xb8e
  | 32 => 0x148e
  | 33 => 0x184e
  | 34 => 0x194c
  | 35 => 0x94056
  | 36 => 0x95394
  | 37 => 0x5254
  | 38 => 0x94054
  | 39 => 0x95254
  | 40 => 0x5394
  | 41 => 0x125394
  | 42 => 0x4954
  | 43 => 0x124054
  | 44 => 0x124056
  | 45 => 0x138054
  | 46 => 0x138056
  | 47 => 0x8e
  | 48 => 0x98e
  | 49 => 0x128e
  | 50 => 0x150e
  | 51 => 0x10056
  | 52 => 0x130056
  | 53 => 0x21254
  | 54 => 0x20054
  | 55 => 0x20056
  | 56 => 0x5554
  | 57 => 0x4214
  | 58 => 0x155254
  | 59 => 0x154054
  | 60 => 0x154056
  | 61 => 0x154e
  | 62 => 0x40e
  | 63 => 0xd0e
  | 64 => 0x160e
  | 65 => 0x188e
  | 66 => 0x98c
  | 67 => 0x154c
  | 68 => 0x194054
  | 69 => 0x5954
  | 70 => 0x124954
  | 71 => 0x124956
  | 72 => 0x138954
  | 73 => 0x138956
  | 74 => 0x128c
  | 75 => 0x150c
  | 76 => 0x10956
  | 77 => 0x130956
  | 78 => 0x40c
  | 79 => 0xd0c
  | 80 => 0x160c
  | 81 => 0x188c
  | 82 => 0x194954
  | 83 => 0x95954
  | 84 => 0x139254
  | 85 => 0x139256
  | 86 => 0x11256
  | 87 => 0x131256
  | 88 => 0x21256
  | 89 => 0x155256
  | 90 => 0x195254
  | 91 => 0x125954
  | 92 => 0x11396
  | 93 => 0x131396
  | 94 => 0x195394
  | 95 => 0x139954
  | 96 => 0xa0114
  | 97 => 0xa0116
  | 98 => 0xa1314
  | 99 => 0x10a14
  | 100 => 0x130114
  | 101 => 0x130116
  | 102 => 0x131814
  | 103 => 0x180114
  | 104 => 0x11814
  | 105 => 0x20116
  | 106 => 0xb0116
  | 107 => 0x140116
  | 108 => 0x29314
  | 109 => 0x11494
  | 110 => 0x28114
  | 111 => 0x10294
  | 112 => 0x149314
  | 113 => 0x148114
  | 114 => 0x148116
  | 115 => 0x130a14
  | 116 => 0x130a16
  | 117 => 0x180a14
  | 118 => 0x180a16
  | 119 => 0x194a14
  | 120 => 0xa1954
  | 121 => 0x181314
  | 122 => 0x181316
  | 123 => 0x21316
  | 124 => 0xb1316
  | 125 => 0x141316
  | 126 => 0x130294
  | 127 => 0x29316
  | 128 => 0xb9316
  | 129 => 0x131494
  | 130 => 0x149316
  | 131 => 0x195314
  | 132 => 0x131954
  | 133 => 0xb0214
  | 134 => 0xb0216
  | 135 => 0x20b14
  | 136 => 0x20b16
  | 137 => 0xb1554
  | 138 => 0x21414
  | 139 => 0x140214
  | 140 => 0x140216
  | 141 => 0x141554
  | 142 => 0x21416
  | 143 => 0x28214
  | 144 => 0x20d
  | 145 => 0x28216
  | 146 => 0x29554
  | 147 => 0x20294
  | 148 => 0x21854
  | 149 => 0x20296
  | 150 => 0x184214
  | 151 => 0x184216
  | 152 => 0x185554
  | 153 => 0x21856
  | 154 => 0x194214
  | 155 => 0x21954
  | 156 => 0x140b14
  | 157 => 0x140b16
  | 158 => 0x194b14
  | 159 => 0xb1954
  | 160 => 0x155414
  | 161 => 0x155416
  | 162 => 0x41414
  | 163 => 0x140414
  | 164 => 0x140d
  | 165 => 0x41416
  | 166 => 0x140416
  | 167 => 0x189414
  | 168 => 0x141894
  | 169 => 0x189416
  | 170 => 0x141896
  | 171 => 0x195414
  | 172 => 0x141954
  | 173 => 0xb8294
  | 174 => 0xb8296
  | 175 => 0xb9494
  | 176 => 0x28b94
  | 177 => 0x148294
  | 178 => 0x148296
  | 179 => 0x149854
  | 180 => 0x184294
  | 181 => 0x29854
  | 182 => 0x148b94
  | 183 => 0x148b96
  | 184 => 0x184b94
  | 185 => 0x184b96
  | 186 => 0xd0b96
  | 187 => 0x194b94
  | 188 => 0xb9954
  | 189 => 0x185494
  | 190 => 0x185496
  | 191 => 0x161496
  | 192 => 0x195494
  | 193 => 0x149954
  | 194 => 0x5556
  | 195 => 0x4216
  | 196 => 0x154d
  | 197 => 0xe8e
  | 198 => 0x18ce
  | 199 => 0x74c
  | 200 => 0x4956
  | 201 => 0x58d6
  | 202 => 0x4e96
  | 203 => 0x56d6
  | 204 => 0x94754
  | 205 => 0x958d6
  | 206 => 0x94e96
  | 207 => 0x95456
  | 208 => 0xb02011e
  | 209 => 0xa18d6
  | 210 => 0xa0e96
  | 211 => 0xb02131e
  | 212 => 0x130b96
  | 213 => 0x131816
  | 214 => 0x130296
  | 215 => 0x131856
  | 216 => 0x1318d6
  | 217 => 0x130e96
  | 218 => 0x130596
  | 219 => 0x130754
  | 220 => 0x194b021c
  | 221 => 0x19420b1c
  | 222 => 0xb02195c
  | 223 => 0x141556
  | 224 => 0x140096
  | 225 => 0x1418d6
  | 226 => 0x140e96
  | 227 => 0x1415d6
  | 228 => 0xb8116
  | 229 => 0xb9896
  | 230 => 0xb98d6
  | 231 => 0xb8e96
  | 232 => 0x149856
  | 233 => 0x148416
  | 234 => 0x1498d6
  | 235 => 0x148e96
  | 236 => 0x131796
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 49
  | 7 => 1297
  | 6 => 4847
  | 5 => 4858
  | 4 => 535
  | 3 => 48
  | 2 => 3
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
  | 8 => packedAt gbK8 (1428+((h/22+packedAt gbK8 (1274+(h % 22)*7) 7) % 105)*7) 7
  | 7 => packedAt gbK7 (53522+((h/503+packedAt gbK7 (47989+(h % 503)*11) 11) % 1811)*12) 12
  | 6 => packedAt gbK6 (255354+((h/1746+packedAt gbK6 (232656+(h % 1746)*13) 13) % 6287)*14) 14
  | 5 => packedAt gbK5 (308410+((h/1676+packedAt gbK5 (286622+(h % 1676)*13) 13) % 6034)*14) 14
  | 4 => packedAt gbK4 (39280+((h/183+packedAt gbK4 (37450+(h % 183)*10) 10) % 727)*11) 11
  | 3 => packedAt gbK3 (4000+((h/16+packedAt gbK3 (3888+(h % 16)*7) 7) % 122)*7) 7
  | 2 => packedAt gbK2 (278+((h/1+packedAt gbK2 (276+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc03ffffffffff803ffffffce1fc7fc7ff1ff
  | 1 => 0x7fffc0fc0fc07ffffc0fc01ff5e6399fa47e67
  | 2 => 0x7fffff000fff80fffff0001ff9f83e1fc78f87
  | 3 => 0x81fffffff00000ffffffffe03e003fe3f80ff8
  | 4 => 0x1ffffffffffff00000000003fffc003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x9600051412d0a118011454cc400ac2ac09b0ab
  | 1 => 0x2ad2c0ac85447a6b640e815694e61995a45665
  | 2 => 0x4d656b0109bd08b5aba0029b29782e1ac68b86
  | 3 => 0x1b9b2cba00810c6d2cb2b003e003543700d50
  | 4 => 0x1fe3cf3ce2e5c00e0820c023fb54003ff6000
  | 5 => 0x7030208200306007030c301c3fdfbffc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37417
namespace PEqualNP.Outside.L_meta_37417
open PEqualNP.Outside.L_meta_37417.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 2 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 30 := bs3_3_0
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
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_544 : Interval s3Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_608 : Interval s3Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_640 : Interval s3Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_704 : Interval s3Atlas 4 704 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 712 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 (concat bs3_4_192 bs3_4_224)) (concat bs3_4_256 (concat bs3_4_288 bs3_4_320)))) (concat (concat (concat bs3_4_352 (concat bs3_4_384 bs3_4_416)) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512))) (concat (concat bs3_4_544 (concat bs3_4_576 bs3_4_608)) (concat bs3_4_640 (concat bs3_4_672 bs3_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_704 : Interval s3Atlas 5 704 31 := block_range (n:=31) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 735 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 (concat bs3_5_192 bs3_5_224)) (concat bs3_5_256 (concat bs3_5_288 bs3_5_320)))) (concat (concat (concat bs3_5_352 (concat bs3_5_384 bs3_5_416)) (concat bs3_5_448 (concat bs3_5_480 bs3_5_512))) (concat (concat bs3_5_544 (concat bs3_5_576 bs3_5_608)) (concat bs3_5_640 (concat bs3_5_672 bs3_5_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 42 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 5 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 bs5_4_768)))))
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
theorem bs5_5_800 : Interval s5Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
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
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 48 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_512 : Interval gbAtlas 4 512 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 535 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)))))
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
theorem bgb_5_4832 : Interval gbAtlas 5 4832 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4858 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)))))) (concat (concat (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))) (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))))) (concat (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)))) (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400))))))) (concat (concat (concat (concat (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))) (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136)) (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296)))) (concat (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456))) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 (concat bgb_5_3584 bgb_5_3616)))))) (concat (concat (concat (concat (concat bgb_5_3648 bgb_5_3680) (concat bgb_5_3712 bgb_5_3744)) (concat (concat bgb_5_3776 bgb_5_3808) (concat bgb_5_3840 (concat bgb_5_3872 bgb_5_3904)))) (concat (concat (concat bgb_5_3936 bgb_5_3968) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 bgb_5_4128) (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224))))) (concat (concat (concat (concat bgb_5_4256 bgb_5_4288) (concat bgb_5_4320 bgb_5_4352)) (concat (concat bgb_5_4384 bgb_5_4416) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))) (concat (concat (concat bgb_5_4544 bgb_5_4576) (concat bgb_5_4608 (concat bgb_5_4640 bgb_5_4672))) (concat (concat bgb_5_4704 bgb_5_4736) (concat bgb_5_4768 (concat bgb_5_4800 bgb_5_4832))))))))
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
theorem bgb_6_4832 : Interval gbAtlas 6 4832 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4847 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)))) (concat (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)))))) (concat (concat (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))))))) (concat (concat (concat (concat (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))))) (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)))) (concat (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))))) (concat (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))) (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224))))) (concat (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 bgb_6_4352)) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))) (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))))))))
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
theorem bgb_7_1280 : Interval gbAtlas 7 1280 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1297 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 38, 54),(inputs.getD 5 zero, 22, 54)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80eaeaea80eaa8ea80
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
    slice_correct (ms:=fixRows 48 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941264000 * 2 ^ 32 + 3936938624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37417.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[0,6]⟩,⟨.or,[5,7]⟩,⟨.and,[1,2]⟩,⟨.and,[4,8]⟩,⟨.and,[0,9]⟩,⟨.or,[10,11]⟩,⟨.or,[0,9]⟩,⟨.or,[3,12]⟩,⟨.and,[13,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3936938624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264000 * 2 ^ 32 + 3936938624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37417

open PEqualNP.Outside.L_meta_37417 in
theorem PEqualNP.Outside.L_meta_37417 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264000 * 2 ^ 32 + 3936938624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264000 * 2 ^ 32 + 3936938624) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
