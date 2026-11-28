import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37249.Model
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


end PEqualNP.Outside.L_meta_37249.Model

namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
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

def SBf (j : Nat) : Nat := [7, 5, 6, 7, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37249

namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1036bd1960e342000000c003800000560512c509870000008803e243035c786242eb4a8f3a649294084d2704a82931628a084a00604024b0800001cc0417c0ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1d9a8361f3f0682432301d030442f10c4a633d0a822270120006553281072010a0000c5a22a14007d000c46e200005452723b0b4006f40800102b250000a001e8001a16000000079230b0128328974c87100000a86727a086a1e080d0000e2d9acb85f0390878192b89896001f800907b3682c8e590014c82613b884d80c340c0f05012130923605000660000000004e118b8004d371d4c428201c0003a111cca413000742e841f03cf8582b1a4002f33000fe380e0081810209098081804000018240410ac080828003c04300000002c082c00080098240808180c0c481000009e7ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x68049e81602ec0002670090000628800088000e01402cc90304000600aa80800000080000c80c68718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (3970+((h/44+packedAt s0K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s0K3 (1036+((h/8+packedAt s0K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcc32
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
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 2 => 0xe07f01ffffffffff0781e07c0fffffffe493ff
  | 3 => 0xff8001fff03f03fff801ff800fff07c0f8e3cc
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x220a100460821040188a228462884a4a092615
  | 2 => 0x491462c88514c18b0320c868853194b46490ea
  | 3 => 0x8526b55123a856d568497b2129da4706b8e34c
  | 4 => 0x1658d9a24a0e9b66b5ec12424e6ce218df03b0
  | 5 => 0x1860e1c38c30e3b8c6719c7380708420f6d800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2000400a6800df32dd32de31dc31ee21ec21
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x202a8a299710c421
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s2K4 (104+((h/2+packedAt s2K4 (96+(h % 2)*4) 4) % 10)*4) 4
  | 3 => packedAt s2K3 (56+((h/1+packedAt s2K3 (54+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x81fffff80ffe0c1ff87fc3ffffc1fe018cfe7c
  | 1 => 0xfe07e0ffffffffe0ff83fc1c07fffffe7333ff
  | 3 => 0xfff800fff07fffff0003ffe007fe1fff83c38f
  | 4 => 0xffff800ffffffc000007ffe003fc03f0
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8c30c808e10454031814c0a471d1321884563c
  | 1 => 0x14910111242800a068814408924244a83130d5
  | 3 => 0x28425aa243514d4d0452aac124b5195382c30a
  | 4 => 0x71659cc48a1d6e76b558228247399063dc03e0
  | 5 => 0x418610870c618b98c6633313802001836ba800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaacc88cc00eeeeeeaacc88cc00eeeeeeaacc88cc00eeeeeeaacc88cc00eeeeeeaacc88cc00eeeeeeaacc88cc00eeeeeeaacc88cc00eeeeeeaacc88cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x74e0878026ac01a140000000440000061500005831f00013280000ea54400d80403000058016a33c854a4005480d160c2813848c94001040e125c18083000000100604000008202ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x7ac28a4a3808904084001418426826200002985e00009c3e0a7200000046243a00a84c00b27eb096b444828e000c009ea254001c00ac00525a8628a42e3c6e00000022bc700010800e5c16622a32c0b8789ac41a4858666436aa76baae3074126a945004be4e8ca0922c7c1eb60600606ca634005600882c341860004400182c0010c08080009003c023c0120218104000010a0b6e5210edaa421cf55242af29c855d5390b5ea4a14f95042af298855d5310b3e85996750b32af28e653e548ca7aa9195754e32d6a1465ad424caeea2995d14532e7a92659f424cb9c84996750932e6a12658d424cbaea2995714532ea28a6554514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96835f53506b8a6a0d754a31cfa14639d428c6bca318d754831cfa10639d420c6bca218f5944319f2a6433d54c86bca790d754f21ea18e435f53886b8a710eb50a21afa9a435c534867ca810cf55021af298435d530875a8410f50c421bd280437950086bea6a05714d40af298815d53102dca4205b54840bb288817551102eca3185d546309faa2613c544c27ca9904f55320af29e415d53c835a85906b509209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd4803d100000100010738500a00001308331440624b20100d8400b254214532a3592424cb8542d4532c3508514cb854214532c5d08514cb464214532c5508514cb454214532c1508514cb0d5250831c3d4d428870d5350821955943108785420c421ca509500875031540218b588544c2546154f20c354d42c8344520c510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x408000605655083108780a1062a8043411c55350b20
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s3K5 (841+((h/15+packedAt s3K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s3K4 (2904+((h/33+packedAt s3K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (833+((h/7+packedAt s3K3 (798+(h % 7)*5) 5) % 30)*6) 6
  | 2 => packedAt s3K2 (150+((h/1+packedAt s3K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0ff87f0ffff87fe07d19f3f3
  | 1 => 0xf81f0ffe0fffc3f0ff87f0e07f87ff82e6ccfc
  | 2 => 0xffe00ffff0ffffff0007ff007ff8ffff070f1f
  | 4 => 0xfffff0003fffff800007fff0003f80fe0
  | 5 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10c2008c200840011809012318092118085171
  | 1 => 0x32441114645004506883104528824b0862c4b4
  | 2 => 0x4108aa2082a222a60444aa0845509463050a0a
  | 4 => 0xe596cc494a3aab3bb550881276640633b80fc0
  | 5 => 0x861888718cc333ccc666cc9c04401843d7a000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0eeeeeaeae8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 2 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 3 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 2 => 0x842551042aa445582225504255022531850c0a
  | 3 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037c83a06f10740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037c82a06f10540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081be421037884205f94440bea8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fd20461f9408c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530ef18a61dc314c3f480987e50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320fd18641f930c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f681087e10210fd18421f930843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec42887d48510fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7c86a16f10d42f7a1285be4250afea2a15f14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332efa1e65dc43ccafca3995f54732bf28665fa50ccaf4a1995f54332fca86657950ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483be42907788520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc6490fb4c921fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087de4210fd88421f690843f521086fca010fe94021bd28
  | 2 => 0x60cd248002ec858001a036672455a311140008d15800000131a600008e05a00000062c000002ee4dc118b6000000002673d46d8000780005747c8000000007f9f31d0234aca7035810c811e54fc4a00025343e0010806f4680000017f000000000061a47040000000000000242268000000000000005301e000828000fc31a888be80040800000000000000000000007f0000d71ec38c000190000000015146a23cd19d618e8ccce81f28253000000434000d319f0005b8000000003f91d86007e40c000000004f0280000aa00000221000a4c0011c00076ccc8000000000000017672c002721b89b0b50000920bd4680043606c3b8890885c87d8b2000000c0800000000fa8000d011cb8a23000320000000000012a2832429954b92b3ec7b0000ac2d60006107f26c000001b0000000f387d0004e41c9300006540025d10e000000000006f4000000009d8000740000ac001320624b4b2800000000001eb2eaa540000048a37d359074a481c499ae4a0a282f8004d2964228ba000001379b404c6708097432ea1000000000000001a200044c5018a34a6484e000000008000000003d00002401c00000000000a44000000980000000000032c000003a62f81d10a070000000324f8498110730006c8fb9de014000e00bc0007a40000000000000000000000521800005b5310004e617800000000000dc8f7000000001cf2b4000a31670003191f9113520480000000000401c0100100800c0180000c01406000000004000000060000080000000800000010000010010100040080000202400803002008010000000000200000c0080080100000001802010000010010120000000501a01000000000008008050000040100100002403003000000008030020100180002e0300200300001401801002004048040000080500002601c028060060000000000600002803004000008000020140100b0020040500600a00000805000018020030000040280200200c0080700000000001016000008010040040180c0060080500200a00000000004008020000020000000200600c0000400001c0000800800c0680000000002001004030008040000340000500c00400003010000020020220000000000000800804000008028040000000100000200000003bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7216fd0e42dea1c857
  | 3 => 0x15c3b8000000000d4d791400085051a3e106000e611d00051c00000000000000003e82b40021100000000000000020e502e00000000256000514dc27527e5a5008990007153d98243c3b40010e3aa2540005a028a3cf78d915e3e0000004bc00000000000000000004f0000e68710000000000000000c00000000000358000000002907c00000059800000000000002a09e526a4009e000000004600012fa280003a40000000021800000000750c78a2000000000003300000004a120000001df00058400076078000d08002e01b8298001f48ac201001881200026e0004f91d0004d045c738000009e8db9ab4c819ca707a1702004ba2e49c4240028e02e000001be3a2000b3029000000629f13ba0004d8000001386d0001fa5200e80001a920f08f006817084229424000ff800000000000001a827cb228c26a0000000000093c2083d276294dd0210005ed0b80004096c1d800000000dd80046e0b400000000000001ee1c4000001d200050c00290000000000000000000009d16e855368c93d0678321da0003c4001c40c4a509495215215c38000000000878940000000000000000000000000001442550001180008b0ba014009791603448f2614124bcfe8d33c85282122531049c5525a1949100000041e00000000258001388004b85bd061420cc8e507157000000ad8de3c00008d8753e04f4368eb1ac9440001c000000000002806c4779a8208928c80270001f800123378000000001860000028913c0008818338c1eca790600000149000000589028150003980000040c000c99d9102000000250003c80016c0a80008c00050e000001e2000000000000006911e8dd496000988000001649d1e63b0000000003f40000b0a700052c0000046c0000000000091c972274100004d0d53a084c861861300a83600000000000000000000000ec0260012300000003c0008e19c0009291930a9300000000000003a1d2e6570eba77000000000b103470800000386000000000580440026a0006a8c612400002435187020578be27f52c5585f9b528833c488a10508a8fca0b000214001680003003ca1900069d41000000248c70650000000022d0000014313329a3d41f000516000df9f806e0006c0000000000008217a0c0608000000000023200000000000150001331492f0000fd861000394001c720a00000000000030000002f40005c9121a00000000000000000000000000000000000000000000078c5a938322458268000009d10180039058c2c00000036c000002fc220000000000000022c00018d4080022a668000004388800005624439000153000230001ce3288bd122854fa3a88f80048648000096000a011e1dc41a0d8cd8691e689800000000380f900000000042000216000aa0000000103900032c904000001c2624af80001
  | 4 => 0x21a060258000000002d80035a000aa80025495d000510007f90c0004b0580c20cc0007b4000cd0000000020200000000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2434c25c6550d30a7593324c31c54cc930b6983324c31c544c930d3149324c31c548c530a7590314c31c540c530b3588314c2da600c530ce152404c39a43901309e195404c39943501308f596540c23e64150309798c540c27a6015030c7553300c339548c03097d95300c31d544c0309ed95300c339544c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f208fd9151c823c645472097d8d51c825c6354720b658c40c82b8644c3209798c548825d63152208fd91538823c6454e208f990538823d6414e208f992518823d64946208f992544827b60551208f994544823e6494d208f59253482796094d208fd91534823c6454d209dd8553482746154d20ce153204825e63d50209758f540827661d50209d587540823d6595020ce181540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530835a6094c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083706054420ce553400837151d00209e59440082d96310020dc5444008279658c020ce5523008371518c020ae1913008339544c020d694d3008371514c020dc546200826f65480209ed9520082b86448020dc545200823e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c42f06048710ce95320c433a5408310bc58420c425e63d52109758f548433860552109798c548425d63152108f993538423d64d4e10c7952538431d5494e10d6982538431e5454e10c7551538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528425e6314a109758c528433954d0210b658c4084339548c210ae1913084339544c210d694d30842b86448210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534423f64549108f191524425f63549109718d524427b60549108f990524423d64149109798c524425d63149109d195214427a65d0110b658c4044278654c110ae19130442f0614c1109e99620442786548110ae19120442ba64c41109e983540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530427a6014c108fd91520423c64548108f990520423d64148109798c520425d63148109d984520427a60148108f992510423d64944108f992500423d64940109798e500425d63940109e59720042796508010bc584200427965840109dd95100427b6544010
  | 1 => 0x69e63908418fd95411069c63504419dd95411067a60153319e58054cc63e6494b318f59252cc63f64543318f19150cc67a60d52319e583548c6d96010e318fd91528c63c6454a319ed81528c6786054a31a7992328c63e64942318f592508c63e649513197d8d544c63e651513197997324c71c54cc931c7151324c71c548c5319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d96010c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c435483197596320c69e648c831d354a320c74d520c831d354b310c65f654c431a7191310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c65e63d53219758f54c867b60553219e18154c863e64d4f218f59353c863e6494f218f59253c867a6094f219e58253c863f64543218f19150c867a60d52219e583548865f63552219718d548863f6454e218f191538863e6414e218f590538867a6014e219e580538863e64942218f592508865e63942219758e508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534874d6214d21d314e324866c654c921ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c504875853141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530874d53c84219bd95210874d53484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087722154021dc485500865e6394b409758e52d02b86050b4097d8d51d025c6354740ae98241d02b96010e40a798e429029c63506408f997435023e65d0940ae18142502ba60905408f994415023d6590c40c754e431031d5310c40ae580431023d6590840a798e421031d5390840c754c421031d53d04408fd95411029c6350440c754d411031d53d0040d654e401023f6550040c754d401027b6550040d654d401026e62d53309b58b54cc23e6494b308f59252cc29d64ccb308fd9151cc23c6454730a759031cc2cd620c7309d987548c27561d52308fd91528c23c6454a308f992518c23d64946308f992544c23e6515130c758c544c3396015130c715
  | 2 => 0xc0000006b8091d26989501831c7647e88d1822601b89020c664530003ee000000d800044845941000000000000007e000078206599021e100047c5296f1564a0bd0cc1060f4e712b02a1dc978733ae000c41da0000006d052000600850e3410310900002124906f07e000000351b23882a02b9ca148080e1a07000414169f2324000640dd098278448553b0000000f430e250000002be0d00006e00047400059000000c30000002200000017a0000000033c3185d882000000001bc000000ae000000314b68001d6830d98581386bcdf8b02466a5098003be714bc93c2c2000001e30007003199c000000f3000000001028b70b8000c58002ea0004b80e2ba3b8d682338c114e1000000864460a93408480e8004120004b000000124001cb0000000200016000020600d000030940200c030000500006000010000000400008180240208405004000081500400010110100b008000181700800000010000b0480504c05004060000002007000250200102c0a01808038000080a0080203c1700007004000040205801000010541e0480c0000b03c0001c1202c020500000400004290080000c00004150140101002040080080303c09008020080600800010110040001004008110080001c0501c000040700002088031000105401000080000301c020141b00000008010280b018000240701005000010000002c0000c010167b6054b439e18152d0e7a60947439e58251d0e3f6550c4397d954310f3b4354043d690d5010f394354043d650d5010eb96010f429e98251d0a7960947429e9825390a796094e42d69825390b596094e42c794f4390b1e5350e42c794f4290a3e6510d42ae5804350a9e63909429798c5050a5d6314142d698c5050b596314142ce90c5050b384314142ce9085050a3f6550c428fd954210ab860508429bd954210a5f63544429718d5110a7a60d53329e58354ccb1c63553329e98054cca796015332c755343ccad96010f32ce95250ccb395494332ce95150ccb395454332c7953328ca7761551329d185544ca7b60551329e181544ca5e65d0d32b6580434ca9e648c9328f990514ca3d64145329e980514ca7960145328f990504ca3d64141329798f540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3e64948328f592520ca5f654c8329bd95320ca3f64544328f191510ca3f64540328f191500ca5e6394b419758e52d06b86050b41ae580439069e6390a419798e509065d6394241d698e50907596394241ce90e50907384394241ce90a50907384294241ced06509067a6014d419e580535075a6014d41d6580535063e65d0d41c714f435071c5350d418f997425071c53d0941c714d42506b86050941c714e41506ba60905418f59643106b96010c419ed81521067860548418f596421
  | 3 => 0xfa0120000006e2103ea0000012c31e004b59272080008716c28059c00000164000bb1cd166384968002c823840129000000888002ca000000003bc000001b60002480018915a0000000000041c0000031a00000000000000488e52961100a07b0007d8e98061ee0000000019414ce8a0a000210000b616a4d5088d208e6b0b199710a7e4a195a2f8008120390007901d9c70c21e4088ff0623f0898482762fccd9144287050688f0004e4ab1a30000100021a0500ccdc9160f47881f11502e300668d00c85407200002c7542f000298000ad846000000af00000054c000a70000b8001770007401080010c67c000600de2c42e8f936e6745e1542aa24c741fb0002bcf71513d2000000f13085c49a000202030738002f069cff003374604f29a8144510b48d42f6420001b500030c000001f07f4000df000460f58e23700006990200076cf3800270608ac84f40c5c8001451b67bd0780030a000000001ac5d0eb1951da7508683206c7740019829a0f04d099218000001e03f40210b0cb0007fc00000000000e9019114000b404e1de284130b42fa1a03611b0000005014f404000d1200136128d080037645c9714a3906a84383827c0d4d89004068043598341616c6a98c2e60402b18a3287b00d8290f8464881600e44881601326643c7504027e3e8c98b93e0144339212ae3b03e8f00342e8ee0e00007a0930c72744dc3a8050008547b0c92d45084e9f13da0002104b264000068000b401c208d932c0a8a3066016000d2947356560000700ca524218f31027cc050ae3203445f1b41e4398368220e228cf50fb3f8668001c92342548e062398094000000a84c0859ae24a09c3a1913485b81594e23c6f49b1be01e3082683a2902a85602f0ec3d50b8000be6c00015207e4f4e797f2620004f97019c000b101f41c2e02801e1fc0003480000033c000302fc000000000001fd0c01
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5580101022d150e5c048018700c3ca5880050d3009040342b08607001465c25350e42a34e7210a0a15197018d54cca8d39c8528483465c05350d41c30a630284a0e1853982415068cb80c6aa063525c04354831c1cc8a946418e0c64549310c64cb98c0a1281265ce6090540c32c6b00a89841d76153324c20ebb0a818a6183151620c530a32e6302a81065163544400821c3b2a8980418c191514c020c60c8a8a40106325458420c428cb98c0aa4210e1d9544c210
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4000001300819869ce4214142819869ce42942418198714c60509418198714e6090541
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s5K3 (1265+((h/8+packedAt s5K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (244+((h/1+packedAt s5K2 (240+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83fff81ff87e3e1f0f878ffe3fc0e0fe21f793
  | 1 => 0xfc0fffe0ffffc3e00ffff0ffc3ffff003e79fc
  | 2 => 0xfff0ffff007ffffff007ff0ffc00ffffc78e1f
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 4 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa86288c62494620583c189962646225a20b391
  | 1 => 0x920114240200440048a902240924a080a50b4
  | 2 => 0x10842208114800aa10042208880894a0c50c0a
  | 3 => 0x52cac490940cab33a950088d332c0433700f40
  | 4 => 0x630c871ce67133dcce674cc0223018c3bfe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0fce8ece0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a0400001ffd5007fe5401ff55007fc5401ffd4c05fe5301ff54c05fc53007fd0c05fe43007f50c05fc4301ffd48077f5201ff94807fd52005f54807fc52007fd0801fe42007f50801fc42017fcc801fe32007f4c805fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2101ffd4003fe5001ff54003fc50007fd0003fe40007f50003fc40017fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24006fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff0412003ffecb88026ff65c4013ff32e2003bf9971004ffacb88026fd65c400ffe32e2003bf1971003ffec988002ff64c4001ff3262000bf99310007fac988002fd64c400ffe3262000bf1931004ffea988027fe54c4013feaa62009ff1531003ffec788002ff63c4011ff31e2002bf98f10007fac788002fd63c400ffe31e2002bf18f1004ffea788023fe53c4013fea9e2008ff14f10007fe8788023fe43c4001fea1e2008ff10f1003ffec588002ff62c4001ff3162006bf98b10007fac588002fd62c400ffe3162006bf18b1004ffea5880277f52c4013ff2962009ff54b10006faa588027fc52c4001ffa162000ff90b10007fa8588003fc42c4011ff9962000ff8cb10007fa6588023fc32c40037f30e2009ffd471003ffca388027f651c4013fea8e2009fd5471003ff8a388003ff41c400fff20e2000ff5071003ff88388023ff31c400fff18e2000ff4c71003ff86388003ff21c400fff10e2000fd88710007fa4388003f521c400ffe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188017ff654400b7fb2a2000dfd9510004feca88017fe65440077f32a2005ff5951002dfaca88017fc65440077e32a2005df1951001cf8ca88003ff64440017fb222000ff99110005fcc888003fd64440017eb222000ff19110005f8c888017ff544400bff2a22005ff5511002ff8a888003ff63440017fb1a2004ff98d10015fcc688003fd63440017eb1a2004ff18d10015f8c688017ff5344009ff29a2005ff54d10027f8a688003ff4344009ff21a2000ff50d10027f88688003ff62440017fb122000ff98910035fcc488003fd62440017eb122000ff18910035f8c488017ff524400bbfa922005ff9491002ffaa4880037d524400bfe2922000ffd0910007fc8488003fd4244001fe2122004ffcc910007fc6488003fd3244009fe1922001bfd851002ffea288017fe514400bfb28a2005ff5451002feaa288017fc5144001ffa0a2000ff90510007fa8288003fc4144009ff98a2000ff8c510007fa6288013fc3144001ff90a2000ff88510007ec4288003fd2144001fa90a2000ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fc414c005ff98a6002ff8c530007bc629800bfd314c005fe18a6002f70c530007fe4298003fe214c001fe90a6000ff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c005fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffc4098007fc204c003ff0826001fe8413000ff8209801bff65c800d7fb2e4006ff9972001dfccb9001b7e65c80073f32e4006ff5972006dfacb9001b7d65c80013eb2e4006ff19720035f8cb9001bff64c800d7fb264006ff99320005fcc99001bfd64c80017eb264006ff19320035f8c990037ff54c801bff2a6400dff5532006ff8a99001bff63c800d7fb1e4006ff98f20015fcc79001bfd63c80017eb1e4006ff18f20035f8c790037ff53c8019ff29e400dff54f20067f8a790003ff43c8019ff21e4000ff50f20067f88790006fe62c800dffa964006dfd4b20037fca59001bee52c800dfea964006df54b2006fdaa5900036d52c800dfe2964006ffd0b20037fc859001bfd42c800dfe2164006ffccb20037fc659001bfd32c800dfe1964006ffd8720037fcc390002fe61c800dfeb0e4000bf58720037f8c390037ff51c801bff28e400dff5472006ff8a390003ff41c8001ff20e4000ff50720007f88390033ff31c8001ff18e4000ff4c720067f8639001bff21c800dff10e4006ff48720037f84390006fd60c8003ffa864001ff9432000ffaa190007fc50c8003ffa064001ff9032000ffa8190007fc40c8003ff9864001ff8c32000ffa6190007fc30c8003ff1064001fb8832000ff44190007fc20c8003f61064001ff8432000ff8219002fff65480177fb2a400bff9952001dfcca9002ffd65480177eb2a400bff1952001df8ca90003ff64480017fb224000ff99120005fcc890003fd64480017eb224000ff19120005f8c89002fff5448017ff2a2400bff5512005ff8a890003ff63480017fb1a400aff98d20015fcc690003fd63480017eb1a400aff18d20015f8c69002fff5348015ff29a400bff54d20057f8a690003ff4348015ff21a4000ff50d20057f88690006ff6248017ffa92400bdfd4920037fca49002fee5248017fea924000df5492005fdaa4900036d524800dfe2924000ffd0920037fc8490003fd424800dfe212400affcc920037fc6490003fd324800dfe1924000ffd8520005fec290003fe6148001feb0a4000ff18520005f8c29002fff5148017ff28a400bff5452005ff8a290003ff4148001ff20a4000ff50520007f8829002bff3148001ff18a4000ff4c520057f8629001bff2148001ff10a4000ff48520037f84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9
  | 2 => 0x4009ff8a5a004bff42d0001dfa168000ff90b40007fa85a0003bd42d0025fe2168011ffccb40007fc65a0003fd32d0023fe1968012ffd8740007fcc3a0002fe61d0001feb0e8000bf58740097f8c3a004fff51d0027ff28e8013ff5474009ff8a3a004bff41d0001ff20e8000ef90740007fa83a004bfc41d0001de20e8011ffcc740007fc63a0003fd31d0023fe18e8000ffc8740007fc43a0003fd21d0001fe10e8001bf5834000ffea1a0007fe50d0003fea868001ff1434000ffc81a0007be40d0003fd2068001ff1034000f7881a0007ff30d0003ff1868001ff0c34000ffc41a0007fc20d0003ff0868001ff04340087fecaa0042ff6550001bfb2a80009fd9540087fccaa000efe6550021feb2a8010bf59540087f8caa000efc6550021be32a80039f1954000dfec8a0043ff5450021ff2a28010ef95140087faa8a0043bd5450021fe2a28000ffd8d40005fec6a003ffe63500057f31a8000ff58d4007ff8c6a000afc6350021ffa9a800fff94d40087faa6a003ffc5350001ffa1a8000efd0d4007ffc86a0003fd4350001dea1a800fff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a001afc6250021ffa928010dfd4940087fca4a0043fd5250001bea928010ff14940007fe84a0003bf4250001ff2128000ff509400077a84a0003fc425001fff9928000ff8c940007fa64a003ffc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf18540087fea2a0043fe5150021fea8a8010ff14540007fe82a0003fe4150001df20a8000ff50540007f882a0003bc415001fff98a8000ff8c540007fa62a003ffc3150001ff90a8000ff88540007fa42a0003fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd0140007f680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007fe2050003fe1028001ff8414000ff820a003bff654c01d7fb2a600eff9953001dfcca9803bfd654c01d7eb2a600eff1953001df8ca98003ff644c0017fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c89803bff544c01dff2a2600eff55130077f8a898006ff634c005ffa9a6002ff94d30017bca69800bfd534c01deea9a6002ff14d30017fe869800bfe434c005ef21a6002ff50d30007ba869800bfc434c001ffb126000bfd8930007fcc498003fd624c001fe3126006bf18930077fea49803b7f524c01dff292600eff54930006faa49803bfc524c001ffa126000ff90930007fa8498003fc424c005ff9926002f7cc930017fc649800bfd324c001ee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c01dffa8a600eff94530077faa29803bfc514c001ffa0a6000ff90530007fa829800
  | 3 => 0xfb1a4200bfd8d21007bec690802df6348433ff31a4202bf98d21007fac690802fd6348433fe31a4202bf18d21007b8c69080adc6348435ffa9a4219ff94d210d7faa690867fc5348401ffa1a4219ff90d21007fa8690867fc4348435ffa92421adfd4921037fca49086bfd5248401bea924206ff14921007fe849081bfe4248401fea124206ff109210cffe649081bfe3248401f71924200ff4c921007da649081bfc3248435ffa8a421aff945210d7faa29086bfc5148401ffa0a4200ff90521007fa8290803fc4148433ff98a4200ff8c521007fa6290867fc314840dff90a4206fdc8521007fc4290803ee2148401ffb024200bfd81210c7fcc090806fe6048401feb024218ff1812100df8c09086bff5048431ff282421aff541210c7f8a090863fe4048431fe2024219ffcc1210c7fc6090863fc3048431ff1024206ff081210c7fc2090863fc104840fffb284206bfd9421037fcca1080efe650840dbf32842039f99421037faca1085afd650840dbeb2842009f5942103ff8ca1081afc650840fffb204206bfd9021037fcc810802fe640840ddf3204200af99021037fac810802fd640840ddeb204200af5902103ff8c81081afc640842dffaa04216ff950210b7faa81085bfc540840fffb184206bfd8c21037fcc61080afe630840def3184202b798c21037fac610802fd630840deeb184200b758c2103ff8c61081afc630842dffa984215ff94c210b7faa610857fc5308401ffa184215ff90c21007fa8610857fc430840d7f3104206ffd4821036fea41081bfe520840dfea904206df54821037f8a41081bff420840dff2104206ff50821037f8841081bff320840dff1904206ff4c821037f8641085efe610842dffa884207ff944210b7faa21081ffc5108401ffa084207ff90421007fa821081ffc410842bff9884207ff8c421007fa621081ffc310840dff9084206fbc842103ffc421081bf6210840dfe9084200fb48421037ea421081fff600840dff3004201bf98021037f4c010806fa600840dfeb004200bf58021037f2c010802f9600840ffe3004201bf180210b7fea010853fe500842dfea804214ff140210a7fc8010853fc400842bff9804214ff8c0210a7f8601081bfe200840dfe1004214ff8402103ff8201084bff65d00277fb2e8013ff9974001dfccba004ffd65d00277eb2e8012ff1974001df8cba0006fe64d0027ffaa68012ff9534009f7ca9a004ffd54d0027deaa68012ff15340097fec7a0047fe63d00057f31e8000ff58f40005fac7a004bfc63d00057e31e8013ffd4f4008ffca7a004ffd53d0023fe29e8012ffd0f400077e87a0047fe43d0001fea1e8000ef50f40097f887a004bff62d0001ff3168006bf98b40007fac5a0002fd62d0025fe3168013ffd4b4009efea5a004ffe52d0027fea968000df54b
  | 4 => 0x80bdc314c405fa18a6200ffd8131005fec098883fe604c4037f3026200ff58131107f8c098806fc604c443ffa826220ff9413110ffaa098883fc504c441ff2026220ff10131017fe609880bfe304c405fe1826220ff88131107f84098883fe104c441fe0826206ffd9721035fecb9081bfe65c84077f32e4206df9972101cfccb9081bfd65c843f7eb2e4206df59721004facb9081bfc65c840d7e32e4206ffd9321035fec99081bfe64c84017f3264206ff59321005fac99081bfc64c840d7e326421fffd53210fffca99087ffd54c843ffe2a64206ffd8f21035fec79081bfe63c84057f31e4206ff58f21005fac79081bfc63c840d7e31e421fffd4f210f7fca79087ffd53c843dfe29e4200ffd0f210f7fc8790803fd43c843dfe21e4206ffd4b21036fea59081bfe52c840dfea964206df54b21037f8a59081bff42c840dff2164206ff50b21037f8859081bff32c840dff1964206fb8cb21037fa6590803ed32c840dfe196421fffd47210fffca39087ffd51c843ffe28e4200ffd0721007fc8390803fd41c8401fe20e421effcc721007fc6390803fd31c843dfe18e4206ffd8321037fcc190806fe60c840dfeb064200bf58321037f8c190806fc60c843fffa86421dff943210fffaa190877fc50c843bff206421dff103210f7fe6190877fe30c843bfe1864206ff88321037f84190877fe10c843bfe0864207ffd96210bdfecb1085ffe65884077f32c4217ff596210bdfacb1081ffc65884077e32c4207ffd9221005fec910803fe64884017f3244200ff59221005fac91081ffc64884017e3244217ffd52210bffca91085ffd548842ffe2a44207ffd8e21005fec710873fe63884057f31c4200ff58e21005fac71081ffc63884057e31c4217ffd4e210e7fca71085ffd5388439fe29c4200ffd0e210e7fc8710803fd4388439fe21c421abf58a210bffea51085f7f528840dff2944217ff54a21006faa51081bfc5288401ffa144206ff90a21007fa851081bfc4288439ff9944206ff8ca21007fa651081bfc328840d7f30c4217ffd462103ffca31085ffd518840ffe28c4200ffd062103ffc8310803fd418840ffe20c421cffcc62103ffc6310803fd318840ffe18c4206ffc8621007de431081bf7218840fffb04421bff9822100dfcc110803fd60884017eb044207ff1822100df8c11085fff5088437ff2844217ff542210dff8a11086ffe4088437fe204421cffcc2210dffc611086ffc3088437ff1044206ff082210dffc211081ffc1088435ffb2a421abfd95210d7fcca9080efe6548435feb2a421abf595210d7f8ca9080efc6548401ffb224200bfd91210077ec890802bf6448401ff3224200bf99121007fac890802fd6448401fe3224200bf1912100778c890802bc6448435ffaa2421aff951210d7faa89086bfc5448401f
  | 5 => 0x4c41137faa620897fc5310425ffa188225ff90c4112f7c8620803fd4310425fe2188225ef10c4103ffec420803fe621040d7f3108200ff58841005fac42081ffc621044dffa908226dfd4841137fca42089bfd5210401bea908226ff14841097fe8420803fe4210401df2108200ff50841097f88420803bc421044bff9908200ff8c841007fa6420897fc321044f7f3088226ffd444103ffca22089bfd511040ffe2888212ffd04410077e822081ffe4110401fb2088200ff504410077a8220803f5411044bff9888207ff0c44103ffec020893fe60104037f3008200ff58041005fac02081ffc60104037e3008226ffd4041127fca02089bfd5010449fe2808224ff90041097f88020897ff3010449ff1808224ff0c041127fc4020893fc2010449ff0808207ff0404103ffecb1888eff658c447ff32c6203bf9963111ffacb1888efd658c40ffe32c6203bf1963103ffec918802ff648c401ff3246200bf99231007fac918802fd648c40ffe3246200bf1923111ffea91888ffe548c447feaa46223ff15231015fac71880bff538c405ff29c6202ff54e31017f8a71880bff438c401efa1c6202ff90e31017fa871880bfc438c405ee21c6207ffd8a31007fcc51881afe628c401feb146200bf58a3103ff8c51888fff528c447bfa946223ff94a3111ffaa5188037d528c447fe2946200ffd0a31007fc8518803fd428c401fe2146202ffcca31017fc6518803de328c405fe9946202ff0ca31017b8651880afe618c447ffa8c6207ff9463111ffaa31881ffc518c401ffa0c6207ff90631007fa831881ffc418c405ff98c6202f7cc631017ee631881ffc318c405fa18c6207ffd8231117fcc118806fe608c401feb046200bf5823103ff8c118806fc608c447ffa846222ff9423111ffaa11888bfc508c445ff2046222ff10231017fe611880bdf308c405ff1846202ff0c231117fc411888bfc208c445ff0846207ff0423110ffeca98886ff654c443ff32a6203bf9953110ffaca98886fd654c443fe32a6203bf19531007fec898802ff644c401dfb226200afd9131007fcc898802fe644c401feb226200bf59131007f8c898802fc644c401de3226200af1913110ffea898887fe544c443feaa26221ff15131015fec69880bff534c405ff29a6202ff54d31017f8a69880bff434c405ff21a6202ff50d31017f88698803ff624c4017fb126200ff98931007fac498803fc624c40d7e3126221ffd493110efea498887fe524c443fea926200df5493110ff8a498803ff424c401ff2126200ff50931007f8849880bff324c405ef9926202ff8c931017fa6498803dd324c405fe1926202bfd853110ffea298887fe514c443fea8a6221ff14531007fe8298803fe414c401fea0a6200ff10531017fe629880bf7314c405ff18a6200f78c531017f86298
  | 6 => 0x1fea168200ef50b41097f885a08bfff32d0401ff1968200ff4cb4117ff865a08a3ff51d0451ff28e8228ff54741147f8a3a08bfff31d045ffe18e8212ffd8341177fcc1a0806fe60d0401feb068200bf58341097f8c1a0806fc60d0451ffa86822eff94341147faa1a08bbfc50d045dff2068212ff1034117ffe61a08bbfe30d045dfe186822eff88341177f841a08bbfe10d045dfe0868207ffd964113dfecb2089ffe65904077f32c8227ff5964113dfacb2081ffc65904077e32c822bbf5924113ffea92089ffe549044ffeaa48227ff1524103ffec7208b7fe63904057f31c8200ff58e41005fac72081ffc63904057e31c8227ffd4e4116ffca72089ffd539045bfe29c8200ffd0e4116ffc87208b7be4390401fea1c822dff10e4116f78872081fff6290401ff3148206bf98a41007fac520802fd629040ffe3148227ffd4a4113efea52089ffe529044ffea948200df54a4113ff8a520803ff4290401ff2148200ef90a41007fa8520803fc4290401de214822dffcca41007fc6520803fd329045bfe1948226bf9864113ffea32081ffe519044ffea8c8207ff14641007fe8320803bf4190401fba0c822dffcc64103ff8632081fff6090459ff3048201bf98241007fac120802fd609040ffe3048201bf1824113ffea1208b3fe509044ffea84822cff14241167fc81208b3fc409045bff984822cff8c241167f861208b3fe2090459fe104822cff8424103ff821208afff65504577fb2a822bff9954101dfccaa08affd65504577eb2a822bff1954101df8caa08afff5450457ff2a2822bff5514115ff8a8a0803ff63504017fb1a8200f7d8d41005bec6a08abfe63504057f31a8200ff58d41157f8c6a080afc6350401ee31a8202b718d4115ffea6a08abfe5350457fea9a822aff14d41007fe86a0803bf4350455ff21a8200ff50d410077a86a08abfc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128206bf1894115ffea4a08af7f5250457ff292822bff54941006faa4a08affc5250401ffa128200efd0941007fc84a0803fd4250401dea128200ff10941157fe64a0803fe3250401fe992822aff0c94115ffea2a08affe5150457fea8a822bff14541007fe82a0803f74150401ff20a8200ef90541157fe62a08abfc3150401ffb028200bfd814114ffcc0a0806fe6050401feb028229ff1814100df8c0a08afff5050453ff282822bff5414114ff8a0a08a7fe4050453fe202822affcc14114ffc60a08a7fc3050453ff1028229ff0814114ffc20a08a7fc105040fffb288226bfd9441137fcca2080efe651044dfeb288226bf5944103ff8ca2080efc65104517f3208226ffd5041097fca82089bfd5410425fe2a08207ffd8c4112ffcc62080afe6310401feb188200bf58c4103ff8c62080afc631044dffa988225ff9
  | 7 => 0x2104bfc401086bff9808434ff8c0421a7f8602101bfe201080dfe1008434ff840421a7f8202101bff658c80d7fb2c6406ff9963201dfccb1901b7e658c8073f32c6406ff5963219dfacb1901b7d658c8013eb2c6406ff19632035f8cb1901bff648c80d7fb246406ff99232005fcc91901bbe648c8015f3246406ff59232005fac91901bbd648c8015eb246406ff19232035f8c9190cfff548c867ff2a46433ff5523219ff8a91900afd638c805ffa9c6402ff94e32017faa71900bfc538c805ffa1c6402ff90e32017fa871900bfc438c80d7f3146406ffd4a32036fea51901bfe528c80dfea946406df54a32037f8a51901bff428c80dff2146406ff50a32037f8851901bff328c80def9946402fbcca32037f8651901bec328c80dffb0c6406ff98632005fcc31901bfd618c8017eb0c6406ff1863219ffea3190cffe518c867fea8c6433ff14632017fe631900bfc318c805ee18c6406ffd8232037fcc119006fe608c80dfeb046400bf58232037f8c119006fc608c867ffa846432ff9423219ffaa1190cbfc508c865ff2046432ff10232017fe611900bfe308c805fe1846406ff88232037f841190cbfe108c865fe0846431ffd953218dfeca990c7fe654c8077f32a6431ff5953218dfaca990c7fc654c8077e32a6400ffd9132005fec899003fe644c8017f3226400ff59132005fac899003fc644c8017e3226431ffd513218ffca8990c7fd544c863fe2a26406bfd8d32017fea69900bfe534c805fea9a6402ff14d32017fe8699003df434c805ff21a6402ff50d32017f8869900bdc434c8057fb126431ffd493218efea49901bfe524c863fea926400df54932037f8a499003ff424c80dff2126400ff50932037f8849900bff324c805f79926406ff8c932037bc649901bfc324c80dee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c863ffa8a6431ff9453218ffaa2990c7fc514c805ff98a6402f7cc532017f86299003ff604c8017fb026430ff9813200dfcc099003fd604c861fe3026401bf1813218ffea0990c3fe504c863fea826430ff14132187fc80990c3fc404c805ff9826402f7cc132017fc609900bfc304c861ff1026406ff08132187fc20990c3fc104c825ffb2e8228bfd9741147fccba080efe65d0451feb2e8228bf59741097f8cba080efc65d0451ffaa68212ff95341147faa9a084bfc54d0425ffb1e822fff98f41015fcc7a0803fd63d04017eb1e8212ff18f41015f8c7a08a3ff53d045fff29e8228ff54f4117ff8a7a084bff43d0401dfa1e822fff90f41007fa87a0803bd43d0425fe21e8212ffd8b41007fcc5a081afe62d0401feb168200bf58b41097f8c5a08a3ff52d0451bfa968228ff94b41147faa5a08037d52d0451fe2968212ffd0b410077e85a0803fe42d040
  | 8 => 0xf59642036facb210027d659080dfe32c8406bf196421d5fac9210f7ff549087bff2a4843dff552421eff8a92101bff639080dff31c8402bf98e42037bcc72100ade639080dfeb1c8400bf58e42037bac721002dd639080dfe31c8406bf18e421effea7210f3fe539087bfea9c843cff14e42007fe8721003bf4390879ff21c8400ff50e420077a87210f3fc439080d7f3148406ffd4a42036fea52101bfe529080dfea948406df54a42037f8a52101bff429080ddfa148400fbd0a42037fe652101bfc329080dffb0c8406ff98642005fcc32101bfd61908017eb0c8406ff186421effea3210f7fe519087bfea8c843dff146421e7fe63210f3fc319080dffb048406ff9824200dfcc12101bfd60908017eb048406ff1824200df8c1210f7ff5090877ff284843dff542421dff8a1210effe4090877fe204843cffcc2421dffc61210effc309080dff1048406ff082421dffc21210effc1090875ffb2a843abfd95421d7fccaa100efe6550875feb2a843abf595421d7f8caa100efc6550875ffaa2843aff951421d7faa8a10ebfc5450801ffb1a8400bfd8d421cffcc6a100afe6350801feb1a8439ff18d42015f8c6a10ebff5350873ff29a843aff54d421cff8a6a1003ff4350873ff21a8439ef90d42007fa86a10e7fc4350873de21a843affd49421d6fea4a101bfe5250875fea928400df54942037f8a4a1003ff4250801f7a128406ff909420377c84a10e7ff325080dfe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542005f8c2a10ebff5150875ff28a843aff545421d7f8a2a10e7ff3150873fe18a8400ffd8142005fec0a10e3fe60508037f3028400ff581421c7f8c0a1006fc6050875ffa828438ff941421d7faa0a10e3fc5050871ff2028438ff101421cffe60a10e3fe3050871fe1828438ff88142037f840a10e3fe1050871fe0828406ffd9442035feca2101bfe65108077f3288406df9944201cfcca2101bfd651086d7eb288406df59442004faca2101bfc651080d7e3288437bf990421b7fea82104bfe541086dfeaa08412ff15042037fec62101bfe63108057f3188406ff58c42005fac62101bfc631080d7e3188436ffd4c421affca6210dbfd531086bfe2988412ffd0c420077e86210d7fe4310801fea188400ef50c42097f8862101afe621080dffa908406dfd4842037fca42101bfd521080dbea908406ff14842037fe842101bbf421080dff2108406fb90842037fa842101bbd4210801f6a108406ffcc842037f8642101bff611080dff3088400bf98442037fac221002fd611080dfe3088436ffd44421b7fca2210dbfd511086dfe2888435ffcc4421aff8622101bff601080dff3008401bf98042037fac021002fd601080dfe3008401bf180421b7fea0210d3fe501086dfea808434ff140421a7fc80
  | 9 => 0xc8bfea968645ff14b43017fe65a180bdf32d0c05fe1968612ffd8743007fcc3a1802fe61d0c01feb0e8600bf58743097f8c3a1917ff51d0c8bff28e8645ff5474322ff8a3a180bff31d0c05fe18e8602f70c743097fec1a1913fe60d0c037f3068600ff58343005fac1a184bfc60d0c037e3068645ffd4343227fca1a1917fd50d0c89fe2868644ff90343097f881a180bff30d0c05ff1868602ff0c343227fc41a1913fc20d0c89ff0868644ff0434321ffecaa190eff6550c87ff32a8603bf9954321ffacaa190efd6550c87fe32a8603bf19543015fec8a190fff5450c87ff2a28643ff5514321ff8a8a180aff6350c05ffa9a8602ff94d43017faa6a180bfc5350c05ffa1a8600f7d0d43017fc86a180bbe4350c05fe21a8602ef10d43017b886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c0d7e3128643ffd494321efea4a190ffe5250c87fea928643ff14943017fe64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8600bf1854321ffea2a190ffe5150c87fea8a8643ff14543017fe62a180bfc3150c01ffb028600bfd8143217fcc0a1806fe6050c01feb028642ff1814300df8c0a190fff5050c85ff2828643ff54143217f8a0a190bfe4050c85fe2028602ffcc143017be60a180bfe3050c05fe1828642ff88143217f840a190bfe1050c85fe0828600dfd9152006fcc8a90037d6454801be322a400dfd8d5220efcc6a90037d6354883be31aa400dfd0d5220efc86a90037d4354883be21aa403dfd895201cfec4a900f6f6254883bf992a406df0c952006fec2a90037e6154801beb0aa400df1855220efe62a91077c3154801bfb02a440df98152006fac0a91037c6054881bf202a440df1015220efe60a91037e3054881be182a440df88152036f840a91037e1054881be082a412ffd97421bdfecba10dffe65d08077f32e8437ff597421bdfacba104bfc65d08077e32e8437ffd5342097fca9a10dffd54d0825fe2a68412ffd8f421fffcc7a100afe63d0801feb1e8400bf58f42097f8c7a100afc63d086fffa9e843fff94f421bffaa7a10fffc53d0825ffa1e843fff90f421ff7c87a1003fd43d0825fe21e843fef10f421bffea5a10df7f52d080dff2968437ff54b42006faa5a101bfc52d087fff9968406ff0cb42097fec3a1003fe61d08017f30e8400ff58742005fac3a104bfc61d086fffa8e8437ff947421bffaa3a10dffc51d087fff98e843fff0c742097fec1a10fbfe60d08037f3068400ff58342005fac1a104bfc60d08037e3068437ffd43421f7fca1a10dffd50d087dfe286843eff90342097f881a10ffff30d087dff186843eff0c3421f7fc41a101bfc20d087dff086843eff04342037fecb2101aff659080dff32c8403bf99642036fccb2100e7e659080dfeb2c843db
  | 10 => 0x1c00000007c0000780140cc00800400c00800003400800001400c00000c0080100040400000bc09800000803001801c07c00400800005401800008804000403000c0080180000140380140040000000500400900000741f000002403405401c0a400406800c00002c09806408801016402000c00000400404800006407c02002000001c01401c06000400c00400000400400001c00400000c00400000c00402800001404000401401800405800c0100080a802c00402c00809002c0c800c05c02405400019400400400801c00000408412401408000805800803400400800403800000000000000800000000c02c00804c0480080a400403c00405c03000000400800804809400009c04409800406400000002000400006404c00c01c0000040240a002000001000409000401801801c07401004000800801400000000801401005000001c00000828c00005c03001400400802800000400002000000404004001000805000800c1300000000300000000100040180040000000000c805c00001800000404000c05410401000001c00802000000004802804c02402000400000402406407000003400001800001004400804401001001400000000800000003002c09800001c01405001409800400804404000800402400000400426400405400c00801402400003000404010c02816c00c01808803801409804800405000000003000000001000c00001000004800000001400000401400800000000001403c04409c01c0040000000a807402c0240c400002c00805400c01800400801800c00c00400001c02003002400001c00800401000000000000801804805c0280700180000380000380240000080000d802c00401000000803c02800c0040b00000040780000000b401000001800000001406805401801409c0000040c000401805c02000000003400c00000003c02000c00c00001400001c04c03401800000c00000405407c01c0400040140100540000000080000000080540000040040200000200000a401006403000001c0b403800808810c01003012c00c0140040540280a00000000a80100640180000b401000c0bc0d401c00c03401000800c05000406000401800403002c02404800000c0440000000040940000180000140001bc0000000300140380180e000003c09400c0000100140480300e001832004400002808000001409802001c00c01c00c25ffb2e8645bfd974322ffccba180efe65d0c8bfeb2e8645bf59743097f8cba180efc65d0c057f3268645ffd5343097fca9a1917fd54d0c25fe2a68602bf58f43017fea7a180bfe53d0c05fea9e8602ff14f43017fc87a180bbe43d0c05ef21e8602ff10f430177887a184bff62d0c01ff3168606bf98b43007fac5a1802fd62d0c25fe3168645ffd4b4322efea5a1917fe52d0
  | 11 => 0x3774368000af87e000010fc00031900005f482e51503e95b00ea263000077c3d026d02b8a1404200038580000006480b98238864479035a1003e410239e84bc73421a1c39c6cc8a2cf0cd1ae0db665131b978804632d04093c4f905c61e80c9cda27770331fdcd4425908208ac51408600020c824477f15b1f9884a89a00014f084850b23a1f086b233e0941ffc0a278e049158c9d624e3f90a4c5a86281d788b4e788b740120f03f855e176160c0000001fd19e0900529343a174c108b404a8f481ac7aa0000298b0000000d00000004ec329a03c24c38c3679354c3818f305000062666b0001fcc000698248895854844d2509f9057e000000107440073a378133800065b3551e4093c2260899a44000586000054c0004e01a400000000003370220f6e1670000fc4e7c316017000000005b1db91245b00000001b040001f82f70bd00005660000900c622601bc0000a124a042b17f80006933269ca0fba4e20001d3c00027b00000006be00006e81c000085a0000000e6e000038800054437d000016057033b435054880661d3338000ba207921e1ab8c7458733f16a89fe7db14d226cfa81432a99a0439451a1919274eca1472811a740003d60ec829c55c45e0000c44d180360001f5884c06d0e69de877a1560f896a462809e2ed998c9444810fb0e9c49e7fd0081414a2c2e418d95b50d817012d83ccd726d338085601263d308396ec2ba3c91438f68d204a905c122c3e038245b16dc3f67933710674ee449a2061608e088424038be90c85b105a886d15c5d844888c41e41de0001ee09f46520f7000089e1e73c41754144554234133485639c00004cc00000041f800c0001c333a93501fa4bb1ed80006c67082a286349ce50c0001940d980243361370c1c00007198a81ce3a12870164dc80003508d548447a73fa0000f2a2194491abce4e52000000010820002460838de68af01e00001160000fb828c1ec30615299a084e25f42584dce827d30000a548966362a194dc1967131fd800027e533131000000000000002f42d4602256193c43e0f800021940000000881048bee83e41c0000904351000000000c01003c00402801c0e810000400000002000419400000000001018800801401001406000c03000002400402c00423000002800803c00800401800401002000c00000405400400404400400403c0000cc00002001400400818c0b017c03001400402001c03400802801c00800800801804400001c00800003804006401800000800000403c00405800400001400007000000c0000100d401003801c00808001400000800800800401c02c00001000004003000002000401400400809806c00000000000008c01801400800000400802401c06805000407802800c02001400003002401c00c00400403403000800002801403c01
  | 12 => 0xe4a5a301380009b60000f0800000006500000009a27e100000010f268e333124000015a009028487435229515a477887a0001e2c5f23e93d602d80000fc3d09b282f43180001c1c8901930000d30b1e24b1cf22e42ee32c1c885f88302c635f1c5026a5a21ff162ce5c4ab397910506c5102e6800051a114140949817c8243f896b4c9c18b24c1fbc64c3eb0001d2c8f452422c99d800043b341000000031d0dc213ca825313b404005b87973ad88c86f40002cc8908ef003b0f69d8044a000221a110b485a01e78d08dfe3ab1b79cc8fa21630001ecc08800e000075419c52e00588fc0007a000000010187b000006401724c10640d00e8833644603e876461f1741630aa460f1778330e4c0002088000000851000000000089935a99842345563fc9d70e925e7387800000087d000217c96c26f08b8000000000111967470c3e8098166800000023680000003350ca89249144b034d87e89b02461fc00000004c528a000000032b186a19cac46d72650000f860003cd9100c0c2762e985a0f920004138f910285df1e700000626f5014000000062639689b00000000000000000000023000000044a3a000000005571cb22e8c4610316597a88683330000000a7059018d05e4e7247639a197c0004211ffa2810726a33b3131891252219b9148bc00ad257101464426916e8acc4583433588c400006de34b80003c000027e8000ad445a04d84b400051b40900008c28b11ca9bf8f443711ea80005947310000000e7627013b91fcc12000095800000033013a8274af6000000000002a00033100007b27e52981a9446650038a8e4c00070a1d18b68fd60000001ec80002ad0000420d76266170129063e2c83e7127000036400009840003ed0e0a0100000c41be05ec73667c00f0c94fb439703991ccb4e18e06193590a00160f4a18056a86f009800023263b1610b3054c8590f20b7cdb24453999d750b800037a12cc0a039003222ec16049237e14a04905910db800032e5ff1491df40001f91bb02b8e7061024f8d1458a7424530000b6c71c2b88fc87d80d20001ee400084e3378044d9a0000001c644987e73fb0340bc224a24a89e0d1a4ef0000ad068e4444170000000062312894078600000b9e643963003421f1804079103b80000000000e2000056001c2f400010a843613d000000068000005887d4000000126d11a00009a00000008b8342800000042e35600000004c70001fb80000000038add06622407d8590d660000000fb8a0c33a3aa9108b7e03f0050f447482e137000001fe312000000088c06911f1a90000000000000015683d0249d90a4a0000002114de27d011e8e984e608f0000f9c96837b0500b8cd3c74528c8744a2615f2d40000a461380001e7cd866b71500fd00006bc4470d40cca1862a00000dfa4bc1a08000
  | 13 => 0x80000c12f91c8504a3282a51eb451038a18416f851852c1cc000050869c06688346ea29b06c99e84280260a800dcb2a0000d088489dc4ad000153000057f0001a7c59a2db40c000013e0003b780000005b40001efc77c7572fb04543280000890e2000048f1d0080510c00033206a47586a700022b4b862e93ab0dfc0123fd206890c0005392e415d475c6c51759df065c6e1012800073a2523e61fe80006c236e06c42922fb3dd17bc0000430c621c097c0002fe91600280ee0000000ffc0002d791a4b2c018000048cf141a7400a0a0c402641179b488ea3ef00e810863807215392f4d9673626006a8c721a40d0171114a78c3b88ff007a4882d700a411a57022b8d60eea15916f220c8666ea07803084a22154249fa4a2232100001809d260c11480b014a4621a2152408a4fc0000a44cf6217368001436434e35e9d889d41f4209869471c62e3da14f880018437419a88ca44716185b80000000fe88e87980000d58d9c26c8260d800010d00000cb0d846b829d00022a48040000000000b4c0e91418aa8f2c0c50000c3003e45b287962112859f1b587746540000b31db503a29712a126433c29c0000c2cba85e60ed82bcdd845d000137c42046f1db0f8d1425641799764a746b61b70f7879a8030698008aba0003159b543c43a230d03440000f91ae8000f804d212b8d18d888100001db103800f37298c8b420ba2fc800075a2d138b0ba916400000008880007764439c9077e40f1e30f8053045c09216347803ba18194604f275824a0bdc7ca11b0871214f383012150a005f881a15d18140a820b0db02c474a03508f87ac6e61b30a89a1809e25c0bf9eac87a8881089a250d21852e610503d4706103094ce5840b33815390943390831714b2e0630ee10d4b5831e0be05bc1506d442d8d2ce9402a317962487081f2168eec6646b043318b4b3c2f817106440987de33a09c80724fe11820206ca8480f9a000a7603e44f1cfc57854d1fc930c6480982009f050744b203089a102e58e293919c55013112089547ee6552bc0bb866858a05b929c1683b13af99244fe60d0d7071509830f1b8025024a41a0cc21d905e59833b947cf4c70506b89a80005b909604b918074c3e798782e403a0110e6400065616703c47165fc0e022148f88c244492c430254b25411ac9986ef4499fe08e02891c90b1c0007300d18d787884e6137153d04087702b086021e410004000000057928180b494638904210c47540c604e0b045ce89f00020340007541ca0bf43d800000020840d02373441bed0686382e905d096a79a4410cc50c666016497a403200023600005320002a41d451826301358c24d6487f22981bc8464e50068000c2873541a92dc65247207f13240942672ed230c4500002438000f8e8b34310abce90000000073c00057d39590c07e0000
  | 14 => 0xf3a1410ce18d50a42f60a5026812200027d885846a00022a0000f1200139497000004de000186400000011396e80000003e913d02167432048e0cf046c72640f1cd5a6e318211800000000001ebce040000001ff000036c06d1848c0205c13a16f0a1025e43a00000820e8000119112056b00007380000000b680000000000000000000000000107800044c27b037807039f36e9a64f0880e000151000005f2d90874e2e20f2f194f41e867208f1d8c22c5eb1e504f437c59c32c01f800044e44b1390aa0000415a0a84060bb0ae079917c04d0b021f00002452ad97e83a4643070a024a841d700017e081c46a00022886e821c32d19011140000001bd810e53600001b8ba07462e580000005f12991be40000000002054a3c00035308140f83dc3d289f513071a1aa01fce9c7ed386106cc440003a9957d138711269a29c6404f3321074cf9a0a923e9210ae47813b50824be67591ab86d4ac24aa3dd8e042c228e3b3855421a00034522fc0007e2183a1d4bba42903d0ac86fc7c40000000fb800006d8264d9029f000000095e290000000000040642f00000000001978000c7e0003a39c3446c0000000f2c00067d37b820040e81e0000224d1600044e871c6f20851011910b265343efa2009722650298c285e00000d69e78766000355984c0006b428510b086e7a928915d8db05c100001d0fd053f1ee8ae46c400026d000000063c0000ed43444502a304e457c2f20a21144be04d70ed00010580001c29b7cf6a0000000b4c3c652b05906ed15400015196f4ddc0c70000b4000018708083d50140000030698c3067110f00000000000000b10cba6e70a6195cafc8580000e3cb6086e4111aa00641420000f500006341e09ef006822a2b40c540007181f10fd891a8550c016946d41453ad0000f7c4bf36d1d4011423b27c1c8880e0c0374862425278600000000006c90ad8000b282fe276a2ac0001923039ae912e0002d999e4f94140000000099e5ec1a51da4ac05c70a315601180d816ba2d49745810f280111481d42da8328adc8a81ad03907be40a238918c9c280b2b981789ee14d02d00006700bc24b9e1433e05515d852c00062c13f000090c70e23300000006ce40c9e0c5287ea1050dc8dcc0ec0e3138c8404c4033a14c85e0473f189c47cc55a09004702743d804183886924f505f9ded0600e5438986d0361b43b090a0bea6472e48608ade8953f6084c4f86333258db4d5200018710f8fea43926c84ec4107870001794ab217500013e47705de2418ea44ba41519ea01401859b0d78b9819e75210600001c02f5439025c23a5e40e40d34e465f400006f0cb27802bb800000000006480009e44772eb19500000002a880011165741d41bac69e2044561afc1cc1fe1b00b941da55c0a7060c26428238183ac000000442201
  | 15 => 0x3682922a9de4edc0ac3800000c4e238000096012c1d83bf1e600001f53630884e9a5841b4800050c0002740d980001654218000c2a0002370f0918849617f9a5410471e1561f1456260427819b449a2a903c20ec53c84d3001918dac8310dd172902c3800908000c7c41f3f8170824e4a50e8055c3727732fd837c31064c16902cc1aa2ed08505c41208573fd9eb867e1781f9a11c5426f20b4941c9a00d44358d5876028b0f78578c9482d339975ca6a03034a1dc092630528b83a80ba8a32b281ece120483c69614bb83c84629c803fe1cc0e480000804b81c21ec43840001f080011606410350af43143c52b38a3c350302000000000038d2d5943517a0000d60000f28000082a0dccb840820b1f602d872a0000b590e614f29797b4c2e0002c914704884dd0de951cf4652d37c1a48a427a80849a0c37e8811601a3cb9e0f701782902d622e45e02a8f6c55506e1ef4dda2d523c204ccfe78f0000d6cd2c1d61da046009c6210cc99a40006fa3eb930800048e17881d8096846305a1f8f4877403604440560001100a58af43f52e7115827871d0a40000c7a51d28205d87ae2392020da0ebc2473501070f2486100008d04b476b0000cf000087b388000027c00043c000000065e22f980c0000000951f2c94c4191559f5499662434d11f8d8000007794050225b800004302a83173149c4911e82330880cce3e2d923d800000000030b08f00a43531dc9f6433600
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf654c51010e7c654c510005bf744c510005bc744c510006df634c510016dc634c510005fb704c51000df8704c51000cfe76c851000cfc76c851002d7e75c85100057d75c85100067f65c85100fe7c65c8510006ef62c8510036ec62c851000dfa70c8510005f970c85100a4fe76885100067f65885100be7c658851000df8708851003ff010885100a5f67688510006f67688510265f77588510265f5758851000777658851025f7465885100c5f57288510036f66288510036f4628851025f77528851000775528851003ff3708851000df6708851000df4708851003ff0708851003ef760885100dff230885100dff22088510034ff764851000cfe76485100c4fd764851000cfc76485100067f65485100d67c6548510005bf7448510005bc7448510005df7348510025dc7348510006ef6248510036ec6248510005fb704851000df870485100c7f0104851000df47648510036f4764851000cf47648510255f77548510255f5754851000777654851024f746548510007b77448510007b47448510007d77348510007d47348510007e77248510007e76248510036f66248510036f46248510007e4624851024f775248510007755248510007e63248510007e53248510007f3704851000df6704851000df470485100c7f070485100c6f760485100c7f230485100c7f220485100dcfe760851002d7e75085100057d75085100067f65085100b67c6508510005be7408510005bd7408510025de7308510005dd73085100ddf6710851000dfa7008510025f8764c110016f8764c110014f8764c1100077b654c11024778654c11000dfb734c11000fdb734c110007db634c110016fa634c110016f8634c110027d8634c110027da534c110247d9534c110027da434c110007d9434c110005fb724c1102477b524c11000779524c110027db324c110007d9324c110007f3714c11003df8714c110007f0714c11000efb614c11000ff3614c110247f2514c110247f1514c110007da314c110027d8314c110007f2214c110007f1214c110005f87648110036f87648110034f876481100077b654811023f786548110005fb7348110005f9734811000dfb724811000feb7248110007eb6248110036fa6248110036f86248110007e8624811023f7b524811023fea524811000779524811023fe95248110007695248110007f3714811003df87148110007f0714811000efb614811000ff3614811023ff2514811023ff15148110007f22148110007f1214811000dfa76c411000efa76c411000cfa76c41100077b65c41102377865c411003dfb73c4110005f973c411003dfb72c4110005f972c41102377b52c41100077952c411000dfa71c411000ff271c411000efb61c411000ff361c411003ff251c4110237f151c411003ff221c4110007f121c4110
  | 1 => 0x8910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910006ef72589100067f52589100ecff7158910006f771589100c4ff7058910006fb70589100dcfe761891002d7e75189100057d75189100067f65189100067c6518910005be7418910005bd7418910025de7318910005dd7318910036ee6218910006ed62189100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549100067e64549100067d64549100067c64549100067f635491020e7e63549100067d635491020e7c63549102757f725491002f6f72549100067f62549100367e62549100067d62549100367c62549100077671549100077571549102067f61549102067f60549102077a30549102076f20549102077a20549102076d2054910207761054910207741054910207781054910094ff76d0910004fe76d0910004fd76d0910094fc76d09100067f65d09101be7c65d0910096be64d0910006bd64d0910006ef62d0910036ec62d0910034ff7690910004fe7690910004fd7690910034fc769091002d7e75909100057d75909100067f65909101ee7c6590910006bf6490910006bc6490910025de7390910005dd7390910005f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101d67c6550910006be6450910006bd6450910034ff7610910004fe7610910004fd7610910034fc761091002d7e75109100057d75109100067f65109101b67c6510910006bf6410910096bc6410910006ef6210910036ec6210910005f67110910005f5711091000dfa7010910005f97010910034ff768c910004fe768c910004fd768c910034fc768c91002d7e758c9100057d758c9100067f658c91019e7c658c910005be748c910005bd748c910006df638c910016dc638c910005f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91018e7c654c910016de634c910006dd634c91000dfa704c91000cfe76d051000cfc76d05100067f65d05101467c65d0510006bf64d0510096bc64d051000dfa70d0510005f970d0510124fe76905100067f659051013e7c6590510006be6490510006bd6490510094ff765051000cfe765051014cfd765051000cfc76505100067f655051015e7c6550510006bf6450510006bc6450510005df7350510025dc7350510005fb705051000df87050510164fe76105100067f65105101367c6510510096be6410510006bd641051026cfe768c5100067f658c51011e7c658c510016de638c510006dd638c51000df8708c510014ff764c51000cfe764c510104fd764c51000cfc764c5100067
  | 2 => 0x174ff7159110006f7715911014cff7059110006fb7059110164fe76191100067f65191100067c6519110006bd6419110094ff751911001cfe7519110004fd7519110094fc7519110096be7419110014fe7319110004fd7319110014fc7319110006be4319110096bc4319110034fe7219110004fd72191100067f521911003cfe711911003cfc711911003cff701911000cfe7019110124fd701911000cfc7019110096bf4019110126bd4019110014fe76d8d100067f65d8d100067c65d8d10026de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10094fe74d8d10004fd74d8d10026dc43d8d10034fe72d8d10004fd72d8d100067f52d8d10026dc32d8d1003cfe71d8d1000cfd71d8d1003cfc71d8d10026df31d8d1003cff70d8d1000cfe70d8d10114fd70d8d1000cfc70d8d10116df30d8d10116dd30d8d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10026dc6358d10005ef7258d10005ec7258d1027df77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10094fc7458d10006bc7458d10004bc7458d10114ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10034fc7258d10006ec7258d10034ec7258d100067f5258d10026df3258d1027cff7158d10006f77158d10026dc3158d10104ff7058d10006fb7058d10094ff76d0d10004fe76d0d10004fd76d0d10094fc76d0d100067f65d0d1022e7c65d0d10096be64d0d10006bd64d0d10006df63d0d10016dc63d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1021e7c6550d10006be6450d10006bd6450d10005f77150d10005f47150d10034fe76d891002d7c75d89100067f65d89100067c65d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d89100067c75d891001c7c75d8910094fe74d8910004fd74d8910014fe73d8910004fd73d8910014fc73d89100067f52d8910006ef32d8910006ec32d891003cfe71d891003cfc71d891003cff70d891000cfe70d89100dcfd70d891000cfc70d89100deef20d89100deed20d891002d7e75989100057d75989100067f65989100067c6598910006ef62989100c5f571989100057f755891002d7c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910025dc73589100edf77158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910094fc7458910006bc7458910004bc7458910004ff7358910006df735
  | 3 => 0xd76c871004d7e75c87100057d75c871000df5768871003ef5768871000cf5768871003df775887102adf57588710036f6628871003fe6628871003fe5628871003ef462887102a777528871000775528871000df6708871003ff2708871003ff1708871000df470887100ecff7648710005bf7448710005bc7448710005df7348710045dc73487100edf77648710006f7764871029df7754871029df57548710007b77448710007b47448710007d77348710007d4734871003fe77248710036f66248710036f46248710297775248710007755248710007e63248710007e5324871000df6704871000df4704871028d7e76d951002e7e76d951001c7e76d95100067e63d95100067c63d95100057d72d95102877771d95102877471d95102877a30d95102877a20d95102877610d95102877410d95102877810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f32d95100067c32d95102867f71d951002e7e71d95102867d71d95102867c71d95100067f31d95100067c31d95102867f70d95102867e70d95102867d70d95102867c70d95102867f40d95102867e40d95102867d40d95102867c40d95102867f30d95102867e30d95102867d30d95102867c30d95102867f20d95102867e20d95102867d20d95102867c20d95102867f10d95102867e10d95102867d10d95102867c10d95100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d9110034fe72d9110004fd72d91100067f52d911003cff70d9110164fd70d9110166bf40d9110166bd40d911002d7e75991100057d75991100067f65991100067c6599110006bf649911014df57199110094ff759911001cfe75991100967e759911001c7e7599110004fd75991100967d75991100047d7599110094fc7599110094fe7499110014fe7399110004fd7399110014fc7399110034fe7299110004fd72991100067f529911014cfd7199110096f57199110174fd7099110096f970991100057f755911002d7c75591100067f65591100067c6559110005df7359110025dc7359110005ef7259110005ec7259110175f77159110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef7259110034fc7259110006ec7259110034ec72591100067f5259110
  | 4 => 0x8f10034fe72d8f10004fd72d8f100067f52d8f1003cfe71d8f1003ef671d8f1003ef970d8f1003efa10d8f10014ff7658f1003edc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10094fc7458f1003edf7358f10004ff7258f10034fc7258f100067f5258f10046df3258f10014ff7158f1000cfe7158f10014fd7158f1000cfc7158f1003ede3158f1003edc3158f10106df3058f10106dd3058f10106fa1058f10094ff76d0f1003cfe76d0f10004fd76d0f1003cfc76d0f10096be64d0f10006bd64d0f10004ff7650f1003cfe7650f10004fd7650f1003cfc7650f10006be6450f10006bd6450f10005f77150f1003df47150f1003cff75d8b1001cfe75d8b10004fd75d8b1003cfc75d8b10094fe74d8b10004fd74d8b10014fe73d8b10004fd73d8b1003cfc73d8b100067f52d8b1003cfe71d8b1003ef671d8b1003ef970d8b1003efa10d8b100c4fd7698b1004d7e7598b100057d7598b1003eef6298b1003eec6298b10034ff7658b1003eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10094fc7458b10004ff7358b10014fe7358b10014fc7358b1003eef7258b100067f5258b10034ff7158b1000cfe7158b10034fd7158b1000cfc7158b1003eee2158b1003eec2158b100c6ef2058b100c6ed2058b100c6fa1058b100067f7654b100067e7654b100067d7654b100067c7654b100067f6454b100067e6454b100067d6454b100067c6454b100067f6354b1020e7e6354b100067d6354b1020e7c6354b102757f7254b1004f6f7254b100067f6254b100367e6254b100067d6254b100367c6254b10007767154b10007757154b102067e6154b100077b7054b10207787054b102067d6054b102076f2054b102076d2054b10207761054b102077a1054b10207741054b10094ff76d0b1003cfe76d0b10004fd76d0b1003cfc76d0b10096be64d0b10006bd64d0b10034ff7690b1003cfe7690b10004fd7690b1003cfc7690b1004d7e7590b100057d7590b10045de7390b10005dd7390b1003df67190b10005f57190b10004ff7650b1003cfe7650b10004fd7650b1003cfc7650b10006be6450b10006bd6450b10034ff7610b1003cfe7610b10004fd7610b1003cfc7610b1004d7e7510b100057d7510b1003df67110b10005f57110b10034ff768cb1003cfe768cb10004fd768cb1003cfc768cb1004d7e758cb100057d758cb10005be748cb10005bd748cb10036ee628cb10006ed628cb1003df6718cb10005f5718cb10004ff764cb1003cfe764cb10004fd764cb1003cfc764cb10016de634cb10006dd634cb10036ee624cb10006ed624cb1014cfd76d0710174ff7650710005df7350710045dc735071027cff764c710005bf744c710005bc744c7100c4f
  | 5 => 0x34fd70d85200eef710d85200076d5298520006f761985200057f755852005d7c7558520005bf7458520005bc7458520005df7358520055dc73585200076d52585200076d5218520006f5611852003cff751852001cfe7518520004fd751852003cfc7518520094fe7418520004fd7418520014fe7318520004fd731852003cfc73185200067f52185200067d521852003cff701852000cfe7018520034fd701852003ef9701852000cfc701852003ef7101852003efa10185200a6f51018520004fe76d0520004fd76d0520094fc76d05200076d52d0520004fe7690520004fd769052003cfc7690520006bf6490520006bc64905200076d529052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520005df7350520055dc73505200076d5250520004fe7610520004fd761052003cfc7610520006bf6410520096bc6410520035ee7210520005ed72105200076d521052000dfa7010520005f97010520004fe768c520004fd768c52003cfc768c520006df638c520016dc638c5200076d528c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005bf744c520005bc744c5200076d524c52000cfe76885200076d5288520006f7618852003ef4618852000dfa7088520005f9708852000cfc7648520005bf7448520005bc7448520005df7348520055dc73485200076d5248520006f76148520006f46148520005fb704852000df8704852003cff75d931001cfe75d931003e7e75d931001c7e75d9310004fd75d931003e7d75d93100047d75d931003cfc75d9310014fe73d9310004fd73d931003cfc73d9310034fe72d9310004fd72d93100067f52d931003cfe71d931003ef671d931003ef970d931014cfd769931003ebf6499310094ff759931001cfe7599310004fd7599310094fc7599310006bf5499310096bc5499310014fe7399310004fd7399310014fc7399310034fe7299310004fd72993100067f529931000cfe719931000cfc719931003ebe419931003ebc4199310096bf4099310176bd409931003ebc6459310004ff755931001cfe7559310004fd755931001cfc755931003ebf7459310006bf5459310006bc5459310004ff7359310014fe7359310014fc7359310004ff7259310034fc72593100067f5259310094ff715931000cfe715931014cfd715931000cfc715931003ebe415931003ebc415931014ebf405931014ebd405931003cff751931001cfe7519310004fd751931003cfc7519310094fe741931003ebe7419310014fe7319310004fd731931003cfc7319310034fe7219310004fd72193100067f521931003cfe711931003ef6711931003ef9701931003cff75d8f1001cfe75d8f10004fd75d8f1003cfc75d8f10094fe74d8f10004fd74d8f10104fd73d
  | 6 => 0xd7019120096bf40191201a6bd4019120014fe76d8d20056de63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20094fe74d8d20004fd74d8d20034fe72d8d2000cfd72d8d20034fc72d8d200067f52d8d20056df32d8d2003cfe71d8d20004fd71d8d20056dc31d8d20034ff70d8d20034fd70d8d20196df30d8d20196dd30d8d20196fa10d8d20056dc6358d202bdef7258d20004ff7558d2001cfe7558d20004fd7558d2001cfc7558d20004ff7458d20094fc7458d20194ff7358d20006df7358d202bcff7258d20006ef7258d200067f5258d20004ff7158d2003cfc7158d20184ff7058d20006fb7058d20186fa1058d20094ff76d0d20004fe76d0d20004fd76d0d20094fc76d0d20006bf64d0d20096bc64d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d20006bc6450d2001e7f76549202067e76549202067d765492001e7c76549200067f64549200067e64549200067d64549200067c64549200067f635492020e7e63549200067d635492020e7c63549200357f725492005f6f72549200367f62549200376e42549200376c42549202b76f32549200376e32549200376c32549200376f21549200376c21549200077b70549202077870549200367f60549200377b20549202076e20549200376c20549200377820549202077a105492005f6f765492001e6f76549202076c765492001e6c76549200076f74549200076e74549200076d74549200076c74549200076f64549200076e64549200076d64549200076c64549200076f73549202b76e73549200076d73549202b76c73549200076f63549202b76e63549200076d63549202b76c63549200076f43549202b76e43549200076d43549202b76c43549200076f71549200076e71549200076d71549200076c71549202b76f31549202b76c31549202076f70549200076b70549202076e70549202076d70549202076c70549202076870549200376f60549200366f60549200376b60549202076f40549202076e40549202076d40549202076c40549202076f30549202076e30549202076d30549202076c30549202076e10549202076a10549202076c105492000cfe76d092000cfc76d0920006bf64d0920096bc64d09200076d52d092000dfa70d0920005f970d0920094ff765092000cfe76509201c4fd765092000cfc7650920006bf6450920006bc64509200076d5250920005fb705092000df87050920014ff764c92000cfe764c920184fd764c92000cfc764c920006df634c920016dc634c9200076d524c920005fb704c92000df8704c9200076d52d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520094fe74d8520004fd74d8520014fe73d8520004fd73d8520014fc73d85200067f52d85200067d52d8520
  | 7 => 0x872001cfe7598720004fd759872003cfc7598720094fe7498720004fd7498720014fe7398720004fd739872003cfc739872000cfe729872000cfc72987200367f52987200367d529872003ef67198720036f7219872003ef4219872003ef710987200def51098720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720006bf7458720004bf7458720094fc7458720006bc7458720004bc7458720004ff7358720006df7358720004df7358720014fe7358720014fc7358720006dc7358720014dc735872000cfc72587200367f52587200367d5258720036f77158720036f72158720036f42158720036fa2058720036f920587200c6f71058720094ff76d0720034fe76d0720004fd76d07201467e65d07200067d65d0720096be64d0720006bd64d07200076d52d072003cff7690720034fe7690720004fd769072013e7e65907200067d65907202d6bf64907202d6bc64907200076d5290720004ff7650720004fd7650720034fc765072015e7e65507200067d6550720006be6450720006bd6450720005df7350720065dc73507200076d525072003cff7610720034fe7610720004fd76107201367e65107200067d65107202cebf6410720096bc6410720035ee7210720005ed72107200076d521072003cff768c720034fe768c720004fd768c72011e7e658c7200067d658c7202c6df638c720016dc638c7200076d528c720004ff764c720004fd764c720034fc764c72010e7e654c7200067d654c720005bf744c720005bc744c720016de634c720006dd634c7200076d524c720004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006bc54d9120014fe73d9120004fd73d9120014fc73d91200067f52d912003cfe71d9120004fd71d9120034ff70d9120034fd70d91201debf40d91201debd40d9120006bf64991201c5ed7299120094ff759912001cfe7599120004fd7599120094fc7599120094fe7499120014fe7399120004fd7399120014fc73991201c4fd7299120096ed72991200067f529912003cfe7199120004fd71991201f4fd7099120096f970991200057f755912005d7c75591201f5ef7259120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120014fe7359120014fc73591201f4ff7259120006ef72591200067f5259120004ff715912003cfc71591201c4ff7059120006fb70591201dcfe7619120006bd6419120094ff751912001cfe7519120004fd7519120094fc7519120096be7419120006bf5419120096bc5419120014fe7319120004fd7319120014fc7319120034fe7219120034fc72191200067f521912003cfe7119120004fd7119120034ff7019120034f
  | 8 => 0x367d72597200347d72597200367c72597200367f42597200367e42597200367d42597200367c42597200367f32597200367e32597200367d32597200367c32597200067f71597200067e71597200067d71597200067c71597200067f31597200067c31597200367f21597200367e21597200367d21597200367c21597202067f70597202067e70597202067d70597202067c70597202067f40597202067e40597202067d40597202067c40597202067f30597202067e30597202067d30597202067c30597200367f20597200367e20597200367d20597200367c20597202067f10597202067e10597202067d10597202067c1059720094ff759932001cfe7599320004fd7599320094fc7599320036be7499320014fe7399320004fd7399320014fc7399320006be4399320096bc439932000cfe729932000cfc72993200367f52993200367d5299320036be4299320036bc429932003cfe7199320004fd7199320096bf40993201f6bd4099320004ff755932001cfe7559320004fd755932001cfc7559320036bf7459320004ff7359320014fe7359320014fc7359320006be4359320006bc4359320034ff725932000cfe7259320034fd725932000cfc72593200367f52593200367d5259320036be4259320036bc4259320004ff715932003cfc71593201c6bf40593201c6bd4059320004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20094fc7458f20036df7358f20066dc4358f20034ff7258f2000cfe7258f20034fd7258f2000cfc7258f200367f5258f200367d5258f20036de3258f20036dc3258f20004ff7158f2003cfc7158f20066df3158f20186df3058f20186dd3058f20094ff76d0f20034fe76d0f20004fd76d0f20034fc76d0f2022e7e65d0f200067d65d0f202f6bf64d0f20096bc64d0f20016de63d0f20006dd63d0f20004ff7650f20034fe7650f20004fd7650f20034fc7650f2021e7e6550f200067d6550f202eebf6450f202eebc6450f200376f7654b200356f7654b202e66f7654b200076f7454b200076e7454b200076d7454b200076c7454b200376f6454b200376e6454b200376d6454b200376c6454b200076f7354b202df6e7354b200076d7354b202df6c7354b200376f6354b200376e6354b200376d6354b200376c6354b200076f4354b202df6e4354b200076d4354b202df6c4354b200076f7154b200076e7154b200076d7154b200076c7154b200376f6154b200376e6154b200376d6154b200376c6154b202df6f3154b202df6c3154b202076f7054b202076e7054b202076d7054b202076c7054b202066d6054b202076f4054b202076e4054b202076d4054b202076c4054b202076f3054b202076e3054b202076d3054b202076c3054b202076e1054b202076c1054b2003cff759
  | 9 => 0xf724c930007cf624c930036de624c930036dc624c930007cc624c930036cc624c93031f5f524c9300075d524c930005dc714c930007db704c93000dde704c93000ddc704c930187d8704c930016df604c930017db604c930187da104c930004ff75d853001cfe75d8530004fd75d853001cfc75d8530094fe74d8530004fd74d853000cfd73d853027edd73d8530034fe72d8530004fd72d85300067f52d85300067d52d8530316df32d8530006dd32d8530316f631d8530316f531d8530316dc31d8530014fd70d853027ef710d8530006f76198530025f970985300057f75585300757c7558530005bf7458530005bc7458530005ef7258530005ec7258530045fb7058530006f5611853003cff751853001cfe7518530004fd751853003cfc7518530094fe7418530004fd741853000cfd7318530034fe7218530004fd72185300067f52185300067d521853003ef6311853030ef5311853003cff7018530014fd701853003ef9701853003ef7101853003efa101853026ef51018530004fe76d0530004fd76d0530094fc76d0530015de73d0530005dd73d05300079d43d0530004fe7690530004fd769053003cfc7690530006bf6490530006bc6490530015dc739053016f9e439053000dfa7090530005f97090530004ff7650530004fe7650530004fc7650530005df7350530015dc73505300079d4350530004fe7610530004fd761053003cfc7610530006bf6410530096bc6410530015de7310530005dd731053012f9e431053000dfa7010530005f9701053000dde768c530116de768c53000cde768c530305df758c530305dd758c530005df748c530005dd748c530006de648c530006dc648c530005dd728c5302c6dc628c5302ff5f528c5300075d528c530015de718c530017d6718c530006df618c530007d7618c530007d4618c53000dde708c530117da708c530007d9708c53000ddc708c530016df608c530017db608c530117da108c530004fe76c8530004fd76c8530034fc76c85300757e75c85300057d75c8530015de73c8530005dd73c8530007cd32c8530004fe7688530004fd768853003cfc7688530005df7388530015dc7388530006ef6288530036ec628853000dfa7088530005f97088530004ff7648530004fe7648530004fc7648530005bf7448530005bc7448530005df7348530015dc7348530007cd3248530004fe7608530004fd760853003cfc76085300757e75085300057d7508530005be7408530005bd7408530015de7308530005dd7308530006ef6208530036ec620853000dfa7008530005f970085300067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067e43597200067c43597200367f72597200347f72597200367e7259720
  | 10 => 0x9130225df735913008dfb7059130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130006bf7459130224ff7359130006df7359130004ff7259130034fc72591300067f5259130004ff715913003cfc7159130214ff7059130006fb7059130354fe7619130006bd6419130094ff751913001cfe7519130004fd7519130094fc7519130094fe7419130096be7419130006bf5419130096bc541913000cff7319130014fe731913000cfd7319130096dd7319130014fc7319130096bf4319130096de431913034ebd4319130034fe7219130004fd72191300067f521913034edf321913003cfe7119130004fd711913034edc3119130014ff7019130014fd7019130096bf4019130346bd401913000ddc7650d30216dc7650d3000cdc7650d3033ddf7550d3033ddd7550d30015df7450d300179f7450d300079f6450d30096de6450d30096dc6450d300079c6450d30005df7250d303375f5250d30005dc7150d30007db7050d3000dde7050d3000ddc7050d30217d87050d30016df6050d30017db6050d302179f4050d302179d4050d30217da1050d30034fe76d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930094fe74d8930004fd74d893000cfd73d89300067f52d893032eee32d893032eed32d893003cfe71d8930004fd71d8930014fd70d89302beef20d89302befa10d89300757e75989300057d7598930005be7498930005bd7498930006ef6298930055f97098930065fb70589300757e75189300057d7518930036ee6218930006ed62189300067f76549300067e76549300067d76549300067c76549300067f64549300067e64549300067d64549300067c645493020f5e73549300075d73549302067f635493020f5e43549300075d43549302757f72549300776f72549300067f62549300367e62549300367c625493020f5f325493020f5c31549300077b70549302077870549302067f605493020f7b30549302075e30549302075c30549302077830549302077a1054930004fe76d0930004fd76d0930094fc76d0930006bf64d0930096bc64d0930015de73d0930005dd73d09301ff9e43d0930004fe7690930004fd7690930034fc76909300757e75909300057d7590930015de7390930005dd73909300079d4390930004ff7650930004fe7650930004fc7650930006bf6450930006bc6450930015de73509301cf9e4350930004fe7610930004fd7610930034fc76109300757e75109300057d7510930015de7310930005dd73109300079d431093000dfa7010930005f9701093000ddc764c930036dc764c93000cdc764c930325df754c930325dd754c930005df744c930005dd744c930006de644c930006dc644c930015df724c930017c
  | 11 => 0x385bd75905400073f659054037f3c6590540005bd739054016ebe639054016ebc6390540005bd72905402d6bc629054037f3f52905400073d5290540125be7190540006bf6190540007b76190540007b4619054000dbe7090540167ba709054000dba7090540007b9709054000dbc7090540166bf609054000cfc76505400067f655054015e7c6550540005df735054007ddc7350540006f76150540006f46150540005fb705054000df8705054014fb84050540174fe76105400067f65105401367c6510540175be7610540006be7610540375bf7510540375bd75105400073f651054036f3c6510540005bd731054012ebe631054012ebc6310540005bd72105402cebc621054036f3f52105400073d5210540165be7110540007b67110540006bf611054000dbe701054000dbc7010540096bf6010540004fe768c540004fd768c54003cfc768c5400067f658c54011e7c658c540005bf748c540005bc748c540006df638c540016dc638c5400079f438c540004ff764c540004fe764c540004fc764c5400067f654c54010e7c654c540005bf744c540005bc744c540004fe76c8540004fd76c8540034fc76c85400857e75c85400057d75c85400067f65c85400fe7c65c8540005be74c8540005bd74c8540004fe7688540004fd768854003cfc76885400067f65885400be7c6588540005bf7488540005bc7488540006ef6288540036ec6288540004ff7648540004fe7648540004fc76485400067f65485400d67c6548540005bf7448540005bc7448540005df734854007ddc7348540004fe7608540004fd760854003cfc76085400857e75085400057d75085400067f65085400b67c6508540005be7408540005bd740854007dde7308540005dd7308540006ef6208540036ec620854000dfa7008540005f9700854000dfa76d014000efa76d01400077b65d01403677865d014000dfa74d014000fba74d014000efb64d014000fbb64d0140097ba54d0140367b954d0140097bb43d0140007b943d01403677b52d01400077952d0140097bb42d0140007b942d0140007ba41d0140097b841d0140004ff75d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130006bc54d913000cff73d913000cfd73d913035ebf43d913035ebd43d9130034fe72d9130004fd72d91300067f52d913003cfe71d9130004fd71d9130014ff70d9130014fd70d9130356bf40d9130356bd40d9130214fd7699130006bf6499130215dd739913007df97099130094ff759913001cfe7599130004fd7599130094fc7599130094fe7499130214fd7399130096dd7399130096de4399130034fe7299130004fd72991300067f529913008edf329913003cfe7199130004fd719913008edc3199130224fd7099130096f970991300057f75591300757c755
  | 12 => 0xe74549400073d74549402067f64549400067f635494020e7e635494020e7c63549400073f43549400073d43549402757f72549400876f72549400067f62549400367e62549400367c62549402067f60549402073e40549402073c40549402077840549401a4fe76d09400067f65d09401be7c65d09401a5be76d0940006be76d09403a5bf75d09403a5bd75d09400073f65d094039f3c65d0940005bd73d09401febe63d09401febc63d0940036be62d0940036bc62d094039f3f52d09400073d52d0940005be71d094000dbe70d094000dbc70d0940096bf60d094000cfe76909400857e75909400057d75909400067f65909401ee7c65909401c5bd749094007dde7390940005dd7390940006ef6290940036ec629094000dfa7090940005f9709094000cfc76509400067f65509401d67c6550940006ef6250940036ec6250940005fb705094000df8705094000dbc7650940036bc765094000cbc7650940395bf7550940395bd75509400073f655094038f3c6550940005bf73509401cebe63509401cebc6350940007af7250940007af6250940036be6250940036bc6250940007ac625094038f3f52509400073d5250940005bc7150940007bb705094000dbe705094000dbc70509401c7b870509401c6bf60509401f4fe76109400857e75109400057d75109400067f65109401b67c65109401f5be7410940004fe768c940004fd768c940034fc768c9400857e758c9400057d758c9400067f658c94019e7c658c940005be748c940005bd748c940006ef628c940036ec628c940004ff764c940004fe764c940004fc764c9400067f654c94018e7c654c940005be744c940005bd744c940006df634c940016dc634c9400079f434c940006ef624c940036ec624c9400067f65d85400067c65d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540176bd74d8540014fe73d8540004fd73d8540014fc73d8540006bf43d8540006bd43d8540034fe72d8540004fd72d85400067f52d85400067d52d8540006bf42d8540006bd42d8540176f710d85400857e75985400057d75985400067f65985400067c6598540006f761985400057f75585400857c75585400067f65585400067c6558540005df735854007ddc7358540005ef7258540005ec72585400067f65185400067c6518540006f5611854003cff751854001cfe7518540004fd751854003cfc7518540014fe7318540004fd731854003cfc7318540034fe7218540004fd72185400067f52185400067d521854003ef71018540126f51018540124fe76d05400067f65d05401467c65d0540097b840d054000cfe76905400067f659054013e7c6590540006f7619054003ef4619054000dfa7090540005f9709054000dbe7690540166be769054000cbe7690540385bf7590540
  | 13 => 0x95400067e63d95400067c63d95400057d72d95403cf3e40d95403cf3c40d95403cf7840d95403ce7f74d95400867e74d95403ce7d74d95403ce7c74d95400067f73d95400067e73d95400067d73d95400067c73d95400067e43d95400067c43d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95400067f32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067c31d95403ce7f70d95403ce7e70d95403ce7d70d95403ce7c70d95403ce7f40d95403ce7e40d95403ce7d40d95403ce7c40d95403ce7f30d95403ce7e30d95403ce7d30d95403ce7c30d95403ce7f20d95403ce7e20d95403ce7d20d95403ce7c20d95403ce7f10d95403ce7e10d95403ce7d10d95403ce7c10d9540014fe76d8d400067f65d8d400067c65d8d4007ede63d8d40004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d4000cfd74d8d40014fc74d8d4007ede43d8d40034fe72d8d40004fd72d8d400067f52d8d4007edf32d8d4003cfe71d8d40004fd71d8d4007edc31d8d40226df30d8d400057f7558d400857c7558d400067f6558d400067c6558d4007edc6358d40344fe76d0d400067f65d0d4022e7c65d0d40097b840d0d40345be76d0d4035ebe76d0d403c5bf75d0d403c5bd75d0d400073f65d0d403bf3c65d0d40215bd73d0d40016be63d0d40016bc63d0d40005bd72d0d402f6bc62d0d403bf3f52d0d4007f9f32d0d40005be71d0d4007f9c31d0d4000dbe70d0d4000dbc70d0d40096bf60d0d4000cfc7650d400067f6550d4021e7c6550d40006df6350d40016dc6350d4007f9c4350d40005fb7050d4000df87050d40217b84050d4000dbc7650d40016bc7650d4000cbc7650d403b5bf7550d403b5bd7550d400073f6550d403af3c6550d40225bf7350d400079f7350d400079f6350d40016be6350d40016bc6350d4007f9c6350d40005bf7250d402eebc6250d403af3f5250d40005bc7150d40007bb7050d4000dbe7050d4000dbc7050d40217b87050d40216bf6050d402179f3050d40034fe76d89400857c75d89400067f65d89400067c65d8940004ff75d89400067f75d894001cfe75d8940004fd75d894001cfc75d89400067c75d894001c7c75d8940014fe73d8940004fd73d8940014fc73d89400067f52d894003cfe71d8940004fd71d89401f6ef20d89400857e75989400057d75989400067f65989400067c659894007dde7398940005dd7398940006ef62989400057f75589400857c75589400067f65589400067c65589400857e75189400057d75189400067f65189400067c6518940036ee6218940006ed62189400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400073
  | 14 => 0x40f3f52d0b400073d52d0b40005be71d0b4000dbe70d0b40097ba70d0b40097b970d0b4000dbc70d0b401c4fd7690b4009d7e7590b400057d7590b4008dde7390b40005dd7390b401dcff7650b401ddbf7650b40006bf7650b40405bf7550b40405bd7550b40005bf7350b401cebe6350b401cebc6350b40097af7250b40036be6250b40036bc6250b403ff3f5250b400073d5250b40005bc7150b4000dbe7050b4000dbc7050b40034ff768cb40094fe768cb40004fd768cb4009d7e758cb400057d758cb40095be748cb40005bd748cb40004ff764cb40004fd764cb40094fc764cb40095be744cb40005bd744cb40016dc634cb400079f434cb40096f7619874003cff759874001cfe7598740004fd759874003cfc759874000cfe7498740014fe7398740004fd739874003cfc7398740034fe7298740004fd72987400067f52987400067d5298740096f7419874003ef4419874003ef71098740166f51098740005df735874008ddc7358740096f46158740004ff755874001cfe7558740004fd755874001cfc755874000cfc745874014ebc7458740004ff7358740006df7358740004df7358740014fe7358740014fc7358740006dc7358740014dc7358740006bf4358740006bd4358740004ff7258740034fc72587400067f52587400067d5258740006bf4258740006bd4258740096f74158740096f4415874014ef7105874014cfd769074014dbd7690740006bd76907403f5bf75907403f5bd7590740005bd739074016ebe639074016ebc6390740005bd72907402d6be62907403ef3f52907400073d5290740006bd619074000dbe709074000dbc7090740164ff7650740005df735074008ddc735074000dbd7610740096bd761074000cbd7610740095bf75107403e5bd7510740005bd731074012ebe6310740096bc6310740005bd72107402cebe62107403df3f52107400073d5210740097b67110740097b66110740006bd6110740097b5611074000dbe7010740097ba7010740097b9701074000dbc701074003cff768c740094fe768c740004fd768c740005bf748c740095bc748c740016dc638c7400079f438c740004ff764c740004fd764c740094fc764c740005bf744c740095bc744c740034ff76c8740094fe76c8740004fd76c874009d7e75c87400057d75c8740095be74c8740005bd74c874003cff7688740094fe7688740004fd7688740005bf7488740095bc7488740004ff7648740004fd7648740094fc7648740005bf7448740095bc7448740005df734874008ddc734874003cff7608740094fe7608740004fd760874009d7e75087400057d7508740095be7408740005bd740874008dde7308740005dd730874000dfa7008740005f970087403d57e76d95400867e76d954001c7e76d95403cf3f74d95403cf3c74d
  | 15 => 0xa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f84358021036fb7258021036fa7258021036f87258021036fb52580210367b5258021036fa5258021036f95258021036795258021036f85258021036fb4258021036fa4258021036f94258021036f84258021036fb3258021036fa3258021036f93258021036f832580210a6fb715802103efa7158021006fb515802103efa5158021006f9515802103ef85158021006fb415802103efa4158021006f9415802103ef84158021006fb315802103efa3158021006f9315802103ef83158021036fb215802103efa2158021036f22158021036f92158021036f1215802103ef82158021014ff7658f40096dc6358f40004ff7558f4001cfe7558f40004fd7558f4001cfc7558f40014fd7458f4000cfc7458f40096df4358f40096dc4358f40004ff7258f40034fc7258f400067f5258f40004ff7158f4003cfc7158f40216df3058f4000dbd76d0f40016bd76d0f4000cbd76d0f40095bf75d0f40435bd75d0f40016be63d0f400979e63d0f400979d63d0f40016bc63d0f40005bd72d0f402f6be62d0f4042f3f52d0f4008f9f32d0f40005be71d0f4008f9c31d0f4000dbe70d0f40097ba70d0f40097b970d0f4000dbc70d0f40354ff7650f40016dc6350f400979c4350f40355bf7650f4034ebf7650f40425bf7550f40425bd7550f400979f7350f400979f6350f40016be6350f40016bc6350f400979c6350f40005bf7250f402eebe6250f4041f3f5250f40005bc7150f4000dbe7050f4000dbc7050f402179f3050f4009d7e7598b400057d7598b4008dde7398b40005dd7398b40096ef6298b40036ec6298b40034ff7658b40096ec6258b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4000cfc7458b40004ff7358b40014fe7358b40014fc7358b400067f5258b40096ef4258b40096ec4258b40004ff7158b4003cfc7158b401c6ef2058b400067f7654b400067e7654b400067d7654b400067c7654b400073e7454b400073d7454b402067e6454b4020e7e6354b400067d6354b4020e7c6354b400073f4354b400073d4354b402757f7254b4009f6f7254b400367e6254b400067d6254b400367c6254b400077b7054b40207787054b402067d6054b402073e4054b402077a4054b402073c4054b4000dbd76d0b40036bd76d0b4000cbd76d0b40095bf75d0b40415bd75d0b40005bd73d0b401febe63d0b40096bc63d0b40036be62d0b40097ae62d0b40097ad62d0b40036bc62d0b40
  | 16 => 0x8c21004ff7058c2100cfe7058c2100cfc7058c210aedf3058c21006de3058c210aedc3058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c21036df7258c21036de7258c21036dd7258c21036dc7258c21036df5258c210365f5258c21036de5258c21036dd5258c210365d5258c21036dc5258c21036df4258c21036de4258c21036dd4258c21036dc4258c210aedf7158c2103ede7158c2103edc7158c21006df5158c2103ede5158c21006dd5158c2103edc5158c2103ede4158c2103edc4158c21036df2158c21036cf2158c2103ede2158c21036dd2158c2103edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006de4058c21006dc4058c21036df2058c21036de2058c21036dd2058c21036dc2058c2103edf1058c21006de1058c2103edc1058c21094ff76d0c2103cfe76d0c21004fd76d0c2103cfc76d0c2122e7e65d0c210067d65d0c21096be64d0c21006bd64d0c21016de63d0c21006dd63d0c21226fa60d0c21004ff7650c2103cfe7650c21004fd7650c2103cfc7650c2121e7e6550c210067d6550c21006be6450c21006bd6450c21016de6350c21006dd6350c21005f77150c2103df47150c21216fa6050c21004fd76d04211467e65d04210067d65d0421096be64d0421006bd64d042117ede63d0421006dd63d0421176fa60d0421004ff765042115e7e65504210067d6550421006be6450421006bd6450421005df73504210addc7350421156de6350421006dd635042114efa60504210e4ff764c42110e7e654c4210067d654c421005bf744c421005bc744c421006be644c421006bd644c421016de634c421006dd634c421106fa604c42103def7648421006ef7648421004ef764842103f6e654842103f6d6548421007af7448421007ac744842103fae644842103fad6448421007cf7348421007cc734842103eef634842103fce6348421006ed634842103fcd6348421006cd634842103def7148421037e7714842103eee614842103fe6614842103fe6514842143fe5514842103fe64148421007e5414842103fea604842103fe96048421004ff755802101cfe7558021004fd755802101cfc7558021004ff7458021094fc7458021004ff7358021014fe7358021014fc735802100cfd72580210367f52580210367d5258021036f62158021036f5215802103efb7058021006fb50580210a6fa5058021006f950580210a6f850580210a6fa40580210a6f84058021006fb30580210a6fa30580210a6f83058021036fb2058021036f8205802103efb105802103ef81058021006fb7558021006f
  | 17 => 0x6be4099021096bc4099021096bf7599021006be7599021006bd7599021096bc7599021096bf7399021006be7399021006bd7399021096bc7399021006bf5399021006be5399021006bd5399021006bc5399021036bf7299021036be7299021036bd7299021036bc7299021036bf52990210363f5299021036be5299021036bd52990210363d5299021036bc5299021036bf3299021036be3299021036bd3299021036bc329902103ebe719902103ebc7199021006bf519902103ebe5199021006bd519902103ebc5199021006bf319902103ebe319902103ebc3199021036bf219902103ebe2199021036bd219902103ebc2199021096bf7099021006be7099021006bd7099021096bc7099021006bf5099021006be5099021006bd5099021006bc5099021006bf3099021006be3099021006bc3099021036bf2099021036be2099021036bd2099021036bc209902103ebf1099021006be109902103ebc1099021004ff755902101cfe7559021004fd755902101cfc755902103cff745902103ebf7459021006bf5459021006be5459021006bd5459021006bc5459021004ff7359021014fe7359021014fc7359021006be4359021006bc4359021034fe7259021034fc72590210367f52590210367d5259021036be4259021036bc425902103cfe715902103cfc715902103ebe415902103ebc4159021004ff705902100cfe705902100cfc7059021006be4059021006bc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc5359021036bf7259021036be7259021036bd7259021036bc7259021036bf52590210363f5259021036be5259021036bd52590210363d5259021036bc5259021036bf3259021036be3259021036bd3259021036bc325902103ebe715902103ebc7159021006bf515902103ebe5159021006bd515902103ebc5159021006bf315902103ebe315902103ebc3159021036bf215902103ebe2159021036bd215902103ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021006bf3059021006be3059021006bc3059021036bf2059021036be2059021036bd2059021036bc205902103ebf1059021006be105902103ebc1059021004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21094fc7458c2103cff7358c2103edf7358c21006df5358c210aede5358c21006dd5358c210aedc5358c210aede4358c210aedc4358c21034fe7258c21034fc7258c210367f5258c210367d5258c21036de3258c21036dc3258c2103cfe7158c2103cfc7158c2103ede3158c2103edc3158c21036ef215
  | 18 => 0xe72d0521005ed72d0521004fe7690521006bf6490521006bc6490521006df639052116edc6390521094ff7650521004fd7650521034fc7650521006bf6450521006bc6450521005df73505210cddc7350521006df6350521156dc6350521005ef7250521035ec7250521004fe7610521006bf6410521096bc6410521006df631052112edc63105210f4fe768c521006bf648c521006bc648c521006df638c521016dc638c521007ce328c521014ff764c5210ccfd764c521034fc764c521005bf744c521005bc744c521006bf644c521006bc644c521006df634c521016dc634c521005ef724c521035ec724c521007cd324c521006bf6488521006bc6488521006df63885210e6dc63885214476f52885210076d5288521035f67188521036f76188521007af6488521007ac648852103def7388521005ed7388521007cf6388521007cc638852103dee718852103eef6188521037e7618852100cfe76d8121006bf64d8121006bc64d8121006df63d8121006dc63d81210c6fa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121094fe74d8121004fd74d8121014fe73d8121004fd73d8121014fc73d812100cfc72d81210067f52d81210067d52d8121034fd71d8121006fb50d81210c6f850d81210c6fa20d81210c6fa10d81210057f75581210d57c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df73581210cddc7358121006df6358121006dc63581210c6f860581210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067e43594210067c43594210367f72594210367e72594210367d72594210367c72594210367f42594210367e42594210367d42594210367c42594210367f32594210367e32594210367d32594210367c32594210b67f715942103e7e71594210b67d715942103e7c715942103e7e415942103e7c41594210067f315942103e7e315942103e7c31594210367f215942103e7e21594210367d215942103e7c21594210067f70594210067e70594210067d70594210067c70594210067e40594210067c40594210067f30594210067e30594210067c30594210367f20594210367e20594210367d20594210367c205942103e7f10594210067e105942103e7c1059421094ff759902101cfe7599021004fd7599021094fc759902103cfe749902103ebe7499021006bf5499021096be5499021006bd5499021096bc5499021014fe7399021004fd7399021014fc7399021006be4399021096bc4399021034fe7299021034fc72990210367f52990210367d5299021036be4299021036bc429902103cfe719902103cfc719902103ebe419902103ebc419902100cfe7099021004fd709902100cfc7099021
  | 19 => 0x8d21006dc10d8d21005bf7458d21005bc7458d21006bf6458d21006bc6458d210cedc6358d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d21094fc7458d21006bc7458d21004bc7458d210ccff7358d21006df7358d210e4ff7258d21006ef7258d210067f5258d210f4ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21005de7618d210cede7618d21004de7618d210cf5e7518d210cf5d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d210cfcd7218d210075f5218d21456df6118d21457d72118d21457d42118d21006de6018d21006dc6018d21094ff76d0d21004fe76d0d21004fd76d0d21094fc76d0d21006bf64d0d21096bc64d0d21006df63d0d21016dc63d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21006bc6450d21006df6350d21016dc6350d2101e7f76549210be7e76549210d67d765492101e7c76549210067f64549210073f64549210063f64549210067e64549210067d64549210067c64549210073c64549210063c64549210067f63549210075f63549210065f635492120e7e63549210067d635492120e7c63549210075c635492120e5c63549210357f72549210d76f72549210367f62549210376e42549210376e32549210077771549210077471549210367f61549210377721549210376c21549210377421549210376421549212067e60549212067c60549210376f2054921004fe76d0921006bf64d0921096bc64d0921006df63d09211fedc63d0921005f671d0921005f571d0921004fc7650921006bf6450921006bc6450921006df63509211cedc63509210076d5250921005f77150921005f47150921037e42150921005ee768c921036ee768c9210376e758c9210376d758c921037ae748c921037ad748c921007af648c921007ac648c9210cded738c921007cf638c921016ee638c921016ec638c9210cfcc638c921016cc638c92103dee718c921036ef618c921037e7618c9210cfcc318c921014fc764c921006bf644c921006bc644c921006df634c921016dc634c92144f6f524c9210076d524c921037cc324c921005f7714c921005f4714c9210cdec764c921016ec764c921014ec764c921007af644c921007ac644c921035ef734c921037cf734c921007cf634c921016ee634c921016ec634c9210cfcc634c921007cf434c9210cfcc434c921007e7714c92103dec714c921007e4714c921036ef614c921037e7614c9210cfcf314c9210cfcf304c921034fe76d0521006bf64d0521096bc64d0521006df63d052117edc63d0521035e
  | 20 => 0x6bd5419121096bc5419121014fe7319121004fd7319121014fc7319121006be4319121096bc43191210067f521912100cfe7019121004fd701912100cfc7019121006be4019121096bc4019121005be7619121006be7619121004be7619121006bf6519121006be6519121006bd6519121006bc6519121006be6319121006bc63191210073f52191212cfb721191212cfb42119121006be6019121006bc6019121096bf7519121006be7519121006bd7519121096bc7519121096bf7319121006be7319121006bd7319121096bc7319121006bf5319121006be5319121006bd5319121006bc5319121096bf72191212cebe7219121006bd7219121096bc7219121006bf52191210063f52191212cebe5219121006bd52191212cebc5219121006bf32191212cebe32191212cebc3219121096bf7119121006bd7119121006bf5119121006be5119121006bd5119121006bc5119121006bf3119121006bc31191212cebf2119121006bd21191212cebc2119121096bf7019121006be7019121006bd7019121096bc7019121006bf5019121006be5019121006bd5019121006bc5019121006bf3019121006be3019121006bc30191212cebf2019121006be20191212cebc2019121006be1019121006bc1019121014fe76d8d21006bf64d8d21006bc64d8d210cede63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21094fe74d8d21004fd74d8d21006df53d8d210cede53d8d21006dd53d8d210cedc53d8d210cede43d8d210cedc43d8d210ccfd72d8d210067f52d8d210cedf32d8d21034fd71d8d210cedf31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210cedf30d8d21006de30d8d210cedc30d8d210cdde76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d210069c64d8d21007cf72d8d210075f52d8d212c7d721d8d212c7d421d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d212c6de72d8d21006dd72d8d212c6dc72d8d21006df52d8d210065f52d8d212c6de52d8d21006dd52d8d212c6dc52d8d212c6de42d8d212c6dc42d8d212c6df71d8d210cede71d8d21006dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d212c6df21d8d212c6dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006de40d8d21006dc40d8d212c6df20d8d21006de20d8d212c6dc20d8d21006de10d
  | 21 => 0xc744c62103edf634c62103edc634c62103ded76c8621036ed76c86210376e75c86210376d75c862103eef63c8621006ed63c862103fe661c862103fe651c862145fe551c862100cff76582210057f75582210bd7c755822103ef86058221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221094fc7458221004ff7358221014fe7358221014fc73582210067f52582210067d525822103cfc71582210defa30582210defa205822103efb105822103ef81058221004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006be54d9121006bd54d9121006bc54d9121014fe73d9121004fd73d9121014fc73d9121006be43d9121006bc43d91210067f52d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006be63d9121006bc63d91210073f52d91212d7b721d91212d7b421d9121006be60d9121006bc60d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121006bf72d91212d6be72d9121006bd72d91212d6bc72d9121006bf52d91210063f52d91212d6be52d9121006bd52d91212d6bc52d9121006bf32d91212d6be32d91212d6bc32d91212d6bf71d9121006bd71d9121006bf51d9121006be51d9121006bd51d9121006bc51d9121006bf31d9121006bc31d91212d6bf21d91212d6bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006bf30d9121006be30d9121006bc30d91212d6bf20d9121006be20d91212d6bc20d9121006be10d9121006bc10d9121006bf64991210cdde7399121005dd7399121094ff759912101cfe7599121004fd7599121094fc7599121094fe7499121004be7499121014fe7399121096de7399121014de7399121004fd7399121096dd7399121004dd7399121014fc7399121004fd7299121096ed72991210067f5299121004fd7199121096f5719912100cfe7099121004fd709912100cfc7099121005df73591210cddc7359121004ff755912101cfe7559121004fd755912101cfc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc7359121004ff7259121006ef72591210067f5259121004ff7159121006f77159121004ff705912100cfe705912100cfc7059121004fe7619121006bd6419121094ff751912101cfe7519121004fd7519121094fc7519121096be7419121006bf5419121096be5419121
  | 22 => 0x9221006bc43d922103eed72d92210067f52d92212d6be42d92212d6bc42d922103ef671d922100cfe70d9221004fd70d922100cfc70d9221004fd769922103ebf6499221094ff759922101cfe7599221004fd7599221094fc7599221014fe7399221004fd7399221014fc73992210067f529922103cfe719922103ebe419922103ebc419922100cfe7099221004fd709922100cfc709922103ebc6459221005df73592210e5dc7359221004ff755922101cfe7559221004fd755922101cfc755922103ebf7459221004ff7359221006df7359221004df7359221014fe7359221014fc7359221006dc7359221014dc73592210067f525922103cfc715922103ebe415922103ebc4159221004ff705922100cfe705922100cfc705922103cff751922101cfe7519221004fd751922103cfc7519221094fe741922103ebe7419221014fe7319221004fd731922103cfc7319221006be4319221096bc431922103eed72192210067f52192212cebe4219221096bc421922103ef6711922100cfe7019221004fd701922100cfc701922103cff75d8e2101cfe75d8e21004fd75d8e2103cfc75d8e21094fe74d8e21004fd74d8e210e4fd73d8e210e6dc43d8e2103eed72d8e210067f52d8e212c6de32d8e212c6dc32d8e2103ef671d8e2103edf31d8e2100cfe70d8e21004fd70d8e2100cfc70d8e210e6df30d8e21014ff7658e21005bf7458e21005bc7458e2103edc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21006bf7458e21004bf7458e21094fc7458e21006bc7458e21004bc7458e2103edf7358e210067f5258e210e6df3258e2103cfc7158e2103ede3158e2103edc3158e21004ff7058e2100cfe7058e2100cfc7058e21094ff76d0e2103cfe76d0e21004fd76d0e2103cfc76d0e21096be64d0e21006bd64d0e21006df63d0e21016dc63d0e21004ff7650e2103cfe7650e21004fd7650e2103cfc7650e21006be6450e21006bd6450e2101e7f7654a2101e7c7654a210067f6454a210067e6454a210067d6454a210067c6454a210067f6354a2120e7e6354a210067d6354a2120e7c6354a210357f7254a210bf6f7254a210367d6254a210376c4254a214676f3254a210376c3254a21007777154a21007747154a210367e6154a210376f2154a21037772154a21037672154a21037742154a212067e6054a212067c6054a210376f2054a21096be64d0a21006bd64d0a210076d52d0a2103df671d0a21005f571d0a21006be6450a21006bd6450a21005f77150a2103df47150a21014ff764ca2103cfc764ca21016de634ca21006dd634ca21005f7714ca2103df4714ca2103ebf64d062103ebc64d062103ebf645062103ebc6450621005df73506210e5dc73506210acff764c621005bf744c621005b
  | 23 => 0x367e21597210367d21597210367c21597210067f70597210067e70597210067d70597210067c70597210067e40597210067c40597210067f30597210067e30597210067c30597210367f20597210367e20597210367d20597210367c20597210067e10597210067c1059721094ff759932101cfe7599321004fd7599321094fc7599321036be7499321014fe7399321004fd7399321014fc7399321006be4399321096bc4399321034fe72993210367f52993210367d5299321036be4299321036bc429932100cfe7099321004fd709932100cfc7099321004ff755932101cfe7559321004fd755932101cfc7559321036bf7459321004ff7359321014fe7359321014fc7359321006be4359321006bc4359321034fc72593210367f52593210367d5259321036be4259321036bc4259321004ff705932100cfe705932100cfc7059321004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21094fc7458f21036df7358f210f6dc4358f21034fc7258f210367f5258f210367d5258f21036de3258f21036dc3258f210f6df3158f21004ff7058f2100cfe7058f2100cfc7058f210f6df3058f21094ff76d0f21034fe76d0f21004fd76d0f21034fc76d0f2122e7e65d0f210067d65d0f212f6bf64d0f21096bc64d0f21016de63d0f21006dd63d0f21004ff7650f21034fe7650f21004fd7650f21034fc7650f2121e7e6550f210067d6550f212eebf6450f212eebc6450f21005f77150f21005f47150f21035ef764cb210aeef764cb210376e654cb210376d654cb21037cf734cb21037cf634cb21016ee634cb21036ec634cb21037cc634cb21007cf434cb210f7cc434cb2103dec714cb210f7cf314cb210f7cf304cb211467e65d07210067d65d0721096be64d0721006bd64d0721035ee72d0721005ed72d072113e7e65907210067d65907212d6bf64907212d6bc649072115e7e65507210067d6550721006be6450721006bd6450721005df73507210f5dc7350721005ef7250721035ec72507211367e65107210067d65107212cebf6410721096bc64107210ccfd768c72111e7e658c7210067d658c7212c6df638c721016dc638c72103dec728c7212c7ce328c721014ff764c721034fc764c72110e7e654c7210067d654c721005bf744c721005bc744c721016de634c721006dd634c721005ef724c721035ec724c721007cd324c721004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321094fc7458321004ff7358321014fe7358321014fc73583210367f52583210367d5258321036f62158321036f52158321036fb7058321036fb2058321036f820583210eefa105832103cff75d922101cfe75d9221004fd75d922103cfc75d9221014fe73d9221004fd73d922103cfc73d9221006be43d
  | 24 => 0xf76549310067e76549310067d76549310067c76549310067f64549310073f64549310063f64549310067e64549310067d64549310067c64549310073c64549310063c645493120e7f635493147d7f725493110f6f72549310067f62549310076f62549310066f62549310367e62549310367c62549310076c62549310366c625493120f5f325493120e7f615493120f77315493120f5c315493120f7431549312067e60549312067c6054931004fe76d0931004fd76d0931094fc76d0931006bf64d0931096bc64d0931004fe7690931004fd7690931034fc769093110d7e75909310057d7590931006bf6490931006bc6490931015de7390931005dd7390931004ff7650931004fe7650931004fc7650931006bf6450931006bc6450931004fe7610931004fd7610931034fc761093110d7e75109310057d7510931006bf6410931096bc6410931015de7310931005dd7310931005f67110931005f57110931034dc764c9310079f644c931006de644c931006dc644c9310079c644c9310069c644c931015df724c931017cf724c931007cf624c931036de624c931036dc624c931007cc624c9314775f524c9310075d524c931007d7714c93103ddc714c931007d4714c931016df614c931017d7614c931014fe76d0531014fc76d0531006bf64d0531096bc64d0531015de73d0531005dd73d053112cfe769053116ebf6490531006bc6490531094ff7650531014fe7650531154fd7650531014fc7650531006bf6450531006bc6450531005df7350531015dc735053116cfe7610531006bf6410531096bc64105310079f648c531006de648c531006dc648c5310079c648c5310069c648c531005dd728c5312c6dc628c53146f5f528c5310075d528c53103dde718c53103fd6718c53103edf618c531017d7618c53100cfe76d8131006bf64d8131006bc64d8131106fa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131094fe74d8131004fd74d813100cfc73d8131034fe72d8131004fd72d81310067f52d81310067d52d8131046df32d8131006dd32d8131014fd71d8131006de31d8131046dc31d8131106fa30d8131106fa10d81310057f755813110d7c7558131005bf7458131005bc7458131006bf6458131006bc6458131005ef7258131005ec7258131106f860581310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067e43597210067c43597210367f72597210367e72597210367d72597210367c72597210367f42597210367e42597210367d42597210367c42597210367f32597210367e32597210367d32597210367c32597210fe7f71597210fe7e71597210067d71597210fe7c71597210067f31597210067c31597210367f2159721
  | 25 => 0x9131006be20d9131006bc20d9131006be10d9131006bc10d9131006bf6499131155f57199131094ff759913101cfe7599131004fd7599131094fc7599131094fe749913112cbe749913117cfd7399131096dd7399131034fe7299131004fd72991310067f529913117edf3299131154fd7199131096f5719913117edc319913100cfe7099131004fd709913100cfc709913117df77159131004ff755913101cfe7559131004fd755913101cfc7559131006bf7459131154ff7359131006df7359131004df7359131004ff7259131034fc72591310067f525913117cff7159131006f77159131004ff705913100cfe705913100cfc705913116cfe7619131006bd6419131094ff751913101cfe7519131004fd7519131094fc7519131096be7419131006bf5419131096be5419131006bd5419131096bc541913103cff731913112cfd7319131096bf431913112ebd4319131034fe7219131004fd72191310067f521913112edf321913112edc311913100cfe7019131004fd701913100cfc7019131006be4019131096bc401913116dbe7619131006be761913116cbe7619131006bf6519131006be6519131006bd6519131006bc65191310073f521913112f9f321913112fb7311913112f9c311913112fb43119131006be6019131006bc6019131096bf7519131006be7519131006bd7519131096bc7519131096bf731913112ebe731913112ebd7319131096bc731913112ebf531913112ebe531913112ebd531913112ebc5319131096bf7219131006be7219131006bd7219131096bc7219131006bf52191310063f5219131006be5219131006bd5219131006bc521913112ebf321913112e9f321913112ebe321913112ebd321913112ebc3219131096bf711913112ebd7119131006bf5119131006be5119131006bd5119131006bc511913112ebf311913112ebe311913112ebd311913112ebc311913112e9c3119131096bf7019131006be7019131006bd7019131096bc7019131006bf5019131006be5019131006bd5019131006bc501913112ebf301913112ebe301913112ebd301913112ebc3019131006be2019131006bc2019131006be1019131006bc1019131006bf64d8931006bc64d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931094fe74d8931004fd74d89310067f52d8931006ee52d8931006ed52d89310e6ee32d89310e6ed32d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d893110d7e75989310057d7598931005be7498931005bd7498931006bf6498931006bc6498931006ef62989310cdf57198931005bf7458931005bc7458931006bf6458931006bc64589310f5f7715893110d7e75189310057d7518931006bf6418931006bc6418931036ee6218931006ed62189310067
  | 26 => 0x2067e6054a312067c6054a3120f5f3054a31094ff76d0a3103cfe76d0a31004fd76d0a31096be64d0a31006bd64d0a31015de73d0a31005dd73d0a311ff9c43d0a31034ff7690a3103cfe7690a31004fd7690a3111d7e7590a310057d7590a31006bf6490a31006bc6490a31015de7390a31005dd7390a310079f4390a31004ff7650a31004fd7650a3103cfc7650a31006be6450a31006bd6450a31005df7350a31015dc7350a311cf9c4350a31034ff7610a3103cfe7610a31004fd7610a3111d7e7510a310057d7510a31006bf6410a31096bc6410a31015dc7310a310079f4310a3103df67110a31005f57110a312c75e758ca312c75d758ca31005de748ca312c79e748ca310059e748ca312c79d748ca312c5dc748ca31015de728ca31017ce728ca312c7ce628ca312c6dd628ca31007cd628ca312c75f528ca312c75d528ca312c7d6718ca31005dd718ca312c7d5718ca31016de618ca31017d6618ca31005dd708ca31154fd76d063103ebf64d063103ebc64d0631015dc73d06310079f43d063117cff765063103ebf645063103ebc6450631005df7350631015dc73506310079f435063100cff76582310057f755823111d7c755823103ef86058231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231094fc7458231004ff7258231034fc72582310067f52582310067d525823103cfc7158231116fa3058231116fa205823103efb105823103ef81058231004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d9131006be54d9131006bd54d9131006bc54d913103cff73d913116cfd73d913116ebf43d913116ebd43d9131034fe72d9131004fd72d91310067f52d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131006bf65d9131006be65d9131006bd65d9131006bc65d91310073f52d913116f9f32d913116fb731d913116f9c31d913116fb431d9131006be60d9131006bc60d9131006bf75d9131006be75d9131006bd75d9131006bc75d913116ebf73d913116ebe73d913116ebd73d913116ebc73d913116ebf53d913116ebe53d913116ebd53d913116ebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d91310063f52d9131006be52d9131006bd52d9131006bc52d913116ebf32d913116ebe32d913116ebd32d913116ebc32d913116ebf71d913116ebd71d9131006bf51d9131006be51d9131006bd51d9131006bc51d913116ebf31d913116ebe31d913116ebc31d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d913116ebf30d913116ebe30d913116ebd30d913116ebc30d
  | 27 => 0x7525044100775525044100cff76580410057f75580411357c755804103ef86058041004ff75580410067f75580410047f755804101cfe7558041004fd755804101cfc75580410067c755804101c7c7558041004ff7358041014fe7358041014fc7358041004ff7258041034fc72580410067f52580410067d5258041126fa5058041006f95058041096fb4058041096f84058041126fa3058041126fa205804103efb105804103ef8105804103cff75d923101cfe75d9231004fd75d923103cfc75d923103edd73d923116ebe43d923116ebc43d923116edc43d9231034fe72d9231004fd72d92310067f52d923103cfe71d923103ef671d923100cfe70d9231004fd70d923100cfc70d923116edf30d9231154fd769923103ebf6499231094ff759923101cfe7599231004fd7599231094fc7599231096bf439923117ebd4399231034fe7299231004fd72992310067f529923103cfe719923103cfc719923103ebe419923103ebc419923100cfe7099231004fd709923100cfc709923103ebc6459231004ff755923101cfe7559231004fd755923101cfc755923103ebf7459231006df7359231156bf4359231156bd4359231156dc4359231004ff7259231034fc72592310067f525923103cfe715923103cfc715923103ebe415923103ebc4159231004ff705923100cfe705923100cfc7059231156df305923103cff751923101cfe7519231004fd751923103cfc7519231094fe741923103ebe741923103edd731923112ebe4319231096bc4319231034fe7219231004fd72192310067f521923103cfe711923103ef6711923100cfe7019231004fd701923100cfc7019231006dd76d0e31015de74d0e310179e74d0e31006df64d0e310079e64d0e31006dd64d0e310079d64d0e312c5de72d0e314875f52d0e31007d671d0e31005dd71d0e31007d571d0e31016de61d0e31017d661d0e31005dd70d0e3111d7e7598a310057d7598a3103eef6298a3103eec6298a31005bf7458a31005bc7458a3103eec6258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31006bf7458a31004bf7458a31094fc7458a31006bc7458a31004bc7458a31006df4358a310cedc4358a310067f5258a310ceee3258a310ceed3258a312c6dc3258a3103cfc7158a310cedf3158a3103eee2158a3103eec2158a31004ff7058a3100cfe7058a3100cfc7058a310cedf3058a310067f7654a310067e7654a310067d7654a310067c7654a310067f6454a310067e6454a310067d6454a310067c6454a310075f7354a3120f5c7354a3120e7d6354a310075f4354a3120f5c4354a3147d7f7254a3111f6f7254a310367e6254a310067d6254a310367c6254a312c75c3254a3120e7e6154a3120f5f3154a3120f773154a3120f743154a31
  | 28 => 0x8c41004ff7058c4100cfe7058c4100cfc7058c4112edf3058c4117cff7650c4112dbf7450c4117ebe6450c410979c4350c411357e75988410057d759884103eef629884103eec629884103eec6258841004ff755884101cfe7558841004fd755884101cfc7558841004ff7358841014fe7358841014fc7358841006be4358841006bc43588410067f5258841006ee5258841006ed5258841096ef4258841096ec425884103eee215884103eec2158841004ff705884100cfe705884100cfc70588410067f76548410067e76548410067d76548410067c76548410073f74548410073c74548411467e645484120e7e63548410067d635484120e7c63548414b73e43548414b73c43548411357f72548411376f72548410367e62548410076e62548410366e62548410067d62548410076d62548410066d62548410367c625484113e7e61548412067e60548412067c6054841004fd76908411357e75908410057d759084112dde7390841005dd7390841005bd76908412cebd7690841004bd76908412cf3e75908412cf3d759084112dbe73908412cf9e739084112d9e73908412cf9d73908412cdbc7390841006bd6390841095be72908412cebd62908412cf3f52908412cf3d5290841005bd71908412d6be6190841005bd7090841004ff76508414aebe64508410973e75108410973d751084112dbe7310841095bc7310841006bd63108412cdbe7210841097ae7210841097ae62108412cebd6210841097ad62108412cf3f52108412cf3d5210841097b67110841005bd7110841097b571108412d6be6110841005bd7010841034ff768c84103cfe768c841004fd768c8411357e758c8410057d758c841095be748c841005bd748c841036ee628c841006ed628c841004ff764c841004fd764c84103cfc764c841005bf744c841095bc744c841016de634c841006dd634c84112f9c434c841036ee624c841006ed624c841005f7714c84103df4714c84112dbe73d0441095bc73d0441006bd63d04412cdbe72d0441006bd62d04414a73f52d04410073d52d044103dbd71d044103ebe61d0441005bd70d0441095f57490441096f6649044103fb6649044149fb64390441097b44390441497775290441007755290441007b64290441097b44290441004ff7650441005df735044112ddc735044103dbf7650441006bf7650441004bf76504410079f735044112dbe735044112dbc73504410079c735044112d9c7350441006bd63504412cdbc7250441006bd625044148f3f52504410073d525044103dbf715044103ebe615044103fb6515044148fb55150441005bf7050441095f77650441006f77650441004f7765044103df7745044103fb77450441096f66450441097b66450441097b6545044148fb55450441007d77350441007d4735044148f7
  | 29 => 0x67d76549410067c76549410067f63549410075f63549410065f635494120e7e635494120e7c63549410075c635494120e5c63549410073f43549410073d435494115d7f725494115f6f72549410067f62549410076f62549410066f62549410367e62549410367c62549410076c62549410366c62549412067e60549412067c6054941004fe76d0941006df63d09411fedc63d0941005be76d0941006be76d0941004be76d0941005bd73d09410079f63d09411febe63d09411febc63d09410079c63d09411fe9c63d0941036be62d0941036bc62d09414e73f52d09410073d52d094103dbe71d0941096bf61d094115d7e75909410057d75909414ddbd7490941155de7390941005dd7390941006df63909411e6dc6390941006ef6290941036ec6290941005f67190941005f57190941034fc7650941006df63509411cedc6350941006ef6250941036ec6250941005f77150941005f47150941034bc7650941005bf73509410079f63509411cebe63509411cebc63509410079c63509411ce9c6350941007af7250941007af6250941036be6250941036bc6250941007ac62509414d73f52509410073d5250941007b7715094103dbc7150941007b47150941004fe761094115d7e75109410057d75109414cdbe7410941006df63109411aedc6310941004fe768c941004fd768c941034fc768c94115d7e758c9410057d758c941005be748c941005bd748c941006df638c941016dc638c941004ff764c941004fe764c941004fc764c941005be744c941005bd744c941006df634c941016dc634c9410079f434c941006df63d054117edc63d0541007d763d0541007d463d0541097b743d0541007b543d05414c77752d05410077552d0541097b742d0541007b542d0541006df639054116edc6390541005bd73905410079f639054116ebe639054116ebc63905410079c639054116e9c6390541005bd72905412d6bc62905414bf3f52905410073d5290541007b7619054100cfe76d8141006df63d8141006dc63d814114efa60d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141014fe73d8141004fd73d8141014fc73d8141006bf43d8141006bd43d8141034fe72d8141004fd72d81410067f52d81410067d52d8141006bf42d8141006bd42d8141006be41d814114efa40d814114efa10d81410057f755814115d7c7558141005df7358141155dc7358141006df6358141006dc6358141005ef7258141005ec725814114ef86058141014ff7658c4103edc6358c410979c4358c41004ff7558c4101cfe7558c41004fd7558c4101cfc7558c4112ede5358c41006dd5358c41096df4358c4112ebe4358c4112ebc4358c41096dc4358c41004ff7258c41034fc7258c410067f5258c4112edf3258c4103ede3158c4103edc315
  | 30 => 0xf7258241034fc72582410067f52582410067d5258241006fb5058241166f85058241166fa4058241166fa3058241166fa205824103efb105824103ef81058241014fe76d8d41156de63d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41006df53d8d41156de53d8d41006dd53d8d41156dc53d8d41156de43d8d41034fe72d8d41004fd72d8d410067f52d8d41156df32d8d41156dc32d8d41156df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41156df30d8d41006de30d8d41156dc30d8d41155de76d8d41014de76d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d410079f74d8d410075f52d8d41006de60d8d41006dc60d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d41006df74d8d41156de74d8d41006df54d8d41006de54d8d41006dd54d8d41006dc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d410065f52d8d41006de52d8d41006dd52d8d41006dc52d8d41006df71d8d41156de71d8d41006dd71d8d41006df51d8d41006de51d8d41006dd51d8d41006dc51d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d41006de40d8d41006dc40d8d41006de20d8d41006dc20d8d41006de10d8d41006dc10d8d41156dc6358d41005de7618d41156de7618d41006df6518d41006de6518d41006dd6518d41006dc6518d411579d7418d410075f5218d41006de6018d41006dc6018d4116cfe76d0d41016dc63d0d41005be76d0d4116ebe76d0d4116cbe76d0d41155bd73d0d410079f63d0d41016be63d0d41016bc63d0d411579c63d0d410169c63d0d41005bd72d0d412f6bc62d0d414f73f52d0d411579f32d0d4103dbe71d0d41096bf61d0d411579c31d0d41014fc7650d41006df6350d41016dc6350d41005f77150d41005f47150d41155bc7650d41016bc7650d41014bc7650d41155bf7350d410079f7350d410079f6350d41016be6350d41016bc6350d411579c6350d410169c6350d41005bf7250d412eebc6250d414ef3f5250d41007b77150d4103dbc7150d41007b47150d411579f3050d41006df63d8941006dc63d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941014fe73d8941004fd73d8941014fc73d89410067f52d8941006ee52d8941006ed52d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d894115d7e75989410057d7598941155de7398941005dd7398941006df6398941006dc6398941006ef6298941005df7358941155dc7358941006df6358941006dc635894115d7e75189410057d7518941006df6318941006dc6318941036ee6218941006ed62189410067f76549410067e7654941
  | 31 => 0x8341006bd4358341004ff7258341034fc72583410067f52583410067d5258341006bf4258341006bd4258341096fb4058341096f84058341176fa1058341014ff7658e4103edc6358e4116f9e4358e41004ff7558e4101cfe7558e41004fd7558e4101cfc7558e4116ebe4358e4116ede4358e4116ebc4358e41004ff7258e41034fc7258e410067f5258e4116edf3258e4103ede3158e4103edc3158e41004ff7058e4100cfe7058e4100cfc7058e41154fd76d0e4116dbe74d0e41016dc63d0e41014ff7650e4116dbf7450e41016de6350e41006dd6350e4116f9c4350e41005f77150e4103df47150e4113d7e7598a410057d7598a4103eef6298a4103eec6298a4103eec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41014fe7358a41014fc7358a41006be4358a41006bc4358a410067f5258a4103eee2158a4103eec2158a41004ff7058a4100cfe7058a4100cfc7058a410067f7654a410067e7654a410067d7654a410067c7654a410073f7454a410073c7454a4115e7d6454a4120e7e6354a410067d6354a4120e7c6354a415073e4354a415073c4354a4113d7f7254a4113f6f7254a410367e6254a410067d6254a410367c6254a411367e6154a412067e6054a412067c6054a4113d7e7590a410057d7590a4116dde7390a41005dd7390a41036ee6290a41006ed6290a4103df67190a41005f57190a412d73e7590a412d73d7590a4116dbe7390a412d79e7390a4116d9e7390a412d79d7390a412d5bc7390a41006bd6390a412d7ae6290a412d6bd6290a41007ad6290a412d73f5290a412d73d5290a412d7b67190a41005bd7190a412d7b57190a41005bd7090a41034ff7650a41036ee6250a41006ed6250a41005f77150a4103df47150a4113d7e7510a410057d7510a41005bd7610a412d6bd7610a412d73e7510a412d73d7510a4116dbe7310a412d5bc7310a41006bd6310a412d7ae7210a412d6bd6210a412d73f5210a412d73d5210a41005bd7110a41005bd7010a41034ff768ca4103cfe768ca41004fd768ca4113d7e758ca410057d758ca41005be748ca41005bd748ca41036ee628ca41006ed628ca41004ff764ca41004fd764ca4103cfc764ca41005bf744ca41005bc744ca41016de634ca41006dd634ca4116f9c434ca41036ee624ca41006ed624ca4103dbd76d0641006bd76d064116dbe73d064116dbc73d0641006bd63d06412d5be72d0641006bd62d06414ff3f52d06410073d52d064103fb651d06414ffb551d0641005bd70d0641005f576d0641096f576d0641097b654d06414ffb554d06414ff7752d06410077552d064100cff765824103ef86058241004ff755824101cfe7558241004fd755824101cfc7558241004ff7358241014fe7358241014fc7358241004f
  | 32 => 0x456dc321853203edf311853203ef631185320aef5311853200cfe701853203efa701853200cfa7018532004fd701853203ef97018532004f9701853200cfc70185320aedf301853200cfe76d813218d7e75d81320057d75d8132186fa60d8132004ff75d813201cfe75d81320067e75d813201c7e75d8132004fd75d81320067d75d81320047d75d813201cfc75d8132094fe74d8132004fd74d8132034fd73d8132014fd72d81320067f52d81320067d52d813203cfe71d8132004fd71d8132186fa30d8132186fa20d8132186f86058132014ff7658f41096dc6358f41004ff7558f4101cfe7558f41004fd7558f4101cfc7558f41096df4358f41096dc4358f41004ff7258f41034fc7258f410067f5258f4117edc3258f4117edf3158f41004ff7058f4100cfe7058f4100cfc7058f4117edf3058f41095bd76d0f41016bd76d0f41014bd76d0f41016be63d0f410979e63d0f410979d63d0f41016bc63d0f41005bd72d0f412f6be62d0f4151f3f52d0f4117f9f32d0f4103dbe71d0f41097b671d0f41097b571d0f4117f9c31d0f4112cff7650f41005bf7650f4112ebf7650f4112cbf7650f410979f7350f41016be6350f41016bc6350f41005bf7250f412eebe6250f415173f5250f4103dbc7150f4117f9f3050f411457e7598b410057d7598b4117dde7398b41005dd7398b41096ef6298b41036ec6298b41096ec6258b41004ff7558b4101cfe7558b41004fd7558b4101cfc7558b41004ff7358b41014fe7358b41014fc7358b410067f5258b41096ef4258b41096ec4258b41004ff7058b4100cfe7058b4100cfc7058b410067f7654b410067e7654b410067d7654b410067c7654b4120e7e6354b410067d6354b4120e7c6354b410073f4354b410073d4354b411457f7254b411476f7254b410367e6254b410067d6254b410367c6254b412067e6054b412067c6054b41034bd76d0b41005bd73d0b411febe63d0b41096bc63d0b41036be62d0b41097ae62d0b41097ad62d0b41036bc62d0b4150f3f52d0b410073d52d0b4103dbe71d0b41097b671d0b41097b571d0b411457e7590b410057d7590b4117dde7390b41005dd7390b41005bf7650b41006bf7650b41005bf7350b411cebe6350b411cebc6350b41097af7250b41036be6250b41036bc6250b414af3f5250b410073d5250b4103dbc7150b41034ff768cb41094fe768cb41004fd768cb411457e758cb410057d758cb41095be748cb41005bd748cb41016de638cb41006dd638cb41004ff764cb41004fd764cb41094fc764cb41095be744cb41005bd744cb41016dc634cb410079f434cb41005f7714cb41005f4714cb4100cff7658341096f86058341004ff755834101cfe7558341004fd755834101cfc7558341004ff7358341014fe7358341014fc7358341006bf435
  | 33 => 0xc7599132094fe74991321fcfd7399132096dd73991321febe4399132096bc43991321ccfd7299132096ed72991320067f52991322f6be4299132096bc429913203cfe7199132004fd719913200cfe7099132004fd709913200cfc70991321cf9c43591321fdef7259132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc7559132006bf74591321ccff7359132006df73591321cebe43591321cebc43591321cedc43591321fcff7259132006ef72591320067f52591322eebe42591322eebc4259132004ff7159132006f77159132004f7715913203cfc7159132006f47159132004f47159132004ff705913200cfe705913200cfc70591321cedf30591321e4fe7619132006bd6419132094ff751913201cfe7519132004fd7519132094fc7519132096be7419132034ff7319132034fd7319132096bf43191321aebd43191320067f521913203cfe7119132004fd711913200cfe7019132004fd701913200cfc7019132035de76d0d32006de76d0d32034de76d0d32015de74d0d320179e74d0d32006df64d0d320079f64d0d32006dd64d0d320079c64d0d32035de72d0d32007ce72d0d32007cd72d0d32035dc72d0d32016df62d0d32017cf62d0d325275f52d0d322f79e42d0d322f79c42d0d32005dd71d0d32005dd70d0d3201e7f765493220e7e765493220e7d765493201e7c76549320067f64549320067e64549320067d64549320067c64549320075f735493220f5c73549320367f63549320075f435493220f5c43549320357f725493218f6f72549320367f62549320376c425493220f6f32549320375e32549320375c32549320376c32549320374c325493220f5f31549320376f21549322067e60549322067c605493220f5f30549320376f2054932014fe76d0932014fc76d0932006bf64d0932096bc64d0932015de73d0932005dd73d09321ff9c43d09320076d52d0932094ff7650932014fe76509321ccfd7650932014fc7650932006bf6450932006bc6450932005df7350932015dc73509321cf9c4350932004ff75d853201cfe75d8532004fd75d853201cfc75d8532094fe74d8532004fd74d8532034fd73d85320067f52d85320067d52d85320f6f631d853200cfe70d8532004fd70d853200cfc70d8532006f76198532005bf7458532005bc745853218d7e75185320057d7518532005be7418532005bd7418532006f56118532185fa7018532005f9701853203cff751853201cfe751853203e7e751853201c7e7518532004fd751853203e7d75185320047d751853203cfc7518532094fe741853203ebe7418532004be7418532004fd741853203ebd7418532004bd7418532034fd7318532006df43185320aedc431853203eed72185320067f52185320067d5218532456de3218532
  | 34 => 0x9232036bc2099232006be1099232006bc1099232004ff755923201cfe7559232004fd755923201cfc7559232036bf7459232006bf5459232006be5459232006bd5459232006bc54592321cebf43592321cebd4359232034fe7259232034fc72592320367f52592320367d5259232036be4259232036bc4259232004ff715923203cfc7159232004ff705923200cfe705923200cfc7059232006be4059232006bc4059232006bf7559232006be7559232006bd7559232006bc75592321cebf73592321cebe73592321cebd73592321cebc73592321cebf53592321cebe53592321cebd53592321cebc5359232036bf7259232036be7259232036bd7259232036bc7259232036bf52592320363f5259232036be5259232036bd52592320363d5259232036bc5259232036bf3259232036be3259232036bd3259232036bc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc51592321cebf31592321cebe31592321cebd31592321cebc3159232036bf2159232036be2159232036bd2159232036bc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc50592321cebf30592321cebe30592321cebd30592321cebc3059232036bf2059232036be2059232036bd2059232036bc2059232006be1059232006bc105923203cff759863201cfe7598632004fd759863203cfc7598632094fe7498632004fd7498632034fe729863203eee7298632034ee729863203cfc72986320367f52986320367d529863203ef6719863203ef631986320e6f5319863203eef2198632036f7219863203ef4219863200cfe7098632004fd709863200cfc7098632004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632094fc7458632034fc72586320367f52586320367d5258632036df3258632036dd3258632036f771586320cef631586320cedc3158632036f72158632036f42158632004ff705863200cfe705863200cfc7058632004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232094fc7458232034fe7258232034fc72582320367f52582320367d5258232036df3258232036dd3258232004ff715823203cfc7158232056dc3158232036fb7058232196fa3058232036fb2058232036f82058232196fa1058232004ff75d913201cfe75d9132004fd75d913201cfc75d9132034ff73d9132034fd73d9132006dd73d91321e6bf43d91321e6bd43d91321e6dc43d91320067f52d913203cfe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d91321e6df30d9132006bf64991321ff9c43991321cded7299132094ff759913201cfe7599132004fd7599132094f
  | 35 => 0x36bf4258442036bd4258442036f77158442096f74158442096f44158442036f72158442036f42158442004ff705844200cfe705844200cfc7058442004ff755804201cfe7558042004fd755804201cfc7558042004ff7358042014fe7358042014fc7358042006bf4358042006bd43580420367f52580420367d5258042036bf4258042036bd4258042004ff715804203cfc7158042036fb7058042096fb4058042096f840580421a6fa3058042036fb2058042036f820580421a6fa10580420067f74596320067e74596320067d74596320067c745963220e7f735963220e7e735963220e7d735963220e7c735963220e7f435963220e7e435963220e7d435963220e7c43596320367f72596320367e72596320367d72596320367c72596320367f42596320367e42596320367d42596320367c42596320367f32596320367e32596320367d32596320367c32596320067f71596320067e71596320067d71596320067c715963220e7f315963220e7e315963220e7d315963220e7c31596320367f21596320367e21596320367d21596320367c21596320067f70596320067e70596320067d70596320067c70596320067e40596320067c405963220e7f305963220e7e305963220e7d305963220e7c30596320367f20596320367e20596320367d20596320367c20596320067e10596320067c1059632094ff759923201cfe7599232004fd7599232094fc7599232036be7499232006bf5499232096be5499232006bd5499232096bc5499232096bf43992321febd4399232034fe7299232034fc72992320367f52992320367d5299232036be4299232036bc4299232036df3299232036dd329923203cfe7199232004fd71992321fedc319923200cfe7099232004fd709923200cfc7099232006be4099232096bc4099232096bf7599232006be7599232006bd7599232096bc7599232096bf73992321febe73992321febd7399232096bc73992321febf53992321febe53992321febd53992321febc5399232036bf7299232036be7299232036bd7299232036bc7299232036bf52992320363f5299232036be5299232036bd52992320363d5299232036bc5299232036bf32992320369f3299232036be3299232036bd32992320369d3299232036bc3299232096bf7199232006be7199232006bd7199232096bc7199232006bf5199232006be5199232006bd5199232006bc51992321febf31992321febe31992321febd31992321febc31992321fe9c3199232036bf2199232036be2199232036bd2199232036bc2199232096bf7099232006be7099232006bd7099232096bc7099232006bf5099232006be5099232006bd5099232006bc50992321febf30992321febe30992321febd30992321febc3099232036bf2099232036be2099232036bd209
  | 36 => 0xf75d814201cfe75d8142004fd75d814201cfc75d8142034fd74d8142014fe73d8142004fd73d8142014fc73d81420067f52d81420067d52d814203cfe71d8142004fd71d8142006fb50d81421c6f850d81421c6fa40d81421c6fa20d81420057f75581421d57c75581421c6f860581421b67f74594420967e74594421b67d74594420967c74594420067f73594420067e73594420067d73594420067c73594420967f43594420067e43594420967c43594420367f72594420367e72594420367d72594420367c72594420367f42594420367e42594420367d42594420367c42594420367f32594420367e32594420367d32594420367c32594420067f71594420067e71594420067d71594420067c71594420967f41594420967c41594420067f31594420067c31594420367f21594420367e21594420367d21594420367c21594420067f70594420067e70594420067d70594420067c70594420967f40594420067e40594420967c40594420067f30594420067e30594420067c30594420367f20594420367e20594420367d20594420367c20594420067e10594420067c1059442004ff7558c4201cfe7558c42004fd7558c4201cfc7558c42036df7358c42096df4358c42096dc4358c42034fc7258c420367f5258c420367d5258c42036de3258c42036dc3258c42004ff7158c4203cfc7158c421aedf3158c42004ff7058c4200cfe7058c4200cfc7058c421aedf3058c42095bd76d0c42016bd76d0c42014bd76d0c420973e65d0c420973d65d0c422edbd73d0c42016be63d0c420979e63d0c420979d63d0c42016bc63d0c42097ae72d0c422f5bd72d0c42097ad72d0c422f6be62d0c42097ae62d0c422f73f52d0c422f73d52d0c422f79f32d0c42005be71d0c421af9c31d0c421fcff7650c4221e7e6550c420067d6550c422edbf7650c421febf7650c421fcbf7650c422ef3e6550c422ef3d6550c42095bf7350c420979f7350c42016be6350c42016bc6350c422edbf7250c422eebe6250c422efae6250c422ef3f5250c422ef3d5250c42005bc7150c421af9f3050c42035ef7650842006ef7650842004ef76508420376e65508420376d6550842035ef7450842037af7450842096ee6450842037ae6450842097ae545084252fad545084203cff759844201cfe7598442004fd759844203cfc7598442014fe7398442004fd739844203cfc73984420367f52984420367d529844203ef67198442096f7419844203ef44198442036f7219844203ef4219844200cfe7098442004fd709844200cfc7098442004ff755844201cfe7558442004fd755844201cfc7558442004ff7358442006df7358442004df7358442014fe7358442014fc7358442006dc7358442014dc7358442006bf4358442006bd43584420367f52584420367d5258442
  | 37 => 0xa42096ed76d0a420376e65d0a420376d65d0a42037ae74d0a42097ae54d0a4254fad54d0a42037ce63d0a42037cd63d0a4203cff759864201cfe7598642004fd759864203cfc7598642014fe7398642004fd739864203cfc73986420367f52986420367d529864203ef67198642036f7219864203ef4219864200cfe7098642004fd709864200cfc7098642004ff755864201cfe7558642004fd755864201cfc7558642004ff7358642014fe7358642014fc7358642006bf4358642006bd43586420367f52586420367d5258642036bf4258642036bd4258642036f77158642036f72158642036f42158642004ff705864200cfe705864200cfc7058642004ff755824201cfe7558242004fd755824201cfc7558242004ff7358242014fe7358242014fc7358242006bf4358242006bd43582420367f52582420367d5258242036bf4258242036bd4258242004ff715824203cfc7158242036fb70582421defa4058242036fb2058242036f820582421defa1058242014fe76d8d421cede63d8d421cf9e43d8d42004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d42034fd74d8d42034bd74d8d421cebe43d8d421cede43d8d421cebc43d8d420067f52d8d422f6be42d8d422f6bc42d8d421cedf32d8d4203cfe71d8d42004fd71d8d421cedc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d421cedc6358d421cf9c4358d42005f77158d42005f47158d421e4fe76d0d421cdbe74d0d42016de63d0d42034fc7650d421cdbf7450d42006df6350d42016dc6350d421cf9c4350d42005ef7250d42035ec7250d4201e7f76549421be7e76549421d67d765494201e7c76549420073f74549420073c74549420367f64549420067f635494220e7e635494220e7c63549425473e43549425473c43549420357f72549421d76f72549420367f62549420373e42549420373c42549420376c42549420372c42549425476f32549420376c32549420376f21549422067e60549422067c60549420376f2054942035be74d0942036bf64d094253f6f52d09420076d52d0942035ee74d0942036ef64d0942037af64d0942537ae43d0942097ac43d0942004ff75d854201cfe75d8542004fd75d854201cfc75d8542014fe73d8542004fd73d8542014fc73d85420067f52d85420067d52d8542006f731d8542006f431d854200cfe70d8542004fd70d854200cfc70d8542006f76198542005df73585421cddc7358542006f5611854203cff751854201cfe7518542004fd751854203cfc7518542014fe7318542004fd731854203cfc7318542006be4318542006bc43185420067f52185420067d52185422cebe42185422cebc4218542006f7311854203ef4311854200cfe7018542004fd701854200cfc701854200cfe76d81421c6fa60d8142004f
  | 38 => 0x96f840583421f6fa20583421ee7f74596421ee7e74596420067d74596421ee7c74596420067f73596420067e73596420067d73596420067c73596420067e43596420067c43596420367f72596420367e72596420367d72596420367c72596420367f42596420367e42596420367d42596420367c42596420367f32596420367e32596420367d32596420367c32596420067f71596420067e71596420067d71596420067c71596420067f31596420067c31596420367f21596420367e21596420367d21596420367c21596420067f70596420067e70596420067d70596420067c70596420067e40596420067c40596420067f30596420067e30596420067c30596420367f20596420367e20596420367d20596420367c20596420067e10596420067c1059642004ff7558e4201cfe7558e42004fd7558e4201cfc7558e42036df7358e42006df5358e421e6de5358e42006dd5358e421e6dc5358e421e6de4358e42034fc7258e420367f5258e420367d5258e42036de3258e42036dc3258e42004ff7158e4203cfc7158e421e6df3158e421e6dc3158e42004ff7058e4200cfe7058e4200cfc7058e421e6df3058e42006de3058e421e6dc3058e42006df7558e42006de7558e42006dd7558e42006dc7558e42006dd7458e421e6dc7458e42006df5458e42006de5458e42006dd5458e42006dc5458e42036df7258e42036de7258e42036dc7258e42036df5258e420365f5258e42036de5258e42036dd5258e420365d5258e42036dc5258e42036df4258e42036de4258e42036dd4258e42036dc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006de5158e42006dd5158e42006dc5158e42036df2158e42036de2158e42036dd2158e42036dc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e42006de5058e42006dd5058e42006dc5058e42006de4058e42006dc4058e42036df2058e42036de2058e42036dd2058e42036dc2058e42006de1058e42006dc1058e421ccfd76d0e4222e7e65d0e420067d65d0e42016de63d0e422f5bd76d0e421cebd76d0e421ccbd76d0e422f73e65d0e422f73d65d0e42016be63d0e422f79e63d0e420169e63d0e422f79d63d0e42016bc63d0e422f5bd72d0e422f73f52d0e422f73d52d0e422f79f32d0e42005be71d0e421e79c31d0e42014ff7650e4221e7e6550e420067d6550e42016de6350e42006dd6350e42005ef7250e42035ec7250e422edbf7650e42016bf7650e42014bf7650e422ef3e6550e422ef3d6550e420079f7350e42016be6350e422ef9e6350e420169e6350e422ef9d6350e42016bc6350e422edbf7250e42007af7250e422efac7250e422ef3f5250e422ef3d5250e42005bc7150e421e79f3050e42035ed76d
  | 39 => 0xe70585522057c70585520077870585522057870585520fd7e76185520057e74185520057d741855220d7e73185520057d731855220d7c73185520b67f62185520b76f62185520067f61185520077661185520067d61185520077561185522057e70185520057d70185522057c70185520067e60185520067c60185522057e76d81520057e74d81520057d74d815220d7e73d81520057d73d815220d7c73d815206f6f72d81520357e72d815201d7d72d815206e7f62d815206f6f62d81520057e71d81520057d71d81522067e60d81522077a60d81522067c60d81522077840d81522077a30d81522077a20d81522077810d81520057f74581520073f74581520053f74581520057c74581520073c74581520053c74581520057f735815220d7e735815220d7c735815255d7f72581520076f725815255d6f725815205e7f625815205f6f62581520057f71581520057c71581522057f70581520077b60581522067e60581522067c6058152207786058152206786058152014ff7658f42096dc6358f420979c4358f42004ff7558f4201cfe7558f42004fd7558f4201cfc7558f42034fc7458f42034bc7458f421fede5358f42006dd5358f42096df4358f421febe4358f421febc4358f42096dc4358f420067f5258f422eebe4258f422eebc4258f421fedf3258f42004ff7158f4203cfc7158f421fedc3158f42004ff7058f4200cfe7058f4200cfc7058f421fedf3058f421acff7650f421fdbf7450f420979c4350f4201e7f7654b4201e7c7654b420073f7454b420073c7454b420367e6454b4220e7e6354b420067d6354b4220e7c6354b425573e4354b425573c4354b420357f7254b421bf6f7254b420367d6254b420373e4254b420376e4254b420372e4254b420373c4254b420376e3254b420376c2154b422067e6054b422067c6054b420376f2054b42096f7619874203cff759874201cfe7598742004fd759874203cfc7598742034fe7498742014fe7398742004fd739874203cfc7398742006be4398742006bc43987420067f52987420067d52987422d6be42987422d6bc4298742096f7419874203ef4419874200cfe7098742004fd709874200cfc7098742096f46158742004ff755874201cfe7558742004fd755874201cfc7558742034fc7458742004ff7358742014fe7358742014fc73587420067f52587420067d5258742096f74158742096f44158742004ff705874200cfe705874200cfc705874200cff76583420057f75583421bd7c7558342096f86058342004ff75583420067f75583420047f755834201cfe7558342004fd755834201cfc75583420067c755834201c7c7558342034fc7458342004ff7358342014fe7358342014fc73583420067f52583420067d5258342004ff715834203cfc7158342096fb4058342
  | 40 => 0x91520077b70591520057b70591522057e70591522057c70591520077870591522057870591521ed7e76191520067f64191520073e64191520067d64191520073d641915220d7e73191520057d731915220d7c73191521b67f62191521b76f62191520057e71191520057d71191522057e70191520057d70191522057c70191520067e60191520067c60191520073e40191520073c401915220d7e76d8d520057e74d8d520057d74d8d5220e7e63d8d5220f5e63d8d5220e5e63d8d5220e7c63d8d520357e72d8d5201d7d72d8d5219e7f62d8d5219f6f62d8d5220f5f32d8d520057e71d8d520057d71d8d5220f5c31d8d522057e70d8d520057d70d8d522057c70d8d520067e60d8d520067c60d8d520057f7458d520057c7458d5220d7f7358d520075f6358d5220e7e6358d5220e7c6358d5220f5c6358d525657f7258d520076f7258d525656f7258d5218e7f6258d5218f6f6258d520057f7158d520057c7158d520057f7058d522057e7058d522057c7058d520067e6058d520067c6058d5220f5f3058d520057f76d0d520057e76d0d520057d76d0d520057c76d0d5220d7e74d0d520073f64d0d520073c64d0d5220d7d73d0d5220f3e43d0d5220f5e43d0d5220f3c43d0d520357e72d0d520076e72d0d520356e72d0d520057d72d0d520076d72d0d520056d72d0d520357c72d0d5247e7f62d0d5222f6f62d0d5220f5f32d0d520057e71d0d520057d71d0d5220f5c31d0d522057e70d0d520057d70d0d522057c70d0d520057f7650d520057e7650d520057d7650d520057c7650d5220d7f7450d520073f6450d520073c6450d5220d7f7350d520075f4350d5220f3e4350d5220f3c4350d5220f5c4350d520057f7250d520357e7250d520357c7250d5247e7f6250d5221f6f6250d520057f7150d520057c7150d520057f7050d522057e7050d522057c7050d5220f5f3050d520057e74d85520057d74d855220d7e73d85520057d73d855220d7c73d85520067f63d85520067d63d85520fe7f62d85520ff6f62d85522057e70d85520057d70d85522057c70d85520057e74985520057d749855220d7e73985520057d739855220d7c73985520d57d72985520076d72985520d56d72985520be7f62985520bf6f62985520b57e71985520067f61985520077761985522057e70985520057d70985522057c70985520067e60985520067c60985520057f74585520073f74585520053f74585520057c74585520073c74585520053c74585520057f73585520075f73585520055f735855220d7e735855220d7c73585520075c735855220d5c73585520067f63585520067d63585520bd7f72585520076f72585520bd6f72585520d67f62585520d76f62585520077761585520067e61585520057f70585520077b70585520057b70585522057
  | 41 => 0x3ef4419874303ef6319874316ef5319874300cfe7098743004fd709874300cfc7098743096f46158743004ff755874301cfe7558743004fd755874301cfc7558743014fc7458743004ff7258743034fc72587430067f5258743156df3258743096f74158743096f44158743156f63158743156dc3158743004ff705874300cfe705874300cfc705874300cff76583430057f755834322d7c7558343096f86058343004ff75583430067f75583430047f755834301cfe7558343004fd755834301cfc75583430067c755834301c7c7558343014fc745834307ede4358343004ff7258343034fc72583430067f525834307edf3258343004ff715834303cfc715834307edc3158343096fb4058343096f84058343226fa3058343015de74d0d430179e74d0d43016df64d0d430179f64d0d4356f5f52d0d43005dd70d0d43004ff75d894301cfe75d8943004fd75d894301cfc75d89431febd74d8943006df43d89431febe43d89431febc43d89431fedc43d89430067f52d89431feee32d894303cfe71d8943004fd71d894300cfe70d8943004fd70d894300cfc70d89431fedf30d894321d7e75989430057d7598943006ef6298943005f77158943005f4715894321d7e75189430057d7518943036ee6218943006ed6218943004ff75d854301cfe75d8543004fd75d854301cfc75d8543034fe72d8543004fd72d85430067f52d854317ef631d854300cfe70d8543004fd70d854300cfc70d8543006f76198543006f5611854303cff751854301cfe7518543004fd751854303cfc751854303ebd7418543006df431854312ebe431854312ebc431854312edc4318543034fe7218543004fd72185430067f521854303ef6311854312ef5311854300cfe7018543004fd701854300cfc701854312edf301854300cfe76d8143216fa60d8143004ff75d814301cfe75d8143004fd75d814301cfc75d8143014fd74d8143034fe72d8143004fd72d81430067f52d814303cfe71d8143004fd71d8143216fa40d8143216fa30d81430057f755814321d7c7558143216f8605814320d7e73d91520057d73d915220d7c73d91521ee7f62d91521ef6f62d91520057e71d91520057d71d91522057e70d91520057d70d91522057c70d91520073e40d91520073c40d91521b57e74991520067f64991520073f64991520063f649915220d7e73991520057d739915220d7c73991521d57d72991520076d72991521d56d72991521be7f62991521bf6f62991520057e71991520057d71991522057e70991520057d70991522057c70991520067e60991520067c60991520073f64591520067e64591520057f735915220d7e735915220d7c73591521bd7f72591520076f72591521bd6f72591521d67f62591521d76f62591520057f71591520057c71591520057f705
  | 42 => 0x2c014003400b0050015000800a000c0080028003001800100080020010000003401200180050090000002000500200090000000001400500380000008002000000100040060044005001800200000000004003000400b000c00800040030000001000400a000401e000400100040000010007000400000340000000001001000000240120000001000000b0018002002c0030004001003c004001c0120028006000001c00000020044001000c007001000300000050000000000000500000220004005001c0030000000001c00c0004000000c00e001c000001c00000000000000002000400200440150000001001c004000401f00140020004001003000a003c0010008004000000a0000000007c0040048004001800200000250004002002c034003c00300100020008002005c00000140040000005005400200000160000004002c0050004002000800100080030000002001801600000000000022001c00000040000004009005800100080080000000000800200040020008003016c006000800000100050000011005000e000c00100300010000006001c00900040040070000000c0030000012004c003000c000017800000040040008010000c0000000007001800e0024005000400000500010000003001c0060000004003c000002c005001400000040030000002001c013000c00000580050044005002800200140110014009000400000100000000003001c036000000d001400000180000030000000000000740080034001005000c00080060014001000c002000000000040050000001000c005000000b00300000034008001400400100040010007000400a001c000000000b000802c000000100680050070000000000d0000010004c004000400200000050074002000400b0000000000400d000c004000c000001000200000020014000000c010000800400080050014000000402d001c00500040060024003000000300100000038000002000000000220000027000c0030004000000000700100000008005001c004004800000040020008008003c0080000004000000f000c000000c000000c00f0020003000c00e000800100080050030006000802f22d7e7598b430057d7598b43096ef6298b43036ec6298b43096ec6258b43004ff7558b4301cfe7558b43004fd7558b4301cfc7558b43014fc7458b431cebc7458b431cebe4358b431cebc4358b430067f5258b43006ee5258b43006ed5258b43096ef4258b43096ec4258b431ceee3258b43004ff7158b4303cfc7158b43004ff7058b4300cfe7058b4300cfc7058b43096f7619874303cff759874301cfe7598743004fd759874303cfc7598743014fe749874303ebe749874316ebe439874316ebc4398743034fe7298743004fd72987430067f5298743096f74198743
  | 43 => 0x4002c0010048010000c002000001d000400200000020068002000800000080000000000000c000000c0090018000004400b000000000040060014007003c0020000032001c00100280000010000000c003000c000001000500240050008000004801b00b001a002c0090008009001000a001400b00100000034001000000500000000000000000400b001c0010000001002400300080020014002000c00900200000004009000400b00b0000000c003000800e00140030000008001400300240000020002000000000040030004006007800700040060018004001000000c0001006c00600440250018004002c00d0008002000000e000800b0014001000000800080010018002001800b00140000008001000000000040020024003003400300000020004003001c00a00000070000004000000000000040000000000000d000400000380000008008001000a004400e0010000000001000140020000007000400000080010008000000400000200030074001000000b000c0040004000000001000440000034000000c00000100100024005000000c0008010003c0000004001007000e0014000003c01000a800300200160080001002c000000c00a0010001000001600000020000010002c00100140090018036004000f000c006004c00100200270018000000c0190058005000400000040050000004000c00b00200010000000000000200000080008000000800000080020000003001400500000080008000000001500900000014009001402e002800100100010008000000c01a00200000004001000000000140070000004001c00600500170000004000400100100090004002001c0060000000000800200040010000001000000900080270004001000000000000080000003000000e0004005000400000940020010009002800000000140004003000c003001000300ac00100000010010001000400000600030000002003c001000001e00000050008001001800200240030004017000000000000040000001000c002002c00d0000003000400e0008003001000900180040010012000000200a000000300020000000000800e0070002000c015000c001000400b00000000044018002404c0000005000800200040030024006000800b00000080000011004c0000000001005400300680020220004002000b000c00f000400d000800a0004017000000d0000016000800100000040024000000000000000050070004000c00000000000010001000400000040010004000000000300000000004000000401a00000000000000000c0000014006000000f004802300000060000004000c00d0000001000000c0004000000c0040008002000800d00040010000019000c014000000400100030024008000400200200070088001003400
  | 44 => 0xc005005800d001400100000080010005002c001000800000000000008009001000a0000014000400c0000002000800100b0000008400b0098003003c000003800300000000000004002800000280000008003000c0080030001000000400380020000006000c0000008008003000e000400000a4000000c007000000200180000000000002800300a0000002801a002c001000800100000000010001000c03800080000000019000400100000000004002000c002000801c00040070004000000000b00c00060000001003c0190000007000c0100008001000c004001000f002c01700040000004002000401200100010000002000c0000010000004000900100010000000003800000100000010002003c0030008001001400b00180000000013000400000040030000006003c00f000400000400170070003000800b000c00000000070014002001400b0018000001400000000050000003004c002006c0050014000000001f0000005000c025001c008000c00a0004010003800000b000300040010000000000400400040110008008000000400040110000000001c0060000003000800f002c000000800300180010018005000400a00040150000001000000a002000000000020004002000001c00000030000000000000a00040010000013000c00000080010004005003800900840090008000000400a002400d00000020058004001000000740020028002012c0040018000005000f001400700040050000005000000000100070000004000c0040000002003800000000000004005001400a0078003006000000540000024000005401900040010000001003c0060008002002400300080000000001000c00900080000044016001001d00240010000012001000f00100090010000000000900040070000000000c00e000c00d00080180000002000800600080000000000000c002003c005000c0090034007001c0030010003003400500380020000000000c0040000009000000100000000000005009c003000c0020028005001400200000010014000001000c00000020008012008c00f001c00c0004000000c00d0004000001400d0000001002800500480010018008000c0110000002000000f001800000000110004018000001100040020018001000c004004400b0028002000400000080000028002002000c000001a000001c000001c0008000003002e001000900340020004028003c017000000100140000030006001c0020000002003002e0044002000400400000000000001000c000002c00000100080008004000801400140000020001000001800000080014000000000a000400e0018007000400d000c0050010003000c00000400030000002006c008004c0000000001000000000000020014001001c000004c00300
  | 45 => 0x2800100000030014006000800300200010000002000c0010008001000c00f00040010000003000c0010000009000c0030004019001800800000010000000000000b00000030000000000000300040060000001001c00c0074007004c0090038004000400400000000010002000000100a00000000001000000200000030000000001c0040010001000000000000120000005000400100100010000003002000200100010060009000c00400000120010002003c000000c0000000003000c008000c0080014004000000500200060000006000c001003c0050000002000400000200070008009000c0000000001000000000000070000004000402100040030000008002000100a8003000400300080000000001002000600140000000003001801a0000003002400700040030000001003000200040050000025002400b000400500240000098007000800500180020000000005000600000300000009001800a002c021004401300000070010021000000000b4002000000200100000060000002c000000c00e0020000000401200040020054004001000000040010014001001c00d00040030000006001803000000050004000002c00f0030016000000000100060030002002c00400100080000002001000200040050004002005800100040050028000004800300000090020004004400900000020068013000800400000010000004000c001000c00200000010004000000c0000020008000000000340030004008001000400040000004000000800000000070000000002c0070014000002c00e001c017000c0170038000003000e00100000008010000c000000800200240030004008003c00c0000000000000a0000004000000300040020000003008c0030000008000c00000140010000001001400000000000000001003c00b0024000000400100f400100080000000001001c03c000401200000000010003000000400000080028000001400300080000000002003000100200030000004007800500040020000002007c000005c000000800000040020000000000400c000000000000150000001000003000080000050005001c00200200000044002000000d0000006002c00000040300000001009000f000c0010010001001c00500000010004001003800100040000010012000000400080060058005001c005000000400140000018003004c0020000005000402700040110054016000c002005c0020000001001800f001000100040000004002003000000040030000001005c002001800100280040014003000002d000000300100300004001000400700000060004011006000200a000e004400000000000000002001c000000000200540010004002001400000100030008013000000e001c00100480000014002000c00a00000
  | 46 => 0x59027194349f2a178cf2331246b15761d3a90e000313825f8eeecc22a0c01b1aa259584ce11aa53e67920cca2bafee93a00006bf0000a670a7885c8dd409098c48190ace0001e0c08f00000002f68061000000037c215619a631498946d3239683a1bf454e805aba78362b8f987cd97b71a4468a6810a18a2dd01482c6c327c61a0000228b11062281a2b11800071791dca1c8000051aa2000028860002740c742a02c0b9d3a00013f4e0d810cbc6800043b2a1e070ad643ee1c28a111c86b873582b0b31ca0001f607cd800088e34846038126c8328886c30000d4aa69200000004bc263ea86154e2152d08245353c869b61e00011fa845000093080000002fce0cd864463400003aa000063f0094bf4000000012be0000408558897c00000005ba000096d17948db2f0e80a9390bd4000000000000001f6e38f025200000006e2317092900000001a32cb70000e0b000000028801a60000b2d000000000004a92306e0096820001cb600000000001064000042caa080008149c1a00003b228680004dc8ce003f80000002a4657c80008f42124a4d16304b4134e44081fc0eb91800002f58000039a000057c0000b7c71d0000d1601900000000ad98000000144c2d92962c9780009300cc444a9f4e363a02806a08ea275a0e0c94b61a63386b0b768290151274a65c28b6660a042d59233c7b58f4a0ca26306bd00006a583a0c9d0140e109a060000000156828aa2c2af000b2cead06af9212d83fc000084a59c09761fc298633892783c4140e00010f4c990756b96ae1e52423fa1e50000a1899c200016f85562d9845819040000000580063cc2d18ae00000004df23c0ddea40a000174c00000000000000000000091f0000030939a5c78000000221a2f8851a0000000000000000032e678ca77c0000000bd30000000000000000002072918000202c000000021989ac14b000000009bcd4c0000b5600040004006002c0010004009001c000002400600000080008007002000200140040004001005000f0000018001800c00000000038001004c00000180050004001001001f002801600100090004000000800e00780000014008000000b00000000000008001c00d003c00a00040060000007001000e000c0080008000005801300740000018007000800000180080000000000c0070094011002000d000c00100740000040031000000000000040000001000400c0020000000c000002000f009401500280030078012000c00000300010024000001c000000400501740160030000004400200000070000004000c0000004002000000400780020004001001000000180170058000003c002000000c00280080000002000400501580000000008002800100580010000007002001500480010004002000000000580020010005000000200000010
  | 47 => 0x5d1260a432b3bc91c364e9e113a4922ab345e981f8418887c5ab848cb3f2e509c78ff0b6580006209dc800004642272e2cacb2958baa94ccb6a018cafa99507d4ab72000000000030125022f98000291a0788b08674800000000000000210670000000035c20000000000000081f80007ec8eb4c888000565800047893926820000b0106d84efa3a452c8000000092070900807da957c0002f60000000000032aa00017560000000710000088580000000d9008186881ff3426372800098ca038a9a8000ce90b2400010926b6800059f000005a1c4e1c908c80002e52a0202a20ef0edad1d0000898a7aa11b80dcdf5b18edd81e3017e35188f2034854397421240000a3fb36ec768000000085ebbe0000323928427c93706679f946e988b465baa2828403bee07080e4811fd850a0be4d5100007a12b2a0b692b464892c4505294e087b354bce2d002ff1302549ac8687c849cb6c800000000000a0a84200016125f90000e0325726b78f3800000009f4acb8ac2184a7f418c03ef8d1e0001e06b5a9c88000000000037cc00000000000f5c2f98fa6327834400000002e400000001d4499a08425eb15ecb070f8492e1e6463d141025809cec470db62c8282201d248c159af32a790dded079a6244424ac73e0000000302208c83cc42185dcb78281498180001e180009eeadbcc89000009e92fc931b3dc4f29d722478000bbeb40086416ea3060e369191cba000000000027e46ea36b0c782600cff00009eca2f68f9000000000003cd19f20449622694a39289580000003436900074c77c817a1f42bb414025d6cc18f088371fbaaa707e081195dc88e9754a299e20523169c6f50d64000000000021b40000000a5d289adf7000077b8000b082ee200010ea0000f705822dd2c251764b68050cc3c0aba1582546a40b3e257517a200000005b50000b0c18e40000000c59902e69d28a2b361610000000000000007bea8c63dfa93649aa17a4948e024ba2c500e38c5a06c80004d78ebe00000008129ddc8578000b9e25e2a45000000017860002abc00000007ba337e000000000000000470000000000034cb7c400000000000000c7a9a2ca9cb21400017e000004148c68c36c9c98baa981c825689b7e4f8810844cb80e09200000198000dd987f264a0ae4647253a0002164b9a16c23d68000b578a6ebb2826a40a2cbe0002d1aa6e80004a714d60b00e8e950000076a0ad00000f662d4195e9349ce277f8bb62bd29549ac1750000198cc87a02477798606c580004d092e0dc09c3c000094200035ecda30000e0400001c18f3233283c6000148e4e7242827a01cc293abbe18382d80002c60d4e1bb0834b00600021461c000000000000293276a90180000000dc2000000000033be482800090d299800034eab89b7c83910fac9049104460a480a4e0
  | 48 => 0x50e993146ac7d000075e8d260001cf68b1800080f8a94de900005e0000098f0000000063800000007b992485a60000000000070400005fd800025c10d80000000299aae400000000001f3800026b20000ffa5ca1ec65ed0e2488791fc000297a3e6a4d600000003628000a9f00000000f4e8458000166000056cb22ca0b00000000000a1c00000002f7430e28be000000000016648650edc4238000661992a000000034f0000959800008f800000028e400022f4000000000000000000000000149600022dc6f29c907af2d8e5a486241148ea63b8025e60780000a68000000000000000000002ca617ea41e0000000bec0000ccf80004f48000000000047c0000ca28000251a3cc6e70f94b5511768acaa6800013e828db2b0000000092d9fe600000000000000bac80000003710403298e000283a0001f9acc3a5da32b0d5400016683822e2e33e8670dffa17000022864728c5828b06723a7a11883c946cc082884272b1468e8948a5de00f02b288063340aecb089068010b57ad6fa69e0000000dd60d00c8485567ca02d0c673246393ae7eaa001f043434180fa0d92659852200003d2db895307cfb5a2af388a8104a484c6d92e2cfc2b5c61bb5c0dd799ac00026343be178e00000006802faa0650000dd096ca6fd9672374ae62553128200002a83959260b17065888235a8658000076aafe625693ee2290ed03af0da0986b23aa5a1d96b2b00004930000a25b638688ae480000000d6631b400005b8c4a000000003e6844a7dc5f880000002706cd4b666190108c58fa5c6da536cc2fc06cadc1a8024021b8c6902e10a3883203bab522dec254e14bac2601819b691b9192a62b70463f8beac569e18b631d1811403b80c48ac2623abd82200d44000113828d1b40662024000028328048ade00000000001abc972a3bc88280000000000000028445700006370d380002b16000152a000276065f0000bf7000055b80009bd800000000008e1a07c79ab7980002a5400022e2ac989ba6770226bff16aa260068a22608783ea80006b19f2e000119856922c400029b40001bb8513aecc4cc98a413681e600015e20e7831e4ed91ee61580000001208a2d00000000932dfb20400001ba0967173e11d000000037b40fbaebe0002e6aa1400005da8000000000000002de0000000000000000000000000000000273262d06006dd1e4ac4602441a10ed4af700007e0196a0001a6a7f200000bd3744c188000a7737c0000340400024ec109800016d1206bb233667a81a2437d07580002450cf00000000000000027821c890884969d9c0000000b1f947e000000076f208cdfa8000dbc03dc405271ccb822e49f592009d712da707a8c8c7515aa3f0013c8012abaa5caae811fa80c59e9524c24a382ae7a960244abbc7c62ac81e902f609f0bc8664ae6c
  | 49 => 0x6c99800000000002cb2de4dbd0c168798010101a78e0000000b3f83d000013c4b311a6600000009f432500870000402a1c69f18aea767a29052fb6208fa17d85a519fa84a2eb496f0c30ceda30423000000802f4ed2097b80058c20b27a7e89e02be262d9100e0c065a749856e97110ae99823983bf8a3e9c6b5103e8890253a15863fa291c4169592c402ad06db946e0e60838880aec4ae68e622d88d76270a700c8f1d249fbb57cb3b2502bee11c266eaec02ce3126a76aaa48f19cae461296c00028d29bc9aa86be246a6ca0000926073a2d722502f133ac989258809900c664904c00071e9e0cc9b42357b1326a7af7207c9c049e8aa4cc35163c939a1e8ac6b2ee0002f2a03e00002489b046849eb6de8ae7675f8ceca292f26000000000030f800001425f6acb246380008a60000e11aa568e68000aa3800000000001600000000111200009f000037baa59088e1cb32c406f08d85d19d2aaa8800066500001be814ac212ea00000f2cb5b23780061de62cc2744c80a0fcda92ea4b9c80000000000ce331a200000001bf82385b8ad2a506032ec5096a8919ac6203a25985299cc663303c040b3478252803272c1db4373036a3208000000000082d11e40002f9e00020e616f2b68173822abf4800000000000000000d932ba09ba26e61cf2e8aa6c9b501b00000d3b87c612e89b2c6406fcbbb894c556b54019302547372a42d51b05817a80007fa1776ce7aab46fa372a733a2807718000d298000d5b1b5a0000da48d3800067780000000000759800015a14784928840d0c37be0de80000000000586900e91e800000000005e134f200000007ce80009c3b15c14cb1062d112ca5ea255816da72819a04fa00034f011595c8d970000cf49514754a43ac2d82d258e0e5067b128e93786d2cb52e0600010da575a3ce465196c2432c906acb6c4000000000027ec000000085a1e48ae58ffccc69974b0aa1628c5227e8b60000bbc90e6ae09aaa5f1374c0b508ecdbc8b1e8eeb46257ba134b1c0ca064e8000b7410d4c10ad6e497267e2f7b36a1c12f2200000003b00000ab526a64c00ff64298636962800083880009ed800000004360000000000000046cb67e2189b2033382120000d1c37e95d80df936e000327827b3140000232200021fe75da5f0a4b000000000001210000d6e22d0263a5d079514cac8e000013d8000ba9ae5800000000000000043b0982ad8b40a83883ad8b8000d200ee88a532da6070734835ad1c154931822493464f680ea0000d860001b5e7fc30c8d3e203a2d603cab03000039bb4666db3552d242826c3d11ae00000007120b006248bf4656a33e000000058a33b0189b4de89b800005980000000000a3d07cc0002e44e0e8c060002d3a172a0bc5ad986ccc10a3aa0114661fb048e0220c928d33700ce81712b58
  | 50 => 0xb11684b62f8a802897800018589e490f800024bca7c83d81732c6ac2a0cd87531b987e9800031c17cc00034c2bcdb6080002758000190816f80004472cb6703a87a8ed8c0ae01b1f64438e1cd7e29d83a18b8ec2c8f280cf877c4ef15da188068cccb1cd25c81d9254783762702a6c71586164eb07dc9d4300c47a2eac3492aa6729086a5c694ee654b66a6298082a6e2b8a0a484e049a0be8be9a9942e2095e000065418193d0d968000000000091e004e00000001c4800032b84b2000012c96433d8000133e00018400000cc66f0b1800bb0f1e000000000000008488000000000000000000000000000000015b0000000000045d26c44fb1fda0002a6e26833a689524d400017f200003340000000000000036e8000a6806b68dba082916a5747dd0000233b6d6000000000011a82c99e6c000345c0000e18029b7a600036562a598fa1e1152010409e68720000dafa2be785b1de2461d285348000d2c80000938000cb590a81ed94a81fe014c0001beaa4aa05abf78e685ee84d498731648638000a1a22c04aa993ea3a2b4427d031a9f88096b3808b63b2ab108810cb60000000264000000010dc2c280001209f4400035124f3000081a80000fd8000c31b4d25a98000ca5b1ee9dc2048dd1800001c2270a0000007eb000000030d60002710818000087e05ac000300200000000000000ce20000000187e00000004d88000725133415e2d18d04800087813967bf000000017ea3cb9f2245e9f90b7a3788b4c10fa3f0a79a479913e50f0f865c52f8e86c04a48aa9eaa5f418de33a1d8e1c5a52cab3b1d870491ba1ca9ac02a31f0e41380000001fc4a069d5a0fb02aad56b1f25d78000c21982c2748000148329e5e7b3440000c7e04c306edba9a1e92a061073008fa149a6dadbfb46e1ab13a83c58994bfc0e2045c9884a7b10e800003d60681ca800018ca0000baa0001c0a21130be000263842c00004bb01ba000214c40700007063064d0ba70cc6180000000e7e0000000d9c000016c80000000000beb0000000161c0000000000000019b2b4c71fa5ea0000000000000003c9c1c00029e67c504b81b12992d058000499a318086072806aa99e577a0e410f201e49500007640000aa62d3c2029a0a1000000000000000000004da0000ca08000000154aaa5800000015ca000339800000008be0000000000051d9e7e021007a798a97820f9b36ac7169ebb41448cfb90f6c37b672ade80000000e80220ae0819f8000000110cb0525de000000054b0000d30056a7b40000dc312f6071a16a73c053a9720fda6cc0af00728338ae9a1fc2b6af7ebb18000d7f80000001e0e6ba13ea1e7800070c855e39201380001bd2000159809d231e3450c88000212c3128000689800022f185a89f0024db037089428d167a395540e089b6dd2a53cd982e8
  | 51 => 0x9ad5c00009b400000608098a4c8432909800048eaff26d218126da36025ae279089808c4d6c1c788b3142e7a5221cd4201206640ba2a36062c09303b0969b54240c0a6c44c0a62542aa9ad330000000006ecd3b210d88b6f628f36cad990000000000000000000000000c6ba8ba000000000000003e280008f6219eb210d6a000170e000108a4f71c6c0000d5c85380000002a12d7aa13a00000006ff13d43bf00648b8144494a000073b9a1c37cb73a16ba04425d0c4c4d0266c52f3680000000000000000001fc0000000097f8000bc2b640a8ca504bf631d2000028894000007ca80000002f869bb800000036a600000000000988000053800002b2b2aa2288998000a1d00004c90000de59708131000000020700000000000000008500001e600000000cea97317fe946b1c07da0000c3a08706780000d579a28de0000078f800017f3350a6c2e341b3b3b46ae90bcc4a8a3277531226c9000019a966000012c620032acc1223e20002c429cbb50421d07ee708b76874836a89440da8ab72496641b52e1b3304c9cfa7da77eb096a6f19e61aa14f08cc9fe0bef096201024e478aa97e0002cf00b90f525699a4ebf90000b41a33623f1148645adb030a967802e1cea68c000049180006198000475ab3e99f0000bd0912e41a800080c80007be01ce00033fab9380e0c2f2ebc7978c8a99500005d6a2d25cc28de6e0264e4c9b4ac45b88eed951a8a4a514325db313eb208cd26f3884c4458dc60002a100000000000151684c80001b0830a780932a1720f2675021beb8f0f24ddc153600030ae53436ee8dd9e58d4e80004d6800026a9a8600023f40000d2a000133a70f8000c0414e0000000040900007d28000cb604440000000000292663c000000000009f31b920002d1400009ee000287e00000000000c74000000055a8caa0000000ce7307e48c800000013a60ea24a0000077aaea071e69e0530000179620d8000000000000001fa0000000690b298b7b93f060620d45288e04063b3cc00027645a21da635a161692b95b682c8a06055816eba52d4671d8a5666132ec6e9000000024742e58000344893663181ee3beac2854e34bad40b6e47d215f4daf00006e589661298000a380528b39a18a827b50a952973800180000000000000000000019f40000000000000000000000000000e0680000000000000191839d00000b31b6057108daca1a5ba022b05406580002e980000000ffe00016f2000323617c11700001ad80d680000000000040800005813780000000000344e617338a0002c125118d8218d19d6000002a9f78000000195c00000000000000c0f0f140000cc078b8eae00006460000b6a3d512ccbe1000094ca5f499980000001aae00019f8000089e95324420002218c2686563bd9cec476b2f60001da013fa1da6ff92a68e
  | 52 => 0x3898000c1a2b94d168e4c48d9e9241d06129ab30fc76ea5ec2ee00000001d1c02aaafe98580000c3b6dc000000058625eece0870cb54b3c24c1b26c86e175cba014225a6b78eafd858a52223540eb1ad609f8796b40ae9019eb678d41a0141942a64000000031a1552579000099c99f08271bc4926a5961748f44b52866e7ed1de014aa00e096881e37b805c69b29c2a278c96bdb9df817c8000e088000b9e95c641fb83421b000079431e24c58694af08a24d2b8000acb9b94b8a90ce00000004312c10a4136d20000000000143ecaa00006120000000268a7ab80005de8000df6ad12e0a8fec00010900312670b668000000000096131b8000000000000000002882000061e9ce97fad0399d8d79b0720e59df42419f001308a765108000373857e3c28f1874f0d36650085c00000000dc115a7e1ada6dc80fa8c1e3526000256a141138849100000670bf6903000068eb1240002586832b60455a16bec33a85eb6d1afe161197ea8b890805a9af64a300009a6322e33b80008572688761000000000221e38000000127a410b37a912b0a000032c2b13a77624a800000000000000000c6f9c380002f08647b2949c505b0a10190e0000000c5c9196cbc0cf4adab6128a9800036c31bcdab0000bfda26c00000003502e9a7590000c3882b8b0b80008748bfea2634a0c65b4aad8d22522e7a29631c88aa8d58ef00001838ce485a2ddb2b527b39c54b6b87820001a4400008f42dc2e7c5390f6c9d383740002f76a7c02eabd893c2abd8000cf78c34000356ad119ccc000355c7cd371c3a295ea4fd80000000f6a00e05d88cd33460000000997adde2a2000001107ca3b2000000000008f53752626346c9449a3e0fd187400014261fe9b54000000099080001e6b31681da28401e0000bf01edc0002ad8383afc8540aa14b1325ac2de80000002e6659fa78a46693c04200a7e3f888648482c340003218b6eb648c29299a000000016508149b88d220000000b0f00006af955ec529e8658c9f640002c94d6f36d0afd12ee490857423c8000000043a5bbab5000000006a426140d5a9c46eb015800030bab802a62a7eac72000000000007b88f5a058144a26a000372e05e2c8c19089a83528000a248000a27382eb1d8a9e2dd003a84ab7142f60d487a61ef6448054a7ba94f889610600839f961dd1144c80159c86e93826ef35b645e21a8c53129e99e23aa36b9df0a479cda7dc87205a1af0217803da10f86a00003594ba48000000068600027fcc1d2aee3e20e320002f9489c80268e41798ac3a83cca48930c90a5a8000000006b29843e7000000000000000d66000000000028240001438493800000035006000afc48f8000a92184c00000000002d82bcf8000d290000237b3ce60e9b34c169e3a82421423da000082580004eaa6
  | 53 => 0xd203008aacb978256adbb7f49df90949989f6247c83649d503a2aa101dc0000000ad926cc70eac7aacc9a729c63108d3100003e038120000000b7200003eb9cfeb7309008f8141a3f193140178000204354ca5b80005369afa000310231f126c294b1880551e2686035b2af20cd680b80e21a4af001eeb368552224c65599cc2381e528b691c05b187e63c70ed2a0d36b265305928fba198ace0000a7a879c000225c6fc977c0450000000000069eb644dfe0000801800000000001f4add48b50aa26a91f9e61e800000d94f478f34f6c7383585b329f459002e0aeb13224b202ce8c2099ed262e128e11926b1b2a1c73f00e6aae17664b018422060000da60f042f002580000000861200232faee88d6b3e6d25198a000000000035a02858b760001a4635f8000a7f1dda0003314ab780000001b6282289a232f20fa518800044eb6de00027c482bb794e02942a4629d0a4d8381e8739b52000286e7cc88cc01524920000072858377c5c4294c00037ee00000000000000b6e00000750000a6f80003620000d8c21bc912199c0cc17c03ecb7e82d525aee0f8000a44a232a13b5ee00022e6467a69c00006306ed219c3701cd662e1bd6032000081e905408232e800000008e396842ae09044b521e41121e74ad60fd6b91831600001e84d2000006d10b20000f928d796b485d8aaec5e2086069a018d9f000056d1b76b90000000031546fb0000ded88b07c717d6b739c9ac630000cae98f24d41ad200000d4809b7563c69152af0180200019d491a21ea380228814d00003419c526d188768ba0e7009b000000024b4a1280000000a128ba80000000f783e4000000007a800016da7c587a6c7e84040001cacd841e3830b0c605fd00000000000296884800000008b380007618000c23b6b853104d600000004c10e14d61180a56e0b3603b0b2239690c8d7634dcc221310cbd049e3cf2f703962de29d1ad84c69b11e74e044c66f088877a1eeec028d0a695053ebc580000002c36cc41db200005c44d30cf627e00008911b9e0760492000000047a8bdad3205da3790000b538b9c05d89686b236463a32c48c0c1b9a609b83c6360e92bd91c6a9c5a9d28cb8998861abd400020ec6cf0d34abe28b80000028c4d13c6d0431cc08117dc0000cf08f68e6ac52112c9f5000015eb4bca86a25e00000000002748b7c00000ca893c5cb907800000000001dd6cfa8000889000000000007ae000047da4522f58f2a00000004ab24ceda080000001d0017d00009b4958c4268d567bc930c05cb566bf18850770a3ca000258e0000ab259880007e8aece0000000000381656b13b8283000000031e4b8da75e814347c5581f2400000002c52be4c5b800077f000000000004ff1c300001df600000001868f628ff2d78dd213303769f8e81b98328ae8f8eb3236060
  | 54 => 0xae48d0200000004e614c25bf321c6a0800083780005c9b45000003c8aea800093800005b58bc200000006c4b0566ce8a0a00019a806d80006940000dd68d3e0000f4652d9076000223c00014720000000aaa0d80000038c5a897400000c7600004620000000000000079018dab8380007271e12000098a587a96a5d297f8aec0000d8e8000d66a5f800016b00000c44be220b81ea800000035cecbe94d8ace9e5c04a125640583b617880da0e28068871000093b855c9e9962ac3cac32954a44631b848a4079b4e8b2112675a1e4eb002ed8d029f54058ad5c29d00ac75b268416a9166a5d95ccafba0a27469adc660088a4db0000a9e000000028a80001a3cad58000a3b277a175a7ce7e2b5ac7de1328000000000020da38680004068000d0f0000000293c6ad9f1000022a0a1936ba35406800e49c5c790a7e00002c4000022c20000460000078aa048fe4d730000000317c6971e90c0907322a900005c0b3c6ad0309e99a9b720002f10add01166440bae9b629ca0002f2009ba80eb4384cc0a5800035627b0a0fa7a00000000ca82ef6cd900000000000132a6964331dd06a9841c85fa5820000000d030fea455a6ca9ebb10c32d0000d53a9ac151a02228e32ca53fad72bae07180f91d7c39f260e3e7a24e1aba8300000000238b3209b08000d5da9ccbd580002fb130a98329f8c46800000000004a8346aa8d05f6dc60000abe8000000000059701a4906a43000015907050000091a424428000000030fe82aabfca0e2e30c93182e1038c1283e000082f951cda70bfab3490dedbe000000022304528000000000000000007cb2df88be8000000000071180000248b02000307a000000052b00002e816ac7d6000058280000000000ae880000000000b8a0000000000000000000000d6c0000000b6480003cea8aad15b5de00000001f0a11a00000000000000489841a55fb62831ea15a31529a20000750000000040636180000ab4000000005f8000d7400000000000000000082ea46c000230e291882a000000000000000000000c44b78a7fb01b8000321a1b19ae20000000668139425421a4a24000000000002610000000256c979aaae6481b8e5e42d2200000000000000d122d04688356090fa8e62370bc612c0e2e5ce80000000a58b959542b68ae642eca85459b2d76595062a93cb696d5d0000c7f9d60ac8a2f0ae11f461418cb8970350c49c8730955965ac9897f000000009ae993416096c0000000000029de524a9a48909c36bbf9d9403383266e2ad94a54281e0000760000223e0000000957923c60900b200bb36c23da2b402309febb5ad8adf79c72c58afca7cc00000001006427b7fc0001bcc0000dd84f91a04000000000000000cf07da41c07de6b91d82d94a4dcd1806783ed00007b5099ac9690f2ba700004e000008ea0
  | 55 => 0x2770000884acf2bed84acaa795001658000745aa16000000000029526738bf2367a0f465380005b480000000dbeae335480000000dc29fbc617815cce69cf43f48d0c30fb6d8b55aa863bb00000000bba17191282f32f820000ae000000004008a2600008845f18000c64b556ce1352c047a33029000000a7153c9bf00000002350599af24ad1800067b800087d0000000000022510be0012088399a9d454b80000001b826968000000000048621ec0001bd84d49eba26f800086cb16874380001a6ab4a5f98ad891780005cc9ec2474b49ec0101440003032b28876c7b6243c103059a9b38000ae60000ae0357285597aa0001e561d283ce32881da485800000012d68ce30b8c30a4da53b000046800005e82bae5c10b3400011a4cec8000a1f0e846b126649dd28b2aee189600000000000000d6b800000016f600013560001cbcdcf0a1e01f010a79a1cde1929d8824400487230d0e9f601d28d0b15e04eaea2988279eab48cc842d8f6ea3a9572ab11ab004d1a5678204f43ae06b400013444f62c743632bc44960cbaa1688acd9d9134074046c90b970099d3332720342ccc7b7781318ad401291c66668d721d0235c153183ca130000000313c000069e03592c2000356800025f200000008778a507d3301e84c0000656000028b800010b800089d0000ac00adc7f3a20c87591bc8ed1f6664d97ce4c690343fca85c7bb16febab8572221824a3f7324865d88f0bc79d62179898c0c8ae961f917c84bea7c8de112f412fb34c4fe2e3ad2e0c4227423ae92085109c08c9ac881880b5696e4b67168a6c402f292c073e9fe80009322bf03f98a8e3ac1a5e1ce2538bbb26fe313ac78773adcad232bb2de48764a51800022e98c2d720d60ab5800072980be0002ac20002a4a00002dcc7238006a21b060000c2437d8000d21af548deb3a8ad83034bd7103e7289e8a2920000000268600004eca1b3514ab9a6c820b0d1a00030dade68a8000d00009de00006f2132c5319ec8a5f15788880abe20c17246b987bc1b92bfa1683532a0623be96f800002187ae8a380002e035e400037288473028da893a06efa4fcabf35fa7ddb7f096801fe95d8d3ab6786f24ba84d8d0ea2b0134ad6622c8192000335a0001f1addb92647c334426f7074294637e455418ee9591de4a2306aadc5b586ba30778ca10230a0b8106e10155c00000007fe00003dda4940002d445d89c0000028ce732845ea1aac4a70bb5d4bbc00000a3375c3bc98862ec0710098000064c800040a80007ef8000d1298e04da8000d0197528440000cac80003dc800087400000000000ae70736d238f307df2ae25e22940000000040112e4a370f60000000000000002d980005f08000ac52cae550000002c00000000a8a079093a000000000034a2da3800000033d40002d16d359cc4
  | 56 => 0xa4836e69cf22fe17087be56111d0d8b1376d1fa8ac272358a9cc22920001d48dba15a05488000bfd000028a368a88a8000d1c80000000f6448c09b4ac6037ca05a77225000006188db400006529c492dc981000098a21ae0002530b0e9c4438180007192fa01b82d2c00000003f8000018ba066326374ec4bb1f8dcd8000473affe45927ac5e7308ccbe1ec45dc24ea6a6b4b6b98147084f2cd65b22adac7a2344904290660d9e8852a80cc4420dbc23937629159f56df8130876684f090b2cf68f4b324c539ff2d3a2a44a96233a000252e1d79be07b806d40001d9823e30088e511c423f9f2004c80e454ca5b84d90000a4a000002e800084000000002836b1b800002810323201db839e10aa00014c0b22988800005160001c7c705a9e000000000001d08527a76cc070000ce5a3260d4250cd3d24e2000098655b174e9f0383870d00000cb1eb01b41a980779ffc4e78b986c38394c39916c05917740be8e347c7af96b018442c1a99a220480004123726490071a5b78af800022ca385b3022bc9a02a3f2f90aafa47274d948428602f8c5fb4ec3660e76163347a47b1eb462a0000ac2977e00000002020fd013c80006ed80000000000d7c030200037b8c110d080f8a7c22498b10aa51118d7f31768f70000a3404720002d422f480000000928000000008b0e424c720a069da10a915000000008c64f58000000000000000005a32d38000149a000000000021ca336ae9885b8aa029788c2c06b394de80eb2000150c3f11b2e0002a4095c000014f240447300006f400000002b282cb8ec251a1ff654187905ef0000d5f841800024ca287177246f8fbc0000000000224aab819c400013e60002324870a9445148f58af6a4880e12e88c9a0d420002de66928000b330000a9380120000e943a8800000019fc0002d90abc90ba0000fd4671ab785ed8824591b41c5558e980000f820000b0c000000000000000001b1ad0e0000000165ea23a5fa0002cfa94db49600006ec725941c8268000ad0a78c0002e3200018e800012f84e3b7f6cd88000bac24c432c82a4d1a04e645ab774af80000411b8268c08d7000025f676b280696db5a60002762700a644cb931949c2b0a6cc2960c1b5a37499210a200005c0724ab480808000309941262324a6000131ed9b00005d60b0683d8db8c62adc052d21fa2e11498aed83aa82a222c1a5839c56bac389ea26dc7352f8c1da8948bceaca04698b92d0c8de8af2ac9a1e2000033f1bf00c18ed8cea922045380005f78000734342000000004c49456041168ecf81ff4000085a6021d144879d3e956851c60680003532a309cdb692d7a000024e1e9a6518b3cb4434e00000c50cd600002c60b040000000c51000000000007188f2256293b08311b901ba0000beb86646ad1e1c0002534aaca14a000235205b
  | 57 => 0xaa402b3797181ec2788dcc9336678a3f861d9b840db89567910ac029524f80b598ea3a802e6d1326bc3a58468a32819e449272a44d92a847e080c8ec34146241e9c63b065c8b790980008000738327e000000000023f2df19fa4b2700007199c6056c1a8c36a8dc83f6156491d9674c273492015aa0a34128d6a0a33e40bfb1b23de9e1440f239c000085695f8972e0a0ce4b92800097a3422994205ec542656a351a7caac1238218228a000325c20a02be447b090d0a185042e047cb76075a9bea51cdb3b2e20001ae09a38000c9b80000000000228000059b8000ba111b8ce38b5279e18f64a60f40188960e6fb953e0002edeb7180000001f824941d801fa2360787ac026c031308d90ee63a914ce2ed2f063f79a600001ffe0002c1ebcd000000033183a6922a00007c80002140c3b01c883233720000000000000000000005679d8cb6f8000c89938a0000afa778800000037d800000008510ae23e3140a9651864bc72efc00006bad151a8459da44c1c080307d7b4e28a7b5aa7ec0c62288b58c25ab516dc92e4c113a796089222e46d9ffa64513fa4a68bf8bd0169600027268c4000068380a27130000a3c80008498c4076c0c0e00016900000000000000000017ee6399e2468db6744ae9af081324fe2571fb80d299721201eded3f1ee41acaf5229c8000b86145c01426023a41942d11236800018be6eb8cde4cb86a4b480000448ab069ce37766c600000000000c669b56cd5af800001d74a6ba0f0ce000008da8000c4580003e920340001830c7180007f2937e408190a891a4fa7f8807e48086a210829e20e00666501333a5bb1e5aadc1da2de1b43ec30044a000000083f9ea8a16077ea1e2f4840e94fa0a0303800010c0000000000018280d090667bf800046303ea94903de1be082000031566e8b24447fa640a4faaf421ca92eaab1292cb384549189056d0a80008a685a4b26000000014000001650968ae22379a6f08750f068fc24d053a8c00605b43437f30c46c50000be90000739027070b2a8a319800013b9dc000033f295f2a501670000082a27893d0e229fe07c0c6aa74cbe699447408000369a8bca6a20a499d86dc13f0e9c0002fa800011aa4560e0a8212158bb90000c5e80000000aee00024320000186000228c69b840221b8000000234a000099200000000000c1c3b3800064e00005160000000261e9b78d84d4d80008bc80000000cfe51d09a40000000bf8201a330800075601e0b9b8000bf68000000082e00032562ca80005b708d07578868c75af2e0db04666389c061eb000000036ec1740000000087e0000000000372c000384854400000001384ae1800000000006e1a6f453d9b1c00010fc00000000001528ccd00003c4a4f6744a05c996379c00000009238662a48b7645d2275292c8d305c7276e833a02
  | 58 => 0xdf40ddc8dc0000000201000000007bd15be00000000069f5c49f0000614800000009440000000000074830400003a21d6abecac0e60d1234dc3aed44d999ae685a5628f080000002cd4692000083437fa62f10c200016d886231a46f88000cdd8540cc000009b5000081b00003010d6e00034e6c1182aca3b9ee2744320602f31982a4ad2ea40021a80f197a9afb84419f366eb8e290c308800081e14805960e1e2a0a1f6cdc30160020b6ed362e0a000000000011864870324984290897621085fa145e000089094519c8bfa93f2455087a098917c0fe8b1adce097a00002c2255022800030b000030eea888458239800000000006521450000119c2aa800000000003031e4600032b6b0900000001cc80002c0a00000001f3aa3e00023206139ef00000000000000000000000000000a8b02c46a4ace800032de17b9feec839cbe0003686329a66e75598aad4a2358996b44034bac96000064e2e300007f7a58000030eabf1115000000002a18000167a56056a1e768ae18c8c7980008e22cc200000001c2035cc67b288498b3ec6a720c0cce06487b28e5e00009fac0635ca928ab30000268064b250eaf40dc4b5e95d018610d23c39cd8026b60e30ea6ae2bfaa5e0002f2c2aa00003fd0000b06075241f094e4890e1011719d0b6d996266d0000000000009d828e6ab0000c340ede0001bba39b06144f7850285b2daa8d8b2be0521210b7a91b493c224881380000000000000262225bab76000304eaa302c8994909600010acdf280009ef8000a082d8027f182a71410440001e9689a17609d5abf226b8ac48c3223441702866fe00fa000001ed34323e486a3a0a459aeeccbab0c39812bc327006ab478000c1734e41dc1214a97165278a0000b15aea88732c645b98c56b89196403418545ae9fccd2c23ea43f872e60516bc297184451e964455105e400000000000e72116942053729565e0ae161872056cde0000d899d6e30200007410000d941188abaa84681d012200035f4c4d80000c534fa3df158800002f0a9fa98085508b815899b0593800046400001ae0dd079c0c94bd180005efae20d600a9800015f66830000bef8062d32b3a20000c3298a890e00006f697903c2d091cf20000000d2700000002c3e0000000a508c5c13e000079f1f40458b10e5812acc15c1f0438e000014792b264c09f6cbfb77299735e085200000000aa6b711c984162b2400027666088b5a41eb20a0000000000220041b80000001900cfd371eb3e25222f70a7cb1f2fd49baa34878d27ea1f500000a60000cee9634e0500006deb5bacd021063b89dea0002c8e840ae020000588966989c0002a040ae80000001e4c00000001a9b360a609d422009b0a392869cd438ba4b2205ec970b1147df88321dc92122d801987b02b3c0e4237cc981acecc8850abd
  | 59 => 0x52800000015fc81c90e4005130e4a0000096c1dec2c700000000000bc3000003d14ba8c2888c67d87920000000000029ed8f980c0af28f08df8000a8e80008d1a2d6bed1f6c000299612a2c5ec5b26a20002c1a1d73614d0095e61829a1031b04bcb02017009c9a8ebae83ba10e34647c0800063536588ee37ae712a95e27aae702f5213e4deab7c08b991a31e0f501f102a60001454000164c0001eb2000127088d80000002d40ad79b3e11eaa260000fb6290980427114b0c5d07ea2f8020c5f481be8308378b4d85fe31a9f884689b706ba92fe97529880000a4458b21044ecb1600000b8a54d16ce046a7e6b9528cc24936dac1b092ccb20000626b184ccd9eac00000000001e2cb7f181000000007a900001820000774b78200030dc4d5000010d00000000916299000033300000000046bbd034094a800000020d88af1d300000000cbf000068622222b9b0cc000000000000000d30000c9600000000000bba8da200000008e7ad345a000009c880000002e4200030267c991f4730a1e20002d8885410f05f5231c6ca8e5c1a08766404ab6c1c9b77e72c91400ab8b488c006f400023664a2813e4f20180d9ea2a42f38804d891f7a8968e821810cf2000320810909587b487b4945910a3210a9c00006eacee0e12df4b08224fb4d400033d67812d7c1392aa033e0300a740e4000000008f9b72200000006d900003781bdea8033d03bd0000b7d92901b9815a9ff800000014309360000b16b820a7580001f58000000000061a9d3482c2810066812e2c496140001caa63580005638000866a5ce0000000a890cdc00026aa7faad0c0000d2c00026d6000154600000003193712000000000000000000ee4ad88f420001b1e4ff8ed6d65999614226a037f8000a5c2a06d4f80000000b7ed76904a34a12b651f00b6cd735540001ad0c8a00003d59d061d1800010ab23400011de02a0d62518163a0000554000000000300000000386644ae740f8066029aa08e37e2bfe2800eb6885000058b8000000000084317360002dfea02800016391d85ec06be000025c35e813600000008a092de285128897f0000c038d7442712b012183882b22ff842088d41d10b56c3d800035f0000e0ca690989b0fa53f197868e10eebb82b5aae90b8673eb6d440400003218000102b6ae000293a0000acc727870a70200008ca90c6b5204a0c1780004eb80009ed2328b2a0c2e8ab0feec3900000000b729ad8f200000000000000082500000001be46118000a44000000003fe0001fdc000295c138990c4418d78a718a020000000000279cda200000001f922732dfa9498000d3f922200004ea13a000000000009482a8800028602f41be687b8000bd1000091126e0180a486d8f134aa700826b3d0000b2f0000581a6e400015802cfb2326d9927e5bd000000000
  | 60 => 0x58abb00c095a2ce210880200d3800000005a65fb2708000262c1c705182b58674cba800048b9f70c9e800000000000000000000000000000000000000000000000037f2818800008823160000000802359c2a68000afb02369478e52c939a2ea949e1a1521296247070e5be9594ddab3ae1bc07e2c128bca409815e2791d2ebe72544dea80ca7eaadec5092e1a7081582824a506908000000009da41c80009cd21aa0000f4cb4f800000019a40270496dbe80000000000000000079cb3f6000164a6551c686ea863e64f2df420f0c289171c42acd8000000031000000000001806ce42fa24b3976ebb9951800030a238fa9b600000006dab75000031c40001aca8e2a7980440e542328346000106c0000000da7800000001f600031200000000699090a06b88d6366b7a8c4b0000544b5d227893ced1d80009058000afa28fa0000000bcc0000000133cbb08de2ac48446d69210e96c8c3c6b5240e6a5241c42919e80002c44000000014d992e000122800023b22ac0632e021eda07b00000000d960000000803359024d00000001e6e6df0ae8d830000bb6a080260b562deb099ce0136a000025485c180004149b08000008ebca25420b180002ce800063e36b40000000000000000026b40000000cad151a00000000628000000322a05426820000000d63800000008ae5c58000bb49e66d2a3818b4a096c56e8bbc00030520001ecc0000ca80000000ca6aac684d9dcab370e7a0001e0000000000001d320001d70c362b20b149e7a000000082983f800031a02b4867690a994a6d132d29162016dad849a7d69a8067a99ca3ae98b090e04aecd78ba8292823a24bb82411c144050183a67a300eebdeb0003b10e4619784d066c92e600022ae2779d5486daa3830510b45ec9fe4497b3c4a9e8ac67e31dbeb30295aa8da182c19800080d86e203f02b478d92768e31d0c79837bcd46810028c00000000ce6a4c2ab68bb0ec616e800000028f6c9d9320451b5b40d8138c7f0800051297a43b300000000000bc12436cf298d207129a669fb2806f1809ebc48754003adac275022272815ced872fbaa998416b058f0c65a14c8c7c0abc0002068b3416e092ea55cccc35247a094e2640b78c0998372c6090d67e800005eb80007e6238038c27f2cf6b2a22d08b9a59234b4864800029e9f842db035eda432a641406ee25913380000000ac79c846d730caafe03d469a0bee17535c4a22b1c2399000002b80000000a0e88402fc6d280006850000a8232f2de429e8589113ca14acce9b1a7f4cfa303e09a076e5031d4acdd142c52717343ec320400020ee8a880005a81c8ea8f2e0c000031c0002bde6ae2264ab2a64a1539f0a1b7a8c2caf0d1057e25085e4b6c80003104000115e000000000012ae000000000000d20000000d1780004d724cc8e983f2a
  | 61 => 0x27f000010380a5000028100000001c26c0a905e00020ac000000020580008d000008cb0000c560000dbf32402cc8000c1f00008ad80005b12ac00462f66000000062b00009a5000000025dc6cb12741b6b13ab9714a0b2023fe000000000000000000780905162000016b2b3b8000a070000d7d9c7a89e800057eb37c00031523fe05e8c0d8000969361600000009b004947571768a9d270452b8c90d78800091804de438068e3ab323032901f43aa89e091f87a22d795d266380000000dea2981b3878436006c0a924214a19616187f6cd228c0bf8b014000078cd92b59e9da00000000000000366280c0000a0a920e86800000bbb73e30684c812231ac53cb29c6c9800076280000003488cd095e0000000022980000001a5800024183569dcc000213875e099649b978a1451af2ae39e228599e802de0fca5908000ba3957a00000000002fd618e96029bb0440a6a95e8d14a20ed5b800008d159a000326a0001bb200021d8246a44066e00000000000d4d2e14000000000036e045f800000000000ceb7e2150a8c466f8000df9800095e182040005de0001ce65f29f9c0c200005ca800000028a071b80000001c0ccd2a9c800000008dc8000000000076d970a0000e2c000000000008e81e82f4a000120c0000000bf09bfa000000000000007f480000000b823dd004c0549cb49cb1b580002a5a9d6800000031ecae403520002f7c0002856af4a422b4935d60ac310aa8a9e0a62831dc0d9b408d52803c225b4da0b2ac581f61998000000000025e00000f02df3a990991a1dcccf0b4c00030e09748000d7c8188000172c89d8f00af988d2c10258c0000b68c34ac66cfe0d18521a866a7383f00e911b068a943a26e20eab49a7204530e2a3178a2092a9b7869327868898b4e0c314e686337342761f423230a70db19f063f38f3e44512f2bde22a8a6320541da23ecb75881aa7da0b61ec95c09fdab4ecb01bdaae20c481261daea520762d772d70af33254b2c0e0c3e5b0509021a70b5fa3c4c7f0bbe36b21a20001c5a41317fc1dd805285d362a0000d4eaf591c8b291fd6bf3358855c06bc9e9303a5e312a2dd503b4408b328bfe8e3a60f800084b80000000000107b2cc22f94360490000c8580000002a769550216d339da400000006cc9494b1502502c58c1e0ba0b4a1fd2f5e09e00003e814dea2500007c48846d5408224e1ab7e9ee369a000351c000249e12a9ce800004787488000c0b0a909be104026c34c6ad51aa01590bacd5e1c70d8d99aa475308059a84dc95b812a87c00001c526b8a36b2b851900007518524d8c817c0002876dcc2e820002cc67c220980001ea2a42847620d13ba52900005898d520000174000000043892b80001c2a000000058daeb6aa498b2da10000a121f50000035400028f8913aa900002e04ac08
  | 62 => 0x1acc80000000002ddc8fdaa70000000061c9508bc50000000000098600004dd0d94daaa7bca598000000000061e0f5e7f52636bcf351e00000000002d86c6a0000b2e80000000000b3695fe48b00000002d683e634bed560db2b7080000001fa867f90360000b94bfa189eca914d42ca030472e0af610c11e0b54349ad1c2c92cabb28e3f32aaa03619da00000000002da40b8800000005a8d9a1d1e0002edc15da312bdb20c67cf1bc0000000a000000000000003f200004d627940da000000030aad719b22d90af5a7a980b49c9211e0001fc6753a4be0000a080000f48954003ec2b348a00000005a9089aca4000000013e095e869000035200000000a7f8000000000056f21521b20000bc60cb0000332a982267ab4c8000cb407fe5c30a849648df03670cd496aa1c05168858ce18000aeeb27038a26a8cc70dd601db79e000141600031ba8f7b070c9293b4b7c95c22139d2c924156605380de0001fae8bb82b6927268c0002fec06c0b467161a34d649fb6c5a80009a90550decacca000150400037d40290000a7b80000002ce4cc98318b53000025495749679ebe0f101ea00000008a71dc40a800004b49aecdb080008900fba0001c8a5cf2c688bf0000421000000026120000000269972200000009d0800000004b400016d00002b043cdb60ac1804a20702d622c3940200032c685f1ac237b2d7477601d618a201c98e928600021acc1d8c467540d46b4296f003d987018313a25e6800000015f000000000002bc6cffa206000009028aa62e507b08a0000000cc314b8000328c68680004508000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9c83591424400d55904b22848800e1f21676109100043fc2aec212200387c855d8424402517908bb0848800237e0d76109100146e41aec21220068ec825d842440010f90cba884880021fe1f65109100043ec3eca21220008bd87d9042440031e90cb88848801b39189711091003c7c432e0212200387c859da32440010ff0abb4648800e1f215768c9100043e432eb192200087f87d9632440010fb0fb2c64880030fd96748c9100061e32ce9192203fc9c639d2324400187ecaba464880030f195748c9100064f3a6c719220018f4865c6324400f1f10cb84648800e1fa17764c9100043ec2eec992200087f855d932440070f90abb264880022fe11764c9100945e422ec99220008df835d932440011df04bb2648804a2fa10764c9100045ec20ec99220068dc8758d324400153908b1a648801ab3209634c91000c5fc3ac920a202da9c8359241440b555904b248288003171cf65505100064e39ec8a0a20008be871914144001938e6322828800317d9773505100062e32ee6a0a20008bf87590414404b53906b208288166ab209641051000c6fc3ac718a2000a9c8458e31440b159904b1c62880030fd97744c5100061e32ee898a2000c3f651d13144001878ca3a262880972718c744c5100064e3a6c698a205187c865d721440a10ff0fb2e42880021f61f65c85100053a432a510a2006e666254a21440018b8e7b2a42880030fd9774485100061e32ee890a2000c3f651d12144001878ca3a242881672b18874485100062fb2ee690a2000c5c65dcd2144001958e9b124288003331cf624851000c7d436e090a2000c7865dc121440a18e8edb2a428816b2d1db74485102ce5a3b0e890a2058cd476dcd21441159a8ec39a4288003651d0734851000733b28c490a2000bc58318921440014e90ca92428801b1d1d9524851003732312a490a2000ae4864c9214402d0f90cba842880021fe1f650851002c3ec3eca10a2000c5e73d9421440a18f4e1b2842880030fd9674085100061e32ce810a2000c3f655d02144001878caba0428800317d9573085100062e32ae610a2000c7876d9530440017a102a1a60880029e219524c11020e3c3b2a4982204dada868c53044001bc6e510a6088003f04c9214c1100063c328ec9022000c7876d95204400f1f10cb9a4088002da61462481100053c432a49022006c78765492044001cd70ca924088002daa195248110005b4432a49022000e6886549204400dcd6eca92408801b9a1d95248110007b140aa49022000f61815492044081cd6c2a924088103d8d855248110007b0a96e29022000f61521c5204400f9e0ed10a4088003d854a214811000d78432429022006cf076485204400ddc0c490a4088003d854921481102863d3b6cb8822007de2215cb10440014f10ca96208801b1e9d952c4110
  | 1 => 0x904b2286880063da1b7150d1000536c16ebb122000a6d821d762440010ff0aba6c48800e1f21574d89100046fc1ae9b1220028dc835d362440010ff0ab9ec48800e1f21573d89100045fc22e7b1220128bc845cf624400155d09996c48800e1fa1b75589100043f43ecab122000c5c73d9562440010fd0e32ac488003171cc65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100062fb2ee6b122000c5c65dcd62440070fd0fbaac4880022fe1175589100945e422eab1220008df835d562440051b906baac4880023ee0175589100043f438eab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100061fba6a4b122000c3c74d4962440018bee7a92c48823f171cf52589100063c3aee0b12200587d87d9462440018bce7b28c4880029b60b65189100062f398ca3122000a6d8219462440a38eae2328c4880030fd9674189100061e32ce83122000c3f655d06244001878caba0c48800317d9573189100062e32ae631220008ef87588624400155908b10c488002b320d62189100043f434eca922000a6d829d952440010fb053b2a4880031b60a765491000637904eca922000c6d209d9524400147f08bb2a4880028f21176549100052fc1aeca922041a5c835d952440014df04bb2a4880029ee0176549100063ac08eca922000c7a301d952440018de403b2a4880031e880765491000636900eca922000c78101d952440010fd0f322a4880021f61e64549100043fc3ac8a92200087c8759152440014bf06b22a4881069720d645491000537c12c8a922006a6c82591524400d4dd04322a4880029b60864549100043fc3ac6a92200087c8758d524400147f08b1aa4880028f211635491000537c12c6a922006a6c8258d52440070f90fb12a4880021fe1d625491001c3e43ac4a922000a3f84589524400147908b12a48800297e0d625491020d2e41ac4a922000c74769c552440956cb0538aa4881029d2197154910265b3c12e2a9220068be849db42440010ff0abb6848800e1f21576d09101fd4e41ac9a122006aac8259342440070f90b3b484880021fe15769091001c3e42aed212200087c865d642440010ff0fb2c84880021f61f65909100062f39ecb2122000c9e73d92424400193ce6324848800317d9573909100062e32ae721220018f4865c6424400f1f10cb84848800e1fa1776509100043ec2eeca12200087f855d942440070f90abb284880022fe1176509100046fc1aeca1220028dc835d942440011df04bb284880022fa1e64509100345e43ac8a122039
  | 2 => 0x63d95102853d406e9b2a2000a7980dd3654400187ae83a6ca880028fa1073d95100051ec20e7b2a2000c5d731cf65440a14f50039eca880029e60073d95100051f420e5b2a2000a3d841cb65440014bd06396ca880029760c72d95102653b408e5b2a2050a75811cb65440a14f500396ca880029e60072d95100051f42665b2a2000a3d84ccb65440010fd0e196ca880021f61c32d95100043f43863b2a200587d870c7654400147d0818eca880028f61031d95100053741063b2a2000a6d820c765440a14f50018eca8801e3e60375d91100043fc12eb322200387f87d4a64440010fb0fa94c8880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c6f65dc964440018d8cbb92c8880031bd94725911000636328e4b22200387e87dd564440010fb05baac88800237e0d75591100146e41aeab2220008ef825d5644400d1d904baac8880021fa1c75591100146f43ee6b222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd64440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440018df0bb92c8880031b217725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b22200087e87d4964440070f90fa92c88800317dcf525911047e2e39ea4b222000c6f72d49644400d8d8e5a92c8880022fe1d64191100054e41ac83222000aac82590644400117f08b96c68804a2f21172d8d100043f43ecab1a200087e87195634400187ecbba2c6880030f1977458d100061fb28e8b1a2000c3c651d16344001938c63a2c6880031bd977258d100063632ee4b1a2000c6f651c963440018d8ca392c6880033318c7258d1001c3f43eeab1a200087d82dd5634400117f08baac68804a2f2117558d1000477c12eab1a20068ec825d563440010fd0e3aac68804a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064f990e8b1a2000c9c311d16344001938e9b9ac68801a3ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637c2ee4b1a2000c6c85dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d1001c3e43ea4b1a2000c3f74d496344001878e9a92c6880031bdcb5258d1003636396a4b1a20028be849db43440010ff0abb6868800e1f21576d0d100045fc3ac9a1a2002a9c8359343440bd55904b26868800e1fa177650d100043ec2eeca1a200087f855d943440070f90abb286880022fe117650d100046fc1aeca1a20008ef825d9434400d1d904bb286880022fa1e6450d100145e43ac8a1a2002a9c8359143440bb55
  | 3 => 0x8a924000b6b805d152480816d100ba2a4900db1b1d8745492000717b24c8a92400096f8759152480172d90eb22a4900038b590645492019e363b6e6a924000a6f865cd52480814d90cb9aa4900c71b1d97354920005b5c02e6a924040b68805cd524815dc9cc7b1aa4902bb9318d63549200053743686a924000a6d86d0d52480816d101b8aa4901029ba1a715492000536c34e2a924017c6c769c552480816d50138aa490002da602715492000537c32e2a924040a6c865c5524800165f08b8aa490002cb2117154920005a7c1ae2a924056b4c835c552480016d700b8aa490102da20171549200b6363b0e2a924040b6a801c552480016d30038aa490102daa1f7054920206b543ee0a924006b6a86dc1524800d6d10db82a4901035a9db7054920206b43b6e0a924000b6981dc152480818dceca9684900038bd9152d0920206b5382a5a124000d69525c342480818d8eca9284900038b1915250920006b4a96e0a124040c6c765493248083c98c6a9264900035a54b704c92000732a96c330a400b96c875496148001a5ee8a92c2900034b1d15258520006a7b9aa4b0a4056d4c7354961480011ef0eb08c2900039954961185200363cb86a430a4040d6a7054a4148001ad2a4b84829000a37a0e76505200046ec1ceca0a4000c6f7654941480018d8eca92829000353dcd52505202b6a639aa4a0a400087f855d841480070f90abb082900063b2197210520006373b2a420a4000c6d765484148081ad4e0a90829004b2e1917010520006b4a92e020a400087f855da31480070f90abb462900022fe11768c5200945e422ed18a4040d6a7054a3148001ad2a4b84629004a2fa12764c5200045ec24ec98a4000c6f7654931480018d8eca9262900034bdd1524c520006963a2a498a4040c6e7654a2148081ad4e0a9442900039954b6188520006b4a92e110a4040c6c765492148001a5ee8a9242900034b1d15248520006a7b9aa490a4056d4c735492148001ccaa430a42900035a54b70485200043fc12ebb26200387f87d4b64c40010fb0fa96c98801e2f211759931003c5f43ea8b262000c3f75d5164c400f56d03aa2c9880063d2057650f1003c5e43ac8a1e2002a9c8359143c40070fd0bba2c5880021f6177458b100051f424eca962000a3d849d952c40014db053b2a5880031e1c27654b1000537c12eca96200087e87d9152c40010fb0fb22a5880029be096454b1003536412c8a962006a6e8219152c40014db04322a5880029be096354b1003536412c6a962040a75869c552c40018eeed38aa58814ed960a7154b10006b8384e2a962055b67825c552c40816e100b8aa58801e2f21d6450b1003c6e43ac699620078ec8758932c400d8eaeca94438801b999895288710006ca3a0e690e2006e646254921c400147d0831eca880028f61
  | 4 => 0x14c0019d6c4b8042980030fdd274597200053dc02e8b2e4040a78805d165c800147d0939acb900028f61273597200062fb9ce6b2e4040a7a809cd65c80014f30139acb900028fe1171597200051e422e2b2e4000a5f835c565c80014b906b8acb900029ee0171597202053c402e2b2e400087e870c565c80010fb0e18acb900028fa1031597200051ec2062b2e4006a6e820c565c80014db0418acb901029ea0031597200053cc0062b2e40068bc845ce64c80bb17b0f21cc99001a2fa1e43593202f45f43886b2640028bc845db43c800d1bf0eb1e879000a2f6137650f200047bc0aeca1e40078f4815d943c80014db0d3a2a5900029be197454b20005b5c02e8a964040b68805d152c80014df0cb9aa59001a9ba1b4354b2000536c3686a964000a6d869c552c80014df0cb8aa590002cbe117154b2000596422e2a964000b4f835c552c80b769906b8aa590002dae017154b20205b4402e2a9640008df835d261c80051b906ba4c3900022fe1173987200945e422e730e40008bf845d561c802517908baac39000237e0d75587200146e41aeab0e405ac3f52dd161c80b587aa5ba2c3901670fd4874587202ce1ea90e8b0e40028de87dcd61c800193ee9b9ac390003271d373587202c62fa96e6b0e4058c5d52dcd61c800193ee839ac390003271d073587202cc5fc3ac9a0e405a8bf845d941c80011bf06bb2839000a3720d76507200062e39acaa0e405a8be8799141c8001938e73228390003271cd64507200062f32ee6a0e4000c5d65dcd41c80018deeca92839001b1b1d95250720006a7b9aa4a0e405bd4c7354941c802517908bb0839001b1b9c9651072000636b2ae420e4006c6e7654841c80018daeca9083900022fe11768c7200945e422ed18e40008bf845d931c802517908bb2639016237e0d764c7200061f32ee898e4000c3d65dd131c800187cca3a263900030f594744c72012e4f318e898e4000c9c7458d31c80018deeca92639001b1b1d9524c72000697ba2a498e4000d2c7454931c800187aebaa6c890002ab60b54d912001c3f43eeab2240008bf845d564480011f700baac8900021fa1c75591200061e3aee8b22400087e87d4964480070f90fa92c8900031e1d770591200045fc3ac83224000a3c85590644802517908ba8c89000237e0d71191200146e41ae232240008bf845d5634802517908baac6900023de057558d2003c7a40aeab1a400087f855db43480070f90abb6869000a2f21176d0d200043fc2aeca1a400387c855d943480011ef02bb2869001e3d2057650d200145f43ec8a1a4002a9e83d9143480010ff0eb22a49000e1f21d645492020536c16c6a9240aee4f32d8d52480814dd0d3a2a4900029b61a74549201be363b4e8a924040b6a809d152480016d3013a2a4900029be19745492020536432e
  | 5 => 0x3171cf654854000c5f436e890a8000c3f65dd12150001878cbba242a00030fd9474485400061e328e890a8000c5f65dcd21500018b8cbb9a42a000e1f216760854003c5e424ec10a800087f855d821500070f90abb042a00021f21975085400043fc3eca10a800087d87d9421500018bce7b2842a01e71e9c365085400061fb2ce810a8000c3c659d021500031790cba042a00030fd9574085400061e32ae810a8000c5f655cc21500018b8cab9842a001b33189730854000656ba6c410a8000ccd73d8821500018f6cab8042a00031e195700854000675b12e010a8079c7a76d9740500f3c76c9b2e80a00029e21952d014014cdcc3c83a028000c3d75d53644c00153b07aa6c89800e1fa1f75591300043ec16eab2260008bf845d5644c0010fd0e3aac8980030f1d774591300043f43ea4b22600387c87d49644c00117f0eb20c8980028f21564191300945e422ea322604ec5d73d48644c0033b50038a869800a3e60375d89300043fc2ae9b12600387c855d3624c0010ff0ab8ec49800e1f21571d893000477c3ac43126000a6d829d9524c00147f08bb2a4980028f211765493000537c12eca926000a77815d9524c0014e902bb2a4980031e1c1765493003537416c8a926000a6d82d91524c00d4dd05322a4980029b60a64549300043fc3ac8a92600087c87591524c0814b90cb9aa4982bed3e097354930006ac382e6a926040a5c8650d524c0834f50db82a4980021fe1576d093001c3e42aeda1260018dc865cf424c00d1b9073b48498006372197390930014cfc3a872126000c9e7650e424c0031b90cb9884980fe67e1d43109300347c432e02126000d99435c0424c0031b90cba2649800275205744c9300346f43cc89926006ace82991324c00d59d0db12649801b171d9524c93003726312a4992600095d851c5324c00133b0838a649822b33188714c93000ced400e299260018dd83dd7614c09d8bae7a96c29822a37e1d32d85300047bc3ac230a608fc7970d48614c00d8dce4a90c2980031b5c9521853000c6e432e7a0a602599f8750f414c00f1f10cb84829800a3720c765053000c6f436e6a0a600299c8750d414c001938eca1a82980021fe15761053001c3e42aec20a60018dc865cc414c00f1f10cb80829804b2e191701053000c6f436e918a60008dd87992314c00133f08b946298103179d9528c5300246ec3ec318a60018dc865cf214c00d998ec99642980021fe15768853001c3e42aed10a60008bf845da214c02517908bb4429800637a1b73885302c666316e710a60078f8865c2214c02517d093b242980022f61276485300146e418ec90a60018de86dcd214c0053990e9924298003331d9324853003c6e41cec10a60018f8809d8214c0031b90cb98429801b33189730853000666b9ec410a60078f8865c02
  | 6 => 0x477c3ac4312800087e869d952500014db053b2a4a00031b60a765494000637904eca928000a3f845d952500014df04bb2a4a00029ee0176549400061ec20eca928000c3e401d95250001878803b2a4a00031e100765494000637900eca928000c6d201d9525000147d0d3a2a4a00030f1da745494039596c14e8a928040a3c865d15250001878ecba2a4a01d2cbe0974549402059c402e8a928006a6e82d8d52500014db05b1aa4a00030f1db435494000596c1686a928040a3c8650d5250001878eca1aa4a00fe2f21973d09400051e432a5a128006e2e6254b42500033750138e84a01ea1f21975909403cc3fc3ecb212800087d87d9642500018bce7b2c84a000317d9573909400062e32ae72128006ccc625ce425000199ae7b1484a00031e19770509403ce1e3b6caa128000e2f6518942500014790ca9284a001b0f1d9525094003716312a4a12803687c865d442500010ff0fb2884a00421f61f651094001c3e42ced19280068bc849da32500010ff0abb464a000e1f215768c94003476412ed192800087c865d632500010ff0fb2c64a00021f61f658c9400061fb2ce91928000c3c659d232500031790cba464a00030fd95748c9400061e32ae91928000cad74d8a32500070fd0bbb264a00021f617764c94000c5e432e899280009b4815d132500bdd18c5a1a64a000a3ba1f624c9403d61eba0cbb0a80018bd84dd7615000117b0fa1ec2a00962fe1d43d85402761eba6a5b0a80008bd87d0b61500b317f0ea16c2a02c30f5d0659854001c3f436eab0a800087e87d9561500018b8e7b2ac2a00021fa1c65585400062e398cab0a8000c5f65dcd61500018b8cbb9ac2a00031bd9772585400063632ee4b0a8000c6f651c961500018d8ca392c2a00023de1d611854003637392a430a8000c6d7254861500018f0cab8482a01e70f9db65905403ce9d386cb20a8000a3c8654a415008187ceca9482a01034e9c152905400071bb2ec320a80019bb875c241500018b8e7b2a82a000317d9773505400062e32ee6a0a8000d9840dcd415004b1790cb9882a01662f21972105400051e432a420a8000d2d7254841500010ff0abb462a000e1f215768c54000477c12ed18a80068ec825da315000317d0dba462a00066ea03748c54001c3f42eec98a800087d85dd93150025179083b262a00062fa1b744c5400061fb2ee898a8000c3c65dd1315000337501ba262a00030fd94744c5400061e328e898a800387c859db21500010ff0abb642a000e1f21576c85400043e432eb90a800087f87d9721500010fb0fb2e42a00062f21974c85400043fc2aed10a800387c855da21500011bf06bb442a000a3720d768854000c5f436e910a80019ba80dd221500070fd0bbb242a00021f61776485400146f41cec90a80008dd839d92150025179083b242a
  | 7 => 0x7b855d160084014f10aba2c01081aba20974580210056d418e8b004200ad9831d1600840d5d505aa2c010802ba60b54580210071daa4a8b004200a7a859cd60084014f30b39ac01081aba20973580210055d420e6b004200ab9841cd600840d5d505a9ac010802ba60b53580210072da9ca6b004200af38150d600840f5e102a1ac010802b6e0d41580210056c41a82b004200abb844c560084015710898ac01080a2f6137258f402ec5ec36e4a1e800387e85dc562d00010fb0bb8ac5a00028fa127654b4000536c14eca968000c78709d952d00014df04bb2a5a01028f61a7454b400061fbb4e8a968080b2d829d152d0001a70e13a2a5a00028fe197454b4041597c12e8a968040b38805d152d008147b0da1aa5a0002cb60b4354b400063cbb6e0a968006c3d7654b42d000dc5cc4a9685a00e6a7a0f7650b401cc5ec36e6a168006e2c6254942d000d17b08bb465a00062fa13764cb40004da40ae899680018bc845d561d00011bf06baac3a000a3720d75587400146f43ee6b0e8000c9c74dcd61d0001938e839ac3a00b62fa1f43587400164e39e86b0e80008bc8750d61d0005938e6a1ac3a013b0f1d352587400062fb9ea4b0e808fc5c73d4961d00018bee6a92c3a0107171cd525874000637b92a4b0e8006c6c7254961d00b517d0fa12c3a00ff271cf42587400045e43a84b0e8039c9c7350961d005b53906bb483a00b62fe1973907402d45fc32e520e80018bf8758641d005b53906b0c83a01030f5d9521074000696b92a420e8025a9c8358441d000317908bb463a00b62fe11764c74000c5e422ec98e80018bc845da21d00011bf06bb443a000a3720d76887402d45fc22ec90e80018bc845d921d00011bf06bb243a000a3720d764874003c5ec22ec10e8000a6e8298f65500014db0531ecaa01e28fa1073d95403cd1ec20e7b2a8000c5d731cf65500f34f50039ecaa00029e60073d95403a51f420e5b2a8079a3d841cb655000147d09996caa00028f61332d95400043f43865b2a800087d870cb65500dd47d09b8ecaa01e68f61371d95400043f43863b2a800087d870c7655000147d0818ecaa00028f61031d95400053741063b2a8000a6d820c765500f34f50018ecaa00029e60031d95400145e422e5b1a800087e87d9563500010fd0e32ac6a02cb0fdd06558d402f45e432e5a1a80019ba809c74350001c3887b2a86a01e70f1db6550d400070e31ecaa1a8000a6d82dd762500014db043aec4a00021fe1573d894001c3e42ae7b12800087f855c762500070f90ab8ec4a0003179cf65989400062f398cb3128000c5f655ce62500018b8cab9cc4a001b33189739894000666b9ec5312800087e87d9562500010fd0e32ac4a02c70fdd065589400843ec3eca3128000a6d82d9462500f587ae8328c4a00029b60865189400
  | 8 => 0x4284c81081eada0450990210055ac08a13204200a3e85cc2640840147b0b984c81084a2fa1c30990210045ec386132042128be87842640840153d07084c810802a760e109902103c5f43ea8b204200c3f75d51640840d55d05aa2c81080f0f9d6545902103c5e43aa8b2042078be8790d640840153d06202c810802a760c40590210061fbaceab204206aae829d5640840155b053aac81081ead205735902103557416a6b204200aad82d4d6408401c3ea729ac8108028fe1570590210051e42ae0b204206aac825c1640840153d06382c810802a760c70590210045f438a0b2042008bd87141640840153d06282c810802a760c505902103557410a0b204200aad82141640840f56d02282c810802ad60450590210051f42e60b204200a3d85cc1640840117d0e182c8108022f61c30590210045ec3c20b204200a9e83841640840153b07082c81081e37a1f5358c210062fbaea6b184206ace82d4d630840f1b90ea9ac61080e1fa177058c210043ec2ee0b184200c5f759d5630840d59d053aac610802b360a7558c2103d6a40ae8b184206ace82d51630840159b05aa2c61080387d525458c210052f42ee0b184200a5d85dc1630840d59904b82c610802a7a107058c210054ec20e0b1842008de8714163084011bb0e282c610802a7a105058c210054ec20a0b184206ace82141630840159b04282c61081eb5a045058c210056ac08a0b1842008de8710163084011bb0e202c61085637a1e1058c210046ec3c20b184200a9e84841630840153b09082c61081e37e1d63d0c2103c7a40aeca1842078bc87591430840f1b90eb1a86108032d5937150c210066ab1ee2a1842028dc83dd941084018b8e6b2a8210803271ce64504210064e39ac8a08422a8dd86dcd41084018bccbb9a82108031759773504210064f326e6a084200c9d64dcd41084019b4c1b9a821080237a1d63504210ac6e43ac6a084200c3e65dd1310840187acbba262108b72798f744c4210065d306e89884200c3e651d1310840187aca3a262108972798c744c4210065d300e898842008be8799131084251790f32262108022fa1d644c4210045e43ac89884200c9f7458d3108401938e8b1a62108032be13764842100656426ec9084200ccf83dd9210840199907bb2421081f39947764842100672a8eec9084200caf76dd1210840195eec3a2421080333ddb734842100667bb0e69084200ace8758d21084015990eb1a4210803a3dd16348421007463a2c69084207ccf7158d210840dd8ee2b1a421081fb1905634842100762b1a8290842078fa87d41600840f1f10ea82c0108029ea1730580210053cc2e60b004200aba841d56008401573083aac010802b6a0c75580210056cc18eab004206aea821d560084295d3043aac01081ebca0475580210a578c08eab004200a
  | 9 => 0x645492120d2e41ac8a924200a6f8259152484b547d0c322a490967c908464549212cf17410c8a924200e2d8219152484b387ee4322a4908038bdc864549212cf17190c8a924259e2c2119152484b3c5e40322a490a2a97a1b63549210070fb26c6a924200e1c64d8d52484b1e8843b1aa49096317dcb635492100727b96c6a924258e4f20d8d524840147f08b1aa4908028f211635492146537c12c6a924258a5e8618d5248401c3ec831aa490803871906354921457a2108c6a924212cb4649c742484018d8eca9284908038b19152509215472631aa4a124200cd463dc5424840196ec838a84908033518c7150921006b2a90e2a124200e8c63d923248401d18c6324649080ab3a1b638c921006673b6c71924241c6c765493248401c58c8a9264909079318d524c9210065a326e29924200cb4641c532484019aec638a649080359548714c921004f8c00e29924200cac76d913248401958ec3226490867331db634c921016663b686992428adc7731c532484017c30038a649080237e0d76505210146e41aeca0a4200c9c73d9141484b5958e5b228290803271cc64505214546f436e6a0a4200c9f64dcd4148401938c9b9a829080237a1f63505212c46e43ec6a0a428acce768ca31484b317d0dba262908b72718f744c5212d45f430e898a4225c9c631d1314844b17d0fb22629096a2f21f644c52116c5f438c898a42128bc87191314840193ee9b1a6290803271d3634c5212c666396c698a42079cc874c9314840f5990c9926290803631d1324c52103de240a6498a4200e2c6454a2148519c98c6a94429081b599c5528852103733b0aa510a4206c6c7254b604840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c7319160484b11b90db9ac09080327d9373581210064e326e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac0908030fdd274594210062fb9ce6b284200a3e841c1650840147b08382ca1080297a0c70594210052ec18e0b284206a6e821c1650842d4db04382ca1081e9da0470594210b53ac08e0b284200a5e8310165084014bb06202ca108021fa1f30594210043ec3e60b284200a3e840c1650840147b08182ca108028fa1210594210051ec2420b284200a5e8384165084014bb07082ca1081e2f21175990210961fbaea932042078bc845ce64084010ff0ab84c81080e1f215709902103c5e422e13204212c3f759d66408401c3ea729cc8108028fe1570990210051e42ae132042128be87142640840117b0e284c810802a7a0c50990210054ec18a13204206aae82142640840155b
  | 10 => 0x3224200abb80594644840157100b28c8908028fa1463191210051ec28c63224200a9e83980644840153b07300c89084b0fdd675191210070fa9ca63224259aae8214c644840155b04298c89084a2fa1f32191210045ec3e643224200a9f835c4644840153906b88c890966aba0b511912100556c16a232242128be870c4644840117b0e188c8908028fa1431191210051ec28623224259aae820c4644840157500188c890802ae60031191210051fc2ae03224200a3c855c0644842517d0e280c8908022f61c50191210054f418a03224200a9d8314064484b355d04280c890802ab60850191210055b408a03224200ab581140644840147d0b980c8908028f61730191212cd57416603224200aad82cc0644840156d03180c890802ad60630191210945f4386032242008bd870c0644840117b0f080c890802a7a0e10191210054ec1c203224200c5d75d4f63484071bf0ea9ec6908021fe1570d8d2101c3e42ae1b1a4200a9e84997634840153b0932ec690802a7e1165d8d210054e422cbb1a4200adb8059763484015b100b2ec690a2b179db52d8d210070fb26a5b1a4200e1c64d4b634840153d09306c690802a761260d8d210062eba8ebb1a4200e1f54953634840153f08b96c690802a721172d8d212c727296a5b1a4200e5751947634840153d09386c690802a761270d8d210052fc2ae1b1a4200a5c855c363484015ad02386c690962b560470d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d212c567410a1b1a4200acd8214363484015ad02286c690802b560450d8d210046f43881b1a42008dd8710363484011bb0f086c690802a7a1210d8d210054ec2421b1a4200c9c63dd16348401938c63a2c6908022fa1f6458d210045f438c8b1a42008bf845d5634842517908baac69080237e0d7558d210047dc02eab1a42018f8805d5634842517d0fba2c69080327dd37358d210064e3a6e6b1a4200c3f74d496348401878e9a92c6908032d1d37158d210046ec3cca31a4200a9e84994634840153b09328c690802b360a6518d210046fc3aca31a4200a9f84594634840153908b28c690802b6e016518d210056c402ca31a4200c9e76d906348401c3cebb20c690803875d76418d2100746b96c831a42008dd87990634840153d09320c69080237e1d6418d210054f430c831a4200c9e761906348401c3cea320c690803875d46418d2100746b90c831a42b3e97211906348567d2842320c69080387d935218d210070e326a431a4200a9e84980634840153b09300c69080a2f21176d0d210045fc22eca1a42008f7815d9434840517d0fb22869084a37a1f6350d212d79210ec8a92425ac3f72d915248401c5ee5b22a49096b8bc8364549212cd1f424c8a924241a5e8399152484014bb07322a49080297e0d
  | 11 => 0xc84018dacbb92839081b1b1c9654c7210061f32ee898e4200c3d65dd131c840187cca3a263908030f594744c72112e4f318e898e4200c9c7458d31c84018dacbb926390803631d1324c7210045fc22eab0642128bc845d560c84011bf06baac91080a3720d75592210146f43ee6b2442b4c9f741cd64884018bee7a92c910a3f171cf52592210043fc2ae0324420387c855c064884010ff0ab86c71080e1f21570d8e215a64e318e8b1c42008bf845d5638842517908baac71084a2fa1f7458e215a64fb98e8b1c4200c9f321d1638856993c623a2c710ad3270c47458e210061fba6a4b1c4200c3c74d49638840117f0eb26871080aa720d64d0e210045fc22eca1c42008df835d9438840117d0f322871081e2f21d6450e210154e41ac8a1c425ae2c42d9152884014bf06b22a5109069720d6454a212c726196c6a944200a3f8458d528840147908b1aa510ad793cc96354a212d45fc3ac9a14423fa9c835934288401c5ac8a9685108035954971d0a212cc5f43cc8a144239a9c83591428840153908b1a6510ad327d8c744c6215a64e318e898c420387e87dd560884010fd0e3aac1108029b60875582210043f43ea4b04425c87c87549608840187aebaa6c89080e2fe1d54d91210054f41881b224200a9d83103644840153d0732ec890802a760e65d91210054fc1acbb224200a9c83597644840157700b2ec890802ae20165d91210051f428c7b224200a3d8518f644840153d07306c890802a760e60d91210061eba8ebb224200a3e851cf644840147b0a39ec89096aaba0873d912100556c10e7b224200e1f5394f64484b5c5ca5a96c8908022fa1f32d91210045ec3e65b224200e3751947644840117d0e18ec8908022f61c31d91210051f42863b224200a3d850c764484b555d0418ec890802aea0031d91210055cc0063b224200a3e85dc3644840147b0bb86c890802a7a0e70d91210054ec1ce1b224200ab6811c364484b556b02386c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c89096aaba0850d912100556c10a1b224200ab681143644840156b02286c8908028fa1730d91210051ec2e61b2242008be870c3644840117b0e186c8908022f61e10d91210054f41c21b224200a9d83843644840193ce7b24c89080327d9173991210964e322e7322428fc5e73d4a64484018bae7a94c8908022fe1175591210046fc1aeab2242028dc835d564484011f700baac8908063e20175591210064fba6e6b224200c9f741cd64484018bee7a92c890a3f171cf52591210066a39ee2b2242008bf87590644840153f06b20c890802a720d64191210945e422ea322420087f855c064484070f90ab80c8908022f61e65191210054f41cca3224200a9d83994644840117f0eb28c890802a7e0d65191210054e41aca
  | 12 => 0x8029be09645493103536412c8a9262a0a3e86191524c57187ee4322a4988038bdc864549315bf0f990c8a9262b7e1c31191524c40d4dd0db12a4988038bd93625493100716326c4a926203a6e87d89524c4074d90fb12a4988029b603625493100717b20c4a926200e2c64189524c40187cebb2484988030f5d7649093116e4f39ec92126200c3e75192424c40187aea3248498897279cc64909310064e322e72126212c3c645d4424c40187cebb2084988030f5d764109310964e322e62126212cb4649c4424c40d1e90cb88849881a37a1e644c93112d4f424c89926225c9f72191324c44bd1ee4322649880387d48644c9315a64e388c89926200e8c64d89324c40d8b8eca92649880387191524c93103726312a49926200e9464dc5324c401d28c838a649884b2719173d053116e4e39ec8a0a6225c9c73191414c401938c9b9a82988aa3761e648c5315a54f424c918a6200e1f52192314c56993ce23246298ad3a59c4648c5310146e432e518a6200c9c645ca314c4b1998c4b94629880387191528c5312c726312a518a62008be87d91604c40187eebb22c0988030f1d764581310045f438c8b026200c3f75191604c401878ea322c0988032bd93725813100656326e4b026200caf641c9604c401958c8392c0988030fdd274597210053dc02e8b2e4200a78805d165c840147d0939acb908028f61273597210062fb9ce6b2e4206a6e829cd65c856d4db0539acb908029ea0273597210053cc04e6b2e4206a6e8290d65c84014db0521acb908028fe1171597210051e422e2b2e4200a5f835c565c84014b906b8acb90a2e9be0971597210053dc02e2b2e4200a78805c565c843f0fd0e18acb908021f61c31597210051f42062b2e4200a3d840c565c840d4dd0418acb908029b60831597210053d40062b2e4200a79800c565c840147f08b82cb908028f21170597210051f420e0b2e4200a3d841c165c84014bd06382cb908029760c705972103537410e0b2e421fa6d821c165c843f4ed02382cb908029d60470597210063cb80e0b2e4200a5e8310165c84014bb06202cb9081a9ba08405972100536c1080b2e420087e87cc165c84010fb0f982cb908028fa1030597210051ec2060b2e4206a6e820c165c84014db04182cb908028fa1210597210051ec2420b2e4200a5e8384165c84014bb07082cb9081a9ba0a105972100536c1420b2e42068bc845ce64c84bb17b0f21cc9908021fe15709932101c3e42ae132642008fb805d564c84031f100baac99081a2fa1e43593212f45f43886b26420387e85dc163c84010fb0bb82c79080a2f21176d0f210346fc3ac7a1e42028bd84dd943c84b317f0eb268390803171cd655072103636392caa0e425a8be8799141c8401938e73228390803271cd64507210062f32ee6a0e4200c5d65dcd41
  | 13 => 0x64eb14e91946258d1f529d2328c4b1a3aa53a46518a2b27986748ca311fecb30ce9194628a8df865c6328c45593aeda1e8318ad267a1f435063117e4fbb686a0c620387e87dd5608c4010fb05baac1188021fa1c75582310043f43ea4b04620387c87d49608c4010fd0ea92c1188021f21d52582310061ebaea9b2262038bf87553644c40153b06206c898802aba0a65d913100556c14cbb226200c3d751d7644c40147d0b396c8988028f61672d91310051f428e5b226200a3d851cb644c40153b06396c8988038dd4651d91310051f42ee1b226200a3d85dc3644c45b53d07386c898802a760e70d91310065db84e1b2262008be87143644c40117b0e286c8988b6a7a0c50d91310054ec18a1b226200aae82143644c40155b04286c898802ada0450d91310055ac08a1b2262008be87083644c40117b0e106c8988028fa1420d91310051ec2841b22622da9e83083644c40153b06106c898802ada0420d91310055ac0841b22622d8be87843644c40117b0f086c8988b6a7a0e10d91310054ec1c21b2262008bf845d5644c4011bf06baac89880317dcf52591310045fc3ac832262128bc845d4644c4010ff0ab80c89880e1f21570191310965c202e032262008bd87994644c40155d05328c898802ab60a65191310045fc3aca32262bcab581980644c42587eeb3a8c8988028fa1672191310051ec2ce43226200a9d839c8644c577c3e65a90c898aef870c7521913112d4f41ca43226200a9d83948644c44b53d06290c898802a760c521913112d4f41ea23226200a9d83d44644c40153f06a88c898896a720d51191310051fc2ae03226200a3c855c0644c425970e0b80c89884a2fa1c50191310045ec38a03226225a9e83140644c40153b06280c898802aba08501913100556c10a03226200ab681140644c40156b02280c89884a2fa1c20191310045ec38403226200a3e85080644c40147b0a100c898896a7a0c20191310054ec18403226200ab681080644c40156b02100c89884a2fa1e10191310045ec3c203226225a9e83840644c40153b07080c89880e3be1d52d89310043fc2ae1b12620387c855c3624c4014db0a106c498802b360c20d893100572c0841b126206c6c625d6624c4b193ec73a4c4988030f9d764989310061ebaec93126200c3e75192624c40187aea324c4988031b5d762989310045f43ec8b1262008be87191624c57596ee2322c4988030f9d764189310061ebaec83126200c3e75190624c40187aea320c4988023be1d62189310051f426eca926200a3d84dd9524c4014db053b2a4988028fe1176549310051e422eca926200a5f835d9524c4014df04bb2a4988029ee0176549312053c402eca9262b9c3f72d91524c401c5ee5b22a498a5a8fa12645493103537414c8a926200a6d82991524c4014bf06b22a498
  | 14 => 0xc635ce415056953d0db1c82a096a2f21972905410064e31ae520a825acac625ca4150541c38c6a9482a096b8b18952905410164e39a87b0282008de87d8d60504018beebb1ac0a0803171d763581410046f438c6b028200c5f7518d60504018b8ea31ac0a080333d8f72581410066631ee4b028200ccf631c96050401998c6392c0a081e3721d5358c410047dc02eab1082018f8805d562104b317d0f21ac420966aba0a43588410045f43886b108259aae8210d621040f1d90ea92c4208029b60a765484100537c12eca908200a7b805d952104814f100bb2a42090697a0c76548410052ec18eca908240a7a801d952104014f3003b2a4208028f61874548410061ebb0e8a908259e2c42589521040d4df0cb12a42080e9ba1d625484101d3643ac4a908259e2f845895210401c5ee8b12a4208038b1d162548410071721ac4a908200e2c4358952104014df00b12a4209670fd4976908412ce1ea92ed21082258bf8758e421044b93ce6b1c84208022fe1d631084112e4f39ac6210822599c835c4421040d8dcc4bac64208031b5d5628c841096573a2c519082008bd86dd1321040f1d90eb126420803a310d624c84103e7238ac499082258bf8758f411044b93ce6b1e82209662fe1d62d04412ce57392c5a088200e2d6254b411052772d0721482208030fd4b765044103e5b28eeca088200cb551dd9411056933d0fb9a822080327ddb73504410064fbb0e6a0882258bc8758d411044b938e6b1a82209662f21d62504410064e39ac4a088259cac72589411040187eeca928220a5b471cd52504412ce96392a4a088200e2d62549411042596ca9bb282208032d55376504410063ba96eca088200cd776dcd41104019aeec39a8220ad365dd073504410063bbb2a4a08820387e87dd560104010fb05baac0208021fa1c755804100536c10eab00820087e87d4960104070f90fa92c0208021fa1d52580410043e43aa4b0082078f88754160104010ff0ab80c91880e1f215701923116c6fc3ac9a1c62b499f87593438c569b2ce938e87188be37e1971d0e310045fc22eab1462128bc845d5628c4011f700baac5188063e2017558a310064f41ee8b146200c9d83dd1628c40193e61ba2c51880327dd34358a310061fba6a4b146200c3c74d49628c4014db053b2a5188028fe117654a310051e422eca946200a6f825d9528c4014f700bb2a5189029e2017654a3100537c12c8a946206a6c82591528c40d4dd04322a5188029b6086454a310062ebb6e6a946258b4e82d0d528c40147f08b12a5188028f2116254a312c727192c4a94625899c845cf428c45b93ce7b248518897279cc6490a311cccec3e872146200c9d76d0e428c40117d0f32285188022f61f6410a310064ebb68621462029d4835c4428c401b2e86b88851896327d8a748ca312c
  | 15 => 0x328ec6a08aaa7a1270d8d410054ec24e1b1a8200a5f855c363504014b90ab86c6a080237a1c50d8d410046ec38a1b1a8200a9e84143635040153b08286c6a0802b3a0850d8d4100566c10a1b1a8200ad68114363504015ab02286c6a080237a1c40d8d411546ec3881b1a82008de8708363504011bb0e106c6a080297a1420d8d410052ec2841b1a8200a9e84083635040153b08106c6a0802b5a0420d8d410056ac0841b1a82008dd87843635040153d09086c6a0802a761210d8d410046ec3cca31a8200a9d84994635040159d05328c6a0802b360a6518d410046fc3aca31a8200a9f84594635057bc3ec9a90c6a0802a76126018d410056ac0cc031a822dc9c639db435040553d0db1e86a0803279db63d0d412f45e432e5a1a8239c9c635cb43504019aec638a86a08b6a7a1b7350d410164e3b6e6a1a8202a9e86d8d4350455938edb1a86a08022fa1b7250d411fe4e31ee4a1a8200d97731c543504071df0ea96c4a08021fe1570d894101c3e42ae1b128200a6d85083625040155b08106c4a0802b960420d894103636312eb3128200c5e75d8e62504018baebb1cc4a0803179d463989410062eba8c73128200c6d75d8a62504011bd0fb1ac4a080237a1c63589410062f3aec63128200c5d75d8c62504018bcea318c4a0803175d4631894100477c3ac43128241a5e83dd952504014bb07bb2a4a08029b60a76549410051fc22eca928200a5f835d952504834b906bb2a4a08029be0976549410053dc02eca928240a78805d952504834bd0db1aa4a080393dcb63549415051f43686a928241e1c63d0d525040165b05a1aa4a097b8b18b435494120d1e43286a928241e1c6350d52504bbc58c4a1aa4a081a9ba1b625494100727b1ec4a928200e4c63d8952504074dd0fb12a4a080e9b21f625494100536c06c4a928200e4f631895250401c98c6312a4a096b0fd4a76d09411fc5e432e7a12823fc9c635cf425047f53d0db1e84a0803279db63d09410064f3b0c7a12825ac3e7654b4250555c38c6a9684a081b8b18952d09410062e31aeb2128206c6c625d642504011b90cb9c84a08023761f63909410062f3aec72128200c5d75d8e42504018daebb1484a08033518f71509410066a318e2a1282008be86dcd4250473938c7b9a84a08e6a7a1b63509415a64f3b0c6a1282a6e8c63dc94250401d18c7b1284a081b0f1d952509415470e31aa4a128206e2c625494250401d28c7b8a84a0803a518c71509410062e31aea2128200c5e75d8c42504018baebb1884a09071718d758c9411fe4e31ce91928239c9c635d232504018bcebb1c64a0803175d7638c9410064f3a6c719282008be869d1325047f938c73a264a081e2f219744c9411ce4e31ae899282079b4815d1325045b53d0da1a64a0803271db434c94116c5e432e720a822dc9
  | 16 => 0x1591320065b210e2b226400cb4421c5644c8019ae6038ac8990022fe1d64191320055a40ac832264398dd87d93434c87333b0fb26869901a37e1d64d0d320056a40ac9a1a6439d8e745cb434c9151b90cb8e86992a29b60a64549322ef16212c8a926400a7781591524c8014e902b22a499107179db7354932035a7416e6a926406a5e86d0d524c80d69d05a1aa49917bc310b43549322ec5ec3ec9a12640699c845cf424c8838dceca9684990038bd9152d093220ea739aa5a1264aaf0c4354b424c8bd17d0e32284990023de1d61185320055a422c230a648f87f825d4614c8018be60ba8c29900327e0d74185320064e41ae830a6407cb4815d0614c80193e60ba0c299003275d3431853201c3fc3ea430a640087d87d48614c80187ce9a90c2990030f5d352185320362eb9ea430a648fc6d72d48614c89d8f4e1a90c29907e1fe1d521853220c3ec3aa430a6400c3e74548614c80187ae8a90c29922b930c952185322063d382a430a6400c7b525c0614c8018f2a4b80c29901f3c88570185320043ec3cebb0264bea6d829d7604c8070ff0ebaec09923e1fe0975d813201c3fc3ea5b02640087d87d4b604c8b90ff0ea96c0991061f61d52d81320045fc22e3b0264128bc845c7604c8031b906b8ec09900e1fa177058f410043ec2ee0b1e82008bf865cb43d04bb17b0db9287a080e1fa177058b410043ec2ee0b168241a5e839d952d04014bb073b2a5a08029b60a7654b412053d404eca968200a79809d952d04014df04bb2a5a09068f61b4354b4100596c1686a968296a3f8650d52d040117f0cb9e85a08ff2798d73d0b410361ebb2a5a168206e2e6254b42d047317b0db9a85a08e72798f7350b4103716312a4a168212c9e7458e32d040f17d09bb265a081e6d205744cb410064fbb68699682009b5841c532d0401b2e8638a65a080e1fa177058e410043ec2ee0b1c82008be8790d62904b555d0521ac52096a2fa1c4358a412d55741086b14820387e85dc162904010fb0bb82c5208029b60a7654a412053d404eca948200a79809d952904014df04bb2a5208030f5db7454a4100537c12c6a948206a6c8258d52904b5c5c84b12a52081b339897390a4100666b9ac521482008bf8758e429045b93ce6b1c85208b62fe1d6310a4116e4f39ac6214822d99c835c4429040195ae8b14652081e3b21d624ca410074621ac4994822d8bf8758f419045b93ce6b1e832096a2fe1d62d06412d657392c5a0c8200c5d75d4f63504071bf0ea9ec6a08021fe1570d8d4101c3e42ae1b1a8200ace82997635040159b0532ec6a0ad3279db74d8d4147e2f3b6a5b1a8200c5d751d76350401c3ea92a6c6a080297a1672d8d410052ec2ce5b1a8200a9f845cb635045553908b96c6a080297a1472d8d410052ec28e5b1a8200a9d841cb6350401caea
  | 17 => 0x288400a5c835c565108010fd0e18aca210021f61c31594420951f42062b288400a3d840c5651080d4dd0418aca210029b60831594420053d40062b288400a79800c5651098147f08b82ca2104a8f21170594420951f420e0b288436a3d841c165108014bd06382ca210029760c705944203537410e0b288436a6d821c165108014ed02382ca210029d60470594420043f43e60b28840087d87cc1651082547d08182ca210028f61030594420951f42420b288400a3d8484165108014bd07082ca210029760e105944201c3f42ee0b18840087d85dc1631080117b0d38e862104b2b953765084200656aa6eca10840087f855c261108070f90ab84c22100237e0d75584420146e41aeab0884028de87dcd61108b18bea5b9ac2211631754b735844216c5f43e86b088402c9c73d0d6110805938e6a1ac2210030fdd2745963203537414e2b2c64bfa6d829c5658c8014bf06b8acb191069720d71596320051f420e0b2c6400a3d841c1658c8834bd06382cb190029760c705963203537410e0b2c6433a6d821c1658c8014ed02382cb190029d604705963220d2f41880b2c6400a5d83101658c80147d09082cb190028f612105963220d2f41c20b2c6400a5d83841658c80d4dd04082cb190029b60810596320345e422eb3246412c3f75d52648c8010ff0ab84c91900e1f21570992320961fbaceb3246400a9f835c6648c87f53d07a8cc919002a760f51992320054fc1aa3324643fa9c83546648c80147f0ab84c9190028f21570992320945f438a132464008bd87142648c87f53d06284c919002a760c509923203557410a13246400aad82142648c80156d02284c919002ad60450992320945f43c2132464008bd87842648c87f53d07084c919002a760e10992320345f43ea8b246400c3f75d51648c80d55d05aa2c91900f0f9d654592320345e43aa8b246400a9d83101648c80187eeb3aac91901aaba0a755923200556c14eab246406aae829c5648c80153f06b8ac91901aaba08515923200556c10a2b246400a3f855c1648c8014790ab82c91901aab20970592321cd4f418e0b246400a9d831c1648c80117d0e282c9190022f61c50592321cd4f418a0b246400a9d83141648c80d55d04282c919002ab60850592320055b408a0b246400ab581141648c80117d0f082c9190022f61e10592321cd4f41c20b246400a9d83841648c80d55d04082c919002ab60810592320043fc2ae130c640387c855c2618c82517d09b8ac1190022f61371582320346ec1eebb226406c5d73d4b644c8010ff0ab84c89900e1f2157099132006ca218e2b2264008f7815d5644c80f1e902baac8990023ee01755913200c7c402eab226400c7752dc5644c80196ee838ac89900335dcc71591320065b218e2b226400cb4431c5644c8019a88638ac8990031dd487
  | 18 => 0x80d87ce9a94c3a100e1fa1f75583420043f438eab068400a6d821d560d08010fd0fa92c1a11721f21d52583420146f41ee2b0684008dd83dc560d09894df04ba2cb210029ee0174596420053c402e8b2c84c7a3e849cd659080147b0939acb2100317dce73596420053d404e6b2c8400a79809cd659080d4dd0521acb210029b60a43596420051fc22e2b2c84c6a3c845c565908010fd0e18acb210021f61c31596420051f42062b2c8400a3d840c5659080d4dd0418acb210029b60831596420053d40062b2c8400a79800c5659080147f08b82cb213168f21170596421ed1f420e0b2c8400a3d841c165908014bd06382cb210029760c705964203537410e0b2c843da6d821c165908014ed02382cb210029d60470596420353741480b2c8400a6d8290165908014bd06202cb210029760c40596420043f43e60b2c840087d87cc1659080147d08182cb210028f61030596420051f42420b2c8400a3d8484165908014bd07082cb210029760e10596420353741020b2c8400a6d8204165908018beeba9ac72101ab3a0b5358e420346e43aa6b1c840387e85dc163908010fb0bb82c72100317dd67558e4203567414eab1c8400acd829d563908015af02ba2c721002b52057458e4203567416a8b1c8400acd82d516390801c3ea92a2c721002a7e117158e420052f428e2b1c8400a5d851c5639087953d0838ac721002a76107158e4203567410e2b1c843cacd821c563908015b50038ac721002b66007158e4203567410a2b1c8400acd8214563908014bd0bb82c721002976177058e421e54f420e0b1c8400a9d841c163908011bd0e282c7210023761c5058e420054f420a0b1c8400a9d84141639080d59d04282c721002b36085058e420056b408a0b1c8400ad58114163908791bd0e202c7210023761c4058e420046f43c20b1c84008dd87841639080153d09082c721002a76121058e420356741020b1c8400acd82041639085b93cc738e87210033358f7250e421cd4ec36e6a1c8402c9f76dcd4390801b1ee7b9287210022f6187150e4212e4f318e2a1c840087f855c261908070f90ab84c3210962f21d43586420164f39a86b0484028de83dc560908011bb07b8ac12101b0f5d352d8d420043fc2ae1b1a840387c855c363508019a8c638ac6a10036510c7158d42536c621ee4a1a84c4c3e76dd1525080d47b09b1aa4a117b8b10b635494261f27996c6a928406d2e7454b425080dc5ec8a9684a1002ad61031d854200572c1063b0a84008f78758461508015a906b08c2a10022f61e43185425a74a1888630a8406c3d74d4861508b3c5884a90c2a10021fe15701854201c3e42ae030a84008df835c760508051b906b8ec0a104a8fa1273594426151ec24e6b288400c5f739cd651098347f08b8aca2104a8f21171594420052fc1ae2b
  | 19 => 0x257e0d711915220cae41ae2322a41796f825c464548018f2e0300c8a9002cb60a40191520058ec1880322a400b2d821006454801c70c0200c8a90de5be0974d8d52034b6412e9b1aa40696e829c763548352db0538ec6a91061f61c60d8d5220d2f418c1b1aa400a758118363548018f2e0306c6a933753dcf7258d5220d2f418c0b1aa400a758118163548012db05bb686a90025be0976d0d52004bdc02eda1aa440978805db435488327b0e32686a917a4f21172d0d522f696212e5a1aa40696f875cb43548072dd0cb9686a900e5b21972d0d522f697c22e5a1aa4c3d2c845cb4354801a5ec8b9686a90034b19172d0d5261e9721ae5a1aa4c3d2c435cb43548012df00b9686a90021fe1970d0d520043e432e1a1aa40096d82dd943548012df04bb286a90025de057650d52004ba40aeca1aa40097b805d943548812f100bb286a91064fa1f6450d520061fbb6c8a1aa441b1e83d9143548bb27b09b9286a91774b90b7250d52034b7410e2a1aa40096d821c543548752db053a6c2a91061f61f63d855220e2f39ec7b0aa4ccd6572d8661548014eb02304c2a90030fd8b745855200697b16e8b0aa400c3f621d16154801a5ec43a2c2a910657a1f73585520068fba6e6b0aa400d1c74dcd61548018bec5b9ac2a900353d8b73585520068fba0e6b0aa400d1c741cd61548838b8e7b1ac2a90031e1c363585520063c382c6b0aa400d2f74dc96154801a58e9b92c2a900353dcf7258552006a639ee4b0aa48bd6772d8561548812f50fb82c2a90034edd370585520069c3a6e0b0aa400d5b73dc16154801ab0e7b82c2a90035adcb7058552006b5c16e0b0aa400c7b62dc16154801ad6c5b82c2a90031edd870585520069dba0e0b0aa400d38741c16154801ab6e6382c2a9003561cc7058552006b5b90e0b0aa43796f825d061549592df04b98c2a932ed960a61185520043fc3ac230aa400a788058461548012ef0eb08c2a932ad9e0961185520063cb80c030aa40696e829d360548752db053a6c0a90de5be0974d8152034b6412e9b02a4ac96f825cf605480d2d904b9ec0a901a5ba0a71d81520d4b6c14e3b02a40093f845c7605480127908b8ec0a900257e0d71d815220cae41ae3b02a41796f825c7605480d2d904b8ec0a90038e18374581520061fb16e8b02a400d2f62dd16054801a5e41ba2c0a90034b48374581520063c300e8b02a400e38601d1605480187ec43a2c0a90034bd8874581520061f300e8b02a400c3c601d16054801a70c03a2c0a90030e180745815200697900e8b02a400d2d201d160548018f0c1b9ac0a90034bdd37258152006963a6e4b02a4c9e6860dc960548018f0c038ac0a91029ea1b60581520069c3a6c0b02a4c8d6b72d8160548251b90ea9ac7a101b0f1d35258f420351e422c6a9684008bd8710e61d
  | 20 => 0x200040020130038000004001000000c00200400000200000000000000000000000800400000000600000040040000024010000003801400600d00400400120040008000000001003800001c000001000800000a0000028036000000800001000000680000000000000000012000000800400a003004801c0000010010004004007001800000c00000000140160070008014000003003800000e001005800c000000001800c00000700000240000000020000024001003001c000000001800002e00000080040140090010014006009000000000e000006001c0000060078008004005006004400400f0010000006004004003c004002002802001e001001001800000600300000000000088004000021000001001800000180000040010000034014004000800c002005001001400600000100040040010000000018003000800003a000002801400000000380080080020000004000003000000c0020010008010006001002001400c001005000c00000200000000000000018010000002000003000000600000000020010000000000005003000c010003000001000001400400000300000048030002002004000000400000000000020000058004000002000000000000e000000402a0000000004004007003800400a0070068020008008000002800800000080000000000008000024002000800c012019002000c000011000800c00600000000040000020000004004002000800400000700000080080070028010000000003001c00800100000100020000010000008000000000c00800100000000320010008024002014000804c00000000a8000000017006000400200f00100000020020000004020000000003800800000080040517908baac5a18023ee017558b4300c7c402eab16865ec3c74d4962d0c251d90ea92c5a1a3f0f9d3529874301c3f43eeab06860087d82dd560d0c010fd0e3aac1a18029b60875583430043f43ea4b06860387c87d4960d0c25b3680b8686a180a2f61375d89432ee1eba6a5b12860087f855c36250c070f90ab86c4a1a9b2b5d3629894300477c3ac431286008f7875846150da356f08b08c2a1a3f0f5d352185430043fc2ae030a860387c855c06150d592df04b9ec8a906a5b60a71d91520051ec3481b22a400b2d82903645480163b06206c8a9002cb60840d915268696b96c9322a400a3d87d92645480187b0fb24c8a93430f5cb649915200717b22e5322a400a3d8498264548018f2e1304c8a90028f610609915254e97ba6e4b22a44097a87dc16454801ad6e5b82c8a90035ae0b70591520063db16e0b22a400d6b62dc164548018f6ec382c8a90034edd07059152006b5b90e0b22a4cfb2d8299064548010ff0eb20c8a90029e20164191520049fc3ac8322a4ceb2f82590645480167100b20c8a90
  | 21 => 0x2d5ea77e00009b8718000428800000037036891cc432000000000000088c00016fc000000000146c0000005038c1d2702173d9806c68873b56f00005ec45b000000000000000000013140002e60064bf28b7000133135212e43d0a4800081b1038c211e4a5c4b515200000fa57fa4885cc000000000000048b1960ef4001000000c0020020020000006001002800001600000400000020010048000000004002000c00800300080300000030030000000004001001c002004004004400000500080000060010050004002000010001401a0000018004002006002800c000001000000400000c01600180100030030020000000000800402e0060000008004001001801800600000000080000000008000002001001000800000f00980040060030038020014001002801002e000004800001c0050010010006000000800c00e003003800001e0010040000000005000800800a0040000004000005010000801e000002000000400c002000000200a00000000000070000014004002000000000000000080100160000010040006000002005000400000000000200020030008000000003800800000000000000060000000000014009001801001a003000800000c000000000c0040000010008008000003800000e000000000001e00200c000400000c004002c00200f003800000400000000140160000020000004005007004000a002003000400001900000240000000020008002000001000800a000005000400800900a80040020070028034012017000800800a00000280000040010070018004005001006c016000000801c006013003800400a00b004800400e002002004000000000100140060020008000000002000000400000400080140000140000004024003000000400c0000018010006001001801000a002000005c00000000000000000020000004000003001800c000000006000000a002000001000200000c00280040010020004004002000800800000000080000560030068004024001001800c006000000000002400c0000004002004005000400200a007800c01400500100680020110008018006003000001000000e00100700100030058000016001000800800000d000800c000004001800c00e0080000004002001000000c000002002001c00600300000140000110020000004001000000800800e000002400800c00c000800a00d0010020002000000000001c0020010010002000001001400a0010008000004000000000000600100080180000210000014008000001801c00c001000003c01000000100000180050068008002000000000400a0000030004008001000000000c0050048008004000000801800000a007000c02e008002000000c00100c80080100020000004000004000000400600000b000001e00100
  | 22 => 0x22a123891407d800000036a14f29840009d22fe8e845000cf1d50d480002144128000c7e7853d120511e200018aabc918800008d884400000024680004040000001170f066b704080000008ba12917b8bac87657800f91764ae11f8840000000450841925600048496f888a00023f9e8c00000029500000000000000000af486913c000000000051f0000000000028000127451744f04c818e00046d1774dbe70b00007c40007de344800128000004ba5c8d4407a00004b400000c074045000059606c12ec9565164228000950acf0540d7873000005a279956a37f0d580006545b730080002ba5052d0a6509ee29700029542382c521395f8b488373db80000006794ab80008540000000000752000000000000007e3ec00000002350000b880000001559dd948e3a500016bc75c9c44f8a17c5505095789c7c2501b613e8000b9695d3b68e3c60473f4d400000000000000000fb27520002564a6e82100009fcd6c2ad000000000082c00000000007541480034798000000250800072100000000000002a81e8400000057100011b800000017bc000855394191942c000546a8c85184ee0001ff1572a0b5402410a4841d36a239cb7a54e48915a039eae836b00000000002c705f88ca8640f7a3e51544170000000516a1100500000000ef00005850da5dc00000000007430002aec0008682b30d7063404313517acb1a5a90450e142427b94c09a20dee000369019830a0044208000b2850a00000006da0000e70000aa47f50001a2800000000025bd22c947000000000000000000008ac2494d7a53c00059700000007122f04fb80010d4000000000000054f0c686100004ca03a16a122e7ba211a9dcd5c4cb000000094a63100020fcc500000aca08800067234683c5382838000177800cb081108000e1ca564e69b4052257d2f180000001e22a98d54eb01ee29d131958c171000000090400023d80013ec00021c8000d684a419681383c003106f8fc854437349295f07280a13be0000e3471613e0a0857800011488253008a9000176c0543e300000000000000001e7cb889a100017242302df000000000082d048000131cac30002c2d45a0000000a5801c98232d99a91e00000d0892c88464303e8554dca0003ad8000b8613900022294a846426180ed32c0000001850e9e00019d800000010106c8b5c54c3d50001f246ce5bb58085e896e14800024b80000000d01eb00008d150102bc8a600010280015260ab0001e6cc207f114d83d8000a3c000000112032f24618dce3a27a0a582880008200002be108461a0001c2885205b3a69a0c2fe9563e083dcd2a00017717c8b9c91300007cc00000008f03a400047126a1800c107aa0918000aba8893399d6800064a57080000005403d58000d9454233d19ac0007bd1de14b40006193930c
  | 23 => 0x93800009b34b0f0413a4863240f28e6c287000096c0000000000000000000393800151085a00022005de8f82c48c8070048f2c58bb11acae9000000000085b0380b3400067400025e09aa44f15526442bc1f6203a8ec3e41af2728c953320d24f9072560c92f07705c14105713da110c6385f812508c081c2f30982c1000000000024300001d43528000000a6c00029f54d69d54b5a46901834e3bf9d5c0007591cd00012e89ea3018cd069a0003970000f88000000000000055f2e0070143841600024a451e38e48c80009880003af9e940005d00002980000a2e0001280a2613d21b800000021c00021849a600000007b518e0004cf06b49c2a052bb2a0c8647f4470a02d3243765548d640005123b90f7c7da2bd1a520445148434be9e5000096448c00007702bb28c9d0548caba54108e8b104020000e8c22c0000000000a767b241b267400000037a00013b80000000f10cc45d10169ce52ca5740301ce947200015704980002fe0000cd4b82463551a9c12b67131139d2c000000000000130e000007a4ccd4e8ae000000000057848000009ba0001548fb8354085000000043054636e800000000014302351b6000000045cb3214f28a8658000766283968d19654d47a215873a4be0000de5554a710000d60000000000000000024356b8000f8c0002ae000000000000005bc89895332f8000000000000094d3063ce1f60000a5831d36c935cc567911eda98d28a04011418d15360f4055000000069017ba7c00009ee49b9b9c0600003338c0d28c000000161d3908e50001d3800034800010803160000209a1d2a4a9a00002fcfe020802b800000040600009c021a0004bd1d880007bb1a809a01644ba12c933ca700001cb8f9061e60c0001c940003f3000281000000000014800009d63d30f64b22000000000000000001400000000ce0a100000000002760000e0e1c258517fd01a8d90000f4c10cabc4ac21f096465c41919dcbc29bb0298d8862424f33785c912a4782561dc424a3690e984f12b89612c306450329e74b9a57c7e86230001ba40000004d594309a000006680000009db00000001009ac000000000063c53392c06b60003ff0000ba62ac3a4290d05672b3618fc434c0000000c5c0005a03e7800000057b00000005c094e1eb9c5c000000000000000000045e0ff400028328e14940001f445c00010ba0000889a3cb620c9000095000000009987b00000260001d0046449a53f17a40000000688000d8c05d0001af000000039480000008ca1f5000000000047215c8aa2000000030094c0003709bd800000000000014a666633c1b5426800000000001f206124828744d875c290a52cdb65c55530640c1e000172a1940007780000000ffa30a0000000000000000060914400013b08d053e806205175d34c65e26f136927e0
  | 24 => 0x21e110127c4c00000c48bf0af200034080000009c305f218c83e2853b711e507847a48a9dd08e098900025b0ad20004581248f8000025c000046e4fe57780001ca4b60000d1d60472202500ccff60000000000b7400000011842cc00023492784e482341d0d580000004220000000000000294800000000028fcb7285909d0ce950260e15000003ee0002301ae50d8000000000006a43b1f0800000041a00000000005813eb80008780000000000e628e34c592a92062750b29590df867f46aa18000017b00028410faa0d095889487e3711cf0000c2c35a0eb8cdc75029d2718000d7600027b1f8000034300024b40000000000000abc0001be20e40009764c61a740000000001c70c76aa100000009620001ee93fc9b828402882e4b4a42c22d27a0cb48580c419147f69a73b494e445a1f80cda4a1272a6d101a23c1e017302f839d12c5b0524a7f8cc253c10580000303c90b70fd4b782d22391d900c87c512c0b0118a0000001600ab26534f793f492881a45f8ed48bc9901e280003583a200006882a000043787ad11680800008b00000000000000cc0a063a300007f83631ed253066000036080007fe6823b41300d8a850397a0151bc4142972b68b4e3ac3c7ab8014e6930c70170b6425f3491f3406cadb059867cc96a8400011d0dae3364f01094ca800000000002c476116f18e844c9754139e480000000001670000000000000000054b0000000ce09e4000118800000018c00000008a75819e1013833e0d394d800000000000000002b724e80016180000000e48ebc00007a8fe9466a1f06e1a5c000000225800000044905211214805e40759c6c0003110002a3c000000000000026201600027b4000a2007e8e6455e0000001f5120c9864f60000e840001e90618afe6b500000000000003dc00008a820c00006740000fe0b383c8e667ee0000000a5275344280009f295135001251b03534a4805481069e000000044600051819d891c1572ad8000ee67bf4bf247405895e000276129081f47f0000f628882a6000000000000014f80000000002b21264a25269247ce980000311db0000abe3fb80001da00037c80e40ac0ba53519f4ed68ec00018980000000001bb12da0002712a184e69dd3291d74fb43ad5258000124644000243490e53f0000ddd1686aa0000e8104c14a45c9bc02c821f1d880015585f526680bd57a7f812300000005a655388cd5d89791e380007ee03800010d84f60523401f88aaa05512080000000001bda9ec000000052a0080001020000440e6e00035190840000004f080000007320ca233c8b01fc16b2148002b0d107800000015416700011289aa0002054000000467037821088339a21991f8024061167c4987903f780015be557120246caca4bf11c1b2036823c38a0b254cc76046a000038e0000002
  | 25 => 0x7814d11a9076c10b16c23f534a44430b9f7c0009d7000000100e1be29996d02b6451331910061279a3260f08000000424800000031b000000031e7933ab133800000001700000004bc000139c00000017395bce484d80ff87f8a3cacc048928847a83d4258fa0716390379893414c78949016b471096e01020b83aa2da37d07a94be59a49a97f94009213bc9c3472a7b500000000522ca00029b80000002da98150240000000000874aa032100002126ea199a6fc90000000000000004e943980005867b60371b70d560f3000000067e9f5000108881e9f427e26c0c9a9fb1d5aa78fac3be00000011327e74c41e3011e9845669f0c5c219700003a86c294d559a86476077000000000000001a2ab100888ea1680b106c800056c00000000003a387480000730cd0000c440003e500000004b52cc00000001c100000000000a30000000b8e79c00015800002c600017d00000000000000a3aa284d9abcc0000000001dbd59c00027800015f4857000000141862f16c80013847a9369800011800025680005f64313f993242700001ef140534021b000000045693415810353a269a4e5aa4815204d15a916531a9950dea9e4d1884f1698c4cb6caed4d211a0ddc1e71f823d8e069c003c00000009da0000000000000548a72426e0004ce26f800065510922040000e151e9a440008af0000720f480d539e0984de4b090680a50d0a00049eabf11e6000000000000014353980001f800000000004e200000013910f042e33888a820085300000015925f300000000002f50bc80000000004d88000112000000000065c3842ce80008be3683b194d0f2c11f3829fc877eafe1008000c3015c47fa2d400033c06d06f020e3d64591c30568a9535794d431417d00020cc0001460fe80000008c82ab06c400000047d00015fa4ed3bd81ed2049fd1348000162000000000040009f3a286fc0000000000000fa69500a600006c00000000e1c00000000000002d234250c28480000001a60000b26000583a5c40000000001b794e4000000000124c8e800000000000003050000d7a000000177ca6025a26080000003b300000014b000023b89702d847c1860000ffe000000203c25429c000000141281e000287800026650d185468000029e93152e02f43f187613783cb195a5dc3c6ac032b98b003400055faabcc5c7a81f58000000000000000021e9eb17d0794e7c0001dc936516c9b4000000107c8df526000000060400000010fe0003561c0800082800022355d4236194000000000000002dc0002931cf80000009013590000000a7822300000003c625c9cf40003c31b5800000000001b9e2c9520004da8280cda8973e595500004b44d717c15b825d4960b081c0000000122026c000568000000000000000000000001b30d442f01404922a154ae
  | 26 => 0x45ab4ef8a684ac7e93ce80014fe000000274c00014700000003640003f58000ad681d1179e795326f82c11c20dfc0004372ac0e323463baa00c128a373598c7c36e26f4c298940f800026427e518c43424e22105644a30000000e000003620000d3800000001c8ba877a0002904ca0000208800000069f174152800000000029900006214240538000000000126c9de99309d8ae000000000019945b600055a187c0000000000000e1e11a0000acc000a0f00015dc00008b00000002400002b100011da89303388b82ec0e40000c786de466009956910c48a00e81301586204842038f5a05938913c434a8e913680006f46a62d727cc0004330328a84cf800000029784bc8770d40001162afb0e6800000063d3be80006be00000000000000000000000fd056e5481e8000000020c0178f3200039000000000003d780008d80000000000c700001a78718696000212000000087100028d800048550a020c0008bd39c27fc0846a9186a968000ab20139cb00b07ce08a80009846983ea8f70e02a9f000000000000000000006920002c9066000069400001d55627dd0002a7444861c2dc0b20a8e0003c68000000aa40d70000000000000024d1de00000000000003b419c000007a4380d2034c1d86360e886ec0005aa2990f440000ae0002b0894e00000000000003f94b3906c9b600000000000001fb000000108e3000002334a46a9c52e8000000405532831800000000023ecdfa4670000000016374200068d3721740002b500008d74fc000102e0005759fd93700b804101140000250002b491c462451d00000001b3000061c7b02cb0038000000a4408e80008a45630001f94e886c00001f090941e90000000fd84354c780013469d900fac014360004530000a8a570000000000000003580008381802c18000d7e03c2058994cb0862350a8d000085e3589ddcd3262900000000000002758000fda00041d8000f145d537212bc4440001990c9c4625c64cd00011cca5000001d800000000000008dc00000000000000003058000000a5b00009d0ad442b000098c2580d44cf80000000002701b3000038a0000000f2ea0352280000001d02cd94ac00009900024140ee01e12200008508c30002b4d27c87b00004112220cb08600004c80000979fa88a01193968b8c53001055b80010f21e41d78001104ad10001510e12195027a4d906a23b4f287852462dd40c0000e089d0268937c00061b01f8be00000003431a2cfb66da04a85a91828540422238c1a0d72e91b24e3c0000002bdd51ca7c55c27280000001468000f300001948488912000456abd000000037400001908eb0002a240000005771bd40009072f3131c1cc00004c1bb400071851600c8b1415a3a8124c3f400044fa04097a6304e30b54802000412149cb2a4f20000be40003222d1
  | 27 => 0xf8000000000000000021c00000021300004952fd80000045142f0031400056d05b1f40cdc19306213a1374063036915d2fe04613c98d4fcc1d948798a86422a54b498cc00050654a00005120000e2000000000000000012c47865349468000000500997400087520902b4000295000207144800005da0d00008d23830afc0000000d800000005002ac0000000000000173c5fa02100005445fe01c00018780000000000834000000000000000000000000013c691e0001f9000000005e19594840002a4800058200001d1ae89d4a3100001b0ece19c3470d7400000000006652d0000000266000015f240800067a50828207784d63f844eabd8000a981f4800000093c511a8283b452f3e9036ccd0000000112860200036729d0000a222f60000b1e0000001a6cbce2151788f5102c7b050980000003e04cb95b0000a97000000000000000009dd0ce6c721698e40006f10002340632393000191c3987e100017d905e5e50ba920c3d0606223973477400054b091c000528000200043a0002178b3114050b565a294e222623322a1c6083bb23b1bec7367552f8904136ca17000159d2f600010203fc37051133615d55ce3e234217f0dd691037f92112a82dc22e81bcd967650fc854827c8c20ef8358d7c3a406e80006a864e0b697640000000ac19ec4726131988000000a2f0c197280007a70001b891488c04939134b206754a21264282149418980833c30e0daa4c10fc00051c14c45107c7000000000039c0000728a2064f3a484a4a1a000015800000021a2c623d400007941500000008924f4905400084601a250c0002e41e4012c00021600027f00005ed4a0851059e1921bc0000cd2813004278810e6110000428000000000000154a000152000028a00016a0f9c0004d600029d40000ca56a89f800000027a00010e80004ea25811220235541cc000037d35813d4000135000000000000033f040c00000032caab487a2ed0c0805c4a22ba0442010e545614a529a01981d6000000149024e528899cf2aa764ef0db001276a42e2330b0a9bd001a9bc7ca0004b30000bc400005e80009300000002a30000a4d1db99008da1530f80000000156316a42c78097c1cb1f4535a3fe02393e86483050b01cd464cae554587140008ac4ad1b98b0825024b11f40002b130480006dc63e582800080661d42024ecff200036686300d000009201c48d48ab0e580000d280900000880005c21c19e200000005572b14db01c31c697a800099b1d300000000000ee044800a000168aa8800074a151800000000029116b13645b30002be4000a1500028aca060000002988ff437502a20c016aa0e2ec1284c828e0122a26879e51831381fd146381000000000000000027389f6000293200492e2b900011d40007870dc9098000000573150c8d680a1e6a4c53f
  | 28 => 0x25800037235c271d56c8b3287a8d55144190002b04000607000038862c28e0000000000000000000070400044c00000000002379eb80002570618000000a213c123255c600019180000000000faa73d5564e61832b1c0000000ee94080281770000a0441c8723778d954f400004f1ef08600005720000c2400036786a47de20600000000000f80000000e2a0000000e1921c00000016780000000000df80000003e4000057c000000289cb9047e356a1c06208f73ee0a9c7a02553c71f314942c7000000000005a4e28304090a2a32898c8ae6a4f12110309f043e0ed93cc5d67800b4258c6721634699010722a264268ec959444e20f02386280e300000008265fa00020a47cc2f228719249660004db91040000001748798bb40001ab9c8c20a9cc00023b868240956b05acdc62b600017dc414000089804874e0000001ef800000014ca37525424837022f80d449122a82c15b214d514849d0d600011f227027e90a04d0000000000427226c4260003610fd92aa2ea0be06e8d500112f41504000add00000000008870000000e2075100000014b200028
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x285000845914000030009000a800248c34940000a44c00440060dc0cd80038d0c414b004984018105c9d090c2cf420648868c0e074b8e86cac001c7cccbcec088054c8f8a0fc011100d400b448f104007800e43c70007033a10001182802c04080190e1c3821004d800068660c601006454801a298218040191520050ea5c60dd1605480183a9818074581520060e660601d16054801c1a9318074581520070664c601d16054801c299218074581520070ca44601d16054801c319118074581520070a183201d1605480142c96480745815269c9364a85dc1639094d48d96dcf7250e4200525a58431c563508014969390871591320068910881591524c8bb42d97d9152d09325a625204835d0614c96949696dcc7150d412f48b25982d0d5250587a0c6360b43549410050e241761d152104b322e9890d62548415a7211c44358932104b342c975895250441007031cd62549411045b19698d0d7110a310050e251701c165c84b542f9759152d0a210048b648855c06448567e042119063549210071118d521c54248401c2464548714c92100658549801c5324856988c861d1324c5210048b64a85cc164085a524d92a177058c210049a64a859cd600840183a841c27654b400041ee6176dc152d000142d9290076549400050764c401d9525000142d9210076549400060e200765d1525000183a7021952905400050b648651d12150001838841c176549300061c204705d9524c001551911c173549300048be6164191524800142c97590645492001c1b25d86d0d524800186876600715492000619e1d52584614800706c985d952105200060ea10709d952c400148d920c47458d100050b648655d0624400144d9219573189100051a64a301d9524400146992040765491000513648655ce424400142d92195748c9100050b648655d0214400144d9219573085100051a648651d920440816609660552481100059825952485204400dc60765492148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x21000303198644601d16054801a08c9b22300e8b02a400d08649911807458152
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x94c
  | 5 => 0x94e
  | 6 => 0x3
  | 7 => 0x2
  | 8 => 0x138c
  | 9 => 0x138e
  | 10 => 0x98c
  | 11 => 0x98e
  | 12 => 0x150c
  | 13 => 0x150e
  | 14 => 0x9ce
  | 15 => 0xa0c
  | 16 => 0xa0e
  | 17 => 0x180c
  | 18 => 0x5
  | 19 => 0x180e
  | 20 => 0x209
  | 21 => 0x20c
  | 22 => 0x20e
  | 23 => 0x140e
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0e
  | 27 => 0x1409
  | 28 => 0x140c
  | 29 => 0x1549
  | 30 => 0x154c
  | 31 => 0x154e
  | 32 => 0xb49
  | 33 => 0xb4e
  | 34 => 0x1449
  | 35 => 0x144e
  | 36 => 0x289
  | 37 => 0x28c
  | 38 => 0x28e
  | 39 => 0x148e
  | 40 => 0x184e
  | 41 => 0xb89
  | 42 => 0xb8c
  | 43 => 0xb8e
  | 44 => 0x1489
  | 45 => 0x148c
  | 46 => 0x1849
  | 47 => 0x184c
  | 48 => 0xcc9
  | 49 => 0xcce
  | 50 => 0x15c9
  | 51 => 0x15ce
  | 52 => 0x409
  | 53 => 0x40c
  | 54 => 0x40e
  | 55 => 0x188e
  | 56 => 0xd09
  | 57 => 0xd0c
  | 58 => 0xd0e
  | 59 => 0x1609
  | 60 => 0x160c
  | 61 => 0x160e
  | 62 => 0x1889
  | 63 => 0x188c
  | 64 => 0xd49
  | 65 => 0xd4c
  | 66 => 0xe89
  | 67 => 0xe8e
  | 68 => 0x18c9
  | 69 => 0x18ce
  | 70 => 0x138956
  | 71 => 0x98956
  | 72 => 0x9c956
  | 73 => 0xb0956
  | 74 => 0x94b16
  | 75 => 0x140956
  | 76 => 0x95416
  | 77 => 0x249
  | 78 => 0x1a09
  | 79 => 0x16c9
  | 80 => 0x14c9
  | 81 => 0x2c9
  | 82 => 0xb1396
  | 83 => 0x138b16
  | 84 => 0x141396
  | 85 => 0x139416
  | 86 => 0xd4994
  | 87 => 0x1709
  | 88 => 0x144b
  | 89 => 0x28b
  | 90 => 0x148b
  | 91 => 0xd5514
  | 92 => 0x8e
  | 93 => 0xe8b
  | 94 => 0x18cb
  | 95 => 0x1449d6
  | 96 => 0x9d456
  | 97 => 0x4c
  | 98 => 0x124c
  | 99 => 0xcc9d6
  | 100 => 0x9ccd6
  | 101 => 0x128c
  | 102 => 0xe89d6
  | 103 => 0x9ce96
  | 104 => 0x589
  | 105 => 0x10c
  | 106 => 0x1789
  | 107 => 0x130c
  | 108 => 0x180a16
  | 109 => 0x28a16
  | 110 => 0xa0296
  | 111 => 0x148a16
  | 112 => 0xa1496
  | 113 => 0xd0a16
  | 114 => 0xa0d16
  | 115 => 0x188a16
  | 116 => 0xa1896
  | 117 => 0xe8a16
  | 118 => 0xa0e96
  | 119 => 0x18ca16
  | 120 => 0xa18d6
  | 121 => 0x1949
  | 122 => 0x749
  | 123 => 0x29816
  | 124 => 0x180296
  | 125 => 0x149816
  | 126 => 0x181496
  | 127 => 0xd1816
  | 128 => 0x180d16
  | 129 => 0x189816
  | 130 => 0x181896
  | 131 => 0xe9816
  | 132 => 0x180e96
  | 133 => 0x18d816
  | 134 => 0x1818d6
  | 135 => 0xb0216
  | 136 => 0x140b16
  | 137 => 0xccb16
  | 138 => 0x24b
  | 139 => 0x155416
  | 140 => 0xd5414
  | 141 => 0x144b56
  | 142 => 0xccb56
  | 143 => 0x1a0c
  | 144 => 0x18d456
  | 145 => 0xb8296
  | 146 => 0x148296
  | 147 => 0x148294
  | 148 => 0x184296
  | 149 => 0xd1856
  | 150 => 0xd4294
  | 151 => 0x148b96
  | 152 => 0x184b96
  | 153 => 0xb9896
  | 154 => 0xd0b96
  | 155 => 0xb8d16
  | 156 => 0x188b96
  | 157 => 0xe8b96
  | 158 => 0x18cb96
  | 159 => 0x185496
  | 160 => 0xd5494
  | 161 => 0x189856
  | 162 => 0xe9856
  | 163 => 0x18d856
  | 164 => 0x18ccd6
  | 165 => 0xd0416
  | 166 => 0x188d14
  | 167 => 0x188d16
  | 168 => 0xd4d14
  | 169 => 0x189616
  | 170 => 0xd5894
  | 171 => 0x128e
  | 172 => 0x170e
  | 173 => 0x18ce96
  | 174 => 0x98d54
  | 175 => 0x9d716
  | 176 => 0x74b91
  | 177 => 0x75611
  | 178 => 0x75791
  | 179 => 0x28253
  | 180 => 0x58a
  | 181 => 0x140d54
  | 182 => 0x154cd6
  | 183 => 0x28d54
  | 184 => 0x29a14
  | 185 => 0x149a14
  | 186 => 0x29554
  | 187 => 0x1a0294
  | 188 => 0x28954
  | 189 => 0x1a1494
  | 190 => 0x150d54
  | 191 => 0x15cb16
  | 192 => 0x41316
  | 193 => 0x41496
  | 194 => 0x40e96
  | 195 => 0xd0d54
  | 196 => 0x161896
  | 197 => 0x160116
  | 198 => 0x160296
  | 199 => 0x1618d6
  | 200 => 0x151296
  | 201 => 0x1a0d51
  | 202 => 0x21416
  | 203 => 0x20b16
  | 204 => 0x154b16
  | 205 => 0x1715d6
  | 206 => 0x41896
  | 207 => 0x40d16
  | 208 => 0x160d16
  | 209 => 0x29494
  | 210 => 0x20d54
  | 211 => 0x160d54
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2246
  | 6 => 7205
  | 5 => 2830
  | 4 => 70
  | 3 => 3
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
  | 7 => packedAt gbK7 (92078+((h/748+packedAt gbK7 (83102+(h % 748)*12) 12) % 2696)*13) 13
  | 6 => packedAt gbK6 (379454+((h/2401+packedAt gbK6 (345840+(h % 2401)*14) 14) % 9511)*14) 14
  | 5 => packedAt gbK5 (179229+((h/943+packedAt gbK5 (166970+(h % 943)*13) 13) % 4109)*13) 13
  | 4 => packedAt gbK4 (5061+((h/23+packedAt gbK4 (4900+(h % 23)*7) 7) % 85)*8) 8
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0f80f83c3ffc3fe01c07f0d1a67e21f793
  | 1 => 0xe01f000ffffc1ffc1fffff8012e59b03e79fc
  | 2 => 0xf001ffff003ffe1ffe001ffffe3061c3c78e1f
  | 3 => 0x1ffffffc0001fffffe0000fc07e03f80fe0
  | 4 => 0x1ffffffffffe0000000000fff8003fff000
  | 5 => 0xfffe000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x121d02883a0c132c1320c4116040821620b391
  | 1 => 0x424200048544044404a4950200608b00a50b4
  | 2 => 0xa04055310022a412a40112a686306140c50c0a
  | 3 => 0x808999da9680111b39958020cbc07603700f40
  | 4 => 0x111ee6ce73b3980110600c30dfb8003bfe000
  | 5 => 0xc9e0007004022002201803040fbd7de8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37249
namespace PEqualNP.Outside.L_meta_37249
open PEqualNP.Outside.L_meta_37249.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
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
theorem bs0_4_128 : Interval s0Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 70 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2816 : Interval gbAtlas 5 2816 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2830 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184))) (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)))))) (concat (concat (concat (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 (concat bgb_5_1504 bgb_5_1536))) (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728)))) (concat (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))) (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))))) (concat (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)))) (concat (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624))) (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)))))))
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
theorem bgb_6_7200 : Interval gbAtlas 6 7200 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7205 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584))))))) (concat (concat (concat (concat (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808))) (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032)))) (concat (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 bgb_6_4480))))) (concat (concat (concat (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928)))) (concat (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152))) (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 bgb_6_5376)))))) (concat (concat (concat (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat (concat bgb_6_5504 bgb_6_5536) (concat bgb_6_5568 bgb_6_5600))) (concat (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696)) (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824)))) (concat (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat (concat bgb_6_5952 bgb_6_5984) (concat bgb_6_6016 bgb_6_6048))) (concat (concat bgb_6_6080 (concat bgb_6_6112 bgb_6_6144)) (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272))))) (concat (concat (concat (concat bgb_6_6304 (concat bgb_6_6336 bgb_6_6368)) (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496))) (concat (concat bgb_6_6528 (concat bgb_6_6560 bgb_6_6592)) (concat (concat bgb_6_6624 bgb_6_6656) (concat bgb_6_6688 bgb_6_6720)))) (concat (concat (concat bgb_6_6752 (concat bgb_6_6784 bgb_6_6816)) (concat (concat bgb_6_6848 bgb_6_6880) (concat bgb_6_6912 bgb_6_6944))) (concat (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072)) (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200))))))))
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
theorem bgb_7_2240 : Interval gbAtlas 7 2240 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2246 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376)))) (concat (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 (concat bgb_7_1632 bgb_7_1664))))) (concat (concat (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792)) (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952)))) (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 bgb_7_2080)) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0feeeeeeafce8ece0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37249.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.and,[3,4]⟩,⟨.or,[1,7]⟩,⟨.or,[0,8]⟩,⟨.and,[2,9]⟩,⟨.or,[6,10]⟩,⟨.or,[0,5]⟩,⟨.and,[4,12]⟩,⟨.or,[3,13]⟩,⟨.and,[1,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37249

open PEqualNP.Outside.L_meta_37249 in
theorem PEqualNP.Outside.L_meta_37249 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4243123424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
