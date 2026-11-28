import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37335.Model
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


end PEqualNP.Outside.L_meta_37335.Model

namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 7, 4, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 65,swapRows 50]

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

end PEqualNP.Outside.L_meta_37335

namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1600012051000001851980101d00100018000be43bc43bf42bd42bf41bd41be40bc40fb30de30dc30f830d830
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa10000000d804808b001464000700002040004d5474296a96835a508c33480186610030cd2186198430c336a8186615030cda106199420c33682186650430
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x1a2000a2588540c2916115030a4587420c28962d0430
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (228+((h/4+packedAt s0K4 (208+(h % 4)*5) 5) % 30)*5) 5
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 26)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe03fc07ffff01e0ffffff01f07fff007fc3fc
  | 2 => 0x7ffffff81fffffff03f01fffff83ffff98fc7f
  | 3 => 0x7fffffffe07ffffffc001ffffffc1fffe0ff8f
  | 4 => 0x8003ffffff8001ffffffe001ffffe001ff0ff0
  | 5 => 0xfffc0000000001fffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x298c471451232602cb327307025390c2bc1bc
  | 2 => 0x24294890c82450a50155095294834a54985455
  | 3 => 0x485291220348a14a540a12a5296814a960aa8a
  | 4 => 0x61632244920ec5939a6c40c1ce528031d50f60
  | 5 => 0x7183c3871c70f9fce38f9cf80c6318c1fef000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
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
  | 0 => 0xfffff03ffffc183fffe0ffffc1ffff0073f3fc
  | 2 => 0xf83ffc1f07fffc3c1ff0f03fe1e07ffaccccf
  | 3 => 0xf003fffe007ffffc01fff003ffe007ffcf0f0f
  | 4 => 0x3ffffff801ffffe000003fffff801f00ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x210011842000200442601118c022310c01515c
  | 2 => 0xa225228c84a90941d0a90a2952145254a4c4c5
  | 3 => 0x454a45106952129c2152a052a540a4a94b0b0a
  | 4 => 0x4a7388294c1b5ceab41888833999c031f00ea0
  | 5 => 0x8c630e318e639f33399ccce0311100c1fea000
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000faaafaaafaaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x900010040001488288969d500c00034000241c015ae0c48e193c0082558a8ba1029d7a3003c10d304451f0a2ca96184cd874c01e0001c004d04009b653129ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x328a4000000000ce763c868007d00000280000120cc4e368bc0a313d0648c731218ca85b1f0e45c0025924f8780784c943c2991c9a6003858de752e1904a6e391401c58180d0ae1d418605a043f8010222200f4c22336108004503008003f000444c1b3100088682f05ca243001ac20003a0d900002a800fc0b350b06e1e388c83e000e1649e5d42930ac3a20834000a3d9c00000018d466001588476152f8010882100a818771c048d208138000200290a0b4090000c4c0428b47000342004682044000c000800042c2c20041000bc04001420042c1804d80020005c7934580c2adca5a1db54b43bb28e877551d0edea4a1db14943b7290876d5210edaa9215b94e42b728c856d5090b5ea8a15b14d42d7a1a85ad4350ad8a2a15bd4142b7290856f54ccadaa9995b94732b6a86656e528ca7ca8194f55032b7aa065ae540cadaa8196b5503296aa0656e530cb9ca6195b94432b6a80655e53d06baa7a0db94b41b6a9683ad42d06dea4a0db14941d6a12836e52106daa420cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518dbd4931b629263d5310c6dea910db55221b729c436c53886dca310db542219f2a0433d54086dea810eb95021b6aa043ad540865aa810db94c21b6298436e51087cca210db54021b7296816d52d02dca5205b54a40d6a14815e53102baa6205b94840b6a9081ad42102eca2205d54440b7294616d528c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320b7aa641ae54c82daa9906b5532096aa6416e53c82d8a7905b94720b6a94416f54482daa8905b94d20b629a416c51483d6a0905b94820b7a96216c52c42dca5085b54a109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8b03007180326a6480a0e5082ae02c124402a9600080601e090000140aa95874350b0c5350d429998754cca2d64947328bd9150cca2d6595032c354d42d06a461509418b590524c64e63d52218b592538862f64542218b596540862d6414c219a580530870d5350840c9509511022d6494a308b59053c824c635512099185544822d6414d208b590514822d64948208b59052c422d6494a10
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (864+((h/16+packedAt s2K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s2K3 (1028+((h/8+packedAt s2K3 (988+(h % 8)*5) 5) % 32)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffc1ffffff81fc1ffffff83ffffe47f1ff
  | 1 => 0xf07e0ffe0fc3fffe1fe1e0f07fc383ffba4e4f
  | 3 => 0xff800ffff003e1ffe001ff007ffc03c1c38f8c
  | 4 => 0xffffffc01fffffe00007ffffc01fc0ff0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x10040044008000002002211108048844009095
  | 1 => 0x25189488650550960d20c8a2324112b89a464a
  | 3 => 0x432dad14a3aa93aae3117a855ea82b0dc38b8c
  | 4 => 0xa514a214a20c54d56541008653270116c0d60
  | 5 => 0x8c618c398c3319f19b999cce06204221f76000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1300005c0000078614000008004009aa1c00e0024a450030955af5cb489b063508b008c82440011163400007500020000013802a740000c000191e7c00000b02880000480000000001001820002201810420006ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32ef32fe32fd32fc32ec32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x120f43806151a02a6a048008e17000000000001f4c2001307c444e3d000f23e26a0000632e14066322b800407c2f9c80e033a8010470000b0006713858e6520f178681400108000028800fc053f840c8382b1109e2b1b800a8122d1981a00001a41c0012800004516884828300000ee7100008c40c000008665001d8ba850516c6c843a08d021a3d9bc5000298b836002c8fcd8191d82c9058258c4800f041b85201179b47455261280000180d400110000072000e92400780018000181e010000009800d600230441c00000000000400041c10301024200800340000040800000408003010140014383c14080020080c1c0802dca5a1db54b43bb28e877551d0edea4a1db14943b7290876d5210edaa9215b94e42b728c856d5090b5ea8a15b14d42d7a1a85ad4350ad8a2a15bd4142b7290856f54ccadaa9995b94732b6a86656e528ca7ca8194f55032b7aa065ae540cadaa8196b5503296aa0656e530cb9ca6195b94432b6a80655e53d06baa7a0db94b41b6a9683ad42d06dea4a0db14941d6a12836e52106daa420cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518dbd4931b629263d5310c6dea910db55221b729c436c53886dca310db542219f2a0433d54086dea810eb95021b6aa043ad540865aa810db94c21b6298436e51087cca210db54021b7296816d52d02dca5205b54a40d6a14815e53102baa6205b94840b6a9081ad42102eca2205d54440b7294616d528c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320b7aa641ae54c82daa9906b5532096aa6416e53c82d8a7905b94720b6a94416f54482daa8905b94d20b629a416c51483d6a0905b94820b7a96216c52c42dca5085b54a109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc9c000a2e780b0203098000a3a022202a100316698190014012000024009006004184a95874350b0c5350d429998754cca2d64947328bd9150cca2d6595032c354d42d06a461509418b590524c64e63d52218b592538862f64542218b596540862d6414c219a580530870d5350840c9509511022d6494a308b59053c824c635512099185544822d6414d208b590514822d64948208b59052c422d6494a10
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s3K5 (880+((h/16+packedAt s3K5 (768+(h % 16)*7) 7) % 82)*7) 7
  | 4 => packedAt s3K4 (3970+((h/44+packedAt s3K4 (3618+(h % 44)*8) 8) % 177)*9) 9
  | 3 => packedAt s3K3 (1036+((h/8+packedAt s3K3 (988+(h % 8)*6) 6) % 38)*6) 6
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffc1ffffff81fc1ffffff83ffffe47f1ff
  | 1 => 0xf07e0ffe0fc3fffe1fe1e0f07fc383ffba4e4f
  | 2 => 0xff800ffff003e1ffe001ff007ffc03c1c38f8c
  | 4 => 0xffffffc01fffffe00007ffffc01fc0ff0
  | 5 => 0xfffff000000001ffffffffff80000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10040044008000002002211108048844009095
  | 1 => 0x25189488650550960d20c8a2324112b89a464a
  | 2 => 0x432dad14a3aa93aae3117a855ea82b0dc38b8c
  | 4 => 0xa514a214a20c54d56541008653270116c0d60
  | 5 => 0x8c618c398c3319f19b999cce06204221f76000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeaaaaeaea8888eeeeaaaaeaea8888eeeeaaaaeaea8888eeeeaaaaeaea8888eeeeaaaaeaea8888eeeeaaaaeaea8888eeeeaaaaeaea8888eeeeaaaaeaea8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffff03e0ffff83c1fffffffc1c07ffe1ff33f
  | 1 => 0x3f83ffc00fffffc01e1e1f03fe007fff924c3f
  | 2 => 0xc003fffff07c1fffe01fe003ffff8781e38fcc
  | 3 => 0x3ffffff801fffffe00003fffff801fc0ff0
  | 5 => 0xfffc000000001ffffffffffc00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x50011801108000c0222211940450894049315
  | 1 => 0x8a67220da63319c30d0d1a22b20a5569924c2a
  | 2 => 0x9329449483412a5520174848d493060ca3854c
  | 3 => 0x2c528929081a54aa57401093292c60315c0ab0
  | 5 => 0x30630e31cc639f3399999ce030304441fb6000
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xfaaafaaaf888f888faaafaaaf888f888faaafaaaf888f888faaafaaaf888f888faaafaaaf888f888faaafaaaf888f888faaafaaaf888f888faaafaaaf888f888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa43f531487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30f7294616e528c2faa5187b54a30b6a94617e518c2faa3185f94230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c3bc6498770c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21f741843e883085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dd0410fa208217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0x1000000008000040040000101200800000004000020010000000080000000001001004004000000000000000200202000001000004018050080000280200000000000002006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832f7a1065ec420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a837f52506f8a4a0fdd0541df20a837f50507f6a0a0ded4141be28283f850506f0a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa0883b541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbcca21f6194437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb18
  | 2 => 0x4000000000000000000004e00062c49800000000001e60000000000000013c0015a3585100000000000000000000460000000000000005d0007b01999c1b68c516a2e3e40000000027c000f580000000000000000000000ab10e1dc000000008909084403e34c6c0000001b4fc86200000000223104000138c21dc0f0759040008c0998130c2154fa000000000000b7456000000a91000000005939a4f47a83f000684001fe00091c00073202170001dc0001a04502000029c000000001580000036600000000370300718001e02100011523a000af98300000028000422000000000180000000d0006ad1e83b0ae000000290000005f80046a0011e000000000cf00040a4689d0fc10a0002394e0be000ffa413b00000000028069837a2805a000000002aa000000f7000000121950000002418404c000000002fe2e0001d227e79c0000000000000000000000000000009100020f0004bc00000000000000000305750b00011000000000000000eb8001a800000000000000000003be000000b3084160881a508a014dd01a2d67245d0df000000181450d800000000000784000000ec000000b400082ce88000005ecd211400059c000000003b4898b200088875000000000000000000004a00000000000000000000000001e6000bb80014c62800000492668551a741200115154000000840ad0004483d06930c8f8e11242b046ce420d00065c000b90000000001202c0010b8c40000007e976000270e30000008c800000000000000af028331230352c2000ba8b10000000008c0005e400000000000000000fc24891000000001030003ee00000000000000000000000010d9c50ca1e05d8a00000006180037c4b0000001780011f85300030517a0143c0a04a800000000b8000000000001cf30a6d452220350000001b40560000010008c4c51b8000000011d8000000010d1c10007640000000000000000000000249c40000000000000000095800000000688000000002f1f01ec000000003763980000000000000000000000a7a390002380023600000000000000001108000001e4e61ce00000011896000000c68c73f606c000000005b40019107400000000372590ce94a48a4b43180824a1503200034674ced800000000e380000500000c0080800200000000000000000010040000180300600400003002014000010080040080000800800000002000000010000040080600000002802000000008030020040100300400000800004004008020020000080a00e0000180400800002002004000030000000000200000c00000000000004020020000000080100200000801000000000000000100700900800400800004000008000060000080300000401005004000008000040000100200000000000000000000000020000000300200402
  | 3 => 0x990001ac000000000860000012832600054182000000e51fa36e000000000000000000018c0000000017a3f84e8001ca000000003c40008615b000000000f92e8000ca06b1c012c000002a2334000000580006d16906410400000122438c7000000001098003dc00000000000000691621c800000000430000000170000012010d000000001ed3aa000339460b6000948003a88d00000012e000000000002840007d00027c000f14067bc33130302000b91f100000000000000000000002904b8839870001300c8512765cd060000000006b80000000000000312000628000000011988f000660000003f80000009e2b85bccf90f2b20004d800000920678e20005800000000000058000000000000390b4000b500029a1d00380005e70c000001aa68000000000840be8003f0000bd21d2540000000040e0000000000000000006000000d10000000001c0000000000000026c22c4190b1de0390f8000006481f000000000000000001ec5b000000000000003ac000ab18806e8280e1f52d80007f800006000930000000004807c00046400000000000df91c000000001b1486000d91f6000000000000005a0ab8004384247a14b42a6d8a11e93ca6301a0000004d0000111300006501d190848938810002d4e00fa0007a0000002f80007c2421ba000000000a4084a0a293e6000001370000000000000000000000000548000001926f000214134578001e400000038000000000d4800000000000000000080000004a000002042fc478001ea0000000001e0000000000036000000000080000de8ec1d0598432001d265800000354000c78000006b4001782060011d1e00003c8000ae0008380014c2148b06f23800051c0000000047ccc9ae3fa0000000913239c000ac0000003a80007a418000002e278c00000000000b1a250000009a8001465944480a22c0000000001600000123204000001d00c00000000020a128e58000006bc3882a000000000000000006c80000000000000000000000000000000000000050c00000000000000000001a80000017c000000000001fca819001e0000001014a384001dd1a00000000005c3386e13c404898468000004e0000003b43ec000000005b800000000480a98a20001b80004d3bc0011380033600000000432000000cb4100540007200000000000000000000000620880003622e60000111000004000002924e400000000000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x541502b86050540dc14740503345190140d394e521034d5394840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440dc181511023d6590440cd54641103355110440cd547401023f6550040ad185401033551500409ed9540102f061500409d98754cc27561d5330b318943cc29d640cb30d354832cc2d5610cb30b318931cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c36a6094a30d394b308c26f62551309b189544c27761551309d185544c25c6550d30b3189434c29d640c930b5584324c2da600c930b3189314c2ce628c1309798c540c26e62150309b588540c27661150309d584540c25f654c0309ed95300c27661d53209d58754c823e6414f208f59053c82766114f209d58453c82cc6350b20ab59032c834d530cb20b958432c82cc63487209798f548825d63d52209798c548825d63152209d98454882756115220d6982538835a534c220d394f208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534826c6550920b318d424826e65cc920ab590324834d530c920b958432482ea600c920b318d21482ea628c1209e19530483c8324c120b398e204825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f59053082766114c209d584530827a6014c209798e500825d63940209bd95200827b65480209bd8953c426c6254f1097d8d52c425c6354b10cd15141c42f06050710ec50740c42f16110310ec90440c425e63152109758c548426e62152109b588548426e62d4e109b58b538425e63d4a109758f528433754106108f992544427761551109ed81544423e6515110cd584544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d52442766590510cd15241442746550510cd15141442f06050510ce153104433454841109798f540425d63d50109b98b540426d62d50108f59654043346155010ce181540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427565d0410cd55341042756510410cd550410433954d0010ecd0740042796510010ec104400433554c40109e59610042776544010ad191100433554440109ed9510042b86444010
  | 1 => 0xaa898700ea6207000291b6000000000000000248000009808274480007b8360008245aa04ea7220000000000010400000391de609d83101000252650001da684f918ab800171562ba98909a47d14492a0c078b20000031800340060000a00005054030200b01c03000030280601405044000140100000004040040001c010000201001000020700005c01014150140001000000030000001c00010010000100c010102a01000000000040101c01000000040700c000440300c0301801018060000000400000000080a02402004010000008c0600402000080080d008000040501401008040a4000940f00c08000050000000005008070066e62942439b58a5090f4f43149438fd954310e5f6550c43b31894310eac6250f429798e5090a5d6394242c714f4350b4c53d09428fd954210a6f6550842b318d4210a7661951329d586544ca5f63551329bd89544ca7661d50329d587540ca7a60d50329e583540ca3d6595032c718d540cb2c62550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cacd6210c32cb553420cb8f43d08329b594420cacd6310832b358e320ca5f654c8329bd95320cacf654c832d3d95320cace644c832b3191320cb8e544c832e3551320cacc614c832b3d81320cb365494432cd552510cbc53294432cd951510cb355454432f14c9510cb3a5494032ce552500cbc93294032dc946500cb715194032ce951500cb395454032f24c9500cb725154032dc545500ca5e63141419758c505066e62141419b588505075a6314141d658c505076a6214141da58850507734114141ce904505066f6254c419b189531065f63548419718d52106b564904418fd9541106b860504419dd9541106f06050441add9541107376550441ecd8141106b46050441ec18141106b06050441cd505501067a60d53319e58354cc66e62943319b58a50cc66e62d52319b58b548c6d5610ca319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d9584524c74c528c5319b988540c66d62150319e980540c6796015031d3548320c65f654c431b3189310c677654c4319e98354c867960d53218f99053c863d6414f219e98053c86796014f219798e50c865d63943219798f548865d63d52218f993538863d64d4e21d3d4c32886e5610ca21f10ca31886e4624c6219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d219799453487556114d21d514e3148674654c521d314e214865e63150219758c540867a60150219e580540863e6414c218f59053086766114c219e98053086796014c219b594320874d530c8219bd9521086cc63484219dd95210866f6254f409b18953d025f6354b409718d52d02b860507408f997415033451d0540cd14
  | 2 => 0x59ab67198c0026e001644e00081a8a3fa164c280849f221800000000000000000010007c0d2000004a00c5d800748e8330a270090a128e780ea000ac000000017c00000001c800000000c20017200000902b2b79b872856a229c3e1a23580000188000000012a0016e9da54b4800001dc00230002bc0a800938f66f8483c2ce2581400000000008a1e66ba7e571424886e9eaaa3b0d46c0b817a0819ac46025883888239ac128f45e8941d1bc922ba9717056950b0a1cb1aea329406599c1a23200178000280000000000000003c9a61600010800000a0522cc000000000000000002b827800382200000000000640000000a3ba70002a600000a083208a900002410218551e4002d41e0000009aa5000002a49420a418baa324c002f48b00000000002383f0b4b011a001f68d8001f9fe9683e7b00000000789d600002002600016a001faa6800a18302d800000005a07a6ea5e9b202442007323eb80007518e9e000a8a440026a649840022458000001f81888c7f1320212c3980070a3c00000000000000000296ab0008e80000264000509f00033a144491eb28b0228000499e8d0faac2c89992e710be549d0002b40003c00000018004090c8b9dabc0dab68d814908000002a02c37abe000161b1345b29e6a1988a94a5f8bc00000812a80000051974841261307200256000008682eb88466d136470000380000000b900016986b40000009c210002980013a926a95e302d81f100560c8180181910abc800b5adc0e000ba000680dc5386a7a84488aee589244f1ce438006c800000548780091aec450007a19a000006283409ae6068e253
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x4900018020f0073405452ce30008a51140001300048310b092826026338cc899065c15513254432e12a8992a01974132545500cb24b1ac4282838c5d46050441d24e63028220e91731814110751390c0a0883a85c86050441a1ce9a986510d0c7454c32482a238aa619241625d0324c120b82e219260906305418141c4258bb482206218c1506050510c60c2302a80853175d074004318b2882200210d1d95444010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x500c11755cc6050441c21755c86050441c81735c86050441
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
  | 2 => 3
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
  | 5 => packedAt s5K5 (17967+((h/195+packedAt s5K5 (15822+(h % 195)*11) 11) % 1244)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 550)*10) 10
  | 3 => packedAt s5K3 (1113+((h/7+packedAt s5K3 (1078+(h % 7)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf87ffff03e3ffe0f1e3f8ffff1c07ff831f33f
  | 1 => 0x7f83f8ffc03ffff01fc7f1c0fe007ff9ce4c3f
  | 2 => 0x7ffc00ffffc1f1ffe007fe00ffff8e060f8fcc
  | 3 => 0x800000fffffe01fffff80000fffff007f00ff0
  | 4 => 0xffffff00000001ffffffffff00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x9105011804420030208824650451250109315
  | 1 => 0x1228a1220c98c0700c431088a20a25a0c64c2a
  | 2 => 0x21093244940d02952005a412349308320b854c
  | 3 => 0x652c4892820652a56900024c92c40c5700ab0
  | 4 => 0x4463000e313189cc9926493800300107ad6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888feeaf888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x46900005cf95000c14a1d00100212460007860048082d8b1b78f458a10e200068000260008000010878c3e006af007073158d4d007e0191032e98004e814335a05d833c88000000000000000250c382020c10000040850002380850000001017fd4803fe52017f54803fc5200ff8c801fd3200ff0c805ff51017f94405fd51017f14401fe41007f50401fc4101ffcc401fe31007f4c407fc3100ffc8401fe21007f48403fc21017fd4005fe50017f54005fc5000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ffc4210027ee2108003fb1084017ffb2a200bbfd9510006feca880027f6544017ff32a2002bf9951005ffaca8802efd6544017fe32a2002bf1951005ef8ca8800a7c6544001ffb222000bfd91100077ec888002bf6444001ff3222000bf99110007fac888002fd6444001fe3222000bf1911000778c888002bc6444017ffaa2200bff9511005ffaa88802ffc5444001ffb1a2000bfd8d10057fcc68800efe6344001feb1a2000bf58d10057f8c68800efc6344017ffa9a200aff94d1005ffaa68802bfc5344001ffa1a200aff90d10007fa868802bfc4344001ffb122000bfd891004ffcc488006fe6244001feb122000bf5891004ff8c488006fc6244017ffa922009ff9491005ffaa488027fc5244001ffa122009ff90910007fa8488027fc4244015ff9922009ff8c910007fa6488027fc3244017ffa8a200bff9451005feca28802ffd5144017faa8a200bff14510007fe8288003fe4144001fb20a2000ff50510007ea8288003fc4144015ff98a2000ff8c510007fa628802bfc3144013ff90a2000ff88510007fa4288027fc2144017ffa822004ff9411005ffaa088013fc5044001ffa022004ff90110007fa808802bff3044009ff1822000ff4c110027f86088027ff2044009ff1022000ff48110027f84088003ff1044001fd8822004ff84110027ec2088013ff65040097fb282004ff99410015fcca080137e65040053f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010005fcc808013be64040015f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c80801fff540400fff2a02007ff5501003ff8a808013ff63040097fb182004ff98c1001dfcc608013de63040076f3182004ff58c10005fac608013dd63040016eb182004ff18c10025f8c60801fff530400dff2982007ff54c10037f8a608003ff430400dff2182000ff50c10037f88608013ff62040097fb102004ff9881000dfcc408013ee6204003773102004ff58810005fac408013ed620400176b102004ff18810025f8c40801fff520400bff2902007ff5481002ff8a408003ff420400bff2102000ff5081002ff8840801bff320400bff1902000ff4c81002ff86408022fe610400fffa882007ff9441003ffaa20801ffc5104001ffa082000fdd0410007fc8208003fd4104001fe2082000fd10410037fe6208003fe3104001fe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x7fd3248003fe1924001fb0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148025ffa8a4012ff94520097faa29004bfc5148001ffa0a4000ff90520007fa8290003fc4148023ff98a4000ff8c520007fa6290047fc3148003ff90a4001fbc852000ffc4290007fd2148001f690a4001ff0852000dfec09004bff5048009ff2824012ff54120027f8a090047ff3048009ff1824000fe8c120007fa6090003f93048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048011ffb2e2008bfd9710047fccb8800afe65c4011feb2e2008bf59710047f8cb8800afc65c4001ffb262000ff99310005fcc988003fd64c40017eb262000ff19310005f8c988023ff54c4011ff2a62008ff55310047f8a988003ff63c40017fb1e2010ff98f1001dfcc788003fd63c40017eb1e2010ff18f1001df8c788023ff53c4021ff29e2008ff54f10087f8a788003ff43c4021ff21e2000ff50f10087f88788003ff62c40017fb16200fff98b1000dfcc588003fd62c40017eb16200fff18b1000df8c588023ff52c401fff2962008ff54b1007ff8a588003ff42c401fff2162000ff50b1007ff88588043ff32c401fff1962000ff4cb1007ff86588023ff51c4011ff28e2008fd94710047faa388023f551c4011fe28e2000ffd0710007fc8388003f641c4001fea0e2000fd50710007f88388043ff31c4001ff18e2000ff4c710087f8638803fff21c4001ff10e2000ff4871007ff84388023ff50c4009ff2862008ff54310027f8a188003ff40c4021ff9862004ff8c310007fa6188013fc30c401fff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800afe6584009feb2c200ebf59610027f8cb08012fc6584009ffb242004bfd9210027fcc908002fe6484009feb242000bf59210027f8c90803bff548401dff2a4200eff55210077f8a908013ff63840097fb1c2004ff98e1001dfcc708013fd63840017eb1c2004ff18e10025f8c70803bff538401bff29c200eff54e1006ff8a708003ff438401bff21c2000ff50e1006ff88708013ff62840097fb142004ff98a1000dfcc508013fd62840017eb142004ff18a10025f8c50803bff5284019ff294200eff54a10067f8a508003ff4284019ff2142000ff50a10067f88508037ff3284019ff1942000ff4ca10067f8650802efd618401dffa8c200eff94610077faa30803bfc5184001ffa0c2000fdd0610007fc8308003fd4184001fe20c2000fd1061006ffe6308003fe3184001fe98c200dff0c610067fe4308003fe2184001fe90c200cff08610025fcc108013ff5084009ff2842004ff54210027f8a108013ff4084009ff2042004ffcc210027fc6108013fd3084009fe1842004ffc8210027fc4108013fd2084009fe1
  | 2 => 0x210b7f8ca9080afc6548401ffb224200bfd9121007fcc890802fe6448401feb224200bf59121007f8c890802fc644842dffaa24216ff951210b7faa89085bfc5448401ffb1a4200bfd8d21007bec690802df634842bff31a4203bf98d21007fac690802fd634842bfe31a4203bf18d21007b8c69080edc634842dffa9a4215ff94d210b7faa690857fc5348401ffa1a4215ff90d21007fa8690857fc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffd092100ffc8490807fd4248403fe2124201ffcc92100ffc6490807fd3248403fe1924201bfd85210b7fea29085bfe514842dfea8a4216ff14521007fe8290803fe4148401fea0a4200ff105210affe6290803fe3148401fb18a4200ff4c521007ea6290857fc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484097e3024216ffd41210b7fca09085bfd504842dfe2824215ffcc1210aff86090807ff2048403f79024201ff08121027fecb10012ff6588009ff32c4002bf99620027facb10052fd6588009fe32c4004bf19620027fec910013fe64880017f3244004ff59220005fac910013fc6488029ffaa44014ff952200a7faa910053fc5488009ffb1c4004bfd8e20027fcc71000efe6388009ef31c4003b798e20027fac710002fd6388009eeb1c4000b758e20027f8c710012fc6388029ffa9c4013ff94e200a7faa71004ffc5388001ffa1c4013ff90e20007fa871004ffc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944004ffd8620027fcc310002fe6188009feb0c4000bf58620027f8c310053ff5188029ff28c4014ff546200a7f8a310003ff4188001ff20c4000ff50620007f8831004fff3188001ff18c4000ff4c62009ff86310007ff2188003ff10c4001ff4862000ff84310012fe6088009ffa844004ff94220027faa110013fc5088009ff9844004ff8c220027f46110013fc3088009ff9044004fbc822000ff64110013fc2088009fc1044012ffd9520095feca9004bfe65480057f32a4012ff59520095faca9004bfc65480057e32a4000ffd9120005fec890003fe6448001feb224000ff19120005f8c89004bff5448025ff2a24012ff55120097f8a890003ff63480017fb1a4011ff98d2001dfcc690003fd63480017eb1a4011ff18d2001df8c69004bff5348023ff29a4012ff54d2008ff8a690003ff4348023ff21a4000ff50d2008ff88690012ff6248003ffa924001ff9492000fdca490007fd5248025f6a924001ff1492000ffe8490007fe4248003f72124001ff50920007da8490007fc4248003ff9924011fbcc92000ffc649000
  | 3 => 0xe21c6200ffd8a310dffcc518806fe628c401feb146200bf58a310dff8c518806fc628c439ffa94621bff94a310e7faa51886ffc528c401ffa14621bff90a310dff8851880fff328c407ff194621bf78ca3101ffa651880ffc328c407ee1946203bf986310e7fea318873fe518c439fea8c621cff14631007fe8318803fe418c401fea0c6200ff1063101ffe631880fdf318c407fb98c6203ff0c63101fe8631886fff218c437fe10c6200ffd8231007fcc118812fe608c401feb046200bf58231007f8c118873ff508c439ff284621cff542310e7f8a11880fff308c407fe184621bffc82310dff8411886bff654c4357fb2a621aff99531015fcca9886bfd654c4357eb2a621aff19531015f8ca98803ff644c4017fb226200ff99131007fac898803fc644c4017e322621affd51310d7fca89886bfd544c435fe2a26203bfd8d3101ffea69880ffe534c407fea9a6203ff14d3101ffc869880ffc434c401ffb126200bfd8931007dec498802ef624c433ff3126201bf98931007fac498867fc624c4037e3126200fb1893100dd8c49886bff524c433ff292621aff549310cff8a498803ff424c433ff2126200ff509310cff8849880fff324c407ff1926203ff4c93101ff8649880eff614c435ffa8a621aff945310d7faa29886bfc514c401ffa0a6200ff90531007fa8298803fc414c407ff98a6203fdcc53101ffc6298803de314c407fe18a6203f70c53101fe86298867ff214c433fe10a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c09886bff504c435ff282621aff541310d7f8a09880fff304c407ef9826203ff0c1310cffe4098867fc204c431ffb2c4218bfd96210c7fccb1080afe6588431feb2c4218bf596210c7f8cb1080afc6588401ffb244200bfd9221007fcc910802fe6488401feb244200bf59221007f8c910802fc6488431ffaa44218ff952210c7faa910863fc5488401ffb1c4200bfd8e210bffcc71080efe6388401feb1c4200bf58e210bff8c71080efc6388431ffa9c4217ff94e210c7faa71085ffc5388401ffa1c4217ff90e210bff88710806fd6288403ffa944201ff94a2100ffaa510807fc5288403ffa144201ff90a2100ffa8510807fc4288403ff9944217fbcca2100ffc6510807fd3288403fe1944201fb0ca2100dfcc310863ff5188431ff28c4218ff546210c7f8a310803ff4188401ff20c4200ff50621007f8831085fff3188401ff18c4200fd8c621007fa6310803f5318842ffe18c4201ffc862100fde4310807f72188403fe10c4201fd08621007fec110803fe60884097f3044200ff58221005fac110803fc6088431ffa844218ff942210c7faa110863fc508842fff9844217ff0c22100ffe4110807fc208842dffb2a4216bfd95210b7fcca9080afe654842dfeb2a4216bf595
  | 4 => 0x7fc324c803f61926401f30c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c84dffa8a6426ff94532137faa29909bfc514c807ff98a6403ff0c53200ffe4299007fc214c801ffb026400bfd8132007fcc099003fd604c801fe3026404bf18132137fea09909bfe504c84dfea826426ff1413200ffe4099007fc204c841ffb2c8220bfd9641107fccb2080afe6590441bf32c82029f99641107facb20882fd6590401beb2c82009f59641107f8cb2080afc65904457eb248220ffd5241107fca920883be5490441feaa48220ef55241107f8a920803ff639044bff31c8203bf98e41007fac720802fd639044bfe31c8203bf18e41107fea720897fe5390441fea9c8225ff14e4112ffc8720897fc4390401ffb148224ff98a4100dfcc520803fd62904017eb148224ff18a4100df8c520883ff5290449ff2948220ff54a41127f8a520893fe4290449fe2148225ffcca41127fc6520803fd3290449fe194821ebf98641107fea320883fe5190441fea8c8220ff14641007fe8320803f7419044bff98c8225ff0c641127fe4320893fc2190401ffb048200ff98241025fcc120803fd60904017eb048200ff18241107fea120883fe5090441fea848220ff1424112ffe6120897fc3090449ff9048224ff08241117fecaa088aff6550445ff32a8202bf99541117facaa088afd6550445fe32a8202bf19541007fec4a0802ff6250443ff3128201bf98941007fac4a0887fc62504037e3128222ffd494110ffca4a088bfd5250443fe2928221ff8c941007fa64a0887fc3250445ffa8a8222ff94541117faa2a088bfc5150401ff20a8200ef9054111ffe62a088ffc3150443ff90a8221ff08541007fec0a0802ff6050401ff3028200ff58141007f8c0a0812fc6050445ffa828222ff94141117faa0a088bfc5050443ff9028221ff081410f7feca2087aff651043dff3288202bf994410f7faca2087afd651043dfe3288202bf19441007fec420877fe62104037f3108200ff58841005fac420877fc62104037e310821effd48410effca42087bfd521043bfe290821dff8c841007fa6420877fc32104417f308821effd44410f7fca22087bf6511043dfea88821efd544410f7f8a220803fe4110401fb2088200ff50441007ea8220803b5411043fff988821fff0c4410effe4220877fc2110401ffb008200ff98041025fcc020803fd60104017eb008200ff180410f7fea02087bfe501043dfea80821eff140410effe4020877fc2010439ffb2c621cbfd96310e7fccb1880afe658c439feb2c621cbf596310e7f8cb1880afc658c401ffb246200ff99231005fcc918803fd648c4017eb246200ff192310e7fea918873fe548c439feaa4621cff1523101dfac71880fff538c407ff29c6203ff54e3101ff8a71880ffe438c407f
  | 5 => 0x17a0950928001b70234e100a8ce0114ee1da81957490a0001c280004dc000000000948ce80000012009100010e00021609e40000001c8000210000fb14d0000000001e413203400004c8000001328000001ec4000001629b30001488000000000000001940d91dad911f09b69ee0000001668981978df8a6df05a39e11510e29108af4b74a71d093817280000000000000006780000000000000000000000016000002780015c4000000000001a080d82400010919980002383f88aa2642f8000000d2888937164ce807896880017f0000060e78000001390000000900000000000da83800022d8000000000cb8002191b19f70670001771eb9611e5a18800000000222c1300000000001380000000000000009d11c9c761c8330d71159f3812223c000fa0d78000000000c6000000400000402402801400000000000000000001c00802400000c01800404400801000400c00405400800801800401c00002000003401000400000000000401c03000000000000802001400800000c04402000001001000001c00000800400400400400402000c00000c00c00800801400400400800000000800001400800c00000002400800401400000000400400002c02401000400001000000000400401401800001800000400c00001800400002401401402400400003000000000000c01400400000800001001000c00800002400002802800401800000000000400000c00401000c00801800400003400c01c00004800002c00405400000001400c00000801804000000000002000001400000800400800000c00000000400001c01800000400000000800001801801800000400400400000801400000800400000002000401403800c01000400400401c00800001c00001400401000400800400001801000000001400000000000000400c03400001006400400800000000001400c05000000800c00c00400800002800000003800401001001c00000400001000000000c00801400800000800400000400401000400000000000800801000000400400002400001403001000402800001401805000400c00001400000000002400400800000001c00000403400400400000400001000801004801400001c01401802000000400000400800400000000000c00800000400000401400800400000000800400c02801c00800800c00401400000c00800401400001000400c00400000001000401001800000002c00800403000000800000000c00000c00c00400800000001400400c02000000000001800000c00000000c00c00000000c01801c01801400000c0000000040040040280004dffb2a6426bfd9532137fcca9900afe654c84dfeb2a6426bf59532137f8ca9900afc654c8037fb126401ffd493200ffca499007fd524c803fe2926401ff8c93200fbc6499
  | 6 => 0x8da98001221dc9141ae9540f00650000b58eb1ae0000eb9e915d9cd50c1e980021b4000f31fa95e0000000000db9e840012312e80004880000000000000000000008114002280020f8001ef92a8000001fe00018f80000e88510b1acc001b48001648001f14000738e687300000010d0001822208000000d38a38001ce0000000000000000000000000001311ff800000000000000116127185e2c58d5638000184001ed19e88b0000a21d15300000a811e1b580016594700000000003d80007cc0000000000000022440382200011a8e980019f80000000000007351807ac000e608000018b0c80000000290001b900500000000000000000000000018f0000000000000ca00c1ead2c17b8ae51b8f51bf970800000000037000000000000000056a1f0d000000003a80000011b2180000000000000bcc0006485a80000000013f13e0001388000000118ec800071800000000163c0014d8000000000000fc8000000000d60031d8c600108000000b3221c0008180000009ba200561714000d51d899083a1ff58a00000003520a800012c000641dea111010000001ca8001d0c001529e28f59a500000947f810d0480007c4000000000001c500000009393391f8000000000000b20849098000001e7a040ad07a52815b0001ab80008e09412b10b40000009080ba071ea1a8024a1b1af1d655e9354000001f80a840000000001981d0299d80b100000000000005809f8e221b9c80ef98b89f1e30a5cea96c0001192210459ec1b296199b8000e8800000000057cf280000010f0720000000db00015d4001f1000000000000000000000175a080001899dd8000000001be0b715bde94000d997396f00000000000020318e8bf8000000ac0000280c88149e65ba8125678001fb8000001d59bd90703005780000000003b8d888f8000000ff80000000000001040000006c80000000000000004780000003d00000000000000000000000000000000000019d80022e8fe0000431030e09ab00017b1035b89e71589aa0cb0000000000000000000000b380820480005e86d87a0fd09e000000000101c00000071d2b83e40006c1308491ad92f0289e8c000f980015d1930cf8000000f48ad8699ce62bc1e1b222a94584703b16213780015f92507b4001a600020299008348b43680000012586457819a8001ca00005e0000ab800000070a068000001d50000000000000000000000000000000690000000001d48b08271d780000002f1ef52689600480019f0000000000000001c38150002020000001a78000000d20000002248c90000000000000000000000000000000001a00000000001c68349f780000000000001105106d22e00f00d006df2a1000000005a0d5a1a17a9fb08d1c20d40d19c7c9e92c8000e653d80002c04a81880a13d00000000000
  | 7 => 0xe08628cd97d87d15a19c87d94f97309a08785380000009dc000200001a89dc10fd0287c0450001569a68dc00000000000000000000000010182300017880009c0001368000e38000830e712919680023022f0000439810000000499960000001e88001cc1ad15c99c1e493481605320f0259d00a68e05831b81801f89ac0620a4a128a295b8821b00002050400dd1818001398000000000000001f90841d2cae8001c88a01871cedd30aa0be000187854a27a25dc91439670164a08000000001d4d2d80000000000000000000011200012080000000010c80000000000000000680000000000000015718d1da40000000005c4001b78000930388cca2a40000000000000000001780000022c1240000000540618010001ec82b1b500016521c01e8df18c1490ac4001eddbc96a14203c0002289c31fd82e0001eec0000000001598e1a720c80000000000020c0b80a30dc8001052259e81408085cd89781a8b78001f0dd75c60d6d615d6d080611298000e41dba121cfc758b50000dfc9d9f20f38cc4750d55af8000639c18b29d25ea80010e80019a00020000015f00004ea009de0001d29ff0c1052800086a271d18019fa0000a885d91d2254798a997404120e94944094780000000703ec000001da0000000000000001adc7e0000000000000cd1778000000b18000000000630002090000000000af0001ac40000022c8ec10945880000011d848450c00000058c0005d080986c000001f00000000000000000002224000000002060000001720000ae04d8bb17d18552380000000000000022699180000022801f8b00919d700000009a9f594c00000000013f888000000184a25000000217a290898000000000000000001dd00000000000000000018820780021400000022b8028100000000002158000000000000000000001009578bf1e503994410203e8fe8001d440000014b00018a93e8000668000000000bc1f30ea0000000780000000000fb80010b91984f0000000001ac8000c70001f40001460fc00000006b95c15a80017e00000019d198a1bdaa8059e9d22876847c7c8c984d1be8001151a40001e7db41e19519950ca96416f86612a1a49e20f11219f99058521521df8000000c480000000007280016d8000000000000ed1288000a107f1c980002a80014846b0c20000c596e0001c10001fe8001550000001530ba1ef00000000000002da28c002010001828a50250001ce8000000000000000001118bd032c001138ff0aaa0a1d38e913c1110558f603f08d8000000c380012e20382c8000001868001431170ccc000000000000ee8658000000020c78001ed5e69a90ac9d616b1580001bc1699ecc001bb88250416906f00021f80021190380017195582a0001061c40d5ce1c870e740013b80000000017620b1d1c000000bd855
  | 8 => 0xa660d8001d90000760000000000001089e74180001dbda588e9d85b38b91631920481cb04600001a0000440e00002139efd0d8001ba02696e99e00000007b8001d3ce300002e84b8be9eb0e50419178501ed85f8000969b114e960926000141a2b44206e22183207a94156617913740022adb61cb80000022d00000010680005c80000000002d21480012f8dd59800013a9591798000000000000fa8000ef14a8000000001330000001938001808001148000f222300016b8000000000002238000000001c480000000000000019b13589580016d00000020b8000001a31e0c5c1768c01508000001c09fc0000001861d9cb69cddcc8001548000000339b1c839ee8598208000000449210a418500005908c800000000000145226c0b00000000021300000000006a8000cf03e00008580001c21e80000013b18a4000000000000989d35560000000000000001f1c0fa2b116800131d1e9b083104a1f600000000013404b0140d49f68b41130000000000000b609b0d093047e8169c71710b48d811897440000000017f80000000006a1c78f688909c9cf92d0a61fd09905080003780000000018d8c09fc9538000a1a24d971cd11c0000000f78dd8000000000000000000001b98000f91318c280000002b80004f8001948000328000000000000001481d98000000518000000000404a7a0e0218ed80000008a5d10000000000000000000000001e05a28001500e58000000000000a5a1e00000020883596e588a1a9278000000000000000000001a1000a27c00000149a108000000000000000260baa1d91280000000000000014286080000022600000e00000000000000000000000000008f0000000000d300000000000011a16a8002229c00000001bd0002240129ee40ca1680006f8001db2170319cf20584fc000000000f820d0d10001c58000001bf0d68000000000000af9d69ea61522a0001700000000088390b89d7cde0bb8f182240007707b0790000000000000715d20000a90000f08000000000cc0000000429db40000000006889201f0000828740000da0000001929e3800000000074a2353600000020180000000000000011004680016c82add42214970ab00000013a0000001f18001df04c100124a274c40000000b640010780000000014e23080000000000000022f8680000000000c18001411bb2198041e6cc501b80015980016804e14c8000b985b985886183800049c0000018900013c8000000002221840f400003080000780000000014a0c318c9350f717c0bc99910f840c4751f05f17c80000648c0c6877800000000144a0988b80020340000000000014b8570f880000000005b229a2cd7e817229c711e0130d3cc0014f0001384998fd9a181b0000000804000de8000000090e48000099751a21e60000001
  | 9 => 0x8a000146a1d0001f480000006e80000000001900000000000000000010a80000000000000001d80003c9d94e19f5070036195800102490d0c510c0000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd63d041017eee62d0410006ed62d041015df576d0410006f576d0410004f576d04101777675d04100077575d041015ef765d041015f7665d0410176f565d041015f7565d04100067565d041015ef764d041015fb664d0410006f564d041015fb564d0410006b564d041015fd663d041015fd563d041015fe662d041015fe562d041015df770d041015df570d041015ef660d041015ff260d041015fb740d041015fb540d0410004ff7690410004fd769041003d7e75904100057d75904101067e65904100067d6590410006be6490410006bd649041012ede6390410006dd6390410126ee6290410006ed629041014df6719041016ef66190410025fa7090410005f97090410004ff76504101167e65504100067d6550410006be6450410006bd645041011ede6350410006dd635041010eee6250410006ed6250410166f66150410004ff7610410024fe7610410004fd7610410024fc76104100f67e65104100067d6510410006be6410410006bd64104100fede6310410006dd63104100eeee6210410006ed6210410007b54110410025fa7010410005f9701041014df57610410006f57610410004f5761041014ef7651041014f766510410156f5651041014f75651041000675651041015df67410410007b6741041014ef7641041014fb66410410006f5641041014fb56410410006b56410410157b65410410157b5541041014fd6631041014fd5631041014fe6621041014fe5621041014df7701041014ff2701041014df57010410007f1701041014ef6601041014ff2601041014fb6401041014fb44010410084ff768c410024fe768c41001cfd768c410024fc768c4100e67e658c4100067d658c410006be648c410006bd648c41001ede638c410006dd638c4100deee628c410006ed628c410025fa708c410005f9708c410084ff764c4100d67e654c4100067d654c410006be644c410006bd644c41001ede634c410006dd634c410005ef724c41002dec724c4100ceee624c410006ed624c41007cff7688410024fe768841000cfd7688410024fc76884100c67e65884100067d6588410006be6488410006bd64884100bede6388410006dd638841000eee6288410006ed6288410025fa7088410005f9708841007cff76484100b67e65484100067d6548410006be6448410006bd6448410005df7348410035dc73484100aede6348410006dd634841000eee6248410006ed6248410025fb7644010006fb7644010004fb76440100077b75440101477875440100277a6544010027796544010007bb7444010007b87444010027ba6444010027b96444010027da6344010027d96344010027ea6244010027e96244010025fb7144010027f3714401013efa6144010027f26144010007f23144010007f13144010007f22144010007f12144010
  | 1 => 0x8c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff76d0c10024fe76d0c10004fd76d0c101ce7e65d0c100067d65d0c10006be64d0c10006bd64d0c1001ede63d0c10006dd63d0c101c6ee62d0c10004ff7650c10024fe7650c10004fd7650c10024fc7650c101be7e6550c100067d6550c10006be6450c10006bd6450c1001ede6350c10006dd6350c10005ef7250c1002dec7250c101b6ee6250c10005f77150c10005f47150c10004ff7558810014fe7558810004fd7558810014fc7558810004ff7458810004fc7458810004ff735881001cfe735881001cfc7358810026ef7258810006ef525881002eee5258810006ed525881002eec525881002eee425881002eec4258810006ef325881002eee325881002eec325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026ee1058810026ed1058810026ec1058810004ff76d0810024fe76d0810004fd76d0810024fc76d08101ae7e65d08100067d65d0810006be64d0810006bd64d08101a6de63d0810006dd63d081000eee62d0810006ed62d0810004ff7650810024fe7650810004fd7650810024fc765081019e7e65508100067d6550810006be6450810006bd6450810005df7350810035dc7350810196de6350810006dd635081000eee6250810006ed6250810005f77150810005f47150810004ff764c810024fe764c810004fd764c810024fc764c8101367e654c8100067d654c810006be644c810006bd644c81001ede634c810006dd634c81000eee624c810006ed624c81002fcc324c810004fd76d041003d7e75d04100057d75d041018e7e65d04100067d65d0410006be64d0410006bd64d0410186de63d0410006d
  | 2 => 0x6bc2199010026bf7099010026be7099010026bd7099010026bc7099010026bf5099010026be5099010026bd5099010026bc5099010026bf3099010026be3099010026bd3099010026bc3099010026bf2099010026be2099010026bd2099010026bc2099010026bf1099010026be1099010026bd1099010026bc1099010004ff7559010014fe7559010004fd7559010014fc7559010026bf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff735901001cfe735901001cfc7359010006be4359010006bc4359010004ff725901000cfe725901000cfc7259010006be4259010006bc425901017cff715901010cfd7159010006f47159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010026f71059010026f51059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bc3259010006be7159010006bc7159010006b47159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006bc3159010006bf2159010006bc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026b71059010026be1059010026bd1059010026b51059010026bc1059010004ff7558c10014fe7558c10004fd7558c10014fc7558c10004ff7458c10004fc7458c10026df7358c10006df5358c10036de5358c10006dd5358c10036dc5358c10036de4358c10036dc4358c10004ff7258c1000cfe7258c1000cfc7258c10036df3258c10006de3258c10036dc3258c1001cff7158c1001cfd7158c10034fc7158c10036dc3158c10024fe7058c10024fc7058c10026de3058c10026dc3058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10036df7158c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df2158c10006dc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de505
  | 3 => 0xc76485100067f65485100b67c6548510006bf6448510006bc6448510005df7348510055dc7348510006ef624851000eec6248510005fb7048510025f87048510004fe76d01100067f65d01101ee7c65d0110006bf64d0110006bc64d0110005f671d0110005f571d0110007b541d0110004fd7650110004fc76501100067f65501101e67c6550110005f77150110005f47150110007b5415011001cff764c110054fd764c11001cfc764c1100067f654c1101de7c654c110006bf644c110006bc644c110006df634c11001edc634c110005f7714c110005f4714c110027f0104c11000cff764811004cfd764811000cfc76481100067f65481100967c6548110006bf6448110006bc6448110006ef624811000eec6248110005f77148110005f47148110027f010481100067f65c41100467c65c4110006bf64c4110006bc64c4110025f671c4110026f761c4110024fa76c41100077b65c41101d77865c4110007bb64c4110007b864c4110025fa71c4110026fb61c4110027f361c41101d7f251c41101d7f151c4110007f241c4110007f141c41100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067f32594100067e32594100067c325941003e7f71594100067e715941003e7d715941003e7c71594100067f31594100067c31594100067f21594100067c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267710594100267e10594100267d10594100267510594100267c1059410004ff7599010014fe7599010004fd7599010014fc7599010026be7499010006bf5499010006be5499010006bd5499010006bc549901001cfe7399010004fd739901001cfc7399010006be4399010006bc439901000cfe7299010004fd729901000cfc7299010006be4299010006bc4299010024fe7099010026be4099010026bc4099010006bf7599010006be7599010006bd7599010006bc7599010006bf7399010006be7399010006bd7399010006bc7399010006bf5399010006be5399010006bd5399010006bc5399010006bf7299010006be7299010006bd7299010006bc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bc3299010006be7199010006bc7199010006bf5199010006be5199010006bd5199010006bc5199010006bf3199010006bc3199010006bf2199010
  | 4 => 0x8910004fd75d8910014fc75d8910004fe74d8910004fd74d891001cfe73d8910004fd73d891001cfc73d8910006ef32d891004eec32d891000cfe71d8910024fd71d891000cfc71d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d89100057f755891005d7c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df7358910055dc735891004eec6258910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf7458910004fc7458910006bc7458910004bc7458910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc735891004cff7258910006ef7258910064ff7158910006f7715891007cff7058910006fb7058910004ff76d0910004fe76d0910004fd76d0910004fc76d09100067f65d09101ae7c65d0910006bf64d0910006bc64d0910005f671d0910005f571d0910004ff7650910004fe7650910004fd7650910004fc76509100067f655091019e7c6550910006bf6450910006bc6450910005df7350910055dc7350910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101367c654c910006bf644c910006bc644c91004fcc324c910024fe76d051005d7e75d05100057d75d05100067f65d051018e7c65d0510006bf64d0510006bc64d0510025fa70d0510005f970d0510004fe769051005d7e75905100057d75905100067f65905101067c6590510006bf6490510006bc6490510005f67690510006f67690510004f676905101f5f775905102177675905101f5f57590510007757590510005757590510007776590510217746590510205f57490510007b76490510006f66490510006f46490510007b46490510006b46490510217b65490510217b55490510025f67090510025f4709051020fb64090510024fc76505100067f65505101167c6550510006bf6450510006bc6450510005fb7050510025f87050510024f47650510205f77550510205f575505100077765505101ff746550510007b77450510007b76450510006f66450510006f46450510007b46450510006b46450510007f37050510025f67050510025f47050510007f07050510004fe76105100067f65105100f67c6510510006bf64105101f5f67110510007b5411051006cfe768c5100067f658c5100e67c658c510006bf648c510006bc648c510024fc764c5100067f654c5100d67c654c510006bf644c510006bc644c510006df634c51001edc634c510005ef724c51004dec724c510005fb704c510025f8704c510064fe76885100067f65885100c67c6588510006bf6488510006bc6488510024f
  | 5 => 0x4fd721911000cfc7219110006be4219110006bc42191100ecfc7119110006f65119110006f55119110024fe7019110024fc701911014ef6101911014ef41019110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006be6219110006bc6219110007b57119110007b65119110007b5511911014fb6101911014fb41019110006bf7519110006be7519110006bd7519110006bc7519110006bf7319110006be7319110006bd7319110006bc7319110006bf5319110006be5319110006bd5319110006bc5319110006bf7219110006be7219110006bd7219110006bc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bc321911014ebf7119110006bf5119110006be5119110006b65119110006bd5119110006b55119110006bc5119110006bf3119110006bc3119110006bf2119110006bc2119110006bf701911014ebe7019110006bd7019110006bf501911014ebe5019110006bd501911014ebc5019110006bf301911014ebe301911014ebc3019110006bf201911014ebe201911014ebc201911014ebe101911014eb61019110006bd101911014ebc101911014eb4101911001cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10056de63d8d10004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10004fe74d8d10004fd74d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10056dc32d8d1001cfe71d8d10024fd71d8d1001cfc71d8d10056df31d8d10054fd70d8d10056df30d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d10056dc6358d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d10004fc7458d10006bc7458d10004bc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1006cff7158d10006f77158d10084ff7058d10006fb7058d10004ff76d0d10004fe76d0d10004fd76d0d10004fc76d0d100067f65d0d101ce7c65d0d10006bf64d0d10006bc64d0d10005f671d0d10005f571d0d10004ff7650d10004fe7650d10004fc7650d100067f6550d101be7c6550d10006bf6450d10006bc6450d10005ef7250d1004dec7250d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d891004eee62d8910004ff75d8910014fe75d
  | 6 => 0xf71d951005e7e71d951005e7d71d951005e7c71d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d951021e7e70d951005e7d70d951021e7c70d951021e7e40d951021e7c40d95100067f30d951021e7e30d951021e7c30d95100067f20d951021e7e20d951021e7c20d951021e7e10d951005e7d10d951021e7c10d95100067f65d91100067c65d9110004ff75d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d911001cfe73d9110004fd73d911001cfc73d9110006be43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d911020fb771d9110007b651d9110007b551d911020fb610d911020fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bc32d911020ebf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d911020ebe70d9110006bd70d911020ebc70d9110006bf50d911020ebe50d9110006bd50d911020ebc50d9110006bf30d911020ebe30d911020ebc30d9110006bf20d911020ebe20d911020ebc20d911020ebe10d911020ebc10d911005d7e75991100057d75991100067f65991100067c6599110006bf6499110004ff7599110014fe75991100067e75991100147e7599110004fd75991100067d75991100047d7599110014fc759911001cfe7399110004fd739911001cfc739911000cfe7299110004fd729911000cfc7299110004fd7199110006f57199110006f65199110006f55199110006f9709911015ef610991100057f755911005d7c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110004ff725911000cfe725911000cfc7259110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c6519110006bd6419110004ff7519110014fe7519110004fd7519110014fc7519110006be7419110006bf5419110006be5419110006bd5419110006bc541911001cfe7319110004fd731911001cfc7319110006be4319110006bc431911000cfe7219110
  | 7 => 0x9210006bd5459210004ff735921001cfe735921001cfc7359210004ff725921000cfe725921000cfc7259210026be4059210026bc4059210026f71059210026f51059210004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e10004fc7458e10026df7358e1006ede5358e10006dd5358e1006ede4358e10004ff7258e1000cfe7258e1000cfc7258e10006de3258e1006edc3258e1006edf3158e10024fc7058e10026de3058e10026dc3058e10004ff76d0e10024fe76d0e10004fd76d0e10004ff7650e10004fd7650e10024fc7650e1001ede6350e10006dd6350e10005ef7250e10065ec7250e10005f77150e10005f47150e10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a10004fc7458a10004ff7358a1001cfe7358a1001cfc7358a10026ef7258a10066ee5258a10006ed5258a10066ee4258a10006ef3258a10066ec3258a10066ef2158a10024fc7058a10026ee2058a10026ec2058a10004ff76d0a10024fe76d0a10004fd76d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10005df7350a1006ddc7350a1000eee6250a10006ed6250a10005f77150a10005f47150a10004ff764ca10024fe764ca10004fd764ca10024fc764ca10067cc324ca100757e75d06100057d75d0610006be64d0610006bd64d0610025fa70d0610005f970d061022f7675d06100077575d061015ef765d061022ef565d061015fb664d0610006f564d061015fb564d061015ff270d061015df570d0610007f170d061015fb740d06100757e75906100057d759061020ebf6490610006be6450610006bd6450610005fb7050610025f87050610007b5411061014df57610610006f5761061014ef76510610226f56510610007b6741061014ef7641061014fb7641061014eb76410610006f5641061014fb46410610227b65410610227b5541061014df7701061014df5701061014fb64010610054fd768c61001cff764c610024fc764c61001ede634c610006dd634c610005ef724c610065ec724c610005fb704c610025f8704c61004cfd768861000cff7648610024fc7648610005df734861006ddc734861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c4210027f271c421005d7e76d951005e7e76d95100147e76d95100067e63d95100067c63d95100067e62d95100067c62d951021f7771d951005f7471d951021f7610d951021f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d951021e7
  | 8 => 0xcec7258f10024fc7158f10086dc3158f10086df3058f10004ff76d0f10004fe76d0f10004fd76d0f10005f671d0f10005f571d0f10004ff7650f10004fd7650f10004fc7650f10005ef7250f1007dec7250f1007eee62d8b10004ff75d8b10014fe75d8b10004fd75d8b10014fc75d8b10004fe74d8b10004fd74d8b1001cfe73d8b10004fd73d8b1001cfc73d8b1007cfd72d8b10006ef32d8b1007eec32d8b10006f671d8b1007eef21d8b10006f970d8b1000cff7658b10005df7358b10085dc7358b1007eec6258b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b10004fc7458b10004ff7358b10006df7358b10004df7358b1001cfe7358b1001cfc7358b10006dc7358b1001cdc7358b10006ef7258b10024fc7158b1007eec2158b1007eef2058b10004ff76d0b10004fe76d0b10004fd76d0b10004fc76d0b10005f671d0b10005f571d0b10004ff7650b10004fd7650b10004fc7650b10005df7350b10085dc7350b10004ff764cb10004fe764cb10004fd764cb10004fc764cb1007fcc324cb100457e75d07100057d75d0710024fd76907100457e75907100057d7590710006be6490710006bd6490710025fa7090710005f97090710024f5769071023df7759071016f76759071023df57590710007757590710005757590710006f66490710007b66490710007b56490710006f4649071016fb6549071016fb55490710025f67090710007f27090710007f17090710025f47090710005f77650710006f77650710235f77550710235f57550710007b77450710007b76450710006f66450710006f46450710007b46450710006b46450710025f67050710025f47050710024fd7610710006be6410710006bd6410710007b54110710025fa7010710005f97010710024fd768c71001ede638c710006dd638c710025fa708c710005f9708c710034ff764c710006df634c71001edc634c710005ef724c71007dec724c710024fd768871000eee6288710006ed6288710025fa7088710005f9708871002cff7648710005df7348710085dc7348710006ef624871000eec6248710005f671d0310005f571d0310007b541d031001cff764c31001cfc764c31001ede634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc764831000eee6248310006ed6248310005f77148310005f47148310004ff7599210014fe7599210004fd7599210014fc7599210026be7499210006be5499210006bd549921001cfe7399210004fd739921001cfc739921000cfe7299210004fd729921000cfc7299210024fe7099210026be4099210026bc4099210004ff75592100067f75592100047f7559210014fe7559210004fd7559210014fc75592100067c75592100147c7559210026bf7459210006be545
  | 9 => 0xc765052000dee7250520004fe7610520004fd7610520004fc7610520006bf6410520006bc641052000dee7210520005ed7210520006f76110520006f46110520007b54110520025fa7010520005f97010520004fe768c520004fd768c520004fc768c520006df638c52001edc638c52000dee728c520005ed728c5200dfcc328c520004ff764c520004fe764c520004fc764c520005ef724c52000dec724c520024ec764852026def754852026ded7548520005ef7448520005ed7448520007cf734852008dee734852008dec7348520007cc734852008dcc734852000def714852000fe77148520007e76148520006ec6148520007e46148520007e63148520007e53148520007eb7048520025ee7048520025ec7048520007e8704852000eef604852000feb6048520265fa768c120026fa768c120245f9738c12001efa638c12001ef8638c12000dfa728c120027ea728c12000dea728c120027e9728c120025f8728c120026fb628c120027eb628c120257ea528c12025fe9528c120257ea428c120007e9428c12008feb328c120257e8328c120257eb218c120007e9218c12000cfe764c120244fd764c12000cfc764c120005ef724c12000dec724c120247cc324c12001ef8764c12000cf8764c120007eb724c12000dfa724c12000df8724c120247e8724c120026fb624c120027eb624c120247ea524c12024fe9524c120247da324c120247e8324c120247c8324c12008fdb314c120007d9314c120247eb214c120007e9214c1200457e75d93100057d75d93100457e75993100057d7599310006bf6499310004ff7599310014fe75993100067e75993100147e7599310004fd75993100067d75993100047d7599310014fc759931001cfe7399310004fd739931001cfc739931000cfe7299310004fd729931000cfc7299310006f65199310006f5519931015ef6109931015ef41099310004ff7559310014fe7559310004fd7559310014fc7559310004ff735931001cfe735931001cfc7359310004ff725931000cfe725931000cfc7259310006bd6419310004ff7519310014fe7519310004fd7519310014fc751931000cfe7219310004fd721931000cfc7219310006f67119310006f65119310006f55119310006f97019310086de63d8f10004ff75d8f10014fe75d8f10004fd75d8f10014fc75d8f10004fe74d8f10004fd74d8f10084fd73d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006de32d8f10086dc32d8f10006f671d8f10086df31d8f10006f970d8f1001cff7658f10086dc6358f10005ef7258f1007dec7258f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f10004fc7458f10006df7358f10004ff7258f10006ef7258f10004ef7258f1000cfe7258f1000cfc7258f10006ec7258f10
  | 10 => 0x9120005df735912008ddc7359120005f77159120005f4715912028dfb70591200957e75191200057d7519120006bd6419120004ff7519120014fe75191200067e75191200147e7519120004fd75191200067d75191200047d7519120014fc751912001cfe7319120004fd731912001cfc7319120024fd7219120286bf4219120286ee4219120286bd4219120006ef3219120286ec3219120004fe7119120004fd711912001cfe76d8d2008ede63d8d2000dee72d8d20025ed72d8d2008fcf32d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004fe74d8d20004fd74d8d2008ede53d8d20006dd53d8d2008edc43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2008eed72d8d20024ed72d8d2000cfc72d8d20256df32d8d2008eef32d8d20256dd32d8d20256ec32d8d20004fe71d8d20004fd71d8d2008edc31d8d2000cfd70d8d2008edf30d8d2008edc6358d20247cc3258d2027dfb7058d20004ff7558d20014fe7558d20004fd7558d20014fc7558d20244ff7258d20006ef7258d20246de3258d20246ec3258d20246cc3258d20004ff7158d20004fc7158d2027cff7058d20006fb7058d20004fe76d0d20004fd76d0d20004fc76d0d20006df63d0d2001edc63d0d2000dee72d0d20005ed72d0d201c7cc32d0d20004ff7650d20004fe7650d20004fc7650d20005ef7250d2000dec7250d20024ec7650920275ef7550920275ed755092000def745092000faf7450920007af6450920006ec6450920007ac6450920007cf735092008dee735092008dec7350920007cc735092008dcc7350920007af4350920007ad4350920005ef7150920007eb7050920025ee7050920025ec7050920007e8705092000eef605092000feb6050920004ff75d8520014fe75d8520004fd75d8520014fc75d8520004fe74d8520004fd74d852001cfe73d8520004fd73d852001cfc73d8520024fd72d8520066f621d8520066f521d8520006f7619852004df970985200057f75585200957c7558520005bf7458520005bc7458520005df735852008ddc735852007dfb70585200957e75185200057d7518520006f56118520004ff7518520014fe75185200067e75185200147e7518520004fd75185200067d75185200047d7518520014fc7518520004fe7418520004fd741852001cfe7318520004fd731852001cfc7318520024fd7218520006ef321852002eec321852002eef211852002ef6211852002ef52118520004fe76d0520004fd76d0520004fc76d05200957e75d05200057d75d052000dee72d0520005ed72d0520006f761d0520006f461d0520004fe7690520004fd7690520004fc76905200957e75905200057d7590520006bf6490520006bc649052000dee7290520005ed7290520004ff7650520004fe7650520004f
  | 11 => 0x9edf3158e2009edc3158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e20246de7258e20246dd7258e20246dc7258e20246df5258e20246de5258e20246dd5258e20246dc5258e20246df4258e20246de4258e20246dd4258e20246dc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dd5158e20006dc5158e20246df2158e20246de2158e20246dd2158e20246dc2158e20026df7058e20026de7058e20026dc7058e20026df5058e20026de5058e20026dd5058e20026dc5058e20026df4058e20026de4058e20026dd4058e20026dc4058e20026df2058e20026de2058e20026dd2058e20026dc2058e20026df1058e20026de1058e20026dd1058e20026dc1058e20004ff76d0e20024fe76d0e20004fd76d0e2001ede63d0e20006dd63d0e20004ff7650e20004fd7650e20024fc7650e2001ede6350e20006dd6350e20005ef7250e2000dec7250e20004ff7598620014fe7598620004fd7598620014fc7598620004fe7498620004fd749862001cfe7398620004fd739862001cfc7398620026f67198620006f65198620006f5519862007ef6219862007ef52198620024fe7098620026f61098620026f41098620004ff7558620014fe7558620004fd7558620014fc7558620004ff7458620004fc7458620004ff735862001cfe735862001cfc7358620026f77158620006f65158620006f5515862004ef6215862004ef52158620024fc7058620026ef2058620026ed2058620026f61058620026f41058620004ff76d0620024fe76d0620004fd76d06200a57e75d06200057d75d0620006be64d0620006bd64d0620186de63d0620006dd63d0620004ff7690620024fe7690620004fd76906200a57e75906200057d759062012ede6390620006dd6390620006f66190620006f56190620004ff7650620004fd7650620024fc7650620006be6450620006bd645062011ede6350620006dd6350620006f66150620006f56150620004ff7610620024fe7610620004fd76106200fede6310620006dd6310620007b54110620025fa7010620005f97010620004ff768c620024fe768c620004fd768c62001ede638c620006dd638c620004ff764c620004fd764c620024fc764c62001ede634c620006dd634c620005ef724c62000dec724c620004ff75d9120014fe75d9120004fd75d9120014fc75d912001cfe73d9120004fd73d912001cfc73d9120024fd72d912029ebf42d912029ebd42d9120004fe71d9120004fd71d9120006bf6499120295f970991200057f75591200957c755
  | 12 => 0xe7650d21004fd7650d21004fc7650d21005ef7250d2100dec7250d2100cfe76d052100cfc76d05210b57e75d05210057d75d0521006bf64d0521006bc64d0521006df63d0521186dc63d052100dee72d0521005ed72d05210ecfe76905210b57e75905210057d7590521006df639052112edc6390521127e4219052117cff765052100cfe765052110cfd765052100cfc7650521006bf6450521006bc6450521006df635052111edc6350521005ef725052100dec725052110fe42150521124fe7610521006df63105210fedc6310521007b541105212acfe768c5210dedf638c52101edc638c5212adf6768c5212a6f6768c5210cdf5738c5210dfd7638c52101ef6638c52101ef4638c5210afd4638c52101ed4638c52100df6728c52100df4728c5210def7628c5210dfd6328c5210dfd4328c5210dfe7208c52101cff764c52100cfe764c5210ccfd764c52100cfc764c521006df634c52101edc634c521005ef724c52100dec724c52100df4764c52101ef4764c52100cf4764c5210ddf7734c521007d7734c521007d7634c52101ef6634c52101ef4634c5210afd4634c521007e7724c52100df6724c52100df4724c5210cfe4724c5210cef7624c5210afd7304c5210cfe7204c521007cf63885210beee63885210beec6388521007cc63885210becc638852100dee718852100fe6718852100eef618852100fe76188521007e63188521007e53188521005ed7088521006df63d8121006dc63d8121004ff75d8121014fe75d8121004fd75d8121014fc75d8121004fe74d8121004fd74d812101cfe73d8121004fd73d812101cfc73d812107efa20d81210adde7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581210b57c7558121005bf7458121005bc7458121005df73581210addc7358121006df6358121006dc6358121006df6318121006dc6318121026fa6018121006f96018121004ff7599220014fe7599220004fd7599220014fc7599220026be7499220006be5499220006bd549922001cfe7399220004fd739922001cfc739922028ebf429922028ebd4299220004fe7199220004fd7199220024fe7099220026be4099220026bc4099220004ff7559220014fe7559220004fd7559220014fc7559220026bf7459220006be5459220006bd5459220004ff735922001cfe735922001cfc7359220296bf4259220296bd4259220004ff7159220004fc7159220024fc7059220026be4059220026bc4059220026ef2059220026ed2059220004ff7558e20014fe7558e20004fd7558e20014fc7558e20004ff7458e20004fc7458e20026df7358e20006df5358e2009ede5358e20006dd5358e2009edc5358e2009ede4358e2009edc4358e20246df3258e20246dd3258e20004ff7158e20004fc7158e20
  | 13 => 0x9121024fe7099121004fd7099121005df73591210addc735912117df77159121004ff7559121014fe7559121004fd7559121014fc7559121006bf7459121004ff7359121006df7359121004df735912101cfe735912101cfc7359121006dc735912101cdc735912110cff7259121006ef725912117cff7159121006f77159121004ff7059121024fc705912110eef2059121124fe7619121006bd6419121004ff7519121014fe7519121004fd7519121014fc7519121006be7419121006be5419121006bd541912101cfe7319121004fd731912101cfc73191210ecff72191210ecfd72191210eebf42191210eebd4219121024fe7019121004fd701912101cfe76d8d210aede63d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21004fe74d8d21004fd74d8d21006df53d8d210aede53d8d21006dd53d8d210aedc53d8d210aede43d8d210aedc43d8d210dcff72d8d210dcfd72d8d210dedf32d8d210dedd32d8d2100cfd71d8d210aedf31d8d21024fe70d8d21004fd70d8d210aedf30d8d210aedc30d8d212adde76d8d2101cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210dfd771d8d210dfd721d8d210dfcc21d8d210dfd421d8d210dfcf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d210dedf72d8d210dede72d8d210dedd72d8d210dedc72d8d210dedf52d8d210dede52d8d210dedd52d8d210dedc52d8d210dedf42d8d210dede42d8d210dedd42d8d210dedc42d8d210dedf71d8d210aede71d8d210dedd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d210dedf21d8d210dede21d8d210dedc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d210dedf20d8d210dede20d8d210dedd20d8d210dedc20d8d210aedc6358d212b5f77158d21004ff7558d21014fe7558d21004fd7558d21014fc7558d21004ff7458d21004fc7458d210dcff7358d21006df7358d210ccff7258d21006ef7258d210bcef7258d212b4ff7158d21006f77158d21004ff7058d21024fc7058d210ddde7618d210aede7618d210dcde7618d210af5e7518d210af5d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d212aedf6218d212afd57118d212aedf6118d212afd72118d212afcc2118d212afd42118d212afcf2018d21004ff76d0d21004fe76d0d21004fd76d0d21004fc76d0d21006df63d0d2101edc63d0d21004f
  | 14 => 0x4fd74d8e210ccfd73d8e21006ed72d8e210beef32d8e210dede32d8e210dedc32d8e210deec32d8e210decc32d8e212acfe71d8e21006f671d8e21024fe70d8e21004fd70d8e2101cff7658e210bedc6358e2100dec7258e210bfcf3258e21004ff7558e21014fe7558e21004fd7558e21014fc7558e21004ff7458e21004fc7458e21006df7358e210bede5358e21006dd5358e210bedc4358e210beef7258e210cedf3258e210beef3258e210cedd3258e210ceec3258e2100cfc7158e210bedc3158e21004ff7058e21024fc7058e210bedf3058e21004fe76d0e21004fd76d0e21004fc76d0e2100dee72d0e21005ed72d0e211c7cc32d0e2110cfd76d06210c57e75d06210057d75d062100cff769062100cfd76906210c57e75906210057d7590621006be6490621006bd649062100dee7290621005ed729062117cff765062100cff761062100cfd7610621006be6410621006bd641062100dee7210621005ed7210621007b5411062100cff768c62101cfe768c62100cfd768c62101ede638c621006dd638c62100dee728c621005ed728c6210dfcc328c62100df5768c62101ef5768c62100cf5768c62101ef6638c6210bfd6638c621007d5638c62101ef4638c62100df6728c6210dfe6728c621007e5728c62100df4728c6210bfe7328c6210dfd6328c6210dfd4328c6210dfe4328c6210dfc4328c6212b4ff764c6210bdef724c62100dec724c6212b5f7764c6212bef7764c621007d7734c62101ef6634c62101ef4634c6210bfe7724c62100df6724c62100df4724c6210cfe4724c62100de4724c6210bfe7324c6210cfe4324c6210bfd7304c621006fb60982210057f75582210c57c7558221004ff75582210067f75582210047f7558221014fe7558221004fd7558221014fc75582210067c75582210147c7558221004ff7458221004fc7458221004ff735822101cfe735822101cfc7358221006ef325822104eec325822104eef215822104efa20582210c57e75182210057d7518221005be7418221005bd74182210bdde7318221005dd7318221026fa6018221006f96018221004ff75d9121014fe75d9121004fd75d9121014fc75d9121006be54d9121006bd54d912101cfe73d9121004fd73d912101cfc73d9121124ff72d9121124fd72d9121126bf42d9121126bd42d9121024fe70d9121004fd70d9121126ef20d91210b57e75991210057d7599121006bf64991210adde7399121005dd739912110df57199121004ff7599121014fe75991210067e75991210147e7599121004fd75991210067d75991210047d7599121014fc75991210ecfe749912101cfe7399121006de739912101cde7399121004fd7399121006dd7399121004dd739912101cfc739912117cfd7299121006ed729912110cfd7199121006f5719
  | 15 => 0xc6518931006ef6418931006ee6418931006ed6418931006ec64189310deef63189310cfe571189312b6ef61189312bfe731189312bfcc31189312bfe431189312bfcf3018931004fe76d0931004fd76d0931004fc76d0931006ef62d093100eec62d0931004fe7650931004fc7650931006ef625093100eec625093101cfe76d05310d57e75d05310057d75d0531006bf64d0531006bc64d053101dde73d0531005dd73d0531006ef62d053117eec62d05310fcfe76905310d57e75905310057d7590531006ef6290531126ec629053112fd4319053101cfc7650531006bf6450531006bc6450531005df735053101ddc7350531006ef625053110eec625053111fd4315053112cfe7610531006ef62105310eeec6210531007b54110531007cf628c5310dede628c5310dedc628c531007cc628c5310decc628c53101dde718c53101fd6718c53101edf618c53101fd7618c531005dd708c531006ef62d8131006ec62d8131004ff75d8131014fe75d8131004fd75d8131014fc75d8131004fe74d8131004fd74d813100cfe72d8131004fd72d813100cfc72d8131086fa30d81310cdee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f75581310d57c7558131005bf7458131005bc7458131005ef72581310cdec7258131006ef6258131006ec6258131006ef6218131006ec6218131026fa6018131006f960181310c57e75d92210057d75d92210bdde73d9221005dd73d92210edf671d9221004ff75d9221014fe75d92210067e75d92210147e75d9221004fd75d92210067d75d92210047d75d9221014fc75d922101cfe73d9221006de73d922101cde73d9221004fd73d9221006dd73d9221004dd73d922101cfc73d9221006ed72d92210ecfe71d9221006f671d9221024fe70d9221004fd70d922110cfd76992210c57e75992210057d7599221006bf6499221004ff7599221014fe75992210067e75992210147e7599221004fd75992210067d75992210047d7599221014fc759922101cfe7399221004fd739922101cfc739922117ebf429922117ebd4299221006ef329922117eec3299221024fe7099221004fd7099221004ff7559221014fe7559221004fd7559221014fc7559221006bf7459221004ff735922101cfe735922101cfc735922110ebf425922110ebd4259221004ff7059221024fc7059221006bd6419221125f67119221004ff7519221014fe7519221004fd7519221014fc751922117cfe7419221006be741922101cfe7319221004fd731922101cfc7319221006ed7219221006ef32192210eeec3219221124fe7119221006f67119221024fe7019221004fd70192210bede63d8e210dfcc32d8e212adf671d8e21004ff75d8e21014fe75d8e21004fd75d8e21014fc75d8e21004fe74d8e21
  | 16 => 0xa310dfcc32d0a3111cfd76d06310e57e75d06310057d75d063101cfd76906310e57e75906310057d7590631006be6490631006bd649063101dde7390631005dd7390631184ff765063101cfd7610631006be6410631006bd641063101dde7310631005dd7310631007b54110631006fb60982310057f75582310e57c7558231004ff75582310067f75582310047f7558231014fe7558231004fd7558231014fc75582310067c75582310147c7558231004ff7458231004fc7458231004ff725823100cfe725823100cfc7258231006de3258231056dc3258231056df3158231056fa30582310e57e75182310057d7518231005be7418231005bd74182310ddee7218231005ed7218231026fa6018231006f96018231004ff75d9131014fe75d9131004fd75d9131014fc75d9131006be54d9131006bd54d913112ebf43d913100cfe72d9131004fd72d913100cfc72d9131024fe70d9131004fd70d913112edf30d91310d57e75991310057d7599131006bf64991310cdee7299131005ed7299131005ef72591310cdec7259131006bd6419131004ff7519131014fe7519131004fd7519131014fc7519131006be5419131006bd54191310febd431913100cfe7219131004fd721913100cfc7219131024fe7019131004fd701913100cfe76d89310ceee62d8931004ff75d8931014fe75d8931004fd75d8931014fc75d8931004fe74d8931004fd74d8931006ef52d89310ceee52d8931006ed52d89310ceec52d89310ceee42d89310ceec42d89310ceee32d89310beed32d893101cfd71d89310ceef21d8931024fe70d8931004fd70d89310ceef20d89310ceec20d89310cdee76d893100cee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310bfe771d89310bfe731d89310bfcc31d89310bfe431d89310bfcf30d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d89310beef73d89310ceee73d89310beec73d89310beef53d89310beee53d89310beed53d89310beec53d89310beef43d89310beee43d89310beed43d89310beec43d89310beef71d89310ceee71d89310beed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d89310beef31d89310beee31d89310beec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d89310beef30d89310beee30d89310beed30d89310beec30d89310ceec62589312a5f771589310bdee76189310ceee76189310cf6e75189310cf6d7518931006ef6518931006ee6518931006ed6518931006e
  | 17 => 0x4ff764c841004fd764c841004fc764c84100eee624c841006ed624c8410efcc324c8410f57e75904410057d75904412edf775904412f77675904412edf575904410077575904410057575904412d5f574904412d5b574904412fef66490441007b664904412f7b654904412f7b5549044114df67090441004ff7650441005f77650441006f77650441004f776504412d5f775504412d5f575504412edf774504412e6f66450441007b664504412cfb754504412cfb654504412cfb554504412cfb454504412dfb643504412dfb443504412c7b642504412c7b4425044114df47050441007b77650441005b77650441006b776504412d7b775504412d5b775504412cfb675504412d7b575504412d5b575504412cfb475504412cfb765504412cfb665504412cfb565504412cfb46550441007b772504412c7b67250441007b572504412c7b47250441007b762504412c7b66250441007b562504412c7b462504412cfb752504412c7b652504412cfb552504412c7b452504412c7b63250441007b532504412c7b43250441007b77050441007b67050441007b57050441007b4705044114db470504412cfb750504412cfb650504412cfb550504412cfb450504412c7b720504412c7b42050441007b541d8041007b54198041006fb60980410057f75580410f57c7558041007b54158041004ff75580410067f75580410047f7558041014fe7558041004fd7558041014fc75580410067c75580410147c7558041004ff725804100cfe725804100cfc7258041006f65158041006f55158041006f64158041006f54158041006b54158041006fa5058041006f950580410f57e75180410057d75180410edee7218041005ed7218041007b54118041026fa6018041006f960180410e57e75d92310057d75d92310ddee72d9231005ed72d92310e57e75992310057d7599231006bf6499231004ff7599231014fe75992310067e75992310147e7599231004fd75992310067d75992310047d7599231014fc7599231186bd439923100cfe7299231004fd729923100cfc7299231006de3299231186dc3299231024fe7099231004fd7099231004ff7559231014fe7559231004fd7559231014fc755923111ebf4359231004ff725923100cfe725923100cfc7259231004ff7059231024fc7059231006bd64192310deee62d8a310dfcc32d8a312bdf671d8a3100cff7658a3101ddc7358a310deec6258a310dfce3258a31004ff7558a31014fe7558a31004fd7558a31014fc7558a31004ff7458a31004fc7458a310deee5258a31006ed5258a310deec4258a310dede3258a310deee3258a310aeed3258a310dedc3258a3101cfc7158a310deec2158a31004ff7058a31024fc7058a310deef2058a31004fe76d0a31004fd76d0a3100eee62d0a31006ed62d
  | 18 => 0xe63d8e41125ee72d8e41005ed72d8e4101cff7658e410067e6558e410067d6558e4112edc6358e41004ff7558e41014fe7558e41004fd7558e41014fc7558e4112ede4358e41004ff7258e4100cfe7258e4100cfc7258e41006de3258e4112edc3258e4112edc3158e41004ff7058e41024fc7058e4112edf3058e411057e75d8a410057d75d8a410067e65d8a410067d65d8a4112dde73d8a41005dd73d8a41126ee62d8a4100cff7658a410067e6558a410067d6558a41126ec6258a41004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a4101cfe7358a4101cfc7358a41126ee4258a41006ef3258a41126ec3258a41126ec2158a41004ff7058a41024fc7058a41126ef2058a41004ff764ca41004fd764ca41004fc764ca411367e654ca410067d654ca41127cc324ca4118e7e65d06410067d65d0641005f576d0641006f576d064130f7675d06410077575d064130ef765d064130f7665d064130ef565d06410077565d06410067565d064130fb654d064130fb554d064115ef660d06411057e75d82410057d75d82410067e65d82410067d65d82410067e65982410067d6598241006fb60982410067e65582410067d6558241004ff7558241014fe7558241004fd7558241014fc7558241006be5458241006bd5458241004ff735824101cfe735824101cfc7358241004ff725824100cfe725824100cfc7258241006bf41582411057e75182410057d75182410067e65182410067d651824112dde7318241005dd7318241125ee7218241005ed7218241026fa6018241006f9601824100cfe76d894110eee62d8941004ff75d8941014fe75d8941004fd75d8941014fc75d894101cfe73d8941004fd73d894101cfc73d894110eee42d8941006ef32d894110eec32d894110eef21d8941024fe70d8941004fd70d8941005df735894111ddc735894110eec6258941004ff764c941004fe764c941004fc764c94110fcc324c9411157e75905410057d75905413073e75905410073d7590541306bf6590541306bd6590541007b76190541005bd7090541004ff75d8141014fe75d8141004fd75d8141014fc75d814100cfe72d8141004fd72d814100cfc72d8141006fb50d8141006f850d8141006fb60981410057f75581411157c75581411157e75181410057d751814110dee7218141005ed721814115ef76118141026fa6018141006f960181410eeee62d884100cff7658841005df73588410fddc73588410eeec6258841004ff7558841014fe7558841004fd7558841014fc7558841004ff7358841006df7358841004df735884101cfe735884101cfc7358841006dc735884101cdc73588410eeee5258841006ed52588410eeec42588410eeee32588410eeec2158841004ff7058841024fc70588410eeef2058841
  | 19 => 0x1004800006c002005800002a00300e00300000230040008000002004800400000700d8000000009000000c000007003810403c0000060004038002007820412a00000880280060090000034006005006800803004001900b412600a000001800400300680e003600f005000000000700a000000200f000003000400000e000c0000030000000052021010803818000d02180080000010020000000009001000c008020000017400600000000040380100020004000003001000402600000e8024012000003000801a00a003803400000000080040000060058000008010000000000a006000800402e011000801800200b001804c0040040018008028011000000000600e0000100012009000000000000d0028024002000000001000001b00b800000a00100b8064042017006000400000500b800001800400200540080000000064000003032800800c0072b7cc32d8532004ff75d8532014fe75d8532004fd75d8532014fc75d8532004fe74d8532004fd74d853200cfd73d853201cfd72d85322a6f631d85322b6f621d8532024fe70d8532004fd70d85320dfcc3298532006f761985320cfcc32585321357e75185320057d75185322afcc3218532006f56118532004ff7518532014fe75185320067e75185320147e7518532004fd75185320067d75185320047d7518532014fc7518532004fe7418532004fd741853200cfd731853201cfd72185322beef32185322aede32185322aedc32185322aeec32185322aecc32185322bef531185322aef52118532024fe7018532004fd7018532024fe76d81321357e75d81320057d75d813227fcc32d8132004ff75d8132014fe75d81320067e75d81320147e75d8132004fd75d81320067d75d81320047d75d8132014fc75d813201cfd72d813227ede32d813227eec32d813227ecc32d8132004fe71d8132004fd71d813227efa20d8132257cc3298132006fb6098132247cc3258132267cc3218132026fa6018132006f960181321057f76596411067f76596410147f76596411073e74596410073d74596410067e63596410067c63596410067e62596410067c62596411067f74596411067e74596410067d74596411067c74596410067f73596410067e73596410067d73596410067c73596410067e43596410067c43596410067f72596410067e72596410067d72596410067c72596410067e42596410067c42596410067f32596410067e32596410067c32596411067f71596410067e71596411067d71596411067c71596411067e41596410067f31596410067c31596410067f21596410067c21596410067f70596410067e70596410067d70596410067c70596410067f30596410067c30596410067f20596410067c20596411057e75d8e410057d75d8e410067e65d8e410067d65d8e4112ed
  | 20 => 0x802c0450008058000018000000000600101c018c02402f00180000780050040004010005000002402e00600a0018092004005000001800000980000000060038130004000000800000e000000004c00000000000000080030000004000002003004403804f004000000000c030801002a000006800c0160040000010004000003005c010000001000400e003016801c000011002802001800100200140020030038000000017007803800001d00000c40000040058000010007000000003c000002001000000200d8060116023003001c000004001006400200202b801800c005000800000000200380000000010010014002000008001001a011001800000a005000001005600b00280140060060030004000007000801c000000000000800c0080268030000010004800800200600080c8012000000001801a001000800400e000003005c00200000100b00160020008004056000004001000e0060068030008005000800001c018000802403000100400000000030170078062000001002c0020b10000080002039006001c04000200081bc00000000000100240000030048002021000000c00000f00e801400c0070018000002069004000000800200b800401000000a80c401000300100000000020010014026016001800002a02000000000240010028018004004001800400c00001100080400170010000112002002800000000000a800000c00200080f000000203c0000006001007803c008015000001c00206a000001000000c0000054000000001812000c025013802800c097006800000e12b00980380000020050004000000005800402600000b0024010000002009002c00a000004000c0000220000000006012800c00e0020168000002004001801c03000201a00e005e03600200000020020008020002000002002400000c00b800003c01a0138008002027000807400400100000040040b9003801802a00000600100800c6000800000801202b00140000020030000000017007801000e0010050000000031007804002a00300180140f00010030014002003000810000800b000000000a0010028098010002007004000400000001100ba029006000802a00700f800400200000b003000000400b00500640000010000008005017000c008000008000000000f003803c032003015001800a000000806003e004000000c00e000001002400000301200140100000018020018008001000000000300180640ec017000805c00400c000002c000005000000c00000b01800040000040000050008000000807c0480020088008004000000000002c02c002800800e01c0018000006014011800000200000000000060060008038002000012000000e053000006403e003000000800200300600ec00600a0120004022003002000000200
  | 21 => 0x281b550b33acd7c31c3dd9f3125da9a04f0bf815ebfc295a324c84707471088b8de0682dda1e981647240e99434c09304b10b89388000000209473077833da2539c93504bad3fc142a99c2424c39087011d1ac900008186359fd066aba1cf32790f90b4d3d59758b204260003184f747ad2c9a76e2c369db718132cc1cc543121105eca5d493274d98059d4a1f285742b9d4049c1578fba362d800150e2f8adc96483d40a380021598ae57f3c52a994ee920000020002e52a056f188b6e5f515317fd48200035190640000004a6274009436a64784f97f76e11378aec8f637a06396d1906a072cd9b0c1bc8e845c223876263501e9c435f650d1b8a0c42e46f34a0add403a63d461acb49546fe1011afc8a20053e22c0d05556555203bc50a181443a8e87687bd049000141a000189a414000000060ab7d25f198627a569141041390896800800029e30c4b4c0003050e4c6f2cdd168800033cb97800232d442cd54d3a67d602a6d639000001d000002000000200600600040000088008000002004809800002e0000010000001007003c004004002001800400c0020018022001000002412800a005007c00402a0000090004001008001801200900a000400a003006000000e046001009c00400202a002402803b003001400c002000001400a0000138004006003004800000400100380140020240078034008004003801800c008000015001400000280d000000b00180100100010000000000058000005809000400280200000150018018034001000000005e001003000006200b0170008002000000001c00e005000800400400400082b800000b000001c00e01f0038000002002000800409a001000801009e0000018018014007000000400800400a8020000013016000400e0270098004000009001803000200400300080060000008014010005002800000a00000000300b2000001807400a0030008004000000005002800600d003001001000200000100020000000034016001005004c002021005004400200d008801403a006003001000e0250000004002004002815800c00400480180de039002800002c000000000800605d00600c00000020018010008000005801400c008006000401800001c011401200400080e00aa00100100ec0000000118020010002001800401e004000808400805800180280000030040034002019000000c00a001015003400200002880080080010030004000008000003c000002000002c00a00e006022000007a007000800402b0018008018000000000000400300380180000030038020000008014801000e001001000404c0020020024002004015802000000201b8014028000001000c0120320000000036003002000400600d00a0018006000001800400400a0020228002012000800400600e00000
  | 22 => 0xfa859ca2826e3d7094c0000a7000033516a80f16400001e2535b5e000078471337ca46570a6505a5000062bcce3c59664004b770002e48abcca634a21806e7c3805e0b6095eabc00007fa000b872b69ec40009605e6a2f1745000389d574f8200029781ed2d065d18ec1cc35cb7f28c8000dba34165c15893b1a1100000019bebe60eb1ea40000000000c29149af9000000000000058631c60004686089a4c0004884cf1d020000001bf9c207240002e12da04968cd16204c85a02db09521a456a9234a0c5b80000352a60000000bc6b9780011ae6c7680164400000000028ec0000000001e4408f90854a01f482b4cf18dca4a5132f753ea838778c360fea3a8640525332af16e2a2bf2469c487f022111120887021841d7a4449f6a783f98c616900e04521128e666301daa07993ac3f0d9a17133ad155e6266ce3682606930a8af070d5a3028c028aab0c42fd11682970cfa4c8d42cad37a439512c9ee06d40617626e430ba8f9460b9a05f9b04bb66acbb80add2948f449a03c93601543ad964a786d074b30374460bb3c158a2115ac7601bb0cc1c20c01ee00f851416106fac00ffebad0d4098d58818020c2c6965641d496a45164227500006298fc365cc003d114e72d0d7a91078e3941f098b93381690cb8dd0e7e2c0cd028f00001820d02e1027e00000000019dc0000001dd88aec2416f00391181d30cd29d4a5c56f00000900105823cb09e87d05ba57700e4d3f2c01558000b282d68d8b0810549ed37b89794980003cdaded9160006323150000000429000000000051f80009d8bf549c2e958680003dcd9bc5ac00c490a5620008cc34400a0c927141332cd00000003810000000bca252000079a257000237c2405245cc169c0000004e1abccd8000050db2259327b416c8cb8000068cacaca49fc87c2f819b01c849f5bc8504dd7065a199fe818c511db620d439e3690c7a6900585b50dc8e9ce7008467aa3802226f7a809f346930780559d252560ee185866cf8e06444084b91821c83ee970d4d0a9da859a0c1307042d62bd13844c107d25617823b23de4d7cfb670b1bb29cd62641f3a32cec27767c64d9b2c72a3101f1119c2866113e29cda90e3d85aac0002000a43f0187881c0b56888dbd1661c761d2d117aa69220bc0006ae37289a937551f000628ac15574634216b33c634c963a870f0562a74575b28d7564030e219a600026a06c0a40d66cf32eaa21e3fcbb30a8aa888eec7a000000000000014e30b8dd65221ba9aac3a82ef35310859de7d9000000075c65123e82b57891d70001df827237867465005f609c06e17f87d6a586388cc8000000516989cea4b970b88000d4a58b86509885705e20002fa940c0006648001a0c7f24af2d460009d2c2f817483103466125b97e5118287b460abe00046c1f9c32a60e0002a468
  | 23 => 0xfd66bdbc92dbcfd4404000000174700000023c135a7182e5f1fd3800e64f92d1249c0006090ef59f42c300029c86600003a084cb5b462619387e400090263d80019c000000019734d84482900000000000035800000000065b0000b2d6ec8000000c0cc4a346103d19c0300e820f09c277b000339552773250209555b694902982f886a5dc15b051000094460ba53d02055908427945688a7c6b2f948124ede131df167a6c640aadb984e558626a8629df000103800000097b0001aa10869220af2d94486ca23fc0fc800000052f1f0881abe72789ae2a044b503a2a598d85460f38794000bbb139165590a0360001d880000000000000000000542da00ca46ac0000619888b9b1338141624619e1240017c400000012b882600053da16c00083b000212800000027940000000002a799f917e57da9a9c70e2e00039386a4000d033918a8c00049300000000381912e212c939a5ed1b3000109a00042b8a18a6cacc00000000006f1afb89097785c12e459e4ac000015128b0aeab635c70000e51c2f0000000000c4158a82437da4290002cccf9c4e40002db4c766ae29d26e441a34457c26112c2124673517184237b309d8f0000a7e28500000006228002c340000003b403f0e2b0004ab4da0000b5654bc0002e6000458986800000048da61c0005e7093ac08eae000000023f27200027c00000000000ae0000000a5f0001ad4fc200000019150f65a34a0450000088a44e5fc4ef4000096a0e534ab811f02fdd2e276738f8000afc4fe800270e000a0a8698000000b9e3940000ca700042c08b4e764e00664000ffa00000013e400041e284c0018a000000033111880006249691110c0e3a22e087a8b58245209d86438f25e2d507d27293748b741ce5e1187ad8532a29b16718e517c9354428c5c9a21451eca1447de0250aa8a3c5cc5376400d794841aa03a82a05f46af0d4402405cb8327e29910eebf819517cd52e72446c8e71a0200038e80015ac0000002d5466ca6304aa52cb2981a52a2c8890a96c07b15b815837739aa7384507c0591a760f3000006a9b5c8f020b50f1168000c375f18d2e0004c63aa0e672a40003934bc16380005499ad83f092800000003d009a2e5893102c44765e9180a5051153e18ccc4823e097e430ace8a50001ef80004a1397120c0007453df82888568d20b60850a0117f368aa0f84d9d62a71c8864c0000002eb98d25aa331918c5f2bbd06b8cbd71020f664082400080e0000000f3e0000001178b1440561a85d80bba8b3902b240000004e2a2610381305e5ca6b7906ec1635b59a142e903c9b388b0059475a8fb79172a59c195d5328946291dbc8769d53c62ae04fa38062aa7d11007502d71bd08e6bccb160fe41641cc2000fb4a86797281a1b0a8a5d31f22924a2aa76343ab644f8a4f4d31c591e47cf4
  | 24 => 0x26050260003c328480007da35832ac75aac73d625707065f380000000eeb7a000072513e0003202624a7604d065ae8000099a00022452fc0004cb1edcc5e6a70000000000411330d12b56cbb211b2fc40ac8750000d6c00088650e40000007650000001a2c00000006240000000fb92480006bd26391c400000059cad626cd00022322a56f8a0126131d1558c1cd68016f266c46467ac2000081716e63286588d01476b94860a9c00000009a812133705f679c164525273000000003d4000374000515c0011647d20e8a850a6600027bb2fca591043fca54ca306efe0f00004645d00001a2d2f0c0957694010965215938000aa24363b4800000021c000000173100021c800106e0480474440f02c565019b1154e0000001e9948002f00000009b6a0519d8000273bc24f6000000000003627d800000048080018fa09401884acb9380c0000a1c00000000010707100540000ec13ceb6a00000006220002bb000000022466899e803eb4221a00013ba1055c59018dde9c91c112045c94fd2f88a3e3036f80000ccd2ba38d00010aa0008831d10e389c42cb000280000061c02188e53f000067800009e023f2e25718000000000000121c33d2718e103c49170000d9510428343fa000bec4e509e0c1d7be6150b7915a7ca6164119b68802d171f5128cc9c0d024c0c387f606e5048a1b8a767d1189c3e1f25eb0000ce860ca7f1610f3018831600001c4c0611d0002ea8bcca8304100004c000002d136400000064a93c80000e90000000fd06751dc8b240005ea1a7949929c0004b78d9e408000000077545c54d6012e707fe0d40dc226d7ba7591ea9cacbd2d19170914cbdcb8a07eab207b605e5fb072834807009e8c20ecc9f70001bf568795580007057814ee212977c0001232618f40000000000000000006136e3021760bb60001338ae8000576046c00082e0000f2825271e310979424abee65a1b9c000b5b37964001129135e7800180c56b42d1f547a675666c854c378c5f43b1590c629fa54a8754c47bc1d26a0a46e0d04353f3293561b60274298fdc9ba37f8d7af780005679800de2bc408523000000005fd0000712000000334887484538270a0aa6055472955977cce1311ab9c174c4e2cd1c0681886b497824f1fc3730000a95986ce80001bc2c4fc675630000d3258105485899f83550df00011ce6268000000000000000228400000000026ccd5a000000181565e80303b0131008b4784b2cdc00009d16bb3f4bb27e655e84e8cac000649334cc107d110015e944600008d2a5ba16bcb5228b90ec044f0f31aa863cbe408680000008e34e42f380000000eae9b921432b4be18979ee07a51aac240005630b2a64121674c5f85fdc0006f647b98d8680c585b32b5c66e25941a012d00cabb0001fb047a00009600000000000000000
  | 25 => 0x320643c0d3877123e0f73ca30ac8140000001d8ccc08f35190e856a62e3000264c55273465017f00000002a8000177478d052800021c34200027ac0001e92e4b088fc8bd75d123d80000002919e94f40757800338e57c8d13adc000720a6a00000000000002f62a799721d92c680012620c0d791c008625fa8481b78e1211f26fd264a8e3fd2f200010de59e000324da04503d5788bc0007a1416a6503f465b66a0e9400064fa46000148cac12249992000ced33f94c467876149d80009ef6b100031a0d70000127ac2c4c29360001e900009e22ce0000226000408ae9d3164d844680012da0005e299ac000af1149876d2120693e801937b825257f00003f600063e00019c45835d200000000002359e6400048e3389a4108c073e218b5111e0003690000000d1a0002ab80a20000000000f2a000301000025d0720002bfc00000000017e055ecc666081b47a48c74ff0614a2d4f8b8805ac5dcb3647e800000000062f287c5e806535019622b6731079ae586ceb901e283060b014d274800065a0000002645964000000000000000036c98307560000000000000c7ac3f00013be12864f00000c42f808084317d80004b5000167c7483b71fd49ea52e8d82f271aa6cd01697de000530010982cf6c950da619c1872295b7900d2480c5d30f80000000000000e5c00000064d2fac000000184c00060aaf600014fd608a890001f9448a229293862c9a636fba71e3f0e274b5b4a3ec0000002431b4d4a67933ba846a0009cb07c278cce6000111a9ac7bc3c6686ad898907df2e50000bba0002eb86584768fc4ee0904470c1b23f8581a3619957e0b379201da24000012306683da933038c39b81d978c0009753c128640000ced9610bc0000002d9923d15425f3125dd13825d86893420824c1d609aacd82c5c08001d3c68c4b851a32a186000023610b178c2110000f001a228100000404ca68d59924f59c864c11325cd97c9d20150281116cf4167b29161e6442cfa88155a269675129542e6675079bc082e1ac2094b1c18a170000043d2ca9e14c7a0294727dc0ab0f693d0681000272945e598000000173f6070110d8c0000001dd25900000002baeea400000000000012e97a32a928885aa6910000d4c00000000003a89580005d7800000000026dcd38ebcc530000000000cd0000091000021341f8000bf1ac0509c00011e00014fc36c850000000127131a8ac0000000c8600016e08b800000000012cd0d048b5c78000ad80003ac0c349ed09327ac00148641b0b5262834a00000024e8d9023c0000330000137000237905e00000015e709e0c957b8000b44b95622800176e4a03dc0bea7bec9460a000030121916280000006f51df2150d1e49b4c10000c5254966f018e4560000001e4a000000000000196e04f5fc8000eaa98555ba6d1728c59
  | 26 => 0xe000036800000045346cf7c2000561114116cae01e49d4400039b0586ee0e4a32403e1d1d4c204a8001a28b8e8424640362eb41bf472000100ec10046ed81806bfd25ca28b53a00000031cc00000000015c8000000000186d3d264d5c322b8e6c6041a9282f84620a31b91654ac17705f5d4d95ea915a006d15c40cf2e89f78000d1c393219d21a000643191c212c88000147081649a2e2a534cc878f5900172be8bb90fb1ae4e580003d9b2b8cd4a262151550000000222a6e022d35616900592aabfe3a5006c52a2f34a38000ee400013c0918e605a04da9961835a3db2e1df51b85e02bb5b6c2624a930795eb7923aa1668d16f6047e2c7ab78ad24952a2063851a97f1c6021442c55a07d8dc80704be2012bd47f88d455a1fc0e1e78738a41d63ea1de3e9b2b023c3f13b8af641164a7449265d700c65450108143a3f30000c11a3a30bcff9570e86314cf80651064c0154905a16bcab53231194ad4a6721c11110e65660a2c5d4566ac305b131122401300011b455ccaa483a3089206c562580c800000039b8000c941d80396f784346ca0284d6464691545800004f658966c20505d406a68a105867047a1cf18e00005d22b800004a071a1faab14b5e3092db000000061223a0d7045891600014c60a46d50001c44000000391ef6d1a600034d833913805b0001e416ec00060c2fc914c79c17946f400098e4d49aa47fc597265800093a8845e393412ac2806462c5852262536fae30cab00014c442d036acb00000015a814c58b94b4c1ace344ca52000000000021400000003b223c400052900000006dc0000000d899b400059d04bc284a6236817782fc4f34b1a50892ec1957d000101a0003cd2d5ccb200058cb43969c4bf1091d088468f527584199602eb203800069a0c7800217844e70643716c0ae60003a020154a0000189c000000000000000000009f45d9d752d360900000015e030c0c1ac796ad0c236a2d9c3e20005272a9527c5ad26b80003c6ba818db35909866100028acb9c63e4e8a0c000039f3f18000748b5c1de4000bb400022fa6f80006665f0000107c15a5128fd854089709d8320e2565bd6887fd1f0895b3a30a50244940001138d0c48230c800000093f1a5910468a2475cca56c698ce2b412fcc0000bd53dc00000000043ea0a000009900025a40000000000a48f4437cb7d0001978000057197b98e29b800241873400024b33e0a273119f1a95c1d05323cea8d88204e719097e48f83b810a97f580a00000005e4668b1d00025c19762e8019915860091d41b10b831846403756591de52c00032449a417b4f024688aa53d000188109c000124208450f35a376a36c8ea00014200000001a300000000000005cf57ecad034a61624a89ec988529224e000c4c5a3aa20c7e2066079fbcdccc7825eb06950cbb500022c
  | 27 => 0xef4501a256ea86027065f1c50db74b671aae409b0ba80030f5b42580ebb4c7c9966528a8c1b68a8400cc752df15058eb7c90be21e499095f2dfa0f49924e82df5f517f969c4f8a719410bfb21f05407ae9994bd327c6fc0ff0710a30f063f79a1a4b11da08e60f8000df657d29c85606a89f9194857573e677027eb614f22770002c440008af40c546c03414860a80017a21a130a2f0e3867fe4970d605349860afa28d9b60006318528be90000001e2151e04de4e0fb0000a6951980000000000000000000bd45d622aa0807739f300f00242e50001fb458236b156886c000000282ad489b89ae0002b8d25200015d00019f2000040b09600009b005333063a3d10a30000d4402600000005336e50301d340000000002e34000aa800012c52a22d31929f598f28da1c8990535e322000186118c38738625d000046e24882765215a120d2a1117aba4dffa1982329a100f1a796822a764b8000d0abef5e81ae80009ac55f211c2b29f34eb82ccccbaa30b31b300004ba50d0ce4aaec0a432000029e5cd0f6a71d808042570af60e1c5aac882d64d482bc50590fce728591fc4b7d9743992a42104af25773592b353de00000007c8a94a6f5bc008000093732a92a06c2442024703422c55518f80016b400000020216fc13350119780004d514f1fed7d262a34e99d8a960860a596a15d489d61da3b994e50b88901119b8c76a6289282b10004820000000000000001d7a62fd08ba994b163bf44806342048aee7dadac08e3b30c90001278c8a558000096c00000032080000000000000000351000086000000054280016140003c000000005cc44494d00009de11520e8a7c2ed55002dd048cfe37406acb876972830820b8f62b0ab89e433a9922c01a119ce5b214c8fb9520000046947ca8063a12eacf0f121d7d47049800052b94102206ba0155331adc28e77365889905482fe87f339e1ac2f243a09589943d66368f9c00090f164d889902d1343533c47525779248df058cb642be318136e6d816c4971a1e0492f91fd9462b5f287011516ec8e32a0b9ca193034ed1b80f5e0f51070708790b3f22e9aec716b3057423985ea73a33491886246badbe8a6117275f3168640a100b92890228e063482dc1ad14706625e16c1d6e44da25ba5e590e8ba0d9195243aba659321012e4bcaa6695ec2e8ce63eb9300380429d940950ee3a2712da005058a5c34a830d9ae9460ef89c45646e221bb03044aa515c996216ba1cb429884183757140c92ec55087825331b939e7ca1941a5873a8a867b343149f0bb61288cc20e408075a68c000802cab8eec032a3d470941c94400027531018ee00008a0af4000045a0a83b0cad7fc1650cfc29c6480f81c1aca63965382a08c263fa03f16ad35027f0a480fccaf1cd0f21474000d050d300010c658c00008046281c
  | 28 => 0x9da0005a180009cf70b80000000005171d00cf8f640006791b084b0066d92aed15c860140f8000122000000882236966d46e910c632b7047d2a014188202c38a74968bd63b69f2c9de4de5590a2430ead52c21148c50b0e256a50c1188554de9db17229578a929650702fc14733b00c62cc2fd064c74c2ff554a828206a9859882a937876a11a9968ce4504ade228868f6c94a826614900572b080e96e2651a5581bc5e2870041a726af93a80e94364a70a370f9ac601605104ec973d5a43c404b944ca8400b4c1912d5940274db1f600be9253d3acb852c2aa54d87f17e096754508307580b4101a8552fa5e84ea1874527ab904389ad4381224b587483dc78e1e78138ed60670bfdf184a2c9859511a8a1868914fb1a887a64edf1ef683e81ec61f0c086d824d4dd915159ca5a1458fd086477f08a71700cc8c54922fa18cc4d611a12c03762743e149d8d9e294bd4075342661028f08148dea7a1beae25786b352ce6bbd5fabd24f50cc417087203fac50b0a9451581bb89cc9aa6658b6843ca24659ab9843e426d882b4c69200d5dfab708ec02911b803d68a416bc28d913fa26d48f04d05585c002332a51d823a1c291845d8895652a24c000aa12d893a24e0c2d523b00163658e5d0521115668e27d24701da2e013f109d60c5040782194a3426865aa3a53649a242ead400b845b3d530f50160115a88fcab4a6782d491a58b45860e29cf47821630be92249c1abf6469ee4e3202b31900019fec424bb2dcc44019c0001e100000000f0a3fc0003f722600000009d3cb9626937e0004938c047ba4df4aa28a4e7c6fc08e06b54aa69f37516f4f3c360540808d3b698c34c2a7ca12c70325927988e833183df0c7961e03f4ad254e21360f7ad3c68e4f400002c4000a2a00000009e1b1f2202ba4cb50002ad80013f6ce940110890da47039e21858380e31db885c2daab1546a278000bc00db8454bdea104bb91982f07773f109cd99a64f3bc8e1876c8495a5a7f0d34aaa23ca92c8489b11f8145800044d3ae1c2862a2b96882dd02f4510cebd6
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc5e635d741040018dcc4bae820801e1fe1d65d04100043ec3acba082000c3e75993410400187aeb32682080030f9d564d04100061ebaac9a082000c5e7558f41040018baeab1e82080031b9d562d041000636baac5a082000c76755db41040018ed0abb682080031d61576d04100065b422eda08202bcb5845db410405796e80bb682080af2d50176d04100063abb2eba08202ea778759741040014eb0eb2e82080af1ddc165d041015e3ab82cba08202be37405974104057c6a80b2e82080038d9d564d04100071abaac9a08202bcb770593410405796ae0b26820800a1fa1776904100043ec2eed20820298f681dda41040050fd0abb482080021fe1975904100062f31aeb2082000c6e625d6410405b8ecc2bac82080021fe1d65904100043ec3acb2082029c7671596410400187ceb32482080030f5d664904100061f3aac92082000c3d7559241040018bceab1c8208003175d56390410006373aac52082000c6d7558a4104001972c8b8482080122f21376504100245ec22ec2082004c7a7059441040c556b02b208208013369c1631041002675382c42082000cb776504410400196aeca0882081678d99541104100071ab2a82208205be96635044104001d2ac6a088208163a9989411041000752b12822082000c79655c04104001974c8b8082080033658d701041000674b12e02082029ab5845d8410405396b08bb082080032d95176104100065aaa2ec2082029cb6405d8410405396880bb082080038da1165104100071ac22ca208202bc767459441040538eee0b2882080a79c9c1651041014e3ab82ca2082029e36405944104053c6880b288208002ad61a74104100065abb4e82082000b35859d04104001c6acb3a082080ae3de1d641041015e5b3a2c82082000ab787590410405796f0eb208208002ade1564104100055ac2ac82082029ab680590410405356900b2082080a72ddc1641041014e5ab82c82082000e71655c04104001b64e8b8082080033658d708c41000636392ca9882000cac729913104001958e4b226208003331c9634c4100cc76c36e49882000c6e65dc931040018dacbb9262080032b993724c41000656b26e49882017cce63dc9310400199ac7b9262080023ba1d624c41002c7643ac498820048ef8758a21040019d2c4b844208003171cd65484100064e39cc89082000c9c73591210402b1bb0db9a42080031799773484100062eb2ee69082000c9e64dcd210400193ac9b9a420806f3398b73484100046f43ac690820068dc8758d210400199ee6b124208003331cd62484100063c3aeec8802000c7b85dd910040018f10bbb220080032ee1376440100065c426ec8802000c7b76dd51004001976edba220080032edd874440100069c3a8e88802029db3711d110040017c70498a2008002f4e0d2144010
  | 1 => 0xb053aac608002b3e097458c1000566412e8b182000ad4815d163040014bd0a3a2c608002976147458c100056b40ea8b182000ad581d516304001c3ea92a2c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608003335c87258c100056b408e4b182006ad5811c963040095b500392c60801ab66007258c100046f43ea4b1820008dd87d4963040015ad03212c608002b56064258c100052f42884b182000a5d8510963040014bd0a38ac608002976147158c100054f426a2b182000a9d84d456304001caea328ac60800297a142158c100052ec2842b182004ada8008563040015b30010ac6080122f61e64d0c100246fc3ac7a1820018ec82dd943040011df04bb286080063b2097650c1000636392caa182000cac7299143040091790eb2286080032b1c96450c1000666392c6a1820008ed86dc943040018dccbb9286080031b5977250c1000657326e4a182000cad64dc9430406999cc7b9286080033358f7250c100063ab2ee2a182000cb564dc543040019aac7b8a86080023d6187150c100063ab28e2a182000cb5641c543040050fd0a3a2c4080021f61474588100247743ea4b102000ace83d49620400159b07a92c4080123b21d52588100247743e64b102000ace839d5620400159b073aac408002b3e0d74588100056641ae8b102000ae4815d162040014dd0a3a2c4080029b61474588100057340ea8b102000ae581d516204001c5ea92a2c4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408003335cc735881000573408e6b102005ae5811cd62040095d50039ac408016ba60073588100047743ea6b1020008ed87d4d6204001c9ea729ac408002b9a06435881000572c0c86b1020008ef8750d62040011d90ea1ac4080029ba14435881000536c2886b102000a6e851c562040014db0a38ac408002aba13515881000556c26a2b102000e675194562040014dd0a18ac4080029b61431588100257540062b102000ae9800c5620400917b0f32684080123be1d62d081001c6e41eeca1020008df835d942040071b906bb28408003171cd65508100064e39cc8a1020048bc875914204001938e6b2284080023761b73508100062f32ee6a102000c5d65dcd420400193cc9b9a84080032759373508101c667316e6a1020008de8758d42040011b90eb1a84080123b21d625081000667b9ac4a102000ccc7358942040018eacbb8a84080032d593715081000672b16e2a1020008f5861c542040018eaca38a84080032d59071508100246e41eec99020048ec82dd9320400199865bb26408003330c9764c81000726192ca9902000e8c329913204001d1864b2264080123721d634c81000d66412c699020048ec87589320400759906b12640800a1fa1576d041018c3fc32eba082000
  | 2 => 0xc32594100043ec3864b282000a3e840c9650400147b08192ca080029da0432594100053ac0864b282004a7a800c965040014f300192ca0818e9e60271594100043f43862b28200087d870c565040010fd0e10aca080021f61c21594100061fbaea93202000ab681d52640400917b0f2a4c80800b0f9d654990100245ec38a932020008ef825ce64040031d904b9cc8080122f61c43990100051f428873202000a3d8510e64040011bf06b94c80800e3720d72990100245ec38853202000a3e8510a640400147b0a214c8080030fdd675990100055b40ceb3202000ab5819d6640400155f04b9cc808002ab20973990100051f428e73202000a3d851ce640400155d05a9cc808002ab60b53990100070fa9ca73202000a9f835ca640400153906b94c8080028fa1472990100051ec28e53202000a9e83d4a640400153b07a94c8080022fa1c32990100045ec38653202000a3e850ca640400147b0a194c808002ada0432990100055ac08653202004aba800ca640400157300194c8080028fa1671990100051ec2ce332020008be87d46640400117b0fa8cc8080028fa1431990100051ec28633202000a3e85086640400147b0a10cc8080023d20575590100247c402eab2020048be87d51640400187eebaa2c808002ada0754590100161f3aca8b2020048bc87551640400156902aa2c8080122fa1e43590100055b40c86b202000a3e8510d640400147b0a21ac8080122fa1e42590100055b40c84b202000a3e85109640400147b0a212c8080030fdd675590100055b40ceab202000ab5819d5640400156f02baac808002ad20575590100055dc02eab202004ab8805d5640400156d0339ac808002ad606735901000557c12e6b202000aac825cd640400156902b9ac8080028fa1473590100051ec28e6b202000aae82d4d640400155b05a9ac80800387d4e53590100055b40ce4b202000ab5819c9640400153f06b92c808002a720d72590100055a40ae4b202000a3e851c9640400147b0a392c808002a7a0f52590100054ec1ea4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000ab6810c9640400156b02192c808012aea0032590100055cc0064b202000a3e859c5640400147b0b38ac8080032ddd471590100065aba8e2b202029cb6701c56404053968e038ac8080022fa1f51590100045ec3ea2b202000e375194564040095750028ac808002ae60051590100051f42862b202000a3d850c564040095750018ac808002ae60031590100051f42842b202000a3d8508564040095750010ac808002ae60021590100143f428e8b18200087d851d163040091bd0fa9ac60800317dd75358c1000567416a6b182000acd82d4d63040091b90ea9ac60801237a1e3258c100062fbaceab182000ace829d5630400159
  | 3 => 0xc992200087d85dd9324400117d09bb264880022f613764c91000666194ec992200087f855d932440050f90abb264880022fe11764c9100045e422ec99220008df835d932440011df04bb26488003330c8764c91000726196ca9922000e8c32d913244001d1864322648819a1f21975d051021c3fc3ecba0a200087d87d97414400187cebb2682880030f5d764d05100061f3a8c9a0a2000c3d751934144053974e0326828800a1f21676905101043e432eb20a200087f87d9641440170fb0fb2c82880030f9d764905100061ebaec920a2000c3e75192414400187aea32482880031d19676905100063b3aced20a2000c77859da41440018e90b3b482880a72de1276905100065b2a4ed20a2000cb5549da414405396c813b482880a72d10276905100063b3b2eb20a203e974865d641440012ef0fb2c82880031d9db65905100065b3b6c920a2000d3575d9241440018eaeb32482880031d5d4649051014e5b3b0c920a2000d35751924144001c6eca32482880038d19464905100065bba8c920a2000e3675192414400196aea32482880038d5d464905100061aba8c920a2029cb6701924144053968e032482881072e1c364505100063c32ee0a0a2043c7476d95414400156d0dba282881072d1db64505100047b438c8a0a2000e37651914144001c68ca3228288002ada1c64505100065b438c8a0a2000cb775191414400196aea32282881076cdd070505100071bb2a8220a2059e346550441440018d8e5b2a62880032b1cb644c51000656390c898a2000ccc72d8d31440018decbb9262880031b197724c51000657b26e498a2000cac64dc931440018b8e7b2a4288003271cf64485100064e398c890a2000c5f65dcd21440018b8cbb9a428800327d9373485100064e326e690a2000ccc73d8921440531ed0d38e80880025d61671d01100065a324e3a022000cb4645c740440095690ca0e80880021fe1576501100143e42aeca02200287c851d940440010fd0fb2a80880021f21f65501100063bb2ee2a022000c7465dc540440018eeca38a80880031d19471501100065bb20e2a022029cb4641c540440095690ca0a80880032d1d94150110025d840282a022000cb464dc530440012eb0a38a60880032d190714c1100065a326e29022000975851c52044001968c838a408810f1e9db65c411020e5d3b6c98822000e386519310440016e30b20e20880029da07745941003d3ac0ee8b282000c3f749d165040cb4ef02ba2ca080029d20574594103253dc02e8b282004a78805d165040014dd05b9aca080029b60b73594100062fb9ce6b282000a768190d65040014eb0321aca080021fa1c43594100043ec3886b282000a5e83dc965040014bb07b92ca080029da0642594100053ac0c84b28200087e8710965040010fb0e212ca080021fa1
  | 4 => 0x4440014790a880c88800a1fa1674d8d100043ec2ce9b1a200087e87d9563440018d8e5b2ac6880021fa1c6558d1000636390cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200287e87dd5634400117f08baac6880022f2117558d1000477c12eab1a20018ec825d563440010fd0e3aac6880030fdd77458d100061e3aee8b1a2000c3f751d16344001878ea3a2c6880063ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000cb474dc563440050fd0bbb686880021f61776d0d1000c77416eda1a20008ed82ddb43440010ff0abb6868800a1f21576d0d1001c5ec38c9a1a2000975859c74344001968c938e86880032d19171d0d100143f42eeca1a200087d85dd943440031dd053b286880023b60a7650d1000636396caa1a20038be87d914344001958e5b2286880032b1c86450d1000637b2ee4a1a2000c6c65dc9434400195ec9b9286880032b1937250d100143f42ce9b12200087d859d362440050fd0dbaac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac48800a1fa1f75589100045fc22eab1220008bc845d562440011bf06baac48800e3720d75589100043f438eab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220038de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c4880032d1d371589100143f42eeda12200087d85ddb42440071bd07bb684880023760f76d09100043fc2aeda12200287c855db424400317b0e32684880025d61671d09100065a324e3a122000cb4645c742440050fd0bbb284880021f617765091001c6f41ceca1220008dd839d942440010ff0abb2848800a1f21576509100045fc22eca1220008df835d942440071b906bb284880023de0576509100062e39ecaa1220018be87d914244001938e7b228488003271cc64509100062fb2ee6a122000c5c65dcd424400193ec9b9a84880032719373509100143f42ee
  | 5 => 0x80028f61443191100055ac08863222000ab98010c64440011bf06b90c88800e3720d72191100051f428843222000a3d85108644400156b02210c888002ae60042191100163b3aca23222000ab5849446444001c6ea9288c8880038d55251191100055bc22a23222000e36545446444001c68a8a88c8880030f9db651911033f1bc0eca3222067e3610d9464440cfc6821b28c8880022f61e65191100045fc3aca3222000c3e761946444001c6b02328c8881a38d84065191103471a080ca3222000a3e8598c644400147b0b318c8880028fa1662191100051ec2cc43222000e37655c46444001c68cab88c888002ada1a51191100071bb2ca23222000e346594464440535690ca88c8880038dd9551191100071a32aa23222000ab681dd4644405356b03ba8c8880030fdd675191100055b40cea3222000ab5819d4644400153d063a8c888002a760c751911000557410ea3222000aad821d4644400156d023a8c8880a6ad604751911014d5d400ea3222000ab9801d4644405356b03b98c888002abe09731911000556412e63222000a3e851cc644400147b0a398c888002aba08731911000556c10e63222000ab6811cc644405356b02398c8880a6aea0073191100055cc00e63222000aae82d4c644400155b05a98c888002ada0753191100055ac0ea63222000e1f5394c644400156d02298c888002ad604531911014d5ac0ee43222000a9f835c8644400153906b90c8880028fa1472191100051ec28e43222000a9e831c8644400153b06390c888002ada04721911014d5ac08e43222029aba801c8644400157300390c888002a7a0f52191100054ec1ea43222000ab681d48644400156b03a90c888002ada0452191100055ac08a432220008be870c8644400117b0e190c8880028fa1432191100051ec28643222000ab6810c8644400156b02190c8880a6aea0032191100055cc006432220298be87d44644400117b0fa88c888002ad61e51191100071b3aca23222000e3575944644405356d01288c8880a6ad202511911033f1b284a23222067e3450944644400157700a88c8880a6ae20151191100055bc3aa23222000e37855446444001c6eeaa88c8880038d1d551191100071ba9aa23222000e35535446444001c6ea4a88c8880038d549511911000759c02a23222029ab680544644405356900a88c888003ac20151191100071aa88a23222000a3e850c4644400147b0a188c8880028fa1421191100051ec28423222000a3f855c064440014790ab80c888002ada0750191100055ac0ea03222000e3551d40644400156f02a80c888002ad20550191100071aa8aa03222000a3e85cc0644400147b0b980c888002ada0730191100055ac0e603222000a3e85c80644400147b0b900c888002ada0720191100055ac0e403222000a3f854406
  | 6 => 0x247743e64b14200087f855db42840050f90abb685080021fe157650a100143e42aeca1420008df835d942840071b906bb28508003331cd6250a100143f42eec994200087d85dd9328400199865bb26508003330c9764ca100061ebacc9a0c2000c3d7559341840531ef0eb2683080029de1564d0610006b8baae1a0c2042c75615d6418405376100a0883080029de1576106100059ac2ce820c2029bb2809d041840014ef0ab208308003331c9634c6100066639ac490c2000a3e8498f654400147b0931eca880028fa1262d95100051ec24c5b2a2000a77815d365440174e902ba6ca880030f5d074d95101f53b408e9b2a2043a75811d365440014df04b9eca880029b20973d95100062eb98e7b2a200087e8710f65440010fb0e21eca8800297e0d72d95100052e41ae5b2a200087e8710b65440010fb0e216ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880029da0432d95100053ac0865b2a2043a7a800cb65440014f300196ca880021fa1c31d951005c3ec3863b2a200087e8708765440170fb0e10eca880a29da0770d95100043f43e61b2a200087d87cc365440010fd0f906ca880021f61f20d95100061ebaea9b222000ab581d536444005878eb2a6c88800a2fe1d54d91100051f42887b222000a3d8510f644400147d0a216c8880028f61442d91100071ac08cbb222000a3e8598f644400147b0b31ec8880028fa1662d91100051ec2cc5b222000e346594764440835690ca8ec8880030f5d475d91100055b408ebb222041ab5811d7644400155d05b9ec888002ab60b73d91100051f42ce7b222000a3d859cf644400155d05a9ec888002ab60b53d91100070fa9ca7b222000a9e83dcb644400153b07b96c8880028fa1672d91100051ec2ce5b222000a9e83d4b644400153b07a96c8880022fa1c32d91100045ec3865b222000a3e850cb644400147b0a196c888002ada0432d91100055ac0865b222041aba800cb644400157300196c8880028fe1571d91100051e42ae3b2220418be87d47644400117b0fa8ec8880028fa1431d91100051ec2863b222000a3e85087644400147b0a10ec8880028fa1770d91100051ec2ee1b222000a3e85cc3644400147b0b986c8880028fa1720d91100051ec2e41b222000c3e75d92644400187aebb24c88800b1d9d651991100147bc3aa3322200087e87d9564440010fd0e32ac8880023de0575591100047dc02eab222000c7775dc564440018e8ebb8ac8880031e1d770591103363ab88ca32220008bf87590644400147f0ab20c8880028f21564191100051f42ce83222000a3d859d0644400187eebaa0c888002ad60754191100145ec3ca83222002c3e75950644400156b032a0c888002ad604541911000477c12e632220018ec825cc644400147d0a218c88
  | 7 => 0xdc835d841480050fd0a3b082900021f614761052001c6f418ec20a40008dd831d8414800147b0a3208290002ad604641052000656322e420a40119cc835c841480014eb0a3088290002ad610611052000672b90c220a4000ab68650441480015690ca0882900063e2197010520006d8a0ae020a400087f855da31480050f90abb4629000a1fa14768c5200043ec28ed18a40018ec821d931480091d90cba242900467320d74485202ace743ee690a400f8ee871852148001998e630a4290047711ce314852000cf243a6290a4000ae4864c52148001b90e7b8242900027ae1d428c12008de441a8518240009eb8748630480237910690c6090122f2a0f724c120245e4412629824011bc8834853048001f826290a60900030f5d764993100163b3aca332620008bf8759064c40011bf06b90c98800e3720d72193100053ac2ce232620028f58794464c40058eceb288c988002ad61251193100071b2a2a2326200287e859d363c40010fb0b3a6c7880023be097558f1000c76412eab1e20018ee87dc963c400199ee6392c78800a1fa1776d0f100043ec2eeda1e20018ee82ddb43c40011db05bb6878800a1fa1676d0f100043ec2ceda1e2000975859c743c40011df04bb287880063b2097650f100143f42ce9b16200087d859d362c40011bf06baac58800e3720d7558b1001c6f43ee6b162000ccc73dc962c40050fd0bbb685880021f61776d0b1001c6f41eeda1620008dd83ddb42c40050fd0b3b685880021f61676d0b10004bac2ce3a1620008df835d942c40071b906bb28588003330ca764cb100046fc1aec99620008ef825d932c40050fd0a3b265880021f614764cb1000666190ec9962000a3d8599241c40018eaeb3248388002cd61664907100063aba8c920e2000d71755c241c40012eb0bbb28388002ec60364507100047b438c8a0e20009b68719141c400156d0e32283880032da1c64507100065bba8c8a0e2000cb57519141c4001d630032283880a72d9c0645071014e5a380c8a0e2000a3d8599041c4001b6282b80838806eb3209638c7100246f43ec698e2000ccc72d8d31c402f59906b1443880123ba1f62487100066639ec490e2000975859c740c40571ef0cb8e8188122b3209634c310004bac28e29862011acc8358920c40012eb0a38a41880122f61e54992100161f3aca932420008ef825ce64840031d904b9cc90800237e0d729921001c6e41ae5324200287e87dd564840d38ee21baac9081a71d44375592100161e3aca8b2420048bc8755164840050fd0a3a2c7080021f6147458e100246e43aa6b1c20048de878c963840010ff0abb6870800a1f21576d0e100043fc2aeca1c200287c855d943840011df04bb287080063b2097650e1000666392c6a1c200287e851d162840010fb0a3a2c5080123b21d5258a100
  | 8 => 0xc6a08829086f331cb634c5210be6631ee498a4203cd476dcd3148437b88e5b9a629086f351db634c5210ce723b6e498a4255ace86d8e214842fd88c718c4290806b921931885210bf6231a6310a4200ccc635c221484050fd0b3a6c0908021f61674d812101c6f41ce9b0242008dd839d360484371b90db9ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b024255cce7218c60484011f70eb00c0908122f61e54992200161f3aca9324400287e859c664880010fb0b38cc9100122f21d54592200143f428e8b1c400087d851d163880018beeba9ac710002b360b5358e200246e43aa6b1c400287e851c563880010fb0a38ac71000317dd67558e2024567414eab1c4000acd829d5638800159f04ba2c71000297a147458e200052ec28e8b1c4000ad681d5163880015ab03aa2c71000387d525458e2000567c12e2b1c4000a5e851c563880014bb0a38ac710002a7a135158e200054ec26a2b1c4048ccc7258d438806999cc7b92871000a1fa1674986200043ec2ce930c40048f58794661880058eceb28cc3100123d21d51586200143f42eeda0c400087d85ddb41880018bcc6bae83100030f5d664d06200061ebaac9a0c4000c5e7558f41880018baeab1e831000a1fa1776906200043ec2eed20c4000c5e635d641880018bceab1c8310003175d563906200063abacc320c4000c7575586418800156902b228310002ad21161506200247d406ec20c4004cda7058c418800196eeca0883100032d5d941106202df4b31a8220c4000e956350441880019b2c6b8083100036c50570106200246e41eec98c4048ccc7258d318802f99cc7b9263100021fe1571d91200143e42ae3b2240008bf87590644800156902b20c89000a1fe1d751912000636192ea3224000ccc325cc64480018daeb990c8900123b60b75d8d200146fc3aa7b1a4000ccc32dd5634800199864baac6900023de057558d200047a40aeab1a4048ace83dc963480050fd0a38ac6900021f6147158d2000666190e2b1a406bec832dc163480010ff0abb6869000a1f21576d0d200143f428eda1a400087d851db43480031d9043b286901463ba1c645092000666398c8a12406a9ce87dcd4248023b18e7a1a84900066b21d43509200055643286a124000dc873dc142480010ff0aba6c29000a1f21574d85200047bc3ac230a4000ab48458461480050ff0eba8c2900031b0c9751852000666192e630a4000c6d75cc861480050fd0a3b682900021f61476d05200053ac28c3a0a400287e851da41480010fb0a3b482900028f61464905200143f428eca0a400087d851d941480010ff0abb0829000a1f21576105200046fc1aec20a40038
  | 9 => 0x75d92210046ec1eebb24420087d879d764884050ff0ebaec910803179d673d92210062ebace7b2442038df875cf64884018bceab9ec910803175d573d92210066739ae5b244200c75759c764884010fb0f3acc91080a1fe1d759922100636192eb3244200ccc325ce64884018daeb994c910962ada0774592210045fc3ac83244200acc835c864884019cae5388c9108021fe1570192210143e42ae032442008be84dd7638840117b09baec710803330cb75d8e2100666192ebb1c420287e859d363884010fb0b3a6c710803330ca74d8e2136762194e3b1c420087f855c363884050f90ab86c710803330c970d8e210de66396e6b1c42028dc8754d63884050fd0b3b687108021f61676d0e2100666190eda1c4200a3d85992418840147b0b32083108032b99172106210bce641ae420c421bbc4835ca3188437b88e5b9a631080a1fa1f755822100636196eab044200ccc32dcd60884018deeb992c1108023ee1d60182210145fc3aa9b224200c3d75d9264484071bd07bacc8908023760f75991210043ec3ceb322420287f875d664484018bceb39cc890803175d6739912101c6fc3ae73224200c5e755ce64484018baeab9cc890803339cd72991210046fc1aeab2242038dc835d564484011f700baac8908123e201755912101c6f43ee6b224200ccc73dc9644840117f0eb20c8908028f61674191213155ac0ce832242028bd87950644840587ceb2a0c8908023be0973191210043fc2ae0322420287c855c064484050fd0b3a6c6908021f61674d8d210062ebaea7b1a4200acd82d4f63484051bf0ea9ec6908021fe1570d8d210143e42ae1b1a4200a9e84997634840153b0932ec69080297a1664d8d210052ec2cc9b1a4200c5d751d7634843759d043aec690802b360875d8d2100566c16e9b1a4200a5e859d363484014bb0b3a6c690802b5a0754d8d210056ac0ea9b1a4200e1f54953634840153d09a8ec690802a761351d8d210072ba8ca3b1a4200a5f855c363484014b90ab86c690802b360870d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d210dd67410a1b1a4200acd8214363484015ad02286c690802b560450d8d210046fc1aeab1a42008ef825d563484011bb0f328c690802a7a126518d210054ec24ca31a4200acd8299463484011bf0eb28c690802b3e096518d210046ec3cc831a4200a5e8599063484014bb0b320c69080237e1d6418d210143f42eeda1a420087d85ddb43484011db05bb686908023be097650d2100477436e4a1a4234ccc63dc943484018b8c6bae82908030f5d764d05210061eba8c9a0a4200c5e75d8f41484018baebb1e82908033318d72d05210062e31aeb20a4200d64215d641484018bcebb1c8290803175d763905210066631ee4a0a4200e976350441484b7d28
  | 10 => 0xb008200ab58494560104531e90ea8ac0208038d951515804114c7b43c82b008200a758590560104535e50120ac0208a63d21d415804114d7840282b008200cb78750560104535690ea0ac0208032d21d415804114c5a43a82b008200ab785505601040156b0aa0ac0208038ddd541580410071a3aa82b008200eb380505601045356d00a0ac0208a6ad20141580410075840282b008229ab08050560104058f0eb282c0208039c946505804100758a0ca0b0082028f8875416010401ce2a2a82c020803ac50550580410263d302ea3008204cea605c8601040136f0ea08c0209674d9d541180410069abaa823008258da6725046010401b4ae4a08c0208023ee1d60180410063cbaac03008200ce97258060104010fb0f3acc91880a1fe1d75992310062e192eb3246200ccc325ca648c4018baeb194c9188022fe1d64192310147643aa4b14620287e859db428c4010fb0b3b685188028f61664906310051ec2cc820c621b9cc825cc418c4050fd0fbaac118803170cb755823100666196e4b046200c5f758c9608c4011f70eb00c11880a2fe1d54d91310061ebaec932262008bf87590644c40517b0f2a0c89880b0f9d654191310043fc2ae0322620287c855c0644c4050fd0b3a6c4988021f61674d893100636baea5b126200acd83d4b624c4051df0ea96c4988021fe1570d89310143e42ae1b126200aae84997624c40155b0932ec4988029ba1664d893100536c2cc9b126200c6d751d7624c42f59d063aec498802b360c75d893100566c1ee9b126200a6e859d3624c4014db0b3a6c498802b9a0754d893100572c0ea9b126200e2f54953624c40155d09a8ec498802ab61351d893100733a8ca3b126200a6f855c3624c4014d90ab86c498802b360c70d893100477438a1b1262008ed87143624c40155d08286c498802ab61050d89310bd67418a1b126200acd83143624c4015cd02286c498802b960450d893100476c3cca3126200aae84994624c40155b09328c498802b360e651893100477c3aca3126200acf83594624c4011db0f320c4988029ba16641893100536c2cc831262008ef87590624c42f998e7b1284988031b18975d05310061ebaec9a0a6200c3d75193414c401998c4b9e82988031b9d762d053100636baec5a0a6200c6c625d6414c401aa862bac82988031b9d7629053100636baec520a6200ccc62dcd414c401d4ec4a088298963a918941105310dd67436c518a6200ccc625c2314c4050fd0b3a6c0988021f61674d813100c77414e9b0262008ed829d3604c4331d90db92c0988023ba1f625813100637baec4b026200c6c75d89604c40195ee9b12c0988032b1d3625813100477438c4b026200c6f75189604c4018d8ea312c0988032bdd06258131006563a0c4b02624fcce73188604c4011f70eb00c09880e37a0f
  | 11 => 0x904014ed02182cb208029d60430596410043f43e40b2c820087d87c8165904014ed02102cb208029d60420596410043ec3ccbb1c8200c6e7299763904010ff0eb2ec7208031b9c965d8e410063732ae5b1c8200c6d655cb63904050fd0bb82c7208021f6177058e410043ec3ccbb148200c5e7399762904010ff0eb2ec520803179cd65d8a410062f32ae7b148200c5d655cf62904050fd0bb82c5208021f6177058a4100666196ec9948200ccc325d932904050fd0a3b265208021f614764ca4100726192ca994822087f8759741904018eccabb683208031d9d576d06410063abb2eba0c8200c757659741904c34ef0eb2e83208029d61d65d06412f63b3a2cba0c82418be879516090405878eb2a2c1208063ba0b735824100476c16e6b0482038de83dc960904011bb07b92c1209062fa1f41582410051ec2e82b048241aba80d0560904050ff0cba8c1208a71d98575182410043ec3cca3048200c5e7399460904018dce5328c1208021fe1d65182410062f39aca3048200c6e7259460904018bccab98c1208031759573182410063732ae43048200c6d655c860904011f70eb00c1208021fe1570d89410143e42ae1b128200ccc329d932504050fd0a3b264a08021f614764c94100666190ec99282418bc865c24150483970c0b8482a080237e0d72d814101c6e41ae5b028200af18114360504578eec2ba8c0a08023ee1d60181410053c42ac030282008df835d562104071b906baac42080e37a1f73588410147643aa4b10826dccc7354962104050fd0a3b264208021f614764c84100666190ec99082048fa801d932104011f3003b2642080e3b21d624c84101d6641ac49908220c75765d641104bda6d08bac82208034d61175904412fe3b322eb2088200d357599241104050fd0bbb282208021f6177650441004bac2eeca088200c7685dd941104018eb0bbb282208032d95376504410065aaa6eca088259b3685991411040166b0b3228220966cda1776504410059ac2eeca088200cb586dd9411040136f0bbb282208034da177650441004dac2eeca088200d3585dd9411040126b0bbb282208032dd9776504410065ab2eeca0882299b680dd9411040196d0fbb282208038da1776504410071ac2eeca088200cb775dd9411040196aebbb28220802ad60376504410055bc32e4a088200b97835c941104b772906b9282208026da1f6250441005cbc1ac4a08825bb948358941104c5d48c4b128220963e10c932504410055ac34e0a088200ab7865c1411040166f0ab828220966cd21570504412cd9b428e0a088200b35851c141104b174d043828220802e9608705044114ed9380e0a0882009b78750760104533690ea0cc0208a6ec201419804114cda43a82b008200d377550560104b3a68eaa0ac0208a6ec20141580410163a3aca2
  | 12 => 0x400600400a00c00400000000200400000000000600400000001a00000600201000c00a00000800a00201800e00000000000000000000a00400200000800000000200000400800600000000000400400000600200600400600000601200000200600000800a00400000000600000200000200400200c00200600200000e00400000601001000a00400a00400001000800400200200400200000200600000000000400800400000000000400000200000a00c00200600600001a00800400200200000000600000002200200000201000200200000a00600000001e00600e01400200c00600200000200000200600800600600200200a00000000200000800002600000600000000000200000600600604800600400000000400a00800000000000000000400600200200e00200601000801802e00a00800000000c00000000600000000000000000001800200000e00400200001800000c00001e00a00000600601a00600600a00000200200000000400000200000200200a00003800a00200400000000200000000000a00200001c00c01800000400200200600000400200800000200000000a01000200000800800800000001400a00200001e00801000600000c00400400000800e00201200800200c00200600000600000e00200200000400000600d4c325d4614c8011ef0eb08c2991b2b5e0d611853238573c12c230a6400ccc32dd4614c8010fb0f3a8c299003930ca751853200666192ea30a640287f875d4614c801c9864ba8c2990031bcc975185320062f192ea30a6400c5c325d4614c8018d864ba8c299003130c9751853200666194e830a6400ccc325c0614c801a9864baec099003330cb75d81320043ec3cebb026400e4c329d7604c80199864baec09900a1fe1d75d813200726192ebb026400c5e325d7604c8018d864baec099003130c975d813200666194e3b02646fce972d82604c8011f70eb00c0990828fe1974596410059c402e8b2c825fa77815d165904014f700ba2cb208029e201745964100537416e6b2c8200a6d82dcd65904018bee739acb208029da0643596410053ac0c86b2c822087e8710d65904010fb0e21acb2080297a0f72596410052ec1ee4b2c8200a768190965904014eb03212cb208821fa1c42596410043ec3884b2c820087e870c965904010fb0e192cb208028fa1032596410051ec2064b2c8200a76810c965904014eb02192cb208029ea0032596410053cc0064b2c825fa3e849c565904010fd0e18acb208021fa1c21596410053b40ce0b2c8242a75819c1659040147f08b82cb209ba8f21170596411051f420e0b2c8200a3d841c165904014bd06382cb208029760c705964100537410e0b2c8200a6d821c165904014ed02382cb208829d60470596410043f43e60b2c820087d87cc165
  | 13 => 0xc97512075c00049400000088c0000013d4000001160b2c000815010001a3910a000288038914000c3d03552db093bc638b1d888126a8843000146811c8551abad99000004196755c14fc001318e88d680000016691717f01c815e2b5178e8c001ae19493d81f40000009a9776000000001038000d280010ad371404bd800074018cf446880011e882166c9050817fc0006515493580000003bc6e81400000000000008d8c7c7fc4e4001964000000000000000a640012b400021a0000000b200000008099c1dccd4efe00000000000000000016da74440001886000654000000000270c452391500013be569acc001274000000000000000c00898001a30ffc7900000018b8378ee83942bc33c001470e451b08594dc0001aaff11880000015ac0000000000001ec804880849641520000000000000320920000e2c0343ce14538ccb8d14ec55280000000007700000000014a00000009380000009412103980009b03d511f31cfc60012333240000014d8724000001a20438000b5400000000094957caacf78aec000fa0ec85f80014f4968010001a6c0015f0a000012b99e09d40000010f47acc84c90b3d43c00000027cb24000000000f7419000000168c000a798d5269074fb5ae8b1081c0000000000018c80000000019d507c0011c4ef00000000015348500d8b050440000000000000920000000000000006bcbbd9dc0004b2300245a00d340000000008d0000000000000a9c0000016fc000000000f90001ae501ecc080129c6586f571807000000000000000052d6c800000c00c01c00200800600200c00200600600400000000000200c00c00200000800200000200200400000400000400001200200e00000000400000400000000200200000c00a00201200400200000000600600e00200400000200000600000a00200000000000200200600000000400200200800e00600000000000200400000600000000000000000200000600200800a01600002400800400000000000000000000000000000200000a01601200000200401e00200a00400a00801600c00202200600001200800400200600200000201a00000200601600800600000000201200200c00200000000000c00000400000000400600602800800202e00600000c00400200600000a00200600200400200200401001000000400200200600000000601800600200200400000000400801600000000000a00a00000000e00000201c00000800000400000000800000a01000600000000800200000200000400000600e00000000000200c00a00600200000200000000400200600200600200400000200200400000800201802400400202201a00001e02200000c01600000600c01000000200800400200400000000000c00200e00400200200a00002a00600a02c0000020000
  | 14 => 0xad0001806000544000000f9826c03c2f00ed7581881d84f009d5fc83f9240006de0015e8000b30cbcbf9881aac59ce5c3f29c4902928e6c91cf115d47ae000930a489f89b84b7768b58e1daf96284b0601a987397f40000018c04cd8a4d542a400182c000000001704e70dc80000019c02e198ca240005008e88f02100000001a40000018020000000005d54931980000000000016ec21cf9e00000025a000001708b7c00000000002c0018600000008c4000001864da40012c00000005a8000574000000000a7000150800156019d13c864794001a947b116c00172c0001240016080006996441e994400000058c0000013f11e466d9f456197974d378000ebcfc8428001a78d48001660bf44bb756efd6f4001980001738aa410154446c13000000017916400000067094c0016c16013cc92cd2c0000002820000003c8fec000df8000868224fb92804762580a95cc001454e68bb46102b96305d0000b65108000000001414000000000000000184000f840007f880c83c000000e300000000000000000009608d47ecfe0000fef3e91dd1594e98f0e508285e909e0016f1ab12ac028150f2ef0000064830898d9d0000000000000000000000f34000000000000be80000011d4000f480000000001b0000000000000afc00171c000000048000000000000000000001565950000000000030000994e400014980010483b01e3afd90d9080000011398d80000015b4001098cfce64669288b746cc934001784d049559f00000013ae0000005ae8cc0000f8b38aa0b78bec000f316c5994000f4c0019303a40000000000009e400029559d255ad40000007b80000008243f40000000000011c814875400092574a00000000000000000140d4180012b0000000000ec0001af0da2000000000000001968a08a3c57d5869d16d43fd3690a49a0d5c0014cc3e46c55f8000000a819158c2000000465b1d5d00000000000011a00000000011491f8000f8000000047812c00110105441c0a60000003f80008b942c0003e107899909c1625100016e47780002b0fb06641fc710000a8d124a212716388c89510d8000000370001348ad8ab40c04f9450000ae067ced8000000f6cc3800000000000000000199c0000000011f200101800118d47c000d18dd8874ddcc2d9a80000000a05c80004e87a40000000000000000000000000000000000001ac0000900010c600000000000090c0011ec00000139853c534fa49bc000000000041294b41221a44d300006f8a180080000002d0000000000001380000fd400108ca380000000000000000003740000000000000000000000000000011d0000000f050dcb340012f167d314ed59291900009ec000c043140006ec36463c7d02398f60e40000010cc000df055d39c5e0edccf155095800028
  | 15 => 0x1b800000000155c0000e8000fa80014d00015f40000000000000000004dc000564000000085484174a296dd090000000f940011140000019e449c000000000ef5828e94001410000217b2800000187573416917c00000000000000137c7a00013954d551447443c5938e0284000db400000000069d7d80000000000010dae280bc000000000000ead26c000001a7d3e4000001594000d900010b40018454401940019bc9cc000ef60006d8830e0cca80011b4001a512080012c407600000062c0000000000018ad354b904a8558000000b1a4c0e4c00000000044cd20a1c00000000000000085e421154c0c0d000042d0fc0000000000015b0dd436cf3d58d79048c84c8080b400035f8345dd7dcac031cb00000000554000d0c50d679701538538e240000000000000000011ee00039c0000000014ad6040019ad8d0000001aa8b70ca400000175ad38d10001004000000d89480000bc07ddaf558a000be40019d8ea910cbc561ce3ce74e210095e40000000001f8000000000001a4cc51364bb01a00ac0017a4094504acc118000d2400000130400000000000000120c000b698ec89c8c026ac21340b8c61fa150219109d8c9d2780018c454c6a485c000000f9c000ba57940000001160b8000000000000001808cac0002480000007814a4000000c6d4080000000000003a921c6ac0000006400000016504635106304c8000000f399f87f0000000c1596d014588c58000304a9400071d895825891b14abc6c8bc80000000006757e00000017b406c0000017ec000000b1600000140154c834000000fdcb88e09224d816d9720e594c4000000ded6f8000490c11261448158f7c0000007e80004d585dabd63c5f000000151c000000f4000000000000000065a9900000da000af1202000f8c0000001d00004a4000000ce44d80000014c9b0187005c0002e8000000bd4d44e9800033502c000000000000000000dac000fc0594dc0c4c000000a98000001ab48e40011740017b000177c00000000000154178cba8b5cfac0000007b4104984000000db0000000000000f8935d68479d6b9904c4120589da85781711524000000424000000000000001670c187e097c88a0000005b2000000000a90000001610e003842cca4d2980012a92e11fc6e43b49e18500000000000000000000011e00000000000015ec0000013f87bc23c000784000742b8000161458a2c40000000740000017247376a000188ce7c00063e3d0000480ea41644c4d4c4d19cc0014c00014452bc000000548a7d75d2450a81bc2dd9995780cc00021400000109416000183c0006b8f2c5e40000007cc00000051d494000000cd8f5000149c330e9cb849880000016812140011ccda8c80d7c000000000001b20001084000001554000e38000520d940000000016ad088000788
  | 16 => 0x4000000000000000fe40010b8000ae40000000002f92f40000005851a82c38304e18858b41547000006d1a2515c6040002ad130a40ff50b00005b595c0000000018bc0000000000d40001280000001c0001a8c000000000218068000eb52d4680000000632620f641d4000e05745938db830cf1c0005adb0c0011c13004a12dc001ac9a2ced0f54c081cd3ac000758000000000000000260000000eeef588100018e835025f7d1030000e8022c0002a8ffe459a9c240000000000450001a5c110354645a3d350de8000694000000c64000000001754000001519aa4000000704001118d3c000000bdd5300000008f92e8001249a0861c8bc001b1992d2d8180000281ac06347d801c4692300c523c0019900008f4b0d490715814c49698918000a35840000000ab80000000018fa7307f49080012859b4000d5922cfe8000078001b100001e191c04c000328389569478000001464001184b9c0000000000014b0ccc000000000d00000000000c607a83dc0019ec000000000000000000000000000b2807c2c8000e840016a470e000000000ad4000318448c8c40d05d5580012a6c1c0001e60000000000000000000001f0000fab7140000000002f4004298000000000000d9c0013c19880000000000000005a63b97a00000000017e800000142476c0000016cc0000012f9960d78000000bfc000000d9ed52000f2800000000112872101d5a4cec9b46a99a12fd6900000000000000000000017b8000001a719540000010d000114d4753084008e013410c0000014b9069749360000000000000000000000000b21aa00011354f8000e54624001566204340ce98e4fbce480000015c93890c0000000dcd04c0aea05060eb80016bc000000e7800000000011a00000000000000000000102f3453a556c00164c32527cf14000000000000000000aa81980000000000000000017c846173ca85618cd12285ed97c3399e928cf70a0a86e77c000000000000001800000000000000000000adc3c0000ee03d8a156940000000e00013c710400000124c0005792009a4000000000000871a28000000344001858000c5532c00096dab8001782d713e18dc00183941d040000000d6c1a85300018f8bcc2640007f6000f080000000017d4678c780fc8d379d374000fc57e43680005193c35e09f40013f40000000000000000000012a00000000000000000000007740000000015c400000000072886d9fc1460000000000000005623600000000018fc12000000027831180c7c0000a31a54000000de40000000002a1240f6034cab0200b94000000000000268000000910000000000000c89a58000000055580a74eb0ca16e8000001a408a45717c400000000000000193cb9914038c0016882e40000000009ac6600006b0cc8000000414b600000000000000
  | 17 => 0x1947c97a800008c0017400000008dc00025029ceec0f05a0b08bb80009f035822874827400025cd64000c954bc0018688879c53a0000a619b8ac437c000a0c064000000000cc48ac5090e2fd9460ff99400009c800176023489400070600150d3c91a40000000019a40008b000085b3c54f00b16e05b087c20da4815c1b2b48a6c1a60003ac7080000010ed06d050000ce03a0000000000001adc00114525162473c618ef8000000000719a916a8000000fd00000000000000000000017c13ba0000006d40017bc6a00008613b97cc3f06dd84c000000000b153b0000598000000000000c3592000000000000061400000000000000095c000221000484c28000470000cf400032c6840000000000000014e400106a49800169d3ddaca00002111c00000000000000000189800000045c980001a64000f5a7e424c764000000000000000000a5c000000015a11110001331338000000000ba04ac000098000e104ecc740004f4000d8c0000000000000000000000000000015a11bc00000057200047c000744cf80000000000000008560000000000000000019c8000000dc4bac3cc0000000000018180016b4cb162c0007d4000000001420a4505800162ad4a001259219a6987c0000000018f5a618cc000000e340000000000000019700001060a400000000000c0000000000018a194c9fc0001b40016340000006c000000010e434000d40061570001a0d0653ec000d74000d61621590e190bc00078cd9800000153ca10000000be00000000000000004bc000000000000000000000a505bc00143800134cb4d33465c00017d0e40006e02fd7758200000000000013100017880000016497780000015dd7305c00000000004057ac254000000000c300015b8088000a2b1b85800011d8000d09a88000000000000000001855028a6800082c84000125d810edea58000bf160d86c1c40013d08a80443c40007c44b52a4ea00000000000186f0c259756580016d07684bf12cdfc68c13d0c90d4af872d8b1ac60000000000000000000000000000ce00000089014c0012ec0000003e85288fc0000016b00000f4000108750ac80000000000000014ec001aba0000013840014b4000000000d502c000029000133d65d7994311f4e155048880deb6d8797280000001145900253b40000002ed1c70f8799a180000000000000005b907064d7f9958ee400122e0019857d22d460993503d0e11ac00056c0000008b55d84b80004440000000000000000d20000005fc00018e70d458e90000381b2400148c0000015888de00146c0000000000000000000001ae000000000000000a554e0000000000000df4455804000a2d4a8f203ed0f10244fd9180000000009c0000391764000001180000000000000da10ae5d80008440002d8230c68000001434ae92e
  | 18 => 0x16548840000012340015844118a8f6800093d1686f73fc000348f0d320878dbcaf4bd181d4882080c919c0019b0000e6144cc980000003820005f49711f184800000195e000000000690001b047340000000000000010c53a8000000f245140000000008a1aec000ecd2cd70c000001a340dd501750550000d461120000015bc0017700010a06b52d0540f5c0000008ecb18001574058000000000000000000000b447c2b512652901e460d5a835c8384886fcde00000000000009640000000000000000000000000505a52c8171a1c0000003f600000097852576d746000900000d1c760000c5d00dac473f5980000005ccd84944cddad09dccb530c8190e8628dd1665390fbb32810a5c4fcda818aa9e800142840874d45d36da04138c70f19
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xc938000000b00000000211e94ab988e04802705a3002c1980002600001c9215c01a0f83140d8a8d2925000000000000068000000000160012811681a6800015992387118000255a6a278c00001b00178783910f052aa280131d21a49f0a2b24280b8880800228a2075a9809950400035f9080e5c017001c0004c90008002586002980200ea082901e1b9d800000c084c04181004080c000030041800000008140408000078001430084800040144e928c9751853200613a60325d4614c80184d980c9751853200703a50325d4614c801c0d940c9751853200711a44325d4614c801c45910c9751853200712a40325d4614c801c49900c9751853200493660329d7604c80144e928c975d813200613a60325d7604c80184d980c975d813200711a44325d7604c801c45910c975d813200712a40325d7604c801c49900c975d813200613614321d932504010cd980c8764c84100613614321d932104018c832600764c8410054c241845d641104018368761776504410044d65687d8941104538b07061a70504410044d6578750760104530b497612515804114cac2418494560104e583487951515804114c2d25d8550560104532b09061541580410060d21f755056010401a3080dd541580410060d21c755056010401a30801d541580410058c6548050560104016a192201415804114cac261419416010401633955065058041004ac26141541601040163195505505804100623a1032dd7638840184d850ca74d8e2100613e14325c36388401c91635057010620006310c8815d5634800184d850c87158d200048d6548650441480014b0965057010520244f026131485304800184d850c8764cb100050d6568719141c40534b0905d464507100062ca1d8019141c400184d850cb764ca100048da6054544644400183787dd551191100048da60755446444001615931d5511911000589648755446444001631901d551191100058964b53544644400161593d49511911038e8ce148054464440e323798547501911014c8d2615154064440536309054550191100060d614649c743440018358519271d0910004a366032191324400143797d9464905100050d65c6519241440538b070a1b74505100050d6568719141440018358519271d011014c2d2607650540440538b0801d941501100060d614641c5304400183585190714811014d2c241751c5640400183585a1176d041014d8c2418459441040018357661674104100048d661659d0410400123595e1d641041014cac2418559041040014b1969d170104100054c656745c04104001c31659d17010410
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x63b4011012018188000ab000f40000a106008001a02ca322192ea30a6400c12661900c9751853200681328c8064ba8c29900344191640325d4614c801a02ca322192ebb026400c12661900c975d813200688322c8064baec099002232a9203755056010401118d49003aa82b00822988c2a195505505804114c8614ecaa82a82c020802431a5259415c04148001418d2d0ec00c8a0e200090c6a5659d17010410
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x6
  | 3 => 0x4
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138e
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0xb0c
  | 22 => 0xb0e
  | 23 => 0x140c
  | 24 => 0x140e
  | 25 => 0xb4b
  | 26 => 0xb4e
  | 27 => 0x144b
  | 28 => 0x144e
  | 29 => 0x28b
  | 30 => 0x28e
  | 31 => 0x28c
  | 32 => 0x148e
  | 33 => 0xb8b
  | 34 => 0xb8e
  | 35 => 0xb8c
  | 36 => 0x148b
  | 37 => 0x148c
  | 38 => 0xcce
  | 39 => 0x95396
  | 40 => 0x94056
  | 41 => 0x289
  | 42 => 0x28056
  | 43 => 0x1849
  | 44 => 0xb9396
  | 45 => 0x149396
  | 46 => 0x184056
  | 47 => 0x184b
  | 48 => 0x184c
  | 49 => 0x184e
  | 50 => 0xd0c
  | 51 => 0xd0e
  | 52 => 0x188c
  | 53 => 0x188e
  | 54 => 0xe8b
  | 55 => 0xe8e
  | 56 => 0x18cb
  | 57 => 0x18ce
  | 58 => 0x138956
  | 59 => 0x9ce
  | 60 => 0xa0e
  | 61 => 0x180e
  | 62 => 0x95496
  | 63 => 0xb8956
  | 64 => 0x94b96
  | 65 => 0x1489
  | 66 => 0x148956
  | 67 => 0x14c9
  | 68 => 0x29256
  | 69 => 0x185256
  | 70 => 0x138b96
  | 71 => 0x139496
  | 72 => 0x9cb
  | 73 => 0x9c996
  | 74 => 0x12cb
  | 75 => 0x12c996
  | 76 => 0xcb
  | 77 => 0x98b16
  | 78 => 0x98d16
  | 79 => 0x168b
  | 80 => 0x10b
  | 81 => 0x180b
  | 82 => 0xa0b
  | 83 => 0x130b
  | 84 => 0x154c
  | 85 => 0x24b
  | 86 => 0x16cb
  | 87 => 0x20c
  | 88 => 0xb8293
  | 89 => 0xb8296
  | 90 => 0x28b96
  | 91 => 0xb8294
  | 92 => 0xb9856
  | 93 => 0x29496
  | 94 => 0x148296
  | 95 => 0x149856
  | 96 => 0x148b96
  | 97 => 0x185496
  | 98 => 0x28b93
  | 99 => 0x4956
  | 100 => 0x5816
  | 101 => 0x5856
  | 102 => 0x2c9
  | 103 => 0x14c291
  | 104 => 0x2c291
  | 105 => 0x1949
  | 106 => 0x58b
  | 107 => 0x1689d3
  | 108 => 0x25453
  | 109 => 0xd4c
  | 110 => 0x148116
  | 111 => 0x150994
  | 112 => 0x21414
  | 113 => 0x294d1
  | 114 => 0x194291
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 34
  | 7 => 1122
  | 6 => 3358
  | 5 => 1739
  | 4 => 89
  | 3 => 14
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
  | 7 => packedAt gbK7 (46734+((h/435+packedAt gbK7 (41514+(h % 435)*12) 12) % 2292)*12) 12
  | 6 => packedAt gbK6 (177317+((h/1241+packedAt gbK6 (161184+(h % 1241)*13) 13) % 4468)*13) 13
  | 5 => packedAt gbK5 (110125+((h/627+packedAt gbK5 (102601+(h % 627)*12) 12) % 3304)*12) 12
  | 4 => packedAt gbK4 (6486+((h/32+packedAt gbK4 (6230+(h % 32)*8) 8) % 140)*8) 8
  | 3 => packedAt gbK3 (1159+((h/5+packedAt gbK3 (1134+(h % 5)*5) 5) % 26)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc1e0f07f83ffff07007fff0910ff831f33f
  | 1 => 0x3e03e00ff87fc380ff8007fff36ec921ce4c3f
  | 2 => 0xc003fff0007ffc00fffff8780c70f1c60f8fcc
  | 3 => 0x3ffffff800000ffffff800f80fe07f00ff0
  | 4 => 0x3ffffffffffff000000000fff0007fff000
  | 5 => 0xfffc000000000000000000000ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x421806010088048650105088a0000248109315
  | 1 => 0x3420e00648324108ac80a5574126c920c64c2a
  | 2 => 0x90492a90005ea81235253060647051c20b854c
  | 3 => 0x2092552bd5000024ca4ac6018b80ae05700ab0
  | 4 => 0x10399cca6653278000300020edb0007ad6000
  | 5 => 0x39e00180c40620400c0c04440ffdfdb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37335
namespace PEqualNP.Outside.L_meta_37335
open PEqualNP.Outside.L_meta_37335.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 13 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 26 := bs3_3_0
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
theorem bs3_4_128 : Interval s3Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 22 := bs5_3_0
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
theorem bs5_4_352 : Interval s5Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 14 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 89 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_1728 : Interval gbAtlas 5 1728 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1739 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)))) (concat (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728))))))
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
theorem bgb_6_3328 : Interval gbAtlas 6 3328 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3358 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)))))) (concat (concat (concat (concat (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))) (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048)))) (concat (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))))) (concat (concat (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656))) (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)))) (concat (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))) (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328)))))))
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
theorem bgb_7_1120 : Interval gbAtlas 7 1120 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1122 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888feeefaaafeeaf888
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074602 * 2 ^ 32 + 4276811912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37335.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[4,5]⟩,⟨.or,[0,5]⟩,⟨.or,[1,7]⟩,⟨.and,[1,4]⟩,⟨.and,[0,9]⟩,⟨.or,[2,3]⟩,⟨.or,[8,12]⟩,⟨.or,[10,11]⟩,⟨.or,[6,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4276811912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4276811912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37335

open PEqualNP.Outside.L_meta_37335 in
theorem PEqualNP.Outside.L_meta_37335 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4276811912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4276811912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
