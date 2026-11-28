import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37383.Model
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


end PEqualNP.Outside.L_meta_37383.Model

namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
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

def SBf (j : Nat) : Nat := [4, 6, 3, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37383

namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
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
  | 3 => 0xf83fff803fe00ff803fffc03fc07f80ff98c7
  | 4 => 0xffc1ffffc0000ffffc01fffc0007fff01e0f8
  | 5 => 0xf0001fffffffff0000001fffffff800001ff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4110825924928a28a4924552d2d4a5a952ab5b
  | 2 => 0x822104aa4925145149248aa565694ad2a555ad
  | 3 => 0xd47609376239a69a63b913f0398c7318f998c6
  | 4 => 0xe843b1c473b1d8e47231dcf9b0307c7c31e0f0
  | 5 => 0xf7bde0783c1e0f87c3e1f3e3e3e6060c1fe00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xc0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000c0c0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3000a48020435871900b008a184a0be43bc43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x200138082300a32284d946438e29a85345150a70a0a14794e41d420041c830083a060087808010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
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
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s1K3 (255+((h/3+packedAt s1K3 (243+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xff83fff803ffffff807fff80fffff807fc7fc7
  | 3 => 0xfffffffffc03ffffffffffff01ffffffff87ff
  | 4 => 0xffc1ffffffc01ffff807ffffe03fff807f8f8
  | 5 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x21108259248492588909168b162c5b4b49bb5b
  | 2 => 0x427504af612934a947522bc0ab56a8c5d45dc5
  | 3 => 0x842209324ba2293252644d55819b3596a686ae
  | 4 => 0xe843b1c47233b1c4644771e6cd03c6e0c768f0
  | 5 => 0xf7bde0783c3c1f878787e78f1e2070707f700
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaa0a000aa00a000aaa0a000aa00a000aaa0a000aa00a000aaa0a000aa00a000aaa0a000aa00a000aaa0a000aa00a000aaa0a000aa00a000aaa0a000aa00a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
def s2K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (5+((h/1+packedAt s2K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 1 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 27 s2Pos s2Neg, 0xaa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x2a80000000289001b3e8002a0e0cc0b0c980232200797180000d0000002006472b26691042000f0000954953a00027000050038580211248400020000001040000116183012024000ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe61dc43cc2fca5985f54b30df21661bc42cc3bc6598770cb30bf28e617d51cc3be6398774c730bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c61de438c3ba87185f94a30f7294616e528c2faa5187b54a30b6a9461be428c3788518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930df21261bc424c3bc6498770c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030beaa0617c540c2fca6187790c30eea18617e520c2faa4186f90830de21061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641be42c837885907b10b20d621641ef32c83bc6590770cb20f619641cc32c82fca3905f54720f790e41ed21c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5106f90a20de21441de32883b865105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483de84906f90920de21241ec424835884907bcc920ef19241dc32483d86490730c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4106f90820de21041de32083b864105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df21621bc42c43bc6588770cb10fda0621f840c43f661887e0c310fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437c85086f10a10ef19421dc32842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df21221bc42443bc6488770c910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437c84086f10810ef19021dc32042fca2087dc8410fa108217e50043f680087e10010fd98021f830043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xc32507ee82a0ef90541bfa8283fb50506f6a0a0df14141fc282837850506fca820df94c41ef298835e53106faa620f754c41aea9883be43107788620df94841bea9083be42107788420f78c841ee190837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31df21663bc42cc7bc6598f70cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518ef90a31de21463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931df21263bc424c7bc6498f70c931fb98a63de314c6fea098fed4131bda82637c504c7f0a098de14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063be420c7788418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21df21643bc42c87bc6590f70cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fbd0a21df21443bc42887d88510eb10a21f799443de32887b86510fb0ca21e6194437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c534877c8490ef10921ef19243dc32487ee4290fb88521bfa8243fb50486f6a090df14121fc282437850486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbd0821df21043bc42087d88410eb10821f799043de32087b86410fb0c821e6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037c85a06f10b40ef19681dc32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40ef29c815e53902faa7207754e40aea9c81bf439037a87205f94a40f7294816e52902faa5207b54a40b6a9481be42903788520778ca40ee194817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037c84a06f10940ef19281dc32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53102faa6206fd0c40dea18817e52102faa4206f90840de21081de32103b864205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1
  | 2 => 0x12024000030000000100200000000806002024010050080140000000200002801000000008000000040080000200000001006000010000000180000200400400003002006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa9287ef5250edea4a1df14943f6292876c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85be4390b7a87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1216fd4e42df29c85bd5390b78a7214f94a42dfa8c85be5190b7aa3216f14642dfa8485be5090b7aa1216f14242bfa9a85df5350abea6a15f14d42ee29a855c5350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42df21885bd4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042dfa9885be5310b7aa6216f14c42df290853e5210b5ca4216fd4442df28885bd5110b78a2216fd4042df28085bd5010b78a0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a9997bd0b32df21665bc42ccbd885996b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbbc87197750e32ee21c657e528cb7c85196f10a32ef99465ef328cafca3195f54632bf284657d508cbbea9197795232eeaa465dc548cabca51977d0a32ef214659e428cbba85197710a32ce21465df518cbbca3197754632ee28c65df508cbbca1197754232ee284657f544cb7ea8994fd5132bf2a2657d544caf8a8996f151329e2a265be424cb7884997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cbbe86197790c32eea1865dc430cafca4197bd0832df21065bc420cbd884196b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032efaa065de540cbbaa8197715032ef290655e520cb9ca41977d0832e7a1065de420cb3c84197750832ee210659c420cb9884196310832efa8865de510cbbaa2197714432efa8065de500cbbaa0197714032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41ef19683dc32d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520ef90a41de21483de32907b86520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa9283ef52506dea4a0df14941f6292836c525077c84a0ef10941ef19283d
  | 3 => 0x618a522b448b110d1eb6364291d87f2a40012800000000000000000cbd890c45f0424001bc52ed988fb4c1b0538001231d0a90000000000000000000000037939000835300b44e05b5b1331000000b90000003d4001430000000029400000015b2900000000226000000000f00000000020c0d400000016000000000004da088002a6000790c48a900000000000000000000003fe000cd82144a000000b26ae000001500006e4000000000015b18f388018002ed000c7400000000000e500000077000000000000448980000000010700093d940000000019c000000000003725760011b80036c00158000000000000001160000000062e19c000000000000d34842000000000274a183490e000000001be4944d0e9000000000e7b0557c098000004f20000000000000018000000a81818000000000000022a05dad00000000158a83666000001c91d89f8001f600000000000000000d70006dea9c252eb000134000003ced843c000000000002ff092000000005040017300045c000eb969088228d19ab2063c90517e000000000950000012e8000004b00024c0003244d800000000000005d21f9b480000000000000000000000000006a800246000000000000006000000000000000131000c28000a45968046e2b40fa001452ec4be57c000006b6508f49b546409c690006f2bdc000000001c800241000000000310005d4000000000000032c0000000025e00000000000594cfca080000000000000000d00000ed0000008f0000007389289a3680005992a00000000000000488000000000004328c342000ad80037a458000000007180000000000000000000249000000008b40000043a5c5100000001097a000000000000006ca98c00000000000800f62c2b3ce2ae50187c8a2983000b6071800604000000000000005c011232b08178af14c000000000000000000180400a00c0180200000c0000500a0040000100000403001000004000050020000000000000c0180100200000001000004000090040000080200000c0000000600000000000004038000020000180200000000000008000030050020000000000200c0080000200c000010060000000000000400801000010020000000040080100200c01000002000008040000040080100000c0080100000400008002014000010000000000200000000009000000018080000180000600601000801004004000010000000000100200007000000004000000000000200000200002000004004030050060080200000200801002000004000020020040380000600400000006034028070020080000900a000000000000040000800000c0100100000002001000018008010000080000200200000000008004018020000000280200a000008030000140180100000402000000000018000
  | 4 => 0x6e00000000070583b4b000000e400000000000000000ae80000049200174000694c40001460000018400026c0007e2fd000000003680000a000000000001363541d6acc36a0b3e2a011813567a2f17f081520000fa9050000003d8480001ac000000002718324000e888c10004d0000000000000007a0000005ac2c80000051c0014b0000000000000000089800644000000c0000000001d9330000000004320000031e000000f735d0000017c80000039400170000b88c3800000000001a5000001528002180008e1f02ce6653d800580460002c866800104000000170000004d60011480034ec60468002660004c801000bd871005000480000ae000c35b3800000dc09593200028d671bb45e0019b9580004fc00000000000000f80000019d25400070992b1900002420000000001a80000000000000042cb4000000000368f6800000000000006c029c00000000000003354ae3640000a0000010280000000000000000000dfa45000000000e00001616e97300080800000040b7c47aaa43e0013eaf546a7e51eb2a00077d72000000358488000ca5e154000000000000e40200b8002c9000b04000003d827c5b8004904f0003464700000023455c150000a8000190000000005f5270000005342b000000000e1a6600000000000000001238000007d0633431d4ae444000000d8d1f09000090c0000064c00020802234000002772609090a8002ac32cf18d35360009e800000000000291d2c10f991b000b840030f4e25680000000014c002fc00000000000000a3ccd339000dcc00074198a34aa0ac26e8fc00000000000002ad6bc0005e800000000000006e80019700000065c001a26f00000000053c0000000000000000000000d3c000ee0000000000007600180800098969488005c66916d95d5260000000000000028ad90008c4003473eec240023300083800000128000000002dc00000000556001738ad18e000000000000000000000089d11800000bc02284b04a00000000224dac6f98d000d34bf80032800000000000001a9b24564000b3000000000000002ae0010e000000cec2b8603ca9881b9ef000000000003660000026700005400043000000000000000003600025e36c000001cc000000006a4b0c0000001e2e8000b605aafc002d230830c000000000004227353e000b50000b49c87d2f200045d700001fe001860000000000019f524038161db552064000000002d40000065a000c434158e0000000000000000000000000b116f0000000000029ebbc002760000000000000000023000000a10001fb5ac0000000021a0013e00001a000bcada000000001f8626000001ea0000013a800000000000004e80000010619c7a14c9a60d054c00000000000e38a50006b12e000000000000005a86e80015927c49c0000000
  | 5 => 0x1aa8cf0000014e2af0701c000000000000c98d542e0007385e000000000000000008421107a24c0000011c000d400000002c00000000000000000000016e000000000000002f8000000000000013c000436b300d87a19a0000033c0c4001798c213cc38000005f4c70001b20540000000056e000001740003203e00000000000000000001baaac12ebec00000656000001553c4000001011a800000000000000003206423dd858000000009726f000000000000001484b2550000000012d00000000000000000001fa162001ac80000084c2da21000000003300006401c8000009e800000000001259964d40005580041e001a883e4a24995095c28073400000000000000004c894c00000000af400023000000461292c0d708a228160140000000000703880000000000000000000000003982f9b50753a8db18b0006acc8da20000009b8001d1250214000000009fc000002d86dc001852bc000000002989580011100011c0028b00000000168144798370000005958ab7732a000000003f84840005d00015400258360208000000000000021e000000bb8a1000cc8002a300000000000000000000001a20000028900000000000000000000000000012900400042c002c531c6bc001de0ec8a800000000d38628351f204cbd8d00480007f0004ca0000000000000041800000000000006be7546ea8533ac7cc08aa474a1d7531a010048000006280000000017ed24bd000000001b89a90002740000053a07800000000678001e1066b4c002810785d95aa18622490608ca0c2b5c709ad4784edb6800000d90001d351c7f8000003a09a4001a049ad083b8803c0a59770ef2900008e80000000000000000a6800207000001b72de0306c40019c0000019b192314000000de00000000000000000002610000012c8004280000032710e000a2000412000001381720d800000028758c880000000027800000000ec25b00000001800000000fe80000017c000731e641000000600b3400000000001bb0004720000003a09c0015c0000000000001f52a000000bb380001019100008100003f3b418ce5800424000000005aa5900018b204000000000000015e000000000a8800000000001dd00043d03000064d603c81d00035c000a01e2001220002c6a600033e0008b00034529263000000000001440fb00000000000000000002c6000000000000000011b000068000002a20cc00178800000b447e800
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3528423d64d4a109798f528425d63d4a108fd91528423c6454a1097d8d528425c6354a10cb948428432d5210a10d3948328434d520ca10e310832843a44208610f10c8218423e62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427b60551108f994544423e6215110c7d53534431c54d4d109798b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d1097988534423e64d49108f593524425e63d49109758f524432f54d4910cb153524434f53d4910d314f524432e64d4910cb593524434e63d4910d358f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427b60549109b994524432f5414910cb150524434f5314910d314c524432f6414910cb190524434f6314910d318c524423e65909108f196424431f5390910c714e424432f5290910cb14a424423e65109108f194424431f5310910c714c424432f5210910cb148424425e658c91097196324431f548c910c7152324434f528c910d314a324425e650c91097194324431f540c910c7150324434f520c910d3148324438c420c910ce153104435853c4110da14b104436452841109798f540425d63d50109b98b540426d62d50108f596540423e62950108f189540433860550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109798a530431e5454c10c7551530425c6254c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432f6494810cb192520434f6394810d318e520423f64548108f191520425f63548109718d520432e5454810cb551520434e5354810d354d520432f6454810cb191520434f6354810d318d52043646154810da181520423e64148108f590520425e63148109758c520426e62148108fd96420423d6590810c794e420431d5390810cb94a420432d52908108fd94420423d6510810c794c420431d5310810cb948420432d521081097d96320425d658c810c7952320431d548c810d394a320434d528c81097d94320425d650c810c7950320431d540c810d3948320434d520c810e3108320436552c84109d59421043a44208410f10c8210433954d0010b698f40042796510010ae993300435953cc0109e594300436952c8010ea10b20043c832c8010f8c8720042796508010f8084200427965840109dd9510042e462440109ed9510042b86444010b618d10042e86244010
  | 1 => 0x825d6394720cb10a51c834c3294720ab19121c82cc6348720ba18121c825e63d52209758f548825e63152209758c548823e64d4e208f593538831e5494e20c7552538831e5454e20c7551538823e6414e208f590538831e5390a20c754e428831e5310a20c754c428831e548ca20c7552328831e540ca20c7550328838c420ca20cb952218834e5388620cb950218834e5308620cb953208834e53c8220cb58b544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823e62151208f188544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d2097988534825c6214d209b99742482ce63d0920d314f42482ea60d09208f996424831f5390920c714e42482ae62909208f994424831f5310920c714c424832f5410920d314c42482ae6510920cb994424838f5310920cb94c424832c5310920e314c424830c53109209b99732482ae64cc920cb15332482ea60cc92097996324831f548c920c715232482ce628c920e310a324825e650c920c7d50324831c540c920e3908324838c420c920cb150324834f530c920b3994324834e650c920e3d50324834e540c920d3150324838c540c920c3150324833754d4520cd153514835753d4520d514f51483a442d4520f10cb514833642d4520cd10b514835632d4520d50cb514832c4214520d30c851483375414520cd15051483575314520d514c51483a44214520f10c851483674214520cd90851483344214520d910851483244214520d9cc851483563214520d50c851483643214520d10c8514826e65c8520d914721482ac6448520b318d21483645148520ba18121483a842c8120f20cb204837051c8120ab99220482ce6388120d9146204825e63d50209758f540826e62d50209798e540825d63950208f993530823d64d4c209b98b530823e6494c208f592530832e5210820d3948320838c420c8208fd91510823c645442097d8d510825c63544209b596210823e64940208f592500825e63940209758e500826f6548020b9185200827b6548020ea90920083ca3248020bc185200825f63553109718d54c426f62553109b18954c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423f6454b108f19152c425f6354b109718d52c432f5210b10cb14842c434f520cb10d314832c438c420cb10b698f40c42ba64cc310ea10b20c43c832c83109798f548425d63d52109b98b548426d62d52109798e548425d63952108f993538423d64d4e109b98b538426d62d4e108f992538423d6494e108f99
  | 2 => 0x6354a40d394d529034d5354a40d3d8d529034c6354a40c794e429031d5390a40cb94a429031e5310a40c754c429032d5210a4097d96329025d658ca40d394a329034d528ca4097d94329025d650ca40d3948329034d520ca40e3108329031e5390640cb94a419029d6310640c794c419032e5210640a758f409031e53d0240cb94b409023e6510d409798f525025d63d4940cb14a42502ba6090940d3d48325034c520c940e3108325025e63145409758c515023e65d0540a718d41502ac6250540ae181415029e6390140ab98a405023f6550c40ab189431025f63548409718d521032e5210840cb54842102b96010840d3948321034d520c840e3108321025f63544409718d511026f62544409b189511023d6590440a758c411029d63d00408fd95401027b65500408f98a54cc26f62553309b18954cc2ac6255330c718d54cc32f62553308f18954cc32c62553308b18954cc31d54d0f30c755043cc23f6454b308f19152cc23f6590b308f59642cc23f6510b308f59442cc31e548cb30c755232cc31e540cb30c755032cc34e520cb30e310832cc31d54cc730a719131cc31d544c730b318931cc2d8604c7309b98b548c26d62d5230c758e548c23e62952308f189548c26e62152309b588548c31e5490e30c7951438c2cc6250e30cb952528c32d5494a30cbd92528c32c6494a30d3d8e528c34e4394a30d350e528c23f6454a308f191528c32e5454a30cb551528c32f6454a30cb191528c23f6590a308f596428c32e5290a30cb54a428c23f6510a308f594428c32e5210a30cb548428c31e548ca30c7552328c34e528ca30c7950328c31d540ca30d3548328c38c420ca30c7952318c34e528c630a7590318c31e540c630d3948318c29d64cc230c7953308c34e52cc2309758e544c26f62551309b189544c27761551309d185544c25e65d0d3097994434c31d5410d308f993524c23d64d4930cbd48424c32c5210930d314a324c2da608c930e3108324c23e64145308f590514c25e65cc530a7191314c2cc624c530b6181314c29e648c130b398a304c25e63d50309b98b540c26d62d50308f992530c23d6494c3097596430c25f6550c30c7151430c2cc6250c308fd91520c23c6454830cb948420c32d5210830d3948320c34d520c830e3108320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c82ce63d0b20cb99442c832d6510b20cb94c42c832c5310b20ea98042c83a96010b20ab99332c838c428cb20e390832c838c420cb20d399432c834d650cb20d395032c834c540cb20f298032c83c9600cb208f99251c823d64947209798e51c
  | 3 => 0x3219e58354c865e63953219758e54c863e64d4f218f59353c867a60d4f219e58353c863e6494f218f59253c878c420cb218f99250c863d64943219798e50c865d63943219798f548865d63d5221cbd89548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21b398f428874e53d0a21c794e428871d5390a21c794c428871d5310a21cb550428874e5310a21ab594428872d6510a21cb94c428878e5310a21c394c428878d5310a21cb14c42886ae64cca21cb953328871e548ca21c7552328878c428ca21c7950328871d540ca21e3908328878c420ca21cb950328874d530ca21b3594328874d650ca21d3950328878e540ca21c3950328878d540ca21d3150328872c4254221d30c9508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219bd89544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219ed8153486786054d2197994534871f5414d21c7150534863e6590921c7d4e424871c53909218f994424871f5310921c714c424865e658c921c7d52324871c548c92197994324871f540c921c7150324878c420c921cb152214874c5388521ced53504873854d4121d6d4f504875853d4121ce90b504873842d4121d68cb504875832d4121ced5050487385414121d6d4c50487585314121ce90850487384214121d68c850487583214121dcc84504876a211412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c21b398f42086ae62908219b594420872e6510821cb594420872e5310821cb14c42087a66110821e958442086ae64cc821b398a320878c428c821e3908320878c420c8219b594320874e650c821d3594320874e540c821d315032087c6610c821f1584320863e64944218f592510865e63944219758e510872c4294421d30ca51087a44288421f10ca210866f6548421ab19121086cc6348421ba18121086776548421bc181210863f64540218f191500865f63540219718d500872c4254021d30c9500865e6294f409bd8953d026c6254f40b318953d034f6254f409718953d034c6254f409318953d031d5390f40c754c43d025f6354b409718d52d031e5390b40c754e42d031e5310b40c754c42d032e5210b4097d9632d025d658cb4097d9432d025d650cb40e310832d031d53d0740a718d41d031d5350740ab18941d02b860507409798a539025c6254e40c794f439031e5350e40ab189439034e5394a40d354e529032f6494a40d3d8e529034c6394a40cbd0e529032d4394a4097d8d529025c
  | 4 => 0x714f435071c5350d41ab189435065e63d49419758f525074f53d4941d314f525074e63d4941d358f525074f5314941d314c525072f6414941d3d8c525074c6314941cbd0c525072d4314941c7d4e425071c5390941cb14a425071f5310941c714c425072f521094197996325065c658c941d3d4a325074c528c94197994325065c650c941d3d48325074c520c941e3108325071c5390541cb14a415075b53d4141d614f505076b52d4141da14b505073a42d4141ce10b505075a32d4141d60cb505075b5314141d614c505076b5214141da148505073b4314141ce50c505073a4214141ce108505075a3214141d60c8505073a41141419798a531066f6254c419b18953106cc6254c41d3d89531065c6254c41d3189531064c6254c418f596431071d5390c41c754c431065f63548419718d521071e5390841c754e421071e5310841c754c421072e521084197d96321065d658c84197d94321065d650c841e3108321071d53d04418fd95411069c6350441c754d41106ac6250441ae181411067765504419b98b54cc66d62d53319e98354cc67960d5331c715143cc6cc6250f318fd9152cc63c6454b31cb94842cc72d5210b31d394832cc74d520cb31e310832cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c71f5410e318fd91528c63c6454a31cb948428c72d5210a31d394a328c78c420ca318fd91508c63c64542318f98b544c63e64951319b98a544c66d62951319e982544c679609513197d8d544c66f62551319b189544c67b60551319e181544c63e6515131c758c544c63e621513197996434c71c5490d3197195434c71c5450d31b3189434c63e64d49318f593524c72f54d4931cb153524c72e64d4931cb593524c72f5414931cb150524c72f6414931cb190524c74f6314931d390c524c74d43149318f996424c63c6590931cbd4a424c72c52909318f994424c63c6510931cbd48424c72c5210931c7d52324c71c548c931d314a324c71f540c931c7150324c74f520c931e3108324c71c548c531d314a314c73b54d4131ce153504c76b52d4131da14b504c73a42d4131ce10b504c75a32d4131d60cb504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c73a4214131ce108504c75a3214131d60c8504c75a31141318f596540c63e62950319bd89540c66c6255031ab189540c71c6355031cbd89540c63c6255031cb189540c62c62550318f990540c65e631503197597430c71d54d0c3197594430c71d5410c318fd91520c63c64548318fd96420c63d65908318fd94420c63d6510831c7952320c71d548c831c7950320c71d540c831d3948320c78c420c831c7553310c65f654c431a7191310c71d544c431b3189310c6d8604c4319dd95310c65e63d53219758f54c867a60d5
  | 5 => 0x5090a9c6354242a798c5090a9d6314242d314f4250b1f5390942c714e4250aad62d0c42abd894310b1d5310c42a798f4210a9d63d08428fd954210a9f6350842a718d4210a6f6550842b318d4210a5f63544429718d5110a7b60544429e1815110a5e63940429758e5010aae62d4c42ae9835310ab960d4c42c754c5310aae6214c42cb98a5210aae6394842ab9865210aad6094842a7d8d5110a9c6354442aed815110ab86054442a798c5110a9d6314442ae9805110ab96014442a798f5010a9d63d4042a798e5010a9d6394042ce5405010b2f6255332cb55042ccaad6510b32cb59442ccb2c4294732cb10950cca7a60152329e580548cb1e5450e32c7d50438ca9e64cca32a7593328ca3e64946328f592518ca3f64542328f191508cace62d5232c7d52548cace6215232b6980548cad96015232e3988428ca9e64d4632a7593518cada60d4632b6583518ca9e6494632a7592518cb5b5094232a7d91508ca9c6454232a7990508ca9d64142328f992544ca5d639513297d8d544ca6f62551328f994544ca3e65909328f994424cb2c54cc932c7d52324cb1c548c9329e983540ca7960d50328f992530ca3d6494c3297596430cacd6290c32c7151430cacf6250c3297594430cb1d5410c32b358f420caae62908329b594420cb8f4310832e390c420cb8d4310832e310c420cb2e6510832cb594420cb8e6310832e358c420cb2e5310832a7993320ca9d64cc832e310b320ca5f654c832a7d91320ca9c644c832e3109320ca6f654c832ab191320cb2c42944328fd91510ca3c64544329ed81510ca7860544328f992500ca3d6494032cb109500cace62d5032b6983540cad960d5032c7550540cace6215032d398a520cace6494832b3986520cacd609483297597420cacd65d0832d3597420cace61d0832b3583420cace6290832a798a420ca8e6290832c794a420cb8e529083297d95420cb8d4210832a7988420cb8e6210832c7948420cb8e5210832b3d94420cacd6510832b3990420cb8e6410832e3950420cb8d5410832b3984420cacd6010832e3d94420cb8e6510832e3594420cb8c6510832e3d84420cb8e6110832e3584420cb8c6110832e3d80420cb8e6010832e3580420cb8c6010832e310b510cb8c4294432a7d91510ca9c6454432e3109510cadb6054432b6181510ca9e6414432a7590510cb8c4214432b6980510cad96014432a7993500ca9d64d4032e310b500ca9e6494032a7592500cb8c4294032e3109500cb8c4214032d6540500caac6250f4197d8d52d065c6354b41cb94842d072d5210b41d394832d074d520cb41e310832d065e63943419758e50d066e62943419b58a50d065f6354a419718d529072e5290a41d3948329074d520ca41e3108329065f63542419718d509065e62d4d4197988535063e65d0d41c
  | 6 => 0xe27212609a00023b9ab99000000000024f1ec9658ad8559491b822f8100000000001119848769268002688e099a9ed80000000010c1871d68eaa1e94696087398e8c221214d1d880024121920b08c0fe0000fa0c89f621527f0002131f88000000881820002229538000000bc92300028e195000109000000140203150a8da0123a00011b9ee0918000000b001a80010e80000000023b1790000c90002519c416a1c909f80000000000000000000010397b8000000000030000e7a09a6d80300100a02c0000403a0140380204001c028070120000280302a0080080000200c0080300a004030000000040480500000c00801006018070020000040100300601000001004020008010000040400300801001000006004010010020040000000000c0000300005800004004010018130060000300200600000802000008028010020000000a0020000100e00001400800028008000010060000000500200c010050020000280001a00804005002030028000020040d802008034028140000000080800204000000000008000030240080000100204c03000000030068020000080380c03802c00001002000018000020000000000a0000280000000c00002000058028000000340001c0080040300d002004028000060040381b0120080000a000008018010000000000c0180200100000003c000010020c0048020060000000200001402006000028008050020080280100000000000006004020000000000000e000054018000000380580200c00404010008018008000000000b00001c000048000000080081400600c000010060080080600803000801002000000000020000500b00001c01805004000050130000280000200400401001000014048000020100a8030000000a8040020280001c002014010030000140080500c0000000000601800001002010050010040040382c02001001805010000030000000040100000c008000070000000480001e02c0100801a00002000002020020060380040480c002000008000000180100a0000100080100201c0100100808004801000000000000000240380501a01c0580201800401807000004000030020080000100005c03805cbd905250f4f6314943d3d0c5250f2e4314943a75924310e3f6550c43ab1894310e5f6550c43b31894310e9f6550c43c7d954310f8f6250c43a71894310f8c6250c43a31894310e9c6150c43a7d814310f1d4394843c750d5110e6f62544439b1895110e7b60544439e1815110f1d43940439b98a5010e6d6294043d3d8953d0b1e5350e42a798f4290a9d63d0a429798e5190a5d639464297d8d5090a5c6354242ab98b5390b1f5394e42ab9885390aba6014e42ae5805390a9e63d4642a758f5190aba60d4642ae5835190a9e6394642a758e5190b3b5094242a7d8d
  | 7 => 0x1e218895182ca820001f08000002771a485023500020099300022f15600011e80004e99b9548908f518180019e8d09e50001ca9c6a5c94089f14f00013925025f8001b98731430a70ee89109aa05a629a31761cc84c21c8ea0f68429ac0000000629a68f985980028f0cc8280000002170000789d383d80000013d0000f800000025417088f2340000000d88c380000000000018985389300000000000000000000000000028d1748609be1dea0d99d8530001a70001ee98680000018b9fa00000028b96299c0f91cf1de00024b80000016a8d29d9a4e80024d25a00012286e800011016000000044a7b9660002438d180027b1b60001010000d301526d00011800027c8000000e91e78001768000ae0002062841350a40a09dc02c1dd87d9cb91385c8658d48000000a3930a020001c300000004a08e1f181f274a8b105292008a1a8800ab8000000000b580005b80000013580000019f80001d1300001b49c800020c9ce0000a5a9400020c0002460000001db000054822817a100000002040000ab142a330001698a78750002600772658001ea8cd9f722696e2270000e690e06b0001ff08c800220800275240089a7aa710001e98000002698000001c5000000000290a5800008f80004597709387615780000016300020d16d0639728bc05b1af29d81e10d9520000001780001fa9580002452989a5948000000000000000000223a481c496c1000001af9b427901b83e96180000006a26a9e380001715597500000000007f8001e318d8000201438ad16680022486a8000001fc82200480011c00000384f00b0420d207092189b16b1589c18238002578001ba8e307b8000da85d1860948001fd0001970928d005904683a86d80000022c8000000001370000ae8fc00026800009706f80022b0000000fe8080208409e62861ea0bd08aa798bba11a63a2898084fa9b12da37061802233800072057a7828aa0a806a610361cd97a00011480011080013280000000019c8000001d71b18001650729179b506f0000000c19978279d12928741d91a100003591d0000002788000fa8be0000000001d791700000008b1f00000000c80002982108a1178a859690df80002880000015c8000000000db0000002091e08000000001a50e3a01a0880018d11f00000000011c8001072028000de14f93e8b70b899101b1c79c28ff0001e8a488f021e0000000d62319d19881858fd03300025b9c897a9c39061160000000a8a5900024a8d680014d8aa800141000050a3c19185c00000000000021d88580000007021d0878000e8a6f0000000001db866a661eb00000000000000015ea18975800000043800096a892968001f1119049289a93a7e8678b1a112349e195f099a448b117d9ae91218f91b25480028c2291b68c30528af85183928703728e8002430e
  | 8 => 0x1169a080000d8869d80851288000000bd9081c00000400001d00000f490a0cf0001101d08960e404e02900180000000025697d00005a0a50888000000648c00000b900000001f98c0001ef0002068001a90000890e584c80024980006500014b01a00000007a00023d8000002078002598000799e918e245a2502f1cc1e680000003b81c0a20000b7a2a00023a800139a8a25e00000000000005e1e41d51b32768ce0cb18783c14c8001b20000000001bf81824918a8ec8000af12d0000000000002919058b280022193f8000001568000000bb1fb14599f1388000eda729bb0138ef000267a4c27f87810222589e03882d24e0381250dc00291e01ca2e25112125715d021a4fa478fb02a8ec0b61be9c20269fd8991a212f0c708b87906300013e1dc80003f03c8ed0f713a0312368431f30d58f11721d2041a8283e133007a8080c8000451489aa87d11100000022d9980001d280000000014b8001738000001e017fa70a5280001401298ca5d1df0f20819f3a6e0000bf0000580d10000cb936824a308000000d90000298be80a80000029614a25880020800010b8601e10001bb9298002621840000000002199920001ec00000009b80f2278c480000000012b10a8000000070000e29ed0a49d60621909321198688000f0a9300000006600013100000000019396786d07a8000fc8b480005100000008e8670002839540540169259099462140ba0149df80000011f8900001319f58001499ff89508a1fe0000000b38958000dc800000000264a6b9150e70e627d2819828f41b292c9838000981e49da82d8bf8000001ad90c8001fe8000a284a8000000001eb8000c78efa9a0a9a1b9528f30001ef80000000012c000000000071217800000215a8300029c8e484d14425f0a1a6c0ac1811b70001380f881589200015019b00000005ea389610a60000000c29240fd900800000204a050002200001f40001c70b325b00006412f9130040001478cea311cb0251040dd9b10f2811a3f04b9aa26724b0000848560001bc183275a9106c89d8350000da0eb0eba641a01800d502602f82e29709e92e93492815a1a39f293384805f80002582b25225580005a80013f00005d8000398001a180007b19480000021628112921810283b20f09c99983f9968b225e8d39a623816f86920020f9ac8ca89412a9731c080009d0f790325a800000000000000000240a0e9cf81900020e098a3016017400028f9f22471fb80024a0000de80015d8d800017f1a80000000240ba8000001a88d7a669f90062320000aa0001a995e00500000000000021380c0121f8083a360130aca9a80029ba978b40000059510000002329f684da1682b8000001890a317780ba37800000000071a6f8198000000c401ea738000000860b52800e1077a4693400e1471bf02a000
  | 9 => 0x1671689a41361200a022101da5d94e9069c58002399c60871c99989249e28231f48d717e1ca1701960d42950c60000368000000001d59bd25393c80015c000000000000018837a7d80000000e8001ae000212a6c80000000000000000000014492392708d87e2778001f792082723ea6e9278e205723593b00025314e2618000008011b91ba2561bc8f18cf8b80000001da26500000000022c0979bd8f60e515710f0a683d24c80024da1fa1f1ce8c090f80001080008080014180014c1048000fb99a0a82508348821958b98000001f9a390000810d9a0a00000017ea990ff80029000000000000000000000013b80000000000021c0092070002761dd10b28896d8e980023e27427a1d4a8c9a28001e5a281159b791a0000002881621089420c992211296b95300004122a92a0001b58b080026321a074a3d06106825515aa3f8001d400016e91d8cc1b00df03000d0759e81b884715506986b9b3a41800107a7c0000c680000015980000008416f00020397992e00000000013780000003080000018f00022300000019916c88d00000000000028780010d009a2d15f87e9928000000000000000000002240dd000286a5c0ca00026b00000a0000c100021b00006c00016417b0000c50000001f500013da4291402e80029d00000013c00000021483380007c2298002690000001ad00003404b1188e800000027000f8000000000000002261718000000499648000002998000328001e727197c98522b80020ba440cd27300013a8b69fc1b099417c0f595b858a2e82100018b00007ca8500015918a00009c0000a900010192b8000e005f28499e0488479a7832044294a4200019d0000001d329c00023c8db96814a97111a8569ab00000000007f1450000000000001638001c105500027e052082a60a6a22204606e0832958f395b0e18c59cd03a0318000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98d0e72d50438c617396c8a8463431c96315131c18a83128698d0e72d50324c6873a6a419263439d4420c931e1084196a098d487250c504c78421064282638318c6255031c1ee6312a818e0c73189540c686392a9a1863431c95410c31a18e4aa46418d0c72550320c687ba88419063431c954cc431838ecaa26218d0c72551310c706aa0c49886386550604c431a1cea2106490e0e65108324878421065a8243c21083214121a18e6b288410c2d7614c4208694b80a621043681c16110821a18e8b286410c4d7615032086a4b80a819043701c1610c821c1cc6214a210e0e640ca510870631884a8043831903254021c1ee8312a7a060c7418953d0286392a721e81431c95310f40a18e4a9c85a050c7254c42d0307b288419681431c953d0740a18e4a9a83a060d5318941d030ca98c0a0e818394c6250e40a18e4a98852050c735484290306b288419481231c96310640c1ac7290832048c7258f4090306b1ca5a0481131c96314540a18e6a908420589701083210246392c620881231c963d0040c18c6312a99860f7318954cc306398c4aa661431c954d0f30a18e4aa0879850c7255232cc286392a81966143dd4420cb30a18e4aa6639841c7655131cc286392a898e6183550624c730c32a8302639850c7258e548c3072a0c4a1c61431c9540ca30a18e8a90651850d75108328c246392c818c61075da540c630c1ac9290631848c72593308c20ebb4a9984618359252cc230a18e4aa0869851471550434c216392c828a61831506250c30a18e8a90641868842580320c246392c818861231c964cc030a18e6b28859050c7459432c83073188528e41839903294720a1ce729884905267194c42483073288519241431c8540c920a1ceb210649050e7495032482a338ca819241c114c42d4520e08a8196a290704420cb51482933a88428a41c1d4c4214520e08a6210a290546750c85148383aa06428a41c11503214520a8ce7a10a29056270d0851482933a66428a41589c33214520e0885190a290706420c851483822106428a41891905148520c88c628a42907204214720483a0190a390241899905188120c8cc628c409044c7258e5408216392c929841a89086148020d846430a401044c7258c54c4216392c829e21439cf5210b10a1ce9a90658844c7258e5484216392c929c21431cd5210a10a18e8a90650860e6498f5244306320c629221439cb5310910a1ce7a90848850e72d5032442873a6a419221439d4420c910a18ea210648860e6510832443063288419221831906394810c18c831aa408624641855204322318c2a9021981846054810a18e4a98840850c735484204286392a819021431d1520c810a1eea210640850d751083204307b28841902183594420c810c4aca2104208645650c82104294ba88590021525d432c8010
  | 1 => 0x26a402cbe4f20dba001f184c49845101385200215a2002f00000130001d76974d1415e8639239bc554b1c0f8b72116150093f06c8c001a8185c0225b4000645e0002a785a800000013974a6010000086055eb1932d95736c064f3633c0054713212ad24f8ec74101a0bdb8365a0a5946f412985a2c4634cd04718b38240c5c33410c53eab560001535d969d52078cada368018edf020289c894000124300012800221200000005633126a130000003c221a8307711880000019b04003738800000d002fc00005c9141c00000014a002e2a8007f349e4b62b548014000002c47276439ad84880bb80aea348999868f0fae8228d000a0f60064a9c4c75241d1281d2b1b9020007b5800e12499c70212086544c04d851a8000017d081a6a9447ab3262acb48b319647eb2620c8167312ad9b01c3d0060e018240e00070280801048240200020040204000140802058000a060c8140803000080800008b014010000802060100c2412030f8002201828000b00000000f0580002020006012010000c0001020bc0c001cd2a70d905250ea5386c62928783d946250c43c1eea3128621d0c7250e5210e8639286a88878350c6254443c3286302a221d0c7250e5010f06a1cc528087439cb5394e4291ce730ca42148c735825210a87396a92a465835944310832a52e1328841948e74986520ca463a2c129065325c36510832b14e1b28841958970d94420cac5384ca21065625c26510832c1aca328841950f75584420cac5b82c221065621c16110832b14e0308841958970184420ca86bacc021065a2580601083291cec212a21968842d81510cb44210c0a8865a210a6014432d1084b00a21948d7610a500cb84212a028065431cd5210b4189ce5b1aa120e0c531894350687396a621283439cf5210941c1cca21064a0f08420cb50506943928628283c21083214141c1ee8312a620e0c741895310686392a721883431c95310c41a18e4a9c8420d0c7254c4210707b288419083431c953d0441a18e4a9a8220e0d53189411070ca98c0a0883831506250f31a18e8a9065
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x7521802000d580c910023000a08860a0a80dd46250c43a088250c6054443a0a80dd06254c41a088254c6050441a0a80dcc625503180c87550624c431a0882550604c431a0a80dd06254f40a088254c6050740a0a80dcc625533080c87550624c730a0882550604c73080c87592520c63080c8759252cc230
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 227
  | 2 => 14
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
  | 6 => packedAt s3K6 (802+((h/14+packedAt s3K6 (704+(h % 14)*7) 7) % 69)*7) 7
  | 5 => packedAt s3K5 (27286+((h/296+packedAt s3K5 (24030+(h % 296)*11) 11) % 1890)*11) 11
  | 4 => packedAt s3K4 (55826+((h/446+packedAt s3K4 (50920+(h % 446)*11) 11) % 1945)*12) 12
  | 3 => packedAt s3K3 (11798+((h/75+packedAt s3K3 (11123+(h % 75)*9) 9) % 273)*9) 9
  | 2 => packedAt s3K2 (860+((h/4+packedAt s3K2 (840+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfff03fff81ffffff81fffe07ff03ffff3f8e3f
  | 1 => 0xfffffffffffffffffe07ffffffffffffc3ffff
  | 2 => 0xfffc07ffe03f80ffff83ff81ffc0f80fcf3cc
  | 4 => 0xf000007ffffc000fffffc0001ffff000ff03f0
  | 5 => 0xffffff800000000fffffffffe0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x929485188c48934380594a4325219caa1d8615
  | 1 => 0x24210a21109124041602948c4a4621544238ea
  | 2 => 0x88c2934a243a4159aaa8275113a88e06acd34c
  | 4 => 0xce8b2c744920766ecd34c1861cf3c418f703b0
  | 5 => 0xf0c307871c3878f71c739e780c30860fbec00
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xe8e8c8c8c8c88888e8e8c8c8c8c88888e8e8c8c8c8c88888e8e8c8c8c8c88888e8e8c8c8c8c88888e8e8c8c8c8c88888e8e8c8c8c8c88888e8e8c8c8c8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x7400600000005a1011a4e98c9506b0f2e1c3520c526d1a51070000001c03160004aa0050585000051022000004200c0140000005059793008890f00000002e00f80560204602060030b26240800c00101ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32de32fd32fc32dc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x98002d8ed188d2b820bc0c278c01c39039bd002708a4c0c910b9ec5e9a291f442a34d8f53a042b0011e242a804f44a228012a731e000f2674c8010882080fcee504b05032000000000484e00c58003004c2c0000014000a0011c4a002fa0c561d1a088e4460f9751441331390a3a000c81e0000000dc401f1e0b40b2880092000aa90fe7e19800000032800006c168a8d67143950001c220007000091a8e0000000000613212cec680010d0c2329a7c409751280369800034ea6d2c18c9a004480800000000030903e00000692c8c40000048006c28312380000002783437000d400a117000000014a49288145878b88800098e842000a83020380840301828001008202000003068003010080000180008000030284000900000080808280868007820083008080000300804f94b439f28e873d50d0e7aa921dbd4943b6292879f5350f5ea4a1cf14943d6292872c5250e78a2a1cfd41439f2a0875e53d0abaa7a14f54e429f294853e5190a7aa12157d4d42ae29a853d5310a7ca4216b948429f288853d5010a7ca9994f55332d6216653f548ca78a91967d0e32cea1c659f548cb38a9195794a32cf214659c428ca7ea8994f151329f2a0653d540cb3e86196750c32d6210659e540cb3aa8195794832e729065cf420cb3c84196710832e6210658c420ca7aa720cf94a41cf194839c329067ca320cf54241af298835d531073ca620cf54c41cea98831d531067ca420e78c841ce190833e511076ca220cf540419f2a6633d54cc73a8798cfd52319e2a4633f544c678a898e750d31b7a92636c524c6f6a098de141319f2a0633d540c67ca990cf553219f2a4433d54886bca710d754e21e6194433f5448678a890d7d4d21ae29a437b50486f0a090cfd50219e2a043cc32086bca7a05754f40cf29e813d53d033aa7a04754f409f296819e32d033865a04f947409eaa4813f5350278a4a0678c940ce192813c5150376a0a04f950409f2a6613d54cc27ca9184f55230cea1c616e528c2daa5184f951309eaa2613e540c27aa8186750c309faa6413c54c839865904f952209eaa4415e53882baa7104fd51209e2a2415f53482b8a690730c920bba8a4174514827ca8104f550209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x95b80728159900b02900000014300001c2604b3b346d7032ab44a85e0191f10d55231c9db1d224930b08cd83a441c00f1a0188000d001e0084017480030a040003800a40001800084800e00118060061104200843800080c3d4c5250f0f63149438758e5190a1f63542428e580548ca8e62d5232a3988548ca9960152328b594420ca8e6290832a3d94420ca8d6510832a3984420ca8d6010832c3948329061f635424193189531062c6254c41a3189531070f6254c4187189531070c6254c4183189531061f658c84187594321068c6250f318b98b548c61c6550d31a3189434c70d4314931c650c504c61d6395321c3950328861d63150218e580540870c540c8219318953d022c6254f40a318953d030f6254f408718953d030c6254f408318953d021f658cb408759432d030c520c9408758c515028c6250e30c350e528c21d63951308b189544c2346155130a3189430c21d6315320c315032c830c540c920d10c8514821d63950208758c54c421d6395210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1012741800204051820285386c629287225c3651083281ce5b1aa120d087250c504c606bb0a819043425c0540c821818e4b18a2a040c7258e5408206392c62a621031c96395210
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
  | 4 => packedAt s4K4 (4895+((h/55+packedAt s4K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf03fff81fffffff81fffe07ff07ffffe7e31ff
  | 1 => 0xfffffffe07ffffffe07fffffff81ffff8ffe3f
  | 2 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 3 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1485188c41224c180594a432503299543610d5
  | 1 => 0x210a211032449021602948c4a48122a888e62a
  | 2 => 0x42934a2490e904caaa82751139540c0d534b4c
  | 3 => 0xb2c74492481d974d34c1861ce69c031ec0db0
  | 5 => 0x8c307871c70e1e7f1c739e780c7188c1ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xe8c8e8c8e888e888e8c8e8c8e888e888e8c8e8c8e888e888e8c8e8c8e888e888e8c8e8c8e888e888e8c8e8c8e888e888e8c8e8c8e888e888e8c8e8c8e888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x1c0000003c230000000009f8b208225a0f000240000000bc80000022c7c8004ba000000003e00001a800000000078004102686800000048800000000001218002940012d0001d459c1a1242aa00007000000710001a70246bc000001680000000021a8f4c680002e0004386a1480011a80015c845180000007a0000000003f8000160c80007d0004a06c0000000000000000046c68126a1c2902dc6a8000000000000000077c00224000160cc0000000005e9a8130589020901225b85191a00026c730000000012b0dd19a000a093900054c0000000041415800000000e4a8523a00000000184904fa800000000180004be32c0a9022aca40990f839e23c8b27f0181cc000ff000000ad0000000011b8000b20000007f29e524000b6000000000000160000000033c000001b80003d000000000000000cc4da68400000000001029920003582a0000000010692f3f8798001a930c2100026c43c0000014c00091c240000000010c85a000000470e5000918650ad0340013980a0f60013e17e000000f28fb304320001a50da45400225000000002922fa9e4db00036483811000080000f200027c000000000c6780198004ee084000d20000009e9732387503e97012c0012480000080800000000000af16a00000000110000000fd800000000fa000000880f706e182460001c808c000000002101e8000000007fc000000ec0000010c224000000000000006280000000000000001002000000000020000000000e0040400000000000802002000038010000000000300401000001000000000020060000000000000000000000000000000020040000300000000000006000008000000000100000001c000020000100000000200400001004000000000000040080000600800801000020008000020000000200a0000000200000400000004000008010020000200700200c0280100000003002004028018070000040000100000000800004000008010000080100000000c00803002008008040020000000400000000800008004000010000000000100801001003000000008000080040000100000001801000008008030000040100100400c0000000400000000000000008000060000080700000002001000010000020080100080300a00000800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x1740000000000000000000106000000000262bc00075000000000000000000000000000000000000000128503686f0490004b600000000000000dd267000390d5000000a500000000000012000286858000e8000000000001fa8ed1f2690000000000000081c8380000059400000000000000620000000020300000000000000001388002c600000000000000000003980006480000024c000000009d4788000002c4290004203a40016d00054800032000001090000003647b000000000d58b82d6000000001a6650000431e0624000310060011c8002ba001460000009540000013ca2c000000d02ac00000000001288000000000000052a2fc002334a80000023c09c9e92280024a9980004c1c4000da8004dc000000000000000022700000000000000000bf800000000000000bc71c8a28a0006b4000060005e000000000000c80004540010d80050415c00000000000000002a2664001880008b05099f0222c8000c02843b800000000888002230001c0000000ba000250780b88a400000000000000ce000000001ed4121f8000de0323454428700008c759691143800028f000000e18003588c8ed8003ba000800000001d02280038c0000000000000143000000770001d000012c0024a3b08680001845c000000000000000001d35c4d80008d0006141da440005e8c6056000000001b9232668222960ee674000c600013400000000000000004a49bc448000ce754e59613b2000002580004ec5a80049c74c301ca2b0000000000000000000000000000000000000002780000007794617600000000000818002010006049514b1c6254001f23ac0000000000000000000000250c00001ae800cb02d12e1ac3c8000006f81524c3f0000000001f8000f3a0b0007140000004c0b0000000000000027b052a0c0022622240c178000002b0981292ee000fb0001ce000790000005380000008e000000005222049d0384fa908000000be93c000004c400132000000000c2000000000000a600000000000000a04000004b2000a2000256000599e94428ac000be000000f9a6800036cf58f71400a000000000000fd20f000000cb9ea0a600000000000218c89280005b03e000000000c50000020008f000000021468aa0008e0000b000000093a172e4000b78000000f40000000048c000000cc7382a9a300037c00000008708289c10000008d80026a0012e0004301c8000004e8438000003f200000000000830c3a312ec000a68004d400000000000000f109c3c6000cd8005260000028913a0000000022e00000000000000000000004b8762534bc4180006c0003ccfe8650000006a000000000001b32142e5240000000000004f2400000000000084c000690000000000000042c0f8002120000000000000080a760007dcd200006e0000489f00
  | 4 => 0x34c000000882780000021d474124001952b6000000000009c12b80000a0006c10f31c5f00e1de3a4384308da074000df800000000001f1000000a2a0a3068b40d8000000002083e28e0001c9740005c40000014e4cc00261000000e68020000000013f5080000003f338000001210002a000157000000ff000000000e001032649800000000001140003a2a00af8000005000000000000089a6b000000ed000000000b31e12f60002d8002a8540f6000270200002630000011f8002d00010a21f45e688000c452e00063800000000000000009c86e10400000000000000000001593ae000000a249609c0000042a4c40000000000000000000000000a5000000000001786dc000000000000000000000042820000000001b100000000160000000000000de000000000847bd1a11f000001300000003d4000000004b000000152000000002ea62c618000004d09b80001a000de8000000d87680019e0b947071000994000000000000000000000000099000000000142b8000000000006ec0018f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x3240b01a20f17a530001d90d079cbf093000000608de1c0000ac8b9200000280001a00cc000aa3a25807e000246000000003982d47a94f19a0005b0df3a40a0221b330e6185c0a62b455c2b024038014fc8250b032840800000620f7800312538001172a0710b480000043c10800000798ec1c20c27707d0991886583e1242f042cb58000008383708e000690000000005dc0000020e0000000038e450a981a25e270bb086158258fb08d0520000000037a74c7580021c70c0006c3e814cb887e0b2314ff89f000000bd8000000000004d3ea0002a000208000e58360281dc8619e01c268e504a000220001153600001a8000000000000021a000dc00018e0000507538200000a13000758169a30004cce31da00052c0000017e040000000000141700001000000200001004000060100000c04000000040d0040102800010050480000c0b0b8050140501c00000100140a004200040500808000000480400c010240100c00000100000501c2500000018010502200005000000000400c0103002014110280004000010090040b0100406c0f01401004000140c02c0500804020010800500800004090180300c0002c000040b03c06008000000300002024010381a014030005d00001018100440100808004020000d008010900000400008000000700800010000000203c140080e0540101002000020180007c060380d0026f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x4b800000000c0a0b15a77cca15f316000000d30002400c0033d64582b80000038426000000560000ba1ac000001e5000474000000000006013b000260000002c27f4000000003f8000ae1da7a4a09ec256000760002e4000000cc3145e48194842a788000003006f8000000000000000030a6ec002111a21906d20223258c2d08b2dc6b4b99983364f4af1b6250170069ea0a4188021b907e7c48c0dd33a5b49b9db23836cc800028c2903182603e000841391ca38c000003a06a0a194a08a1240007d000000cd01d0000006e1640f0000001700007cc0000017c804f08f6000000781931b02dc2fa060006bc4618411e000000461c4000000000007910c8004100010c0670003fc950f90000bc4d80016656c5d800304810488303407008f1300de1d0f69a90464e8d8905222000111a723e29c618af0e2000fe2102248306a8f726406c420322342488083c08e5001506b2847810299140621cee9c54005f10698f1ce2ac2799742e694200002ca174f7042128000a29b41140010a0003441c8002070006dc7998d0004fc030550004f0000a5000198048b20f459c4490a0e64f8000000d40005114409c7e8380001407782416c2a22c0ce03a0263c86787f02e1441d8f42b8180158822ea4d8ff12c3ee031049211a80dcca9d70d2000000f835678ccf9ac1908683c80f2d4574e7126162524901133062f09497428e5fc0a97a27084800000364588000c23906d4b78ee02c3187d9680044b8939bf0004d49105e3a86e8f80001de3f4000430004401c17d3540008491b000000038003786b813925106000d3012192044000b41b2064a90e91cc0c40007b0da6840000039e858b31d520c2746b8080ec55051800000390fc18e000724058000000f4549022620000005b1a4284ab09503c3a0968a839a630cc8851967a0f902e19c19420a0a13c0e4a683e268200788ea096554fd82
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1802c055100100a00001300001600000000039401730000024300000548000000f207000000000602350100020001020058318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x21a080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 3 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 4 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 3 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 4 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888eac8e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xb0040d001af108000f58240000013000150f00c8000000199d005d33e00380223e808800000000002403a687822750000014afc02c6cedb80006c00032b9c005a706310e000166a154b9288c000042801506ac906302002f0204080000604184000010400083091a0c48001ffd5005fe5401ff55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc4301ffd4807fe52005f94807fd5201ff148077c52017fd0801fe42007f50805fc4200ffcc803fe3200ff4c803fc3201ffd4407fe5101ff54407fc51017fd0401fe41007f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4007fe5001ff54007fc50017fd0001fe40007f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200bdf1951001cf8ca88003ff64440017fb222000efd91100057ec88802bfe64440057f3222000ff59110005fac88802bfc64440057e3222000ef1911001578c88802fff5444015ff2a2200bff55110057f8a888027ff63440137fb1a2000f7d8d10005bec688027fe63440037f31a2009ff58d1004dfac688027fc63440037e31a2009f718d1000db8c688027ff5344013bfa9a2009ff94d1004ffaa6880277d5344013fe29a2009ffd0d1004ffc8688027fd4344013fe21a2000ffd8910005fec488003ef624400177b122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488003ec624400176312200bffd491005ffca4880037e5244017fea92200bff1491005ef8a48802bff4244001ff2122000ff50910057f88488027ff3244013ff1922009ff4c91004ff8648802fff5144009ff28a200bff54510027f8a28802bff4144009ff20a2000ff50510027f88288027ff3144009ff18a2009ff4c510027f86288003ff2144009ff10a2000ff48510027f8428802fff5044017ff282200bff5411005ff8a08802bff4044001ff2022000ff50110057f88088027ff3044013ff1822009ff4c11004ff86088003ff2044001ff1022000ff48110007f84088013ff1044009fd8822000ff84110007ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013be64040055f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c80801fff540400dff2a02007ff55010037f8a808013ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c1002dfac608013dd63040016eb182004ff18c10025f8c608017ff530400bbfa982005ff94c1002ffaa6080177d530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe62040017f3102004fb98810005dcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481003ffca4080037e520400ffea902007ff1481003ef8a40801bff4204001ff2102000ff50810037f88408017ff320400bff1902005ff4c81002ff86408012fe6104009ffa882004ff94410027faa208013fc5104009ffa082004ff90410027fa8208013fc4104009ff9882004ff8c410027fa6208013fc3104009ff9082000fdc8410027fc4208013fd2104009fe1082004fd08410045fcc00801fff500400fff2802007ff5401003ff8a00801bff4004001ff2002000ff50010037f88008017ff300400bff1802005ff4c01002ff86008003ff2004001ff1002000ff48010007f84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x3ec21080297f3004013ffd402009ffca01004ffd5008027fe2804012ffd0020007fc8010003fd4008025fe2004011ffcc02008ffc6010047fd3008023fe1804000ffc8020007de4010003fe2008001fd1004000ff48020007da4010003f92008009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2010bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262000bf59310027f8c988012fc64c4021ffaa6200fff95310087faa98803ffc54c4009ffb1e2004bfd8f10027fcc788006fe63c4009feb1e200ebf58f10027f8c788012fc63c401dffa9e200edfd4f10077fca78803bfd53c401dbea9e200eff14f10077fe878803bfe43c401dfea1e200eff10f10027fec588012ff62c4009ff3162000bf98b10027fac588002fd62c4009fe3162004bf18b10087fea588043fe52c4001bf2962010ff54b10087f8a5880437c52c401fffa162000ff90b10007fa858803ffc42c401dff996200eff8cb10077fa658803bfc32c4009ffa8e2004ff94710027faa388013fc51c4009ffa0e2004ff90710027fa8388013fc41c4009ff98e2004ff8c710027fa6388013fc31c4009ff90e2004ff88710027fa4388013fc21c4021ffa862010ff94310087faa188043fc50c401fffa062000ff90310007fa818803ffc40c401dff986200eff8c310077fa618803bfc30c4001ff9062000ff88310007fa4188003fc20c401bffb2c200dbfd961006ffccb0800efe658401bfeb2c200dbf5961006ff8cb0800efc6584001ffb242000bfd9210067fcc90800afe6484001feb242000bf59210067f8c90800afc648401bffaa4200cff9521006ffaa908033fc5484011ffb1c2008bfd8e10047fcc708006fe6384011feb1c2008bf58e10047f8c708006fc6384011ffa9c2008dfd4e10047fca708023fd5384011bea9c2008ff14e10047fe8708023fe4384011fea1c2008ff10e10007fec508002ff6284001ff3142000bf98a10007fac508002fd6284001fe3142000bf18a1006ffea508037fe5284001bf294200dff54a1006ff8a5080377c5284019ffa142000ff90a10007fa8508033fc4284011ff9942008ff8ca10047fa6508023fc32840137eb0c200dffd4610027fca308037fd5184009fe28c200cffd0610027fc8308003fd4184009fe20c2008ffcc610027fc6308023fd3184009fe18c2000ffc8610007ee4308013fe2184001fe90c2004ff08610007e84308012fe608401bffa84200dff9421006ffaa108037fc5084019ffa042000ff90210007fa8108033fc4084011ff9842008ff8c210047fa6108023fc3084001ff9042000ff88210007fa4108003fc2084009ff8842000fdc4210027f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f32a200bff5951005dfaca8802ffc65440077e3
  | 2 => 0x20007fac310002fd6188001fe30c401affd46200d7fca31006bfd5188035fe28c4019ffd0620007fc8310003fd4188033fe20c4014ffcc6200a7fc6310053fd3188029fe18c4000ffc8620007fc4310003ee2188001fe90c4000ff08620007d84310046fe6088035ffa84401aff942200d7faa11006bfc5088033ffa044000ff90220007fa8110067fc4088029ff9844014ff8c2200a7fa6110053fc3088001ff9044000fbc8220007f64110063ff65480317fb2a4000dfd9520004feca90063fe65480077f32a4018ff595200c5faca90063fc65480077e32a4018df1952001cf8ca90003ff64480017fb224000efd91200057ec89005ffe64480057f3224000ff59120005fac89005ffc64480057e3224000ef1912001578c890063ff544802fff2a24018ff551200bff8a89005bff634802d7fb1a4000f7d8d20005bec69005bfe63480037f31a4016ff58d200b5fac69005bfc63480037e31a4016f718d2000db8c69005bff534802dbfa9a4016ff94d200b7faa69005b7d534802dfe29a4016ffd0d200b7fc869005bfd434802dfe21a4018ffd49200c7fca4900037e5248031fea924018ff149200c6f8a49005fff4248001ff2124000ff509200bff8849005bff324802dff1924016ff4c9200b7f86490003ff61480017fb0a4000fdd8520005eec290003fe6148001feb0a4000ff18520025f8c290003f461480017a30a4018ffd45200c7fca290063fd5148031fe28a4017ffd0520007fc8290003fd414802ffe20a4016ffcc5200b7fc629005bfd314802dfe18a4000ffc8520007de4290003fe2148001fe90a4000fb48520007f84290063ff5048031ff2824018ff541200c7f8a09005fff4048001ff2024000ff501200bff8809005bff304802dff1824016ff4c1200b7f86090003ff2048001fd9024000ff88120007dc409004fff65080277fb284013ff9942001dfcca1004ffd65080277eb284013ff1942001df8ca10003ff64080017fb204012ff99020015fcc810003fd64080017eb204012ff19020015f8c81004fff5408025ff2a04013ff55020097f8a810047ff63080237fb184011ff98c2000dfcc610047fd63080237eb184011ff18c2000df8c610047ff5308023bfa984011ff94c2008ffaa6100477d5308023fe2984011ffd0c2008ffc8610047fd4308023fe2184015bf9882009ffea41004ffe5208001bf2904013ff5482009ff8a41004f7c5208025ffa104000ff90820007fa841004bfc4208023ff9904011ff8c82008ffa6410047fc3208001ffb084000ff98420025fcc210003fd61080017eb084000ff1842009ffea21004ffe5108027fea884013ff14420097fe8210003fe4108001fea084012ff1042008ffe6210047fe3108023fe9884011ff0c420007fe4210003fe2108001f71084000ff48420007f8421000
  | 3 => 0xeb1a801dbf58d400eff8c6a0006fc635003bffa9a801ddfd4d400effca6a0077fd535003bbea9a801dff14d40017fe86a000bfe4350005fea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0002fc625003dffa92801eff94940006fca4a007bfd525003dfe292801edf14940017fe84a000bfe4250005fea128002ff109400effe64a0077fe325003bfe992801dff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0012fc615003dffa8a801eff945400f7faa2a007bfc5150005ffa0a8002efd0540017fc82a000bfd4150001dea0a8002ff105400effe62a0077fe315003bfe98a801dff0c540007fe42a0003fe2150001fe90a8000ff08540015fec0a007bff505003dff282801eff541400f7f8a0a000bff4050005fda028002ff901400077c80a000bfc4050005de2028002fe101400effe60a0077fe305003bfe982801dff0c1400e7fecb90072ff65c8039ff32e4003bf997200e7facb90072fd65c8039fe32e4003bf19720007fec990002ff64c8037ff3264002bf99320007fac990002fd64c8037fe3264002bf193200e7fea99006ffe54c8039feaa6401bff153200affec790056ff63c802bff31e4001bf98f200affac790056fd63c802bfe31e4001bf18f200affea7900577f53c802bff29e4015ff54f200aefaa790057fc53c802bffa1e4015ff90f200affa8790057fc43c8039ffa96401cff94b20006fca590073fd52c8039fe296401cdf14b200dffe8590003fe42c8001fea16401bff10b200affe6590057fe32c802bfe9964015ff0cb20007fec390003fe61c80097f30e4000ff58720005fac390003fc61c8039ffa8e401cff947200e7faa390073fc51c8037ffa0e4000ff90720007fa839006ffc41c802bff98e4015ff8c7200affa6390057fc31c8001ff90e4000fbc8720007fc4390003fd21c8001f690e4000ff087200e7fea190073fe50c8039fea86401cff143200dffe8190003fe40c8001fea06401bff103200affe6190057fe30c802bfe9864015ff0c3200d7fecb1006aff6588035ff32c4003bf996200d6fccb1000e7e6588035feb2c401abf59620006facb100027d6588035fe32c4003bf19620007fec910002ff6488033ff3244002bf99220007fac910002fd6488033fe3244002bf192200d7fea910067fe5488035feaa44019ff152200a7fec710052ff6388029ff31c4001bf98e200a7fac710052fd6388029fe31c4001bf18e200a7fea7100537f5388029ff29c4014ff54e200a6faa710053fc5388029ffa1c4014ff90e200a7fa8710053fc438802d7eb14401affd4a200d7fca5100037e5288035fea94401aff14a200d6f8a510067ff4288001ff2144000ff50a200cff88510053ff3288029ff1944014ff4ca200a7f86510003ff6188001ff30c4004bf986
  | 4 => 0x803ff60484017fb024200ff98121007fac090803fc60484017e3024227ffd412113ffca09089ffd504844ffe2824226ffd0121137f88090897ff304844bff1824225ff4c12112ff86090813ff65084097fb284204ff9942101dfcca10813fd65084477eb284204ff19421025f8ca10813ff64084097fb204204ff99021015fcc810813fd64084017eb204204ff19021025f8c81088fff5408445ff2a04223ff55021117f8a810813ff63084097fb184204ff98c2100dfcc610813fd63084437eb184204ff18c21025f8c610887ff5308443bfa984221ff94c2110ffaa6108877d5308443fe2984221ffd0c2110ffc8610887fd4308443fe2184224bf9882111ffea41088ffe5208401bf2904223ff5482111ff8a41088f7c5208445ffa104200ff90821007fa841088bfc4208443ff9904221ff8c82110ffa6410887fc32084097f3084204ffd4421027fca210813fd5108409fe2884204ffd0421027fc8210813fd4108409fe2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da4210803f52108409ffb004204ff98021005fcc010813fd60084017eb004204ff1802111ffea01088ffe5008447fea804223ff14021117fe801088bfc4008443ff9804221ff8c02110ffa6010887fc3008441ffb2c8020bfd9640107fccb2000efe6590041bf32c80039f99640107facb20082fd6590001beb2c80009f59640107f8cb2000efc65900057eb248002ffd5240017fca92000bbe5490005feaa48020ef55240017f8a92007fff639003f7fb1c801fff98e4000dfcc72007ffd639003f7eb1c801fff18e4000df8c72007fff539003fbfa9c801fff94e400fffaa72007f7d539003ffe29c8002ffd0e400177e872000bfe4390005fea1c801fef50e40017f88720003ff6290001ff3148000bf98a40007fac520002fd6290001fe3148020ffd4a40107fca5200037e5290041fea948020ff14a40106f8a52000bff4290005ff2148000ef90a40017fa852000bfc4290005de214801fffcca400fffc652007ffd329003ffe1948000ffd8640007fcc320012fe6190001feb0c8000bf58640007f8c320083ff5190041ff28c8020ff54640107f8a32000bff4190005ff20c8000ef90640017fa832000bfc4190005de20c801fffcc6400fffc632007ffd319003ffe18c8000ffc8640007fc4320003fd2190001fe10c8002bf98240107fea120083fe5090041fea848020ff14240017fe812000bbf4090005fda048002ff10240017f0812007fff309003fff184801fff4c2400fff8612007bff655003d7fb2a801eff9954001dfccaa007bfd655003d7eb2a801eff1954001df8caa000aff6450005ffaa28002ff95140017faa8a000bfc545003bffb1a801dbfd8d400effcc6a0006fe635003bf
  | 5 => 0x8f21127fea7908937f53c8449ff29e4224ff54f21126faa790893fc53c8449ffa1e4224ff90f21127fa8790893fc43c8459ffa96422cff94b21006fca5908b3fd52c8459fe296422cdf14b2115ffe8590803fe42c8401fea16422bff10b21127fe6590893fe32c8449fe9964224ff0cb21167fea390813fe51c8459fea8e4204ff1472115ffe8390813fe41c8401fea0e4204ff10721127fe6390813fe31c8449fe98e4204ff0c721007fec190803fe60c84017f3064200ff58321005fac190803fc60c8459ffa86422cff94321167faa1908b3fc50c8457ffa06422bff10321127fe6190893fe30c8449fe9864224ff0c321027fecb10812ff6588409ff32c4203bf99621026fccb1080e7e6588409feb2c422abf59621026facb108027d6588409fe32c4204bf19621027fec910812ff6488409ff3244202bf992210277cc91080abe6488409feb244200bf592210277ac910802bd6488409fe3244204bf19221157fea9108a7fe5488455feaa44229ff15221027fec710812ff6388409ff31c4201bf98e21027bcc710806de6388409feb1c4228bf58e21027bac710802dd6388409fe31c4204bf18e21147fea7108a37f5388451ff29c4228ff54e21146faa7108a3fc5388451ffa1c4228ff90e21147fa87108a3fc438844b7eb14422affd4a21157fca5108037e5288455fea94422aff14a21156f8a5108a7ff4288401ff2144200ff50a2114ff885108a3ff3288451ff1944228ff4ca21147f86510812fe6188409ffa8c4204ff94621027faa310813fc5188409ffa0c4204ff90621027fa8310813fc4188409ff98c4204ff8c621027fa6310813fc3188409ff90c4204fbc8621007ee4310813ff6088409ff3044200bf98221027fac110802fd6088409fe304422affd4221157fca1108abfd5088455fe2844229ffd022114ff881108a3ff3088451ff1844228ff4c221147f8611089fff654844f7fb2a4200dfd9521004feca9089ffe65484077f32a4227ff5952113dfaca9089ffc65484077e32a4227df1952101cf8ca90803ff64484017fb224226ff99121015fcc890803fd64484017eb224226ff19121015f8c89089fff544844dff2a24227ff55121137f8a890897ff634844b7fb1a4225ff98d2100dfcc690897fd634844b7eb1a4225ff18d2100df8c690897ff534844bbfa9a4225ff94d2112ffaa6908977d534844bfe29a4225ffd0d2112ffc8690897fd434844bfe21a4227ffd492113ffca4908037e524844ffea924227ff1492113ef8a49089bff4248401ff2124200ff50921137f88490897ff324844bff1924225ff4c92112ff8649089fff5148409ff28a4227ff54521027f8a29089bff4148409ff20a4200ff50521027f88290897ff3148409ff18a4225ff4c521027f86290803ff2148401fb90a4204ff88521027dc4290
  | 6 => 0x3fe98a8431ff0c542007fec0a1002ff6050801ff3028400ff58142007f8c0a1002fc6050865ffa828432ff94142197faa0a10cbfc5050805ffa028402ff1014218ffe60a10c7fe3050863fe9828431ff0c142027fecb20812ff6590409ff32c8203bf99641027facb208c2fd6590409fe32c8204bf19641015fac92080bff5490405ff2a48202ff55241017f8a920813ff63904097fb1c8204ff98e4100dfcc720813fd639045f7eb1c8204ff18e41025f8c7208bfff539045fbfa9c822fff94e4117ffaa7208bf7d539045ffe29c8202ffd0e41017fc872080bfd4390405fe21c8204ffd8a41027fcc520802fe6290409feb148200bf58a41027f8c5208c3ff5290461ff2948200df94a41187faa5208c3fc5290461be2948202ffd0a41017fc852080bfd4290405fe214822fffcca4117ffc65208bffd329045ffe1948204bf98641027fea320813fe5190409fea8c8204ff14641027fe8320813bf4190405fba0c8204ff10641027e88320813ff3190409ff18c8204ff4c641027f86320813ff6090409ff3048200bf98241027fac120802fd6090409fe3048230ffd4241187fca1208c3fd5090461fe2848202ffd0241017f8812080bbc409045fff984822fff8c24117ffa61208bffc309045dffb2a822ebfd9541006fecaa08027f655045dff32a8203bf99541177facaa08bafd655045dfe32a8203bf19541176f8caa080e7c65504097fb228202ffd5141017fca8a080bbe5450405feaa2822eef55141017f8a8a08b7ff635045b7fb1a822dff98d4100dfcc6a08b7fd635045b7eb1a822dff18d4100df8c6a08b7ff535045bbfa9a822dff94d4116ffaa6a08b77d535045bfe29a8202ffd0d410177e86a080bfe4350405fea1a822def50d41017f886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e312822effd4941177fca4a08037e525045dfea92822eff14941176f8a4a080bff4250405ff2128200ef90941017fa84a080bfc4250405de212822dffcc94116ffc64a08b7fd325045bfe1928202bfd8541177fea2a0813fe515045dfea8a8204ff14541017fe82a080bf74150409ff20a8204ef90541027f882a0813bc4150405fa20a822dffcc541027fc62a08b7fd3150409fe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08bbff505045dff282822eff54141177f8a0a080bff4050405dfa028202ff1014116ffe60a08b7fe305045bfe982822dff0c141167fecb908b2ff65c8459ff32e4203bf99721167facb908b2fd65c8459fe32e4203bf19721007fec990802ff64c8457ff3264202bf99321007fac990802fd64c8457fe3264202bf19321167fea9908affe54c8459feaa6422bff15321127fec790892ff63c8449ff31e4201bf98f21127fac790892fd63c8449fe31e4201bf1
  | 7 => 0x3a00800801000400200000000000c00800000600001200002000000400000200800000400000200600001a00001a00001e00a00000000e00800000000200400e00000603005000000800200200201600002a00a00200800000601e00a00a02603400000400000600dfd92521b6fcc9290037d649486dbe324a435dfd8e521acfec7290d77e639486bbeb1ca4359f58e521aef8c7290d77f439486bbf21ca435df50e521aef8872900f7e62948073f314a403db98a521b6fe85290db7c429486bbf994a435df8ca521aefa65290d77c3294801bfb0ca400df98652006fac3290037c619486dbfa0ca436df106521aefe63290d77e319486bbe98ca435df0c652006fec1290037e6094801beb04a400df182521b6fe81290db7c409486bbf984a435df8c2521aefa61290d77c3094869ffb2c8434bfd96421a7fccb2100efe6590869feb2c8434bf596421a7f8cb2100efc65908057eb248402ffd5242017fca92100bfd5490805fe2a48433ffd8e4219dfec7210cffe63908037f31c8433ff58e4219dfac7210cffc63908037e31c8433ffd4e4219efea7210cffe5390867fea9c8433df54e4219ff8a72100bff4390805ff21c8433ef90e42017fa872100bfc4390805de21c8402bf98a421a7fea5210d3fe5290801bf2948434ff54a421a7f8a5210d37c5290805ffa148402efd0a42017de852100bfc4290805f62148433ffcca4219ffc65210cffd3290867fe1948400ffd8642007fcc321012fe6190801feb0c8400bf58642007f8c3210d3ff5190869ff28c8434ff546421a7f8a32100bff4190805dfa0c8402ff1064219ffe63210cffe3190867fe98c8433ff0c642007fec121003fe60908017f3048400ff58242005fac121003fc6090869ffa848434ff942421a7faa1210d3fc5090805ffa048402ff102420177881210cfff3090867ff1848433ff4c24219ff861210cbff65508657fb2a8400dfd9542004fecaa10cbfe65508077f32a8432ff59542195facaa10cbfc65508077e32a8432df1954201cf8caa100aff6450805ffaa28402ff95142017faa8a100bfc5450863ffb1a8431bfd8d42007bec6a1002df6350863ff31a8401bf98d4218ffac6a10c6fd6350863fe31a8401bf18d4218fb8c6a1006dc6350863ffa9a8431dfd4d4218ffca6a10c7fd5350863bea9a8431ff14d42017fe86a100bbf4350805ff21a8402ff50d4218f7a86a100bfc43508057fb128432ffd4942197fca4a10037e5250865fea928432ff14942196f8a4a100bff4250805f7a128402ff909420077c84a100bfc4250805de2128402fb1094218ffe64a10c7fe3250863fe9928431ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1012fc6150865ffa8a8432ff94542197faa2a10cbfc5150805ffa0a8402ff1054218ffe62a10c7fe315086
  | 8 => 0x4000000ecc0012880011e9650230000000000abc308a79b48d4c0001c18510e43396a0f41860a0cc7d02c000e5400000058827c4c0c882e06e53cc7ad3ac000704b0c001711408000000001b44508000001b180000000000005216a58a4c7439c0016b00000006b9799060caca386f82548f0bccd44e59184160c9d97c00146c95d229990ca08a0ffc4c4000aed4ac26c11c164f703b11f0f00700674d88ec90701fdb2c00184d2c0f210f869cf9400102850ca407605240001940011b4b2c00030c000218000000000000000b798f4b7c98980944427400080807000171800139974ce85220ce99a80c800141cce518000124c0000001cc000fc19d000000e02201002600000000000200001e00a00000000002000002400800a00000a00000200002400e00e00000e00200000600400000000000200601801600000200000600800000e00400200200e01e00400200200000c00400e00000200200000203200200001a07400e01400000400400400200e01c00a00c00400000e00c00200202201601800200000200200200000000000000800600801400600600201c00000200400000c00000000000a00000800200a00201800a00001200000000000c00200c00800000404802a00c01800001600200000200000000201601200e00000800400000000602200000000401800400001400600200400201200200000200000400a00a00400000400600e00401e00400000405001400200200a00200600800001400400000c00800001400000200004800000000000200400202000401a02c00200200200003e00001200000400200601e00000e01000000a00200000400000e00001400e00400201800200200602e00000200601200200a00600200000001600802400400800200000403200e00001000000000000200200801c01401e00600600000000200a00001800000000600800200000000000400803e00200c00600601400000401c00200e01400c00200801600002800001200402e00000c00600002800000000000a00000a00400000000600600600800000200600002201c00200600002000000200000800001a00200800001601e00200200400a00200000a01e01200200000200c00400002a04e01400201400a00e01000800600800200000200202c01402200600000c01e00400600400a00200200600600400e00a00000000800e00200600200001a00000000000c00200400000000000600000200800200400000400e00000c00200000201c01400001c00400600600000001000000c00600400c00a00a00800a00000200400000000400000600400000200400000000001000200000800805000a00000600003200801e00200a00001400000400000400801600000400c00200000000e00000200400a00801400c00202800600000000e0
  | 9 => 0xf380b49685cc6490745a4c980000000000000006fc0000000000005e40008ddaf0001ae89100002957e57500000000000000011c96411c48c92bdaf961000000000079c001438000a594c4ea99fd52c0001756b4000949961aa800000088c0f0340000001270000000e18e940000012940010a4a9da6d9a48cc00000180dabc2610ec000000c58000ac8c2000082c000fc5b015580000012b95540000000001a97a0000da9774ee53e44f863d7793505f484930493003c02875c0000000001303e421c8d40000003e14fc0006086ed5080401059a1128000000000810000738c49490000bfc00000183900c9a00000001854b8e90000a340e8d6c364278000000019765601230000000000000e744fc9413789652c51400b06f00002e84340000007d8c400000005c55a0000000000000000000758e40000000001a902516c9164000791539ab8000c0c0000e14293704259ac00163800585c000000694000000000d7c000000000001440000000ec00001e09203c0b5c83c5d482871874596c4b58ad2253b413c125310f29510000df8cbd0688400019998e14d8749b11381afc0012e50942596f51ec0cc0006b46f400000000000000054400000129c0015a852c740e7d5fc000750c1d86c000e346d066951c350c19a0c8d11bd9c833da74da0da4a054f4a5d690330a0042d21c0000000003d11e40010f40000000000001b95e400000169819d100000001840000604e889000006000003600000000000010142c00009156940013a00004607d55a569c7bc000000000c800009718f0000001144665755aec000328001414000000000001411794000000b7407d76d588000f6533000136800000116c6848ec1e4000ce0428001a58000000a4400154c0000000000000000017d45f80000000309e0acc06c6c4e2c0018bc6b00000007a000055c0001f4001a340000006c8ef52ad0b8110b080009580003d807898150cba17013095c000000062c0000005280000000000c40007b47304e80000017cc74d451628d080001c58113f8000001ad4001814444000001b40001a04000fcc9a800194c000ae8000fc84a4580000238a4d4bc8a405c0000f89f0000000000000000879aad0a90f131877c0000000000843100015b0c902ecb296dc4196e84ec000000000000001ad000000113112c00159c000868a94830001279a14000000000000000c117acfd4c38ff40007948e43209b18e8d3ce6034d458000d81514874000000000001848f04000a48769968dc13294dc1d8fb042000102525532d8e56657f86207ec5d8ad0f2d56435cde5a682816d022c0016cc9c02bc00148800000109816c8b40d00a4001adc001aa00000000003907f564c7e40009f83254c8000001a284dd17d3c000109da2c950ba8000000d10001911818e1069945488111594
  | 10 => 0xac000cd91d53f415c000f8c000d580005380012b400182000167c0000012398848f40000b80017585540000018c9934f0c000001771430000f15479340c69208a305b086c3e83181286a400189400161800000000022047939c000f7d784000000498001248000df07200003748980008ad8b40000018350cc1c9a4408cadc00000068d7440000006bd0080001ecb617b40000000006507a80000009c40000000000000006917f55d8000b6401084c000e4543db0530000193047cc34000ff8000a90fac3fc244000cc91619d50dcdbc0957e0a50455830af00008b800000000067c8d80014d0001005a9cdcc000ddc000001890000548ea461c0002a45355e90512687280016546cc918aa51f911054d150000000be552017000138cb3c0003896f1a64000d5400088800000000115c000464f892fd53ce6c1554e133548545c0007708600015d179d658000c149940011a45ac5ed83c00101000029dae4b1cd840003c5a80001a388a87243ad6ac2f52a59f80012d03ec00000113cc28000000f799b40000000000005dc6600016151388901ad2ed6ec00160d26c000db02ccab08bc000000c00000000000681b4c349168b4173c0007c0000000d704940000000000004900012806100019186d4eec0257619e40018a00009603152f585595cf353c8001a6197400024d3a96805c903105d0bd98ce00000000a88000d91b500000019ec0007554a00015500006296f8fe46e882522c0000fd0d80002b0798814000644000488000a0818cdd5389684ea00001680017040740000011b16b920d1880000007b80000013943dd0b00000001986354c0b9ce78eb0a9800071400147c12c0000000000015284c9a7d824000d040000000000013649e400000000000048cb8c3a8b540017bc82000157c00127c0013dc0000001d00013440018c457d74971cc54150cb4000b98cf838400000071cbd800000000000000107c40c000001971858efd4f948cbf822853cd004cc2240019395f4001a480c0570000000aac00065caa8064d38d68f114d40000000000012f00013fc8707d120189857800017c0015257680011cd5f80000000000000013bc0010540005c00000000004f0de10d091c7f1b315ec000001320000ead9e97d0ba4000000069634345498e4cb44e490fc1798687e87f949cd0c9fc0004691544804b00bc7c458577d424121a1c25d1a90e13383680018a8000e0c500001ac4000001064cc400172020400000097800130c9380004f42f80000003a1ac97fcd480008e00000000913eda3d58d8b956988cbc4a6800085d35cfb42ac6a9a887b00009b8c784840acc607dc864c051b9a09740000000504000e8c02d0b5078d3540cef8de8d747fc148414bc8a2d7b96d98c06ace24670c71519b08049b299dcfe94f11182653d021498cca963c
  | 11 => 0xd391420000000edc000000000f9c001984000001609980000000bec0000000000006781a5a713613540000000000000005580013d8000e50d5cfa0000c2dac00004e0780851540a14000bac774240f51474dc8f74000afc000000db40005145fc0000012d90000005b4ab508ca7c000ec46c19e0200b840e58d8f1d829631ad86a1274dd80a937c0dc000614d1823534daf40019bc00175cb24cd41801356443947843c887d4ec3b4a3c4ac3cca645e915823ce80370001a514a596438058ca6d375958014ae0bb4e680004d0284c955b9470788000f593b91dc9d956cd2590d901648000000b0000096c001a943a4000000a18000000e202b904ce5d2e09f400125000043d55ce395f0088000595570a75448c64fe1418000000000000e65504d40000000000decaf824846d93cf98001235b144d54600013140019c578ced5204b481dc00d3f13e96248fd560bdd3595dd1a02c8ff06d800000064d2b0cc09259d9924001404000640000dfcf69889468f484a0f4d2450c8955a118cc0000000012dc97c0000000001b5049080000000000000000000818458000000e70630000000001ae13a4000000000000268000dd12191089e973800029128432c000c8d5c501d9c04b89d49a561c7094e8358000ac57f119c8858700000011d0000000ccc9ed038d94000000000054f84000f5536c0017a80598fd2a8fa80012f8001979590000b1133cbd180592c530ee0ca517526465836d4b4fbd4018795791f57c90357ddacca716e4e98f5c4bd735040b94c5000118c9ad10d78010d9f154400192040800124037cd8cbd4cfc000ae514d5349913e00012ccc31709a41928000000aa00017ec779120000108000000b04001574574db91949bd0c56fc7a42dc8043bc0000003f82b4f081880980017240014640000015d4000f456a8ab80000f40000006191344040352d40000000000019f494c008138000858a8c00085400149566800045172cb4d6c1214000000001800bf50907c98dce08378000000d64288000fb8b80ad99b80002c4001385260000000001580710000f18000000000cf00014a800000000199400000000182c000000000001480fd05bcf800001d55980000a0b8814041004511c5687e17c4000d15a78001875ab11e00013b0000c6d03d8b0298000000000894000cf4000800d60ed8001864bf1298354df4000c240d40005e09299893c48342a8dadb34a280002080006550d41f16d456d905aa565d06c0000015e15ac0000000000016bd1917905b8d20bb0000000d9c60c4d8b389841a01bd8d09dca1d0ac09cd1c000000ee845cbe0431084000b1400189c0002d82d4a55940000b511c0a24000d500005914342d19cd0586e16786dc81ccb0b18e14a8484489ce285f0b6d99da5404c000ed0638001728000001b385a8be91fd1
  | 12 => 0x40000162c000000eb4c5c000af4565954f6031c14c000000e1c000001a9870c561b2400187c33514800190944c4a8934000974000e05044ad4e3d124ebc000001a849cda318d531c0003000000000010880d890cbb8c4cb312e93480009b4f3c00000000080c73571438c000000000fdc0000394e55cc00142db0da00d28c3d198b58cb8021a1872c20cfed019a4d8801f80617a4f6cc459502f13245196c47cd7d91d82108b168844c76c304dc48e80005980001580000016e00003f00000000000000000000009c9a200005418452c94cd1701180000000001e81146250217897308c568d5c9675670e9cfa49d03997e8270b20944f91ab4b698ec51d104bc0e312a1620a604703f4d98f300019b0fd80004e48f8d3191ca20000cd01b00000000000010c15004482a049d1780000000000000000000000005a159523c838000c09a8cac0145a5c00055000000092d3d473d5855b4cecd782e4b90000001b1d530051b20eb966041c00047478c0018f80000012100000000019140000000005d0bbc00028c99981d25843970c00154800099cef010090890594801c3b95bcd2d7c000066d0a1a243d40017b0688000001b3d29093d28cc840001914b0000000000001604764a810e8b700ec00008059c4400008c0f2400125c2fc510a10b34cdd66
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7690810004fd7690810024fc76908101a67e65908100067d6590810016be6490810006bd649081019ede6390810006dd6390810006ee6290810006ed6290810004ff7650810024fe7650810004fd7650810024fc76508100057f755081003d7c75508101967e65508100067d6550810016be6450810006bd6450810005df735081002ddc735081018ede6350810006dd6350810006ee6250810006ed6250810005f77150810025f47150810005fb7050810005f87050810025f576c8410006f576c84100277665c84100277565c8410027b664c8410027b564c8410027d663c8410027d563c84101ff7753c84101ff7553c8410025f672c8410027e672c8410026f762c8410027e662c8410006f562c8410027e562c8410006e562c84100077652c84101f77452c8410005f570c84101eef660c8410027f260c8410064ff7690010024fe7690010014fd7690010024fc769001003d7e75900100057d75900101067e65900100067d6590010016be6490010006bd64900100fede6390010006dd6390010006ee6290010006ed6290010025f67190010005f57190010064ff76500100f67e65500100067d6550010016be6450010006bd64500100eede6350010006dd6350010006ee6250010006ed6250010004fd76c80100e67e65c80100067d65c80100debe64c8010006bd64c80100aede63c8010006dd63c8010006ee62c8010006ed62c8010025f471c8010007e721c8010004ff7688010004fd768801003d7e75880100057d75880100d67e65880100067d65880100cebe6488010006bd64880100a6de6388010006dd6388010006ee6288010006ed6288010025f67188010005f571880101e7e42188010004ff76480100057f754801003d7c75480100c67e65480100067d6548010005bf7448010035bc74480100bebe6448010006bd6448010005df734801002ddc73480100b6de6348010006dd6348010006ee6248010006ed6248010005f77148010025f47148010007e72148010004ff7608010024fe7608010004fd7608010024fc760801009e7e65080100067d6508010096be6408010006bd640801008ede6308010006dd6308010006ee6208010006ed6208010025f67108010005f571080101dfe42108010025f77644010006f77644010004f776440100077775440101c7747544010027766544010027756544010007b77444010007b47444010027b66444010027b56444010007d773440101d7d47344010027d66344010027d563440101d77753440101d7755344010007e77244010005f67244010005f47244010007e47244010005e47244010027e66244010027e562440100077652440101c7745244010025f77044010027f370440101cef66044010027f260440101c7f250440101c7f150440101bff340440101bff04044010
  | 1 => 0x8810026ec5198810026ef4198810026ee4198810026ed4198810026ec4198810026ef3198810026ee3198810026ed3198810026ec3198810006ee7098810006ec7098810006ef5098810006ee5098810006ed5098810006ec5098810006ef4098810006ec4098810006ef3098810006ee3098810006ed3098810006ec3098810026ef1098810026ee1098810026ed1098810026ec1098810004ff75588100067f75588100047f755881001cfe7558810004fd755881001cfc75588100067c755881001c7c7558810004ff7458810014fe7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d5358810026ef7258810006ef5258810006ee5258810006ed52588100067c5258810006ec52588100066c5258810006ef4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026f47158810024f47158810026ee2158810026ec2158810026f421588100acff70588100b4fd7058810006ef75588100066f7558810006ee7558810006ed7558810006ec75588100066c7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026e47158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec3158810006ee7058810006ec7058810006ef5058810006ee5058810006ed5058810006ec5058810006ef4058810006ec4058810006ef3058810006ee3058810006ed3058810006ec3058810026ef1058810026ee1058810026ed1058810026ec10588102057f76948100067f76948100047f76948102067e76948102057d76948100067d76948100047d76948102067c76948102067f64948101b67e64948102073e64948101b63e64948100067d64948102073d64948100063d64948102067c649481021d7f739481021d7d73948102067f63948101ae7e63948102075e63948101ae5e63948102167d63948102075d63948100065d63948102067c639481020d7e729481003f6e72948102067f62948100067e62948102076e62948100066e62948100067d62948102076d62948100066d62948102067c62948102067e619481020774219481006e7e60948102077710948102077a1094810207791094810004ff7690810024f
  | 2 => 0x6be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc52590100063c5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc2159010036bf7059010006be7059010006bc7059010006bf5059010006be5059010006bd5059010006bc5059010006bf3059010006be3059010006bd3059010006bc3059010026bf1059010026be1059010026bd1059010026bc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c100065c5258c10006df4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1002edf7058c10006de7058c1002edd7058c1002edc7058c10006df5058c10006de5058c10006dd5058c10006dc5058c10006df4058c10006dc4058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff75988100067f759881001cfe7598810004fd759881001cfc75988100067c759881001c7c7598810014fe7498810004fd7498810014fc7498810004ff739881000cfe7398810004fd739881000cfc73988100067f53988100067d5398810026ee7298810006ef5298810006ee5298810006ed52988100067c5298810006ec52988100066c5298810006ef4298810006ec4298810006ef3298810006ee3298810006ed3298810006ec3298810024fe7198810024fc7198810026ee2198810026ec2198810006ef75988100066f7598810006ee7598810006ed7598810006ec75988100066c7598810006ef7498810006ee7498810006ed7498810006ec7498810006ef5498810006ee5498810006ed5498810006ec5498810006ef7398810006ee7398810006ed7398810006ec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810026ef7198810026ee7198810026ed7198810026ec7198810026ef5198810026ee5198810026ed519
  | 3 => 0x671c8110005f571c8110004fe768811005d7e75881100057d75881100067f65881100d67c6588110006bf64881100cebc6488110006df63881100a6dc6388110006ef6288110006ec6288110004ff7648110004fd7648110024fc76481100057f754811005d7c75481100067f65481100c67c6548110005bf7448110055bc7448110006bf64481100bebc6448110005df734811004ddc7348110006df63481100b6dc6348110006ef6248110006ec6248110005f77148110025f47148110004fe76081100067f650811009e7c6508110006bf6408110096bc6408110006df630811008edc6308110006ef6208110006ec62081100067f658411006e7c6584110006bf6484110066bc6484110006df6384110046dc6384110006ef6284110006ec6284110025fa7084110026fb6084110025f67684110026f67684110024f67684110007776584110227746584110007b76484110007b46484110007d7638411022fd4638411022f77538411022f755384110007e76284110006f66284110006f46284110007e46284110006e46284110007765284110227745284110025f67084110026f76084110027f360841100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100047c72594100067f42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941003e7f70594100067e705941003e7d705941003e7c70594100067f40594100067c40594100067f30594100067e30594100067d30594100067c30594100267f10594100267e10594100267d10594100267c1059410004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010006bf5459010036be5459010006bd5459010036bc5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d5359010036bf4359010006be4359010006bd4359010036bc4359010004ff7259010004fc72590100067c5259010036bf4259010036bc4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc4159010014ff7059010014fd7059010034fc7059010036bc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010
  | 4 => 0x8910006ec5318910006ef4318910006ee4318910006ed4318910006ec4318910006ef71189101deee7118910006ed71189101deec7118910006ef51189101deee5118910006ed51189101deec5118910006ef41189101deee41189101deec4118910006ef31189101deee3118910006ed31189101deec31189101deef7018910006ed7018910006ef5018910006ee5018910006ed5018910006ec5018910006ef4018910006ec4018910006ef3018910006ee3018910006ed3018910006ec30189101deef1018910006ed10189101deec10189100067f76949100057e76949100067e76949100047e76949100067d76949100057c76949100067c76949100047c76949100067f64949100073f64949100063f64949101b67e64949100067d64949101b67c64949100073c64949101b63c649491023d7f739491023d7d73949102367f63949100075f63949100065f63949101ae7e63949102367d63949101ae7c63949102375c63949101ae5c639491005d7e729491005f6e72949100067f62949100076f62949100066f62949100067e62949100067d62949100067c62949100076c62949100066c62949102077b1094910004ff7690910004fe7690910004fd7690910004fc76909100067f65909101a67c6590910006bf6490910016bc6490910006df639091019edc6390910006ef6290910006ec6290910004ff7650910004fe7650910004fd7650910004fc76509100057f755091005d7c75509100067f65509101967c6550910006bf6450910016bc6450910005df735091004ddc7350910006df635091018edc6350910006ef6250910006ec6250910014fc76505100057f755051005d7c75505100067f65505101767c6550510006bf6450510016bc6450510006df635051016edc6350510006ef6250510006ec6250510005fb7050510005f87050510004fe76c85100067f65c85101667c65c8510006bf64c851015ebc64c8510006df63c8510126dc63c8510006ef62c8510006ec62c8510005fa70c8510005f970c8510004fc76485100057f754851005d7c75485100067f654851013e7c6548510006bf6448510136bc6448510006df634851012edc6348510006ef6248510006ec6248510005fb7048510005f8704851007cfe769011005d7e75901100057d75901100067f65901101067c6590110006bf6490110016bc6490110006df63901100fedc6390110006ef6290110006ec6290110014ff7650110054fd7650110024fc76501100067f65501100f67c6550110006bf6450110016bc6450110006df63501100eedc6350110006ef6250110006ec6250110005f77150110025f47150110024fe76c81100067f65c81100e67c65c8110006bf64c81100debc64c8110006df63c81100aedc63c8110006ef62c8110006ec62c8110025f
  | 5 => 0x4fd75989100067d75989100047d759891001cfc7598910014fe7498910006be7498910014be7498910004fd7498910006bd7498910004bd7498910014fc7498910004ff739891000cfe7398910006de739891000cde7398910004fd7398910006dd7398910004dd739891000cfc73989100067f53989100067d5398910004fe7298910004ee72989100067c5298910004fd7198910006f57198910004fd7098910006f970989100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df735891004ddc7358910006df6358910006dc6358910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef72589100067c5258910004ff7158910006f77158910004f77158910004ff7058910006fb7058910004fe761891005d7c75189100067f65189100067c6518910006bf6418910006bc6418910006df6318910006dc6318910006ed62189100076c5218910004ff75189100067f751891001cfe7518910004fd751891001cfc75189100067c751891001c7c7518910014fe7418910004fd7418910014fc7418910004ff731891000cfe7318910004fd731891000cfc73189100067f53189100067d5318910006ee7218910006ef5218910006ee5218910006ed52189100067c5218910006ec52189100066c5218910006ef4218910006ec4218910006ef3218910006ee3218910006ed3218910006ec3218910024fe7118910024fc71189100a4fe701891008cfc7018910005ee7618910006ee7618910004ee76189100076f75189100076c7518910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d53189101dfeb10189101dfe81018910006ef75189100066f7518910006ee7518910006ed7518910006ec75189100066c7518910006ef7418910006ee7418910006ed7418910006ec7418910006ef5418910006ee5418910006ed5418910006ec5418910006ef7318910006ee7318910006ed7318910006ec7318910006ef53189100066f5318910006ee5318910006ed53189100066d531
  | 6 => 0xc52d8d10006df42d8d10006dc42d8d10006df71d8d10246de71d8d1004edd71d8d10246dc71d8d10006df51d8d10246de51d8d10006dd51d8d10246dc51d8d10006df41d8d10246de41d8d10246dc41d8d10246de21d8d10246dc21d8d10246df70d8d1004ede70d8d1004edd70d8d1004edc70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006dc40d8d10246df10d8d1004edd10d8d10246dc10d8d1005d7e75d89100057d75d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d89100076c52d8910004ff75d891001cfe75d89100067e75d891001c7e75d8910004fd75d89100067d75d89100047d75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef52d8910006ee52d8910006ed52d89100067c52d8910006ec52d89100066c52d8910006ef42d8910006ec42d8910006ef32d8910006ee32d8910006ed32d8910006ec32d89100076e75d89100076d75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d89101e7eb10d89101e7e810d8910006ef75d8910006ee75d89100066e75d8910006ed75d89100066d75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101e6ee71d8910006ed71d89101e6ec71d8910006ef51d89101e6ee51d8910006ed51d89101e6ec51d8910006ef41d89101e6ee41d89101e6ec41d8910006ef31d89101e6ee31d8910006ed31d89101e6ec31d89101e6ef70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ec40d8910006ef30d8910006ee30d8910006ed30d8910006ec30d89101e6ef10d89101e6ec10d891005d7e75989100057d75989100067f65989100067c6598910055be7498910005bd7498910006bf6498910006bc649891004dde7398910005dd7398910006df6398910006dc6398910006ef6298910004ff759891001cfe75989100067e759891001c7e7598910
  | 7 => 0x91100069c63d91100073f53d91100073d53d91100073c52d9110257bb10d9110257b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d91100063c52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110256be71d9110006bd71d9110256bc71d9110006bf51d9110256be51d9110006bd51d9110256bc51d9110006bf31d9110256be31d9110006bd31d9110256bc31d9110256be21d9110256bc21d9110256bf70d9110056be70d9110006bd70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110256bf10d9110256bc10d91100057f755911005d7c75591100067f65591100067c6559110056bc6459110005df735911004ddc7359110006dc6359110005ef7259110005ec7259110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110054ff7459110006bf7459110004ff7359110006df7359110004df735911000cfe7359110004fd735911000cfc7359110006dc735911000cdc73591100067f53591100067d5359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec72591100067c5259110064ff7159110006f7715911007cff7059110006fb7059110005be7619110056be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d53191100073c521911024ebf601911024fbb101911024fb8101911004dde76d8d1004ede76d8d1000cde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075c52d8d10247db10d8d10247d810d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d100065
  | 8 => 0x7e46208610007765208610277745208610005f57008610027f26008610014fe7690210024fd769021006d7e75902100057d7590210016be6490210006bd6490210025f67190210005f57190210034ff7650210006bf6450210016bc6450210006ef62c8210006ec62c8210007e721c8210024fd768821006d7e75882100057d7588210006ee6288210006ed6288210025f67188210005f57188210007e421882100057f754821006d7c7548210005bf7448210065bc7448210005df7348210045dc7348210006ef6248210006ec6248210005f77148210025f47148210007e72148210024fd7608210006ee6208210006ed6208210025f67108210005f57108210007e42108210005f576c4210026f576c421026f7753c421026f7553c4210005f672c4210025f472c42100077652c42102677452c4210027f260c421005d7e76d951005e7e76d951001c7e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100057e72d951025f7b10d951025f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100047e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951025e7e71d951005e7d71d951025e7c71d95100067f41d951025e7e41d951025e7c41d95100067f31d951025e7e31d95100067d31d951025e7c31d951025e7e21d951025e7c21d951025e7f70d951005e7e70d951005e7d70d951005e7c70d95100067f40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d951025e7f10d951005e7d10d951025e7c10d9510014fe76d91100067f65d91100067c65d9110056be64d9110006dc63d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110056be54d9110006bd54d9110056bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110056bf43d9110006be43d9110006bd43d9110056bc43d9110004fe72d9110004fd72d91100067c52d9110056bf42d9110056bc42d9110024fe71d9110054fd71d9110024fc71d9110056bf41d9110014fe70d9110024fd70d9110014fc70d9110056bf40d9110055be76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d
  | 9 => 0xe75d8a100067e75d8a1001c7e75d8a10004fd75d8a100067d75d8a100047d75d8a1001cfc75d8a10014fe74d8a10004fd74d8a10014fc74d8a10004ff73d8a1000cfe73d8a10004fd73d8a1000cfc73d8a100067f53d8a100067d53d8a100067c52d8a10006f571d8a101e6ee21d8a101e6ec21d8a10006fa70d8a10004fd7698a10006ef6298a10004ff7598a1001cfe7598a10004fd7598a1001cfc7598a10014fe7498a10004fd7498a10014fc7498a10004ff7398a1000cfe7398a10004fd7398a1000cfc7398a100067f5398a100067d5398a100067c5298a100057f7558a1006d7c7558a10005bf7458a10065bc7458a10005df7358a10045dc7358a10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a10004fd7358a1000cfc7358a10006dc7358a1000cdc7358a100067f5358a100067d5358a10006ef7258a100067c5258a10006f77158a10006ed6218a10004ff7518a1001cfe7518a10004fd7518a1001cfc7518a10014fe7418a10004fd7418a10014fc7418a10004ff7318a1000cfe7318a10004fd7318a1000cfc7318a100067f5318a100067d5318a10004fe7218a10006ee7218a100067c5218a10006f57118a101deee2118a101deec2118a10006fa7018a100067f7694a100067e7694a100067d7694a100067c7694a100067f6494a101b67e6494a100067d6494a101b67c6494a102957f7394a102957d7394a1028e7f6394a101ae7e6394a1028e7d6394a101ae7c6394a1006d7e7294a1006f6e7294a100067f6294a100067e6294a100067d6294a100067c6294a1005e7d6194a102067e6094a102077b1094a10004ff7690a10004fe7690a10004fd7690a10004fc7690a10006bf6490a10016bc6490a10004ff7650a10004fe7650a10004fd7650a10004fc7650a100057f7550a1006d7c7550a10005df7350a10045dc7350a10005f77150a10025f47150a10014ff76506100057f755061006d7c7550610016be6450610006bd6450610005fb7050610005f87050610006ee62c8610006ed62c8610005fa70c8610005f970c8610006f576c86101ef7753c86101ef7553c8610025f672c8610006f762c8610007e662c8610006f562c8610007e562c86100077652c86102877452c8610007f270c8610005f570c8610007f170c8610026f660c86100057f754861006d7c7548610006ee6248610006ed6248610027e42148610005fb7048610005f87048610005f57608610026f5760861027f77530861027f755308610027e67208610006f76208610007e76208610006f56208610
  | 10 => 0x9310006bd4359310004ff7259310004fc72593100067c525931007ebc4259310024fc7159310026be4159310026bc415931007ebf4059310004ff7598b1001cfe7598b10004fd7598b1001cfc7598b10014fe7498b10004fd7498b10014fc7498b10004ff7398b1000cfe7398b10004fd7398b1000cfc7398b100067f5398b100067d5398b10026ee7298b100067c5298b10024fe7198b10026ee2198b10026ec2198b10026f41098b10004ff7558b100067f7558b100047f7558b1001cfe7558b10004fd7558b1001cfc7558b100067c7558b1001c7c7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10026ef7258b100067c5258b10024fc7158b10026ee2158b10026ec2158b100067f7694b102067e7694b100067d7694b102067c7694b102067f6494b101b67e6494b100067d6494b102067c6494b102a57f7394b102a57d7394b102067f6394b101ae7e6394b1029e7d6394b102067c6394b1020d7e7294b100876e7294b102067f6294b100067e6294b100067d6294b102067c6294b10004ff7690b10024fe7690b10004fd7690b10024fc7690b10016be6490b10006bd6490b10004ff7650b10024fe7650b10004fd7650b10024fc7650b100057f7550b100857c7550b10005df7350b10075dc7350b10005fb7050b10005f87050b10054fd76903100857e75903100057d7590310256bf6490310016bc6490310014ff7650310024fc7650310016be6450310006bd6450310005f77150310025f47150310006ee62c8310006ed62c8310025f671c8310005f571c83100857e75883100057d75883101e6ef62883101e6ec62883100057f75483100857c7548310005bf744831007dbc7448310005df7348310075dc7348310006ee6248310006ed6248310005f77148310025f471483101deef62083101deec620831006d7e75d92100057d75d9210066be64d9210004ff75d921001cfe75d92100067e75d921001c7e75d9210004fd75d92100067d75d92100047d75d921001cfc75d9210064fd74d9210066be54d9210006bd54d9210004ff73d921000cfe73d9210004fd73d921000cfc73d92100067f53d92100067d53d9210066bf43d9210006bd43d9210004fe72d9210004fd72d92100067c52d9210066bc42d9210006f571d9210256be41d9210256bc41d9210006fa70d9210066bf40d9210014ff7659210066bc6459210004ff755921001cfe7559210004fd755921001cfc7559210006bf7459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210004ff7259210004fc72592100067c5259210066bf4159210024fc7059210066bc405921006d7e75d8a100057d75d8a10004ff75d8a1001cf
  | 11 => 0x26f66118420006f56118420024ff7690420004fe7690420004fd7690420004ff7650420004fd7650420004fc76504200057f755042009d7c7550420016be6450420006bd6450420005ef7250420005ec7250420005fb7050420005f87050420024fd76c8420336ee62c8420026f661c8420006f561c8420005fa70c8420005f970c8420004fd768842009d7e75884200057d7588420095be7488420005bd748842008dde7388420005dd73884200076e528842032f6c5288420005ed76884201deed7688420004ed76884201df6e75884201df6d75884201dfae74884201dfad74884201dfce73884201dfcd73884203276f53884203276d53884201ddee71884201deed6188420005ed70884201e6ee6088420004ff76484200057f754842009d7c754842031eee62484200076e52084203176c5208420026f66108420006f56108420007e52108420005fa7008420005f9700842030f6f530842030f6d53084201ddee71084201dfe671084201dfe661084201deed6108420007e561084201dfea7008420005ed70084201dfe970084201e6ee60084200ccff7690020014fe7690020014fd7690020094fc769002009d7e75900200057d7590020016be6490020006bd6490020005ee7290020005ed72900200ccff76500200076e52c80203076c52c80202ff6f53c80202ff6d53c80201ddee71c8020006ed61c802009d7e75880200057d75880202eded72880202e6ee62880202df7a75880200077975880202f77b53880202f77953880202edf972880202e6fa6288020007ea62880200077a52880202df785288020007ea2188020007e82188020004ff76480200057f754802009d7c7548020005bf7448020095bc7448020005df734802008ddc73480200076e52480202af6c5248020005f77148020005f47148020005ef7648020006ef7648020004ef76480200076f75480202af6c7548020007af7448020007ac7448020007cf73480202c7cc73480202c76f53480202c76d5348020007e771480201ddec7148020007e47148020005e47148020006ed61480202d5ef70480202ceee60480202afea50480202afe95048020005fb7648020006fb7648020004fb76480200077b75480202af787548020007bb7448020007b87448020007db73480202c7d873480202c77b53480202c77953480202bdfb7248020007eb72480202b6fa6248020007ea62480200077a52480202afea52480200076a52480202afe952480202af785248020007f37148020007f07148020004ff75593100067f75593100047f755931001cfe7559310004fd755931001cfc75593100067c755931001c7c7559310026bf745931007ebe5459310006bd5459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d535931007ebf435
  | 12 => 0xf63501200eedc6350120005ef7250120005ec7250120006f76150120006f461501200067f65c81200e67c65c8120006bf64c81200debc64c8120006df63c81200aedc63c8120006f761c8120006f461c81200077b65c812035f7865c8120007bb64c8120007b864c8120007db63c8120367d863c81203677b53c81203677953c81200077a52c812035f7852c8120007f361c8120007f061c8120007eb21c8120007e921c81200c57e75881200057d75881200067f65881200d67c6588120006bf64881200cebc6488120006df63881200a6dc63881200076e52881203576c5288120006f76188120006f461881203576e75881200076d75881200076f65881203576c6588120007af6488120007ac6488120007cf638812034fcc638812034f6f538812034f6d5388120005ed7188120007e761881201e6ec6188120007e46188120006e46188120007eb608812009d7e75d90200057d75d9020096be64d9020004ff75d902001cfe75d90200067e75d902001c7e75d9020004fd75d90200067d75d90200047d75d902001cfc75d9020094fd74d9020004ff73d902000cfe73d9020004fd73d902000cfc73d90200067f53d90200067d53d90200dcfe72d9020006ee72d90200067c52d9020024fe71d9020004fd71d90200ccfe70d9020006fa70d9020014ff7659020096bc6459020004ff755902001cfe7559020004fd755902001cfc7559020006bf7459020006bf5459020096bc5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d5359020096bf4359020006bd4359020014ff7259020014fd7259020094fc72590200067c5259020096bc4259020004ff7159020024fc7159020096bf4159020094fc7059020096bc40590200e67f769482001e7e769482001e7d769482009e7c76948200067f64948201b67e64948200067d64948201b67c64948203457f73948203457d739482033e7f63948201ae7e639482033e7d63948201ae7c639482009d7e729482009f6e72948200e67e62948202067e61948200077a70948200077970948200d67e60948200dcff7690820014fd7690820016be6490820006bd6490820005fa7090820005f970908200dcff76508200057f755082009d7c7550820005df735082008ddc7350820006f761984200057f755842009d7c7558420004ff75584200067f75584200047f755842001cfe7558420004fd755842001cfc75584200067c755842001c7c7558420004ff7458420014fe7458420014fc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d53584200067e52584200067c5258420006f63158420006f53158420024ff705842009d7e75184200057d7518420095be7418420005bd741842008dde7318420005dd7318420
  | 13 => 0x8520006775318520006f65318520006f55318520006755318520006f45318520006f74318520006f64318520006f54318520006f44318520026f77218520006f75218520006f65218520006765218520006f55218520006f45218520006745218520006f74218520006f64218520006f54218520006f44218520006f73218520006f63218520006f53218520006f43218520026f77018520026f57018520006f75018520006f65018520006f55018520006f45018520006f74018520006f44018520006f73018520006f63018520006f53018520006f43018520006f52018520004fe7690520004fd7690520024fc76905200067f65905201867c6590520006bf6490520016bc6490520006df639052017edc6390520005ee7290520005ed7290520006f76190520026f46190520004ff7650520004fe7650520004fc76505200057f75505200c57c75505200067f65505201767c6550520006bf6450520016bc6450520006df635052016edc6350520006f76150520026f46150520004fe76c85200067f65c85201667c65c8520006bf64c852015ebc64c8520006df63c8520126dc63c85200076e52c85203976c52c8520026f461c8520005ee76c8520006ee76c8520004ee76c85200076f65c85203976c65c8520007af64c8520007ac64c8520007cf63c852038fcc63c852038f6f53c852038f6d53c8520007e761c8520026ee61c8520026ec61c8520007e461c8520026e461c8520005ee70c85200c57e75885200057d75885200067f65885201567c65885200bdbe7488520005bd7488520006bf648852014ebc64885200b5de7388520005dd7388520006df6388520146dc6388520385ed7288520006f76188520026f46188520005fa7088520005f97088520024fc76485200057f75485200c57c75485200067f654852013e7c6548520006bf6448520136bc6448520006df634852012edc63485200076e524852037f6c5248520006f76148520026f46148520005fb7048520005f87048520024ec76485200076f754852037f6c75485200076f654852037f6c6548520007af6448520007ac6448520007cf6348520377cc63485203776f53485203776d5348520007e77148520007e76148520026ee6148520026ec6148520007e46148520026e46148520007eb7048520005ec7048520007e87048520004fe76085200067f650852011e7c6508520006bf6408520116bc6408520006df630852010edc630852036dee7208520006f76108520026f461085200dcfe76901200c57e75901200057d75901200067f65901201067c6590120006bf6490120016bc6490120006df63901200fedc6390120006f76190120006f46190120014ff76501200bcfd7650120014fc76501200067f65501200f67c6550120006bf6450120016bc6450120006d
  | 14 => 0x6f451d8520006f741d8520006f441d8520006f731d8520006f631d8520006f531d8520006f431d8520024fe70d8520006f765d85200077765d85200067765d8520006f665d8520006f565d8520006f465d85200077465d85200067465d8520006f764d8520007b764d8520006b764d8520006f664d8520006f564d8520006f464d8520007b464d8520006b464d8520006f763d8520007d763d8520006d763d8520006f663d8520006f563d8520006f463d8520007d463d8520006d463d85200077753d85200077553d8520007e772d85200077652d85200077452d8520006f775d8520006f675d8520006f575d8520006f475d8520006f774d8520006f674d8520006f574d8520006f474d8520006f754d8520006f654d8520006f554d8520006f454d8520006f773d8520006f673d8520006f573d8520006f473d8520006f753d85200067753d8520006f653d8520006f553d85200067553d8520006f453d8520006f743d8520006f643d8520006f543d8520006f443d8520006f772d8520006f752d8520006f652d85200067652d8520006f552d8520006f452d85200067452d8520006f742d8520006f642d8520006f542d8520006f442d8520006f732d8520006f632d8520006f532d8520006f432d8520006f770d8520006f570d8520006f750d8520006f650d8520006f550d8520006f450d8520006f740d8520006f440d8520006f730d8520006f630d8520006f530d8520006f430d85200c57e75985200057d75985200067f65985200067c65985200bdbe7498520005bd7498520006bf6498520006bc64985200b5de7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520006bf6458520006bc6458520005df73585200b5dc7358520006df6358520006dc63585200067f65185200067c6518520006bf6418520006bc6418520006df6318520006dc6318520026f66118520006f56118520005f67618520006f67618520006f76518520007776518520006776518520006f66518520006f56518520006f46518520007746518520006746518520006f76418520007b76418520006b76418520006f66418520006f56418520006f46418520007b46418520006b46418520006f76318520007d76318520006d76318520006f66318520006f56318520006f46318520007d46318520006d46318520007775318520007755318520007e57218520007765218520007745218520026f77518520026f67518520026f57518520026f47518520026f77418520026f67418520026f57418520026f47418520006f75418520006f65418520006f55418520006f45418520026f77318520026f67318520026f57318520026f47318520006f7531
  | 15 => 0xd53591200ccff7259120006ef72591200067c5259120004ff7159120006f77159120004f77159120024fc7159120006f47159120024f471591200dcff7059120006fb7059120005be76191200bebe7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120006bf6319120006be6319120006bd6319120006bc63191200079c63191200069c63191200073f53191200073d53191200073c52191200b5de76d8d200b6de76d8d2000cde76d8d200075f75d8d200075c75d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d200079f64d8d200069f64d8d20006de64d8d20006dd64d8d20006dc64d8d200079c64d8d200069c64d8d200075c52d8d20006df75d8d200065f75d8d20006de75d8d20006dd75d8d20006dc75d8d200065c75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d200b6de72d8d200b6dd72d8d200b6dc72d8d20006df52d8d20006de52d8d20006dd52d8d20006dc52d8d200065c52d8d20006df42d8d20006dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006de51d8d20006dd51d8d20006dc51d8d20006df41d8d20006dc41d8d20006df70d8d200b6de70d8d200b6dd70d8d200b6dc70d8d20006df50d8d20006de50d8d20006dd50d8d20006dc50d8d20006df40d8d20006dc40d8d200b6dd20d8d200057e76949200d67e76949200d47e76949200067f64949200073f64949200063f64949201b67e64949200067d64949201b67c64949200073c64949201b63c64949203b57f73949203b57d73949203ae7f63949200075f63949200065f63949201ae7e63949203ae7d63949201ae7c63949203af5c63949201ae5c63949200c57e72949200c76e72949202067c61949200ccfe76909200067f65909201a67c6590920006bf6490920016bc6490920006df639092019edc63909203a76c5290920014fc76509200057f75509200c57c75509200067f65509201967c6550920006bf6450920016bc6450920005df73509200b5dc7350920006df635092018edc635092039f6c52509200bfac4250920005fb7050920005f870509200067f65d85200067c65d8520006bf64d8520006bc64d8520006df63d8520006dc63d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d85200067e52d85200067c52d8520006f751d8520006f651d8520006f551d8520
  | 16 => 0x95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95200c67e72d952001c7e72d95200c67d72d95200c67c72d952001c7c72d95200067f42d95200067c42d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95200067f70d95200c67e70d95200c67d70d95200c67c70d95200067f40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d95200c67d20d9520014fe76d91200067f65d91200067c65d91200bebe64d9120006dc63d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d91200bebe54d9120006bd54d91200bebc54d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d91200bebf43d9120006be43d9120006bd43d91200bebc43d9120014fe72d91200bcfd72d9120014fc72d91200067c52d91200bebf42d9120024fe71d9120004fd71d91200bebf41d91200bebc41d91200bcfd70d91200bebf40d91200bdbe76d9120014be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006bf63d9120006be63d9120006bd63d9120006bc63d91200079c63d91200069c63d91200073f53d91200073d53d91200073c52d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d91200063f53d9120006be53d9120006bd53d91200063d53d9120006bc53d9120006bf72d91200bebe72d9120006bd72d9120006bf52d9120006be52d9120006bd52d9120006bc52d91200063c52d9120006bf32d9120006be32d9120006bd32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d9120006bf70d91200bebe70d9120006bd70d9120006bf50d9120006be50d9120006bd50d9120006bc50d9120006bf30d9120006be30d9120006bd30d9120006bc30d91200057f75591200c57c75591200067f65591200067c65591200bebc6459120005df73591200b5dc7359120006dc6359120005f77159120005f47159120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c75591200bcff7459120006bf7459120004ff7359120006df7359120004df735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc73591200067f53591200067
  | 17 => 0xa5dc7350a20005fb7050a20005f87050a200d57e75d86200057d75d86200067e65d86200067d65d86200067e65986200067d6598620006f761986200067e65586200067d6558620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620014fc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d53586200067e52586200067c52586200d57e75186200057d75186200067e65186200067d65186200cdbe7418620005bd74186200a5de7318620005dd7318620026f66118620006f56118620024ff7690620004fe7690620004fd76906201867e65906200067d6590620004ff7650620004fd7650620004fc76506200057f75506200d57c75506201767e65506200067d6550620016be6450620006bd6450620005ef7250620005ec72506201667e65c86200067d65c86200d57e75886200057d75886201567e65886200067d65886200cdbe7488620005bd74886200a5de7388620005dd73886200076e52886203e76c5288620026f66188620006f56188620005fa7088620005f970886201e76e75886201e76d75886203e76e65886200076d65886201e7ae74886201e7ad74886201e7ce73886201e7cd73886203df6f53886203df6d53886201e7e661886201e6ed6188620007e561886201e7ea7088620005ed70886201e7e97088620024ff76486200057f75486200d57c754862013e7e65486200067d6548620026f66148620006f56148620005fb7048620005f8704862011e7e65086200067d65086200076e52086203d76c5208620026f46108620007e52108620005ed76086201e6ed76086203d76e65086200076d65086203cf6f53086203cf6d53086201e7e67108620007e761086201e6ed61086201e7e46108620005ed7008620014fe7690220014fd76902200d57e75902200057d75902201067e65902200067d6590220016be6490220006bd6490220005ee7290220005ed7290220094ff76502200f67e65502200067d65502200e67e65c82200067d65c82200076e52c82203bf6c52c8220005ed76c8220006ed76c82203bf6e65c82200076d65c82203c76f53c82203c76d53c82201e5ee71c8220006ed61c82203bfea50c82203bfe950c8220005f976c8220006f976c82203bf7a65c82200077965c82203c77b53c82203c77953c82200077a52c82203bfea52c82200076a52c82203bfe952c82203bf7852c82200c57e76d95200c67e76d952001c7e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200c57c72d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d
  | 18 => 0xc75487200076e52487203ff6c5248720005ef7648720006ef76487200076f75487203ff6c754872031f6f534872031f6d5348720007e77148720026ee6148720026ec6148720005ec7048720026f66108720006f56108720005fa7008720005f970087200bcfd76903200e57e75903200057d7590320006bf6490320016bc6490320014ff7650320014fc7650320016be6450320006bd6450320005ef7250320005ec72503200d57f76596200d67f765962001c7f76596200067e64596200067c64596200057f73596200057d73596200067f63596200067e63596200067d63596200067c63596200067f74596200067e74596200067d74596200067c74596200067f73596200047f73596200067e73596200067d73596200047d73596200067c73596200067f43596200067e43596200067d43596200067c43596200d67f72596200d67e72596200067d72596200d67c72596200067f42596200067c42596200067f32596200067e32596200067d32596200067c32596200067f71596200067e71596200067d71596200067c71596200067f41596200067c41596200067f31596200067e31596200067d31596200067c31596200d67f70596200067e70596200d67d70596200d67c70596200067f40596200067c40596200067f30596200067e30596200067d30596200067c30596200d67e20596200d57e75d92200057d75d92200067e65d92200067d65d92200cebe64d92200a5de73d9220005dd73d9220004ff75d922001cfe75d92200067e75d922001c7e75d9220004fd75d92200067d75d92200047d75d922001cfc75d92200ccfd74d9220004ff73d922000cfe73d9220006de73d922000cde73d9220004fd73d9220006dd73d9220004dd73d922000cfc73d92200067f53d92200067d53d92200cebf43d9220006bd43d9220006ed72d92200067c52d92200cebc42d9220024fe71d9220004fd71d9220006fa70d9220014ff76592200067e65592200067d65592200cebc6459220004ff755922001cfe7559220004fd755922001cfc7559220006bf7459220004ff735922000cfe7359220004fd735922000cfc73592200067f53592200067d5359220006be43592200cebc43592200067c52592200cebf4259220004ff7159220024fc71592200cebf41592200cebc40592200057d7694a200c67d7694a200c47d7694a200067f6494a201b67e6494a200067d6494a201b67c6494a203f57f7394a203f57d7394a203ee7f6394a201ae7e6394a203ee7d6394a201ae7c6394a200d57e7294a200d76e7294a202067e6194a2009e7e6094a200bcfd7690a201a67e6590a200067d6590a20006bf6490a20016bc6490a20014ff7650a200057f7550a200d57c7550a201967e6550a200067d6550a20016be6450a20006bd6450a20005df7350a20
  | 19 => 0x8540006ec6208540006f76108540026f46108540005fa7008540005f9700854042f3e75901400073d759014042ebf659014042ebd6590140436bf6390140436bd63901404373f53901404373d5390140006bc62901400073e529014042f3c5290140005bd7190140256bc6190140015be7090140017ba7090140016bf6090140017bb60901400debe64d9320004ff75d932001cfe75d9320004fd75d932001cfc75d93200dcfd74d9320004ff73d932000cfe73d9320004fd73d932000cfc73d93200067f53d93200067d53d9320006ee72d93200067c52d9320024fe71d9320004fd71d93200debf41d9320006f970d93200debc40d9320014ff76593200057f75593200e57c75593200debc6459320004ff75593200067f75593200047f755932001cfe7559320004fd755932001cfc75593200067c755932001c7c7559320006bf74593200debe5459320006bd5459320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d53593200debf4359320006bd43593200067c52593200debc4259320004ff7159320024fc71593200debc41593200debf405932001e7e7694b2001e7d7694b200067f6494b201b67e6494b200067d6494b201b67c6494b204257f7394b204257d7394b2041e7f6394b201ae7e6394b2041e7d6394b201ae7c6394b200e57e7294b200e76e7294b202067e6194b200077a7094b20007797094b20014fd7690b20016be6490b20006bd6490b204176c5290b20005fa7090b20005f97090b20094ff7650b200057f7550b200e57c7550b20005df7350b200addc7350b2040f6c5250b200dfac4250b200e57e75d87200057d75d87200ddbe74d8720005bd74d87200adde73d8720005dd73d87200e57e75987200057d75987200ddbe7498720005bd74987200adde7398720005dd7398720006f76198720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d53587200067e52587200067c5258720026f66118720006f56118720024ff7690720004fe7690720004fd7690720016be6490720006bd6490720005ee7290720005ed7290720004ff7650720004fd7650720004fc76507200057f75507200e57c7550720006bf6450720016bc6450720005fb7050720005f87050720024fd76c87200076e52c87204076c52c8720026f661c8720006f561c8720005fa70c8720005f970c8720024ed76c87203376f53c87203376d53c8720026ee61c8720007e661c8720007e561c8720026ec61c8720005ee70c8720007ea70c8720007e970c87200e57e75887200057d75887200ddbe7488720005bd74887200adde7388720005dd73887200057f75487200e57
  | 20 => 0x4fd7648640004fc76486400057f75486401057c754864013e7e65486400067d6548640005bf7448640015bc7448640006ee6248640006ed6248640024ff7608640004fe7608640004fd760864011e7e65086400067d6508640255bf7408640015bc7408640005fa7008640005f970086400f57e75d89400057d75d8940004ff75d894001cfe75d89400067e75d894001c7e75d8940004fd75d89400067d75d89400047d75d894001cfc75d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d89400067c52d89400ceee42d89400ceed42d8940024fe71d8940004fd71d8940006ef62989400bdf970989400057f75589400f57c7558940005df73589400eddc7358940005f77158940005f471589400ddfb7058940006ed6218940004ff751894001cfe7518940004fd751894001cfc7518940004ff731894000cfe7318940004fd731894000cfc73189400067f53189400067d53189400067c5218940096ee4218940096ed4218940024fe7118940004fd7118940096bf4118940096bc40189400067f76949400067e76949400067d76949400067c76949401b73e74949400073d74949401b67f649494045d7f739494045d7d73949404567f63949401ae7e63949404567d63949401ae7c639494044d7e72949400f76e72949400067f62949400067c62949402067c61949401b73f41949401b67f60949401b77b40949401b73c40949401b7784094940004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540004fe72d8540004fd72d85400067e52d85400067c52d8540066f641d8540066f541d8540006f76198540055f970985400057f75585400f57c7558540005df73585400eddc7358540005ef7258540005ec725854007dfb70585400f57e75185400057d75185400edde7318540005dd7318540026f66118540006f56118540024bc76505400073f755054043f3c755054043ebf655054043ebd6550540446bf6350540446bd63505404473f53505404473d5350540006bc62505400073e525054043f3c5250540015bf7150540017b77150540007b76150540026be6150540026bc6150540007b46150540007bb7050540005bc7050540007b87050540016bf6050540017bb6050540004fe76c8540004fd76c8540004fc76c8540006f761c8540026f461c8540004fe7688540004fd7688540024fc76885400f57e75885400057d7588540015be7488540005bd74885400edde7388540005dd7388540006ef6288540006ec6288540004ff7648540004fe7648540004fc76485400057f75485400f57c7548540004fe7608540004fd7608540024fc7608540015be7408540005bd7408540006ef620
  | 21 => 0xd6558a40004ff7558a400067f7558a400047f7558a4001cfe7558a40004fd7558a4001cfc7558a400067c7558a4001c7c7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a400bebf4358a40006bd4358a400067c5258a400beee4258a400beed4258a400bebc4258a40006ef3258a40006ec3258a40004ff7158a40024fc7158a401057e7518a400057d7518a400067e6518a400067d6518a40006ed6218a400cdfa7018a400057f7694a400067f7694a400047f7694a400067e7694a400057d7694a400067d7694a400047d7694a400067c7694a400073f7494a401b73c7494a401b67d6494a404ad7f7394a404ad7d7394a404a67f6394a401ae7e6394a404a67d6394a401ae7c6394a401b73f4394a404a73d4394a4044d7e7294a401076e7294a400067e6294a400067d6294a401b73c4294a402067e6194a401b73c4194a401b67e6094a401b73f4094a401b77b4094a401b7784094a4049dbf7590a4049dbd7590a404873e6590a400073d6590a40495bf7390a40495bd7390a4019ebe6390a4019ebc6390a4048f3f5390a4048f3d5390a40015be7290a40017ae7290a40007ae6290a40006bd6290a40007ad6290a400073e5290a404873c5290a40255be7190a40007ba7090a40005bd7090a40007b97090a40016be6090a40017ba6090a401057e75d86400057d75d86400067e65d86400067d65d8640035fa70d86400067e65986400067d6598640006f761986400067e65586400067d6558640004ff755864001cfe7558640004fd755864001cfc7558640056be5458640006bd5458640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640056bf4358640006bd4358640004ff7258640004fc72586400067e52586400067c5258640006be4258640056bc4258640056f64158640056f54158640256bc4158640056bf40586401057e75186400057d75186400067e65186400067d65186400fdde7318640005dd7318640005ee7218640005ed7218640026f66118640006f56118640065fa7018640255bf759064047dbd75906404673e65906400073d6590640255bf7390640475bd739064046f3f539064046f3d5390640005be72906400073e52906404673c5290640015be7190640017b67190640257b66190640256bd6190640007b56190640257ba7090640005bd7090640257b97090640016be6090640017ba6090640004ff76c8640004fe76c8640004fd76c86401667e65c86400067d65c8640015be74c8640005bd74c8640006ee62c8640006ed62c8640024ff7688640004fe7688640004fd76886401057e75886400057d75886401567e65886400067d6588640015be7488640005bd74886400fdde7388640005dd7388640004ff7648640
  | 22 => 0x84214d6f66248421027e662484210077652484214cf7452484214c7e632484214c7e53248421005f47048421004ff759802101cfe7598021004fd759802101cfc7598021014fe7498021004fd7498021014fc7498021004ff739802100cfe7398021004fd739802100cfc73980210067f53980210067d53980210067e52980210067c5298021026fa7098021006fa5098021006f95098021006fa3098021006f93098021026fb1098021026f81098021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021006bf7458021004bf7458021014fe7458021014fc7458021006bc7458021014bc7458021004ff7358021006df7358021004df735802100cfe7358021004fd735802100cfc7358021006dc735802100cdc73580210067f53580210067d53580210067e52580210067c5258021026ef2158021026ed2158021026fb7058021006fa5058021006f95058021006fa3058021006f93058021026fb1058021026f41058021026f810580214bd7f76596401067f765964001c7f76596404b73e74596400073d74596400057f73596400057d73596400067f63596400067e63596400067d63596400067c63596404b73f43596400073d43596400057c72596404b73c42596404b73c41596404b73f40596404b77b40596404b77840596404b67f74596404b67e74596404b67d74596404b67c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596404b67f43596404b67e43596404b67d43596404b67c43596400067f72596400067e72596400067d72596400067c72596400047c72596404b67f42596404b67e42596404b67d42596404b67c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596404b67f41596404b67e41596404b67d41596404b67c41596400067f31596400067e31596400067d31596400067c31596401067f70596404b67e70596404b67d70596404b67c70596404b67f40596404b67e40596404b67d40596404b67c40596400067f30596400067e30596400067d30596400067c30596401057e75d8a400057d75d8a400067e65d8a400067d65d8a400fdde73d8a40005dd73d8a40095fa70d8a401057c7598a400067e6598a400067d6598a40006ef6298a40004ff7598a400067f7598a4001cfe7598a40004fd7598a4001cfc7598a400067c7598a4001c7c7598a40004ff7398a4000cfe7398a40004fd7398a4000cfc7398a400067f5398a400067d5398a400067c5298a400deee4298a400deed4298a40006ef3298a40006ec3298a40024fe7198a40004fd7198a400057f7558a401057c7558a400067e6558a400067
  | 23 => 0x24fc76509210057f755092113d7c75509210067f65509211967c6550921006bf6450921016bc6450921005df735092112ddc7350921005f77150921025f47150921014ff7650521134fd7650521014fc76505210057f755052113d7c75505210067f65505211767c6550521006bf6450521016bc6450521005ef7250521005ec72505210067f65c85211667c65c8521025ee72c8521026ef62c85210077765c85214ff7465c85215077753c85215077553c8521025f672c8521026f762c8521027e762c85210077652c85214ff7452c85210067f65d81210067c65d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d81210067e52d81210067c52d8121006fb40d8121006f840d8121006fb30d8121006f830d812113d7e75981210057d75981210067f65981210067c6598121006fb60981210057f755812113d7c75581210067f65581210067c6558121005bf7458121135bc7458121005df735812112ddc73581210067f65181210067c6518121006f96018121004ff751812101cfe7518121004fd751812101cfc7518121014fe7418121004fd7418121014fc7418121004ff731812100cfe7318121004fd731812100cfc73181210067f53181210067d53181210067e52181210067c5218121006f721181211deee21181211deec2118121006fb4018121006f84018121006fb3018121006f83018121004ff75590210067f75590210047f755902101cfe7559021004fd755902101cfc75590210067c755902101c7c7559021026bf7459021116be5459021006bd5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021116bf4359021006bd4359021114fc72590210067c5259021116bc4259021024fe7159021024fc7159021026be4159021026bc4159021004ff7059021004fc7059021116bf40590211667f769482101e7e769482101e7d76948212067c76948212067f64948211b67e64948210067d64948212067c64948214f57f73948214f57d73948212067f63948211ae7e63948214ee7d63948212067c639482120d7e729482111f6e72948211667e62948212077671948210077571948212067e61948212076f21948212077621948212076d219482115cff7690821024fe7690821014fd7690821024fc7690821016be6490821006bd64908214e76c5290821025f67190821005f5719082115cff76508210057f755082111d7c7550821005df735082110ddc73508214df6c5250821117ac4250821025f77648421006f77648421004f776484210077775484214cf7475484214c77753484214c7755348421025f77248421027e7724
  | 24 => 0xe7558221004fd755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d53582210067e52582210067c5258221026ef2158221026ed2158221026fb7058221026fb1058221026f8105822113d7e76d952113e7e76d952101c7e76d95210067e64d95210067c64d95210057f73d95210057d73d95210067f63d95210067e63d95210067d63d95210067c63d952113d7c72d95212076e21d95212076c21d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210047f73d95210067e73d95210067d73d95210047d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95212067f72d952113e7e72d952113e7d72d952113e7c72d95210067f42d95210067c42d95210067f32d95210067e32d95210067d32d95210067c32d95210067f71d95212067e71d952113e7d71d95212067c71d95210067f41d95212067e41d95212067c41d95210067f31d95212067e31d95210067d31d95212067c31d95212067e21d952113e7d21d95212067c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067c40d95210067f30d95210067e30d95210067d30d95210067c30d95212067f10d95212067c10d9521014fe76d91210067f65d91210067c65d9121136be64d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d9121006be43d9121136bc43d9121024fd72d91210067c52d9121136bf42d9121134fd71d9121136bf41d9121004fe70d9121004fd70d9121136bc40d91210057f755912113d7c75591210067f65591210067c6559121136bc6459121005df735912112ddc7359121005fb7059121005f87059121004ff75591210067f75591210047f755912101cfe7559121004fd755912101cfc75591210067c755912101c7c7559121134ff7459121006bf7459121004ff7359121006df7359121004df735912100cfe7359121004fd735912100cfc7359121006dc735912100cdc73591210067f53591210067d5359121136bf4359121006bd435912114cff7259121006ef72591210067c5259121136bc425912115cff7159121006f77159121004ff7059121006fb7059121004fb7059121004fc7059121006f87059121004f870591210057e76949211567e76949211547e76949210067f64949211b67e64949210067d64949211b67c64949215157f73949215157d739492150e7f63949211ae7e639492150e7d63949211ae7c639492113d7e729492113f6e72949212076e219492114cfe76909210067f65909211a67c6590921016be6490921006bd6490921
  | 25 => 0x9221026bc7159221026bf5159221026be5159221026bd5159221026bc5159221026bf3159221026be3159221026bd3159221026bc3159221026bf2159221026be2159221026bd2159221026bc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006be5059221006bd5059221006bc5059221006bf3059221006be3059221006bd3059221006bc3059221026bf1059221026be1059221026bd1059221026bc1059221006df7558e21006de7558e210065e7558e21006dd7558e210065d7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e21146df7258e21146de7258e21006dd7258e21146dc7258e21006df5258e21006de5258e21006dd5258e21006dc5258e210065c5258e21006df4258e21006dc4258e21026df7158e21026de7158e21026dd7158e21026dc7158e21026df5158e21026de5158e21026dd5158e21026dc5158e21026df4158e21026de4158e21026dd4158e21026dc4158e21026df2158e21026de2158e21026dd2158e21026dc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006de5058e21006dd5058e21006dc5058e21006df4058e21006dc4058e21026df1058e21026de1058e21026dd1058e21026dc1058e212057d7694a2113e7d7694a2113c7d7694a212067f6494a211b67e6494a212073e6494a211b63e6494a210067d6494a212073d6494a210063d6494a212067c6494a215457f7394a215457d7394a212067f6394a211ae7e6394a212075e6394a211ae5e6394a2153e7d6394a212075d6394a210065d6394a212067c6394a2120d7e7294a211576e7294a212067e6194a212076f2194a21134fd7690a211a67e6590a210067d6590a21016be6490a21006bd6490a2119ede6390a21006dd6390a215376c5290a21014ff7650a21024fc7650a210057f7550a211557c7550a211967e6550a210067d6550a21016be6450a21006bd6450a21005df7350a21145dc7350a2118ede6350a21006dd6350a2152f6c5250a2114fac4250a21005f77150a21025f47150a21025f576c8621006f576c86210277665c86210277565c8621027b664c8621027b564c8621027d663c8621027d563c86215277753c86215277553c8621027e672c86210077652c862151fe652c86210076652c862151fe552c862151f7452c8621004ff759822101cfe7598221004fd759822101cfc7598221014fe7498221004fd7498221014fc7498221004ff739822100cfe7398221004fd739822100cfc73982210067f53982210067d53982210067e52982210067c5298221006f72198221026f42198221026fa7098221026fb1098221026f81098221004ff755822101cf
  | 26 => 0x5f57190b21114ff7650b210057f7550b211657c7550b21005df7350b21125dc7350b21014ff7650721014fc76507210057f75507211657c7550721016be6450721006bd6450721005ef7250721005ec72507211657e75d83210057d75d832115dbe74d8321005bd74d8321125de73d8321005dd73d83211657e75983210057d7598321006fb6098321004ff759832101cfe75983210067e759832101c7e7598321004fd75983210067d75983210047d759832101cfc7598321014fe7498321004fd7498321014fc7498321004ff739832100cfe7398321004fd739832100cfc73983210067f53983210067d53983210067e52983210067c52983211e6ee21983211e6ec2198321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d53583210067e52583210067c5258321006f960183210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596211567f72596211567e72596210067d72596211567c72596210067f42596210067c42596210067f32596210067e32596210067d32596210067c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e41596210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067e30596210067d30596210067c30596210267f10596210267e10596210267d10596210267c1059621004ff755922101cfe7559221004fd755922101cfc7559221026bf7459221006bf545922114ebe5459221006bd545922114ebc5459221004ff735922100cfe7359221004fd735922100cfc73592210067f53592210067d535922114ebf4359221006be4359221006bd435922114ebc43592210067c525922114ebf4259221024fc7159221026be4159221026bc4159221004ff7059221004fc705922114ebf405922114ebc4059221006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf53592210063f5359221006be5359221006bd53592210063d5359221006bc5359221006bf7259221006bd725922114ebc7259221006bf5259221006be5259221006bd5259221006bc52592210063c5259221006bf3259221006be3259221006bd3259221006bc3259221026bf7159221026be7159221026bd715
  | 27 => 0xe639494157e7d63949411ae7c63949411b73f439494157f3d439494144d7e72949411776e72949410067f62949410067c62949411b73c42949411b67f61949411b77741949412073e41949412073c41949411b77441949411b73f4094941024be7690941575bf7590941575bd75909410073f659094155f3c659094156dbf739094156dbd739094119ebe639094119ebc63909415673f53909415673d5390941015be7290941017ae7290941006bf6290941007af6290941007ac62909410073e529094155f3c5290941025be7190941007b67190941007b57190941025bc7190941016bf6190941017b76190941005bd70909410067f65d81410067c65d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141024fd74d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d8141004fe72d8141004fd72d81410067e52d81410067c52d814107efa40d8141006fb30d8141006f830d81411757e75981410057d75981410067f65981410067c6598141006fb60981410057f75581411757c75581410067f65581410067c6558141005df735814116ddc7358141005ef7258141005ec72581410067f65181410067c6518141006f96018141004ff751814101cfe7518141004fd751814101cfc7518141024fd7418141036be5418141006bd5418141004ff731814100cfe7318141004fd731814100cfc73181410067f53181410067d5318141036bf4318141006bd4318141004fe7218141004fd72181410067e52181410067c5218141006be4218141036bc421814124ebe411814124ebc4118141036bf4018141036f94018141006fb3018141006f830181411657e75d93210057d75d932115ebe64d9321004ff75d932101cfe75d93210067e75d932101c7e75d9321004fd75d93210067d75d93210047d75d932101cfc75d932115cfd74d9321004ff73d932100cfe73d9321004fd73d932100cfc73d93210067f53d93210067d53d9321006ee72d93210067c52d9321006f571d9321004fe70d9321004fd70d9321014ff765932115ebc6459321004ff755932101cfe7559321004fd755932101cfc7559321006bf7459321006bf545932115ebc5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d535932115ebf4359321006bd4359321024fc72593210067c525932115ebc425932115ebf4159321004ff7059321004fc705932115ebc405932101e7e7694b2101e7d7694b210067f6494b211b67e6494b210067d6494b211b67c6494b215557f7394b215557d7394b2154e7f6394b211ae7e6394b2154e7d6394b211ae7c6394b211657e7294b211676e7294b21007767194b21007757194b21024fd7690b21016be6490b21006bd6490b21025f67190b21
  | 28 => 0x8241004ff7258241004fc72582410067e52582410067c5258241024fc7158241026bf4158241026bd4158241026fb7058241056fa4058241056bc4058241026fb1058241026f8105824159d7e76d95411767e76d954101c7e76d954158f3f74d95415973c74d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95415973f43d95410073d43d95410057e72d95415973c42d95415977741d954158f3e41d954158f3c41d95415977441d95415973f40d954158e7f74d95415967e74d95415967d74d95415967c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d95415967f43d95415967e43d95415967d43d95415967c43d95410067f72d95410067e72d95410047e72d95410067d72d95410067c72d95415967f42d95415967e42d95415967d42d95415967c42d95410067f32d95410067e32d95410067d32d95410067c32d95415967f71d954158e7e71d95415967d71d954158e7c71d95415967f41d954158e7e41d95415967d41d954158e7c41d95410067f31d954158e7e31d95410067d31d954158e7c31d954158e7e21d954158e7c21d95410067f70d95410067e70d95410067d70d95410067c70d95415967f40d95415967e40d95415967d40d95415967c40d95410067f30d95410067e30d95410067d30d95410067c30d954158e7f10d954158e7c10d95411757e75d89410057d75d89410067f65d89410067c65d8941004ff75d894101cfe75d89410067e75d894101c7e75d8941004fd75d89410067d75d89410047d75d894101cfc75d8941024fd74d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d894114ebf43d8941006bd43d89410067c52d894114eee42d894114eed42d894114ebc42d8941006ef32d8941006ec32d8941004fe70d8941004fd70d89411757e75989410057d75989410067f65989410067c6598941006ef6298941135f571989410057f75589411757c75589410067f65589410067c6558941005df735894116ddc735894115df77158941005fb7058941005f870589411757c75189410067f65189410067c6518941006ed6218941004ff75189410067f751894101cfe7518941004fd751894101cfc75189410067c751894101c7c7518941024fd7418941004ff731894100cfe7318941004fd731894100cfc73189410067f53189410067d53189410067c5218941116ee4218941116ed4218941006ef3218941006ec3218941004fe7018941004fd70189410067f76949410057e76949410067e76949410047e76949410067d76949410057c76949410067c76949410047c76949410073f74949411b73c74949412067f64949415857f73949415857d739494157e7f63949411ae7
  | 29 => 0x67c6518542006df6318542006dc6318542026f66118542006f561185420067f65d81420067c65d8142006df63d8142006dc63d8142004ff75d814201cfe75d8142004fd75d814201cfc75d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d81420067e52d81420067c52d8142024fe71d8142004fd71d81420defa40d81421957e75981420057d75981420067f65981420067c659814218dde7398142005dd7398142006df6398142006dc6398142006fb60981420057f75581421957c75581420067f65581420067c6558142005df735814218ddc7358142006df6358142006dc6358142005f77158142005f471581420067f65181420067c6518142006df6318142006dc6318142006f96018142004ff751814201cfe7518142004fd751814201cfc7518142004ff731814200cfe7318142004fd731814200cfc73181420067f53181420067d5318142096bf4318142006bd43181420067e52181420067c5218142006be4218142096bc4218142024fe7118142004fd7118142096f94018142004ff7598a4101cfe7598a41004fd7598a4101cfc7598a41004ff7398a4100cfe7398a41004fd7398a4100cfc7398a410067f5398a410067d5398a41026ee7298a410067c5298a4115eee4298a4115eed4298a41024fe7198a41026bf4198a41026bd4198a41026ee2198a41026ec2198a41004fe7098a41004fd7098a4115ebc4098a41004ff7558a410067f7558a410047f7558a4101cfe7558a41004fd7558a4101cfc7558a410067c7558a4101c7c7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a41026ef7258a410067c5258a41136ee4258a41136ed4258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a41004fc7058a410067f7694a412067e7694a410067d7694a412067c7694a411b73e7494a410073d7494a411b67d6494a415ad7f7394a415ad7d7394a412067f6394a411ae7e6394a415a67d6394a412067c6394a4120d7e7294a411876e7294a410067e6294a410067d6294a412067e6194a412073f4194a411b7774194a41207744194a411b73c4094a41004ff759824101cfe7598241004fd759824101cfc7598241004ff739824100cfe7398241004fd739824100cfc73982410067f53982410067d5398241004fe7298241004fd72982410067e52982410067c5298241024fe7198241026fa7098241066f94098241026fb1098241026f81098241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c7558241004ff7358241006df7358241004df735824100cfe7358241004fd735824100cfc7358241006dc735824100cdc73582410067f53582410067d535
  | 30 => 0xc41d95420067f31d95420067e31d95420067d31d95420067c31d95420067f70d95420067e70d95420067d70d95420067c70d95421b67f40d95421b67e40d95421b67d40d95421b67c40d95420067f30d95420067e30d95420067d30d95420067c30d954218dde76d8d4218ede76d8d4200cde76d8d420075f75d8d420075c75d8d42006df65d8d420075f65d8d420065f65d8d42006de65d8d42006dd65d8d42006dc65d8d420075c65d8d420065c65d8d420079f74d8d4218f9c74d8d420075c52d8d425e7cf42d8d425e79c42d8d425e7cc42d8d42006df75d8d420065f75d8d42006de75d8d42006dd75d8d42006dc75d8d420065c75d8d425e6df74d8d4218ede74d8d4218edd74d8d4218edc74d8d425e6df54d8d425e6de54d8d425e6dd54d8d425e6dc54d8d425e6df72d8d4218ede72d8d4218edd72d8d4218edc72d8d42006df52d8d42006de52d8d42006dd52d8d42006dc52d8d420065c52d8d425e6df42d8d425e6de42d8d4218edd42d8d425e6dc42d8d42006df71d8d42006de71d8d42006dd71d8d42006dc71d8d42006df51d8d42006de51d8d42006dd51d8d42006dc51d8d425e6df41d8d425e6de41d8d425e6dd41d8d425e6dc41d8d42006df70d8d42006de70d8d42006dd70d8d42006dc70d8d42006df50d8d42006de50d8d42006dd50d8d42006dc50d8d425e6df40d8d425e6de40d8d425e6dd40d8d425e6dc40d8d4244d7e76949425de7e769494244c7e76949421b67f64949425d57f73949425d57d73949425ce7f63949420075f63949420065f63949421ae7e63949425ce7d63949421ae7c63949425cf5c63949421ae5c63949421b73f43949425cf3d439494244d7e72949421976e72949421b67f62949421b76f42949421b73c42949421b76c42949421b72c42949422067c61949420073f65909425b73c65909425c5bf73909425c5bd73909420079f639094219ebe639094219ebc63909425bf9c639094219e9c63909425bf3f53909425bf3d5390942015be7290942017ae7290942016bf6290942017af62909420073e52909425b73c52909420067f65d85420067c65d8542006df63d8542006dc63d8542004ff75d854201cfe75d8542004fd75d854201cfc75d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d85420067d53d854215ebf43d8542006bd43d85420067e52d85420067c52d8542006be42d854215ebc42d854215ef641d8542004fe70d8542004fd70d85421957e75985420057d75985420067f65985420067c659854218dde7398542005dd7398542006df6398542006dc6398542006f761985420057f75585421957c75585420067f65585420067c6558542005df735854218ddc7358542006df6358542006dc6358542005fb7058542005f870585420067f6518542
  | 31 => 0x82521b57c74182520067f64182520067d64182520057f73182521ad7e73182520057d73182521ad7c73182520067f63182520067d63182520e57e72182520076e72182520e56e721825209e7e621825209f6e62182522057e71182520057d71182520067e61182520067c61182520d57e70182520067f60182520077a60182520067d60182520077960182520067960182521b67f7694a4201e7e7694a4201e7d7694a421b67c7694a421b73e7494a420073d7494a425f57f7394a425f57d7394a425ee7f6394a421ae7e6394a425ee7d6394a421ae7c6394a425ef3e4394a421b73c4394a4244d7e7294a421a76e7294a421b67e6294a421b73f4294a421b76f4294a421b72f4294a421b76c4294a422067e6194a421b73f4194a421b73c4094a421a57e75d86420057d75d86421a57e75986420057d759864219dde7398642005dd7398642006f76198642004ff755864201cfe7558642004fd755864201cfc7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d53586420067e52586420067c5258642136f64158642004ff7058642004fc7058642026f66118642006f56118642006fb6098242004ff759824201cfe7598242004fd759824201cfc7598242004ff739824200cfe7398242004fd739824200cfc73982420067f53982420067d53982420067e52982420067c5298242024fe7198242004fd71982420cef940982420057f75582421a57c7558242005df735824219ddc7358242004ff75582420067f75582420047f755824201cfe7558242004fd755824201cfc75582420067c755824201c7c7558242004ff7358242006df7358242004df735824200cfe7358242004fd735824200cfc7358242006dc735824200cdc73582420067f53582420067d53582420067e52582420067c5258242004ff7158242024fc71582420bebf41582420befa40582420bebc40582421a57e75182420057d7518242006f9601824244d7e76d95421967e76d954201c7e76d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95420075c63d95420065c63d95421b73f43d95420073d43d95421b57c72d95421b76f42d95421b73c42d95421b76c42d95421b67f74d95421b67e74d95421b67d74d95421b67c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95421b67f43d95421b67e43d95421b67d43d95421b67c43d95421b67f72d95421967e72d95421b67d72d95421b67c72d95421b67f42d95421b67e42d95421b67d42d95421b67c42d95420067f32d95420067e32d95420067d32d95420067c32d95420067f71d95420067e71d95420067d71d95420067c71d95421b67f41d95421b67e41d95421b67d41d95421b67
  | 32 => 0x1967e62592521976e62592521b73c42592520057f71592522057c71592521b73c41592520057f70592520057c70592521b73f40592521b57e74d86520073e74d86521b53e74d86520057d74d86520073d74d86520053d74d86521b57c74d86520067f64d86520067d64d86520057f73d86521ad7e73d86520057d73d86521ad7c73d86520067f63d86520067d63d865211d7e72d86520076e72d865211d6e72d86521667e62d86521676e62d86520057e70d86520057d70d865213d7d76986521b57e74986522073e74986521b53e74986520057d74986522073d74986520053d74986522057c74986520067e64986520067c64986522057f73986521ad7e73986522075e73986521ad5e73986520057d73986522075d73986520055d73986522057c73986520067f63986520067d639865220e7e62986521576e62986522067f61986520077761986520057e70986520057d70986520057f74586521b57e74586521b57c74586520067f64586520067d64586520057f73586521ad7e73586520057d73586521ad7c73586520067f63586520067d635865213e7e625865213f6e62586520077761586522067e61586520057f70586520057c70586521b57e74186520057d74186522057c74186520067e64186520067c64186522057f73186521ad7e73186520057d73186522057c73186520067f63186520067d63186521657e72186522076e72186521656e721865220e7e621865211f6e62186522057e71186522067f61186522077661186522067d61186520077561186520067561186520057e70186520057d70186521b57e74d82520057d74d82521b57c74d82520067e64d82520067c64d82520057f73d82521ad7e73d82520057d73d82521ad7c73d82520067f63d82520067d63d825209d7e72d82520076e72d825209d6e72d82520e67e62d82520e76e62d82522057e71d82520057d71d82520067f61d82520067d61d82520c57d76982521b57e74982520057d74982521b57c74982520067f64982520067d64982520057f73982521ad7e73982520057d73982521ad7c73982520067f63982520067d63982520d67e62982520d76e62982522057e71982520057d71982520067e61982520067c61982520067f60982520077b60982520057f74582520073f74582520053f74582521b57e74582521b57c74582520073c74582521b53c74582520067e64582520067c64582520057f73582520075f73582520055f73582521ad7e73582520057d73582521ad7c73582520075c73582521ad5c73582520067f63582520067d63582520c67e62582520c76e62582520057f71582522057c71582520067f61582520067d61582520077b60582520067e60582521b57e74182520073e74182521b53e74182520057d74182520073d74182520053d741
  | 33 => 0xc01400380000000000000008000014000007400e0050008104000002001002c00c001000004800a002007811400000000600480100000010000032000002800403400100880100080000098000000005003003803400a0008004028002033000400201200600000000080000028006009000003002800100d00000020110000004000000002800c01203c005000002a00d00000080040010088044034008003800002600f001001c014016006803000c002002800c00200a0020074004000001803c00000a00c00000000030038008004028000006000a00000000100160230188000010000000004002400b01780340000060028000000000000006401a00f002000000001a000800401600302f0010074009007000801e00f00700300200040008398002004000000c0140110030004028000001000002400600000000000030008008014003000801001c0db003800c08c0110018014008000001003001201202a8008002000001000405c012000003805c00b001801800600d02500100040010000030046003002000000000700a0040002050004800c0160040228008000004000001c01c018002000800000c000000c06403f003816402400a00080080000010070094000001001804000e002000801002200500000480040b3000802400a00f0060000026014001801000000600180880000040000018006005001002c01c011000804800a000001002c004041000800802001e000001402002f0018000038000003001400c00400d00a8002002021800000c0070000014042008000000c01601200b0000048017003003c00800400b00e002a00f01b0054032009000004002401300080b8040000018000000e006004801401c00001300000000070000034004002000800800400d003800c0080080008004000009006804c0000090018008002022003000c0000070010018056002002801800000b0038014000002002800003600903b00040000000018008006000002000c0300000040020000016000800400400c0000004016013000001401e000007003c002005001802001e00400080dc00401001880000040030000078000000004000000000700680000440821b57d74d92521b67e64d92521b73e64d92521b63e64d92521b67c64d92520057f73d92521ad7e73d92520057d73d92521ad7c73d92520067f63d92520067d63d92525fd7e72d92520076e72d92525fd6e72d92521a67e62d92521a76e62d92522057e71d92520057d71d92521b73f41d92520057e70d92520057d70d92521b73c40d92521b57f76592520073f64592521b67e64592521b67c64592521b73c64592521b63c64592520057f73592521ad7e73592520057d73592521ad7c73592520067f63592520067d63592521b73f43592520073d435925201d7c7259252
  | 34 => 0x38000002007002800000a04301d804000200601780040700010010010000003021000000200000f80080240000018000008000000004000a0100030018002003001000008e01d000800000000100300000020130010070000010001000001000100200040000130098010000005000800000e006008006000200300180080020000048000002000000006c0040080010018004000001801c002023009003c0020000000000000000001002c000000000001808800000380040000010098058006006000800001a008000003804800c001801c00800900180000020730000008000017001800001e00000a800800201e00000cc02c00c0000030000002002803400002d002008402400400400200220010000008000002000000000200000a0030000004002002000000002d01a8000015004005401a00e00000241ba000000002803800400d800800a001000800c000000004000000e0030000040006006003804000400100200080140230108108014008000000000202200580040020020050004000010000003000a009001001009804800d80100180700038000062001000002c00400a00b004804a0000030000012002004000006c0180068014000000000000c00200000b0058020042000807c02000200b8000010000004010c02a00c000002c00e00e004805801c00300c004001200400380140000020020004028009000000402c000000800c01a011010000c014009004006800000c003800400601400100300280110020030030003020800c03800b00000bc00a00600b80140c200400d8048006019000800805a00400000000a40100000028026019000000805c001000002c02c005026001c004002005006804a02100c000400000000100940a4009009800c0000040008070000003003800404a003001000800401f000800402e000000000401600a0060000060021001800c00200d000001c03a005002801800c00200000240020160000014002001008002800400100d8000000001000800001a026006801401801f00b801400c02200000080040000000000008003000002400400300b000000007000000000100010010040002010022801000c0080000000004022000801000e00000100080040000000000000003036000c01a00c00b0008006000000800400e001003001803a01c000004000000001c000800600000100040120110000014004000001000000c00400900080080020010060034003009800c00000900b800004e000002800000001000080240000030000004016001000002400000100000580ea002005802c000003001800c0120030008000006006005800c00a002000801000000a002804402e00c01600fc00600c0000028002003003804401402900000040000100008000000021008000802e00000000000
  | 35 => 0x1e08a0000008000004001000800800f00a000000000f0000000016005000000404601000e8034000001011800400800301a00000000050408000006000000001000600600000480180040048010120001000000c002036001015c00400801d800c04c025001000400a004000000000e0010030014028000003005400e01300180000080020198080006009006806c00200000180080060070050000002012000800400002c00080080140000010004002000002003800600e000002800801f00881e800a00501e0014050088000003000a002002800403600000380040040000028018002000000000400e0090010038032000000000001600200980200040010018024000018002806c00a000000000000a005001802000e00200780040000000050000044004003800400a00e001800000000400200000020010060000002008000001400802e000805800a009000000c00000b003802401202a00f00c000c007000004000a09100400100020070008004010004000002001000000000380000000000000004001001800800e005004002000000701a006801000400b801000000100000140120030000010000001009000401400000d8024002000003000400400300d8000000002005801400a00800000140080010000048004002008806401601b0028000004004001000800402d00000540120040060088000000000002400e0020058024010002024000002e0260050000000006000000c00e001000001c0060010000024000002000800001c0030070018000002001801c00400b04f0010028002002001c008008001003c056002006801402a02300080ec016004001000c0060a90060000000018001802c000012001003001000e00980000080070128000046000005002c00c0030008060004011003004000a0030000000010014003003800200d0010004002013000000002200900c800006c004002804000600000000080ae006002000000000000001e00600180000004006015000005000605400c001006e0040080014004016000803003e00a0000004006000000800c002003000800405c004003000400000f00a805001000e002800c0020000058000002014000800804200400181bc018007000000803c005000004400000b007002402a00000e000402e005026800000000400e800005c009000800400000400700100f4007000000004a00e00200000060000100000000015002002001000a008000401001100100a40000000000014002018001800801a005000800c01200400000000000040000004000003000004400000400b806800600500000e0004005019800c00003e00b80f400000600e000000a000002800002a0080000000000007042008c000001000001c00a0040050010046000000000401c02300500300000070
  | 36 => 0x2f135c7f452d141a180c58d007cb3f00008824fd4c7525140003464ab8088c000000000047a060022541453d300001b3c00032500df45e43fd4cb026a57b0f56000105615e106509392b200004053e54c460dd93d21c612c7418464e1d04000551800044809ab00004e800005ca1b7d4504e881180000b8600004f83d4c0000000000158928848443e3000077d2f48a0b0000306000000027b412f00003ed3c4cd7344ed0f02a8884807b48351e7cbad29ac0002d0116352751b800009692e88000000110b42092544e451ed000120821c000000002324ba10ba4ef4b370000273225899e00005071e694cf017c0004708000062c00040808c9373800041d00000000d400001389193c2f800004865434bbd1a18c6b1c9159024205f21ea8af90bac74546bcd0c415c70539f46dd519d00553e830103090801d106c4525529626c0a1f00007490d70e4d36986534d780a44c500002a7954b1d1c68a00014031c50e2556dcb56402c53f498d03917bc6553c101c21a2cbec4410aaf2b687b5557871a25a800000006bd1430f3345b505d29782e61ae52ce0bc40002c7c5cc00004202e1c0301dec0003b491573e5058724840002019423000150251cc00047380004e9c9ef025911611b94561f9134c00004a34b14b4b34e800007b01382e102210000cf61f0853d19140660e250ac36549d90a408ab1184a5223d8dd912f4ae61d5400039e8d010000ef0000026438540000001184226c0000000a352fc838a3bf14f400004231790cf752bc21300006f400fd1b747611f700015783ca0000531000000007670b280a8162400051f8d76525d00c000111d22dd52f00009d81eb4e3317ad24a04a80e537a50cd43295cb256078112b41b51a5ceaf55b83650001520540c000550c73d4c1c89702ac0003fe88e64b9d32d45089c05670f0e0288e850af82c456a92dc532c6d0430025118591450654faa25f10c8276c6c1055cb1903c40004424fed1fbc5ab09d096c1ca961500d4cab00d0f632a645b03810ae202b8092340c972403ce5f173ca024b9800032082631804fc01410ba72a9c06f3f80d611fa483c000000019c545c08b49843dd486d3e9482c22c00000000e9a3c34aa3005800a0040000002005000000400a02400000280000180038028014006000000000e002000000000e004003000000a035001800405a0000050010000003000002800400f001006800c001012000802600400a800001200b001000c02c01400180040140020008014008004003003400400100280300480110050020026000003800401004c00c8000000004023000000003b034803400c00000c800011800c002000000000c00c0010006004006001401e002000000000a000000000000e0110008004046000001000800c001005002c01401600480400000000178008
  | 37 => 0xb85cb2dc45bb47a4fee1100000467d0c35838ff138dc7c0126c4f208b151f2da124f0000d7a00015e50becf1c1604f36227800000002554b2c0000fa13e50e9508652192605808335583c0000000c005098980411ccce247800000004ae3774e4f31bc00009815eb2a201d407f000050b010f3b080001314e2c0000b5b2ec8132000159200013b20a743542dd528a2d20c9548894b32e00d9d000159a222800053bca0900015d10000d931dcc6ab4a340004c7000044d0dac35453e2000000000002a14cb883218bcb78197064c45b00001a1503e41e40001f04a2600003d4489c6ec530c47b00011970fc15311e9d0fe0000000394c4d005e08aa313800004590e00720cec15fc00035e000048b8f0547e4bc409acb0811c0d37377867a19b03cd250ce3151892742ec02b737d8dbf1ecc0003bcc8be48b00000134ff94a7d1833dc8e2e48e430531dca671ad090b2048793427503c3ab01873cb81294ce12bf4be0fec33a8c2124a89420edc7195748fb945c4544434c96d4c0c7124e5879d0f406eb52c0a40309107339b501942d49bf29c92db542d3643400b9e4fe87a84d088220638f4a10f13a43c014830000f8e3e8d3fd2e4d2d42fdc8690bdc9160000a830000000498918d4a1112e20bd42129cc49e4b4454c0ba8a6450cc858011d532559d369034404600000001d70f9c1d287bc343d1fb0acca9836293521150da31de0f0f0fd83de32cc6b51bbc0000d68da1221035750b40005474ac2148cb3e0000000499c000000000000000004e5537a38901ff33000000000ecd19e4988000000053d4912000000000000001dd151800012c300003cf5318045341400000003f3406069231f800038f14270000a4f1af85e52bd558934940004578cb51fb8c5837a885147bcd2e48a896e14c4e7428a475000008371f402540000cc837842de515d26539b00003afc1f8425512304e89f60548b10521128c03b008d3d1514f0000fb843d80003a0400000000004fec3023c9d26a335c9da00000002cd4b9c19b462d0000ab00aec4772490ec02c3059949a0a8900014dd0000627237c000000000017b40004cd4de60000e1f18fc00000000002464ac528752be23b8c093a28d9052651ec3af155d000123f58512302fb80000fe111e0100f2440ec0002bd0f8f0bc80005724000366c0004f255831248ffe37dc000000000031205a646ad4782ba07e215ece8b3360d1c0b9cca123e4fa711f83994bd10cf056c5f64fc100600e0ebe4c300004af40f60ad901b0000c403610880000000000000000184000562031e00000000da0ec550f14e13bb80002d1071e000000000000002098d5e18704ca00002400fa823900014fc55b53ca00000001838b76263c0004324763315129d0001513481000010e8d5f1494a340338000437000046d035e381ca
  | 38 => 0x6033e0aed454545f00000000000abc37a00000000c5d09f4000534c0000000fb532a042813c47510ad08e4166c23f20106a82f18f10262c5d43a8445944610a83178931001453b4814be334d03a30d2cb5e1d9830b3f313e3280cdb63aa86bb2e6c90000000000b445a807a93b0327c28d00000001f380002acd27b56c00004914000354095000e932418e00000404dd83a9d4751a9c0000b1883e261c630000000012c48c600003b9192ccb057f4db210bc3bc308113d56d95e031807c90000808312400000004762b74a2c3e240003ed80004bd40000024a822b848d9456001a19dc000449800057502e551293af000039b000000047d8000542413e15cc0d846a0fab000024230ec00007d906a45c9256408cf872fc400031a800028a12860000f4753880000000000000132b2bc0b7d3a785dc080c78d00042c11c340004414a221a50000562800019b800000014b90f0806c14dd14c4c6c0784298fe7000000040a42cd000136a05640f4247000006c8b4145040b70000acb3a7c4f537249e834a0d601c88cbe159d53c459435205884a528700b42378a9d2124017258000d3eb0a50028c19803f45a146700004d65108000021b350ca1830fc91857549c7000115d0000d5b000000053ad59e0000000000052e00d8000000043200000005360000448800031a102441dc41315389534f385c71979599548860a0c9490a05f85a03624ed70e501f236f8505024d52300009863e0cc3a35a8e5143ac00048e812037ccf0352906d83e14b99177464a25dd10d42a800026d0df92f846690f0d0811d214de080800052f408b45a05330334bf913f8cf406f02fd1a801ce0400e4a08e0000391470431ec7f70594ea34b08b0415c961700007280000dcc42e00002f681c71210ec60d28b9122e87132154a8b00000003348bc73db10492728e8e07a406a033d4ce0decd2000000004b7c0002c2c00022880dd4c9400045fc88d0704ec32918b7432640000000000050d09330389920000caf48ac50a3ae8000000000038014ad00900000000d7c3e114d239b89a90ab916f477c00050d00000000cee00000130774c234b90fa147789ea39653dc00003513d4134f00008d710003d901c4c74229475d0f6d0df089cfca0868b704698588310ca6d4a2c66553dc9dd0d98729000054916c8d703bd90023b4c05b24b48563d8505916b41880d884d85364a4554842062cf0634000114a363cfd0363118b311c7b21ab955b1b95402000000010d40004600000266cb8b0ae8000504051b0000ea61898854000032e13e869551d040329e8ceb44440004b4c13022d8f323bd000000008c357b53cc12fc0002b9c000367158b41b553f32050f518207ab2568bb15398ee83fec5be31e13cd53b054104d826f1dc81b127c81580e40055364841e01513970eed3415
  | 39 => 0x127c8a100002a7577c9661d4d12b000114300004d221d00004e84000114000000000004d54b6200000004c2800026440000000ec70b8031c0000000000145a1308000535c00000000532d48f74000014a0d1910a156065006f47e71ef953029f559724c127f572962127b9379083d1362758ef1198020537951610a4d3d804fc0d901890dd2034ace49e535b000000000000000000a171cf80000440cfd1bcc6e3000103f000000043a8d720644000447cdf10000d8e13383080000e41432d5514f84ba0485cbfd1254ab437e15ef1b6d504474404855685ff231c9492794bcc18514b12054bae28295fc13dd44b4c450542cc15f324952432c588c203b41534d58aea0dd113e54015d8290492f42d8da93ca8e583ddd5dc2fd000000005e9008c2db27f8000000056457d03cb22c9542353901221f809a1b141e22d0ca0e05c4cd000000003f7800000010c54f440000b1408100001c900002fa216c0004e1800038acae000013f40000f080ca0b3305d0d0a39d42ed331c0003dcd06629d52481324e4225388391a3000000015770c756232e345bd000042d0064a574e800001ce80000ce80004abc83b4640d97379cdcd43e80a606b4cd30c68b3923f0ca700000000000c5758651c605200e21f5900a4cec0004768d2c1558000291c00000000000000eff2224c7f07795ee4f98de210a40000000db856440000000000000094026b8f1b000004426880000a380002d3461000015414674e124c8541d0c3d4580294000000161e4fe0098545000020800004758448000000028787654660a430df89eb00002432c740000000375000144400007af37b90224cd899a298520201405c80f547982b301aa31e8edf490047d47cc0b61ec52a602ccc2935b037257d80002eac0004bec0001df047200000000ea0fbb4ba47d721dc09722d4a9a373c6a32f5817d4624ea0205d5c5047d06226f513013e53c33e593b158300001e006e039a80002bdc92943f0620124d1ae145142448c42850b08000134c4cb26ccb901f995152419246486903700007a318d800049f800049851f50000c9c0000000000000025340000000000000085336043d3000002c000000050786fe1be4e8600005080000f8b22b52ff0b68b5d000019e10c00c6538c0b90040e10000063e0000000000118844e4bc9000000041ec74d185ce72483c0003e1950a536c3174e78bd12060e872e6882d18ad19500000001f308a92694ff830055e725fd102275007943d0d3300000001ed000038a8675244400011ac00048c953817887fd2f3480544b41464c5432120e8f4f0099098038052f09dc8721660c3342948f80a280251e911ea1c182941f549ac2ca000014341722958d6f1c8071d183d0bd3b5036a49c47924af0e7645f8000397151a55282664d9522600000000bfc07352a4
  | 40 => 0xc30002c8359355cc4c34f84fb505c32f24145f44144aa90804738144d58146ecadc523cbea46c478544dc4e2248d47610b06bf5058d26000098136e8a6234491382a286783f900d2538145e00013e806a00000000f4e0000a704f749640bf000000001693d10feb3d80ae502ec03145ec00000000000000c8700006cc000000034240be115c1d744043f21ac44734bd831600010ec3c2c0000000000000072e1d8400047c0000183000040c45f70314000000000022e0f06000056f1c3c00015dd12700008d537b09f812b05ea08c082e429c000461c0002d1c2cb000143036891ff22200373d3490c00000000ac06d40000311530461f000042b18b84623adcad62ab04fc17852ca2488be40f7425a12f89944a3d29b0a7c4e33e6867f2c98dfa000000009e4ab222d00000b7cf5b08a51915694d7e0f18fe600007f6238c00009754071b344d600000002e991e72ffd12c3ec83a936f530d0b5c000000000000000001fecbcb00000000af0b3118540bc000067c43fc57a376c833201c86400007e038a400000009970aac34000000000000bac0ec55fa2a111a754e40003df880a0160dbc000000046cc06b3da4936061412711443af000086a43bc92800000b53b9ce142f740b838d071543a4717069949b00015b82a1c000000146f0000000390000025e09bc3c50dda149842400014b2000143941fcf2100100000000ca532f000031b8d7f513030a57e00001a44000005149e379138453680002c4800019f8fc43f70aa43354e5233994e7570c3233f7d0ae375cc7c37b4eb02338d3f053c4cd03a453c360834d3f60d461bd85fe00014130f9d42f4a384462d60c0813fc00030d0e901310d6d43312901c084e13ec54a624409fc4fa862550c40000000000239c1ca3b40e7b12a55d70d30be6200c00054f44793d0134b1149624000000000000004d28000000000000001df48f80000000c5b000082a52402dc37f88eb416d4f03d4929500000004140ff052f0ed515795dd0a8d3755880000000086f407541c41c800039385b60e714e8582400047e80560de530907dc0002bcc0001b70dc4417800000011f225e800042295e2497c0000c1c0000000000064cc074b40ade1ba4dcb03c800000003ac32995c2404000000013ac30a0a490c6cab60af409d000109c119d29110601031d780001be09d34cd0a7b00011ad37f0a6e17b80000c81067518c38442fcd42060429e048c5574db5432000000000008930000000192404a4ab82f942e51d200000002d704c6421429a5224490392cc4f26e4fa833755da14c000005982ec325c00048383734978b0f582d3ba57c431420680002038a96497518620915e60000000371476f41e86662e08d2b4d846c220c445c354cb95114c94b55602591c241a3480c3c92f50698018d4683978e3d069d14e
  | 41 => 0x3e7469d3eb8b6300004ab50882980c38ce805f011e5471435471c0000000c9d269c27b1bf000000000c722ec37d2bbc000348400024d0dd22d7ce8f33855fb249c39205100de26c94f3458900401709753ea4000031000005dc1f01ba062a0000e4634bcec41bb8fe30ae000026a8d180db88e2154c000332c3c446f0bb43fdd3ec092501e3c24c0d14555cf053114d29d80e60ca46b30b3d02b36dce9d0fd0ee0147c04100b933f0000287525872751a8b1b051c0e13c48adb034c9131cd416157d45611b249f906840fc001cb4f203c43412e00003fcc2c8283515c4e3c9ad30d4000319d4d1545cfea4f4111c00f8125000090e060d1c8000000027194a8000020911094b64f1897d426cb4e243c04f188ce8226ed12147990d7000150e5819084298c2ef000068237ad5ae1960cef3d0c0004a6836f37451764be83871e38b020078ead30505af0cec6a14f9c6d60a0846a03240000dfc1cd0b30b4c32248f4076003b4f212cc02f400021b80293b2d1130000a7800000002c7093c39f80002274b551694006000102a487469b03fc16436ac00028209e91a3528110dc1960abcc9227246cb36809854ac0ba81270bbc09d456b2000bd301b87ea02bd56a3d64c830f7000047f87341c995504ca93c745580005680e4731087391d512fd2bf0e793b9800000004160000ccc000027f0eb47c34ea078249040003cf800019740002280c6d4ffcec945e8baa41a4ac30c0c861006d2f10f302573210d043ad553700005fa52705ba4aad5800410f6501b459e0000c5339510113751579423027a000121e1a714290fe82d3300823643ccf1e47813d90860d68383cb6b31412351018a3c3e7c881391124c19343b614582f31d80e393da8c9b04648bd1f50bce352c6f02a0109a41d866421f424d045c01807ace3800001794c0559b150c7f304395855510bdc2caccbf47b81d220742e8067c0002fd931a16b8dca009c00027c000000010f23ab8000000c00038c8f30569d2b9000000057c07a12188b1e25288ed3f514dc0e986b7164930400011a33ad8fa40b390c2000078b2e243ef04ed15004d061d554d5ac14d85d841710e72964b294e48d9e4edcf790780d980cfcbb5000098e004541236ec8fb0ab00004c387690d58487034010b445d2553b841fe53540c82efc1dc2af4bba4bbcbb317a13d633cc3be3d54a5a3fa108d00302c027805465710cfc119888330944f31ed8bf053300002ebc00000009cd13a534552153f626c4f111f4874f09582a23ebca190000a3e00007a2377089c000058b4a7955200007a923290b2000000024995ea37bc000541439330ac0001e5c20800005b91478000000127a50455840000e9407c40d520700001c38d244df03ab00004f63cdc00000014724fa51dc5444ec82da913300488c10ce0b3b066ccca385
  | 42 => 0xec9ce3dbcbe03e4459c37083c021d481324f8000062412b5294d640000fc1000055b58043220000e1601fc14200004cc10944b711909d700015d90370cf01860643510536858613d52594cb43d60d675590ccd503478a112cdaf39c09e616d056a40010251f7c56d26a07ed5889170012c99554a4e633588e6b20304dd23a956b1d30dc140d93d71e6cf3d3520a7954b8b9840e020c51447ba55d45c24614db5464d1ac18111e138703c506ec0aa18c8eb8213476c22a059f34c866b29303814a8c63b3e48f410b88244403880118354463b048a3465863d48b43aa38451dd06285f304b03781f68be73d5d0de46e82f6345912a1f84396224004302c441b48d8e9b51f04d44a4d29c1e44742227c51a2ce92f924dd0e341c0841547846008544c31404a4206d87164bf05d70c907d84c20296343905546807dd5351469425caf8052d5824bb936e36003e62c911d41379052181444713b0ebd5635244353087c5430c4527dc28648cc7c43d0809b54a84ee3524a0728dd419390c40c54482fe322099c164048f01494cd1b494be3e2947d08f4a1a3574be802e8b3d46c8d83519550f404c98d51642122d5c31339f000023f400046304b64ea8ad82c013e0494d3704c2ca150d3c45b5720e2132305cd4a8104411a4fd929293100000b1a0224f7a2fac5685100d8d398811a3aad33d4b3cedc158101c55700003898000314430d1344057411437a0000d1111308d43620628174cff50cd0270231139043841d3154122f54d8c6517010e644a44a14f1440753210c13aa04af1b18f6d26615554b34e6441f131e1e7869308112a508d4e690a5c6292480b1423003a247110c443610580f3944306e0c9a1c447c848906b6035c34746f425027705db04f4f6451dd2ad436d155330c0804350f1a423807e042007c09f83864a140002ff926c2b2416d1dc5114000079633b400050181ee0a3145456acadf00000004e2c000148544f000143a28fd2d60db484734c460b274929211343d100013710038bd83fd91c1321419015704190a0c2624c0921c000021123741fa119445d2b4400000000002a84e652dcc32c30449e4335081f2b4c95239209040b4888b4fdc2c7057c0fa24ec12e3bb082930687f230c061a05547f8367c00025cd03200005701bfc0ef5820cb600011ca2140000555cda407688861f4d37231c49c416a8aec467849151c433d1de4f0257c88872b3432718d46f528000001d90f2c11e019c00740000bc000000000000000000000000034a8fe24efc382410c86314d4000299800000004a60d6c65424fcfbf2b9000000000000c244081a9400000006a932a8000000121412f0552345c838125000037200003a940003a705e04e3800000000004ae8bb801241414bcc9553de00001cbc92b00000db06b919b0001527186d1f1000000
  | 43 => 0x8c0000000000087b00000004d38000240800000000003170c8005b058e01d40cb19f43120000fda000024c00005b300000000ec8ffc3cb4d871ffd10e1ccc81b01c840a3b644b22cd8000476cb81097010727cd1b0479464207854943c6421e4a00db442b4ed635b88ae4d713d3318813317d400000003a742dc48255ec0c00aa424635ec9d11a0022854ed04a0d8c72d0e9108b3fbc54b0ddc0000000c5f0000b590000000000133e00000000000b5a45100000000a6000012513b88f1f00007254c60b5400004e6567479900000003b31091268400031c8439347439d1d6000008cc471241ce28000109000012e22510315000000046513ae234d33257900002e14d9a44f1087000000015e400000004f03f4800045d09901224ac12268000549800000000003a0d0a449a48c84a1cf901e515e900002a4427879549b42b2459028f0000c9800012a235d40000000816179c18d0f9104b0f840003c800000000000522cf2f479000049e0000000000029c400006a44222e7d4e550214184948d13000044551e8e96541c65b0000000000140500000001c1c5d2171495f1d6c000358cc7d2fb4f262c892d5240d4e42e754530e2c602556545b0008ad500a098c2e950a9529c66344c8000000097948f00002c340000000e2f063c0001f2c0000000d770000000306c0002e293940000963000000000000002b3cabf35d1535488542b4e70a241b890b334f04a4194405a0000cc10000c32370c4db0428dd00b0ce1951b000012d09704a24000178c6ba4bf8a2d1408fba37c865f3ae4bc5000132716e14aa16547f00000a5d000103d4ad08421f1c7d9381445f50800003bdc0004f3c85d57e44963d20ae911591be2f6d33a1b91088177cdb037d0699005425f513805921c40000948000000114600012151d88a2349b8b602118da811b48e5399c53a13ad2ac302c67b3dac8f353f4fb7000000000000004de10a12380a944f00892000000041a04a84ae11670000d4f42d06d318c4000310553e54644da00007a6247413123854a34dbd33105ac00000002e108e86fa4d7ca8e14ace302b28f7000000000001447463c1063a904973f209af2b18968301039a1d3814e388101724e40e838288732740cc647342a54e7ce3648a4b8e07d4bd02ff0a7c0efcf390ecc1490e8106b010873b4388cb200000e3000067027ec0000c403f558280000000fb055cd218070007b05c08b133889760631135387441242ad5d611e95c01b9c7cf3380b7c348c17b02b502600006213ef93513d24c36139c000030400f160011c116051100001cc00001802bc43da0488b6142ecd291704d3b31550d5210c00046e51a91c04000085d02802280004e300003048344152004c5588b095698b6e26d948038b480b264d4871d645661b641e62520ee430a8a5300005f038
  | 44 => 0xc4c71c143846f4c7c7ca00001d117408ec15d01820ccca0404906ce2d409fa30143ee26e90d1484d13114b4c5a1a20afb32ecc4a0000fcd0d84f23195d3c2045483f2bc80864608f935778a6c53f822646d86112ad531305d4e570a008da25ecc1f32dc2a043c506039bc000523815003a800000000003bf4065000086c00000000e14a100b64a77112400055d873c0ee80002730269210096b3344fcb3a306bc0fed464352824b27f55d01390bd91cfc00000008bc0d4c3fe4e4d0b0277915f000072310d835d0d253731ae0d06559447f0870000000051c1a68e9843195e83a202d44cbcbf8454c5d11cc01e84c8c28950245931024ad73f085343e5c0ca0ca920b55c45860350f6e353477748647b723c55080f28dae000130f39c48f50000fb34d80aaa4e28074000002f00000511c0078f55852d94468a9b149044f364531900000001320e1e000149f28c40001db8e971280c8a52ec8fa00ad23735e4b2f217800038055db473009e478c0000cd80000ad419a3234b0330f54c5000011328ec74014a14f8277cfd6283ceb42ed90c7021139b1ee157a4d241c51ba81d5129c5420e4487914803f12c04a7e23c161107bd220333d3543e30c2c34346830434000044800052604833240afd4338488351078310a8339532912417588d82180e034940aab14e428100012820000cfe1fe4b1720a020a025555f39542dd1b9885c212cdf01010fd34b612c843592b551fc2c906c0be928b8e780d04d1e5220c3e563cdf504e5574033072b3820e1a115415445f4abb357140003b803d5685021078cf2530dd04e00a82200cf05f80000e801ab46411a245654dd8000472435515142a648401d90020f82520800027fd59421e8a3d09e15bb07f542a0e60db31fb152419c876800002952bd92ed53b523d00000002a7c0000000a2700001f4123800000015bd19891bf00000000b540003110cf119851fc30b8d5551ec00037ecfc735f515b27c53ed01f519a09940224100ef53f0c00057dc9e121305753560f353370b234d010a343e009c0690a92223c32d4f7c9571b0cc18110523443b94b84a0cc790c64d36286d2e33c5515240c022e237020018f1344065152d4b81312251c3582c149e71555600240544d06f8ab91dc0331027c19d52347d15874ac41a0460654e8f013accfd712e533012e800013047892d9c0004fb902f3ac821f12d4000268c8cb4f2c00016900000ac4bbb4a911191cd8a1449914b73324f7108eca6f468813c13d00d621a104c2b003d649c0c69149c3e003dcece1d2cd301bc54ab0571442087431f3164daa3df403354ac1a015d8f5e21fc75f46d46d710745824d8cee51b1d2c445f037150e139d000000028c89c14dfd48c0000000000054d0000e3a31b05590bb8cde1cdc2bf00001ba4a512733b450030d38000558d5
  | 45 => 0x3d237f45d551b44751440dff126895d4d992a7304cb2c23bc00051853c1410862c4d1d3a6158c52a00009cf2bf8d523a24bc33cfc00029d12ea4824e5b3d44cf22f545221e807871864c1011790e42884444140d2c157fc241362c00041bd1a10000bc141f80003aed59f32e4f9e2f2091b029c96f17b15962a5c94f145c9f53e80c160b8d60754b0fb4272c3b809c4b9748050a05810ffd13a95250d7cad215b0e560e396133c882f40890b5300000002578ef94ddc0003f840f3169c0004400000000034354048653d9d0750ba40a043646b202c00000000d2707948344fc409923fd4bf0cf933932e0d5a4801362260d5d32f885e6322ca584e206fd48941db3cacee3000013545dc0005149357000000000011a455390164ee0db9028506e2341382418c00050f4ff400010831460cba53a546b0001115537c51d20780000e540001efc00028e8f5f1bec0005030485000100826e136c1e713a94ac470a08515e100011d32844bfa3888a382e90f4b24f46c024c8b650a48dd515a507d2788aff2cb91f4093c78c000022247e00913dfd20700000900f0514705bc8233974935171887629a80003be01510e792570e300001abc00020f4b8f10fc0eb444800038fd54026dc0000bd458a00000002238e93452c5f100001020c3033755807211e215e300015284e9400020ac480245c1d6110d0152344000000093839fcb4a5010dc0475c0001568000070d16a388c00045d400048340004c15383295549a118d4490000612215d5af54d0e9242bd04f09b15930000509000000050f80001674d102e8cc9e04749512e301a222e42ad1ec04313ffc0003e600004d0d17350d86da109c3c70e7cc174c98ce4284c3f72ce15bc1ff92492518b2516f06133ef400046054700ff11aa3b608f208bcc960000ad4216558722640a948e0f3a0f613334e011060ffcc3c12ec55143f41b70e00b5110e0637551535d35ad24e2148d41000000000000c35520cda49f4c2201dcae34aa557d553543b38092c92994e4951810713b6d4a2384c0e43f749e30984d142af8fd14bac2451234a51470020d0718de32f7957f2ee463a3e6c9d51644c643158954416921f1050e99235897412a8b462a70c861a98cf52128e0b2c382881d691c51f3477a3184f5416146074cdc5c957044682c808a72920d3913bcf5d3fc88fe0000000506c4cf3ba55984adc68753c43f93cf160d01e8fa62be86d1213c4174fbc6332c541762ab950619583c823491cb33a4000561849d4f7800000009614aecdc615f8c70000000000000004d413223b28a5f4968efa4340000292c51200005404050000584000049c83ae0000000107d12f4c804e000006c80f9516b4bb026755bca362fbc0004b7800046386f2157d212106814d168c0e709c8f620000ca90000ecf0000433000085a2
  | 46 => 0xa4400000000002e8524b3c7400040e889156c4000403400058140004d6800005b902e3b74000046d4483598e8d000104d00000000500000036800030540000da554738245c33694c8f4ed453e580ccdf2ab463931980000a6c000082c88c14640003f555b94fc8c2f45680fb1920fe52698e3529100004df40000580000000143f10ec8142d900004b94c52000000001d840e417ca16256d00915c53da021447c44a12a14c74547196929819bd001478916900009c50000bf508f0a8c0000aee0f7d4d0000000008a940a142d5a843a062200003182c4493a0aa15541f70c8e00005fc1ef4a120000cff2ca92da000092e3488000000000000015b400000000000000000113f3cc433233e40004b5c00002b02e4155099f4c580002504b42000116e000000000013db4e1d45d152857d153c3e223301d006bd01a0d4000049993d4000000006ccc912a9400055a4e5a42c42194bc0b9230987520000000423cb94346892c1824d542260b2d4ef8000122c000199cc194ca06ca2dc886658713e449ace95000000000007432a3462400000001964bc200002aa46281a5102cd94081d0be0dc00000d9c00000005d9000096249340004ee400000000000424402000000024ccbd7503d4f900005de4d1836c439400000003603940000515400039314ff0000c1c56915c634b466a40cceed00011a5339d20c0ed000000009a40894163335800003f800000b400041200004bc88ac266458329a000025c4c2732f4b7742642d62894d1b059d3993a887de10f49144430d4727204c00a10bb730b4d8519a10da32b899d293415a35947760000b7e28c15a951e468403d408c2adce8432c442127b059a0000a5c3408f660fad5b21d195704eb4cac3c590a20664c933e2041c0ef46a25050f0c2f28d08019c2b92de95a3217d5cc49dd568502d4ba1a9134d2fed3174754d385094b212de446c4accb3426081971e1817a019126f04508273f144e540d425b4ff957e2a54e60072d5ad296d61b2f7d3f924252c00a711cf371cda74c00f3b52808210978cfb4960d5953ecbbe587d39a2a4cca41c6cb0712cd4014ff158e3e88674347d5ce1df86d52024e2735c510f2db538d1a7ca8f50a0aba58592d20fb048c3f6c1c43f24e3e39dc8e830e007004dc474173954c3e64aa629386ed3e351483c60a2b2138be52564ef2446c05e211038f2250e681f6d3ab0610126342c98a105404e5300f7651b805d386027c40d14ae3308a8516d505348ecc764ded3b60b60b7b535803c1fd4d3d4b1880256e953355b00203d704014580ab1571c86b3df08a607e548a02fd12541e109f1bdcfbc23a5374488ccfa55592973ca49672e59566137076b40b03b515f05f92aa08f731cd4b5103c3044e60d453310c0c17f42d0000016a1ee544542f01053364efe3ac428b2dfc
  | 47 => 0x524c0210220d690238de030e50f73658db100001ac53d8d152624ce53830b453bac00014a472c0000000000000020943a10f5c1bf06193b304a1466007048122bc111307400000011920000e0e00008b343b488545649be3018000023cc31553d2aa30283b014e0ede47ac0322b64000422494c5440087143c0691eb07bb01a06e11c20a2a21e11541630a9046651d94b84258565455d1e94b493a44a54091d37e4190eea53a8fad1dfd4c749f14c92fcc7751f148451168cdb16884ed434853200007ae57f842600295be300c58f43ecd56303c00b0cacb320d08b6605780002e20f0a4bdc0f9128800028811d052044fd000133c0790f460000d354ed071f2f3c6ac1c40397270c0822680647000067300008672c605b7104536b48584c7000038324681f329fc95c137c00000000001ac07fa165c4b03e0000026d541f0000a0c136517817ed22843e47eb1c2cd8605fc97e08c412154593bb0fa514053b800000003451f9468f00000003bbd3c4546c22b49d479040b4000000026d52b020e00013eb0928b0605ccfc620c056e2455107497038d00007e31fa036b2ea4f3820d940e2db08104e04f5a328800008d0f071d58d071c300002b1c0002da541503c0000094c7c64908b6f2a801561aa869000000003cd061e09a16124ad80833f380000000a0500e501f1418e1b3e040000000cc54104192243423e28048a416b0f1708dd2dd1a580000859027425881110b8ca0374d5bf42515b307eca914d2040d312d21b23355cd265881939853bc0e20d992c9c5c449d92a8470c5a906d01cf3aa426e0c980945244ac847f48bf1040ad048280001650b83057450003e00003f3c91f0000000328c76a2708e7348181b941b0efb2a0475714b069e161076d4fccf6819d8bc02bad61a38348db0cc124755c836404315a24d6000000007fc000113a16c525909d849929a4731000044e255812d28186524d9d5b51b7800011280002a1864406acf7b135464017695493758eda440d49216fc8c510f80001e114f219194c200014374d4d25b338cc4d52842991fc40004e1448a0d207033078dad27d0cad4249299084000000000000000b0a000114900000000000a390df068e09200000000000318c00000000004c18fe91cc88cf41184980000000401d1100000ddf079ca333818000459800005a0596000000055f13a33999329
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3d7559240040018bceab1c8008003175d56390010006373acc52002000c6d7598a40040018dceab1480080031b5d562900100065ab22e320020048f4815db20040019caed90e400800e1fa1776880100043ec2eed100200387e855da20040010ff0cbac40080030f99175880100062f31aeb100200087f8759620040010fb0eb2c40080030f9d564880100061ebaac91002000c5e7558e20040018baeab1c40080031b9d6628801000636bacc51002000c6e7558a20040018daeab1440080f2b9205628801000672b12e3100200387c85dd9200400517909bb240080063720f764801002476416ec90020008f781dd920040310fb0dbaa40080030f99375480100062f31eea900200087e87595200400f0f90eb2a40080030f1d165480100062e39aca9002004c7471595200402f17b0dba240080030f99774480100061eb2ee89002000c9e63dd1200400117d0eb22400801a2f21d64480100061fbaac89002000c3c755912004001938e6b2240080132d1c564480100b46ec36e69002000c5e65dcd20040018bacbb9a40080032799373480100064eb26e690020008de8758d200400b1b90eb1a400800317dd563480100062e3aac69002000c9f7458d2004001938e8b1a4008013351c5634801000637bacc49002000c6c75989200400195ee931240080032b1d2624801000667b9cc49002000ccc7398920040099c8e331240080031bdd56248010006363aac49002000caf745892004001958e8b12400800333dcd62480100066639ac49002004ce47158920040018eccbb8a40080031d59771480100065b326e29002000cb564dc520040019acc7b8a40080033558f714801000673316e29002000ce562dc520040793cd0f90a400800339ddb214801002476c12ec1002004cd67158c20040091db0f31040080eeb920562080100066ab1ae21002000ce6625c420040018e8ebbb22008003351cf76440100063bc2eec8802000c7485dd9100400196f09bb220080032d21376440100066bc1eec8802000cd483dd910040018eea7bb220080031d54f764401000673c16ec8802000ce482dd910040018e8a5bb220080031dddb75440100065bbb6e88802000cb7761d110040019aeedb9a200800339ddb72440100047ac34e4880203b9e6829c91004001ac8a4392200800339dd87244010006b3ba8e48802000d64751c91004001b4ee83922008003691d07244010006e3b98e48802000dc4731c910040773cf0c39220080ee796187244010006b3c28e48802000d64851c91004077accca39220080ef5959472440101ded3320e4880203bda5641c91004077b8cc639220080ef7158c7244010006b3a98e48802000d65531c910040019ccc039220080ef789807244010006f1a00e48802000de0401c910040018eeed2922008003591ca5244010
  | 1 => 0xd0839ac408002ab61073588100053743ea6b102000a6c87d4d6204181cc8e3a9ac4083069b616535881000727a9ca6b102000a6e8754d62040014d90ea9ac40800393e0d535881060f3238aa6b1020c1e4f3154d6204183c9a62a9ac4083029ba1453588100053742c86b102000a6d8590d62040014dd0a21ac4080029b61443588100053742ce0b102000a6d859c162040799c8e3382c4080ef391c4705881000557426a0b102000aad84d41620400159d07a82c408002b360f505881000735a84a0b102000a6e85d0162040014db0ba02c408002b3a0f405881000566c1e80b102000a6e85cc162040014db0b982c408002aba13305881000556c2660b102000e4d538c162040014dd0a182c4080029b614305881000726a9860b102004ae6810c162040015cb02182c408003b24c0305881000537416ed2902000c6e72dda52040010ff07bb4a4080021f60f769481020c3f416ed2902000c6e82dda52040814db04bb4a4080031b9c976948100043fc1aed290200087d835da52040018dd04bb4a4081031b609769481001c3e412ed2902040c74215da520400187ee6b24a4080030f5cd649481020e1f392c92902000e2e7259252040018bd0eb1ca4080031761d639481020e2f392c72902000e4e7258e52040070ff0f314a4081021f21e629481020e37394c52902003a6f8798a52040838df0f314a40800e9b61e62948102063643cc52902000c6f7398a52040018dae7314a4081061fe1d629481020e37392c52902040a748158a52040014df0eb14a4081071be1d629481000637b9ac52902000c6d7358a5204081cc902b14a4080122fe1d649081002476c3cc5210200387c85dd9420400917909bb284080063720f76508100043fc2aeca10200387c855d942040011bf06bb284080063720d76508100247a40aeca10200087d86dd5420406d87cc9baa84080031798f75508100043f43acaa10200087c8759542040018b8e6b2a84080122f21d64508100061fbaac8a102000c3c755914204001938e6b2284080023761b73508100062f32ee6a102000c5d65dcd420417993cc9b9a84080032759373508100046f43ac6a1020008dc8758d42040018beeab1a8408003171d5635081000637bacc4a102000c6c75989420400199ee73128408003331ce62508100247643ac4a102000c6f7558942040018d8eab12840800333dcd62508100066639ac4a102000cb564dc542040019cac5b8a84080032e593705081000674b16e0a1020008f9861c142040095cb04bb642080039914962c841002573c3ac59082000e678558b2104001cc90ab16420800399d4d62c841000732a9ac59082000a758694b2104001ccac529642080021fe1975900104b61f322eb2002000c5e635d6400412f0ff0eb2c800825a1f61d65900100061f3aac92002000
  | 2 => 0xc75988100053742ce93102000a6d859d262040014df0aba4c4080029b215749881000567c1ae93102000acc835d26204001c5ea92a4c4080029ba16739881000536c2ce73102000a6f855ce62040014d90ab9cc408002abe11739881000556422e73102000a6e851ce62040014db0a39cc408002aba10739881000556c20e73102000a6e87d4e62040014d90fa9cc4083069b616539881000727a9ca73102000a6e8754e62040014d90ea9cc40800393e0d539881060f2798aa731020c1e4d3154e62041814dd0a29cc4080029ba16439881000536c2c873102000a6e8510e62040014db0a21cc4080029ba16709881000536c2ce13102000aae84d42620400155b09a84c408002b3a0f509881000566c1ea13102000a6e85d0262040014db0ba04c408002b3a0f409881000566c1e813102000a6e85cc262040014db0b984c408002aba13309881000556c26613102000e4d538c262040014dd0a184c4080029b614309881000726a9861310200387e87dd562040818e8e3baac4080021f60f755881001c3f416eab102040c6d82dd562040070f905baac4080123d20575588102043f438eab102041c74711d562040010ff0ab9ac40800e1f21573588100045fc22e6b1020028bc845cd62040091e902b9ac4080023e20173588100043f43ea6b10200387c87d4d62040014dd05a9ac4083031d1c753588100043f43aa6b10200087c8754d62040014d904a9ac4083071d1c553588100247743ea4b102000c6f75d4962040078dceb292c40800f1b1d652588100247643aa4b10204087e8714962040838e8e2292c4080031bdd4525881020537438a4b102000c6e8714962040014db06292c408107991c452588100247743e84b102000a6e85d0962040014db0ba12c4080123ba1f32588100053742e64b102000a6d85cc962040095cd03992c4080029b21632588100247643a64b102000a6f854c962040014d90a992c408002abe1132588100055642264b102000a6e850c962040014db0a192c408002aba10325881000556c2064b102000a6d83dd56204081cc8e3baac4081069ba16755881000637baceab102004ae6819d562040015cb033aac408002b9e0575588100257240aeab102040a6e871d562040018dd0e3aac4080029b60c755881020f32388eab102000a6e859d162040014db0b3a2c408012b9a06745881000572c0ce8b102000a6f855d162040014d90aba2c408002b3e0d74588100056641ae8b102004ae4815d162040015d100ba2c4080038bd5254588100053742ce6b102000a6d859cd62040095cd0339ac408002b9606735881000537c2ae6b102000a6c855cd620400155f08b9ac408002ab211735881000573c0ae6b102004ae4815cd62040015d700b9ac408002ba201735881000537428e6b102000a6d851cd620400155
  | 3 => 0x6b2020c0a3e8514d640400147d0bb92c8080028f61772590100051fc2ae4b202000a3c855c9640400153f06b92c808002a720d72590100255a40ae4b202000ab8805c96404001c5ea5292c8080028f60c52590102051f410a4b202000a3e85cc9640400147b0b992c808012ada0732590100055ac0e64b202000a3c858c9640400117f0e992c8080022f21d32590100051fc2a64b202000a3c854c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400147d0b382c8080028f61670590100345f43ea0b2020008bd87d41640400153d07a82c808002a760f50590100071da84a0b2020068be87cc1640400117b0f982c8080028fa1730590100051ec2e60b202000e1d538c1640400147d0a182c8080028f61430590100070ea9860b202004ab6810c1640400156b02182c80800317dd67558c1060d2ec3ceab182000a5e829d5630418d5b700baac608002b62017558c100062fc3aeab182000a5c825d563041838bee2baac608307175c57558c100072dc02eab182000e58805d563040018b8e0baac60830297a147558c100052f42ee8b182000a5d85dd1630418b5b700ba2c608002b62017458c100052f428e8b182000a5d851d16304001c3ea92a2c60800297a177258c100052ec2ee4b182000a5f855c963040014b90ab92c608002a7e117258c100054e422e4b1820c4ad7815c963040095a902b92c60830eb6e017258c100056c402e4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b182000e4f5294963040014bf0e292c6080029761c5258c102052f410a4b182000a5e85d0963040014bb0ba12c608012b5a074258c100056ac0e84b182000c5d759c163041855ab03382c60801637a1f5058c100046ec3ea0b182000a9e84d41630400153b09a82c60800396d425058c1002c6f43e80b1820008dd87d0163040014bd0ba02c608002976174058c100256b40880b182000ad58110163040834dd05bacc4081029ba0875988100043fc2ae9310200387c855d262040011bf06ba4c4080063720d74988100043fc2ae7310200387c855ce620400117f08b9cc40800a2f21173988100043f43ea7310200387c87d4e62040014dd05a9cc4080021f21d539881000536412a73102000c6f75d4a62040091db0f294c40800f1b9d6529881020537410a531020048ed8714a62040838db0e294c4080029b60c52988100053742e853102000a6d85d0a62040091db0e214c4080029ba17329881000536c2e6531020048ed878ca62040014d90b194c4080029be1532988100053642a653102000aaf844ca620400155908994c4080123b61c329881000537428653102000a6d850ca620400155d08194c408002ab610329881000536c1eeb3102000c6f759d662040018dd0e3acc4080029b60
  | 4 => 0x441970fd0dbaa40880030f19375481100062e31eea902200087e87d9520440970f90fb2a40880030f1d365481100062e39eca902204bc7471d95204409317d0dba240880030fd9774481100061e32ee89022000c9c63dd1204400117d0fb22408812a2f21f64481100061fbaec89022000c3c75d912044001938e7b22408812b2d1c764481106546f436e69022000c5f65dcd20440018b8cbb9a408800327d9373481100064e326e690220008de87d8d20440911b90fb1a408800317dd763481100062e3aec69022000c9f74d8d2044001938e9b1a4088123351c7634811000637baec49022000c6c75d89204400195ee9b1240880032b1d3624811000667b9ec49022000ccc73d8920440799c8e3b1240880031bdd46248110006363a8c49022000caf741892044001958e8312408800333dcc624811000666398c4902203bce47118920440018eecbb8a40880031d19771481100065bb26e29022000cb464dc520440019aec7b8a40880033518f714811000672316e2902204bc7676d96104409596cedb24208800b2d9d864841102466b3b6c7082203cce676d8a1044001cc8a431420880ef399d8628411000733b28c50822000e646518a1044001d4ec83142088003a9190628411000763b18c50822000ec46318a1044001ccf0a314208800399214628411000733a98c50822000e655318a1044001cc8c529420880030fdd274594100043f416e6b2820c187d879cd65040018bee739aca083269ee0173594100053c402e6b282000c5f835cd65040010f904b9aca080031ee0173594100063c402e6b2820c087e871cd65040010fd0f21aca080021f61e43594100043f43886b28200087d8710d65040018dee5392ca083229de0572594100253a40ae4b28200087d831c965040010fd0fa12ca080021f61f42594100043f43e64b28200087d87cc965040010f90f192ca080021fe1d32594100043e43a64b282000a3f844c9650400147908992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca0831e9d606705941003c3f43e80b28200087d87d0165040014bd07a02ca080029760f405941003c3f43e60b28200087d87cc1650400147d09982ca080028f61330594100062eb9c60b28200087e870c165040010fb0e182ca08003175cc30594100072c98060b2820048be87d51640400187eebaa2c8080122f21d54590100047c402e6b2020048be8790d640400147d0b21ac8080028f61643590100245e43a86b20200387e85dc964040010fb0bb92c8080030fdd675590100051f42ce6b202000a3d859cd640400157700b9ac808002ae20173590100051f428e6b202000a3d851cd640400147d05a9ac8083068f61653590100070fa9ca6b202000e1f8354d640400147904a9ac80830787cc5535901060f0e98aa
  | 5 => 0x80031b21c629491000637b98c52922000c6d7318a52440070fd0bbb484880021f617769091000c6f41eed21220008dd83dda42440011dd05bb484880021fe15769091001c3e42aed21220008df835da42440031b906bb4848800a3b61c629091001c3f42eeca12200087d85dd942440031bd07bb284880023760f765091001c3f42ceca12200087d859d942440031bd073b284880023760e76509100043fc2aeca12200387c855d942440011bf06bb284880063720d765091000477c12eca1220008f7815d942440011f700bb2848800e1f214765091000c6e418eca12200087e86dd5424406d878c9baa84880031718f75509100043f43ecaa12200087c87d9542440018b8e7b2a84880030fdd764509100061e3aec8a122000c9c73d9142440011bd0db9a848800317d9773509100062e32ee6a122000c9f64dcd4244179938c9b9a848800237a1f63509100046e43ec6a122000c5f75d8d42440018b8ebb1a848800a3ba1f625091000637baec4a122000c6c75d89424400199ee7b128488003331cf625091000637ba8c4a122000c6c75189424400199ee63128488003331cc62509100043f436eaa0a20b2c3c64dd541440018b8c7baa82882ce1fa1f65505105943e43ecaa0a2000c3f75d914144001878ebb22828800317dd763505100062e3aec6a0a2000c6f75d8941440018d8ebb1282880031bdd46250510006363a8c4a0a2000cd863dc141440019d0c5b8282880032ed9070505100066c318e0a0a2000ce8621c141440019d0c5386428800e1f21476485100043f436ea90a2000c3c64dd521440018b8c7baa42880021fa1f65485100043e43eca90a2000c3f75d912144001878ebb22428800317dd763485100062e3aec690a2000c6f75d8921440018d8ebb1242880031bdd46248510006363a8c490a2000cb864dc121440019b0c7b8242880032e19070485100066c318e090a2000ceb621c121440410f90cbac808825b0f19175901100062e31aeb202200087f87d9640440170fb0fb2c80880030f9d764901100061ebaec92022000c5e75d8e40440018baebb1c80880031b9d7629011000636baec52022000c6e7518a40440018daea314808812b2d1c764501101de72388c4a022000ce462dc540440779cce231640880033918971c811001c3e42ced102201a87c865d62044001878c8bac40880031718d75881100043fc3ecb102200b87d87d96204400187cebb2440880030f5d764881100062f3aec71022000c5d75d8e20440018dcebb1440880031b5d76288110006373a8c51022000c6d7518a20440070fd0bbb240880021f61776481100145f426ec90220008bd84dd920440031bd07bb240880023760f76481100043fc2aec902200387c855d9204400117f08bb2408800a2f21176481100046fc1aec90220018dc835d92
  | 6 => 0x727c1aa63122000a6e8514c62440014dd0b218c4880029b616431891000537428863122000a6d8510c62440775cd02218c488002b9604431891000537c2ae23122000a6c855c462440014dd0b988c4880029b617311891000726a9e623122000e4d534c462440015d700988c488002ba201311891000537c2ae03122000a6c855c0624400155f08b80c488002ab211701891000567c1ae03122000acc835c0624400155d09a80c488002ab61350189100056741ea03122000acd83d4062440775cd03a80c488002b9607501891000573c0aa0312203bae48154062440014dd0ba00c4880029b61740189100056741e803122000acd83d0062440775cd03a00c488002b960740189100053742e603122000a6d85cc0624400155d09980c488002ab61330189101dd7340e603122000ae581cc06244001c9aa7180c488002b9e0530189101dd7240a603122000a6e850c062440014db0a180c4880039354c301891000537c2a203122000a6c85440624400155f08880c488002ab211101891000567c1a203122000acc83440624406d47d09bb4a4880028f61376949101ad2f41eed2922000a5d83dda52440014dd05bb4a4880031718e769491000637394ed292200087f839da52440010fb073b4a4880031b20a76949100051fc22ed2922036a3c845da52440014bf06bb4a4880d69720d76949100043f430ed2922000c5c631da52440014dd043b4a4880031b9c876949100043fc18ed292200087d831da52440010fd043b4a4880031ba0876949101b51f436c92922000c3e76d925244001878edb24a4880038718f64949100061fb9ec92922000c3d73d92524400187ce5b24a4880038b9cb64949100043fc3ac9292200087c8759252440014bf06b24a4880d69720d649491000537c12c92922000a6c82592524400147d0c324a4880030f9d864949100061e3b0c92922000e1c63192524406b4bd0db1ca488003179db63949100062e3b6c72922000e1f64d8e5244001c38c9b1ca48800317e1f63949100062e43ec729220ccc5e72d8e5244001c9ce5b1ca4880021f61f629491000637396c52922000c6e76d8a52440018d8edb14a4880038bd93629491000716326c52922000e4f63d8a5244001c98c7b14a4880029b61f629491000636c3ec52922000c6f73d8a52440018dae7b14a48800e1f61e62949101b51f424c52922000a3d8498a524406b4bd07314a4880029760e629491000537414c5292200087f8758a524400147f08b14a4880da8f21162949100052fc1ac52922035a5c8358a52440014ef02b14a48800e1fe1c62949100043e438c52922000c6e7218a52440014dd0c314a4880031b9d8629491000717b20c52922000e2c6418a5244001c9ec6314a4880039318c629491001d37c38c52922000c6f8718a52440074db0e314a48
  | 7 => 0x6e85cc862440014db0b990c4880063b61e32189100053642c643122000a6f854c862440014d90a990c488002abe113218910005564226431220008ed870c862440014dd0a190c4880029b614321891000557420643122000aad840c862440015cb02190c4880029ba16761891000536c2cec3122000c6e859d862440018db0b3b0c4880029ba187518910006373b0ea3122000c6e76d9462440014db07b28c4880023b61e651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000c6e7619462440014db06328c4880032b9db641891000717b2ec83122000e2c65d906244001c5eebb20c4880038b1d7641891000476c3cc83122000a6e8599062440014db0b320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400195cec320c4880038bd94641891000716328c83122000e2f751906244001c58ea320c48833baac40641891067754080c83122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e8c64d8c6244001c9f0bb18c48800393217631891000727baec63122000e4c75d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c4880023be1d631891000537c2ac63122000a6c8558c624400155f08b18c488002ab211631891000537428c63122000a6d8518c624400199cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c48800393a14631891000726c28c63122000e4f7518c6244001c98ea318c488337b2c40631891066f64080c63122000a6e86d4c62440014d90da98c4880031b9db531891000717b26a63122000e2c64d4c6244001c9ec7a98c4880039318f531891000537432a63122000a6c8654c62440018dceca98c4880038bd91531891000716322a63122000e4f6354c6244001c98c6a98c4880029b60f751891000637bacea3122000aea801d462440775d3003a8c4880031ba1c751891000536c18ea3122000e6a801d46244001cd3003a8c4880029ba16741891000536c2ce83122000a6f855d062440014d90aba0c488002b3e0d74189100056641ae83122000aea801d062440775d3003a0c4880038bd5254189100053742ce63122000a6d859cc62440014df0ab98c4880029b215731891000557c22e63122000aac845cc62440014dd0a398c4880029b614731891000557420e63122000aad841cc62440775cd02398c488002b9604731891000575400e6312203bae9801cc62440014dd0fa98c4880029b21f531891000536c2ca63122000e4f5394c62440014dd0ea98c4880029b21d53189100
  | 8 => 0xe7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc645891000c6f436e6b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b1220008de87d8d62440018beebb1ac488003171d763589100064fba6c6b122000c9c74d8d62440011bd0e31ac48800317dd463589100062e3a8c6b122000c9f7418d6244001938e831ac4880021f60f75589100045fc22eab1220028bc845d562440011bf06baac4880063720d755891000477c12eab1220008f7815d5624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100043fc2ae6b12200387c855cd624400117f08b9ac48800a2f211735891000477c12e6b1220008f7815cd62440011f700b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f535891001c3e43ea6b122000c3f74d4d62441a3878e9a9ac48800317dcf535891000e2e39ea6b12200087e8754d62440010f90ea9ac4880030fdd153589106861e3a2a6b122000c5f7354d62440038b8e6a9ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000c3f741496244113878e8292c48800317dcc525891067e2e398a4b122000c7775dc562440018e8ebb8ac4880032ddd371589100065a3a6e2b122000cd773dc562440019a8e7b8ac4880031dd4f71589100063aa9ee2b122000c7452dc56244001970e9b82c488003361cf705891001c3f42cec312200087d859d86244001878ebb20c4880030f1d464189100062e3aec63122000c5c7518c62440011df0eb10c4880029be1562189100053642ac43122000aaf84588624400155908b10c488002b3e0d62189100056641ac43122000e2f641486244001c58c8290c48800393d8c521891000726318a43122000a6e82dd462440014dd043a8c4880021fe15741891001c3e42ae831220008df835d062440031b906ba0c4880021fe15731891001c3e42ae631220008bf845cc624400517908b98c4880021fa1f531891001c3e43ea63122000a6e82d4c62440010f90ea98c4880029b20953189100053742ce43122000a6d859c8624400155d09390c488002ab61272189100056741ce43122000acd839c862440018deeba90c48800e3b61e521891001e373aca431220008ed8714862440015d300290c4880031b61c521891000536c18a43122000e6a801486244001cd300290c4880029ba17421891000536c2e843122000a
  | 9 => 0x63d891000726ba8c7b122000a6e86d4f62440014d90da9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000a6d839d762440018df0ebaec4880029be0d75d891000636ba8ebb122000a6e85dd362440014db0bba6c488002b3a0f74d891000566c1ee9b122000a6e851d362440014db0a3a6c4880038bd5254d89100053742ee7b122000a6d85dcf624400155d09b9ec488002ab61373d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000537428e7b122000a6d851cf62440014df0fa9ec4880029b61f53d891000727a9ca7b122000a6f8754f62440014db0ea9ec48800393e0d53d89100053742c87b122000a6d8590f62440014dd0a21ec4880029b61443d89100053742ee3b122000a6d85dc762440014dd0b98ec4880029b61731d891000726a9e63b122000e4d534c7624400155d09a86c488002ab61350d89100056741ea1b122000acd83d4362440014dd0ba06c4880029b61740d89100056741e81b122000acd83d0362440014dd0b986c4880029b61730d89100055742661b122000aad84cc36244001c9aa7186c4880029ba1430d891000536c2861b122000e4d530c3624400187ce9b2cc488003179cf65989100061f3a0cb3122000c5e73196624400187ecaba4c4880030f19574989100061f3aec93122000c3d75d92624400193ce7b24c4880030f9d464989100061eba8c93122000c9e7319262440018becab9cc4880031719573989100064fb22e73122000c9c645ce62440018bcebb1cc488003175d763989100064f3a6c73122000c9d74d8e62440018bcea31cc488003175d463989100064f3a0c73122000c9d7418e62440018dcebb14c4880031b5d76298910006573a6c53122000cad74d8a624400199ce7b14c488003335cf62989100145f426eb31220008bd84dd662440031bd07bacc4880023760f75989100043fc1aeb3122000c3e759d2624400187aeb3a4c4880030f9d574989100061ebaae9312200387e85dce62440010fb0bb9cc48800a2fa1373989100045ec26e73122000c5e759ce62440018baeb39cc488003279d273989100064eba4e73122000c5e755ce62440018baeab9cc488003279d173989100064eba2e73122000c5e855ce62440018bb0ab9cc48800e1fe1f53989100043ec3ea731220d1c3e74d4e624400187ae9a9cc488007179cf53989100062eb9ea7312200087f8754e62440010fb0ea9cc4883430f9d153989100061eba2a73122001c5e7354e62440018bae6a9cc4882270f9d052989100061eba0a531220cfc5e7314a62440018bae6294c48800e1fa1b75589100043f43ecab122000c3c74d9562440018b8
  | 10 => 0xb1a2000c5e70dd763440018b8e1baec68800297a1675d8d100062eba8ebb1a2000a5e871d763440018bd0e3aec68800297a0875d8d100052f42ce9b1a2000a5d859d363440014bf0aba6c6880029721574d8d100070faa4a9b1a2000a5e85dcb63440014bb0bb96c688002a7a1372d8d100054ec26e5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000a5f855cb63440014b90ab96c68800393d4a52d8d100052f438a5b1a2000a5c8714b634408f4bd04296c68800297a1742d8d100052ec2e85b1a2000c5f75dc763440755b501b8ec68812237a1f50d8d100046ec3ea1b1a2000a9e84d43634400153b09a86c68812237a1f40d8d100046ec3e81b1a2000a5e85d0363440014bb0ba06c68802e1f61f65d891000537416cbb122000a6e82197624400187cebb26c4880030f5d764d89100061f3a8c9b122000c3d7519362440018bcebb1ec488003175d763d89100062f3a8c7b122000c5d7518f6244001c5ec8296c4880038b19052d891000727b18a5b122000e4c6314b62440010ff06baec4880031be0975d891001c3f42ee7b12200087d85dcf624400517d09b9ec4880022f61373d891001c3fc3ea7b12200087d87d4f62440014dd05a9ec4880021fe1d53d89100043ec3aa7b122000a6c8254f62440018daeba96c48800f1b9d652d891001e363aca5b1220038ef8754b62440018daea296c4880029b61c52d891000636c38a5b122000a6d8314b62440014dd0ba16c4880029b61742d89100053742e65b122000a6d85ccb62440014d90b196c4880063be1d32d891000537c2a65b122000a6c854cb624400155f08996c488002ab21132d89100053742865b122000a6d850cb624400155d08196c488002ab61032d891000536c3ecbb122000a6d83d97624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc8359762440014db0632ec4880038bd9764d89100071632ec9b122000e2e75d936244001c5aebb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000e2e751936244001c5aea326c48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec48800393e1763d89100072642ec7b122000e4e75d8f6244001c9aebb1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec4880029ba1463d891000536c28c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4e8518f6244001c9b0a31ec488003939d4
  | 11 => 0x440011f700b9ac88800237a1c73591100062fba8e6b222000c5c751cd644400193ee839ac8880021fa1f535911001c3e43ea6b222000c5f73d4d64440038b8e7a9ac8880021fa1d53591100043e43aa6b222000c5f7354d64440038b8e6a9ac88800e1fa1772591100043ec2ee4b222000c6f75dc964440018d8ebb92c8880032bdd3725911000667b9ee4b222000ccc73dc964440018dd0bb92c8880031b617725911000637a9ee4b222000c6d53dc964440018deea392c8880031b1d4725911000657ba0e4b222000ccf731c96444001998e6392c8880031be14725911000636428e4b222000c6f531c964440018daa6392c8880021fa1c525911001c3e438a4b222000c5f73149644419f8b8e6292c8880031bdc8525911000636390a4b222000ce472dc564440019b0e7b82c8880033a1cb70591100061f3b6ca3222000a3d83d94644400147d05b28c8880022f61e65191100051f42cca3222000a9e83994644400153b07328c888002aba0a651911000556c14ca32220008bf87594644400153f06b28c888002a720d651911000557c12ca3222000aac82594644400147d0c328c8880030f9d865191100051ec18ca3222000a3e82194644400117b0f318c8880028fa1663191100051ec2cc63222000aae8298c644400155b05318c8880022fe1d63191100051fc2ac63222000a3c8558c644400155f04b18c888002ab20963191100055dc02c63222000a3e8518c644400147b0a318c88800387d9463191100070e328c63222000e1e8518c6444001c3b0a318c88834ba6c4063191106974c080c63222000a3e86d4c64440014790da98c8880030f9db53191100070fb1ea63222000e1c63d4c644400147d0ca98c8880028f21953191100061f3b2a63222000e1f6354c6444001c38c6a98c8880028fa1852191100070e318a43222000a5e86dd763440018bcedbaec68800297a1875d8d100062f3b0ebb1a2000c5e76d9763440014bd05b2ec6880023761e65d8d100052f42ccbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a20008df87597634400153f08b2ec688002a721165d8d1000567c12cbb1a2000acc8259763440014bd0c32ec688003179d865d8d100052f410cbb1a2000c9e76d936344001c3ecbb26c6880038719764d8d100070fbaec9b1a2000e1c75d9363440011bb0f326c68800297a1664d8d100052ec2cc9b1a2000a9e84993634400159d05326c688002b360a64d8d100046fc3ac9b1a2000a5f8559363440014b90ab26c688002b3e0964d8d1000566412c9b1a2000a9e86193634400193cec326c68800387d9464d8d100070e328c9b1a2000e1f751936344001c38ea326c68800297a1852d8d1067e2f3b0a5b1a2000e1f6414b6344001c38c8296c68800297a0b75d8d100062eb8eeb
  | 12 => 0x28f61330d95100043f43861b2a200b87d870c3654400187aebaa6c88800e2fe1d54d91100051f42c87b222000a3d8590f644400317f0ea1ec8880021fe1572d911001c3e42ae5b222000a3d83d97644400147d05b2ec888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec888002a7e0d65d91100054e41acbb222000aaf82597644400155904b2ec8880028f60c65d91100051f410cbb222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b222000a3f8558f64440014790ab1ec888002abe0963d911000556412c7b222000a3e8518f644400147b0a31ec88800387d9463d91100070e328c7b222000e1e8518f6444001c3b0a31ec8880028fa1b53d91100051e436a7b2220d1c3e76d4f6444001c3ec7a9ec8880038718f53d91100051f432a7b222000a3c8654f64441a187ceca9ec88800387d8d53d91100070e31aa7b222000a3e8614b644411387cec296c8880038718c52d91100061eba8ebb222000a3e859cf644400147b0b39ec8880028fa1473d91100051ec28e7b222000a3e82d4f6444001c3ea729ec88800387e0d53d91100051e412a7b222000a3e85dcb644400147b0bb96c888002a7a0f72d91100054ec1ee5b222000a3f855cb64440014790ab96c8880038bd4a52d91100051ec18a5b222000a3e85ccb644400147b0b996c8880028f21632d91100045fc3a65b2220008bc874cb644400147f0a996c8880028f21532d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100051f42ee3b222000a3d85dc7644400147d0b98ec8880028f61731d91100070ea9e63b222000e1d534c7644400147f0ab86c8880028f21570d91100054fc1ae1b222000a9c835c3644409517d0fa86c8880022f61f50d91100054f41ea1b222000a9d83d43644409517d0f986c8880022f61f30d91100051f42e61b222000a3d85cc36444001c3aa7186c8880028fa1430d91100051ec2861b222000e1d530c36444001878c9baac8880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c9c64dcd64440018beea31ac888003171d4635911000637b2ee4b222000c6c65dc96444001958c9b92c8880033318f725911000637b28e4b222000c6c651c96444001958c8392c8880033318c725911001c3f43eeab22200087d83dd564440010fd05baac8880022fe1175591100046fc1aeab2220018dc835d564440011df04baac8880023b20975591100043f438eab222000c3f75dd16444001878ebba2c88800637a1f73591100062fbaee6b222000c5c75dcd644400193ee9b9ac88800317e1773591100062e42ee6b22200087f855cd64440070f90ab9ac8880022fe11735911000477c12e6b2220008ec825cd64
  | 13 => 0x62e42ee6b14200087f855cd62840070f90ab9ac5080022fe117358a100145e422e6b1420008de871cd62840018beea39ac508003171d47358a100064fba0e6b142000c9c741cd62840010fd0fa9ac50800e1f21f5358a100061fba6a6b1420d1c3c74d4d62840018bee7a9ac508007171cf5358a100043f43aa6b14200087c8754d628400187ee8a9ac5083430f1d15358a100062fb9aa6b142001c5c7354d62840014d904a9ac5080030fdd05258a1044e1e3a0a4b142000c5f73149628419f8b8e6292c5080031ddd77158a100063a3aee2b142000cb774dc56284001968e9b8ac50800335dcf7158a100066a39ee2b1420008ef87588628400517d09ba8c5080022f6137518a1000537416ed2942000a3f845da528406d47908bb4a50800297e0d7694a101ad2e41aed2942036a3e841da528400147b083b4a5080029ba087694a100043f43ec9294200087d87d9252840010fb0fb14a5080021fe1d6294a100051fc22c52942036a3c8458a52840014bf06b14a5080d69720d6294a100043fc2aed214200387c855da42840011bf06bb485080063720d7690a1001c3f428ed214200087d851da42840070fd0b3b285080021f6167650a1000c6f41ceca1420008dd839d942840010ff0abb2850800e1f2157650a100045fc22eca1420008df835d942840031b906bb285080f23be1d62c861000732b14a590c203b8ee8798921840011eb0fb1043080027961f62086101ddf1406c410c203cbe280188218400917d0fb2281080023ba1c62482101de72388c490420009e687c8520840011df0eb1041080027920976c42100052f41cc9b2a2000a5d8399365440014dd05326ca880029b60a64d95100043f436e7b2a200387f87d8f65440018bae7b1eca880021f61e63d95100051f424c7b2a2000a3d8498f65440014dd0531eca880029b60a63d95100043fc3ac7b2a2000a3f8458f654400147908b1eca880029be0963d951000536412c7b2a200b87d8718f65440018bae631eca880031761c63d95100062e31ce5b2a2000c3d741d365440010fd05b9eca880021f61e73d95100062fc1ae7b2a200087c825cf65440010fd0e39eca88003175cc73d95100043f43c87b2a200087d8790f65440010fd0e21eca880021f61c43d95100043ec1ce5b2a2000c6d721cb65440010fd0fa16ca880021f61f42d95100043f43e65b2a200087d87ccb65440010ff0f196ca880021fe1d32d95100043e43a65b2a2000a3f844cb654400147908996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880e29ea0371d95100043f43e63b2a200087d87cc765440018bee798eca8800317dcd31d951025c3f43e81b2a200087d87d0365440014bd07a06ca880029760f40d951025c3f43e61b2a200087d87cc3654400147d09986ca88
  | 14 => 0x7531c52008001acaa638a40100ee3b21d61480201de7238ac29004000c7875dd920080019b0e7bb240100031ed4f76480200063ca9eec9004000cea52dd920080019d2a5bb240100031e14b76480200063dbb6ea9004055b6882dd52008001976edba240100032edd874480200066dbb6e69004000b6985dc920081ab2f50f29240100031edda5248020005b543ca490040d5d6a879492008001ad6ed29240100039adda524802000635bb4a49004000f2b749492008001e50e92924010003d2dce52480206a7a439ca49004000cf376dc52008001ec4a5b8a40100033cdd87148020006d83a0e29004000dd0731c52008001bc6e438a4010003d8948714802001c3f43eeab26200087d83dd564c40010fd05baac9882c61fa1c75593100245e43aa8b26200087f855cd64c40070f90ab9ac9880023be09735931000476412e6b26200087e87d4d64c40070f90fa9ac9880021fa1d53593100043e43aa6b2620048bc8750d64c40070fd0bb92c9880021f61772593100043f438a4b26200387c8714964c400517d09bacc5880022f6137598b1001c3f43eeab16200087d83dd562c40810fd0e3aac5880021fe157358b1001c3e42ae6b1620008bf845cd62c400517908b9ac5880021fa1f5358b1001c3e43ea6b16200087e8754d62c40010f90ea9ac5881021fa1c5258b101b51f426ed2962000a3d84dda52c40014dd05bb4a5880021fe1d6494b100043e43ac9296204187f8758a52c40070fd0bbb485880021f6177690b100245fc3ac9216200087f855d942c40070f90abb2858800237e0d7650b1000c6e41aeca16203b8ef8758b20c40791dd0f3124188013391c662483100267238ac4906200087d879d764840070ff0ebaec9080021fe0d75d92100043e412ebb2420038bf8755364840070fd0bb9ec9080021f61773d921000477416e7b2420008ed82dcf64840070ff0fa9ec9080021f61f53d92100043fc3aa7b24200087d8754f648400317f0ea1ec9080021fe1572d921001c3e42ae5b24200387f8714b64840010fb0e296c90834f3c5c670d92100062fb9aa6b242001c5c7354d64840070fd0bb92c9080021f61772592100043fc1aebb14200387e85dcf62840010fb0bb9ec50800a2fa1373d8a100045ec26e7b14200387f87d4f62840010fb0fa9ec5080021fe1d53d8a100043ec3aa7b14200087f855d262840070f90aba4c508007179cd5398a100062eb9aa73142000a6c8254e62840070fd0fbaac5080021f60f7558a100045fc22eab1420028bc845d562840011bf06baac5080063720d7558a100043f438eab1420028be87dd1628400187eebba2c5080030f1d77458a100061fba8e8b142000c3c751d162840031bd0fb9ac50800317dd77358a100062e3aee6b142000c9f74dcd6284001938e9b9ac50800317e177358a1000
  | 15 => 0x830a4290003b1d8c614852000762318c290a4000d6b751c12148001bc6e238242900821f21975901204b61e322eb2024000c5c635d640480012d904bac80900021fe1f65901200c43ec3ecb2024000c3e75d92404800187aebb248090003179d763901200062ebaec72024000c7675d8640480018eaebb0c80900031d9d461901200063aba8c32024000caf641c940480019cee430a8090003391c861501203bd3d434a59024000eb0641872048001da0c630e409006a1f21975881200061e322eb1024000c5c635d620480310fb0fb2c40900030f9d764881200061ebaec91024000c5e75d8e20480018baebb1c40900031d9d761881200063abaec31024000c767518620480018eaea30c409000399948618812000732290c31024018c6e76d96204802f95cedb24409000b2b9d864881200b6673b6c7102403c8ec865c620480799c8c2b8c409000399d94618812000732328c31024000ea7641862048001d48c830c4090003b1d8c618812000762318c3102403cce5871862048001cccea30c4090003995d4618812000733a98c31024000e65531862048001cd6cbb0440900021f61e75d902001c3fc3aebb20400087f835d764080070fd0bb9ec8100021f61773d902000477416e7b20400387f87d4f64080010fb0fa9ec8100021fe1d53d90200043ec3aa7b20400387f8714b64080010fb0e296c8100028fa1774590200045f43ea8b204000c3f75d5164080018bee6a9ac810007171cd535902000c5e43a86b204001c9c7350d64080010fd0fb24a41000e1f61f64948202ae3c3b2e1290400087d83dd561080010ff0ab9ac21000e1f21573584200045fc22e6b0840028bc845cd61080010fd0fa9ac21000e1f21f53584200043f43aa6b08400087c8754d61080550fd0f292c2100021fa1c525842000c7a43a62b084000e55534c561080099acc2b98c2100023de1d61184200066ab9ac2308400087f855da41080070f90abb482100021fe15765042001c3e42aeca0840008df835d941080031b906bb282100030f1d5645042000656b20e4a084000c6c525da21080018daed29442100031bd4d768842000636a9aed1084000d6a525c02108077bc020b8042100030f9d5649002000656b24e5200403b8ef8758720080779cce2b0e401006b1e5d975880206bcbcc3ca510040d6e6a6294a20080018d8a5bb240100031bdda5248020006b3290e29004000d64521c520080018d8ebbb24010003331cf764802000637a9eec9004000c6d53dd920080019d4a1bb240100033a543764802000637bb6ea9004000caf76dd1200800195eec3a2401000333ddb734802000673bb6e29004000ce7761c52008001aceea38a4010003591d47148020006d3ba0e29004000da4741c52008001b8ee638a4010003711cc71480201de72c30e29004000d6
  | 16 => 0x1852000573416a030a4000ae582d406148001ce6a1280c290002b9e09501852000572412a030a4000a7685d0061480014eb0ba00c290002b5a0f40185200056ac1e8030a4000ae682d0061480015cb05a00c2900029da1730185200053ac2e6030a4000ab684cc0614800156b09980c290002b9a0b301852000572c166030a4000e55538c061480015cf04980c290002b920930185200053b4286030a4000a75850c06148001caaa6180c290003b44c030185200053bc2a4030a4000a7485480614800156f08900c290002ad21120185200056bc1a4030a4000ad48348061480010ff0abb4829000e1f21576905200046fc1aed20a40018dc835da41480091e902bb482900032bd9272905200267230ce520a4004ce4615ca41480070fd0bbb282900021f617765052000c6f41eeca0a40008dd83dd941480070fd0b3b282900021f616765052001c3e428eca0a400087e86dd54148165878c9baa82900031718f7550520004b7416eaa0a40b1c7461dd541480010fd0fb2a82900021f21f65505200061fbaec8a0a4000c3c75d9141480018beebb1a8290003171d763505200147b43ec2a0a4000c7775d8541480018e8ebb0a82900031b14a76c8520006373b4a590a4040e646194b21480018d8cb3b642900033318e76c852000637a9ced90a4000c6d539db21480019cf033b642900031b9db65c8520006573b6c990a4000cae76193214800199cedb1e4290003399db61c852000733b28c390a4000e64651872148001d4ec830e4290003a919061c852000763b18c390a4000ec46318721480799c8c338642900021f21975885200061e322eb10a4000c5c635d621480098e8c2bac42900021f61f65885200061f3a6cb10a4000c5e73d9621480011790cba442900030fd9574885200061e32ae910a4000c9c635d22148009968c2ba442900022f61f64885200061f3aec910a4000c3d75d92214800193ce7b2442900023721973885200062fb2ae710a4000c5c655ce214800193ec8b9c42900032719173885200266a30ae710a40008dd87d8e21480018bcebb1c4290003175d763885200064f3a6c710a4000c9d74d8e21480018ecebb0c42900031d5d761885200065b3a6c310a4000cb574d8621480019ace7b0c4290003355cf61885200267830ce110a400087e86dd52148001878c9baa42900031718f75485202063a30eea90a404187e87d95214800187eebb2242900030f1d764485200062fbaec690a4000c5c75d8d2148081cc8c329242900031ddd761485200063a3aec290a4000cb864dc121480019b0c7b8242900032e19070485200066c318e090a4000d6a521c121480019e6c238242901031b1db75485202073230eea90a4000ae686dc521480095cd0db0a429000399d94614852000732328c290a4000ea7641852148001d48c
  | 17 => 0xa4000ad58399461480011ef0eb28c290002ade1165185200055a422ca30a4000ad78359461480015a906b28c2900031d9d865185200053ac18ca30a4000cb676d906148001c6ecbb20c2900038d19764185200047ac3cc830a4000a768599061480014eb0b320c290002b5a0e64185200056ac1cc830a40008f78759061480014ef0ab20c2900029d21564185200056bc1ac830a4000ad483590614800196cec320c2900038dd9464185200071a328c830a4000cd676d8c6148001caecbb18c2900039519763185200074bb26c630a4000e9464d8c6148001caf0bb18c2900039521763185200047ac3cc630a4000a768598c61480014eb0b318c290002ada1263185200055ac24c630a40008f78758c61480014ef0ab18c2900029d21563185200055bc22c630a4000ab48458c61480014ed0a318c2900029d61463185200066b3b0c630a4000e576518c6148001ca8ca318c290003a5d9063185200074a320c630a4000e568518c6148001cab0a318c2900029da1b53185200053a436a630a4000e3764d4c6148001c68c9a98c29000395d8f53185200072a31ea630a4000a768654c61480014e90ca98c2900038dd9153185200071a322a630a4000e576354c6148001ca8c6a98c290002d9209531852000733b2ae430a4000e64655c86148001d4ec8b90c290003a9191721852000763b1ae430a4000ec4635c861480014ed0d290c2900038dd9252185200071a324a430a4000e57639486148001ca8c7290c2900029da1852185200071bb20a430a4000e34641486148001caec6290c2900039518c52185200071baa4a830a4000ae68295061480015cb052a0c2900029da0b531852060733396a630a4000e575394c61480015cf04a98c290002b920953185200072bc1aa630a40c1e567354c6148183caae6a98c29000399e0953185200053a412a630a4000e648254c61480014c904a98c290307999c953185200053b42c8630a4000a758590c61480015cf04a18c290002b920943185200053b4288630a4000a758510c61480015cd04218c290002b9608431852000733a94a430a4000a758394861480014eb06290c29000399a08521852020f33390a430a4000a7685d0861480014eb0ba10c2900039914a42185200053bc2a8430a4000a748550861480015af06a10c290002b520d4218520007322928430a4000af38050861480015e100a10c290003a950842185200053b42e6430a4000a7585cc86148001cc8a5990c2900029de1632185200053a42c6430a4000a77854c861480014e90a990c290002ade1132185200055a4226430a4000af3804c861480015e100990c2900029da1432185200053ac286430a4000ab6840c8614800156b08190c2900039914832185200055b426a030a4000ab584d4061480015ad07a80c290002b560f5
  | 18 => 0x80014eb0b39ec290002ada1273d85200055ac24e7b0a4000a76851cf61480014eb0a39ec2900029da0b53d85200072ba9ca7b0a4000e578354f6148001caee6a9ec290003951cd53d85200053a412a7b0a4000a768590f61480014eb0b21ec2900029da1443d85200053ac2887b0a4000a7685dcb61480014eb0bb96c29000399d4a52d85200053ac1ca5b0a4000a758314b6148001ccd04296c2900029da1742d85200053ac2e85b0a4000a778550b61480014e90aa16c290002b5e0d42d85200056a41a85b0a4000a7685ccb61480014eb0b996c2900029de1632d85200053a42c65b0a4000a77854cb61480014e90a996c290002ade1132d85200055a42265b0a4000a76850cb61480014eb0a196c290002ada1032d85200055ac2065b0a4000a7685dc361480014eb0bb86c290002ada1370d85200055ac26e1b0a4000ad683dc361480015ab07b86c290002ada1350d85200055ac26a1b0a4000ad683d4361480015ab07a86c2900029da1740d85200053ac2e81b0a4000ad683d0361480015ab07a06c2900029da1730d85200053ac2e61b0a4000ab684cc3614800156b09986c2900039554e30d85200053b42861b0a4000a75850c36148001caaa6186c2900131d18575985200061f3a6cb30a4000c5e73d96614800187ce832cc290003179cc65985200061fb2ae930a4000c3c655d26148009968c2ba4c2900030f9d764985200061ebaec930a4000c9e73d92614800187cea324c2900030f5d464985200064f398c930a4000c5f655ce61480018b8cab9cc29000327d9173985200064e322e730a4004cd4615ce61480018bcebb1cc290003175d763985200064f3a6c730a4000c9d74d8e61480018bcea31cc290003175d463985200064f3a0c730a4000c9d7418e61480018ecebb0cc2900031d5d761985200065b3a6c330a4000cb574d8661480019ace7b0cc290003355cf619852001c3f436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a40008be87d91614800187eebb22c2900030f1d764585200064e39ec8b0a40008be87191614800187eea322c2900030f1d464585200064e398c8b0a40018de86dcd61480018becbb9ac2900031719773585200064fb26e6b0a4000c9c64dcd61480011bd0fb1ac29000317dd763585200062e3aec6b0a4000c9f74d8d6148001938e9b1ac29000237a1c63585200062fba8c6b0a4000c5c7518d614800193ee831ac290003271d063585200047bc3ac230a4000a778558461480014e90ab08c290002ade1161185200055a422c230a4000ad78358461480015a906b08c2900031d9db65185200053ac1eca30a40008f587994614800156d09328c290002ad61265185200056b41cca3
  | 19 => 0x30fdcf64949200061eb9ec92924000c3e72d925248001c5ce5b24a4900021fe1d64949200052fc1ac92924035a5c8359252480014ef02b24a4901029d20564949200051f430c92924000c3e761925248001c38c6324a4900d697a1b63949200062f3b6c72924000e1f64d8e5248001c38c9b1ca49000317e1f63949203b62e43ec729240d9c5e72d8e5248001c9ce5b1ca4900021fa1b75509201b61e326eaa124000c5c63dd542481130fd0fb2a84900da1f21f65509200062e39ecaa124000e2c42d95424800187eebb2284900030f1d764509200064e39ec8a1240008de86dcd42480018becbb9a84900031719773509200064fb26e6a1240bcc9c64dcd42481b11bd0fb1a84902f23721f63509200062fbaec6a124000c5c75d8d4248001976c8382849000317dcd53d852000e2e39aa7b0a40038f787547614800156d0828ec290002ad61051d85200056b418a3b0a4000ad58314761480014ed0a20ec2900029d61441d85200056b41883b0a4000ad58310761480014ed0b98ec2900029d61731d85200072aa9e63b0a40018f7874c76148001caaa698ec2900029da1431d85200053ac2863b0a4000ab6840c7614800156b0818ec2900029d60f65d85200055b424cbb0a4000ab58499761480015ad0732ec290002b560e65d85200055bc22cbb0a4000ab48459761480015af06b2ec290002b520d65d85200053ac18cbb0a4000e3765d936148001c68cbb26c2900029da1664d85200053ac2cc9b0a4000ad68399361480015ab07326c2900029de1564d85200053a42ac9b0a4000ad78359361480015a906b26c2900038dd9464d85200071a328c9b0a4000e5765d8f6148001ca8cbb1ec290003a5d9363d85200074a326c7b0a4000e5785d8f6148001ca90bb1ec2900029da1663d85200053ac2cc7b0a4000ab68498f614800156b0931ec2900029de1563d85200053a42ac7b0a4000ab78458f614800156908b1ec2900029da1463d85200053ac28c7b0a4000e576518f6148001ca8ca31ec290003a5d9063d85200074a320c7b0a4000e568518f6148001cab0a31ec2900029da1b53d85200053a436a7b0a4000e3764d4f6148001c68c9a9ec29000395d8f53d85200072a31ea7b0a4000a768654f61480014e90ca9ec2900038dd9153d85200071a322a7b0a4000e576354f6148001ca8c6a9ec290002d920953d85200053b434a5b0a4000e376494b6148001c68c9296c29000395d8e52d85200072a31ca5b0a4000a768614b6148001c6ec8296c2900038d19052d85200072bb18a5b0a4000e546314b614800156d093aec290002ad61275d85200056b41cebb0a4000ad5839d761480014ed0bba6c2900029d61774d85200053b42ce9b0a4000a75859d361480015ad073a6c290002b560e74d85200071baa4a9b0a4000a76859cf614
  | 20 => 0x5ec3cc63224000a3e8598c644800147b0b318c890002ada0663191200055ac0cc632240008bf8758c644800147f0ab18c8900028f21563191200055bc0ac63224000ab48158c644800147d0a318c8900028f61463191200070fb28c63224000e1c6518c6448001c3d0a318c8900038761463191200051f436a63224000a3c86d4c644800187ceda98c89000387d8f53191200070e31ea63224000a3e8654c64480014790ca98c8900030f9d953191200070fb1aa63224000e1c6354c644800165904a98c8900028fa1852191200070e318a43224000a5e86dd763480018bcedbaec690366d3a0b75d8d200052f430ebb1a4000c5e761d763480018bcedb2ec6900023761e65d8d200052f42ccbb1a4000a9e84997634800153b0932ec690002b5a0665d8d200056ac0ccbb1a40008df87597634800153f08b2ec690002a721165d8d200056bc0acbb1a4000ad48159763480014bd0c32ec690003179d865d8d200064f3b6c9b1a4000e1f65d936348001c38cbb26c69000387dd764d8d200070e3aec9b1a40008dd8799363480014bd0b326c6900029761664d8d200054f424c9b1a4000ad68199363480015ab03326c69000237e1d64d8d200052fc2ac9b1a4000a5c8559363480015af02b26c690002b520564d8d200054f430c9b1a4000c9e761936348001c3eca326c6900038719464d8d200070fba8c9b1a4000e1c7519363480014bd0c296c69033f179d852d8d200070fb20a5b1a4000e1c6414b63481b359d05baec690002b360b75d8d206cd2f416ebb1a4000e4e82dd763481b349d05baec6900039360b75d8d200062f386ebb1a4000c5c70dd763480014bd0b3aec690003175d475d8d200052f438ebb1a4000c5e871d763480ed4bd043aec69036eb3a0b74d8d2000566c16e9b1a4000a5e859d363480014bb0b3a6c69000297e1574d8d200052e42ae9b1a4000e1f5495363480014bd0bb96c6900029761772d8d200054f426e5b1a4000a9d84dcb63480b15b501b96c69000393d4a52d8d200052f438a5b1a40d9a5c8714b63480ed4bd04296c69036b939c852d8d206d726b90a5b1a4000a5e85d0b63480014bb0ba16c69000317dd771d8d200052f42ce3b1a4000a5d859c7634800153d0938ec690002a761271d8d200052fc2ae3b1a4000a5c855c763480018beeab8ec6901b6b3a0871d8d2000566c10e3b1a40008de8714763480011bb0e28ec690002a7a1051d8d200054ec20a3b1a40008de8710763480011bb0e20ec69000297a1441d8d200052ec2883b1a4058ace82dc363480011bd0fa86c6900023761f50d8d200054f426a1b1a4000a9d84d436348001cb6a1286c69000237a1f40d8d200046ec3e81b1a4000a5e85d0363480014bb0ba06c6900031718e76949201b51f436c92924000c3e76d925248001c38c7b24a4900
  | 21 => 0x855cb6448001c5ea5296c8900028f60c52d91200051f42e65b224000a3d85ccb64480014790b196c8903722fe1d32d912019c5e43a65b224000a3f854cb64480014790a996c8900022fa1c32d91200bc5ec3865b224000a3e850cb644800147b0a196c8900028fa1771d91200051ec2ee3b224000a3e859c7644800147b0b38ec890002a7a0e71d91200054ec1ce3b224000aad821c7644800117d0e28ec8900022f61c51d91200054f418a3b224000a9d83147644800147d0b98ec8900028f61731d91200070ea9e63b224000e1d534c7644800117d0e18ec8900022f61c31d91200051f42863b224000a3d850c7644800147f0ab86c8900028f21570d91200054fc1ae1b224000a9c835c3644800117d0fa86c8900022f61f50d91200054f41ea1b224000a9d83d436448001c76a1286c8900022fa1f30d91200045ec3e61b224000a3e85cc3644800147b0b986c8900038754e30d91200051f42861b224000a3d850c36448001c3aa6186c8900030f19375591200043f43ecab224000c5c73d9564480010fd0e32ac890003171cc65591200062fb2ee6b224000c5c65dcd6448001938c9b9ac89000317dd463591200062e3a8c6b224000c7765dc564480018e8cbb8ac8900032d19371591200066a31ee2b224000c77651c564480018e8ca38ac8900032d19071591200066a318e2b22400387e87dd564480010fb07baac8900022fe1175591200046fc1aeab2240018dc835d564480011ef02baac8900123d20575591200043f438eab224000c3f75dd16448001878ebba2c89000637a1f73591200062fbaee6b224000c5c75dcd644800193ee9b9ac89000317e1773591200062e42ee6b22400087f855cd64480070f90ab9ac8900022fe1173591200047bc0ae6b2240048f4815cd64480011bd0e39ac89000317dd473591200062e3a8e6b224000c9f741cd64480010fd0fa9ac89000e1f21f53591200062fb9ea6b224001c5c73d4d64481818e8e3a9ac8900021fa1d53591200043e43aa6b224000c5f7354d64480038b8e6a9ac8903071d1c553591200043f438a4b224000c5f73149644819f8b8e6292c8901071d1c452591200063bbaee2b224000c7475dc5644800196ee9b8ac89000335dcf71591200066a39ee2b224000c7753dc564480018eaa7b8ac8900031d14b71591200063bba8e2b224000c74751c5644800196ee838ac89000335dcc71591200066a398e2b224000ce7721c564480019e0e3b82c8900030f9db65191200051ec1eca32240008bd87994644800147d0b328c890002a7a0e65191200054ec1cca3224000ab681994644800156b03328c8900022fe1d65191200054fc1aca3224000a9c83594644800156f02b28c890002ad20565191200051f430ca3224000c3e76194644800147b06328c8902268f2086519120004
  | 22 => 0x326ca900021fa1b73d95206ccb7416e7b2a400387f87d8f65480018bae7b1eca900021f61e63d95200051f424c7b2a4000a3d8498f65480014ed0331eca900029d60663d95200043fc3ac7b2a4000a3f8458f654800147908b1eca900029de0563d95200053a40ac7b2a401887d8718f65480018bae631eca900031761c63d95200061eba0e9b2a40dfa6e821d365480014db043a6ca9037a9ba0b73d952000536c16e7b2a40cf87e82dcf65480018dd05b9eca900031b60b73d95200043ec3ce7b2a4000c5f835cf65480070f904b9eca900021fa1c73d95200062eb98e7b2a400087e8790f65480010fb0f21eca900021fa1c43d95200043ec3887b2a4055a7a80dcb65480010fd0fa16ca900021f61f42d95200043f43e65b2a400087d87ccb65480070ff0f196ca900d61f21e32d952067c3fc3a65b2a403587c874cb654800147f08996ca900028f21132d95200043f43865b2a401887d870cb654800147d08196ca900028f61032d95200051f424e3b2a4000a3d849c765480014bd0738eca900029760e71d95206ed37410e3b2a4000a6d821c765480010fd0e20eca900021f61c41d95200052f41883b2a4000a5d8310765480010fd0f98eca900021f61f31d95200062fb9e63b2a4000c5f734c765480010fd0e18eca900021f61c31d95200051f42063b2a4000a3d840c765480ab4dd05b86ca900021fa1f40d95200043ec3e81b2a4000a5e83d0365480014bb07a06ca900021fa1f30d95200043ec3e61b2a4000a3e84cc3654800147b09986ca900021fa1c30d95200c43ec3861b2a4000e59300c3654800187aebaa6c89000e2fe1d54d912000476c16e7b224000a3e8590f644800147b0b21ec8900062fe1d43d91200051ec1ecbb224000a9e83997644800153b0732ec890002ada0665d91200055ac0ccbb224000a9f83597644800153906b2ec890002ade0565d91200055a40acbb224000a3d83197644800147d0b31ec8900028f61663d91200055b40cc7b224000ab58198f644800147f0ab1ec8900028f21563d91200055bc0ac7b224000ab48158f644800147d0a31ec8900028f61463d91200070fb28c7b224000e1c6518f6448001c3d0a31ec8900038761463d91200051f436a7b224000a3c86d4f64481a387ceda9ec89000387d8f53d91200070e31ea7b224000a3e8654f64480014790ca9ec8903430f9d953d91200070fb1aa7b224000e1c6354f644800165904a9ec8900028fa1852d91200070e318a5b224000c3d751d7644800155d05b9ec890002ab60b73d91200051f42ce7b224000a3d859cf644800147d0a39ec8900028f61473d91200051f416a7b224000e1f5394f6448001c3f06a9ec8900028f20953d91200051f42ee5b224000a3d85dcb644800153d07b96c890002a760f72d91200051fc2ae5b224000a3c
  | 23 => 0x596200051ec20e2b2c4000a5e831c565880014bb0638acb100021fa1c41596200043ec3882b2c4000a5e8310565880014bb0620acb100021fa1f31596200043ec3e62b2c4000c5d73cc565880018bae698acb100021fa1c31596200043ec3862b2c4000a3e840c5658800147b0818acb100028fa1270596200051ec24e0b2c40d6a6e829c165880350fd0fa02cb100021f61f40596200052f41e80b2c4000a5d83d0165880350fd0f982cb100021f61f30596200051f42660b2c4000a3d84cc165880018bae7182cb100021fa1c30596200043ec3860b2c4000c5d730c16588001cb260182cb100021f61e65d92200062f39ccbb24400087f8759764880018bce6b2ec9100031799573d92200062eb2ae7b2440018de83dd764880011bb07baec9100021f61e75d922001c3fc3aebb24400087f835d764880070fd0bb9ec9100021f61773d92200046ec3ce7b244000c5e759cf64880018baeb39ec91000637e1d73d92200062f3aae7b244000c5d755cf64880018bd0ab9ec9100031761573d922001c3fc3ea7b24400087d87d4f64880038bce7a9ec910003175cf53d92200043fc3aa7b24400087d8754f64880038bce6a9ec910003175cd53d922000c5fc3a87b244001c9e7350f648800199ce6b96c9100021f61c52d922067e2f398a5b244000c5d7314b648800153d07ba2c9100022fa1e43592200043ec3ec92944035a5e83d9252880014bb07b24a5100cea7a0f6490a200043ec36eaa14403687e8759542881130f90eb2a8510003171cd6550a200064e39ac8a144000c5e65dcd42880018bacbb9a85100022fe1175586200145e422eab0c400387f865d461880010fb0f328c3100030f9d265186200062f39cca30c400087f87594618800187ce8b28c310003179cd65186200061f32ae830c4000c3d655d061880018bccab98c3100031759573186200047bc3ac230c400387e859da41880010fb0b3b4831000e1f21776506200043fc2aeca0c400387c855d941880070fd0a3b283100021f61476506200043ec36eaa0c400087e8759541880010f90eb2a83100021fe1975886200043fc3acb10c4000c3e7459621880018bce6b2c43100030f99574886200061eb2ae910c4000c5e655ce21880018bacab9c43100039994961886201e6f010ce110c4000d6a525c22188001ccacab0c43100021f61b754862020c3e43aca90c4000c6e655d821880018daecb2843100027961f6108620005f1406c210c400087f865d6408812f0ff0eb2c811025a1f61d65902200063732aed9044000c6d7659720880791df0eb0e41100f3399c561c82200063d32aed9044000c797659720880d74f30d2964110002da61a52c822035f34c34a59044000d697694b2088001cd2ed296411000297a0e64d95200052ec1cc9b2a4000a768199365480014eb03
  | 24 => 0xc8000c79659c021900018f2cab80432000a6e211700864001c3fc3aebb12800087f835d762500070fd0bb9ec4a00021f61773d894001c3fc3ea7b12800087d87d4f62500010ff0ea9ec4a00021f61d53d894000536412a7b1280008ef8758862500015c902b10c4a000a2f211731894000536412a6312800087f855c462500070f90ab88c4a00030f9d3769494000537416ed2928000a3f845da52500014bf06bb4a4a00d69720d769494000537410ed2928000a3c865d25250001878ecba4a4a000317dcd53d854000e2e39aa7b0a800087f855cb61500070f90ab96c2a000237e0d72d854000c6e41ae5b0a804ac3f645d4615009593ec8b98c2a00023de1d611854000572412c230a80b1c3c76dd5415000127d0f29282a00322fa1870505400069dba8e0a0a800387e859db21500010fb0b3b642a00122f212768854000656ba0c510a800387e859d921500010fb0b3b242a00021fe15760854001c3e42aec10a80008df835d821500031b906bb042a00123e21970085400267830ae010a8096c3e765d6405012da74e0bac80a00024f61e52901400145e432e3202804acb4615c640500038bce6a9ec990003175cd53d932001c3f43eeab26400087d83dd564c80010fd0e3aac99000e2f21d54593200043fc2ae6b26400387c855cd64c80010fd0fa9ac99000e1f21f53593200043f43aa6b26400087c8754d64c80031790ea1ac990002ab20943593200043f438a4b2640bb87f8759252c80038bce6a9ac390003175cd53587200047bc3ac230e400387e859da41c80010fb0b3b4839000637a0e76907200046ec1ced20e400087f855d941c80070f90abb283900025ba0b75507200245f43ec8a0e4040e666194b21c8001ad4a538643900031b1d7764872000637bb6ea90e400096c825d640c80010ff0cb9acb100021fa1f63596200051f426c6b2c4000a3d84d8d65880350fd0f31acb100028fa1263596200051ec24c6b2c4000c5f7398d65880070fd0eb1acb1000317dcd63596200043f438c6b2c4000c3f749d1658800187ae83a2cb100021f61e73596200051f424e6b2c4000a3d849cd65880018bee739acb1000317e0d73596200043f438e6b2c400087e8790d65880010fb0f21acb100021fa1c43596200043ec3886b2c4000a3f845c9658800147908b92cb1000297e0d72596200052e41ae4b2c4000a77815c965880014e902b92cb1035a9ee0172596200043f43e84b2c400087d87d0965880010fd0f992cb100021f61f32596200062fb9c64b2c403587f874c9658819f0f90e992cb100028fe1132596200051e42264b2c401a87e870c965880010fb0e192cb100028fa1032596200051ec2064b2c4000c5f730c965880018eee338acb100028fe1171596200051e422e2b2c4000a6f825c565881c14d904b8acb100028fa1071
  | 25 => 0x14bd0638acb200029760c71596400043f43e62b2c800087d87cc565900018bae798acb20003175cd31596400043f43862b2c800087d870c5659012d47d0818acb200028f61031596401043f43e60b2c800087d87cc1659012d47d09982cb200028f61330596400062eb9c60b2c800087e870c1659012d0fb0e182cb20003175cc30596400062f39ccbb148000c5e7359762900018bccab9ec5200031759573d8a400056741ec53148000a6e82dd662900014bb063acc5200029ba087598a400043fc2ae7314800387c855ce62900010fd0fa9cc52000e1f21f5398a4000537416a7314800087c8754e62900038bce6a9cc520003175cd5398a4000536412a73148000aad840ca62900010ff0ab8cc52000e1f2157198a4000537414cab14802087c8759562900014d904b2ac52000e1fa1f7558a400043ec1eeab14800087f855cd62900070f90ab9ac5200021fa1f5358a4001c3e43ea6b148000a6e82d4d62900010fd0ea9ac5200021f21d5358a4000536412a6b1480dc8bc8750d629000155904a1ac520002ab6103258a4071747a1864b14800087d8799462900010ff0eb28c5200023be1d6218a4000537416ed294800087f83dda52900010fb07bb4a5200031ba0b7694a400043ec3ced2948000c3f845da529000187908bb4a5200021fe0d7694a400043ec1aed2948000c3f435da529000187a86bb4a5200030f1097694a400061e20aed2948000c3f405da52900014dd043b4a5200030f5db7494a4070d97416e929480198bf8758a4290001c5acab1485200028f61a5290a4000716b14a5214801b8bf865c2429000127f0ab84852000267e0d7090a4000477c12eab0c80008ec825d561900070fd0bb92c3200021f617725864000c6f41ee4b0c80008dd83dc9619000195885b92c3200031bdc8525864000636390a4b0c800387f865d461900010fb0f328c320003179ce65186400043fc3aca30c8000c5e7359461900018bccab98c3200031759573186400063732ce430c8000c6d659c861900018dccab90c3200031b59572186400047bc3ac230c8000a3d8694a4190001c6acab0c83201262fe1970906400049fc2ae120c800099f835c241900070fd0b3b643200021f61676c864000c6f41ced90c80008dd839db219000187ccaba643200032b5d262c864001c3f42ced10c800087d859da21900070fd0abb443200021fe1975886400043fc3acb10c800087d87596219012d87ce8b2c4320003179cd658864000536412cb10c8000c3e655d2219000187acaba443200031799573886400062eb2ae710c800387c85dd921900010ff0abb2432000e1f215764864001c3f428ec90c800087d851d921900010fb0dbaa43200021fa1d65486400043e43aca90c800387e859d821900010fb0b3b043200029b20965086400247cc34e010
  | 26 => 0x2ae21160181210056c41ac030242028be84dd4604840117b09ba8c090802b6a0f40181210055d426603024200e59530c060484070fd0fbaac8108021f60f75590210043f416eab2042b187e871d564084091790eaa2c8108021fe15735902101c3e42ae6b2042008ec825cd64084010fd0fa9ac81080e1f21f53590210043f43aa6b20420087c8754d64084091790ea1ac810802ab20943590210043f438a4b20420387c8714964085770ff0eb24a4108021f21d64948212063a3b2e32904200c7475dd921084018eea7bb242108031d54f76484210063a296ec9084200c7776dd521084832ed0f29242108031ddda52484210062fb9aa73004201c5c7354e60084091f30f284c0108123e61e30980210072ca9c61300420387e87dd560084978e8e3baac0108021f60f75580210045fc22eab0042028bc845d560084011bf06baac0108063720d755802165e3a388eab0042028be87dd1600840187eebba2c0108030f1d774580212565a38ee8b004200c3f751d16008401878ea3a2c0109272d1c4745802100c6f43ee6b004200c5f75dcd60084018b8ebb9ac01080327dd373580210064e3a6e6b004248cd471dcd60084018bf0bb9ac0108031721773580210043fc2ae6b00420387c855cd600840117f08b9ac01080a2f21173580210062fba8e6b004200c5c751cd600840193ee839ac010803271d073580216566a388e6b00420087e87d4d60084070f90fa9ac0108030fdd3535802168e1e3a6a6b004200c5f73d4d60084038b8e7a9ac0108021fa1d53580210043e43aa6b004200c3f7454d60085a1878e8a9ac01080317dcd535802100e2e39aa6b004200a6c8254d60084350fd0f292c0108030fdd252580211b61e3a4a4b004200c5f73949600846b8b8e7292c0108021fa1c52580210061fba0a4b004289c3c7414960084018bee6292c010b3f171cc525802101e3c3aca0b0042048f88754160084039b0e7182c0108039654e30580210247c43a60b004220a3f865d165900010ff0cb9acb200021fa1f635964000537416c6b2c8000a6d82d8d65900410fd0f31acb2000317dce635964001c3f43ac6b2c8000c5f7358d65900010fd0e31acb200038798d43596400043f416e6b2c800087d879cd659012d47d0939acb200028f61273596400062fb9ce6b2c8000c5f835cd65900010f904b9acb200021fa1c735964000637b94e4b2c8000a3f845c9659012d47908b92cb200021f60c72596400043f43e64b2c800087d87cc965900010f90f192cb200021fe1d32596400043e43a64b2c8000a3f844c9659012d47908992cb200021fa1c32596400043ec3864b2c8096a3e840c9659000147b08192cb200031ddc671596400051fc22e2b2c8096a3c845c565900014df04b8acb200029b20971596404b51f420e2b2c8000a3d841c56590
  | 27 => 0xec26e3b2a4299a6e82dc765484010fd0f98eca908021f61f31d95210062fb9e63b2a4200c5f734c7654840147f08b86ca908028f21170d95210052fc1ae1b2a4200a5c835c3654840147d08386ca908028f61070d95213fd37410e1b2a4240a6d821c365484010fd0fa06ca908021f61f40d95210052f41e81b2a4200a5d83d0365484010fd0f986ca908021f61f30d95210051f42661b2a4200a3d84cc365484018bee7186ca908021fa1c30d95210043ec3861b2a4200c5f730c365484010ff0ab86c89080e1f21570d91210046fc1ae1b2242018dc835c364484010fd0fb2ac890803171cf65591210043f438cab224200c5c7319564484018becbb9ac8908031719773591210063db2ee0b224200c7865dc164484018f6ca382c8908031e19470591210065c320e0b22420387e87dd564484010fb07baac89080237e0d755912100c6e41aeab2242008fb805d564484011f100baac8908021fa1c755912100c6f43ee6b224200c5f75dcd64484018b8ebb9ac89080317e1773591210062e42ee6b22420087f855cd64484070f90ab9ac8908022fe11735912100477c12e6b2242008fb805cd64484011f100b9ac89080237a1c73591210062fba8e6b224200c5c751cd644840193ee839ac8908021fa1f535912101c3e43ea6b224200c5f73d4d64484038b8e7a9ac8908021fa1d53591210043e43aa6b224200c5f7354d64484038b8e6a9ac8908062f21d435912100e4e39a86b224200ccc73dc964484010fd0e292c89080317dcc525912167e2e398a4b224200c7b75dc164484018f0ebb82c89080336dcf70591210066c39ee0b224200c7b53dc164484018f2a7b82c8908031e14b70591210063dba8e0b224200c78751c16448401976e8382c89080336dcc70591210066c398e0b224200ceb721c164484019e6e2382c8908031ed4c70591210063ca98e0b224200cbb431c1644840197286382c8908031e14870591210065c210e0b22420087f8759252484014bf06b24a4908d69720d64949210053dc02c92924200a7880592524840917f0eb2484908cea720d64909210055c402c9212424187e86dd542485130fd0fb2a84909021f21f65509210062e39ecaa124200c9c73d9142484018becbb9a84908031719773509210043f436eaa0a42b387e87d9541485650f90fb2a829090399d8b65c852151d3b434a590a4240e676294b21484010ff0aba6c09080e1f21574d812100e2f39aa7b024200c5d7354f60484015b507a06c090802aea1330d81210072ca9861b02420387e86dd560484810f90dbaac0908021fa1f65581210061e3a6cab024200c5c73d9560484010fd0e32ac0908030f1d065581210062e398cab024200c3f65dd16048401878cbba2c09080317d9773581210062e32ee6b024241c6d7219460484011f70eb00c09080
  | 28 => 0x79d563885514bd053aac710802b3e097558e2172566412eab1c4200c5f875d56388401c9f04baac710b92972097558e2100726412eab1c42e4a4c825d563885838bee2baac710b07175c57558e216052f428eab1c4200a5e85dd163884014bb0bba2c710802b3e097458e2173566412e8b1c4200a5e851d163884014bb0a3a2c71080387d525458e210052fc2ae4b1c4200a5c855c9638840153f08b92c710802a72117258e2172d6bc0ae4b1c4200adb805c963884015b100b92c71080393d4a5258e217252fc38a4b1c4200a5d8714963884814bd04292c710b8f93dc85258e2171f26390a4b1c4200a5e85d0963884014bb0ba12c710812b5a074258e210056ac0e84b1c4200a5e85dc163884014bb0bb82c710802a7a137058e210054ec26e0b1c4200c5d759c1638840159f04b82c710992b32097058e210052f428e0b1c4200a5d851c163884018baea382c710803365c07058e210046f43ea0b1c42008dd87d41638840153d09a82c710802a76135058e210046f43e80b1c42008dd87d0163884014bd0ba02c710802976174058e210061fb9ac92944200c3d73592528848387ce4b24a5108038b9c96494a215462f43ac72944200c5d8758e52884838bce4b1ca510803939c96394a210043ec36eaa144236c3e64dd542884018bcc7baa85108da1fa1d6550a2144c3e43acaa144200c5c735954288401c5884b2a85108030fdd56450a210061e3aac8a144200c9c7359142884011bb0db9a8510803179977350a210062eb2ee6a1442bcc9e64dcd428840193ac9b9a8510af237a1d6350a216c46e43ac6a144200c5f7558d42884018b8eab1a85108032d5937150a214fd3ac34a590c4240b658694b218853fccb0d2964310903595da52c862100732bb4a590c4240f266494b2188481e4ac92964310903d198e52c8621207a2b1ca590c4200c5f7354e60884038b8e6a9cc11080e1fa1774582210043ec2ee8b044200c5f7354d60884038b8e6a9ac1108029b20953582210043f436e7b2a420387f87d8f65484018bae7b1eca908021f61e63d95210043fc3ac7b2a4200a3f8458f654840147908b1eca908029ee0163d95210053c402c7b2a422787d8718f654840147d0831eca908028f61063d95210062eb98c7b2a4200c3f749d3654840187ae83a6ca908021f61e73d95210062fc1ae7b2a420087e871cf654840147d0839eca908028f61073d95210062eb98e7b2a420087e8790f65484010fb0f21eca908021fa1c43d95210043ec3887b2a424087e87d0b65484010fb0fa16ca909021fa1f32d95210043ec3e65b2a4200c5d738cb654859f0ff0e996ca909021f21d32d95210051fc2265b2a4200a3c844cb65484010fd0e196ca9089e1f61c32d95210051f42065b2a4200a3d840cb65484018bae6196ca908028fa1371d95210051
  | 29 => 0x82c99080e1f61f6494b210061e3aac8a0e4200cad641c941c84010ff06bacc19080e1fa1773983210043ec2ee730642028be84dce60c840117b09b9cc19080e1fe1f53983210043ec3ea7306420087f8754e60c84010fb0ea9cc1908621f61e52983210043ec38a5306420387e85dd160c84010fb0bba2c19080317dcd535832100e2e39aa6b0642008fb8758060c840187ee93a2cb10ba69ba0a745962100536c14e8b2c42c187d879cd65884018bee739acb108029be09735962174536412e6b2c4200c5f835cd65884018df04b9acb108031b20973596216043f438e6b2c420087e8790d65884010fb0f21acb108021fa1c43596210043ec3886b2c42e7a77815c965884010fd0fa12cb108021f61f42596210043f43e64b2c420087d87cc9658846b0ff0e992cb10b3e1f21d32596210051fc2264b2c4200a3c844c965884550fd0e192cb108021f61c32596210051f42064b2c4200a3d840c9658840147d09b82cb108028f61370596210052f41ee0b2c4200a5d83dc165884018f6e1382cb108029be09705962132d36412e0b2c420087e87d0165884010fb0fa02cb1080297a0f40596210052ec1e80b2c420087e87cc165884010fb0f982cb108028fa1330596210051ec2660b2c4200c5d738c165884010fd0e182cb108021f61c30596210062eb9860b2c42048be87d51648840187eebaa2c9108122f21d54592210245f43c86b244200a3e8590d648840147b0b21ac9108122f21d435922101c3f42ee0b24420087d85dc164884031bd07b82c9108023760f70592210061fbaceab244200a3e859cd648840147b0b39ac910802abe09735922100556412e6b244200a3e851cd648840147b0a39ac9108028fa0b535922160d1ec2ca6b244200e1f5394d6488401c3f06a9ac9108028f209535922160f0f98aa6b2442c1e1d3154d648858147d0a29ac9108028fa1772592210051ec2ee4b244200a3f855c964884014790ab92c910802a7e0d72592210054e41ae4b244200abb805c9648840157100b92c9108038bd4a52592210051ec18a4b244240a3e82149648840147d0b992c9108028f61732592210255b40e64b244200ab581cc964884014790b192c9108ce2fe1d32592216e45e43a64b244200a3f854c964884014790a992c9108a62fa1c32592210045ec3864b244200a3e850c9648840147b0a192c9108028fa1770592210051ec2ee0b244200a9e83dc1648840153b07b82c9108028fa1670592210051ec2ce0b244200aaf825c1648840117d0fa82c9108022f61f50592210054f41ea0b244200a9d83d41648840117d0f982c9108022f61f30592210051f42e60b244200a3d85cc16488401c3aa7182c9108028fa1430592210051ec2860b244200e1d530c1648840956d02182c910802ad60430592210062fbaceab1c42c1a5d8
  | 30 => 0x95410062fb9c61b2a820087e870c365504010fb0e186caa080317dcc30d95411743ec3ecbb128200a6e82d9762505d587ae832ec4a08029ba0865d894101c3fc3aebb12820087f835d762504070fd0bb9ec4a08021f61773d894101c3fc3ea7b12820087d87d4f62504014dd05a9ec4a08021fe1d53d89410043ec3aa7b128200a6c8254f62505b917f0ea1ec4a0802ab20943d894100556c2065b1282ece8f430cb62504010fd0fb2ac4a0803171cf65589410043f438cab128200c5c7319562504018becbb9ac4a08031719773589410063db2ee0b128200c7865dc162504018f6ca382c4a08031e194705894100477c3ac43128200acc8358862504015d100b10c4a08029ba0b75189410052ec18ea3128200a6e821d462504010ff0ab98c4a080e1f21573189410043f43ea6312820387c87d4c62504014dd05a98c4a08021f21d531894100e2f39aa63128200c5d7354c62504014d904a98c4a0802ab610321894101c3f42ce0312820087d859c062504010ff0ab80c4a080e1f21570189410046fc1ae031282018dc835c0625040147b09bb4a4a08029ba0b76949410061f424ed2928200c3d849da52504010ff073b4a4a08021f60e76949410061fa1ced2928200c3d439da5250401878853b4a4a08030f90676949410061e20ced2928200c3f409da52504010fd0c3b4a4a08029ba0876949410043fc18ed292820087d831da52504018dd043b4a4a09028fa1b74949410061f3b6e929282ebb2e82dd2525056387cedb2c84a089a2f61f629094100717b2ec52128200a3e8694a4250401c5ec529484a09262f21970909410049fc2ae1212820099f835c242504038bce6a9ec0a0803175cd53d81410043fc2ae5b02820387c855cb6050401cb2a6186c0a080e1fa1b755814158c3e436eab02820087e87d9560504018b8e7b2ac0a08021fa1c65581410062e398cab028200c5f65dcd60504018b8cbb9ac0a08031bd9772581410063632ee4b028200c6f651c960504018d8ca392c0a0bab0f5d065181410047dc3ac03028200ad88358060504015d104b00c0a08023ba0b751814100476c16ea3028200abb8050c60504010ff0ab90c0a080e1f21572181410046fc1ae430282018dc835c8605040195884b90c0a08031b9c8521814100636b90a43028200ab984cc06050401cb2a6180c0a0803a650c301814100578c0860302820087d879d764c84070ff0ebaec9908021fe0d75d932101c3f42ee7b26420087d85dcf64c84011f501b9ec9908023e60373d932101c3fc3ea7b26420087d87d4f64c84010ff0ea9ec9908021f61d53d93210051f42ee8b2642008be87d5164c840187eebaa2c99080317dcd535932100e2e39aa6b2642018bc8750d64c8403938e6a1ac99080e1fa1770593210043ec2ee0b2642018de83dc164c84011bb07b
  | 31 => 0x84008de87d8d60508018beebb1ac0a1003171d763581420046f438c6b028400c5f7518d60508018b8ea31ac0a10031dd9771581420063a32ee2b028400cd763dc560508019a8c7b8ac0a10031dd9471581420063a328e2b028400cd7631c560508019a8c638ac0a10023ee1d60181420057840ac030284028ed82dd460508018bee6a98c0a1007171cd531814200e4e39a863028489c6d7214860508010ff0ab88c0a100e1f21571181420046fc1ae230284018dc835c460508014d904a9cc52080e1fa167098a410043ec2ce1314820387e87dd562904010fb07baac5208021fe157358a4101c3e42ae6b14820087e87d4d62904070f90fa9ac5208021fa1d5358a410043e43aa6b148200a6c8254d62904810fd0e292c5208029ba0b7694a410061fbb2e9294824187f8758a52904018bee6a9cc120807171cd53982410043fc2ae5304820387c855ca60904011bf06b94c1208063720d729824101c3f43eeab04820087d83dd560904010fd05baac12092f0fd07755824125e1ea0eeab048200c3c40dd560904011bf06baac1208063720d755824100c6f43ee6b048200c5f75dcd60904018b8ebb9ac12080317e1773582410062e42ee6b048248c9f41dcd609049193a83b9ac1208032710373582410043fc2ae6b04820387c855cd60904018beea39ac120803171d473582410043f43ea6b04820387c87d4d60904018bee7a9ac120807171cf53582410043f43aa6b04820087c8754d60904018bee6a9ac120807171cd535824101c3f42ee4b04820087d85dc960904010fd0f292c1208021f21e52582410062fb9ca4b048235c5c7394960904010fd0e292c12080e1f21c52582410062fb98a4b0482cfc5c7314960904010fd0db9ecaa080e1fe1f63d95410062eb9ec7b2a820087d8798f65504010ff0eb1ecaa08029be0963d954100536412c7b2a8200a7b8058f65504014f100b1ecaa08ba1f61c63d95410062eb98c7b2a82b1a3c8650f6550401c38c6a1ecaa08021fa0b73d95410043ec3ce7b2a8200c5f835cf65504010f904b9ecaa08021fa1c73d95415951f420e7b2a82b1a3d841cf65504018bae639ecaa0aca8fa1372d954158d1ec26e5b2a820087d839cb65504018dc43396caa08031b08672d954100636b90e5b2a820087e87ccb65504010fb0f996caa08021fe1e32d95410043fc3a65b2a820087c874cb655040147f08996caa0aca8f21132d95410043f43865b2a820087d870cb655056547d08196caa08028f61032d95415943f43e63b2a820087d87cc765504018bee798ecaa080317dcd31d95410051fc22e1b2a82b2a3c845c365504014bf06b86caa08029720d70d95415951f420e1b2a82b1a3d841c365504014dd04386caa08029b60870d95410043f43e61b2a820087d87cc3655056547d09986caa08028f61330d
  | 32 => 0x14bf06b86caa10029720d70d95421b51f420e1b2a8400a3d841c365509034dd04386caa10da9b60870d95420063cb80e1b2a840087e87cc365508010fb0f986caa10da8fa1330d95420051ec2661b2a8400c5f738c365508010fd0e186caa10021f61c30d95420062fb9861b2a8400a5e86dd763508018bcedbaec6a100297a1875d8d420062f3b0ebb1a84f2c5e76d9763508011bb0f32ec6a13be97a1665d8d420046fc3acbb1a84eea5e8619763509e38bcec32ec6a10c6a7a1b74d8d4219e4f3b6e9b1a84f0b8e82dd363509dd4bd0c296c6a133f179d852d8d4276d2f416ebb1a8400a5e859d763508018baea3aec6a100297a1c75d8d420062f438ebb1a84baa5e821d76350801c9ea5296c6a100297a1c52d8d4276d2e438a5b1a84baa5e8214b63508018beebb8ec6a100297a1671d8d420052ec2ce3b1a8431a9e849c7635080153b0938ec6a100297e1571d8d420052e42ae3b1a8400c5f755c763508011bd0e28ec6a10023761c51d8d425e54f420a3b1a8400a9d8414763508014bd0b386c6a10029761670d8d420062fbace1b1a8400a5f855c363508014b90ab86c6a1002a7e1170d8d4218d4e422e1b1a8400c5f751c363508011bd0fa86c6a10023761f50d8d425e54f426a1b1a8400a9d84d43635086b4bd0db1ca4a13bf179db639494277786216c72928400c5f87d8e52509758b90fb1ca4a13b7179cb639494200727396c72928400e1c63d96425086dc5ec5b2c84a10cea7a1b639094244d1f434a521284bde1c6394a425086da5ce529484a10db8bd8a529094201476c16ebb0a8400c5f7354f61508038b8e6a9ec2a1007271cd43d854244e36b90a5b0a840387e859c361508010fb0b386c2a100637a0e70d85420046ec1ce1b0a8400c5e73d9661508018bce632cc2a100317d9573985420062e32ae730a8400c5e75d8e61508018baebb1cc2a1003179d463985420062eba8c730a840087e87d9561508018b8e7b2ac2a10021fa1c65585420062e398cab0a8400c5f65dcd61508018b8cbb9ac2a100237a1f63585420062fbaec6b0a8400c5c75d8d61508011bd0e31ac2a100317dd463585420062e3a8c6b0a84ecccf7218d61508018f6cbb82c2a10031e19770585420066db1ee0b0a8400cd863dc161508018f6ca382c2a10031e19470585420066db18e0b0a8400cd8631c161508011ef0eb08c2a1002bc201611854200e2f39aa7b028400c5d7354f60508018bce7b2cc0a1003179cc65981420062fb2ae73028400c5c655ce60508018bcebb1cc0a1003175d763981420062f3a8c73028400c5d7518e60509c599ae431cc0a100e1fa1b75581421b43e436eab02840087e87d9560508018b8e7b2ac0a10021fa1c65581420062e398cab0284018de86dcd60508631b90db9ac0a100317d9773581420062e32ee6b02
  | 33 => 0xf9d3641825241637396c8304a400a7980d9060948010ff0eb20c1290db0f9d1641825240e37392c8304a43693e84dcc609480127b09b98c1290025ba0b73182521ac3ec32e6304a43587d87d8c609480187ce9b18c1290030f5d363182520062eb9ec6304a400a7980d8c609480187ce8b18c1290030f5d16318252006973a4e4304a400d2d749c860948010fb0f308c1290028f61261182520061f3a4c2304a400a5d83984609480187ce8308c1290031d5c461182520053cc00c2304a400c3e74d8060949adad4e5300c1290021fe1d60182520051fc22c0304a400c3e7458060948014bf06b00c1290025ee1d60182527a6b5392c0304a400a7b8758060948018f70eb00c1290038ee1160182520071c422c0304a400e3a745806094801c72e8b00c12900396e0d60182520072c41ac0304a4f4c7a725806094801cd4e4b00c1290db0fdd97494a4244cb6412eb30c84028ec825d561909138d8e4292c32100e1fa1470586420043ec28e0b0c84008f78758461908051dd05bacc1212271b9c852982420043fc2ae3304840387c855c660909132dd05baac12100e1fa1f75582420043ec1eeab04848987e82dd5609080187e83baac1210030f10375582420046fc1aeab0484018dc835d560908031bd0fb9ac12100317dd773582420062e3aee6b048400c5f85dcd60908018b90bb9ac12100327d0773582420064e206e6b04840087f855cd60908070f90ab9ac12100317dd473582420062e3a8e6b04840087e87d4d60908070f90fa9ac12100317dcf535824200e2e39ea6b04840087e8754d60908010f90ea9ac12100317dcd535824200e2e39aa6b04841a87e87949609086d0f90f292c12100317dce52582421ae2e39ca4b04840087e8714960908070f90e292c12100317dcc525824267e2e398a4b0484008fb8758060908010fd0db9ecaa100e1fe1f63d95420062eb9ec7b2a840087d8798f65508010ff0eb1ecaa10ca1f61c63d95420062eb98c7b2a8400c5d8718f65509e7c3d0831ecaa10038761063d954279f0e210c7b2a8400e1c6350f655080165904a1ecaa10021f61e73d95420062fc1ae7b2a840087e871cf655086d47d0839ecaa10028f61073d95420062eb98e7b2a843687e87ccb65508010fb0f996caa133e1fe1d32d95421ac3e43a65b2a8400a3f844cb655086d47908996caa10021fa1c32d95421943ec3865b2a8436a3e840cb655080147b08196caa10da8fa1371d95420051ec26e3b2a849ba6e82dc7655086d4db05b8ecaa10da8fa1271d95420051ec24e3b2a8400a5e839c765508014bb0738ecaa10031d5c471d95420043f43e63b2a840087d87cc765508018bee798ecaa100317dcd31d95420043f43863b2a840087d870c7655086d47d0818ecaa10028f61031d95420051fc22e1b2a8436a3c845c365508
  | 34 => 0xc3ec7b0ca400c3e74d8f619480187ae9b1ec329003175cf63d86520061f3a2c7b0ca400c3d7458f6194801a5ce9396c3290034b5d272d865220e1f312e930ca400d2e625d2619488187ec2ba4c3291030f58574986520061eba4c930ca400c3d7419261949d34dd04324c3290031761973986520062f322e730ca400c5c645ce61948838bcc4b9cc3290035398973986522062fb0ae730ca440c5d615ce619480187ce9b1cc3290030f5d363986521ae2f39ec730ca400c5d73d8e61949d14dd05b1cc3290d61fe1d63986520061f3a2c730ca400c3d7458e619486b8bce6b1cc329003175cd63986527d5b3416c330ca41396c825c261948010fd0fb22c3290db0f9d364586522043e43ac8b0ca436c3c7459161948814e902b22c329003175cf63586522043e43ac6b0ca400c5f7358d619486b8b8e6b1ac3291029d20563586524cdb3416c2b0ca43693e841c1619480127b08382c3290725ba0870586520043ec3cc830ca400c3f74990619480187ae8320c3293e69ba0864186520053ac08c830ca43587d87d8c619486b8bce7b18c329003175cf63186527c537416c630ca400a7581d8c61948012ef0eb08c3293df599c961186522053bc3ac230ca400c778758461949ef8ece4b08c329103999c961186520049fc22e030ca43693c845c061948012bf06b80c3290d65720d70186520061eba0c9b04a4f6a6e8219360948012dd05b9ec1290d61f61f63d82521ae2f39ec7b04a400c5d73d8f60949eb4dd05b1ec1290029ea0363d82520051f426c3b04a436c3c74d92609486d0ff0eb24c1290db0f9d164982520062fb9ec7304a43587f8758e609486b8bce6b1cc129003175cd63982520053dc02c7304a40093f845c6609486d27908b8cc12908e5b20971982520051ec24c3304a400a5d8398660948014f30130cc12916edaa0b60982521b49f43ee8b04a400c3e62dd16094801a5cc5ba2c1290030fdd264582520053d404c8b04a40087e87191609480187ee8322c12937e9ba0864582521acaf43ee6b04a400d1f74dcd6094801a38e9b9ac12900317e1b73582520062f326e6b04a400c5c64dcd60948018bcc5b9ac1290035398b73582520049fc22e6b04a43693c845cd60948012bd0e39ac12900347dd073582520068e3a0e6b04a400c3f74d8d6094801878e9b1ac12900317dcf63582521ae2e39ec6b04a4dea6e82d8d609486b0f90eb1ac1290030fdd163582520061e3a2c6b04a400c5f7358d609486b8b8e6b1ac1290029e20163582520043f43ec2b04a400a3e84d85609480187ee9b0ac12900317dcf61582522043e43ac2b04a400c3f7458560948018bee6b0ac1291031d1c561582520053c402c2b04a455b6a82d81609480187ee9302c12900317dce60582521b49fc3ae8304a400c3e625d06094801a5cc4ba0c1290db
  | 35 => 0x40098002000003802401e0020000000000000001000000000a0258000010001004000001a003000000c02400000080400220090018000016005000015800a00d00280040140000000000004001002004c00a001003000400c000000004000000200d005000c01a000003401000100300480120050048008022009007000000200500700000000010030034002000006806002e00200000080000020058000034006004001000600400a005401001700b003400000000f801802e0030198028006014000000c00e0020060020022005000808803800000282e000000b000000800e005001002800001a001801c05400002d801c01c05500b0000002024009002000000800100980000000000004002001009002c0060000040038002004003001400200100c004007000600080000000010000010052005000000001e0000000020018000000801800e000000007400400000d800800e009001000406e0110080010000007000800c008007005804c0000000000000026003000005400600003200100020060008000006016000800c008000003801800e001000000c00200c00480180020410000044006009000009c000006000800400000800300c800a004010000005801100f012000c003003800c002001008000c000013012001000c00c027001c05600e0040000020000000800400200900d801c00000201180380200000070018002000000000400003e00b80240260180010048008000002000002a0320258140000001000001803a042002001c00600000a8000012015034003c0020030038000000000006016c0020260008014042005003015c00200a00b008803401c009002000000000080040000390110010002000003002c000000001000400400700080400f601f000808400000000e801004c00800080240180080020044000002000001c0140080000018010066007000000200601000940060010078000010000001000c004000000800000c0190008000002000002008c01c0000030004004000001800800e00200100000180110008014004003001005003800300100b40187cc9b9ec9290025ba0b73d92520061f322e7b24a43587d87d8f649486d47d09b1ec929003175cf63d92527e717324e5b24a400c3e645c364948012bf06b86c9290d65720d70d92521b61fbb6c8b24a4fbb2e82d91649486d47909b1ac9290d61f21d63592521b51e422c6b24a400c5f7358d649486b8b8e6b1ac9290d64f21d43592520051e43286b24a435d1c7350d649480187ced3a6c3290da4fe1d74d86520061f312e9b0ca400d2e625d361948810fb0fb26c3290db0f9d364d86524e637396c9b0ca436c3e7459361949378dce4b26c3290da4fa1373d86520049ec26e7b0ca40096e82dcf61948012f501b9ec3290025e60373d86522043e
  | 36 => 0x34004001003000400e00002d8000000004005003400200b007807800a023002800c00403a008800401a000001000001c000001009402e000000004403c0000000004006061000001000e002005800000a0480000000006010005800800200000000240000010058018004001002800801001a00e008008600a00680000000000000018000003000000400c008015007c008005015000c00c00600680100260000000024012000002000400000b00000500040000000000024037005000c006006000000000401300000040060000010010000003001005000801500600240360000000048016011000000c0100010000004014002000001c00000000d008800201100b800801a001000001407a00300c80a8006002015000000a0230060008012000000002000e00401980000140080008020000006000003c00600d0010030004019000000001a00c00000140000260000058006010001001c01a00400300480040000000000014006001803c00e00600080340080110028040002005005800801800a0018008006028001800401600d001000c00000b004004402800c00100040000480008000000003000000c00600401b800000000e000000803a0000010010000002005000000c000001803804a04600600000900010040058002002001000c00002b00b802000e004001000c0000020128000000001004001400400b00180480000000148014002004002000001405800080000220070170070006011003013c030001000804c00201d000001001e0000000000026001000000000e01400a80600c00030008038010012000800000c001001802400200100200000080000028054004002004002400e01f004002401000f003807400804a0000000000018002000c00c007000000404c00000180340000010000050006000003000401e000000005400e003001800400601f0000054000004000000000001200300180200000000060000000000000402200600a802c000001002002000000100000780000050008040008000002005400a000003800c002004002800406e00100080140000070058000002002000803801c0010030018008002008801000800f0020014000013010802c00a001001801000000100400000480030000000008001000800001c00600080d405e00a0040000006019011803002800c0038004000001000800c0900000008000058000013800005800400a8010000002011802001c00d00000040000100010018004001000805801000000d8080034008001000c00a022000000800a003006804c000000001803801400b002000c00a00000080140060060000068008006001800002e000001801000200800b00d404c003000004401600201200040000070070004008032005800c000001006002000003100100f400600
  | 37 => 0x454116fc5ec0174e18411c000359c62500000001618c1a032493a0d4c94c039c74a2a80ee10de46f837d8de31af0f8f395cc1b05d831249000000000bf941d8000000000047a0000215492036491dc00010521bd40001ea4df50000eb7418caa249e40000000000160c47215341f021a8b2a2fccc80261c3b71c88ad5373c76c318478445e400040c91a105380000ac88ca10180004b00dd8446d228141c5d91a292f024041801d6c001002000c01202500e800001200000000640080000000000038013000001800601700080340000080048000006021000002400601c003804c0000000018000008000007003400c000006000000000300000a8000005000801400c019008800800000400980000000000008088008000005003000001b00480040280010000034002003000004800000802a800c0060000060008000000006000801e009000000000000f00000ec00200100c00d00060180128008006003006807801e000003000000200000000840020050000010000038000800000a0000020004000000000001c000010000800001c01700000000020000108010052000000005c002027009802004c035002003401e00e02b0018004007000801800400b0000008012021024000002e05a0098000038018007800400001b00100040160010008028028000001001000801400380000000000000004030000000801c0000020008000026002000004802e00e00601840040300020058004006003000c01800900500b8014000007003803800200000c000204b006800000005e000002401c004001000c01c00100101300f8018003003400800500780b000400e000005800a003014000000e00d0040054002001013804c00000600c800402800600100c800000a00400040400030060000004008000001000000200d0004000000004805c010003003800000c000000802804e00e004000000e011008801c03200f003003403a00000b00a000e02700480040260010060020090000003800403e00800400040000040020004002001005001003404f0020000000010002002c02c000000008c00002b0018010002005005800004e002001000000a01600b800001000400b8018002016000804c0060000078034004015000000c010000003806800000100200000720070088018000001006800000200700100240100010200000004002002804402a004001000001a004010008c00600202100000040010008000000002015007c00003b003000001000900d001400400b01d806001c0000010004000002000001001400f0000000028001000000000600102d804800e00e0008014008004001001c012000004800404002b002817c00001e0050018002015003006402400e001801c01c00500500040040000028030012022001801401800100000
  | 38 => 0x14008ea81d680f900440002a840001bb43ad001832f05989e41f00828314c21f23a400047044733e486790798e5820240cd1b9c1c44b10cb400000000f300000000a3140e453102507e12c108b43b803bd1ea8b2c4be0000000071438fc9150c6d05b28543dd1f88ed53fbc0002d551cf330473026140000000045202800000007640b9865e166c9fd4541303000000004302c9195439e2078b070000acd20e46ec1d948af0000000151800000003b21938dd30000cae3169169029000040f4000467c1d1003832d2ed8b6e3d74ea12280bcd2784ce900008f72f8cbb12ab8bc94b48ba72b6435b437465141812970c0489324d86a127951d83cc1077408c4a40a48c0d000111d30ec7722b74407223cc2008f4f91022ca281800000296ca8d328c50405c0bb43afc000216c5114b8c00044e8d4000003e14830a963d05021008055000000004251247000000000010492a0000000011b805108e648f869c042108222fc0701838b530000d314188f6a14ecef510e8000436849718d4f820a30fb9356c10f0704a2b003cf503ed051204d51df0c344570154b940990de833910843a284091afc2d23e1cb884424a6d44102d54564d793f50e4100012d71ae04d90e6c22e00008dd39005610a5c0001d040000000a6e38440000cd8000000086249d000040c40000000e642b7c00000011d5432ce3d0ff80000000000071476d0000c8f2e6c1ff35d8f62340813d1dccb193dc8aa8302c45d196c51e3dbc00000000002b10d38000035520f800000012a30000a5600006820dfc0003d3893700010d1060cee82c44fda0cf0fbf1a2cbca43e8b60211c3003d98c40340c8263c48a1e425473900007814924a5e2b38bb94ae4cfb16812af11d8f8600012bd32800cc0000b641f9cafe3a406c642cc00028c0c17128000043dcf061b8800017984af1bd066f0868c2d209c22a162890c0b210af41d4fb0164481413689643428da02b69180369829610f0e83074916d2f50ad61a780b008bc0b6458d048489440347b06283f3c37c16acc2f1f1c8973b4000010750ab38d8c5d0930a650ea92293c7882339389c104bd0cc20ec9a1405878803a45ee14f4f3d2ec08ad00dcc6249d48152d3cbb5420c75f3224c7d1e250fd2f88d1f0f8800043c00001a804f545343b014904361f30fc81d0001e00001d031ec12c19008ae07a900e312400008480004884c0717bc0002e04b9d228caad35cc84c000052a00011e64244e3c0000000000126e36bc45000011fb46d4b69000000007b0c773ff4000310c917116c3690004b1311acf37000000041a80001cc516f000025600007be4aac0000000c8344682e231300001fa0cc92d94cc0234c39839bd15b454c2f2000000000001912fb4cdd19a49260648c1c2da09cc118c78024d00002dd8bfd000000007cc000114
  | 39 => 0xcc3a11be447e39e0eaa37dc443134903000000001c2c0001eb8000201d23037ec000337c4d821981191aec3b41b0c04049ec4d72a0d1671848000159c316000085f0524084000000000007660000a7020b8ffc46bc0000a7475847d803b25ed1fd38b0d7c00000003f4d2be27ec00012ac2a700002ab0000000424c0000d64d5800004c73edc81247fc00023491ca00000001f407491e991450814bbd22e000046489d348e897c17745d0427c95e017820c090c5564b5856041081940f14a8444d046606a0e070a4400005e0c522e711063d9011536f8361023060a40249b12158b094650dd2321cd871c6ceb83e7c8921d4845226440003c1019b45b8a63091055212284a600009ee139430c2a910bb30a4ebb00000001cec0002bd0cb512c800043e00001adc27c0000000140400029251e0455814c000128337c0dfa07a480600000001af48e53b2c3ff2e78e4f15746cd0a9930e0b9cb8241c52c503792140514af909791214290eb1387d0850f44a3812b0053000052b40ccdd90b3089f4158a2a04740002bd401b1b28f762a2925002582a2482c81148c84c8000037424a4c5736e408a1a240f748b0a6b141800015ac3cd02440001050d140eb8a3e111800025bc7f139ac94a31a00003218a7d42dc00014f80003308d8f20340001f78f4a000000009383b51cb0648000000000000001ad50f9000011a000038c0ccd09941345fc0ac44cf144d08146b9200203c0a724f8a3c1aa82ca42a521809c0c4221b097506f475509141140b68c7638d03a623ec76006ed0504c5902434711f40d3cd3a007418a1f0414002b414d0fd09bf04dca931264d5e20912c126cc00841ecf55342c60b142863b1744adc2c2cccd29488403fdcc5112ccefb35b4ee31e70791117cee52c7130b1eec1551ed454232446b44a5413201a12660234e3e01583a009740003948b21093cf0c0458a393a949a20870ef42bac1411f0839703940000ee0c4a250c2ec0e9498e20f4f1b13fc890403506d2074412263445c4ab42492af027d0000f0b1da0000063c4300380b851e290ac078cb322ebcff545d0a61124c2f500a800031c50eb1c40b1020a48ab3f9507e18dd1a0009818c17ec57e1c804260000f9643ecba64164ccb08d8cb319e0e262dbc6673bf800000001c9000080e0000e2a2764fcb218000000006100000cd33dd000014304f7298800009a40000000e723a151134c20f7b40d91a900011d1447909d288c07b3fc0e233084ede3598a8c1e604310a7ce5b3fb0b201bc4f2f2b95064205c9392408b7f0880f3c0000b0f0994df90f6852725e0d1645482e0021471e42c10d52f6094829c42ad28fcc4b22c00004b888584588260212c649000000000007540f8005236f4afd2ec83ea3be8bb72c28632074ced6085810714a08cc2780c72441d26311f0b3
  | 40 => 0x13171c4868716ec00000004dd11c10701aac000210400000cc9e92ee01840000f7e3908b032e90ab831200002e5908b37e01793b3cdc00000fd50778000000000042985580000f512d2c7f036c10bf44940323f780c02e445cd3c8497938005f12e842fe23ac9ad1dc400003fce932e1d21f44fc3e9300cc6f455115c392115a11249800fed066244500f09e89923c5c479431440f07dc41910444db2ad44de22dc0000000f600b380001a5888926e8000273920808643932fc800020840340c5c188445c0d643d800020bc0001850fb341e4028292d2f5216898107f400000007170cdc5eb10ac3f1000021735711bc0000000000000036a4cb8417c883249400036608be26400f50f4c869047c7c917487e4490ca354a2cb39152c55e138c9053a8cd9e1ac47060b8c0fb1a50533206c23e019c00031d4a861f1800038b90d00001313400c4ba1bf4000450888c0000000000000018f0ad0026ce060000bf0000000000003d4000074d356929a0398ffe111c0f40a0905112b4b8a475c0002df41ad2294e9d46c11de06140000b787bc054cfa7414c3954031124324c00c2f080002dc07133eeca984c34b080d7c77a062c9a64b543281a9800000008351e74bcb2b8c6b00000000273c4ee10047920000cca1cd88fd00006b600002f01e8c00043b86fe2c890e145a82f3269c0001ebc658308837000000004408000000000000000274a21226000000008cc32b3a3469836b4ed73fb47530a1cce02a1451b2550000452cdb81e5cf4f2cccf150e04d2b417897d1a8d0e40698e0e3d650e84ba522e0544804081cae112ecab616e4c5933e47993e7478e4b909df40a0a450c3d0d4309d1182f9079f2d8d2a40d44d622500134082d0aa124400004906194c484c016d8007377c744058d183267842f472024a3ce095649684020000bd3278cb9200012650b651992d9c5db03e80002014e3b0270000392cab71c340000000e0d38412772f58fe9267c1610aa8c6346440003f5c51f3a7917318549af0d48cec000098b30c026d3f646243bf0b742bb507c37410f42f0c95b279832c48481f90780a5f1e1cfee13f50a8457d22742d873f188c7b73ad87004544092000066a181c6af369c8fa3f911d0476d29446346200f08d541a9c4eb03c454c367077416580001f6896d000104f0000e1d4a28a722dac19a219c56e329000032d800003f0c383d5886b0fd519e154c96018cc0b4222ce2d1b5cc9a12486663b991a21884eb4207cb712dc8f8448742803f44d553170000307889a3c642340f0cbeb26ec6ce4048b060a9400023c416746900001714e170af40004b7c82d48f4b281a68b662150348083cd8d43584c41910bd51aa0ade0e152c627484952f810962560590110016947e84f832f8a24000052335c52e821bc00009e4b8d49fc70e48
  | 41 => 0x750a991054c3944c80000b6092119f0c5b4a7cc011fe4400356400009b00002dd47e545187e6379000000000003e2442938c400040a8d2c00000000000a7e46c400046689b708c8c040000a0b3fc801c4430000160528f0000000000004708980004a44000000058f265c000150c1b21f6c00048fce1b39ecd2400000970b0124b14d0cf22e4c0862bb09661cf8b4c0c8c7eb25f874e2bb86c71bc0ed31c545442d7c95f4add287118435e45604fa1f64a2600000004580878202c0002c38004123426e0f18fc0351046428d000004612100db0aba01705004b1d2f30c70a890ba80003bbd2b21b58aa327a8eb22e68fc63db8c1610b10c10000746132ccc72aa90be4c011682f64cc62ea0a9a0a110d700012543ca8cc4294ccef40fc03107748e34b3826642302291b4cdcb27212154168ff811b0cd4000098318e80001754000368896a00000002828bbb494438400000000000000164c00010fcc5f18b400015d5090482400000000000000000434c38319ac00036c43be239000a1e887c430cc78c137c00000000000000000000091c2338000197d25c01d401714607bd3c00f472b5c00000008571e1400000007d30f543a44524f1a499123440dc24849b04f1000812641303d8000129e00000000ff0a9505dc4551a40547289cd9d06d91f216a40003a9126a1becc90247413037140000000d5340acd341ba8000382400018ac7a0000000000000000000d1b3ea04ae00012413b1ccf7046ca554064000000059728c8e4426f0ce80000347437cabb1d149524a4000000000000594cf8494c00010a0f8500004b73ccc685268c9820bac31038e91720001257221cbfa22285a206d07f6112c7cb2a94b4148d81aa3890f2803b402e26a482b08dc2520000f0a09fd0254bc800039d8c7317080003a1d0540a207291214f572ef86644bfc00d06fd1cd18fc3254834d4c03c9239147021017f912a08ec0000d9c1d826c81b7175800014552ac00000003cd87931f501ab03f8fdb284444f3cb919b2c14276083868c0f10b2427083304b68dc70954039478c0ab37452e73d08d3e00000992810d5649ac2fa34c85f6349509b0b8471f273402334a45662f309ec102c2230de8faf4ad4bba21d42b31c900b922d40d73b88b4d18a44591fb0ab947ac6d90fdc3130000846281c93c413873716200003544b2903b00000000f54000023f3d60d8c1b812f429000000a9046d00009a800011974a74c0500000000df400000010f1000000045e85ca07688823d8cfb1050855a3f7d1ed384800000000003fd8ea70000b3400000141820fcc4ae09710ecc31a309400000002b7343800000000001b6800000000003e644ec00009d6000070a080433f427859e4658d9b21780870000ae200000003e8846900002060000f350000800096c00020d11cc3a980
  | 42 => 0xfbc0908d770000000000084d1b2070f21649861e2d21b04247c3455400002f8ce7000000034887e33a00ee9000112928cc61a17c8fc10000b3021ccd3b36d05712b2406b49c816432bd01d013c4ed4174f7140606471c146dd3e849190c100001a7c0f30fb82274c700001ff063037500002c5127642d111c190c1463c98e292b280d80808525459883708a076942186d51d203de3d6ce161a545ac16642dd3a3c2721398f782e2429307ad1ea0000ebc0fd840500000002c9c67312746dc0b08a124c291f935fd06e120017e2d6060d1fe8e6733442d7106cea00000000377800000000000000d35000023a1108ca600000003978ce63c04083204013c33d885322909c52b450571bf131019183444234f112340c1009d0b6d000092c1904c661b0040d3f58f2900007a43b482d41d1c48628f524f119492e49f0e20006817515a8e4900004f627d090902e85cf41a48bd3b2109804fcf8d36906e547910923bb0bfe4b8013134a80c3270cad34bc4377246920608acc7042b51cb307d02e280d03c42c4e2b31101971ecd2194ba89030550d2d268080c12092f94b28ec93e8cfcd05d0dbb34452a1019527138309143c881f529a4dc20b3c87d386848f18b8095444470c32640212b2018e0000000000033417e40b800000000874a060580000094c86821f8a4139a10cd0001005166854f0000fe645200000000000000050900000c200005b0035400009d438e27c8dc914c80003808000000000000009c926b8000358011310d5040000000000008e81aa495140786d207183c013c806f3e30c6e1c8458427105022f5cfaa19d8386000071a03f40000d28ced20c891f108cf88104ce2217cc7f432b0b3818d04ce49f456d1c08b50155c8db004ca58031d22f1f38d0701351333a30f073f085c82c785ae09645c731550fe2a2cbd03fed13b21e469d402cd943fc44753c50a6616ccdcd06651902afcdca232c373382c4583f88820321118b0f585a5291032e04e044d000004e2cbce25000071d02ed2ba0000ebe1fdc17a488ca2133c4db71d888b31ca02a31b4044e1094c4f1b6c000142d0fc27e01290c08c082da889832489be3a644fb3658d5f000000040e064b23fc50d24f43db00012fa13809d020885a60bd07f5406c3562b9cd61182411e4c640a82b0c1cb30743493b683292f7c000000000000010d908352ae000091e0bbc0002af40000000bc4000025800000760000000214800005c4b1d0000d300da07dd0000e9b399832427d8ac71c60cf43420387252c3d70fe017b2fdc12d2fd0ca501f4aef45d44783aa4ee42070d7412a4dee0348db515c000043d4cd22a6c2b910cc00036ac82a3b18fd819840002e2cec4097c0000b400dd447cd8e1314b8f2d24a1800000002ecc0002e6400000000000000b7e0be059f0385068241c9ed0
  | 43 => 0x5600000e680000ce85a73150d830000dea0390972206863127c40000e700bf38c83e64c6ce14379cc882b6d115301800000000004bb8bd100004b100005b73984000000070108e488d4b086390c9cf533b283dc0c6400039580c42f940003cb4b3c129c9122d6400031802be20052a8000000000005e02b3cd8223f117d0ba4c67480924e1bfcf3e28692a62aac0004bac152440427e0000f94276000019e8494462903b0000c1100010c3000000022c80000cf43c723344bf0000e2f2e8c077000076b281457c0828000000012120cc638000000000000001cf4d470000deb000036536b861100000004c680003c60d8b00008aa0344000000000000012010fac0cb0000ab128210ae3404a810e2cdef000003835bc0001b3d2dc256800014e4a7907d9299266c6e931f800042f11201ce80003988529000000000010b817f46cb2420c9c181873540d00000000a6c2970af7000000007f041c47c48a22d0c14a3704dbf0000d9f4670a5431e8562439800010f8530000000004f918f1a200000150be70000df20000b6c2a500004200c261f1476712d467f127cfc40400a5d21eca90040cf5f30d4604023c54e075c9500f64a4838c10f30a340d000008c51038a360000000148400000003a239cc0640670f7a174c0001b100000c150464c18516290c1ce000000010784d5213c77614bc3712304000185c5d700000003dfc8250a38cee000066e00001e72b18000017d1281c5892217c057a2b2cf09028cd682fb80001a5c1d5000066239fc3fd22640000000bf5402117e4400e0330c81fb39dd2a90c2930210290612be858937311e52838a6449b4813036c31e2c94f7017901332becb52187912d3ddc7ac3538fa41df44103b50e374b74f48333888030ac55412d05df4380d804280cfe2fd916b1c9406610203df084d06744b0a570b0d11037d0ef0459514313a4cf32938d1048ac41f22b06de04a8c090e350ea41149412840c0a48b448b26242dc05c862c4614b470bdc7c81df8f4b46749653bc82cd042c6420640e28135858535ac01f05f472d2aa4af30c889cb2584bce2fa4b5132ec692389cc4e1d84cfa365c7074270da53f40e8e2788bff14d4a0c243c9490bec7b40000498000077b25888d939d036e03b815f3ae8b002b0800023600000000a512cdc000282400041c836a0000b0c000005040bcdb632284fc2cd9044249022144d460531b4e9a0ce054921fd0221304ed84a942ee0e64891458473c10e52461060cc81f2814f067d1c93931205000033100ac000449c0003140881452819814b014800000d42f846d407c47d80e483571fc800026c000047091ce06b006146040000410000463800011fd22019f80da1648ac500005360c8000029e8a3b0000b1f05b91393c9d1c7000000020fc9283ee812e440c16a0000c2c1cb8
  | 44 => 0x86ae36281be30d0ad24a10f65129458d2b30d23347855b1414f9831ac0d923ccecc21902030f8ce65462064a30387ea0a0c2782184f8011888bc1350ce200f02ff2ce90bd0238de913f89db2bc055f2918df32de031534bc186381439106f004131340513a20a9e30fd0972d005f70000ad41d0d0b220f07d618043e811142bb33842d111503d2266061809c493305cc8483df4d42180826b0ad107441cd2ec0d380003acd1be32781af0108496210d1b920e8fbd3f28de6090400027e4cb700005c007580000494000323807900001cf4bf836d00012ed1ec00000940bc61a10e011330bbf19f509a0aa400034a000022a11ee3e685bd24c04ef0afc0a10fb450829bd2fd2418ca91ffc000327c674296911403a072a4b4c000000000028bc0000e20c6a1308ff9244c00004343a736cc87240a448c00008c9383c00000001a53d3465a1cc80000b2c00001c8000049cd0000000000000000000069b10f40df32e8a470304000044485d255c15737587860000f432a7cfea000000000009c62cac00000000000000000000000009185ed0000d2148c400000000000000fa00000f1000001ee2310000442d2960a2c1a9098868300008a73eacdda3dac0003cac00049a406318982b02c8c4d00b180000000ece00b0cf50000ceb40540001a8800049884cd36a800049c0a292e5c8a100c000000000003d4857d119c00000000003f70b5d00008942c60ccc12e114c0ab11c306e0ab2088816b0b90e1c194ceae330d1360efc1283d2447b431cc9415652243df11c60c243750be50002a086ac0130838394c9a4305484a14980003b0490e145c00035ec3964434f2037f00ae0bc488e2668da82ba429017a00b22dec8ba2d08e5d1d783f329810de364077f2630f5e000056c00006b225d8c4705f0b9502740e3000091046e90ff462436201e02240c9928e22c51dd433ceed1cbc0ce1cac000000000029305af47e06eb0d60d50428c97730dc9bd09701b5033c08025c0f25309095d0000069000125f12f800026d8000000000035204b00000c8d4b2117b24010650558bfc41b0dc8254d0ce259c4a211b8bde000006012e406c4b3126f09ccbdb10843891f7c52d2d6876e3190ca8128d04a16a00001268afc094444a2c4878f2e386991d3123b1a4c05747488b63cc813635f40003ee002d0a80a7740451bf14e000000001b11d8d0c6355c000423c00001c400034fcedc0d992d41d6403531181680a3c2db17fc2252388e4a00006571e682683a2d20a304802217707a105400001a3ccdb4a609d745c09841e34c8530f4f6148dcc7411592923c58211109c0001ae41a03358ba90dc80000f0400002788fe19748083d710d20cec4224224ca118f8503397cdff2d38f753f1c6e82fb0000085051016e80000000000184cc5e02608e14c1cf83052cde2
  | 45 => 0xa000043743008cf000097f0000f6811bcefd1d4127815008700f3d035000000000009993d680000000f6c4accda1068d02026d489d23551a5461803a4370ef911e80003de451d3794000163930140291193940bc03364b902d787ed3ac000039a80000000c9d00fd18200010e300009f729f0000000059d3cec7754a301c80000d153bd8777091ce6325341010a6c42e1af877c00005cb3da400000000000f900003a5d01022708f429cc53a07e80000000a7437f8778231ce6c373884900012db4a9c9dd325c3fa0d088ec4af102c4c6000032586d1000052e000121e30e842a496c26f4b6010a2cf8e5942e92c305b00a0000000000008ed000101316a90ec4b24000258c33938106ef00000000000000000061f0000000359506b1e5493100007f3000045a08200440cf8be82f98708000000000000d323186a54c441c019c4cad22991931a1800043287b64ad803d0d812fc0fc91bd1ec8000283c884401ce9409a8bf147ccf08350d2072a203a33ba87e00a28aac198ccb14a181b3230c3502864062334000b162c34016852130df8f9b0c20fb6193cfce23e4e9f1080d6c069c8c0000000000000292dcc000474d1b725ac885016400039b43f02a486ad3b0c9dc000000000000000abc00000001472888a6a0ee400002d40000268aa727fd0870000f81000000004ed25e46ecdc3308c1ef3b44cb931585a4439c7423719222461cd20405c0002cd51643e984bc39f400000643af25b01dc0000574010ca00105879609ec22c0e74a3a28b0ed9000116c4448b3d263c6030568e350c60fe822584e13d9c0ac0b7ccd848107ab3b6c4d1146828639d45642834b5b32c80bc253c622338d2e52f041ae2a1c5d825d091622e48310570448479c05b251d0a5194101a34b81c725b861d44285220448af242850c423d4a2d00006811cd0c45304c6651b14d272d5c0102d7035404e40001da834d00007572a4513d37702002f14417242d29308d43a91c98cfd12200ef0ee82991ff843b29e053703143413f1400047850783970c950c0d1413ce876f2ba8c0f11f41b9000125930502e53f4800000004bd0d68de000000000000a8f3abc000095029a4bbc2ed00007334610000000000024fc0000000e2100011a800000000a040000f212fb02f471927d40000000b3f0000e3845e000000000001d2c0004974d3301687cd4a085f419491a304140af30f0d391d44d694488ab01324cbd0728fff0684d12000121133fc0003ed46f6000031146c82ba4630fad44ac3ec29085c10cc89a53f8089e08785792e1082c1ec521c36242c74b78ff30000c314a005784948580339400039f0000000081627691c002a508e4a2507a21380000a846a42d145c443a50ed15a119800008f2286c13a19b021837111372d5904b49852b44a70520451018121d870925e
  | 46 => 0xc4888099cead1b60cdc09851403000fa53418ae80ca8230000000000004ca0fbc00049f846000f80090000a9c01b524500bc0003204bc81a34b80000000046b0c790f94e8444f89184414576390ce7a00000001f54b4a3ef80000000f1d143c193248c9f01e50a20027cb164bdd1f0344c5b500004413e709381e085510000fe70e4077912a87a846b44c630f915733f0d811e0c12001200002750f39000061b00000000000aff206522a0000f8b00011a6335c8d7000000000000002e940003918d8833a824001248ea18f4dac076c9e803c0c023c9000000007900000bad000079b35348ef16e00001bb8d46285c8452f74f310588abe3bac5b101b91fe47880003c3d0a2483c6e32b80000200c7dc0000d054b6528512d89550bf0ef829d837b28587ba3d00e1529ec9eb45c40dc1970e1e0c8431f0241006077d1da165431402989424321314246c70401f82852a7489b3c3851415ecac10d905874908f23407c10221d11c52a382ae30a8eff139cd0c18709de343c05801d0eb919ec6b314f0363436ce130ea00b102dd2cd3b9d00434f41c32170fac42e4c8b279ce0a3bc51d443c92b0235930f31a4ef30674d1d3aac2c136652cb37f4bcf264ca4a47f099d041814302245bc495821b1178d84001424d168c31d0ead2683e54e8616b4c7f3b00f3f3c7c7cf20c0ab4475810e0ad80002e812813574000280915d073000025a12e618d8e4735c80003c14df1000112e0bd890a134ce19000105c173864c1b0899430a03460810000000000014fc000469c0001b8524415548862e7cb8300011b642d474f3e280001528fe13e39026438860f40044dc1ee08f03934a4f22546f213a81e129d4db20ec40004438d37218c92f13cd30421dd17f3d30263000038a34248ee12386160000000000102d2b9000000000002870c583dcc9ac0000ca727f0ac00000d8600009273a885da00000000000cde3a70727241113c4b848c23260bdc36f05650000b15287486d0000d932d180003a244842754da3170c8422d8400000d91ab3644d361750e0826e4d7e27bcef73b7c6df2cb85941464b0139501f40d710430c2d0580a70a13095c67231b0cb04980bef19dc18d1fe02771388fae2eb046a27cc12200009fa24351aa000119507092a01730468179c00008f08711c0cae60054000432400016309691520d8530607bf47a400026288653434959451d17725103bc4a6c6802de438f00007d206240e2151484400011303668a01326c12b4c74c8c26ac00040f8c3635e062a0090c2e29640730dbc65900000004b408a90000f4643bcc7c000015e00007ef12240000000d042c98000235016d39e44e40000a500f4114f00002892514000495503a178825a05fc08111d00f63c08cda23e09b804700ca44203b63f24e5114384040000d45000000028dc9a
  | 47 => 0x262034c1b04bda08e01ed48d477003e064501180aa0000000167000000000001b980000000f9300000004b3c86e00004f000007d13194000251807c48681cd000079e11106f73b7434b0000e4517780000000b3b0000000270019600003350a505f8436080210691f7000126715dc2d644c4ebd00000184308d6a01e83942ef0b5448391f5061c7fd39b80000000b98333c3c932f00000a5442d34f05ea39800003cb00a5310512f1bcc19e3c4cfb219343ac1b300821d7465439543802e887ad16f89c73f0c0c846cc3451a44f9e30306272bc4ecd012c87c15a4b7a49608e719806e43504e5a1c8cd18000057317e88dc45791b40e080000000e8135486754b4475c49e80000c38cab23680000ba00000ad400000000003cd000027f800000002a83e400eb00012aa0de060c024ccbf00002c53208a7f24ec8d10000fe3028800000003cb3d100003b081591c44bd20574000214400015c84830000d7513a08de1d580003a081a20000e39000000026707a54a3468e45f05c6079107f18bc668375c0253ab106f443d3051204ddb4c54cc510c92bb069065624acaf644583433a6092d44e03bb2cb4bea07e04872a985e100484a1085404a092d1c4103093507648f642282fd3fe84f4480cdd5065524d045c29825384a8178c08819c0d7023203e73fac49e24a901c405020947bc1b02c692483db4b1b48e0d1a42212bf01fc8500f28490485c1fe39f8e913d14a143ad44530000c7810d0e700dd80000dace3300009b4265859849288e035b85e90f380001be8a1f15fc5f532880001ce011034640033a582b849ccd954858d4f00010a72d887e92acc8360000bab00000000000f0d00000001ee449b1fb81ba0788b0d439443800012f648f0d2605bc55c056c1234104b171ae8af83e5d17602ccbfb299c00000000001f5c0003064e69000023100011260000000172422d000044c0c1800000000000b4cb8c00005b20e7c4f911dcd4b0000a251c7095c0000a4d000081829a0d633c0cec500010270000d4a0000dba000029e35e87a728b800000012a224c800033c00003ea4b444c244c30608de103a8d493fd0b7c32a8b4807a0b8637b06c937741f22ea887a25cc8df2ddd2b14c3114e2654d171794eee2b60f1c0000b023a540000fe51d927282bc1270bae22ec5b441f524c000000033551232a5c0162abc5630318fdd3a48bf815bc4710c1c4240b101e535905821fec35d274406a19b505537b4bc739
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xf94262a001b130a000b03220915121b9da7801a1d04009aa9969085a8290f219c0800062281161e0780000ca0051e870025801f0e208e9c88902100182489918d178c13998b86a70028800012829901801114a3800a8da524000200159fa6988000230483801701870c400000204000120000302081852224005080051918100182e64a0b73d92520050ea42645c3649480181e64e0d70d92520040fa5c8650d649480182e829d3639865200613a0973d8e619480182e821d3635825200613a0b73d8d609480185b73201635825200607a1373d85609480181e7460e6118252006079d383580609480185b8720d60182520070a5d272580609480144e92e1773582420041ba4a8754d609080103e98dd97494a4100513a4b85dcd609040106e92a1d535824101c172617354c625040103d9810676949410050764c419da525040103d98d0276949410050764f409da5250401a51536043018141006a450d810c06050401a155360430592217249324987149638840103f985d074d952100513a4b85dcd600840182c74209535802100613dcc8254d60084014589754e305802100592249538c1600840705c985cd5398a400040fa60415da529000141d931057694a400040fa63405da529000141d93d017694a400040fa60765d2525000103f985d074596200048b2488654c6448001a0c63209531912000583a4b75d93634800160e92dd464d8d206cc93a4a8714b6348001a246420953d852000691d8c8254f614800126696209531852000689d908254c6148001a2464209531852000691d8c8254c6148001a44632095318520006919cc8254c6148001a45732095318520004992498590c6148001a44831494218520005a124d421086148001a258414832185200059164c520c861480016449254e301852000499249850c061480016449254c30185200061918682dd541480014e296dc47048520005192497518640480014679754c61881200051aa4b53dd9200800186882ddb7548020007121cf769492008001c2b76dd252480200070add8749492008001c4b76dce524802000718dda52dc5200800156297948714802000718dda521c52008001d20749487148020007501ce521c5200800182c742095358a1000613dcc8254d6284001a495320131189100068554d810c16404001864712095358810006191c48754d6204001a45536043058810
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc81611931483218520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124c
  | 9 => 0x94c
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124d
  | 13 => 0x124e
  | 14 => 0x138c
  | 15 => 0x138d
  | 16 => 0x138e
  | 17 => 0x8c
  | 18 => 0x8d
  | 19 => 0x8e
  | 20 => 0x128c
  | 21 => 0x150c
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128d
  | 26 => 0x128e
  | 27 => 0x150d
  | 28 => 0x150e
  | 29 => 0xa0c
  | 30 => 0xa0e
  | 31 => 0x130c
  | 32 => 0x130e
  | 33 => 0x20c
  | 34 => 0x20d
  | 35 => 0x20e
  | 36 => 0x154c
  | 37 => 0xb0c
  | 38 => 0xb0d
  | 39 => 0xb0e
  | 40 => 0x140c
  | 41 => 0x140d
  | 42 => 0x140e
  | 43 => 0x154d
  | 44 => 0x154e
  | 45 => 0xb8c
  | 46 => 0xb8e
  | 47 => 0x148c
  | 48 => 0x148e
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0x160c
  | 52 => 0x160e
  | 53 => 0x164c
  | 54 => 0x164d
  | 55 => 0x94055
  | 56 => 0x94056
  | 57 => 0x95254
  | 58 => 0x94054
  | 59 => 0x8a
  | 60 => 0x128a
  | 61 => 0x155254
  | 62 => 0x154056
  | 63 => 0x154054
  | 64 => 0x164a
  | 65 => 0x44a
  | 66 => 0x164054
  | 67 => 0x5654
  | 68 => 0x124956
  | 69 => 0x124954
  | 70 => 0x164954
  | 71 => 0x95654
  | 72 => 0x12ca
  | 73 => 0x10a
  | 74 => 0x130a
  | 75 => 0x134a
  | 76 => 0x139256
  | 77 => 0x139254
  | 78 => 0x21256
  | 79 => 0x21254
  | 80 => 0x155256
  | 81 => 0x165254
  | 82 => 0x125654
  | 83 => 0x165394
  | 84 => 0x139654
  | 85 => 0x98096
  | 86 => 0x99514
  | 87 => 0x9294
  | 88 => 0x98094
  | 89 => 0x99294
  | 90 => 0x9514
  | 91 => 0x128096
  | 92 => 0x129514
  | 93 => 0x8994
  | 94 => 0x128094
  | 95 => 0x150094
  | 96 => 0x150096
  | 97 => 0x20094
  | 98 => 0x20096
  | 99 => 0xb1514
  | 100 => 0x140094
  | 101 => 0x140096
  | 102 => 0x155514
  | 103 => 0x164094
  | 104 => 0x9654
  | 105 => 0x128994
  | 106 => 0x128996
  | 107 => 0x150996
  | 108 => 0x150994
  | 109 => 0x99554
  | 110 => 0xb0994
  | 111 => 0xb0996
  | 112 => 0x98b14
  | 113 => 0x154994
  | 114 => 0x154996
  | 115 => 0xd0996
  | 116 => 0x160996
  | 117 => 0x164994
  | 118 => 0x99654
  | 119 => 0x151296
  | 120 => 0x151294
  | 121 => 0x21294
  | 122 => 0x21296
  | 123 => 0x141294
  | 124 => 0x141296
  | 125 => 0x165294
  | 126 => 0x129654
  | 127 => 0xb1516
  | 128 => 0x155516
  | 129 => 0xd1516
  | 130 => 0x161516
  | 131 => 0x165514
  | 132 => 0x151654
  | 133 => 0x130a16
  | 134 => 0x130a14
  | 135 => 0xb8a16
  | 136 => 0xb8a14
  | 137 => 0x44d
  | 138 => 0x164a14
  | 139 => 0xa1654
  | 140 => 0x149316
  | 141 => 0x149314
  | 142 => 0x131494
  | 143 => 0x131496
  | 144 => 0x161316
  | 145 => 0x161314
  | 146 => 0x131614
  | 147 => 0x131616
  | 148 => 0x165314
  | 149 => 0x131654
  | 150 => 0xa4d
  | 151 => 0x198d
  | 152 => 0xb0214
  | 153 => 0xb0216
  | 154 => 0xb1554
  | 155 => 0xd0216
  | 156 => 0x160216
  | 157 => 0x164214
  | 158 => 0x21654
  | 159 => 0x154b16
  | 160 => 0x154b14
  | 161 => 0x164b14
  | 162 => 0xb1654
  | 163 => 0x155416
  | 164 => 0x155414
  | 165 => 0xd1416
  | 166 => 0x161416
  | 167 => 0x165414
  | 168 => 0x141654
  | 169 => 0x165554
  | 170 => 0x155654
  | 171 => 0x160b96
  | 172 => 0x160b94
  | 173 => 0xb9614
  | 174 => 0xb9616
  | 175 => 0x164b94
  | 176 => 0xb9654
  | 177 => 0x194a
  | 178 => 0x14cd
  | 179 => 0x2cd
  | 180 => 0x165494
  | 181 => 0x149654
  | 182 => 0x160d16
  | 183 => 0x160d14
  | 184 => 0xd1614
  | 185 => 0x164d14
  | 186 => 0xd1654
  | 187 => 0x188e
  | 188 => 0x15cd
  | 189 => 0x165614
  | 190 => 0x161654
  | 191 => 0x40e
  | 192 => 0x1a4a
  | 193 => 0xeca
  | 194 => 0x4954
  | 195 => 0x5514
  | 196 => 0x5554
  | 197 => 0x5814
  | 198 => 0x5994
  | 199 => 0x4956
  | 200 => 0x5556
  | 201 => 0x5696
  | 202 => 0xca
  | 203 => 0x14a
  | 204 => 0x94454
  | 205 => 0xc092
  | 206 => 0x10092
  | 207 => 0x44c
  | 208 => 0xecd
  | 209 => 0x1a4d
  | 210 => 0xc112
  | 211 => 0x4955
  | 212 => 0x1649809c
  | 213 => 0x9296
  | 214 => 0x129516
  | 215 => 0x8996
  | 216 => 0x3cd
  | 217 => 0x98454
  | 218 => 0x44994
  | 219 => 0x98414
  | 220 => 0x40c
  | 221 => 0x99556
  | 222 => 0x983d6
  | 223 => 0x99616
  | 224 => 0x128216
  | 225 => 0x130416
  | 226 => 0x3c995
  | 227 => 0x45414
  | 228 => 0x140454
  | 229 => 0x141554
  | 230 => 0x140414
  | 231 => 0x141556
  | 232 => 0x1403d6
  | 233 => 0x141616
  | 234 => 0x74a
  | 235 => 0xb8416
  | 236 => 0x3d415
  | 237 => 0xd0454
  | 238 => 0x15d655
  | 239 => 0x15c455
  | 240 => 0xd0414
  | 241 => 0x443d5
  | 242 => 0x1643d5
  | 243 => 0x3d655
  | 244 => 0x99516
  | 245 => 0x1503d6
  | 246 => 0x151616
  | 247 => 0xb1556
  | 248 => 0x203d6
  | 249 => 0x21616
  | 250 => 0x140216
  | 251 => 0xd0416
  | 252 => 0x45655
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1749
  | 6 => 5669
  | 5 => 4894
  | 4 => 85
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 101)*7) 7
  | 7 => packedAt gbK7 (71709+((h/583+packedAt gbK7 (64713+(h % 583)*12) 12) % 2538)*12) 12
  | 6 => packedAt gbK6 (296669+((h/1889+packedAt gbK6 (272112+(h % 1889)*13) 13) % 6803)*14) 14
  | 5 => packedAt gbK5 (309949+((h/1631+packedAt gbK5 (288746+(h % 1631)*13) 13) % 5873)*14) 14
  | 4 => packedAt gbK4 (6146+((h/28+packedAt gbK4 (5950+(h % 28)*7) 7) % 103)*8) 8
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff00ffffffe01ffe03ffffffcf9f9f8cfe31ff
  | 1 => 0xffff01f803fffffffc03fffff461e3ff23fe3f
  | 2 => 0x7fffe0003ffe03ffffc0f80387e7cf3c3cfcc
  | 3 => 0x7fffffffc00003ffffff0003f807f03fc0ff0
  | 4 => 0x7ffffffffffffc0000000003fff8003fff000
  | 5 => 0xf800000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xc900162b24a10a4a01a51caa818e8d844e10d5
  | 1 => 0x124b0150414a3494a402a1551421223920e62a
  | 2 => 0x4595aa00a27542274ae80e01a85654d2c34b4c
  | 3 => 0x86e6cd9dc8060439f353c0063e807b03b40db0
  | 4 => 0x7f8f1e6f39f9f00606084183f7b8003fbb000
  | 5 => 0xe0c0810700181801838308603ffdffec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37383
namespace PEqualNP.Outside.L_meta_37383
open PEqualNP.Outside.L_meta_37383.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 9 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_64 : Interval s3Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_128 : Interval s3Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_160 : Interval s3Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_192 : Interval s3Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_224 : Interval s3Atlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 227 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs3_4_704 : Interval s3Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_736 : Interval s3Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_800 : Interval s3Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_832 : Interval s3Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_896 : Interval s3Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_928 : Interval s3Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_992 : Interval s3Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1024 : Interval s3Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1088 : Interval s3Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1120 : Interval s3Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1184 : Interval s3Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1216 : Interval s3Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1280 : Interval s3Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1312 : Interval s3Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 (concat bs3_4_928 bs3_4_960)))) (concat (concat (concat bs3_4_992 bs3_4_1024) (concat bs3_4_1056 (concat bs3_4_1088 bs3_4_1120))) (concat (concat bs3_4_1152 (concat bs3_4_1184 bs3_4_1216)) (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312))))))
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
theorem bs3_5_704 : Interval s3Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_736 : Interval s3Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_800 : Interval s3Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_832 : Interval s3Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat (concat bs3_5_96 bs3_5_128) (concat bs3_5_160 bs3_5_192))) (concat (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)) (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 bs3_5_416)))) (concat (concat (concat bs3_5_448 (concat bs3_5_480 bs3_5_512)) (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640))) (concat (concat bs3_5_672 (concat bs3_5_704 bs3_5_736)) (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bgb_4_64 : Interval gbAtlas 4 64 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 85 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_4864 : Interval gbAtlas 5 4864 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4894 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)))) (concat (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)))))) (concat (concat (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))) (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))))) (concat (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)))) (concat (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400))))))) (concat (concat (concat (concat (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))) (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136)) (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296)))) (concat (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456))) (concat (concat bgb_5_3488 bgb_5_3520) (concat bgb_5_3552 (concat bgb_5_3584 bgb_5_3616)))))) (concat (concat (concat (concat (concat bgb_5_3648 bgb_5_3680) (concat bgb_5_3712 bgb_5_3744)) (concat (concat bgb_5_3776 bgb_5_3808) (concat bgb_5_3840 (concat bgb_5_3872 bgb_5_3904)))) (concat (concat (concat bgb_5_3936 bgb_5_3968) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 bgb_5_4128) (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224))))) (concat (concat (concat (concat bgb_5_4256 bgb_5_4288) (concat bgb_5_4320 (concat bgb_5_4352 bgb_5_4384))) (concat (concat bgb_5_4416 bgb_5_4448) (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)))) (concat (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 bgb_5_4768) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))))))))
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
theorem bgb_6_5664 : Interval gbAtlas 6 5664 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5669 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624))) (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))))))) (concat (concat (concat (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520))))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))))) (concat (concat (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)))) (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))))) (concat (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))) (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280)))) (concat (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))) (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664))))))))
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
theorem bgb_7_1728 : Interval gbAtlas 7 1728 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1749 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608))) (concat (concat bgb_7_640 (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 bgb_7_832))))) (concat (concat (concat (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 bgb_7_1056))) (concat (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)))) (concat (concat (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504))) (concat (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)) (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 21, 53)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888eae8e8c8eac8e888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3941132488 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37383.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.or,[3,6]⟩,⟨.and,[1,2]⟩,⟨.and,[2,3]⟩,⟨.or,[4,7]⟩,⟨.or,[1,9]⟩,⟨.and,[8,10]⟩,⟨.and,[4,7]⟩,⟨.or,[0,12]⟩,⟨.or,[11,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132488 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132488 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37383

open PEqualNP.Outside.L_meta_37383 in
theorem PEqualNP.Outside.L_meta_37383 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941132488 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941132488 * 2 ^ 32 + 3939035272) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
