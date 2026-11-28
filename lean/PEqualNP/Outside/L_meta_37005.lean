import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37005.Model
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


end PEqualNP.Outside.L_meta_37005.Model

namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 5, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37005

namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x400025a809184a031c800c7be42bc42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1180c400940418c420ca58a4a0ce14141a7294632e5290298a4985514530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 2 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x3450880008c7a72a0000038000000000b8a181800000491243a980023e004000001580000000108010990000d90000018050000000001280163400500a4000001c00000600003c00013000071600a80200000009000000081020c2000810000000c000ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x30466e0000a29e0a605e06a014007608b20058726a0000002466000016006c180e4400008a0092004a000400003a3e68509c009690648c2036a87c527a0ca600003c22b05400acae321e00000078562c4c628e0000b60086a4001c000042008800003400007e102e9a4e00000028b4aa800070488438405c122a82025a2674001a9894000006040001000203020402000800010006030100000302000001000300010c9f286873d5490edea4a1db14943bba8a87745150ef6a0a1de14143cfa9a87af5250f58a4a1edd4543da28a87bb5050e78a0a1ee141439c282873e5410eeea2a15d145429f2a6653d54ccaeca3995d54732bb28c6575518ca7ca8194f55032b7a92836c525067ca998cf55331b7296636d52cc6dca518db54a319f2a0633d540c67ea890cf15121f2908436e52902daa5205d94640baa8c813d539035ca5206b54a40db28c81b5519027ca1204f54c409f28081ba501027ca9984f55330dc206613f548c278a9184fd51309e2a2616f524c2d8a4985dd4530ba28a613e540c27aa8185b94830b6a906176510c2eaa2186e100309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520bb2884175510827ca9884f553109faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x4080a26e0c01c91485150f2b5214143ca1485050f335114143cc1445050ea46448421c994a51902396510030
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
  | 4 => packedAt s1K4 (2724+((h/30+packedAt s1K4 (2484+(h % 30)*8) 8) % 134)*8) 8
  | 3 => packedAt s1K3 (312+((h/2+packedAt s1K3 (304+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0xfc0ffffe03f81ff83e0fc0ffffc1f01d31fcc
  | 3 => 0xfff03ffffc001fffc00fff03fffe001e3e3f0
  | 4 => 0xf00003ffffffffffffff00003ffffffffc03ff
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x60420808c489082014a12c514610a54c056e15
  | 2 => 0xa496319143922ae58168554d9ad49614d316cc
  | 3 => 0x490c5aa289074d6aac109b652d5ac42963a370
  | 4 => 0x8c28a344122461934a5a020831a318b1b801aa
  | 5 => 0xe30c3871c3871dc739ce38e01c210c1fed800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaa0000faaaaaa0faaa0000faaaaaa0faaa0000faaaaaa0faaa0000faaaaaa0faaa0000faaaaaa0faaa0000faaaaaa0faaa0000faaaaaa0faaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xd100000a007cb2a0a013173c456801c4c4ac3a941280e500153200e2420000001e1862934ac900408d1211610c01069cd960031400080c10052400deff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21f721fe21fd21fc21f421ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x6410000000000000070000241e2c2a625b38720000005637514e2600000000004d05000e03000d400000490000000071424f570000000043004b00125c00003b654c0000310c063a2160290000746f276b1c687000002e472d00341400001900000000000035586723636c2f0b53001b000000006600001f00444500330000000a000000160008005500004152004a610000000000000100000004001d2b0000002502001318006a3c6d005f54362017111a3f32395e503e005a15466e69280f732200485930005d000009003d000a000500000000008001000382870002010100800000810288000680000009800300008001805b94a43b6a9487765190eeaa321dd94742baa8e853e5290aeea2a15d14542af298855d5310b3ca6216754c429f29085ae5210a7ca9994f55332bb28e657551ccb5885194fd51329e2a265ac424caeea2995d14532bda826578504cadea4a0db14941daa08833e54cc67aa998db94b31b6a9663b642c87688590cf952219eaa443ac42886eca310cfd51219e2a2435e53086baa610eb10821eb29843d553086eca410f994821f3a1043b642087688410f910821d221043e632087ca6410d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05d94440baa88819e428c338851875c8630ea10c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830cf210619c420c3aca2187554430eb90861d4210c2bca0187694030af29e415d53c83b061904f952209eaa441ac42882eca3105d54620f210c413f5448278a89057d4d20ae29a417751482e8a2906b10820f210841d830082bca7885754f109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x400688070022868092e00a60e42048009e5a6314aac00b004c432c9108514cb284214132a9189411070d5310821a998a42086c56310821e198c42087856310821e194c42087855310821a919132086e0604c8219918951103844208630c3551520c21d6510830d1549510c2556508430e1108210c3244294620c99502188388420c020f0084300822c6255010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xa6000a0aeb3188410c857694c4208682ba88410861815944208430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (826+((h/15+packedAt s2K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 205)*8) 8
  | 3 => packedAt s2K3 (952+((h/8+packedAt s2K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 3 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 4 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 3 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 4 => 0x68b1468912320db34a59019218e59611f40350
  | 5 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800eeaaee00aaaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xe0fff81f81ffffe0f81ffc1ff0f80fffb38ccf
  | 2 => 0xffffffe001ffffff001fffffff000fffc3ff0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126014a690c16315c
  | 1 => 0x4a6450c832930ca05b09650a90d0aa54b284c5
  | 2 => 0x8488a2034524114b04128a552a0144a9415b0a
  | 4 => 0x14d1049260365a729640c219cca58031e80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf38188c608c1ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0eaeae0e0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x100df32dd32
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
  | 4 => packedAt s4K4 (35+((h/1+packedAt s4K4 (32+(h % 1)*3) 3) % 8)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe03ffc07ffc0e0fff07ff07ff07fe01c79e7c
  | 1 => 0x7ffc0ffffffffff03ff81ff81ffffffe78e3ff
  | 2 => 0x7fffffff81ffffffc0001ffffff83fff80ff8f
  | 3 => 0x80000ffffe000fffffffe0001fffc003ff03f0
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1298644714495602cb42a742a7467218c38e3c
  | 1 => 0x429248920910450154a094a090ca4a858a0d5
  | 2 => 0x585089120d224aa540849294d2d2195380570a
  | 3 => 0x5162ca24483a6b39a694c0849ce31063ad03e0
  | 5 => 0x61830c3871c38dce38e71ce70084218376f800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeee0eee0c8c0c8c0eee0eee0c8c0c8c0eee0eee0c8c0c8c0eee0eee0c8c0c8c0eee0eee0c8c0c8c0eee0eee0c8c0c8c0eee0eee0c8c0c8c0eee0eee0c8c0c8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1b5685f3500fd82748e54a83c9802c0440001265888e1e14bbc5c8c01a2888caf007060054743b4129502d30ec580661043a065469f7049b3714000000cc80000001eb1000c0c20906202802810281082c00b0200580bda8287785050eeca221dd54443af29e855d53d0aeca3a15d54742af29c855d5390af4a1215e54242bba8a6574514caf4a0195e54032afa9a835c53506dea4a0db14941bda82837850506bca620d754c41b7a92636c524c67ca818cf55031afa9a435c534867ca810cf55021af298435d53086f4a010de54021afa9a815c53502bca6205754c40b7290816d52102eca2205d544409faa2613c544c2dca4185b548309faa2413c54482bea6905714d20bba8a417451482bca6105754c209f2a6213d54c42bca7885754f10af29c215d53842dca5085b54a10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (718+((h/13+packedAt s5K5 (640+(h % 13)*6) 6) % 49)*7) 7
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffffe03ff8307c1fff87ffff83fe011cfe7c
  | 1 => 0xf81f83ffffffff801f07f8780ffffffe1333ff
  | 2 => 0xffe003ffc1ffffffe007ff800ffc1fffe3c38f
  | 3 => 0x3fffe003ffffff800000fffe003fc03f0
  | 4 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x30c320238411500c83298288e3a1321904563c
  | 1 => 0x5244464490a422820d82c85124c644aa1130d5
  | 2 => 0xa10928890d411534a02513024929195162c30a
  | 3 => 0xc59673122875b9dad6b042448e739063bc03e0
  | 4 => 0x618421c31862e6318c6646700420182dba800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfaeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0faeac8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5001fe54007f55007fc5401ffd4c01fe53007f54c07fc53007fd0c01fe43007f50c01fc4301ffd4805fe52007f54805fc52007fd0805fe42007f50805fc42007fcc805fe32007f4c805fc3201ffd4403fe51007f54403fc51007fd0403fe41007f50403fc41007fcc403fe31007f4c403fc31017fc8403fe21007f48403fc2101ffd4001fe50007f54007fc50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824000ffd0120027fc8090003fd4048009fe2024000ffcc120027fc6090003fd3048009fe1824002ffc8120017f64090013fe2048009f71024004ff08120027d8409000bf82048015ff8824004ff04120027fecb08012ff6584009ff32c2003bf99610027facb08002fd6584009fe32c2004bf19610027fec908012ff6484009ff3242007bf99210027fac908002fd6484009fe3242004bf1921004ffea908003fe5484001feaa42009ff15210027fec708012ff6384009ff31c2000bf98e10027fac708002fd6384009fe31c2004bf18e1004ffea708003fe5384001fea9c2009ff14e10007fe8708003fe4384001fea1c2000ff10e10027fec508012ff6284009ff3142002bf98a10027fac508002fd6284009fe3142004bf18a1004ffea508023fe5284001fea942008ff14a10007fe8508023fe4284001fea142008ff10a10007fe6508023fe3284001fe9942008ff0ca1000dfac308007ff5184003ff28c2001ff5461000ff8a308007ff4184003ff20c2001ff5061000ff88308007ff3184003ff18c2001ff4c61000ff86308007ff2184003ff10c2001ff4861000ff84308012fe6084009ffa842004ff94210027faa108013fc5084009ffa042004ff90210027fa8108013fc4084009ff9842004ff8c210027fa6108013fc3084009ff9042004ff88210027f44108013fd2084001fc9042004ff08210027fe2108013f71084003fd8842004ff04210027f02108003ff65440017fb2a2000dfd9510004feca8801bfe65440077f32a2000ff59510005faca8801bfc65440077e32a2000df1951001cf8ca88003ff64440017fb222000ff9911003dfcc888003fd64440017eb222000ff1911003df8c88801bff5444001ff2a22000ff55110037f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c68801bff5344001ff29a2000ff54d10037f8a688003ff4344001ff21a2000ff50d10007f88688003ff62440017fb122005ff98910015fcc488003fd62440017eb122005ff18910015f8c48801bff524400bff2922000ff5491002ff8a488003ff424400bff2122000ff5091002ff88488003ff324400bff1922000ff4c91002ff86488012ff6144003ffa8a2001ff9451000feca288007fd5144001faa8a2001ff1451000ffe8288007fe4144003fb20a2001ff50510007ea8288007fc4144003ff98a2001ff8c51000ffa6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022006ffd4110027fca088003fd5044009fe2822000ffd0110027fc8088003fd4044009fe2022000ffcc110027fc6088003fd3044009fe1822005ffc8110027fc4088003fa2044001fe9022000fe48110027f84088007ff1044003fd8822004ff84110027ec2088013fc1044009fa0822001fe04110
  | 1 => 0x3fd320c021fe1906004ffd8430027fcc218006fe610c009feb086000bf58430027f8c218012fc610c023ffa88600eff94430007faa21803bfc510c001ffa08600eff90430007fa821803bfc410c021ff988600eff8c430007fa6218043fc310c01fff908600eff88430007fa421803bfc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba6018003f9300c009ff9006004ff08030027fe2018013fc100c009ffb2c4004bfd9620027fccb1000efe6588009feb2c4000bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc91001efe6488009feb244000bf59220027f8c910012fc648801bffaa44000ff95220007faa910037fc5488009ffb1c4004bfd8e20027fcc710002fe6388009feb1c4000bf58e20027f8c710012fc638801bffa9c4000ff94e20007faa710037fc5388001ffa1c4000ff90e20007fa8710003fc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a20017fc851000bfd4288005fe2144002ffcca20017fc651000bfd3288005fe1944004ffd8620027fcc310006fe6188009feb0c4000bf58620027f8c310012fc618801bffa8c400cff94620007faa310033fc5188001ffa0c400cff90620007fa8310033fc4188001ff98c400cff8c620007fa6310033fc3188005ff90c4002ff88620017fa431000bfc21880097f3044004ffd4220027fca110013fd5088009fe2844004ffd0220027fc8110013fd4088009fe2044004ffcc220027fc6110013fd3088009fe1844004ffc8220027de411000bfb2088009fe1044004fe08220027fe2110013fc1088001ffb2a4000bfd952005ffcca9000efe6548001feb2a4000bf5952005ff8ca9000efc6548001ffb224000bfd91200077ec890002bf6448001ff3224007bf99120007fac890002fd6448001fe3224007bf1912000778c890002bc6448017ffaa24000ff95120007faa89002ffc5448001ffb1a4000bfd8d20007fcc690002fe6348001feb1a4000bf58d20007f8c690002fc6348017ffa9a4000ff94d20007faa69002ffc5348001ffa1a4000ff90d20007fa8690003fc43480097fb124002ffd4920017fca49000bfd5248005fe2924002ffd0920017fc849000bee4248005fea124000fb50920017f8849000bff3248005ff1924002fb8c920017fa6490003ed3248005fe1924000ffd8520005fec29002bfe61480037f30a4000ff58520057f8c290006fc6148017ffa8a400aff94520007faa29002bfc5148001ffa0a400aff90520007fa829002bfc4148001ff98a400aff8c520007fa629002bfc3148005ff90a4002ff88520017fa429000bfc21480057fb02400bffd4120027fca090003fd5048009fe2
  | 2 => 0x30027f8c918012fc648c02fffaa46000ff95230007faa91805ffc548c0017eb1c6017ffd4e30007fca718003fd538c02ffe29c6000ffd0e30007fc8718003fd438c001fe21c6004ffd8a30027fcc51800afe628c009feb146000bf58a30027f8c518012fc628c02fffa946016ff94a30007faa51805bfc528c001ffa146016ff90a30007fa851805bfc428c001ff9946016ff8ca30007fa651805bfc328c009ffb0c6004ff9863000dfcc318013fd618c0017eb0c6004ff18630025f8c31805fff518c02bff28c6000ff546300aff8a318003ff418c02bff20c6000ff506300aff88318003ff318c02bff18c6000ff4c6300aff8631805bff218c02bff10c6000ff486300aff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230007f66118013ff208c009fe1046004ffc4230027f82118003ff654c0017fb2a6000dfd9530004feca98053fe654c0077f32a6000ff59530005faca98053fc654c0077e32a6000df1953001cf8ca98003ff644c0017fb226000efd91300057ec898003fe644c00f7f3226000ff59130005fac898003fc644c00f7e3226000ef1913000578c898053ff544c001ff2a26000ff551300a7f8a898053ff534c001ff29a6000ff54d300a7f8a698003ff434c001ff21a6000f790d30007fa8698003dd434c001fe21a6000ffd8930005fec49804ffe624c0057f3126000ff5893009ff8c49800afc624c029ffa926013ff94930007faa49804ffc524c001ffa126013ff90930007fa849804ffc424c001ff9926000f7cc93009ffc6498003fd324c001ee9926013ff0c930007fec298002ff614c025ff30a6001bf98530007fac29804bfc614c0037e30a6014ffd4530097fca298003fd514c025fe28a6000ffd0530097fc8298003fd414c025fe20a6000ffcc530097fc6298003fd314c025fe18a6013ffc8530097fc4298003fd214c025fe10a6014ffd4130027fca098003fd504c009fe2826000ffd0130027fc8098003fd404c009fe2026000ffcc130007f66098013fe304c009ef1826013ffc8130027f8409804bff104c009fe0826004ffd9430025feca18013fe650c0077f3286004ff59430005faca18013fc650c0097e3286004ffd9030025fec818013fe640c00f7f3206004ff59030005fac818013fc640c0097e3206011ffd5030007fca818003fd540c023fe2a06000bf98c3008ffea618043fe530c001fea986010ff14c30007fe8618043fe430c001fea186010ff10c30027fec418013fe620c0057f3106004fb98830015dcc418013fd620c0017eb106004fb58830005dac418013fc620c0097e3106011ffd483007ffca418003fd520c01ffe2906000ffd083007ffc8418003fd420c01ffe2106010ffcc83007ffc641800
  | 3 => 0xf10a8000ff485400f7f842a0083ff5050009ff2828000ff54140027f8a0a001fff405000ffda028004ff901400277c80a007fff2050009fe102801effc4140027f820a0013ff65100097fb288004ff9944001dfcca200137e65100073f3288004ff59440005faca200137d65100013eb288004ff19440025f8ca2001efe641000fffaa08007ff9504003ffaa82001ffc5410009ffb188004ff98c40005fcc620013de63100016f3188004ff58c40005fac620013dd63100016eb188004ff18c400effea620003fe5310001fea98801dff14c4003ffe862001ffe4310001df2188007ff50c4003ff8862001fbc4310009ffb108004ff98840015fcc420013ee6210005773108004ff58840005fac420013ed621000176b108004ff18840025f8c420077ff5210039ff2908000ff548400e7f8a42001fff421000fff210801cef9084003ffa842001ffc421000fde2108000ffcc8400e7fc6420003fd3210039fe1908004ffd8440027fcc220006fe6110009fb3088001bd98440027fac220002fd6110009fab088000bd58440027f8c220012fc611003bffa88801bff94440007faa22006ffc511000fffa088007efd044003ffc822001ffd4110001dea088007ff10440007fe622006ffe3110001fe988801bff0c4400e7fe422006ffe2110001fe908801bff08440025fcc020013ff5010009ff2808004ff54040027f8a020013ff4010009dfa008004ff90040027f48020013fd4010009dea008007fe50040027fe4020013fc2010009ff8808004ff04040087fecb98002ff65cc035ff32e6003bf99730007facb98002fd65cc021fe32e6003bf19730087fec998002ff64cc001ff3266007bf99330007fac998002fd64cc021fe3266007bf193300d7fea998003fe54cc001feaa6601aff153300d7fea798043fe53cc001fea9e6010ff14f30007fe8798043fe43cc001ef21e6000ff50f30007ba8798043fc43cc021ffb166019ff98b30015fcc598003fd62cc0017eb166010ff18b30015f8c59806bff52cc033ff2966000ff54b300cff8a598003ff42cc033ff2166000ff50b300cff88598043ff32cc001ef9966019ff8cb30007fa6598003dd32cc021fe1966010ffd87300c7fcc398006fe61cc001feb0e6000bf58730087f8c398006fc61cc035ffa8e6018ff94730007faa398063fc51cc001ffa0e6018ff90730007fa8398063fc41cc021ff98e6018ff8c730007fa6398043fc31cc033ff90e6018ff88730007fa4398063fc21cc035ffa866004ff94330007faa198013fc50cc001ffa066004ff90330007fa8198013fc40cc033ff9066004ff083300c7fe2198013fc10cc009ffb2c6004bfd9630027fccb1800efe658c009feb2c6000bf59630027f8cb18012fc658c009ffb246004bfd9230027fcc91801efe648c009feb246000bf592
  | 4 => 0x1efc65d000fffaa68007ff9534003ffaa9a001ffc54d000fffb1e8007ff98f40005fcc7a001ffd63d00017eb1e8007ff18f40137fea7a0003fe53d0001fea9e8026ff14f4003ffe87a001ffe43d000ffea1e8007ff10f4003ffec5a001ffe62d00057f3168007ff58b40005fac5a001ffc62d00057e3168026ffd4b4012ffca5a0003fd52d004bfe2968007ffd0b4003ffc85a001ffd42d000ffe2168000ffccb4012ffc65a0003fd32d004bfe1968007ffd874003ffcc3a0006fe61d000ffeb0e8000bf5874003ff8c3a0006fc61d004dffa8e8024ff94740007faa3a0093fc51d000fffa0e8007ff9074003ffa83a001ffc41d0001ff98e8024ff8c740007fa63a0093fc31d004bff90e8024ff88740007fa43a0093fc21d004dffa868004ff94340007faa1a0013fc50d004bff9068004ff08340127fe21a0013fc10d0009ffb2c8004bfd9640027fccb2000efe6590009feb2c8000bf59640027f8cb20012fc65900017eb248023ffd524003ffca920003fd549000ffe2a48004ffd8e40027fcc720002fe6390009feb1c8000bf58e40027f8c72008fff5390001ff29c8000ff54e4011ff8a72001fff4390001ff21c8000ef90e40007fa872001ffc4390001de21c8004ffd8a40027fcc52000afe6290009feb148000bf58a40027f8c520012fc6290047ffa948022ff94a40007faa52008bfc529000fffa148022ff90a401177c8520003fd429000ffe2148022ef10a40007fe652008bfe3290001fe9948022ff0ca40027fec320013fe61900037f30c8004ff58640005fac320013fc61900097e30c8023ffd464010ffca320003fd5190043fe28c8007ffd06400077e8320087fe4190001fea0c8000ef5064003ff88320003ff3190043ff18c8000ff4c64010ff8632008bff2190043ff10c8000ff4864010ff84320012fe6090009ffa848004ff94240027faa120013fc5090009ffa048004efd024003ff68120013ff2090009fe1048004ffc4240027f82120003ff65500017fb2a8020ff9954001dfccaa0003fd65500017eb2a8020ff1954001df8caa0083ff545000fff2a28000ff5514003ff8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500017e31a8020ffd4d40007fca6a0003fd5350041fe29a8007ffd0d40007fc86a0003fd435000ffe21a8000ffd8940005fec4a007ffe62500057f3128000ff589400fff8c4a000afc6250041ffa92801fff94940007faa4a007ffc525000fffa12801fff90940007fa84a001ffc4250001ff992801fff8c940007fa64a007ffc3250001ffb0a8000bfd85400f7fcc2a0006fe6150001feb0a801eff1854000df8c2a0083ff515003dff28a8000ff545400f7f8a2a001fff415003dff20a8000ff5054003ff882a0003ff315003dff18a8000ff4c5400f7f862a007fff215003df
  | 5 => 0xd21007fc8690803fd4348401fe21a4201bfd8921017fea49080bfe5248405fea924202ff14921017fe849080bfe4248405fea124202ff10921017fe649080bfe3248405fe9924202ff0c92100dfec290807ff5148403ff28a4201ff5452100ff8a290807ff4148403ff20a4201ff5052100ff88290807ff3148403ff18a4201ff4c52100ff86290807ff2148405fb90a4201ff8852100fdc4290807fc2148403f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090812fc6048457ffa82422bff14121017fe409080bfc2048403ff8824201ff0412101dfacb28013ff6494009ff324a007bf99250027fac928002fd6494009fe324a003ffd525001ffca92800ffd5494007fe2a4a004ffd8e50027fcc728002fe6394009feb1ca000bf58e50027f8c72800fff5394007ff29ca000df94e5001ffaa72800ffc5394007be29ca000ffd0e50007fc8728003fd4394001fe21ca004ffd8a50027fcc52800afe6294009feb14a000bf58a50027f8c528012fc6294007ffa94a003dfd4a5001ffca52800ffd5294001bea94a003ff14a50007fe85280abfe4294001fea14a02aff10a50007fe65280abfe3294001fe994a02aff0ca50027fec328013fe61940037f30ca004ff58650005fac328013fc61940097e30ca003ffd465001ffca3280a77e5194007fea8ca003ff1465001ef8a328003ff4194053ff20ca000ff5065014ff88328003ff3194053ff18ca000ff4c65014ff863280abff2194053ff10ca000ff4865014ff84328012fe6094009ffa84a004dfd425001ff6a128013fc5094009fc284a004ffc8250027f84128013ff1094009fe084a004bfd9550007fec8a8002ff6454001ff322a000ff59150007f8c8a801efc6454007ffaa2a003dfd515001ffca8a800ffd5454001beaa2a003ff15150007fec6a8002ff6354001ff31aa000ff58d50007f8c6a8002fc6354007ffa9aa003ff94d5001ffaa6a800ffc5354001ffa1aa000ff90d50007fa86a8003fc4354001ffb12a000bfd8950147fcc4a800afe6254001feb12a028ff18950015f8c4a800fff5254007ff292a003ff5495001ff8a4a8003ff4254051ff212a000ff50950147f884a8003ff3254051ff192a000ff4c950147f864a8003ff61540017fb0aa027ff9855000dfcc2a8003fd615404ffe30aa001bf1855001ffea2a800f7f5154007ff28aa003ff54550006faa2a800ffc5154001ffa0aa027ff90550007fa82a809ffc4154001ff98aa027ff8c550007fa62a809ffc3154051ff90aa027ff88550007fa42a809ffc21540077fb02a003ffd415001ff6a0a8013fe5054009bf282a004ff14150026f8a0a800ff85054051ff902a004ff0815013ffe20a8013fc105400fffb2e8007bfd974003ffccba000efe65d000ffeb2e8000bf5974003ff8cba0
  | 6 => 0x3fea8a8201ff1454100ffe82a081ff74150403ff20a8201ef9054100ff882a0807bc4150403fa20a8201ff8c54100ff862a0807ff2150403ff10a8201ff08541007fec0a0802ff6050401ff3028200ff58141007f8c0a0812fc6050463ffa828231ff14141187fe40a08c3fc2050403ff8828201fdc414100ff820a0843ff65cc4017fb2e622fff9973101dfccb98803fd65cc4017eb2e6210ff1973101df8cb98843ff64cc4017fb266200ff9933103dfcc998803fd64cc4017eb266210ff1933103df8c9988bfff54cc401ff2a66200ff5533117ff8a998806fe63cc45fffa9e6210ff94f31007faa798843fc53cc401ffa1e6210ff90f31007fa8798843fc43cc421ffb16622eff98b31015fcc598803fd62cc4017eb166210ff18b31015f8c5988bfff52cc45dff2966200ff54b31177f8a598803ff42cc45dff2166200ff50b31177f88598843ff32cc401ef996622eff8cb31007fa6598803dd32cc421fe1966201bf5873100ffea398807fe51cc403fea8e6201ff1473100ffe8398807fe41cc403fea0e6201ff1073100ffc6398807de31cc403fb18e6201ff0c73100fb86398807ff21cc45dfb90e6201ff8873100ff84398807f421cc421ffb066200ff98331025fcc198803fd60cc4017eb066210ff1833117ffea1988bffc50cc45dff906622eff0833100ffe2198807fc10cc401ffb2a6200bfd953116ffcca9880efe654c401feb2a6200bf5953116ff8ca9880efc654c401ffb226200bfd9131007fcc89881efe644c401feb226200bf59131007f8c89881efc644c45bffaa26200ff95131007faa8988b7fc544c4037fb1a622dffd4d31007fca698803fd534c45bfe29a6200ffd0d31007fc8698803fd434c401fe21a6200ffd8931005fec4988b3fe624c4057f3126200ff58931167f8c49880afc624c45bffa92622cff94931007faa4988b3fc524c401ffa12622cff90931007fa84988b3fc424c401ff9926200f7cc931167fc6498803fd324c401ee992622cff0c93100dfec298807ff514c403ff28a6201ff5453100ff8a298807ff414c403ff20a6201ff5053100ff88298807ff314c401fb98a6201ff8c53100fbc6298807fc314c403ee18a6201fd0c53100ffe4298807fe214c403fe10a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c0988b7ff504c45bfe282622cffc8131167f84098807ff104c403fe0826200ffd9521005feca908affe65484077f32a4200ff59521005faca908affc65484077e32a4200ffd9121005fec890803fe644840f7f3224200ff59121005fac890803fc644840f7e322422bffd5121007fca890803fd5448457fe2a24200ffd8d21005fec690803fe63484017f31a4200ff58d21005fac690803fc63484017e31a422bffd4d21007fca690803fd5348457fe29a4200ffd
  | 7 => 0x99003fd604c801fe3026404bf181321b7fea0990dbfc504c805ff9026402fbc8132017f840990d7ff104c86bfe0826401bfd9551007fec8a8802ff6454401ff322a200ff59151007f8c8a881efc6454407ffaa2a203ff9515101ffaa8a880ffc5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa200bf18d5101ffea6a880ffe5354401bf29aa203ff54d5101ff8a6a880f7c5354401ffa1aa200ff90d51007fa86a8803fc4354401ffb12a200bfd89511a7fcc4a880afe6254401feb12a234ff18951015f8c4a880fff5254407bfa92a203ff9495101ffaa4a88037d5254407fe292a200ffd09511a7fc84a8803fd4254469fe212a200ffcc9511a7fc64a8803fd3254469fe192a201bfd855100ffea2a880ff75154403ff28aa201df9455100ff8a2a88077c5154403fa28aa201ff9055100ff882a8807fe3154403fe18aa201ffc855100ffc42a8807fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a204bf1815101ffea0a880f7f5054407fe282a234ffc81511a7f840a8807ff1054403fb882a201ff0415103ffecba081eff65d040fff32e8203bf9974103efccba080e7e65d040ffeb2e8200bf5974103efacba08027d65d040ffe32e8207bf1974100dfcc9a081fff54d040fff2a68207ff5534103ff8a9a081fff63d040fff31e8200bf98f4103ffac7a0802fd63d040ffe31e8233ffd4f41007fca7a0803fd53d0467fe29e8207ffd0f4103f7e87a081ffe43d040ffea1e8200ef50f4103ff887a081fff62d040fff3168202bf98b4103ffac5a0802fd62d040ffe3168202bf18b4119ffea5a08cbfe52d0401fea968232ff14b4103ffe85a081fbf42d040fff2168207ff50b410077a85a081ffc42d0401ff9968232ff8cb41007fa65a08cbfc32d04037eb0e8201ffd474100ffca3a0807fd51d0403fe28e8201ff9074100f7c83a0807f641d0403fe20e8201ef1074100ffc63a0807fc31d0403ff90e8201ff8874100ff843a081fff60d040fff3068204bf9834103ffac1a0802fd60d040ffe3068233ffd434119ff8a1a08cbff20d0465fe1068201ffc434100ff821a0803ff65504017fb2a8231ff9954101dfccaa0803fd65504017eb2a8231ff1954101df8caa0806ff6450463ffaa28207ff95141007faa8a081ffc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d4118ffea6a0803fe5350401fea9a8231ff14d4103ffe86a0803bf4350401ff21a8200ff50d410077a86a081ffc4350401ffb128200bfd8941187fcc4a080afe6250401feb128230ff18941015f8c4a08c7ff5250461ff2928200ff54941187f8a4a081fff4250401dfa128230ff90941007fa84a0803bd425040ffe2128200ffcc941187fc64a0803fd3250461fe1928201bfd854100ffea2a0807fe515040
  | 8 => 0xfc43421dff821a1003ff65508017fb2a843aff9954201dfccaa1003fd65508017eb2a843aff1954201df8caa100aff6450875ffaa28407ff95142007faa8a101ffc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d421d7fea6a1003fe5350801fea9a843aff14d4203ffe86a1003fe4350801fea1a8407ff10d42015fec4a100bff5250805ff2928402ff54942017f8a4a100bff425080ff7a128402ff909420177c84a100bfc4250805de2128402fb10942017fc64a100bfc3250801ffb0a8400bfd85421cffcc2a1006fe6150801feb0a8439ff1854200df8c2a10ebff5150873ff28a8439ff145421cffc82a101ffc4150873ff18a8439ff0c542017fe42a100bfe2150805fe10a8400ffd8142005fec0a1003fe6050801feb028400ff18142025f8c0a10ebff5050875fe2828402ffc8142017de40a100bfc2050873ff8828439ff04142087fecb99002ff65cc871ff32e6403bf99732007facb99002fd65cc821fe32e6403bf19732087fec999002ff64cc801ff3266407bf99332007fac999002fd64cc821fe3266407bf193321c7fea999003fe54cc801feaa66438ff15332015fcc7990e3ff53cc821ff29e6400ff54f32087f8a799003ff43cc801efa1e6410ff90f32007fa8799043fc43cc801ee21e6402bf58b32017fea59900bfe52cc805fea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b86599043ff61cc86fff30e6401bf98732007fac399002fd61cc821fe30e6401bf187321c7fea3990dffe51cc86ffe28e6437ff907321bff883990dffe31cc821fe18e6402ffc8732017fc439900bfc21cc821ffb066400ff98332025fcc199003fd60cc8017eb066410ff183321c7fea1990e3fc50cc805ff9066402ff083321bffe21990dffc10cc801ffb2a6400bfd9532006feca990027f654c86dff32a6403bf99532007faca99002fd654c86dfe32a6403bf19532006f8ca9900e7c654c801ffb226400bfd9132007fcc89901efe644c801feb226400bf59132007f8c89901efc644c86dffaa26400ff95132007faa8990dbfc544c8057fb1a6436ffd4d32007fca699003fd534c86dfe29a6400ffd0d32007be8699003fe434c801fea1a6400ff10d32007b8869900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017fa849900bfc424c805ff9926400fbcc932017fc649900bde324c805fe1926402f70c932017d86499003ff614c8017fb0a6400fdd8532005eec2990d7fe614c8037f30a6400ff585321aff8c299006fc614c801fa30a6401bd185321b7fea2990d7fe514c86bfe28a6435ff905321aff882990d7fe314c86bfe18a6402ffc8532017fc429900bfc214c801ffb026400bfd8132007fcc0
  | 9 => 0xc83ff18a8641ff0c543217fe42a1907fe2150c83fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143025f8c0a190fff5050c87fe2828642ffc8143217f840a1907ff1050c83fe0828610ffd944303dfeca2181ffe6510c077f3288607ff59443005faca21843fc6510c0f7e3288607bf9904303ffea82181ffe5410c0ffeaa08607ff15043005fcc621903ff5310c21ff2988600ff54c43087f8a62181fff4310c0fdfa188610ff90c4303fbc862181ffd4310c01dea188607f750c43087fec42181ffe6210c057f3108607ff58843005fac421843fc6210c057e3108640ffd48431fffca4218fffc5210c0fff2108607ff108431fffc6421843fc3210c21ffb088607ff9844300dfcc22181ffd6110c017eb088610ff1844300df8c221903ff5110c7dff288863eff1444303ffc822181ffc4110c7dff1888610ff0c4431fffe42218fbfe2110c7dfe1088610ffd804303ffcc021812fe6010c0ffeb008600bf58043087f8c021903ff5010c81fe280863fffc80431fff840218fbff1010c7dfe0808602bfd9552007fec8a9002ff6454801ff322a400ff59152007f8c8a901efc6454807ffaa2a403dfd515201ffca8a900ffd5454801beaa2a403ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9002fc6354807ffa9aa403ff94d5201ffaa6a900ffc5354801ffa1aa400ff90d52007fa86a9003fc43548057fb12a402ffd495201fdea4a900bfe5254805bf292a402ff14952016f8a4a900bec5254805ff212a402ff10952017fc64a900bfc3254801ffb0aa400bfd85521effcc2a9006fe6154801feb0aa43dff1855200df8c2a900fff5154807bfa8aa403ff9455201ff8a2a90f7fe415487bfe20aa43dff8c5521eff862a900bff2154805ff10aa402ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9012fc6054807ffa82a403ff1415201ef8a0a900bff2054805fe102a43dffc41521eff820a901fff65d080f7fb2e8407ff9974201dfccba101ffd65d08017eb2e8407ff1974203df8cba100afe64d080fffaa68407ff9534203ffaa9a101ffc54d080fffb1e8407ff98f42005fcc7a101ffd63d08017eb1e8407ff18f421e7fea7a1003fe53d0801fea9e843cff14f4203ffe87a101ffe43d080ffea1e8407ff10f42015fac5a100bff52d0805ff2968402ff54b42017f8a5a100bfe42d0805df2168402fb90b42017f885a100bbc42d0805ff1968402ff0cb4203ffec3a101ffe61d08037f30e8407ff58742005fac3a101ffc61d08037e30e843cffd47421dffca3a10effc51d080fff20e8407ff107421dffc63a10effc31d0805ff90e8402ff88742017f843a101fff60d080fff3068404bf9834203ffac1a1002fd60d080ffe306843cffd43421e7f8a1a100bff20d0805fe106843bf
  | 10 => 0xa6a980ffe5354c01bf29aa603ff14d5301ef8a6a980fdc5354c01ffb12a600bfd895325ffcc4a980afe6254c01feb12a64bff18953015f8c4a980fff5254c07ff292a603ff1495325ffc84a992ffc4254c97ff192a64bff0c953007fec2a9802ff6154c95ff30aa601bf98553007fac2a992bfc6154c037e30aa603ffd455301ffca2a980ffc5154c95ff20aa64aff10553257fc62a992bfc3154c97ff90aa64aff88553257f842a9803ff6054c017fb02a600ff98153007fac0a9803fc6054c097e302a603ffd415301ff8a0a992fff2054c97fe102a64affc4153257f820a981fff65d0c0f7fb2e8607ff9974301dfccba181f7e65d0c073f32e8607ff59743005facba181f7d65d0c013eb2e8607ff1974303df8cba181fff54d0c0fff2a68607ff5534303ff8a9a1927ff53d0c01ff29e8600ff54f4324ff8a7a181fff62d0c0fff3168602bf98b4303ffac5a1802fd62d0c0ffe3168602bf18b4324ffea5a1923fe52d0c91fe2968607ff90b4303ff885a1923fe32d0c91fe1968607ffd874303ffcc3a1806fe61d0c0ffeb0e8600bf5874303ff8c3a1806fc61d0c93ffa8e8647ff9474323ff8a3a181ffe41d0c0ffe20e8647ff8c74323ff863a1923ff21d0c8fff10e8647ff0874303ffec1a181ffe60d0c097f3068607ff58343005fac1a181ffc60d0c93ffa868649ff14343247fe41a1923fc20d0c8fff8868647ff04343087fecb21802ff6590c8dff32c8603bf99643007facb21802fd6590c21fe32c8603bf19643005fac92191bff5490c0fff2a48600ff5524303ff8a92181efe6390c8dffa9c8610ff94e43007faa721843fc5390c0fffa1c8600efd0e4303fbe8721843ff6290c8bff3148602bf98a43007fac521802fd6290c21fe3148602bf18a43237fea521917fe5290c8bfe2948645ff90a4303ff88521917fe3290c21fe1948610ffd8643227fcc321806fe6190c01feb0c8600bf58643087f8c321806fc6190c8dffa8c8644ff94643227f8a321913fe4190c0ffe20c8644ff8c643087f86321917ff2190c89ff10c8644ff08643087fec121803fe6090c097f3048600ff58243005fac121843fc6090c8dffa848646ff1424322ffe4121917fc2090c89ff8848644ff04243007fecaa1802ff6550c87ff32a8603bf99543007facaa1802fd6550c87fe32a8603bf1954321ffea8a181ffe5450c01feaa28607ff1514321ffea6a1803fe5350c01fea9a8643ff14d4303ffe86a181fdf4350c01ff21a8600ef90d43007fec4a1802ff6250c85ff3128602bf98943007fac4a190bfc6250c057e3128643ffd4943217fca4a190bfc5250c85ff2128607ff10943217fc64a190bfc3250c01ffb0a8600bfd854320ffcc2a1806fe6150c01feb0a8641ff1854300df8c2a190fff5150c83ff28a8641ff1454320ffc82a181ffc4150
  | 11 => 0x2d00400800000a00102100400000900300d00300302600400600700000000000800000a00c00000100800700000300000100500000100000700000201403000400000200100700b00000000000301dfacb2a01efe649500fffaa4a807dfd525401f7ea92a00f3f549500ffe2a4a807ef1525403ffec72a01ffe63950017f31ca807ff58e54005fac72a01ffc6395007ffa9ca803ff14e5403ffec52a01ffe62950057f314a807ff58a54005fac52a01ffc62950057e314a803ffd4a5401ffca52a00ffc529500fff214a807ff10a5428ffc652a147fc329500fffb0ca807ff9865400dfcc32a01ffd61950017eb0ca807ff1865400df8c32a00fff5195007ff28ca803ff1465403ffc832a01ffc41950a1ff18ca850ff0c65428ffe432a143fe21950a1fe10ca807ffd825403ffcc12a012fe609500ffeb04a800bf5825403ff8c12a00fff5095007fe284a851ffc825428ff8412a143ff10950a1fe084a807bfd955401dfec8aa00fff5455007dfaa2a807ff9515403efca8aa01ffc545500fbe2a2a803ef15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa002fc6355007ffa9aa803ff14d5401ef8a6aa003ff62550017fb12a84fff98954015fcc4aa003fd625509ffe312a802bf1895401ffea4aa00f7f5255007ff292a803ff1495427ffc84aa01ffc425509fff192a84fff0c954007fec2aa002ff615509dff30aa801bf98554007fac2aa13bfc61550037e30aa803ffd455401ffca2aa13b7e5155007fe28aa803df14554277fc82aa01ffc415509dff18aa84eff0c55427ffe42aa13bfe215509dfe10aa800ffd8154005fec0aa003fe6055001feb02a800ff18154025f8c0aa00fff5055007bfa82a803ff1415427ffe40aa13ffc205509dff882a84eff0415401dfacb29843ff6494c01ff324a607bf99253007fac929802fd6494c21fe324a603ffd525301efea92980ffe5494c07feaa4a600df5525301ff8a92980efe6394c07ffa9ca603dfd4e5301fbea72980f5f5394c21fe29ca603f714e53087fec529937fe6294c057f314a600ff58a53005fac529843fc6294c057e314a603ffd4a5301ffca5299377e5294c07fe294a603df14a5326ffc8529937fc4294c9bff194a610ff0ca53087fec329933fe6194c037f30ca600ff58653005fac329843fc6194c037e30ca603ffd465301efea32980ffe5194c07fe28ca64cff90653267f88329933fe3194c21fe18ca64dffc8653267fc4329933fc2194c21ffb04a600ff98253025fcc129803fd6094c017eb04a610ff1825301ffea12980ffc5094c07be284a64dffc825326ff84129933ff1094c99fe084a603bfd9553007fec8a9802ff6454c01ff322a600ff59153007f8c8a981efc6454c07ffaa2a603ff9515301ffaa8a980ffc5454c077fb1aa603ffd4d5301fbe
  | 12 => 0x500000100000100200000c00100700000000500000b00000000400700800000400200000100500000800000602400000700000700700000100600000100500100500300400200000402000c00000000200a00a00400100000402701000000200100000800c00300300e00000f00700100000000000102d00100900000000d00000400000100100000000200500000600300000400900501600000200000000100000002100301000300b00000800200200000600200400000b00400000100600900400c04200900300400000600200200700200001400000500300000100900600200b00000800100600200701000200000200500100c00302a00000000100500900000000200101a00b00000700800000b00000100200400100b05a00a00100000200000000200301200101200300400202101c00000e00200100100000900d00000700300000400000000500500800400600600400d00000400100b00200100700301a00e00500c00100200600300800104d00100500500a00400000400000000500100000000100100700000b00100d00100000300001300000200200800100100700201500600000000400800300100000b00100000600e00a00301d00000000300000001b00000000000a00700400100900100100000000201400000800000b00300100800400100500000000000200500d01300401900100400a00000200401500400200100700700500000000000400000100100b00e00200003000100000201200401700c00400800200000300400000800100000000100400201b00000801b00000100000000a00200000000100200000202900600200100501700c00300200100100200500900101400400000d00600000000100001100200201600000400d00b00000000200800300300e00100200000400700b00c00f00100a00000200100000400900000101700000b00f00900400100001600000000600200002000300100801100100001d00000000000000000100000100100301800f00800100f00401500000000601000f00000500300d00000700000000000000100000000000000200000200004500b00a00e00700000800100000000200100a03000400100600300e00000700600000c01000200100000600200c00000200100000100100100b00000800100700300800500000400000100400501600400600300000101500000000400000600000001600300000100000100000400900100500a00300100000100100200000200200900000000000700400200200500102500300000601b00000701501400b00400001900400600701700900100900500000f00000100300000101900e00b00401002400100000200a01000000000100000000200200000b01400100400e00401900601a00000100000f000006002003041001012
  | 13 => 0x90628600000007691450f18fb600016e87e000000000027240008304dd244c28030f3be2924c7c00049c00000000003d280000005df0001bc0a841f71e589f400005300007b12985890fa800027e05727526140003142fd1a2cf2a3e027804f413c8714b08afc89a73a00019e400000019685608d200041c8da8de615c4b6046885e45e0e0885923497c000123c00027b0000d9800015e4b2000046000000005bcef40001ef000000000045b15d52924053818cfc7ae32b20a9a68b1e6b143287e8d7c59d237205428a12f20fa76082c4f62698f05498142330813484a20d0e99a100006e951225710127eb00001bc48a7072818000b688071c8007861400000000000005f41449ccc7860410930f512e20001e6a30c00000018618492b22e40001b9d41631d240a168d9a12018b1a30d565e102a90a81cc4463d3a398a7429044e808400095827d8454d026ee4338000fe695f1c18000dee62d0ff87949be3f90e11f4542a22742c119029084f4b40000a4c34a08e192c5083812d100080007c407480243948780001ebc59c8bf060a1405d2466237a0fc8ee0003910000e48257124a6f4f6883736019bd0982364391c6d2fc17d35a894400000004803300008e20000000f506ae3dfa608000000000000050474e44e00007c600028e906cea80003f60b68ebe9f417990503063da24c27ecdb433000021b13b206222a90488427fb00007441a28820000f208f431100c8f5845a8e5101a09c0bc1f12da8f404c06011e005b12723be00025e0d1214c0001bfc00023a000243c00000018380006129a9000070000031900000283089422b90e4837055a03413a40000003f88000c427492c514d53d20fc2688a14bd600000020bcdcc99f0560a01390000000197d1e469100015fc9d60004ab9030c7246b000045837c27133d000000000000011800008362941790b567b74a51a60dc82ad0ad9188740a393d683011b215600011c522c00041e8000ee42833e10000f4c8e03ac00013ec0000e327311d272e4f7025c55845229c0aa874e0b94e69bf40006290000c7800000000013800006044b7800000029821690a43a025046800002fc00021c132431400000000000005080000b2c00001800000800600f00a00600d00000600001700101400200700500000200600000100200000100100900200a00000d00800000800400800001400700000600700200600900200000000901800200000200100400000000000c00003f00400800000100400000000000400000000200100d01000600000100b02800300000600100300200e00200100000f00400200300000200600000400500600000700100100300000100000200000000d00600e00002300200100700300600200c00600a00100600300800500200100700200000100b0040020000010040070
  | 14 => 0x851c7dc45629c8b0cbf67cb0f5242927c3563d1935c0007be0c40000000000333800000000000021e83be3ed0f400000002f939e8ca04502700000dc800000038f0000aee664000027124e9c519c80010540c511020d0000a483c2a6186e64d509286607045813b090685464f31be092800016729117d8000000266a3900002e04ee1e0c93e000250000111c8213aa86dc00000000025a80000005170000000361282800000025200016152661292c60710dc01b90000f1c87218600a0e8ccfc7c64c999c415650e16914788a07e8188139483a6a842a99cd1d63581d8207ca306d41aa24b94121a1459004c2668b80f7179c670000525100c0008dc0001bc4794000000000081c00000025401b84ee253a8344829621898044cf82d030e828c9484f13f200010588903f710f830a53312589f0e406ea1db800093a46a2240c947980db0d702753105d12e18478060a1e17e19310ee82e00b036462a3783fea8f8bb64a8024253537c5531bf07acda08a83cf1ea8a9c46d1b79a906e20c43708b791fe4a3257a3c0c8a55908983ec0009b70ab80012a635f00009b4000000435936474c10f29ba03c32a7da48b81d943a20a17800008b01bd0f21a9c05245a0000000bea00017394501bc1531a89f0c000a3b39e05fd20e39a0950a1800072b45a000111886e00015f015287425c1c4cf285043c480f467a18b0000000a340003469a7ce90a46000000141e5ee11d92a8b6000051101993ce7e7000264831800000e0000fa009b000091000050635982c51028fa155a4d00009aa000280101c2a8000000117c000000252c1444db08c219000000000000000009830720f3c47066a3512934d360003d100014840000b717881329ab1178c600ac0f22cd09f844a38a0001244d5e8e30e48a58dba0001610acc0a4320000102072a60d3ba8e586b600005a80013c69c417c0e70e6a9280c89d1023a06d1c4a4253141c80000000aa428c0001b7cb4089b143a26105a9f000028940400a82ec21c008a1602572138e8e92f2db88653cc6ce322097846837f0000000eec00043a9c042f61771111444a400e83e514ac21833b02e0b54d3c8d41ff22bc3c039848591ecf183ea0578000f820002e811f4c7683e00000000984fe00000008404630dfa080bcc6302fe00000008920001eac00000000018dc0100000000000c587574faa1f400000022502c0f088b51e725380000000000000a36a440001cec4fe34c0000a5c62e00000000011de07b49a95b0f0e38e03820980007424ed21fd3822a724606c0fd461400026bcfde6f400028b00004c534c80000007793a580013c265a3a600009e49ec0000000b260004b293289c240b45480001688540000658832550000000000054700000000005ea0420000f4800000011c038a00003526d883c6702920d74000
  | 15 => 0x879000093000000026580006ee6742a5000054a0001d78000d9006300000004a60000001a9822254d13c00000000001d90000ac62cf03c999800091c00026cc0000000000eb43c472950ba5dd00c5a450418fc5ec37a0090878aa885c307001c4ba000446987c00000047e000133681e0b2944c00000025809b947e3d9000191809c8243a1897c0002684f1170077a36733182512443d506d20a400009f06812d80840000e7a69800030600012b0000000000006c0008bc26e14fca2c92c4f008b8000610000249522200048108f109630421705b48a80000000000af09081d29dbc24e28f50911143588a72ca00000005461ee84840002e150526643bc50026b22b1218582071a1b4000399000199400088f00006350343f8213904c11ea3719511ccf8a5cd0f4879ce800393eca5b855261b1a48efc99c93200000000007643a30d4000000048f88fc44c000000087c00056d4f2800103a00009617bc3b09981840000cd8166000041ce349192638bd098600049804d11be0004da996cdac00000019fc000497132000034a833240248013076b0db25fd252793000000030062b13520ac4b825a50b00000004180000b44b46000003228c0000000ca000035400035090a116200000004c106a139476800044622b0000f151a6000000229800039b0000000fc416b000000000030e1c42504faa0cd21da04400098c0000c9c0005ec228a060a1a7e639316a4000000431800000040000000000001643ec215c9de61c377a08843a2c00dd95e869a64d5011a946c64044b00000bfc6220001e3ce6056100000009b01a02c00d642448b30001d944aa1172508000cd021b00000000008f82340000b58442376000135879251d1c8519a41c36c05880540f52de86890780a123c06c53120753f296200003f544d1e85142a4b0d5960c6fa6f93ce953ced83c94551afc94a42c1a328384ec85f27424606242810779a510046784f698a01f41e3496800005c0003e60934000000000000048e79f00000000003fc3189c58c7886211487582d40002261bc8fa69033ee00ec9c8541000258d29e0000001868000000169a818000000000000000009a00023182f078624a166cff457b02d08c8b3c89100014645e200023605c54807f600009bcbb44da135811c7b678d2f91e5902061700019a40009fd00005640000001bb00010de32200025e8e8a2e30000ea93c879b42b05d0d8678b3208000efe2a239680013ba10e00002440005a143300c80000003a88000edc1a72bc8dec3ec7b24c7867c3de20e2c31718f4013e49b867542013513d291cbc00a042e81e00a88e10d6838441e000123071ce6c62645ea4c498c7e9000126c89c51200000000004e600022640000000000000cea0004da03f90289d416a22b851011b4e71c5cc5e38c28ba2b43fc401442
  | 16 => 0xd25b454098415a99805fc1d23c70b184806202ab0db0e548010818ee40008ee4ea9a0896a3022ae800096ea2947f0d009322634608e2d14a6480d995b85d897d3cc87d00c202c108193cf7a9db26404f0a7849002e905cbf069314f8b6c8566e3409a67098065c09b06d452858b30589992aa6d30780e88d846cb1e2003c3020003f90000bd085e4a198c80009de0000000fbe741186800000021422e019c6e000011093300000000ae85a132c0000800b307784ed127942400077321b99ec1ae2d704680000002154891eb800052127e0c1400088b00000000007914ad1a7543e2b144a0000a643e835a1c20a9893c39a1b5c0005742e90cd40000000000b20bc62b24029b480007b950880008ce99a0000b04000000000211146c20915d80000000002e5800006e11f00000006ea1520002200e2000049196cc000706207a4752eaa200000784aaa4bc3929b710c21053918000dc4000150a30800061e00015a94782e6043181400061125900000000001dc12240001ce261241502e1d900000f8c8e9454641764ab62fd2ca811875c3f010d04ac0ee000001822c0001613b38938a20a042458000490074000000000084800018d00000000b900013609b82069c012282cd2ffa0a019e10d2a218a812c81b07a25505ee00031d1ff81960000000001156000000188c73e65610918302f28d6420a08cf9e2c41bca69c8b654000000000005cc34a877456e000000000108e4233b6914c8929ff00000e0ea6000000000023200000019b52360001570ac00000003dd000057a1a64d2a1281023d200000000000000ba974c1e631b40594bca2a40a08300004580001da0eec18e5700000c7d148083397833812457d30aa7bc3529f336602309ba1db0f800349a07e14bc8d04ee26fe2471ac8a3e0003ba04e0cbc4b42b8a328cd63030001f580008b0360800000088802f975c00000002206391a440747b03dc1aa3a94d911d07e82914e802b8d0e0002d409a488893d000000068a90e2e5283021200036500010006273c80bd512a67708580d8ad600000000000006590c480007ee000000000000021c3f19310f380002760328c843483e3a6540000001b280000005c83740a902c60340000000c321043de1b1400044f0000000e327982180b24e3a8d548f08f40009ad2328b5875600000023300006a3399000000000030b000130007e2fb95d90c00881ef80145947802cb10089a820b43e0cb0df61012c20d5c18c04f01580004c4496331020145e0000c900002a8000047000030e7783581a492d60004af000111465d2eb1da0c140430001c240001f24ca10fcdb226738f94f4ff28515018af8f3413b3820000b3e00036f016130e000000263400000000000014825dd25100009048dd02504284846184e7a498fc0990000000000003f000000000
  | 17 => 0xa68b9044a8704b200041d000000036232900000000000002148638000000000000048535c1640acc00046702cc03e8d100000014326c40000960b762561ca0dac0004be27b81ac04e0002d3005cdec0153428c04bda7cd52280012760000000000aa26b6032a0c52ce00029601c41ce8c019300000000000001f7495a1d4339150ceba47513a89dd386000423037c1ba2b632180013be84207685cc51c000462030c32e0002950a7000000000000013e20be00000005f6435052284c000000012884c40e25b0000da08b2000449a74800000016f8540000000000000000005146b8f98fe86f80de00003b46c600027a800018200017c05d40003bb8ccc0000000080d805720003b18000000000000000000073f000110c0009fe49500011929743d8221c00000036784b40006fc0001c3800058d280921c6a40003ad85244722a62d897083640d80810fd84c203a51c02c94646352e09ee01707ff069973805e33e1a3a5200b620047a21a80962ee0da000040a5cf0000000a6c0bd00016a800000030492a458e8ea2f28e0076680427ea500eb229d38c1cb0d2e36d0a703e486c44b098a20c2107bb09d00011b62ed0000a5400074d0ad000000067d0000000d740004c700000000000001f494867f8000030800049524d28a07ce00047420480005bc0000000050000255800134868e19a00005b80000000c000004b319094703e64091aa955c6b8762139885c10ea015158a2c33823e0001df511215f132848c70e70f077000000055c0000e8400000000011040001fc1c2a0ecbd2069000066cc0482551a122076c2d805d1da940a0000a20010b8e0330cc8228d7860710607f4b5c3eb07b24845340001f986e93163ff0a3000004620621a05550f6a4e0e6a28068833c01e053d34056907f966093c5310000000e0406c47a9dec3aa0000390000c487ce0000f940000bc0e6251898219e1c69c553a20001f619606647384d188c518a3ac36d90c80009d64b4800000000000005c00000002879a5800000000021140006130001fd4e1a81600000013844931f111f103200000004b80006a019780008fc0000000ea000000013a00000005602fc800094c92445d0000c0090124327f04305b600000000005234cb8000abe84329f26c45f40732201778ca270b4d712c54305a5307803119e00025d152509277e0d21ec440492b15e23ec6bc3372b28a6c7e43b12b3852c6a62c53a8285000029e08a111c5244bf24208206861f945126a0ade1fb06a17541260003af2678caa1430a09d593f262e00020e0f2e1511fd000000000000000000003240000000e284921a595143b800032020702d289e4421f5010474f2b9933cfbca3500004dcb924f901a8f6000036e00000009e89c021ea32c0005970d41040e6e71c0000000a165be2b41348fae9bb15
  | 18 => 0xd7a0002af164872687e298000101a6b73c40f70878a07271a1d92083e9172875c0004b9121800134493646f0ca4ca00000000cd8000000000000091a406000000072e8691578000a0e0003f8231c000233000000070c84d0000000e0a59113905e884400048808dce229c600001649f06ad4bb1a292e05295138ed4b745fd2f89fdcd540260000000d0c19a1a711fc00000000000003203d12451eb06c86d500000011fa26c39380000005644eb9ce4df495d18d225cc100000001bb473c58700000001d8000000000000000000018cd1b07b314c91d85686f52dc26e49ce5d42189e0897a32e33b01f4ca67120d19a7149e3910bb245432675241925452cc7c903e01b93028031f09670e623fb112080445490d32701e94464720a51dc00c073e40516c8c6c01d1fea7e901052e0000bac00075a17927dc3862350a6a898c4a1e604a85f071e8864f90b64d720a719198f44086a9011271c01c70a340002cda20b727d149c1ca28d0920000e5097200023b019295b05698180004de00000008f20000002030c940f80000b8800293a45b87b40fe74a24183a81ac25445da86c2642b800000001a455824e27a02509eb2929bac00050a429952073a0313370000d1ea330001b240005c40c79fb400000000000005262ef20880000002795168000cae00000000014348f13018000b4e8f722f91847488960000000000a3029d8060b7e0001dd0000f6c97b07e8068b5a457296a8840a02111ad1ea45fe9cb42da8a94625af2c71664c7002d3daa6740000e004296e50800244d0800000030b344251c9ea0004800fbcf906bb3e01a0cdca89f219a4fc78400007121a137e85900019240005343fe25581e236947397cc00069000000001d645d3b0272814c040052977009275c08902ed0e63f14fc0f9016c00047ca74cf0200000000000000001988320684a3d032000000078a2a58ce839600032a000017e9912bf06bc0005c5088000069e0004b9909800000021213fcac43743860000d585023b3000087400025da6f00008f3363a3680002e80550e1000094427125487
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe76cc910004fd76cc910084fc76cc9100067f65cc9101c67c65cc910086de63cc910006dd63cc910006ef62cc910016ec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100357c754c9100067f654c9101b67c654c910006de634c910006dd634c910005f7714c91000df4714c910025f4765451001ef47654510024f4765451000df7755451000f77755451000777655451001ef6655451001ef46554510037746554510005f77454510007765354510037745354510037775254510007755254510007f37054510025f67054510025f47054510007f0705451000ef7605451000ff36054510037775054510025f4765051003ef47650510024f47650510005f77550510005f5755051000777655051000774655051000df7745051000fb77450510007b7645051003ef6645051003ef46450510007b46450510007b74350510007b54350510007b74250510007b54250510007f37050510025f67050510025f47050510007f0705051000ef7605051000ff3605051029fb6405051029fb4405051001cff765411000cfe765411013cfd765411000cfc76541100067f655411001e7c6554110005f7715411000df47154110007755154110027f0105411000cfe76d011000cfc76d01100067f65d01101367c65d0110006bf64d011003ebc64d011000df671d0110005f571d011003cff765011000cfe76501100f4fd765011000cfc76501100067f65501101067c6550110006bf645011003ebc6450110005f7715011000df4715011000cfe76cc11000cfc76cc1100067f65cc1100d67c65cc110006df63cc110086dc63cc11000df671cc110005f571cc110084ff764c11000cfe764c110094fd764c11000cfc764c1100057f754c1100357c754c1100067f654c1100a67c654c110005bf744c110005bc744c110006df634c110006dc634c110005f7714c11000df4714c110295fa7688110026fa76881100077b6588110007786588110055f97288110016fa6288110016f8628811000dfa7188110025f87188110026fb6188110027f36188110067f25188110007f15188110067f24188110007f14188110014ff764811000cfe7648110054fd764811000cfc76481100067f654811005e7c6548110005bf7448110005bc7448110006ef6248110016ec6248110005f7714811000df4714811000df87648110016f8764811000cf876481100077b6548110007786548110007bb7448110007b87448110025fb7248110027eb7248110007eb6248110016fa6248110016f8624811002fe8624811002fea4248110007e9424811002fea3248110007e93248110007f3714811000dfa714811000df87148110057f07148110026fb6148110027f36148110057f25148110007f15148110057f24148110007f14148110
  | 1 => 0x8d1003cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d10094ff7158d10006f77158d100c4ff7058d10006fb7058d100acfe7618d100067f6518d100067c6518d10006dd6318d1001cfe7518d10004fd7518d10084fc7518d1003cfe7418d10004fd7418d10086de7318d10014fe7218d10004fd7218d10014fc7218d10006de3218d10086dc3218d10024ff7118d1000cfe7118d10024fd7118d1000cfc7118d10086df3118d10076dd3118d10024fe7018d10024fc7018d10084ff7694d10004fe7694d10004fd7694d10084fc7694d100067f6594d1001e7c6594d100375f5394d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d1003cff76d0d10004fe76d0d10004fd76d0d1003cfc76d0d100357e75d0d100057d75d0d100067f65d0d1024e7c65d0d10006df63d0d10006dc63d0d1000df671d0d10005f571d0d10084ff7690d10004fe7690d10004fd7690d10084fc7690d100067f6590d102367c6590d10006bf6490d1003ebc6490d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1021e7c6550d10005fb7050d10025f87050d10084ff7610d10004fe7610d10004fd7610d10084fc7610d100067f6510d102067c6510d10006bf6410d1003ebc6410d10006df6310d10086dc6310d1000df67110d10005f57110d10014fe76d89100067f65d89100067c65d891002eee62d891001cfe75d8910004fd75d891001cfc75d891003cfe74d8910004fd74d8910084fe73d8910004fd73d891002eec42d891002eec32d8910024ff71d891000cfe71d8910024fd71d891000cfc71d8910066ef21d8910066ed21d8910024fe70d891000cfd70d8910024fc70d891002eef20d89100057f75589100357c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc735891002eec62589102a5fb7058910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df7358910084fc7358910006dc7358910004dc7358910064ff7258910006ef7258910054ff7158910006f771589102a4ff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c655491003cff76d0910004fe76d0910004fd76d091003cfc76d09100067f65d09101e67c65d0910006ef62d0910016ec62d091000df671d0910005f571d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101d67c6550910084ff76cc910004f
  | 2 => 0x67f7559510004ff745951003cfc7459510004ff7359510084fc7359510004ff7259510014fe7259510014fc725951013cff7159510006f771595102bcff7059510006fb705951014d7e76195100367e761951014c7e76195100067e62195100067c62195102af7671195100377571195102b67f61195102af7641195102ae7f60195102af7b10195102b77610195102b77410195102af78101951003cfe76d91100067f65d91100067c65d911001cfe75d9110004fd75d911001cfc75d9110084fe73d9110004fd73d9110014fe72d9110004fd72d9110014fc72d9110006be42d9110006bc42d9110024ff71d911000cfe71d9110024fd71d911000cfc71d911010ebf41d911010ebd41d9110024fe70d9110024fc70d91100357e75991100057d75991100067f65991100067c6599110006bf64991100f5f970991100057f75591100357c75591100067f65591100067c6559110005df7359110005dc7359110005ef725911002dec7259110125fb7059110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110084fc7359110006dc7359110004dc7359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec72591100f4ff7159110006f77159110124ff7059110006fb705911029ebe405911029ebc405911010cfe76191100067f65191100067c651911003ebe6419110006bd641911003cff7695110004fe7695110004fd769511003cfc76951100067f659511001e7c65951100373f549511000df67195110005f57195110004ff7655110004fe7655110004fd7655110004fc76551100067f655511001e7c655511000df671551102777651551100067f65d8d100067c65d8d1001cfe75d8d10004fd75d8d1001cfc75d8d1003cfe74d8d10004fd74d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10006dc32d8d10024ff71d8d10024fd71d8d100aedf31d8d100aedd31d8d100357e7598d100057d7598d100067f6598d100067c6598d10006df6398d10095f97098d1001cfe7598d100867e7598d1001c7e7598d10004fd7598d100867d7598d100047d7598d10084fc7598d1003cfe7498d10004fd7498d10084fe7398d10014fe7298d10004fd7298d10014fc7298d100c4fd7198d10086f57198d10094fd7098d10086f97098d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d1002dec7258d100c5fb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d1003cfc7458d10006bc745
  | 3 => 0xd7690e10024fc7690e10086de6390e10006dd6390e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10006de6350e10006dd6350e10005fb7050e10025f87050e10084ff7610e10024fe7610e10004fd7610e10024fc7610e10004ff7558a1001cfe7558a1001cfc7558a10004ff7458a1003cfc7458a10004ff7358a10084fc7358a10026ef7258a10006ef5258a10046ec5258a10046ee4258a10046ee3258a10056ef2158a10056ed2158a10024ff7058a10024fe7058a10024fd7058a10024fc7058a10026ee2058a10026ec2058a10004ff7654a10024fe7654a10004fd7654a10024fc7654a102d67f6554a1001e7c6554a10005f77154a1000df47154a1003cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10016ee6250a10006ed6250a10084ff76cca10024fe76cca10004fd76cca10024fc76cca10086de63cca10006dd63cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca1004d7c754ca10006de634ca10006dd634ca10016ee624ca10006ed624ca10005f7714ca1000df4714ca10025fb76482102cefb7648210007bb7448210007b87448210027eb7248210016fa6248210026f86248210047ea4248210007e94248210047ea3248210007e9324821000dfa714821000df8714821001cfe76d95100367e65d951003cfe74d9510004fd74d95100367f54d95100367c54d9510084fe73d9510004fd73d95100367f53d95100367c53d9510014fe72d9510004fd72d9510014fc72d95100367f52d95100067e52d95100367c52d9510024ff71d951000cfe71d9510024fd71d951000cfc71d951014e7f51d951014e7d51d9510024fe70d951000cfd70d9510024fc70d95100367f50d95102ad7e76d951001c7e76d95100067e62d95100067c62d95102c77771d951014f7471d951014f7641d951014f7b10d95102c77610d95102c77410d951014f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067e32d95100067c32d95102c67f71d951014e7e71d951014e7d71d951014e7c71d951014e7f41d951014e7e41d951014e7d41d951014e7c41d951014e7f31d951014e7e31d951014e7d31d951014e7c31d951014e7f21d951014e7e21d951014e7d21d951014e7c21d951014e7f70d95102c67e70d951014e7d70d95102c67c70d95102c67e40d95102c67c40d95102c67e30d95102c67c30d95100067f20d95102c67e20d95102c67c20d951014e7f10d95102c67e10d95102c67c10d95100367c65595102bdfb705951014cff7559510
  | 4 => 0xc520015ee72cc520005ed72cc520007cd32cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c520006bf644c520006bc644c520007cd324c52001cff7654120014fe7654120144fd7654120014fc76541200067f655412001e7c6554120006bf6454120006bc6454120005ef7254120015ec7254120027e82054120014fe76d0120014fc76d0120006bf64d012003ebc64d0120015ee72d0120005ed72d012003cff7650120014fe76501200fcfd7650120014fc7650120006bf645012003ebc6450120005ef7250120015ec7250120014fe76cc120014fc76cc120006bf64cc120006bc64cc120006df63cc120086dc63cc120015ee72cc120005ed72cc120007cd32cc120084ff764c120014fe764c12009cfd764c120014fc764c1200057f754c12005d7c754c120005bf744c120005bc744c120006bf644c120006bc644c120006df634c120006dc634c120005ef724c120015ec724c120007cd324c120027d8304c120027e8204c1200267f7559610004ff745961003cfc745961004e7f5459610004ff7359610084fc7359610004ff7259610014fe7259610014fc725961013e7f515961013e7d5159610024ff7059610024fe7059610024fd7059610024fc70596100267e50596100267c5059610026f71059610026f51059610004ff755921001cfe755921001cfc7559210026bf7459210004ff7359210084fc7359210004ff7259210014fe7259210014fc72592100f6bf41592100f6bd4159210024ff7059210024fe7059210024fd7059210024fc7059210026be4059210026bc4059210026f71059210026f5105921003cff7695210024fe7695210004fd7695210024fc769521004f3f5495210004ff7655210024fe7655210004fd7655210024fc765521001e7e65552100067d655521001cfe7598e10004fd7598e10084fc7598e1003cfe7498e10004fd7498e10026de7398e10006df5398e10086dc5398e10014fe7298e10004fd7298e10014fc7298e10086df3198e100c6dd3198e10024fe7098e10024fc7098e10026de3098e10026dc3098e10004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e1003cfc7458e10026df7358e10006df5358e10006dc5358e10004ff7258e10014fe7258e10014fc7258e10096df3158e10096dd3158e10024ff7058e10024fe7058e10024fd7058e10024fc7058e10026de3058e10026dc3058e10084ff7694e10024fe7694e10004fd7694e10024fc7694e102de7f6594e1001e7c6594e1004f5f5394e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1003cff76d0e10024fe76d0e10004fd76d0e10024fc76d0e1004d7e75d0e100057d75d0e10084ff7690e10024fe7690e10004f
  | 5 => 0x86dc5318d20024ff7218d20014fe7218d20024fd7218d20086ed7218d20014fc7218d20086df3218d20086ee3218d2007edd3218d2000cfe7118d20004fd7118d2000cfc7118d20006de3118d20086dc3118d20084ff7694d20004fe7694d20004fd7694d20084fc7694d200067f6594d2001e7c6594d20006bf6494d20006bc6494d2005f5f5394d20015ee7294d20005ed7294d20025fa7094d20005f97094d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20006bf6454d20006bc6454d2003cff76d0d20004fe76d0d20004fd76d0d2003cfc76d0d2005d7e75d0d200057d75d0d20006bf64d0d2003ebc64d0d20015ee72d0d20005ed72d0d20084ff7690d20004fe7690d20004fd7690d20084fc7690d20006bf6490d2003ebc6490d20015ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2003ebc6450d20015ee7250d20084ff7610d20004fe7610d20004fd7610d20084fc7610d20006bf6410d2003ebc6410d20015ee7210d20005ed7210d20025fa7010d20005f97010d20025ec765092003eec7650920024ec7650920015ef7450920017af7450920007af645092003eee645092003eec6450920007ac6450920005ef7350920007eb7050920025ee7050920025ec7050920007e87050920016ef6050920017eb6050920025ec764c920006ec764c920024ec764c9200076f754c9200076c754c920005ef744c920005ed744c920007af644c920007ac644c920015ef734c920017cf734c920007cf634c920086ee634c920086ec634c920007cc634c920007cf434c920007cc434c920007e7714c920007e4714c920007eb704c920025ee704c920025ec704c920007e8704c920016ef604c920017eb604c92000cfe76d8520006bf64d8520006bc64d8520056f661d852001cfe75d8520004fd75d852001cfc75d852003cfe74d8520004fd74d8520084fe73d8520004fd73d8520024fd72d852000cfc72d8520006f751d8520056f451d8520056f431d8520056f621d8520046f521d8520024fe70d8520014fd70d8520024fc70d8520056f710d85200057f755852005d7c7558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520005dc7358520056f461585202e5fb7058520004ff7654520004fe7654520004fc765452001e7e65545200067d6554520006bf6454520006bc6454520005ef7254520015ec7254520004fe76d0520004fd76d052003cfc76d052005d7e75d05200057d75d0520006bf64d052003ebc64d0520015ee72d0520005ed72d0520007ad42d0520004ff7650520004fe7650520004fc7650520006bf645052003ebc6450520007ad4250520004fe76cc520004fd76cc520084fc76cc520006bf64cc520006bc64c
  | 6 => 0xc65191200e7ae7219120007ad72191200e7ae3219120006be6119120006bc61191200e7bb20191202efae20191202efac20191200e7b8201912003ebf751912003ebe751912003e3e751912003ebd751912003e3d751912003ebc751912003ebf731912003ebe731912003ebd731912003ebc7319120006bf5319120006bc531912003ebf721912003ebe721912003eae721912003ebd721912003ead721912003ebc72191200e6bf52191200e6be52191200e6bd52191200e6bc52191200e6bf32191200e6be32191200e6bd32191200e6bc321912003ebf711912003ebe711912003ebd711912003ebc7119120006bf5119120006be5119120006bc5119120006be3119120006bc31191200e6bf21191200e6be21191200e6bd21191200e6bc211912003ebf701912003ebe701912003ebd701912003ebc7019120006bf50191202eebe50191202eebc50191202eebe30191202eebc30191200e6bf20191202eebe20191200e6bd20191202eebc2019120006bf10191202eebe10191202eebc101912003cff7695120004fe7695120004fd769512003cfc7695120006bf649512003ebc649512005f3f5495120015ee7295120005ed7295120004ff7655120004fe7655120004fd7655120004fc765512001e7e65551200067d6555120006bf645512003ebc6455120005fb7055120025f87055120006bf64d8d20006bc64d8d2001cfe75d8d20004fd75d8d2001cfc75d8d2003cfe74d8d20004fd74d8d20006df53d8d20006dc53d8d20024ff72d8d20024fd72d8d200b6df32d8d200b6dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006de31d8d20006dc31d8d20005be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d2009df97098d2001cfe7598d20004fd7598d20084fc7598d2003cfe7498d20086be7498d2003cbe7498d20004fd7498d20086bd7498d20004bd7498d20084fe7398d200ccfd7298d20086ed7298d20086ee3298d2000cfe7198d20004fd7198d2000cfc7198d2009cfd7098d20086f97098d200057f7558d2005d7c7558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d20005f77158d20055f47158d200cdfb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d2003cfc7458d20006bc7458d2003cbc7458d20006df7358d2009cff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d200ccff7058d20006fb7058d200b4fe7618d20006bf6418d20006bc6418d20006dd6318d2001cfe7518d20004fd7518d20084fc7518d2003cfe7418d20004fd7418d20086de7318d20006df5318d20
  | 7 => 0xc620015ec724c62001cfe76d952005e7e65d952003cfe74d9520004fd74d9520084fe73d9520004fd73d952005e7c53d9520024ff72d9520014fe72d9520024fd72d9520014fc72d95201567f52d95201567d52d952000cfe71d9520004fd71d952000cfc71d95200067e51d952005e7c51d9520014fd70d952005e7f50d952005e7c6559520005bf7459520005bc7459520005df7359520005dc7359520005f77159520055f471595202fdfb7059520154ff75595200067f7559520004ff7459520006bf7459520004bf745952003cfc7459520006bc745952003cbc745952005e7f5459520004ff7359520006df7359520004df7359520084fc7359520006dc7359520004dc7359520144ff7259520006ef7259520004ff7159520006f77159520004f7715952000cfe715952000cfc7159520006f4715952000cf4715952005e7f51595202fcff7059520006fb70595202d67e50595202d67c505952003cfe76d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006bc54d9120084fe73d9120004fd73d9120024ff72d9120014fe72d9120024fd72d9120014fc72d9120116bf42d9120116bd42d912000cfe71d9120004fd71d912000cfc71d9120006be41d9120006bc41d912003cbe76d9120006bf65d9120006be65d9120006bd65d9120006bc65d91202f7af72d9120117ac72d9120117ae32d9120006be61d9120006bc61d9120117bb20d91202f7ae20d91202f7ac20d9120117b820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d91202f6bf72d9120116be72d9120116bd72d9120116bc72d9120116bf52d9120116be52d9120116bd52d9120116bc52d9120116bf32d9120116be32d9120116bd32d9120116bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d9120116bf21d9120116be21d9120116bd21d9120116bc21d9120116bf70d91202f6be70d9120116bd70d91202f6bc70d9120006bf50d91202f6be50d91202f6bc50d91202f6be30d91202f6bc30d9120116bf20d91202f6be20d91202f6bc20d9120006bf10d91202f6be10d91202f6bc10d9120006bf64991200fdf9709912012dfb7059120004ff755912001cfe755912001cfc7559120006bf7459120004ff7359120084fc73591200fcff7259120006ef7259120004ff715912000cfe715912000cfc715912012cff7059120006fb7059120114fe761912005d7e75191200057d751912003ebe6419120006bd6419120115be7619120006be7619120114be76191200073e75191200073d7519120006bf6519120006be6519120006bd6519120006b
  | 8 => 0x27ea624c030027e9624c030087db324c030007d9324c0300267f7559620004ff745962003cfc745962006e7f5459620004ff7359620084fc735962006e7c53596201467f52596201467d5259620004ff715962000cfe715962000cfc715962006e7f5159620024fe7059620024fc70596200267e50596200267c5059620004ff755922001cfe755922001cfc7559220026bf7459220004ff7359220084fc73592200febf42592200febd4259220004ff715922000cfe715922000cfc7159220024fe7059220024fc7059220026be4059220026bc4059220026ef2059220026ed205922003cff7695220024fe7695220004fd7695220024fc769522006f3f5495220004ff7655220024fe7655220004fd7655220024fc765522001e7e65552200067d6555220005fb7055220025f8705522001cfe7598e20004fd7598e20084fc7598e2003cfe7498e20004fd7498e20026de7398e20086df3298e200cedd3298e2000cfe7198e20004fd7198e2000cfc7198e20024fe7098e20024fc7098e20026de3098e20026dc3098e20004ff7558e2001cfe7558e2001cfc7558e20004ff7458e2003cfc7458e20026df7358e2009edf3258e2009edd3258e20004ff7158e2000cfe7158e2000cfc7158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e20084ff7694e20024fe7694e20004fd7694e20024fc7694e2001e7e6594e200067d6594e2006f5f5394e20025fa7094e20005f97094e20004ff7654e20024fe7654e20004fd7654e20024fc7654e2003cff76d0e20024fe76d0e20004fd76d0e20024fc76d0e2006d7e75d0e200057d75d0e20084ff7690e20024fe7690e20004fd7690e20024fc7690e20086de6390e20006dd6390e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20006de6350e20006dd6350e20084ff7610e20024fe7610e20004fd7610e20024fc7610e20025fa7010e20005f97010e20004ff755862001cfe755862001cfc7558620004ff745862003cfc7458620004ff7358620084fc7358620026f77158620066f65158620066f64158620066f43158620066f6215862002ef52158620024ff7058620024fe7058620024fd7058620024fc7058620026f61058620026f41058620004ff7654620004fd7654620024fc765462001e7e65546200067d655462000ef66154620006f5615462003cff76d0620024fe76d0620004fd76d062006d7e75d06200057d75d0620306bf64d062003ebc64d0620004ff7650620004fd7650620024fc765062029ebf645062003ebc6450620005ef7250620015ec725062000ef66150620006f56150620084ff76cc620024fe76cc620004fd76cc62000ef661cc620006f561cc620004ff764c620004fd764c620024fc764c620005ef724
  | 9 => 0xf7258830006ef525883007eee525883007eec525883007eee425883007eec4258830086ef3258830086ec3258830004ff715883000cfe715883000cfc715883007eef2158830006ee215883007eec2158830024fc7058830026df3058830026dd3058830026ee2058830026ec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883007eef7358830086ee7358830006ef5358830086ee5358830006ed5358830086ec5358830006ef4358830086ee4358830006ed4358830086ec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ec5158830006ee4158830006ec4158830086ef3158830006ee3158830086ec3158830026ef7058830026ee7058830026ec7058830026ef5058830026ee5058830026ed5058830026ec5058830026ef4058830026ee4058830026ed4058830026ec4058830026ef3058830026cf3058830026ee3058830026ed3058830026cd3058830026ec3058830026ef1058830026ee1058830026ed1058830026ec1058830004ff7654830004fd7654830024fc7654830005df7354830085dc7354830016ee6254830006ed625483003cff76d0830024fe76d0830004fd76d0830016ee62d0830006ed62d0830004ff7650830004fd7650830024fc7650830016ee6250830006ed6250830005fb7050830025f870508300ccff764c8300057f754c83008d7c754c8300cede634c830016ee624c830005f7714c830075f4714c830004ff755843001cfe755843001cfc7558430004ff745843003cfc745843000cfd7358430004ff7258430014fe7258430014fc7258430026f77158430076f65158430076f64158430086f73158430086f43158430024fc7058430026f61058430026f41058430004ff7654430004fd7654430024fc765443001e7e65544300067d65544301a6ee6254430006ed625443000ef66154430006f5615443003cff76d0430024fe76d0430004fd76d043008d7e75d04300057d75d043003ebe64d0430006bd64d0430196ee62d0430006ed62d0430004ff7650430004fd7650430024fc765043003ebe6450430006bd6450430005df7350430085dc7350430186ee6250430006ed625043000ef66150430006f561504300c4ff764c430166ee624c430006ed624c430004ff7648430004fd7648430024fc7648430005df7348430085dc7348430016ee6248430006ed6248430025fb764c030006fb764c030004fb764c0300077b754c03000778754c030007bb744c030007b8744c030025fb734c030027db734c030086fa634c030027da634c030087da534c030007d9534c030007db434c030087d8434c030
  | 10 => 0x530005de73d0530005dd73d05300079d43d0530004ff7650530004fe7650530004fc76505300067f655053018e7c6550530006bf645053003ebc64505300079d43505300acfe76cc5300067f65cc53017e7c65cc530006bf64cc530006bc64cc530024fc764c5300067f654c53016e7c654c530006bf644c530006bc644c530006f7614c53000ef4614c530005fb704c530025f8704c530004ff7648530004fe7648530004fc76485300067f654853015e7c6548530006bf6448530006bc644853001cff76541300a4fd765413001cfc76541300067f655413001e7c6554130006bf6454130006bc6454130005df7354130005dc7354130027d83054130004fe76d01300067f65d01301367c65d0130006bf64d013003ebc64d0130005de73d0130005dd73d0130027d830d013003cff7650130004fd765013003cfc76501300067f65501301067c6550130006bf645013003ebc6450130005df7350130005dc73501300067f65cc1300d67c65cc130006bf64cc130006bc64cc130025de73cc130024fa76cc1300077b65cc1300077865cc130007bb64cc130007b864cc130025fa73cc130027db63cc130087da43cc130007d943cc130087db32cc130007d932cc130024ff75594300267f7559430004ff745943003cfc745943008e7f545943001cff735943001cfd7359430084fc73594300867e53594300867c5359430004ff7259430014fe7259430014fc7259430004ff715943000cfe715943000cfc715943008e7f5159430024fe7059430024fc70594300267e50594300267c5059430004ff755903001cfe755903001cfc7559030024ff7459030026bf745903003cff735903003cfd7359030084fc7359030086be4359030086bc4359030004ff7259030014fe7259030014fc7259030004ff715903000cfe715903000cfc7159030024fe7059030024fc7059030026be4059030026bc4059030026df3059030026dd305903003cff7695030024fe7695030004fd7695030024fc769503003ebe6495030006bd649503008f3f549503028eee6295030004ff7655030024fe7655030004fd7655030024fc765503001e7e65550300067d655503003ebe6455030006bd6455030005df7355030085dc735503027eee6255030005fb7055030025f87055030084ff7598c3001cfe7598c300d4fd7598c30084fc7598c30084ff7498c3003cfe7498c30004fd7498c30084fc7498c30086de4398c30014fe7298c30086df3298c3000cfe7198c30026de3098c30026fa3098c30026dc3098c300d4ff7654c3025eee6254c30004fd76d0c3008d7e75d0c300057d75d0c30246ee62d0c30004ff7650c30006de6350c300879c4350c30216ee6250c30004ff755883001cfe755883001cfc7558830004ff745883003cfc7458830014fd7358830026e
  | 11 => 0x2067c6510d30006bf6410d3003ebc6410d30005de7310d30014fe76d89300067f65d89300067c65d8930006bf64d8930006bc64d893009eee62d893001cfe75d8930004fd75d893001cfc75d893003cfe74d8930004fd74d8930024fd73d8930014fc73d893009eee32d893000cfe71d8930004fd71d893000cfc71d8930006ee21d893009eec21d893009eef20d89300057f75589300a57c75589300067f65589300067c6558930005bf7458930005bc7458930006bf6458930006bc645893009eec6258930005f77158930095f47158930004ff7654930004fe7654930004fc76549300067f655493001e7c6554930006bf6454930006bc6454930004fe76d0930004fd76d093003cfc76d09300067f65d09301e67c65d0930006bf64d093003ebc64d0930005de73d0930005dd73d0930004ff7650930004fe7650930004fc76509300067f65509301d67c6550930006bf645093003ebc64509300b4fe76cc9300067f65cc9301c67c65cc930006bf64cc930006bc64cc930005de76cc9300b6de76cc9300075f65cc9300075c65cc930005df74cc930005dd74cc9300079f64cc930316de64cc930316dc64cc9300079c64cc9300069c64cc93009ddd72cc930016de62cc930016dc62cc930025de70cc930025dc70cc930024fc764c9300057f754c9300a57c754c9300067f654c9301b67c654c930006bf644c930006bc644c930006ef624c930016ec624c93009fcc324c930005f7714c930095f4714c930005fb704c930025f8704c930025dc764c930016dc764c930024dc764c9300075f754c9300075c754c9300075f654c9300075c654c930005df744c930005dd744c9300079f644c93030ede644c93030edc644c9300079c644c9300069c644c93009ddf724c930007cf724c930007cf624c930016de624c930016dc624c93009fcc624c930007d7714c930007d4714c930007db704c930025de704c930025dc704c930007d8704c93009fcf204c93000cfe76d85300067f65d85300067c65d8530006bf64d8530006bc64d8530096f661d853001cfe75d8530004fd75d853001cfc75d853003cfe74d8530004fd74d8530024fd73d853000cfc73d8530014fe72d8530004fd72d8530014fc72d8530006df32d8530006dd32d8530096f631d8530006f721d8530096f421d8530096f710d85300057f75585300a57c75585300067f65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef725853009dec7258530096f46158530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530006bf6454530006bc6454530005df7354530005dc7354530004fe76d0530004fd76d053003cfc76d05300a57e75d05300057d75d05300067f65d053019e7c65d0530006bf64d053003ebc64d
  | 12 => 0xc75591300067c755913001c7c7559130006bf7459130004ff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff715913000cfe715913000cfc7159130004ff7059130006fb7059130004fe76191300067f65191300067c651913003ebe6419130006bd6419130005be7619130006be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c65191300079d7319130006be6219130006bc6219130006be6119130006bc61191303279e30191303279c301913003ebf751913003ebe751913003ebd751913003ebc751913003ebf731913003ebd731913003e9d7319130006bf5319130006bc531913003ebf721913003ebe721913003ebd721913003ebc7219130006bf5219130006be5219130006bc5219130006be3219130006bc321913003ebf711913003ebe711913003ebd711913003ebc7119130006bf5119130006be5119130006bc5119130006be3119130006bc3119130006bf2119130006be2119130006bc211913003ebf701913003ebe701913003ebd701913003ebc7019130006bf5019130326be5019130326bc5019130326be3019130006bd3019130326bc3019130006bf2019130326be2019130326bc2019130006bf1019130326be1019130326bc101913003cff7695130004fe7695130004fd769513003cfc76951300067f659513001e7c6595130006bf649513003ebc64951300a73f5495130005de7395130005dd7395130004ff7655130004fe7655130004fd7655130004fc76551300067f655513001e7c6555130006bf645513003ebc64551300bcfe7694d300067f6594d3001e7c6594d30006bf6494d30006bc6494d300a75f5394d30024fc7654d300067f6554d3001e7c6554d30006bf6454d30006bc6454d30005fb7054d30025f87054d30024fe76d0d30024fc76d0d300a57e75d0d300057d75d0d300067f65d0d3024e7c65d0d30006bf64d0d3003ebc64d0d30025fa70d0d30005f970d0d30004fe7690d300067f6590d302367c6590d30006bf6490d3003ebc6490d30005de7690d30006de7690d300075f6590d300075c6590d30005dd7490d300079f6490d3003ede6490d3003edc6490d300079c6490d3003e9c6490d30005dd7290d30025de7090d30025dc7090d3031f9e4090d3031f9c4090d30024fc7650d300067f6550d3021e7c6550d30006bf6450d3003ebc6450d30005fb7050d30025f87050d30025dc7650d3003edc7650d30024dc7650d300075f6550d300075c6550d300079f7450d300079f6450d3003ede6450d3003edc6450d300079c6450d3003e9c6450d30005df7250d30007db7050d30025de7050d30025dc7050d30007d87050d30025d87050d30004fe7610d300067f6510d30
  | 13 => 0x95300067e62d95300067c62d95300067e61d95300067c61d95302df5e30d95302df5c30d95300067f74d95300067e74d95300067d74d95300067c74d95302de7f73d95300a67e73d95300067d73d95300067f72d95300067e72d95300067d72d95300067c72d95300067e42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067e41d95300067c41d95300067e31d95300067c31d95300067f21d95300067e21d95300067c21d95300067f70d95302de7e70d95300067d70d95302de7c70d95302de7e40d95302de7c40d95302de7e30d95302de7c30d95300067f20d95302de7e20d95302de7c20d95300067f10d95302de7e10d95302de7c10d95300a67c6559530005bf7459530005bc74595300a4ff75595300067f7559530004ff7459530006bf7459530004bf745953003cfc7459530006bc745953003cbc74595300bcff7359530006df7359530004ff7259530014fe7259530014fc7259530004ff715953000cfe715953000cfc71595300d4ff7059530006fb70595300057e76195300a67e76195300047e761953032e7f63195300067e62195300067c62195300067e61195300067c611953032f5e301953032f5c301953003cfe76d91300067f65d91300067c65d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130006bc54d9130084fe73d9130084fc73d9130014fe72d9130004fd72d9130014fc72d9130006be42d9130006bc42d913000cfe71d9130004fd71d913000cfc71d9130006be41d9130006bc41d913003cbe76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d913031f9f73d9130006be62d9130006bc62d9130006be61d9130006bc61d913031f9e30d913031f9c30d9130006bf75d9130006be75d9130006bd75d9130006bc75d913031ebf73d9130006bd73d9130006bf53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bc52d9130006be32d9130006bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bc51d9130006be31d9130006bc31d9130006bf21d9130006be21d9130006bc21d9130006bf70d913031ebe70d9130006bd70d913031ebc70d9130006bf50d913031ebe50d913031ebc50d913031ebe30d913031ebc30d9130006bf20d913031ebe20d913031ebc20d9130006bf10d913031ebe10d913031ebc10d91300a57e75991300057d75991300067f65991300067c6599130006bf64991300057f75591300a57c75591300067f65591300067c6559130004ff75591300067f75591300047f755913001cfe755913001cf
  | 14 => 0x14fe7259230014fc7259230004ff715923000cfe715923000cfc7159230024fc7059230026be4059230026bc4059230026df3059230026dd305923003cff7695230024fe7695230004fd7695230024fc76952300bf3f5495230004ff7655230024fe7655230004fd7655230024fc765523001e7e65552300067d6555230005df7355230005dc7355230026de3058e300a4fd7694e302de7f6594e3001e7c6594e300bf5f5394e3001cff7654e30024fc7654e3001e7e6554e300067d6554e30005fb7054e30025f87054e300bd7e75d0e300057d75d0e3003ebe64d0e30006bd64d0e30025fa70d0e30005f970d0e3031ebf6490e3003ebc6490e3003cff7650e3003ebe6450e30006bd6450e30005fb7050e30025f87050e30326bf6410e3003ebc6410e300079d4310e30004ff7558a3001cfe7558a3001cfc7558a30004ff7458a3003cfc7458a30026ef7258a300b6ee4258a300b6ee3258a30004ff7158a3000cfe7158a3000cfc7158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a30004ff7654a30004fd7654a30024fc7654a30005df7354a30005dc7354a3003cff76d0a30024fe76d0a30004fd76d0a30004ff7650a30004fd7650a30024fc7650a30016ee6250a30006ed6250a3009cfd76cca30014ff764ca300057f754ca300bd7c754ca30016ee624ca30006ed624ca30005f7714ca300adf4714ca30005fb704ca30025f8704ca30004ff755863001cfe755863001cfc7558630004ff745863003cfc7458630004ff7258630014fe7258630014fc7258630026f771586300aef651586300aef641586300aef63158630006f721586300aef42158630024fc7058630026f61058630026f41058630004ff7654630004fd7654630024fc765463001e7e65546300067d655463000ef66154630006f5615463003cff76d0630024fe76d0630004fd76d06300bd7e75d06300057d75d0630306bf64d063003ebc64d0630004ff7650630004fd7650630024fc765063029ebf645063003ebc6450630005df7350630005dc735063000ef66150630006f56150630094fd76cc63000cff764c63000ef6614c630006f5614c630005fb704c630025f8704c630004ff7648630004fd7648630024fc7648630005df7348630005dc7348630025f976cc230086f976cc230027da73cc230087da53cc230007d953cc23001cfe76d95300a67e65d953003cfe74d9530004fd74d95300a67f54d95300a67c54d9530084fe73d9530024fd73d9530084fc73d95300a67f53d9530014fe72d9530004fd72d9530014fc72d95300a67f52d95300067e52d95300a67c52d953000cfe71d9530004fd71d953000cfc71d95300a67f51d95300067e51d95300a67c51d95300a4fd70d95300a67f50d95300a57e76d953001c7e76d
  | 15 => 0xd75d0f30025dd7690f30086dd7690f30024dd7690f3003ede6490f300879e6490f300879d6490f30086dc6490f30005dd7290f30025de7090f30087da7090f30087d97090f30025dc7090f3031f9e4090f3031f9c4090f30005df7650f30006df7650f300879f7450f3003ede6450f3003edc6450f30005df7250f30025de7050f30025dc7050f30086ec6258b30004ff7558b3001cfe7558b3001cfc7558b30004ff7458b3003cfc7458b30024fc7358b30086ef3258b30086ec3258b30004ff7158b3000cfe7158b3000cfc7158b300ceef2058b30004ff7654b30004fd7654b30084fc7654b3001e7e6554b300067d6554b3003cff76d0b30084fe76d0b30004fd76d0b30085de73d0b30005dd73d0b30004ff7650b30004fd7650b30084fc7650b30005fb7050b30025f87050b30025dd76ccb30016dd76ccb30024dd76ccb30085df74ccb30005dd74ccb30316de64ccb30086dc64ccb30016de62ccb30087ce62ccb30087cd62ccb30016dc62ccb30025de70ccb30087da70ccb30087d970ccb30025dc70ccb3007cff764cb300057f754cb300d57c754cb30016ec624cb30087cc324cb30005f7714cb300c5f4714cb30005df764cb3007edf764cb300075f754cb300075c754cb30005df744cb30005dd744cb3030ede644cb3030edc644cb30087cf724cb30087cf624cb30016de624cb30016dc624cb30087cc624cb30007d7714cb30007d4714cb30025de704cb30025dc704cb300cfcf204cb30086f46158730004ff755873001cfe755873001cfc7558730004ff745873003cfc7458730024fc7358730004ff7258730014fe7258730014fc7258730006df3258730006dd3258730086f73158730086f431587300c6f71058730004ff7654730004fd7654730084fc76547300067f655473001e7c6554730005df7354730085dc735473003cff76d0730084fe76d0730004fd76d07300d57e75d07300057d75d073003ebe64d0730006bd64d0730085de73d0730005dd73d07300079d43d0730004ff7650730004fd7650730084fc765073003ebe6450730006bd64507300079d4350730074ff764c730004ff7648730004fd7648730084fc764873001cff765433001e7e65543300067d6554330005df7354330085dc7354330027da305433003ebe64d0330006bd64d0330085de73d0330005dd73d033003cff765033003ebe6450330006bd6450330005df7350330085dc7350330027b840503300267f7559630004ff745963003cfc74596300be7f54596300be7f5359630004ff7259630014fe7259630014fc72596300067e52596300be7c5259630004ff715963000cfe715963000cfc71596300be7f5159630024fc70596300267e50596300267c5059630004ff755923001cfe755923001cfc7559230026bf7459230004ff7259230
  | 16 => 0x8440026f64058440026f54058440026f44058440026f73058440026f63058440026f53058440026f43058440026f72058440026f62058440026f52058440026f42058440004ff7654440004fd7654440024fc765444001e7e65544400067d6554440006de6354440006dd63544401a6ee6254440006ed625444000ef66154440006f56154440005fb7054440025f8705444003dbf7650440126bf765044003f3e655044003f3d6550440005bc735044003f9e6350440006bd635044003f9d63504400069d63504400e5be72504400e5bc725044003fae6250440006bd625044003fad6250440006ad625044003dbf715044003fb7715044000ebe615044003fb6615044000eb6615044003fb5615044000ebc615044029dbf705044029ebe605044003fba605044029fb71050440084ff76cc440024fe76cc440004fd76cc44017e7e65cc4400067d65cc440005bf74cc44003dbc74cc440086de63cc440006dd63cc440176ee62cc440006ed62cc44000ef661cc440006f561cc440004ff764c440004fd764c440024fc764c44016e7e654c4400067d654c440005bf744c44003dbc744c440006de634c440006dd634c440166ee624c440006ed624c44000ef6614c440006f5614c440004ff7648440004fd7648440024fc764844015e7e65484400067d6548440005bf744844003dbc7448440006de6348440006dd6348440016ee6248440006ed624844000ef66148440006f5614844003cfe74d9730004fd74d97300d67f54d9730086de73d9730014fe72d9730004fd72d9730014fc72d973000cfe71d9730004fd71d973000cfc71d97300d67f51d9730086f970d97302de7e50d97302de7c50d97300867c65597300867f7559730004ff745973003cfc7459730024fc73597300867e53597300867c5359730004ff7259730014fe7259730014fc72597300d67f5259730004ff715973000cfe715973000cfc71597300067e51597300d67c51597300d67f505973001cfe75d9330004fd75d9330084fc75d9330086de73d9330014fe72d9330004fd72d9330014fc72d933000cfe71d9330004fd71d933000cfc71d9330086f970d933031ebe40d933031ebc40d93300d57e75993300057d7599330086bf6499330086bc6499330086bc6459330004ff755933001cfe755933001cfc7559330086bf7459330024fc7359330086be4359330086bc4359330004ff7259330014fe7259330014fc7259330006be4259330006bc4259330004ff715933000cfe715933000cfc715933003cff7695330084fe7695330004fd7695330084fc76953300d73f5495330085de7395330005dd7395330004ff7655330084fe7655330004fd7655330084fc76553300067f655533001e7c6555330005fb7055330025f8705533008cff7654f300d57e75d0f300057
  | 17 => 0x6ee7558840006ed7558840006ec755884003eef74588400e6af745884003eee745884003eec745884003eef545884003eee545884003eed545884003eec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec535884003eef435884003eee435884003eed435884003eec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ee5158840006ec515884003eef415884003eaf415884003eee415884003eed415884003eec4158840006ee3158840006ec3158840026ef7058840026ee7058840026ec7058840026ef5058840026ee5058840026ed5058840026ec5058840026ef4058840026ee4058840026ed4058840026ec4058840026ef3058840026ee3058840026ed3058840026ec3058840026ef1058840026ee1058840026ed1058840026ec1058840004ff7654840004fd7654840024fc765484001e7e65548400067d6554840005bf745484003dbc7454840006de6354840006dd6354840016ee6254840006ed62548401eef66154840084ff76cc840024fe76cc840004fd76cc8401c67e65cc8400067d65cc84003dbe74cc840005bd74cc840086de63cc840006dd63cc8403179c43cc840016ee62cc840006ed62cc8401bef661cc840004ff764c840004fd764c840024fc764c8400057f754c8400ed7c754c8401b67e654c8400067d654c840005bf744c84003dbc744c840006de634c840006dd634c84030f9c434c840016ee624c840006ed624c840005f7714c8400ddf4714c8401aef6614c840005fb704c840025f8704c840004ff755844001cfe755844001cfc755844000cfd7458440004ff7358440084fc7358440004ff7258440014fe7258440014fc7258440024ff7158440026f77158440006f751584400def651584400def4515844003ef7415844003ef441584400def631584400def43158440006f721584400def621584400def42158440024fc7058440026f61058440026f41058440006f77558440006f67558440006f57558440006f4755844003ef7745844003ef6745844003ef4745844003ef7545844003ef6545844003ef5545844003ef45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f4535844003ef7435844003ef6435844003ef5435844003ef44358440006f77258440006f67258440006f57258440006f47258440006f75258440006f65258440006f55258440006f4525844003ef7425844003ef6425844003ef5425844003ef44258440006f73258440006f63258440006f53258440006f43258440026f77058440026f67058440026f47058440026f75058440026f65058440026f55058440026f45058440026f7405
  | 18 => 0xf2198c40006de2198c40006dc2198c40026de7098c40026dd7098c40026dc7098c40026df5098c40026de5098c40026dd5098c40026dc5098c40026df4098c40026de4098c40026dd4098c40026dc4098c40026df2098c40026de2098c40026dd2098c40026dc2098c40026df1098c40026de1098c40026dd1098c40026dc1098c40004ff7558c4001cfe7558c4001cfc7558c40026df7358c40006df5358c40006dc5358c4003edf4358c4003ebc4358c4003edc4358c40004ff7258c40014fe7258c40014fc7258c40006de3258c40006dc3258c40004ff7158c4000cfe7158c4000cfc7158c4003ebf4158c40006de3158c40006dc3158c40026de3058c40026dc3058c40006df7558c40006de7558c40006dd7558c40006dc7558c4003edf7458c4003ede7458c4003edc7458c4003edf5458c4003ede5458c4003edd5458c4003edc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006de5258c40006dc5258c4003edf4258c4003ede4258c4003edd4258c4003edc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006de5158c40006dc5158c4003edf4158c4003e9f4158c4003ede4158c4003edd4158c4003edc4158c40006df2158c40006de2158c40006dc2158c40026df7058c40026de7058c40026dc7058c40026df5058c40026de5058c40026dd5058c40026dc5058c40026df4058c40026de4058c40026dd4058c40026dc4058c40026df2058c40026de2058c40026dd2058c40026dc2058c40026df1058c40026de1058c40026dd1058c40026dc1058c40084ff7694c40024fe7694c40004fd7694c4001e7e6594c400067d6594c40086de6394c40006dd6394c400ef5f5394c4026eee6294c40266f66194c40004ff7654c40004fd7654c40024fc7654c4001e7e6554c400067d6554c40005bf7454c4003dbc7454c40006de6354c40006dd6354c4025eee6254c40256f66154c40005fb7054c40025f87054c4003dbd7690c40006bd7690c4003f3e6590c4003f3d6590c4003dbe7390c4003f9e7390c4003f9e6390c40006bd6390c4003f9d6390c400069d6390c400e5be7290c400e5bc7290c4003fae6290c4003fad6290c40005bd7190c4003fb66190c4003fb56190c4031dbd7090c4031ebe6090c4003fba6090c40004ff755884001cfe755884001cfc7558840014fd7458840004ff7358840084fc7358840024ff7258840026ef7258840006ef52588400e6ee52588400e6ec525884003eef42588400e6be425884003ebc425884003eec42588400e6ee32588400e6ec3258840004ff715884000cfe715884000cfc715884003ebf41588400e6ef2158840006ee21588400e6ec2158840024fc7058840026ee2058840026ec2058840006ef7558840
  | 19 => 0x85400f6f710d85400057f75585401057c7558540005df7358540005dc7358540005ef72585400fdec72585400f6f46158540004ff7654540004fe7654540004fc7654540024fc7650540006f7615054000ef46150540005fb7050540025f87050540004fe76cc540004fd76cc540084fc76cc540004ff764c540004fe764c540004fc764c540004ff7648540004fe7648540004fc764854001cff7654140104fd765414003cfc76541400067f655414001e7c6554140005bf745414003dbc7454140027b84054140024ff75594400267f755944003cff745944003cfe745944003cfd745944003cfc745944003e7e545944003e7c5459440004ff7359440084fc73594400ee7f53594400ee7c5359440004ff7259440014fe7259440014fc72594400ee7f52594400067e52594400ee7c5259440004ff715944000cfe715944000cfc71594400ee7f51594400067e51594400ee7c5159440024fe7059440024fc70594400267e50594400267c505944003e7f745944003e7e745944003e7d745944003e7c74594400067f73594400067e73594400067d73594400067c735944003e7f435944003e7e435944003e7d435944003e7c43594400067f72594400067e72594400067d72594400067c725944003e7f425944003e7e425944003e7d425944003e7c42594400067e32594400067c32594400067f71594400067e71594400067d71594400067c715944003e7f415944003e7e415944003e7d415944003e7c41594400067e31594400067c31594400067f21594400067e21594400067c21594400267f70594400267e70594400267d70594400267c70594400267f40594400267e40594400267d40594400267c40594400267f30594400267e30594400267d30594400267c30594400267f20594400267e20594400267d20594400267c20594400267f10594400267e10594400267d10594400267c105944001cfe7598c40004fd7598c40084fc7598c40024fe7398c40026de7398c40006df5398c40086dc5398c4003edf4398c40086dc4398c40014fe7298c40004fd7298c40014fc7298c40006de3298c40086dc3298c4000cfe7198c40004fd7198c4000cfc7198c40006de3198c40086dc3198c40026de3098c40026dc3098c40086df7598c40006de7598c40006dd7598c40086dc7598c4003ede7498c4003edd7498c40086dc7498c4003edf5498c4003ede5498c4003edd5498c4003edc5498c40086df7298c40006de7298c40006dd7298c40086dc7298c40006df5298c40006de5298c40006dc5298c4003edf4298c4003ede4298c4003edd4298c4003edc4298c40086df7198c40006de7198c40006dd7198c40086dc7198c40006df5198c40006de5198c40006dc5198c4003edf4198c4003ede4198c4003edd4198c4003edc4198c40006d
  | 20 => 0x24fe76cc640004fd76cc640005bf74cc64003dbc74cc640004ff764c640004fd764c640024fc764c640005bf744c64003dbc744c640004ff7648640004fd7648640024fc7648640005bf744864003dbc744864001cfe76d95401067e65d954003cfe74d9540024fd74d954003cfc74d95401067f54d9540084fe73d9540004fd73d95401067c53d9540014fe72d9540004fd72d9540014fc72d95401067f52d954000cfe71d9540004fd71d954000cfc71d95400067e51d95401067c51d954003cfd70d95401067f50d95401067c6559540005df7359540005dc7359540104ff75595400067f755954011cff7459540006bf7459540004ff7359540006df7359540004df7359540084fc7359540006dc7359540004dc7359540004ff7259540014fe7259540014fc7259540004ff715954000cfe715954000cfc7159540134ff7059540006fb7059540024fc76551400067f655514001e7c6555140005fb7055140025f8705514003fb8405514001cfe75d8d40004fd75d8d4001cfc75d8d40006df53d8d40006dc53d8d40014fe72d8d40004fd72d8d40014fc72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d40006de31d8d40006dc31d8d40006df6398d400057f7558d401057c7558d40006dd6318d4001cfe7518d40004fd7518d40084fc7518d40006df5318d40086dc5318d40014fe7218d40004fd7218d40014fc7218d4000cfe7118d40004fd7118d4000cfc7118d40006de3118d40086dc3118d40326be4018d40326bc4018d40004fe7694d40004fd7694d40084fc7694d400067f6594d4001e7c6594d401075f5394d40004ff7654d40004fe7654d40004fc7654d40024fe7690d40006df6390d40086dc6390d40025fa7090d40005f97090d4003fb84090d40024fc7650d40006df6350d40006dc6350d40005fb7050d40025f87050d40014fe76d89400feee62d894001cfe75d8940004fd75d894001cfc75d8940024fd74d8940014fc74d8940084fe73d8940004fd73d89400feee42d894000cfe71d8940004fd71d894000cfc71d8940006ee21d89400feec21d894003cfd70d89400feef20d89400feec6258940004ff7654940004fe7654940004fc76549400067f655494001e7c6554940024fc7650940006ef6250940016ec6250940005fb7050940025f87050940004fe76cc940004fd76cc940084fc76cc940006df63cc940086dc63cc940004ff764c940004fe764c940004fc764c9400057f754c9401057c754c940006df634c940006dc634c940005f7714c9400f5f4714c94000cfe76d85400f6f661d854001cfe75d8540004fd75d854001cfc75d8540024fd74d854000cfc74d8540084fe73d8540004fd73d8540014fe72d8540004fd72d8540014fc72d85400f6f641d854003cfd70d8540306be40d8540306bc40d
  | 21 => 0xf7558e4001cfe7558e4001cfc7558e400067c7558e4001c7c7558e40026df7358e40004ff7258e40014fe7258e40014fc7258e40004ff7158e4000cfe7158e4000cfc7158e40024fc7058e40026de3058e40026dc3058e40084ff7694e40024fe7694e40004fd7694e402de7f6594e4001e7c6594e4011f5f5394e40004ff7654e40004fd7654e40024fc7654e40005bf7454e4003dbc7454e40086de6390e40006dd6390e40025fa7090e40005f97090e4003dbe7390e4031f9e6390e40006bd6390e4031f9d6390e40115be7290e40115bc7290e40005bd7190e4031fba7090e4031dbd7090e40007b97090e4003ebe6090e40006de6350e40006dd6350e4003f9c4350e40005fb7050e40025f87050e40325bd7610e4003ebd7610e4003f9e7310e40006bd6310e40115be7210e4003dbc7210e40005bd7110e4003dbf7010e40325bd7010e4003fba6010e40004ff7558a4001cfe7558a4001cfc7558a40004ff7358a40084fc7358a40026ef7258a40116be4258a40116ee4258a40116bc4258a40116ee3258a40004ff7158a4000cfe7158a4000cfc7158a40024fc7058a40026ee2058a40026ec2058a40004ff7654a40004fd7654a40024fc7654a402d67f6554a4001e7c6554a40005bf7454a4003dbc7454a40014ff7650a402f5bf7450a40016ee6250a40006ed6250a40005fb7050a40025f87050a40084ff76cca40024fe76cca40004fd76cca4003dbe74cca40005bd74cca40086de63cca40006dd63cca400079c43cca40004ff764ca40004fd764ca40024fc764ca400057f754ca4011d7c754ca40005bf744ca4003dbc744ca40006de634ca40006dd634ca400079c434ca40016ee624ca40006ed624ca40005f7714ca4010df4714ca40004ff75586400067f75586400047f755864001cfe755864001cfc75586400067c755864001c7c7558640004ff7358640084fc7358640004ff7258640014fe7258640014fc7258640026f7715864010ef6515864010ef64158640024fc7058640026f61058640026f41058640004ff7654640004fd7654640024fc765464001e7e65546400067d655464000ef66154640006f56154640305bd76d064003ebd76d064003f3e75d064003f3d75d0640005be73d0640006bd63d0640115be72d064003dbc72d0640006bd62d064000ebe61d064000ebc61d064003dbf70d0640305bd70d064003fba60d064000cff765064000ef66150640006f56150640005fb7050640025f8705064029dbf765064000ebf765064000cbf7650640005bc7350640006bd6350640115be7250640115bc7250640006bd625064003dbf715064003fb7715064000ebe615064029fb6615064029fb5615064000ebc615064029dbf7050640007bb705064029fb8705064003ebe605064029fb71050640084ff76cc640
  | 22 => 0xc550004fe764c550004fc764c550006df634c550006dc634c550004ff7648550004fe7648550004fc764855003e7f7559740024fc745974003e7e545974003e7c5459740004ff7359740084fc73597401367c5359740004ff7259740014fe7259740014fc72597401367f5259740004ff715974000cfe715974000cfc71597400067e51597401367c51597401367f505974001cfe7598f40004fd7598f40084fc7598f40024fe7498f40086de7398f4003edf4398f40086dc4398f40014fe7298f40004fd7298f40014fc7298f4000cfe7198f40004fd7198f4000cfc7198f4031ebe4098f4003ebc4098f40004ff7558f4001cfe7558f4001cfc7558f40024fc7458f4003edf7358f4003edf4358f4003edc4358f40004ff7258f40014fe7258f40014fc7258f40004ff7158f4000cfe7158f4000cfc7158f40084ff7694f4003cfe7694f40004fd7694f4001e7e6594f400067d6594f401375f5394f40004ff7654f40004fd7654f4003cfc7654f40005fb7054f40025f87054f40004ff7558b4001cfe7558b4001cfc7558b40024fc7458b40004ff7358b40084fc7358b4003eef7258b4003eef4258b4003eec4258b40004ff7158b4000cfe7158b4000cfc7158b4012eef2058b40004ff7654b40004fd7654b4003cfc7654b4001e7e6554b400067d6554b40084ff76ccb4003cfe76ccb40004fd76ccb40004ff764cb40004fd764cb4003cfc764cb400057f754cb401357c754cb40005f7714cb40125f4714cb40005fb704cb40025f8704cb40004ff755874001cfe755874001cfc7558740024fc7458740004ff7358740084fc7358740004ff7258740014fe7258740014fc725874003ef7715874003ef7415874003ef4415874029ebe405874003ebc4058740126f71058740004ff7654740004fd765474003cfc7654740005fb7054740025f87054740084ff76cc74003cfe76cc740004fd76cc740004ff764c740004fd764c74003cfc764c740004ff7648740004fd764874003cfc764874001cff765434003cfc765434001e7e65543400067d6554340005bf745434003dbc7454340027785054340027ba40543400267f755964011e7f5459640004ff7359640084fc7359640004ff7259640014fe7259640014fc7259640004ff715964000cfe715964000cfc715964011e7f5159640024fc70596400267e50596400267c505964003efb4059240026be4059240026bc4059240026f8405924001cff7655240024fc765524001e7e65552400067d6555240005fb7055240025f8705524003fbb405524001cfe7598e40004fd7598e40084fc7598e40026de7398e40014fe7298e40004fd7298e40014fc7298e4000cfe7198e40004fd7198e4000cfc7198e40024fe7098e40026de3098e40026dc3098e40004ff7558e400067f7558e400047
  | 23 => 0x257e70551500257c705515000778705515002578705515001e7f605515001f7b6055150024fd75d8d5003cfe74d8d50004fd74d8d500bede53d8d500bedd53d8d50014fe72d8d50004fd72d8d50014fc72d8d50006de32d8d50006dc32d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006df6398d500a5f97098d50005bf7458d50005bc7458d500d5fb7058d50006dd6318d50024fd7518d5003cfe7418d50004fd7418d5008e7f5418d500067d5418d50086de5318d5008edd5318d50014fe7218d50004fd7218d50014fc7218d50006de3218d50086dc3218d5000cfe7118d50004fd7118d5000cfc7118d5008e7f5118d5032e7e5018d5032e7c5018d50004fe76d0d50004fd76d0d5003cfc76d0d5001d7e75d0d500057d75d0d50006df63d0d50006dc63d0d50004fe7690d50004fd7690d50084fc7690d50006bf6490d5003ebc6490d50004ff7650d50004fe7650d50004fc7650d50004fe7610d50004fd7610d50084fc7610d5001d7e7510d500057d7510d50006bf6410d5003ebc6410d50006df6310d50086dc6310d50014fe76d8950146ee62d8950024fd75d8950014fc75d895003cfe74d8950004fd74d895006e7f54d89500067d54d8950084fe73d8950004fd73d8950146ee52d895006eed52d895000cfe71d8950004fd71d895000cfc71d895006e7f51d895001cfd70d89503467e50d89503467c50d8950146ef20d8950005bf7458950005bc7458950005df7358950005dc7358950146ec6258950005f7715895013df4715895033dfb7058950004fe76d0950004fd76d095003cfc76d095001d7e75d09500057d75d0950004ff7650950004fe7650950004fc7650950004fe76cc950004fd76cc950084fc76cc950004ff764c950004fe764c950004fc764c9500057f754c95001d7c754c950005f7714c95013df4714c95000cfe76d855013ef661d8550024fd75d855000cfc75d855003cfe74d8550004fd74d8550084fe73d8550004fd73d8550014fe72d8550004fd72d8550014fc72d855013ef651d855004ef551d8550006f721d855013ef421d855001cfd70d855013ef710d855013ef46158550335fb70585500257c765455000e7c76545500247c76545500057f74545500067c63545500067f625455001d7f715455001f77715455000777615455000e7e615455000e7c615455013f7461545500077b70545500257e70545500257c705455000778705455001e7f605455001f7b605455013f771054550004fe76d0550004fd76d055003cfc76d055001d7e75d05500057d75d0550006bf64d055003ebc64d0550004ff7650550004fe7650550004fc765055001d7e75505500057d7550550006bf645055003ebc6450550004fe76cc550004fd76cc550084fc76cc550006df63cc550086dc63cc550004ff764
  | 24 => 0xa7094e502dd7d7094e50007797094e50005797094e5001e7e6094e5001f7a6094e5003cff76d0e50024fe76d0e50004fd76d0e5001d7e75d0e500057d75d0e50084ff7690e50024fe7690e50004fd7690e50086de6390e50006dd6390e50004ff7650e50004fd7650e50024fc7650e500057f7550e5001d7c7550e50006de6350e50006dd6350e50084ff7610e50024fe7610e50004fd7610e50004ff7458a5003cfc7458a50004ff7358a50084fc7358a50026ef7258a50156ee5258a5005eed5258a50156ee4258a50156ee3258a50004ff7158a5000cfe7158a5000cfc7158a50006ee2158a50156ec2158a50024fe7058a50024fc7058a50026ee2058a50026ec2058a502d57f7654a500167f7654a500147f7654a500067d6454a500057c7354a5001d7f7254a5001f6f7254a500167e6254a502d76e6254a502d76d6254a500167c6254a5014d7e7154a5014d7c7154a502d57f7054a500077b7054a500057b7054a502d7787054a5001e7e6054a5001f7a6054a5003cff76d0a50024fe76d0a50004fd76d0a50004ff7650a50004fd7650a50024fc7650a50016ee6250a50006ed6250a50084ff76cca50024fe76cca50004fd76cca500057f75cca5001d7c75cca50086de63cca50006dd63cca50004ff764ca50004fd764ca50024fc764ca500057f754ca5001d7c754ca50006de634ca50006dd634ca50016ee624ca50006ed624ca50005f7714ca5014df4714ca50004ff745865003cfc7458650004ff7358650084fc73586500067e53586500367c5358650004ff7258650014fe7258650014fc72586500367f52586500067d5258650026f7715865014e7e515865014ef6515865014e765158650036f5515865014e7c515865014ef64158650024fe7058650024fc70586500267f50586500267d5058650026f61058650026f4105865003cff76d0650024fe76d0650004fd76d065001d7e75d06500057d75d0650004ff7650650004fd7650650024fc76506500057f755065001d7c755065000ef66150650006f56150650084ff76cc650024fe76cc650004fd76cc65001d7e75cc6500057d75cc650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c650004ff7648650004fd7648650024fc76486500057f754865001d7c7548650024fd75d915011ebe54d915011ebd54d9150084fe73d9150004fd73d9150014fe72d9150004fd72d9150014fc72d9150006be42d9150006bc42d915000cfe71d9150004fd71d915000cfc71d9150006bf6499150105f97099150005df7359150005dc7359150135fb705915003ebe6419150006bd64191500247c765515001d7f745515001f3f74551500073f645515003e7e645515003e7c64551500073c64551500057f71551502767e61551502767c61551500077b7055150
  | 25 => 0x8d21176f72198d211bef42198d21024fe7098d21004fd7098d210057f7558d2115d7c7558d211bdef7258d21175f77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d2103cfc7458d21006df7358d211bcff7258d21006ef7258d211acff7158d21006f77158d21174f77158d21004ff7058d21024fc7058d2135cfe7618d21006dd6318d2101cfe7518d21004fd7518d21084fc7518d2103cfe7418d21004fd7418d21084fe7318d21086de7318d21006df5318d21086dc5318d2100cff7218d2100cfd7218d21086df3218d21356dd3218d21014ff7118d21014fd7118d21086df3118d2134edd3118d21356f72118d2134ef42118d21024fe7018d21004fd7018d21084ff7694d21004fe7694d21004fd7694d21084fc7694d210067f6594d2101e7c6594d2115f5f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d2103cff76d0d21004fe76d0d21004fd76d0d2103cfc76d0d2115d7e75d0d210057d75d0d21084ff7690d21004fe7690d21004fd7690d21084fc7690d21006df6390d21086dc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21006dc6350d21084ff7610d21004fe7610d21004fd7610d21084fc7610d2100df67110d21005f57110d21024fe76d812101cfe75d8121004fd75d812101cfc75d812103cfe74d8121004fd74d8121084fe73d8121004fd73d812100cfd72d8121014fd71d81212e6fa20d81212a6fa10d8121006fb60981210057f755812115d7c7558121005bf7458121005bc7458121005df7358121005dc7358121026fa6018121006f96018121026bf7459250106be5459250106bd5459250004ff7359250084fc73592501067c5359250004ff7259250014fe7259250014fc72592501067f5259250004ff715925000cfe715925000cfc71592500067e51592501067c5159250024fc70592500267f50592500267d5059250026be4059250026bc405925003cfe7498e50004fd7498e50026de7398e50086de5398e500d6dd5398e50014fe7298e50004fd7298e50014fc7298e5000cfe7198e50004fd7198e5000cfc7198e50006de3198e50086dc3198e50024fe7098e50024fc7098e50026de3098e50026dc3098e50004ff7458e5003cfc7458e50026df7358e500a6de5358e500a6dd5358e500a67c5358e50004ff7258e50014fe7258e50014fc7258e50004ff7158e5000cfe7158e5000cfc7158e50006de3158e50006dc3158e50024fc7058e50026de3058e50026dc3058e500067d6494e5001d7e7394e5001f5e7394e502df5e6394e500067d6394e502df5d6394e500065d6394e500057d7294e5026e7e6294e502de7c6294e5014d7e7194e5014d7c7194e502df7
  | 26 => 0x75c754c93130ede644c93130edc644c9311bddf724c931007cf724c931007cf624c931016de624c931016dc624c931167cc624c931016cc624c931007d7714c93100dde714c93100ddc714c9311afd4714c93100dd4714c9311aedf614c931167cf204c93100df673cc53100fd673cc53100ef763cc53100fd763cc531176f662cc531176f462cc531087d732cc531007d532cc53101cfe75d8131004fd75d813101cfc75d813103cfe74d8131004fd74d8131014fe72d8131004fd72d8131014fc72d8131006df32d8131006dd32d81310c6fa10d8131006fb60981310057f755813116d7c7558131005bf7458131005bc7458131005ef7258131165ec7258131026fa6018131006f9601813101cfe76d952115e7e65d95211ecfd75d952103cfe74d9521004fd74d952115e7f54d9521084fe73d9521004fd73d952115e7c53d952100cff72d952100cfd72d95213967f52d95213967d52d9521014ff71d9521014fd71d95213867f51d95213867d51d9521024fe70d9521004fd70d952115e7c50d952101cff765952115e7c6559521005df7359521005dc735952137def725952138df77159521384ff75595210067f7559521004ff745952103cfc7459521004ff7359521006df7359521004df7359521084fc7359521006dc7359521004dc735952137cff7259521006ef72595211ecff7159521006f77159521004ff7059521024fc705952103cfe76d912101cfe75d9121004fd75d912101cfc75d9121084fe73d9121004fd73d912100cff72d912100cfd72d9121376bf42d9121376bd42d9121014ff71d9121014fd71d912136ebf41d912136ebd41d9121024fe70d9121004fd70d91211ccfd769912115d7e75991210057d7599121006bf6499121005de7399121005dd73991211cded7299121185f5719912103cff76591211ddef7259121195f77159121004ff755912101cfe755912101cfc7559121006bf7459121004ff7359121084fc73591211dcff7259121006ef72591211ccff7159121006f77159121004ff7059121024fc705912136cfe761912103ebe6419121006bd641912103cff7695121004fe7695121004fd769512103cfc769512115f3f5495121004ff7655121004fe7655121004fd7655121004fc76551210067f655512101e7c655512101cfe75d8d21004fd75d8d2101cfc75d8d2103cfe74d8d21004fd74d8d21006df53d8d21006dc53d8d2100cff72d8d2100cfd72d8d21366df32d8d21366dd32d8d21014ff71d8d21014fd71d8d2135edf31d8d2135edd31d8d21024fe70d8d21004fd70d8d211acfd7698d21006df6398d211aded7298d21165f57198d2101cfe7598d21004fd7598d21084fc7598d2103cfe7498d21004fd7498d21084fe7398d211acfd7298d21086ed7298d211bcfd7198d21086f5719
  | 27 => 0xd72d9531014fc72d95310067e52d953116e7c52d9531084ff71d9531264fd71d95312667f51d95312667d51d9531024fe70d9531004fd70d953116e7c50d953116e7c65595313a5df7359531005ef7259531165ec7259531264ff75595310067f7559531004ff745953103cfc74595313a4ff7359531006df735953116e7c5359531004ff7259531006ef7259531004ef7259531014fe7259531014fc7259531006ec7259531014ec7259531254ff7159531006f77159531004ff7059531024fc705953103cfe76d913101cfe75d9131004fd75d913101cfc75d9131014fe72d9131004fd72d9131014fc72d9131084ff71d9131224fd71d9131226bf41d9131226bd41d9131024fe70d9131004fd70d913116d7e75991310057d7599131006bf649913120ddd7399131165ee7299131005ed729913123ddf7359131004ff755913101cfe755913101cfc7559131006bf745913123cff7359131006df7359131004ff7259131014fe7259131014fc725913120cff7159131006f77159131004ff7059131024fc7059131224fe761913103ebe6419131006bd641913103cff7695131004fe7695131004fd769513103cfc769513116f3f5495131005de7395131005dd739513100df67195131005f57195131004ff7655131004fe7655131004fd7655131004fc76551310067f655513101e7c655513139cfe7694d3101e7e6594d310067d6594d3116f5f5394d31087d43194d3101cff7654d3100cfe7654d31254fd7654d3100cfc7654d310067f6554d3101e7c6554d31005f77154d3100df47154d31257d43154d3100cfe76d0d3100cfc76d0d3116d7e75d0d310057d75d0d31006bf64d0d3103ebc64d0d3100df671d0d31005f571d0d311f4fe7690d31087d43190d3103cff7650d3100cfe7650d3120cfd7650d3100cfc7650d31006bf6450d3103ebc6450d31005f77150d3100df47150d3120fd43150d31224fe7610d310079d4310d31014fe76d8931166ee62d893101cfe75d8931004fd75d893101cfc75d893103cfe74d8931004fd74d893100cfd73d8931006ef52d8931166ec52d8931166ee42d8931166ee32d89311beef21d8931024fe70d8931004fd70d8931166ec20d89310057f755893116d7c7558931166ec6258931004ff7654931004fe7654931004fc7654931004fe76d0931004fd76d093103cfc76d0931004ff7650931004fe7650931004fc7650931006ef6250931016ec625093134cfe76cc93134dde76cc931366de76cc931316de64cc931316dc64cc9311addd72cc931016de62cc931016dc62cc93100dde71cc93100ddc71cc931086df61cc93100cfc764c9310057f754c93116d7c754c931006ef624c931016ec624c931005f7714c93100df4714c93100ddc764c931016dc764c93100cdc764c9310075f754c931
  | 28 => 0x9731014fc72597312567f51597312567d5159731004ff7059731024fc705973117e7c505973101cfe75d9331004fd75d9331084fc75d9331084fe73d9331086de73d9331014fe72d9331086ee72d9331014ee72d9331004fd72d9331086ed72d9331004ed72d9331014fc72d9331086f571d9331024fe70d9331004fd70d933120cfd7699331086bf6499331086bc649933103cff7659331086bc6459331004ff755933101cfe755933101cfc7559331086bf745933100cfe735933100cfc7359331086be4359331086bc4359331004ff7259331014fe7259331014fc725933120ebf415933120ebd4159331004ff7059331024fc705933103cff7695331084fe7695331004fd7695331084fc769533117f3f5495331085de7395331005dd7395331004ff7655331084fe7655331004fd7655331084fc765533101e7e65553310067d65553313a4ff7654f31257d63154f3120cfd76d0f3117d7e75d0f310057d75d0f31086bf64d0f31086bc64d0f3123cff7650f31086bf6450f31086bc6450f310879c4350f31014ff7658b31086ec6258b3100df47158b31177e72158b31004ff7558b3101cfe7558b3101cfc7558b31004ff7458b3103cfc7458b3100cfc7358b31176ec4258b31086ef3258b31086ec3258b31176f77158b311aeef2158b31176f72158b311aef42158b31004ff7058b31024fc7058b31176ef2058b31004ff7654b31004fd7654b31084fc7654b31005f77154b3100df47154b3103cff76d0b31084fe76d0b31004fd76d0b31016ee62d0b31006ed62d0b3100df671d0b31005f571d0b31004ff7650b31004fd7650b31084fc7650b31005f77150b3100df47150b3100ddd76ccb31016dd76ccb3100cdd76ccb31316de64ccb31086dc64ccb31016de62ccb31087ce62ccb31087cd62ccb31016dc62ccb3100dde71ccb31087d671ccb31087d571ccb3100ddc71ccb31177d721ccb311bfd421ccb3135cff764cb310057f754cb3117d7c754cb31175f7714cb3100df4714cb3135ddf764cb31356df764cb310075f754cb310075c754cb3130ede644cb3130edc644cb31087cf724cb31016de624cb31016dc624cb31177d7714cb3100dde714cb3100ddc714cb311afd4714cb3100dd4714cb31177d7214cb311afd4214cb31177cf204cb31086fb6098331026f86098331005bf7458331005bc7458331086f86058331004ff755833101cfe755833101cfc7558331004ff7458331006bf7458331004bf745833103cfc7458331006bc745833103cbc745833100cfc7358331004ff7258331014fe7258331014fc7258331006df3258331006dd3258331086fb3058331086f83058331096fa105833101cfe76d953116e7e65d953103cfe74d9531004fd74d953116e7f54d953100cfd73d953116e7f53d9531014fe72d9531004f
  | 29 => 0x3ebe76d0d4103f3e75d0d4103f3d75d0d41086bc63d0d41005bd72d0d4100dbe71d0d4100dbc71d0d4103ebf61d0d4103fb761d0d4129dbe70d0d4123fb710d0d4100cfe7690d4120dbd7490d41006df6390d41086dc6390d4100df67190d41005f57190d4100cfc7650d41006df6350d41006dc6350d4103f9c4350d41005f77150d4100df47150d4103fb44150d4100dbc7650d4120ebc7650d4100cbc7650d4103dbf7350d4103f9f7350d410079f6350d41086bc6350d410079c6350d41005bf7250d41007b77150d4100dbe7150d4100dbc7150d4120fb47150d4103ebf6150d4103fb76150d4129dbc7050d4120fb71050d41014fe76d8941186ee62d894101cfe75d8941004fd75d894101cfc75d894100cfd74d8941084fe73d8941004fd73d8941006ef52d8941186ec52d8941186ee42d8941186ee32d894103cfd71d89411deef21d8941024fe70d8941004fd70d8941186ec20d8941186ec6258941004ff7654941004fe7654941004fc765494101e7e65549410067d6554941005f7715494100df471549413adbe76d094103ebe76d0941005bd73d09411cdbd72d0941016be62d0941016bc62d094100dbe71d094100dbc71d094103ebf61d094103fb761d094129dbe70d09411dfb710d094100cfc7650941006ef6250941016ec6250941005f7715094100df4715094100dbc7650941016bc765094100cbc7650941005bf735094103dbf725094103faf7250941007af6250941016be6250941016bc6250941187ac6250941007b7715094100dbe715094100dbc71509411cfb4715094103ebf615094103fb7615094129dbc7050941187af20509411cfb71050941004fe76cc941004fd76cc941084fc76cc94103dbe74cc941005bd74cc941006df63cc941086dc63cc9410079f43cc941004ff764c941004fe764c941004fc764c9410057f754c94118d7c754c94103dbe744c941005bd744c941006df634c941006dc634c9410079f434c941006ef624c941016ec624c941005f7714c94100df4714c94101cfe75d8141004fd75d814101cfc75d8141126bd74d8141084fe73d8141004fd73d8141014fe72d8141004fd72d8141014fc72d814103cfd71d8141006fb50d8141006f850d8141126fa10d8141006fb60981410057f755814118d7c7558141005df7358141005dc7358141005ef7258141185ec725814118d7e75181410057d7518141026fa6018141006f96018141254fd75d973103cfe74d9731004fd74d9731084fe73d9731086de73d9731014fe72d9731004fd72d9731014fc72d9731086f571d9731024fe70d9731004fd70d973101cff76597310867c65597310867f7559731004ff745973103cfc745973117e7f545973100cfe735973100cfc73597310867e53597310867c5359731004ff7259731014fe725
  | 30 => 0xc7654b4101e7e6554b410067d6554b4103dbf7650b413bebf7650b4103f3e6550b4103f3d6550b41005bf7350b4103faf7250b41016be6250b41016bc6250b4100dbe7150b4100dbc7150b41305bc7050b41197af2050b41084ff76ccb4103cfe76ccb41004fd76ccb411c67e65ccb410067d65ccb4103dbe74ccb41005bd74ccb413179f43ccb41016ee62ccb41006ed62ccb41004ff764cb41004fd764cb4103cfc764cb410057f754cb4119d7c754cb411b67e654cb410067d654cb4103dbe744cb41005bd744cb4130f9f434cb41005f7714cb4100df4714cb41004ff755834101cfe755834101cfc755834100cfc745834103ebc745834100cbc7458341004ff7358341084fc7358341004ff7258341014fe7258341014fc725834103ef6415834103ef5415834103efb705834103efb405834103ebc405834103ef840583410f6fa105834101cfe76d954118e7e65d954100cfd74d954118e7f54d9541084fe73d9541004fd73d9541014fe72d9541004fd72d9541014fc72d954103cff71d954103cfd71d95412867f51d95412867d51d9541024fe70d9541004fd70d954118e7c50d9541286f710d954118e7c65595413b5bf7459541005df7359541005dc7359541005ef7259541185ec7259541005fb7059541005f87059541284ff75595410067f75595413b4ff7459541006bf7459541004ff7359541006df7359541004df7359541084fc7359541006dc7359541004dc735954118e7c5359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec725954118e7f5259541274ff7159541006f771595412767e51595412767c5159541004ff7059541006fb7059541004fb7059541024fc7059541006f87059541024f8705954118e7f5059541276f7105954101cff765514100cfe7655141274fd765514100cfc76551410067f655514101e7c6555141005f7715514100df4715514103fb4415514118d7e75d8d410057d75d8d4101cfe75d8d410067e75d8d4101c7e75d8d41004fd75d8d410067d75d8d410047d75d8d4101cfc75d8d41006df53d8d41006dc53d8d41014fe72d8d41004fd72d8d41014fc72d8d4103cfd71d8d4123edf31d8d41024fe70d8d41004fd70d8d41006df6398d41185ee7298d41005ed7298d41006dd6318d4101cfe7518d41004fd7518d41084fc7518d41086bd7418d41006df5318d41086dc5318d41014fe7218d41004fd7218d41014fc7218d41084ff7118d4103cfd7118d41086df3118d411f6dd3118d41024fe7018d41004fd7018d41004fe7694d41004fd7694d41084fc7694d4101e7e6594d410067d6594d4103dbe7494d41005bd7494d4118f5f5394d4100df67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d411f5be76d0d41
  | 31 => 0xc951024fe76d815100cfd75d815103cfe74d8151004fd74d8151084fe73d8151004fd73d8151014fe72d8151004fd72d8151014fc72d815101cfd71d8151336fa50d81512befa10d81512c67f6598151005de7398151005dd73981511a5ee7298151005ed7298151006fb60981512c67f6518151026fa6018151006f9601815103e7f755974100cfe745974100cfc745974103e7e545974103e7c5459741004ff7359741084fc735974119e7f535974119e7c5359741004ff7259741014fe7259741014fc725974119e7f52597410067e525974119e7c52597412767f51597412767d5159741004ff7059741024fc705974119e7f505974119e7c505974103e7f745974103e7e745974103e7d745974103e7c74597410067f73597410067e73597410067d73597410067c735974103e7f435974103e7e435974103e7d435974103e7c43597410067f72597410067e72597410067d72597410067c725974103e7f425974103e7e425974103e7d425974103e7c42597410067e32597410067c32597412767f71597412767e71597412767d71597412767c715974103e7f415974103e7e415974103e7d415974103e7c41597412767f31597412767e31597412767d31597412767c31597412767f21597412767e21597412767d21597412767c21597410067f70597410067e70597410067d70597410067c705974103e7f405974103e7e405974103e7d405974103e7c40597410067f20597410067c20597412767f10597412767e10597412767d10597412767c105974101cfe7598f41004fd7598f41084fc7598f4100cfe7498f41086be7498f4100cbe7498f4100cfc7498f41086de7398f41086bf4398f4103edf4398f41086dc4398f41014fe7298f41004fd7298f41014fc7298f41006de3298f41086dc3298f41086df3198f41226dd3198f41024fe7098f41004fd7098f4103ebc4098f41004ff7558f4101cfe7558f4101cfc7558f4100cfc7458f4103edf7358f4103edf4358f4103edc4358f41004ff7258f41014fe7258f41014fc7258f41006de3258f41006dc3258f4120edf3158f41004ff7058f41024fc7058f41084ff7694f4103cfe7694f41004fd7694f4101e7e6594f410067d6594f4103dbe7494f41005bd7494f4119f5f5394f41004ff7654f41004fd7654f4103cfc7654f4101e7e6554f410067d6554f4103dbf7650f41006bf7650f4103f3e6550f4103f3d6550f4103f9f7350f41086be6350f41005bf7250f4100dbe7150f4100dbc7150f41305bc7050f41004ff7558b4101cfe7558b4101cfc7558b4100cfe7458b4100cfc7458b41004ff7358b41084fc7358b4103eef7258b4103eef4258b4103eec4258b41196ec3258b411ceef2158b41004ff7058b41024fc7058b41196ef2058b41004ff7654b41004fd7654b4103cf
  | 32 => 0x3e6be54d91513e6bd54d9151084fe73d9151004fd73d91513e67c53d9151014fe72d9151004fd72d9151014fc72d91513e67f52d915101cfd71d91513b67e51d91513b67c51d91513b6bf41d9151024fe70d9151004fd70d91513e67f50d91513b6f710d9151006bf649915118df57199151005df7359151005dc7359151005ef72591511a5ec725915119df77159151005fb7059151005f8705915103ebe6419151006bd641915100cfd75d8d513a67d75d8d5103cfe74d8d51004fd74d8d513dede53d8d513dedd53d8d513de7c53d8d51014fe72d8d51004fd72d8d51014fc72d8d51006de32d8d51006dc32d8d5101cfd71d8d513a6df31d8d51024fe70d8d51004fd70d8d51006df6398d5116df57198d51005ef7258d511a5ec7258d5117df77158d51006dd6318d5100cfd7518d5103cfe7418d51004fd7418d51086de5318d513d6dd5318d51014fe7218d51004fd7218d51014fc7218d51006de3218d51086dc3218d51084ff7118d5101cfd7118d51086df3118d5139edd3118d51024fe7018d51004fd7018d5100d7e7694d512667e7694d5100c7e7694d510067f6494d5101d7e7394d5101f5e7394d510067f6394d510075f6394d510065f6394d510075c6394d510057d7294d5126e7e6294d5126e7c6294d5100d7e7194d51267767194d51007757194d5100d7c7194d5101e7f6194d5101f776194d510057d7094d512de7c6094d51267771094d51004fe76d0d51004fd76d0d5103cfc76d0d5101d7e75d0d510057d75d0d51006df63d0d51006dc63d0d51004fe7690d51004fd7690d51084fc7690d51004ff7650d51004fe7650d51004fc7650d510057f7550d5101d7c7550d51004fe7610d51004fd7610d51084fc7610d51006df6310d51086dc6310d51014fe76d89511a6ee62d895100cfd75d895103cfe74d8951004fd74d8951084fe73d8951004fd73d89511a6ee52d89513ceed52d89511a6ec42d89511a6ec32d895101cfd71d895137eef21d8951024fe70d8951004fd70d89511a6ef20d8951005df7358951005dc73589511a6ec62589513c5f7715895100d7c76549510167c765495100c7c76549510067f64549510057c735495101d7f725495101f6f72549510076f62549510167e62549510167c62549511a76c625495100777715495100d7e715495100d7c71549511ef74715495100d74715495101e7f615495101f7761549510057f70549512d67c60549511ef771054951004fe76d0951004fd76d095103cfc76d0951006ef62d0951016ec62d0951004ff7650951004fe7650951004fc7650951004fe76cc951004fd76cc951084fc76cc9510057f75cc95101d7c75cc951006ef62cc951016ec62cc951004ff764c951004fe764c951004fc764c9510057f754c95101d7c754c951005f7714c95100df4714
  | 33 => 0xf2010d320076f65cc9320076c65cc932015ee73cc932017ce73cc932016ef63cc932017cf63cc932007cf43cc932087cc43cc932005ed70cc93200cfe76d85320067f65d85320067c65d85321aef661d853201cfe75d8532004fd75d853201cfc75d853203cfe74d8532004fd74d8532014fd73d8532006f751d85321aef651d85321aef451d85321aef641d85321aef441d85321aef631d85321aef621d8532024fe70d8532004fd70d85321aef710d85321aef410d85321adf676d853200cf676d8532006f765d85320077765d85320067765d8532006f665d8532006f565d8532006f465d85320077465d85320067465d8532006f764d8532006f664d8532006f564d8532006f464d8532177d773d8532007d743d8532007d443d8532007e732d8532177d632d8532177d432d8532177e432d8532177e720d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d8532176f773d85321aef673d8532176f573d8532006f753d8532006f653d8532006f553d8532006f453d8532006f743d8532006f643d8532006f543d8532006f443d8532176f772d85321aef672d8532176f472d8532176f752d8532176f652d8532176f552d8532176f452d8532176f742d8532176f642d8532176f542d8532176f442d8532176f732d8532176f632d8532176f432d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f450d8532176f720d8532176f620d8532176f520d8532176f420d85320057f75585321b57c75585320067f65585320067c65585321aef46158532175f676185321aef67618532006f76518532007776518532006776518532006f66518532006f56518532006f465185320077465185320067465185321afb674185321afb57418532006f76418532006f66418532006f56418532006f464185321afd5731853235ef76318532007d74318532007d443185321bef76218532007e73218532357d63218532357d43218532357e43218532357e720185320067f65d81320067c65d8132006f761d8132006f461d813201cfe75d8132004fd75d813201cfc75d813203cfe74d8132004fd74d813200cfe71d8132004fd71d813200cfc71d81320cefa20d81321b57e75981320057d75981320067f65981320067c65981321adf67198132005f57198132006f76198132006f46198132006fb60981320057f75581321b57c75581320067f65581320067c6558132005bf7458132005bc7458132005f771581321adf47158132006f76158132006f461581320067f65181320067c6518132006f76118132006f46118132026fa6018132006f9601813203cfe76d915100cfd75d9151
  | 34 => 0x953226c7e76195323ee7f63195323ee7f62195323ef5e32195323ef5c32195323ef6c32195320067e61195320067c61195323ef6f201953203cfe76d91320067f65d91320067c65d913201cfe75d9132004fd75d913201cfc75d913222edd73d9132084ff72d913222cfd72d913222ebf42d913222ebd42d913200cfe71d9132004fd71d913200cfc71d9132024fe70d9132004fd70d913222eef20d91321b57e75991320057d75991320067f65991320067c6599132006bf6499132215dd73991321adf67199132005f571991320057f75591321b57c75591320067f65591320067c6559132245df7359132005f771591321adf47159132005fb7059132005f87059132004ff75591320067f75591320047f755913201cfe755913201cfc75591320067c755913201c7c7559132006bf7459132244ff7359132006df7359132214ff7259132006ef7259132004ff7159132006f77159132004f7715913200cfe715913200cfc7159132006f4715913200cf47159132004ff7059132006fb7059132004fb7059132024fc7059132006f87059132024f87059132216ef205913222cfe76191320067f65191320067c651913203ebe6419132006bd641913203cff7695132004fe7695132004fd769513203cfc76951320067f659513201e7c65951321b73f5495132286f46195132004ff7655132004fe7655132004fd7655132004fc76551320067f655513201e7c6555132005df7355132005dc7355132276f461551323ecfe7694d3226e7f6594d3201e7c6594d321b75f5394d32087cc3294d32266f46194d3201cff7654d32014fe7654d3225cfd7654d32014fc7654d320067f6554d3201e7c6554d32005ef7254d32015ec7254d3225fcc3254d32256f46154d32014fe76d0d32014fc76d0d321b57e75d0d320057d75d0d320067f65d0d3224e7c65d0d32006bf64d0d3203ebc64d0d32015ee72d0d32005ed72d0d3223ef461d0d32015de76d0d32246de76d0d32014de76d0d3230f5e75d0d3230f5d75d0d320075f65d0d320075c65d0d3230edf64d0d320079f64d0d3230edd64d0d3230f9c64d0d32015de72d0d32247ce72d0d3230fcd72d0d32015dc72d0d32246df62d0d32005dd71d0d32005dd70d0d32247cf20d0d321fcfe7690d320067f6590d322367c6590d321fdde7390d32226f46190d3203cff7650d32014fe7650d32214fd7650d32014fc7650d320067f6550d3221e7c6550d32006bf6450d3203ebc6450d32005ef7250d32015ec7250d3220ef46150d3222cfe7610d320067f6510d322067c6510d321f6f46110d3222dde7610d3230ede7610d320075f6510d320075c6510d32245de7410d3230f9e7410d3230edf6410d3230edd6410d32015de7210d32015dc7210d32086df6210d32005dd7110d32005dd7010d321ffc
  | 35 => 0x3ebe6495332006bd64953321c73f5495332004ff7655332084fe7655332004fd7655332084fc76553320067f655533201e7c655533203ebe6455332006bd6455332005df7355332085dc73553323f4ff7654f3225fce3254f32214fd76d0f321c57e75d0f320057d75d0f32215dd76d0f32316dd76d0f323175e75d0f323175d75d0f32316df64d0f32316dd64d0f32015de72d0f32015dc72d0f32005dd71d0f32005dd70d0f32244ff7650f32015dd7610f32086dd7610f32014dd7610f320879e7410f32086df6410f320879e6410f32316dd6410f320879d6410f32015de7210f32087ce7210f32087cd7210f32015dc7210f32005dd7110f32005dd7010f3200cff7658732086f46158732004ff755873201cfe755873201cfc7558732004ff745873203cfc7458732014fc7358732086f73158732086f431587321bef62158732004ff7058732024fc7058732086fb6098332026f860983320057f75583321c57c7558332086f86058332004ff75583320067f75583320047f755833201cfe755833201cfc75583320067c755833201c7c7558332004ff745833203cfc7458332014fc735833209eee3258332004ff715833200cfe715833200cfc7158332086fb3058332086f8305833209efa205833201cfe76d95321b67e65d953203cfe74d9532004fd74d95321b67f54d95321b67c54d9532014fd73d95321b67f53d9532084ff72d953226cfd72d953226e7f52d953226e7d52d953200cfe71d9532004fd71d953200cfc71d95321b67f51d95320067e51d95321b67c51d9532024fe70d9532004fd70d95321b67f50d95321b67c50d95323ed7e76d953201c7e76d953226f5e32d953226f5c32d953226f6c32d95320067e61d95320067c61d953226f6f20d95320067f74d95320067e74d95320067d74d95320067c74d953226e7f73d95321b67e73d953226e7d73d953226e7f72d953226e7e72d953226e7d72d953226e7c72d953226e7f42d953226e7e42d953226e7d42d953226e7c42d953226e7f32d953226e7e32d953226e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067e41d95320067c41d95320067e31d95320067c31d953226e7f21d953226e7e21d953226e7d21d953226e7c21d95320067f70d95320067e70d95320067d70d95320067c70d953226e7f20d953226e7e20d953226e7d20d953226e7c20d95320067f10d95320067c10d95321b67c65595323f5df7359532005f771595321adf4715953226cff75595320067f7559532004ff745953203cfc74595323f4ff7359532006df735953225cff7259532006ef7259532004ff7159532006f77159532004f7715953200cfe715953200cfc7159532006f4715953200cf47159532004ff7059532024fc705953226d7e76195321b67e761
  | 36 => 0xf7459542004ff7359542084fc735954227cff7259542006ef7259542004ff715954200cfe715954200cfc7159542004ff7059542024fc705954201cff7655142014fe765514227cfd7655142014fc76551420067f655514201e7c6555142005ef7255142015ec725514203fac425514201cfe75d8d42004fd75d8d4201cfc75d8d4203cfd72d8d42246df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42024fe70d8d42004fd70d8d42246ef20d8d42006df6398d420057f7558d421d57c7558d42005f77158d421cdf47158d42005fb7058d42005f87058d42006dd6318d4201cfe7518d42004fd7518d42084fc7518d42084ff7218d4203cfd7218d42086df3218d421fedd3218d4200cfe7118d42004fd7118d4200cfc7118d42024fe7018d42004fd7018d42004fe7694d42004fd7694d42084fc7694d420067f6594d4201e7c6594d421d75f5394d42004ff7654d42004fe7654d42004fc7654d42014fe7690d42006df6390d42086dc6390d42015ee7290d42005ed7290d42014fc7650d42006df6350d42006dc6350d42005ef7250d42015ec7250d4200cfe76d85421cef661d854201cfe75d8542004fd75d854201cfc75d8542014fd74d8542084fe73d8542004fd73d854203cfd72d85421cef641d85421cef431d85421cef621d8542024fe70d8542004fd70d85421cef4615854201cfe75d8142004fd75d814201cfc75d8142084fe73d8142004fd73d814203cfd72d814200cfe71d8142004fd71d814200cfc71d814212efa20d81422f6bf6498142006fb60981422f6bf6418142005de7318142005dd7318142026fa6018142006f9601814225cfd75d973203cfe74d9732004fd74d97321c67f54d9732084fe73d9732086de73d9732086ed72d973226e7e52d973226e7c52d973200cfe71d9732004fd71d973200cfc71d97321c67f51d9732024fe70d9732004fd70d97321c67c50d973201cff76597320867c65597320867f7559732004ff745973203cfc7459732014fe7359732014fc73597320867e53597320867c535973225e7f525973225e7d5259732004ff715973200cfe715973200cfc7159732004ff7059732024fc705973201cfe75d9332004fd75d9332084fc75d9332084fe73d9332086de73d9332086ed72d933200cfe71d9332004fd71d933200cfc71d9332024fe70d9332004fd70d9332214fd76993321c57e75993320057d7599332086bf6499332086bc649933203cff7659332086bc6459332004ff755933201cfe755933201cfc7559332086bf7459332014fe7359332014fc7359332216dc7359332086be4359332086bc4359332216bf4259332216bd4259332004ff715933200cfe715933200cfc7159332004ff7059332024fc705933203cff7695332084fe7695332004fd7695332084fc7695332
  | 37 => 0xd52004fe7650d52004fc7650d52006df6350d52006dc6350d52004fe7610d52004fd7610d52084fc7610d5201d7e7510d520057d7510d5200cfe76d85521eef661d8552014fd75d855203cfe74d8552004fd74d8552084fe73d8552004fd73d855201cfd72d85521eef651d85521eef641d85521eef431d85521eef621d8552024fe70d8552004fd70d85521eef410d8552005df7358552005dc73585521eef46158552024fe76d8152014fd75d81522fe7d75d815203cfe74d8152004fd74d815233e7f54d81520067d54d8152084fe73d8152004fd73d815201cfd72d815200cfe71d8152004fd71d815200cfc71d815233e7f51d815233efa50d81522d67c50d81522fefa20d8152006fb6098152005bf7458152005bc7458152005df7358152005dc7358152005f771581521edf47158152026fa6018152006f9601815203e7f7559742014fe7459742014fc745974203e7e545974203e7c5459742004ff7359742084fc73597421e67c535974227e7f525974227e7d5259742004ff715974200cfe715974200cfc71597420067e51597421e67c5159742004ff7059742024fc70597421e67f505974201cfe7598f42004fd7598f42084fc7598f42014fe7498f42014fc7498f42086de7398f42006df5398f42086dc5398f4203edf4398f42086dc4398f42086df3298f4222edd3298f4200cfe7198f42004fd7198f4200cfc7198f42006de3198f42086dc3198f42024fe7098f42004fd7098f42004ff7558f4201cfe7558f4201cfc7558f42014fc7458f4203edf7358f42006df5358f42006dc5358f4203edf4358f4203edc4358f42216df3258f42004ff7158f4200cfe7158f4200cfc7158f4203ebf4158f42006de3158f42006dc3158f42004ff7058f42024fc7058f42084ff7694f4203cfe7694f42004fd7694f4201e7e6594f420067d6594f421e75f5394f42004ff7654f42004fd7654f4203cfc7654f42004ff755874201cfe755874201cfc7558742014fe7458742014fc7458742004ff7358742084fc735874203ef77158742006f751587421def4515874203ef7415874203ef441587421def431587421def62158742004ff7058742024fc70587421def71058742004ff755834201cfe755834201cfc7558342014fc7458342004ff7358342084fc735834203eee425834203eed4258342004ff715834200cfe715834200cfc715834203efb705834203efb405834203ef840583420fefa205834201cfe76d95421d67e65d9542014fd74d95421d67f54d9542084fe73d9542004fd73d95421d67c53d954203cff72d954203cfd72d954228e7f52d954228e7d52d954200cfe71d9542004fd71d954200cfc71d9542024fe70d9542004fd70d95421d67c65595423fdbf745954228cff75595420067f75595423fcff7459542006b
  | 38 => 0x2067c5159443004ff7059443024fc70594432067f5059443084ff7598c4301cfe7598c43234fd7598c43084fc7598c43086bf4398c4303edf4398c43086dc4398c43014fe7298c4300cfe7198c43234ff7654c43085bf7650c43006bf7650c43004bf7650c43085bf7350c4303f9f7350c43086be6350c430879e6350c430879e5350c430079d5350c43325bc7050c43004ff755884301cfe755884301cfc7558843086ef725884303eef425884303eec4258843086ef3258843086ec3258843004ff715884300cfe715884300cfc7158843004ff7058843024fc70588431feef2058843004ff755844301cfe755844301cfc755844303ebf4358443006bd4358443004ff7258443014fe7258443014fc7258443086f77158443006f751584431f6f4515844303ef7415844303ef44158443086f73158443086f431584431f6f62158443004ff7058443024fc705844303ebc40584431f6f71058443004ff755804301cfe755804301cfc755804303ede435804303edd4358043004ff7258043014fe7258043014fc7258043004ff715804300cfe715804300cfc7158043086fb705804303efb405804303ebc405804303ef84058043086fb3058043086f8305804303cfe76d9152014fd75d9152416be54d9152416bd54d9152084fe73d9152004fd73d915201cfd72d91523febf42d915200cfe71d9152004fd71d915200cfc71d9152024fe70d9152004fd70d9152006bf6499152005de7399152005dd73991521d5ed72991521edf67199152005f571991521e5ef725915203ebe6419152006bd64191520157c765515203e7c76551520147c765515201d7f745515201f3f74551520073f645515203e7e645515203e7c64551520073c64551520076f72551520157e72551520157c725515227f6c725515201e7f625515201f6f62551520057f71551522767e61551522767c61551522d57c7055152014fd75d8d5203cfe74d8d52004fd74d8d5240ede53d8d5240edd53d8d5201cfd72d8d523f6df32d8d5200cfe71d8d52004fd71d8d5200cfc71d8d52006de31d8d52006dc31d8d52024fe70d8d52004fd70d8d52006df6398d521b5ed7298d521c5ef7258d52005f77158d521edf47158d52006dd6318d52014fd7518d5203cfe7418d52004fd7418d524067f5418d520067d5418d52086de5318d52406dd5318d52084ff7218d5201cfd7218d523ee7e5218d523ee7c5218d52086df3218d523eedd3218d5200cfe7118d52004fd7118d5200cfc7118d524067f5118d52006de3118d52086dc3118d52024fe7018d52004fd7018d524067c5018d52004fe76d0d52004fd76d0d5203cfc76d0d5201d7e75d0d520057d75d0d52004fe7690d52004fd7690d52084fc7690d52006df6390d52086dc6390d52015ee7290d52005ed7290d52004ff765
  | 39 => 0xe2158a4322eec2158a43004ff7058a43024fc7058a4322eef2058a43086f46158643004ff755864301cfe755864301cfc7558643084fc7358643006bf4358643004ff7258643014fe7258643014fc7258643226f64158643086f73158643086f43158643004ff7058643024fc7058643086fb6098243026f86098243086f86058243004ff755824301cfe755824301cfc7558243084fc7358243004ff7258243014fe7258243014fc7258243004ff715824300cfe715824300cfc7158243086fb3058243086f8305824301cfe76d954321e7e65d954321cfd74d954321e7f54d954303cfd73d954321e7f53d9543014fe72d9543004fd72d9543014fc72d95430067e52d954321e7c52d954300cfe71d9543004fd71d954300cfc71d954321e7f51d9543024fe70d9543004fd70d954321e7c50d954321e7c6559543005fb7059543005f8705954321cff75595430067f7559543234ff7459543006bf745954324cff7359543006df735954321e7c5359543004ff7259543014fe7259543014fc7259543004ff715954300cfe715954300cfc7159543004ff7059543006fb7059543004fb7059543024fc7059543006f87059543024f8705954301cfc76551430067f655514301e7c6555143005df7355143005dc735514303f9c435514324cfe7694d4301e7e6594d430067d6594d4321f5f5394d4301cff7654d4321cfd7654d4303cfc7654d430067f6554d4301e7c6554d43005bf7454d4303dbc7454d4303dde7390d43085be7390d4303f9f6390d43005bd7190d43014fe76d8943216ee62d894301cfe75d8943004fd75d894301cfc75d894303cfd73d8943316df43d8943316dc43d8943216ee42d8943216ee32d894300cfe71d8943004fd71d894300cfc71d8943024fe70d8943004fd70d89430057f755894321d7c7558943216ec6258943005f7715894320df47158943005fb7058943005f8705894300cfe76d854320ef661d854301cfe75d8543004fd75d854301cfc75d854303cfd73d8543014fe72d8543004fd72d8543014fc72d854320ef641d854320ef631d8543006f721d854320ef421d8543024fe70d8543004fd70d854320ef4615854301cfe75d8143004fd75d814301cfc75d8143014fe72d8143004fd72d8143014fc72d814300cfe71d8143004fd71d814300cfc71d8143006fb50d8143006f850d8143006fb20d8143006f820d8143006fb60981430057f755814321d7c755814331ebf6418143215ee7218143005ed7218143026fa6018143006f96018143084ff75594430867f755944303cfe745944303cfc745944303e7e545944303e7c5459443084fc73594430867e53594430867c5359443004ff7259443014fe7259443014fc72594432067f5259443004ff715944300cfe715944300cfc71594430067e5159443
  | 40 => 0x9743014fe7259743014fc725974324e7f52597430067e525974324e7c5259743004ff715974300cfe715974300cfc715974324e7f51597430067e515974324e7c5159743004ff7059743024fc705974324e7f505974324e7c505974303e7f745974303e7e745974303e7d745974303e7c74597430067f73597430067d735974324e7c735974303e7f435974303e7e435974303e7d435974303e7c43597430067f72597430067e72597430067d72597430067c725974303e7f425974303e7e425974303e7d425974303e7c42597430067e32597430067c32597430067f71597430067e71597430067d71597430067c715974303e7f415974303e7e415974303e7d415974303e7c41597430067e31597430067c31597430067f21597430067e21597430067c21597430067f70597430067e70597430067d70597430067c705974303e7f405974303e7e405974303e7d405974303e7c40597430067f20597430067c20597430067f10597430067c105974321cfd7694f4301e7e6594f430067d6594f4324f5f5394f4301cff7654f4303cfc7654f4301e7e6554f430067d6554f43005bf7454f4303dbc7454f43004ff7558b4301cfe7558b4301cfc7558b4303eef7258b4303eef4258b4303eec4258b43246ee3258b43004ff7158b4300cfe7158b4300cfc7158b4303ebf4158b43006ee2158b43246ec2158b43004ff7058b43024fc7058b43246ef2058b43004ff755874301cfe755874301cfc7558743004ff7258743014fe7258743014fc725874303ef7715874303ef7415874303ef4415874323ef63158743006f7215874323ef42158743004ff7058743024fc705874323ef71058743004ff755834301cfe755834301cfc755834303ede435834303edd4358343004ff7258343014fe7258343014fc7258343004ff715834300cfe715834300cfc715834303efb705834303efb405834303ef84058343086bd74d9643086de73d9643014fe72d9643004fd72d9643014fc72d964300cfe71d9643004fd71d964300cfc71d9643024fe70d9643004fd70d96430867c65596430867f75596432367f5459643084fc73596430867e53596430867c5359643004ff7259643014fe7259643014fc7259643004ff715964300cfe715964300cfc7159643004ff7059643024fc705964303edf435924301cff765524301e7e65552430067d6555243005df7355243085dc735524303f9f4355243204ff7654e43085bd76d0e4303ebd76d0e4303f3e75d0e4303f3d75d0e430879e63d0e430879e53d0e430079d53d0e4331dbe70d0e43086ec6258a43004ff7558a4301cfe7558a4301cfc7558a43084fc7358a4330edf4358a4330edc4358a4322eee5258a4322eee4258a43086ef3258a43086ec3258a43004ff7158a4300cfe7158a4300cfc7158a43006e
  | 41 => 0x86bc4359253004ff7259253014fe7259253014fc7259253004ff715925300cfe715925300cfc7159253004ff7059253024fc705925303c7f765525301d7f745525301f3f745525303e7e64552530073e64552530073d645525303e7c64552530057f73552530075f73552530055f73552530075c735525301e7e635525301f5e635525326d7e725525326d7c72552530057f71552532767e61552532767c61552532dd7c7055253014ff7658a5301d7c7558a531b75f5358a53086ec6258a5326f6e5258a53004ff7458a5303cfc7458a531b67f5458a530067d5458a53084fc7358a5326e7e5258a5326eee5258a5326e6e5258a5326e7c5258a53086ef3258a53086ec3258a53004ff7158a5300cfe7158a5300cfc7158a531b67f5158a53004ff7058a53024fc7058a531b67c5058a5326eef2058a5300cff765865316f5f5358653086f46158653004ff745865303cfc7458653084fc7358653004ff7258653014fe7258653014fc7258653266f65158653266f64158653086f73158653086f43158653004ff7058653024fc70586530bf5f5398253086fb6098253026f860982530a75f5358253086f86058253004ff745825303cfc74582530a67f54582530067d5458253084fc7358253004ff7258253014fe7258253014fc7258253004ff715825300cfe715825300cfc71582530a67f51582530a6fa50582532de7c5058253086fb3058253086f83058253236be54d9153236bd54d91532367c53d9153014fe72d9153004fd72d9153014fc72d915300cfe71d9153004fd71d915300cfc71d9153024fe70d9153004fd70d9153006bf649915321ddd739915324ddf7359153005fb7059153005f8705915303ebe6419153006bd64191530067f6494d530857e7394d530875e7394d530867f6394d5301f5f6394d5301e5f6394d5326e7e6294d5326e7c6294d53014fe76d895325eee62d895303cfe74d8953004fd74d895301cfd73d895325eee52d895325eee32d895300cfe71d8953004fd71d895300cfc71d8953006ee21d895325eec21d8953024fe70d8953004fd70d895325eec6258953005f77158953255f4715895300cfe76d8553256f661d855303cfe74d8553004fd74d855301cfd73d85530067e53d855317e7c53d8553014fe72d8553004fd72d8553014fc72d8553256f651d8553256f631d8553006f721d8553256f421d8553024fe70d8553004fd70d8553005ef725855325dec7258553256f4615855303cfe74d8153004fd74d8153014fe72d8153004fd72d8153014fc72d815300cfe71d8153004fd71d815300cfc71d81530d6fa50d8153006fb6098153005bf7458153005bc74581532de7f6518153026fa6018153006f9601815303e7f755974303cfc745974303e7e545974303e7c545974324e7f5359743004ff725
  | 42 => 0xe7198e54004fd7198e5400cfc7198e54024fe7098e54004fd7098e5403cfc7458e5403edf7358e5421ede5358e5403edf4358e5403edc4358e54004ff7258e54014fe7258e54014fc7258e54006de3258e54006dc3258e54004ff7158e5400cfe7158e5400cfc7158e54004ff7058e54024fc7058e5403cfe7458a5403cfc7458a5403e7f5458a5403e7d5458a54004ff7358a54084fc7358a5403eef7258a5428eee5258a5403eef4258a5403eec4258a54004ff7158a5400cfe7158a5400cfc7158a54004ff7058a54024fc7058a5428eef2058a5403cfe745865403cfc7458654004ff7358654084fc7358654004ff7258654014fe7258654014fc725865403ef77158654286f6515865403ef7415865403ef44158654286f63158654006f72158654286f42158654004ff7058654024fc7058654286f7105865403cfc745825403e7f545825403e7d5458254004ff7358254084fc7358254004ff7258254014fe7258254014fc7258254004ff715825400cfe715825400cfc715825403efb7058254106fa505825403efb405825403ef8405825403cfd75d8d5424ede53d8d5424e7c53d8d54014fe72d8d54004fd72d8d54014fc72d8d5400cfe71d8d54004fd71d8d5400cfc71d8d54006de31d8d54006dc31d8d54024fe70d8d54004fd70d8d54006df6398d54005fb7058d54005f87058d54006dd6318d5403cfd7518d54086de5318d54206dd5318d54014fe7218d54004fd7218d54014fc7218d5400cfe7118d54004fd7118d5400cfc7118d54006de3118d54086dc3118d54024fe7018d54004fd7018d54014fe76d895427eee62d895403cfd75d895401cfd74d8954084fe73d8954004fd73d895427eee52d895427eee42d895400cfe71d8954004fd71d895400cfc71d8954006ee21d895427eec21d8954024fe70d8954004fd70d895427eec625895400cfe76d855401d7e75d8554276f661d85542777651d855403cfd75d855403c7d75d855401cfd74d8554084fe73d8554004fd73d855419e7c53d8554014fe72d8554004fd72d8554014fc72d855419e7f52d85542767e51d8554276f651d85542767651d85542767c51d8554276f641d8554024fe70d8554004fd70d855419e7f50d8554005df7358554005dc7358554005ef725855427dec7258554276f46158554005fb7058554005f8705855403cfd75d8154084fe73d8154004fd73d8154014fe72d8154004fd72d8154014fc72d815400cfe71d8154004fd71d815400cfc71d8154136fa50d8154006fb10d8154006f810d8154006fb6098154005df7358154005dc7358154275f67118154005f57118154026fa6018154006f96018154086bf6499253086bc649925324f5f5399253086bc645925321f5f535925321ebe545925321ebd5459253084fc7359253086be4359253
  | 43 => 0x40000004000000c0000004002000c005000400d0000000000400000000060018000000000d002c0040000006002400000100020000002000000300040000024009000c000000000000040020008005000000100000000004000000c00000040000068001001c001003000200080000000000000000b00040000008001000000200080000008003002c0010000000000400200480020014001000000100200090018002000800000000050000001000000d000400300000000010001001000000000120010002001400200180000020000000000200000000000000000c000000c0000014000000c00100140000024001000400200040010000000000400100040090010000000c00000000060008000002800200100010008001000000400000020000003001400000000000004000000000000080010048007002c0000050001000000200000010000001000000000040000014001000000e00180040000000000000200000020008004001001500000070018003000000000000030008001001400000080060004007000800100040000014008000c0090008004002800300000010004006000400000000020000000000000100040010000000003000200140030000000000400000000000000002000800000380020000008000c001000400300080020010008000000300100000004008000000200100000008000000400000000000010003000800d000000300000030014000000000000000010008004000c0020000001001c0010018000000000000180030000000001800100000020010000000000200000010000004000c00300040000010009001000200000050000002000000a0000008000000000000000018008000c022000800100080050004000000c00200180050000000000000a00100070000000002000000180030000001000c001000400d00100060020000000400200000020010001000000000000040008001000000500040040018006000400c000c0000000000000800100180020004000000c0000000001000c0000008000000c0030000002000c0040000000000c0000000006000c001000c00700000000000000000c0030018001000c003000000c0014000002000600080030000001000000000000010000001000c001000000a001000100000050000001000000100080000008004000c00e000c001000c00000000020000001000000200080040000000000400a0000001000000400000000034000000c00100000030018002000000100080060020003002400200000060000000000400103cfe7498e54084fc7498e5403e7f5498e5403e7d5498e54086de7398e54086de5398e54236dd5398e5403edf4398e54086dc4398e54014fe7298e54004fd7298e54014fc7298e54006de3298e54086dc3298e5400cf
  | 44 => 0x1001c0000000000001000000080030000000000400000500010000003000400200000000000002001c00200040000028003001c012004c002000400800000050004008001c000000000300000010000000001400000100020000000001c005000c000000400000040110000003000000600040040000000000000000040000028001000800600000090040001000c0000020006000c00d000001a0008003001c0010000005000800400040000000001002400100a40000000000000c0000000001000800100000000000001000000600040000000004000000100180020000000000c0000004001000c005000800000040020008001000000200080000004003000c0030008004000c0020000000000000000100020004001000c000000000500000010008007000c0000004000000c001001c004001000c001c0000084005001c001000800000000020018003000c000005800400040000004000001400300000030000001001400100200070004002000000800040030000000000400000000010000001000400c0000000001400000000000000000000000100080040004003000400000040000018001001c000000000200040000000003001800600000000014002001c001000000100000010020000000000c0004005005c00f002400000140030004000000c0050014000000000300000000004003000c001000000a000400100000000000000001000000100080004013000c001000400000040030000001000000c0004001000000e00000020000004000c0000000001001c001000c000000000000000070004000002400000080000020005000800000200020004002000c00400040000004001000c000000400000040010008000000001b00000000004002000c0020008001000800200000000000004000000000040010000000000000000000000014003000400000100020014001000c0010014001000800000000000000003000800b0000000000c001000400a001000100000000014000000800200140040014000001000300080050008008002801000000070000008000c0000004004004c0000000000002400000000000008000000c0110000011000000300080070008007000c000000400000000020000000000400c0008002000800000080030000003000000100000000008001000400200080050008004000000000000000000000001400000000010000004001400000000030008000000000300040020000000001000600080010010000002c0000000000002000300200030004002000c004000000200140000000001000c0050000005000400200000000004005000c002000c000002800200040020014000000000400180010000000000c00300040000000000000800000040090000000000400300000000000000
  | 45 => 0x300000030000002002c00000000040004008000800000100030004000000800800000120020006000000200180020008005000c00a001400000080020000003000000100000040000006000c000000000000000000030005002c003000000d0004009001400000040000004000001c000000000800040000014000002800000040000000001000400300040030000000001000000100000000002001400100080000004000000000a0000000000c01e0004003000c001000400000080040000003000c00600100000008002000800800180030010000007c006000000300000020004001001c000000c005000000000000030010001003400100040000000002000400200040000018000002c003000400000000000000002000000000040010000000000400200140000008002000000000040010028003000c005000000000000010008005001000600000090004000001000100040010000006004800000000000000000000401800040030008002000400200140000004004003000000000010000002001000100000000000008000800400040070008000000c001000800800040000000002002000c003c000002800000000020004001000c00100000030008000000800000080030000001001400000000080008000000c00100080040004000000000900080030000001000800000000000008004001000800080000004000002000000000000014002000c00500040030004005000000500000000004005000000100040000004001000c006000000200680000000002000000800000030010008000c000000c002000400000000020018003000000700000030000001000000000080000000000000800300000080000002000400300040000004000000c00000000090000000000000100000010000001001000200040000000003001800700100050014002000400100080000000008001400900140000004000000000600040010000000000c000000000c0000002000c0000008003000800000040020000001000001100000000000003000800100040000000000000800100100030008004000c004001000800200080014000000000700000000008001000c0000000009000400000040020008000000c000001c00500040040000000000c00100000000000001001c00000180070004000000c00400000000014000000c00000000000000002001000100000040000000001400600000000004002000c000000400200000070000008000000100000010004000000000e000000000000000000002001000c000000000100020010003000800100080040000004000800600000000010001001000000000000004001001000000040010000001001000000100010000000000400300180000018000000000000000000020005000c004000
  | 46 => 0xc002000c001000000000200020018004000800500080040000005000000500100030000001000002000000020000000001000a000000000100010014000001c002000000000040010000002000000100000000008000001400000000030008003000c00400040060010001000000800080000000001001800000100020000000000800c0004002002c00300000030000000000c002000400000000040000005000000000140050014002001c0000000003000000700040000000000000400b000000000100050004000005c009001800000340040000008000c00a00100000000002000400000240010000002000000b00180020000001002c00100080000004000001800e001800400000010004000000000b0008006005c001000000600040000008003000400000000020004002003800300000000020000000c006000000500040000000009001000d001c009000000000000000000005000400400000000008005000000000000070000002000000000080040008000001c003000000200080010000001000000400080020014000000c0000004001000c00500080010000003000c0000000000000400100100010024001000000200140030000000000000300000010010000000c000001c003000c0000004005000000000080000004000001c00d00000040004002000000000040000000006000800000080020010000000000800000020000000000400200000000004007000000b0014005000400400040000004000000800000100020000000000000700040040008000006c006000c0000000006000000300040060000004000c0000000000000400900000030004000000c0070000002000c0080000005000c001002400100000020000000000000100040020020001001400000000000000000000000000000010004002000800200000010004003001000100000080008003003c00200000000000002000000000080040020001001c003000800b0000000000000500200070000000000c005000400000180090004000000000200340010010000000000100140000008000002c002000c0090004000000c001000800f001400600000070000009003000000140000008005000000000080060000001000000300100080014008000c0000000000000000d000c002000400000000020000001000800400000040000000000c0010000006000400400080000004005000c00000180000004000000000c004400000180020000002000800100000030004003000000b000400b000c0000000002000c0030010001000c001000400d0004002001c001000400600000040000001002c00700000060000000000400000280000008000000000400000060000007000000000000020000004000000a0020001000800f000400
  | 47 => 0x2e2c8800061200005e083a67831e9c00000004a396b024097342cc8000000000070b000003000006d2000062b83a42c827261f0ad8a7281ebe0908c689510f6600000001f10000000000042a26d2e38a16e41b8000da180009fb800051d3934aefa158000222c00000000000000b710000642a98e51e0000000000000000004e98f38953abac00000000000000184069e000059800000000002b2a35780000000000000000000000000000abe94d9d8878a36e000005565be0000000196c65fb2a0922b55a41608ba624a8bcafb85943278dd60000fe4000000017300000000cee82c000000000ba00000000000000a590000727800000000000000000d80800000007f000000006188000c7380000000000000000000000003960000b5f0a1c9b8a2d20001b780000c303f9818a0000ed000000000000000000345a9cf212cd768000076aa96e20ad8e4e580000000000000000063fb8760000000000000016c8570e1a80000000000a4e1fccc19ae166800000000177654f000000008fe508a0609383642bfc00000000000bde8000a7585642eb0c0ce1080000000000000000001200000001824000000000000004a20000000000025b80000001c540000000a94a0847701092c859dbea2800000a98132000000011732a697d80000000fc2d3911948e12440c8f246e5f29ec8046af94d45800018eab7603100005d08cfc00002fc5c12e462e2289800021c432a1034000350e81e800031201b086b16a40000000b0322860000000abd93f60000000000000000000008358c8600028f4e0a17686940000d68800000030f43078fe20000000510000000000008f60604bd3a942000359e10ea6a6390040489587380001f76719800000000000000e74567b67000029246c399b277b07a4000119c202000000032d453a1d0a0001ca485b00008b415b8000000000010f252c9ba8a30231ad720000a0ea6ea1b1b2ac00034c44c810521d7b6660000000e4b80000002454000195a4e50ebea2480006e19c10690000000017541180001000400500080020010004000001d0018000000c0000000000002c001002000000040030024010000c006000c001000c002000800a00000000008003000400300000000008000000c0050008000000000000200030000000000400000000010008000001c00100080020000001000000000180100004001000c00000040000004001000000000000000014007000400200180000008000000c001001c002000c0010000000000000100140020008000000400800040090014002000400100000010000002000800000000010018001000c00100080050000001000000000100070010000000400000000010000000000000100000030008004000c001000400000000020004001001400300180010004000000000000
  | 48 => 0x362205eb322000000068112e2000000000000008d08000959379cc792ccc000000000008b000023ba00008de0000c06a0380000a90e3c0000ec80001ce00000000b98b184000000000000000000000ba00000c8a000000033580001722000000096280004350c0000025a297f036a7748000a35acf641d800000006584ac8000df29fce0000000657000000002ec54e0974000000075337089b5155c30a1186047ad52a081f164721bb65d980005fa8000000000000000000000000b52000000000000000000580a2b0000213a68c9cc0000000032e0ea83530000000000073a8000647000076d800000000008c900002ef800098002a852737f045db028a4d0000000000000000000dd800000035ee0000000000000090a80000000fd8000000000f0000594b288000000000000000002d2e0001aa862fa18c51d800000000000000f2c5751aeadbd28cc3150000de0800000000000000000d943260c60126489ea404d6a1a2e6f280b6c4913ca467b7e81fd342a1f73342000000000000000acb8a4249942a3110000cc00000571a116c5900000030000000062c000194eb0180000000000a4500002f980003ed00000000000102b2589099a64d1400000000000809aeb00000000064800000009e0b2e00004811860afca396b653810000182200017147c98cb000020a800021e41a28000000000000018e01bd800000030646240798c1c35ce2d6aac87cc8d3620e800000002e4000000000000000001b14000393aa3a847ac93800077f000017f1420310000000035e2000000076b8000899000000000001370000000000066100004c5a4e2000166a0000f9a6cc00000000000000000056b2ff8af0317a7e10000000000000011c6000238a9dc10da7d50000c7338f200020ea1cfb658000200610381045c800000001f1a000000005f9fc2b070a64000234c1a500000002dd800031d23c7037c6fc0c7836220da7ab0c7e5871a6227099da88a0ee616b80008f2a2023f108a67f71f7a28a80000001ad8e2f800000005a4a1b80000000000db0806835c182075480009ca297e55c82b07908000dc30e00e2027ac6998000c0e8000c9898c000000000000b82000028400000000001f8c2fb9cd86d9186c0000000a1da94e8ed25120001450a5ea59a838b3c802c2b16000000033e245c54700007670000cfa11e800000005ae9c6ac4e00000000000c5000520000000d41800034e000000014e422922348f580000002592e3680000000000446a696c6f00005631baa00000009190000000000000000000000ff6000357c000345c00000009942ac6db980000000000b4a0000000000000000000001e44000052e7db9f7e1120000da7b898c9a1eb06152422603b0ac67a9312c718d74a8700000000000a40118c00000000002c58e561cec27431
  | 49 => 0x2e2abe83dd025a0000df267d0000000019c000000000000001ff330e9a78b346b980002b8afc200032d8b8d97a004f84861fb918059c0000000000094a8e9e00036d40002bc6a7c2efed5a800092a8476d352e4a0001ca6b080000268800075fb4c800021c63cf800006d337845b9b16000275e00000005b90000000145e0000000016182a42588227c2800000018fc00000000000b72000358c18c144e86100001f8800040d8000c23000063a96a886e800000011d2973800000025a40000000c361ed84b28000c068000560a28cc6994fa0000852812800089b2d0e00006c0e1d0000ce6000000000000003714a678000000000028b0000e401694b908cb42200e388d10000a2b21909fa90f4a6f80000001fe0684800000037f65868c0861f9a345d60000b42800000014a86afb11a72c80000002ddc0000000a3e03e2000000000018080000000000000000000000001c928cc00000003272d9a8020963939c891b740000137600003ae9cfa55c8c3396a783b9105f98478000000000031ae0e20dec9670000543000000000009410000bd02c5c143800003334a4ce231269ed00000000e60000000070909188ad000000000000000000b8b800000000000000e22000000000000003b48000b50800000000004ee800000000002aa1562d588d9c00000006ae996045eb3bcdf000009770000000000000000000000000c8000003628000000000000039360000000000000000000000002a8c8070bd0dbaad580000000714000090a0e0a0000000a9b00be00b000000033ee6e50480e45b5e600000004d60bfe0001c365690a6845fb42e5c925fe6b389aa17a912449b80008e4800000000006b3000077c8cdc0002b8a8d8978cbd2a982000000000037aa1768000a731494d6498e4c292668000000067c0000a760000521a8749278000d7135f2ddd181e82800003f4800000027d0000211e000000000010fc322b6ce3321ffa1bfaa4c3beb0e400000008b68000ad7ae4000000000000000e0b000000028daad8800028d800000032b800029565f8b9706a6800000012ce0000676cbd9c6ea7c8624e48136822b80000f60538cdc18d2000000000032dcb7480000e51ae400000006b000004c980000000c144d5a14e000154a9e40000717800068f0000000356e0000000000000000021a43ce8722667a4e80000c7c5c60000000000097e0eb4299800093b000000008d84c389ae00033d2198888e5568000000000000000000000000dd720f0a1a9442314236c000000000033e2b0d8d325f6b4e0000222ec6e20ba00d8306c89000000013e40001cfe0000188bee8000de90000164200800007489f7a16a000024ea7194263c6a0021bc000029d948880000002b8000076d0000e353058da593b6309864a6101ea8b6eb4fa09a800040c80000
  | 50 => 0x468a56c9121bc6cf528a2b12851806c80008a3b5aabae000021080006b5000000015080003728562b76800000003d700001c5a628222236e9200000000000000000005ab0000812061800018c6524000000000000000000000000036006a6de120bc000083e0000264c64001c0000e163a580000000e620000000d8b00000000dcec8c96560002a9cc8395b4000000000000007793364726ad6e98db4de0c6a5145f228689b038840002176cf9b16a5c09bc01ab839c0000000000000000000004a521cc56f335600028c60ab00009ac1940000290654880008e5000000003cc00016fa420a5422c5800000000000000000aafb3307551f1e0d086485380000af5aa6a0001d400000eca00000007398000000372e00000002548e8c0001c061b435bc3ff187000035a0000000000021060002fe8c4218ca4ef85a89ea1930c8b1c380ce8000000000094d2be489c8000a8b8000a77b00488c8000677800075a000020a000000006cccfd8000000374200000001fd9816000000000003b200032ba00002d00000a1400032f28dd80000000000dfea21a402000000000007ee01ee0000000c24000095e21f6000384467280006410000000058e00000000000000000000082614000000000009af540001d22363270a25593329a3946c000111e0000000000000000000000000000000000000000000001374b1e9c60d0700005a68c160000ab8000000064d8ad8000009600019921c1881000021ea00025b02a8857c000085000009b6b5a80005eb00000000000ac7a0aa9362c7600000000000000e0e830a0aa94a61d4a3b800031a800016a06df80008a48000000000000000009cc8000da2000073d2b181c3a19439700000558000000000000000000000ce40000c5a399150a0000000381b1ec24b834618b9d0e3d0000072e0000000259e000000000015180002f82000060a0000000e3e049e35e070a0e8a33a30e0e2ace01c72ae40000e0817f0c1380000000000dcf000026fa4300c4ac02d6120ec000363e1e718460000000a4b906a28398c200000000530000981800000000000ba00006c00e3e52d00007d11ae2746872c58001d0000000023a935a4fe00000d69cdca9100000000abc08e278c2c18000000266240400000002370c9900000000634c850000317b6322f394649520000a6b0000a25349465c0b3a0000000000112eaec9134cb68000000000055a0c9a0000000a878a7edf4000001300000002216bbca7bc7a2800047b1acac2080000000000000000000000004e4800000009c8d0b0e9ad5c2066b8380007188000000275c000338659900000000000000000000019e200000008cd91020002584000078c7cea90400021ee0000d907c836906fd8000000000058786d899f29b26d3b9140002776000000000013060000c106128
  | 51 => 0x8000000007c7cb8000000152800010bc74f8358000044e00019d42e609fa12f000000038600000000000187800000008ab800097c34123542d3e00006beb1e2c7c12b80000001b3c0000000a790000cba000000000000000000532a9bcb15b4520000a205a48000c5580007a680000001bcc260189a00030ca00d000000005060000000000016e000000000018280000754cc42dac8ec87640000000a15257a000000000028f6bf4000044a00000000f12049800000013fc94f87c05539bfc000000000024f000000008a1311e39200007e4a1203be3814816b2aa29d19482468f42452000000020b89b789a6dde9a3013207b45b98000ce980000001dba000000000005b000000000003502b58000000016d8a883346926ae320000144b12162c00000000001c7ca9f887435d96da0001f740af0910cb3000036800000000000265800000000000000000000000000003a8e3429d04f8959aae327fc00019fea8304b619087ea555800000000005eea78e00033c61608c90c2384dedd59f422c60000bbf00000001f24000354e000355200016d600000000000000000000073a0000872100604a000000000005a20000a49b422b7ba230635800000003de000000000000000000000000000000011be1ff8450892903e17981a238b87a6b5c8dd87eea5ba2281e1cc9b000000000000000000e07800000036a87a800000000000cf8097600035b000013bc0002d300000000000000000037103ca0b080001136583325000039120001feacdf9dc465ab8c83732f8658e96760000ab62bb0000b5e8000c0000000000d1cc9e800011fa8ce41c800060b80000000130ca000000000b663212a0400000009d522f06a199b83a7080cb96b0fc5ff3540dfe00000002dda83981540000000b590000dd12e8e0b38000000000000000000000ac60000000d0100001389f4c674148e31995a00001feedd78000c87378c17511dcdfb11ce5a41e4a0002c161932eb200000000002ecc9dc94be459956448c8000996800075400004e63522a940000129800023203ca0c9b68e9c20000000000085f354a00036bc00019d6da100ce000000024d8000b80b84c123ac8a00029a454e8b84b442e50b43000027d0df6c66800000000000000ff03e3b86e4fb0a6a00000002fd02440002cf200022423cd28cabfd0000d4e285c0deaa4e0001e92a8503228761ddc0000f6831ab2545a780000000dca8cf00005898000000000000000000000000af201365e000000001cc600027aa92d00000b08c220000000c4a0a10000000000033a261cac801db80000000000520000079ba03600000000000000ad195d2d7f2ace0000000000000000002eae1000000ee0c0ae140000000094600000000000000488000000000000000000c2800005ed80000002e588c3affc2531b5a
  | 52 => 0x799800045c0000000000000017b497a03b400000bc464168600034be599a64e00000008e72ba4621800000034f20000fec9258000aeaa65c19c35140003032000327600038780000000b1f9f802a21e520001b4a58f80000000000a570000b9b8000000098673f333e5e70000000000000021463538000a30800026822ee0798000000248edeba7240000000000000083b8d7e00024989ed800000000000000000c4f35f40001a70000358000000000000000ad49446ba1095ed0cb6a200000006618000000000081500000000000e0a8074bd800840001beab29859c39980009c5800000000000000000391026c00000e2e2baf3200000000002540000000000000000002cc4a5c8000537b23471daed0245adcc32b80000ee8000000000039680000001d820000000a04800012600007fe1d4e00013c283a00000000000000000000000000002e1e20a9830bcaa96a000191600000004f2002430d29c09322d269d82998769a19a0002e2a5a58fd000000001d6ae769c18000469125095f000040e800090e1a1632a8010000000000003000000f720000000000188459500001342474a771fbcd24b5a44fbac4ed75067a4890dea530800072f8000d570c4652e000000005960002b0c000163cdb68f940001a18000269cb3aa386000000000016a25df8000c1f2db40000588cea000035a8eec49220500002a94bd58000000219e00000002d1acfe000000000004c6000000047c01086a4925a00025660002dae000000000002fa4f5b2ce000000000000004eca72e00004a004b899a2e00000cc538ba0001c1a0002bb400022b2000000000033600001f3400000008ea2c2200000000002208000109e6fb800000021fcc8e1ba6000000000000008ed8000a8980000000000000000074417dcaa00000000099e00000007938c8e00000000000f8600014cc000001a000000000025680000afc000198a28d240c0001c644da97a400003c2dac1c208728000000000000000002fa8000df1106400000002a9a9a8a709aa08e033aa69380008970920416b37680900000000d244b3000000000000000000de39014000000041c05ca7b8a862600800007d06ec6d522900002d128f3a7b096b172a0c79fc40178ef60000000e010c9cc2e16c4c0511fead5800061731a06291cb600000009bd0000000000000000001d61c0e78c8000000111881026aa000000000028b621f048c2b32af4000000037800000000c4edc880000000000cd4a71c42cae3ab7d80005ca21bc000000010015e40001d7a7891894b810000000000000000002ea0000d5b1d2c83d0000000303400009c00000aa49e2235a00008c090580002db000091091881ce8000cd684ead23a1f40372d5a00033947898826068167c852ab5a000309aa858bae00000000002e927bc239a2f6
  | 53 => 0x399720c1223aca41708622800007fa950383000000029d2a2a0000b9c9710559a5e652d837e1da073005e28140e80000e3b8c2000029660000000000315a00000000000000803800099e8000da6b6f04df35d64cf9a1012880000002d820001b0c000072048f9614231864e17a0000000176a00000000001764a0f08f48939b666f528a4924a3fa97b92340000000147b71a813a9a655e2da43698000c6080005988af6b790000000000000000000000000ba9a88200013ea8851aaa6fe80000000000db880001982cd6a7a8746e23156e000000022783c0916000027d80001bb8eae00000000001c8c9c480000000000258aafeda80b04c019a8e2418eb63c800000001aeecff233800017848b80a06af629aa39b80000000000a6db8cc000383400000008c70000e4907d67590000c76ae1a568800000000000001610df50000ceba40a00000001a893100001a88750afe2000000000036142f606ac988800048e8000000000053b87829f2add68c800006f80f887f9179a757aea06d13198a80329c000235e000000002d000000000000000000000000000026c87229e884109f18a18106602cabcea108000b6300000000d9825f343469281a60000be210580000000000dc1304c72c2da84d304f000000006bf1c580000000a7d0e5400003d4d91800046c80000000dbe0002c5a0000b30a09b1f82fc04ee00012769700000067800000013a40000000d9b361e000211a6dd19cc00000000002eb600002eec1eb852b6e1cca0000000b6f8c2e000000020387e46590d0cac4a76228b800090bab40af88000c752f5270a807220f000073e17e85ea15b29b91e787f7b81850c8f040fe107e380922621180000002c2e0000000ac1322ac648c1cd9b8a860af833e7312224e460008dad9da861d19d800003b600009da9750000000000098584d4423a6a008c1fec00000000000ad20001976bc511ae0000dacabf35b28f52c469af8000000042271a0532c0b9eae3fa9e3c01f9e7e7df000070f892a1ac000000000000003762000000000012120000000b8f80000000000000000000020fe0000e840001e3066f174a0001fb075c0000000381a00000000000000b199020b890000000000000000001ea8c984e21b68d1ab854071105e11905dc00006b20000d18b2a062a756012c948800050e025e4ae9dc662b0fa67a32b240000ea600022521de800000002f676f0f8200000000000000000000000000001450000000000000000000000000c2f1e5caf0800040b000007512eac298000c2c000000000000000000418000018f8000000000000000000002c34cbe000000000000000000b559ed291a98f8000000000037d800038dc000348a00032fa00000000001b06000058637223eed82a7c8682aa3297d11a85d7ace619533248fc80008f0800
  | 54 => 0x351a1640299e82733000000000000000000bea00000000000000033c2a38000000000008700000002e861a4290c000261a000000088e1b805fd0000686800000000000001e4cd560000000354c7d28000deda804d9209ecc1d32424bf20acc338f4e0000dc00001e081f496d44360000b4aadbc0000000000000006138c2000000000000002c680006b11e0400000000001f1c0003568000201ad33a77cd281a06243b29a0002d3a00019b493d391a830800024e19c289c1ada21b008e0000ce2b74020c7dcb31e67b082400030c6a78274808a8000000074c00034f018da4d24f3a79c00000004af02400000000bc280000000000ae1800000026ce48b80000003490d598000637000003c947012c1fa8caa0000000000022600000000000000000000031ea0000000825000000032060000118000000000000000000d60e02a6b4000000004700001dd0000cf5b866b0a800000037fc3478000bf3047423a174821e37b4ad380000002b22c8290901b38000000000000000000000000000000063da38210a80007558000a9616ea700005a0000000000087e3771d36ad61a841da94623aa89647708000768050a14a0000ce7998200012a00002954d83a5c43162768a2c8afe2f33172a362482515b74c0000000d810da4bcf26f0b4883180000e6a3a18d425d39e0600000000002df400000000000000d021f680000ce600000001feb25e00000009f100000002f681c01b889e59838197050c000000000000002e3ace2751129a075800041500d01208000000000000030e60000000c7b82e200000000003904a268000c6c0000a979f8a4ff914c00022ccdd92408bb90000c8c098e4f785fa57eb36a000000000000000000000ba5a0c679235902182f0856c11a00001c4e0000000000036200000000000f1e00000000000000000000000014d4000000000016d0000000000000009eeb67e00000000000000b72973a5fc8cd60000000be201220002ac400015ca54480000000000000000097a8000c38000000019740000000000000000080000001762d70aab86e400002970442a2580005f79ade69aaefa0001afa000290e2b79e6808d38f04559bc840a18ecd55b5ba000000000022e6000163042b9b8a7780d2c8a68deeca917d272a856800027c0af5392c16f0000a5b0000a680000db9052400000001598794422b5e02d608ec93b8ea213e8a1a3bd336689a0eda86daa08000323600020323a82b54bc0ab640b01aae8f300002b98552000101a000144499080005b706ea0001fa49682e608ae80000002f22a2d110e000000010680009c500000000000226b7eab70b6ae00000000000bde0000000000388a2a50000000000034e8e804a12eae0003194615b3b600016be04e80000000c4a7752afa550b436cf01edc0001cf277
  | 55 => 0xcf200000002d4b442169872463a00006db84c29fd024a000319c0000000000000000000001c40000a3f800094c8000a3b0b0025089cc000224049091fc000061a0000990c598a6c1c100003b3041800004562110b76cd7800026c8b2ed541c46b938efc000011000033bea5e022ea3825726dd8000d4200000000000c9f00007338000be8b66200000000000000b24800000000000000000103000000011ee000000000030de0000b4a0000000000235c0db0000d660000000000000000003cca91c2f7232e0000000036800000038a200000000002b080e6b5b8a390000bda800000032d6c1c8bca00000000000000000039800025be5b4aeee00031789290000000032c000047200012b40000000000000000000000379c4a0000e560000000cfb0000000000083223da670209a4b10000000241a64e800039400000b52140000332817b9a36ade18da9f739440000664a81911ca9e28500261d2edaa99ac00033f40000338a50000057f800000000000000000dc48000000000000000000000000e258000b472e8c00034300000a80000000011480000000000374317c4c880007f89dd800022a60000000000000000038b4000318c0000a9e784000010f0000915ad500002ad0183800022f000078e8c727dc0e34cac800079eb68a356acac000000000000000001198acf2dea0002818ae9abd0795000015b00000000000a1795321710834000000092e2aca0000000000000000000000000000797b7c80000000000000000000000000000000000000032c63ea96dee118000c86a4e6b0e8000000068ca481fbed6980006542a8a7bd80000000000005128a6362e5c8300626d7a085ae0e00002df8000bdc96388042560166960e49c944ae1f2dfc2059980ddb08cc9fa1eb660f1cd233b02b4a0bb8327bba54a000000029e8884cc4827a0000000707000000000000000000c97000000007a2d4930ae0e28000000047c0000000000000000000000002318000220a9828000aba9cf600037767cda2cedec0000000366000000000000db6904800094ea8908ba2450b64843290d91d6000308400010dc0001c52c808000c69000000004d6e41800000000006bb00000003962000000000005a00000420000084e23f000000000000000cfa33f800000000000003638baf0000000000000000000000266000000000000006920000e429d3c0bc800058600007a00fa8000000000038d80000000000000000000001dd8000cba8000000237e30fb5ec000369c92b340600024a8000172c00000007b980000000000000000000003f464980003ac0000217234a00015c0000000064680000000000000000000032c4000000000000000000576069376e2b4090400000000001b5200000005170e70a9a00005e79a9600000004ed11f82f9000000000
  | 56 => 0x4886c080000000e520000000000000072a00000000000e2980003c8a3f6449a71e049000000034964070000457a9d4b148000a0e000054400004412aac000000013c80000002c3c50ba182d77800000000000000000b068000000000000000000001252bb0b4f800003140000000000000038e8000147034ad949c90117b5b4cb2000000000000001df400000000000000afa800012a28aaa8d08703eb0000000016c00018b40002046adc276c0d3a47cd41000000000009b400d2000136e00000003c0000000001c62c09826000236088486bc000000000000000000000000000027900000dc351c4ac35fa83c83ac0001a7c00000000000000000000000020f822e199c0000000000362600027f037a00004aaa0ae0000d94343a8843ae83543183484e4f86ba5de094838521721528000151b3fe495b244000000000008a871680000000000909010c000034c7e5357a336b954c4db73a91c80000000000000200c1f7a15600000009d12368ad0b0f813d0000000265e00017d4c248bd6bed219c6e88f3c00c24becd031be14eb6f2c35b7de6e38adcaf98410e338744c3c27c234c38064d91e96658a552c5c2bdc52b800000000000000000000000000000001ef8000a4a0000000272c478021e00034ec1be0102c03b864008b8bc378b4d87b2a3ecb9980009de8000105171c000000023c3304b7e2d0400031c21531818d038e4c001acb29c100003b100000000000918957a09f1c785e429120000000bd08000000277e000352a46e980a000175a0000000206800000031fc0000000e3980000000d96a3408da000206800000000001ec242d0000bcb0000000000000026748c98000c40257400013e075d1d18d1119a6b2812869d924da0e0800011a1dd64d880000000000c11b830000000000033b40000000d2b80000000000c2600006dca2c2a079540000283635529620b3000046d000000000000000ed8000000000000002d1000000030a2532000000007ca00021f0000030c0002334c5380000001f0232d9a1c000000000037ee00000009811e1200009d60000000ba200000001ca2000191eb3bb64e72716588f2076c708800000000d65c98000ae7a61e0930330c0280005d321fa000000042e113c00022be000373265180000002c4000002866ab0000dd4aa640000000e168000a6c00001cb80000000066d30a4c000021ae0000000aff00000001df63f728dc49a00000000000000058c48c1efe0000000acd00000002ef60000fd40002ad43ed80000000000a459cbac450000000000000000009a4000036d01340000000000063800004feda60000000000000012ee818a0faaa92d1a24a2fd26621d9800011921e40fcc3ec0000000000056a998e7c42d466798000a6b80000001e7000000000000000000000000000000
  | 57 => 0x52f0000333b17433022b800018c816b0000356000000012aeab09932000000000000000ff2fb60000000a4280005df0000df8858000039402c334660002d144170be03820000b41b13498e86d65f58000ca30000d36800080f288e0000aba4488f4436f2e2225f800000000000000c0e00000000001f629a516a6d3fa1800002e14b050b248de00008f80ef067b82587ed25de0002d90940800000000000001d7200022740000aac1c50000cc68000000321018f0a569652466b55000000004300000000000000000011fa7e702060002f2ee12324a3b18000643afb20000000337800020531ac0ae0000741101208c80e80001cd0c8e80000ae9390b00000044c000000001e06ae000081100007450000429067edad00007420000000000077e8000000000000000006f09bf8cb48000acd9ad28880e949d2aa46a9683da000000014000000002a6e56f8c649071f4625a91da51f8e0ea0c8a420fa8000aaa800000000007e8800000003ec000279e00000000000000d430000bb6800000000008cb0000225800083288e60000a8a00004f6000000073e800000018aa0000000dbeb6200000000000149a08b0000000000094b80000000000000000000011e60000000a0d23a698baa24dcb2b80a9226c25cdb63c791a7a20000856b3800000002d6c0000e5e1c3083807aa720000029000013d293fa1100000000000000000003405cc80009e4a69200028660b12a8856190c6000000000021082d3800000000000001b7a02b8000d8d288819584ce0000b6063b80005ba2236df7000000000000000000c9489fca9d8000197aee03ef000000000004bc000000000000002fb000028100000000000362e29000006e900001e8000065587f800000003db215000017cc8bf00000002b44506820e000000033a936021900003eca31205180000802e280bc1a3800006e8b990f8000004da0002fa64cb30880000acabd20000bc934aa0000ec0000289c0000f6a00000000000000482866e00000000000000000000060f80000000000000000053680000003640d2b00000001350d6f8cd000000003c400000000000000007ae5b20d2000093a07c80000000000b1c0000000000000000000000000000000000013b00000806e420c560002310785157e96b8000000227c00008e009c0000b5a035e8532b3a502346400000000000000000000043d96800001fe6000190c05700003048000000000084f8000a98a1a279c8174b2600000000000de5000000020c40002f0e00000000000000627ac38239000000038d2e1a2570000141400000000000000000000012a800000000002bb8000000225e5c1aa8200000001e69d9600002b60000000e3a800000018ce0000f645c4841e0000000000122800000000002f8a00000000001700000000032980000000
  | 58 => 0x2484beb800000000005f1000014d81f8a788000000000074e800000009b4bf9000047900003d503fa888800086f80000001b9c7ba000037900003c900000000c180000df01e583b0dd3800000000002132d0800000003e89026758800000000000003372c2fa4ceb81b26e6c100caa950000000113e8d00000000230acad877e00028560000000a7686060000000e2a2a9041a000000000004528a98000000000000002938000c6180009c6973c0000000000000000034fcab800007ad0000000313a0918000d4b800031325886141fd00001f5e62ea87cc4f800094e0000d3985fe0000000000252456108f2b7fb968b959e76baa1b080000a5a81f1ea2000000026b000031d0044000230200036c06953672074a152b3919384e1a3aac2e938a0000000963000067730d47e0ab5cbce80000cd151ed232cb40002f78a0180009c40000b789a6ea56acdc3250a9a41b0000000000000000000000000b4f2c7200000000002626000368c4852f9aa5d0000528199aa233316024a3e2000357e58a0e1ec550000233a51ab208b10c04a81c3440aaec33081e7a39c14c4aa738000120c000000000000000001dc86fb376aca11c8e0002cec0000000978b448000000033c31120220000000164ca7e80003412bccdbdb772c78a1e6bdc0004ae88fce428094400016aee17aee8994860caac238e6ac8cbe22485de0000000000077cc7126546c8a35000021a603b31e62f200007d20a58616b52897487b625500001c200002fe89ba086b15cabe16b6558000000017e41f511b0000000000000000000000000000000000003cc00000000000000000000014d8b3e0c023b712da85d16849af017219c86aad5538e415500000000c921e0000000000000000b50000000017b31307fc0000367a68689fb06c00000000000000a6e800093f37a87a5000000000006c484cc3848802c6d9f220000000000340a6689c34b94a01800000008910000000253c50600002ed904a05a1b2a224000093aaec4000015aaf780004e68000913a948694aa0a0000000000209070c101e2719ff2802a130b3a27d6c2c81fa4581466000000087511c42ec066c48a8d44000000000000f600000000000000d8d80000001e1e29f38f40002a9e00020746220000000000000000004e30000dcfacd84e88000aeea8400000000d66b110ce281c29a080000000f580f399020001f2800000000000ee888796ec6690492cd200004ee353cab8b77e2a70000c05b94c93d8c5200018582cb0000000000061ab82e0d48000896a2b6000112cc53246c0000fb829b8000000228a98b32920000000da095d8bd300000002bfa00016460002b66592234664f800028010cea408000000052c000000000000001f60e98487800038106e0a5f0de6e0d80008e41514aebb476bb58dae0000f48
  | 59 => 0x9d58000000348200010ec911b4e20001882b6ca2067eb0000e49aa3c76507366ef35741a908182c515ea00012fa01dac88c0f163692f36ba4a88f14217aeea69cacd479d19b047da6124c697e050d8000325800056ea1dc000000000000000003668000000000008620001a241b79fd2000000000000000000000000000000038c000033a40001d8c00000000000000000000000019f69530000a8e1330b279b2e000000000000000001fc60829b1a0000000cd2800019a00000000000dec8000000000000029ca0001a760002b9600000000002fec000000000000000000000be40000000000000000000002186000309e0bd2df26112e0c188afc85260000a5304e6000000000010e2aba000000000000000000000137ad13800028992083e79f6a7688000d0e80000002488dc6387a3b7931c0b7000000030ea6109746513332c0000000c070982dfd0000c15a2620000000d6d80000de114400000000000000000275000000009740000b1d1df00000fe8b2c387017400000000000b1b800006e0000848a03074734a8000371c50b011400000000000000000104c0002a120000bb2dc79cae0001eda000120e00000000000000b0b00000001f2c4de00006e612c00000000000000062331c8291255a0000000000261056000000000a0c0000000000328ec1a2ad6dae1e2abf1180c61a000090d173000000003c29afe0002fee0000000ba880001d58000000084800020920000000d8a80000000e100001eba4c1242c59700006288f5a000243e0000466000111000000000000000df82634000247e00034ccbf38f70a982102d9d8000000183200000000000000b1b1c28000000000000000000000e0233ac18c80000002e9a2788000b2b80006258cd415733506530000000000022300000000000000000009d99e4b9500000000d6400000008faa28000002c654b8000b45800000000002370000000259614f000000000000000000000000000005e00000000545b84ab1305b46bcac500000000a4c000000032ca000000000013c63b895049560000000000045c80006cd2e82870800037e8000097000000000004d0800022b0d6ea8a8000000280a8580000248865a00036ecad30ed4000000000000000000000000000000003500000000000000000000000000000540800000000e096ab27000000004c092dc7573212758194200038a00000cac00000000000000ca789686e100000000000939203400031ba000117c0002c5e000018200037580003106000000069b10400000000af813a00001a2000000000002c848d21be82c7b5420001454000000000035c697680000000000bfd9ec4000000031710ee81aaa7c164a5f2dc5800000006f228eb0f6263000032800fe429a2fa00000000000000000205ebd18000a32061205881d8000
  | 60 => 0x91c00000000000000000354445600006640000ab9000073c000076a8766e0586b80000000000273aa6332ee6c819d2e528718bc4024800031f0341806200033b80a0a2c00400b9a0000000107000000029c49001c0a000351e00000000000000a7f9cda08a018698080000002b98371800000000009ab00005230d0000000000000000140993459428168d9000000038224328d160000000000000000000000000000df692de1cf2acc3308000db7090c8048000a7d80001b0800034f0000685000000032863c30000a9d00000000000b97acba8f992d200000001e3a5c800000001941024a11b39c000097a00000000000000deb1bb200015520001218000000084b80000d5800004e06fc7ac800081086a883780000000000bd41ebc00022046cd800000007340f8000000000000000000000234e0000000000091200000000000000e0991f200037981e1800055188d400000000000000d27236a0000000e218b9c23e000000000000000000000000000032e2000000000035342dc2460e4c24b2ac1800000029c822d80000000000000141000003900988000d42b05e000000000023c400006f4400800011680005819278dd2a3ac0000000629800083d95e600000000002bfe00010fa0003548000000067f1434e57000057d80000002e7a00000009a20000d44800066a81bcc81146e0000dbabaa800016780000000000000000000000004af83600000000141000000022a00002822b681a4cd1c8000c3406867e580000000000cdd208215e1246cf6acd22ed0000000000000000002cab624000375ab0900001b99c0233a196e124335420d80009958000d3a8ac8000000000000007392fde00000007b7b58200000000000000cb409ea00000000001334dc3832a1ec97a27ebb93217395f0e0f00000000000000046a0a237060000000e4780002da2b7e000000058100000000000e4f0000000269ad092ff200031de3c18b4085c24c400000000003158999056a7679ff600031d83e100000000000df98000bc480006dc00000001576002800000027fa0001d9000004d85c280003451eb85550000a86800000000005dca92c5032198418800000030f2c3b0cba3e901ec0002988a120000b31866a761021676e304068fb6be4a32fd6b79aeac9852e902ee2984000000022f8000000327803080002a80000000000050f00006a8a2dcaa39a8047a8000bca2e6c0d100000001f906271b3a000183a0000000000141c000364400000005a7000000027a0000000011100009820000109a3727d908827aa8406d1c017643900006b417440000000db794241ee0000b5004d208fa3e474183680a30000bf2800000000006400000289000000020e0216250c208000000028e20000000000000000000000000000e2e00002fa0ae8000000
  | 61 => 0x15cc000262ad2f00009042d360000000000000067e0000000000099611b62101678b0232f400000000000000000027e1a82d2c0000000be9361c00000000000396c0b000000000000000000e35a60c43118f2a1b00003571296c18125e12d13d4acc0000000000055d0000000228834980000001152dd8345e00030180000000846000000000007940000000000000002805560000d5d8000b8600000d21b5c000333400000000001d9a8de98d40000000391ab02ce40000d9e0000000000061bb0dab33800000020b4000000000018e6d5e0000a928afa0000000000173e88aaf1c000061e851000000000003f799c40000f6200000008e20000cecb5000001c32b28800000000000000000d1500000000000946215c3ab3664cf2800000004c099b276e00000003778000d8c00000361596dd5167221a000000007ac516364a4540000000287e15116c200030380000e6c0000fc8d791b7c2e1b0b60000000738800014d2188e2c926a5438000000000000009f2cce83aad67267e6ee000000000009b300000000000000000073780000000000000147a00000008d529f80000000000000000021a8a2c00000000000829800000000002500548d7f9f8805f0000b6791148568000000244a089800000014b000000000000000acbb6fe06a2ec617600000000000bd630ee3a4a028aada2bc5ef34b600000000000000022931400026fa00001e8ddc09debd71b3200004fc6a314d00002d8885a0000000000069f80000000000000124a00000000000000883000054d8000644800074c00001cca5b200000000002e20c7713700000af000017fa4322cda0000000be01dded48000000000000000ea4620246800022ac892110aa27881c0003734000000036c330a00000000003248000000000000007ba800000016340001c040180000a8e800064600000f4a968de00cbc00000000000950000000098f8366707800075b94a20000000000274e000285a9b9945a0003462e250000923108c60500005b00000000280c00000000000000988000000022785e2a0a20002daac088000a3a0000b028b6200000000000000e43268400000007d3a0ce00016e00002f1600000000000000472800086e2500c86115a0efb4b86b0800000000000000000000000000009e6bb3806c00000003a093725d7310492d8000354ad80d96a81a00000000000000000318e00016fe434035c00000002c7000083f247801934f4000395acc300004a600000000000bdf000093500000b61d4a86580000000a46000299aba91c7a2fb000003919c6000000000002200000000883898800024908e9000000012925d01de2000000000000000000000000000034ba9e60fd8000defadc80002648e1b000000000000000000e47019a31b2bc4000000000017aa00
  | 62 => 0x1e80006f4a0cc0821534bd680004c000000000000573a952484000000000007ea800000012708b20fca000379e00000002b6b2ec0000000504b14860d83e86f9b1b289b80000000000000000002e2e7cdc000003b80000000266a00000004fd0000000000080a80000000000000000000007ba00e01947b38000d9d09720000000000004000027b2000000023480007bb13ae0000000ac027d80003054740857e0001d8aa672d7eb04287000000000000000000226a095800000007ceb03800020b80000000c244761f9ea861a2c8059928aee308a4ad894e9cd00000002a3e0000000000000000000000000000081146000000006979b92a5b800037d0db20002d245480000000000008080002421ab600017940000000000000000028ba000171a00012e0000000000000000000000acf92f2000030800000000001be44f4170c85783e400026b800031f4000326a68980004bd20640001d00000000057e0000d29aa7a7518000bae8c820000000aaf000000000005d5800000021d600000000000000041800000000002ad210e7c185ba490128010fa0585e6334ccabb38c8a88000007b5f600600000003078000000011b12d8c529d86000178e00000007bc849c52786926b22516000144822880002ee9978ac2aaa6d61af920000000bfe8000dee1b28000291a7a9b2e400000000000dfc180207814680001f1800015b9a08d6b02788ff2aecc99a3f80c5b240df0b788000317e2ca1c26a642c625dc10d61e48fc0dcc1a6099c825200037867e9a10c798a922bdb94284402d5e00000006e30000000000000013da000332e893000000000000000012262a8ae4988e7c00000006a51bb4000000053b0000c32002a139119aa440d8e06e964059b000000000002000000bbb235292700000001b38d7700004bf8000cd38c80000000000000000000ad49b28000d97ab0e0001a567bd0a54000198c0000000000000000000008c21db00f2000094710de6451d2a094046e8c514f21d40000a4e8d0800020a400016f4626000000000000000000807874200000004b51834c5b010a0000000000000000000003c0a1e01b89bbe0001e4066a1ffc3e600000a6361033300003acb2c064a8000df3000001e00005ad099200001640000000000195200000002ef344ac0800000cd800000014827f5b5c062c094aafdb3f0288961262c800000019ae7f68000000000003e00000003382000000000013c0c10b61a1d8079e0001a8200000008648000b048000b34320c02a282a5db8e1cc8ba50643a0332b7eb78a0000000000000000000008e6000000021b0bd993aa7f296747432e34ba2a6ec294b4b4687b2202671e647222ba000000004a9a2febdd0000000282c000006e00036a45ec91962b00000000000000000000000000a95b0aa000000000000
  | 63 => 0xfba00000003eb959c0001cacc6aa07e84a36c80001c9602888aa4ea000021c800000000008b5121a0000086000000000018ded3400009a881ac00007e8c1b907c8c880007b186740002800825816ae2b0000000000017082ca36880008bd08c40002fc08a7029a28a37a600038fa000000000000000000000e3f8000000000034fb23e0000000000095c1480000cd1160a12126f667c800000008869bb800000000003dd8000c0207da013b53600000000002f84cdb9074000129c00000000002730052b7920001b268b60000000000000023d23220000c96800e19480007bf0000921b8b6000176044310cc00010980001e38dd405c84088c7a1b70924b8f343c9fe3526112b95250186cae381ea40fcaf8c9169b400cb964a77427d40a384b20fc2c4289408fa6e0a4fadffb4ee01097d80dcac1ec2010b63890000bbd090ae4a9864dc900000002f76000000000000006f70000df395500000000000000000000006bd00003c60e4ec58000088032965ef991017db5eace49908e161af679b00006238000c5d8000000000051a9274277309462da162e578cd22c380000240daa6d4257e131000028114f4000132ed00000043800006b5848a0001d926db074ad730000000000048700000001318000117400019fa000049a0000000bd129b44b1800000000000000000000000059e8000000009c5371c7ec50826e08d8166815a038000209e8fc000058200004ba2294ce1387e0000000d8a20dc0002cc8000000000021aac090000000217a97600002cd80003e5b1f6d1831b466508947b5800000000009c8a45e0000e789308000cc81c8200000005e4a590000000000000000000000000115c39e997c00000000000000c168000000000000004badf5971e0000000cc9b7265891178348800000020d0a2180007e60cf69daac8e73b8712000165e92e80009708000adb91d4000000000005400002f0400013f0000109400000000000000000000000000000000000000000077a0000000000000017d09d180004d780009559c4400000000002a3039f80000000c2a0001abce3281582b1056035c8000be78000125249491329b8b61a05c09c8d86000000035009ce0000000000000000024cca1615a600028d43ca92900e3000000000f480880002400000549140a0000254000000000000007520ba6000000003b80001ec2b1ad9ea7da5f01004000351882cb256cd714d2e03813c9d480009d08000d32800010a2e9c142231e0003302c1fb618a131a2a0000000000000012b0000d6280008c1800000005f2000000052b00000000a1200032fca7a000051480002f001f6392b4b0de80000043b3de05480007be00000000fc60001716d659aa4df1b81256b984c54c000041e13fa80f91f49e19236d760550d2c97744c3000000000005889c749
  | 64 => 0x72500000000000a510df8a6500000000bfc00000005b30ab20000000000299624c35727599ee000009b84f10000000341e000221800018660000000496000060000003db800000004b80001bfe0002edc71300007122c8c2f1a82888f31023109e2e421114ecca90180000efe4fa2e48d740000ac4000017890c20000000ca8a5800e00d2a8b29b9a3a3b1fe20caec8d200ffe4971a0c97800000000b1200000000000000000000078d00008f1a90858a81cc0722b1c66fb5d2de8ad5c402aebe292000000000002b09d6c0000000000071c0000688c09a2549c32a920000000000000000000000002f2000001165fb11160000000000139e0001a7a0003426000364c000000000015e800033063d3195e00000004d48000336000000000000003546bd78b3c00000000000000000304a000000000000009eb800049f8000e4093cce4e05120001f0444a8000c5a09348a5ab38000000000032741b200000000000000161651f000000000000000f50000000056a00001c08dd45aa80c61498120e26a63c461353e0000000000086e8b8ad9626c000072180002a3000000000000002cde0000d020000000000359400021f80000000000061c000000000000001999738bb038fc03aab486d58866da037d2158b47a5ae08546e5a3e877983240e11dee0002c960001b9e0001a9c0ffb116ba78dd29fdb70a287a7e484130d24ca8e20000000000000000000000000000000000004ce2798dd21e183cda076d0fa6fc849052a00026a45fd9df850e8b96000000042e9f580c0805c0000000aa10000000000000000003b080000000966b0c83d092980000000000cf92fb8e0080006d6001668a33d80000000000000000000007808000000000000000002c2954c0000000dbb90880002670b9a8000430373800031e028600006d78000000000000000000001698348385c00000000002ef8a22a1daccf38c641e80000001f0c02015c84d2a9ec3448000c889f5c9e12bf8969b0c225692ac2fe0b3e65280008bb23be56d85c0364926089821ce000129e5ff8000000000000000003bc80000000000b0600000000000000232820101ce8523694e5598fa00008b4000000000000006f600001caa50a00000000001a3a00000009f89d2000038f6b751254d26a6e80002ffe144000093c800000000000001d2400030e20001dea000237c000181a5708000162800072027cc55200000000000be580000000eea3de8000000092c89d80000003246000000005c000087780001a611e2b2524b000027e00000000caf000000000000001f5035e91540a82ed200026d82b5800000000002611a5cd3000001d88bf64142f006dab8e800000000000000000388e03523669498000afd000000000004d516c6c7ea62412910ac59385b6282b19674782120000
  | 65 => 0x18760000000caf800078000000000000000000000000000000000e0f8000a0f80000000000c7a000000009d8d3da6b200032b4e5900000001c7001400000000000000310e0002a98000000000000007c500009e000000002f26bad0000bcf800000000008a602e60000000c04318a000000000031500001590a0900000000000000200465a0c36b6704f8175ae4cb11000076b17c63c594ba00000000000000000345824f0000c372802c14b52c0000dda000000000000000000000cfe00000f100009329108c67978684a89c4c9f80009018ba26d08e185910000b40acaa1910000000316e0000000cde9f867cf80000000000000000000012e62e480000be000000028780a88000d57972e0002face4380004f98dfe66eb72ad858d68000134494a0000cfe800078b000042038ec1ad9ff41a680000000000000003200013f20001cc8d318000bb88000000000038c10a26b7331c66d80fc3a280009b8067c42aa6600000ffa3b91b1e000379a8bc80000002ada9608000370800000028eea9716b200000000002c040ef00000002b888393766d8e9a68ac980000003488d2e98e2488af6c00000002ea80004d721d22aa8000b66987a0000000000038e0002a365258ca2000000000000000000000000000000000000dd07400000000294133c000000058b8000000000018a000000000000000000a5c084a86c84ec5ee18520001f3c18092f600000000002b8400000000001f520000000bcd0000000000000000000000f4a6780402cf3800000000000b6800086800009ca9216dfcb332859967e49300000000000b9a0f7c45a23dc02522a8000000000000002bc8c700002adc0000000000134600000008c5aa66a3e9fb20a48000000000073580009de126667214683380000b328000ad831ca00009e80509fd86b81f30000208093580003fc8000b9f80003e40000000000084d9ed06048000000000096e0000aa8284a26f03d62f0b2e05bb8000522a33e8272cbe00024527063002000000000028447fa03647882740e48b0a807700006a41c1282d96f08d634204aa1954de4018cb698000065800000024aed4ea02c3cba0d89442aae0000000c0aad4a00014e69b700008ef000000020860000000a580000000068400026325f09ecc0002d4e00000000000000000000000000006eb2a4000002147de32989d6803a6738000dab00000001e228ec000085e000070bab3257f07d000000006bc000000000000000000000000010d27a699b800017c00000002de0a3f000000037bca460b7c000000000000008b590be0000000a8b0000292800063d13d8a7b94aadb40000c3ea4140000000000005600036d8b77800000011de0002a0e00001aa403965ab58ad4c2bd0000000089c1b100000000000cce05be000028a0001c5c3898000710a418
  | 66 => 0xa4d800000000002f480000000000000271800007ec00033d02930e32c742e300002e1200000000000ccaac50000aa6888aa3784ca20b0aced27806a28c206e235b588b7c1a74d0300000001f0e0000000000000027480a46138000012af360000000000000096f00000002958680b11c78db03000000001850000b5d0000b8b00000000fa0ba624700000000000000000034180000000000000000014c49d6114261f1fb68702946a4f955e84f256ac512ad2702180488fa766000000009a00005bf136c0c4000000008e2d7e2fc60000000000000053a800007f05f458c87bc4d200000000000000000000000000000000000000000000000000000000103c65100004a936546fc800000012440002f9c000116a889b4860000000899800044e000000000004ce8000000000050380000000000b6c000000014f0b4000000000000000000043f800000018b800034e800016f60002c86361000000000000002fe02da8ff400000009ef8f9ccb0800000000000000f92000168c00010f800000006c6166805028648bd958e1dc15e275a9bba0000000000000000006400002bda47300000000b4c00027b800000000002af25358678ada00000000000aaea87a000000000035f0690802e5a3a1e8e5215f40000542000000039a2a42d7280008052c6a25e00000891380adcb10c75f2852d102d32538afda48b17f81be89940980000aad0c1a7308000d4c32de38b2b4a0889f9a0002e0a00000009f4b65c000250e8bab890000000000004be29c800000019e8000000000000000002fd800015da0000000a2f952c000068e59800004c2000054695d6d1e3736df900000000000000000014c08ee0000a9095d8000cb9b1460000000aec0000412000000000003908000e09000021a800000000000002ac04cd80000000ed61020000000000068880000001f3800000000000000d26000000033086f42b9c3d79e860000000d008ba400001de0000b7400000005908000bd918d000000000000000617a356aea099800000009fc8000000232ab9d0000411b7024448b8c896168a1f324a2b242eca1e111207e8207254a9a78b841132e158070577b3b07b000000002830b739f66ae6841232910861fcb2b000000009be24d0cdf0e3600011ac000000000000007a40000000000000000005e2000000000000001e980000e90000311838a100001198c40002530afc000018824dc3fb8f8c21ea7fe6f592f8501000000025ec53180000000f56c89acfa0b20616bce193cadf00000002304000116c23436b26d800000788392000268a9dd25ccb7a15f22ac19060000000aac800065980009aa00000000000000213430c8000b5c274cb0fa736ab6389200025b653d8b5621db60cc301e568c0381c8b780009e9000000000000002db6000
  | 67 => 0x306a1ea0000371000006035329f98000c218cb22d20cf4451800000005220000b5400000001568b9e00000004d009148b195c443a80005d407e60002374000000042c1cd40db800000000000000000000000000010d2116372000000000001682b2d9382e2207aeb09af62d6b9e60118800000021b4000203aa739f5a23092e4282054e0002b2c0000000c75800079680005b223a20790000e031ac6000346e000000000000008400000d63b9660208d6c000321e000192229c2ade20480000002edec033044000000007c28f0000351099326c4668000074c800000000000001fc8cf70000e58044633118cc00008309f18000849af7e3598000d348000000000000014fe00000000000000000000000000000000000b3026aea398ff8d159b62168b38e0000000000000015ea50800006d40002666533821846e2d340000000000000016a8000000324ce18909a6eba6380521b2c6d18a920000000000000000000000002dc0a47800000000000001ae880830fe00000008ff80000002fbe1a0b1f29918f8aaa18000000000000f8bc402300002583120be38b42b291810b463928abc0000a8880003b38000355a562822000000014300000000ada80000002d2064903869478fd69c389a4000000028ca98000000000f707280000a780000000d80000000033c484480007a780007be80006281dcc0001016000134e000097000000000001a5ac1d9f5600000006f380000000000000268cb3f0d620000000000000000000003df800000000005de800024c9a8a0000f087d038002fcae26b68800000022e4000120000015e078680000001b4c0b5a8f2d0a0000b3c2c689910000000157cd1d0000705b6e81f80000863800000000000001d808be13666ac2d660539f8e1b6a5e4af2ae940002f0c02b00000001f6cadd23aed592e38c702f98c42a2c4b66023aae49f2ac0fa5caabb93845f381be8228112adb000000000000000000000000000005c685500000000000000208c02a999650f800031b9806db10000a52930ae3114f81a0333682f80002baae780001c6c40ba56eb5d800065603c6b2f000010da546afb14a4961800000000002be3062b4e00000000000931800042734680000000366b208000000000024de0000a820002fa0cf310e60002ed49a600005b3a5c6bc6a78200021380002c2888400000268000000000081c0000000389c2d79bdac120000000000000a14c046a8e1a49e800071033c2000000000026d60000190000000099017a6000000000009a8c2d0000ca28cc65af06460001da457ba6fe0000000715800094b0000000192000002e01c986e400000000fb976c31880000000000000000047080000001b0a0000000000179600000009a0123800015ec0f980000001d340000000000000000000000000000000000
  | 68 => 0x1c95415061de2554bf728d20002f300000000000000070f00009b1800000029fca4f00000001a44000100c22c913a70eb2f09e29e3ea68800000000a000000009adb6fc0a5b67c00000006ec009e0000a169870000000208e00000006f7b3f20000000000120200036f80000ae40000ba04418b26d040000000336c145b60872f000000000009c0229e30e81c07568000d95959441104e006b857411336d200000001a580000001ed42dea8a6cee9fd45660000000315ea628000b4780000000000ab98438000000000000000001f080000000000000000000001f2000000030c400000001822fd450780000660eee8f00a3e2f512c28cc80001091e0a256131e16e2c30c62000036e000000000000000000000000000000000000000000127c63c07880000000000096c000000006dac9c796000072d0210bfa800006392b85b8b438474331868380000001d3800004700000000dee80000001a9e00000000abb39662f00000728b943230000000023c298a808000000097e800077f800000021d00000000000156c749a4f82a5a678d0580000000ebc232a976bef000096a1472000279a4158a8491dad44e2c055e462b6d60000000e5380000001e6a00027029fb0000000000000006d20001e164bb305ccd8800000005d240c1fc045900000002a70d051e7c48180007c02f1e88711bc4df8000352800000021fe000000075daa2800005e42d9260ee5bb3a00000e764eb00006fd36c6845295e3f8192e156000000023d0dde00000001af81d725d600004964a09c840a50000d288000000000000035605bc924e000126cd068b5cca500000000000d1b384eb5e00c827e36120002b2000031a2c0d8d7c0bf800027b940287c9d16835369228e0000bf9ab509110a600ca00000000000862871e00000000002e0800000002478000000104ecbf80006c4240e27f99980a7ac9a00010380000000d372880b18309c4b2000000024202db8000000000028f1d28000118e80b8da85d48000e51800005833eae1ca6ba17e2a02e2a893e65ea3de057adc6b9c0d2843c042ca13b47e0000000000264a13a1be26a99484c0780003d1b368e508a5e9281d7872630e800000004c900000000000da9800000000e6744800000000003d82c64000138e7ff80000003152000000000028c4d819ba00150454db286b400026180000c76000000000000000001b3e62a00001dc8b900000fbe55c0000000239e5740000b15154496d16ca03c00001a72f180000d48dd195000002a100c70000c4c8fdaaef204c6a617ae8a0800000000000000e880000000d13000000015260000000000243a3c3b89e00000003428000280902a81b00000001bc4000071a1e28f78aa8b282c48a1ec58830507d82e443c994fc7c4b796d35853e00026da85f9a4600000000000eb800
  | 69 => 0x23dadec0000000ade982cb3d000000002de000347c00023a00c8057200000000002faa0000000000000000015880003096202b39a0000000000240200038de000000000000000001d8e5ec170e000241e0002d8403e80008aa9e84a2e22a4a4c9ab4696243c00000000002520ae3800056492d6469800000000000000f528428000458a6f2ae52ee6e541db200000002ce0000d1193dc4b4238cbc1abb6a619dda0a7044084c95dca9cae00ae08c0434d039e04ab77c161214230f1416bb62b28772992cc4b2598c5880006c92aa85fba55e4700000bbc0000a4a8000000000000000000000000af489d40000000346842e00000006c7030e000156a360800098c00000000000000279409d0e72000166e814800000000008fd123c703181c9f380004502e1c87880004608b78000351a0000000000000000002d20540000a64a676272acc2a1c8000000153e000132800000000000000db309f05249ee41d3a43230b21
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8fa86dc143440018f0cbb8286880021fe157610d1001c3e42aec21a20078bc845d843440211b906bb086880023be097610d1001476412ec21a20048f4865c443440018e8cab88868801f2d1917110d100866a31ae221a20008df835d362440211b906ba6c4881621f21b75589100043f43ecab12200087e87195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d16244001958c43a2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800333188735891001c3f43eeab1220078be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440211bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000c7475dc562440019a8e7b8ac4880021fe1576549100045fc22eca9220078bc845d952440011bf06bb2a4880423720d76549100047bc0aeca92200387c851d952440050fd0fb2aa4880021fe1576d091001c3e42aeda1220048f4865c742440018e8cab8e848800e1fa1776509100043ec2eeca12200087f855d942440070f90abb284880022fe1176509100046fc1aeca1220108dc835d942440011df04bb2848800a37a0e76cc9100043fc2aed992200387c855db32440011bf0eb1e648818aa721163cc91001566412c7992200387e85dd932440010fb0bbb2648800e1fa16764c9100043ec2cec992200087f855d932440070f90abb264880022fe11764c91003c5e422ec99220008df835d932440011df04bb264880023de05764c91001c3e428ec99220018f4811d932440010fd0dbaa64880021fa1f654c9100043e43eca9922029c7471d9532440011bd0f31a648800a3721d634c91030d4e422c69922002acc8258d32440091ed0db8a64880031dd97714c9100063a32ee29922058c7476d9551440078e8ed29aa2880029d219525451001e3a3b2a4a8a2058d73751c151440091e90cbaa82881631d1db65505102b63a3b0caa0a2000e376519141440a776100a1a8288002ad219425051014e3a38ecaa822000c7765dc550440092e90ea8aa0880129d2195154110025b8402a2a8220538bd87d9340440ab0fd0dbaa60880021fa1f654c11014c3e43eca9822000c3f65dd13044001878cbba260880030fd94744c1100061e328e89822000c9c74d8d3044001938e831a60880030fd9774481100061e32ee89022000c3f651d12044001878ca3a240880732b1887448110006563a6c490220048f686dc520440018e8cbb8a40880a71e1db654811000734316ca9022055c78761952044045970edba240880732e1d87448110006d8388e89022000ae88650920440013e10ea0a4088003e85094148110
  | 1 => 0xe0b1a87080123ba1f5258a1000637baea4b14200287d85dd952840091d90eb1285080021fe1576cca1001c3e42aed994200087f855d932840070f90abb26508003171d6634ca100246e43ac69942000c5c7558d32840091d90eb1265080031b1d5624ca100066b31ee2994202ece662dc532840014bd06316ca880029760c62d95100061eba0e9b2a2000a5e831d365440014bb063a6ca881629d60474d95100062eb98e7b2a2000a5e831cb65440014bb06396ca881629ea0072d951014d3cc00e5b2a2000a5e8390b65440014bb07216ca880021fa1c42d95100043ec3885b2a202987e87c8365440010fb0f906ca8800297a0c62195100052ec18c432a200087f855cf64440070f90ab9ec888002a7a0e42d91100043f43ecab222000c6c72d9564440010fd0e32ac8880031b1c8655911041e3db80cab222000c5f65dcd64440018b8cbb9ac88800317d9473591100062e328e6b222000c6f65dc964440018d8cbb92c88800e1fa1f75591100062fbaee6b222000c5c75dcd64440018beea39ac888003171d473591100064fba0e6b222000c9e401cd64440019388039ac88800a3ba1f725911000637baee4b222000c6c75dc9644400199ee7b92c888003331cf725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000c7875dc1644400117f0eb20c888002a720d641911000556412c83222000a3d84d9654440538ece3b2ca8880123d21971951100063bb2ae32a2200087f855d954440011bf06bb2a8880423720d765511000477c12ecaa220028ec825d954440011f700bb2a8880031d944765511003c3f43ecaaa2200087e87d9563440018d8e5b2ac6880021fa1c6558d1000636390cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a2000c6f65dc963440018d8cbb92c68800e1fa1f7558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a20028ee87dc963440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c688003391cb7158d100046fc3ac631a2000a9c8458c634400159904b18c6880021fe157218d1001c3e42ae431a2000a5d83d9653440010ff0abb2a6880022fe117654d1003c5e422eca9a20008ef825d953440051d904bb2a6880421fa1f6554d1001c3e42ceda1a200087f855db43440070f90abb686880021f21975d0d100043fc3ecba1a200087d87d9743440091e90cb8e86880021fe157690d1001c3e42aed21a200387e85dd943440010fb0bbb286880021fe157650d1001c3e42aeca1a20008bf845d943440011bf06bb286880023be097650d1001476412eca1a2001
  | 2 => 0x77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000cb874dc163480011bf0eb18c690002972156318d200056a40ac631a40108dc835d463480014bd0b188c6900022fe117694d2003c5e422ed29a4000a5d83d965348001c3ea7b24a69000387d4c6494d2002476432e529a4000c6f655ca53480051f10cb84a6900031ed957094d2003c5f426eca9a40008bd84dd953480010ff0abb2a6900022fe117654d2003c5e422eca9a40008df835d953480011ef02bb2a6900063d2057654d200845e422eda1a4007c3c645d7434800187cebb2686900030f5d764d0d2002476432e5a1a4022cae72d9243480091d90cb9486900021fe157650d2001c3e42aeca1a40008bf845d943480011ef02bb286900063d2057650d200047dc02eca1a40108be87d91434800f17908bb086900123b2197210d200147c432e021a405ecac76d91424800f958ec322849017b6add07050920006363b6ea9924000c6c761d532480091d90cba2649017b2b1db644c9202ee563b0c899240029ce87d0d32480017930021a6490003391db714c920006723b0e29924000d64751c53248001ad6ea38264900021fe1573d852001c3e42ae7b0a4000c7575d47614800117d0fb22c2900030fdd764585200061e3aec8b0a40008be87191614800187eea322c2900030f1d464585200064fb26e6b0a4000c9c64dcd614800193ec839ac2900032719073585200066a308e6b0a40078be84dd9514800117b09bb2a2900061f21d65545200052e41acaa8a4001a74815955148039958e4322a2900032b19372545202f45fc22eda0a40018bc845db414800f878c8bae82900030f9d764d05200061ebaec9a0a4007cac645cb414800f5590ca16829000e1fa1476505200043ec28eca0a40078bc841d9414800317d0fb22829001eab2194250520006563b284a0a40008bf845db314800f17908bb662900732b9c864cc52000656322e598a40078be84dd9314800117b09bb26290003331d9324c52000637b2ee4a824022cac72d9140480095990c996609016f5a083754c1200e45f436e898240228be861d1304800117d0fb22609008a2f21f644c1200061fbaec89824000c3c75d91304800117d0e322609001e2f21c644c1200061fba8c89824000c3c7519130480bbd30603226090003171d7634c1200062e3a8c698240049cc874c930480095990c9926090003631d1324c120025e440264982400487c8759554840091b906bacc70800e1fa1f7558e102de2ec1eeab1c20048de87d4d63840018beeba9ac70800317dd45358e102dc3fc2aeca9c200087f855d943840070f90abb287080123e2017650e100246e43ac6a1c2007a9c8458d43840099b
  | 3 => 0x89806000cbb761d1300c001a70ea3a2601800336dd9534c0300056cc36869806000b5985d0d300c0016b70a992601800e1fa1773592200043ec2ee6b2440008df835d954880211b906bb2a9100123e20176552200243e43acaaa44004c787059554880090ff0eb2ca71000297e0d6594e200246e43ac6a1c400387e85dcd61880010fb0bb9ac3100121f21d65546200247a43ac2a8c40018bc845db418800317b09bb2831000237e0d76506200846e41aeca0c4000c757194765480014f30128eca9000317194735952003c5f43ee8b2a4000c9f74dcd6548001938e9b9aca9000317dd473595200064fba0e6b2a4000c9c741cd65480018bea839aca9000317d4473595200062f280e6b2a4000c5c501cd65480031ed0fb8aca900032ddd371595200065a3a6e2b2a4000cd773dc565480019a8e7b8aca900031ddd471595200065bba0e2b2a4000cb4741c565480019aee638aca90003351cc715952042e3dbaee0b2a4000c3d75d5364480010ff0ab9ec89000e1f21573d91200043fc2ae3b22400387c855c7644800153f06b2ec890002a720d65d91200055bc0acbb224000ab481597644800147d0a30ec8900028f61461d91201155cc06ebb224000c3d751d7644800147f0ab9ec8900028f21573d91202f556c10e7b224000a3f855c764480014790ab8ec8900028fa1471d91200051ec28e3b22405eaba801c764480455730038ec8900038dd4651d91200051f42c63b224000a3d858c7644800117d0e18ec8900022f61c31d91201145f43e21b2240008bd87c43644800f878c8ba8c8900022fe1d641912003d56414ec3224000c3e769d4644800187cecba8c8900022f61e65191200045fc3aca3224000a9f83594644800153906b28c890002ade0565191200055a40aca3224000a3e85184644800147b0a308c890072aba08531912000556c10a63224000e375194464480bb57500288c890002ae60051191200051f42c623224000a3d858c464480bb57501188c890002ae602311912003c5f4386232240008bd870c4644800f17d0f880c8900022f61f101912003c5e422ed2a240048ec865ca544800117f08bb2a89000237e0d76551200846e41aecaa240008f7815d954480031e902bb2a89001e1f21d655512003d1e422caaa24000a5c83595544809d4e902b2aa89016b1e1c1655512001c5f43ec8aa2405ecb870d9154480051f50db82a890003175d753d8d200052f42c63b1a40008be87d91634800187eebb22c6900030f1d76458d200065a38ec8b1a40008be87191634800187eea322c6900030f1d46458d200065a388c8b1a4084cbb70191634800196ec9b8ac6900032d1937158d2001c3f43eeab1a4000c3f75dd16348001878ebba2c6900030fdd47458d200061e3a8e8b1a4000c5c75dcd63480031ed0fb8ac6900031ddd
  | 4 => 0x24c0010fd0fb2ac2980031b1cb65585300043f438cab0a6000c6c72195614c00187ecbba2c2980030f19774585300061fb28e8b0a6000c3c651d1614c00117d0fb22c2980030fdd764585300061e3aec8b0a6000cac72d91614c00117d0e322c2980030fdd464585300061e3a8c8b0a6000cac72191614c0018decbb92c2980031b197725853000657b26e4b0a6000cac64dc9614c00f17d09bb2a2980022f613765453000c3f43ecaa8a6000c5f65dcd514c001938c9b9aa29800317d9473545300064e320e6a8a600387c859db414c0010ff0abb6829800e1f21576d053000c5e422eda0a600087c865d7414c00f878c8bae82980021fe1f65d05300043ec3ecba0a6000c3e75d93414c00187aebb26829801f2719273d053003e4e322e7a0a6007a9c8650f414c0c173100a1e829800e1fa1776505300043ec2eeca0a60018be87d91414c00f5390ca1a8298003271d9435053029dcc40286a0a600387e85dd9214c0010fb0bbb2429801e2fa1376485300045ec26ec90a6000c5f65dcd504c001938c9b9aa09800317d9473541300064e320e6a826007c9c649cf404c00f938c8b9e80980021fe15765013001c3e42aeca026000c5c65dcd404c0018b8ca39a809800327d9073501302de3d3b6cb982605be5b63d97304c0078f4ec32e609818f2e9db64cc13003e5d3b0c99826000e3865193304c0211b906bb2a8180123e20176550300243e43acaaa06004c7870595540c0091790eb22a8180031b98975d0c300146ec1ee8b106010acc835d5620c0015cf02baac418002b920575588300856741ee8b10600facd83dd1620c0095d100ba2c4180029ba14745883000536c28e8b106000e2f54951620c00159f06aa2c418042b320d545883000575c02a8b106004ae880551620c021c9ca7a9ac4180029ba17435883000536c2e86b106000a6f855c5620c0014d90ab8ac418042b320d715883000537428e2b106000a6d851c5620c00155d0838ac418002ab610715883008567418e2b10600facd831c5620c0095d50038ac41803eba60071588300856741ca2b106000acd83945620c001ccea328ac418012baa02415883000574c0482b106000a6e858c5620c0014db0b18ac4180023de05765483000c7a40aeca9060048ec87589520c00199ee6b12a418043331cd62548300247c402eca106004ce870589420c0019d2c5b8284181371b98b754c83017673316e2990600487c87595510c0091e90eb0aa21801f0f99175d043000637312eba086000c3d75593410c0018dceab1682180031b5d562d04300245e43ac8a086000ccf73589410c021998e6b1282180123b20b76484300043fc2aec908600387c855d9210c0091d90eb12421800333dcd62484300866639ac49086010cda53dd9300c0018f6edbaa60180031edd8754c0300065dbb6e
  | 5 => 0x80123721973951300062fb2ae72a26007c9c645ce544c0093b100b9ca8980022fe1176551300046fc1aecaa260008fb805d9544c00f0fd0fb2aa89800e2fa1f64551302dd2ec1ecb29a6000e1f53d92534c001c3ea6324a69816f1e1c36554d303265c380c8a9a6000cb864dc1534c0cb0f90cbae869801f0f19175d0d302dc3fc3ecba1a600087d87d97434c00187cebb2686980030f5d764d0d3003e5c322e1a1a6000c5e76196434c0091b90cba48698003279db6490d300070fb28c921a6000e1c65192434c0c3938c8b94869818f2e1c36450d300063c32ee0a1a605bc5c76d95434c0b7ab0e1b2a8698197171d86550d3032eac380caa1a6000a9e86dd1434c00f938edba2869801ea7a1b6450d3031e4e3b6c8a1a6063d9870d91434c00f938ec322869800387d946450d300070e328c8a1a6064d9870191434c0c5938c9b92869801276a1f7050d3031ecdba0e0a1a6007c9c649cc434c0051b906ba6c4980021fa1f65589300063a38ecab12600087e87195624c0018e8e232ac4980030fd9774589300061e32ee8b126000c3f651d1624c001878ca3a2c4980022fa1f64589300061fbaec8b126000c3c75d91624c001968e3b22c4980022fa1c64589300061fba8c8b126000c3c75191624c001968e2322c4980031dd9771589300063a32ee2b126000cb764dc5624c001968c9b8ac49801e2fa1376549300045ec26eca92600287e87d95524c0010ff0abb6849800e1f21576d09300145e422eda126000c5c659cf424c00f938c939e84980031719573d093003e4e322e7a1260049d8805cf424c0070fd0bbb284980021f61776509300145f43ec8a126000c5e76197324c0c51b90cba6649818b2719174cc9300070fb28c99926000e1c65193324c0c593d0e326649818b2761c64cc93031747410c99926062e8d82193324c0cb0fd0dbaa64981f61fa1f654c9302dc3e43eca9926000e4c32d95324c0018e8e3b2a64980030fdd7644c9300061e3aec89926000cb471d91324c00187eea32264980030f1d4644c9300065a388c89926064cb870191324c0019c8e3b1264980031dd97714c9300063a32ee29926000cb764dc5324c001968c9b8a64980032e193704c93026e2e3b6ea992607dc5c761d5324c0b78b8edb2a64980039318b654c93032e2e3b0ca9926061c9c64dd1324c0091b90cba2649818727191744c930024ec402e89926061a9e86d91324c0c7938edb226498193271d8644c9300070fb28c89926000e1c65191324c0c393d0e32264981872761c644c9300070fba8c89926000e1c75191324c0c593ee43226498003a3c80644c93000746326e49926000e8c64d89324c05d9a8edb8a6498003a5193714c9303566a3b0e29926000d54751c5324c001d28c838a6498003a6193704c930006adba8e09926000e98641c13
  | 6 => 0x53b408e9b2a6000a75811d3654c0014bd06396ca9816e9760c72d95302dd3d400e5b2a6000a79801cb654c0014bd07216ca980029760e42d95300043f43885b2a600087d8710b654c0b74bb07b8eca980031d5c471d95300043ec3c63b2a6000a3e840c7654c00147b0818eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca9800297a0c21d95300052ec1843b2a605ba7a80087654c0014f30010eca9816f1e1c170d95300043f43e41b2a600087d87c83654c00147d09886ca980028f61310d95300061e32ee8b2a6000c3c651d1654c00f17d0fba2ca980030fdd774595300061fba8e8b2a6000c9c74dcd654c001970e9b82ca980028fa1262195300051ec24c432a6000a3e84984654c00147b09308ca980029760e61195300061ebaea9b226000a3e8510b644c00147b0a216c8980021fe1571d913001c3e42ae3b226000a3e8598b644c00147b0b316c8980028fa1661d91300051ec2cc3b226000c3d751d7644c00147f0ab9ec8980028f21573d91300051f42ce5b226000a3d859cb644c00153d06396c89818ea760c72d91300051fc2ae3b226000a3c855c7644c001c6ea328ec8980028fa1631d91300051ec2c63b2260008be870c7644c00117b0e18ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec898002a7a0c21d91300054ec1843b226063aba80087644c0015730010ec89818f8e94350d91300051f42e41b226000a3d85c83644c00117d0f886c8980022f61f10d913003e1e322eb3226000c3e75d92644c00187aebb24c8980021fa1f65591300043f438cab226000c3f75dd1644c001878ebba2c898003171d773591300063c3aee0b2260008bf87590644c00147f0ab20c8980028f21564191300061f3b6ca32260008bd87994644c00117f0eb28c8980030f9d865191304370f180ca3226086e1c30194644c001c3ecab98c8980038719573191300051f42cc43226000a3d85988644c00147d0b308c8980028f61661191300054f41ca43226000a9d83948644c0c957501290c898002ae60252191300054f418a43226000a9d83148644c001c6ea3288c898192aea0051191300055cc00a23226000a3e858c4644c00147b0b188c898192aea0231191300055cc046232260078be870c4644c00117b0e188c898002a7a0f21191300054ec1e4232260078be87084644c00117b0e108c8980028fa1421191300051ec28423226000a9e83084644c00153b06108c898192aea0021191300055cc00423226000a3f854c0644c0014790a980c8980028fa1720191300051ec2e403226000a9e83c80644c00153b07900c89801e2fa1f10191300045ec3e203226000c3f549da544c00f17908bb4a8980028f613659513001d1e42ec92a26000c5f659ce544c00f938c939ca89
  | 7 => 0x3e74597321000187acaba664200726720d74cc8400864f31ae99908000cad7458b32100070f90bbb264200063d207764c8400043fc2aec990800387c855d932100011ef02bb264200063d205764c8400043ec36ea990804dc6e62dd532100018ecc3baa64200021fa1d654c8400043e43aca9908000c747159532100018beeb31a6420003171d6634c8400066a38cc699080048dc8758d32100018beeab1a6420003171d5634c8400064fba2c69908000cd47158d32100018deeab1264200031b1d5624c84000657ba2c49908000ce47158932100011eb0db8a64200031d997714c8400063ab2ee29908000cd663dc532100019aac7b8a64200bb3998b714c84000672b16e29908000cd963dc132100019d2c5b82642000e1fa1773584400043ec2ee6b088000c7775d4561100018eeeb3aac220012bc20175584400053b42ee6b088000a7585dcd611000f56908b9ac22001eada1073584400dd5ac20e6b088000e575394d611000f56908b92c2200029da1472584400053ac28e4b088007ab6841c9611003756b08392c220002b5a0c72584400056ac18e4b088004af2801c961100375e300392c220012bca02525844000578c04a4b088007ab684cc9611000156b09992c22001eada1232584400055ac2464b0880008f7874c961100011e90e992c2200029de1532584400053a42a64b08800487c85dd951100091f100bb2a2200121f21d65544400247a43ac2a888000c7965dc151100019e2c3b82a2200032721d635044003f4bb8ac6a088053e971058d41100a7d2a20b1a82200722f21d62504400e657c3ac4a08801ccac87589411000fd4ee2b12822014fa9c41625044029f52882c4a08801c9ae82dd3311000193ee8b1e62200123720f764c4400246e43ac69888000c9f7458d311000196ee8b0a62200123b20b76484400247a40eec90880048ec87589211000195ee8b1242200123d21d61484400065bba2c29088000c777194565cc02153d07212c99800e1fa1771593300043ec2ee2b26600787e87d9554cc0b78f0e1b2aa99800a1f21d6554b300246f41eeca166062c9e645d332cc1118beec3aa65981863761b744cb3030e4f326e899660049d8805d132cc10f9aeec38a6598003551d4714cb300166639264b0e60008ef825d951cc0051d904bb2a3980061fa1f655473001c3f42eeca0e600087d85dd941cc0031790eb22839818e2fe1d64d03300864e39ac8a066000c6f72949658c0090f90eb2aa9180031759773552303245fc3ac9a1c6004cb870591438c0090f90eb2aa3180123d21d615463000c5e422eda0c60018bd84dd9418c0011df04bb2831800a3b20976506300052ec1ca5b2a6000c7571947654c00147d09316ca980028f61262d95300051f424c3b2a6000a3d84987654c00187ae83a6ca9816e9760c74d95300
  | 8 => 0xe10aca2001e8fa1021594400051ec2042b288000a5e8308565100014bb0610aca200129ea0021594400053cc0042b2880048dc835d663100218beeba9cc6200021fe157298c4001c3e42ae531880048dc835ca63100011ef02b94c6200063d2057298c400246e41ae33188000a5e858c663100014bb0b18cc62004317dd67598c400052fc2ae53188000a5c855ca63100015af02b94c620002b52057298c400052f42ce33188000a5d859c66310001caea328cc62004237a1c2198c400046ec38433188000a5e8508663100014bb0a10cc62001ea7a102198c400054ec20433188004ada8008663100015b30010cc62000317dd75358c4003d4f426a6b188000a5e858c563100014bb0b18ac62001ea7a123158c4003d4f42062b188000c5f759d5631000f53d093aac620002a76127558c4003d4e422eab188004ad8805d563100c5938e9b92c62001ea7a127258c400054ec24e4b188000a5f855c963100014b90ab92c62001ea72117258c400056bc0ae4b188000ad4815c963100095b100b92c62001ea7a135258c400054ec26a4b188004ada8094963100015b301292c62001ea72137158c400052f42ce2b188000a5d859c5631000f53d0938ac620002a76127158c400256d404e2b188000ad9809c5631000f53908b8ac62001ea7a107158c400054ec20e2b188007a9e84945631000153b0928ac62000395d465158c4003d4f420a2b188000a9d8414563100095b50028ac620002b66005158c4003d4f42442b188000a9d8488563100011bd0e10ac6200023761c2158c400052f42842b188000a5d85085631000f53d0810ac620002a76102158c400256d40042b188000ad98008563100018bea6bb4a62000297e0d6594c4001d2f42ac72988000c3d65dd153100091b90eb1aa62000327dd16354c400063cb2ee0a988000cd963dc1531000193ac6b8c862001eaba13525884003d5742442b108007aae849d5621000155b093aac42001eab211755884003d57424e6b108000a6f855cd62100014d90ab9ac42001eab211735884000573c0ae6b108000ae4815cd62100095d100b9ac42001eaba13535884000556c26a6b108000e4f5394d621000f55909b8ac42001eaba12715884000556c24e2b108007aac845c562100014dd0a38ac4200029b614715884003d57420e2b10801caad841c5621000159d0638ac420002b360c715884002575400e2b10801cae9801c5621000f55d0928ac420002ab612515884000733a8ca2b108007aae84145621000155b0828ac420012baa00515884000574c00a2b108000a6e858c562100014db0b18ac42001eaba12315884000556c2462b108004aea808c562100015d30118ac42001eaba10315884000556c2062b10800487c87595521000187acbba2a4200123b21d625484000657ba2c4a908007c
  | 9 => 0x75cca500047bc0aec994a0018f4815d9329409b8dcc5baa652800317dd6634ca500066a38cc6994a0048dc8758d32940018beeab1a6528003351c5634ca500067238ac4994a00097980dd541940018eeeab0a83280025e603754c6500054f41c85b22a000a3d8510b645400117f0eb20c8a8002a720d64191502b43f436e2aa2a00497a87dc154540011bf0eb18c6a8002a72116318d5032d3c402a831aa010ccc325c863540011ef02b90c6a80063d2057218d5003c3e42ceda1aa000c5d75d8f43540018baea31e86a800237e0d74d89500846e41ae9b12a068a788055362540031ed033b264a80023d606764c95001c3e428ec992a00187c855cf615400f0f90b3b682a80062f21176d05500046fc1aeda0aa0108dc835db415400187aebb2682a80121f2197550550024bc402eaa0aa0018be87d91415400117f08bb662a801e2f21176cc55000c6e41aed98aa0018de87d8d31540018eee328acba000297e0d6594f400143e43acaa9680028dc835db32d00051bb07bb265a00021fe15764cb4001c3e42aec99680008f7815d932d00031e902bb265a000e1fa1773587400043ec2ee6b0e80008df835d951d00211b906bb2a3a00023be09765474001476412eca8e8004c787059554900070fd0fbaac720013361c16350e400143ec2eeca9480008df835d952900211b906bb2a5200023de057654a4000c7a40aeca94800087f855db32900070f90abb6652008a6761c43cca400043fc2aec994800387c855d932900011ef02bb265200063d205764ca400246e43ac6994800387e87dd561900b10ff0abb2a3200121f21d65546400247a43ac2a8c80228bf8758b419004535d05ba663200021fe15764c64001c3e42aec98c80008ef825d931900051d904bb263200021fe15764864001c3e42aec90c80008df835d921900211b906bb243200031d5c651d95400062e328e6b2a8000c5f751cd655000193ee839acaa0003361cf70595400062ebaea7b1a8000a5e858c7635000153b0818ec6a000237e1d6318d400052e42ac631a8000a5e858c463500014bb07b2ca6a00433618d7090d400143f43ecaa92800087f855db32500070f90abb664a000a3720d76cc94001c3f42cec992800087d859d932500031ed033b264a00023d606764c9400146f43ec69928000c5c75d8d32500019a8e3b1a64a0003171d4634c9400066a388c6992800087f855cf61500070f90ab9ec2a00030fd9774541400063bb8ca2b288000c5f739cd651000f47908b9aca200129e20173594400253d404e4b288000a79809c9651000f47908b92ca2001e8fa1232594400051ec2464b288007a3e849c5651000147b0938aca200031ddc671594400253c402e2b28800087e878c565100010fb0f18aca2001e8fa1031594400051ec2062b28800087e8708565100010fb
  | 10 => 0x29a820087d859d953504018daeba96c4a08021fe1570d894101c3e42ae1b12820287c8759552504054d904b2aa4a093b1d1c565549412d53c402caa9282078f686dc552504070fd0b3b664a08021f61676cc9410146e41aed99282018bc865d332504070fd0b3b264a08021f616764c94100c5e432e899282539b8805d132504051bd0fb1a64a0803171d7634c9410062e3a8c69928200c6c75d8932504019a8c7b8a64a08bb3918b714c9410063cbaea1b028200ab984d4360504015e302286c0a08023ee1d60181410053c42ac0302821087c8759554cc4070fd0bb82c5988021f6177058b3108477c3ac5a1662078f7865c742cc401aa8e3baa6598a3317dd8754cb31006aa388ea9966262c9c74cc960cc4c3938e8992c1988029760e52d953100636b94a5b2a628bc5f75dcd654c4051dd0fb92ca988031bdd4725953100667b98e4b2a6200ce472dc5654c40117f0eb20c8988063721973951310847a432e32a262008df835d9544c4011df04bb2a89880a3b20976551310047dc02ecaa262048f8805d9544c40f0fd0fb2aa8988061fe1d6594d313dd2fc1acb29a624da6c82596534c4018eecbb8aa6988031b5d752d89310043fc2ae1b12620387c855c3624c40f1dd0fb1284988031b1d7624c93117672316e2992624dc5c76dd5324c49bc98c5baa6498803551c7754c9313ee2e3b0ea992627de4c621d5324c401aa8e23aa64989b2b3a1b724c93101567436c499262019d687dc5324c46b9a8edb8a64988bbb118b714c93135cebc3a6598a6201ad4864cb314c45dd88c4996629880b331c932d81310047dc3ac03026200c5c651cd65484018beea39aca90803331cf72595214563bbaee2b2a4200cd473dc565484010ff0ab9ec89080e1f21573d91210045fc3ac832242008df835d954484211b906bb2a8908023be0976551210047dc02ecaa242048f8805d9544840f0fd0fb2aa890803175d753d8d2101c3f43eeab1a4200c5c75dcd63484018d8ebb92c6908031ddd77158d210063a3aee2b1a42008df8758c63484014b90ab18c690a26b5e056318d210846e41aea31a420087f855c063484070f90ab80c6908022fe117018d2103c5e422e031a4200a5d83d9653484010ff0abb2a69080237e0d7654d2100477c12eca9a42008f7815d953484010ff0abb4869080e1f2157690d210846e41aed21a420087f855d943484070f90abb286908023de057650d210047dc02eca1a42048f8805d9434840f1bd0fb1a869080a3d2197110d210047dc3ac03024200a5d858c663940014bb0b18ac728002a76103158e5032c3fc3ac729ca017a5f8758e53940cb8bf0eb1ca7281371b9897294e502dcbdc32e129ca000c7b865c253940012f301baa872800317dd56350e5003d4e422c6a1ca05a97986dc152940018f30db82a5280025e603
  | 11 => 0x4c8018ecea30cc0990031d5d4619813226c3e436eab02640087e87d95604c8018e8e3b2ac0990021fa1c65581324862fb98cab026400c7471195604c80187ecbba2c0990030f19774581320061fb28e8b026400c3c651d1604c86b1e90db8ac0990031dd9771581320063a32ee2b0264008f687d85604c8018eeebb0ac0990031d1d761581320065bba6c2b026400cb474d85604c8011ed0e30ac0990031ddd461581320063a3a8c2b026400cb774185604c801968e830ac09923f35dcc61581320047dc3ac03026400ab884580604c91d87aebb24c8a89631ed9470591510045fc3ac8322a200a5d858cb63544011bf0eb18c6a8802b32096318d510864e21ae831aa22d87d87d8e535445b4bb0fb1ca6a88031761f6394d512ac3e432e129aa20187c865d743544018baebb1e86a8803175d463d0d5100c3f436eaa1aa2008ef825d843544051d904bb086a880237e0d74d89510846e41ae9b12a20287c855c36254401998c439ac4a89db1d1c7645495100cbb43ee2a92a25587e86dc152544032e903b82a4a88061fa1b75cc95100cbb40eeb992a20187e86dd532544071ed0db8a64a88023ee1d60181512c53dc2ac0302a207a3e849cd65d04018bee739acba081e8fa1272597410051ec24e4b2e8200a5e839c965d04014bb07392cba08029ea0272597410053cc04e4b2e8207a3e848c965d040147b09192cba081e8f21170597410052fc1ae0b2e8200a5c835c165d049d4ed02382cba08029d60470597410043f43e40b2e820087d87c8165d040f47d08102cba08028f61020597410052f41840b2e8200a5d8308165d04010ff0ab94c7a080e1f2157298f4130c6ec3c6531e820087f855c263d04070f90ab84c7a098a37a1c3258f410052fc1acb29e8200c3d655d253d04070fd0bb82c5a08021f6177058b410143e43acaa9682028dc835db32d040f87ce8b2e65a08030f59574ccb4101c3e42eec99682018be84dd932d04051bb07bb265a08021fe15764cb4101c3e42aec996820087d86dd532d04010fd0eb2a65a08021f21d654cb412763a38aca99682019b4815d132d04c137100ba265a08031d997714cb410063ab2ee29968200c78651c1655051b87eebba2caa080317a1773595410147743ee4b2a8200ccf73dc96550401998e7b92caa080333dcc725954100666398e4b2a8200cdb73dc165504019b0e7b82caa08033adcb705954100674396e0b2a8200c7b751c165504019b6e6382caa0803361cc705954100675b90e0b2a8200ce8721c165504018eecbb8aa8a080e1fe1d75d8d410062fc1aebb1a8200c5d75d4f63504018baea29ec6a080333d8d7298d410866631ae531a82008df8758c63504211b906ba8c6a08021fe157018d4101c3e42ae031a8200a5f83596535049b4d904b2ca6a096e9e2016594d4100c5e432e9
  | 12 => 0x31ddd471595320066bb98e2b2a6400ce7721c5654c80147d08308ca990028f61061195320043fc2ae3b22640387c855c7644c8018ece3b2cc89926f175cc65991320063b388cb3226400c77655c6644c8018e8cab8cc8990021fa1f65591320063a38ecab22640087e87195644c8018e8e232ac8990031dd9771591320063a32ee2b226400c7b65dc1644c8018f0cbb82c8990031ed9470591320063c328e0b22640387e87dd5644c8031ed0fb8ac8990031ddd771591320063a3aee2b226400c77751c5644c8018e8ea38ac8990031edd770591320063c3aee0b226400cf371dc1644c8019e0e3b82c8990031edd470591320063c3a8e0b226400cbb741c1644c8019e6e2382c8990033c1c470591320045fc3ac83226400ab880590644c8011ef02bb4a8990063d20576951320051ec26cb2a264018f681dd9544c8011eb03bb2a8990021fe1576551320047bc0aecaa264018f4815d9544c8011f700bb2a8990123e201765513203c3f43ecaaa264028de86dcd544c8018becbb9aa8990033518773551320062fb28e6aa26400cd4611cd544c89b8d8e5b2aa6991f61f21975d0d320063a30aeba1a644d87f87d97434c8010fb0fb2e8699137179db65d0d323ee2f3b0cba1a6400e1f65d93434c9358bcec328869900a732097110d3226f27b1ecb9926410dcb305c3324c8018eaeba8ec2990022fe1170d853203c5e422e1b0a6400a7685993614c8014eb0b326c2990029de1564d85320053a42ac9b0a6400af380593614c8015e100b26c2990bab5a1b43d85320063aba8ebb0a642ead583dd3614c8015cb05ba6c2990029da1474d85320053ac28e9b0a6400e3754953614c801caea729ec2990029da1743d85320053ac2e87b0a6400a7685dc3614c8014eb0bb86c2990029da1670d85320053ac2ce1b0a6400ab7845c3614c80156908b86c2990bab560c70d853200572c10e1b0a64008f687143614c8011eb0e286c2990031d18775585320043f43ecab0a640087e87195614c9338bee632ac2992631d9db65185320071b3a6ca30a6400e3574d94614c92fcaae7b28c2990023d61e65185324b53b42cca30a64008f787594614c92b5af06b28c299002b9e0965185324a53b430ca30a6493c7676194614c801c6ce8328c2990038d5d065185324672ab98ca30a648ce5632194614c919ca864328c299233990c8651853246733900ca30a64008f587990614c8014ed0b320c2990029d61664185324956ac1cc830a6400ae582990614c8011ef0eb20c2990029de1564185320053a42ac830a6400af380590614c8015e100b20c2991aab5a1b43185320072a32e8630a6491ad68610c614c801ca8ca218c2990039919732185320063b38ecb3026400c7671196604c8018eecab8cc0990031d19571981320063b3aec33026400c7575d8660
  | 13 => 0x63bb8ca2b2e8600a7b805cd65d0c014f100b9acba180297a0e72597430052ec1ce4b2e8600a7a809c965d0c014f301392cba181e8fa1232597430051ec2464b2e8607a3e849c565d0c0147b0938acba18031ddc671597430052fc1ae2b2e860087e878c565d0c0f47d0818acba18028f61031597430043f43842b2e860087d8708565d0c0f47d0810acba18028f61021597430052f41842b2e8600a5d8308565d0c014f50010acba18029e60021597430052fc1ae0b2e8600a76811c165d0c014eb02382cba18021fa1f20597430043ec3e40b2e8600a5e8308165d0c014bb06102cba181e8fa1310597430051ec2620b2e860087e8704165d0c010fb0e082cba18030f5977454f4301c3f42ee0b16860087d85dc162d0c018dae5296caa18031e19470595430063dba8e0b2a8600cbb741c16550c019b6e6382caa180317d97735514303c3fc3acb29a8649a5f835965350cb74f100b2ca6a18030fd977454d430043fc2ae1b12860387c855c36250c018f2eba86c0a1802bc60450d81430053d42e41b028600ad9830836050c011f70eb00c0a18029e21560181430063bb8ca2b288610c9e53dd94310c0193eeca9a86218031ddd751584430045fc3ac8322a400a5d858c7635480153b0818ec6a900237e1d6318d524f52fc2ac631aa400ad48158c63548014bb0b188c6a90022fe117018d5203c5e422e031aa410cd8305c063548050f90cbae86a90023de057690d5200c7a40aed21aa4108ec865ca43548050f90cba886a90022fe1170d855203c5e422e1b0aa400cd4611cd61548011f70eb00c0a90031ddc651597420846e41aeb31e8400a5e858c663d080f1bd0fa9ac7a100317dd75358f4203d4f426a6b1e8400a5e858c563d080f53d0918ac7a101ea7a103158f420052fc1acb29e840387e85dcd61d08010fb0bb9ac3a10031ddd7515874200c5ec26e0b0e849dc3f75dd165508011bf0eb18c6a10029760f6594d4230c6ec3ec721a84628de8718d43508010ff0ab9ec2a100e1f21573d854200c5e422e1b0a84008fb8758060508bd57708b00c0a100a3720d76553320047dc02ecaa664048f8805d954cc80f0fd0fb2aa99901e8fa1365553320845e43ac8aa664078be84dc161cc80117b09b82c39900e1fa1f75583320052ec1ca3b2a6400c7571947654c80147d0830eca990028f61061d953226d2ec1ee9b2a6400c3d741d3654c80147d0838eca990028f61071d95320052f418e3b2a644da5d831c7654c8018eae238eca991361fa1e31d95320043ec3c63b2a6400a3e840c7654c80147b0818eca990029da0670d95320053ac0ce1b2a644da5d831c3654c8014db04386ca990028fa1310d95320051ec2621b2a640087e87043654c8010fb0e086ca990031d19771595324e62fbaee6b2a64018f687dc5654c8018eeebb8aca99
  | 14 => 0x100680000a80080980000000080000480100100300000280080000180400980000000000100380000180080100000000000000300180880100000300000080380080380000000180080000001080380400000280100080100100080180080180080001200180080000000200180000b00500000000300980080080280300280200180200a00200080480080000080000100100000000180000300280300200000000080000080100000580100200080200000200280000100580000300200080380080600100a80400080100500100b80000180380400080080580480200080180880180080100080800480000300080100e80000000000100000000080100180400100500080000080000100000500600000080000000000000280100500300200000000000200000000180300000580080200000300000200280100080000000100080000000100000100100100000280000100000100000180200080100280100000000000280400000280080000380100380000080001680100000300000000200d00100000000280000200280280100000080080000700000000000180a00100080100300b80100000080000980080080000980300480000080280000180080200000880100100381300800900080080100180000100880100000080180b00100300000380080080000100000200080800500080080201280280100000000100480a00080281080000080100380280680100000000000200080400000080100000080300080000500000280000d00000100400000400180000000000000400000000080000000000080080080000c80500000000a80100080080680b00100000100080100080000180480500a80180000580080400000100300480180000900280580180480080100000080080000000000280080000180180080c00580180100780100200080a80100000080180580000000000200300880000580180300500580200000080180000580880200b80000000000000080300080000180080280000000000300580400580000600000000180000000080200080000000200880c8078000010008000018018000000048000000010008000030000020028000060000040000010018008030010018008020028080000010030000000008038028040000038018000008028000000010078080038000020028030000030008000000008023de057298e5400c7a40ae531ca800a5d858c7635500153b0818ec6aa00237e1d6318d540056c402c631aa810cd4315c463550014bb0b188c6aa0029e61410d81540047dc3ac0302a800ad88358060550870fb0db9aa92990e5761b73552530062ec36e6aa4a6008bf875906454c0157100b20c8a98022fe1170d855303c5e422e1b0aa6008fb875806054c0157108b00c0a98029760e525974300
  | 15 => 0x600013e49715a7397980000000007880004034790000000006c14a64eb62f1454b90000004594be3a00325205535401180000005cc00000000050a0002580000000005836d003942500000010219b5bf59a0000004de6e500000010e0000000000005a32bb07d42722960842f29500000000000000021654a03100000000074c11a1e46fa6ef6193f329f4444943be34500002c2860f10006600000002822a85906946435290005f800000000000053679431c3e900061153800000052c00000000000012f0000000000dc2bd27f4da06407e0000006e83c55150000002630000000004e263713461a6400005fe3855df1ac38e4d972600068c0000000000001790000851934c80000000000de28a0006c53e612e05600012600048b0004c54400000007200000000003120000001bc23b68e0000000005aa73b76333071638300000001a0001016d40004014fa0760001f13a148c0005d831a35b5974cb0000000ad6c048400017a0002b500041b03e0000003464457106675be00025d00045838b32b27d76a41554b5ee16d60c00072a0003556283280e246753d4bb5172396c22e13840304925f471800000004c6351660000000007977060000000002000000812a20000006b100000061e1e977d51f4043764960f70000a411100054578c25200022a7760000000700005c500054473d15f4d333e0f94417612264050003b612c0002370942d836b00000000051960300036826c0006b413f35e5240000000003886cd00000000009d0004436a20000000dd1337144bf6ed0000000000000000002d71841362365891f231114b00e69812743f00007300017537967f0d920c3770001e639d0556f66af75e60d00010c71500057570d1b73c140f23810b2a05d64dd4894af00017200021d4364c20000000000005965d44fb61565f16c01313100000049d68b5c679f20873645f43e0906733fe63f7380003ab64a0000007190000001a76a96537111ab3db00077b0000000000006440002d110f4f979c3490000000004560000000000000660001f44357955e244d0004f325534b6cb11408c5131250e30002dc5a12bf48f1ea3ae70a00068431030f3e121a03600000000005a46036e2cf00009a00000072c0006ce0006e20000000004025a844854d00015169d25b78600038111900028e4f44ad05800046f4096be60045400013725e0bf3a31a922730d5603c40001160950465390000005b96232fb0f51ce35309843170f54600015767467552d00000000100780080380700500000200100000380080000000000000000000000480080100180180080100080080100080000100100200000180000700480200200000000180180300280001000300200000000080080000000000480100000280e80000000280d00080d8070088000010008010
  | 16 => 0xce00044f0000004ef00066d00062279d00000029745d0416da0003fd00035a7816b723e37800018c2110005414b80000002e26321391eb3e43fc4a10002cb4ed18600079b62b0002be2211de27b00f00000027465500000000900014d0005e764b62d0007960002b31d900000048d0002fa0ef00059e1890000006d100055800000000000057900000008a1766d234f3fa00071376c0eb0006b83c06ee3f50e400000017f2875c326873700037d0860831800001e549e04a48306902a6c93c70000cd26d75c34c6ad0004ce1904620000fb0c567c0003b700000000009634a0000000002cc31625629b00006100052300000b24957250b2037017792996913410002420006921ee2ce19100070b0001bf00000000073a1a41497a24ae0243b32792022513d458f00000000065d00000021e0000000000006726482e30005f71e80007740005310000000000000ba42056800000000004900000000000000071a64d0000000000005a906f63300053536000015d00000000077c27e2fe0000000007a16df0000001e702b44c0000002f500000000000071221f6a33d800000000006a5a500000035200000075600000059319e50e3fb4955a44166a46065a02282f333837c0ab7026654aa4f000000028059500017e4d72220ee43c33100039a4fd4875925e10005672e63740000001c63d60005b836a4e60001c80001b042200011b69e5320006bc00000016063c3b90000ca0006500000004e100054958b00033d00000057e78507f0001be03d77a0e800000000000000045c1171610000033e80006f759900000055e0000000000000000005260000006ac38c0002625bc20723c00000026900050563e2243e00cc68f00000069f1dc00000058e0000000b059147358000059f0f250c6807ab75300025000016e6ab4c30002aa6297756017aa6410006fd0002c400006700038a00010443d04855c0000790522a500013c5946956971cb42e22d0000005bb17b66b7a52d200076d0000000006a80006c30124101465214e760f00067a0a26b06e34785da3070006f80aa6820cf0007270117a77220602a454701f0005ce0002f02ad00033f00043b2610a149000022c1b26eb3ed6266c602759b67079023d00000074a71b31836f4db1941062060c847b78a6f45f91a600d00077f02f0000005770103e23aa2602a90d02830fa1dd71f46838f4a209243a51e1446cf33700065b0c70000000003170000004753636ff7787703356f104d6075cb56f4714187691e13ce6ea00001c0000000840002d36f90a953f0214d251d4ca4e551860b0a555a3274a863811d00076b4551080002536210003b04a33653eb00055b00060400000043368d3a51af3510263965980000000000000006963990000000002e900000000000000067d00000000000000026e32
  | 17 => 0x76bb06c2d45302886bf3c26c814116732414e00813b20f0e15fb1fe0d264728d3c358243824d7843af36661400028b46421b7604cc74d5271a569318251465677e37f0b13a81fd0a065a22e49347e73f45703c48140c0ea0000000872de5e018e0000000000003b20004d10003d90003ee0000000005dc19860e0005c229318a00005b00065c4210006b50003e50be00066a0000000006b30006cc0004a000000015b00015905e0b23df00043400014f20a5ec5164773863590f40002345f15f25d35043984502d629e00035c4f85b300051b0170002040d500000000046d00000066200000000000000000000030a3671950000007726fb4bd66f4e047f6303d22902c70330000000000002fd3dd0002590002856630000001850002470004b60006891f80000df4d40002ed0004b400044918d0040fd1b930939c4860002c60003644980001500005e400072d14861300005973072e0002673d500000042a01600024b33c0005743805c00000004691d452500052a53a2a13046361200000000006660003b51fb0340a30000006a02c90000000c42b62707625d50000002f77350005080002945b65ae2d00a75e94ea48500000012138d1280bc0001032640884245780721ba4b100c0cb0441c50000930b600047a3056fc3f00006f329a7777a45d13211b832f00000000073e29c0002b73723bc20d3424cf00064524c4b02174232b110a2f85504ec0000000235ed4c100030819a0000001cd5017500000006ae0000973bf14731f1f90002a600057300000000000044e1a05ef35400000013d00047664f62c0b90000002b01434f775a0000001620d100004e1c20004530f05af0005cf2090e67ac6b91226e132a17158100039200005c57001900056b2ca44748e6182ab6343cf00041376f1353911960c226a00032e57c00041f0003032b80005430003dc4304a73b806b78909b0002e80001127660000004d60006614705520005ad03b42814a0ec4113730000003f80005120d34e31542485333a611f1bb0004d85a617c00000000000035d5d71c70000003c661b1fa2f60000b425a59c1b616f3232f424568130c56301d1d879154f40d31e1304c753b2305887553703f45ba01e51c4f50e73582af37a1e06e91882145d05dd33235f30b0001875c702e0570f821807b6520fc64c5c856904511508d09f31341463a12361717d00078b0003140002760001b445a0000000006831b51000000002ae49900008e4b30000001325cd00019d0000000000007170004b20000001584a54ab0003bb5c12440f30000000000000000000000000780002c06fe00006878d0000000000004126d30001050000000000000751e300000000055500046e0476164ee61f0990003a229d31b0500007a95e370e2540000002f92015000000007412f25fd67e71d
  | 18 => 0xd0004f67050000000001406585db55425f00000000000010d00044244b0005b168600000000029149c0001db2d96f279e26b0001530000005b74c06b61b31ec6517516dd33423557a61d2ac7653505bd1b14e808b37e3222d54911650db00048058457116a5f540a54c5de0025d20000c005f5e60001834191737213ff7280000004d000014265e55f39f1f040b0910006d578f1d33a40006dc00000029627220b1e20001aa0006c70370740b50af3b10b80006b20000000007933200000007831777315280000000005ca72b74e5653560000005b200069b0142ef5626872770005e87684173ec36927a67600032c61002976456c1693ef0005422c20000000005b452b51a2310062c114c06d45155d72f0000d475f0000c311000000000000000016866c2c82753d300000023f40727c1d55666f07483bd10908016b4a40005115223f20007475ff3015b079a3ca0000000000e95570000000001ed0006e650f34377339367b7a077140023232d1741c93cd0000000005646880532a33625483570bd4e400040e2e46711da2462194bc0002f13cb17805419731522b0006aa3da4292844fc0001a86397460c12ec15c6a55b54610ae00074239e69a5f667721c5a21f61565ab74904339b04b53c13826f00020e2c339000000000025700000000000022331d0000005c93c91633290000002c553436d0000004633002ba3254cd00000000000000000033b43200057f00000011c1520007290001a336100013a00000000000000053e73300056e08f5e501b3972a70000000003f100574470036c00049f58c0000004b50003cc0150002ff0d600064e00000008916400a00000034e08250918b2050001d65860000006690000005f32e76090005f06571f300000047d06e7094e92b93e36545376256424461a241e50d1cf5c449a1ae26524e34d2e519c1ef3f60e07527040bb00002838200033903f47c0000710006123750005104080002130000006460005ac2df24f1292100000ed3f97081c363b66e6993a90000007826d94370000002bc0004d52da2124264dc6680ac71c00058d00060503522f6787401700001927a80005024741fc3940000000006d776e3de6e049b1f712d56a0257250ff2b400075d3e73b441c0fe1ad6e47a65d904075470c1242cd2985762896ba3483d74a90a806246a00075838900056d0000e572300071e6316bd15e3334ba75b23360246b3196de0d82b201800000000000160a00062e0000000001d10386d80001ca07a44a52f28c78e3956e70000005fc00000003a3406ca5854f12e073c41a0001d00512ee0007240000f61df0000000006200000000004c62660650d70c604200030e7436d675945242d6792200000000005060001cc5fa02d1c42730000000001553ac55134773218f30605d19937b3d155648a0
  | 19 => 0x79200076769c4720207340da23a0000002810b300000052e00079909c46c4df50324345b5eb0c957b65925c00000057d00040633a12b06368a0004b70a643911300000000000048200000000000069074f00000028f70321511e19f0006276852dd0003360000000000003ba00000000000000000000000054e6a700000046512a00029200007c00000074b6247570003d01c024a4886a14ff0223ad6f51f555958700045e7450b759d1bd3024f258a7876c42eb6641d224161c3870000000002784fe5613c80774c92710001d75a742b3447805076a600063d3a700000000000009e3ea0000003f700042c1070006ec0003712fc0007076490000000002ea0004664c46db0000000000000000000000001a10002db7a30004ac2251811c162a04f0002401ff5ea41
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x81b01280020000038204b711188711d5324c50dc18701946450d30007051d4641c5324c001455911407359520006161c0835955448001531951c474481100066821d4250520440016a0965094148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94b
  | 6 => 0x94e
  | 7 => 0x5
  | 8 => 0x124b
  | 9 => 0x124e
  | 10 => 0x98a
  | 11 => 0x98e
  | 12 => 0x128a
  | 13 => 0x128e
  | 14 => 0xca
  | 15 => 0xcb
  | 16 => 0x4
  | 17 => 0xce
  | 18 => 0x9ca
  | 19 => 0x9cb
  | 20 => 0x9ce
  | 21 => 0x12ca
  | 22 => 0x12cb
  | 23 => 0x12ce
  | 24 => 0x168a
  | 25 => 0x168b
  | 26 => 0x168e
  | 27 => 0x10a
  | 28 => 0x10b
  | 29 => 0x10e
  | 30 => 0xa0a
  | 31 => 0xa0b
  | 32 => 0xa0e
  | 33 => 0x130a
  | 34 => 0x130b
  | 35 => 0x130e
  | 36 => 0x180a
  | 37 => 0x180b
  | 38 => 0x180e
  | 39 => 0xa4a
  | 40 => 0xa4b
  | 41 => 0x134a
  | 42 => 0x134b
  | 43 => 0xb0e
  | 44 => 0xb4b
  | 45 => 0xb4e
  | 46 => 0x16cb
  | 47 => 0x16ce
  | 48 => 0xb8b
  | 49 => 0xb8e
  | 50 => 0x184b
  | 51 => 0x184e
  | 52 => 0xbcb
  | 53 => 0xcca
  | 54 => 0xcce
  | 55 => 0x170a
  | 56 => 0x170e
  | 57 => 0xd0a
  | 58 => 0xd0e
  | 59 => 0x188a
  | 60 => 0x188e
  | 61 => 0xd4a
  | 62 => 0x58a
  | 63 => 0x58b
  | 64 => 0x58e
  | 65 => 0xe8a
  | 66 => 0xe8b
  | 67 => 0xe8e
  | 68 => 0x178a
  | 69 => 0x178b
  | 70 => 0x178e
  | 71 => 0x18ca
  | 72 => 0x18cb
  | 73 => 0x18ce
  | 74 => 0xeca
  | 75 => 0xecb
  | 76 => 0x17ca
  | 77 => 0x17cb
  | 78 => 0x104a
  | 79 => 0x104b
  | 80 => 0x194a
  | 81 => 0x194b
  | 82 => 0x8a
  | 83 => 0xb89
  | 84 => 0x150a
  | 85 => 0x14a
  | 86 => 0x2c9
  | 87 => 0x198a
  | 88 => 0x14c9
  | 89 => 0x4b
  | 90 => 0xd49
  | 91 => 0x17c9
  | 92 => 0x138b
  | 93 => 0x409
  | 94 => 0x1609
  | 95 => 0x198b
  | 96 => 0x1849
  | 97 => 0xccd
  | 98 => 0x170d
  | 99 => 0x1789
  | 100 => 0x589
  | 101 => 0x5c9
  | 102 => 0x138e
  | 103 => 0x150e
  | 104 => 0x1a09
  | 105 => 0x3ca
  | 106 => 0x24b
  | 107 => 0x15ca
  | 108 => 0x144b
  | 109 => 0x160a
  | 110 => 0x148b
  | 111 => 0x1a0a
  | 112 => 0x164a
  | 113 => 0x19cb
  | 114 => 0x14cb
  | 115 => 0x5ca
  | 116 => 0x1a4a
  | 117 => 0x40a
  | 118 => 0x1a8a
  | 119 => 0x28b
  | 120 => 0x154e
  | 121 => 0x140e
  | 122 => 0x24e
  | 123 => 0x144e
  | 124 => 0x148e
  | 125 => 0x5cb
  | 126 => 0x1a4b
  | 127 => 0x1a8b
  | 128 => 0x3ce
  | 129 => 0x15ce
  | 130 => 0x160e
  | 131 => 0x15812
  | 132 => 0x11693
  | 133 => 0x199353
  | 134 => 0x5c591
  | 135 => 0x240d3
  | 136 => 0x5c0d3
  | 137 => 0x256d3
  | 138 => 0x19d4d3
  | 139 => 0x1a57d2
  | 140 => 0x5c253
  | 141 => 0x1a9952
  | 142 => 0x1a9052
  | 143 => 0x252d3
  | 144 => 0x5d2d3
  | 145 => 0x25793
  | 146 => 0x24e93
  | 147 => 0x5d6d3
  | 148 => 0x257d3
  | 149 => 0x25a53
  | 150 => 0x245d3
  | 151 => 0x17c253
  | 152 => 0x17d6d3
  | 153 => 0x5d453
  | 154 => 0x5d793
  | 155 => 0x5ce93
  | 156 => 0x1a57d3
  | 157 => 0x1a9953
  | 158 => 0x5d7d3
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2640
  | 6 => 7353
  | 5 => 1965
  | 4 => 8
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (108240+((h/880+packedAt gbK7 (97680+(h % 880)*12) 12) % 3485)*13) 13
  | 6 => packedAt gbK6 (387258+((h/2451+packedAt gbK6 (352944+(h % 2451)*14) 14) % 12917)*14) 14
  | 5 => packedAt gbK5 (123795+((h/655+packedAt gbK5 (115935+(h % 655)*12) 12) % 2853)*12) 12
  | 4 => packedAt gbK4 (570+((h/2+packedAt gbK4 (560+(h % 2)*5) 5) % 17)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc1f00fffe07fffffc0ffe00027dc79d1cfe7c
  | 1 => 0xfe000f81ff83f007fffffff1db278e21333ff
  | 2 => 0xffffff001fffc0007ff03fffe1c380ffe3c38f
  | 3 => 0xfffffffe00000007fffc000fe03ff03fc03f0
  | 4 => 0xfffffffffffffff80000000fffc0003fffc00
  | 5 => 0xf00000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x54030418a60151471c8a72060014c38d04563c
  | 1 => 0x8a0106a0ac83a09251ca4aa0cb058a21130d5
  | 2 => 0x654d6500951580124aa219546143805562c30a
  | 3 => 0x4e76b6b6c041082473c71018b603ad03bc03e0
  | 4 => 0xb98d8c719e62cb801040060dfe80002dba800
  | 5 => 0x8000e004018430c002082180fbff76f8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37005
namespace PEqualNP.Outside.L_meta_37005
open PEqualNP.Outside.L_meta_37005.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
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
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 64 := (concat bs5_4_0 bs5_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 40 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 8 := bgb_4_0
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
theorem bgb_5_1952 : Interval gbAtlas 5 1952 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1965 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 bgb_5_576)) (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 bgb_5_704))) (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)) (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960))))) (concat (concat (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184))) (concat (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696))) (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 bgb_5_1952))))))
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
theorem bgb_6_7328 : Interval gbAtlas 6 7328 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7353 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648))))))) (concat (concat (concat (concat (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544))))) (concat (concat (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 bgb_6_5216))) (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 bgb_6_5472)))))) (concat (concat (concat (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696))) (concat (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 bgb_6_5920)))) (concat (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144))) (concat (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))) (concat (concat (concat (concat bgb_6_6432 (concat bgb_6_6464 bgb_6_6496)) (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624))) (concat (concat bgb_6_6656 (concat bgb_6_6688 bgb_6_6720)) (concat (concat bgb_6_6752 bgb_6_6784) (concat bgb_6_6816 bgb_6_6848)))) (concat (concat (concat bgb_6_6880 (concat bgb_6_6912 bgb_6_6944)) (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072))) (concat (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200)) (concat (concat bgb_6_7232 bgb_6_7264) (concat bgb_6_7296 bgb_6_7328))))))))
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
theorem bgb_7_2624 : Interval gbAtlas 7 2624 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2640 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 (concat bgb_7_1824 bgb_7_1856)) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952))))) (concat (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112))) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))) (concat (concat (concat bgb_7_2304 bgb_7_2336) (concat bgb_7_2368 (concat bgb_7_2400 bgb_7_2432))) (concat (concat bgb_7_2464 (concat bgb_7_2496 bgb_7_2528)) (concat bgb_7_2560 (concat bgb_7_2592 bgb_7_2624)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0feeaeee0faeac8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809440 * 2 ^ 32 + 4209690816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37005.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.and,[0,4]⟩,⟨.or,[0,2]⟩,⟨.or,[3,7]⟩,⟨.or,[0,1]⟩,⟨.and,[5,10]⟩,⟨.and,[2,10]⟩,⟨.or,[9,12]⟩,⟨.and,[6,8]⟩,⟨.or,[11,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209690816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209690816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37005

open PEqualNP.Outside.L_meta_37005 in
theorem PEqualNP.Outside.L_meta_37005 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4209690816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4209690816) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
