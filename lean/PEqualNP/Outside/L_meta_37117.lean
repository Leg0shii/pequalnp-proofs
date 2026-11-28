import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37117.Model
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


end PEqualNP.Outside.L_meta_37117.Model

namespace PEqualNP.Outside.L_meta_37117
open PEqualNP.Outside.L_meta_37117.Model
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

end PEqualNP.Outside.L_meta_37117

namespace PEqualNP.Outside.L_meta_37117
open PEqualNP.Outside.L_meta_37117.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083f680107f90020fea0041fc40083f080107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c437ca9884f95310feaa6217d54c437aa9884f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087ed0210ff20421fd40843f881087e10210ff98421fe30843f461087f4c210fc98421fc30843fe41087f88210fd10421fd20843f241087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21fd41443f882887fcc510ff18a21fd31443f862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443f680887f90110fea0221fc40443f080887fcc110ff18221fa30443fa60887e4c110fe18221ff20443fc40887e88110fe90221f920443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8087f55010beaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd414c3f882987fcc530ff18a61fd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8187f55030beaa061fc540c2f8a8185f94c30ffa1861fe430c3fa86187f10c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861fd510c2faa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907ed0320ff20641fd40c83f881907e10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241bf544827ea8907f95120bf2a241fd54482faa8907f15120be2a241bc5448278a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20ff21a41fd43483f886907fd0920ff21241fd42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841f651082eca2107f54420bea8841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff98
  | 2 => 0x3fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81be43903fa87207f10e40de21c81ff52903fca5205f94a40fea94817d52903f8a5207fd0a40ff21481be42903fa85207f10a40de21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640dfa0c81fe41903fa83206f50640fe20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a07f94d40fea9a81fc53502f8a6a07fd0d40ff21a81fd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff425037e84a07f90940fea1281bd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881fe431037c86207f50c40fe21881bc43103fea4207f94840bf29081fd52102faa4207f14840ffa1081fe421037c84207f50840fe21081bc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881bf41103fc82207f50440dea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661df32cc3fc65987f4cb30ee99661fc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3fa63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8986fd51309faa261fe544c2fca8987f55130beaa261fc544c2f8a8986f151309e2a261ff434c3fc86987f50d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61f
  | 3 => 0xa098ffd5031bfaa063fe540c6fca818ef950319f2a063fd540c6faa818ef550319eaa063fc540c6f8a818df94c31ffa1863df430c7fc8618ff50c31fe21863dc430c7fea418ff94831bf29063ee520c6dca418ff54831bea9063ed520c6daa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018fe94031bd28063fd500c6faa018fe54031bca8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21f719643fd32c87da6590ff0cb21ffa0e43fe41c87fa8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490fb8c921fe99243ed32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043be540867ca810ff55021beaa043bd540867aa810ff15021be2a043ff53086fea610ff94c21bf29843de53086bca610ff54c21bea9843dd53086baa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fa50086f4a010ff54021bea8043f950086f2a010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d
  | 4 => 0x7fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa1e83bf43d07fc87a0ff50f41dea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683bf42d07fc85a0ff50b41dea1683fc42d07fe65a0ff8cb41fe99683fc32d07fea1a0ff94341bf28683fd50d06faa1a0ff14341beaa483ff53907fca720df94e41fea9c837d53907f8a720ffd0e41ff21c83be43907fa8720ff10e41de21c83ff52907fca520df94a41fea94837d52907f8a520ffd0a41ff21483fd42907f88520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907f4a120de94241fea84837d50907f2a120de54241fe28483ff53506fea6a0f7d4d41afa9a83fe53507faa6a0ff14d41be29a83dc53506b8a6a0ffd0d41dfa1a83fe43507fa86a0ef50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941dfa1283fe42507fa84a0ef50941fe21283ff32507fc64a0ff4c941fe19283ff41507ee82a0ff90541df20a83ff50506fea0a0ff94141fea8283fc50506f8a0a0df95041ffa9883fe53106fca620ff54c41bea9883fc53107fe8620ff90c41df21883fd43107f88620ef10c41ffa9083fe52106fca420ff54841bea9083fc52107fe8420ff90841fea1083fc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598f7ccb31ff19663fd32cc7ba6598ff0cb31ffa0e63fe41cc7fa8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31efa1c63fe438c7fa8718ff10e31ee21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff19463fd328c7f86518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898efd51319faa263fe544c6fca898ff55131beaa263fc544c6f8a898ef151319e2a263ff434c7fc8698ff50d31fe21a63ff524c6fea498ff94931fea9263fc524c6f8a498ffd0931ff21263fd424c7f88498ffcc931ef99263fe324c7fa6498f74c931fe19263ff414c7fc8298ff50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8
  | 5 => 0xa43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa9087fe5210efca421ff54843bea9087fc5210ffea221ff94443bf28887fd5110efaa221ff14443ffa8087fe5010efca021ff54043bea8087fc5010ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85fe43d0b7c87a17f50f42fe21e85bc43d0bfea3a17f94742bf28e85fd51d0afaa3a17f14742ffa8685fe50d0afca1a17f54342bea8685fc50d0afaa9217fd4e42ff29c857e5390bbca7215794e42fea9c857d5390bbaa7215754e42fe29c85ff4390bfc87217f50e42fe21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42ff21a85be4350bfa86a17f10d42de21a85ff4250bde84a17f90942df21285ff5150afea2a17f94542fea8a85fc5150af8a2a17fd4142bfa8285fb5050af6a0a17f94142fea8285fc5050af8a0a17e14142bc282857e5410bfea6217f94c42bf29885fd5310afaa6217f14c42ffa1885fe4310bfa86217f10c42bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65df43ccbfc87997f50f32fe21e65dc43ccbfe85997f90b32fea1665fc42ccbfea3997f94732bf28e65fd51ccafaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccbfea9195fd5232ff2a4657e548cb7ca9194f95232feaa4657d548cb7aa9194f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbfa85197f10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32efa1a65fe434cbfa86997f10d32ee21a65ff424cbfc84997f50932fe21265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf88419
  | 6 => 0x9251ac748b40001964ea16604a8f8e1c9420a2000000d8c00200200000000000000101400100000400f00100200100000100301700500400800000400102d00000800100800100d00000801000400b00000e00100e00800000300700000000900400000400800400700000500500f00700400000200100b00100700000700700200401600000000a00000c00200101200001200400102a00000a00700100000000000500200d01400600900300000000700000201000100400500000701300b00100100000000900202d00f04400501600100000a01400300200d00900700000100100c00300f01d00800300400300900300002400100000301500000400100000900000000800000400d02200000000100100000000101501100000200200300000300100100300900200700100000200100000901400000200201301200201200600300000900000000501900d00000300700000300000000002600b00400000600100402100000200000400c00f00700400000500000601c00800900100000100500600700000000200000000100400600100000100700000a00100001300100000700200100000f00200102e00900000600b00a00900500000000900600000000000501f00c00001600100900d03000600600800101500200700100700600100000f00000a00e00000000000400d00600000700400200701600500200300000500f01000000500000000001200300000100000300000001700000000000200000201f00a00200200300500001700200000200400201100e00500200000600f00200a00000500800000500200400300000300801300300100100000000000000b00100000600000f00000200101400300000100200700300400000300400000001000102100100000e00000400200500000400200001800800100101601500a01300000302901100300100900000100000700200000701300200200400200400700000000700200b00000100a00500000900900700b00100601b00c00900300300d00000700400200200200001500e00800000f01700800000000700800101800000300000100000f00001201800000401700100a00200100200000000100000300c00801400600400e00300c01400000e00001c00000a00000100000d00001400300500000200503100100800600000200501700401b00000a00100500000100000000000200500600200200300200700200100000200100000000e00000700000000900400000d01200200200700000500100000300001c02300300700000100000000001800e001007002007000ffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4
  | 7 => 0xc450ba800064a0d249467403a000c9a00000000a2a40000001b02645caaf44683f2b9832000057c0763163500008720000006d842200090e2822e09be00000000092812ca107d2d8400059a000000b9a0007ce000000000b8c0000000006065b04ee0000b8a3aa54d96232000000780038d707ba4669a4b1ed2690ac0e692c14c3ce386265ea046de275c68a8182147886fe37a562de809400cd683c2192926e185202e4652000000d9a000000608000598510b522bc5e04165e2008a481cc934d8e00028ec0656c0007c6b46d08d643c80000fcbea0006de0f6954c9497e7140ba00014ecd6a22814a38cda7e40444282c8000ca8790a4658a0548ce84e0e6bf220485adb80000a4bc61d29eabda9328887f89ac524b6a7fcd4c000694000436dbedb456a2f4bb60005c21542aa0004bcd6e00000032e000970690bc8bf41a0cce35a0c0bb86280564268ca6c8b06c46000630d7c72a53831000034c96aa246789b0a44000a7c2d84d6e5c7a09e80005063220e47b20005b289acfa10ad66aaa8964d4daca1a1d0d029f60005344ba2fc8fc6722622cc6dcd14e3e85e70601e09a4fab5a274a6a6566b87105bca0ecb01523ac1b2a6c82c7285f4e1a3a4dba0003cc996c48516d06550d8a5da418ce01300eeaae7400d01be000cf42ce00035e0000009f40000005b800081e000dd494633a000b40e5e000260000142cc086e3bc000000d2e5ba4d2000cbab0e0001a85fa0e0a0a7322800000006bc0ae0000000000002787f20004408e2d8200073eb725d87ca000000e44d88000000120000880ddc00000009c000aec00043000000000000001000040800065abdc0001708d4c988b25d6778000000396e3035480427e000bbe858000000000000b582e60029d8000a803d02680fe7c2ad4dd64e88ae09e5729ba41cccc5f8caed12000ba6786aa02f6ac63866d09aad98a060280000001984c400048862c4a2b8400000074c00001a2ec7be5e8c40444000c64d78000a421e85d4644ae8ac07926f0000da6000000e5a0007986a0b28074650d8052675a29e16c0000005a42c6dec7da000bc09c8004b023c62be8ba8f0000000000406cec24a73878e9b461c000000000682000244e348fed36c22a2e3ea52c0000c2000a8a55848e0001f4000e0e7fa0000009d0e3a82002c398000e203f82ea000364ad8000000ab443a000d52000486a56000ae4078e48c68000574b4c8606409760002d0a74000cde0c80002b8e323aeb0a1881fec6ce66b5c0009002dc99400000000046c0000007960001740003a6e08000000d604d018285c8d6000910b1a752866cc8dc6000a8c52a9a8000a9aac2b3edce4aa70ec5e5824105c896221c9cc230068660dd81d8022c2a62449cc7cafe90c00020e1e2000000acc75871800095e15a8ac50e3886be53e3d60c6b
  | 8 => 0x39caca8b661e9242fe0b6e40498d3442c000000e1047a0000bc000000000e2a0a6670238000982000698ad600043c000000000a9e38a00082860e0006a4000cd41ec9d400078cbe4c040002b49e20003e8c620000000001e6e00000baa034522b5e592000000000000bae23a000000aa6000b8a16ad62318c90ca2536e58d1800092085011a0182dacb2d1e7d4720c2080e2b064602445cdc87bcdfa81c0000be000bf6dd08de5ac622172d0030ad92dc00004b2c2ec78688a205f67f0590e2e2188e49e648cb22dea3740000008566aa000b6e0007d07726b6d4a17ccf827200e3fc1b65aa0000004e46f2564b32518000d0a0002fa4b839200025819ac32b868c4bca0000003eebf88d2136ade7ace5256ed0e94c000d20ab07c8726de00b0b143b054ab380f8084470ba05a8a2a088826c58000af800033000000000000049200000036e000be25006204cc384768684000b0cbd6000b1c040000da025e0001162760001f64b60000da69ca94b3688a2e86baca0c88000026000000000000000bd4324c50000b825040008dc000842138e621dc6da16040204e9680009980e872453a7e692200087a42076e42a000c72d16b48228da8c844a879439005249e66acaa96e55293c3e018a680d5633c3b639e224a0826c57825cad0528abcac47ea6b0a68b046124829d217680cbd0000d24a860001c23f610cb2c21eb9c3a800023c70805c000000000c7e000000000b9630c73a000a508a8000bba7f40c4000454df633200083a55c342c7624c0000006e80008e6000cf623600000046ad3e414bac8a400097cab87aee0a122200270bbc8626344c2d9eada8c280ab12c6e06469a6b400000054c6f481a0f0a047cc9e4cbc0008462a83360001841c4400d400001a6bb0958e24a1e7642d4c569fe2f89c07d600036c376cdccd800061414850c73617a000c0200000003c3e4000844000914132dde4f8048378a62c2c4ded5e0dc4248162b68c00000000004807c437c0006c00001ca92a93608e00047c5a6000adc00074a6ec0008d0d94c829bcd2287cb18676d742128903b2222580000d587c000000000068ecfe36a14c0000000005125fecfc71238edfc9a2668af0a3c2881006ac000cd0a4ae563821acc10000dee000daa0008cc000da27dc10e952000000cc483ca90062128000000bee0000003dea120003020a8000a3618ce60df2b80c0c0001da38055adc4746870cd24f063c756c36666b6c9569de584aa20006ea43e2c25ee000bce15c1babf0e04000d38848e26a78452000000000c6675e9ec1eabd267eb249f8b667a407200000020a0000003dc000000000a60000b7e00054200016e5764be15ece40001fa13c0003f45f24d81ae0003aa742290afc00019e59cbcc0000aa7f697a72c0001f200000012a8547a2784d86c2400000067
  | 9 => 0xfc41225ace8ba275000019046281045e570c1aa160d8000000a8e0000000000000000005c0d3c00058e144000c26000dcc00000070c2ca00063a824af291ad2a4dcda469e10486c0980000000007b69f0878dc2d1c3607345a0c9c6fa00055e000658000c4c3ce0427485fc000000000000d5440478206e9dad7e12e40e06a0000006d4618e14d4e7028c65be4e21b893000000097800059ea3014096084cce24c628658c4840f2aa413a00088e0000009a60000000000000000000002f0000000cf20000008da000000ace4a065c432370a586cc442b60000a4061600027a6e43d2cb6766a76000884000000000a2cc4496400042ea283a000057e4fe000000000000000ca400000038cb424ca00035226a79c2ee77498692e000834000b788f6a7a496b640609c2000000530502000d3a24000063266c446066944346604000306b8e1aa566bb200000000002a00000000000000000062ad44642c169f2852d1ad2895a9b81246fc64c0cc2a0700b903e2000de4802e0279a0000004ce00000089ce4a47468c3482c05de00094a52e00008a53c5ce7a826e1c03041c6a5e3c435873c86a546106cf0000a6418e1b43fe8089a045a02e2a61120001460004560009928a02424783e69800000000000000ca1346a2000000000000db600075482e66ec960007e827c7a68b80820864720d6c385b40900000000000001185cc48a012000c3e54477043800000008c8be8768686967ec33400032aa7ece6d324ec9661c8974000d7ae12c92e16db0362a143b8080db2000b5003e806000000b080006ca2d600092c000000cc20d44e6000a1c4f250a00014ad423388e8ae6000000b449b6000cee9844ac000760ca6c4e368050704000e544f6e3c00071a020cb431a22c00000000007c000874908abea5c0000ea000b686c6ad2a82aba01493ebdea0cdbc5ec65e000d5ca3e0000005c61bc8bc000000000514216292000c706e22020a09e025200005a00013e8aa0000000004b03d4a9cd104604c87d833e0ac186000dd2a523a26640000006f877a0b2000016366c605940001e471e000e649508300000005ae000000d3000029c9eee28000ddac30e426e03da16800034a4480000000009900008a6000b2a2060005f00005a29dc0000000003560006a62564c0000000000c0800000000044e2a2326912c1e3440004580002de000b56be6000000000df06ce000a00a9272eba499e2d2662554d6a29820cbeca72234194000cb882200000098e4e074eb3a0001a200000076c03060ac420004a4c8c5c43d800099cb62c4aaac5e61027ee78ab4ebfa1ce654b10096bd826606cb7a51e64ed906aea343ba07063e1505e400088c00028a8eaaea8926f6036110000b00bfe0003ca91ecead0c7de44c0002babfc99a0000002e20000008d80003b4246904000
  | 10 => 0xb88000250b302c4de66d68b08ec23e05e32cc8e0fa83644ab3c864c1c31e1a4cac938126e36b7440cb9ea66d501780b477e6c400058688200000041a000df8000ab2b4ad760009d64ae000000000c54d2c918916e2cd5a6a89aee22a4cc6a1fcbe8dfeb2e68605883e108a0271c812092000b2034eb3430e29ae0c114000638a840001808f2b5489400089e31cc003fa7b48980001ee98a0000009b29c60007e2c0aaa8000032b70568596d4696c254a1821070a6c222040ac80c280000000e2000e4e00000000091c6027b00004f49ce61a76200097246e54e0004a69fa8c8cbe8a2cca29600024e5b6000730000000c9e57a000000dca000340a88a5a41e0006b2000000c7a90200000037e00039a60c4da00021a00007e0003be00098c000ac8bb4ae23141d6e1e0de838744000b1647649ab766e6e4c76a82aa6e294000ab62489067fe7165dc11c04c15877c948000d9caf6b7c0ec00000087ed04636e069ca5d24347b8c5c328bc220817e6d207ad482f228467a19c1d400093aa26ae030895c8fa840a981f86100060000003ec28c560df400000084abe01e0000156c349880008ee22e9c41f0bc45080003c02b27760008f48e000054000094e000a4e000c8a5d07aa4b472280016411e3f000000051c372c5a79e556a963944fcc520f401c47e6eed6ce46532e50490c12cc6d72648a702ae000548300000c1800000000062e1de2ac58822ab94b2635cc86c3a000312dae940464aeeafa6008327e08860cea321622269
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x6320427c658c810af99232042bd648c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c8109f992510433e64944108f992510427d6494410cf592510423d64944109f98e510427d63944109f98a510427d62944109f597410433f54d0410cf153410427f65904109f596410433e5490410cf55241042fa6090410be582410427f6550410cfd51410433c5450410b7d8d41042dc63504109fd94410427d6510410cf950410433d5410410be98041042f960104109f597310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c410afd9131042bc644c4109fd94310427d650c410af99031042bd640c410d794c310435d530c410bb98831042ed620c410be98031042f9600c4109f597210427f65884109f596210436e5288410db54a21043765188410be98221042f960884109fd95210437651484109fd94210427d6508410af99021042bd6408410b798c21042dd6308410db948210436d5208410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f586500427d65d0010de943400427f65900109f596400433e5490010cf55240042f66190010bd586400427f65500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f56110010de940400427d65cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010de942300427f654c010afd9130042bc644c010de941300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010de942200427f6548010afd9120042bc6448010de941200427f65080109f994200427d65080109f19420042be6408010af59020042de6308010b758c200436e5208010db54820042f66108010bd58420043e92008010af99310042bd64c4010dd59710043b664c4010ed593100437752c4010dd54b10042f56184010dd94610042f96584010de59610042796584010de95210043785484010ded4e10043795384010ded4a10043795284010be586100437a5184010fc946100427f6544010bdd95100437765440109dd9510043775244010dd54910042f76044010dd94110043f24044010fc50110043f33044010fc0c110043f22044010fc48110042fb6544010ded95100427b6544010de95110043785444010ded4d10043795344010ded4910043795244010bed8510043f36144010de94510043f25144010fc90510043f14144010fccc510043f03144010fc88510043f12144010
  | 1 => 0x43f13084110fc88210443f120841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109e983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a53042bf6454c10af191530427f6454c10cfd91530423f6454c109f191530433c6454c108f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c109fd96430427e6590c109f596430427c6590c10cfd52430433c5490c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c109fd94430427e6510c109f594430427c6510c10cfd50430433c5410c109f993520427d64d48109f98f520427d63d48109f987520437661d48109f983520437a60d48109f596520436f52948109f992520427d64948109f98e520427d63948109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f58152042be6414810af59052042de6314810b758c520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109f984520437661148109d984520427e6014810de980520427a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d08109fd96420427e65908109f596420427c6590810b798e42042dd6390810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bed8142042f860508109fd94420427e65108109f594420427c65108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f59
  | 2 => 0x5288510dd14a21443f36088510bd98221443f060885109f195214436f5248510db14921442fb6048510be181214437465485109d19521443e76248510f9d4921443765248510dd14921443e45248510f98c921443e53248510fcd8121442f46048510fc181214427e6508510af99021442bd6408510b798c21442dd6308510bd98421442fa60085109f997404433f54d0110cf15340442f661d0110bd58740442fa65d0110de997404427a65d0110ded5340443bb54d0110de55340443b854d0110be58f40442f962d0110de94b404437852d0110eed0b40443b942d0110be98740443f261d0110bc98740443f161d0110fc88740443f121d01109f996404433e5490110cf55240442fa60901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd185404427e6510110cf950404433d5410110ee50040442fa6510110de99440442fa6410110ee990404437b5410110ee95040443795410110ee55040442f96310110ee90c40443b84310110be588404437a5210110de14840443ba4210110ee10840442fa6110110eed0440443b94110110fc88440443f121101109f997304435f53cc110d714f30442f661cc110bd587304427e658c110be996304437a658c110be99230442f8648c110be58e304437a538c110de14e30442f9628c110be98630443f2218c110fc486304427f654c1109f595304427c654c110afd9130442bc644c110d7d4d304435c534c110bdd8530442f4614c110be1953044378654c1109e19530443bb644c110be99130442f8644c110ee19130442b8644c110f6d8d30443db534c110de94d3044378534c110f614d30442fb624c110f6cc930443d9324c110fcd8530442f8614c110fc18530442f0614c110fc88530443f1214c1109f99430442fa600c1109f997204436f52c8110db14b20442f661c8110bd587204427e6588110be996204437a6588110be99220442f86488110bed8e20442f96388110be58a204437a5288110de14a20443f36188110be98620443f06188110fc88620443f121881109fd95204427d65481109f19520442bf6448110af191204436f5248110db14920442f76148110bd18520442f86548110de19520442786548110eed9120442fa6448110be19120443b86448110ae19120442fb6348110be58d20443eb6248110fad49204437a5248110de14920443e85248110da14920443f36148110be18520443f06148110fc88520443f121481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420442fa6008110af99310442bd64c4110be99310443ba64c4110ae99310443b964c4110be19310442fb63c4110be58f10442fb62c4110be58b10443f221c4110fc48710442f76284110bd58a10443f35084110fcd0210443f04084110fc8c2104
  | 3 => 0xd10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10be98243442f96090d109fd95434427e6550d109f595434427c6550d10bdd8543442f46150d10bed8143442f86050d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910af99052442bd6414910b798c52442dd6314910db548524427e6414910cf990524423e64149109f590524433d64149108f590524427e6314910d798c524425e63149109f58c524435d63149109758c524436e62149109f984524437561149109f184524427e6014910de580524427c60149109fd97424427e65d09109f597424427c65d0910cf953424433d54d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910b798e42442dd6390910bd98642442f56190910be98242442f960909109fd95424427e65509109f595424427c6550910cf951424433d5450910bed8142442f860509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910d794f324435d53cc910dbd4b324436c52cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910af99232442bd648c910d7d4e324435c538c910bd98632442f5618c910be98232442f9608c9109fd95324427e654c9109f595324427c654c910d794d324435d534c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414427e6590510be982414427c6550510cfd51414433c5450510b7d8d41442dc6350510bed8141442f860505109f99441443b541105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f19531442bf644c510af191314435f534c510d714d31442fb604c510be181314427e650c510af99031442bd640c510bb98831442ed620c510f54c431442fa600c5109f997214436f52c8510db14b21442fa60c8510be583214427e6588510bd99621443766588510bd58a2144376
  | 4 => 0xd98440842f56110210ee50040842f96510210de59440843ba6410210ded5040843ba5410210de55040843b95410210be58c40843ba4310210ee10c40842f96210210de94840843785210210ee90840843b84210210be98440843f26110210fc58440843bb4110210ee504408435e538c210d754e30842f6618c210bd58630842f9658c210de59630842fa648c210be192308437a538c210f694e30843d9538c210de14e30842f9628c210be98630843f2618c210fc58630842bf644c210af19130842fb654c210ded9530843bb644c210be99130842f8644c210ee19130842b8644c210f6d8d308437a534c210de14d30842fb624c210f6cc930843d9324c210be185308435e530c210d754c30842f6610c210bd584308436e5288210db54a20842f66188210bd58620842f96588210de59620842fa6488210be19220842fb6388210be58e208437a5288210fa94a20843e95288210de14a20842fa6188210fc98620843f16188210afd9120842bc6448210bed95208437b6548210eed9120842fa6448210be19120843b86448210ae19120842fb6348210be58d20843eb6248210de94920843785248210be18520842be6408210af59020842de6308210b758c208436e5208210db54820842f66108210bd58420842be64c4210af59310842f565c4210dd59710843b664c4210ed593108437752c4210dd54b10842f965c4210de59710842fa64c4210ee99310842ba64c4210ee59310842f864c4210bed8f10842f963c4210bed8b10842f962c42109f98f544427d63d51109f98b544427d62d5110de583544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f180544427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d10de580534427c6014d109fd97434427e65d0d109f597434427c65d0
  | 5 => 0x548427d6215210dd584548437a6015210af99353842bd64d4e109f993538433e64d4e108f993538427d64d4e10cf593538423d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538437a6094e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438435e53d0e10d754f438427f6590e109f996438427d6590e109f196438433e5490e10cf55243842fa6090e10be582438427f6550e109f995438427d6550e109f19543842fb6050e10be181438427f6510e109f994438427d6510e109f194438433e5410e10cf550438435e5310e10d754c43842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10de982528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a109fd96428427e6590a109f596428427c6590a10b798e42842dd6390a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10bed8142842f86050a109fd94428427e6510a109f594428427c6510a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10af99232842bd648ca10be98232842f9608ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610be582418433e5450610cf55141842df6350610b718d41842fb6050610be181418435e53cc610d754f31842fa60cc610be58331842bf644c610af191318435e534c610d754d31842fb604c610be18131842be640c610af59031842ee620c610bb58831842f9600c610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610af99021842bd6408610b798c21842dd6308610be58021842f965d0210de597408437b54d0210de55340842f963d0210be58b408437a52d0210de14b40843bb42d0210ee50b40842fa61d0210cf952408433d5490210bd98640842f56190210cf950408433d5410210b
  | 6 => 0x27e6550b109f59542c427c6550b10cf95142c433d5450b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10cf95332c433d54ccb10d794f32c435d53ccb109fd9632c427e658cb109f59632c427c658cb10af99232c42bd648cb10cf95232c433d548cb10db94a32c436d528cb10bd98632c42f5618cb109fd9532c427e654cb109f59532c427c654cb10cf95132c433d544cb10d794d32c435d534cb10db94932c436d524cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10cf95032c433d540cb10bd98432c42f5610cb10cf95341c433d54d0710cf95241c433d5490710be98241c42f96090710cf95141c433d5450710b7d8d41c42dc6350710cf95041c433d5410710ed50441c42fa6010710be58041c433e54cc710cf55331c433e548c710cf55231c435e538c710d754e31c42fa608c710be58231c42bf644c710af19131c433e544c710cf55131c42be640c710af59031c433e540c710cf55031c435e530c710d754c31c42ee620c710bb58831c43d5310c710be98031c42f9600c710cf95321c433d54c8710cf95221c433d5488710db94a21c436d5288710be98221c42f96088710dd59621c43b65488710ed55221c43765288710f994a21c43e55288710dd14a21c42f66088710fc98221c43f16088710cf95121c433d5448710bdd9521c43776548710ed95121c43b55448710f9d8921c43765248710dd14921c43e63248710f94c921c42f46048710af99021c42bd6408710cf95021c433d5408710b798c21c42dd6308710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cf95240c433d5490310cf95140c433d5450310bdd8540c42f46150310cf95040c433d5410310cf95330c433d54cc310d794f30c435d53cc310bd98730c42f561cc310cf95230c433d548c310afd9130c42bc644c310cf95130c433d544c310d794d30c435d534c310bdd8530c42f4614c310cf95030c433d540c310cf95320c433d54c8310db94b20c436d52c8310bd98720c42f561c8310cf95220c433d5488310afd9120c42bc6448310cf95120c433d5448310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310cf95020c433d5408310b798c20c42dd6308310bd98420c42f56108310fa48020c42de63d5210b758f548427e63d5210d798f548425e63d52109f58f548435d63d52109758f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f18954843786055210cf550548433e64152109f98c548427d63152109f988
  | 7 => 0x448020ee19120082b86448020ee95120083b95448020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fa90920083e94248020fa8c920083e93248020fc94520083795148020fc54520083715148020fa88520083e821480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f6395310cf98e54c433d6395310cf18e54c433f6295310cf98a54c433d6295310cf18a54c433e6195310cf18654c433f6095310cf58254c433f64553109fd8d54c427c63553109fd8954c427c6255310cfd9554c433f6355310cf98d54c433d6355310cf18d54c433f6255310cf98954c433d6255310cf18954c433e6155310cf18554c433f6055310cf58154c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c433e54d4f10cf55353c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f109f58b53c437661d4f10de58353c433e5494f10cf55253c435f5394f109f99253c427d6494f109f98a53c427d6294f10cf95153c433d5454f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c42be6414f10af59053c433e5414f10cf55053c435d5314f10bb98853c42ed6214f109f99053c433e6414f108f99053c427d6414f10cf59053c423d6414f10d798c53c427e6214f10db98853c426e6214f109f58853c436d6214f109b58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c433e54d0f10cf55343c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c427f6550f109f99543c427d6550f109f19543c433e5450f10cf55143c42f76150f10bd18543c427f6510f109f99443c427d6510f109f19443c433e5410f10cf55043c42f66110f10bd58443c42be64d4b10af59352c433e54d4b10cf55352c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b109f58f52c437661d4b10de58352c433e5494b10cf55252c436f5294b109f99252c427d6494b109f98e52c427d6394b10dd98652c433e5454b10cf55152c427f6454b109f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10cf95052c433d5414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b10b798e42c42dd6390b10bd98642c42f56190b109fd9542c4
  | 8 => 0x20be98321082f960c84209f596210833e5488420cf552210835e5388420d754e210837551884209fd95210833e5448420cf551210835e5348420d754d21083765148420af99021082bd6408420cf950210833d5408420b798c21082dd6308420d794c210835d5308420dd94421083755108420be98021082f960084209f992500827d64940209f98e500827d63940209f597400833e54d0020cf553400835e53d0020d754f400837651d0020dd54740082f965d0020de597400837b54d0020ee953400837954d0020ee553400833954d0020f694f40083d953d0020be58b400837a52d0020eed0b40083b942d0020fc947400837951d0020fc547400837151d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020dd94640083755190020be982400827f6550020cf951400833d5450020d794d400835d5350020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020dd94440083755110020ee50040082f96510020de59440082796510020be99040083ba6410020ded5040083ba5410020de55040083b95410020f694c40083d95310020ee90c40083b84310020fa98840082f96210020fa58840082e96210020de94840083ba4210020ee10840083f25110020de54440083f15110020dc54440083bb4110020ee504400827d65cc020cf953300833d54cc020d794f300835d53cc020dd947300837551cc0209fd96300827d658c020cf952300833d548c020d794e300835d538c020bb98a30082ed628c020dd9463008375518c0209fd9530082bf644c020af191300833e544c020cf551300835e534c020d754d3008376514c020dd545300827f650c0209f994300827d650c0209f194300833e540c020cf550300835e530c020d754c30082ee620c020bb5883008376510c020dd544300833e54c8020cf553200835e53c8020d754f200837651c8020dd54720083ae54c8020eb55320083ce53c8020f354f20083e651c8020f954720083eb40c8020fa103200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620082fa6488020be19220083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020fc94620083795188020fc546200837151880209fd9520082bf6448020af191200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020ebd9120083ac6448020eb95120083ad5448020f394d20083cd5348020f994520083e55148020bbd81200836e5048020fa90120083e94048020fa8c120083e93048020bed95200837b65480209ed9520083bb6448020be99120082f86
  | 9 => 0x4c832082fa600c820be58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420ddd9251083766494420dd59251083746494420ddd8e51083766394420dd58e51083746394420ddd0e51083764394420dd50e51083744394420dd18a51083774294420dd90a51083754294420dd10a51083773294420dd8ca51083753294420dd0ca51083766094420dd182510833e5454420cf551510835e5354420d754d510827f64544209f191510827f63544209f18d51083776554420ddd5151083765454420ed95151083365454420dd55151083b55454420cd55151083745454420ddd4d51083765354420f594d51083565354420dd54d51083d55354420d554d51083745354420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf553410835e53d0420d754f410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd94641083755190420be98241082f960904209fd95410827d65504209f195410833e5450420cf55141082df6350420b718d410835e5350420d754d41082ef6250420bb18941083765150420dd54541082fb6050420be181410827f65104209f994410827d6510420cf950410833d5410420d794c410835d5310420dd944410837551104209fd97310827e65cc4209f597310833e54cc420cf553310835e53cc420d754f310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f19531082bf644c420af191310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420cf950310833d540c420d794c310835d530c420bb98831082ed620c420dd9443108375510c420be98031082f9600c420cf953210833d54c8420d794f210835d53c8420dd947210837551c84
  | 10 => 0x40836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c20d7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430835e53d0c20d754f430827f6590c209f996430827d6590c209f196430833e5490c20cf552430835e5390c20d754e43082ee6290c20bb58a43082fa6090c20be582430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082fb6050c20be181430827f6510c209f994430827d6510c209f194430833e5410c20cf550430835e5310c20d754c430827e64948209f592520827e63948209f58e520827d65d0820cf953420833d54d0820d794f420835d53d08209fd96420827d6590820cf952420833d5490820b798e42082dd6390820d794e420835d5390820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d42082fb60508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f320827f658c8209f59632082be648c820af592320833e548c820cf552320835e538c820d754e32082fa608c820be582320827f654c820cf951320833d544c820d794d320835d534c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820f3
  | 11 => 0x3f5490520cf15241482fa6090520be582414827f65505209f995414827c6550520cfd51414833c5450520b7d8d41482dc63505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841482fa6010520be580414827e65cc5209f597314827c65cc520cfd53314833c54cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e31482fa608c520be582314827f654c5209f995314827c654c520afd9131482bc644c520cfd51314833c544c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520cfd52214833c5488520ddd4621483745188520be98221482f96088520cfd51214833c5448520ddd4521483745148520bed8121482f860485209f99421482be6408520af590214833f5408520cf15021482de6308520b758c21482fa60085209f997404833f54d0120cf15340482ee62d0120bb58b404827e6590120cfd52404833c54901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb189404827e6510120cfd50404833c54101209f997304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b304827e658c120cfd52304833c548c1209fd95304827d654c1209f19530482bf644c120af191304833f544c120cf151304835f534c120d714d30482ef624c120bb189304827e650c120cfd50304833c540c120cfd53204833c54c8120eed53204837a54c8120de15320483b854c8120ce15320482f961c8120cfd52204833c5488120ebd5220483ac5488120fad4220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020ee182540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020de181540833f6555020ee181540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf18154083386055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f9885
  | 12 => 0xd5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd52544827e64951208f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de582544833f64551209fd8d544827c63551209fd89544836f62551209fd85544827c61551209fd81544837b60551209ed81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d6115120af994544833e65151208f994544833f6315120cf98c544833d6315120cf18c544833f6215120cf588544833f6115120cf984544833d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d209f993534827d64d4d209f987534827d61d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534833c5414d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20bb98843482ed6210d20be98043482f96010d209f997424833f54d0920cf15342482fa60d0920be583424827e6590920cfd52424833c5490920b798e42482dd63909209f195424833f5450920cf15142482fb6050920be181424827e6510920cfd50424833c54109209f997324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920af99232482bd648c920cfd52324833c548c9209f195324833f544c920cf151324835f534c920d714d32482fb604c920be181324827e650c920cfd50324833c540c920cfd53514833c54d45209f993514827d64d45209f98f514827d63d4520af99251482bd6494520cfd52514833c5494520ddd4651482bf6454520af191514833f5454520cf15151482df6354520b718d514833f5414520cf150514837551145209f990514827d64145209f98c514827d6314520de580514827e65d05209f597414827c65d0520cfd53414833c54d05209f996414827d65905209f19641483
  | 13 => 0x9f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f58653882bf6454e20af191538827f6454e20cfd91538823f6454e209f191538833c6454e208f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e209fd96438827e6590e209f596438827c6590e20cfd52438833c5490e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e209fd94438827e6510e209f594438827c6510e20cfd50438833c5410e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20cfd52428833c5490a20b798e42882dd6390a20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20d794f328835d53cca20be98332882f960cca20af99232882bd648ca20d794d328835d534ca20bed8132882f8604ca20f34c832882be6494620af592518837751946209f992518833e64946208f992518827d6494620cf592518823d64946209f98e518827d6394620de982518827f64546209f191518827f63546209f18d518837551146209fd97418827e65d06209f597418833f54d0620cf153418827f65906209f996418827d6590620be98241882f960906209fd95418827d65506209f195418833f5450620cf15141882df6350620b718d41882ef6250620bb189418827f65106209f994418827d6510620be98041882f960106209fd97318827e65cc6209f597318827f658c6209f996318827d658c620be98231882f9608c6209fd95318827d654c6209f19531882bf644c620af19131882ef624c620bb189318827f650c6209f994318827d650c620af99031882bd640c620bb98831882ed620c620be98031882f9600c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620af99021882bd6408620b798c21882dd6308620be580218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882ee6210220bb588408835f53cc220d714f308835e538c220d754e30882ee628c220bb58a30882bf644c220af191308835f534c220d714d308835e530c220d754c30882ee620c220bb58830882ed65c8220db59720882f965c8220de597208837a54c8220de15320882f961c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63
  | 14 => 0x9353c823e64d4f209f59353c833d64d4f208f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c835e53d0f20d754f43c827f6590f209f99643c827d6590f209f19643c833e5490f20cf55243c82fa6090f20be58243c827f6550f209f99543c827d6550f209f19543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c833e5410f20cf55043c835e5310f20d754c43c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82de6390b20b758e42c82fa6090b20be58242c833f5450b20cf15142c82f86050b20cf95042c833d5410b20be98042c82f96010b20d7d4f32c835c53ccb20af99232c82bd648cb20d794e32c835d538cb20be98232c82f9608cb20d7d4d32c835c534cb20d794c32c835d530cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c82be6414720af59051c82de6314720b758c51c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c827f65907209f99641c827d6590720be98241c82f960907209fd9541c827d65507209f19541c833e5450720cf55141c82df6350720b718d41c82fb6050720be18141c827f65107209f99441c827d6510720bb98841c82ed62107209fd9731c827e65cc7209f59731c835e53cc720d754f31c827f658c7209f99631c827d658c7209fd9531c827d654c7209f19531c82bf644c720af19131c835e534c720d754d31c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720bb98831c82ed620c720be98031c82f9600c720dd94721c837551c8720be98321c82f960c8720af99021c82bd6408720b798c21c82dd6308720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320be59740c837965d0320ded5340c83ba54d0320de55340c83b954d0320fa98b40c82f962d0320fa58b40c83bb42d0320ee50b40c837951d0320cfd5240c833c5490320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833c5410320ee50040c82f96510320de59440c83ba6410320ded5040c83bb5410320de55040c83b85410320ee90c40c83b84310320be58840c83ba4210320ee10840c83795110320eed0440c83b94110320d794f30c835d53cc320bb98b30c82ed62cc320afd9130c82bc644c320d794d30c835d534c320bbd8930c82ec624c3209f98f548827d63d5220db58b548827e61d522
  | 15 => 0xc27c64548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d08309fd96420c27e65908309f596420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c2be648c830af592320c27f654c830d794d320c36e520c830db548320c3cd320c830be980320c2f9600c830ddd46510c27e64944309f592510c27e62944309f58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c27f65904309f996410c27d6590430dd946410c3755190430be982410c2f960904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c3765150430dd545410c27f65104309f994410c27d6510430dd947310c37551cc430be983310c2f960cc4309f596310c27f654c430afd91310c2bc644c430af990310c2bd640c430bb988310c2ed620c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c36e52c8430db54b210c27f65884309f996210c27d6588430dd946210c37551884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c2fb6048430be181210c27f65084309f994210c27d6508430af990210c2bd6408430b798c210c2dd6308430be980210c2f960084309f992500c27d64940309f597400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f65500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030d754b300c2dd638c030d794e300c2f9638c030de94e300c3da538c030de546300c27f654c030afd91300c2bc644c030b7d95300c35f654c03097d95300c39f644c030e7191300c35d524c030b7d81300c35e504c030f6901300c3d9404c030bed95300c37b654c0309ed95300c3bb644c030ee191300c2fb634c030f6d8d300c37a534c030f694d300c3da434c030f650d300c379514c030b798f54c82dd63d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320ded8154c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c82be64d4f20af59353c827e64d4f20cf9
  | 16 => 0xd64d45309f98b514c27d62d4530d7ccb514c35d32d4530af992514c2bd6494530cfd52514c33c5494530ddd46514c2bf6454530af191514c33f5454530cf151514c2ef6254530bb189514c33f5414530cf150514c37551145309f990514c27d64145309f988514c27d6214530de580514c27e65d05309f597414c27c65d0530cfd53414c33c54d05309f996414c27d65905309f196414c33f5490530cf152414c2fa6090530be582414c27f65505309f995414c27c6550530cfd51414c33c5450530b7d8d414c2dc63505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c2fa6010530be580414c27e65cc530cfd53314c33c54cc530cfd52314c33c548c530ddd46314c374518c530be982314c2f9608c530afd91314c2bc644c530cfd51314c33c544c530ddd45314c374514c530bed81314c2f8604c5309f994314c2be640c530af590314c33f540c530cf150314c2ee620c530bb588314c3d5310c530be980314c27e65c85309f597214c27c65c8530cfd53214c33c54c8530b798f214c2dd63c8530f34cb214c37751c8530dd147214c27e65885309f596214c27c6588530cfd52214c33c5488530dbd4a214c36c5288530be982214c2f960885309fd95214c27e65485309f195214c33f5448530cf151214c3cd32485309f994214c27d65085309f194214c2be6408530af590214c33f5408530cf150214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c33f5490130cf152404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc63501309f994404c33f5410130cf150404c3b94010130cfd53304c33c54cc130eed53304c3b854cc130f6ccb304c3d932cc130be587304c33f548c130cf152304c39f548c130e7152304c2dd628c130f6d42304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c309fd96430c27d6590c30cf952430c33d5490c30be982430c2f96090c309fd95430c27f6510c309f594430c33e5410c30cf550430c2fa6010c30be580430c36f52948309f992520c27d64948309f986520c27d61948309fd9152
  | 17 => 0x86309fd96218c27e65886309f596218c3765188630dd546218c2fa6088630be582218c27f65486309f595218c27c6548630b7d8d218c2dc6348630dd945218c37551486309fd94218c27e65086309f594218c2be6408630af590218c2de6308630b758c218c2fa6008630be580218c33e5490230cf552408c2de6390230b758e408c33e5410230cf550408c2de6310230b758c408c3b94010230b7597308c35d65cc230d754b308c2f965cc230de597308c2f961cc2309f98b544c27d62d51309f987544c27d61d5130cfd8f544c33d63d5130cfd8b544c33e62d5130cf58b544c33c62d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c27e64951308f992544c27d6395130d758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c33f64551309fd8d544c35f63551309fd89544c27c62551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c2be6515130cf994544c23e6515130cfd8c544c33d6315130cfd88544c33e6215130cf588544c33c6215130cfd84544c33e6115130cf584544c33c6115130cfd80544c33d6015130cf4c0544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c33f5490d30cf152434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c33f5410d30cf150434c39d4310d30cfd53524c33c54d49309f993524c27d64d49309f987524c27d61d4930af992524c2bd6494930cfd52524c33c5494930dbd4a524c2bf6454930af191524c33f5454930cf151524c2f76154930bd185524c33f5414930cf150524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c33f54d0930cf153424c27e65909309f596424c27c6590930cfd52424c33c5490930b798e424c2dd63909309fd95424c27e65509309f195424c33f5450930cf151424c2fb6050930be181424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930be980424c2f960109309f997324c33f54cc930cf153324c2de65cc930d7997324c39f54cc930d7953324c35c54cc930e7153324c31c54cc930d714b324c2de60cc930af992324c2bd648c930cfd52324c33c548c930b758e324c36f528c930db14a324c2fa608c930be582324c33f544c930cf151324c36f524c930db149324c2fb604c930be181324c39f544c930d7951324c35c544c930e7151324c31c544c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c3db604c930b7181324c3d8604c9309f994324c33f540c930cf150324c2de630c930cfd53514c33c54d45309f993514c27
  | 18 => 0x9fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc2bf644c730af19131cc2be640c730af59031cc2ee620c730bb58831cc376510c730dd54431cc3d5310c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc2de63c8730b758f21cc36e52c8730db54b21cc3cd32c87309fd9621cc27e65887309f59621cc27f65487309f59521cc27c6548730db94921cc36d5248730f34c921cc2fb6048730be18121cc27f65087309f99421cc27d6508730af99021cc2bd6408730b798c21cc2dd6308730be98021cc2f96008730cf95340cc33d54d0330b798f40cc2dd63d0330cfd5240cc33c5490330cf95140cc33d5450330b7d8d40cc2dc6350330cfd5040cc33c5410330bd987548c2f561d5230d758f548c27e62d52309f58b548c27e61d5230dd987548c27661d52309f587548c37561d52309d587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30cfd52438c33c5490e30cf951438c33d5450e30bed81438c2f86050e30cfd50438c33c5410e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c2be6414a30af590528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c27f6590a309f996428c27d6590a30b798e428c2dd6390a309fd95428c27d6550a309f195428c33e5450a30cf551428c2fb6050a30be181428c27f6510a309f994428c27d6510a30be980428c2f96010a30af992328c2bd648ca30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c2be64d4630af593518c2be6494630af592518c37751946309f992518c33e64946308f992518c27d6494630cf592518c23d64946309f98a518c27d6294630de982518c27f64546309f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c33f54d0630cf153418c37651d0630dd547418c27f65906309f996418c27d6590630cf952418c33d5490630be982418c2f960906309fd95418c27d65506309f195418c33f5450630cf151418c2df6350630b718d418c27f65106309f994418c27d6510630cf950418c33d5410630dd944418c3755110630be980418c2f96010630dd946318c375518c630be982318c2f9608c630afd91318c2bc644c630dd945318c375514c630bed81318c2f8604c630af990318c2bd640c630bb988318c2ed620c630be580318c27f65c86309f997218c27d65c
  | 19 => 0x621102fa6088440be582211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102be6408440af59021102de6308440b758c21102fa6008440be580211033e4394040cf10e501033e4294040cf10a501033f4194040cf50650102be63d0040af98b401033d52d0040af58740102bd6490040cf95240102f96490040de95240103ba5490040ee90e40103b84390040be98a40103ba4290040ee10a40102f96190040eed0640103b941900409fd9540102bf6550040cfd95401023f6550040af18d40102bc6250040cf54940102bf6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103bb4350040ee50d40102f86250040ee90940103b84250040bed8540103bb4150040ee50540102ee62d5330bb58b54cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33e5490f30cf55243cc2fa6090f30be58243cc33e5410f30cf55043cc39d4310f30be98043cc2f96010f30af99352cc2bd64d4b30af99252cc2bd6494b30dbd4a52cc27e6494b30cf99252cc23e6494b309f59252cc33d6494b308f59252cc27e6194b309f58652cc27f6454b309f19152cc27f6154b309f18552cc36d5214b309fd9742cc27e65d0b309f59742cc33f54d0b30cf15342cc36e52d0b30db54b42cc27f6590b309f99642cc27d6590b30cf95242cc33d5490b30b798e42cc2dd6390b309fd9542cc27d6550b309f19542cc33f5450b30cf15142cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30db94842cc36d5210b30db94b32cc36d52ccb30be98332cc2f960ccb30d795332cc35c54ccb30d794b32cc3ce52ccb30f354b32cc2de60ccb30f698332cc3d960ccb30af99232cc2bd648cb30b7d9532cc35f654cb30d795132cc35c544cb30f3d8932cc35e524cb30b718132cc36e520cb30db54832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730d7cc951cc35d3254730af99051cc2bd6414730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d07309fd9641cc27e65907309f59641cc2fa6090730be58241cc27f65507309f59541cc27c6550730cf95141cc33d5450730b7d8d41cc2dc6350730
  | 20 => 0x33d5390c40af98a43102bd6190c40af582431027f6550c40d794c431035d5310c40be98043102f96010c40af98c431039e6310c40e794c431033d5310c40e754c431031d5310c40af98843102bd6110c40ee98043102bd6010c40ee58043102b96010c40dbd4a521027e63948409f58e521027e61948409f586521027f63548409f18d521033e4354840cf10d521027f61548409f18552103786054840b798c52102dd6314840db54852102f66114840bd584521033e54d0840db94b421036d52d0840be98342102f960d08409f59642102de6390840b758e42102bd6590840cf596421023d6590840af98e421039e6390840a798e421039d6390840af98a421033d5290840af58642103bb6090840af58242103b860908409fd95421033e5450840bed81421036e5210840db54842102fa6010840be58042102be6310840af98842103ae6210840eb948421033d5210840eb54842102bd6110840ee98042102bd6010840ee580421027f65cc8409f997321027d65cc840af99332102bd64cc840d794f321035d53cc840e710f32102fa60cc840be583321027f658c8409f996321027d658c840af99232102bd648c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321039c434c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432102bf640c840af190321037751944409f98e511027d6394440cf90e511033c43944409f98a511027d6294440de982511027f63544409f18d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d0440af98f411033d53d0440af98b411033d52d0440cf94741103b651d0440ed54741103ba60d0440af58341103b960d04409f59641102bd6490440be582411027f6550440b7d8d41102dc6350440afd95411033f6550440e7d8d41102bc6350440e718d411029c6350440cf54d41102bc6250440cf54941103b76150440cf94541102bf6050440ee98141103b96050440af99041103765110440dd54441102fa6010440be580411027f65cc4409f997311027d65cc440afd9331102bc64cc440d794f311035d53cc4409fd96311027e658c4409f59631102be648c440af592311039c438c440dd9463110375518c440be98231102f9608c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd545311027f650c4409f994311027d650c440af99031102bd640c440e710c31102ee620c440bb58831102fa600c440be580311027f65c84409f997211027d65c8440afd9321102bc64c8440db94b211036d52c84409fd96211027e65884409f59621102be6488440af59221103765188440dd54
  | 21 => 0x65086409f59421902be6408640af59021902de6308640b758c21902fa6008640be58021902bd65d0240cf59740902be63d0240af98b409033d52d0240af58740902f965d0240de597409037a52d0240de547409027e62d4d409f58b535027e61d4d409f587535035f5394d40bb98a53502ed6294d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435039d4310d409f98f525027d63d49409f987525027d61d4940b798e52502dd6394940dbd4a525036d52149409f98c525027d63149409f984525027d61149409f99742502be65d0940cf997425023e65d0940cf14f425033c52d0940af98342502bd6490940b798e42502dd6390940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940cf14d42503af6250940ebd49425033c5250940eb14942503bb6050940af18142503b86050940ae181425027e6510940af990425027e65cc9409f597325027c65cc940d7d4f325035c53cc9409f996325027d658c9409f19632502be648c940af592325036f528c940db14a325027f654c9409f995325027c654c940d7d4d325035c534c940dbd49325036c524c9409f994325027d650c9409f19432502be640c940af59032502fa600c940be580325027e63d45409f58f515027e62d45409f58b515033f42d4540cf50b51503775194540b7d8d51502dc6354540bbd8951502ec6254540dd544515027e63145409f58c515027e62145409f588515027e65d0540ddd4641503745190540be98241502f96090540b7d8d41502dc6350540ddd4541503745150540bed8141502f860505409f99441503b541105409f997315027d65cc5409f197315027e658c5409f596315027c658c540d7d4e315035c538c5409fd95315027e654c5409f19531502bf644c540af191315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540bb98831502ed620c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af593215027e65885409f596215027c6588540dbd4a215036c52885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540dbd48215036c5208540be98021502f96008540de14b40503bb42d0140ee50b405037b51d0140cf14e40502bd6290140cf14a405033f5190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c40af596431033d6590c40af98e431
  | 22 => 0x7409f59421d02be6408740af59021d02de6308740b758c21d02fa6008740be58021d02f661d4e40bd587539035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c539035e5390e40d754e43902fa6090e40be582439039e5390e40cf54e439039d5390e40af98a43902bd6190e40ee98243902bd6090e40ee582439035e5350e40d754d43902fb6050e40be18143902bd6510e40cf594439039e6310e40cf54c43902be6210e40af58443902bd6010e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529033e4354a40cf10d529027f6154a409f18552902de6314a40b758c529036d5214a40bd98452902f56114a40b798e42902dd6390a40db94a429036d5290a40be98242902f96090a40af98e429039e6390a40a798e429039d6390a40eb94a429033d5290a40eb54a42902bd6190a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902bd6510a40cf59442902be6310a40eb988429033d5210a40af58442902bd6010a409fd97329027e65cca409f59732902be64cca40af593329035e53cca40d754f329039c43cca409fd96329027e658ca409f59632902be648ca40af592329027f654ca409f595329027c654ca40afd9132902bc644ca40d794d329035d534ca40e710d329027f650ca409f994329027d650ca40afd9032902bc640ca40be98032902f9600ca40b798f51902dd63d4640ddd46519027e63946409f58e519033e4394640cf10e519027e62946409f58a519027f63546409f18d519027f62546409f18951903755114640af597419033d65d0640af98f419033d53d0640af98b419033d52d0640cf94741902bd60d0640dd94641903755190640be98241902f96090640b7d8d41902dc6350640dd94541903755150640bed8141902f86050640e7d8d41902bc6350640e718d419029c6350640cf54d41902bc6250640cf54941903b76150640cf94541903b65150640cd94541903b55150640afd8141903bb6050640ee181419027f65cc6409f997319027d65cc640afd9331902bc64cc640dd947319037551cc6409fd96319027e658c6409f59631902be648c640af592319035e538c640d754e319039c438c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c640af99031902bd640c640d794c319035d530c640e710c31902ee620c640bb5883190376510c640dd54431902fa600c640be580319027f65c86409f997219027d65c8640afd9321902bc64c86409fd96219027e65886409f59621902be6488640af59221903765188640dd546219027f65486409f595219027c6548640afd9121902bc6448640dd945219037551486409fd94219027e
  | 23 => 0xd88550087752154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087eb2154021fc88550087e92154021fc485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500877a4254021de50950087784254021decc9500877a3254021de4c950087783254021de985500877b4154021de90550087794154021de105500877b3154021de8c550087793154021de0c5500877b2154021de88550087722154021de48550087712154021de08550086be6414021af590500873e5414021cf55050086de6314021b758c500875e5314021d754c50086fa6014021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d035e5310f40d754c43d039d4310f40be98043d02f96010f40b798e52d02dd6394b40dbd4a52d027e6394b40d798e52d025e6394b409f58e52d035d6394b409758e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d037b6054b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d033e53d0b40cf94b42d03ae52d0b40eb54b42d02be60d0b40ee98342d03b960d0b40b798e42d02dd6390b40be18142d02bf6550b40cfd9542d033e5350b40ebd8942d033e5250b40eed8142d02bc6050b40ee18142d02b86050b40db94842d036d5210b40be98042d02f96010b409fd9732d027e65ccb409f59732d02fa60ccb40be58332d027f658cb409f99632d027d658cb40af99232d02bd648cb409fd9532d027d654cb409f19532d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40ddd4651d027e63947409f58e51d027e62947409f58a51d037960947409fd8d51d027c63547409fd8951d027c6254740cfd0951d033d4254740dd54451d037651d0740dd54741d02fa60d0740be58341d02fa6090740b7d8d41d02dc6350740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc7409fd9631d027e658c7409f59631d02fa608c740be58231d027f654c7409f59531d027c654c740afd9131d02bc644c7409fd9431d027e650c7409f59431d02be640c740af59031d02ee620c740bb58831d02fa600c740be58031d027f65c87409f99721d027d65c8740af99321d02bd64c87409fd9621d027e65887409f59621d02fa6088740be58221d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e6508
  | 24 => 0x320875d534c821db949320867f650c8219f594320873e540c821cf550320875e530c821d754c32086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d0421cf953410873d54d0421d794f410875d53d04219fd96410867d6590421cf952410873d5490421d794e410875d5390421bb98a41086ed6290421be98241086f960904219fd95410873e5450421cf55141086df6350421b718d410875e5350421d754d410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb588410867d65cc421cf953310873d54cc421d794f310875d53cc4219fd96310867d658c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c4219fd9531086bf644c421af191310873e544c421cf551310875e534c421d754d310867f650c4219f994310867d650c4219f19431086be640c421af590310873e540c421cf550310875e530c421d754c31086ee620c421bb58831087d5310c421be98031086f9600c421cf953210873d54c8421d794f210875d53c8421eb95321087ad54c8421dbd4f21087ce53c8421db54f21087cd53c8421d354f210873e5488421cf552210875e5388421d754e21086ed6288421db94a21087b65488421ed55221087d65388421f554e21086f56288421dd94a21087e652884219fd95210873e5448421cf551210875e5348421d754d21086ef6548421dbd95210866f6548421eb95121087ad5448421dbd4d21087ce5348421db54d21087cd5348421d354d21086ef6148421db94521087e64148421f950521086f76548421ddd9521086776548421ed95121087b55448421f594d21087d55348421bdd8921087e76248421dd94921087e65248421f990921087e54248421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021cf952500873d5494021d794e500875d5394021ded42500867e64940219f592500867e63940219f58e500877b5494021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087eb2194021fc88650087e92194021fc486500877b6494021de99250087796494021de192500877b6394021de98e50087796394021de18e500877b4394021de90e50087794394021de10e50087786294021ded0a500877a4294021de50a50087784294021decca500877a3294021de4ca50087783294021de186500877b4194021de90650087794194021de106500877b3194021de8c650087793194021de0c6500877b2194021de88650087792194021cf951500873d5454021d794d500875d53540219fd91500867c64540219fd8d500867c6354021d
  | 25 => 0x6f960150219f990540873e64150218f990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e58054086be64d4c21af593530873e54d4c21cf55353086fa60d4c21be583530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21cf952530873d5494c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21e7952530871e5494c21d7552530879d5494c21c7552530875c5494c21d7d92530875e6494c21d7592530875c6494c21d798a530875c6294c21d7986530875c6194c21d7d82530875e6094c21d7582530875c6094c21cf951530873d5454c219fd91530867c6454c21d7d8d530867f6054c219f181530875f6554c21d7d51530875e5454c21e7951530871e5454c21d7551530879d5454c21c7551530875c5454c21d7d91530875e6454c21d7591530875c6454c21d7989530875c6254c21d7985530875c6154c21d7085530875f6054c21d7981530875d6054c21d718153086be6414c21af590530873e5414c21cf55053086de6314c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530865e6314c219f988530876e6214c219b988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430875e53d0c21d754f430867f6590c219f996430867d6590c219f196430873e5490c21cf552430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086f76150c21bd185430867f6510c219f994430867d6510c219f194430873e5410c21cf550430875e5310c21d754c430867e64948219f592520867e63948219f58e520867d65d0821cf953420873d54d0821d794f420875d53d08219fd96420867d6590821cf952420873d5490821b798e42086dd6390821d794e420875d5390821bd98642086f561908219fd95420873e5450821cf551420875e5350821d754d42086fb6050821be181420867f65108219f594420873e5410821cf550420875e5310821d754c42086f66110821bd584420867d65cc821cf953320873d54cc821d794f320875d53cc8219fd96320867d658c821af99232086bd648c821cf952320873d548c821d794e320875d538c821db94a32086f6618c821bd586320867f654c821cf951320873d544c821d794d
  | 26 => 0x54d219f994534875d5314d219f990534867d6414d21d798c534876d6214d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21bb98a43486ed6290d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921b798e42486dd63909219f195424873f5450921cf15142486f76150921bd18542486fb6050921be181424867e65109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921af99232486bd648c921bb996324876e658c921eb99232487ad648c921bb58e324876e538c921db14e32486ee618c9219f195324875f534c921d714d32486f7614c921bd185324876c654c9219b19532487cf634c921f3d4d324876e534c921db14d32487cc534c921f3d0d32487cc434c921f9d8532486ec614c921f9185324867e650c921bb98832487cd320c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e6590521be98241486f960905219fd95414867d65505219f195414873f5450521cf15141486df6350521b718d41486ef6250521bb189414867e65105219f997314875f53cc521d714f31486ee62cc521bb58b31487cd32cc5219f996314867f654c5219f595314867c654c521afd9131486bc644c521d7d4d314875c534c521bbd8931486ec624c521f34c9314867e650c521af99031486bd640c521bb98831486ed620c521be98031486f9600c521f98cb21487e532c8521bd58321486ef6388521bb58e21487e751885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121b798f54086dd63d5021be98354086f960d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540877a60d50219e983540867d60d5021de583540867960d50219f596540873f54950219f98e540867d63950219f982540867d60950218f596540873f6395021cf98e540873d6395021cf18e540873e6295021cf18a540873e6195021cf186540873f6095021cf982540873d6095021cf182540873f64550219fd8d540867c63550219fd81540867c6055021cfd95540873f6355021cf98d540873d6355021cf18d540873e6255021cf189540873e6155021cf185540873c2155021cfd81540873e6055021cf581540873c6055021af990540873d5415021b798c54086dd6315021be9805408
  | 27 => 0x219f592538867e6094e219f58253886bf6454e21af191538867f6454e21cfd91538863f6454e219f191538873c6454e218f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c53886fa6014e21be580538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de58053886796014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e21d7d4f438875c53d0e219fd96438867e6590e219f596438867c6590e21cfd52438873c5490e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e219fd94438867e6510e219f594438867c6510e21cfd50438873c5410e21d7d4c438875c5310e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21b798e42886dd6390a21cf951428873d5450a21bdd8542886f46150a21bed8142886f86050a21d794f328875d53cca21bd98732886f561cca21af99232886bd648ca21d794d328875d534ca21bdd8532886f4614ca21cfd53418873c54d0621cf952418873d5490621bb98a41886ed6290621be98241886f96090621cfd51418873c5450621b7d8d41886dc6350621cf950418873d5410621bb98841886ed6210621d7d4f318875c53cc621d794e318875d538c621bb98a31886ed628c621afd9131886bc644c621d7d4d318875c534c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621be98031886f9600c621bb597218876d65c8621dbd4f218876d53c8621bd597218877565c8621bd58321886be64d4221af593508877b50942219f992508867d64942219f98e508867d63942219fd91508867c64542219fd8d508867c6354221de540508867e63d51219f58f544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786
  | 28 => 0x18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f21db98a53c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21d754c53c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21d794f43c875d53d0f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f21bb98a43c86ed6290f219fd9543c867e6550f219f59543c867c6550f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21d794c43c875d5310f21bb98843c86ed6210f21cfd5342c873c54d0b21cf95242c873d5490b21b798e42c86dd6390b21bd98642c86f56190b21cfd5142c873c5450b21bed8142c86f86050b21cf95042c873d5410b21bd98442c86f56110b21d7d4f32c875c53ccb21af99232c86bd648cb21d794e32c875d538cb21bd98632c86f5618cb21db59632c87ae648cb21eb59232c876e538cb21f394e32c87cd538cb21db14e32c86ee618cb21f998632c87e5618cb21d7d4d32c875c534cb21bbd9532c876f654cb21f3d8d32c87cf534cb21db94d32c876c534cb21f314d32c87cf434cb21f310d32c86ec614cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c86fa6090721be58241c873e5450721cf55141c86df6350721b718d41c86ef6250721bb18941c875e53cc721d754f31c86ee62cc721bb58b31c87cd32cc721afd9131c86bc644c721d794d31c875d534c721bbd8931c86ec624c721f34c931c86be640c721af59031c86ee620c721bb58831c87d5310c721be98031c86f9600c721ded4250c867e64943219f59250c867e63943219f58e50c86bf6454321af19150c867f6454321cfd9150c863f64543219f19150c873c64543218f19150c867f63543219f18d50c86be6414321af59050c86de6314321b758c50c87795014321be98354886f960d52219f98f548867d63d5221db58b548877661d52219f983548877a60d52219e983548867d60d5221de583548867960d5221cfd52548867e63952219f58e548867e60952219f58254886df6355221b718d548873f64552219fd8d548875f635522197d8d548867c6355221d718d548865c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e
  | 29 => 0x10c6f5638c431dd94e310c7d6538c431f5d0e310c7d4438c431f994a310c7e5528c4319fd95310c6bf644c431af191310c73e544c431cf551310c76e524c431db549310c6df654c431d7d95310c65f654c431e7d91310c6de644c431b7191310c79c644c431a7191310c79e544c431e7551310c7ce524c431d7549310c7cd524c431d3549310c6df614c431d7945310c7d6414c431f5505310c6f7654c431ddd95310c677654c431edd91310c7b4644c431ed951310c7b5544c431bdd8d310c7d7634c431dd94d310c7d6534c431f590d310c7d5434c431f9949310c7e5524c431f58c9310c7d4324c431af993500c6bd64d4031cf953500c73d54d4031bb98b500c6ed62d4031db94b500c76d52d4031cf952500c73d5494031db94a500c76d5294031ded42500c67e64940319f592500c67e62940319f58a500c77b5494031de952500c7ba5494031ce952500c7795494031ee552500c7395494031de152500c7db4394031f610e500c77b5294031de94a500c7ea5294031da94a500c7795294031fa54a500c7695294031de14a500c7db3194031fc8c6500c7d93194031fc4c6500c77b6494031de992500c7796494031de192500c7786394031ded0e500c77a4394031de50e500c7784394031ded8a500c77a6294031de58a500c7786294031ded0a500c77a4294031de50a500c7784294031decca500c77a3294031de4ca500c7783294031de186500c77b4194031de906500c7794194031de106500c77b3194031de8c6500c7793194031cf951500c73d5454031db949500c76d52540319fd91500c67c64540319fd89500c67c6254031ded95500c77b5454031de951500c7ba5454031ce951500c7795454031ee551500c7395454031de151500c7db4354031f610d500c77b5254031de949500c7ea5254031da949500c7795254031fa549500c7695254031de149500c7db3154031fc8c5500c7d93154031fc4c5500c77b6454031de991500c7796454031de191500c77a6354031ded0d500c77a4354031de50d500c7784354031ded89500c77a6254031de589500c7786254031ded09500c77a4254031de509500c7784254031decc9500c77a3254031de4c9500c7783254031de985500c77b4154031de905500c7794154031de105500c77b3154031de8c5500c7793154031de0c5500c6be6414031af590500c73e5414031cf550500c6ee6214031bb588500c76e5214031db548500c6fa6014031de540500c6de63d5321b758f54c867e63d5321d798f54c865e63d53219f58f54c875d63d53219758f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321bed8154c86f86055321cfd9154c867f63553219f18d54c867f6055321ded8154c867b60553219f18154c877860553219e
  | 30 => 0x5d6510c31b7990430c79e6410c31d7d50430c79e5410c31d7550430c79d5410c31f5984430c6dd6110c31f5584430c6d56110c31af993520c6bd64d4831cf953520c73d54d4831be983520c6f960d4831cf952520c73d5494831dbd4a520c67e64948319f592520c67e60948319f582520c76f5494831db952520c7ae5494831cb952520c76d5494831eb552520c72d5494831db152520c7cf4394831f310e520c76f6494831db992520c76d6494831db192520c76c6394831dbd0e520c76e4394831db50e520c76c4394831db986520c76c6194831dbd82520c76e6094831db582520c76c6094831cf951520c73d54548319fd91520c67c6454831d7d0d520c75c43548319fd81520c67c6054831dbd95520c76f5454831db951520c7ae5454831cb951520c76d5454831eb551520c72d5454831db151520c7cf4354831f310d520c76f6454831db991520c76d6454831db191520c76e6354831dbd0d520c74f4354831db90d520c76d4354831db10d520c74c4354831db985520c76c6154831db0c5520c76f6054831db981520c76d6054831db181520c6be6414831af590520c73e5414831cf550520c6ee6214831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831e710f420c76e52d0831db54b420c67f65908319f996420c67d6590831cf952420c73d5490831b798e420c6dd6390831db94a420c76d52908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c79c4350831db949420c76d5250831bdd85420c6f46150831bed81420c6f860508319fd94420c67e65108319f594420c73e5410831cf550420c76e5210831db548420c73e54cc831cf553320c75e53cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c6be648c831af592320c73e548c831cf552320c76d528c8319fd95320c73e544c831cf551320c75e534c831db949320c73e540c831cf550320c76e520c831db548320c6f6610c831bd584320c67e64944319f592510c75f4394431d710e510c67d65d0431cf953410c73d54d0431e7d0f410c76e52d0431db54b410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c79c4390431db94a410c76d5290431be982410c6f960904319fd95410c73e5450431cf551410c6df6350431b718d410c79f4350431db949410c76d52504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431e710c410c76e5210431db548410c73e54cc431cf553310c76e52cc431db54b310c6de64cc431b7193310c79e54cc431e7553310c7ce52cc431d754b310c7cd52cc431d354b310c73e548c431cf552310c6dd638c431d794e310c76e528c431db54a310c7b6548c431ed5523
  | 31 => 0xcc931c7153324c75c52cc931b7987324c6be648c931af592324c73f548c931cf152324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931cfd51324c73c544c931dbd49324c76c524c931bdd85324c6f4614c931e7d51324c75e544c931d7151324c79c544c931c7151324c7cf624c931f3d49324c75c524c931f3149324c7d7614c931b7185324c7d4614c931b5185324c67e650c931cfd50324c73c540c931b798c324c7cd320c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e6590531cfd52414c73c5490531be982414c6f960905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531cfd50414c73c5410531cfd53314c73c54cc531edd53314c7b454cc531f5ccb314c7d532cc531cfd52314c73c548c531e7d52314c75e548c531d7152314c79c548c531c7152314c6dd628c531f5d46314c73f54d4131cf153504c67e64d41319f593504c67e62d41319f58b504c75f32d4131d74cb504c6be6494131af592504c73f5494131cf152504c77b5094131afd91504c6bc6454131cfd51504c73c5454131bbd89504c6ec6254131cfd50504c73c5414131de540504c67e64141319f590504c67e62141319f588504c6ee62d5031bb58b540c6fa60d5031be583540c67e63d5031d798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d5031de983540c67a60d50319f583540c77960d50319e583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031e718e540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f6455031d718d540c67f62550319f189540c67f60550319f181540c73f6555031e718d540c73e6355031cf18d540c71c6355031cfd89540c73e6255031cf589540c73c6255031cf985540c73c6155031cf0c5540c73f6055031cf981540c73d6055031cf181540c6be6415031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c63e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c73e54d0c31cf553430c6dd65d0c31d7597430c75f54d0c31e7953430c75d54d0c31e7553430c71d54d0c31b7587430c67f6590c319f596430c73e5490c31cf552430c6de6390c31bd986430c6f56190c319fd95430c73e5450c31cf551430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bd984430c6f56110c31d7594430c6
  | 32 => 0x1af590528c76d5214a31be980528c6f96014a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c79c43d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c67f6550a319f595428c67c6550a31cf951428c73d5450a31b7d8d428c6dc6350a31e710d428c6fb6050a31be181428c67f6510a319f994428c67d6510a31bd984428c6f56110a31af992328c6bd648ca31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31cfd53418c73c54d0631e7d0f418c73e5490631cf552418c6de6390631b758e418c79c4390631be982418c6f96090631cfd51418c73c5450631b7d8d418c6dc6350631e7d0d418c73e5410631cf550418c6de6310631b758c418c79c4310631b7597318c75d65cc631b7993318c6dc64cc631d754b318c6f565cc631dd597318c6be64d4231af593508c77b50942319f992508c67d64942319f98a508c67d62942319fd91508c67c64542319fd89508c67c6254231de540508c67e62d51319f58b544c67e60d51319f583544c73f63d5131cf58f544c73f62d5131cf98b544c73d62d5131cf18b544c73f61d5131cf587544c73f60d5131cf983544c73d60d5131cf183544c73f54951319f992544c63e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131cfd91544c67f6355131d7d8d544c65f63551319fd89544c67c62551319fd85544c77761551319fd81544c67c60551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c6be6515131cf994544c63e6515131cfd8c544c73d6315131cfd88544c73e6215131cf588544c73c6215131cfd84544c73d6115131cf4c4544c73f6015131cf980544c73d6015131cf180544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c73f5490d31cf152434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c73f5410d31cf150434c73f54d4931cf153524c67e64d49319f593524c67e60d49319f583524c6be6494931af592524c73f5494931cf152524c76f5294931afd91524c6bc6454931cfd51524c73c5454931bed81524c6f86054931cfd50524c73c5414931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931cfd53424c73c54d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c67f65509319f995424c67c6550931cfd51424c73c5450931bed81424c6f860509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c6f66110931bd584424c67e65cc931cfd53324c73c54cc931b7997324c75e65cc931e7d53324c75e54cc931d7153324c79c54
  | 33 => 0x8d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cfd5343cc73c54d0f31cf95243cc73d5490f31bd98643cc6f56190f31cfd5143cc73c5450f31cf95043cc73d5410f31bd98443cc6f56110f31af99252cc6bd6494b31dbd4a52cc67e6494b31cf99252cc63e6494b319f59252cc73d6494b318f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc73f54d0b31cf15342cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b319fd9542cc67d6550b319f19542cc73f5450b31cf15142cc6f76150b31bd18542cc6fb6050b31be18142cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31db94b32cc76d52ccb31bd98732cc6f561ccb31d795332cc75c54ccb31d794b32cc7ce52ccb31f354b32cc6de61ccb31f598732cc7d561ccb31af99232cc6bd648cb31b7d9532cc75f654cb31d795132cc75c544cb31f3d8932cc7cf524cb31d794932cc7cc524cb31b718532cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cfd5241cc73c5490731be98241cc6f96090731cf95141cc73d5450731b7d8d41cc6dc6350731cfd5041cc73c5410731ded4250cc67e64943319f59250cc67e62943319f58a50cc6bf6454331af19150cc67f6454331cfd9150cc63f64543319f19150cc73c64543318f19150cc67f62543319f18950cc75f3254331d74c950cc7795014331be983548c6f960d5231d758f548c67e62d52319f58b548c77661d52319f983548c77a60d52319e983548c67d60d5231de583548c67960d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f6455231d7d8d548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c75d65d0e31d7d53438c79e54d0e31d7553438c79d54d0e31f5987438c6dd61d0e31f5587438c73f5490e31cf152438c73e5450e31cf551438c6f76150e31bd185438c73f5410e31cf150438c79d4310e31b7594438c75d6510e31e7990438c75f5410e31e7d50438c75d5410e31e7150438c6dd6110e31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c75f4354a31d710d528c67f6054a319f181528c6be6414a3
  | 34 => 0x506be644c941af591325075f534c941d714d325079f434c9419f994325067d650c9419f19432506be640c941af590325075f530c941d714c32506f6610c941bd584325075f53d0541d714f41507d753d0541f514f41507b743d0541ed50f41507b742d0541ed50b415075f5390541d714e41506fa6090541be58241506bd6390541e7d4e415073c5390541e714e415071c5390541af58a41507b75190541af98241507ba6090541ae98241507b96090541d7d4f505075c53d41419f98f505067d63d41419f98b505067d62d4141cfd0b505073d42d4141b798e50506dd6394141d7d4e505075c5394141ded4250506df6354141b718d505075f5354141d714d50506ef6254141bb189505075f5314141d714c505077950141419f98c505067d63141419f988505067d6214141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41cf953431075e53d0c41d754f43106f661d0c41bd587431067d6590c41af596431073d6590c418f59643106be6390c41cf54e43106bd6190c419fd95431073e5450c41d794c431075d5310c41e750c43106f66110c41bd58443106be6310c41e798c431079e5310c41cf54c431079d5310c41ed98443106bd6110c41ed584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c6354841cf90d521073c43548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521073e54d0841db94b421076d52d0841bd98742106f561d08419f59642106de6390841b758e421067f6550841cf95142106fb6050841be181421076e5210841db54842106f66110841bd584421067f65cc8419f997321067d65cc841d794f321075d53cc841e710f321067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321079c434c841db949321076d524c841bdd8532106f4614c8419fd94321067e650c8419f594321073e4394441cf10e511077a6094441de58251106be63d0441cf54f411073d52d0441af592411073e5490441be98241106f96090441bd59241107765490441ed95241107b64390441ed10e41107f26090441fc582411067f6550441b7d8d41106dc6350441afd95411073f65504418fd95411079f6350441af18d411079c6350441a718d411073d5350441cf54941106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f5d8d41107d46350441ded42501067e63940419f58e501073e4394041cf10e501067e62940419f58a501073f4194041cf506501067f63540419f1
  | 35 => 0x86294241ded0a509077a4294241de50a50907784294241decca509077a3294241de4ca50907783294241de186509077b4194241ced06509067f63542419f18d509067f62542419f189509077b6554241ded4d509077a5354241de54d50907785354241ee90d50907b84354241ded49509077a5254241de54950907785254241eed0550907f34154241de591509077b6354241de98d50907796354241de18d509077b4354241de90d50907794354241de10d509077b6254241de98950907796254241de189509077b4254241de90950907794254241de109509077b3254241de8c950907793254241de0c9509077a6154241ded05509077950142419f98b535067d62d4d419f983535067d60d4d41e7d93535075f64d4d41d7d8b535075e62d4d41d758b535075c62d4d41d7d87535075d61d4d41d7d83535075e60d4d41d7583535075c60d4d41d7d4e535075d5314d419f988535067d6214d419f980535067d6014d41b7994535075e6514d41e7590535075f6414d41d7d88535075e6214d41d7588535075c6214d41d7d84535075d6114d41d7504535075f6014d41d7980535075d6014d41d7180535067e65d0d41d714f43506be65d0d41cf997435063e65d0d41e7d4f435073c53d0d41e714f435071c53d0d41af58b43506be61d0d41af98343506bd6490d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d41e7d8d435079f5350d41cf14d435079c5350d41c714d43506bf6250d41edd8543506bc6150d41ed18543506bc6050d419f99443506be6410d41d7d4c435075f53d4941d714f525067e63d49419f58f525067e60d49419f58352506de6394941b758e525075f5394941d714e525076f5294941b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525067e60149419f580525067e65d0941d7d4f425075c53d0941af997425073e65d0941af58f425079f53d0941cf14f425079c53d0941c714f425073c52d0941af98742506be60d0941af59242506de6390941b758e425075f5390941d714e425076f5290941db14a42506f66190941bd586425075f5350941d714d425076f5250941db14942506f76150941bd18542506fb6050941be18142506bf6350941e7d4d425073c5350941e714d425071c5350941ebd8942507af5250941cf14942507ac5250941edd8542506bc6150941ed18542507bb6050941af18142507b86050941ae181425067e6510941af990425075f5310941d714c425067e65cc9419f597325067c65cc941af99332506bd64cc941d7d4f325075c53cc941e7d0f325067e658c9419f596325067c658c941af99232506bd648c941d7d4e325075c538c9419fd95325067e654c9419f19532
  | 36 => 0x4b419f58e52d075d6394b419758e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41af58f42d073e53d0b41cf94b42d07ae52d0b41eb54b42d06be61d0b41ed98742d07b561d0b41af98342d06de6390b41b758e42d06fb6050b41be18142d06bf6550b41cfd9542d06bf6350b41cf94d42d07af6250b41cf94942d06bc6150b41eed8142d06bc6050b41ee18142d06b86050b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d079f43ccb419fd9632d067e658cb419f59632d06be648cb41af59232d067f654cb419f59532d067c654cb41af99132d06bd644cb41e7d0d32d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d073f4254341cf50950d07795014341be98353906f960d4e41d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98853906ed6214e41be98053906f96014e41d794e439075d5390e41bd98643906f56190e41e794e439073d5390e41e754e43907b66190e41af58643907b56190e41d794d439075d5350e41bdd8543906f46150e41e750c43906bd6510e41cf594439079e6310e41e7d4c439073d5310e41e714c43906bd6110e41be98352906f960d4a41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529073e4354a41cf10d529067f6054a419f18152906de6314a41b758c529076d5214a41be98052906f96014a41b798e42906dd6390a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41bed8142906f86050a419fd97329067e65cca419f597329075e53cca41d754f329079c43cca419fd96329067e658ca419f59632906be648ca41af592329076e528ca41db54a329067f654ca419f595329067c654ca41afd9132906bc644ca41d794d329075d534ca41e710d329076e524ca41db549329067f650ca419f994329067d650ca41bd98432906f5610ca41af597419073d65d0641af98f419073d53d0641cf54b41906f565d0641dd597419077b50942419f98e509067d6394241cf90e509073c43942419f98a509067d6294241cfd06509077b5394241de94e50907795394241de14e50907ba4394241ee10e509077b5294241de94a50907795294241de14a50907bb4194241fcd06509077b6494241ded8e509077a6394241de58e50907786394241ded0e509077a4394241ce90e50907794394241de10e50907384394241ded8a509077a6294241de58a509077
  | 37 => 0x9e980514ca7d6014532de580514ca7960145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d61141329f98f540cb5e63d50329798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494c329f592530ca7d65d0c32d794f430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32d794c430caee6210c32bb588430ca7e6494832cf992520ca3e64948329f592520cb3d64948328f592520ca7d65d0832cfd53420cb3c54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420cb3f5450832cf151420cafb6050832be181420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cb5e54cc832d7153320cabe648c832af592320cadd638c832d794e320cbae648c832eb592320caed638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832d7951320cb5c544c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c6454432d7cc9510cb6e3254432d74c9510cb6d32544329fd81510ca7c6054432af990510cabd6414432dd544510cafa6014432be580510cb7b50940329f992500ca7d64940329f986500ca7d6194032afd91500cabc64540329fd91500cb3f64540328fd91500ca7c6454032cf191500ca3c6454032d7cc9500cb5d32540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d073e53d0f41e794f43d079d53d0f41af58b43d06be61d0f41ed98743d07b561d0f41af98343d06bf6550f41cfd9543d079f6350f41cf94d43d06bf6250f41af18543d06bc6050f41d794c43d075d5310f41bd98443d06f56110f41b798e52d06dd6394b41dbd4a52d067e6394b41d798e52d065e639
  | 38 => 0xe428cb3e5450a32cf551428cafb6050a32be181428cb3e5410a32cf550428cade6310a32b758c428cbad4210a32cf953328cb3d54cca32b7597328cb5d65cca32d7953328cb9e54cca32c7953328cb9d54cca32d7153328caed65cca32db597328cbae54cca32eb553328caed61cca32af993518cabd64d4632cf953518cb3d54d4632cf952518cb3d5494632ddd46518ca7e64946329f592518ca7e60946329f582518cb3e5454632cf551518ca7f64546329f191518cb5f32546329fd81518ca7c6054632af990518cabd6414632cf950518cb3d5414632dd544518cafa6014632be580518cabe64d4232af593508cb3e54d4232cf553508cb3e5494232cf552508cb7b50942329f992508ca7d64942329f986508ca7d6194232cf951508cb3d54542329fd91508ca7c6454232d7cc9508ca7f61542329f185508cabe6414232af590508cb3e5414232cf550508caf66114232bd584508cb795014232d758f544ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d32d7997434ca5e65d0d32d7d53434cb9f54d0d32d7553434cb9c54d0d32b798b434cbce62d0d32b398b434cbcd62d0d32b7587434cadd60d0d329f996434cb3e5490d32cf552434cade6390d329f195434cb3f5450d32cf151434caef6250d32bb189434ca7e6510d32cf950434cb3d5410d32e750c434cade6510d32d7994434cade6410d32e7990434cb5f5410d32e7950434cb5d5410d32e7550434cade6210d32b7584434cadd6010d329f997424cb3f54d0932cf153424cade63d0932b758f424cb9c43d09329f996424cade6390932b758e424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932e710d424cafb6050932be181424ca7e6510932eb508424cbcf43cc932f310f324caed61cc932af992324cabd648c932b7992324cb9e648c932a7992324cb9d648c932b7192324cbcf528c932b7586324cadd608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cabe6414532af590514cb755114532be980514caf960145329f990514cb3e64145328f990514ca7d6414532cf590514ca3d6414532d7d0c514cb5c43145329f980514cb7a6014532
  | 39 => 0xabf6250842cf9494210bbb6050842af1814210bb86050842ae1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842ebd0d4210bad4350842fad814210be86050842ddd465110a7e63944429f58e5110a7e60944429f5825110a7f63544429f18d5110b3f4254442cf5095110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010b3f4254042cf5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042be98354ccaf960d5332d798f54ccb6d62d53329f98754cca7d61d53329f98354ccb7a60d53329e98354cca7d60d5332de58354cca7960d5332cfd5254cca7e61953329f58654cca7e60953329f58254ccb3f6455332d718d54cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccadd65d0f32d759743ccb5f54d0f32d755343ccade62d0f32b758743ccadd60d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32cf95043ccb3d5410f32e750c43ccaee6210f32bb58843ccb5d6510f32e799043ccb5f5410f32e795043ccb5d5410f32e755043ccade6210f32f398843ccbcd6210f32b758443ccadd6010f32cf95342ccb3d54d0b32b798f42ccadd63d0b32e710f42ccade6390b32b758e42ccb3e5450b32cf55142ccadf6350b32b718d42ccb9c4350b32bed8142ccaf86050b32ddd4651cca7e64947329f59251ccb5f4394732d710e51cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccabe6414732af59051ccb755114732be98051ccaf96014732af99350ccabd64d4332ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6395232cf58e548cb3e6295232cf18a548cb3f6195232cf986548cb3d6195232cf186548cb3f6095232cf982548cb3d6095232cf182548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cfd95548cb3f6355232cf58d548cb3e6255232cf189548cb3f6155232cf985548cb3d6155232cf185548cb3f6055232cf981548cb3d6055232cf181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5490e32cf552438cb3e5450e32cf551438caef6250e32bb189438cb3e5410e32cf550438cb3e54d0a32cf553428cb3e5490a32cf552428cade6390a32b758
  | 40 => 0x63942429f9865090a7d6194242d794d5090b5d53542429fd8d5090a7c6354242cfd095090a7f61542429f1855090ade6314242b758c5090b5e5314242d754c5090af66114242bd5845090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350afa6094d42be5825350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350abe6390d42cfd4e4350b9f5390d42e714e4350abe6290d42eb98a4350aae6290d42eb58a4350abd6190d42af5824350b5f5350d42d714d4350aef6250d42bb1894350a7e6510d42e750c4350abe6510d42cf9944350abe6310d42e798c4350b3f5310d42e794c4350b9d5310d42af9884350abd6110d42af5804350bae43d0942eb10f4250ade6390942b758e4250abe6390942e798e4250a9e6390942e758e4250baf5290942af5864250abd60909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150afa6094542be5825150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d6314542cf90c5150b3c43145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142eed935050b7b53d4142de94f5050b7953d4142de14f5050bba43d4142ee10f5050beb42d4142ee90b5050b7b51d4142de9475050b7951d4142de1475050b7b64d4142ded8f5050b7a63d4142de58f5050b7863d4142ded0f5050b7a43d4142de50f5050b7843d4142ded8b5050b7b42d4142de90b5050b7b61d4142de9875050b7961d4142de1875050b7b5094142de5405050a7e63141429f58c5050b3e4314142cf10c5050b3e42141429f9845050a7d6114142be9945050b7a6514142ee5905050b7b5314142de94c5050b795314142de14c5050bba4314142ee10c5050beb4214142ee9085050b7b5114142de9445050b795114142de1445050b7b6414142ded8c5050b7a6314142de58c5050b786314142ded0c5050b7a4314142ce90c5050b794314142de10c5050b384314142ded885050b7b4214142de9085050b3a4214142de5085050b7b6114142de9845050b796114142de1845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42cf9524310a7f6550c42cf9504310b5e5310c42d754c4310aee6210c42bb5884310b5e6394842d758e5210b3e53d0842af9834210abd6490842cf9524210ade6390842b758e4210aed6490842db9524210bae5490842f398e4210bcd63908429fd954210afb6050842be1814210abf6550842cfd954210a3f6550842cf94d421
  | 41 => 0xc439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43afd894310ebc6150c43af1814310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b7d894310edc6150c43dbd4a5210e7e61948439f5865210e7e60948439f5825210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110e7e62944439f58a5110e7e60944439f5825110f3f4354443cf50d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42af59643d0b3d6590f42cf54e43d0abe6290f42af58643d0abd6090f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0b9e6310f42e794c43d0b3d5310f42e754c43d0abe6210f42eb98843d0bad6210f42af58443d0abd6010f42ddd4651d0afa6094742be58251d0a7e63947429f58e51d0b3e4394742cf10e51d0a7e6094742de98251d0a7a60947429f58251d0b7960947429e58251d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0b3e4394342cf10e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b5f6494e42d798a5390b5c6294e42d7d865390b5e6194e42d75865390b5c6194e42d7d825390b5e6094e42d75825390b5c6094e429fd855390a7c6154e429fd815390a7c6054e42d7d955390b5d6454e42d79895390b5c6254e42d7d855390b5e6154e42d75855390b5c6154e42d7d815390b5e6054e42d75815390b5c6054e42d754c5390b5e53d0e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42d754c4390b5e53d0a42d754f4290abd65d0a42cf5974290b3e53d0a42e794f4290b1e53d0a42e754f4290abe60d0a42bb5974290b6d65d0a42f394f4290bcd53d0a42b798f5190add63d4642d794f5190b5d53d4642d794e5190b5d5394642ddd465190a7e63946429f58e5190a7e60946429f5825190b5e5354642d754d5190a7f63546429f18d5190b3f42546429fd815190a7c6054642b798c5190add6314642d794c5190b5d5314642dd5445190afa6014642be5805190ade63d4242b758f5090b5e53d4242d754f5090b5e5394242d754e5090b7b50942429f98e5090a7d
  | 42 => 0x90030000000000100080020000001000000800000000004000000c005000800000340110014002000400b0000000002c0030000006000400000000020008000001000000040100000003003c000002000000b4000000c0010058001004800f000c0040000002000000000000160024000000c00000000030014000000c012000c00000ac003002800400040000008005000400100000050000008003400000040050008017000c004005000500080000040003000400100000000020002005000000080000004000001c011003400400240020000001000000b000400000d400100000030000007000400200440080010003000400000100010000000000000000040040008042001c0000000000000c001002c01800040000000005002400000000000004008000c00100a4000000400c000800400040020004002000400000140040000004002400100000010008011000c00f00040000004000001c01a006000000000030000003001f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f775194743be98251d0ef960947439f98a51d0e7d62947439f98251d0f7a60947439e98251d0e7d6094743de58251d0e7960947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390ebd62d0e43af9874390ebe60d0e43b75974390f5d65d0e43be9835290ef960d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f5f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290f775194643d7d0e5190e7e62946439f58a5190e7e60946439f5825190f3f43546439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643dd5445190efa6014643be5805190eee62d4243bb58b5090f7b50942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090f9f5390d43af5864350f5f43d4943cf90f5250e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543be9825150ef96094543dd5445150f5f4314543cf90c5150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050ef66194143bd5865050f7b5094143de5405050f3e43141439f9885050e7d62141439f9845050e7d6114143af58b4310ebe61d0c43af9834310ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b758a4310ede6190
  | 43 => 0x2f00000000008001000c000001c002005000000080010004000000c002000000200440000000013000000a00000160014004000c00200000000004001001c004000800800000010004000000800700180090018005001000000b40030000000007c002000000200040030000000002000900000010004002005c00000380020004005001800100700020004002003400b001c00000000020008001002000000100090008004000400b000400b000000f000000c0090000001400f0000005000801300000000004004001400100000000004004000400100000050000014000c0190028006002400500040010000002003000100140000000012000800d00040020018003000800000100020020001003c0000004001000401b0048000008c00100040000000000005c0030018001009000100180000040004001c025000000100380000014002000400700000020004003000c005000000000180020000004000000400040080010002001400200080000000000001800000000000004001000800000040000000001000000000040000000009000c0000030007001000200040000004000000000d0000000001000c000000300180000000003000000000080170004003001800400240030014002000000b00000080010001001c003000400000000010004001000400b001400000000000018001002c000000400a0004000000800400080000000014000c002001800900000150000001000000a0000000000000600380000004008003000200180030004005002400000000030004005000c00300100000010000002000000200100014000002c00000040020004002000400000080000004004001c0030018002000800000080130008004000000000080000024009000400000000300004006000000000000000000026000c0000000004003000700000010040010000000500000020000000001801500000050000012000000000140080000000000400700080000004010000c0090000006004c000000c0030008004000000100540090010005001c008000c006001000300080030000001004800200000000014004001800500480090000003000800b00040000028000000000100040000010003000000e00000010004000000c00300000000020000000000300000010030001001000200080000000002000c0030008003000800500000040040000000800200380010004001000000d0014004000c010002c002000c002000c00a00000070000001002000e00080060004005000400800040000008000000c005001800700080120000001000000700040130018000000c0000014008000800000080000000001000000100000000000000000c004000000600040030000009000000000080000008002000801b0000000003800200340000
  | 44 => 0x11000401f0008003000c000000000600100010004005002c0070010001003400900000080000000001800300000020020000007c01b00140050000001000c00000000070064005000000300580000000007001c00100000050000003000400400100000000019000000100200020004004000800700040040004003000c000002c002004800100040080004000000000b001c000000c0000074001002000300180000004001001c0000000010000c0040000005001800000200030000016001c000000400e00140060000003001800100200020000009000400e00040000000002000c000000800100000000004005000800300000000000011001800000280010034003003c00100100000000000001800b00400000000002000400200040030004003001800100a000e00080000004002000801400080050000002004c00000000080000000001c0060000004001c00c001c0000034000000800000000000058005002400100040010000004000400100100030004000000800000840010000002002c005002000100140000004005003800000100030000008000000000000030010000004c0000000000000400a0018000000c002001801b0030000000c001000c001000401f001000f00280010000000000000b0008000000000b004000f0008000001800a002000200040010004003000c00b0020000000000200000010004002000000600000120044007002400200080000024000001001400300030018000000000000200100038017002c000000000b000000b000800a0004014000800b0008003000800b00040040004000000000000600060030000000000000040000000000000000400040060000000003c0050048000000000b0030024001000f0000002000000800080090008001001000000000040008001000c01e0000004001800000200000048000000c017000000000080020000008000c010000000100100040000000005400400080010000003000000200140000008000000000400000000014003002404800040000000001000800000000000000000000c000000000d000800000040000014004000c000002400a00100020000000000800000a00000008000000401b00040050000004001400000040140000014000c00100080090028011001400000080060018000000801b00140000068000000000200040080004000001400700000030004006000000900140030004000000c000000400200000030004004001000200180000004006000400500200000004004000000900d800d0058001000c0010004001000c000001001c0008002000c0060020006005c004000c002000000100340000008003001400c0000000000000d000400000040020000008000800200200010000000002c0030000008006c0010000
  | 45 => 0x801100200010000000000000e0004000001000000300010000001000400a000000300080000000007000c001003000d002400000040000000001000c0070000003001400100140010000001001400a000c000000400200040030004000000c00e0000005000000000000030040004002c00100040010000000000000000100000010004000c00d00100010018005000000500080010028000000c0000014001000c0040000038002800200100070004018000400e000000000040030048001000000c000000000000060000002000400100640000018002001800000b0001000000000000000014000002000000000110028001001000500000010014006000000300000010004000000c01b004c0220004004000800200000000000001000400c0028000000000300180070000000002400500540070068004000000000180040024003001400e0004012000c001000000b0000000001400b00000010034000000000000040020004000003000a0000002000400000000090018000002c00e000400300040000000000002c00a00000050000000000401a000000100140010000003003c0000000007000400300280000004000001000f000000b000c0020008000001000500000000000003000400100640100008003001000a001001b0004000000800a0020003001c015000400100040010008005001000d001000e0000002000000b00040030014000001801a0004003000800200180000008009000401a000800c000000e00100000004002001400100000020000006000400000000030008026000800000000040010002000c001001000a0004000000c001000000600080030010002003c00400540000008000004000200140040048000002801700140000000027000c00400000000010011000000400100000000001002c00a00000030008000000c00000000000000000000800c00000000000000000c005000401200180000000018000400a002800c000c001000000400080010018000000000b000000000040000000003000000400040000028018000000100000040000005000400000100010000000000c00d00000010034001000c009001c000001800e000400400040100000002001000300040000004006000800000000030010001005c0000008000000000000000020000001000000000000000014006007c0030010014000000100080030020000000c003000c0030010011002800000180000058002000c004003c000000400200000030000002000c00300100000028004000c0000000002001000100000050000006000800200180000000002001400700040080000000000c0000014001000400300440000030000001400700140020008006000400200480090000000001400000040010000001002000c00000010000000
  | 46 => 0x800240000000017000c004000000200000010000000000000a0004002000000100000070000006000000000000000028001000000200000000000004002000200000040000003002c002000000500300020000003000000400140040000000000800100100020004027001000200580020004003000c0000010005000000000240010000002000800000040000008001004c0070000008000000000280000028000001c00900140000000007001c0010008000001800000080000090004000800800040010000001000000000000050000000000400600080000000003001000200000050018000000c000000c01a002c00200100050000005003001e002c000000c001000000e00000030034003000400900100000020006000c0040000001000c0000000001000c004002400400180030008017000000000080010004008000800000000000010006002800000040060000002000000100140480008001000c003000400000240000004000003800200380240018008003000000040000000001000c01800000000024003000800000080110010004001000300380060020009000000300080140060015000000b000000300580000010006000400f000400100040000000000000002d00140000000029000800000580020064001000000500000000030014000c017001c01000280000004001001800b0024000001400000200000054000002400000380000004000000000a003400000080000040000000800200bc0130020006000000000000210004000001000e0004001000800100000000000003000002a000001200200000000000000000300040060000006000000c000800500140010010000001c009000000c000000100680020014000000000000080000000000000000300140000000002000000a000c009000000d0000003000000000000110008005002800000000070034000000c0020014001001400000000000014000000400000300060000005005c0110000000000402c00100000004003002c00e000400200100000048000000800a00100000000001000800400000000068012000c00e00000000004004000800500100060000003001c00100080000000000002001500100000004002002400800080080000005000400000100090014008000400800200100000000001000700000040044000000c00000100000010001000000200100070004004001000500000030000005001802a00080040000006000c0020030008000000000000040000005003800300200000004005001400000200080000001000000a00000000008002000400100600020060002000800100000020010000002000c000000000040000000013000000f0028001002c00100080000050001001c00500080040004008000800100100000004001000
  | 47 => 0x6f80ae18c3181c0000992167939aa00486eb0ad43f5439e068e9e3f02680000ac7000000008454c43239700000000d270000024c2c84dc89f271b0e8de80258c9320440b2c4b58f20200e0000a470ef800000ffc703000013e22bd0e55972a42b0779cdba8000141c648c8a9885f0000000110c8f7d0000502000000050004000000c00600000020010001000000200000010004008001000200140060004007000c0040000000000c0010040001001800100000050000017000c00900000000024001000000000200030000002001c001000800000000010004004002c005000000100080020000000000c0040008006000400000180000004019000400000140000000002000000d00040010044000000800d000c01500000000018004000000a00880050004002004400c001c00000000000000001000800a000c00d00000000000000001c00300000000014000000c0080004000000000500040000014000003000d000400000000170000001000c00d0000005000000a000000400040040004001001c0030048008000c003000000100080010018000000000800300010000006001c007000000a003000000100040024003000c00100240000004004000000200000170008005000000000000000000000000000b0010005000400000080010014002005c0020004000003c00300000000024000000000000240020008012003400100000030014001001000500140030008000001000c0034001000c000000c0000010005002c00000040000020000000800000040010000001000c00400000000010019003c012004000100000040010001001400d00100000008005001001600180000020007000c00200000000000000002400000100000000000000c00600080000000000002000000000040008000000001f0000001000001800000000000002000800800000050004003000c013002000f000000a001400900180000010011003000000140000004005000000100000070000008000c0030000007000000000100070004019001000200080050010000000000c0034001000000400140000010004000c0050008000002000200000000000003001c0030018001000c00100040020038000001c0000000007000c0090000001000400300000010004008000c0080010009001000d00000000028005004000000000030000002001401b000c00500000000010000004400000700000000002000400c00040010000001000000000000000054004000000a000000000080020000006000c005001c0040004001000000f000c0040000004000000c00000020034007003c02c00180000004002000400400040160000000001c00300200000004003000c000000400000080090000004000001900140000010008000000100000000034000000000
  | 48 => 0x36a400011741510379c00003900000000000000000000000057680000000777cf80800000003fa053e890f000025b80000000000010483b50000131a0000000000029766120000000000004de4a7804442c8a51f433612c73cc063c80b3000000000000e1816320dbc00000000007087400003c0104800006d50acb18b0074a8824000234f00005eac000134e00006b144ee016d42fe867903b8434000002e406c800000000000d120e5a00002108000000000000000000078b00008f940000c5441b00000b9d80003d2c1134e2695e505de00002f714473ab0654864c800005fa6b08000000027d45d8c00000003172000038080003d404af446f176116aa4b3c00009800d5e1aec0000073004a2764b6987a920ee06e0bc41e9823247c0d16800000000000086f06c727040000d6d0c3611d47af800000003cc6330c000000009cc51f87441d2e3bfe4bd90ce80000000000016b1e230b92137c1c600000414758800000000626026ca3217ef0d987de0000035a21e634e8e0421733b9c6ab86c9967221ae0000a098c1911a030c0e500fe5445854847fd076011248eb013083fe0b6c82a422b150e167c5ee0a9e1a342a2414905228b87107e84acee41e702f6a44641c8a3071e566f4c7aa1938283a509cb98218f1d723e200c105650000000066e010a40260618c9287b90dae000000000000000706808b1a6b0c2800000000000231400001cb800027f073940d4070022f2000085f9f4000120f0824000cf0e321a6400000001b0600000000000000000011820b1527282dc0e101333350a792832496462cb025e4eab0a0c0c5000004d3800010580000000000038c216a800003632dc600007e480003e5c74100000f1b000039ec00015cf0f400000000188300000c50785848b10c4000014d171f0000494ce14125f2f7e000000000c900003dd0000000000008c640000324000047e400010a935b0089cf6a97be2ebc3ecc9eb921b1f7a89c89c2a067000000000001a1100006dfcc3b109000000000000201a000000000001d720000000080520ea000000003118000150e000061b800042dc0000000022900002ed41de000000000cc05d5086f0000874ce11000014de19402d582ce00003a9907f90973c6002987b71a503b207750cfd908b10ac0954a7223422b8e3f3c000210a000000000000000441600000001b0631aa0000e6297a70000000000000000000178c0000000000015445a29d930000359890c1b7d00ba8bc4ef101e520f848a8cc60000408e085400015c9468e0008ccf85c4054a0000c9d80003b3a3e0c000065f000000006dd962724086cf4000025c3b8000007a300000ed025981d60000000000000000bc900000000000075800000290b671ba83566258c49e1b152aa0000108480000d86789465b1ca921ce8
  | 49 => 0x4e583b100008124c551236314e0000c301f8c3b823c8ca40000006c200002a914730f3c00000001ddb00000cb89d98c650000000000000002206000000012ab2b38000063aa1360000000000000003a24405ca26a39b09ee22c800f213d329625fc084800029548c4cf21a05f010e2274000202a00003878eaa800000000000031000043f400005188000000017ac05e0000243400000000000349a00008b9000000001f000000a13152a6398eb69091000046dc6371c4b000025e800000000b34885000000000000352116507a62fb444590708dd000000000ec28e4d33da154ccc7040e000059d4000000000000000000000039f451948698000120c0000f7c0bca447a00000000000334e0000000057300000860f6b80000000000035f872f06621ba8b3204d324b61ce40000cc9466e0000a2f800031240000000134c19388d1005f9c7d38ec6461121000004b221fc0002198000000008d9223e234e68e4f1714c22b10768c94d157635ea50a0f32888616141d341589fdf109c07d43cd93f900001ec0a1610df246871e0dcc0fb91382831cfa8996d1a2c53b82b42305024e2e64f4a9a6c0948352c6fa8fd71a601f7cce394e53d6687885c807d43cfe00011259eb21de64f580001fb30000000000012460bb4017c644000004fe8ae42e8000011ba00000000000000060c800002c400004d7ca2d0b9100000000f1e934d3d3a0000bd09aed3d4a2f7474c800000000000000000000000000000000000000000000000000000000c29042d407c0000b4184cc10e80b480000717114000003b80000021c121497e15d20218000042c078643ee8ab022996ed259268dcb5e12da1062707000008cf421a00005888a8c477600000000e8f40025ec08d48000330649700000000144e7dfce65800000000000000000000003ac4ce623c90ba25c940001c0e0000000016314970000000000006e400002d7101580003b348c88000167b3734000080f837d00000000000128200006eb0000133e3f080000bde22e51f364b804968ee400004634a5a00003d620c58c4e1ce03b066e9c11318e1182e73248561e9200001be020a000036180000abf000016644ec400020e411a8136074d84e1194a00004919160308e3618000000039760470000000010f43d7458b89a51d54277ca02000000002adc01c000000000000000000000000000d8c004023e40000f2b020f00000000000126c055400008a80000226020a8c4798050000826c000000034b8000000018151d78000076a22c50e8e00000000000000030e893283e8000028b8000000032ba3ff4000185e37925558000228700000ac1087159930c27eb0bf19f872f481bf83410000000000000001f960ece6968b9ca04c008e0000a48000000aa7c8cc2c000020a85a900000000000000000000
  | 50 => 0x800000002ff045f853235bc00000998e042e587630611000013643140cbc800000005594000201e00000000b2a8566000012cc00017d4022600000000000000003b0e6e1e0a3d820000000161a2cce00009ff800037b22c001430e631ad63338626000030486b451529aa945d85a0005184bb470a0958ae01e7c150c2f103cb842519ce08b4b050ae3367e3448b4d8f0100002a2d132000012a20714d0b000010380001128188e2d7a05f44c304ff00000000aa307b60000721030e0e24415e6c68b2f00000000000089090f500002ef05a60d262d5a0dbc7d88fcb1c600000e1b9d602eca79c8a3a9f9b0ace7b3cf56920639ba7f8cb001bc3134c56b805f09e20c5a5078c0915801196123cc569f6c2438664c0e82107408a00000c085d8461271c0000000000000000000000c1da2530ca16a33424c000006dc8581000060fc000111c19340000000005600000000000096c1b7e532400000003a7030b40000000114a0000053889300000e141ab866939bc8c300000bb3356c78401ce097106f08f3868207d1291e01ec000000044f600000000000351a31703d99794251a000000017c72a440000d3f1e0e0e622ae0000000000000ba4659800001821fa80001dc60c7c6084000000000000000b8208e929567a18abc0bc5216c0590bf585d911fe5c482e0053016026024c8c985c2bde59681db8263256e49b4d531e3639c850b8101a0c92ae4000018200001bb6133c74d1384429a00000000000000017fc000196800005d04b7604233c640620bab11d043c60000000145000008e60fce000007f2253863603f3026a0db8bc1000000001fe40000a9d0000237c4c480004382000000017aa000000647f200000000429cfea8d611e840000000104301160e00b559e4525060fd0e85896f068c5fec93211011fa214510d188b63ce2000000001f108c04ed44e200dd143e81f01ef104a2142244000014b621244da000019150b7e0000ed619091e20809504621a211e044d87b800000000000000010410000000054b0000000061cc00000003c2c1cf1179004d0000070d1cd000001f800000001efb2d863ab504000af22ee32d48929da540b8789c2138a34200243a8256a26b182000000000000312a86a420d800000008b44707800031e61aa8000000040040000000000000006d24000000000004ae0000026b0000000116a14201d6419e8db113371a1014d476e117d2b4c1138aab94de09321f34bcf03a400006d7000000000eb88be8000163502f45fb893e800005746708cca0b2d1432000000012dc000053f4d8a088d308043d91bb8cc03fc20000342808d437e00009e104b11e3c00009250000000004e42f50000000005e06cc20120a663c98aae000047420000000000016282ec0ded000001ce4a986159ce600006e0c12a00000000
  | 51 => 0xc8b0000007d300000000fc493fc41227ff030c188700002934aaa00000000414800000001ace0218000211f000000000000030000000005561bee000000005882383000000000000abf1cfc3110f4f8e6d372a2014f7993c4193c2f04b17000033300a78000237500000000ad3a1bd172a00000000d50393c74584f707352a4e000018085e6432e71b86951b9f0000000059e80000000000028b15af0000808c16d0000000000000000000000087700000e10000064cc000165737a800000000f250000000060d18ca2c98000039b9cd42b8474f43760838085e126c73321000e300cccce90a5c0f5c7f1c10e84910ebe195087a011b02ee89d46a1982a2b3e6ac51ad0fa90034635c93585e5000063744e4827900000000ee500002c4a88807d580001bee0000b1f8f0913e431e899005103cd282901a512c50c7e3494f90000032787c240001a20365a314c6df000010c8601c4da842229a60000cbd8171433817f400014b10672166c4309f10000056c00000bc81af0681c829a0b1424a62584aba13b140617d478016c5000015080000c23018a71c808a800010c000000000000000000000000000475a000003199d52d5c2b9400011bb0f445208e89a0953bb46f08ef5824c0cba5f4494a23741ede813400005c20fb40000000000000003d4cba2842400000000000000005703df06d9000000003ffc3200fea00000d14000000006523414000000000005f2519aa382000006943a900000e6008ec0000000000067a05bb859c000037e8f6698c50e52597ca9787ad44c646e80001f57000008f86be800000005d50cd300001ca8150c9079d7e1a5a2214ca803a0000020ccb271ff43958378000000001ce041400000000406a5374ea31b9c33d83f6907c9b9300004fc900b0bae0c027094d8e20722a520000ce300002b4a0000913000000000000f72800000000000c76800000004ded1db84c247725fa119895340d340000000062a375a000000003a807d68fa00001aca47bc7224fc71b070c0e2674fe6966e00007ae8f23150924c64d906ba9e5323fc8cc04a8153f460442c452798b3335a61a47f09c48473e3f0c7e600003f168efc0002015000000002228ee30000489c000075a29d80000000000017560000000000000001c5000000000fe866410c2000018ec0000a810ef245a4000054c17681f003fc8ed70544088e71ec00009e44094795066285b9395e04740001109177c000069d800033e800006b88d17067a00010db96ba452818c87db865e000086cc07d8f073e2c7a34000201800005138000000036e200004f2800024de2148ab6953a000004f0a0c010109521f850830a6943764e1c9f395bc09943d142308952000061a000000001c625edcf70000000000000000000000000000bda00002fe200004059db9000054311c5
  | 52 => 0x30e44d8ce2e900f3a3c88446af81532b0831e49e00c211ff00cb06db05b420304f951a0090c1fc45508e2d0cde21505a1c9df840c1f200ebc42593583a741ebca1f1a8817b26430a390a81265647644d404891b9051248ec2112087a8b68fb5020645240000c0c88692d1c00005e599f31eae89d8f5e195a000050e08061c593c485ab0b4484cd46be65180a9053a0f942ab832d800020cc552400018a63f6c6879027800021e253cc0001417000000000000000000000010b49654387062ac9c5916e45363465093800000000000000186c43b082142408106304e2b891b28000000000000d7000025020000000235618b61560454217c20be4594cfe058900008b2c1f300001dce6d8000014b23be40000c74227d20b600001e3000000000000cad8a6535c80001154148615f86c48c921ed82bee12b0000000000000b6d1b8000001e0379803e89cd01c82ac8e66a2283d8e578094b1f4717d805341f21b05220c1f6c29d83ec0dc6061c40692d725d28d7506e800000000000000000046520000fed0967061c353891f800028bc00002d90e47120082246bf05592e426f6cedb0ea22ed2302456ba1ae000015783098f8c1f1e5834b8093cd11b6844d19e18b2000070ac0000c021ed65554d3a800003fe000000020080ae817e00558b6400000000000236c00000000000087943906150e428e8d0000000012b9d1704ee18400001e1f31c000009310cfd00005d5ce7d800008720dc0edf085a01980000b061dea007404785651a991d262b9809e9a1517fc3e1c0000000343a0ec85ec0f1f28f8146837a000000000000e5a09b3000000000000cba38a24d00e1d8a520a246cad0a70c45000000003d5a3990000400863588c244e600000000e2100004ea800005cb0abe23846e380003fbc48f8c00856d0ecc15d40fc8000127c03e800020c00d9a3c849c0000000006110000000029d0683810d1ad400000000000000014743de865780000000526cffe800046a03e68000195627d02f4433000343fa681e4e84862706fe48dcb24200702065f483a0840b00002d6416698230cc83b48a5192903f3200010ef86fa00008570ca392d80000794906a12e100006ff90f680001ac811311c820bc064a000000014fe0000120c000000000000000c8d92ba2d38000000007a400000000000000000000000a601407225610ac36c0c3208144b0d0fe9d142776242400016c71548198498900000000492c01a89e331302d2519d17fa1d7409b449004c4041a89b4570927141ca5b34bb699bc31323a548af21eb1c8c188117b16703c6e5158eb313b6408666d401392ce0fae03e015116222a621b7483499fa2e0e8174a121bb10fe0510cf06957934007ce4f99925d1af68f58000000037764070cd28d5c3caa4778c5d8564153e6d7c67b903713f
  | 53 => 0x214866060419b63e64000000024b40000022000023ba683c000000000000000000000026c200002c1000023d21260add2247000076040001ac3000000004a00fbb471e000000000001d3c21c40001943000082390bc181b00000000fd780003b668698000000000005ca00001d2200000000000109d3fb2000000000001cc26b8c96f869c431000007170dd23110812c0000000166800000000000253e16bcc80047a2eba692c22d12b6396600010c3a17700008098aec0ca736940000a0823c20000000091400002d4270d8000000000000000000000000004dc8000000000e200000000b371d0c54540000000000000000000a101c50000000000000000165403200003df46adc7e80f692c7600003fc1a82000000000001b3600001ed109c162f000000011ce9d431cbe31444689ace00000000bd6000027a40000000177611740000000114f000042f91b20000079a8250000224a2c360000efb10611c742f7843c01932c16355427a9573177e67f80f01cee2c2c620404e19cf023e07703ca03c820e87744019836a17104ec0000106d00000000000000000007d70fe883e900001920219a0fd000005611e180000000000000019030cc4210c5271ae2269e05bcefb97f800006924b300e0a00000000e9a8000231200000000c1d45ba8554000000000005fdc000000000007384a52800000004a7000000003252000054492d50000256c1e7227c00004df81f7000019c43e4c04995a3000070e509080002d9015580001ca50000089109807cc1f940000d218000011c0000966857d000000000000000173e000000000002a002468df31367142c000000001fc423a00000000000000062504fd8000194029e8000000034e60000000111f292210c010b9ee125ca57ace319a10241c6e284ee84b43204236863e844b000000000000de400000978c788c4d2564000077b0fb00f8830d0000000013d60000eb38000367232f864509a025d4142c1ee940d4126263104798e4463c00006399d733ee81a3400000000afc727cfbd80ee053e00000000da6000038f4514838e0000761c70a0a060d7c55a400000001fb02dd00001d2f11620000000000007ea6b341919bd5000017f86ce009e000062e0000039f16f000000000000000000000001c4000003dd4000000000002104de70000114209b8db5919739ec49007069cb6185018bc4fb07f610ea8524a1296f3239e4fa476e818f1ec852c00001ef63ca25dd45a312f142fc5305004924821f464c000021721ed800006ff00001d0a00011998411214a30fc2c5860225e8507cf18835100005958f148000092074f8000000000003a58ebd19590000100c00000001e2800000000000000008a0000227a00005cb4b0f9d2d0000000099b18671a004814000000000000000c648d3500005b2400
  | 54 => 0x4200004408000000000000000000000017de465600008f108b9317a000038d06b70000660075a97f5000080400001c2f3f88466cb340dd92b8c0f54f6216861ada5d08fcea3c1321437b000018431f4c1274a25075b0000000039305e03ffe7e80fd11d2c00000000d508fa3147c000000021181cea85d8000162a00002e286fb0b6f1dac00001a18000310400003ec881f17d40000f7e15160000739c9392161000025b44329e12419e27cce5d0000327200000000000000011411641e47260a0000d97133900007f804b200c400000504b781a92444e5b3c7ec9d6e43506aa0bbc14e2092a03886e2849a3aea81ec42a885b0fda5b811721e2f3b7401d8010888712224dacf8f094806ca55fc10a0be827f659a8d3805e106ec7a1c89d9d0a0b5c000000004bc2e7433f8000000032c00848ee208c0069e0000f2f00000000000000000001df65d3c000000037ce73a00000059000000000000b8f223c1a740218d5835e21c38000000000000001019a1e541c431dc9a480001b781ca093493ae00002868c0a0914016e1aa4eef03e1246a87d493089c000007cfc00021de012838f04b08004320a558c0001da00f260d24b3600000000032c0ef8000447e000000000000000348400000003be6265800000003cc8252c3ab8432000055d45f485b03020000094984ef23b646f8dbf06ac2b300000000000029cc4aa49cd80002a9c70307390000363a2c4c0000000000000000ad052342a640d0d4f0f383e5450391b480000000000000009bd0802003c000000000003dc800023230e4a000053f80000000467000001082c4c8ca80001618000000000000e5c1a7a47f49210000000000000000f28231019d8f9880000000821896590d40000585400014f700000e4805881f62ee86a6000000002e5e41f4908214a44fc2620f9493460b628634d7714941b2800000001151209e00000001f69217a79cc00011b12ad4701d14c0fee2e6e7df824b238129987fc06be19870fa4198c00011df33700000aea80002d3a3de504500000faa3288000056b00008c680000e91366e12d84e3901300002f4046e0b1f13ac116062f9663000038d000000002f96361472415920fee00011580a072f0c0000787800000001774110800033927d4c3cb00001b180000cf0007e29061b091e30f033f78456c5ad012e1d0e0000551a3aa103214c4e0300000a8c3b6819b1fdd092e19280002190034c0000000000032d20000000000006760904dce80001c80829478a800037ae42680000e4313f28aacf9600001f58852027e00000000271400006750d2808e47619cdf00000000e300000000058cc000000000007d408ae8c60457633344db9b533554000070c8b29038e2b0c7fc9dc20000000081918cc0274468c000172339621d20fbb8aec136880c04c8225900
  | 55 => 0x67e4eac0af80000000055898e91a825fc000000000003a4e00008ac051e426600006e68b63000000001dd0000471a0000000000030b62b087529c10323a8a24000186a44cc3f540000000000041fcf5080001d960001079191a3990000000018343f040000ce29b5d0000000000019db067c0000000000016b00000966223c000000000000000000000011991dc5000072fc4ca0000362613e4b8c9a293ae26fa4d72997f00008a5caf086e508825be8dd998fd37f6000086122103d122814000043800002f3cbd68ccf0444000086d1cd829c64448dbc073d0a2a000019a8a843f76444c0000c5e075c81689ed15710b480000000081003780000000118118020464233800019820000d4398a23800294079f99822e802298ec518de41f0318c175234d00004e1800000002d200000000000030de21ec30c800000007f9c62e98740000358000008123a620e0c0051ce913f400007e0a1f200000000000232f0000000088e80000d4a7f981561d240e644b2000023cd185c00009f8041600000000614800038982cb0000000044ba7d940000000000011e4e12000030260bd8000026c00000001118000042de4a3ce99800022707f941768140000006f8ea880002a9e6bcc55a8af300002ed0e6918fb050e8e10000076917ae007070d0a8e0000186836496840d1e60bcee39b8c36b63e7c00005e2129a11a8a8f83e3122c80ec34f000033f080d840619220000443800000003f2868e08468000367400000000000000052e4a0b009905e4078400000002a96076055680a5000015a917c029702e8240908f15383d0a4ab0381106a000062b0c6f94030000592800023e100005e34b740000000000008a100000000155055e8000000033d9091800000000000e3d00000000150022a00001e34720ceae000000000000a19a2d60da81fbc3f1086a000000000000000000072080000d4014460000ba6a1e12b2600010b380000000585c0001d63000016441ec144f00000000d7e8f8d419600b90508ad500008d2ca66948d0f466b80457a24319e608300000000000086a80000000086e00010000000000041cc000000032e4866446b0000160c5f3ca5f0b842a9488180000afb1e4400000000e5200004a8800005552f82000039a0000207074f00000000000015041be000019e40be11e38131377e000023f1da6090c000041700001b9e2e780000ec8051068fc00000000000464c00000002e383d8000015c1000000011b18000000056501642373000000011778e741ae848cc157000000b82ae400011a000000000000000027960000000182d00008ecc000015b00001e38f87000003222d850b28f27000000000002159454e1c748bd000000000000e098ab0000000000000000000085c4633019c1f648978000000000008b3cb019bf427e82ff43
  | 56 => 0xfb7101e3ca0464461280000000000000008d82b6a57d8000000000001738000218c216806e88138ad2307400000001251450c0000af498223a8a4c3400004ed2be4134495a000043348b6505c0e5636f21ff00a21fd208120000b410a5339f01bc800010943a0a8c7c2871b16278a1c20000000032ca66c4a44031f11c045050c884c01e2e0d789239e0244aa6fb45c311220b2c48640610ec534cc32b0c2e8b5b41241ef80000b8d28d619082358000016440ac707157d25a805d486593021476000000016960000786d0580ff411380434ad99e9b1fbe6ccd1670c1f3356000000012ec1f0a0000cd08000355a47ec00000000000000000016db3de812c02fb800000000000000109e0000000000008fc3eb6334c8f29c0f03440a38c7f95e3000037a83b21b233dc833c00000000000069c40001e4b349400000000000000000004c111ff00006790d960000000032c86bd1b57052454981c7802246a6223114f87ce11007ac01b9a07d20e41f0c1609f0b064287d0d9d8000000053ec1860000191878ec102022c0000000052b800000002c64e358f4f3db6000000001f0000024c8ab110e8000032a03d3800017306798df298a41c565bac00013110000303c0001161000083390af00000798473800000000000440800016a71e2600009680000000049dca5d000000000000b7d911400000000af980000000000000000001b1200001e0836845fa6098000000000000000000000032fa0000000000040f400008b782fc360411dc0001166210c6dbc00019e2208e285c7518cff00006d98a541adc36b4860c735951a1a788c7445993511d4000000001a572476000ce2a1bc4000049c0fcf9a6816062e14b9700002b7c82dd0331fbf312e4280f198ccc3e0045d47980000332c0a58e5683b402d6000029e8c87000040e87b51b31052020e8ef40e582f3a20d04a4a22335d46e0087c9e0605b84ff4d2104732d444d5c3f38000286443f0f2000000000000013c00000000000000020ad40b28958c80800015ee000052e912806be02b8153800000000ee4ebf80003d224254898800047c6000065da0df00004db851e1f7c306c249cf8c2105388c8194422859f08d835e48db12bb05c400000000000000024bc00000000000091067301a407920000bb899d000005e440001e8b136c13d885a800000006774cd9000000008508faa8827000000003d8820e000033950731d980000000060d9be129d40dad03f8aea2f7a00000fd8000390e4f6c000000033460000000000000007ad11a3000000006ee80c695d700007a3911b08a700004a901bf1316446a54406d119d3158e349c9270ec427ee1f04025000047180000000000000f8000000000000000765caeda117000054dc1c68f62000000010ca87fe38cc000017c8b7f000000010480c411
  | 57 => 0x2ed85534021000031b058081c49fc907080000000113a02966fcc00000000000000093a1437137664e844ba2bf23f41c34d3500001fd8079c0000000260600004c88000206a00000ff192811ec19640000e571cc43b24a351d1b29b673d054d035900000000ff40a7b2130700800013fa264a2da4000083e00001c8477f0f05008c7d040001e4c38d416cc00010f734c846b0ae2172013f809d0851060d00005cd410899e10000348902920d914500000000113e000000000000000000000004d0800034fe3dcc00015f4000068f80001ecb0f1800006f914c614ec000058b1ec040d237288e880000000235cf688a2a0ac472a000021da3cf03b805e980000e7c4f4c000102c000007203bd800000007c745f68850107651a400023d30000688498c94fc42ac534889e800011308bec000000000000aac0001a31299600004ae80000d567bac1e8010f2d5e283cc27014200003a280001aaf0000432458f1560459200000d495411ba27288fd5908e171c73f400022f4251216ec000000025541f70d09170b29ae0ea454a0d2843ec7d747961ad9037600009d200001a0c0000c0c18ec2ece2b780001a4c0000000097921c219f62b38000000026900000433800047a80000a3d800012b40000e16800014ee0ed8000000000008cb8ebc999a000000000000bff0000396cf55000000000000358989d3544000009b9fa731ea10345eb10c83942412cdf894a9210e0000ae620de377a4b78b7c9d1a000000000d091451c846fb1096000000000000000223900000000577843e00002208000039e0000000015b947422b41a2cf101e261908000000000000d120000e1a000023ae154107005c545c48be4ff59377367000005d215a009421e601a42258000000007c7065a00dc4d8055780000e164854aa200000a5c25c88b80000014214ac0000000018e2084000018b000000009398000333a62d02728d8a000048e11c4800019a8833074609f4187a0414000000005360000e5f1ad7097c4158e3422cd000000010d0188c000088bc6fa041900003dd8bb50cd847a232080000000000054500000000341a5bf4000000007fa000000000000000000000000b31efe1210000194d41f65160d7306c100005b1911580750000899cf2706360dc0373063a23ca29da5e048211be800006da87750000027e00008f8052f0000273892680003cd400000000000000074a0000000000000000c8700740000000000015e626a400000000201248a5d98f40a28b201062bc9f789b8276e11f0bb80c3b16a600000001501000018f400023c5000060b000000000000448c00019df133c8e58f0d0d7f1a7284f8c368000417a370c00000000000000012380000000000104f00000000000000008e70000800cc388e6034783e88000000027b200008fc01a30dc20a8c
  | 58 => 0x855300000000770c00006b5089e000000014dc00001dd4f1692222d3e09742d0a163389c26f84d8220a35d6494000021a700000000000000031a24724a5c14bc45040000000092a25601a900000000025089881a38000383e2a80a4389a400000000000031205286fe800001ad0000000067700001dc40000652000017b805a03bf9cb514aa5d805fb80001a1e62f0000000020202a0d0c089ca40e6000000000000a267964e6180002930325000018c2268e296804e857011f087448d28a631d507ce8c0f104c322400000000b1d215649f85c49b9900000000633890b0000000000009c8191e000069892311f507d90d84930a326a03a80fe8a111ea08f206b510993724275c0001d92000067b8a8c000000000d9c0cc91d500008574c71a0613bc679a0000073b00000e8800000001eb00000153000000005f18caf81d53b048090dd8189e0e3653fca078cf13a886ebc5529eb8000074d00f497e53be000006cb217a20166214b2c800015780000bc9057100000000b258f0d16e20f5caad0936115c5ec85be8000000002d50318889000006c4f3a0c6805800000c3a8c42000017e8000000025fe2c3400007f1425e000001894d834c222dc000110a3bf01e7c8411b44325c21990b804f81d9c6f90b7a107a00000000fd6a1d934ba58b4fdd17a600008d28d1b0e2f105a4d7006d960e36c261440000fe029447c546f822fe32f821189f9850032226528dbd00ed2a6a011401320d106500000000000035821e7429b180e3bae00000001a8438ca65200619fbd00007a8c00000001a36000103a00000b5071d00000f4700001aa0c6700002a8a55bc33fa1c531742be4e39955b201c76a8d170b4a0f1a00000e4907b39f8000039b1ec545dc00000190253373669b8ff90000000000005b504d920600a08000224e103a00001ae800833140000e6b84932b564f2857d00000000886cfb406982e7a1b004c98000122e00001a090aa000010b800002b6170050281288000000046a835b0000239600000000537219c00000000a1c000005f0124800000006814000093a3ad02bc40000823437884fc00000831e680000fd08814057c000000000000000000000015c300000000b6f165d14d800007ee00002758000111a11240c0c2ce415914e029c20000a491bc7000008dc8998ad0156c5ac101e8000000033ac000219b000000000000000000002b000000001c6689bc000000000000d9008d00e6000076f00000000402e000098c0000138c00002eb0bf92e9200043aa94f1091c0000c14000007e476246fc000036ce0000b818df9000000002e1800000000000000000000002d409ef026700007104000000000008968c1887dd2f5c7d481e998a016cc25101869a463a0e21100c1945c000033a113292db393877f8d348c6f00bc3eb44850000
  | 59 => 0x61c4a000097198ef000000009759f6f3e7624785a6a29c00007b687778dfc32643ee0c3803a1077a887c0a781db0656437400011e400006c640fc00002cb83800903800039e600008d806381e5425a8bc51859357400007f300001cd03b1cb0984214552529d013977234584430ebb949a41663e28ffa8449080e2d5c80b09d338fe83ac00007c52ea60000eb221e4000046e0be81b0a289667bca288d7044660000ab41878000000001c500000f648acc0001ae83e4a80c4797000000000fecd7d20a007260000bad00f1206c5e6c5389cbc03406a54ba1850d3ec2000012f9d4200008bd4a42800000002b80000064f1a88320c264801127181bc4e6700000b1c0000000122f18c41c480000000006c515c00000003aec0000000081800003930edd80000000000000000001c72000000023b62faa00010789e6100000000f76965b3668000094289e0347662a40000b2b13cc0c60b518c9744e20000a57000023c2000073e800000002c2c0000b54000081bc3f318930a2e3cf864680000000650025c00003a0200006b48000118c70605468000000053a51749f070568703475611ed1a28087083a996a1b54342902a02233bc07760373022535be00011d221260f761cb4bd11f1b34ac5c5100e800000002ac50738000317c78f0000000000002f6c858018a000087f0382000000000c540000d8d000000011aa00ad412c00009b500003dbe000081f0557067000000ce80f3409c2c382f8024d3b4e6ca4b6c80000b7828040000d973f528190e25167c02648b5c6ef1a5f00000000000000000008ce0ad61baa433e3e791ee00b03e5e58482ed909f1c8241800000dbd27d801e4c1e09f810f8348c11e827645346d0c6a88000166c4dd0e33967321e00aa0b1e91ae28ec0ca84d1000542a07a5c8e11ccc42ea39ccbe404a3000004b000000000000000017716dc06048e8082aa0b22ac2000000000001b248b04d1809ed2ed6602cd401c3e45c6446c2f888a90b7a058889b8fb439240344d3103fa000000009e781a734263994ee69957000072dcd3c0000000000003b59ad62c1006dc00017992af60001053996e3a3e6294f5a95ad0cd48f54f828c81457c7e0c6f112d230fa000048c865200004bb496101143ae83f1c5f9800026760000000000000000000dde08b03d0612bcdfe818e000025cc65c8000142800000000bad2182433c00000001ad000000000f920000856800004e40d2200006000000000000006c792ad00000000663a2ad47288e4404b8000000000009e600000000000000000001c7c00002cc800000000001140137d0000000094c100400000000ce707e40000265c000193e32201b64bac80000000600cfa100000000586400013d036da09c80000f0242fa000000008b81f5c5adcfb91880401e04943ab093d27dc8e3
  | 60 => 0x3485b8000000000000001efd42080000675039d039e55e80000aeb326e000016795f027743d709441ba124ac1280a9c847408940000fd40be312ee8e980bc8d6f2dcc6df000010c7287a44006cd81c4002c00008220c7b29ea00007f494b50000000000013c60d2a59485f88000263421a02ef056101d013808fba2ea2a5c69143960ef011cc3be4ef69c8100006350b3c060812d00cb48cc89aa234c7f6c0a39ddd298e6e0431e0d320c7459b459305e801a600008e415431d080000516123c000000005698000000000005d10e4f2bda29f84c923551dd00000000000000005fd000000000000000000000000000000000000001102000000000000ddc5ea479d000023cc000000005a5147a78d0496173e00007b24c7b812d33540000fe01b4102922594a5780000a1e00011ce006d00000000000000032c420245810000189649a0000074f000018240000000000068f4e3b99b6000066148ae0e7a00000000201138d00006ed8bf00000344c00004ce1afe000002808d08b6c23e849e83fe998b2da270d4efe071e36a089181baa3a3418c7cb40002058252a000000000523b64747000000000176000000000000a1000002e6803900001404cd48ce317dc000000015fa41883ef0e0b0ab32456483000001180ad8865800021e9320c4dbc007128e176e30c49c91638438800000000f0624260000000122d149809ec07ca2b22a10742000000000000000000004eb0000000109b864d000002f40000000372e00000000db00ee400000f300002ee665043c400000000451c0000fc6403e8104000029c4228281113f98c03a3a335c0001ea700000000000000000008ba0fe10bef0000562450006e727344ca8091800006aa8888f7718cb0000000050e96491b3e00005bc800004100000de002c734b01b3835a00000000000050a899531a41f3d1d593a800004fac00000000dd04dd892483f7413059f8cdf8ea1432686c000000000000000031288e20000000000000003e3418740600f4326683bd11a282001bca27bc21e00001d0488e000002fe3d086a580480b97000089d067e193d0af445d90bda2db00000000a158000000000000001a8a1ad86d940000d592b161b1000010ca000038b1068003c1dd20000a0c832233665bc4cea13d53c125b940000d070000537c000080620467854dee124415743a480000000374a6a3c02a001d340c000000005fb03684dd4343192b36e4385ca4988b435d28288ea5237b00001898000014300000000d430efa0000175d0fc803f189e31c45922290396404d8a7d0dc6000028d800013c1019c4cf4f99112939a6413914980002d1e00000000d2e00000350000192100000e04d040000176c3d549c180000000661800000001eb40000980000034da11fcbeb8000000048c07ed800017724668b1f00b
  | 61 => 0xed083c33bceaf000000006dd0ef60000000051040000a9929ec0d3000017bb00000824000233f46c042e8fb3831a00006680e601169098e0000cd70192405a2098000230d0b8254a8c7a0888000004a887c00000d1832ac6680a41242c28e47a699cd000037b800008b5000000001300000377c000000000000000249918c00003b3800000000000440e1c547dd0e98000039a871f9eca125c10a91bea11642d665980aa955200005e4c1ec9089401c8c589938404274e3058beea37f394c6b2cac799771d84522c0001c2c467a1ea0000000000000c286c420550e12488089781072d6c5acc0001ac9072a8a150f88a5419b4386026d1e6f371a28803ef2388274466a00000000256a574c5f09de444822170be1124303ac32dc0001ee7000080440000895053200000001ee33262059486c9738032e6f80b3496b516900b78db980a20b1800005a79e4800002ec8d4d082f2fe62564164835447a00000536a01416c46c7d0da081a252400000000000261e6f4847c8a0832980000000000000004b109400000000008c40000000000044fc0001a280000163cff4877c137280289911a6028c4000000004a51d7e014c3c785e7342e377c4cfa1e031c42f9c000021b000088591150000000045b0000075344800000000000024a800001a8000043960000fbc80001f900000a4480000000000000000000000213000000002fb834d8000072b25a200000000000000065709de2341000000000000000000018003260000000006c035c1d6c2f204d2c16e9abd02ba42e4fe40000000057a90458d54000023bc00000003a764728aa000000b3000010f51139000000004759455218c00005f285903ebe00010a20000305c53686038df10000146115e1f561e6a661055a006620ce2f989be03fc33883118f9e800017c8000045e00003d0039bc40b080738860000b888696214817283680000000000003bb000000000b9cd5f9964000000007e7105c40d065c0b8118ee28543dc464480003a4a1428f3102ca05186a2c44b1ed21ac477a473f9a230000000000023711848000083112ef44ee15680001477082e1c811889495045e7d107b41d703de4551cd3a21b520665d30b5c22dc2d6477e8b1b230a032c51986d185032e88856c2788000434a00005a2047032ea02d015d805b230a0000b159fea387809c0e2496311486000053089db072c000000021b2121000010881edc0000000068580000e1e8a202930000046043f4f560a580ef47d6482d204623300000000000028520000000000008760000f9b87990c14000048d8000435e0000e71156b1bc6459cc4499d73fe23b0490100003c2272e49d0930602940000412055b42c0260435189bf0796000022fa35100007a3087f8abe18946ff09aa80002bf675f031c8bd43ab6066800000002c4288
  | 62 => 0x79c000000000000000aa4016305b000000000000028a00000000000131622a80001f1415d22c142df1fbe30b400000000f4a03540000000000001b861ec00000003d84270800017c5189241248c108c5006e4b5863215902b443e705c1989f32ce16d4000000014b28f1031a8bc20f7484b80001d7b195c00009ee13f62c5237380001c6d0000523044821c915361d88f71054b00f46cd4176150b03e87228eb7916807301ac8381970007707d243f40cdd070c83d08da84bf23983a740001af026a600006042154000000000000aa700000000000000033800000000000000000000000024240c48c40000000014f80000d0100000000705400000000000000063096a5126064200000ce425dc1b7c0ab800010643358e98000038a043400001cd941aa29d0000200422e6564400017e910526d7864e8000000037840650ae7000083680000000000000001b880001bb026645b70e4e337a00000000da70ab800006f5800000007f5c0f686b344260000e959bb209b858b11a186bd0000577071186a73cda89203e4823c205a0acd0439c8621660000b7210e423783808489096030d620d4b0a127606366a9cba880153cb63944613801f258068e86ae99e3054869211c91764033c7c110ff0c35000054cc0000e0c086261f8d0c1b2f01b00000ce09b4e11f6000112f80000ce20dc8c4d1fae00000000d49800014d68a8879e868e00005c6800021ee000076c47d500001b8879d8f9e0fd333ac2e505a023480000654c5a584b743b630f870f84cb2b687ed443691d62b48827076c901a4488241c3b092a00000000090b8f5f1eb200008a7000036f63ad0000077831905d540001a5b2bc400011b68f7700b055c00000000000000009cc93ad00001a2869980000d604b18b4c813e0000096888c1e0026bc0000000000000000000610023800000fbc00017841f6a6a9040780003d2624dcfc880a9000000000001d6b2dae195c000149600000000f441fcb2612000000015bd0f700b9000000001c4000000001aef30a000000000000000000000001cd6000007743f906ff00008bac00000000c4424c4d20117c2d165f64cf91395000000a5163998f21d63f00000000000000000f039ae100000000000131444102fac6ad1317182200008bc028a0000406c3bf02bf15222d4800000000a7014f8c93020b1ec21a5d066866e2c48000000004ee19b200000001dd635384190d460000255c00000000000265e1960c6811f600000000bf384a8000037b4255800013b42454d928c430000000000000000e705ba51b3800035d800002f2000000000000fd19331189c6ad4fba853c00007644e4c9e4d3d5c6720000000002047e049cc138e1aee84301a9024f3cf22d08c0302b52fa654748bd800047c8546cccf026406d228c80000f33418a70e81038e
  | 63 => 0xf954588000056c8bf045841d38bc28d0e06d823f40000e083a4202e00000000000051c4000074300000000000000000003aa44418e500bd800002821bf60000000000000000000773c0001e1407342990288840826da2a3ca5623a71936000000000002d0a44200001f863406104113701c100002c2406b85270000000000000001ffc5c74624234900008db8eb49e38000000000000000000000000000000329e000000004fe00000000000000030ee305000000003e5609cc2830bf400ce0400000213a07ac0000eec87aa0028000000000001c0a7e4cd7da1c616ea5f845821ede0ee20000e3789430f0e0000000030f370e337c129000000000000d73800000000000000000000000000000123d00000000d52976f000000005a0a321000081e000017fd2684016800b924131f22e6917b984d2006182c00015fe238c3bb816f9d54000000000001e2100000000cc4800000000000aac8000000030e00000000000000011e6238a37ee0000aec800040521680dcb054f05d669104be80000000375000016ee1fee5bdc5ce0000000001dca9b205600003530e10951923b46ffc64f80001a7e000000020064194000032e000024ae13180000000000079b00000ba70db43bac817873f40c00f14869118c0f8c34b081e16b124642b3c5d180de47961f2c7ea15ce1484642c520003b1336157483f22aa274044b0f5e9cbd17f4587109a800038362390b44229933ca4a645fb0a5e0dd20000d7b86f6030a67a4a0d80003808000030b957c0260415d14f1ea63928000000020b500000000f5100000048380ce680e800000000003480003de05824000047100000000f210000000083a475f074c1f5e000040f00003f6065e00001a97135838d8872a30146b21ce8000000000000000efd9bd80d40112000000002e260000f730eaf181869f407483c71aec1ed4ba8000041a40000000000000008ae83c280002b7236c43a2883d30827d34dc5955136486850000000032a20b5460589e9000027488030000000076902c186fc44066234b6b000009d40000e4680003b440001076067c2b040d6c000000000004cc8a058d34386600000728d1f0ede0f88a088f811d6e8d987f38bf530727cd4f5b045900000000599800000000000a92000015447ce0c25827c0a120e98568969e1d8045505dd84f209d0117103aa28a000052b400000000000189000020ac000000000000c5612660000ea9000000006dc0000166646362d74d1980002a3c000074a0ef10000772c00000001d48000061516dd3c506ae08cf00000e841d28000146f00000000000000000005b7c124000000005e700000000267800005ce804e429e8f9c0000502388a000000000000f58000000000003f6e00002031abb000036400000000000023d000017ce00000001002800000006
  | 64 => 0x114904689f7000000002a6000040a646e400008a2124800000001422000000ac00017471a024cb800000000c6253e51bc00000000615c0000d7323e660f83eb1b9e102a139cd6620bf0cee41b81b00000000000000000000262a0354b0e9f30000057208519d880000698cf1d0eb02c2035041a991fc1f7c3c7044c912d109241640b99ca3239a2aa000000002d941b3c1a20000341600006f41bdf3c0820881cd871021a236b4b930281018c86285b3800000001fb00000e5d2bf2000086c00000a9a76389d28000000000000000000000000003c9200c282a3608d4d8ae8060a0c9cec323b8010260211168e4a2df00b8c00000001b160c250370655368e67fc7f8058a1f840f0d05a06290000000000008940000000108c90ae222227f4642945b03560001094a3a830220000000004f2dec2d1d1ec8fd62170521059d800035200000000000039546554994145900002b24000000000000410ad40000000084b47669cca40803954d4481b333d4707447990c00bec6d448479fc50dc430980001eec16448c3cc5b0000416c59ad14b000000000000a1300003d3c000000011c51252353cd6d820234360000c3c98020d747564caf000000000000a1c800046d417700000000000057780000000000044140001ad221100000000213c2cc400006580000000006b0fb3024b46a40000af7200b057a88e8000176e45860000e8121ef0fc600011e90000000071900002128000000800000000000067f4000000042102268000000000000b846d782e8121c00001350ba51c706b00b71000008aa0a3417a0efd13a000011c38000000000006dc01cd29e878b1138091f06f440a07a9232639840000709000042721464200188b00001c8800000000000723c00007953bf257681f8800000000000000000016bc7ec8e9ba11a00000000f2e168c389e0000000000000004d95074160f0000000000009ab2e120000ef78afe0552000000007ff062e89a80000fb63756058059e01cb000073c40000af8000013d04bc228c000054950281cc637900000b60815e0000424c67a8a603ec68ef0000000013743548fac0e013d3800002b01b450000000000000000000870c8c8000000000000000000000005c7870e0112000000009f114b30000751cd55955e3c26403400007a53e2e00000000000000051c0e058db33c6a5e30a68800000007418c060feb00000000090800029aa3e580000000197000000001c7102a20000d11114a0000687cdd00cf913620bdc1229c323588332c000027508340000f5d8000474a0000000048c00000000000060328f281b09b114090dda00000001fb40d100220946052238b056fc0e0046433b207a000000e113ce00000f500001a701c4c000000040787fbc0001c0300000000000000000000000000000022981c900000
  | 65 => 0x1d5d1a8a013052d962044628548e220bce1c12000000015d007285e3cebe917e00003b6000000000b280000f90800033220000214000000003f4889e00000000774079b8000421e6ed4bbe8b820000451040b8000316e0000ca212d942c827450a00bbd00003594c9f800000003aacddc00000000000000000000eca0d3400021ff39ee689cc868a70418228902441eaf131c6870ad900002ef40000000112000000320d418ef710bc020800011e32410000048c18eb38b63d307c591ad11e27998b5321ac34e445a8f5485f32aa672589e480002d68000000000002b140000000128735f80000af6086c16745d4800015ca000025a4cd213f52d98078c5f01d0d368c0000000000000000000000000038fc00000000000000000000000962245c36a02e300000000070880e9a9f0fb03fecb7a9d4e3a062910d8f0000454c282880917f0249e6cc08b20a62256600000c20956000005c08361a01234814140fb95e7475c00000000e8300006c040001a911b4a000104b800000008ed48880e5943807c881d69c930000088008589e81430000000000000000000098f977c21c201851131d3f0000000000000000000000000021f84398191c5f1207626d800000000000101059400000000000000007fe000046982eb00000ac80b6e0000f0605c710803724dc116ef11ee253ca8e084f29e40000a1a83da278e8404d6e800030fe0000fcf1c2e35e861b85b68c5809aa2f485900d1016ac1918d3c95f80d785c5813f000000008320bd19eea2a7a0000b3a196c19946fbc7d0a39539d658d10d88f1201ec4270a8787ee45bc2fc90988c901cf242bc1509f85451a09009160bba4324355857a9d0e2c0e67d47bd8b68001642b507d033c36500f103c11b1733865fb477088303b5e260c76a924c00000000f618000280200007c1235e000028980bfa324000000003cd000016360000000230b4348522912e20aa01e80000c63000031200000e52183b0000000000009ec2c0c1e40dd709bc1df81ca82bc191709a817d082f0b600a6873b000008e30526557d1268d203df201a08e98f44439a49e06391452364c840cfb01019374432a5127a1510aec6f04b6a94d622b20000893922900904520635018940da861411a8bc639203e948c30000000032f06e08b5110064ea4000000010561edc188167f12fc33e835c80001b68000110e9fec26880bcca3d00233b7a70980dc97df467c7530c699f5a3e3821f400004b200e47cf914a96da11145804fa410511d5c60742fe000027468df80001ced08ec0000000000041e0560d1500e4b451e000062912f8124a00009c99e7508ba780ce400000000044d0000178e082a7158c278e2a086a4d68ad898162ef60000a501d11000047bc745a2b61c6e000000012e2301e0efc8af9c5e00000000000127f42da
  | 66 => 0x751019000000007f18000212045680000fe815580000000006d00001b846f741c3a1a10ee61e249589ff7000078f800006211b3c0000ecb1c98000029c80449585479e5b84e14912a42681ab800000e300000000c069cc12cde7e00bd005ba41f82a1470e800000000000b9900000000529800013e400003e24000038b00000000000175f19a4000000000000000460d0f40ee600003accdbb8afd274c49e4231126a3b7000005ed00003aca51500001bcb29026a501250f9d10ae0000000097c00008ae000003192d265674a98000000000000000191e00001bd4ba58000000080b00001d4b0000548c763000000003858c6e209d0000366497a800000003bb00000000119c000100c84421fbc09a5196104037c41f08c251a543654085840d992d31461998b8da2691e305bf001e861639de02306749de5408826b8ca1177e30c43fb4000000039b64a7829c802f2fc873fc000000010021688de51f363e68575822b80000e0e0b4400000f2286c08b8000049f0a3a462c409800045b001a800007442a50827c14e800028ba09a0f249f453c9e1bed1060000169c192c0000000130a0000cc9226034a68598b4097db02906fc0000000026521b2c0000b7623ea0000000152000007014000050736080000000000013aa81440001442376806c83f483560c7600010b61e1d1a0472442d1992a146600000001b0b07da000000015ff000080e0c198000000000005d4905808c640e4fe6000000008d887a420b92a223b3c00020ba1c4c000010c942f13c217500f71115151418cc4618679000015a4b9103df00006af800020f53b6a0000dd4912600000000000033400000000000000000000cbc2b7800043ae2c7000006412d1a1b591940dda42be00000000000000074408caa12a000000002908c8b0000000000000002dce7ca11df110d000045c47cc000020ba5c3c00011d4000067d8d88204245cc40a8000000017f64d140000000000073c80db0ada33100a00cdc8ede000013a400012233bfa8abc0000000000013402dc0000000000000001a51000088683f9863400a0000114e98d90af829202b90000152010fc92a90e904ca18c00001ab92d96000027da147000079ec000000000008dbcdd205d30de624a00000f2d000051fc0001efe3d7e5ffc41e23b4456e7dac0681de11276777059a83aa244264506099e821cdc096c456869222fe12e42c9888f2b0c8a0c3408ac4144a000014200000000000046383e705a60000b38a0d328982e2c8a4813801ac2e309ad95fc455c0000a508ed000006b18511000000002df03de11872424377426720d726ba120800016980c3e55300000dd7000000000001ca731e0000000000002f0e4f203511d5f2c841d00bcc21ba00001c14a99214b43ba82b84aa86f907466334b118b0725fa31f0000
  | 67 => 0x208418ae470c00014ca00002290000094a000000006179c4700005c9c2e60000000000000001bd02f625a486a3000000006d8c8a30000473c0000000000000007c44000000008d014a400008ed3070418c00022d500004c4c336837733b08220f0c800000005e54000208205a06778c7390c4011e03dc23a85a730ac000031b800000004c6c91d102900008d8460280000d427268cac1a2a315c47b84f80e9c1c64000034016300000847000013410000077914723172b760000e15181a1e80874093e1fb915965c30a20000027a845580cd969713d40000000000010e05fd910c1f8a24a4665c000000029906080d020802210023f8000033f0000000000001ce00007dd8000000000008dd8000000000006c3400000000000000084b03e500000000000000000000000f640000000000000000000000000000000a093b32774c97c903b1fea52f456e091c0bde1070cb89fa50c0a5574bf514ef110832989dc93d819685cfc5668000234432fccf891bf000000000001aac00000000c97800029a8000000005a900006ac000010ef000051e0be180002c3c0000f45000042c465d000000002602785c67c17800000763cc7c000002c200007a71b682c2263f811a1b8e2988835800016d0286000011b4129100000000000000000000f280000e1300005c380001d9b0000726c000150a000000010c480003a9e2c8c0e98000048c2750b7500002c6e000117000000000286c21b00002aee0000bbc871112840000792130c431650ec333989b1cd862104e18a4600d86368d3d18a1261c76c0015109b1f0c54b117687eb3a5249b9107800038627654000000000001d8c000058600000000000000000003700000159a469c24fd1ab8000371e227c000087300000000000000008dc17b40000d8400006f7802b89752de464d8a1880000000000000000000000000000000fd00000000f078d1100000c005b2a1d224f6000020c0000232800002c900001158000000000001500795c000000026cc7520cbf00000000000106d9b9018fc00000001d2a000057448a686680dde7c9000020203c567d281fc177f071075682c39084188e09c40000a7521644c1cce51fca000008a8d7c02e500008bf0037800000006c0c00012840000239510b8000024888703b687503da6000000010d500002484a5b92dd45fe0000fc900000000000000010313c3c3914d6980003b7e6e99119098700003c648e38adb000008c8ef318f61dea5aa81478465308a1830000000004cc68b448099ac0000000000001f200000000f6b1e7a3d56480cb95a3003d4828bc2b18111395c00000000877000046bcb9880002428605ce7a9e01288a4f0d0b40ca1000000000000b0f31623fc4b868b0c30085418f2d202f446e07cc1e0000039f2782c000059705401250592a2f3000
  | 68 => 0xb84e70f89000001223310000000000000000000000000000000000000000003cc82a294483e1a00009e880002b4221b8fe790c542d45ae51bc88ec3a468f000691335117c5c60ad511bd10a630191c99f0f2422572cfaf104637f08a84495903d18e03c30ab71b202d28107c000000038f80000634a2450000000013e9025129859e800012a300000a0c00004a70000591c0000129300000009c4197a1a565f9844590ec12e0631ceab866f04743aec10803ea35402e843691566098a1d740001d6a14562c680000000418666550f300000d06838c00000000000000030716d20000674400013232a0800000001461122644105b980001e2265ac00010ed000074e40068000121a000116991d205b2324818e8d9112b07dccb488000000069dc2860dae39b41d78f338ae4000033b0ca292250d8a0f500e60aff00008268000175b000073f8bc48000000000000000000000023b8000000000003460a67800045ce41ac9df01ec2012000072f118409e60000000000042f2000036d800000000000257131e00001bacc2300000e5c00000001c622fb0067cced00001b5820a107b141a2bba504883408e8000026a4fc407d000004a2919d8000146000004238000362219cc74085ac17f02dad0f603070000263d15e834e104a4d640000e1100000000bcb95950000382ca1e08d31dfe0ecca4f80000000607c0000000000000000001c1e000000000000000000000000000000178015fc554952d465a8808ecf8cad123a13c061c925e288c4b904790588019a6f449f6a07e36d200007bf0c3c2b0e686400012d31f400000ed69a3234a411b417302f12cca340c0001da12d7669ecc7280000d4c6c8833a199c445c6bfcac6852d436c8a4473b979f3ee2647000000000b5a00000b50000096a633c50595e43fa81ab400000002d50000000000000000000000000001a2a78151ad88110684323814896be00000000000211b1ecc0000fcc0a67111c00a015c934a1598000052580000000715cc148ad80cca1fd4cb7800003a20000000000000000000c7d12f700007b3800016040b90020012713e03e2600000000000000019c000016d4000078a90c0000000006fc81199ed90000000000012ca44c267dc6519a4732403e1054e0c5908bc88a4f7f814c05fe0c808ce9f084068226c4a38cf40000137915212f03cb088780001c791e760000b82800000000000c31a124000029b88859d612f9a8f7c0000b7b26d211f41df00000000754c2bb872300000000738a18e30be0000dfa94630000541c9bf800024b07e5495280003e040000000048a3de200000c81dcc26383d6c2d3000000000000b029fb146283efd1b90078000000000001a4f00001a4000000001ef0000038600003d323d588aa920d28387310a5f85e90000000042880000000445c40
  | 69 => 0xa0809a00006e20af4159b02a08f6c43f1913045609e917806f73fc86f3cc050e3b3332094000004ec25e65ee4368902111467065181a1d63fda83bc912006543725ed82029e5f306a85191588cc82118647c5351d8d3eda50081858998000032c497400003f2e5f28bd78b2800004a9c00006ca000000010dc22531d1c8c38000059d00000000ab380003910000083c80ba0000000001600000f022b74f20a358000000010a60000000000000000000381474985ef88c82e200dd0619a23b2ff800008f4074600005afc9430a730dfa11bc6ff800036dc6d082349dab000041d83de9e39043e00008388000142432180000000000065d80001b1b1838861832b04d70000593449c91b445c23200ffc0000460c31e03830de900000000fee15b62ff205d8a2992af0fca6fe48001d4d370a36e867686d5271200005e19a0c43ce593c0e5137a174c00000bd9c090a3e8a8ce1f8af62e2e1678c12832633f2000003800002b0266e80000000456a540d02403bb3114000000000003cee482ca7c137100007504a338abb00002c9c000102015ac6f18b9a1a1a40d43d04077a1d5057858e8431a03f000000000000e691d2e7678000178b00000000c48800004b015ec000000023885cd89c0812f0000631097300003baa000059c08593828000000000001e14672c4bd800000007fe80000340000000005dc19dc22800000e2f9b841fba1e841f020fe0f90000000000000000503000000000000479c79e1853000000000000000000072740000a563d340d60faa000000007ee027e833a3e8c6904000000042220000a4e0d9d272c7bd4ad4800009ba7de8009893800d6708c90096d81f8a00002102201147088140de8aab12080000335939709c40e08d9e062e273a24d0cc6800000007860000000016106d00448886b000007ac34380f53ff600005790d95094c34dc7d38092356407689aa05471aa63f34460800033605ff800008d221f60000000000001301b2068e23080c5600009d91e6b34b254f8000196318fe56306d587fb3be27610dac9d32000005b09b8000000000000b1c80003f4800000000f94091a82980001b4f00003fcced484d606cc8b3094d800017240b140001ac71a8e00000001f1f38a44214ff98000000003f80000c6d06c43e910358f040cfc438c3a4969a44b613481a580002e2a4ebc47d1da83dd000000001f9031f81d64c878000221e2174042000020f074311631a76367c7df4cd79d200c5886ac0fd0a790ce438b4f54190732e6612436989de12be190ca89933f4286153804f80000000268c697932c1d701e0d02b8c980d3e0db40001c1738d23e4422880003e9e86082130e2200a2000000002fb000062d400000000000000000018ea000062a0840858d0000000051692fb27c600000a30945046c213433e8c0a0d
  | 70 => 0x8c78baf350261545341a8e2660304878b0f1d11984ee113405490de0292816a0e35346a2730f040000232c121cbe20b961c9226106a1101135e42d7ca1d1d1902e466ec0000000000026b4000000023800c70ca480000f08000000015b83ffc5d700001005369650d084182950be4103ca958000361c1d4476d89221a347e340b3a3b1146a83b8f3e95642cee2bc098204c1359e0000000000039c620d8000000024ea47ac5d897580c222c4800016a036ec363810f00000000000038e00001c885fc8e689fce3098000112617cc058405b856f8000000000000000ff630386f3509103cf165c0000000103f3d28357800013b4257c2328cb0800000003b309c780001bde41c0000000046f86c2107b80000c3c5c2000020c238ea6d611c30a93000022789f89916466c59f426d94680a4a79f8661087229d63a7c86da02e000000008790000152e36800000774369851b0945800000001e28000000000000001110a1ce41e6000000006120000649c00021573664000020e9d501dbe8f6845d8000000063a40000fe33cba2c61128914b0000310068f00002f2c152800013ce0000399119c800047c000000000ba80000251804a800000002a840000a9200004f84ef700000a500000239201c43a83d8c0001d400000000000000004044895c216000024b2000038b0000166200002230000000054151de829800fe0000000098a29325278cf80000120a73c06d08bcd000088540001f4b00000000000030300000000000000019aa38a40000000000057d4b548000000000008f880003b1680e40000db5280a0000db210dc00005c291d1000040500c1801f220e3a007e3cda4000000000000973800047c421207af0c951a9a334495c8000000000000000b9b0000000090f16fe27ba6be4000000000004be86cd1f4e032887c05288d0d00000000000232046382364f680d8000000000000000000002b00000000000001914cdb9f0c44f27254afe9b5220ca8179189000006f200000df800000000000bf100001f2e0000bf60f6700000000e29800003c828780000243003600004ec1267000000000000000288887ec00017460a364de00000000298a5910000194e44d843340001c5c1fde5050000000037d60000000000000000000000000000000c7800003ab0000463800010ee38aa82648ab80000000044066320ab00000000000139f47ae00006fe8000265a0000fe18000000041340000ed308f068bc0ca811719c2539c21480000000000000008040082709c000080a00001efc000173c099000000000e6700008890000000036d800007b689743e147910b62000030f408fce8c0d810000435800000000000000034d97a529b20000d5e112e2b6e000000009ff2cc239f0d3e026f253a8514f371b86000004ec0001c0100206f310
  | 71 => 0x7e21ab400005d885a192bc00008f746e58000287e000088d19a2000000011091a2b038c0000a9d950d243a67ac0000e5315545d38000000002fc2a7800000003c441a4c0000f392e94291d00d90fe076a00009ab000000001f80070000000006108fe09706000000000000000000060c116f8aee477466d0f63000017981d5111280003da83b28853121f20284800904800021141470b9983992b3c46cc0c00000280c000000002cc1e5e1100161800007a234251ec1d940e96731c9b980003dde82f839983b02c78000000021ad000000000000000000047800b4a20008b60000d32800017401938000000012a653405b9146d00000000a5218660f8e34f89cf1f43074e5c9042a077900001b190858a5f0000820c60c0060450828841ae00002b8a32a8b610000000014b04a099342d2a381c85d8000264259440000b302a2e6d3464b01b5000000000000eb600005f5800000003ba43b944af080e3b6e0000184000026167f5800018db00000f489a19fe2233e4704322056e01506828d2a9e90226a11ec90513902cec235400000000cf600000001326000000006a513500b08660400004fa1bf66d544aa02f5098600007538000344a3380cdf02853fec2808a3707271d121754ccd80001bb800002510096000000000001ccf31820000d800b811cec3cd89841045000035244bb07771d207bdc99c0000104000008b11c8e40b646001459a9d30564998aba053f119a4090e879ad522a44afcc82142340e027d4e0880003bea2b04dab00001eca0000f0e1bb71e624a5ce4602f000000000000000000006f140759837000000182ef80000000389c09023800b0a15e40aa00000000000000000001a2637545c9964100000000f661b941adc00006e98f51183c2cbc8618c04000073a8dc488392722104c0001c97066e772481700001a5200004649d7800000000e5800000000000000001ef1a18000101b80000000405400000000ed812a85631e8f00006bd80000c550000300cd2f20bb41461c7c6ada03a03ae438000000000000000050698bf46d612f4c6b00003dd200b40001597093c4f7c0000000000000010e50198029c00004558000000000000000000000000000000000000000008130000135e04ac78402ad000019444cd00002dfe44c8e090000182a0dec91c8000280003fd1ae133a12b800000001fd828c015211d480000000148000016c04492577d13c21c700000b5c0000ebd00000000000020544a400005bd17830a546194000000016fc00000000a49387a00008ee11070000000000013fe00000000df515cd00000000bd420812c80000000004e3000000000000000035e18546b91954088681c49f3000025508650648a2543dba36dce5c0000476000010e79a6f3a6c28fc04513bd450200008d59c4230f80be8efa00000
  | 72 => 0x84a17aa7c188710000000029e0fb800002be2000109900002e5280340002327361e5f00d51938a38d86c9c8b596531e1c1df40000e1b2582231013108bd2f341600e459d151e927c980001d49000082a000001e2000012483ce21f306647c645e397b3377219e0b141ad030c80c441fb0c0d07b60630deb01593ec43169192a3af0ba4699cffc849c00304c407a590e62178186c481914303b2173d076968a37c68c543c887fa055e5751081004908cc64b0dd19eb91ac65ee86d2164328420f70c1ea3b23f347adc1701fee1dae45b454100df299c76006921ac807e01c28595060f41b8808465e8e150ca624d443b08f53e98048856292a13b6852740e9116300000000000000023d400000000000341237cc00002891aae5ddc109800000000000ba41fa6185812e8d9091ec000017e44e78f290154000051ba3e62ad820dc837876e42e82998
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863564984520432b31cc2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108f4e132e840845e73197420422eb98cba1021179cf65908108bae7b2c840845e73196420422eb98cb210211d9c465908108f4e032c840864d6394a4204326b1aa5210211e9c265508108f6e0b2a840845e73195420422eb98caa10211e5d46050810c74a83028408639541814204335290c0a10213c5c460508108bce6328840845d73194420423b388ca210211e9c0651081087ce832e640843d74197320423d380cb99021471d153cc81087ce9b2c640843d74d96320421f3a0cb190210f5d0658c8108ece232c640847a701963204316b24a5190218b591528c81087ee8b2a640843c74595320421f3a0ca990210f5d0654c8108f4e032a640851c7454d320423aba8c2990219554c614c8108f2ebb02640847975181320421f3a0ca190210f5d0650c8108ece2328640847a70194320429d386a9a0821475cc54d0410a5ae42a6820847970596410431d2a4c1208218e5526090410a6ce3aa2820853a70d51410421f3b0a8a0821475cc5450410a5ae42a2820861f5418d410430e2a0c6a08210fdd954104108f6eab00820843f74597310421e3a2cb988210f9d3658c41087ae9b2c620851c7454e310423dbaac1188210f9d3650c41087ae9b28620846e72d943104236b96ca188211e5c1650c410c3ac9298620851c7454c310430eb22a6188219394d620c410c9aa6b10620865953980310421f3a6cb108210f5d365884108f6eab04420843e74d94210421eba6ca10821179cf65084108bae7b284208479705942104316b24a4108219358e5208410c5ac8a90420864d635482104334a94c010821179cf65900108bae7b2c800863554986400422f398ca20021175cc65100108dce4328800846d72194400421f3a6cb180210f5d3658c010caaa730c600863864941300421f3a0ca180210f5d0650c0108dce4328600846d72194300423bbaac3100218e192504801087ce9b28400843d74d94200422f39eca10021175cf65080108eae2b28400843e74194200421eba0ca10021179cc65080108bae6328400862d649482004326b1ca4100218b5915208010c9ac6a90400866552984200431ab2cc9880218d59564c40108eaeda96200847576946100423cbb0a908021565cc5484010ad2e42a4200847976d4e100429c3a2a7080211e5db52840108f2ed28c200853a74946100423b3b6a4880215cdd54044010ae2eb98220087615288110042d9ba240880211e9d85444010ab2e62a2200856972151100423d3b6a6880214e1d153440108f4eda92200847a76945100429d3a4a2880216c5d25144010ae2eb20a20087305450510042e839a82880215c5d43144010b62e818a2008751530c510042f0b906288021d854a2144010
  | 1 => 0x304430e320a6982218e197644c1108f4eb32260884ba74991304427938cc8982218e194644c110d30c9a9a608847a7614d304434c320a698221a6193324c110ab0ea9926088698644c93044358326c298221acd90614c110d60c830a60884f27518530443393a8c2982213c5c8614c1109e0ed10a60886b0648853044371b1442982213c1d9214c110d60c890a60887c132485304421f3a4cb102210f5d26588110974e932c40884f271992204423d3aec7102212e1d163881109e0e2b1c40884ba7498620442b93a8c3102215c1d5218811087ee8b2a408843c74595204422fb9aca90221171cd6548110c58c9a92408862c64149204431c32ec8902211e9d66448110974e932240884f271991204431c328c8902211e1d56348110970e8b1a40884f07158d20442b53aec490221aa1935248110c70c9292408856a72949204423d3b0a4902218e1905248110d50c8292408856a7614920443353b0a490221ca9d05248110e52e8292408872b641492044335320a4902219a1905248110e50c829240886286414920443a5398a490221d25cc5248110ec2e229240886b064d852044359b20c2902219c1962148110d60c910a40887605288520442b83aa42902219c1952148110d60c890a40884ba74d8f104425d3a6c588221ac99221c4110dc2c510e20886b26448710442d93a6a1082216c1d13084110dc2c510420885b074482104422f39cc52a021175ce62950108bee6b0aa80845c73585540421fbb2a82a021875516315010c5aa8b10a80861e6458c540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0219558e6115010ccac5308a808659639805404334b14c02a0210f9d261d4c1087ae930ea60843e7498a530421eba4c529821875cc6454c1087ee8b0aa60843c74585530421fba2c0a98210f1d16054c108beeca98a60861d6454c5304326a9ac429821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a608635649845304332b14c2298218e9926014c10c72c9300a60866a629805304334b14c0298211e9c265d0c108dce432e860846d721974304237390cb218211b5c86590c108f4e032c860853a70d52430428eb98a9218214b5c85490c10a38e8a9c860847671995430423d384caa18210fdd16550c108dce432a860846d72195430421f3b4a8a18211b9c86510c108dae4328860847671194430423d380ca218210f5db5410c10a74e1aa0860843d76150430428eb98a8218214b5c85410c1087ee8b1ea40843c7458f520421f3a4c3a90210f5d261d48108f0e0b24a40843f74581520421e3a2c0a90211bdd95214810c5ac8a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290219358e6214810c6cc9308a4
  | 2 => 0xc6a92218b1936254910c98c7b12a48865463d85524431c326c0a92219618f60549108deeca90a48852c7454852442a639aa4292218b1c96414910c76e0b20a48863870590524430f324c629221875926314910c3cc8b18a48861d6458c5244326392c6292218d9916114910c6ac8b08a48865663584524432ab1ac2292210f9d0611491087ae8308a48845e73184524422eb98c2292218e9916014910c72c8b00a48865a63580524432cb1ac0292219c585601491087ce8300a48843d74180524422f398c029221175cc60149108bce7b2e848845d73d97424428e39aa9a12214b1c954d0910a5ae8296848845e73d96424422eb9ecb21221179cc65909108bae632c848861f5498e424430e2a4c7212211d1d561909108f0eab04848845f73595424422e39acaa12211edc165509108f0e032a848843e76951424421e3b2a8a1221471cd5450910a58e4aa2848847a75d81424427938ec0a12218e9506050910c72a8302848845f73594424422e39aca212210f9d065109108bce6328848845d73194424421ebb6a8212211d1d56110910cc8a4b088488478755804244334292c0212210f9d365cc91087ae9b2e648851c7454f32442a6392a799221535cc52cc9108f0eab0664884f071583324421f3a6cb192210f5d3658c91087ce832c648843d74196324430f326a71922187990538c9108e8eab0c648847875582324421fba2ca992210f1d1654c9108eee2b2a648847b70595324422f3b4a699221171d9534c910a38e8a9a648854c7254d324421fba2ca192210f1d1650c91087ce8328648843d74194324422f398ca19221175db530c9108e8eab08648847875580324425c3a2c0192219a149600c910c3ea831a828861c5418d41442ca39a8220a212e1d160cc510c38c9a9a628861c6414d31442ca3a26218a21b1589310c510a9ae629642884b8745832144334292c190a216c9d36088510ae4ea304428854d73149214423b3b0a490a21715cc5248510ac8ea992428856872553404423cbb4a5a02214e5d052d0110e50a5a1680885387550b40442793acc3a02219c9d661d01109e2e530e80884f3768874044279bb243a02215c1d521d0110a38e6aa4808852c72552404422fb9acaa0221171cd65501108dee4b2a808846c72595404421f3b0a8a02210fdd95410110a38e6aa0808852c7255040442d8b8ca8202211edd95410110ad0e4aa080884bb7655040442cc39aa8202216a1c95410110b66e2aa080884f07158c404429cba88620221a658c4310110b62e22188088479761484044334b10a4202212e5da4210110b34e721080885b171908404439429084202216c5c44210110b30e6a088088570754844044370b1242202213c9c6648c110974e930c608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608861c64d4d
  | 3 => 0x526308310c3aa9318418861e5458c20c430eaa2c6106218d9526108310c6aa930841886365458420c431aaa2c210621ca5512008310cacc6b0ea90851e73d52548422f39cc52a421175ce6295210a3ce7b22a90843f765505484338b0cc02a4218d99161d4e10ce2c3306a70851e74d4e538421f3a4c529c210f5d26294e10a3ce9b1aa70845f7654c5384237396cb21c211b5cb6590e10c72a9304870846e721944384236b90ca21c21179cf6454a108bae7b22a50843e74d8d528421eba6c6a94211bdd95214a10c70e0b20a50861e6498c528430eb24c629421879916314a10c3ac8b18a50863664584528431ab22c2294219598d6114a10caac6b08a50867161980528422f39ccba1421175ce65d0a108bce7b2c850845d73d96428422f398cb21421175cc6590a108bce732a850845d73995428431d2a0c0a14218e5506050a108bce6328850845d73194428421f3a6cb994210f5d365cca1087ce932e650843d74997328421f3a6cb194210f5d3658ca1087ce832c650843d74196328421f3a4ca994210f5d2654ca10a98e4a9a65084f170185328421f3a0ca194210f5d0650ca10970e8b00650861e5418d418430eaa0c6a0c212e1d160cc610c38c929a630861c6454d318425c3a2c190c219a54860486108f2ed29681085397414b408431b2a2c2204211edd95410210a72ea21881086996310c4084334b10a4204212e5da4210210b34e7210810859873504408425d3a4c3184211e9d8534c210d30c99926108698644c9308432b29ac2184212e1d16388210974e930c410863b65191208425c3a2c6904213c1c56348210c70c9292410847a76149208431c320a490421995496108210c6acb326210863565593108431cb2cc9884218e59564c4210974e9b1e21084ba74d8b108422f39cc52a221175ce6295110c3ec831aa88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c631895444334316c0aa2210fdd95415110a38e6aa0a88852c72550544421f3a4c529a210f5d26294d1087ee8b04a68843c74582534430e326c6a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10cc8c5b0aa68866862d81534422fbb2a629a21471d15314d10a98e4a98a68843e74184534421eba0c229a211b9c86114d108dae4308a68846e72d974344236b96cba1a211b9cb6590d108dae5b2c868847875582434427838ac121a211bdc96550d108d8e4b2a868847675d85434423d3aec0a1a211bdc96510d108d8e4b28868846e721944344236b90ca21a211d1d56110d10ca8a6b08868847875580434431c2a2c021a219614d6010d108bee6b26a48845c73593524421fba2c7a92210f1d163d491087ee8b04a48843c74582524429c3a2c12922187d936354910c38c9b1aa48861f6418d524430e320
  | 4 => 0x68e2b1aa98861d6318d54c428f39cc4aa621475ce6255310a6ce3312a98853b7058954c428fb9ac0aa621471cd6055310a5ee4b02a98852c7258154c421fbb2a82a6219c9856015310c74c8b06a7886726158353c421f3a4c529e210f5d26294f1087aed2a0a78843f7655053c422fbb2a629e218b9526214f10c5aa9310a78862e5458853c4316aa2c429e219354d6214f10c5cc9310a78862d6498853c4317322c429e218b5916214f10c9cc6b10a78863a6458053c431cb22c029e219a9896014f10cd2c4b00a78846e7219643c4236b90cb21e21471cd5450f10c6aa9b0a878846e7219443c4236b90ca21e21475ce5410f10c6ca8b08878863a6458352c421f3a6c6a96210f5d36354b1087aed2a0a58843f7655052c430f2a4c629621875526314b10c3ca8b18a58861d5458c52c4237bb2a4296219358d5214b10c3cc9318a58861d6498c52c430f322c629621875916314b10c9ac7310a58863a6458052c431cb22c0296219698d6014b10cb2c6b00a5886726158052c422f39ecb21621175cf6590b108bce632c858845d7319642c430f2a4c721621875526390b10c3ca8b1c858861d5458e42c431aaa2c3216218e9536050b10c74a830285886395418142c422f398ca21621175cc6510b10c6ca8b08858843e7499732c421eba4cb996210f9d065ccb1087ae832e658843e74d9632c421eba6cb196210f9d2658cb1087ae932c658843e7419632c421eba0cb196210f5d6648cb1087eeab24658843f7695232c421ebb4a9196210fdd9548cb1087aecaa4658843e7499532c421eba4ca996210f9d0654cb1087ae832a658863a54d8132c431d2a0c0996210f9d2650cb1087ae9328658843e7419432c421eba0ca196218d552610cb10c6aa8b08658863a5498241c431caa4c120e218e9516090710c3ca9b1a838861d54d8d41c430f2a0c6a0e21875506350710b28e6a08838863a5498041c431d2a2c020e218e952608c710c74a8b04638843e7695131c421e3b2a898e210f5d6640c71087eeab20638843d7695031c421fbb2a818e218b952620c710c5aa9310638862e5458831c4316aa2c418e219394d620c710c9aa6b106388594744c431c438aaa26218e21b1589310c710c74a930063886395498031c431d2a2c018e218e551600c710cb2a6b00638863a5498221c431d2a2c110e211d9d8524871087aeb320438843f7559021c421ebb4a810e210fdd95408710c3ca9318438861d5498c21c430f2a2c610e21875516308710c9ac7290438864d6354821c431d2a4c010e218e5526008710c74a8b0043886395458021c4334a92c010e218d95161d0310c6aa9b0a818843d75d9130c421eba8c8986210f9da544c310878ecaa2618843d75d9120c421eba8c8906210f9da5448310878ecaa2418843d7695020c421fbb2a810621879
  | 5 => 0x6396590c40082d539486200414e5d44310020c72ca218801047b755884008275baac4200419add56210020d54a8b1080106a954588400836529ac420041b254d6210020d5486b1080106a843588400825cbb484200418e5964210020b34e721080106a962908400831cb2884200419c5965110020dc2c52888010669625444008338b2aa220041cc9515110020e62a8a8880107525354440083a8a9aa220041b85895110020e64e8a888010731745444008399322a220041cc90d5110020e6086a888010762625444008338b12a220041d85895110020cc2c4a888010732425444008398212a2200418e5974110020d52c5a08801073151d04400831cb2a8220041661cd4110020b50e4a0880106a9625044008398a8a82200419354d628c02087ced2a2601043c76951300821f3b2a8980410f1d9544c020c3ec929a601061c6494d300830fb22a69804187191534c020c6ec928a601063464945300831bb22a2980418d191514c02087ce9328601043d74994300821f3a0ca180410f5d0650c020c5aa9310601062d54588300832729ac41804199989510c020ccac4a88601070d5454f2008392aa2a390041d154d51c80208daed29440107195454e200823cbb4a510041cc9515188020e62a8a8c40107525354620083a8a9aa3100419c9915188020ce0c8a8c401043e76951200821e3b4a8900410f9d95448020878ecaa2401061f6494d200830e324a69004187d915348020c38c8a9a401063764945200831a324a2900418dd915148020c68c8a8a401062f74d9520083163a6ca900418bd976448020c5eca322401062f659512008317b2aa89004193d965348020c9ecaa9a401070d5454d2008333b2ca29004199d955148020e4aa8a8a40107455354520082753b480900416add13048020c76e9b2a401063874d95200831db2ec8900411e5d66448020974e9322401063b651912008354b90c8900412e1da5448020c76cb2a240104b876551200831db2aa89004196d965348020d30c929a401065b6554d200834c322a690041c65515348020c70c929240106a86494920083543248490041725ce42480209d0eca1240105a9748c920083543246490041aa1913248020ce6cb28a40106b064945200831c322a2900419cd955148020d60c8a8a4010732545452008398aa2a290041d494d5148020ea2a6a8a4010733645452008339322a2900419c1915148020e60c8a8a40106306454520083b1b12a290041d89095148020ec284a8a40107623254520083b0992a290041aa1922148020ec2a310a40105a97408520083543204290041725cc21480208bce7314a98845d7398a54c430eb18c72a6214d9c46395310a3ce7314a98851d7398a54c429db82c52a6214d9c46295310a3ce630ca98851d7318654c4297390c32a6214b5c86195310a
  | 6 => 0x10822e39acaa0841179cc65504208bae632a821045d75d8d410830f2a6c6a08418755363504208baea31a821061e5418d410830eaa0c6a0841179da53504208b8ed29a821045e7654d410822e3b2a6a08418b5536250420caec728a821065463945410832bb1aa2a08419518d5150420ccec4a8a821063954d814108338a8ec0a08419c54460504208bce7328821045d73994410821f3a4cb988410f5d265cc42087ce932c621043d74996310821fba2ca988410f1d1654c42087ce832a621043d74195310821ebaec8988410f5d4644c42087ced2a2621043c76951310821f3b2a8988410f1d9544c420c3ec929a621061c6494d310830fb22a69884187191534c420c9aa7b12621063764945310831a324a2988418dd91514c420c68c8a8a621066762545310832ca9ec0988419c547604c420ce2a2302621043e74d94310821eba6ca188410f9d2650c42087ae9328621043d75990310821fbaac8188410fdda540c42087aed2a0621043f76550310821ebb2a81884187992530c420c3ac9298621061e6454c310830eb22a6188418b952620c420c5aa9310621064d5398831083172a2c4188418b551620c420c9ca6b10621064d53588310831b324a2188418d592510c420ccac5288621063664544310831ab22a21884199989510c420ccac4a88621063a54980310831caa4c0188419694e600c420cb2a7300621067151980310831d2a2c0188418e551600c420cb4a6b00621065953580310833928ac0188419c545600c420970e8b06421067151583210821ebacc8108410fdd5640842087aed2a0421043f76550210822ebacc610841879526308420c3aa9318421045f7558c210830f2a2c6108418755163084208baed298421061e6494c210830eb24a61084117dd95308420c3cc8a98421061d6454c210831b324a2108418d5925108420cacc7288421065563944210831b322a2108418d5915108420cacc6a88421065563544210831d2a4c0108418e5526008420cb4a73004210659539802108338a8cc0108418e9516008420c72a8b00421065a53580210832ca9ac0108419c945600842087ee8b1ca01043c7458e50082b8b8ea9a00418e59654d0020e32a929e80106596554f400838caa2a7a00414e5d742d0020a76eaa168010731549474008338b2aa3a0041cc95151d0020e62a8a8e80107525354740083a8a9aa3a00419c58951d0020e6684a8e8010731425474008316aa2c520041179ce65100208bae7328801045e73194400822eb98ca200419354e6210020c5ca8b10801064d535884008333312a220041995895110020c72caa008010719535004008354b128020041cc5454010020c72cb320801057171d50400831cb2ca8200411edd95410020c74c8aa0801063965550400832cb2ca620041965955310020e32a8a98801
  | 7 => 0xa10419694f6050820cb2a7b02841065953980420831d2a2c0210419654d601082087ce9b2c641043d74d96320821ebacc9190410fdd5648c82087eed2a4641043d76952320821fbb2a9190410f5d9548c820c3cc929c641061d6494e320830f322a71904187591538c820cb2a6b04641064d654c83208386aa264190418e552600c820970e8b00641063954580320832d29ac019041b24c9600c820c3ca931ea21061d5498f510830f2a2c7a88418755163d4420c3cc929ea21061d6494f510830f322a7a88418759153d4420a6ce9a8ca21053574d4651082ab39ea328841555cf51944208bee6b24a21045c73592510821fba2c7288410f1d16394420aace7aa4a21055573d525108398382a928841559cc5494420aaae62a4a21053674d4e510829aba6a728841c59525394420e2aa929ca2107165454e510838aaa2a7288414d9d05394420a6ae829ca21057270d9251082abb9ac928841551cd6494420a6ee8b1ca2105347458e510829b3a0c7288414d5d06394420acce431ca2105727018e510829b3a0c5288414d5d06294420aace6314a2105557318a51082ab39c8528841555ce4294420ae6e0a14a210536748ca510829aba465288410f9d0635442087ae831aa21047676d5151082ab39ea8a8841555cf5454420e60e12a2a21073070551510823b3b0a8a8841559cc5454420aaae62a2a21047676d4d510829b3a6a6a88414d5d35354420e2ca929aa2107155494d510838b2a2a6a8841c555153544208ecec29aa2105367414d510829aba0a6a88415c9c36454420aaee6b22a2105547359151082b2392c8a88415c1c16454420a6ee8b1aa2105347458d51082b2392c6a88415c1c16354420a6ce831aa2105357418d51082b3390c6a88415c9c06354420acce521aa2105657290d51082b938486a88415c5c24354420ae6e0a1aa2105707050d51082ab39c84a8841555ce4254420ae4e1212a2105717090951082b9b8284a88415c9c04254420ae2e0212a210536748c9510829aba464a88415c9c23254420ae2e1192a210745320c951082b938064a88415c5c03254420a6ce8102a2105357408151082ab39840a8841555cc205442087aed2a0a21043f76550510830f2a4c628841875526314420c3ca8b18a21061d5458c510822ebb4a628841879925314420c3ac9298a21045f7654c510830f322a628841875915314420c6ca9308a21063554984510832b29cc2288419554e61144208eeeca88a21063664544510831ab22a2288419598d5114420caac6a88a21045e73997410822eb9ccba0841179ce65904208bae732c821063a54982410831caa4c1208419694e6090420cb2a730482104e9729824108338a8cc1208418e9516090420c72a8b04821065a53582410832ca9ac1208419c9456090420ce2a2b04821045f735954
  | 8 => 0xe6295020a3ae7314a81053a70986540828fb9ac32a041471cd6195020a3ce7b22a81051d73d91540829b38ec8aa0414d5c76455020a5ce531aa81053a7098d540829c382c6aa041479ce6255020a3ae7312a81053a70985540828fb9ac2aa041471cd6155020a58e4b0aa81053870585540831d318c0aa0418e18c6055020c74c4302a81063862181540831db08c0aa0418e584605502087eecaa0a81061d5498c540830eaa2c62a0418d5526115020c6aa8b08a81061e6498c540830f322c62a0419358e6215020c6cc9308a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81063654987530831aaa4c3a98418d95161d4c20c6aa8b0ea61063664987530831ab24c3a98418d99161d4c20c6ac8b0ea61067161983530828f3a6a729841475d35394c20aace3a9ca61055571d4e530821fba2c3298410f1d16194c20aace3aa4a61055571d52530838c382a929841559c45494c20aaae22a4a61054e72d9253082ad386c929841479d26294c20a3ae9314a61051f74586530828e3a2c329841479d06194c20a3ae830ca61054e7218653082ad380c329841479d36354c20a3ae9b1aa61055671d8d53082aab8ec6a98410f9d06154c2087ae830aa61045e76d5153082ab38ea8a9841555c75454c20e30e0aa2a61045e7615153082ab388a8a9841555c45454c20ab0e0b22a61051e74989530828eba4c4a984147dd16154c20a38e8b0aa61054c7258553082ac382c2a9841479d06154c20a3ae830aa61054e7218553082ad380c2a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530830f324c629841875926314c20c5ac9310a61063664984530831ab24c2298419598e6114c20c6cc8b08a61063564584530832b31ac229841999896114c20c72c9300a61067161980530823b38ccba18411d5c665d0c208ece232e861047571197430823b38ccb218411d5c66590c208ece232c8610475711964308236bacc5218418b5526290c20c5aa8b14861064e5358a430823cbacc1218418e5526090c20c72a8b04861065a53582430823b38ccaa18411d5c66550c208ece232a861047571195430831caa6c0a18419654f6050c208f2ea30286104e972181430823b38cca218411d5c66510c208dce4328861047671194430823ab88ca218411e9c06510c208bce7b2c841045d73d96420822ebacc721041879526390820c3aa931c841045f7558e420830f2a2c7210418755163908208beed29c841045d7694e420822fbb2a721041175d95390820c72a8b04841063a54d81420831caa6c
  | 9 => 0xce930ea69043d749875348317322c529a418e9916094d2087cedaa2a69043e76151534831baa6c2a9a418d1536154d20c6ea830aa69063454185534831bb26c2a9a418d1936154d20c6ec830aa69063464185534832bb18c2a9a4199d886154d20ce2e030aa69063864d81534833830ec0a9a4117dd95314d20aa8e2a98a69043e74988534821eba4c429a410fdd16114d20878e8b08a69047671d97434823ab8ecba1a411b5cb6590d208f2e1b2c869047771595434823a38acaa1a411edc16550d20a3ce7aa2869047671194434823ab88ca21a41475cc5410d20c58a9310869046c7558843483162a2c421a418e1526010d208f0eab00869063854580434831c2a4c1a12418e15160d0920c3ea931c849061c5498e424830faa2c721241871516390920c70a9b02849063b54181424831c2a0c0a12418e15260cc920c70a8b06649043f76d52324821ebb6a9192410fdd8548c92087aec2a4649063854d81324831c2a0c0992410f9d263d452087ae931ea29043e76d51514821f3b0a8a8a4187d536354520c38a9b1aa29061f5418d514830e2a0c6a8a411ddd95114520aa8e6a88a29043f7458c514821e3a2c628a418ed526090520c70a93048290638545824148274392c120a41179ce65505208bae732a829061f54d8d414830e2a6c6a0a4187d506350520c38a831a829045e73194414822eb98ca20a418b1526210520c70a9300829063854580414821fba2cb98a410f1d165cc52087ee8b2c629043c74596314831c2a4c118a418e151608c5209d0e4b04629043e74d95314821eba6ca98a410f9d2654c52087ae932a629043e75d91314821f3a8c898a410f9db544c520878edaa2629043e76151314821e3b0a898a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629062f5498831483162a4c418a418bd51620c520c58a8b10629064f53588314832629ac418a419958b510c520c76a9300629063854980314831daa2c018a418e151600c520cb6a6b00629067351580314831c2a4c110a418e1516088520c70a9b02429063854181214821fbb6a810a410f5db540852087eec2a0429043d76150214830faa4c610a41871526308520c3ea8b18429061c5458c214831daa4c010a418e1526008520c58a9316809062f5418940483162a4c5982418b15162cc120c98a6b16609043e74d95304821eba6ca982410fdd1654c120878e8b2a609043e75d91304821f3a8c8982410f9db544c120878edaa2609043e76151304821e3b0a8982418e15161c8120cacc730ea81065563987540832b31ac3aa0419558d61d5020ce2c3306a81051e73d52540828eb9ea92a0414d9c75495020a6ae3aa4a81045f73586540822e39ac32a041479c
  | 10 => 0x66a52181420c334a90c0a10610f9d0625443087ae8312a21847776544510c31ab22a228861995895114430ce2a3304821846e72195410c236b90caa0861879506350430c3aa831a821865463945410c32a31aa2a08618d592510c430ccac5288621863564544310c332b12a2188619c546600c43087ee8b2a421843c74595210c21f3a0ca908610f5d06548430ca8c6a8a421866952181210c21f3a6ca108610f5d36508430c3aa931c801845d7694e300c23cbb4a71806187d97644c030c3eca322601863b65d91300c31db28c8980619358e62d5320a3ce7aa4a99051e73d9154c821fbb2a82a6419a9896015320a3ce9a9ca79051e74d8d53c821f3a0c2a9e410f5d06154f208beeca98a79066a6258053c823bb8acaa1e411d1c56550f208ece232887904757119443c828f39ea9a1641879526390b20c3aa931c859051e73d5142c821f3b0a8a16418e1506050b2087eecaa0859051e74d4f32c830f324a71964187991538cb20a3ce9a9a659045e7614d32c822fbb2a6196412e1d1600cb208bee6b24a39045c7359251c821fba2c728e410f1d163947208eeeca88a39045e7399741c822eb9ccba0e4117dcd65507208b8e6b2a839061e5418d41c830eaa0c6a0e410f9d265cc72087ae932e639043f7459531c821e3a2ca98e4187192534c720c38c8a9a63905547154d31c821f3a6ca18e410f5d3650c720970e8b0643906715158021c828f39ea9206410f9da545032087aedaa0819051e73d5040c823cbb6a8206412e5db5410320b34e7aa081905aa72d5040c82d5390a8206414e9d44310320b54e421881904b97690840c82cd39c8420641661cd4110320c38c929a619061c6454d30c8326a98c4986410fdd95415220cd2c5300a91043e74987538821eba4c3a9c4117dd95314e20cd2c5300a71062f5498a438823b38ccaa1c411d5c66550e208ece2328871047571194438828eb98a821c418e1516010e20c3ea931c851061c5498e428821f3b4a8a14418e9506050a20c72a8302851043d76d50428828e3a2a799441471d1534ca20c74c9304a31063964982518823bbb2a228c4117dcd65506208b8e6b2a831053671d51418830faa0c6a0c4187150635062087ee8b2e631043c74597318821f3a6cb18c410f5d3658c62087ee8b2a631043c74595318821f3a6ca18c410f5d3650c62087cec2a2811043f76550408822f3b0a69844117dd9530c220a70e8b2e411061f6398f544828f39ec3aa241475cf61d5120a72e030ea89051e73d83544828eb9ec1aa2410fdd954151208bce7310a89045d73988544822fb9ac22a241171cd6115120c3ac6318a89052d7218c544829b388c62a2414d5c46315120a72e0318a89053970984544828fb9ac22a241471cd6115120a3ce6308a89051d731845448296b90c22a2414e5c0611512087
  | 11 => 0x4c29ab8ec7aa2614e5c362d5130a3ae6316a89851d73d87544c29cb80c3aa2614b9cb60d5130a5ae5b06a89843f76550544c28eb9cc42a2614edc16215130a3ae6310a89853671188544c29ab88c42a2614e5c06215130a72e1308a89851f73584544c28eb98c22a2614b9c86115130a5ae4308a89853970184544c31c2a4c1a1a618ed506050d30a38eaa18869843e74987524c21eba4c3a92610f9db545493087cec2a2a49863754d85524c31a2a6c2a92618dd506154930c68a830aa49846f76548524c2b238aa42926187d526390930c38a931c849861c5458e424c31c2a6c0a12618ed506050930c70a8302849847671194424c23ab88ca21261871526310930c38a8b18849863854980424c21f3acc9192610f1d5648c93087aedaa4649843d76152324c31c2a6c0992618e150604c930a3ce92a2649854e72951324c2a73aec499261c3153624c930e18a9a92649870f54149324c3862a0a499261539d8524c930c9cec292649854d71149324c38c2a6c099261c6150604c930c38a9318649843e7498b514c21eba4c5a8a610f9db545453087cec2a2a29862f54d89514c3162a6c4a8a618bd506254530c58a8312a29847776544514c2b2392a228a618ed526090530c70a9304829863854582414c30e2a6c6a0a6187d506350530c38a831a829846e72194414c236b90ca20a61871526310530c70a9300829863854580414c31c2a4c118a618e151608c53087cebb22629843e75191314c21f3b6a898a610f9d8544c53087eedaa0629843d76d50314c21fbb0a818a610f5d8540c530c5ea9310629862c54988314c317aa2c418a618b151620c530e2ea8988629863b54980314c31c2a4c018a610fdd165c8530878e8b2e429861c5498f214c30e2a2c790a619319532c8530e18a8996429874532d47214c21fba2cb10a610f1d16588530c70a9304429863854582214c21f3a6ca90a610f5d36548530c98ca992429870c544c9214c21fba2ca10a610f1d1650853087ce8328429843d74194214c21f3acc810a610f1d5640853087eedaa0429843d76d50214c21fbb0a810a610f5d85408530c3ea9318429861c5498c214c30faa2c610a61871516308530c9ac7a90429864d63148214c32ab1ea210a618ed526008530c70a9300429863b54580214c31c2a2c010a619ad496008530ce6a2b00429867051580214c30e2a4c7a026187d506350130a70eaa00809843f76550540c316aa2c42a0618d5516115030c5cc8b10a81864e63588540c333314c22a0619958a6115030c6cc8b08a81865663584540c333312c22a061995896115030cd2c5300a81867161980540c31caa4c1218610f9d0615483087ae830aa41846f76548520c316b22a429061995496114830c9cc6a94841847671195420c23ab88caa10618e9506050830c72a83028418
  | 12 => 0x9908187191534c840c3aca21a64205997010d321038621aa4990819654c604c840cd2a4302642043d75d90321024f39ec8190812d5c4640c840972e0320642043d7610e511029ab8887288811b9c863544408dae431aa22045e73189511022eb98c4a88811ddd95114440caac6a88a22066562544511021fbb2a7a08810f5d662d044093ce731682204b97018d411030fb28c6a0881875d46350440d34e031a82206997018d411030e31aa6a08818718d5250440c38c728a822069863981411029dbaac0a0881a6d8d6050440b50e4b0282204b970193311030e322a79888187d94438c440e288728c622046e721953110236b90ca988812e5c0644c440c38c929a622061c6454d311031a324a2988818d191514c4408dce5b28622046d72d94311024ebb0861888187594430c440b2ae2218622068c43588311021ebaec990881279cf64c8440938e6b24422045f73595211022e39aca90881179cc65484408bae632a4220634645452110334a90c0908819c54460484408bce7b28422045d73d94211028f39c85280810f5d84294040a38e6a0ca02049e7398b401021fbb2a5a00818b98952d004087aed2a480204797695240102cd39c8520081aa98a4290040b30e6a0c80206b1615064010316312a4a00812e9db4350040a72eb212802059973909401035431484a008166dcd4150040d66c2a0a802064e6358b54cc335312c1aa6614b9cb5495330a5ce5b22a99843f7655054cc32d31ac02a6618e9516010f30a5ce9a94a59862c7259252cc31db82c9296618e1c16494b3087ce830aa59843d7418552cc237bb2a4296614b9cb54d0b30a5ae9296859861e5498e42cc30eaa4c7216614b9cb5450b3087cec2a2859863b5418142cc31c2a0c0a16610fdd95410b30a3ce9296659854e7295132cc28f3a4a4996611ddd951147308dce532e839846d7299741cc30f2a0c6a0e61875506350730ce2a2b00639843e74d9721cc21eba6cb90e610f9d265c873087ae932e439843e74d9421cc21eba6ca10e614b9cb549033087ced2a2819843d76d5040cc297396a8206619558e61d5230ce2c3306a91853671d52548c29b38ec8aa4610fdd95415230cb2c7300a91853671d52438c21f3b4a8a1c610f5db5410e30a6ce3aa0871846f76548528c23b38ccba14611d5c665d0a30c74a8302851863954181428c29b3a6a328c6187dcd6494630c38e6b24a31863471592518c31d324c128c618e592609463087ce8312a31843d74189518c23bbb2a228c614d9c754d0630a6ae928e831863a54982418c31caa4c120c614d9c7545063087cec2a2831861f5418d418c30e2a0c6a0c610fdd95410630c68c928a631863464545318c21f3a6cb10c610f5d3658863087ce932c431843d74996218c21f3a6ca10c610f5d36508630c3ca8b18811853671d8f54
  | 13 => 0x52d0b40a5ce529a85a051e7394942d031db2ec0a16818e94c6050b40c74a430285a05387050951d023bbb2a228e811b9cb650c7408dae5b2863a045e73d9721d022eb9ecb90e812e1c164c87408bce7b2843a045d73d9421d02ab38ea729c8117dd95314e4087aeb314872046f76548529030f31aa521481a698e6090a40cd4a4302852047671997329023ab8ccb994818759253cca40a98e4a9a65204b571190329025cb80c8194812e1d1600ca40aace7a8ca32043d7690e519029ab888728c81179cc62546408bae6312a32047776544519024f39cc5a0c819c5466090640ca8c728a832065463545419030f3a8c6a0c81875d46350640878eca9a832061c6354d419021eba8c4a0c818718d5250640c38c728a832069463945419029b3b4a2a0c818d9da5150640e2ec728a832063463945419038a31ca2a0c818518e5150640d28c6a8a832069863181419031bb24a398c811b9cb650c6408dae5b28632061d6494c319030eb22a618c81655c4430c640c9ca6b10632064d53588319034621ac418c818d592510c640e2887288632066562944319031ab22a218c8199589510c640cb2a7300632067151980319024f39ec990c81179ce65886408bae732c432049c73592219031ab24a310c81179cf65086408bae7b28432049e7398b4090317312a5a048193d4d6294d408beeca98a6a064d63d4a5250237bb2a4292819358f5290940c9ac629484a066852d81425025d3a8c0a12818e9d46050940c70a630284a04b8705923250316b26a5192811d9c4650c9408eae232864a043e759903250237394c7a8a811b5ca63d45408bce7316a2a045d7398b515029c38285a8a811ddd95114540ce6a2b0482a0636655044150237b92cb18a811b1c9658c540974e1b2262a046e721943150236b90ca18a8187593530c540aaae229862a064f53588315032629ac418a8196d4d600c54087ceb32642a04b870593215022fb9acb10a81171cd65885408bce632842a045d731942150316b26a410a819358f5208540c9ac629042a066b525802150316b10a5202811b9c86154c408dae430aa62045f7654c5310326a9ac4298819554d6114c40a3aeb318862051f7654c431030fbb2a62188147dc95310c40a38e2a98862043d75988431030ea9ac2218812edd56010c40c76eab0086204b872580431025db8ac0218814b9ca4354840a5ce421aa4205397010d521022f398c2a9081175cc61548408deeca90a42064d635485210332a92c2290818e1c16590840972e131c842061d6598e421034d384c721081a65c26390840c3acab1c842061e6354a421029cbaec1210818e5976090840d32c7b04842069a6318242102d8b88c1210818759443cc840b32e021e64204b9709923210317322a5190811ddc5654c8408e8e2b2a642047671195321023ab88ca
  | 14 => 0xa8a9e4210c6d7694a210878aaa2a7108431d5da5288421c5ecb2a24210e2f6555121086373b6a690843535d65348421c9ecb29a4210e4f6554d21087872a2a690843c35515348421c9aa7b0a4210f455390521087a2a9a82908438dd965448421c6ecaaa24210e576594d210872bb2aa690843c55515348421e8aa72924210e1e5498f500870eaa4c7a80438795163d4021c3aa8b1ea010e1e6494f500870eb24a7a80438799153d4021c3ac8a9ea010d3a74d42500869cba6a128043569cf5094021ab2e7a84a010c3f7458e500861e3a2c728043569cf5494021ab2e7aa4a010d5a7315250086acb98a9280434e9d35394021a72e9a9ca010f1a5494e500878caa4a728043c69515394021e32a8a9ca010d3a7414e500869cba0a728043d254f2194021ad6ea90ca010f495348650086b9baa43280434edd16394021a70e8b1ca010d3a7418a500869cba0c528043569cc6294021ab2e6314a010d5a7390a50086acb9c85280431e1d94294021a74e9194a010d39748ca500863cbb4832804356dcd4194021ab0e6a0ca010d3b744c6500869c3a263280431e5d83194021a74e818ca010d39740c650086b539063280435a5c831940218f4edaa2a010d5a73d5150086acb9ea8a80431e9d85454021ab4e62a2a010d5973151500863d3b6a6a80434e9d35354021a72e9a9aa010f1a5494d500878caa4a6a8043c69515354021e32a8a9aa010c7a7614d500869d3a0a6a80434e5d05354021e52a990aa010f4953c8550087992a442a8043cc5522154021ea4a710aa010f515388550086b5baa42a8043ca5512154021e92a690aa010d737548550087992a242a8043cc5512154021ea4a690aa010f515348550086b4392c8a80434edd16354021a70e8b1aa010d687258d50086b838ac6a80435cdc54354021ae0e2a1aa010d5a7390950086acb9c84a80435c9c64254021ae2e3212a010c7b7650950086b938884a80435c5c44254021a74e9192a010d39748c950086b938c64a80435c5c63254021ae4e2192a010d71710c9500869d3a4c2a80434e5d261540218f4ed20aa010d5b7350550086ac39a82a80435a9c84154021ad2e420aa010d3b744c5500869c3a262a80431e9d83154021a74e818aa010d39740c550086b539062a80435a5c83154021ea26218aa010f637248550087b121242a8043d85092154021a74e810aa010d397408550086ad39842a8043565cc215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a628043875915314021c74a9300a010e3954980500872d29cc0280439654e60140218f6eca80a010e3a64540500871cb22a0280439698d5014021cb2c6a80a010c5f7654c53d0237bb2a429681479ce
  | 15 => 0x1e5498c530870eaa4c62984317dd95314c21c3cc8a98a610e1d6454c530871d2a4c0298438e5526014c21cb2a7300a610e3a54580530871caa2c0298439654d6014c21c3cc9318a610e1d6498c5308717324c4298438b5926214c21c6ac9308a610e3a64980530871cb24c0298439698e6014c21cd4c5300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e7261580530863d384cba18431e5c265d0c218f4e032e8610c7970197430863d384cb218431e5c26590c218dce432c8610c7a70196430863cb80cb218431e9c26550c218f2e132a8610c7a70195430863cb80caa18438d5536150c21caaa7b0a8610c7575185430863d384ca218431e5c26510c218dce43288610c7671194430863d380ca218431e5c06510c218bce7b2c8410c5d73d96420862ebacc721043879526390821c3aa931c8410c5f7558e420870f2a2c7210438755163908218beed29c8410c5d7694e420862fbb2a721043175d95390821c6aa8b0c8410e3a54d81420871caa6c0a10439694f6050821cb2a7b028410e3a54181420871caa0c0a10439694c6050821cb2a63028410e5553984420871b2a2c2210439554d611082187ce9b2c6410c3d74d96320861ebacc9190430fdd5648c82187eed2a46410c3d76952320861fbb2a9190430f5d9548c821c3cc929c6410e1d6494e320870f322a71904387591538c821caaa6b0c6410e3554984320871aaa2c2190439594d610c8218bee6b24a210c5c73592510861fba2c7288430f1d16394421c9aa73148210e2d5458a4108726a9ac5208431e5d66090421c74a93048210e3954982410872d29cc1208439654e60904218f6eab048210e3a54582410871caa2c1208439694d6090421cb2a6b048210e1e54d8d410870eaa6c6a0843879506350421c3aa831a8210c5e7694d410862e3b4a6a0843179d953504218b8eca9a8210c5e73994410862eb9cca20843179cc65104218bae63288210e4d5398841087172a2c4208439354d6210421c9aa73146210c6f7558a3108726a9ac5188430f9da544c421878ed2a26210c3e76551310861e3b2a89884387d92534c421c38c929a6210e1f6454d310870e322a6988430f9d3650c42187ae9b286210c3e74994310861eba4ca188430f9d0650c42187ae83286210c3d75990310861fbaac8188430fdda540c42187aed2a06210c3f76550310861ebb2a81884387992530c421c3ac92986210e1e6454c310870eb22a6188438b952620c421c5aa93106210e4d5398831087172a2c4188438b551620c421c9ca6b106210e4d53588310872ab2a6218843651d1310c421e2aa89886210c7975980310871d2a4c0188438e552600c421cb4a73006210e5953980310863dbaac0188438e951600c421c72a8b006210e5a53580310872ca9ac018843c395153c8421e1a
  | 16 => 0x8726a9ac418c434e9d350942218f6eca80a110e1f6418d544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890c3f76550544868e39aa82a2434e1c15415121c38c9b1aa690e3464d85534871db26c0a9a438e1936054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690c5f7654c534868e3a2a629a43561c15314d2187ee8b00a690c3c74580534863d386cba1a431e5c365d0d218f4e1b2c8690c7970d9643486363aac521a431ddc56550d218f6e0b2a8690c7870595434863db82ca21a431e1c16510d218f4e03288690c797019443486363aac421a438b1516210d21c98a6b108690c7475584434872a29ac221a433c5c261d0921c76a83028490e3854181424872a29ac3992433c5c0614c921b1ce9b1a6490c6e7614d32486a73ae869924393197434c921c98ca21a6490dc57110d32486f0b80c299243335ce62d05218bee6b2a8290c5c73595414870faa0c6a0a43871506350521a98ea9966290c3f74595314861e3a2ca98a4387193534c521c38c829a6290d4c754c931487463226498a431edd95014121a70e8a80a090d5873540504861fba2c6282430f1d16314121c9ac7316a810e5a63983540872cb1cc1aa0439698d60d5021cb2c6b06a810e7261583540868f39ea92a043475cf5495021a74e1aa4a810d3970d52540868f39cc52a043475ce6295021a74e130ca810d3970986540868f39ec8aa043475cf6455021a74e1b22a810d3970d91540869a38ac6aa043479ce6255021a3ae7312a810d3a70985540869cb84c2aa0434b1c9605502187eecaa0a810e1d5498c540870eaa2c62a0438e5526015021c72a8b00a810e1e6498c540870f322c62a0439358e6215021caac7308a810e3a64980540872d31cc02a0439658e6015021c74c8b00a810e5a63580540872cb1ac02a0439a9896015021ce4c2b00a810e3a54983530871caa4c1a98438e95160d4c21c72a8b06a610e3a64983530871cb24c1a98438e99160d4c21c72c8b06a610e7261583530868f3a6a729843475d35394c21ab4e1a9ca610d5970d4e530861fba2c1298430f1d16094c21ab4e1aa4a610d5970d5253086ad380a929843565c05494c21a3ce9314a610d1d7498a530868f3a0c329843475d06194c21ab4e030ca610d5970186530868fba2c129843471d16094c21a3ce9b1aa610d1d74d8d53086ad386c6a9843565c36354c218bcedaa2a610d5a70d5153086acb86a8a9843179d85454c21ab4e02a2a610d597015153086aa38ac8a9843479d26254c21a3ae9312a610d1e74185530868eba0c2a9843569c06154c21ab2e030aa610d1e74085530868eba042a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a98430f5da5414c2187eecaa0a610e
  | 17 => 0x80634e5d06254031ab4e6312a018d7271189500c6ad39c84a8063565ce42540318f6eca12a018c7876509500c69d3a464a80634e5d23254031ae4e2192a018d71710c9500c69d3a4c2a80634e5d261540318f4ed20aa018d5b73505500c6ac39a82a8063569cc4154031ab2e620aa018d3b744c5500c69c3a262a80634e9d03154031a72e818aa018d6a720c5500c6b4b9062a80630f5da541403187eecaa0a018e2e54988500c716aa4c4280638b9516214031c5aa8b10a018c6d76948500c717324a4280638b59252140318deeca90a018e2e64548500c716b22a4280638e9526014031c72a9300a018e6a52980500c734a94c0280631edd95014031c74c8a80a018e3964540500c735312a0280639a5895014031a3ce7aa4a990d1e73d9154c871db20c0aa6430fdd95415321a70e0aa0a990e666258454c868f3a6a729e43479d36354f218beeca98a790c3f7458053c861e3a2c029e431e9c36590f218f2e1b2c8790d387055243c8716aa4c521e431edc16550f218f0e0b2a8790c7a7019443c863cb80ca21e434e1c15410f21a3ce7aa68590d387055242c870f2a4c721643875526390b21a3ce7aa28590c3e7615142c871daa0c0a16438e1506050b2187eecaa08590d387055042c868f3a6a79964387992538cb21c3cc8a9c6590e2d6599232c8716b2ac919643479d3534cb218bcec29a6590d8e74d8d32c86c73a6a699643715c7534cb218dcec29a6590cce7614d32c86a73ae869964317dd9530cb21d8a64b086590d387055341c8666b9cc5a0e434e1c15450721c3ca831a8390e1d5418d41c870e324a698e4387191534c721d18c89926390dc4714c931c86ca3a26218e43b1589310c72187ee8b1ca190c3c7458e50c863dbb2a0286434e1d15014321a74e1aa4a910d3a70d91548870fb20c6aa4430fdd95415221a38e6aa0a910e6562984548861fba2c129c430f1d16094e21c38c9b1aa710c5f7654c538868e3a2a629c43871cd6414e21c5cc8b10a710e2d64588538871d324c029c438e5926014e21cd2c5300a710e3a64580538871cb22c029c439a5896014e218f4e132e8710c7970997438868e39aa9a1c43475d053d0e218f4e032c8710c7970196438869d386a921c431e9c26550e218f2e132a8710c3e76951438868e39aa8a1c431e9c06510e218f2e03288710c3d76d50438869d386a821c439514d6110e21a38e6aa68510cf170987428868e39aa8a14438e9506050a21c72a83028510d1c7454f328868e3a2a6994439554c614ca219e2e030a6510d3a70d53418868e39aa920c438e9526090621c72a93048310d3a70d51418861f3b0a8a0c4387d506350621c38a831a8310c3f76550418868e39aa820c43471d1538c621c38c9a9a6310c5e7614d318870e320a698c4317dd9530c621a38e8a986310e4e53588318
  | 18 => 0x250431c9ec6a928218e4c63549410c787a1aa4a0863879516310431a3aea2188218e4e63548410c726b1aa420863c310d5210431e1ca8a966218f0d5454b310c727322a5988639319152cc4318baed29c6218c757694e310c792aa2a5188630f9da544c431878ed2a26218c3e76551310c61e3b2a8988638bd92524c431c58c92926218e2f64549310c716322a49886387dd3654c431c38e9b2a6218e1f65d91310c62ebacc898863279d2644c431c3eca3226218e9571191310c64e3b4a89886387d96544c431938ecaa26218e1f65551310c727b2ca498863a3192524c431c38c8a926218e4f65549310c746322a498863c3951524c431e1aa8a926218f0f64549310c727322a49886393191524c431e18c8a926218e0c64549310c7a238aa49886387192514c431d28c920a6218f4552905310c6e8b848298863351d9414c431e8aa4a0a6218e3774d95310c71a3a6ca988638dd97644c431c6eca3226218e3765951310c71bb2aa898863a5193634c4319aced21a6218e6765949310c733b2aa498863c9551524c431e8ca6a926218d55758c9310c6caba464988638b95262d4031c5aa9316a018e2e5458b500c716aa2c5a80638b99252d4031c5ac9296a018e2e6454b500c716b22a5a80634e9d35094031a72e9a84a018d6a72d42500c6b4b96a1280630fdd16294031878e8b14a018d6a72d52500c6b4b96a928063c61cd5494031ad4e42a4a018d6972152500c78caa68728063745c44394031a74e9a94a018d3974d4a500c7952a4a528063ca5525294031e54a8a94a018f295454a500c7a5a1aa528063d210d5294031a74e8294a018d397414a500c7a4a96632806356dd53194031b30e898ca018f49524c6500c6b9baa6328063569cf6494031ae4e3b24a018d3b7458a500c69c3a2c5280634e9d06294031a72e8314a018d5a7318a500c6b9388c528063569ce4294031ab2e7214a018c7b7650a500c63c3b285280634e9d23294031a72e9194a018c7976906500c6adb9a8328063561cd4194031a76e898ca018d38744c6500c61f3a0c4a80630f5d062540318f4edaa2a018d6a72d51500c6b4b96a8a8063c61cd54540318f4ec2a2a018d6a72151500c6b4b90a8a8063565d74354031e32a9a1aa018f195410d500c6e8b8886a80631e9db5254031a74e9a92a018d3974d49500c7952a4a4a8063ca5525254031e54a8a92a018f2954549500c7a5a1aa4a8063d210d52540318f4ec292a018d3a74149500c69cba0a4a8063c65533154031e92a598aa018f31548c5500c7b0a9462a806356dd53154031b30e898aa018f19544c5500c7a4a9262a80635cdd53154031e62a898aa018f61524c5500c6ac39ac8a8063c650c4354031ae4e221aa018d717110d500c69dba2c4a80634e1d16254031ab0e6b12a018d7071589500c69d3a0c4a
  | 19 => 0x8b06a418e3954583520c6973a6a5290634b5d35294831ad4e1a94a418d6970d4a520c63db82c9290631e1c1649483187ee8b04a418c3c74582520c6b5386a9290635a5c35494831e18e6aa4a418d6a70152520c6b4b80a929063c35534394831b8ae221ca418d4e73d92520c6b5b82c9290635a1c16494831a5ce830ca418d2d74186520c6b5380c3290635a5c06194831a5ee8b04a418d2c74582520c6973a0c1290634b5d06094831a9ce6304a418d6671182520c6aab8886a90630f9d0605483187ae8302a418c6e76d51520c6b5386a8a90635a5c35454831e18e72a2a418f0c73551520c6373b0a8a90635a9c05454831ad2e02a2a418d4d75d0d520c7872a686a9063c35534354831e1ca821aa418f0d5410d520c6e2b8886a9063539cf6454831a98e6b22a418d6471591520c6b5b82c8a90635a1c16454831a9ae3a1aa418f0d4310d520c6b338886a9063595c44354831e1ce821aa418f0e6410d520c786b2086a9063d19c44354831a9ae221aa418f457110d520c6a2b8886a90634b9d06154831a5ae830aa418d6a70185520c6b4b80c2a90634b9d03154831a5ae818aa418d2f74581520c6963a2c0a9063531cd6054831ac8e2b02a418d2e74181520c696ba0c0a9063539cc6054831acce2302a418c3d76950520c61fbb2a8290638b9526214831c5aa9310a418c6f76548520c717322a4290638b5915214831c74a9300a418e3954980520c734a94c0290638e9516014831c72a8b00a418e6952580520c63d384cba10631e5c265d0831a3aea21e8418d957110f420c78621aa5a10631e9c265908318f2e132c8418e1e5498e420c70eaa4c721063355c66390831c3ca8b1c8418e1d5458e420c726b1ca5210639398d5290831c9ac6a948418c7b70595420c63c382caa10631e9c065508318f2e032a8418e1d54d8d420c68eba886a1063655c44350831c9ec6a928418e4c63549420c78621aa4a10638d5536150831ccaa5b0a8418e9443185420c63cbaec0a10638e9536050831c72a9b028418e6a52d81420c734a96c0a10631e5d46050831c74a83028418e3954181420c74c218c0a10639a9486050831cd2a43028418c7a70994420c63cb84ca210639954961cc83187eed2a46418c3d76952320c61fbb2a9190630f5d9548c831c5cc8a946418e2d6454a320c71aaa4c2190638d551610c831ccca4b086418e1d65d0f410c787a1aa5a0863875516390431a3aea21c8218d957110e410c72731aa5208639358d5290431e1886a948218c7975982410c71d2a4c1208638e5526090431d30873048218e6a52982410c734a94c1208631edd56090431c74a8b048218e3954582410c735292c1208639a5496090431c3ca9b1a8218e1d54d8d410c70f2a0c6a086387550635043193ceda1a8218e1f65d0d410c727b1ca4a08639318e5
  | 20 => 0x970d8b544c68eb98c5aa2638ed8260d513187eecaa0a898c7b70588544c63c382c42a263475ce6215131a76e0b10a898d3870588544c68eb98c42a2634d5c46215131a74e0310a898d3970188544c68eb98c02a2634b9c86015131a5ae4300a898d3571180544c71cb00c02a2638d15261d0d31c6ea830a8698c3e74983524c61eba4c1a92630f9db545493187cec2a2a498e3b54d81524c71c2a6c0a92638ed506054931c70a8302a498c6f76548524c6b4382a4292630fdd16014931878e8b00a498e1f5498e424c70e2a4c7212638715163909319a8e2b1c8498c7a70995424c63cb84caa12638ed536050931c70a9b028498e3b54181424c71c2a0c0a12631e9c065109318f2e03288498e1c5498c424c70e2a2c6212638d1526110931c3cca2a66498e1c54987324c61f3acc9192630f1d5648c93187aedaa46498c3d76152324c71a2a6c2992638d150614c931a3ce92a26498d4e72951324c7862a6c499263c3153524c931e1ea82926498f1454d85324c70e2a0c299263c5150614c9319acea30a6498e5675185324c74b3a0c299263a55d0614c931d2ea830a6498e5654185324c72a2a0c299263a5150614c931c28a830a6498ed270185324c768b80c29926387152630c931e1ea89906498e1c5498f414c70e2a2c7a0a638ed526090531c70a93048298e3b54582414c71c2a2c120a63871536350531c3ea831a8298e1c5418d414c70e2a2c518a630f9d262d413187ae9316a098c3e76d51504c61f3b0a8a82638bd536254131c58a9b12a098e2f54189504c7162a0c4a82631edd95014131ad0e4a80a098c3f74588504c61e3a2c4282639398d62d5031cd4c5306a818e6962983540c735312c1aa0639a58960d5031a5ce5aa4a818d2d72d52540c69d386a92a0634e5c354950318f6e0b14a818c787058a540c68f39cc52a0634edc16295031a70e0b14a818d3a70986540c69cb84c32a0634b9cb6455031a5ae5b22a818d3a70d91540c69cb86c8aa0638718f6255031a3ce7312a818d1c73589540c70e31ac4aa0634d1c56255031a76e0b12a818d3870589540c70e31cc2aa0634e9c26155031a72e130aa818e1c63185540c68f39cc0aa0634d9c66055031a38e6b02a818e1c63181540c61fbb2a82a0638b5526215031c5aa8b10a818e3954980540c71caa2c02a0638b9926215031c5cc8b10a818e4e63588540c732b14c22a0638e9926015031cd4c5300a818e6962980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a063535cb54d0c31c3acb2a68618e3554586430c70eb2a86218638d9516110c31d2a86b088618e1d65990430c6a6b96a82186317dd95410c31c3cc8aa08618c5f75584430c66bbaac22186395dd56110c31d2ca8b088618e9554584430c71d2a4c1a90638e55260d4831c74a
  | 21 => 0x70e298c0a1283c614c6050941d66c230284a0e3a75181425074da98c0a12838e14c6050941d30a630284a0e18531814250755a90c0a12838e1486050941d50a430284a0e1e6414f325070eb20a799283479d743cc941c3cc9a9c64a0e1e6414e325070eb20a7192830f9d6644c941968e2b2264a0cb87059132506a7396a69928387990534c941c3ac829a64a0d1e75d0d325070e32e86992831e9c0650c9418f2e032864a0e1e6414c325070eb20a619283535c8530c941ca8a730864a0db07050b415072da9cc120a839614e6090541cb6a6b0482a0e5853582415070eb18a720a83875d85390541c38a6b1482a0e1c53982415078c29cc120a83a6d4e6090541c70a730482a0e9853982415070c29cc120a83acd466090541e30a6b0482a0c5e7398b505062eb9cc5a82830fdd942d4141a70e0a16a0a0c5e76d4d505062f3b0a6a828393d4f6254141c98a7b12a0a0e4f531895050726298c4a82831edd95014141ad0e4a80a0a0c5f7654c5310726a9ac4298839654d6014c418bce6302a420c5d731815210637bb2a4290839358d5214841cd2a4b00a420e2e6454a321063db82ca990831e1c1654c8418f4e032a6420c7970195321061ebaec899083c310d524c841caaa630a6420e94431853210732a90c2990830f5d8439444187eeca9e8220e1e6354f411061ebb4a9208831d5da5490441c3ecbb1a8220e1f6518d411070eba8c6a08838718d5350441c38c6a928220db170d91411072bb2ec6a088395d946350441d2ec831a8220d1c73506501062f398c4a8083175cc62540418f6eca80a020e59635405010734b12a0280830fdd95415331cacc6b08a998c3e7615143cc61fbb2a821e631bdd95214b318f6e0b2a8598c787059542cc697396a8a16638ed506050b31c70a83028598d1e7494b32cc68f3a6ca99663539ca544cb31b8ae3a926598d1e7494932cc6673b0a499663b14c9610cb31c76a93048398e385498241cc61f3b4a8a0e63879506350731c3aa831a8398c3d76d5041cc70e32664a8663871913254331c98c4992a198c7b7654050cc73930ac1aa4634e9c35495231a74e1b22a918c3f76550548c72ab1cc22a4634e9c35490e3187ced2a28718c3d76d50438c69d386a821c63175db5410e3193aedaa08718d9671d50438c6cd386a821c63659c45410e318f6e0b24a518c7870592528c61fba2c1294630f1d16094a318deeca90a518c7a70997428c63cb84cba14631edc16550a318f0e0b2a8518e3a54181428c71caa0c0a1463a610c6050a31a74e1aa68318e3a54982418c71caa4c120c63a610e6090631a74e1aa28318c3e76151418c70e2a0c6a0c63279db435063187eecaa08318c9c74597318c69d3a6a1284630f9d0625423187ae8312a118c7b76540508c69d386c7aa2634e5c363d5131a74e1b16a898d3
  | 22 => 0x4831e9c2658ca418f2e132c6520e2d6454a329063d380ca994831e5c0654ca41e1886a926520c7a70994329063cb84ca194838798d53d0641c3ac621ca120d6a7214e50906b4b90a728483c694e4394241a72ea21ca120f185310e50906ad398a528483565cc5294241a72eba0ca120d7175d0650906ad39ec928483565cf6494241a72e9b1ca120d3b7458e50906b9388c7284834e5c64394241e34e621ca120f1a6310e509078cb1887284834e5c44394241a76e8b14a120d397418a50906ad398c528483565cc6294241cd2c4314a120d727118a50906ad39c8528483565ce42942418f6eca14a120f1843cca509069d3a465284834e5d23294241a76e8994a120d38744ca509078c21a6528483569cc6194241ab2e630ca120d6a7218650906b4b90c3284834e9cf41942418bce6312a120c5d73189509063d3b6a6a84831e9d85354241ad4e429aa120d697214d509069cba886a8483c6d4c43542418f4eda92a120c7a7614950906ad398a4a8483565cc5254241a72eba0aa120d7175d0550906adb9ac8a8483561cd6454241ad6e4b22a120d6872591509069dba2c6a84835cdc54354241ae0e2a1aa120f194310d509069dba2c4a84834e5d06254241ab4e6312a120d59731895090734b10c4a84835c9c46254241ab4e7212a120d597390950906b938c84a84835c5c642542418f0eca12a120d3a748c9509069cba464a84835c9c43254241ae2e2192a120c7b7654050906cd386c9a9a83569c364d4d41ab2e1b26a6a0e4f6298b535068eba0c5a9a83475d360d4d418beeca98a6a0d4e72d9053506a6b96c829a83569c36414d41ab2e1b20a6a0d1d74d88535068eba4c429a83475d06214d41c9ac4310a6a0d557118853506ad380c429a83565c06214d41a3ae9b00a6a0d1f74580535068eba0c029a83539c86014d41a9ae4300a6a0d5571180535070fb9ccba1a838799753d0d41c38a6b1686a0e1c53987435065d384c3a1a838714e60d0d4196ce330686a0e5453986435072ba98c2a1a83479d76350d41a3cec29a86a0e1e7614d435070e29ec4a1a838714c6050d418bce7306a4a0c5d73983525062f3b6a6a9283179d85354941cb6a7b02a4a0e5853d81525072da98c0a92839614c60549418deeca90a4a0d6870548525070eb18a7a12838799453d0941c3aec29e84a0f0e7214f4250786b90a7a12838714e61d0941974e130e84a0e1c53983425065b38cc1a1283179d663909418b8eab1c84a0c5d76d4e425062ebb0a7212839514f6150941ca8a630a84a0e5b53d81425072c29ec0a128396d4c6050941cb0a630284a0e6b521814250734290c0a12830f9d76350941c3ec629a84a0e1e7614d425078629ec4a1283c314f5250941e1ea629284a0f1453d85425070e298c2a1283c514c6150941e30a7b0284a0eb061d814250
  | 23 => 0xcca32c5acaaa6651943e74d81518ca1eba6c0a8c650f5da541463287eecaa0a31947776544518cb1d2a4c028c658e5526014632c74a8b00a31963954580518cb38a8ac028c650f9d2619423287ae930ca11943d76950508ca1fbb2a8284658d9526114232c6aa9308a11963654584508cb1aaa2c2284651edd95014232ce2c2a80a11947a70986544ca3cb84c32a2658dd906155132caec630aa89967361d81544cb3830ec0aa2658ed906055132ce6c2302a89967061181544ca1fbb2a82a2654d1c55415132a70e0aa0a89955471553434ca673acc5a1a65939d662d0d3299ae3316869953471552434ca9c382a921a650f9d85450d3287eecaa0869953471550434ca9c382a821a65635ca5410d328beecaa0869955471550434ca4fbb2a821a6563dc95410d32b28e2aa0869959870550434ca66392c021a658ed506050932c70a8302849969843181424cad43828421265a3993528c9328f6e0b26a29947870593514ca1fba2c1a8a650f1d160d45328eeeca88a29953474544514cab8382a228a6587dcd6414532c38e6b20a29963471590514cb0eb268628a65555c44314532c74c9300a29963964980514cb1d322c028a658e59160145328f6eca80a09953874540504cab838aa0282651e9c261950328f2e130ca81943f76550540cb1aaa2c22a0658e5516015032c6cc8b08a81965663584540cb33312c22a0659c9866015032ce2c3300a81963a64580540cb2d31ac02a0659a9896015032ce4c2b00a81967161580540cb16aa4c521865479cf54d0832a6ae22a6841953970153420cb0f2a4c721065875526390832a3ce7aa2841952e72d51420ca1f3b0a8a10654d5c45450832a72e02a2841963b54181420cb1c2a0c0a10650fdd954108328beeab18841955571153320caacb80a999065175da538c832c3cc929c641946d7694e320ca2f3b0a899065555c4544c832ab2e02a2641951e74949320caa6bac8499065c3151424c832b90e0a12641958d74d8d320caa7baa86990651ddd95114432c6ac8a88a21967151580510ca1f3a4c3280650f5d26194032c72e0322a01961c64cc9500cb0e32264a80651edd95014032c72c8a80a01967161540500ca2fbb2a629e832e9c261d0f418deeca90a5a0c3f7558f42d068f39ca5a16832e9c261d0b41a5ce529a85a0d1e7394942d071db28c0a16838e5d46050b41c74a630285a0e3a5218142d0759388c0a1683ac5c46050b418f4e1b2e65a0c7970d9732d065a38ac8996832e1c1644cb4196ae830a65a0e974318532d061f3b684a86834e1c142543418f6eca80a1a0c5f7654c5390726a9ac429c83275db5310e41b2ce3a988720d8d7214c43906cb388a621c831bdd95214a41c9ac6a90a520e4d6394a4290726b1aa5214831e5d76050a418f2ea3028520c7a70997329063cb84cb99
  | 24 => 0xa9484a147a7098f5150a3cb84c7a8a851ddd95114542aa8e6a88a2a143d7690c5150acd39ec9a82855cdc553d4142ae0e2a9ea0a15aa7290f5050b8ca9887a8285669ce42d4142ab6e6a8ea0a1558735475050aad39ec9a8285565cf64d4142a72e9b1ea0a17194310f5050aad39c85a8285565ce42d4142ce6c330ea0a1539741875050a3dbb2a0282854b9ca4314142a72e1218a0a161d6310c5050a9cb808628285479ce4214142a72e1210a0a14797694c5050a3dbb2a6282855cdc55314142ae0e2a98a0a17185390c5050ad539486282854e9d44314142e34a6218a0a159a739085050a3cbb4a2282851edd95114142ab6e6a88a0a1558735445050aad39ec828285565cf6414142ae4e3b20a0a157171d905050a9cba6c6282854edd16314142a72e8318a0a15697218c5050ab9388c6282855c5c46314142ad4e5218a0a15697290c5050a9cbb486282854e9ca4314142e54e5218a0a152a7290c5050b94b9486282854e5c64314142a72ec218a0a171a7310c5050b8d3188628285c658c4314142a74e4218a0a15397110c5050aad39c8428285565ce4214142a74e7210a0a171a739085050a8d39c8428285c65ce4214142a72e3210a0a153974d845050a9cba4c2282854e5d06114142ab4e6308a0a1559731845050ab4b90c2282859c58461141428f4e030aa621479701855310a2fbb2a6298859554d6114c42cb2a6b00a62143d769524210a36bb4a9210858ed976050842c76ca3028421639751814210b1d298c0a1085635cf6450842a5eeaa1a842166b65d814210b35b28c0a1085aad9060508428f4e031aa2214797018d5110a9c38284a88851ddd95114442caac6a88a221671515805110a9d38684a80854e1c142540428f6eca80a021659635405010b38b0aa0280859a58a60d5332a74e1aa4a99947a7098654cca3cb84c32a6654e9c3645533287eecaa0a99964e6358854ccb172a2c421e6517dd95410f32b1ce421e859963a5418142ccb1caa0c0a1665a610c6050b328f4e1b22a39947970d9151cca1f3a6c0a8e650f5d360547328eeeca88a39953a74d4250cca1f3a4c3286650f5d261943328f6eca80a19947a70986548ca3cb84c32a4654d9c46295232a6ae2314a91953a7018a548ca9cb80c52a4654e9c26195232a72e130ca91951f73586548ca97390c32a4654b9c86095232c72c0304a9195377158d548ca9a38ac6aa4654edc16355232a70e0b1aa91952e72985548ca9d384c2aa4654e5c26155232a3ee6b0aa91952c72581548cb1cb00c0aa4650fdd95415232c9ac7310a91962e5458b438cb16aa6c4a1c65879526390a32c3aa931c851961e5458e428cb1d2a6c0a14658e5536050a32c74a8302851963954181428cb0f2a4c621465879516310a32b50e0a10851961d65953328cb0eb2aa9994658b59654
  | 25 => 0x80000006000000200000020010000000000000000020028000000000200000000008000000800200180000008004000000200100040008000000800000080020000010000000200000020010000000000200100000028004000000000000000000004000000c00000000008004002000000280000000000000800000000000008000000800000000000008000000000400000000000002000000000100000000000000000000080000008004003800000180000008000000000a00000040058000000000400000040020000004000600000000008000000000000100020008000000000000080020000002000800c0000006001800000000000000002001800000300020000000000000000000000000000000800400080000000000001800800100000000004000000200000000008000001800000000000008000000c6f7654852d0e3bbb2a228e871edd95014343974e130e8721d6a70d4a5290e3d380c2a94871e5c06154a438deeca90a521d3671d0d5190e3bbb2a228c875a9cb50942438f6eca80a121c7a709875250e3cb84c3a92871d9c660d49438eae3306a4a1c6f765485250f39a8ac128a871ddd95114543a6ae3218a2a1e7161d425050e3dbb2a0282872e9c261d0c4387aed2a48621c5d769524310e3d380c2a90871e5c061548438ece2302a421c75711815210e37bb2a429087995496114843cd2a4b00a421d3671d0d5110e9a38a86a88871e9c062544438f2e0312a221c77765445110f32b12a2288879c54560144438ece2312a021c75711895010e3dbb2a0280879a5895014043ce2c2a80a021c5f7654c53d0a1fbaac021e850f5d84394742c7487304a3a16384398251d0a3bbb2a228e851edd95014342ab4e1b24a72155970d925390aab388c529c85555c46294e42ab4e0314a7215597018a5390a8fba2c329c85475d06194e42a9ce430ca721655611865390aad380c329c85565c06194e42a3ae9b04a72151f745825390aa7390c129c851e9c06154e428f2e030aa721557715915390aaa38ac8a9c8556dc16454e42ab0e0b22a72151f745855390a8eba0c2a9c85539c86154e42caac230aa72155a701855390aacb80c2a9c8547dd16054e428beeca98a72164e5358a4390b26a9ec4a1c858759653d0a42c3acaa9e852161e539834290b26b2ca7a14859359553d0a428baed298a32145f7654c5190a3bbb2a228c859694e6014642cb2a7300a32165a535805190b2ca9ac028c859c5456014642a74e1a12a12145d7694c5090a2fbb2a6284859594e6114242caaa7308a121656535845090b2aa9ac2284851edd95014242ce2c2a80a12147a709875350a3cb84c3a9a8517dd95314d42aa8e2a98a6a14ae7598a4350b173acc521a850f1d56090d42b1ae529886a149f7654c4350ac7b92a621a85651c55310d42d1cc7
  | 26 => 0x80100000006000000200000040018004000000c0018000000000800000000000010000000200000020000002000000600000000030000000000000000020008004000000400100020000000000000600000000008000000000000080040000012000800c00100000018000001000000180000010004000000400000040000000000800200000020000000001800800000000008004000800400100040000000000000000000000008002000800a00000040000002000000000100020000000000000000000060000006001000e00000020030000001000e00000040000000000000200280020000000001000000000040008000002000200000040000000001800000000100040004000800200000000008000000800200000040020000000800000000080008000000000400000040018000000000000000040000000000000000080060008000000000800000080008002003800200000020008006005000a001000200000040000006001000200000060000000002000000000120000000000800200000000008000000000000080000000000001801e0000002002800c0000002000000000400000008000000000000000000008000000000000000040008002000800000000000000004001800a0008000000000a000000000080000000002000800000480020000004001001a00000000000000001000200000080008002003000e00300000010004000000400000000030000000800600080000070000000800a0008000000000600000020000002003000000000080000000000000a0058000006800000000000000002001800a000000000000000008000000000000180000000000000801000200080000002000000600000020008004000000000180000020000001800000180080008008000800200000000000004000000e0018000003800000300060000000005000400080040000002000000200080000008000000000000180000000002000000000080060050006001000000080000000002000800000080060000000001000200180000000002000000000100000000002000001a00180040000000000000a000000000300060000000000800000000000018006000000000080000000000000000000080020000008000800000100080018000000000000100000008002002800000080080038006001000600000000000014000800000100000000000000000200100000010000000000000180020000000000000c000000800000000000002000800200080020010000000000000000000068008000800200200000000004000000000000000000000001000000380120000000000000000000000000000000800000100060000000000800400000020000000001800000000040000002001800000200020008008000800
  | 27 => 0x801a000800000100040000000000800000200000000000000000c0000000000000400100020000008000800400000020058004000000000000060000000001000400000040000002000000200280000000002000800400000020008000000000000080020000004000001200000040000004000000000100020000002000000200000000000000000000000100080008002000000200380040010000000000200000000028000001000400300040010002000000000000000008000000000e0008000002000200200000000000000000000100040000000000000000000020008002000000000000000008000000800000000000018002000000000080020018000000000000080040000008000800600000080010008002800e0008000000800c00200020000008000000c00180000018002000800000000040000000000000400000000000000002000200000000018000000000200080040020000001800000080000000004000000000200040000000000000200000000000006000800400000000008006000000400000000008000005000800000000000006000000200000040000006000800000000000000008002000000000040000002001000200000000000000004000600000000000000000800000000000000002000000400080060000000000001400080000000002002000000000020000002000000200200000018000000000200000000000008000000000080000000002000000000100080000008000000200080000000002001000200080040000000000000800100040000002000800000000000020000000001000080040000000000000600080000018002000800c0018002000000a0028006000800400180040000000000000000000020028000000000000100000000000000000000000000000000001000400080000010000003000000000000000000000800000300000008002000000000180000000000001000000000020000008000000200000020000002000000200080020008000000000000080000000000000000a000000000100000008000000000000100020000000000800000000000018014000000200000000018000006800200000060000000000800000000000000000000000200000040000000000000200000020008004001800000100000000006001800000080000000002000800000080000010000002000000000000028000000000800000040000000000000200080000000002000000400000020000000000000000000020010000000000000080040000000000000000000040000002000000000000000000000000000000100000008008000800c000000400080000000000000800e0020002000800000000000010008001800200000020000000000000200000000000000000800000
  | 28 => 0xe51000000008c487300000000000000157cad10000e0c000000027dc0000d801082f4c000000000000000000000000062c0000000000134000039a4a5841d85c1016907f00007ee3a3c3a119480000000000000000000001740ac800000000000000905000000010c00000000000040ccfd0000b4b000000000006bd000000000000000000edd34d400001d80001c900000000e07000026c00000000000f0b000000000005930000a4c0c800000dd89940000000000090700000002908000422410c21e000000000000000cd906c40000a7089600000000618000000000000000000000c6041140000000a2f000000000000000000afc254847a3ff40000000000000104e00000000000ca7000000000000000000a39000036b00000000000000221000000000000d690772b1c00000000002f5000000008c200000004300000000022400000000000000000000000000000000000000001a0000000274400000000000000bdc00000000000ce329b40000b5cf5a038400000000001be0a4f312878d00000000000d071e2c0001d3000000001220000c2a000000000000000000ea600005ed0000000000000027d8000000000000000000000000000000042a40002aa8000405c43422640002f4105f03540000000000000000007280000000000000000000000000000c653a78bf400000002970c9a000074e0264000000000017300fb00cc0000000d672f1400010f000000000000000f6613280b539500001cc45eb000000013a0caa00000000da4000212c0000000000000000000004d73bb06a23ae40001568b13000000035d800000006220000000000000033bc0000000654000000019780920000b810000000000000000000000000736000000010ac635000000000010c6199033300006830ba4b633da503819806490000000000000006e05390000abe351020f37446853d4c0002c90a890000ead0000d530444e7f42a80d408780002d9c0003d90000000068000000003c08bd536304e732ccffe0000b002ed0000182c771000000018300000000000000000041f80002b10000234cdc1107c00000009ab000000000006e53f0829f0000db700000000f3460742d000000e80003f0508400001dc00010331088000000000028481770000000000000000000000000e3700000000000000000000008c8000000083400010bf247000000009700470e412fb8e103514000036c000000e000000800000120018000000000000080000000000000000a001000000000000018000000000400180040010000002000000000000000002000000000100020000010000000200080000010000000000200000000018000001000200180020000000000000200300000000000001000400200000040002000801000000000010000001800000000
  | 29 => 0xaa90000000000000000004ce0bec0000044c95327c00032084ef00004670ef8e6d000000000007cc2ba49cb00000000000e520000dd600000000000b03000070e00000003b107bc0000d6b291000000000000000603000000018a400000000000000000000000000008a600000000000000120c000236c0002bb40000000af300000000000f59274c0002c94000000033a000000000000002eac7d800004cb1d5c00016d8f4b00004ff250c4a000005a608600000000aca1004000000021700008a800002b00000000316907d0000000000042d00003df00000000000000000000032902570000991000000034b470131f49aa2ee01550000e8b38c400007fccfa000000000008a70a340000000fdb3bb40000000000069c000000031600000001f1800000000000000ca20000c97131800035980000000000000065f000000041f000031140001ccc0003a5800000000000000000000081c000023f000000000000000000000000000000006180000000000000011a444f17dc0000d3cc03000023e000000031ad01e3f900003ed00002f9c0000000000000000000000000f1cb8f00000cf28f4b3100000000fd0c611b200000000000000072a0000ae80000e0f000000014142b7000000000000000000fcd0000743000039f00000000000b3c09b882600000003c789600d94e220000000286c81100000001bd00000000000000000000000000000a76000000000000000000e3300000000000ded0000fe200000000498000000089b0000ee70000000018c21f0000073000032f0614000000000037240000000a294284000165c00029902980000d5d000000023e8a681854549006c000000000034c8000000017100008241c200000000000000000036d40000000000000032c00000000000000000000000000000d5c000000000d1700fff000000000000000000278352c00000000000694000000000016d00000c040001f84000000000008f01e60000eef17b87c8000000000000000d28c2f00000c80000cc0000000000009a2000000000002821b28be625a4b9642c40000000c8d0000eb62b7800000000000000000000000000000000000fd7000032a0000f4d0000cfb2cdc0002cd48ef221c0002474af9000000002341010cd04d937a0c522a643f50fc09ba03d0d63057cd23065000000003a93d04000000067b00000000000aae34cc9d730d0dfb071c8f93e5034910780001b7c0000000000000000000001560000ecf000000017080003f7c00000000000000000000104c00000000228e190000000000000007b8000093800005380000000f9f2b84000000053d000016f000000000000001aec4e5202400000000000000000000000005886a700000000000000000000000007a400000001b443c00000000007400000000
  | 30 => 0x32fc0002e0c9d900004b923e09d000000000c6cc2c3414fad3eec000000000000000000000000419471827b4000000056f000000000000002d0864c0000000000000042700000000000000013a000000000000000000000000000005500c70000b7100000000000000316c0001cec0000b1000009fc00000000003ce800000003520894000000000000009c7000000000000001580000000091e000075300000000000a3600006200758481000000025ec7340000faa00000000000bf90000000064400033701f500002eb0000000000000000000000000a50000000000009bf00000000000000000000038549d218680003e0c00000000001d54dcc1b900000000821000000000006240000000000000000003a70000fa841bc0000000000000000000000000000000000071b0000417000000000002e004b9019322800000000001e48000000055400000000000000000000000000000000000078800000000002b14b6c25c80e93d3c6a800007a3411cb6b005c3ed23440e627ac1f204d0832336805b02c461b3c6025900000002064000000000000000000000000171c0000b7ce6000000001cbcc380e6443a06dc6d60e20fe70000f2713d4000000000002440000000c3103443ad0000b6a000000000000000000e0a0000000000000034e80000000000000000027a40001c480000000d7f0000b800000f5d138000025d00000000dd032d00001f3c21619a000042dc121000068b35c0682000109239b000000000000000000000000000006ea08a0eee000000020e08d900000000000000003853711f40003048fda3008c5c37d49ee00004b241ac00000000000000c1a39e83d60000ba01d9c0000000a8d213c9c900000000000c4b2a588e700008890ef46ac3388296216872d1cf0000251c69d0000000000000000010621ff80000000000000011e00004d600000003af000000000000000aeb36880000000dba0b440000000bde00000000000000000071900000000000b0225f0000000000000000003b8c566388c00009940000000000000000004c400006d8066000000000000000d00000000000004a80000000000372000000000000000a11000098a000057829d400000000000000f06139800013a49fd0f300000000e8d0000000394c00000005bf12f400015dc96f08209a00000f68000000010c800000000003dd800000005520000000000000000000000000000000058f2ea4000000070f0000bb1000000011cc00020e40000000865000000023a869a3424000287020300006be3fac0000824fbc032800000000001f002ae00009b90000000000000000000000000000339c4a91728db617ec070000000000001c200008ee42e00000000000000000000000000000000000003b00000000
  | 31 => 0xe0c0000000f9100009ac0000db30000ada169c46c2ee8d5708e02bf000019c06840000000b2e0000956000000012b47f31dfc0000000b0807a427d0000000314400035880000000341000045d0000000000000001b0e940000d780000000000000000000000000b8c000000000000004084000000087c3c9417200000000000000000000000000003dcc000000000000000000000000000000000000000000000000076000001d92b00dbe2d480290390000000030f26d8a6600006760000000000000000002420000600000000004f80000dcc00000000303f4c0000000000423ca490000000397869031c400037145160294262118088f046048b2134000421c00026580000000a4b024054c0e50000000025e34506bf000000009a0000000000000000000000963000000007380001138000000000024a40003bc0e591ba4000000000000003260000000000000027900002334117200c00000000000000000000000000000000a6c00015f09dc00000003a08a0731d0b1e117c000000077a0e74872313c00000000001e000002a7400000000001c9cca30000eae00000000698a47000003400010043664af80000e2400000000bd03970000000000000027e49fa000000000009551350000000000000000000000000000022b00000000000000000000000000000d1063c000000007446d7000024f34f40000000d9f36484c90b580000000ee21b7017a0000cf6000000000000001234000000000000000000000a510000d9a29780003f8c0000000a56000000000000003f246c400000000000e630000d0c2e7c0000000000000000000000000e98d5602a80000000000000000000000000000000000102f0000000000000000000000000000137cdf3000000038a800000006ed2cc00000000c7a00000000000cf1000000014f000013b90540000e87000000000000002204adb00000000000c0b3b4846f1f4800000000000d1c000000000000000000624638265c00018500000000248051c0002c24000000000000000000000000000000000010c41c707f4151c0000000000176cc680000000148800000000002a1400000003d8387c000000000000009410000000000000000003430000000000000037c000000000003c2400000000003fa800000000000d88385000000019146b934446a1146400000000000fa0000000000030980000cb8000000051a000052d00005d3000000006bc0000000ed103f10112e28ebe000000000000002ca44a1058c0003a20eb40000a100000d1f000000025502060000000000000000000000000000000042800005690000000000000000b0000000096e000000000001b43b1cf720000000000000000000000000b92000000000000000000a98266cb5812480000000000409800000000000000
  | 32 => 0x4b690000d3100000003bd466900000000000d901908be0391006a1db83b90000ca00000989123c5cf19b85b5000000000010ac3ce00003a7c0001270246000000000000000d2c00000000000000000000082a41280000000000000042c37a482b3c580003d581130750ad224dc000000000000008f035c4d501354d101f3813c0000b163e20fd1000000033cccee0000b750dd0a191784b610000a5f30a00001018000000000038a000000002fa00000003ac80000508b4d00003f10000c202f7cc07048c0000000000000000000000002db40002b0c2890000000000038a38f40000000000000064a1f2800010540000000000000000000003cf415ce0524405290000dee3de10c11008024330cbc700010140000000000107432c400000007e70b8400000000000000fcb29b8000000000022480001a7027534185fe205c4a40fbc00032780000000000000000024b800005f49b306585f23798bbc000054f0f8421906c0000000000034840002804ad900000000000000000100b000000027bc0000000000057400000008f200000000000284413400019f006100004400000e9800002640000000399400021d8e162e6008b000078a0000b7e0edc000000000027880000000000343cdc400009240000000000000000007ec00000001fb4beb00000a32fa800000008a52c640000000000410098100003b4000000000000000000a8b00000004190a181ea4000000015e12181a932980003b640000000000000069500005bb3f6400000002a2084cd653684bf11aa80f6000007a0178000000080016cc000000000000007cd000000000000000000fb100000000d98000000000000000000000706000000000000000000000000000029044681be45120000000000000009c0000020400000001cf00006111cfcbf600008b7000000000000000000ba43874000000027a402800000008930000de025100001f445fd25342da00000000570bfe321ce4e000000000000003fb00002c5000016e829100dc00000009850000e8c0000000000000000000000a5c00000000003a40000000000012ac00000006310000000000000017186c6000107900001100000000000000034aca8c000000031000004258c3a000000000002110000c2423208dd000105a000000000002150000000405800000000000f547ac1878000032cbff09580000c00a0d1e7800002746b80000a9c1510000000000000007d6000000000000001efc000000000000006d00000000000038400009e008680000000e021b690a72e7800000007b610986713aa81880828b8b000000000003e605000000000000000000000007740000e2f17140001e1c946000000036280000000000000000000007aa0bb05e30000000000000003b000010bc0000000000000000000006190898000
  | 33 => 0xe3e302c3000000035d469e0000553189cfc0000032d09f0000000003c000000033780002c6caf521a81570000d0d00000000000000000109a3e9c5240000d2f34e023535dc5dd2368a773324c3f00000001ad093040f00000000c230000df8000000000000000000e4a0000c33285c0000000afd3fd4f8702d80003b04000000000034a000013ac0000000000268463b0000e680000eab25a0efc246474000001790000d82000000000000003ba855d1964a900790000000000000000002cf87c9000000000000000000000397c89400000c332a40001fd84d100000000000000000000000000000000000000000000007b000000000d403281bcc000156c0000000000000000002bc89c000109b00000001d7c0002ad000000000003e140000000684000000000002f500000003e6400037a80003c30d3c26000001ce8b2800008f7000087b000000009300000c8800000000000000a3801dc5b8000000000009db000000037f400000000000000eb5000000020080001a9800034640000000000000000029680001544fc50000000000088d11ec9ea11f07f100000000000ae541a83f940800000000000000000000000001f1447f0000000000084500000000000e1739cc8cc000000000000830000000000000000010ae00000000000871000000000004dc279500700000000000f4700000001ffc00000000002ebc08f00000000000491000000000000000000b560480000011c367006053b0000000000000000000003b8400000000000360da900000000000000000000000000000000000000000000000001a20caf19100000000e200000000310428c00000001ce40001b480003fec000000000000000000000000020800000009e328ac0000000000019cb220000000000000037f0a540000ee900000000000920000030740143630000bc912d498f2508026073433120bc6ae0000b482c7ce930d1400012b8a1f092804a0780d911ac40000000abf00000001d745c43c503d71920a2215d80002dd8ed315d0f110000db400000000000000000077935ec6a000000000000000000000000000000874a6c00000000000cd4000033600002ca0000b74000000000000000a5400000000003f60e6a000000000002b841c4321000000000004bb28a03b3228c0000c287a724fc90c23f000000000001eb8e5b0000000000102700000000000b470000af7000000000000000000b2a3fc06622b310033c0480100003590000b0500000000000b900000bae2fe018d22080000000adf000000040b0cc6000000000000001f507b41d3cce600000000000000000000000000a00000000000093a156400000000000f480000000000000000000000002a2800000000000000c0a00009330000cc818ccc141514b7c22e466100000000000000000056e28b
  | 34 => 0x696349c762000016b3df05a3063c0000000d5e000000000000000000e660000000000000040b80000a1800000000000000000000035d40f40000000c1921e4000000081d37840000000cae0000000000049f00005f300000001660000245800000000000000f1f0000f600458000000000042c8000000089d0000000000000000003e30000ad5294c95d2c0400000000000000752000061c3ed8000000000000000003c100000000a9f20c40fd08ec0000af8023000000000008b00000000110800006f0e5d0000b21000000000000000000aee38780000000000000071e0000000000000000008b1000000002fc0000000000267c00015ec90036780000c0c000322c00000000000000000000000000000003aa4000000000000000002d145ec000000000000000000000000000000000000000b430000000000000000000003cb092d1a30000000000000000000410ee6000000042acb23000000000000002cc800034fcc3d03b8f323f3c0000000000000000001c400000001f3000000000001001b080000ffc000000000001f400000006ee1ec8c1b12300003894da000000000000000000000033d41cb2be800000000003984000000028300000002f60de400009da000000022380880000b4400007382f2039500000000000000000000025f4000165400000009b2000000029c8eeb00000000000b1531f849900183aa000000000004b12218dd900000000000790365045e15c4d46000000000000000000000000000004a4a0609ac0000000000395400040000000b0800006f4b6640d80001af00000000000000000000000000d900001150b77237800000001123a700002b50c09004c0002ae90420000ea800000000ba863925e8ecb0000000316502a0000000000000035e8000000000000000001bdc0000c300a926b481f000000005800000000b0e0000d863b2800000000000000000000000000000000000000072400000000000d84588000000000000002f886d51f98aa0000000034380002784dac3d0836e0000000000000000000000000dd70000f82378cc5414c0c6f0000edf000000000000000000d550000f9b00000001a900001eb400028e800000003d00000000295c000374c00000000000cfc47e3fc4a201790a3c20f46b03e380001ca400000000002830e2c00000002fecd4c144c0003e5c00010f8000419c94c000000000000000000000000108e00000001e045ae00003b130440000000000025c0000000af00a380000000a1600000000000000414887400003173134000364c2ba000035b0e0800000000000000000000000000b40003db800000000000000ba3116806e23d80000000000000000000000003c8c000000000000006cd00002dc1c94e3418b8d1a000005800000f501f00000000e7
  | 35 => 0x3fa00cc00000000520000000000000000000000000000000000005cb0000f613e88000000044631b900200010830000cd53e800000fb80000811072000000000000001dc0000000000000001db00000000a2800009240c11f0800000000002d400000000d470000000000000019400000e2400000000000000f1b00007610000bad0000000259c080350459b07301f933a00003de40001ec4b49000070900000000000000000000001a4ff30000000000000000000001d1c0000000337000000000000000c7c00000000000000000000000000000001cf4ed0427800007ec00022d845c0000000000000000004af00002c600000000000a7c0b542a70000a9525900001dc80000cac00000000000a8c000195509f0000d8f42740000000000000000036c40000000000002c000154084337280000000000000079b0000d34000038b0000000000017021b800040180000f280003b54e4200000000000000000000042ecf1516280000000000000038d00000000000000084000000000000000aa100000d729f451400000000000000000000003480000000c9300000740000a7b3bdc40434b800000009182048000000092c0000ddd273c11a000000000000000000a9e161008c00000000000000121c33d000062f0a78f0500000001f880003a0400004b400000000000000f2622e0766000000000000000000000000000014b80391ab4000000000023d0000000000023d400000000002a000000000cd0000094b000000000000001348670386800027183f6038c000130ced8222856341b80003818a3e0960da628d40001db0000428c02500000000000a7a3d2866d00009b00100c6218140413c4c3a2000081000001fc00000000000000000000012a858d1624b1215d400022cc00000000000000000219c0001024000000108a0000000229000000000000000000000000000005a90a1c94a08840002a5c0000b3c21c00000000000000000088300006780000000000000000006db0000000000039c05ec000000000000009782324000150c3d400007050000000298000040ec0001a047f000000002ff43ae0000e092b9c00022407a5000000018342c000000000cec00000010a60000000019023a4254e3e36b8094000000000000001ee00002ea800000000003220000000000000000002f0400030c82d90000000127801c17603910000dd827c00000000000235c000000000000000000000000243c000000000000000000000cac0a48ec200000000000fd63e84d010000000431400000005041be882200000002a8800000000003b6c00029c00003e2837700000000000a0b00000001020a7419685961c7423900007210b6cf6a03bcc9603240000000000000000042342f8112400016480000000000000016c1334000000000000
  | 36 => 0x14c482000017616840000000000000000000bc0000000000000000000000001268e183e10000000000002dc0002de10083b243f81554bc30000000000000022c800000000000c2c00000005000000a631c690090000000300400002540000000000000049632a01f00000000000000008b8ae341780001d2c00000000000000d39000000000001ef2124000000019b0000000000000016bc00040fc19a0000000000076d00000000000e47000055621180001fa4a592d30aea00000000000d290000cea000000000000000000bc00000000383400010d4002000031300002ad00002340000bcb0000000091000000000003e90000000000025980000000ce000000000c0800038ec0000000c22000044800010b039e41840000000256cf2f00000002d8053f09dcf08399c000277c0d600010340740000407c000204cffa000000000008d515e80000000f6722f000022f80000000000000000042900003d7847600000003be40e500009f413c400000000002a0c0000000b390000cad00005100000000103c0000000000081413700000000000000000000032f400000010600000565000087f000000006800000000000347000038040ba05a4000000000000000000000000428904400000000000273000000000000000000fb731f09a900000000000a5200000000000000000000000010812c28000361ce8a0000000136c0000c60e780000f6500000000000b0700000b30000000252077b13f02710b8c0000000000000000012d029d0000000384800000008253cac15900000003ef40003bc800003c4b261da8000000000000000000000000000019f26d4000112c0001d900000000fd515cc0ea0d7c0000001035289814b029805430343983788d8429750b927f80002e1000000000000000000000000040906162a440000eec00000000001c8c000000000006080000000a2500000001fbc2f6000000000000002bd07df00004ba3820c151cac000080800000000000000000206c000000000000000000000ca100002d800000003200b3d17e4837272809c20d40000b4c7590000851304000000000000000c5000000932ee4000319cf291fdccb80000b910000000000101c00000002a18b181a6029a3af500c22300003c3cce52128000000000000005080000000000000f161c000000000035a48c70000000000000000000000000000248c00009c853e000000029ac0003c9000033b0aab000000025b4ea33de845307f456b1f782c119709251e84000000000015840003ed4f1a2038f9608f438f3fe06171e30535000043600009b81998add00000001b7400000000000000000000008428ec000070400000008df037400018c90780000a37422c000206852a00000000000b9713783ac20e80001ee400000000001040716000000000000
  | 37 => 0xc36130000006400000e1c0003db0c040f88aa600007ab0ba0da829e037a00000000000aff0000000000000022bc854379c0000000f33110c4560000cb7000062b0df80001200da423846c1110417c26482bb31e400000004c4000000033901df205843307110591ad800000000000000000000000000000000000000000000042f90882424699000000013e500f2f1042523703e72f383863624000000069300000000000000000000000010990b4000000000000a5000008a8f1c3afc0002a1c20c000079f0000c7f0000797079400000000000000000000000022ecdf605a00000000000000000024f8000000037900a831c3e4c019168901b412ca40000000000000000000065000027e1dac0000000000000000000000003018000000000003fcb640000000326c60e0000000000000039c00000000000000000035b000000009fc07e00000000000000000000004453700000000000020600000000000000000026980000000000000000000000000000000000092a00000000000000267800000000002d7c000000046100003fb0000f7716e400000008520000e460000e5a3d0000038840002738710323c71f2e7000013040000000e6b1608722000000000000b21bf000032f8f740000b8600000000efc000000000027c80000000e303a8482e000000041ec4940850f0d00000000258f0700010932ac8d9d0000bed0000000000068e177c00009549360000000357000042b4000000000000009c300000ac000067d26a00003b584a8000000021081e100000000000fae0000c9c28d000004b0000000000000000001abc00004940001a280003adc41b00000002e98585000054200000000000000000000037d00000000945000000000005b1000086400000002dc800039202f200004880000a46000000000000ab12100000000bcf0000000201800000007dd0000fdc0000af628900001bc000023a08140000000129400000007a032485d91c805f600200000000ac90000000000000000000003b942300d180000000000000000000001b3094000000000001a2498c384c000000000010a8000097000010280000000b46136059000000483b5016600000000000c37116452f0000fb23f4000014750a836e400030f85bc000001e037c1653fd00000000d7d0000aa43e7400000000002d5000000000000000ba119e4000000067e39148f32c18413000000000000000000000000090300000000000e3600001321dd800000004e3047c00000000000000aa800000000000000000000040f8308282800000000002dcc0002e4c0000000e7b0000000423000000000000000000000000000004cf1dccca50a8094f2f2800000000003a1880c0000000000105100000001d1505d00000000000e111720be42854b7f0000000111c00000000003
  | 38 => 0x1368f0e090c0003bf4000081c0000000000260c979250041924d0000000000000000002fd40001bec939000000017a00002078000097477d000020000000000b880000000ab1000000000000000000000000000000000001bc88440000da7358400000000000000000000000000000000000000000000000010393d300001c985cd1d8cac20d7000000000000000b38000000000000000000458000000000001413344af2000095a233c0000000000373c000000000000006ce00000000000e57000000000004213738000000000000000001aa455800300002d54000000028100005f8000000000003580000000161872e2ccc60138fc380079c0002eec2dd00000001a3c000192c2610050aad3e4000005180003778000002850130b80000000000410c00000000000000c1300000d3000000036c8d8b00004be00000003d7c000000000000000000d08afb2b980000000000000000000001ac000000000003110ad40000000c8c00000000000fe10000000000000000002533a38f48145400000000000b142d4000000026f4000000000011340000000b8512286362184046000000036fc2cc00000002f442e519c8000000106c152ccd800000001460000000000008340003d8c00035440000000b1d2a4800000000da00000001e38b5d000000024486ab0000000000000000000003e98000246c000000056d215800004e4c850000000311000015c8199000000027340001e60000000000000004933084687335c64d00000000001013000000000000000000957386c000256400028c80000000000209c00021880000000fc8371c0003014000000059c00000000000000000000012e04cc3bfcc1d0f4c8d800000003a6c0000df06a30000000000015a00002a800d40000c787e327080003ea4000000000000007460000000000000036f4a33000000000000e03cdc9320000000000085f000000000000000000027242cbd20bfc46e0000b82000000000000000000000000095800000000000000000049d2c3c0000000000000076800007490000b940000d48408800000000000000000000000000000000000000309d02b000079a3ec00000000d0b0000cb608bc0000dd400007b000029880e2238009f1d3400023f80000000000101d0b51d208d03c64fab249cdaf31a800036a8000000000021b000000000000000000000000000001ed00000002f94000403400000000000000bcd0000f460000646000000000000000c9000035380000000ace2d7800000007eb000000030300000c386412100b1700000000000d220000000252400000000000000d883f500000454d13014863f3e600003cfc0003cb400000000000000ae013d800012fc252371800000003ec067800000007931cdc0000000b6e0000f5b0000
  | 39 => 0x8c30338a793a4800000000002efc0000ed452c20f8cfe27d4000389c000000000000000000000000026c57036701350ff4000000000021f800030ec99a0000eda22540000000bd70000000000015837c83dc07780003ee8000000000031d4ab926643de2ac011b38f0d9635bc3103c88000199400000000003fb40002d5cdf700005a534f8e0400000000000977000001024c47bb0000381000000000000000000000000000000000002398744350c000000004318240000000000000074a000077c0000e710000000354800000006b224f400038b8c4800005093e240000001055000000002186d82704d121e18a2317d000000000000000c2b00005020000b7a00000000000000000106d40a00003038000000086b0f6c9bc0000000000027937ac0001df8000000000000008b42c2c00000000001cd4000000000000002bd000000000000000000c4c000000035a8000000000000000000000ede33c81e80000000000000000001b900005ff0000000334c2ac0c48c7805480001c3400000000003174da51074d80099c00000000002778d0a1884000000000000000000000000000000000000003ae00000000000012400000000000000000000000023a4b9900007cb1dd4bf0242027413d0ecd00002fc13c00003b7009e0000000000000000007881d580000000000000042e000034d3210dd200d800007000000000000000071500000000000cfc0000000279c00000000000000d5f00000000000efe19d00002d884770f380000000c5700000000c243fc39dc000000000002f80003fa40001b6400000000004170abd2c400002154000000008500000000000dfe000000000009f300000000000000000000000000b80000b0d000059111ac0001f102b400007db00000000000000000000033c000000000000000000000000000000000000bb000000000000000324400000000004184ceb0000877000000000007b50dbc0000000cc5141c000188c84c27580002d700002e6c75a1d040000000128000069f0000eb000006d300000003e5495c0001097000059e00005ef0f2400000000000000d2400000000438000424000000000002b4000000000000000000000000015a00000ae40000000000000037100000002fcc1190000000000000020fc00000000000000000000054a000010d41605ac14390941f54000000000000000000000000159c000000040000000003cecbec00009950000000000000000000000ea0ba5028400029c424b3f1c000126020b1d4400000000000000000000000000009a5000000000001870000000000089f00000000000b7d00000003850a6a00000001b780000a6491300000002f6c08e000083616003c800000001518e03000000038e000013f40002174000000000000000000000cc700e05dc0000f50
  | 40 => 0xcc80000000437187400006900000000000000000000000000000000000000000000000000000000089100000000000d1e18400000b3400010e46f600000000000c4911905f00000000000000000000000000d02146c000000035100000001f40b3b00000001f040002b18000000000000000000bc4a4800000000000000000000033a400000000000d4c00005b8000000007f1b24149245c000000000000000000000000000000000000000000bbd15700000b20fd200000a8000000000001753c5c00007741ab00008c00000ec500000f200004f3000000000000003a9cb65000000026c400000000001bd40000000f393160000284c00006385e505400000000bda1e0c0002fa014d0000000000000000009652acc00039f43af1390d403274d7925c4d370e6882d413cf9c06f86c00000c293d540001fec00021a40000000d0800010410000000000093c3f300000000000390cf283c80b5b28b8a21050c000000000000000000000000000000000000000f6400000000001fe40ed000083b18941c53c0c18a2a3c0f800000003b380000001012000000020280002e9c3b80000d8e22f4032000000000000f30000000140cb6f382c00021b40003d5c0fa00000001f64750000000000000000000000248866c1d6c00000000000c540000528bd61b2cb681c4c00040c45d40000a0411e40000000a2c3c40d2c3e48237309450d01e000000000000000000000000004e084813200001f7105b3b0c0002bc40c51b303d12adcad60000000000000000000000a3c0000158a2700000000000000000000000000000000c2d1d5000038a404500009d52b5c0000000000000000000000001b800003f747003b186b300000000ee80000000000000000000000000000976000000000006fe2af102500007912bb000036c049b0000107000000000000000000000068c7be00010a51c100000000471147043b000000023ac00003f85c300008570000eaf00000000f2c000368c9f100000000000b0442bcf430ca4000174400000000000dc8000000000000000000000a7310148fd00000001cc000000000002138acb00004e2356c7940000a4a0364000000000002b86d40000c5f00000000000f7d000051f00000002ed46c300005832cb0d85000061f00007423e6800002ec059376c000115400005a853800000000000bb200007e80000aac0dc0000000000000000000001066337cf75000000026409150ff800000000000000000000000000000004040000000047500004ec00010500000ef4000000039d4ea50000000000000000000000000000000000000004b723383e0000000000000000000000193c1c600000002ae06eb0000000000000033847fd19dc00000002f900008a100000000000000346c7110000e6e051043f00005a81198000000
  | 41 => 0x22d447400000000000dd40000c8e0f900003f980000000d64000000030580000f680000000000000000000000000000000000012b0e4c00000009022cb41813a245d53d5000040b4c5e16dc26d00002a600000000000000372c40300000000000d7e000000000000000000ac10aacdda2180c432c3057931ccc390000000340c00010e000032d400000000000000000000000000000000000000000000000004290000be300000003b3033c346000042f479d000000000006cf000045200000002bf909100000000000f6f0000000000000000010bc0f10000000000013dc66f31080002a8c000000cef600008aa000000004fc00000000000000000000000000000001e14de500000000000000000024127a0b8e1314000000044c41cc2f73328489000000000000000000355370c4b00000000000000024447d300000620000a0900009983a0c0002014000000000026bc0000880a6531dc0001fc800000000000000000000107a1590a9324d4000000000037fc6f10000000104800000005e70a9400042e886f00000001bb0000000072c000056a0b90f211ff0000001c0000000000000000000000000db4e4c0000000097c00000000000000dfa0000478000000000000000000000145c000078c1b20000000000000037700000000e6200000000000cb03a800000000c4632f000031544dd1a342e70000612184c00000006370000c6300000002b8839600009140000000418cf45392c26600000002e1c67a14cc0000000000000000006ec0000e380000000000000000000000000000000000000000004ea00000003b5c0000000000000000000000000b98000000013d00000003970f8d00fc00033e0aa7181800017e800031b40681d7059430d428827980000e78ccc00000000000000000000000000001f0c00000000000000d981e88fde000000000000000c6863a0000000000000000000000000000000000000000000000000042800000000003e1800031a453400000f9356804e00000003a10000000000000004621e1000000000000000000000000000000000000000000000000000003fb8304000025a000040e00000003ebc000000000000000000a2c00000000001288885387000000000000000000341053200000890000000000006f348000013f8d83290c1ea2fe8f7f000000000006b700000000000000000000000000000bf85a000010231e70293000000038c854100000000000000000000000000003070f9e030800000000001ad400000000000000000000000000005ea0000000000000000008ad0000d4d22a46ba000000000000000000ec00000000000000011b4000000010b000062c00000001ba0e490000000000035e0000000000000000000002cac0002020000000000017380003f108bf2b4c898000000
  | 42 => 0xd218990b30000ff70000e9532186c5264cc473310000393400034000000000470242800032ec0003ff08cb208c000000019d000014535d00000000758059c3f32f080003ba004b00003050000e2d00000002868f52000000000000001fd40000000d6d0eac00035a0e0005e0a4e2b3ca0000000000000a052ff000000000000ec80001c309ec268c00000005b200007ea086c0a417800000000ef123b4000000000000006632dc00000fe8000000000000000000000000000091f1c2c00009000002164e6400000000000000218c0001a5080735083560000000000000000000003458df900004c71eccb361808f62239098806e800025fc5d0000000011940000d300004218a941070b1a000000007d097505f831d3ae80421b8800000009be03406e10e94cc10000000366c83328081d3000000000000000000bb726700003d3800011c8f8f000000000006560000000000000000000000000000000000000001d50c8c0000000000365401200000003240000000000000000003a000000ef0000000038c0000000000000016f8000000000000000000000000000000000000e72b701a221f506903a00000000d602a940003c48000000098200002ce000055e2fbc000000000000000000000a033d700000bc099d00002bc00008c1000005c0000416000043d27305fc000000000001f6000000000000003000000000052b0000000000000003dc0002f180000000b9d000080d09d8e9904bc000000000021d400000000000000000149442400000000000f303308fa33b80000000000000000001444000000000000005bd00002a403c0a2a09a80003f80000283c00042800000000000000020e000000016309873204000000000039d8000000053a0b78164000000000000000000ee40f1894e1fe0c3c28fce4f02685b000001142a101952d640000000c180000000269000000000002a04d721758000029c0000c94efa0000000000000000000000000000000000000000001e58000000000000000000000000000001500000000000000000022200000000000000303c3b60000000000000031ec0000000841000000000000000000000125c05f0000000234884700000c634c00001498000000000000000000da810500001da000000033e5070217000000000000000000000067500007bd22200001a48000000057f04cc55700000000010cb200000000000000000096c2160e4009ec2b60bbc46a0000b2f098c0bd000000000002f300000002f640003f180000e489040000bf71e24000000000000000000000f71000000000000000000ab600000003fc856207f80003604c9401800002954000000000000000003ee40000000000000400000000000014000000000000000003708021000000000000002a3863e2c80b3f000065b201000000
  | 43 => 0xc080000000000000000007e522b00004054000000022700000002f84db813e86e7000000000000003a440001e542ee194485000000000000000000059d0000000103000000000001cc80000001046000091a0000ba2000059f4200e6f000000032ac000000000024ec000000000000000000000000149c90e0000000000000017680003498e9d31c08d4000000038e800020a01730000000000000000000000000130070c0000000dad3e040000f0c000000000029f80000ec00000000b8900005f1000000000004a3205405d112800000000001c0ca9a0e8c0001f80a4d430c00014d80dc353c000091400000000001e08000000000000000000dfc33000000a209bc0000000e8507e8f31000000000010370000f3600000001f68000000101a1bbc80f2ed823300000000000f7b0d5050f0000000000000030c0fb3118c00000000000000000000000000002c700000001c1c0000000a691140d54091c00005fc76500000001de000000000002a080000000fbf00000000000000000000027e000000000000000000000000000000000000000000000014180002278c72000000000000003e2c00000c40002de43a00000000000000018b40000000000000000000000003acc52009a4000000000024e00000000000222c00000000003e000001c5c4512d2800000000003a88ab500000000000000000000000008ca3ac4647000000000000001ee80001810000000000017a40000000000000000000000000000000000014c00000000000000307c7e420c025400007af000000000000003fd895f14a0000000000034a80eb00000000000000000000000000ad0c9c00000000000000000000088008b000001f84201f5c000000031400008a033740000000000000090d0000000000000000000002310000000000016642362bbcc660000c8900000000000000000051e2e2004434746342e54d8d000006b1bfc54d000000019740000000000000105300000000000000400400000000002c4501826347fa296c0000000e39098001f000000000000000000000153800037bc4a60000000060c8973e9400000008683dc0000000000000007a800000720acc0000000ddf1d780002178339000001627ec00000000000a40000000000000000003f0c000000022d34547280000000000000000004ac19ac0000a146970000000000000024980000000fe500000000000000000034e105000000000000000f5800001f700004f2000000006a0a61000000000000000000d3b041812701e400000000000000cd635b85d70000000332c00000000000f1452131b10c20000efb0000ced000000000006861f1cea400001c8000000000008ec00002120e408e2257800023fc000000000028c400002f0000000108533d0fb83d24444148c2fd1cf80000000c
  | 44 => 0x13ec0000000000000000001543782418769000013b000007b31d800000000000000b3a00005c917890753524a6f06a80001820cb914c400000000c4000000000000000000e9712d8dab10c437d0944c1e10440000000e9a22b86a50424d5812403ea00008fb00000000000973235839b254c0000000000000060a00007b7008000035cc0003f28000000000000001d700000000000000320c45700002c90000000000048e0000000000000000000002ecc0000ce041a0000000000020100000003cf800018a0702014471400003a400001533cd08e316ac000000000000009210000e50000103a0000c4e2d3c00000000000000000000000031900000000000000000018c0dcd00002aa0000000040800010600000000f2a00000002838000000000035f00000000000000025b1dbc0000000000000086606fc0003264ebb000050c00007992a2015b32e800000000003df80001938000000060f00005ad199cfac109c087015c00001408ab3db4e2600000002fc800013b41b512f0bcc2e68000000000000000002d0010f00000000000000000000000000001ddc0000000a9b000092b33dc00000000003958000000058e000000000009a7333815100000000000000053c00000000000000000000000000000000000000271400000004e100003683be000000002a10f7400029fc0004120000102c03e142c00000003480000000202c0000c18000000000015200002d040003cd4000064862a06304230000ba801305d204d8b2722e85f5000066a00000002b902d212cd06838ac9d800000003d440000000962190cff9333c00000000000000f6b00000000000280000000000008c537b00002b2000000002ed00000000000000000059a3334223261002e014cdbc262d00e270000000000280000fbe000101d0000000000000015f400018f40001778fce27fc00000009502d440000000000000000026ec4950000000396000020f00000000000000019303003f700000000000000000000000000000cd4000000000023c502904905aa0000000000000000000000abc5401bf4eac0000ef33cf000000009280fac00008a40090f081d2240400000000b000000000000000116c0000000a1e03789dd00ac70a0000a0825f8df10f9400000001eb21c000009346531b1c7a62abcd17216c0000000b1c000078f0c64a450000000065c00005840000000d4a0000000000004d00000000474485000000013e0000000000001b4000000000003342b1000000019fc0002618000000000000000002f7400000000000000000000000000000000000c56000000007600000000f3d0000a67000033e0000ec81308000383800006b8a1400000000000d5919601ad000000010340002fa4fef0000000336c000000095126389b73754000000058b00006e60
  | 45 => 0x17980002eb03e9305c00000000000000000195c000000050a21e8dbb01d400040c000015f88532b600000000e3500000003c0000000000000000f0a26d0a1d26b830d365cf2e24bc0000000e7c0000000000000000004a7349400000000001b8cacd000000002601982e34e720000000008800000000000000000271000019cc000000000020a4000000089a2cd0abb000000002e40000000c98000003d272069b258416d000000000010320b2c3f22d685a42d4c69115b0000060000034d80000000000000036c2080cff00000004260000000000000000000000000000000000000002ef804f0f04f1d23188e541248a20000e740000000000000000000003d1096b00010b602d0a3000000000000000000082c134c0004208000000037b16040002d38000275064007c4b7b41582a925a8
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x9310c721a1a80d906355221a18835506050a21a148454c614ca21a18835526090621a1a80d506350621a0c8454d620c621c44655c4434c921c0c75191324c521c15651d1310c42191487551310c421b10844c43154021a2a8294c6050b40a1a839486050b40a858110d620c640e044358a510c640a14835925188640a458114d620c54090d821c55310c408b1811c96010c408998798c6090840c92635c46090840a1481594434c840988825c0434c840b098010d524c84089a87d8d6050440c8b631c96050440c15655c4430c440a858110d620c440c90735854190040c897318a4250040a1681d50635063091687d51310c530c14641c5534c720a1681d506350620c15635c46315120c28541c96090520c28541c9608c520a2a8298c6055020a1a839886055020a1883584605502083887551600c820c88744c9600c820e09544c9600c820961821c14354420930845c03254420d41325c03254420c61725466090420c307454560c8420e09535894010020e21625454010020c29659ca4310020e095454d6210020a298510d6210020919859ce4210020c19659ce4210020c8a7358a4210020e22545895110020e21545895110020e42535895110020e41535895110020b10835d15110020b20825d15110020b228290d5110020e22745895110020e21745895110020e22435895110020e20435895110020a31869095110020b12839095110020e21629095110020e21625474110020919851cd4110020c19651cd4110020c88735894110020d10735454110020e216254541100208aa86dd13048020a18865515348020c88645ce42480208a9871923248020a30869515148020a30865515148020e106494d5148020e106454d5148020e21821915148020e20649095148020b41839095148020b21848c95148020e20648c95148020e20644c95148020e206454621480208a9871902148020c88645cc2148020a148158c635531091487551310c710c8474589310c710e0554589310c710928875512008310a18835506050910a28825506050910c2874149600c910c8474589310c510c287414960c85108e1821c56310110928825d44310110a908158c4310110c91635c44310110d20525c44210110c60755892110110c1875191324c110cc0764c9214c110b40854c9214c110e80644c9214c110a2a849905248110a2b871905248110a29871905248110e08649cc5248110d09745cc5248110e08645cc5248110d21745c45248110e20645c45248110d41735c45248110e206414a2148110c30751912148110a148454c614c810a1681d506350410a1a80d506350410a0d82150635041081c87591530c410a0c8454d620c410b11831514144010b21821514144010d10541cd4144010b108454c3144010d117454c3144010d41535c83144010
  | 1 => 0x7db2b231b2800861b14000b800341ac00660400a000000000004980000000a2740000002e40000580010a00540d58a45000a4007a0009400a60da68167f03a088600000012800440017600001d400a4032019a0000000e6040b9aca47b000011e0020058aa7c1000042ac001b822305f000cedd1d8fcda5d44aad7ec454864c48b578745a02420001cc825a9400372a0612c0011800aec9000885c00000000000619780000589a00000000a800001d0d1b0480f33c00d1000009e00000000000512dcd853690c9300065918000026a9c820300000ca2c00109800030800004a46800105f34b38a27817800e0910780000000000000005b265a8a304a4888000d2810eb44f8011c3850a5d140057278ec002c190fc00000008ebd002cc0000060001a0039000010601000010080c040000800280001808000306034260202004040102808020000004040f040080000000000000008080004078080c010280c020900804160200800000001018100300804000700000060891a80dd16194e42b108154c43d4142a198694c4314142b09829cc4314142918835d26114142c51735846114142c61725846114142a8983d906050842a288258060552328c5811c96010d32a31811506050832b0581151424c832b0980151424c832d08541c1424c832a2a8294c6050b41a1a839486050b41b098214c439424191a83dd16294241a1a86d4c4354241b108150c4354241918805d26214d41c45625c46214d41c49625c06214d41c18539c261d0d41c14539c660d0d41c18539c261d0941c14539c660d0941e10531876050941e1053d846050941e0853d486050941e0b531486050941a1880590534c941e0443548614c841a9180d906350441a2a82d506050b31c29725806015131c14541c56390931a1787150614c931a1587150614c931e10549c0614c931c91745c0614c931e10545c0614c931c14631c56255031c18631c16255031c18639c26155031d06545c44354831d05545c44354831d05435c44354831b04815904354831b08805904354831d06645c44354831d05645c44354831b058110d52d0831a458198d5290831b058110d5250831c197510c6050831a918110c6050831e08435486050831b058110d5290431c197510e6090431a918110e6090431e084354a6090431a0e86d0d5250431a0c86951524c431a0c86551524c431e0581191524c431b05841c5524c431e04641c5524c431b41801c5524c431e046454a414c431c90645c2414c431d41525c2414c431894865d2324c431b418110d5294031d08745493194031d11545c44354031b418110d5254031918875513154031d08745493154031d11435c44354031a1a83d906055321a28805526290f21a18805526390b21a1a83d506050b21a18805506350721c84641c5324c721c847458
  | 2 => 0x4cad0ab1824006f2718e003e800c000002e8b200000007c0000001b6001396cee5a00000000069af16a4900000500015801206a6e070cc4c37aa8003300000140000000003d40800f2004da3000da60b5ce2952700426002b0f184000020ce8001235400001c800005c188
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2c01439c428c9ab884a21809ba60083410000290028059e300e0002ac360091820001001018aa03222a0e0a12641950465c545c0614c931a80482c8b8886a90638117560443181420c6c032221aa43028418e045d58110e6090431b00c8886a94c1208632059819071549310c7400c8c00e2a926218f00191525c2414c4318c0c8904b80869908140897551325803208320108992e0192a2105026567358a4210020b0049ae8b12a220041a028358a42544400828132a39ac4a0880107001cd625454110020d0032307212a2900412219819232545200828092eaa2c498863884a06488158c4310110c203b10a9924298221a008519132485304428132e322e6292408850865c645c45248110e00322e6b88a49022150192150735051004222130ba2a618a2008540251535c83144010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1844
  | 5 => 9193
  | 4 => 4295
  | 3 => 223
  | 2 => 30
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
  | 7 => packedAt gbK7 (718+((h/13+packedAt gbK7 (640+(h % 13)*6) 6) % 49)*7) 7
  | 6 => packedAt gbK6 (57156+((h/614+packedAt gbK6 (49788+(h % 614)*12) 12) % 2434)*12) 12
  | 5 => packedAt gbK5 (392230+((h/3064+packedAt gbK5 (349334+(h % 3064)*14) 14) % 13348)*15) 15
  | 4 => packedAt gbK4 (230489+((h/1431+packedAt gbK4 (210455+(h % 1431)*14) 14) % 10043)*14) 14
  | 3 => packedAt gbK3 (14046+((h/74+packedAt gbK3 (13380+(h % 74)*9) 9) % 355)*9) 9
  | 2 => packedAt gbK2 (2190+((h/10+packedAt gbK2 (2130+(h % 10)*6) 6) % 40)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0fffc0ffc7e387c7c7f1ff1f81c1f839f793
  | 1 => 0x1ff03fff07fffc7807f8fe3fe3fffe00c679fc
  | 2 => 0x1fffc3fff807fffff800ffc7fc01ffff078e1f
  | 3 => 0xe00003fffff8007fffff0007fffe0007f80fe0
  | 4 => 0xfffffc000000007ffffffff800000007fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x42a188463109440141c1304b048c44b018b391
  | 1 => 0x4424808a1202009002485211212494104250b4
  | 2 => 0x884211104094802a8800848448112943050c0a
  | 3 => 0x814b2a248480c94cd492000692580865a80f40
  | 4 => 0x118c3038e72712772724e92000603186f7e000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0fee8ece0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37117
namespace PEqualNP.Outside.L_meta_37117
open PEqualNP.Outside.L_meta_37117.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 30 := bgb_2_0
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
theorem bgb_3_192 : Interval gbAtlas 3 192 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 223 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192)))
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
theorem bgb_4_4288 : Interval gbAtlas 4 4288 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4295 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480)))) (concat (concat (concat (concat bgb_4_512 bgb_4_544) (concat bgb_4_576 bgb_4_608)) (concat (concat bgb_4_640 bgb_4_672) (concat bgb_4_704 bgb_4_736))) (concat (concat (concat bgb_4_768 bgb_4_800) (concat bgb_4_832 bgb_4_864)) (concat (concat bgb_4_896 bgb_4_928) (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)))))) (concat (concat (concat (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152)) (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280))) (concat (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)) (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 (concat bgb_4_1536 bgb_4_1568))))) (concat (concat (concat (concat bgb_4_1600 bgb_4_1632) (concat bgb_4_1664 bgb_4_1696)) (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824))) (concat (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 (concat bgb_4_2080 bgb_4_2112))))))) (concat (concat (concat (concat (concat (concat bgb_4_2144 bgb_4_2176) (concat bgb_4_2208 bgb_4_2240)) (concat (concat bgb_4_2272 bgb_4_2304) (concat bgb_4_2336 bgb_4_2368))) (concat (concat (concat bgb_4_2400 bgb_4_2432) (concat bgb_4_2464 bgb_4_2496)) (concat (concat bgb_4_2528 bgb_4_2560) (concat bgb_4_2592 (concat bgb_4_2624 bgb_4_2656))))) (concat (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))) (concat (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 bgb_4_3040)) (concat (concat bgb_4_3072 bgb_4_3104) (concat bgb_4_3136 (concat bgb_4_3168 bgb_4_3200)))))) (concat (concat (concat (concat (concat bgb_4_3232 bgb_4_3264) (concat bgb_4_3296 bgb_4_3328)) (concat (concat bgb_4_3360 bgb_4_3392) (concat bgb_4_3424 bgb_4_3456))) (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744))))) (concat (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 bgb_4_4000))) (concat (concat (concat bgb_4_4032 bgb_4_4064) (concat bgb_4_4096 bgb_4_4128)) (concat (concat bgb_4_4160 bgb_4_4192) (concat bgb_4_4224 (concat bgb_4_4256 bgb_4_4288))))))))
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
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6304 : Interval gbAtlas 5 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6368 : Interval gbAtlas 5 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6400 : Interval gbAtlas 5 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6464 : Interval gbAtlas 5 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6496 : Interval gbAtlas 5 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6560 : Interval gbAtlas 5 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6592 : Interval gbAtlas 5 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6656 : Interval gbAtlas 5 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6688 : Interval gbAtlas 5 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6752 : Interval gbAtlas 5 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6784 : Interval gbAtlas 5 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6848 : Interval gbAtlas 5 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6880 : Interval gbAtlas 5 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6944 : Interval gbAtlas 5 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6976 : Interval gbAtlas 5 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7040 : Interval gbAtlas 5 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7072 : Interval gbAtlas 5 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7136 : Interval gbAtlas 5 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7168 : Interval gbAtlas 5 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7232 : Interval gbAtlas 5 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7264 : Interval gbAtlas 5 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7328 : Interval gbAtlas 5 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7360 : Interval gbAtlas 5 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7424 : Interval gbAtlas 5 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7456 : Interval gbAtlas 5 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7520 : Interval gbAtlas 5 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7552 : Interval gbAtlas 5 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7616 : Interval gbAtlas 5 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7648 : Interval gbAtlas 5 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7712 : Interval gbAtlas 5 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7744 : Interval gbAtlas 5 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7808 : Interval gbAtlas 5 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7840 : Interval gbAtlas 5 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7904 : Interval gbAtlas 5 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7936 : Interval gbAtlas 5 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7968 : Interval gbAtlas 5 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8000 : Interval gbAtlas 5 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8032 : Interval gbAtlas 5 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8064 : Interval gbAtlas 5 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8096 : Interval gbAtlas 5 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8128 : Interval gbAtlas 5 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8160 : Interval gbAtlas 5 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8192 : Interval gbAtlas 5 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8224 : Interval gbAtlas 5 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8256 : Interval gbAtlas 5 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8288 : Interval gbAtlas 5 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8320 : Interval gbAtlas 5 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8352 : Interval gbAtlas 5 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8384 : Interval gbAtlas 5 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8416 : Interval gbAtlas 5 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8448 : Interval gbAtlas 5 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8480 : Interval gbAtlas 5 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8512 : Interval gbAtlas 5 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8544 : Interval gbAtlas 5 8544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8576 : Interval gbAtlas 5 8576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8608 : Interval gbAtlas 5 8608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8640 : Interval gbAtlas 5 8640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8672 : Interval gbAtlas 5 8672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8704 : Interval gbAtlas 5 8704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8736 : Interval gbAtlas 5 8736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8768 : Interval gbAtlas 5 8768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8800 : Interval gbAtlas 5 8800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8832 : Interval gbAtlas 5 8832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8864 : Interval gbAtlas 5 8864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8896 : Interval gbAtlas 5 8896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8928 : Interval gbAtlas 5 8928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8960 : Interval gbAtlas 5 8960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8992 : Interval gbAtlas 5 8992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9024 : Interval gbAtlas 5 9024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9056 : Interval gbAtlas 5 9056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9088 : Interval gbAtlas 5 9088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9120 : Interval gbAtlas 5 9120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9152 : Interval gbAtlas 5 9152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9184 : Interval gbAtlas 5 9184 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9193 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))))))) (concat (concat (concat (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)) (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))))) (concat (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)))) (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)))))) (concat (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 (concat bgb_5_3680 bgb_5_3712)))) (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)) (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000))))) (concat (concat (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 bgb_5_4128)) (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288)))) (concat (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 bgb_5_4416)) (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 (concat bgb_5_4544 bgb_5_4576)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_5_4608 bgb_5_4640) (concat bgb_5_4672 bgb_5_4704)) (concat (concat bgb_5_4736 bgb_5_4768) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864)))) (concat (concat (concat bgb_5_4896 bgb_5_4928) (concat bgb_5_4960 bgb_5_4992)) (concat (concat bgb_5_5024 bgb_5_5056) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))))) (concat (concat (concat (concat bgb_5_5184 bgb_5_5216) (concat bgb_5_5248 bgb_5_5280)) (concat (concat bgb_5_5312 bgb_5_5344) (concat bgb_5_5376 (concat bgb_5_5408 bgb_5_5440)))) (concat (concat (concat bgb_5_5472 bgb_5_5504) (concat bgb_5_5536 bgb_5_5568)) (concat (concat bgb_5_5600 bgb_5_5632) (concat bgb_5_5664 (concat bgb_5_5696 bgb_5_5728)))))) (concat (concat (concat (concat (concat bgb_5_5760 bgb_5_5792) (concat bgb_5_5824 bgb_5_5856)) (concat (concat bgb_5_5888 bgb_5_5920) (concat bgb_5_5952 (concat bgb_5_5984 bgb_5_6016)))) (concat (concat (concat bgb_5_6048 bgb_5_6080) (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 (concat bgb_5_6272 bgb_5_6304))))) (concat (concat (concat (concat bgb_5_6336 bgb_5_6368) (concat bgb_5_6400 bgb_5_6432)) (concat (concat bgb_5_6464 bgb_5_6496) (concat bgb_5_6528 (concat bgb_5_6560 bgb_5_6592)))) (concat (concat (concat bgb_5_6624 bgb_5_6656) (concat bgb_5_6688 bgb_5_6720)) (concat (concat bgb_5_6752 bgb_5_6784) (concat bgb_5_6816 (concat bgb_5_6848 bgb_5_6880))))))) (concat (concat (concat (concat (concat (concat bgb_5_6912 bgb_5_6944) (concat bgb_5_6976 bgb_5_7008)) (concat (concat bgb_5_7040 bgb_5_7072) (concat bgb_5_7104 (concat bgb_5_7136 bgb_5_7168)))) (concat (concat (concat bgb_5_7200 bgb_5_7232) (concat bgb_5_7264 bgb_5_7296)) (concat (concat bgb_5_7328 bgb_5_7360) (concat bgb_5_7392 (concat bgb_5_7424 bgb_5_7456))))) (concat (concat (concat (concat bgb_5_7488 bgb_5_7520) (concat bgb_5_7552 bgb_5_7584)) (concat (concat bgb_5_7616 bgb_5_7648) (concat bgb_5_7680 (concat bgb_5_7712 bgb_5_7744)))) (concat (concat (concat bgb_5_7776 bgb_5_7808) (concat bgb_5_7840 bgb_5_7872)) (concat (concat bgb_5_7904 bgb_5_7936) (concat bgb_5_7968 (concat bgb_5_8000 bgb_5_8032)))))) (concat (concat (concat (concat (concat bgb_5_8064 bgb_5_8096) (concat bgb_5_8128 bgb_5_8160)) (concat (concat bgb_5_8192 bgb_5_8224) (concat bgb_5_8256 (concat bgb_5_8288 bgb_5_8320)))) (concat (concat (concat bgb_5_8352 bgb_5_8384) (concat bgb_5_8416 bgb_5_8448)) (concat (concat bgb_5_8480 bgb_5_8512) (concat bgb_5_8544 (concat bgb_5_8576 bgb_5_8608))))) (concat (concat (concat (concat bgb_5_8640 bgb_5_8672) (concat bgb_5_8704 bgb_5_8736)) (concat (concat bgb_5_8768 bgb_5_8800) (concat bgb_5_8832 (concat bgb_5_8864 bgb_5_8896)))) (concat (concat (concat bgb_5_8928 bgb_5_8960) (concat bgb_5_8992 bgb_5_9024)) (concat (concat bgb_5_9056 bgb_5_9088) (concat bgb_5_9120 (concat bgb_5_9152 bgb_5_9184)))))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1844 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := (concat bgb_7_0 bgb_7_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee8ece0feeaeeeafee8ece0feeaeeeafee8ece0feeaeeeafee8ece0feeaeeeafee8ece0feeaeeeafee8ece0feeaeeeafee8ece0feeaeeeafee8ece0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276677856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37117.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.and,[3,4]⟩,⟨.or,[2,5]⟩,⟨.or,[6,7]⟩,⟨.or,[2,3]⟩,⟨.and,[1,10]⟩,⟨.or,[0,2]⟩,⟨.and,[0,8]⟩,⟨.or,[9,13]⟩,⟨.and,[12,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37117

open PEqualNP.Outside.L_meta_37117 in
theorem PEqualNP.Outside.L_meta_37117 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677856) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
