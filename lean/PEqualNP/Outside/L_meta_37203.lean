import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37203.Model
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


end PEqualNP.Outside.L_meta_37203.Model

namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 6, 3, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 16,swapRows 50]

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

end PEqualNP.Outside.L_meta_37203

namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
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
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1a2441000006539b5e0000e28005a52c2088c120150a464cf000e61683081802c1e990a2500400038ac0173e354955c74282480000440c0000381007003242ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1a800ce4f0011c84481f940740007024387a05040967900138760d001b0f6590914c4c6d19060c2221495834392489c5e5f0583c66771b800b841300104a2326044a4623a8c00c40420003e0039814001e01874001b2c1b8007d00000d20000000486a38000002100000004d098b802432f110f86300050002d330d832001f0d0fe5a0b8588a08002142a552e8a8007e1c1280e723b0ace86f1620d02020000104681e9e1005b189945054231907857288801871358083c8040008800640800b0081c00000c0c88080818000000000c180864280424180024f8480c283c2c3c3c467ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2e020b2818040039c6a601602a024032794c0048008c02260a2040003890071428718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x120a81830be43bc43bf42bd42df32dd32
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x825aa421e350932
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
  | 4 => packedAt s2K4 (102+((h/2+packedAt s2K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s2K3 (56+((h/1+packedAt s2K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffc0ffffc1fc1ffc1ff07fc3ffc0fd8f33f3
  | 1 => 0xfc0fff03fffe0fe0ffe0ff83fc3fff02f1ccfc
  | 3 => 0xfffffffc1fffffff0000ffffffc3ffff01ff1f
  | 4 => 0xfffffe0000fffffff0003fffc0003fe0fe0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x48644628849284052d093424c0664258871171
  | 1 => 0x19248a19091094a0552854a1442a9608b144b4
  | 3 => 0x208910405221094a0210894a2a8128a300aa0a
  | 4 => 0xb2ca249243a52a739a520843b3100c335a0fc0
  | 5 => 0xc30c38e39c39cf9ce39cee70222230c3edf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00ee88ee00eeeeee00ee88ee00eeeeee00ee88ee00eeeeee00ee88ee00eeeeee00ee88ee00eeeeee00ee88ee00eeeeee00ee88ee00eeeeee00ee88ee00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x60040028a00be43bc43bf42bd42df32dd32
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2025aa421e350932
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (104+((h/2+packedAt s3K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s3K3 (56+((h/1+packedAt s3K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3ffc0ffffc1fc1ffc1ff07fc3ffc0fd8f33f3
  | 1 => 0xfc0fff03fffe0fe0ffe0ff83fc3fff02f1ccfc
  | 2 => 0xfffffffc1fffffff0000ffffffc3ffff01ff1f
  | 4 => 0xfffffe0000fffffff0003fffc0003fe0fe0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x48644628849284052d093424c0664258871171
  | 1 => 0x19248a19091094a0552854a1442a9608b144b4
  | 2 => 0x208910405221094a0210894a2a8128a300aa0a
  | 4 => 0xb2ca249243a52a739a520843b3100c335a0fc0
  | 5 => 0xc30c38e39c39cf9ce39cee70222230c3edf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
def s4K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s4K2 (i*4) 4
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s4K2 (5+((h/1+packedAt s4K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdfcf3cf1f8fc7673
  | 1 => 0x6ff3cf3e3f1f8b9c
  | 2 => 0xfffffffffffffffffffffff7fc0fffc01ffc1f
  | 3 => 0x7bfff03fffe00fe0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa06841104a452231
  | 1 => 0x10a8105212492294
  | 2 => 0x902a82484924c0a
  | 3 => 0x6020aa924824d40
  | _ => 0
def s4Atlas : Atlas := ⟨2,rawDecor 15 s4Pos s4Neg, 0xeee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0eee0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81be41d037883a05f55240bf29c817d539037c87206f10e40bf294817d529037c85206f10a40bf28c81f651902eca3205f54640faa8c8175519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81be415037882a07ed0140df202817e54102fca6205f54c40df21881bc43102fca4205f54840df21081bc42102fca2205f54440dfa0881bd41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9985f94b30bea9661df32cc3ba65985f94730bea8e617f548c2fca9185f55230be2a4617d538c2fca5185f54a30bf28c617d518c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a2617f524c2f8a49877cc930ee992617f514c2f8a2987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4187b94830b7290617d520c3daa4185b54830bf28861f6510c2eca2185f54430faa886175510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7907b8cb20f6996417e51c82faa3905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20bf28c417d51882fca1107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41ee32483da64905fd4520be28a41fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6105f94820bf28841f651082eca2105f54420faa88417551082fca0107bc8020fd10041ed20083f240105fd5310bf2a621be54c427ca9885f55310deaa6213d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5887dd0710fa20e21f631c43ea63887d88710fa90e217f54842fca9086f952109f2a4217d548437aa9084f55210be2a4217f53842fca7085f54e10be29c217f52842fca5085f54a10be294217d51842fca1087ed0210fc20421fa30843f261087e88210fc90421f710843f621085fd5110bf2a2217d54442f8a8885fd4d10bf29a217d53442f8a6885fd4910bf292217d52442f8a4887dd0510fa20a21f631443ea62887d88510fa90a21fb40443f080887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be290217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xc5050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42df21e85bc43d0afca3a15f54742bf286857d50d0afaa9215f94e42ef29c855e5390afaa7217754e42aea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccbbe87997710f32bf28e657d51ccafca1995f54332bfaa4657e548cb7ca9194f95232beaa465bd548ca7aa9195f15232bea9c657e528cbde85197b10a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f7a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50907f4a120de94241bea8483f950906f2a120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077c8620ef10c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518df54a31bf28c63df318c7ee6318df94231bea84637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a2637f524c6f8a498f7cc931ee99263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c6fca418fb94831b7290637d520c7daa418db54831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb8cb21f6996437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21bf28c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43ee32487da6490fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28
  | 2 => 0x9c3ba6b800209088000000f30104e4319690ee500eba112769dc2d17c0f057c2419b10284cffa620741f04595d0146489e0004969d4b69a82446610f93200e8009b1840007f88a82e0027b0111943a86644ea2340a33c1da3c0824786190f06c400dc0000008cd031c9254808c60d00000000023624a960a18000000000018f0008c80000006000000000256250000192fe8e4002640006d48f8000000006096c0000000000038c0706d102000378fa000000000130490009ad2b81000004d1a1fc1243601c000376000e10fe00023c00240000254001ad4ba868001ba2824cd1806d16e71d2519300081c34000134001238972c0000001e200000117800000684000002e6000a6000000000548004060000000000000000000000000cb16b0002613a1de000498a70a4000000001760000000000025e00c002251640745895c2a282828800000000000000004a0c885f2c201485800194854fd1ef000000e783e0007dc000000000000004702a0000025b0000000d0a73e6000000000006d0ce1543520cc001fb28c26d2e0004449390088e0008408b80044e000ad800000000430000c4558000003465c4000a12269940000048a01062a420002c00005531a000cf00000000000000000588f50fb4f20008522d000000d880047e1cc000001ea000948000947f400067000000fc8a20368b8bd00037a67c000003c6618f39e4000520000610f4000c4a6100035400000156000b70244aa0085b0000001c40008d0568380000000000000000238000000d70005d45f00013c350dc800000000a58000007b84b0003b00000021b02e7ac000e80008dc000c71b20008d16a0680bd090c238610d3601e000754bc1a6000000578002d0000a80dc2627d46d83f2b0034e70001a40002b01200024c5500033a8b0000000000010f0001500100200401018020000d01000004000000000000000050140100000008010000000006004000040000400010010000a01001000020140300805004070000200003008010000b0040100400010000000200000000000040400004000050000e000000180100400000010580a00000004040180100c020040000006010070000000000030010140400c040000101c02000000000000400000090000a00001054070000000006008100340001401004090040800006000000040700c0400801004020240000000044000100300001000040080100404000130000e00001004040100200c0d00001008010080500011078090080000003000000000100004008010080c0000500400002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf29487ee5290edca521df54a43f6a94876d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877
  | 3 => 0x438a51060000007f8534181e4ef9c01e20000024345228cb206b00077069a3a0800d4000000009b82f000270138e69e93163a8a4a6a0000007325009a6fc0a1800008507d000000898001c80fc9e000216012000bb800000200768002420011400000000083a60000000440000008d4841b328a5347b8bf0006ac001f60003250e8660fe0003b05447c3ac8685d112374000002fa000d7a3b3a0000000e908a344000000220c45e0002a4000fc0000b09c4148000001b000000358000f28002b400110276190424e28c437c94c001011ce54c0000000093c39000000000001cc04e0000024c34e000001120e000000000000000210000b800106a734d0950db0f206e508280e30464c0eb04c2f68109618200093414000054920000b416a490f08bb00086000083310084000002fc6dd0598332a0000002d2282289e800000000ac800198240000001de3d8aaa513a62100791b4b4000d10001c0000000000000009b800320000d001800000060039334000000003541640000001c0008898e172690000000409643d8003e00002b8e200012c5996500000000103196000b1800000000000000161d032000000414350f42e45e48c1da18c4100002547a91000000000385078000002080015732e000c3a6f0fa7800010c000000a7a41000000000bd1701480000008c8c4b38e54be37c9f2630000008c95e10a000000003b66140013f000000771743143380016f03e4b48e9bc48c1949a25e0ea4e91206e442604f40d642e000349f23a400133238000000000004ac7980000025c864d280010e000000000002442d83d2cc2b8668004da00091800000000001c4220000000323964d40012702c480001b00003e4000e4000001338000000013800038251c529f14e43f4000000000001e000000000000000005c00008c1402b0e8800288000e500000029800116410180002694927640000c3da8ac0306f1f80b076000132000001b2000871290ba15a8a84f84f1e03e000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2518c23e64951308f994544c31c54cc930c7151324c34c524c9309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d354b300c371518c03097d95300c34d524c0309ed95300c371514c0309798f54c825d63d53208f99353c823d64d4f208f99253c823d6494f20d314d32c823f64547208f19151c827661d52209d587548823f6454e208f191538823e6414e208f59053882766114e209d584538823e64946208f592518823e64951208f994544823e6494d208f592534823f6454d208f19153482776154d209d185534832c548c9209b195324832c544c920d314d324825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d354f200837151880209bd95200834d53480209ed9520083715148020cd18554c423e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c433554d0710ad19131c42b46448710ce181548423e64d4e108f593538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6414a108f590528425e6314a109758c528433954d0210ae19130842b86448210cd95310842ba64c421097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109d99741442f260d05109d19531442b4644c510bc18131442746548510ad19121442f060485109e99740442f261d0110ec10740443b341101109e19530442b8644c110bc18530442786548110ae19120442f06148110ae99310442b664841109d987540427a60d50109798c540425d63150109b988540426d62150108fd91530423c6454c108f990530423d6414c109b988530426d6214c109d984530427a6014c108fd91520423c64548108f990520423d64148109798c520425d63148109d984520427a60148108f992510423d64944108f992500423d64940109e59610042f161840109dd95100427b6544010bcd9510043736544010dc95110043705444010dcd4d10043715344010dcd4910043715244010
  | 1 => 0xca5e65d0d32b398b434ca6e65d0932b398f424cb8c43d0932e3d0c424caae64cc932a7992324ca3e64145328f590514ca7a60145329e580514ca3e64141328f590504ca7661141329d584504ca5e63d50329b98b540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3e64948328f592520cacd638c83297d95320ca6f654c832b3d95320cb4f654c832d3951320cb4c544c8328fd91510ca3c6454432d34c9510ca3f64540328f191500cb4d32540329b98a53d066d6294f419798e52d065d6394b41ab98a439069e6390a41ce90e50907384394241ce90a50907384294241ced06509077341542418f997435063e65d0941ae982415063d6590c41ab98a431063d6590841a798e42106f160904418fd95411067765504419b98b54cc66d62d53318f99252cc63d6494b318fd9150cc63c64543319e983548c67960d52318fd91528c63c6454a318f992508c63d64942318f992544c63e6515131c7153324c71c544c931d3149324c66e62d50319b58b540c67a60d50319e583540c63d65950318f990540c66e62150319b588540c67a60150319e580540c72e5494831cb552520c72e5454831cb551520c74d52cc43197d95310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c7723154031dc4c5500c65e63d53219758f54c863e64d4f218f59353c863e6494f218f59253c874c534cb218fd9150c863c64543219e983548867960d52218fd91538863c6454e218f990538863d6414e219e98053886796014e218f992508863d64942218f992544863e65151218f992534863d6494d218fd91534863c6454d219ed8153486786054d21cb152324866c654c921cb151324874c534c9219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219b988530867a6014c219e580530874d53c84219bd95210874d53484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087722154021dc485500866e6294f409b58a53d025e6394b409758e52d02ba6090740ab98a439029e6390a40cd90e51903344394640cd90a51903344294640cd94741903365150640cd947409037151d02408f997435023e65d0940ae982415023e6510540ad986405023d6590c40ab98a431023d6590840a798e421023f6550440bc586401023f65500409ed95401026e62d53309b58b54cc23e6494b308f59252cc23f64547308f19151cc27661d52309d587548c23f6454a308f191528c23e64946308f59
  | 2 => 0xb12b8a20003719845234d538c642f82e1122602e6b23e5fb645a9a0c70a09d0ea09854ba022be9f42baf2458c26516836b3c431704a90e183483d2047593e198000da14e6396898d6a9000861b4001ec00000001340006e0038e000000011e000001e800800164e000002384980000230969b08818a0704c6d91095b36000008d8000000000000ab0000019a5f00054b940931aae97834a246e086122a8ce096b62822d8e0bb820bf30a1e000001f04c800e28000029200076003088322200244670f6871a4c4160270000000ae1a7e0d380bfa3272800001be4c064b489abc3580029a003701000099814620000000000082002e20000000120002529633a5bb5cd2800388d4c08e840800cb800001f86185a00000c8270d8884cb1c8002e4002b051b0c2eb52178c05694a0025e000000c0b4dd0cc4b172a10000413aaf80000280002465d8460e9d8000009a000401c40028a148329ab7c0018e9caf63c0006a196e7b28d109e610a2062b4362f4739e2d9acaaa962e0ae05e9488093ca80be7e8009f24e8230e790f27c91a002a23f9e66f3a420062649a660000c8ba050940b208a9b8500039293000242b6a30b053ada2903c01b9cdaa2e818a6de8001ca40a9acc001a263166000e6001cc001442f00033800000000022c00000768005583eca87c542dc7a038d308831216c79c690ab2000fcc023cd800882b508784aaf210c6250030007fb348a8002b00e593043780024800001e0000000000046000001fcc9ba20024800000138707aaec010000034223a0eb98001f8687525cd786c74874de314000006cb90002123e0003e8c6561d0049dc6b800c48007b894b0000e21c09b1283b2d657000d1a7898ad0e13680000000000608000029e0780000000001748680000000df800391aa1ab6c2a12400000014040040100c11060040600d00c0000802028000080000c0708c01000230000102c0a010000c40900001090040f400008070040203c100000e014370000100404004030640d0280a00c0301002008360080309400038000100d00c0404801000060400503804044030000100c0401006000030240801400008040001b00806000030e000014010140d0080000402000010040001c0800412000110040b0180900c020040001c0003c070240200809000000000500020000010240000c0400e7a60947439e58251d0e7661943439d58650d0f2f4394a43d3d0d5290eae6290d43b358a4310e3f6550c4397d954310eae6290f429e98251d0a7960947429d98650d0a756194342c794f4390b1e5350e42c794f4290b4d53d0a42ab98a4350a3e6510d42a798e4250a3f6550c42b358e4210a3f65508429bd954210b1c6355332c755343ccb2c6255232cb553428cb1e54cca32ab993328ca7761551329d185544ca7b60551329e181544
  | 3 => 0x2940037610b1699332a4122002c20039a420005b12e55056c91c20001adc800a61de42802b1b4e6ea8ea72867d844d68280002adb8001713657ade23058000008a19e0011cb500092b3e9eaea53000a5acec18aa980b2418009d8cacc3400002c3b8c8d58008e8000025400104342ae
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1a2010e1024005b00342806284600a873a6ca99065515c4544c832a92e02a2641960c644c9510cb0632264a80654a9ca4394241a34e7214a120d267290e519028b39c8528c814c9d36544010aa2e62a220085617215110042983a2a6880214c1d15244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 634
  | 4 => 467
  | 3 => 14
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (19228+((h/211+packedAt s5K5 (17118+(h % 211)*10) 10) % 1012)*11) 11
  | 4 => packedAt s5K4 (19296+((h/155+packedAt s5K4 (17746+(h % 155)*10) 10) % 617)*10) 10
  | 3 => packedAt s5K3 (706+((h/4+packedAt s5K3 (686+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xff83ffc1ff8ff1c3c78fe3fc7e0ff07c19f673
  | 1 => 0x7fc1ffe0ff1fe3c07f1fc7f8ff07f80667b9c
  | 2 => 0x7ffe3fff001fffff801ff8ff0007fff878c1f
  | 3 => 0xf80003fffffe003ffffe000fffff8003f80fe0
  | 4 => 0xfffffc000000003ffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x10a8404462104200818260941225112808b231
  | 1 => 0x5109408c240280480290a42484a12508225294
  | 2 => 0xa2108910812520154801090920424a51850c0a
  | 3 => 0x20529221090024a65424000a494a0212d00d40
  | 4 => 0xc4631839ce49c93ba749d240018c0c637fe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0fee8eee0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2bd00b859c00002227ec90808c3c34876f922f20cd2b07299bc0500848e1ad440084f220a28c49000000999186c01e0129c116cb5007005d5232cada1d5860f95000000074693891a114020400201122830000880b11a70000017fd5005fe54005f95005fd54017f150057c54017fd48057f52017f94805fd52005f54805fc52007fd0801fe42007f50801fc42007f8c801fd32007f0c805ff5000ff94005fd5000ff14001ff4000ff90001fd4000ff10001ff3000ff8c001fd3000ff0c001ff2000ff88001fd2000ff08003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xe4004ff58720005fac390013fc61c800f7e30e400affd472004ffca39002bfd51c8013fe28e4000ffd072004ffc8390003fd41c8013fe20e4000ffcc72004ffc6390027fc31c8009ff90e4004ff88720027fa4390013fc21c80037eb064001ffd432000ffca190007fd50c8003fe2864001ffd032000ffc8190007fd40c8003fe2064001ffcc32000ffc6190007fd30c8003fe1864001ff8832000fdc4190007fa20c8003fe1064001fb0832000ffe2190007fe10c8003fe0864006ffd9520035feca9001bfe65480057f32a4006ff59520035faca9001bfc65480057e32a4000ffd9120005fec890003fe64480017f3224000ff59120005fac890003fc64480017e3224006ffd5120037fca8900037e544800dfeaa24006ff15120036f8a890003ff63480017fb1a4000ff98d20045fcc690003fd63480017eb1a4000ff18d20045f8c69001bff534800dbfa9a4006ff94d20037faa6900037d534800dfe29a4000ffd0d20007fc8690003fd4348001fe21a4001bfd8920037fea49001b7f5248009ff2924006ff54920006faa490013fc5248001ffa124004ff90920007fa8490013fc4248001ff9924004ff8c920007dc6490003fd3248001f69924004ff0c920007fec290002ff614800bff30a4007bf98520007fac290017fc614800f7e30a4006ffd452002ffca29001bfd514800bfe28a4000ffd052002ffc8290003fd414800bfe20a4000ffcc52002ffc6290003fd314800bfe18a4004ffc852002ffc4290003fd2148009fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe4090013fb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe0824003ffd951001dfeca880037f65440013fb2a2003ff99510015fcca8800ffd65440077eb2a2003ff19510015f8ca8800f7c65440053e32a2000ffd9110005fec888003fe64440017f3222000ff59110005fac888003fc64440017e3222003ffd511001ffca8880037e5444007feaa22003ff1511001ef8a888003ff62440017fb122000ff98910025fcc488003fd62440017eb122000ff18910025f8c48800fff5244007bfa922003ff9491001ffaa4880037d5244007fe2922000ffd0910007fc8488003fd4244001fe2122000ff8c910007fa6488003fc32440037fb022001ffd411000ffca088007fa5044003fea822003fe5411000ff8a088007ff4044001fda022001ff9011000ffa8088007fc4044003fc2022001ffcc11000ffc6088007fa3044003fe9822000fe4c11000ff86088007ff2044003ff1022001fe8811000ffa4088003f92044003fe1022001ff8411000fec2088007fc1044003fc0822001fc04110
  | 1 => 0x3fe62cc0097f3166008ff58b30005fac598023fc62cc01dffa96600edfd4b30077fca59803bfd52cc001bea96600eff14b30007fe8598003fe42cc001fea166000ff10b30047fe6598023df32cc011ff1966008ff4cb30007ba6598023fc32cc011ffb0e6008ff9873003dfcc398023fd61cc0017eb0e6008ff1873003df8c39803bff51cc01bff28e600eff5473006ff8a398003ff41cc01bff20e6000ff5073006ff88398023fe31cc011fe18e6000ffc873006ffc4398037fc21cc0037eb066001ffd433000ffca198007fd50cc003fe2866001ffd033000ffc8198007fd40cc003fe2066001ff8c33000fbc6198007fa30cc003fe1866001f70c33000ffc4198007fc20cc003ff8866001ff8433000ff82198033ff654c0197fb2a600cff99530015fcca98033fd654c0197eb2a600cff19530015f8ca98003ff644c0017fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c898033ff544c019ff2a26000df95130067faa898033fc544c019be2a26001bfd8d30067fea6980337f534c011ff29a600cff54d30006faa698023fc534c001ffa1a6008ff90d30007fa8698023fc434c001ffb126000bfd8930007fcc498003fd624c001fe3126004bf18930067fea4980337f524c019ff292600cff54930006faa498033fc524c001ffa126000ff90930007fa8498003fc424c011ff9926000f7cc930007fc6498003fd324c001ee9926008ff0c930007fec298002ff614c017ff30a6007bf98530007fac29802ffc614c00f7e30a600cffd453005ffca298033fd514c017fe28a6000ffd053005ffc8298003fd414c017fe20a600bff8c530047f86298003ff214c017ff10a6000ff4853005ff84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826008fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ffc413000ffc2098007fa104c003fe0826004ffd9720025fecb90013fe65c80057f32e4004df99720014fccb90013fd65c80157eb2e4004df59720004facb90013fc65c80097e32e4004ffd9320025fec990013fe64c80017f3264004ff59320005fac990013fc64c80097e326400affd5320057fca9900037e54c8015feaa6400aff15320056f8a990013ff63c80097fb1e4004ff98f20045fcc790013fd63c80017eb1e4004ff18f20025f8c79002bff53c8015bfa9e400aff94f20057faa7900037d53c8015fe29e4000ffd0f20007fc8790003fd43c8001fe21e4001bf98b20027fea5900137f52c8009ff2964004ff54b20026faa590013fc52c8009ffa164004ff90b20027fa8590013fc42c8009ff9964004ff8cb20027dc6590013fd32c8001f69964004ff0cb20027fec390013fe61c800f7f3
  | 2 => 0x40095facba004bfc65d00057e32e8001bf99340097fea9a004bfe54d0001bf2a68012ff55340097f8a9a004b7c54d0001ffb1e8000ff98f40045fcc7a0003fd63d00017eb1e8000ff18f40097fea7a004b7f53d0025ff29e8012ff54f40006faa7a004bfc53d0001ffa1e8000efd0f40007fc87a0003fd43d0001dea1e8000ff10f40007fec5a0003fe62d00097f3168000ff58b40005fac5a0003fc62d0025ffa968012dfd4b40097fca5a004bfd52d0001bea968012ff14b40007fe85a0003bf42d0001ff2168000ff50b400077a85a0003fc42d0001ff9968000ff8cb40007fa65a0003fc32d0001ffb0e8011ff9874003dfcc3a0003fd61d00017eb0e8011ff1874003df8c3a004bff51d0023ff28e8012ff5474008ff8a3a0003ff41d0023ff20e8011ff1074008ffc63a0047fc31d0023ff10e8011ff0874000dfac1a0007ff50d0003ff2868001ff5434000ff8a1a0007fe40d0003df2068001fe9034000ff881a0007bc40d0003ff1868001ff0c34000ffc41a0007fc20d0003ff8868001ff8434000ff421a0007fc10d0021ffb2a8010bfd9540006fecaa00027f6550021ff32a8002bf99540087facaa0042fd6550021fe32a8002bf19540086f8caa000a7c65500037fb228010ffd5140087fca8a00037e5450021feaa28010ff15140086f8a8a0003ff63500017fb1a8000ff98d40007fac6a0003fc63500117e31a8010ffd4d40086fea6a0043fe5350021fea9a8000df54d40087f8a6a0003ff4350001dfa1a8000ff90d40007fa86a0003bd4350001fe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940025f8c4a0043ff5250021bfa928010ff94940087faa4a00037d5250021fe2928000ffd09400077e84a0003fe4250001fea128000ef50940007f884a0003ff3250001ff1928000ff4c940007f864a0003ff61500017fb0a800fff9854003dfcc2a0003fd615001ffe30a8007bf18540087fea2a003ffe5150021fea8a800fff14540007fe82a003ffe4150001fea0a800fff1054007ffc62a003ffc315001fff10a800fff0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff4050001fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fc3050003ff1028001ff0814000ffe20a0007fe1050003fe0828008ffd9730045fecb98023fe65cc0057f32e6008df99730014fccb98023fd65cc01d7eb2e6008df59730004facb98023fc65cc0117e32e6008ffd9330045fec998023fe64cc0017f3266008ff59330005fac998023fc64cc0117e326600effd5330077fca9980037e54cc01dfeaa6600eff15330076f8a998006fe63cc011ffa9e6008dfd4f30047fca798023fd53cc011bea9e6008ff14f30047fe8798023fe43cc011fea1e6008ff10f30047fec59802
  | 3 => 0xe100841bffc40420d7fc202106bfc1010809ffb2c6404bfd9632027fccb1900afe658c809bf32c64029f99632027facb19066fd658c809beb2c64009f59632027f8cb19012fc658c809ffb246404bfd9232027fcc919002fe648c809df3246400af99232027fac919002fd648c809deb246400af59232027f8c919012fc648c833ffaa46419ff95232006fca919067fd548c833fe2a46419df152320b5fac719067ff538c833bfa9c6408ff94e320cffaa7190037d538c811fe29c6400ffd0e32047fc8719003fd438c811fe21c6404bf98a32027fea5190137f528c809ff2946404ff54a32026faa519013fc528c809ffa146400fbd0a32027fc8519013fd428c809fe2146404fb10a32027fe6519023ef328c809ffb0c6404ff9863203dfcc319013fd618c8017eb0c6404ff1863203df8c319067ff518c831ff28c6419ff546320c7f8a319063fe418c831fe20c6418ff8c632047f86319013fe218c809fe10c6404ffd8232027fcc119006fe608c809feb046400bf58232027f8c119006fc608c833ffa846417ff942320cffaa11905ffc508c82fff2046417ff102320bffc6119023fc308c809ff1046404ff082320c7fe211905ffe108c82ffe0846416ffd95320b5feca9905bfe654c8057f32a6416df99532014fcca9905bfd654c82d7eb2a6400df59532004faca9905bfc654c8057e32a6400ffd9132005fec899003fe644c8017f3226400ff59132005fac899003fc644c8017e3226416ffd51320b7fca8990037e544c82dfeaa26416ff151320b6f8a89905bff524c82dbfa926404ff949320b7faa4990037d524c809fe2926400ffd0932007de8499013fe424c801fea126404ff10932007d88499013fe324c809ef1926400ffd8132005fec099057fe604c8037f3026400ff581320aff8c099006fc604c82dffa826415ff941320b7faa099057fc504c82bff2026415ff101320affc6099023fc304c82bff1026404ff081320affc2099057fc104c809ffb286404bfd9432027fcca1900afe650c809bf32864029f99432027faca19052fd650c809beb2864009f59432027f8ca19012fc650c809ffb206404bfd9032027fcc819002fe640c809feb206400bf59032027f8c819012fc640c829ffaa06414ff95032006fca819053fd540c829fe2a06414df15032025fcc419013ff520c809bfa906404ff94832027faa4190137d520c809fe2906404ffd0832027fc8419013fd420c809fe2106404ff8c832027dc6419013fd320c811f69906400f34c832027fec019013fe600c8037f3006404ff58032005fac019013fc600c8037e3006414ffd403209ffca019053fd500c827fe2806413ff9003209ff88019023fe300c811fe1806404ff88032027f8401904ffe100c827fe0806412ffd9740095fecba004bfe65d00057f32e8012ff597
  | 4 => 0x8fff5390847bfa9c8423ff94e4211ffaa7210037d5390847fe29c8400ffd0e420077e8721003fe43908097f3148404ffd4a42026fea521013fe5290809fea948404df54a42027f8a521013ff4290809dfa148400fbd0a42027fec321013fe619080f7f30c8404ff58642005fac321013fc619080f7e30c8423ffd4642117fca32108ffd5190845fe28c8422ff90642117f8832108bfe3190845fe18c8404ff88642027f84321013ff6090809ff3048401bf98242027fac121002fd6090809fe3048401bf1824211ffea121087fe5090847fea848421ff1424210ffc8121087fc4090843ff1848421ff0c242027fc4121013fc2090845ff8848421ff8424210ff82121083ff65508417fb2a8400dfd9542004fecaa1083fe65508057f32a8420ff59542105facaa1083fc65508057e32a8420df19542014f8caa1083ff5450841ff2a28400df95142107faa8a1083fc5450841be2a28400ffd8d42005fec6a1003fe6350801feb1a8400ff18d42045f8c6a1083ff5350841bfa9a8420ff94d42107faa6a10037d5350841fe29a8400ffd0d42007fc86a1003be4350801fea1a8420ffd4942106fea4a1013fe5250841fea928400df54942027f8a4a1003ff4250801f7a128404ff909420277c84a1003ff61508017fb0a841fff9854203dfcc2a1003fd615083ffe30a8407bf18542107fea2a107ffe5150841fea8a841fff145420fffc82a107ffc415083fff18a841fff0c5420fffc42a1013fc2150801ffb028400bfd81420f7fcc0a1006fe6050801feb02841eff1814200df8c0a1083ff505083dff2828420ff541420f7f8a0a107bfe405083dfe202841eff8c1420f7f860a107bfe2050809fe102841fffc41420f7fc20a107bfc1050809ffb288404bfd9442027fcca2100afe6510809bf32884029f99442027faca21072fd6510809beb2884009f59442027f8ca21012fc651083b7f320841cffd50420e7fca8210037e5410839feaa0841cff150420e6f8a821013ff6310809ff3188408bf98c42027fac621002fd6310809fe318841cffd4c420e6fea621073fe5310839fea988400df54c420e7f8a621003ff4310801dfa188400ff90c42007fa8621003bd4310801fe2188404bf98842027fea4210137f5210809ff2908404ff54842026faa421013fc5210809ffa108404efd0842027fc8421013ee4210809fea108404ef50842007da8421013ff6110809ff3088407bf98442027fac221002fd6110809fe3088407bf184420e7fea22106ffe5110839fea88841bff144420dffc822106ffc4110837ff188841bff0c442027fc4221013fc2110809ffb008404ff9804200dfcc021013fd60108017eb008404ff1804200df8c021073ff5010835ff280841cff540420d7f8a02106bfe4010835fe200841aff8c0420d7f86021013fe2010809f
  | 5 => 0x10070120000b80e00a02801800002008018030000280300002401000805002000010110020000080900c0100485b0020000200f00205c0200700e0000d80501000c000170040301180101400c1880f03802002001036018130031520103000b01201c0002401e02c018100000cc008180060000000401600801812000004010080180080100000208c0000202600800805000000018000001ac0080b0620002380000400c0f03802403c0183a00007001001000040060090340200501b00200c000090000c007803006040008030160380002e0020380200500800003822066000018180121b00100400401443004000004008030000600000101e0080580f000000360110360003600b00a01000002006004038110000000080300000005bf324a8029f992540167cc92a0037f6295001bf314a800df58a54004fac52a0037c6295001bfb04a828df98254006fac12a0a37c6095051bf204a828df10254146fc612a0a37c3095051bf104a828df08254146fc212a0a37c1095001bfb22a400df99152006fac8a90037c64548013e322a400dfd8d52004fec6a90037e6354801beb1aa400df18d52016fec4a900a7f6254805b7b12a400dfd855213efcc2a90037d615484fbe30aa427df9055213ef882a909f7e315484fbe18aa427df88552026f842a90037f605484dbf302a400df58152136f8c0a909b7e405484dbe202a426df8c152136f860a909b7e2054809be102a427dfc4152136fc20a909b7c105483bffb2e841dbfd9742006fecba10027f65d083bff32e8402bf997420effacba1076fd65d083bfe32e8402bf197420eef8cba100a7c65d083bffaa6841dff95342006fca9a1077fd54d083bfe2a6841ddf15342007fec7a1003fe63d08117f31e8400ff58f42005fac7a1003fc63d083bffa9e841ddfd4f420effca7a1077fd53d0801bea9e841dff14f42007fe87a1077ff52d083bbfa968404ff94b420effaa5a10037d52d0809fe2968400ffd874212ffcc3a101efe61d0801feb0e8400bf5874212ff8c3a101efc61d083bffa8e8425ff947420effaa3a1097fc51d084bff20e8425ff1074212ffc63a1097fc31d084bff10e8404ff08742007fec1a1093fe60d08037f3068400ff58342005fac1a1093fc60d08037e306841dffd4342127fca1a1077fd50d0849fe2868424ff90342127f881a1093fe30d0849fe1868424ff88342027f841a1097ff10d0849ff0868424ff04342027fecb21012ff6590809ff32c8402bf99642026fccb2100a7e6590809feb2c8423bf59642026facb210027d6590809fe32c8404bf19642105fac92108fff5490847ff2a48400df9524211ffaa92108ffc5490847be2a48404ffd8e42027fcc721022fe6390809ef31c8400b798e42027fac721002fd6390809eeb1c8400b758e42027f8c721
  | 6 => 0x55311d78e6089ae6c43462b881a1c315801b73679877e19c0ac9bc18c5f03cc46e5497ec2dc9ce39e5621cb1c035e0180f01251b680a12640a1ca1e66563f77725eb5637fa5db7f24a04430006b563e1a91335685527243406be49a3551b000018e2401bc0378972da9280cd8f256b1c66404cc67659e9784323386960000312aa9c54fb0463790000824064f406a0000006647164a264a0900002c44d27fd44298a79e4fe7d880e2be1cc5bc51a52e0230b401955629847c83c5de4c472e0004bc5ce1e014a0020001b800060a0003d400000041a41032e51200055002900000064600067a00000026d0007b200074a0000000000575a644c1f783e47202173837625057b11828400000000070a4d400097e03500000025624a0009160006c60000146fe0000000000000000d80dc08c00000036e0009c69c18644249d15c000058000033a4cd57a0003ea7a21724860d25e20c204035c5f10008489105cd0f83082640433920000000002c36fc40280075e3d808645a6b802c10200044811e6102e77221786304583c200000039c0005300000c40e800000042200058600000025400048c29448015c9825ec0fe9d920d43429e3a22f67e843c46500000070822263251476e13a12e5b24f99187440003f83285d272a0002ca33201c0388842f25712e277a10457d7a40f21808c148e5ed5c233e0007880007be0535bf34e7fc9540005ea6af00055b00018a2a42367e60000002ec2a619e58209c00037842635226a0000003e85906129dc9a02fc65806557c00085a53c0660007c802d63c3180525c586c5d85b498479485822400e2586c00602c607a6ba45437f4ae9900004c600000000075444a76005b49e006000038020000540100000e0a40100205e0000003809e12c0000b02404c0401b0020140180000000002802006000000010180b80100a0300000c80d01407c000150320100000400200012803000074020010040a00182900e0b40200400002008806004018008000220500380000600c0000a0240180d80000c0080a000002010008060060000200100000001807006010008080120000180000004c03805006004008000040080102d00401c0900701002408000000000068010000140005600602c000020020000000103002c0080001e00c108110060003201c0440000380300201c0101800400002002008018000100060081e00700a0000a80a00000804800002000040050f20000200b0220341402201e00000804006000070160480180000708603c138010060040301002e004000080140200002200200c0080a00c000068010040840b00a000060060070040300400200000c0980401e038050000060f80381306c0d40081000c06404002006024018000080880480000601001800010024048040000900000000001803803
  | 7 => 0x366f004f1c10004ee76a96d00000053f2f42160d93a85c794c61473493a2a298c92c47646c56020e7ca54c16e2820009003bc3368407c41da2fe0fb02a96038c9a83fc56f6b446210362e52621c66e56900041c3641446b03c01741ea5c11e42bf2955236f809843b8f055190a68a54e32401e1fe12066c0e11378d612c14e92a5247ba3317805661e348a69a98627c6949228d407e8962724e60008e04fc84458c6756d82865559649d37100000001405a856a6939148d05c95042681167cc9962c77b08d299c3843aa53409e5e400017a5287e01520007506a65388ae8c66348ac00000005f3f432218402788871e5544f06fa3b68a00150005fa8169576180006b647022e5d98d870482c2006d092e67800c9081f678400b00027e67203204735141260e3742d60f405614849003c41e43a2a05586703102fa5579e22ea37b7c60411225c35003dc24853e1468fe0a21b247a9be3b000000093c0d41829880390360a08461f01ce6da1c40008da00000011263817089c86000034246a74f9ac1660007f500072600011c0002300008866dc55f5dc38300085c4f65d55405ac67c3a66665e143092026c1763e41f885e19b21e04260499827694a4961d64d85d02e06a044e3304ce83600017c86a3ba0000005d68ec31c0009d014500040088a34c6d22926ea00009223250a32a42a9bf0007590ee0001b400096e2968801866860000b000045e1ec5f36d43f661c33c2bc1983560ba6ec37c16254a0844e28195412b41d425a5ca7ac3be0002e33b400000063a00031e15069c5700006de9d265400022000080200034882e70015644589e1e900a7d200000000023400000016a6844aa0001aa90449c5f250645290c5f68f49aa28e7b43a00076689c45924cf35881291a9d72620594fd4e02ee7ee0000120b869962a0fc65e2cc6f61541064508990a45944447121d800087c4fa2d24648f661e0004b61940004843727de00064c0001286c982087a55d9720006d60000962ac0000006800002d00007688420000000f654d6880a82784605076520200008fc00094842c0003c40001ee00073a0882b20b210e2913ae5e900002e96c4e45fc8040009c80137f84a854778a0002020000008183040005f516800069e0009de9440008320000000000000000005080000bc8b20ce0001241e740454f0000dd79600000057f4682888144419a610c5f83068fa63634d71a84a5f42997f05fe37064e90e17e8625b69029dd0486904f293b4662c20114922ce2d86445e349456e8708b08063c609a4150e22bd7146bc74d89442823e6226978248e60255a220443e5849ca94e9cc4d659a9b25b78264462d484c02215a1ba6504c281c9769c731a8922ae99a3a46006480331644ac24c3b20fd2e694611062832c7da8e81a09700ca70207c1a479243805d71c
  | 8 => 0x65ee6827462389ba7bc5bd7d43da30c77097499e32027a6e641857853d4740003d204975555c0aa0000345ef0f900083086e6e00003887660000007900004de1ac3ce7fe02b06c05578c0000000007ae00000000000000000000074800056d7b600098e2a877c15e0006c208e38e6602668be9c02931a20003341963682c87788a65670680000540007565982280b680c39a00882a5d70c08f84b00000000009406204b80001fc0004c865a29b3f227961611b0d64ca5be6e87a07769c20000008b60002f007443f1a574237d8b45a02de3d61ae0001e55423e08a800019786806422a0005035cb1d00003ec74e91c0786e20701300c898095000049840e83487293237e92441408a6628aa87472c3e200020a10a9d644038a39413c57900067e5aa3903fe00f24e7aa57e06e75152a0500090064ba5646ac0ea4da8829c359c7c06021c58784111a613276c7a82b687604b3e65b95465d358e6cc47821201004536a6ee19a56c3005c69cd00000022c52055e1ed34f80865c0000e430e5108b82744160006246c85e561a0005dd0009426957ce3577f61c228c9364b240c9568281e27dc26e42e84e4497825c80da8a20cc1c80007520003359b69929e05597d025e3985a472000d1388ca96a5da0165df89d8de18851629095276257405c0000002d96f29340262144088dc28a8e206329a2c069d5728ba0d16925e03965457323025482600007534d04ff88e0e63660002802b07069a452c00010872875c3c84f85752e80809c905e1924dc37a47e3800009b80005d170e87e0000006ca35419095a4ec5ae1426ce2ba3a716000095e81e81000073e1f200000000000029c0003ca02400053a00000003e00000004464200054b0008c88500000005b07581218980619588e400079a0006a27862060519d41dc00057693030a0d04a45b86f460c4be1a823c9384b48a46a80de8c000085273c50c0581be7f93140ae9cf8545433de0005180000000000fa00000000001a04c45c8560004d368c83879c5ba8908bc9b401f74c9680003ee0000001000006e471851c50100004d11a42013424203b00097a4e85770000280ec0004820000008ea0000007640000be3500001f43950000000009b000000004a0001e83ac9cb31200082296297c43d07220c24400059635a45674096670c6060000625e75c47a677534a3b88c469838602f5cf0005bb00095c0047c20760000000000000007f412a1de0c66a46ae0000003d020809400036c11f54455a75a16c5220009068c24c083a88c00003a25250221a36201d00050e00062600089a51e0008ee3fa21804e6aa66a13e5d45e899425c01768e0000002707f762c7e41142109d54ea5cc3160009a20030009d80e02468cc3f05362757d69db3443823268ce93e39b6745324882f87304a62e440f05a6b23604
  | 9 => 0x7749125730008661d22c17e291e0000000300009267b80a60000005e614c00058822623a58a1fa9da7ea13
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6510910006bf6410910006bc6410910006ef6210910026ec621091003df67110910005f5711091000dfa7010910005f970109100d7f01010910024ff768c910004fe768c910004fd768c910024fc768c91001d7e758c9100057d758c9100067f658c9100ce7c658c910005be748c910005bd748c910006df638c910046dc638c910026ee628c910006ed628c91003df6718c910005f5718c91000dfa708c910005f9708c9100bff0108c910004ff764c910004fe764c910004fd764c910004fc764c91001d7e754c9100057d754c9100067f654c9100b67c654c910026ee624c910006ed624c91000dfa704c9100aff0104c910024ff760c910004fe760c910004fd760c910024fc760c91001d7e750c9100057d750c9100067f650c9100a67c650c910006ef620c910026ec620c910007cd320c91000dfa700c910005f9700c91009ff0100c91003dfa76d011008efa76d011003cfa76d0110175fb75d0110175f975d01100077b65d011016f7865d011000dfa74d011000fba74d0110006fb64d0110007bb64d0110006f964d0110007b864d01100077a54d011016f7854d0110005f973d011016f7b53d01100077953d0110007bb43d0110007b943d0110005f972d011016f7b52d01100077952d0110007bb42d0110007b942d011003dfa71d011008ff271d011003df271d0110007f171d011003df871d011000efb61d011000ff361d011008ff251d011016ff151d0110007f341d011008ff041d011008ff231d011008ff221d011003df8764c110046f8764c11003cf8764c110165fb754c110165f9754c1100077b654c11015f78654c110005fa744c110005f8744c1100077a544c11015f78544c11000dfb734c11000fdb734c110007db634c110046fa634c110046f8634c110007d8634c11015f7b534c11000779534c110005fb724c11015f7b524c11000779524c110007db324c110007d9324c110007f3714c11003dfa714c11003df8714c11005ff0714c11003df0714c11000efb614c11000ff3614c11005ff2514c11015ff1514c110007f3414c11005ff0414c11005ff2314c11005ff2214c110007f1214c11003df87648110026f8764811003cf87648110155fb7548110155f975481100077b654811014f786548110005fa7448110005f874481100077a544811014f785448110005fb7348110005f9734811014f7b534811000779534811000dfb724811000feb7248110007eb6248110026fa6248110026f86248110007e8624811014f7b5248110007795248110007ea3248110007e93248110007f3714811003dfa714811003df8714811002ff0714811003df0714811000efb614811000ff3614811002ff2514811014ff15148110007f3414811002ff0414811002ff23148110007f1314811002ff22148110007f12148110
  | 1 => 0x89100067f52d891000cff71d891003cfe71d891000cfd71d891003cfc71d89101aeef21d89101aeed21d891003cff70d891000cfe70d891003cfd70d891000cfc70d8910196ef20d8910196ed20d891019cfd769891001d7e75989100057d75989100067f65989100067c6598910006ef629891019df5719891002df970989101a7f01098910024ff76589100057f755891001d7c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc73589101a5f7715891004dfb705891019ff01058910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf7458910004fc7458910006bc7458910004bc74589100067e54589100067c5458910004ff7358910006df7358910004df7358910044fc7358910006dc7358910044dc73589100067f5358910006ef72589100067f52589101a4ff7158910006f7715891019cff7058910006fb7058910194fe761891001d7e75189100057d75189100067f65189100067c6518910005be7418910005bd7418910005de7318910005dd7318910026ee6218910006ed621891018ff010189100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100057c74549100067f64549100067e64549100067d64549100067c64549100057f73549100067f63549101867e63549100067d63549101867c635491017d7f725491001f6f72549100067f62549100267e62549100067d62549100267c625491013f7671549100077571549101367f615491013f74415491013f76315491013f7621549101377a70549100077970549101367f60549101377840549101377a30549101377a205491013f7b1054910137761054910137741054910137781054910137701054910004ff76d0910004fe76d0910004fd76d0910004fc76d09100057f75d091001d7c75d09100067f65d09100ee7c65d0910006be64d0910006bd64d0910006ef62d0910026ec62d091003df471d091000df870d0910127f010d0910024ff7690910004fe7690910004fd7690910024fc769091001d7e75909100057d75909100067f659091011e7c6590910006bf6490910006bc6490910005de7390910005dd739091003df67190910005f5719091000dfa7090910005f9709091010ff01090910004ff7650910004fe7650910004fd7650910004fc76509100057f755091001d7c75509100067f65509101067c6550910006be6450910006bd6450910005f7715091003df47150910005fb705091000df870509100f7f01050910024ff7610910004fe7610910004fd7610910024fc761091001d7e75109100057d75109100067f65109100e67
  | 2 => 0x47e74d95100067d74d95100067c74d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95101ee7f70d95101ee7e70d95101ee7d70d95101ee7c70d95101ee7f40d95101ee7e40d95101ee7d40d95101ee7c40d95101ee7f30d95101ee7e30d95101ee7d30d95101ee7c30d95101ee7f20d95101ee7e20d95101ee7d20d95101ee7c20d95101ee7e10d95101ee7d10d95101ee7c10d951001d7e75d91100057d75d91100067f65d91100067c65d91101d7f010d9110004ff75d9110014fe75d91100067e75d91100147e75d9110004fd75d91100067d75d91100047d75d9110014fc75d91100067c54d9110024fe72d9110004fd72d91100067f52d911003cff70d911003cfd70d91101e6f970d91101d6bf40d91101d6bd40d91101d6f840d91101dcfd769911001d7e75991100057d75991100067f65991100067c6599110006bf649911007df970991101cff01099110004ff7599110014fe75991100067e75991100147e7599110004fd75991100067d75991100047d7599110014fc75991101c4fe74991100067c5499110024fe7299110004fd72991100067f52991101ccfd7099110006f970991100057f755911001d7c75591100067f65591100067c6559110005ef7259110005ec725911008dfb70591101dff01059110004ff75591100067f75591100047f7559110014fe7559110004fd7559110014fc75591100067c75591100147c7559110006bf74591100067c5459110004ff7259110006ef7259110004ef7259110024fc7259110006ec7259110024ec72591100067f52591101dcff7059110006fb70591101def840591101d4fe761911001d7c75191100067f65191100067c6519110006bd64191101c7f01019110004ff75191100067f7519110014fe7519110004fd7519110014fc75191100067c75191100147c75191101ccfe7419110006be74191100067c5419110024fe7219110004fd72191100067f521911003cff701911000cfe701911003cfd701911000cfc70191101c6bf40191101c6bd40191100067f76951100057e76951100067e76951100047e76951100067d76951100057c76951100067c76951100047c76951101bd7e749511001f3e74951100067f64951100067e64951100067d64951100067c64951100057d72951101b67e62951101b67c62951100077b70951101477870951101467f60951101477840951101477a30951101477a2095110147761095110147781095110147701095110024fe76d891001d7c75d89100067f65d89100067c65d8910197f010d8910004ff75d89100067f75d8910014fe75d8910004fd75d8910014fc75d89100067c75d89100147c75d8910004fe74d8910004fd74d89100067e54d89100067c54d8910044fe73d8910004fd73d89100067f53d
  | 3 => 0xb70549201377870549200267f60549200277b20549201376e20549200276c20549200277820549201377a105492000cfe76d092000cfc76d09200057f75d09200357c75d0920006bf64d0920006bc64d092000dfa70d0920005f970d0920124ff765092000cfe76509200f4fd765092000cfc76509200057f75509200357c7550920006bf6450920006bc64509200076d5250920005fb705092000df87050920027e8205092000cfe76cc92000cfc76cc9200357e75cc9200057d75cc920005be74cc920005bd74cc920006df63cc920046dc63cc92000dfa70cc920005f970cc92009dee768c920026ee768c9200276e758c9200276d758c920027ae748c920027ad748c920006ee648c920006ec648c9200076e548c92020f6c548c9200aded738c920046ee638c920046ec638c92020f6f538c9200076d538c92000dee708c92000dec708c920026ef608c920027eb608c9200bfea108c920044ff764c92000cfe764c9200acfd764c92000cfc764c9200357e754c9200057d754c920006df634c920046dc634c9202076f524c9200076d524c920027cc324c920005fb704c92000df8704c92000dec764c920046ec764c92000cec764c9202076e754c9200076d754c920006ee644c920006ec644c9200076e544c9202076c544c920025ef734c920027cf734c920007cf634c920046ee634c920046ec634c920007cc634c920046cc634c9202076f534c9200076d534c920007cf434c920007cc434c920007eb704c92000dee704c92000dec704c9200afe8704c920026ef604c920027eb604c9200afcf304c9200afcd304c9200afea104c92003cfe76d852002ef661d8520004ff75d8520014fe75d8520004fd75d8520014fc75d8520004fe74d8520004fd74d85200067e54d85200067c54d8520044fe73d8520004fd73d85200067f53d85200067d53d852000cfd72d852003cfc72d85200067f52d85200067d52d8520006ee32d8520006ed32d852002ef621d852000cfe70d8520024fd70d852000cfc70d85201a6f710d85200057f75585200357c7558520005bf7458520005bc7458520005df7358520005dc735852002ef46158520004fe76d0520004fd76d0520004fc76d0520004ff7650520004fe7650520004fc76505200057f75505200357c7550520004fe76cc520004fd76cc520044fc76cc5200357e75cc5200057d75cc520025ee72cc520005ed72cc520007cd32cc520004fe764c520004fc764c520007cd324c52000cfc7648520006f7614852003ef46148520005fb704852000df870485201fd7e76d951001e7e76d95100147e76d95100057e74d95100057d72d95101f77b70d95101ef7870d95101ef7840d95101ef7a30d95101ef7a20d95101ef7610d95101ef7810d95101ef7010d95100067f74d95100067e74d9510
  | 4 => 0x9120024fe7219120024fc72191200067f521912003cfe7119120004fd711912003cfc7119120006be4119120006bc4119120024ff7019120024fd70191200d6bf40191200d6bd40191200d6fa10191200067f76951200067e76951200067d76951200067c76951201bd7e74951200373e74951200067f64951200067e64951200067d64951200067c64951200057d73951202467e63951202467c63951200057d72951201467f629512023e7e619512023e7c61951201467f60951201b77b20951201476e20951201476c20951201477820951201477a1095120044fe76d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004fe74d8d20004fd74d8d200067e54d8d200067c54d8d200067f53d8d20024fe72d8d20024fc72d8d200067f52d8d2003cfe71d8d20004fd71d8d2003cfc71d8d20006de31d8d20006dc31d8d20024ff70d8d20024fd70d8d200bedf30d8d200bedd30d8d200befa10d8d200357e7598d200057d7598d20005be7498d20005bd7498d20006df6398d200aded7298d20235ef7258d20004ff7558d20014fe7558d20004fd7558d20014fc7558d20004ff7458d20004fc7458d200067e5458d200067c5458d20006df7358d200067f5358d20234ff7258d20006ef7258d200067f5258d20004ff7158d2003cfe7158d2003cfc7158d200acff7058d20006fb7058d200aefa1058d200bcfe7618d200357e7518d200057d7518d20046de6318d20006dd6318d200067f7654d200067e7654d200067d7654d200067c7654d200057c7454d200067f6454d200067e6454d200067d6454d200067c6454d2022d7f7354d200375f7354d200067f6354d200467e6354d200067d6354d200467c6354d200057f7254d202167f6254d202267e6154d202267c6154d202167f6054d2021f7b2054d202176e2054d202176c2054d20217782054d202177a1054d20004ff76d0d20004fe76d0d20004fd76d0d20004fc76d0d200057f75d0d200357c75d0d20006bf64d0d20006bc64d0d20044ff7690d20004fe7690d20004fd7690d20044fc7690d200357e7590d200057d7590d20025ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200357c7550d20006bf6450d20006bc6450d20044ff7610d20004fe7610d20004fd7610d20044fc7610d200357e7510d200057d7510d20025ee7210d20005ed7210d2000dfa7010d20005f97010d200167f76549201367e76549201367d76549200167c76549200057c74549200067f64549200067e64549200067d64549200067c64549200057f73549200067f63549201867e63549200067d63549201867c63549200257f72549200376f72549200267f62549200276e42549200276e325492013e7e615492013e7c61549200077
  | 5 => 0x4fd7610f20024fc7610f200557e7510f200057d7510f2026e7e6510f200067d6510f20006be6410f20006bd6410f20046de6310f20006dd6310f20025ee7210f20005ed7210f20025ef764cb20006ef764cb202676e754cb200076d754cb200276e654cb200276d654cb20006ee644cb20026ec644cb200076e544cb202676c544cb20027cf734cb20027cf634cb20046ee634cb20026ec634cb20027cc634cb20026cc634cb202676f534cb200076d534cb20007cf434cb20007cc434cb2000dee704cb2000dec704cb200afcf304cb200afcd304cb20004ff7558720014fe7558720004fd7558720014fc7558720004ff7458720004fc74587200067e54587200067c5458720004ff7358720044fc73587200067f53587200067d535872000cfe725872003cfd725872000cfc72587200267f52587200267d5258720026ee3258720006ed3258720026f77158720026f72158720026f42158720026fa2058720026f9205872019ef71058720004ff76d0720024fe76d0720004fd76d072025e7e65d07200067d65d0720006be64d0720006bd64d0720004ff7650720004fd7650720024fc76507200057f75507200557c75507202567e65507200067d6550720006be6450720006bd6450720024fe76cc720004fd76cc72024e7e65cc7200067d65cc720025ee72cc720005ed72cc720007cd32cc7200357e75d91200057d75d91200073c54d9120004ff75d9120014fe75d91200067e75d91200147e75d9120004fd75d91200067d75d91200047d75d9120014fc75d9120006bf54d91200067c54d9120006bc54d91200063c54d9120044fe73d9120004fd73d91200067f53d91200067f52d912003cfe71d9120004fd71d912003cfc71d9120006be41d9120006bc41d9120024ff70d9120024fd70d912010ebf40d912010ebd40d9120006bf64991200f5ed7299120004ff7599120014fe7599120004fd7599120014fc75991200d4fe74991200067c5499120044fe7399120004fd73991200067f53991200f4fd7299120006ed72991200067f529912003cfe7199120004fd719912003cfc7199120124fd7099120006f97099120126fa10991200057f75591200357c7559120125ef7259120004ff75591200067f75591200047f7559120014fe7559120004fd7559120014fc75591200067c75591200147c7559120006bf74591200067c5459120004ff7359120044fc73591200067f5359120124ff7259120006ef72591200067f5259120004ff715912003cfe715912003cfc71591200f4ff7059120006fb705912010cfe7619120006bd64191200073c5419120004ff7519120014fe7519120004fd7519120014fc7519120006be7419120006bf54191200067c5419120006bc54191200063c5419120044fe7319120004fd73191200067f531
  | 6 => 0xc1059720004ff75993200067f7599320014fe7599320004fd7599320014fc75993200067c75993200147c7599320026be74993200067c5499320044fe7399320004fd73993200067f539932000cfe729932000cfc72993200267f52993200267d5299320026be4299320026bc4299320026ee329932003cfe7199320004fd719932003cfc7199320126bf4099320126bd4099320004ff75593200067f75593200047f7559320014fe7559320004fd7559320014fc75593200067c75593200147c7559320026bf74593200067c5459320004ff7359320044fc73593200067f5359320024ff725932000cfe7259320024fd725932000cfc72593200267f52593200267d5259320026be4259320026bc4259320004ff715932003cfe715932003cfc71593200f6bf40593200f6bd40593201b57f76953200067f76953200047f76953201b67e76953201b57d76953200067d76953200047d76953201b67c76953201bd7e74953200573e74953201b67f64953200067e64953200067d64953201b67c64953200057d73953201b67f63953202467e63953201b67c63953201b57f72953201b57d72953201467e62953201b76e329532023e7e619532023e7c61953201467d60953201476e20953201477a20953201476c2095320004ff7558f20014fe7558f200067e7558f200147e7558f20004fd7558f200067d7558f20014fc7558f20004ff7458f20004fc7458f200067e5458f200067c5458f20026df7358f200067f5358f2000cfe7258f20024fd7258f2000cfc7258f200267f5258f200267d5258f20026de3258f20026dc3258f20004ff7158f2003cfe7158f2003cfc7158f200aedf3058f200aedd3058f2021d7f7654f200067f7654f200047f7654f2021e7e7654f2021d7d7654f200067d7654f200047d7654f2021e7c7654f200057c7454f2021e7f6454f200067e6454f200067d6454f2021e7c6454f2022d7f7354f200575f7354f2021e7f6354f200467e6354f200067d6354f200467c6354f2021d7f7254f2021d7d7254f202167e6254f2021f6e3254f202267e6154f202267c6154f202167d6054f202176e2054f202177a2054f202176c2054f20004ff76d0f20024fe76d0f20004fd76d0f20024fc76d0f200057f75d0f200557c75d0f202967e65d0f200067d65d0f2028ebf64d0f2028ebc64d0f20046de63d0f20006dd63d0f20044ff7690f20024fe7690f20004fd7690f20024fc7690f200557e7590f200057d7590f202867e6590f200067d6590f20006be6490f20006bd6490f20025ee7290f20005ed7290f20004ff7650f20024fe7650f20004fd7650f20024fc7650f200057f7550f200557c7550f2027e7e6550f200067d6550f20276bf6450f20276bc6450f20005fb7050f2000df87050f20044ff7610f20024fe7610f20
  | 7 => 0x93009dde76cc930046de76cc9300475e75cc9300475d75cc9300479e74cc9300479d74cc930006de64cc930006dc64cc9300075e54cc9302af5c54cc930026de62cc930026dc62cc9302af5f52cc9300075d52cc93000dde70cc93000ddc70cc930046df60cc930047db60cc930237da10cc93000cfe768c9300657e758c9300057d758c930005be748c930005bd748c9300addd738c930006ef628c930026ec628c93000dfa708c930005f9708c93000cfc764c9300657e754c9300057d754c9302a75f534c9300075d534c930006ef624c930026ec624c930047cc324c930005fb704c93000df8704c93000ddc764c930026dc764c93000cdc764c9302a75e754c9300075d754c930006de644c930006dc644c9300075e544c9302a75c544c930045df724c930047cf724c930007cf624c930026de624c930026dc624c930007cc624c930026cc624c9302a75f524c9300075d524c930007cf424c930007cc424c930007db704c93000dde704c93000ddc704c9300afd8704c930046df604c930047db604c9300afda104c93003cfe76d853005ef661d8530004ff75d8530014fe75d8530004fd75d8530014fc75d8530004fe74d8530004fd74d85300067e54d85300067c54d853000cfd73d853003cfc73d85300067f53d85300067d53d8530024fe72d8530004fd72d85300067f52d85300067d52d8530006df32d8530006dd32d853005ef631d8530044fd70d853029ef710d85300057f75585300657c7558530005bf7458530005bc7458530005ef7258530005ec725853005ef46158530004fe76d0530004fd76d0530004fc76d0530004ff7650530004fe7650530004fc76505300057f75505300657c7550530004fe76c8530004fd76c8530024fc76c85300657e75c85300057d75c8530045de73c8530005dd73c8530007cd32c8530004fe7648530004fc7648530007cd32485300067f74597200067e74597200067d74597200067c74597200047c74597200067f73597200047f73597200067e73597200067d73597200067c73597200267f72597200247f72597200267e72597200267d72597200247d72597200267c72597200267f42597200267e42597200267d42597200267c42597200267f32597200267e32597200267d32597200267c32597200067f71597200067e71597200067d71597200067c71597200067e41597200067c41597200067e31597200067c31597200267f21597200267e21597200267d21597200267c21597201367f70597201367e70597201367d70597201367c70597201367f40597201367e40597201367d40597201367c40597201367f30597201367e30597201367d30597201367c30597200267f20597200267e20597200267d20597200267c20597201367f10597201367e10597201367d10597201367
  | 8 => 0x14fc7519130006be7419130006bf54191300067c5419130006bc54191300063c54191300067f5319130024fe7219130004fd72191300067f521913003cfe7119130004fd711913003cfc7119130006be4119130006bc4119130044ff7019130044fd70191302c6bf40191302c6bd40191302c6fa10191300067f76951300067e76951300067d76951300067c76951301bd7e74951300673e74951300067f64951300067e64951300067d64951300067c64951300057d73951301467f63951300057d72951301b67c629513023e7e619513023e7c61951301467f60951302477b30951301475e30951301475c30951301477830951301477a10951300167f7654d302167e7654d302167d7654d300167c7654d300057c7454d300067f6454d300067e6454d300067d6454d300067c6454d300457f7354d300675f7354d300467f6354d300475e4354d300057f7254d3021e7c6254d300475f3254d302267e6154d302267c6154d300077b7054d30217787054d300467f6054d300477b3054d302175e3054d300475c3054d30047783054d302177a1054d3000cfe76d0d3000cfc76d0d300057f75d0d300657c75d0d30006bf64d0d30006bc64d0d3000dfa70d0d30005f970d0d302bcff7650d3000cfe7650d302b4fd7650d3000cfc7650d300057f7550d300657c7550d30006bf6450d30006bc6450d300075d5350d30005fb7050d3000df87050d30047d83050d30024fe76d8930004ff75d8930014fe75d8930004fd75d8930014fc75d8930004fe74d8930004fd74d89300067e54d89300067c54d89300067f53d89300067d53d89300067f52d893003cfe71d8930004fd71d893003cfc71d8930006ee21d8930006ec21d8930044fd70d8930236ef20d8930236fa10d89300657e75989300057d7598930005be7498930005bd7498930006ef62989300657e75189300057d7518930026ee6218930006ed62189300067f76549300067e76549300067d76549300067c76549300057c74549300067f64549300067e64549300067d64549300067c64549300057f73549301367f635493017d7f72549300676f72549300067f62549300267e62549300267c625493013e7e615493013e7c61549301367f60549301877b30549301375e30549301375c30549301377830549301377a1054930004fe76d0930004fd76d0930004fc76d09300057f75d09300657c75d0930006bf64d0930006bc64d0930004fe7690930004fd7690930024fc76909300657e75909300057d7590930045de7390930005dd7390930004ff7650930004fe7650930004fc76509300057f75509300657c7550930006bf6450930006bc6450930004fe7610930004fd7610930024fc76109300657e75109300057d7510930045de7310930005dd731093000dfa7010930005f9701
  | 9 => 0xf7650b30004fd7650b30044fc7650b300057f7550b300757c7550b301067e6550b300067d6550b302eebf6450b302eebc6450b30005fb7050b3000df87050b30024ff7610b30044fe7610b30004fd7610b300757e7510b300057d7510b300e67e6510b300067d6510b30006be6410b30006bd6410b30045de7310b30005dd7310b30026ee6210b30006ed6210b30045df764cb30006df764cb302e75e754cb300075d754cb300475e654cb300475d654cb30006de644cb30046dc644cb300075e544cb302e75c544cb30047cf724cb30047cf624cb30026de624cb30026dc624cb30047cc624cb302e75f524cb300075d524cb30007cf424cb30007cc424cb3000dde704cb3000ddc704cb30004ff7558730014fe7558730004fd7558730014fc7558730004ff7458730004fc74587300067e54587300067c545873000cfe735873003cfd735873000cfc73587300467f53587300467d5358730004ff7258730024fc72587300067f52587300067d5258730046df3258730006dd3258730046f77158730046f73158730046f43158730046fa3058730046f930587302def71058730004ff76d0730044fe76d0730004fd76d073025e7e65d07300067d65d0730006be64d0730006bd64d0730004ff7650730004fd7650730044fc76507300057f75507300757c75507302567e65507300067d6550730006be6450730006bd6450730044fe76c8730004fd76c87302d67e65c87300067d65c8730026ee62c8730006ed62c8730007cd32c87300657e75d91300057d75d91300073c54d9130004ff75d9130014fe75d91300067e75d91300147e75d9130004fd75d91300067d75d91300047d75d9130014fc75d9130006bf54d91300067c54d9130006bc54d91300063c54d91300067f53d9130024fe72d9130004fd72d91300067f52d913003cfe71d9130004fd71d913003cfc71d9130006be41d9130006bc41d9130044ff70d9130044fd70d91302cebf40d91302cebd40d9130006bf64991302b5dd7399130004ff7599130014fe7599130004fd7599130014fc75991302c4fe74991300067c54991302b4fd7399130006dd73991300067f5399130024fe7299130004fd72991300067f529913003cfe7199130004fd719913003cfc71991302bcfd7099130006f970991302befa10991300057f75591300657c75591302bddf7359130004ff75591300067f75591300047f7559130014fe7559130004fd7559130014fc75591300067c75591300147c7559130006bf74591300067c54591302bcff7359130006df73591300067f5359130004ff7259130024fc72591300067f5259130004ff715913003cfe715913003cfc71591302b4ff7059130006fb70591302ccfe7619130006bd64191300073c5419130004ff7519130014fe7519130004fd7519130
  | 10 => 0x97300467d31597300467c31597300067e21597300067c21597302167f70597302167e70597302167d70597302167c70597302167f40597302167e40597302167d40597302167c40597300467f30597300467e30597300467d30597300467c30597302167f20597302167e20597302167d20597302167c20597302167f10597302167e10597302167d10597302167c1059730004ff75993300067f7599330014fe7599330004fd7599330014fc75993300067c75993300147c7599330046be74993300067c549933000cfe739933000cfc73993300467f53993300467d5399330046be4399330046bc4399330024fe7299330004fd72993300067f5299330046df329933003cfe7199330004fd719933003cfc71993302bebf40993302bebd4099330004ff75593300067f75593300047f7559330014fe7559330004fd7559330014fc75593300067c75593300147c7559330046bf74593300067c545933000cfe735933000cfc73593300467f53593300467d5359330046be4359330046bc4359330004ff7259330024fc72593300067f5259330004ff715933003cfe715933003cfc71593302b6bf40593302b6bd40593302457f76953300067f76953300047f76953302467e76953302457d76953300067d76953300047d76953302467c76953301bd7e74953300773e74953302467f64953300067e64953300067d64953302467c64953302457f73953302457d73953301467e63953300057d72953301b67e62953302475f329533023e7e619533023e7c61953301467d60953301475e30953301477a30953301475c3095330004ff7558b30014fe7558b300067e7558b300147e7558b30004fd7558b300067d7558b30014fc7558b30004ff7458b30004fc7458b300067e5458b300067c5458b3000cfc7358b300467f5358b300467d5358b30046ef7258b300067f5258b30046ef3258b30046ec3258b30004ff7158b3003cfe7158b3003cfc7158b300aeef2058b301857f7654b300067f7654b300047f7654b301867e7654b301857d7654b300067d7654b300047d7654b301867c7654b300057c7454b301867f6454b300067e6454b300067d6454b301867c6454b301857f7354b301857d7354b301367e6354b3017d7f7254b300776f7254b300267e6254b300067d6254b300267c6254b301875f3254b3013e7e6154b3013e7c6154b301367d6054b301375e3054b301377a3054b301375c3054b30004ff76d0b30044fe76d0b30004fd76d0b300057f75d0b300757c75d0b300ee7e65d0b300067d65d0b302f6bf64d0b302f6bc64d0b30026ee62d0b30006ed62d0b30024ff7690b30044fe7690b30004fd7690b300757e7590b300057d7590b3011e7e6590b300067d6590b30006be6490b30006bd6490b30045de7390b30005dd7390b30004f
  | 11 => 0x73f655094030f3c6550940005bf73509402eebc635094030f3f53509400073d5350940007af7250940007af6250940026be6250940026bc6250940007ac625094030f3f52509400073d5250940007bb705094000dbe705094000dbc70509400f7b870509400f6bf6050940124fe76109400857e75109400057d75109400067f65109400e67c6510940125be7410940004fe76cc940004fd76cc940044fc76cc9400857e75cc9400057d75cc9400067f65cc9403067c65cc940005be74cc940005bd74cc940006df63cc940046dc63cc9400079f43cc940004fe768c940004fd768c940024fc768c9400857e758c9400057d758c9400067f658c9400ce7c658c940005be748c940005bd748c940006ef628c940026ec628c940007af428c940004ff764c940004fe764c940004fc764c9400857e754c9400057d754c9400067f654c9400b67c654c940005be744c940005bd744c940006df634c940046dc634c9400079f434c940006ef624c940026ec624c940007af424c940004fe760c940004fd760c940024fc760c9400857e750c9400057d750c9400067f650c9400a67c650c940005be740c940005bd740c940007cd320c94000dfa700c940005f9700c94003cfe76d85400067f65d85400067c65d854007ef661d8540004ff75d8540014fe75d8540004fd75d8540014fc75d854000cfd74d85400067e54d85400067c54d8540044fe73d8540004fd73d85400067f53d85400067d53d8540006bf43d8540006bd43d8540024fe72d8540004fd72d85400067f52d85400067d52d8540006bf42d8540006bd42d854007ef641d85401cef840d85401cef710d85400057f75585400857c75585400067f65585400067c6558540005df7358540005dc7358540005ef7258540005ec725854007ef461585401c4fe76d05400067f65d054025e7c65d054003ef661d05401cfb840d054000cfc76505400067f65505402567c6550540005fb705054000df870505401dfb8405054000dfa76d014000efa76d014000cfa76d01400077b65d01402ff7865d014000dfa74d014000fba74d014000efb64d014000fbb64d01400077a54d01402ff7854d01402ff7b53d01400077953d0140007bb43d0140007b943d01402ff7b52d01400077952d0140007bb42d0140007b942d0140006fb61d01400067f74597300067e74597300067d74597300067c74597300047c74597300467f73597300467e73597300467d73597300467c73597300467f43597300467e43597300467d43597300467c43597300067f72597300047f72597300067e72597300067d72597300067c72597300467f32597300467e32597300467d32597300467c32597300067f71597300067e71597300067d71597300067c71597300067e41597300067c41597300467f31597300467e315
  | 12 => 0xf60d0d4000cfe7690d400857e7590d400057d7590d400067f6590d402867c6590d402b5bd7490d40006df6390d40046dc6390d40005ee7290d40005ed7290d4000dfa7090d40005f97090d4000cfc7650d400057f7550d400857c7550d400067f6550d4027e7c6550d400073e5450d4031f3c5450d40006df6350d40046dc6350d40005fb7050d4000df87050d4000dbc7650d40046bc7650d4000cbc7650d400073f7550d4031f3c7550d400073f6550d4031f3c6550d400079f7350d400079f6350d40046be6350d40046bc6350d400079c6350d4031f3f5350d400073d5350d40005bf7250d40276bc6250d4031f3f5250d40007bb7050d4000dbe7050d4000dbc7050d402b7b87050d402b6bf6050d402bcfe7610d400857e7510d400057d7510d400067f6510d4026e7c6510d402bdbe7410d40024fe76d89400857c75d89400067f65d89400067c65d8940004ff75d89400067f75d8940014fe75d8940004fd75d8940014fc75d89400067c75d89400147c75d89400067e54d89400067c54d8940044fe73d8940004fd73d89400067f53d89400067d53d89400067f52d894003cfe71d8940004fd71d894003cfc71d8940006ee21d8940006ec21d8940126ef20d89400857e75989400057d75989400067f65989400067c6598940005de7398940005dd7398940006ef62989400057f75589400857c75589400067f65589400067c65589400857e75189400057d75189400067f65189400067c6518940026ee6218940006ed62189400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400057c74549401367f64549400057f73549400067f63549401867c63549400073f43549400073d435494017d7f72549400876f72549400067f62549400267e62549400267c625494013e7e615494013e7c61549401367f60549401373e40549401373c40549401377840549400d4fe76d09400057f75d09400857c75d09400067f65d09400ee7c65d09400073e54d09403173c54d09400d5be76d0940006be76d09400073f75d09403173c75d09400073f65d09403173c65d0940005bd73d09402f6bc63d09403173f53d09400073d53d0940026be62d0940026bc62d09403173f52d09400073d52d094000dbe70d094000dbc70d0940126bf60d094000cfe76909400857e75909400057d75909400067f659094011e7c65909400f5bd7490940005de7390940005dd7390940006ef6290940026ec629094000dfa7090940005f9709094000cfc76509400057f75509400857c75509400067f65509401067c65509400073e545094030f3c5450940006ef6250940026ec6250940005fb705094000df8705094000dbc7650940026bc765094000cbc76509400073f755094030f3c7550940
  | 13 => 0x8740006bd4358740004ff7258740024fc72587400067f52587400067d5258740006bf4258740006bd425874008ef441587401def7105874000cfd76d074000dfa70d0740005f970d07401bd7e76d95400867e76d95400147e76d95401457c74d95400057d73d95400057d72d95400067e61d95400067c61d95401473e40d95401473c40d95401477840d95401467f74d95400867e74d95400147e74d95401467d74d95401467c74d95400147c74d95400067f73d95400067e73d95400067d73d95400047d73d95400067c73d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95400067f71d95400067e71d95400067d71d95400067c71d95400067e41d95400067c41d95400067e31d95400067c31d95400067e21d95400067c21d95401467f70d95401467e70d95401467d70d95401467c70d95401467f40d95401467e40d95401467d40d95401467c40d95401467f30d95401467e30d95401467d30d95401467c30d95401467f20d95401467e20d95401467d20d95401467c20d95401467f10d95401467e10d95401467d10d95401467c10d95401bd7e769514032e7e76951401bc7e76951401bd7e74951400873e74951401467f64951400057d73951402467c63951400057d72951401b67c629514023e7e619514023e7c61951401467f60951401473e40951401473c4095140147784095140044fe76d8d400857c75d8d400067f65d8d400067c65d8d40004ff75d8d400067f75d8d40014fe75d8d40004fd75d8d40014fc75d8d400067c75d8d400147c75d8d400067e54d8d400067c54d8d400067f53d8d40024fe72d8d40004fd72d8d400067f52d8d4003cfe71d8d40004fd71d8d4003cfc71d8d40006de31d8d40006dc31d8d402bedf30d8d400857e7598d400057d7598d400067f6598d400067c6598d40006df6398d40005ee7298d40005ed7298d400057f7558d400857c7558d400067f6558d400067c6558d400857e7518d400057d7518d400067f6518d400067c6518d40046de6318d40006dd6318d400067f7654d400057e7654d400067e7654d400047e7654d400067d7654d400057c7654d400067c7654d400047c7654d400057c7454d402167f6454d4022d7f7354d400875f7354d400067f6354d400467e6354d400467c6354d400057f7254d4021e7c6254d402267e6154d402267c6154d402167f6054d402173e4054d402173c4054d40217784054d402c4fe76d0d400057f75d0d400857c75d0d400067f65d0d402967c65d0d400073e54d0d403273c54d0d402c5be76d0d40006be76d0d400073f75d0d403273c75d0d400073f65d0d403273c65d0d40046be63d0d40046bc63d0d403273f53d0d400073d53d0d40005bd72d0d4028ebc62d0d403273f52d0d4000dbe70d0d4000dbc70d0d402beb
  | 14 => 0x957e7510f400057d7510f40046de6310f40006dd6310f4000dfa7010f40005f97010f400957e7598b400057d7598b40005de7398b40005dd7398b40006ef6298b40024ff7658b40004ff7558b40014fe7558b40004fd7558b40014fc7558b400067e5458b400067c5458b40004ff7358b40044fc7358b400067f5358b400067d5358b400067f5258b40004ff7158b4003cfe7158b4003cfc7158b400f6ef2058b400f6fa1058b400957e7518b400057d7518b40026ee6218b40006ed6218b400067f7654b400067e7654b400067d7654b400067c7654b400057c7454b401367e6454b400057f7354b401867e6354b400067d6354b400073f4354b400073d4354b4017d7f7254b400976f7254b400267e6254b400067d6254b400267c6254b4013e7e6154b4013e7c6154b401367d6054b401373e4054b401377a4054b401373c4054b401377a1054b4000cfd76d0b400057f75d0b400957c75d0b400073e54d0b4033f3c54d0b40026ee62d0b40006ed62d0b4000dfa70d0b40005f970d0b4000dbd76d0b40026bd76d0b4000cbd76d0b400073f75d0b4033f3c75d0b40005bd73d0b402f6be63d0b4033f3f53d0b400073d53d0b40026be62d0b40007ae62d0b40007ad62d0b40026bc62d0b4033f3f52d0b400073d52d0b4000dbe70d0b40127ba70d0b40007b970d0b4000dbc70d0b40127ba10d0b400f4fd7690b400957e7590b400057d7590b40005de7390b40005dd7390b4010cff7650b400057f7550b400957c7550b400073e5450b403373c5450b4010dbf7650b40006bf7650b400073f7550b403373c7550b40005bf7350b402eebe6350b403373f5350b400073d5350b40007af7250b40026be6250b40026bc6250b403373f5250b400073d5250b4000dbe7050b4000dbc7050b400f7ba1050b4000cfd7610b400957e7510b400057d7510b40026ee6210b40006ed6210b4000dfa7010b40005f97010b40044ff76ccb40004fe76ccb40004fd76ccb400957e75ccb400057d75ccb40005be74ccb40005bd74ccb40046dc63ccb400079f43ccb40024ff768cb40004fe768cb40004fd768cb400957e758cb400057d758cb40005be748cb40005bd748cb40026ec628cb40007af428cb40004ff764cb40004fd764cb40004fc764cb400957e754cb400057d754cb40005be744cb40005bd744cb400079f434cb40007af424cb40005fb704cb4000df8704cb40024ff760cb40004fe760cb40004fd760cb400957e750cb400057d750cb40005be740cb40005bd740cb40007cd320cb400957e75d87400057d75d874008ef661d874003cff765874008ef46158740004ff7558740014fe7558740004fd7558740014fc755874000cfc74587400067e54587400067c5458740004ff7358740044fc73587400067f53587400067d5358740006bf435
  | 15 => 0xc644c832026cc644c83235fcf544c83235fce544c8320074e544c83235fcd544c83235fcc544c83235f4c544c832007cf704c832357ce704c832007cd704c832357cc704c832027cf604c832027ce604c832027cd604c832027cc604c83235fcf504c832357ce504c83235fcd504c832357cc504c832357ce404c832357cc404c832357ce104c832357cc104c832004ff7558032014fe7558032004fd7558032014fc7558032004ff7458032004fc74580320067e54580320067c54580320467f53580320467d53580320267f52580320267d5258032026df3258032026ee3258032026dd3258032046ed3258032006cd3258032004ff715803203cfe715803203cfc7158032024ff7058032026fb705803209efa4058032046fb3058032046f83058032026fb2058032026f8205803209efa10580321467f76953400167e76953400167d76953401467c76953401bd7e74953400973e74953401467e64953400057d73953402467e63953400057d72953401b67e629534023e7e619534023e7c61953401477a70953400077970953401473e40953401477a40953401473a40953401473c40953401477a10953400957e7598f400057d7598f40006df6398f40005ee7298f40005ed7298f40044ff7658f40004ff7558f40014fe7558f40004fd7558f40014fc7558f400067e5458f400067c5458f400067f5358f40004ff7258f40024fc7258f400067f5258f40004ff7158f4003cfe7158f4003cfc7158f402b6df3058f402b6fa1058f400957e7518f400057d7518f40046de6318f40006dd6318f400067f7654f400067e7654f400067d7654f400067c7654f400057c7454f402167e6454f4022d7f7354f400975f7354f400467e6354f400067d6354f400467c6354f400057f7254f4021e7e6254f402267e6154f402267c6154f402167d6054f402173e4054f402177a4054f402173c4054f402177a1054f4000cfd76d0f400057f75d0f400957c75d0f400073e54d0f4034f3c54d0f40046de63d0f40006dd63d0f4000dfa70d0f40005f970d0f4000dbd76d0f40046bd76d0f4000cbd76d0f400073f75d0f4034f3c75d0f40046be63d0f400079e63d0f400079d63d0f40046bc63d0f4034f3f53d0f400073d53d0f40005bd72d0f4028ebe62d0f4034f3f52d0f4000dbe70d0f402bfba70d0f40007b970d0f4000dbc70d0f402bfba10d0f402b4fd7690f400957e7590f400057d7590f40005ee7290f40005ed7290f402ccff7650f400057f7550f400957c7550f400073e5450f403473c5450f402cdbf7650f40006bf7650f400073f7550f403473c7550f400079f7350f40046be6350f40046bc6350f403473f5350f400073d5350f40005bf7250f40276be6250f403473f5250f4000dbe7050f4000dbc7050f402b7ba1050f4000cfd7610f40
  | 16 => 0x932007ae6410932006ed6410932007ad64109320076e54109323776c5410932027cf7310932045ee7310932025ec7310932027cc7310932026ef6310932027cf63109323776f53109320076d5310932007af4310932007cf43109320078f4310932007ad4310932007cc4310932005ed7110932005ed701093200cfe76d81320b57e75d81320057d75d81320067e65d81320067d65d81320aefa60d8132004ff75d8132014fe75d81320067e75d81320147e75d8132004fd75d81320067d75d81320047d75d8132014fc75d8132004fe74d8132004fd74d81320067e54d81320067c54d8132024fd73d81320067f53d81320067d53d8132044fd72d81320067f52d81320067d52d813203cfe71d8132004fd71d813203cfc71d81320aef840d81320aefa30d81320aefa20d81320067e65581320067d65581320aef860581320067f74594320067e74594320067d74594320067c74594320047c74594320267f72594320267e72594320267d72594320267c72594320267f42594320267e42594320267d42594320267c42594320267e32594320267d32594320267c32594320067f70594320067e70594320067d70594320067c70594320067e40594320067c40594320467f30594320467e30594320467d30594320467c30594320267f20594320267e20594320267d20594320267c20594320067e10594320067c1059432004ff75990320067f7599032014fe7599032004fd7599032014fc75990320067c75990320147c7599032024fe7499032026be74990320067c5499032024fe7299032024fc72990320267f52990320267d5299032026be4299032026bc4299032026ee3299032046ed329903200cfe7099032004fd709903200cfc7099032004ff75590320067f75590320047f7559032014fe7559032004fd7559032014fc75590320067c75590320147c7559032024ff7459032026bf74590320067c5459032024fe7259032024fc72590320267f52590320267d5259032026be4259032026bc4259032004ff705903200cfe705903200cfc70590321b57f76950320067f76950320047f76950321b67e76950321b57d76950320067d76950320047d76950321b67c769503236d7e74950320a73e74950321b67f64950320067e64950320067d64950321b67c64950321b57f72950321b57d72950321b67e62950321b76e32950322476d32950321467e60950321467c6095032027cf764c832025cf764c832006cf764c832367cf754c83235fce754c83235f4e754c832367cd754c8320074d754c83235fcc754c832027cf654c832027ce654c8320274e654c832027cd654c8320274d654c832027cc654c832007cf744c832007ce744c832007cd744c832007cc744c832027cf644c832027ce644c832006ce644c832027cd644c832027c
  | 17 => 0x4fe74991320067c5499132004fd7299132006ed72991320067f529913228ebe429913228ebc429913200cfe7099132004fd709913200cfc70991320057f75591320b57c75591320067e65591320067d6559132005fb70591320adf87059132004ff75591320067f75591320047f7559132014fe7559132004fd7559132014fc75591320067c75591320147c7559132006bf74591320067c5459132004ff7259132006ef72591320067f5259132276be4259132276bc4259132004ff7059132006fb7059132004fb705913200cfe705913200cfc7059132006f8705913200cf87059132004fe76191320b57e75191320057d75191320067e65191320067d6519132006bd6419132004ff7519132014fe75191320067e75191320147e7519132004fd75191320067d75191320047d7519132014fc7519132006be74191320067c54191320067f521913200cfe7019132004fd701913200cfc70191320057f76951320067f76951320047f76951320067e76951320057d76951320067d76951320047d76951320067c76951320b57e74951320b73e74951320067f64951320067e64951320067d64951320067c64951320057d72951321b75e32951321467e60951321467c60951320b57f76549320167f76549320147f76549321867e76549320b67d76549320b47d76549320167c76549320057c74549320067f64549320067e64549320067d64549320067c64549320057f73549320075f73549320055f73549320b57d73549320075c73549320267f63549320257f72549320b76f72549320267f62549320276c42549321876f32549320275e32549320275c32549320276c32549320274c325493213e7e615493213e7c61549320276f21549321367e60549321367c60549320276f2054932044fe76d09320057f75d09320b57c75d09320ee7e65d09320067d65d0932006bf64d0932006bc64d0932045de73d0932005dd73d09323876f52d09320076d52d0932027cc32d0932045ee76d0932006ee76d0932044ee76d09320076f75d09323876c75d09323876e65d09320076d65d0932025ee74d0932006ef64d0932007af64d0932006ed64d0932007ac64d09320076e54d09323876c54d0932045ee73d0932007ce73d0932045ce73d0932007cd73d0932045ec73d0932026ef63d0932027cf63d09323876f53d09320076d53d0932007cf43d09322f7ae43d09322f7ac43d0932005ed71d0932005ed70d0932004ff7650932004fd7650932044fc76509320057f75509320b57c75509321067e65509320067d6550932006bf6450932006bc6450932005df7350932045dc7350932027ac4250932027cc3250932005ee7610932026ee76109320276e75109320276d75109323776e65109320076d651093237dee7410932027ae7410932006ef641
  | 18 => 0xe6454e320063e6454e320067d6454e3221f3d6454e320063d6454e3221e7c6454e320457f7354e320cf5f7354e320467d6354e320475e4354e3221d7f7254e320076f7254e320056f7254e3221f6c7254e320467e6254e3221f6c4254e320475f3254e320476f3254e320474f3254e320476c3254e322267e6154e322267c6154e322167e6054e322167c6054e320057f75d0e320cd7c75d0e322967e65d0e320067d65d0e32006be64d0e32006bd64d0e32025ee72d0e32005ed72d0e3228fac42d0e320057f7550e320cd7c7550e3227e7e6550e320067d6550e32006be6450e32006bd6450e320075d5350e32005ef7250e32025ec7250e32277ac4250e32025ed76d0a32006ed76d0a320076f75d0a3238f6c75d0a320276e65d0a320276d65d0a32027ae74d0a32026ef64d0a32027ae64d0a32006ed64d0a32027ad64d0a32006ad64d0a320076e54d0a3238f6c54d0a32045ee73d0a32045ec73d0a3238f6f53d0a320076d53d0a322f7ae43d0a322f7ac43d0a32005ed71d0a32005ed70d0a32004ff7558632014fe7558632004fd7558632014fc7558632004ff7458632004fc74586320067e54586320067c54586320067f53586320067d5358632024fc72586320267f52586320267d5258632026df3258632026dd3258632026f771586320c6f63158632026f72158632026f42158632004ff705863200cfe705863200cfc70586320c6f71058632004ff7558232014fe7558232004fd7558232014fc7558232004ff7458232004fc74582320067e54582320067c54582320067f53582320067d5358232024fc72582320267f52582320267d5258232026df3258232026dd3258232004ff715823203cfe715823203cfc7158232026fb70582320befa3058232026fb2058232026f820582320befa10582320b67f76595320057c74595320076f725953221f5e32595321876c32595320067e60595320067c60595320067f74595320067e74595320067d74595320067c74595320047c74595320067f72595323047f72595320066f725953221e7e425953221e7c425953221e7e325953221e7c32595320067f70595320067e70595320067d70595320067c70595320067e40595320067c40595320067e30595321867c30595320067e205953221e7c20595320067e10595320067c10595320b57e75d91320057d75d91320067e65d91320067d65d9132004ff75d9132014fe75d91320067e75d91320147e75d9132004fd75d91320067d75d91320047d75d9132014fc75d91320067c54d9132006ed72d91320067f52d913200cfe70d9132004fd70d913200cfc70d91320b57c75991320067e65991320067d6599132006bf6499132004ff75991320067f7599132014fe7599132004fd7599132014fc75991320067c75991320147c7599132
  | 19 => 0x9232026be3299232026bd32992320269d3299232026bc3299232006bf7199232006be7199232006bd7199232006bc7199232006bf5199232006be5199232006bd5199232006bc51992322f6bf3199232006be31992322f6bc3199232026bf2199232026be2199232026bd2199232026bc2199232006bf7099232006be7099232006bd7099232006bc7099232006bf5099232006be5099232006bd5099232006bc50992322f6bf3099232006be30992322f6bc3099232026bf2099232026be2099232026bd2099232026bc2099232006bf1099232006be1099232006bc1099232004ff75592320067f75592320047f7559232014fe7559232004fd7559232014fc75592320067c75592320147c7559232026bf7459232006bf5459232006be5459232006bd54592320067c5459232006bc54592320063c54592320067f5359232024fc7259232026ec7259232024ec72592320267f52592320267d5259232026be4259232026bc4259232026ec4259232004ff715923203cfe715923203cfc7159232006be4159232006bc4159232004ff705923200cfe705923200cfc7059232006be4059232006bc4059232006bf75592320063f7559232006be7559232006bd7559232006bc75592320063c7559232006bf73592322eebe7359232006bd73592322eebc7359232006bf53592320063f53592322eebe5359232006bd53592322eebc5359232026bf7259232026be7259232026bd7259232026bc7259232026ac7259232026bf52592320263f5259232026be5259232026bd52592320263d5259232026bc5259232026bf3259232026be3259232026bd3259232026bc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc51592322eebf3159232006be31592322eebc3159232026bf2159232026be2159232026bd2159232026bc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc50592322eebf3059232006be30592322eebc3059232026bf2059232026be2059232026bd2059232026bc2059232006bf1059232006be1059232006bc10592321b57f76952320067f76952320047f76952321b67e76952321b57d76952320067d76952320047d76952321b67c769523236d7e74952320cf3e74952321b67f64952320067e64952321b73e64952320063e64952320067d64952321b73d64952320063d64952321b67c64952320057d73952320b67d63952321b57f72952321b57d72952321b67e62952321b76c42952322476f329523223e7e619523223e7c61952321467e60952321467c609523221d7f7654e320167f7654e320147f7654e320167c7654e320057c7454e3221e7f6454e320067e6454e3221f3
  | 20 => 0x72e5450842397ad54508423976c5450842005ef73508423976f53508420076d5350842007af4350842007ad4350842004ff7558442014fe7558442004fd7558442014fc75584420067e54584420067c5458442004ff7358442044fc73584420067f53584420067d5358442006bf4358442006bd43584420267f52584420267d5258442026bf4258442026bd4258442026ee3258442026f771584420def441584420def63158442026f72158442026f42158442004ff705844200cfe705844200cfc70584420def71058442004ff7558042014fe7558042004fd7558042014fc75580420067e54580420067c5458042004ff7358042044fc73580420067f53580420067d5358042006bf4358042006bd43580420267f52580420267d5258042026bf4258042026bd4258042026ee3258042004ff715804203cfe715804203cfc7158042026fb70580420d6f840580420d6fa3058042026fb2058042026f820580420d6fa10580420067f74596320067e74596320067d74596320067c74596320047c74596320ce7f73596321867e73596320067d73596321867c73596321867e43596321867c43596320267f72596320267e72596320267d72596320267c72596320267f42596320267e42596320267d42596320267c42596320267f32596320267e32596320267d32596320267c32596320067f71596320067e71596320067d71596320067c71596320067e41596320067c41596321867f31596320067e31596321867c31596320267f21596320267e21596320267d21596320267c21596320067f70596320067e70596320067d70596320067c70596320067e40596320067c40596321867f30596320067e30596321867c30596320267f20596320267e20596320267d20596320267c20596320067f10596320067e10596320067c1059632004ff75992320067f7599232014fe7599232004fd7599232014fc75992320067c75992320147c7599232026be7499232006bf5499232006be5499232006bd54992320067c5499232006bc54992320063c54992320067f5399232024fe72992320267f52992320267d5299232026be4299232026bc4299232026df3299232026dd329923203cfe7199232004fd719923203cfc7199232006be4199232006bc419923200cfe7099232004fd709923200cfc7099232006be4099232006bc4099232006bf75992320063f7599232006be7599232006bd7599232006bc75992320063c7599232006bf73992322f6be7399232006bd73992322f6bc7399232006bf53992320063f53992322f6be5399232006bd53992322f6bc5399232026bf7299232026be7299232026bd7299232026bc7299232026bf52992320263f5299232026be5299232026bd52992320263d5299232026bc5299232026bf32992320269f329
  | 21 => 0xf21594420267e21594420267d21594420267c21594420067f70594420067e70594420067d70594420067c70594420067e40594420067c40594420067e30594420067c30594420267f20594420267e20594420267d20594420267c20594420067f10594420067e10594420067c10594420ee7f76950420ec7f76950420167e76950421b57d76950420167d76950420147d76950421b67c769504236d7e74950420e73e74950420ee7e64950420057d73950422467e63950421b57f72950421b76e72950421b57d72950420076d72950420056d72950421b67e62950421b73f42950421b76e42950421b73d429504223e7e619504223e7c61950421467e60950421467c6095042004ff7558c42014fe7558c420067e7558c420147e7558c42004fd7558c420067d7558c42014fc7558c420067e5458c420067c5458c42026df7358c420067f5358c420267f5258c420267d5258c42026de3258c42026dc3258c42004ff7158c4203cfe7158c4203cfc7158c42004ff7058c4200cfe7058c4200cfc7058c4221d7f7654c420067f7654c420047f7654c4221e7e7654c4221d7d7654c420067d7654c420047d7654c4221e7c7654c420057c7454c420ee7e6454c423b57f7354c420e75f7354c420467e6354c420067d6354c420467c6354c4221d7f7254c4221e7e6254c4221f3f4254c4221f6e4254c4221f3d4254c422267e6154c422267c6154c422167e6054c422167c6054c42044fd76d0c420057f75d0c420e57c75d0c422967e65d0c420067d65d0c420073e54d0c423af3c54d0c42046de63d0c42006dd63d0c42025ee72d0c42005ed72d0c42044bd76d0c420073f75d0c423af3c75d0c4228f3e65d0c4228f3d65d0c42046be63d0c4228f9e63d0c4228f9d63d0c42046bc63d0c423af3f53d0c420073d53d0c4228fae72d0c4228dbd72d0c42007ad72d0c4228fae62d0c4228f3f52d0c4228f3d52d0c42004fd7690c420e57e7590c420057d7590c422867e6590c420067d6590c42275bd7490c422f6be6490c42025ee7290c42005ed7290c42004ff7650c420057f7550c420e57c7550c4227e7e6550c420067d6550c420073e5450c423a73c5450c42025ee7250c42275bf7650c42006bf7650c42004bf7650c420073f7550c423a73c7550c422773e6550c422773d6550c420079f7350c42046be6350c42046bc6350c423a73f5350c420073d5350c42275bf7250c42277ae7250c42007ad7250c42276be6250c42277ae6250c422773f5250c422773d5250c4226e7e6510c420067d6510c422f6be6410c42025ee7210c42005ed7210c42025ef7650842006ef7650842004ef76508420076f75508423976c75508420276e65508420276d6550842025ef7450842027af745084239eee6450842027ae64508420076e5450842397ae5450842
  | 22 => 0xd420057d7590d420067f6590d422867c6590d420073e5490d423c73c5490d42006df6390d42046dc6390d42025ee7290d42005ed7290d42024be7690d422ef3e7590d422ef3d7590d420073f6590d423c73c6590d422eebf6390d420079f6390d422ef9c6390d422ef3f5390d422ef3d5390d42025be7290d422efae7290d42025ae7290d422efad7290d42025bc7290d423c73f5290d42005bd7190d42005bd7090d42024fc7650d420067f6550d4227e7c6550d42005ef7250d42025ec7250d420167f76549420ee7e76549421067d76549421057c76549420167c76549420147c76549420073f74549420057c74549420073c74549420053c74549420267f64549420057f73549420067f63549421867c63549420073e43549420257f72549421076f72549420267f62549420273e42549420273c42549420276c42549420272c42549420276c325494213e7e615494213e7c61549420276f21549421367e60549421367c60549420276f20549420057f75d09421057c75d09420067f65d09420ee7c65d0942025be74d0942026bf64d09423bf6f52d09420076d52d09420076f75d09423bf6c75d09420076f65d09423bf6c65d0942025ee74d0942026ef64d0942027af64d09420076e54d09423bf6c54d0942006ef63d09423bf6f53d09420076d53d0942007ae43d094203cfe76d85420067f65d85420067c65d85420fef661d8542004ff75d8542014fe75d8542004fd75d8542014fc75d8542024fd74d85420067e54d85420067c54d8542044fe73d8542004fd73d85420067f53d85420067d53d85420067f52d85420067d52d85420fef641d85420fef431d85420fef621d854200cfe70d8542004fd70d854200cfc70d85420fef710d85420057f75585421057c75585420067f65585420067c65585420fef4615854200cfe76d81420067f65d81420067c65d81420f6fa60d8142004ff75d8142014fe75d8142004fd75d8142014fc75d8142024fd74d81420067e54d81420067c54d8142044fe73d8142004fd73d81420067f53d81420067d53d81420067f52d81420067d52d814203cfe71d8142004fd71d814203cfc71d81420f6fa40d81420f6f830d81420f6fa20d81420f6fa10d81420057f75581421057c75581420067f65581420067c65581420f6f860581420e67f74594420067e74594420e67d74594420e67c74594420e47c74594420067f73594420047f73594420067e73594420067d73594420067c73594420267f72594420267e72594420267d72594420267c72594420267f42594420267e42594420267d42594420267c42594420267f32594420267e32594420267d32594420267c32594420067f71594420067e71594420067d71594420067c71594420067e41594420067c41594420067e31594420067c31594420267
  | 23 => 0x26bf4258642026bd4258642026f77158642116f64158642026f72158642026f42158642004ff705864200cfe705864200cfc7058642116f71058642004ff7558242014fe7558242004fd7558242014fc75582420067e54582420067c5458242004ff7358242044fc73582420067f53582420067d5358242006bf43582420267f52582420267d5258242026bf4258242026bd4258242004ff715824203cfe715824203cfc7158242026fb705824210efa4058242026fb2058242026f8205824210efa10582421057e76d95421067e76d95420147e76d95421057c74d95420057d73d95421b73e42d95421b73c42d95420067e61d95420067c61d95420067e60d95420067c60d95421b67f74d95421067e74d95421067d74d95421067c74d95420067f73d95420067e73d95420067d73d95420047d73d95420067c73d95420067f72d95421b67e72d95421067d72d95421047d72d95421b67c72d95421b67e42d95421067d42d95421b67c42d95421b67e32d95421b67c32d95420067f71d95420067e71d95420067d71d95420067c71d95420067e41d95420067c41d95420067e31d95420067c31d95421b67f21d95420067e21d95421b67c21d95420067f70d95420067e70d95420067d70d95420067c70d95420067e40d95420067c40d95420067e30d95420067c30d95421b67f20d95420067e20d95421b67c20d95420067f10d95420067e10d95420067c10d95420057e769514211e7e769514211c7e76951421057e74951421073e74951420057d73951422467c63951421057d72951421b73e429514223e7e619514223e7c61951421467e60951421467c60951421057c75d8d420067f65d8d420067c65d8d42004ff75d8d420067f75d8d42014fe75d8d42004fd75d8d42014fc75d8d420067c75d8d420147c75d8d420067e54d8d420067c54d8d420067f53d8d420067f52d8d4228ebe42d8d4228ebc42d8d4203cfe71d8d42004fd71d8d4203cfc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d421057e7598d420057d7598d420067f6598d420067c6598d42006df6398d420057f7558d421057c7558d420067f6558d420067c6558d42005f77158d420fdf47158d42005fb7058d420f5f87058d421057e7518d420057d7518d420067f6518d420067c6518d42046de6318d42006dd6318d420067f7654d420057e7654d420067e7654d420047e7654d420067d7654d420057c7654d420067c7654d420047c7654d420073f7454d420057c7454d420073c7454d420053c7454d421057f7354d421075f7354d420067f6354d420467e6354d420467c6354d420057f7254d4221f3e4254d422267e6154d422267c6154d422167e6054d422167c6054d420057f75d0d421057c75d0d420067f65d0d422967c65d0d42024fe7690d421057e759
  | 24 => 0xe7558e420147e7558e42004fd7558e420067d7558e42014fc7558e420067e5458e420067c5458e42026df7358e420067f5358e42006df5358e420065f5358e42006de5358e42006dd5358e42006dc5358e420267f5258e420267d5258e42026ec4258e42026de3258e42026dc3258e42004ff7158e4203cfe7158e4203cfc7158e42006de3158e42006dc3158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e42006df7558e42006de7558e420065e7558e42006dd7558e420065d7558e42006dc7558e42006dd7458e42006df5458e42006de5458e420065e5458e42006dd5458e42006dc5458e420065c5458e42026df7258e42026de7258e42026dc7258e42026df5258e420265f5258e42026de5258e42026dd5258e420265d5258e42026dc5258e42026df4258e42026de4258e42026dd4258e42026dc4258e42026cc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006de5158e42006dd5158e42006dc5158e42006de4158e42006dc4158e42026df2158e42026de2158e42026dd2158e42026dc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e42006de5058e42006dd5058e42006dc5058e42006de4058e42006dc4058e42026df2058e42026de2058e42026dd2058e42026dc2058e42006df1058e42006de1058e42006dc1058e4221d7f7654e420067f7654e420047f7654e4221e7e7654e4221d7d7654e420067d7654e420047d7654e4221e7c7654e420057c7454e421067d6454e423b57f7354e4211f5f7354e420467e6354e4221f5e6354e420465e6354e420067d6354e4221f5d6354e420065d6354e420467c6354e4221d7f7254e4221e7e6254e4221f3f4254e422267e6154e422267c6154e422167e6054e422167c6054e420057f75d0e4211d7c75d0e422967e65d0e420067d65d0e420073e54d0e423d73c54d0e42046de63d0e4228dbd76d0e42006bd76d0e420073f75d0e423d73c75d0e4228f3e65d0e4228f3d65d0e42046be63d0e4228f9e63d0e420469e63d0e4228f9d63d0e42046bc63d0e423d73f53d0e420073d53d0e4228dbd72d0e4228f3f52d0e4228f3d52d0e422867e6590e420067d6590e42025ee7290e42005ed7290e42025ed76d0a42006ed76d0a420076f75d0a423cf6c75d0a420276e65d0a420276d65d0a42027ae74d0a420076e54d0a423cfae54d0a420072e54d0a423cfad54d0a423cf6c54d0a42027ce63d0a42006ed63d0a42027cd63d0a42006cd63d0a423cf6f53d0a420076d53d0a42004ff7558642014fe7558642004fd7558642014fc75586420067e54586420067c5458642004ff7358642044fc73586420067f53586420067d5358642006bf43586420267f52586420267d5258642
  | 25 => 0x87420067c5458742004ff7358742044fc73587420067f53587420067d53587420067f52587420067d525874212ef4415874212ef62158742004ff705874200cfe705874200cfc70587420067f65d83420067c65d8342126fa60d834200cff76583420057f75583420ed7c75583420067f65583420067c6558342126f86058342004ff75583420067f75583420047f7558342014fe7558342004fd7558342014fc75583420067c75583420147c7558342024fc74583420067e54583420067c5458342004ff7358342044fc73583420067f53583420067d53583420067f52583420067d5258342004ff715834203cfe715834203cfc7158342126f84058342126fa205834211e7f745964211e7e74596420067d745964211e7c74596420067f73596420047f73596420067e73596420067d73596420067c73596420267f72596420267e72596420267d72596420267c72596420267f42596420267e42596420267d42596420267c42596420267f32596420267e32596420267d32596420267c32596420067f71596420067e71596420067d71596420067c71596420067e41596420067c41596420067e31596420067c31596420267f21596420267e21596420267d21596420267c21596420067f70596420067e70596420067d70596420067c70596420067e40596420067c40596420067e30596420067c30596420267f20596420267e20596420267d20596420267c20596420067f10596420067e10596420067c10596421b57d76952421067d76952421047d769524236d7e749524211f3e74952420057d73952422467e63952421b75e63952421b75d63952421b57f72952421b57d72952421b67e62952421b73f429524223e7e619524223e7c61952421467e60952421467c6095242046df7598e42046de7598e420465e7598e42046dd7598e420465d7598e42046dc7598e42046df7498e42006df5498e42006de5498e420065e5498e42006dd5498e42006dc5498e420065c5498e42026df7298e42026de7298e42026dd7298e42026dc7298e42026df5298e420265f5298e42026de5298e42026dd5298e420265d5298e42026dc5298e42026df4298e420269f4298e42026de4298e42026dd4298e420269d4298e42026dc4298e42046df7198e42046de7198e42046dd7198e42046dc7198e42006df5198e42006de5198e42006dd5198e42006dc5198e42006de4198e42006dc4198e42026df2198e42026de2198e42026dd2198e42026dc2198e42046df7098e42046de7098e42046dd7098e42046dc7098e42006df5098e42006de5098e42006dd5098e42006dc5098e42006de4098e42006dc4098e42026df2098e42026de2098e42026dd2098e42026dc2098e42006df1098e42006de1098e42006dc1098e42004ff7558e42014fe7558e420067
  | 26 => 0x1377a10581520ee7e76d97420073e74d97420057d73d97420076d72d97421b73e42d97421b73c42d97420067e61d97420067c61d97420067e60d97420067c60d97420067e74d97420063e74d97420067f73d97420067e73d97420067d73d97420047d73d97420067c73d97420067d72d97420066d72d97420067f71d97420067e71d97420067d71d97420067c71d97420067e41d97420067c41d97420067e31d97420067c31d97420067e21d97421b67c21d97420067f70d97420067e70d97420067d70d97420067c70d97420067e40d97420067c40d97420067e30d97420067c30d97420067e20d97421b67c20d97420067f10d97420067e10d97420067c10d97420167e76953420167d76953420ed7e74953420ef3e74953420057d73953422467e63953420076e72953420057d72953420076d72953420056d729534223e7e619534223e7c61953421467e60953421467c60953420ed7c75d8f420067f65d8f420067c65d8f420ed7e7598f420057d7598f420067f6598f420067c6598f42006df6398f420057f7558f420ed7c7558f420067f6558f420067c6558f42004ff7558f420067f7558f420047f7558f42014fe7558f42004fd7558f42014fc7558f420067c7558f420147c7558f420067e5458f420067c5458f420067f5358f42006de5358f42006dd5358f420067f5258f42276be4258f42276bc4258f42004ff7158f4203cfe7158f4203cfc7158f42004ff7058f4200cfe7058f4200cfc7058f420ed7e7518f420057d7518f420067f6518f420067c6518f42046de6318f42006dd6318f420067f7654f420057e7654f420067e7654f420067d7654f420057c7654f420067c7654f420047c7654f420073f7454f420057c7454f420073c7454f420053c7454f420ed7f7354f420ef5f7354f420467e6354f420075e6354f420465e6354f420067d6354f420075d6354f420065d6354f420467c6354f420057f7254f422267e6154f422267c6154f422167e6054f422167c6054f42024fd76d0f420067f65d0f422967c65d0f42025ee72d0f42005ed72d0f420167f7654b420ed7c7654b420167c7654b420147c7654b420073f7454b420ed7e7454b420057c7454b420073c7454b420053c7454b420267e6454b420057f7354b421867e6354b420067d6354b420257f7254b420ef6f7254b420267d6254b420273e4254b420276e4254b420272e4254b420273c4254b420276e3254b4213e7e6154b4213e7c6154b421367e6054b421367c6054b420067f65d87420067c65d874212ef661d874203cff76587420057f75587420ed7c75587420067f65587420067c655874212ef46158742004ff75587420067f75587420047f7558742014fe7558742004fd7558742014fc75587420067c75587420147c7558742024fc74587420067e545
  | 27 => 0xc70d8d520067e40d8d520067c40d8d520067e30d8d521867c30d8d523b67f20d8d520067e20d8d523b67c20d8d520067f10d8d520067e10d8d520067c10d8d520057e7498d521873e7498d520053e7498d520057d7498d521873d7498d520053d7498d520067e6498d520067c6498d521857e7398d521867f6398d520075f6398d520065f6398d520b57d7298d521876d7298d520b56d7298d523f67f6298d523076f6298d5213d7e7198d520057d7198d5213d7c7198d521357e7098d520057d7098d521357c7098d520057f7458d520057c7458d520067f6458d520067e6458d520067d6458d520067c6458d520075f6358d521867e6358d523057f7258d520076f7258d523056f7258d520b67f6258d520b76f6258d520057f7158d5213d7e7158d5213d7c7158d520067e6158d520067c6158d520057f7058d521357e7058d521357c7058d520067e6058d520067c6058d520cd7e7618d520057e7418d520057d7418d520067e6418d520067c6418d521867f6318d521875e6318d521867d6318d520075d6318d523f67f6218d520a76f6218d5213d7e7118d520057d7118d5213d7c7118d521357e7018d520057d7018d521357c7018d5213d7e76d85520057e74d85520057d74d85520067e64d85520067c64d85521857e73d85520057d73d85520067f63d85520067d63d85520257e72d85520157d72d85522d67f62d85522d76f62d855213e7e61d855213f7661d855213e7661d855213e7c61d855213f7621d85521357e70d85520057d70d85521357c70d85520057f74585520073f74585520053f74585520057c74585520073c74585520053c74585520067e64585520067c64585520057f73585521857c73585520067f63585520067d63585523ed7f72585520076f72585523ed6f72585523e67f62585523e76f625855213d7f715855200777615855213e7e615855213e7c615855213f7461585520057f70585521357e70585521357c705855213f7710585521357e76d81520057e74d81520057d74d81520067e64d81520067c64d81521857e73d81520057d73d81520067f63d81520067d63d81520257e72d81520157d72d81520567f62d81520576f62d815213d7e71d81520057d71d815213d7c71d81520067f61d81520067d61d81521367e60d81521377a60d81521367a60d81521367c60d81521377a20d81520057f74581520073f74581520053f74581520057c74581520073c74581520053c74581520067e64581520067c64581520057f73581521857c73581520067f63581520067d63581523dd7f72581520076f72581523dd6f72581520367f62581520376f62581520057f715815213d7e715815213d7c71581520067f61581520067d61581521357f70581520077b60581521367e60581521367c6058152137786058152
  | 28 => 0x82541b57c72582540067f62582540067d62582540057f715825423d7e715825423d7c71582540067f61582540067d61582540077b60582541467e60582541467c60582541477860582541467860582541477840582541857e73d91520057d73d915211e7f62d915211f6f62d915213d7e71d91520057d71d915213d7c71d91520073e41d91520073c41d91521357e70d91520057d70d91521357c70d91520073e40d91520073c40d91520e57e74991520067f64991520073f64991520063f64991521857e73991520057d73991521057d72991520076d72991521056d72991520ee7f62991520ef6f629915213d7e71991520057d719915213d7c71991520067e61991520067c61991521357e70991520057d70991521357c70991520067e60991520067c60991520073f64591520067e64591520057f73591521857c73591520ed7f72591520076f72591520ed6f72591521067f62591521076f62591520057f715915213d7e715915213d7c71591520057f70591521357e70591521357c705915211d7e76191520067f64191520073e64191520067d64191520073d64191521857e73191520057d73191520e67f62191520e76f621915213d7e71191520057d711915213d7c71191520067e61191520067c61191520073e41191520073c41191521357e70191520057d70191521357c70191520067e60191520067c60191520073e40191520073c40191520067f73191520067e73191520067d73191520047d73191520067c73191520e67f72191520e67d721915236e7e421915236e7c421915236e7e321915236e7c32191520067f71191520067e71191520067d71191520067c71191520067e41191520063e41191520067c41191520063c41191520067e31191520067c311915236e7f21191520067e211915236e7c21191520067f70191520067e70191520067d70191520067c70191520067e40191520063e40191520067c40191520063c40191520067e30191520067c301915236e7f20191520067e201915236e7c20191520067f10191520067e10191520067c10191520057e74d8d520057d74d8d520067f64d8d520067e64d8d520067d64d8d520067c64d8d520ce7f62d8d520cf6f62d8d5213d7e71d8d520057d71d8d5213d7c71d8d520067e61d8d520067c61d8d521357e70d8d520057d70d8d521357c70d8d520067e60d8d520067c60d8d520067f74d8d520067e74d8d520047e74d8d520067d74d8d520067c74d8d520ce7f72d8d520ce7d72d8d523b67e42d8d523b67c42d8d523b67e32d8d523b67c32d8d520067f71d8d520067e71d8d520067d71d8d520067c71d8d520067e41d8d520067c41d8d520067e31d8d521867c31d8d523b67f21d8d520067e21d8d523b67c21d8d520067f70d8d520067e70d8d520067d70d8d520067
  | 29 => 0x4000800c00200200180300000070020004042001000006000000f000000c01a000000000c014000002001401200000500000060000040048004000004802000600900000000720020050054016001002001802000000500240080010008010002004001802800a00000c802400c00200500380040190098000000005004000000000000000100000000000008012004002002402a00c000800c00e004000809400c0000000000004004000003400a004007801001a02a001003000a000000800400000000600080000050018000006004001000400c010009000400200200080000180010e57e74d8a540073e74d8a540e53e74d8a540ee7e64d8a540ef3e64d8a542457e73d8a540057d73d8a540067f63d8a5423d7e71d8a540057d71d8a5423d7c71d8a540067e61d8a540067c61d8a541457e70d8a540057d70d8a541457c70d8a540067e60d8a540067c60d8a541057d7698a5436e7e6498a5411f3e6498a542457e7398a540057d7398a540067f6398a541b67f6298a540076f6298a5423d7e7198a540057d7198a5423d7c7198a541457e7098a540057d7098a541457c7098a541067e6458a541073e6458a540057f7358a542457c7358a540067f6358a540067e6358a540067d6358a540076f6258a541b67e6258a540057f7158a5423d7e7158a5423d7c7158a540067e6158a540067c6158a540057f7058a541457e7058a541457c7058a540067e6058a540067c6058a541067e7458a541067c7458a540067f7358a540047f7358a540067e7358a540067d7358a540067c7358a540067f7158a540067e7158a540067d7158a540067c7158a540067e4158a540067c4158a540067e3158a540067c3158a540067e2158a541b67c2158a540067f7058a540067e7058a540067d7058a540067c7058a540067e4058a540067c4058a540067e3058a540067c3058a540067e2058a541b67c2058a540067f1058a540067e1058a540067c1058a540ed7e7418a541b73e7418a540ed3e7418a5436e7e6418a540e73e6418a542457e7318a540057d7318a540067f6318a540067d6318a541b57e7218a541b67f6218a541b76e6218a541b67d6218a540076d6218a540066d6218a5423d7e7118a540057d7118a5423d7c7118a541457e7018a540057d7018a541457c7018a543fd7e74d82540073e74d82543fd3e74d82540967e64d82540973e64d82542457e73d82540057d73d82540067f63d82540067d63d82541b57e72d82540057d72d82540067f62d82540067d62d825423d7e71d82540057d71d825423d7c71d82540067f61d82541457d70d82541467e60d82541477a60d82541467c60d82541477a10d82541457f76582540157c74582540867e64582540873e64582540057f73582542457c73582540067f63582540067d63582540057f725
  | 30 => 0x800e00c0070004014002000001800000b000001400600b00100140520050000010014000003805c00002d0060004006001002800000a00000200380040150010000004012000800001a000009804c000001005800400c007001804000e00000180880040020020018006001000800001401a0000000016004007800002200300100880140000000014004000000000000e00a0020008004000001003400000c01400040000040010020018011002801004e000002804c012005000802800401a003003400c001000803001a00800f800001c004000000c00000600000100000050000004006001001000400600100380040040020000000020008003001800200100000040040000000014000000002000403a001000801400a0070090044004003005802c0280000000074000001000001c00200a00a803400a0010008000004029001000401000000000000020040008000000000000001c008000000807800800000600340020000030000010001000000400200000180080040130000008048007000800400200e00800040040020098000002004018000000000a00680000220040018000008000000802801e001001800c00e004000000000a009002000000c000014004c004000000000c00800600c800000000101b802c0020020008004054006000002000000601780000040010000004014014001002404200c001000c012001000808c01e0020000044006000002800000400000000040140060008000000005001001800200000100000040000010014014004002002c0140000018000000002000804402c0000018008016007010800400000a0040070006000000002c004000000001400600000c001400200000d00000020060008000004002003800c00c0000010010002013002000c018001000000c000000001801001800b000800401400c00280640000050000004014000012002800a0040020010008000002002c028000001802402c004002800800e001000001400000000080080040000008004006009006000400a00d000801800600000c800000e029007000000400e001000000400c00000000000020010004000004007001000000c0010010000000001000000200200400280000050050000000004002000400600000e000c01e000001000400001400880440000060038008028001003801801e00100b000000000700100000000040008000008000000001401800100280000180000008000008003000002000400700b80080040000038010000018001003401c009001009800000100200080000030080000002000000800001600000000040060010000008004000000802403200000f000000400100500000040030000038004000000000000a001007802c00a001000000000a00000c800801400600d000002200
  | 31 => 0x2801c034001000802400e0000010014006001000804400400f000800800c0020000010002001003005800400000100280000080000014004000000800c014000000000001a00600500000080000028008062003001000401a0010018008010017002801000a00400a8000004003001000002200d005004c002008003001c01000700000300020000008000000008000801400e0010010000000000002800400000000580040140060000068000000001801000c0080260014016015004807400401d0038070008004002000000600600000140020070028000006005000000401400d001000000e00c00080000000010000024000000008800000c0110000014000000001000800a00300c800c05000a000000c00a017001801000a00200a000c0060060030004006001009000800000000d806400000d0008008004007004000c00203c0008000004001000005401600d007803c010002000000403600d01a800c000006025802c00000c0030030000005002805000c008001003800600100080080040000030038004008006000000a0070060008000002003003400600000000000000000098000004001000000c000000000802c00c00c001801c00200c000000806e002001000c030001000002c00c0020020010004004002800000e008001002c0000020050000004003004800c00000800280000140000010000000000001001403400301e802000600400c00a000600b0070000012000001000000601e0008008008011000802000001900c001800a0050088000022004003002402c0050010040002018000000800800500e800003e001000000800400100080000020010080008022003003000401c00200d8000002000011001801e0000090020008007003808401a000000001c0180110038014002007003800c024004001800400c005000000000000c00300480020010030000004001005000c002004005000400200000100140080030018034004001002804c0060000030028008000000002800800d0078000004003000800c0080010038000000005000802000c0010028004026001001000402a01c000000000402300000240640010058000012010000001001800c00000000020110030014008002002000c0000030000068000000000002000801200200040160070000004002000000801400400200600000120050008010000017001001000800100080100220000018000016007000001800a001004800401c000001001801e01e001800000400000000000040120018084004001004000001000f007801800600d0000004014004000000000e009001006c008000003000801200100000300000030000018002001003000000200400080000020010038070000003001001c0000030000000018001000000000000300a00
  | 32 => 0x8367038e2ee8acf0000000000000000000001ed0c2b1364ac7001400000006bb3e9466f4bc41802cd81a11f44206a1ac989011924c1d9406935384c2000051f0000dcc377cac400003a40000c0b80001e308c484e48001e80000b55b0b4896a164a812b90f37c850ae818d8e4d07c66972830d961e2a31e0000b8b4e1c5540a281e64d50000369800016d2ca0b7b416f9a180000048000002004001005001800600180100000000010000002000005000000e029003000c004006001800c00c00c00c0008020001002000000c00a000000c00200c001001c0000030000010002002007801400200000500000020080000000002001000801c02c0030048008002006004000003e000000000c0020000060018010002002000000e00a0020000010000005800000800b000001c0180000000054002000004802802000100980180000190110054018006000000c0020020010014012001003804400000100a802000400c000002c00201a001802400a00c000005c04400000700240060010110000008000002000000800e000004000000900800000020040000000000002000000000c0020000010004002008802802200800180180040070008038010001000800c0000020030004082001000000c00200000480080040000098008020004002001000200400100440000020008000012001000800800e0170010008002000005000401200a00e80100060120008018000009002800c0040040008004000004000800c000002004809800a002000001000800b00600140080000010004008006006000c014018005800400c006000003400000000480080000000058000010012002801000000000600280020080018000014003002000c00a005000006800203c0030020016012000006c002005004000000000700480040120000000000000000003001400a00c0030000000003001000c00200000080780000090078000006005003800001e000002000c000004003800800000600080080060010000000010002002804801a001004001c0000010000024000001001800800000b0060010004001007803c00600400100040020050000024000003002000000000700000040080000010000006000002800400a006001000400000000700000000050030004000000002802401000000080740200050038030002007001802400000000780280000160020024002001006000000000d0008008000000000003c0000050028028006002007005000400000080940020380028014010008001801800600f000000001a00000280000060050000000004002000803c010008009000400800400180180060060000000012015001006c00000200280080100090040050008000001000000e0130018004000008006000000801f002000000200000100100040
  | 33 => 0x9000034940002ea87bb0f3415a27d84fb097494a2de00002ce045920410d20000e073e4400032907d800000002a34be1adfd22d170483c38f4b7021c8e424934c249a945f21fa40002c4cb9a4238eb50001112414c29a196f2a009448e20000000000000042a80003af80000db000000009910000000408600000010ec1c288c91e1816980000000000000000000024900000610df60230b8db5b45b4000066831b0000000000038c290e40e0c1700000004c6025f0d805722d289ed15f49a10000e160001258464ca75000014dafc41efc34c38b4b79340348ceba4750f9411e8d560e8099c00012693e6cef1201c2be016138089c43b94dec3781b54b3701ac8f448c115213a48a213c81cf19e0108950133745a862111e0de91d650b918a04e54410e6c35e866a0000db300000000dcc83421d083b420136d271010c2af880632a0a900d280d4065c48319004862ddc0002756b2336540002bf00000000bc72cf2976c59cd6e1948c3f25b09b70f3aa730f0c3f92f280628894a9a853a25e01f4ff04528b28463d1f63eb42b50000bd337e000034689858000a7e02e33bf30903ca1630409c1309d94bdc19522441b12ea200000948b127453b5a8ac948335020b49d47bc3fb058a0b5487aba6c7df471cf182c9c41e0000eb14f211f202b00004e983f522160004b6c37d2c28ab7106800024f93531e59206000000021700000000000000043a800000007346a23e045500000a1580000000c80b7aab00ab4000110b0cb846a3f30000000095c0000b71000000000000001a6d12b0000000000000045bc63c127d0f12b084452f7a674355c728272c64d17224a44094edb03bd0780e9ce8d1508a9884e92673c3c16590080004dc40004d9c37904a0ccd18d410f34b03501b48fd22c345b5055c0449cfcb8f16246800001025a7c8c5d4c9c00006981b90000eed308a3040244548122c42319689592c1c0000eb470f00000000000c8280000000000e2f80005093d9e4cb0f989441d4030b3b5d0211570b92000000004ccc260268000000000000000003d340000000511356000000003130b748fe4a0000036742e832e000000004da0001164004850500000aa0a18e5b2fa0e5e00cc2ed2a840004dd0a95a568dff2ef41f9bee91e846a49c31b5c98634811ab0904d3d4018f5a9e5c1838826c3244d462f41e4c2ca4480001634c740000643000085232892fc1d8928513a80891de4956011ccc4a6e00003bbc00044c51192eac04e068efb5197043e460ae2b82843fc4a980002c0f06039a800003680002f266e14ba8f1d1774ec44894b1f00012d1490000044d00000000fed2b303950398b811c588e500000000688ce8138c3182af419a378ce61800251b3da07b9be24000242441400008642e18edd0000000300842000000002e7660600000b
  | 34 => 0x2d127400000000000000cf61a3400000000000000de00a6c7740d240000e785701ba8773262c000000025900009e54b280000629263496c000000120100005d409f817d208c9be0e346301c4089e1264a5b19e4de63f5c843441c7a93f880000034bcb000000001040000000c3b2c2e0000000abf44e020d0718021013117c00006412e9f13e0000b26038c050000000000000c54aa00000000d3a06190bf337800000000001740be3800000008d93663a80c9d825ad30000000000001ce8000ee03f40b2b38445b984b401f47109fabb70000072c00004e054e00001a9383000047a902845f832b31bc002417480f09110542168a3b107c1123d94bc20cdc0722a44f19210892b14292e01c80ade1024f344f646562b240002db0a080c302cfa250eb8000000000001bd27e00004b502fd000028d48f45ad91b8aa0ae34de83f008e82cb83afc37800006040ba80009a22a7a6380820206429d13617f40000fc2581256c00032ec2078000000387600000000004742ad7bb44000000000000000000254e16be980670000d2800013103bf00002668e18a3ac000054000030c00000000000000000038800001330f0384340000000000000000000004490000000000000000000002bcd0ab0674fc846f0000000033d45a06f700003102d70583ac2cd91392cc8b935c7bfa5f0cc62ed810423f50fc12787e34768d1840a8fb4193eaa189007cfab6ab2a4c88000000000016a8284092400013e0b70a740000185ca97cf04bdb0dbd2e3462c0000000efb0000bf3000000038f068700802eb807a7f520900002fad356a69ccd03dc0000051cc353aa81d18000fc51074354aedc4d117a800000002f30000f404c7852b1370b7d282814d0000e463f4c21f0379345248cfac4f240000000ef601b12f60bc027080ee0cf4524f783cec0002698000436c0001e884a9307a41b0000b650000093cb6864415340000000f7518f8d4325740004f351d2391c09f00011f30000c9280000c9800000000007b600000000e2400028c8af583acb08800041000004d631200001804000000015b0dfc0000ea0a5a43f83530000e60316000004f40003272c451cd82fb35a926d41991a012b92032b140000000a328ed400033b101b3f983943c7c88e1254c13000112200a40002f8000012ac0001d74b58a118172877c000388c7058000f1209a41424d44000010000007b8eeb00003f42c5c5c705c000022e8aad0c3c1f412d525736140002e1486c0000000021099b19dc29009aca16c2f4bad02a44db11f4a7a11101832824b158c388a532b217922c007e00000002b95110084a75102e848d36fc57a00000001a2800028d294b43c842d359c22100010830000000309e0be8000aa22de539800000001dd400000000000000d371c112421d8d197800000000002632a
  | 35 => 0x1ec227529d3760cbd90185553a1cb1d00012f34498b61bc2480907d628b42dc00023ecf430000a3c0cb400000007aa395c32f4f60ae000aca8e2b180003ed8f8c076c1d28322000295cbdc8004f8202ec2f8bb7813b83c473b465443b9fe8adca91a6c78f6cc650cfd2a9428861900007a63de4000278d2e63cb820c10161c805547b500003e10000b3c2a5040380002dda1306509a992933d3cdd41da4db70000a4017ed28c0c440004c58000000000000000002bba6910000000000000000000000000000000000000007d446e000038eaadb3b54db5070d2cb026abafc43902b2f9d1942be83f0385400002a00000000d701940000345c0003a38ffc00005e800002ab42b000015600004b185013b50e3399fd33832049880000134800000018682b320505bb0000ea400005230000f6b47e04bb1c50cb9000092a320cbcd2d0096880000002d8d05b00000000000000153c6d83082121281848f31b60004e2085733b45de4ee000029f48bd254000000000000000bae28c01c780001fa000059a00000000000000003c00013bc6b644bd105000039a4abcf311d787782b1600030ae8b82158a16458ca8b22ec00038b200005b2ab20cc053e3da934e118d21900c400007cea0e00000001d6c000000000030351b32fb4f054e1400049fc70b1b1461600007ed000026143d4000000041548bcdda0c48b9c4d0530147347152a253023708c9638e6f8e0000000000038a0000b1c15940000000000408ec932de80000000d3b0000aa700005db013c4a53e284b42be48042914b7f80004bc47fc1824564aebab0d04080000000000b2019d32d20d183b61984a5d9fec019824c7ca2f98f7736b4000133c00008487a74f4090831050b64904adda23eb7bc78112549a028ac754caf9f230d0347b0ad04bd1ee33e8bb4c65c3d837541fc417885f0000a5639162702ea664b234414e4e3098c47789c11ddca1238a10a807e26d3a08835f2978e58242625605cc5ca04b800031c800037b0f572c06d792aa4fa42840bd031c419b80009d609f42d2a5dd2bb0000e7d2f8800000000000816753288a4fa33c071f3ea4c6e3680a072d2d04a31384211528165000000000001d11654b0ccb5cbf8af76186bf740000b386fb21bd10f0000cc01c4c0000f9c8d001860003b8d2720000a118a4400010700000000f960450000277400000000000b80000000000003e8930000000040a51f027140000000000000014400000004bb40000000ce137e242b394600008ec00019b4db61c78bdd050268b0000000279c216bfc4cfd19f84c13dccbb809e81d800004a106c06b71e1cc363d30c23c02800017c400037f8b031a082890149226075914c2d98deb24987a80d708e726a000028d825700000000000a2600000002a28000000043806581c94d64000271c8
  | 36 => 0x6e2c162bf13d86270b841da32c8cdd2ec05cd0000c4b40d6000494ce91000126200008840000ca5ca340004c48e36000071b3aa0e260788f6026ecaee4afca543124d77000047000000000000ba200000003cfcd021e103e9042c1d5052a8a146352922fec49c1f94f670ae0c2c0000b7480000001c5c0100000c20386455700010209d7c00002400002a6c3be00000000d4eee100000000c040001014bb9020ca7c0000000000084740e6865000021e07d800000000001b4236e3a153c31288dfc1c0a1e51ab514d14d0a5d17801c70eac0000000b8c80000001650df50870ec649a8c9a0b46feb35c4000238c0000000dae000000049140000000f660000f2300010cc233c975284533b31cc00000011832c620003f6caf5306c000029937c183800000003e196700a9800063d2b7c5ef0fe06ba4704000224886d00000004dc87d641711b043586471e6400000000000000e8b45183170b0ac25b3c40000000855000130c00001c23a7c00015ece5d2b62b601a480004a8822907e489b118400025a000000004420598000000000000007063cf41b180007be105c55147e8e2c0000b04c7ac000251831a0b028973510fd42100000198e000298cba000000002c4eb2183b0bcc48a000009e09e4000138f21e000036a8a28068a000377499e4be0f500000000174432400dc3ff11b002a00005f0221474120c0f352ab8ba5195cb450000ab1000122911a465402b8fa007ccee700007711cf800017e4ee94290b903dc4f69b568bf700002820d745433d085782e209e92bb482e0f74000056000038f800000000001d2000021050670001141312800013d0da414a90443868eb64bf85560ad8000000132a42300001c60000000018496b8e1e161307b03ef32c2584b974a68caa0ec90cd0968b63a45095509bc8b52054e6630dad6304189344520f3e39e83b735a1022979417c1150f690ea937742d027910d04414068eca339400003c034e1e2cae648e134ecbe883207b69111d841a803ea8f5193ce5606e0c40427c0002f94000470c00000011dc000072b2d1ae5329a87371fdd34c407f1874b080000000c5e00004e200000001e712b400000003e5c0004bacb1a8770000440091b14784580000000054c6f54d6c5ff0580d1b4d9400027fa2e63720414a04c1f835f044018293b546706fda81ecea3fe439f34ac00001820dd8000ff62d4c00000004e80000d5b3c509a3236c9b132807880e580001a2a3fe000020f2994ba8000002d40540003c1d1ec40f00000000f8f1598c5f16f02f50000000000000041d00c3192842e80000000000a00000107c10b87221a7c0003fa456f000000005660000000fc13c2ce7c4a205e3af7c0002f0c9b34668c6b3c11039170c18d496535c42f0f632964f1e462855b00011442218b0a94908633930c0e0
  | 37 => 0x460ecb080002c4c050db829be000456c00000000920000a140000f0c409b1330000000000050f3d440002094e3680000000000c002af0000000068333c80000000fcd094320c27d52b84ac82871ee44334a3cecf10600001e30c2ec29400043ed00533e53af2bf800032641593e612c73a50cee05ae04900000001bc8000396ab343bf501936d0cfe331ccc24a5030a27b03a2409cc2739d80064de48d637008172c54d872ea50b14ee87c4a2d82e216da1c11be4a2c4e8026ec80853607f82a902f8285c5b4ac12000e832928e5c2c102a029fa5e496004b917dc11707c4172005108609a800000005a200011a13a0112e4ec916c1e351c838ed30607c05c44c8c74f0000c8c4f0a1921d1d2482fc6f583cdcc1e12389f94c24605ac5f17144a80000f503c6000028f0000a762754c500cd4d804d900000000a722b23172026c782047cbc42180b53b64c6a41f8f1ef4e790c300105d60f400003bd41a40280e242e309e023bc063161d36238ee8c4479cfe8465a4730000000000088186d869e00012f23b9000001a0341238525a246840412fc1d4c3aca99ba20000164400000002dfc48d3500b5ed9934c8cd2000048549bc00000000002b501ed46087df861517f2a085974234f5d063062a24800974024056cdbc0003c202321a300002fd09c90000b7e8000fee01500000f3cc781268c5b30bc6030464bc8800000000006a93e400000000d2133604f380005cf3a1080c285400000012c42d9cdcb35ec81f29ac0000000df7000000028f4e3503d8e9805c33354ecd1611be705607ecc19497427438281710d353a744a05c1a02892d2d0831f35487e700000000000bac1874ca606d00003f847ab00012ff4d48aca00006cb197c000000000004606512b403d337652600000000283cb7b00010f4046ca5800000004acc5254f3c245386059224f400047841e9941e0db48492b7080ccce141c00042e8c03161416c05b60004d190b508104b20000d3438fa0000000000184469d0f58e740b8600014cc0004f388580000ff81af0ae100011dd2e0851032081323df067d1bd0e2e00009ce1ce91b136ec96a0001287461423336a4000000000004b109a3d70614253d2e241605ce11c4828301115612280b1b53c0a71b0cc3900011063bfd27b101c000000000004d865ac638000422800001a8a434af837b2ae13c62b35236398485d0234c520f443d90c080004cf400033fc8c600000ca0136c37868704835d898f2e580004d80fde2654bbf000116e11182fa3ee4000000000046b037a22c8d2d3ac800000000000000fa2be0c0000664000000000000000001334d110b5800018542e5088c5ceb9e511b14e0dab43011af03040fb4c5d06a17f024b00012e912048c7478ca0238a8a8c03ce99743fcb050d6cc8d411c2de323c3221ad50d532d4
  | 38 => 0xc85b10a010717910820000f54049c2fe01dc6da2b1e11c08bcf0a0bd10c538c4bc94828ec7358815d2380790383afea25cc00000007fc2124b0e9f34d60a67c0000000a3a00005a6109c7af36613d11b7c7c602fe9c82a8cb2430e8cbe1355305384a000000136ccc3856d291109b26acdb2491c0ed0ed0a6d066c0f5260d09e386d3243ba0a9d31e931400000003414d4d12cc0002129355003835511c854515c40003dc8016370cd47110ccc8391a0002f0000040e8cdb3454000139ae5f1b1ccd70ca85cfa5b313f3add0c22a7e9544cc452603d01f7979cf213fbc07a2280d662e02ece009c88d40dc046c2511e63f0922a37781f21bb8e148c84c7545a4bd4313cc152ae4cfc4a60b84a930f9c1eb05e3000000000f0d4c3b2c9353168a29045a96b40784c9000052c379ced61870b0146c85e1b014e2d8c002a724144d801d0bd90dd919c80012f41b9d115044a00000009e64d2078016ca000149a00000006fc3c900000000000075621a90c01a50c1800000600002d880004a2c502398800008626533f9d30d00001980dc400000002ba000000015cc63f0000f15000002f41b8139000137f0c7047c428c25c80011090000bbc000022e03a8da31f9907e1ef48ea16a0e652544334000000003fa124b0a4c7c3c40ba13c5934f43cc54780000000000aaf241935d44c0ebb1ae713c0000b4945e93a12d682d00000f28178800008d01ee8000c788000000000000039b80004da838520093d700009211aa91583594af19e4c9cf484440a0000ce40000efe000020a80008ca2ad8c4c1facd4a3a848cd07380f228d4ac6c0d111e46900004e387f3457860d308730a00009644384ccbc284ae722727899c007a03eace270b4c0a895ac1b0ab70000004cb6800000001da82df15747261db83a940992a502f106c4ea06a73740f473fcc273275d3b003b83a54cad3b11bfe42fa1fc13b05141481f000cb80006393020949839d2d926fc2802bd0134233f0bb2bc000032da2073dc678baebc10128dc071b42409d44851894ad86e21d9cad9c868bda80002f621f098e06c8d75000c7070000c372868829262800000000001b0800032f232c000097f1b513ac0194aef29200002aa884d3be048800000000d6494e05bcb591730e441420559497c00000000002f9022c1ffd06932444030000ef40ec40622a80a1f4e881d7087435402ac7b330441203a300151eb89fc0000000000000012e804b499043700000000a7014a2eda2cc21de00012a800026050960000f3600004252cd451a00000002a1cade840200000000004c8089a080400049cd39f4ed81a00efc04811410af2cfc000254936c1f3128e00000001bcc00036bc19e800000021a44ee0af53c41a688c500005b73e54ad9475c67b0000973a26000000000c9499800019b8a0d91f8000
  | 39 => 0x23f06980372000161067a0000169000078916ac0001090c530000b459952cfb1e7c8ee05a90712748ae94c685df4164d8f2f7e03e2e900001c0854c8bc4dcf27080001bf81ca0000e9c06ea00013fc45500e932d34751c21ba088b8000cf52c6400000008ce2fd491f13a2c89000000000000000e7400000010354a400000000fda157c09d9b940002212000000126546d8e4139b4cc51af8ad7145c0000000cdc38dc400bdec00017a40000988000000018b000045b00004c030e0000008896e1144000323a66300013430c98a6442cc51c18b8079c84c0000da51ca00000001974000000000006442201195383015ca601cc830503f6eae00007b8a3a400000000000000be90b2043110863ec0cf715f17acbc813bb10d47f40003605140160c8900000f1a000001c264c12b23d800000001a700000003be40c837181313df4a5f11dc00045d0adf854900446b91d108086cd00000001df80000000d5f019872519cc8391e8c533b254bfc017c153c5cc25300daae20f684120578faf3cc80000000aef800000046a0f7e1d1400000000003ce800005dc000067116600002f8307ebd8230846b0ab84eb000115100000003f10d49094a00000010dd2da800000000002df800f89b09ad138100f2c413d60a992dd048c0df27fd339222136903e44f74c549a40f104ce166490420e8d074f3036b079e0001bc48ad0001378391ecc7800000000008df3db4000379447400007ba18b00f9cbbcf2d160815f4f2851600010a900000000000d2900001780000000000000032182e9000000016fc97141accb611a000000000f741c0e4c80f400031191ce0d682b4ae7c9182e249420000dbc0000ea21f683080000ef01c0c0001b44e4e0334e121d8138600000003a40ca100000c04794fa728f80003c386cc2c1aebf1b98c84065068f0cc44df00009b446442f24daca793f8ce2e8b6d09528e4a474d7ce963cd600024b925140fc6b2488c0000000085b94209e000000039dd3d3214404307a523f1e04cb00bdc5dc0e4c66b388a00016ea00008992894984188bee0d36014c44f0980c642d8a00011d400035204e6000000000000002fde7c7cc7424849f0ad52c607c34e2403b40f90c70000f3b8000f1b0000ea3000000000000002e1c0000b248731f880004af02ff00012e80a14b9d000105a38e09030000307000113947c43d538b440e88445c00000caf19800003aa4ba630b60000b1eac282292a421a07a50e10c4300013074ab000007ca9ac00000001224e781f720001be000046a84b70000000432400000005322e462aa34700710000b500000e49800000000000000000f9d374c00012d8388000126c000000000000001b0400033ea208ab440003f7c069b60d21626c8a494640ae30000b481edef5920fca6c0850f26103477f243070c251
  | 40 => 0x648111dbcce2229e0004240fe40be42e30490a7703880cc00000000fcce97085e40b246498700011bd3b4ca2103902770ce139d29166d31e782d7176539c271816d482c7544328000000033cbab4dce00de5191ac4b112892035303133f34c4a882bc33843f2539711d87c9125817e439cb6b182014c915cec014b80000000000000000000008d400001d9307c33e2dbd023473d05500007cba7e8a522aac8aa104d198a03408802cc00021ec6fa0e181ea87ef22b1e604ad00010ee4ae4bfaa99d010207400029fc0000000520000116b3f44d240000f26a72800000000003d200000000000365c0ab8000b8000006a034346551b3800048840000d585fa30f89f100002208000be3000125617ae7c443d200043b4abb2f1e0442c6c000000013ec7b4000000000000000700346067ab0e00023985da0f90f38cab800000000002834a1e0000a010000ddc2320693492d2fb2252cd621f8ef2433cc35a88039b07f2c140174fa34ea822d06b8a82a7a00b6034c1001860a800000bf90bb00004c4cfd8139d03b4df40003c945152810000230c00030044af43c047f0000e061580dfb000000006e68d342c8b02bfc8000000007f49d00004c6c00000000004a54e8908972713b983f4a87400000007c510c88b7c0c8e920d451d936c0f86000133a30580003274c0f8000b511e228380000368000045e4ca0000362c7d2000020000003431460e66a5791bb0da8cc90d00ec8084cad60000971b6191d3006854116b526e4c98000000000025150a62a708c0390ce3c80000001efcbce0000000117482b33cc4291d345c815f04c54874f851cf49490fa053b170e000126ca460000a703248000389ee454e510850d10bd50000000000000039542ee000104e3c348dc00004a300000004b151572edec3400000003e68889af140000000000103cee52a988200a8cb54261a37040d8c9b00b934d3e6461000200000000645000134938880000000000000000000001490000e722770ab01f3c0000b48c9ec50cad24ccc00025047db000000000000000000ffa00000001f20e7b15e50e90000000309ad8407c280124409221aa08ae4134711049902c2a650070c0c000362098498ecf491bd800046120000ecb12d10e87e6896c29e2e3a9070000f5f16d8086400c00043684ec2d78210aef803441fc3cb4d84cab439472f3a6871d11991544bc0e1748b93903ce00004ab469409492c11bac14109b497820dc19000007720000000383600048902a114dc00000010f700000001b18cf400011160000992000074c1708d7d4cd8a8cc88040802080003d100004540f688a38de400010c412e00000000f1c00001750000d35000038c40300b52d5ef004a0cb210d310180812bd100008b71ae20ad00000000000d7400012a10000000000069c2658bd741d800
  | 41 => 0x8b29700001fe088f4e486134948d40073f21822b00002ce40f33db021da69445f134ef3323fcd2e0ecc5634888d0b16e800000000000ab00001ac0f7f4e94e5215d8000000076803a121b000088214c400000001f5000138b28be41610d49252dc8c420000e82174e972837433c3f58e9e276c0b400000000000f8417572b12cc910c00000000ff2d6f24fc612290400000012170001304073000c07004dd1410f3c0adc00045d46ca2d527bc88288b400006a1402ce291e2928200009cc006cb022e1062045dc87da34ecb70c5062b8000af3a60a0d00000000000109c492807c0f8215416bea6800000003d580d7c3e00004d10cac1a645aba9222cb4c9481200000001b900001b3a000000081c0ee01b2a2986653544708000117049f80380000189ac240000000f9f00000000000000174600047dcbfd000033a49dc0002cb44a736f8000074f008330cab500000004ed00768000ea5000018588e08b3000010695dc0002ffc25c259acbc4a7909800000000e488da0000000183000000013bc00000001b6c000000000038500001cb000035086ed0a0c3e3455436100000000f48000000000022587ea3640dd700000003f540000000c904d68a3f000000000000002b4cc310a204c404203bd344053939d47a416940004e6d0c82cc2ad847ec7b1067d0653364dd226d88714740c28cb38b9e413c5d48e641f6bab0795212c1ff09ecfae3d04d6913ae00027f919d3d54347333c2b902649cd3564ca32d744d68000c5412120000000000000090a457524606ec00003830ae4048bc11a3ebea3bb0ce000001e43800f111db068144902763250eaf4e049704758e1000012dc4070a174c449da0bf0000386674a48d0b763e3472941e90f928cc0003d4808e0001117018527601bc3651d2400039906e9477c72146520003ac00000000a1b0000ea600000002e64dc417a6bf6a9389ae033a5be05c62461fd03982d0d2c0422d12009b81102cf41d6a020af8036528146480001ca8f6f1e840000000c5c000000031641742b753ad2e2aa9a3b7c96f25f41c524c80000000c2a07ac4524cc0a1c85cec89b744000294c000000000000011be07ae000398c1b8b02c000000000011340000fc4ec938460001b1062d44710e82474c83b63074635542274eb83dc3d680d20df822a1c68f6e1bf527d00000004080cada471391095506f0a5097b37f46c80000cb406f0606a2e509703fe3e52c5a8bc000000000000000000f92252a54b0000aea3e000000000bda48d4b6da0840000682000240400037e80000000bb1000000019c07ad0000fce000020e00000758000da1000000000009d31718afd28708afae380000b9056c4c640fe08586298f1c00000000000000989b968659412ca138000a51000097a00748d500010e03810c671fc00002d350fd00
  | 42 => 0x534ca74d602374e060003820c33000000000000000000b14000080b3d3800000007d9044461e0000000000058632ccec3000000048c800012f419c80000000000000196c00036c4a9709f0d50244c0000000000327e0002a4cbb5000000000005d5085c3c04cb847b35c8605079ce1f40742b41d0862400000000000040aacc1053ef8000062a0a549e83f7250050c213c00037880003068000000010a00000000128000490cdf248ecd1916a400041840000000000000018f061d373250c2cdb4a80001760000000097233e07ef04a80000e000004b540000fb45f302ba87a47f81a335190924daea2f37b85130000f5495a4b4f3ae400027ec2f680000000000bf800000000000079000035e000000000000003c8800006fc75800006e01f0504936787ee22f81b7a4547de22ac1253d288a73bdc82725e4109424c16ace0024d095088314750002c26ebd13933421920e9d227ad7e002c0004700b61352d39a24a426444ec267031114e18d0a694142e3a2fc324f2d92b3308f40d726f400016b0bde0000df116c6000182c0001cb88ffcda011e277800027cce013920efa38e433305d923a282e9661e691ad38942392bd2c761dec54c01649e22ce8e540d9d06d1f5c4b10b68c8b2a6e205257d20e1918b0fa864c6647d417f0ebcb25383eb0c02bd0e336680004c70a06cf140001ae40760eb6000000000000003253e1c000266033200000003b6800000000961a8af01462ab2c8a6001e447c49311bc3eb9f4c6670b1800029d000017b00003e8800016e010239a4b0f09400000000607000000000007383458d6b343800000005d321100000000000000003d8000967800000000000000f200000000c3c00002e716f474b3725181131d2b50000000314400000005f6000123920f4fbd13f05622bd8e210e846c90000000483d3761210b0dadf20b10b146000a5453f14bc1683cbc24c0000fa800000f81808c474aa92d01bc086e3d46000451ce131e3908801e0e1c0fb8af28d905a31c4894c4b58def18cc88a1dc090f02e43c52dd0c0a3d900fd22bc73506927e42cbd3a92ed08312c6644a1038000000000000011020000fe52bac05c2e9cb47000053d2b20000169d1782a94af12c48000282cb2c0000d734870a842ff22eb06b4e9304c009c3f8091e1f548702cf84de3e4cc6a375816e42f911a28943ea43a828b83080b22fc88540b1c87728a88532408042be20b1a15f86310cec14c130c2d1194a00000010e240bc0001938786989460920d47520f88588227c0001cf0c2200011e2336935700000004224000000000000003fa064c00000007f6032c007143423a119d2e50000bee000000000003f6000000000000002d5c0000000b64000000008df29b24ec1ea1578a5515b80004cf8119a0bcff70a26b51bdb71c54350b1600005
  | 43 => 0x1670000c870000c6000008161cc0fb744b0bc68000000114c000228219d892905714a6c21334cd391280f394b240001678d8216903d700000000678ffd044c0c63f18b954a11184188862940cc34b0ab4c4d120a9f04664381221d1b44b9c6ae2f3d31f0cd8ca905840421edc58f0f052cd36a0fdc097e39c2860000000012200006ab01b249100002b042040002a5511800001b700004f12560000175c0002e28757012200040c400000000003d4c0000000a4b382c57500000000000e1d4600c100000fca018133c36b0e510000acb34510420000f6682f40003fd46bf093c4920000bef00000001fc800040906dd00d2c090a311b507490d8000011606ac3b00c9c29f2eae23f0000000217919810ec1ba0000000412eb3044f400030ab1f42ec89b040b8f5e288607b000000001a2df400000000000000000000000000e5021200015909eb1b58c2e00010d91ff85003f0c0000000afb13f8cae9ec8530060a9284910469cd5e464489cb91285e5c900002420b0052700009900000b4100003eb1158d613b0400036280000000f20450922c4694000303c0b72a781eccb90362000000008a129618c8b1483fca343110e0e2264000000005e4bd43910000000151cef30a94e4a15a8e2f42445461138d9b3fece99000000040380004274a9c8b3c00002c0c702a6097485182a400000004ae8c8a000007380012541a8cbd200007310750999466600000003ef0000c6100007640d984800000000000000024e12331ce43e280000114b3c99d30e6669000000039fc00000000000000000000000000000000590d0f4ee4c388a740000000000222c65e2da4000000000000000000000000359000031ec0002bb2c8e13413bd4580ba5800042c468d00218d6a8f00001508000a6e4d58e35cd28000000027501351c63294137038496712c0e6f0c6c05645d821b000024e3b08000050c0002dcc000058d15c44a4a4f29340000eba000014400042804822a0d3d42e16cc424dd0f600009760fec000479087d0e1c00013f40001990da20000000022c80e00013080ee61fd303ab6e01aa52213d47b02e5115a398a0002fe69820000fb000000002254e2190633992c38d5d04fce5924e80003f1ca2994e8000016cf2b00000002cc5286261477c2bb70c62114e7321020000000c0db420e8d83a42ea26000000000ce338420001e5000000000004b7c00000000004a8cd53000000023220000000d6c0000c0c80000000ac850b061e35803f0cf71d00a1320d80003d842190154dbd4a2844c0000a0536e806e80007192d58b48c4dc0001bfd13a10fee330000a71224d01f0380d8e0000c1c47f077a393c0000000b868f3111413e4b0819b06cf15853474878e704f084263bb89d4459400000008f8000000041c80001fa1207367c9aa183cc84b404d062
  | 44 => 0x8ad2f93ea831d0000000000032580000004a6400000008de43e800000000001b000003cc000013c6e304688be4cb60aa2ab12ace309427f1640f609fb0cbd12f90400338dcd35148f922fcc7f32e81b5435d24e466c38f0f92d1318dcb06124013c200d3950e413d511882a81924c2f97c2dc131b2f0623c8d66808a35725b474e19d517904681c44cbc3ac33313c72a580a329bcc9c00011110000744000057400012c341a061f80000001d58c9f2fb10220fc8d3e1f08000000034803552cc00010d1090c0000000e2b48f0d1e1fe4000121caf2289049408c08501a400000000258000000030747859350bdb8a581e880007fd00006b4000000045ecc7e00000003428cb1000035224b0e8f206d36e00002d9444c0000000e860a4899400002103d884e4258000037c05c50b0c33915690411384e490000b2910922bb2ff88bb9f8438326e800029080001cccb443ba8b12b2793631396f7a0624000245cbe2add47b80ee25b90f7920d23601d08000144a1a90b007d20004f012103ef079d2eaafa1390014b00e506441cc00000003bc00000002f185212e4c8a417480001a2e00046312bd2286787a6a4a852d1e549031c45c22fe8660dd077d0588c552d5400001682d81dad1d83728000000015c0000bfa07dcff431b4651bf6400000000dc00000003856ccb000130f4bb819fb47c59f32fc7dc349836d00012ab37149741f813211ab061b23dc2182e0d0dc25a69a0134cbe13a284f0188d0ef0beab92a42c9af0000a0300000a2020037c045478f1af459b00005ee077859d163806400000004e3483324f0cca1d5489c2d38d5441140001bbc8d70a4c45a00000000f800001a380001d980a0c4285441548d5c3c4c30c8c64203ca452a700b0eb30e08c790d3d1e946fc70527605b384f88c1119b30b1c393b482fc4394058aac492400042651880000cef0f0683e497114540c000037e400017f933400007dd1044a503ca46de0ca05f40ff46ec23e80730362724376c81a2120d920b1040ab7cc88c000107d000000014b5270009093105e800018420000bbc53580009ee1b6400030183773580fff3ec442a00000002df0927154cea7000000000000000000be09298363000104c8b709ea4e8c8e40b5064c02de4ac0c228752d48cd120fe00a2e8cbb5a1e534b0dc85af111c03014a138241dce7e27f51b91cb52e12a76d783834b5f1c8d35e1260a7800000000000d330001013008c9bc1d70d3f17980002fee00040347c71a582973af0e0310bc6dc2225108235e52901d510115fc000449c6880001181b78400000006d01db423e219c02c94a24973a047342f96c69365026515a05aa82147e08000c5722a4cae3188604278496204a40001c9ce0544751cb28e009846e8a7b000000024d87d00344000385f2b048c4223c6560000000
  | 45 => 0x383c8cc4ef914b4e5800040c2f451fc40000000000494000028c5205000000000000004df89b90946d122e6c5a020980003200a86335443d053c1ef2aa08ec414800017850df31a0ed8000003f2d18a2d24bc17b00000090b349530000ed228880000000ce700000361960bd623640003b6466620647ce02046b30ac450624e43422da21aa1a1021a3cb0862325d33228faec50c251c9440d30311b45120d152080000900275a0000000c8524cc1bbad612780dd451442e03233ceb1b747e443c439800019d897e4edc70913b5051000129c00011db2bfd30044c861f20149574588bdc3ad1375172ce3f2d305ed0000880019b0ce0ca519e0e5c4603dd87cb1a24c7d3c5cf4c99c49b539c48dd2c008610000f2a00008ed3eec10e0000000308c000371c00000007852db4d224140a9f0abd04614390cb27bcb52b0a02bc00008b0b4306af47312c800000002984aba0000000226200000000001c345931ae056717d4fb200004224bb001700000002fd8f020000a949d0c642000040c0000d003c9cfbf091c1b33f3c00000013930e98da54a5c0001660fcb000000040040002df600000000450000cdf3a5426800001ac35fc7762d125b3074016eb048e3400002c1000101730f53a411e4db949ac224299875a18981dd000000000000000f3800027d13bb0000535000008f40f40000000000318c0000c589631c267013398000000127920601af0000b223d2ce324f2d14f0001255277cd042c7921543048f318e815125952d33aac3c900002d4800082a12a03c2245848c10fc0322204a2323c02661348e090a886feb3053d20854a2e49780003624000454c2ed800129f2fc10622a482220000bb325a459626100003d6d06309ae8cb32b4000036a0004ca401bc69902d000053c153ac18000000000000002bdc000000041902500000000f033cdaceb000067c07ea9c01e0cd3c2ec2d2f34e12043d181404dc068548dd08432608d20ec200024345b14e28e6b0a64d270f7c695000101137a80000b080000000000000117d09c80d60290bfdc8f8e501b8d0871000bbb31dd37a228c6724bf4c8800000000000152a8b60003578e683e78a9680001d32c1effe0000000423c0000000c5601b416b17e00000000000100505f465800000988a80000adbae60e022bb0188461919f00000000360fb30000083800071c4eaca6200009f7112c1e106f815600008f14824c0741d4f8b340c3a3000000000a0000021c000000000020b08761684436140c0000000ce9469c1478016d410000103399c0000eb811d3b344f30ee800016c8a273b88000082521f08d428101e223c0c345b036350430000135132062b000066213183bb1e481e000000001e6ced02cecb5b2078ada0c54b6e932818e4390f74369c98d11202ca3b307910000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9f0805c4424400f1f10cb8084880133a189701091003cf840ae0212200287c859da32440091dd053b464880021fe15768c9100143e42aed192200087c865d63244001ae020bac64880021fe1f658c9100043ec3ecb1922000a6d82d96324400187ecb3a464880030f196748c9102f64e31ce91922000db0109d2324400187ecaba464880030f195748c910006d8082e91922000c9e74d8e324400155908b146488022b320d628c91000c7a432e319220019f0805c6324400f1f10cb84648801e7c205708c9100143f42eec992200087d85dd932440050f90b3b264880021fe15764c9100143e42aec99220008bf845d9324400117908bb264880023be09764c9100143f428ec992200087d851d9324400117d083b264880022f610764c9100043e432ea9922000d70105d532440010ff0fb2a64880021f61f654c91000536c16ca99220088ec87589324400155908b126488022b320d624c9100143e42cec192200087f855d832440050f90abb064880022fe11760c9100045e422ec19220048ec825d832440010f90cba864880035c041750c9100043fc3eca192200087d87d9432440011db0fb106488002b3a19320c91000566432641922004ccf764c8324400199aec990648800393d95320c91035f2632a64192206afc0104c8324400f1f10cb806488003724c9700c91003cf840ae0192203ec7a76d97404407dae4e3b2e80880ee3e61f64d01100071db2ec9a0220078fb8759340440014f50d2a6808811f1e9da54d01100071db24a9a022047d7271953404400f3e502b9e80881131e9d953d0110226b938aa7a0220079f2815cb404404f8f4eca96808809f5c9c552d011003cf9c3ae3a0220019f187d07404400f9e4eda0e8088003acd9341d01101f63c3b6ca982203ed7071d95304400f1f50d3a2608801e7ca06744c1100069c2a0e898220079f0811d13044001b60823a2608811f1e1da544c11023eb838ca89822000bc98218d30440014f10ca9a60880231e1d9534c110226b838aa698220079f081dc93044001bc443b92608809f1e1d9524c11013eb838aa49822000ad8864c9304400f3e50fb8a60880027ca1f414c110004f843a429822000fc132485304407d8f0edb2a40880fb5c1c7654811003c7d434e890220079f2819d12044001a70a83a2408801e7c2047448110006d8208e89022047c7876951204408fae0e32a2408801e7c2077348110006e918ee690220078f8865cd204400f3e102b9a40881131e1d95348110226b838aa69022000e6b6518920440017930631240880029e21952481100263c3b2a49022004e6862549204404fae0e2a924088002ba219324811003cf943ee290220009f287d0520440013e10e98a4088003f04c9314811000cf843a429022001af086485204400f9e0ec90a4088013b81892148110
  | 1 => 0xb053b2a4880021fa1276549100043ec1ceca92200087d829d952440018db053b2a4880028fe1176549100051e422eca922000a5f835d952440614b906bb2a4880029be097654910006b8080eca92200087e841d952440010fb063b2a4880031da0476549100063ac08eca922000c76211d952440018f5003b2a4880031e60076549100063d100eca92200087e861d15244001a68823a2a4880034e1007454910006b8080e8a92200087e87d9152440010fb0fb22a4880030f1d364549100043f43cc8a92200087d8799152440010ff0eb22a4880021f21d64549100052fc1ac8a922030a5c8359152440014df04b22a4880129b20964549100043e438c8a922000c3c7419152440094dd04322a4880029b60864549100043f436e6a922030c5c63dcd5244001ae021b9aa4880021f21f63549100062fb9ec6a92200087f8758d52440010f90eb1aa4880028fe1163549100051e422c6a922000a6f8258d52440094d904b1aa48800a1f21f62549100043fc3ac4a92200287c87589524400147f08b12a4880028f21162549100052fc1ac4a922030a5c83589524404d4e90cb8aa488002cd211715491040db3c12e2a922026b70805c5524404f4f10cb82a488002ce2117054910405b5c12e0a922027b70815c15244001ae2e2b82a48800a1fa1776d09100043ec2eeda1220088de83ddb42440011bb07bb6848800a1fa1676d09100043ec2ceda12200087f855db42440050f90abb6848800a1f21476d09100043f436eba122000d7010dd742440010fd0fb2e84880021f21f65d09100051f426cba1220048bd8799342440bd53906b268488012ab20964d09100143e42ced212200087f855da42440050f90abb484880021f2197590910006b8082eb212200087f87d9642440010fb0fb2c848800317d9673909100062e32ce72122000c9f649ce4244001938c939c84880037404273909100062fb2ae72122000c5c655ce4244001ba020b9c84880063d219719091000cf8402e321220078f8865c2424400f3e102b84848800a1fa1776509100043ec2eeca12200287e859d942440010fb0b3b284880021fe1576509100143e42aeca1220008bf845d942440011bf06bb284880223720d765091000477c12eca12200287c851d942440010fd0dbaa84880035c04375509100043f43ecaa12200087c87d95424400147d09b2a84880022fa1e64509100245e43ac8a12205da9c83591424400955904b2284880063da1b715091000cf9406e2a1220078fa86dc1424400f3e503b82848800a1f21676109100043fc2aec212200287c855d842440011bf06bb084880223720d761091002476412ec212200087c865d44244001ae020ba884880021fe1f65109100043ec3eca21220008bd87d90424400117b0e32084880063d219711091002672312e22122001
  | 2 => 0x37695110006b8084ed2a2200087d829da54440018f5013b4a8880031e60276951100063c204ed2a2200087e861da5444001ae0203b4a8880028fa1076951100043f420ed2a22000c3e841da54440010fb043b4a8880021f61f64951100143ec3cc92a2200087f8759254440014df04b24a8880da9b20964951100143fc38c92a2200087c8719254440010f90cb94a8880035c041729511023d3d436e12a22084b3a84dc2544408f6e503b84a8880035cdc7709511000536c16ebb122000a6d821d762440050fd0b3a6c4880021f61674d89100043fc2ae9b12200287c855d362440011bf06ba6c4880223720d74d89100043f43ca9b12200087e8715362440010ff0ab9ec48800a1f21573d89100045fc22e7b1220008bc845cf62440010fd0fa9ec4880029b60b53d8910006b8082eb312200287e86dd5624407b0f90dbaac4880035c04375589100043f43ecab12200087e87195624400187ecbba2c4880030f1977458910006d8086e8b122000c3f651d16244001878ca3a2c4880036c04074589100062fb2ee6b122000c5c65dcd6244001ba021b9ac48800317d9473589100062e328e6b122000dd0101cd62440050fd0fbaac4880021fa1375589100043ec1eeab1220008bf845d5624400117908baac48800237e0d75589100446e41aeab12200087e871d562440050fd0bba2c4880021f61774589100061fbaee8b122000c3c75dd1624400187d0bba2c4880030f61774589100061fba8e8b122000c3c751d1624400187f0a3a2c4880030f21474589100043f43ca8b12200087c87951624400187ee92a2c4880030f1d254589102462e39ca8b12200087e8715162440050f90e2a2c4880030fdd054589100061e3a0a8b122083c5c7315162440014db042a2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317e1773589100062e42ee6b122000c5e54dcd62440018b8a9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f53589100143e43ea6b122000c3f74d4d6244001878e9a9ac48800317dcf53589100462e39ea6b122000cac74dc96244001998e7b92c4880030fdd352589100061e3a6a4b122000c5f73d4962440fd8b8e7a92c4880063ea1f7058910006b8082ea312200387d87d9462440014db05b28c48800399487651891000536c10ca312203fc757119462441058f2e0328c4880030fd9674189100061e32ce83122000db0109d0624400187ecaba0c4880030f1957418910006d8082e83122000c5f659cc62440018b8cb398c4880037404273189100062fb2ae63122000c5c655cc624400999cc4b98c48800374041731891000477c3ac43122000aac84588624400159906b10c488003335cd62189100043f434eca922000d70109d952440014d
  | 3 => 0xca1a40008fb805d9434801117d0fb2286900030f1d76450d200061e3a8c8a1a40018ec865c843480091f10cb8086900721fa1f64549201343ec3ec8a924000c3c74d9152480010ff0eb22a49000a1f21d64549200061e3a0c8a924004a7a86dc1524804d8f4edb82a4900030f1d764d09200061e3a8c9a124000c3c75d914248001878ea322849001a5b21d5250920136363b2a4a124000e2c645494248001c58a83246490012b3a0b634c920136363b2a49924030e4c6354932480618d8ecbaa6490002d3e0d754c9201872631aea99240088ee87991324801159d0732264900038b150644c920146363b4a89924048e4c63951324801159d0db1a64900231b1d9534c9200472631aa69924000ace86d0d3248001d18c9a1a6490022b3218434c920005e4c0086992400087f855d361480050f90aba6c2900063e20174d852000536c10a9b0a400287e859db41480010fb0b3b6829000a1fa1676505200043ec2ceca0a40018ec865cb3148011998ec996629000a1fa14764c5200043ec28ec98a4000ccc764c93148001a70813a6ca880035c04274d9510006b8082e5b2a203da7a80dd3654407d4f301ba6ca880021f60a74d95100061f204e9b2a2000c3c409d3654400187ae83a6ca880021f21172d95100043fc1ae5b2a2000a3e841cb654400147b08396ca8800297a0c72d95100052ec18e5b2a203ea76811cb654407b4eb02396ca880f69ea0072d95101f53cc00e5b2a2000d70105d764440070fb0fb2ec8880028fa1365d91100051f420cbb222082c7970197644400f1f301baec8880021f61e75d91100063cb84ebb22200287f875d764440018f2e0baec8880021fe0975d91104363cb80a9b22200287f87d4b64440010fb0fa96c8880028fa1352d911017e3ab8ea5b222085c7970d4b6444001ae020bacc8880021f61e75991100143fc3aeb322200087f825d664440050ff0fa94c8880021f61f5299110006b8086eab22200087e87d9564440010fd0e32ac8880031bd9772591100063632ee4b222000de010dc964440018deca392c8880031b1947259110006f0080e4b22200287e87dd564440050fd09baac88800a1f21375591100043ec16eab2220008ef825d564440091d904baac8880021fa1c755911036e36390a8b222000c6f75dc964440018d8ebb92c88800333dcf725911000637c2ee4b222000c6c85dc964440018d8a9b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100043f43ea4b22200287c87d4964440018bee7a92c8881fb171cf525911000637b96a4b222004c6c72d49644400117f0eb20c888002ab20964191100051f426ea3222000a3e841d464440014db043a8c8880021fe1572191100143e42ae4322200087e87d48644400147d09a90c8880028fa1
  | 4 => 0x3c800147908b2a879000a1fa157610f200043fc32ea21e400087f8759443c80010fb0eb2887900122f61e6410f2028c5fc3ac821e4000aae84dd932c800959d07bb265900029be19754cb203b5a7c1aea9964043e4c635d532c801159d0732265900db9318e544cb2000537c32a69964008e4c6354d32c800959d0da1a6590147a3193434cb2002566430869964000e8e6410d32c800117f08baac3900022f21175587200143f42ee8b0e400087d85dd161c800187ee82a2c3900030f1d0545872000536c10a8b0e4008ccc734c961c800f17b0f326839000a1f21776507200043fc2aeca0e400287c855d941c80010fb0dbaa83900021fa1d65507200043e43acaa0e40078bc8759141c80050fd0abb663900021fe1d65cc7200043ec3acb98e4000b2d8215364480010fb0f3aec89000a1fe1d75d91200061fc22ebb22400087f835d7644805f0ff04baec8900030f5d754d91200061eba8a9b224000a3d87153644800187b0e2a6c8900028f60c54d91200051ec10a9b22400287f87d4f64480010fb0fa9ec89000a1fe1f52d91200043ec3ea5b224000a3e8590764480014db042a4c89000a1fa1f75591200043ec1eeab2240008bf845d564480010fd0e3aac8900030f1d774591200043f43ea6b22400287c87d4d64480010fd0fa92c89000a1f21f52591200045fc3ac83224000a3c85590644800165b042a0c8900029b60854191200045ec38a83224000aad82150644800187b0e2a0c8900028f60c541912000717410a83224000a3d821506448001c5b042a0c8900028b608541912044f1d080a8322400087f855c464480050f90ab88c8900028fa1641191200055cc04823224000ab980104644800147d09bb4a8900030f9d276951200051f420ed2a24000c3e741da54480010fb0fb24a8902230f9d364951200043fc3ac92a24087c3e74192544806dad040b94a8900021fe1574d8d200143e42ae9b1a4000a5d8315363480010ff0ab8ec69000a1f21571d8d2000566c1063b1a4000ad9800c7634800117f08baac6900022f2117558d200047bc0aeab1a40078f4815d563480050fd0bba2c6900021f6177458d200061fba0a8b1a4000c3c7415163480011bf0eb18c6900029760e7654d200051fc22eca9a4000a3c845d953480014bf06bb2a6900029de057654d202253a40aeca9a400096d821d153480010fd0fb22a6900021f61f6454d200061e3a6c8a9a4008a5e8399153480014bb07322a6900021fe1d6454d200043e43ac8a9a4000c3c7419153480050fd0b3b686900021f61676d0d200043fc2aeda1a400287c855db4348001878ebb2686900222f61c64d0d200061e3a8c9a1a40048ec829da43480031d90cb94869000a1fa167650d200043ec2ceca1a400087f855d943480050f90abb286900023de057650d2003c7a40ae
  | 5 => 0x800a1f21574d85300052ec18a9b0a600287e859db414c0010fb0b3b6829800a1fa1676505300043ec2ceca0a60018dc865cf214c009998ec996429800a1fa1476485300043ec28ec90a6000ccc764c9214c00187ee93a2cb900021f60c74597200143fc10e8b2e400287d821d165c80db87e843a2cb901b70f50874597200061f200e8b2e4000c3c401d165c80010fd09b9acb9000a1fe0b73597200143ec16e6b2e4076c5f32dcd65c80ed8ba65b9acb900028fa1273597200051ec24e6b2e4000c5f739cd65c80094dd0539acb9022a9b60a73597200063bb8ce2b2e4000a3f845c565c800147908b8acb9009a9ea0071597200053cc00e2b2e400087e8790565c80010fb0f20acb900030f1d241597201353d40482b2e4000a798090565c8001878e820acb900129ba08415972000536c1082b2e400087e870c565c80010fb0e18acb900028fa1031597200051ec2062b2e4004a6e820c565c80014db0418acb9009a9ea0031597200053cc0062b2e406da3e84dd664c806d47d083acc9900029760c759932000536c10a9326400087f855ce64c80050f90ab9cc9900021fa1f53993200051f426a7326400087f855c664c80050f90ab8cc99000a1fa1f75593200043ec1eeab26403687e871d564c806d0fd0e2a2c9900021fa1f53593200143e43ea6b264000a3e84d4d64c800147d09bb4a9901b61fa1376953200061f426ed2a6400087d83dda54c80050f908bb4a9900021fe0d76953201b43fc12ed2a6403687d825da54c80050ff0f324a9900da1f21e649532036c3fc3ac92a6400087f865ce54c80874bb073aac7901da97e0d7558f200143f42ee8b1e400087d85dd163c80050fd0a3a2c7900021f6147458f200043ec3ca8b1e400087d8715163c80050fd0bb8ac7900021f6177158f200043f426eca9e400287d83dd953c80878dc65bb2a79000297e0d7654f200043e422eca9e407687f835d953c80018bf06bb2a79010e1fe097654f2021c3ec12eca9e400087d861d153c80012db043a2a7900021f21e6454f200061e3a4c8a9e4008a5e8399153c80014bb07322a7900021fe1d6454f200043e43ac8a9e4000c3c7459153c80050fd0eb1aa79010e1f61d6354f200143e42eeda1e400087f855db43c80050f90abb687900222f21176d0f200043ec36eba1e400087e8759743c80010f90eb2e87900028f21165d0f200246fc3ac7a1e400287e855da43c80111db04bb487900021fe197590f200043fc3acb21e400087d8759643c80098dce4b2c879013a2f61e6490f2002657394c921e40048bf8759243c800995ce4b2487900031b9957290f2000636b2ae521e400287c85dd943c801117b09bb287900021fe157650f200143e42aeca1e40008f7815d943c800f1e902bb287900021f61b7550f200043f43acaa1e400087c875954
  | 6 => 0x43ec2ee8b0e6000c3f7415161cc001878e82a2c3980029760c54587300266639264b0e60078bd8799341cc0050f90bbb283980021fe1576507300143e42aeca0e600087d86dd541cc0010fd0eb2a83980021f21d655073003c5e43ac8a0e600287e855db21cc0010ff0eb2e43980021f61d65c87300058ec18a9b22600087d879d7644c0050ff0ebaec8980030fe1175d913022c3fc1aebb22600087f825d7644c00187aebaa6c8980030f5d454d91300051ec38a9b226000c3d87153644c00147b062a6c8980028f60854d91300143fc3ea7b22600087d87d4f644c0050ff0fa96c8980021f61f52d91300051f42c83b226000a5d83152644c0050fd0fbaac8980021f60b75591300045fc22eab22600087e871d5644c001878ebba2c8980021fa1f53591300143e43ea6b22600087e87d49644c0050f90fa92c8980022fe1d64191300051e42ac83226000b1d83150644c0014bb062a0c8980022f61c54191300054ec18a83226000c3d87150644c001c3d062a0c8980028f60c54191300070ec18a83226000a1d83150644c00147b042a0c8982378e84054191300043fc2ae2322600287c855c4644c00147d0b208c898002ae60241191300055cc00823226000a3e84dda544c00187ce93b4a8980028fa1076951300061f3a0ed2a2600087d87d92544c11987ce9b24a8980021fe1d649513045e1f3a0c92a26048d58305ce544c09b0fd0fb22a69810a1f61f6454d300061e3a6c8a9a600087f87591534c0050f90eb22a6980030f1d06454d300061e3aec9a1a6000c3c75193434c001878ebb2286980030f1d46450d30064ae43aa6a1a6042c5c7654d434c001c38c8a9a86980021fe1574d89300143e42ae9b126000a6d82153624c0010ff0ab8ec49800a1f21571d893000566c1843b126000ae980087624c0011df0eb10c4980029b60a76549300051fc22eca926000a3c845d9524c0014df04bb2a4980029de05765493013d3a40aeca92600095d831d1524c0010fd0fb22a4980021f61f64549300061e3a6c8a926004a6e82991524c0014db05322a4980021fe1d64549300043e43ac8a926000c3c74191524c0050fd0b3b684980021f61676d09300043fc2aeda12600287c855db424c001878ebb2684980030f1d464d093000c6e432e7212600287e859d9424c0010fb0b3b284980030f1d764509300061e3a8c8a1260018dc865cc424c001c38a8326649810b171d9534c93021f26312a69926042d587054d324c0878b8ecbaa6498002d3e09754c93021f26312ea9926000d58705d5324c0091bd0f3226498012b3a0a644c9300070e2a0c89926028c5c76951324c06dc98c52a26498012b3a1b624c9300262e3b2a49926004e4c62549324c00159d0da126498003a3193424c93002566430849926000bc980109324c0010ff0aba6c29
  | 7 => 0x7c87d9541500518f4edb2e80a00a38ed9365d01401bd3d434a9a028028e3b64953405000187ee93a2cb9820f0fd0c745973041e1ea18e8b2e600087d821d165cc00187c803a2cb980030f10074597300043f426e4b2e607ec6e32dc965cc0fd8da65b92cb980028fa1272597300051ec24e4b2e6008a5e839c965cc11d4bb07392cb980028fe1171597300051e422e2b2e6042a7a801c565cc0014f30038acb980021fa1e41597300043ec3c82b2e6000c3c7490565cc0854f50120acb980029e60241597300061e3a082b2e6008a5e8310565cc0014bb0620acb980021fa1c21597300043ec3842b2e6000a3e8408565cc00147b0810acb9802297a0c21597300052ec1842b2e6042a7a8008565cc0014f30010acb9820e8fa1375993302451f420eb3266000a6d821d664cc0014bb062a4c9980021fe1572993300143e42ae5326600087e87d4a64cc00147d09a94c9980021fe1571993300143e42ae3326600287e87dd564cc0010fb05baac9981221fa1c75593302443f438a8b26600087e87d4964cc0050f90fa92c9980028fa1352593300051f426ed2a6608387e84dda54cc00187d09bb4a9980021f60b76953300143e422ed2a6600087f825da54cc0050ff0f324a9981221f21e649533041c3fc3ac92a6600087f865ca54cc0614db053aac5981fa9be097558b300143f42ee8b16600087d85dd162cc0050fd0a3a2c5980021f6147458b300043ec3ca8b16600087d8715162cc0050fd0bb8ac5980021f6177158b300043f426eca96600287d82dd952cc0618be65bb2a5980029be097654b300043e422eca96607e87f825d952cc0018df04bb2a5980021f6187454b30004aec18e8a96600087c8799152cc001878e9322a5980129ba0a6454b3000536c14c8a96600087f8759152cc0010f90eb22a5980030f1d16454b300143f43ac4a96603087d8758952cc0050f90bbb685980021fe1576d0b300143e42aeda1660048bc845db42cc0010fb0dbae85980021fa1d65d0b300043e43acba166000a3c8459742cc0111df0eb16859800a1fa157690b300043fc32eb216600087f8759642cc0010fb0eb2c8598023179cd6590b302ec5ec3cc92166008c9e7399242cc01193ce6b248598003179957390b300062eb2ae7216600287c85dd942cc00917b09bb285980021fe157650b300143e42aeca1660008f7815d942cc00f1e902bb285980021f61b7550b300043f43acaa16600087c8759542cc00147908b2a859800a1fa157610b300043fc32ea216600087f8759442cc0010fb0eb28859817a2fe1d6410b300054f426ec9966000a5f865d532cc0fd69f04baa6598012b3a0a644cb300052fc32a49966004e4c6254932cc01159d0da12659817ba3193424cb30007473208499660008bf845d561cc00117908baac39800a1fa1774587300
  | 8 => 0xab8ec4a0002ab61021d894000566c1843b128000ae98008762500018becb39cc4a00031719673989400062fb2ae73128000c5c655ce6250009998c4b9cc4a0003335cf62989400043f43ecab12800087e87195625012187ee832ac4a00421f61f651894000536c16ca3128037c3d7419462500014db04328c4a00023be1d62189400043f434eca928000a6d829d952500010fb073b2a4a00031b60a76549400051fc22eca928000a6f825d952500db0f9083b2a4a00021f60c76549400061f200eca928000c3c401d952500010fd0c3a2a4a023f0fd9074549400043f436e6a92800087c87d8d5250001878eda1aa4a0002cb60b43549401351e43286a928000c3c7650d52500010fd0dbae84a00030f1d676d09400051f436eba128000b2d82dd742500bd1790cb9e84a00028f21953d09400068eb9aa7a128000a3c8654b425006f0f90cbac84a00a21fe1f65909400043ec3ecb2128000c5f659ce42500018b8cb39c84a000317d9573909400062e32ae72128004ccc625ce425000199ae7b1484a00de1fa1b755094036c3f43ecaa12802887c87d954250051878ed2a284a00db8b18a54509401469c384a8a128036c3c76dd54250001a70e1baa84a00a30f1db65509400051e432a6a128042c3c7654d4250001c5eca31284a00028f21952509400261e3b2a4a128004e2c6254942500390f90cba884a00021fe1f65109400843ec3eca212800287c859db32500010ff0abb664a000a1f21576cc9400246e41aed992800087c865d732500010ff0fb2e64a00021f61f65cc9400061fb2ce99928000c3c659d332500031790cba664a00030fd9574cc9400061e32ae99928000c9d74d8f32500050f90b3b464a00122f212768c9400043fc2aed192800287c855da32500091d904bb464a00021f219758c9400043fc3ecb192800087d87d96325000187ecb3a464a00030f196748c94000c5e432e91928000c3f655d23250001878caba464a00032b5d3628c9400143f42eec992800087d85dd932500050f90b3b264a000a1fa14764c9400043ec28ec992800087c865d532500010ff0fb2a64a00021f61f654c94000c5e432e899280019b8805d1325000959d05b1a64a0147a318b434c9400456741ec4992805ee8c63d0932500050f90b3b064a00021fe15760c9400143e42aec192800087c865d432500010ff0fb2864a00021f61f650c94000c5e432e81928000cce764c83250009998ec99064a000393d95320c94035f2632a641928000d8e744c83250001b9264b8064a00062f61375d85401be1eba0a9b0a800287e86dd561500010fd0fb2ac2a00021fa1c65585400062fb2ee6b0a8000c5c65dcd61500018beca39ac2a000317194735854000637b2ee4b0a8000c6c65dc961500018deca392c2a00031b19472585404343f43ecaa0a80288
  | 9 => 0x7650b402ec5ec36e6a168004e2c6254942d00099d4c4b8085a00123720d76ccb4000c5ec34e99968000c9d76d0f32d000917b08bb465a00123b209768cb4000c5ec34e91968000cad76d0a32d00050fd0bbb265a00021f617764cb400143f428ec996800087d851d932d000317b0d3a265a00066e201744cb4000c5ec34e81968000cce764c832d0001b1ce899065a00062f21175587401be1e3a0a8b0e800087f825cf655012b47d0839ecaa00a28f61073d95400062eb98e7b2a800287c845cb65500010ff06b96caa02528fa1072d95401451ec20e5b2a8093a3e84dc7655005147b09b8ecaa00a29ea0271d95400053cc04e3b2a8000c75711c765500510fd0f20ecaa00021f61e41d95401453d40483b2a8000a798090765500010fd0e18ecaa00021f61c31d95400051f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d95401453d40063b2a8000a79800c765500010fd0e10ecaa00021f61c21d95400051f42043b2a8000a3d8408765500014bd0610ecaa00029760c21d95401453d40043b2a8000a798008765500910f90cb9ca8a01231718d73951401b43e432e52a28036c6c625ca54500014bb07baec6a00029760c75d8d400043f43ca9b1a8000a5d8395363500010fd0e2a6c6a00029760c54d8d400043fc2ae5b1a800287c855cb63500010fd0fa96c6a00021fe1571d8d400143e42ae3b1a8000a9d840c7635000159b0418ec6a0002b660031d8d4000637b2ce531a8000c6c659ca63500018decab94c6a00031b1957298d4000667b1ae531a8008ccc635ca63500010fd0fb2ac6a00021fa1c6558d404961fba0cab1a801087d87d9463500014bb07b28c6a00df0f5d06518d400052ec18ca31a80008df8758c63500010fd0d3b2a6a00029760e7654d400062ec1ceca9a800087d829d9535000147f08bb2a6a000297e0d7654d400043ec10eca9a8000c3e401d95350001878803b2a6a00021fa187454d4048e1fb20e8a9a800087e86dc953500010fd0dbae86a00030f1d676d0d400051f436eba1a8000b1d83dd743500014790ca9e86a01462f21972d0d401bc3e432eb21a802887f87d9643500010fb0fb2c86a00031bd967290d400063632ce521a8000c6f655ca43500018d8cab9486a000333d8d7290d400466631ae521a803787e86dd543501070fd0fb2a86a00a21f21f6550d401461e3b4a8a1a8048e1c639514350091878edbaa86a00a30f1db6550d400070fb28c6a1a8000a3c8654d4350011878eca9a86a00238718d5350d4026c3e432ea21a800087f87d9443500210fb0fb2886a00029b60b75d894000536c10ebb12800087e8795362500014db052a6c4a00021fa1c54d894000536c10a9b12800087f855cf62500050f90ab9ec4a00021fa1f53d89400043e43aa7b12800087f855c762500050f9
  | 10 => 0xb20643687e87151640c80147d09bb4a8191b61fa1376950320061f426ed2a0640287c845da540c8050ff0f324a8190da1f21e649503236c3fc3ac92a06404cce87dd9320c801c9d0bbb2641900393617764c83200667baeec9906400e4e75dd9320c80199aebbb26419002b3a13764c83200747426ec9906400a8e84dd9320c801d1b09bb2641900393153764c83200566c06ec9906476b4f875d5320c8d7a9f0ebaa641910ed3e19754c83200727c32ea9906400a4f865d5320c887a9eecbaa641900393dd9754c83200627bb2ea9906400b4c845d5320c887c98c8baa64191aed3a17744c832005a6c2ee89906400d4d75dd1320c80159b0d3a264191aed3216744c83228f46324e89906400acf865d1320c80169f0aba264191aed3215744c832006a6baae8990644ee8c645d1320c80179700ba264191aaf2201744c83235da7428e89906400b4d851d1320c80159d0f3226419002b321e644c83200727c2cc89906400e4c85991320c801c9ceb3226419003935d6644c83202567424c89906404e8e84991320c801d1ee93226419003a31d2644c832007262a4c89906400acd80991320c80169f0f2a26419002d361e544c8321b5a7c34a89906436b4d86951320c86da9eed2a2641900393dda544c83236da7424a8990646bf0e84951320c801c9cc92a264190db93192544c83235da742ee09906400b4d85dc1320c80159f0cb8264190022fe1175580320045e422eab00640287e85dd1600c8010fb0bba2c0190030fdd054580320061e3a0a8b006400a5d83151600c8014db042a2c01900333e1d32580323566643a64b006400e4e854c9600c801c9b0a992c019003331d13258032007272a264b006400e4c544c9600c801d9700992c0191abb2201325803202765b8264b00646aeca404c9600c8d5d9420992c019003334cb71580321463dbb2e12a68000ccf635ca63d0011998c6b94c7a00029760f5258f400143f42ee2b1e800087d85dc563d00011bf0eb18c7a00028fa127654f400052ec1ceca9e8000a5f835d953d012f87cc83a2a7a00a30f5da54d0f402470f31ca9a1e8028d3a7095343d009187aedbae87a0002c760f75d0f400069d386eba1e8000b8d8298f43d001187aeca9e87a00238798d53d0f400061e3aeeca1e8008e1c6354d43d009d17b0db9287a00233698d7010f4002666312e73168000ccd73d8a62d00014db05a9ac5a000a1fa177158b400043ec2ee2b1680008ef8758862d000147d093b2a5a00029b60a7654b4000537c12eca968096c3e641d152d004d47b0da1aa5a0002cb60b4354b401461ebb4a9a168036e2e6295342d0051a74e12a685a00db0f5db75d0b4000596c16eba168000d3a70dd742d008587aeca9e85a0003475cd53d0b40005c6c1cc5a168004c3d7654b42d0009c5cc4a9685a00030f1d7
  | 11 => 0x4c89dc5884b22a4990029de05645493213d3a40ac8a926400a7b80591524c84d4f100b22a49908e1fa1c64549321843ec38c8a92643096d82dcd524c8618bcedb9aa49926f1761b7354932004af426e6a926476d4e82dcd524c937a9b05b9aa4991db17d8b7354932186a7b16e6a92647695e871cd524c8096990439aa4991fb53dc87354932004aec1eeba126436d4c32dd7424c8010f90eb2e84990028f21165d09321862f39acba12644e8bd87d93424c8018bacab9e84990c31b9d952d093200717b22a5a126430d4e7354b424c8018d8eb3b684990031b9db75d093200597426eba126400b4d83dd7424c8618dcecb2e8499002cb21165d0932005a7c1acba126430d4e73597424c801c5acbb2684990029b61a54d0932246373b4a9a126400e2f64953424c891a9ce72a6849900353dd673d0932006a63ace7a1264089cf875cf424c8012d90ea9e84990231b9d953d093200596422a7a126408d4e7354f424c8bde1886a9e84990127361f43d0932046673b687a126400e8f64d0f424c8050f90bbb284990021fe1576509320143e42aeca1264018f8805d9424c8010fb0dbaa84990db530cb75509320043f43acaa12640087c87595424c80147908b2a849910f8b109655093228c5f438c8a12640096f87594424c8018dcecb2884991dad3e0d6510932275c6c1cc821264008ef87590424c80135f0eb2084990038b595641093228dc7c1ac82126400a6d86950424c801c5ac92a084990025be1d5310932046a639aa621264089ad87d0c424c935e1ea7a188499003c354f431093202567436862126400f0e54d0c424c935e18a9a18849902363a1f4310932046c6c3e862126451e8e86d0c424c801d1b0da188499003639db431093228f473b6862126400f0f85d0c424c935e190ba188499147c39d7431093228f86bae86212649af0e65d0c424c801e1acba18849917a6be1d4310932046c639a86212645ed8e7410c424c81139906b88849900363d0d7110932044e641ae02126400d8f435c0424c8010fb0f32ec0990021fe1d65d81320043ec3cebb02640287f875d7604c8010f908baec0990021fe1574d81320143e42ae9b0264008f7815d3604c80f1e902ba6c0990021fe1e54d81320043ec3ca9b02640287f87153604c8010fb0e2a6c0990021f61f53d81324cc3fc3aa7b02640087d87d4b604c9310ff0ea96c0990030fdd2745943236e1fa10e8b28646dc3d421d1650c80147f08b82ca190028f21170594320053b408e0b286400a75811c1650c8010fd0f202ca190021f61e40594320061e3a480b286400a7681901650c8014eb03202ca190030f1d040594320043f43820b28640087d87041650c8db47d09bacc8190da8fa10759903200536c10a9320640087f855c2640c8050f90ab84c81900a1fa1f75590321b43f438ea
  | 12 => 0x12abe1d64d0a3202657c3ac9a146400e2f85593428c801c590ab2685190038bdd564d0a32007163aac9a146400e2f53593428c8014db0d2a685190038b59254d0a32004b643aa7a146400b2c8454f428c801c5ac8a9e8519023539cd53d0a322f78721aa7a14640287e85dd1618c8010fb0bba2c3190029760c54586320143f42ee8b04640087d85dd1608c8014bb062a2c11910ed3a0f7259532006a7b9ee4b2a6400a3e84181654c80147b08302ca990029da0460595320053ac08c0b2a6400c3f749d1654c8014db053a2ca990029be0974595320053dc02e8b2a6400a78805d1654c9398dee7b92ca9900393dcf72595320052ec1ce0b2a6400a6d829c1654c8018f6e1382ca990028fe1170595320051e422e0b2a6400a5f835c1654c8014df04b82ca990029de0570595320053a40ae0b2a6400a76811c1654c8014eb02382ca990031e5c070595320043f43c80b2a640087d87901654c801878e9202ca990029da0640595320053ac0c80b2a6400c3c74101654c8614bd06202ca990029760c405953221d3741080b2a6400a6d82101654c8010fd0e082ca990021f61c10595323f636b94cbb2264088ed82dd7644c8fd0ff04baec89920f1b5c854d9132006373aae5b226400c6d755cb644c80199ae6b96c89900a1fe1f52d91320043ec3ea5b226400a5d83d4b644c8098bae7a96c8991fb1b5cb52d91320051f426eb3226400a6d82dd6644c80147d083acc8990029b60875991320043fc2ae5322640287c855ca644c8018deeab94c8990028fa1352991320043fc2ae1322640287c855c2644c80147d0932ac8990031e1c265591320051e422cab226400c7870595644c8018f4cbb82c8990031e59770591320047dc02eab2264018f8805d5644c86f8f0e02a2c8990021fa1f52591320143e43ea4b226400a3e84d49644c8014bb07a92c8992171d1c7525913217e3c386a4b226400c7b75dc1644c8018f0ebb82c8990033cdc770591320063c2a6e0b226400c7b53dc1644c8018f6a5b82c8990031edd470591320063c3a8e0b226400cf3711c1644c8019e0e2382c89900a1fa1676191320043ec2cec322647e96f825d4644c8010fb0f328c8990021fe1d65191320045fc3ac8322640087d879d4644c8050ff0eba8c8991fa1fe0975191320143fc3ea4322640087d87d48644c80147d09bb4a8990021fa1376951320061f426ed2a2640087d82dda544c8018db05bb4a8990021fe09769513200637c12ed2a26400a3e841da544c8010fb0fb24a8990021fe1d64951320053dc02c92a26428a7880592544c8050fb0e324a89900257e0d72951321b6a6192e52a2641687d861d1524c8dba98643a2a4990721fa1f64549321843ec3ec8a926400c3c74991524c8014db05322a4990021fe1d64549320143e43ac8a926400c3c7459152
  | 13 => 0x51fc2ae6b246400a3c855cd648c89d958e4b9ac919002ade0573592320055a40ae6b246400abb805cd648c80157100b9ac9191778794f535923202557416a6b246400aad82d4d648c80147d0fa9ac9190028f21f535923221d1ec1ea6b246476a3f82d4d648c8edc5d05a9ac9191da8f60b535923200716c16a6b246400a2d82d4d648c8edc58e5a9ac9190028fa1671592320051ec2ce2b246404aae829c5648c80155b0538ac919002aea0271592320055cc04e2b246400a3f855c5648c8014790ab8ac919012ab209715923202557410a2b246400aad82145648c8015750028ac919002ae60051592320051f42ce0b246400a3d859c1648c80955d05382c919002ab60a70592320055b40ce0b246400ab5819c1648c80147f0ab82c9190028f215705923202556412e0b246404aae82141648c80155b04282c919002ada0450592320055ac08a0b246400a3e85041648c80147b0a082c919012aba08105923200556c1020b246400a3e84dda548c80187ce9bb4a9191b61fa1376952320061f426ed2a46436a3d845da548c80187ce8bb4a9190030fa1176952321b61ec22ed2a4640287c845da548c86d8d884bb4a91900a1fe1e64952321b43e43cc92a4646dc3e74992548c80547f0f324a9191b70fe1e64952320151ec3cc92a46436c3c87992548c86d87ee5324a9190db0f5ca64952321b70f994c92a46436e1d32992548c8db0ff0eb24a9191b70f9d164952321b536412c92a46436e2c42592548c80147f0eb24a9191b70fe1d64952321b716412c92a46436c3f72592548c86d87ae4b24a9190030f99173952320061eb22e72a4640096f825ce548c8010fb0c3a2a7191361f21e6454e320061e3a4c8a9c6400c3f87991538c8018790f322a71917b87a0e6454e320070ec1cc8a9c6476c3f73991538c801c3ee7322a71910f0fdca6454e3221e1eb94c8a9c6443e1f32991538c887c3a65322a7191361f21d6454e320061e3a2c8a9c6408a6c82591538c80187f0eb22a7190030f21d6454e323b61fb9ac8a9c6400e1f73591538c887c5904b22a71910f0fdc96454e3221e1eb92c8a9c6408b4c83dc9538c8872db0db92a7190031b61b7254e32004b7426e4a9c6443d2e64dc9538c887a5ac9b92a7190025b60b75d0e3202637392cba1c6400c3f75993438c801878eb32687190030fdd564d0e320061e3aac9a1c6408aac82593438c8018dacab9687190226b21172d0e3200657322e5a1c640087d86dd5438c8010f90eb2a87190030fdd66450e320061e3acc8a1c6400c3f75591438c801878eab228719022ab2096450e320ccae43aa6a1c644fa5f8654d438c801c3cc8a9a8719277c31095350e3200656b26e4a1c6400d4d53dc9438c80955b08bb685190029b61b75d0a3200636bb6eba14646db2e84dd7428c801c58a8b268519
  | 14 => 0xe82105658c8014db0420acb190129ba0a705963220d36c14e0b2c6400c7b709c1658c8014ed02382cb190029d60470596320043f43c80b2c640087d87901658c8014ed03202cb190029d60640596320253741080b2c6400a6d82101658c8010fd0e082cb190021f61c105963236d1f426eb3246436a3e841d6648c8014bb063acc9190030fdd754992320245ec3ca93246402c3e75952648c86d47d082a4c9190029760c54992320245ec38a93246400a9d83152648c8db87b0e2a4c91900387a0c54992320051ec18a93246400e1d83152648c80143b062a4c9191b787cc8549923236f0e990a9324640087e87d4e648c80147d09a9cc9190021fe1571992320143e42ae33246400a3e85906648c80147b0b20cc919002aea0241992320055cc0483324640087f855c2648c8050f90ab84c9190028fa1640992320051ec2c813246400ab681902648c80156b03204c9190028f60f75992321b70f996eb3246436e1d32dd6648c80187eeb3acc91917aa7a0c75992320054ec18eb3246400c3e871d6648c801c3d063acc9190028f60c75992320070ec18eb3246400a1d831d6648c8db47f043acc9191b68f608759923236f0f990eb324646de1d321d6648c80147f0ab9cc9190028f21573992322f70f29ea73246400a3e87d4e648c8014790fa9cc91910e8f60f53992323b51fc16a73246476a3d82d4e648c8edc3e65a9cc9191db874cb53992320051f42ce33246400a3d859c6648c8015750138cc919002ae60271992320051fc2ae33246400a3c855c6648c80955d0438cc919002ab60871992320055d400a33246400ab980146648c80147d0b384c9190028f61670992320055b40ce13246400ab5819c2648c80147f0ab84c9190028f215709923202557410e13246400aad821c2648c80156d02284c919002ad60450992320051f428213246400a3d85042648c8050fd0fbaac9190db1b1cb75592321b61ec26eab2464048ec825d5648c86d0fd0e3aac9191b71b1c875592320245f43ea8b246400c3f75d51648c80955d05aa2c91900b0f9d654592320161e3aca8b2464048bc87551648c86d0fd0e2a2c9191b71b1c854592320061fba8a8b246436a3e87151648c80187d0e2a2c9190028f60c545923236f16390a8b24640087e87d4d648c80147d09a9ac9190029b60b535923204636396a6b246400a3e85905648c80147b0b20ac919002aea0241592320055cc0482b246400a3e85901648c80147b0b202c919002ada0640592320055ac0c80b246400a3d83dd5648c86dc58e5baac9191b68fa1675592320061fbaceab246404aae829d5648c80155b053aac919002abe09755923202556412eab246436a3e871d5648c80187d0e3aac9190028f60c755923236d1fc10eab24646da3d821d5648c8dbc58e43aac9191472b1cb735923200
  | 15 => 0xe18aca210028fa1031594420051ec2062b288404a6e820c565108014db0418aca210029ea0031594420053cc0062b28848fa3f845c1651080147908b82ca210029da0470594420053ac08e0b28841c87e8790165108010fb0f202ca210029da0640594420053ac0c80b288404a6e8210165108014db04202ca210021fa1c30594420043ec3860b288400a3e840c1651080147b08182ca210129ba08305944200536c1060b288400a76810c165108014eb02182ca210021fa1c10594420043ec3820b28840087f865ce54108e78deecb94a8210db1b1d972950421b4b7c32e52a08400c6f865ca54108e78dcc8b94a8210db4b9917295042004b7c1ae52a08443a5d839d563108ed4bf06baac62113e1f61e5458c420143f42ee2b18840087d85dc563108050fd0bb82c6210021f6177058c420143ec1eeca988443c3f42dd9531088787a85bb2a62110f1b8cb7654c420052fc1aeca988400c5f835d953108012db043a2a6210025b60b75d0c423ad1e422cba188404c6e7259743108a547b0d2a686211238798e54d0c4200596c14a9a188404cce7258f43108018dacab9686210034b95172d0c420051ec36eba188400b1d83dd7431080165b05bae86210028fe1953d0c420461ebb2a7a188408e1e6354f4310801a5eeab96862100a1fa157690c422843fc32eb218841c87f8759643108010fb0eb2c86210131b9c96590c420063732ae52188400c6d655ca43108050f90bbb286210030f1537650c4227c3ec36eaa18840096d82dd543108010fd0eb2a86210721f21d6550c423a51e422caa18844fa3d86951431080187eed2a28621002cb60a5450c420061e3aeeca188400c3f85dd943108018790bbb2862117b0fd4f7650c4227657416eca18844ec3f52dd9431089d87aa5bb2862113b2b8cb7650c420061fbb6eaa188400b2d82dd5431080147f0ca9a862117b0fdd95350c420470e31aa6a188400aaf865c9431080195eecb9286210034bdd57250c420043fc3aca2188400c6c75dd942108018df0bbb284210031b2177650842006572a6eca108400cad54dd942108018d8a9bb284210031bd4f765084200637bb6eaa108436b2c84dd542108db2dd0f2a284210031bdda545084236d9743ca8a1084a1d2e87951421086d65f0d2a284210dacb61a54508421b697bb4a8a108400e2f76951421080185eed2a28421002cb60e5450842006972a6e6a108400c6f7654d421080165f0ba1a8421002abe19435084200597c2a86a108400d8f7350d42108014db042a2c2210029b60854580420061fba4e8b2c64a0a6f825d1658c8094d904ba2cb1927e9be09735963202537414e2b2c649ea6d829c5658c8018eee338acb190029ea0071596320053cc00e2b2c640087e87905658c8010fb0f20acb190029ea0241596320053cc0482b2c6404a6
  | 16 => 0xd95420043ec3c81b2a8400a768190365508014eb03206caa10021fa1c30d95420043ec3861b2a8400a3e840c3655080147b08186caa10da9ba0830d954200536c1061b2a8400a76810c365508014eb02186caa10021fa1c10d95420043ec3821b2a844887c865ce54508918b8c6b9ca8a10025be09739514236e1eba0cbb1a8400a5d83dd763508014bb063aec6a10029b60875d8d420043f43ca9b1a8400a5d8395363508010fd0e2a6c6a10029760c54d8d420051f426a7b1a8400a6d82d4f635080147d09a96c6a10130f5d352d8d420043fc2ae3b1a840287c855c763508010ff0ab86c6a100a1f21570d8d420043f43ecab1a8400c7471d9563508018f0e1b2ac6a10021fa1c6558d420063a388cab1a8400c787019563508018eecbb8ac6a10031d1977158d420063db2ee0b1a8400c7865dc163508410fb0fb28c6a10029760f6518d420052ec18ca31a84008df8758c63508010fd0d3b2a6a10029760e7654d420061ec24eca9a8400c5d839d953508014bf06bb2a6a10029de057654d422253a40aeca9a8400a7b805d953508854f100bb2a6a110e8fa1b7454d420061f3b6e8a9a8443b2e82dd153508010fd0c3a2a6a10030f9d87454d420049f430e8a9a8400c3e861d1535080187cc23a2a6a10030f1847454d420061f300e8a9a8400c3c601d15350801878e9b1aa6a11778790f6354d420049f426e4a9a840087e86dd743508014bb07b2e86a11b61f2197590d420043ec3ecb21a8436c6e72d96435086da5ce52a486a1003879536390d4200637b2ae521a8400c6c655ca435080199ec6b9486a10233318d7290d422eec621ae521a8436c3e76d96435086da5ce5b2c86a100387d976390d4241c3f43ecaa1a84a6c3e76dd1525086d0fd0c3a2a4a10da4fa1874549420061f430e8a92846dc3f621d1525080187cc23a2a4a10030f18474549420061f300e8a928400c3c601d152508010fd0db9aa4a10024fa1373549423b696216e6a92841987c87d8d5250801878e9b1aa4a11478b10b63549420049f43c86a928404a3e8690d525080965d0521aa4a11b64fa1375d0942026973a2a5a128404e2f6454b425083b4dd0dbae84a1002cba1375d09421b717b26cba128479a6e86953425086dc5ec92a684a1002cb21153d094200747b1c87a12840087e87d9561508010fd0e32ac2a100a1fa1b75581421b43e436eab02840087e87d9560508010fd0e32ac0a12970f1d2745944252536c14e8b288476c5f32dcd651080147d0939aca2128e8f61273594420062fb9ce6b288404a6e829cd65108dd4db0539aca2128a8fe1171594420051e422e2b288400a7a801c565108014f30038aca210721fa1e41594420043ec3c82b288400a7a8090565108014f30120aca210129ba08415944200536c1082b28840087e870c565108010fb0
  | 17 => 0x1c8400ad8805d1639080959d05aa2c721002b360b5458e420070faa4a8b1c8400a5d87951639086d4bf052a2c7210da9760a5458e421b726214a8b1c8400acf82551639080959904aa2c7210029761c5458e420070f420a8b1c846da5f8215163908db4bb042a2c7211b7931085458e420052f42ee2b1c8400a5d85dc563908014bd0a38ac721002976147158e420054f420e2b1c8400a9d841c5639080959d0438ac721002b36087158e420056d400e2b1c8400ad9801c5639080959d0428ac721002b36085158e420056d400a2b1c8400ad98014563908014bd0b20ac721002976164158e420256741482b1c8400acd8290563908015b50120ac721002b66024158e420052f42ee0b1c8400a5d85dc163908014bd0a382c721002976147058e420054f420e0b1c8400a9d841c1639080959d04382c721002b36087058e420056b408e0b1c8400ad5811c1639080959d04282c721002b36085058e420056b408a0b1c8400ad58114163908014bd0b202c721002976164058e420256741480b1c8400acd8290163908015ad03202c721002b56064058e420052f42820b1c8400a5d85041639080959d04082c721002b36081058e420452e41eeca9c8400c5f73dd953908018bf07bb2a72100a1f60f7654e4221e2e41eeca9c8443c3f42dd9539088787a85bb2a72100297e0d7654e420062fb9aeca9c8400c5f835d953909078bcc63a2a72100a97a1d6354e423b62f43ac6a9c8443c5d8758d53908054b90eb1aa721003171d16354e4221e2fb92c6a9c8443e4c4258d53908918bcc7bae87211238798e54d0e420061e3aaeda1c8400a3d86dd7439080187aedbae8721002c760f75d0e422470f31eeba1c8400a3f8654f4390811c3cc6a9e87210021fe1d6590e4202637392cb21c8400c6e655ca43908018dacab9487210233398d7290e42006363aaeda148400a6d86dd742908018daedbae85211b6cba1375d0a423bd36c34a9a148436b2d8695342908efc5b0d2a685210db4b5da54d0a4200716bb4a9a148436f0e63953429086de1ac72a6852100393d4d63d0a420072742ac7a148400e4d8558f4290801c9eeab1e8521003931d563d0a42027473a2c7a148400e4e5458f4290801c98a8b1e85210039358d53d0a420053d404c3b2a8400a79809876550801c6a8230ecaa10029da0660d95420053ac0cc1b2a84a8a3e84dcf655086d47b09b9ecaa1003175cc73d95423951f426e5b2a8400a7a809c765508014f30138ecaa129e8fa1071d95421b51ec20e3b2a840087d8790765508014f50120ecaa10029e60241d95420043f43863b2a840087d870c7655080147d0818ecaa10028f61031d95421b53741063b2a8400a6d820c765508014f50018ecaa10029e60031d95420053b40ce1b2a8400a75819c365508cd47d08386caa10da8f6107
  | 18 => 0x8010fd0e32ac1a10029760c65583420143f43eeab06840087d83dd560d08010fd0e3aac1a11961fa1e54583420043f438a8b068400a6d8215160d08010fd0fa9ac1a100a1f21f53583420043f43aa6b06840087c8754d60d08010fd0fa92c1a12621f21d525834253537c12e8b2c84aba3e849cd659080147b0939acb2100317dce73596420063bb8ce2b2c8400a3f845c5659095547908b8acb210029ea0071596420053cc00e2b2c840087e8790565908014f50120acb210029e60241596420043f43862b2c840087d870c5659080147d0818acb210028f61031596420253741062b2c8400a6d820c565908014f50018acb210029e60031596420063db84e0b2c8400a3f845c1659095347908b82cb210029da0470596420053ac08e0b2c840087e8790165908014ed03202cb210029d60640596420043f43860b2c840087d870c1659080147d08182cb210028f61030596420253741060b2c8400a6d820c165908014ed02182cb210029d60430596420043f43820b2c840087d8704165908910ff0cb9ca9211231798d7395242004b7c12e72a48400e1f5495263908914bb0f2a4c7210da97e0a5498e421b52ec14a931c8436e1f42952639086dc3a852a4c72120e97e1c5498e4241d2ec38a931c8400e1e841526390907c3ce82a4c7211b697e085498e4236d2ec10a931c846de1f4215263908dbc3a842a4c721002a7e115198e420054e422a331c8400ada8014663908015b30028cc72100297a164198e420052ec2c8331c8400e1c5490663908015b50120cc721002b66024198e420070e2a08331c8400a9f84542639080153908a84c721002b5a045098e420056ac08a131c8400a5e8590263908014bb0b204c721003871524098e420056b40c8131c8400ad5819026390801c38a8204c72100297a141098e420052ec282131c8443a5d839d563908ed4bf06baac7210021f61e5458e420052ec1ca8b1c840087d8715163908014bb062a2c7210029b60b5358e420062fbaea6b1c8404ace82d4d63908ed8bd0fa9ac7211db93a0b5358e4200726c16a6b1c8476e4c42d4d63908058bceb29ac7210123721d5358e420143f42ee2b1c840087d85dc563908014bd0a18ac721002976143158e420054ec2062b1c8404ace820c563908015b50018ac721002b66003158e420143f42ee0b1c840087d85dc163908014bd0a182c721002976143058e420054ec2060b1c8404ace820c163908015ad02182c721002b56043058e420062fbaceab1c8404ace829d5639080159b053aac72100297a127558e423b727414eab1c8476a5d829d56390801c9b053aac7210029360a7558e423b726214eab1c8400c5f875d56390887c9884baac72100297e157458e420052e42ae8b1c844ee8c425d163908015af02ba2c721002b52057458e420056dc02e8b
  | 19 => 0x38b9d172d97420051f426e3b2e8400a6d82dc765d080187ce938ecba10029ea0271d97420053cc04e3b2e8400a3e841c765d080187ce838ecba10029b60871d97420063ab88e3b2e8400a7a8090765d08014f30120ecba10da9ba0841d974200536c1083b2e840087e870c765d08010fb0e18ecba10028fa1031d97420051ec2063b2e8436a6e820c765d08014db0418ecba10029ea0031d97420053cc0063b2e8400a3e84dc365d08014db05b86cba10030f9d270d97420053b40ce1b2e8400a75819c365d080147d08386cba10030f9d070d974200536c10e1b2e8400c79701c365d08014ed03206cba10029d60640d97421b53741081b2e8400a6d8210365d08010fd0e186cba10021f61c30d97420051f42061b2e8400a3d840c365d086d4dd04186cba10029b60830d97420053b40861b2e8400a75810c365d08010fd0e086cba10021f61c10d97421b49e422e52a68436d2f845ca54d08e7a5908b94a9a10db1b9917295342004b7c1ae52a68400a5d8319663d08014db0432cc7a10021fa1f6558f420043f438cab1e845087e8795163d08010fd0e2a2c7a10029760c5458f420051f426a6b1e8402c5c7594d63d08051b90ea9ac7a10021fa1f5258f420051f426a4b1e8404c3c74d4963d08014bb07a92c7a10231798d7518f420052ec1eca31e8400a5d8319463d08014db04328c7a100237e1d6318f420062ebaac631e8400a5d839d953d08014bf06bb2a7a10030fa107654f420062ec18eca9e8400c6d821d953d080187cedba2a7a120f1798c7454f42004b6c10e8a9e8443a3d861d153d080187d0c3a2a7a10030f6187454f4200697410e8a9e8400d2d821d153d080187cc23a2a7a10030f1847454f420061f300e8a9e8400c3c601d153d08018bced31aa7a1003171da6354f420068e3a4c6a9e840287c8758d53d0801878e8b1aa7a117b8710d6354f420ecae43ac6a9e8408a5f8658d53d08018b8ecb1aa7a1003471d16354f420152f43ac6a9e8402a5c8758d53d08018b90eb1aa7a100a1721d6354f422f70fc22c6a9e8400e1f7458d53d08018b8e8b1aa7a1003871d16354f4257f0f212c6a9e84afe1c4258d53d080127d09b92a7a11fb1798f7254f420062eb1ee4a9e8400a5d83d9743d086d8dce5b2e87a10031bd9572d0f4257696c10e8a968400c3e611d152d0801878c23a2a5a10030f9807454b420061e300e8a96841d87e86dcd52d08290f90eb1aa5a10030f1d16354b420052ec18cbb0e840087e87d9561d08010fd0e32ac3a10029760c65587420143f43eeab0e840087d83dd561d08010fd0e3aac3a12b61fa1e54587420043f438a8b0e8400a6d8215161d08010fd0fa9ac3a100a1f21f53587420043f43aa6b0e840087c8754d61d08010fd0fa92c3a12b21f21d52587420052ec18cbb06840087e87d9560d
  | 20 => 0x3ac08e1b1aa400c79701c363548010fd0f206c6a90021f61e40d8d520053b40c81b1aa400a758190363548ed4dd04206c6a90029b60840d8d520043f43821b1aa40087d87043635480187f0d3a4c6a90c30fd8e7498d521861eb1ce931aa47ec3f629d26354801a5ec53a4c6a90c30fd8d7498d521861eb1ae931aa47ec3f625d26354801a5ec4ba4c6a90030f5d26498d520052ec1cc931aa470c6d72992635480187ae8324c6a91bb1b5c86498d524dea6b96c731aa430a5d87d8e63548018bb0fb1cc6a90c3879d36398d521870eba6c731aa49bc5d72d8e6354861c9ae5b1cc6a90021fa1f6458d520061fba4c8b1aa430a5e8399163548df4df04b22c6a927353dcf7258d5259d36c14c2b1aa400c777198563548014f50030ac6a90029e6006158d5220536c14c0b1aa400c7b7098163548014ed02302c6a90029d6046058d52104b6c14e831aa40087d87990635480187ce8320c6a90030f5d06418d520052ec18c831aa40095f8758c635496569f04b18c6a91af93d896318d52024b7414e9b0aa42096d829d3615484f0fb0e326c2a90030f9d064d85520061eba0c9b0aa427a7681193615484f0fb0fb1ec2a90c3179cf63d85520062eb9ec7b0aa427a7681d8f615480187b0dba2c2a90030fd8b745855200697b16e8b0aa400c3f861d1615480187ec43a2c2a90034bd8874585520061f308e8b0aa400c3c611d16154801a6e203a2c2a90030fdd264585520061fba0c8b0aa400c3c74191615480187ee9b1ac2a90030f1d3635855213c3e43ac6b0aa400c3f7458d6154801878e8b1ac2a909e9d205635855200697ba6e4b0aa400d2c74dc9615484f8eeedb0ac2a92c759dcb6158552024b7414e9b02a42096d829d3605484d0fb0e326c0a90030f9d064d81520061eba0c9b02a426a7a80193605484d0fb0fb1ec0a90c3179cf63d81520062eb9ec7b02a426a7a80d8f605484d0fb0fb0ec0a909f1d9c761d81521353d406c3b02a40087f87587605480147908b0ec0a90030f61b74581520061fb16e8b02a400d2f62dd1605480187f0c3a2c0a90030fd88745815200697b10e8b02a400c3e601d16054801878c03a2c0a90034e84074581520061fba4c8b02a400c3f741916054801878e8322c0a90030fdd363581520061e3a6c6b02a42687c8758d605480187ee8b1ac0a90030f1d163581521353c402c6b02a400d2f74dc96054801a58e9b92c0a90021fa1f61581520061e3a6c2b02a42687c87585605480147908b0ac0a90030f1d16158152586b5b96c0b02a400d2e745cb65d08014f50130ecba10029e60261d97420053b40cc1b2e8400a758198365d080147d09b9ecba10029b60b73d97420062fb9ce7b2e8400c3e745cf65d080147d0839ecba1003175cc73d974200536c10e7b2e8472c3e745cb65d08e58dce8b96cba10
  | 21 => 0x80184645480147b0d208c8a9002cea02411915200596c1082322a400a768118064548014eb02300c8a90028f61a40191520059b40c80322a400b2d8210064548394db05b98c8a900317dce731915237536c14e6322a400c5e325cc64548018b864b98c8a9003175cc73191520063bb8ce2322a400a3e841c464548014bd06388c8a90029760c71191520e536c10e2322a400a7a801c464548014f300388c8a90029ea0241191520053cc0482322a400a3d87904645480187b0f208c8a90028f60e41191520051ec1482322a400a3e809046454801c7501208c8a90028ea0241191520071cc0482322a46da6e8210464548014db04208c8a90028f60c41191520071741082322a400a3d821046454801c5b04208c8a90038da0441191520071b38882322a400e3571104645480147d00208c8a90021fa1c31191520043ec3862322a400a3e840c4645480147b08188c8a91b69ba08311915200536c1062322a400a7a800c464548014f300188c8a90031edc270191520051f420e0322a400a5e831c064548014bb06380c8a90729b60870191520053b408e0322a400a75811c064548014ed03200c8a90029d60640191520051ec3c80322a400c3d87900645480147b07200c8a90028f60a40191520051f40c80322a400e3681900645480146d03200c8a90038d606401915236d3741080322a400a6d82100645480147b06200c8a90038ba0840191520051ec1080322a400e2d82100645480147d02200c8a90038ea0040191520071d38080322a400e397010064548010fd0e180c8a90021f61c30191520051f42060322a400a3d840c064548db4dd04180c8a90029b60830191520053b40860322a400a75810c0645480147d09880c8a90028f61310191520071a20e20322a400a3e84840645480147b09080c8a90038e10210191520043f43820322a40087d87040645480147f08080c8a90028f21010191520ecb7c12e9b1aa43087d87d93635480187ce9b26c6a90c297a0f64d8d5250537c12c9b1aa43087d87193635480187ce8326c6a90c297a0c64d8d524f536c14c3b1aa43087d8718763548614bd0630ec6a90031d5c461d8d520053d400c3b1aa400a798018763548834db05306c6a90c21f61c60d8d521852f418c1b1aa400a768118363548014eb02306c6a90031e5c060d8d520052ec1ee9b1aa400c3f749d363549414df04ba6c6a91da9b20974d8d520052ec18e9b1aa419a6d821d363548ed4dd0538ec6a927a9b60a71d8d520063bb8ce3b1aa400a5d831c763548018eae238ec6a90029ea0071d8d520053cc00e3b1aa40087e8790763548010fb0f20ec6a90029ea0241d8d520053cc0483b1aa476a6e8210763548014db0420ec6a91da9ba0a70d8d5220d36c14e1b1aa400c7b709c363548014bb06386c6a90029da0470d8d52005
  | 22 => 0xb1ec52a0da9ba0b63d8a545e61f3a4c3b14a800a7a8098762950014f30130ec52a2ee8fa1061d8a545d61f3a0c3b14a836a6e8218762950018eae230ec52a2e70f9d260d8a540053b40cc1b14a800a758198362950cf47d08306c52a2e30f9d060d8a541b537410c1b14a800c7970183629516f65d09b14c52a1364fa137358a545451f426c6b14a83687e8798d62950018bee731ac52a0da9ba0a6358a541b43e43ac6b14a836a6c8258d62950e565d09b12c52a0da1fa1e6158a541b537414c2b14a800a7a8098562950014f30130ac52a29e8fa106158a541b43f43cc0b14a836a6e8298162950014ed03302c52a0029d6066058a543351f420c0b14a8a8a3e84dcd629500187d09b9ac52a0030f6137358a541051f424e6b14a800c5f739cd62950014db0539ac52a0029be097358a540062eb98e6b14a800a6d829c562950014f50138ac52a0029e6027158a5453d1f420e2b14a836a3d841c562950018eae238ac52a0da1fa1e4158a540043ec3c82b14a836a6e8290562950014db0520ac52a0029ea024158a540053cc0482b14a80087e870c562950010fb0e18ac52a0028fa103158a540051ec2062b14a836a6e820c562950014db0418ac52a0029ea003158a540053cc0062b14a800a6d829c162950014ed03382c52a0029d6067058a543351f420e0b14a836a3d841c162950018f2e0382c52a0da1fa1e4058a540043ec3c80b14a836a6e8290162950014db05202c52a0029da064058a540053ac0c80b14a80087e870c162950010fb0e182c52a0028fa103058a540051ec2060b14a836a6e820c162950014db04182c52a0029da043058a540053ac0860b14a80087e8704162950010fb0e082c52a0da9ba081058a5400536c1020b14a800a6d82d8c62950010ff0eb18c52a0025be1d6218a5439e973a2c4314a836a6f8758862950018df0eb10c52a1cf1b9d16218a541b7173a2c4314a82887d87d8f60950510fb0fb16c12a0a21f61f61d82545b61f3a6c3b04a82887c8758d60950018bee6b1ac12a123171cd63582541453c402c6b04a82887c8758960950018dee4b12c12a0db1b1c962582541453c402c4b04a80087e87d85609512747d09b0ac12a0a21f21d61582541453c402c2b04a8b5b3a84d8160950c12df04b9ec8a90028f61a41d91520059d40483b22a400b2d82107645480147b0d206c8a9002cda0640d915200596c1081b22a4b4d2d72d92645480147b0fb24c8a90030f61f64991525a61eb96c9322a400c3f645ce6454801c5ec8b94c8a90028f61261991520063ab8cc3322a400a7a8018664548014f30030cc8a90028f61260991520063cb84c1322a400a768118264548014eb02304c8a91e74bdd3725915252596c14c8322a40087f87590645480127f0eb20c8a92bacbe0964191520053d400c2322a400a79
  | 23 => 0x400000000040020010000000008000000000000400100180080040040018000000001000000800400300000300060010018004000001000800400a00300000040020000010000010000001800c00c00300200040120030000000000004000000000600a00080040000010000008004002000800c0000000000010000009000001800000000280040020000010008002001000000c000001000800000400000080040000000000000000003000000000000100000000000000000000000001000000400000200000040020010010018000001000801c00a000000800000200000380000080000000004004000002800000000000000000000000048008000000000001c0000020020014000001001800800000100100000000040008000000002001003400c001003000800c002000000000000100180100000010000004000009000001c0000010000000004000001800400800100000000040020000018004000000000000000000180000000040000000004000000000c000001002800c00000000080040020000000000000002000000001800100180000000070008004002005000001c00000b0018000000000000000000a0000000000000007003800c00000200180080060000018008004000002802000000000000040040010000010006004003800c002000000002c00800200080100060000040000000000000000800000000000140000000030010000000000800000200500000040020000038024004004000000800000000000100040010050000004000000000000000100000000000000000004002002000000000800000080000040000040000004000002800800200000080000020090000004000002002800000200000080000000080018008002000000003c0000010008004002000000000400c0000048000000001000802400000300000040000010018004008000003000000000100080040000010000000000000000000c0000000000020008000002000000600000000080040020040000000002000800000200000700000020000028000000000000000000200f002000800000200000100000000000004000000000000000200000000000000060018014000003000800000600100080000000080000004008008002801000a0000000000002008000000000800400080180040010030000000001000000400e000003800000000000100000020010040008002000001000000c0000008000000003000800000200000000080000000090044008000001000000000700000000180000008000002001000000000000000000180000000000004002002000000000000000000040000020000004004000000000000600400000000060040000000006000001801c002001000000800200100280080060080028000eb87ce9
  | 24 => 0x9d2000000000030e0a8a6dc000a1f4770000000000229800010a43a00000000000000000000ba000000020d400000036d400000000000000007ba25900026156a250b117954898ab2c3b782702600c700000014fc0002db059913c0000000098b847d8000000000000000022340009e700000018ce6ee8000000e5c00033b07a4000000000400a000001002000200100400000000000000004002000001800000000000500140000000028008000003000800400000000080080060000000000000002000000c000000000000c00000000000000100000010000008002003000000400200000100020020000008006003000800800000500600140020070008004016000000800000200000080000020020000000006000003000400e00100000000000000000008002004000000c00200000080000060000000000000004000000400000900680080020010000014000002000801000200b0010000000004000002401000100100080060020008000008000001000000200100000040000000018000000004000000c002000001000c002001001000000000000080000020010020008000008000800c00200000000040000020000008000007001800c01200400080000180000000004000000000000800800e00080080020000020008004003001000c00400400080140000010000000004007001800c000001001800000000000100000080060000004006003003000000400000000000080010060000002001000801400c002001800000200100080040020020020004000002000800800200300080280000000020000000001001000001400100700000000010000000002008000000800400000000000100030000010004000003000000800200380000000030000024008005001000800000000080040000000000004006002004000400000000100080000000008008006004002001400200100080000060000018008000001005002400000100000040000040010010000000000800401400000180040000030008014006005004800401a00000280080000090008000000000000000400000a00000000000000000008004007001800400e003000800000a000000800400000100000080000030000000006001000000000000a000800000000000000040060000000004000000001000000000000000000000010038008000001002001400200100280000000010038000000001001800800000000000080000000018004004001001801400000100000000000080010008018001004800c00000000000080060010008004004004001000c0020010000014000003000000800000100000040060000008010002004000000000400100280400040000000000002000000001400200300000000000010000004000000001000c
  | 25 => 0x1aaf7a00005118d6cd8a0000001ff43fc000171abd48e00000519be494299b0001ca43dd45c1218dfc19ea7a0002f500006532f68000eb20f7d22000040e72425194f0000000000302e2be73f05c80449906c8000188000000000015f40000000000000000629000000161800032b80000007b900000000000000002094f7c00000000000800000000000cdb47c000264d3f090f00000fe0007843cdae8c0443910d200000004f735b520c31400041700000000000000000000000000000188a0000000000000000000000125c00051e0000000048d6900000004fc2c40000b1a752566000000000000000000007ab16d86ca0000000000001492b662090000000000000000010675b8000fa96d042c2c700006360ce00001696a40003811a8a25261642acc64a702be00000001900000000000000a3f0001cc0000000275800000075f000076910e0000000000dfa000000005438200000012b000000000028dc000399000000000000000026050587ce0000000000c4e22d800000022200016940000000000c1cbe600047500005c40000000000000000000000000058716380011e70000000000000a6f3e2000000047d4c0000070650c8000000ab30005e42368000000000000000400053827b4000000000138800000045fb1ac0000000000e54c1800000011e400000000000003ba00000026c917665ad8996cce760005ff24c128e00000000000000000001fc40002661e99d90b8a0002438bdc0280000828000f323b908c0000bd86fc62c8000c56c2643e08a000000043decf40000000000e7c000ab749a1972dbb478000000103a0000000000cfab58000000000000031788f438968446880000000000000766b280000000000000c7300000000005e724200014540004371194054ab90b6049caf40000000000f980000000000e380000002f7c00000000000000008391d902380005784b02e68a76ba81803158d6b0002c90000000b8625a906cbea97211c21b10f3c0d2fb93ecbc047350eacf02dc0002a400000000003aa00014acb0e42c2ec445500000022c160236600025c400000038962e0000a6c0000000b3a1a70000d816f01b394880005129f3000000000000000019f07889ce000000000002d0000000b9455e31946949143fc0000000a5c00050281ac64a1333000f3cf181813f506bc00000058400017929db00000000000002828620000b27000000000000021500000000000d3000180600000000007f6000000000061438200001b40000000002640000a510000650000000000000101c3d760300000000001ec8000000ae100000000000000000000eec7040579d5c0000001408000000000431a71c72657b63a18140000000002a2e6b2bd60000000000c351298001278be83655220000
  | 26 => 0x3dd984cd8095700000007246ba0000000482000288c000de164f0001d54694aea161204c7d87070630b01274000000000000081c24895ac2aa00000000e817400000000013a285c80027ac000000139a34e0000005802fe885c00044200000000000ec800000000021813180000003be006c000000000000000000000000010ee34d1e48000bf25f60001430cd29e934e03f80000b4000035400000000000003340000000000000000000000000000000018fa000bb70000dac000000427299c9b26f62d91b7c1eabe23b480004240003021af200000000000007e40000e60000a564861fc8000000000333974d1a83b14812fe40007780000000c7a00000005100000002bc400000098800000012d2153462000000037a0002ea8000577000000134a000000101c0000001f8c8b003200036c87d6000000611400179a00000000000000001a21ac004e6c68000000000000000007d7243f8406d758e5800010ba8680000003a88000000000000000000014000000000000000000001624bf000016e92540002d680012123bb503a0d81401b13d82e5c000c270002664d96000049000184a0d800000018f3000000103c0000bb449800000049041a033400000005300000008db3e5800000000007c8aa0710000000000147a000000263000023b49e80004182495032d6d7660000000880b52087016000000077a0000bcd6f600000000011d3bb6494937800069836199820000003a7800000000000003ccb825bb0002228000c64000000000000050c80002ca0004c5ae2d430652323117c000000000000000000000027f82e45a84da80003df8df2462c44fd86f455e00012a40a900000011c00000001e24000000000000000078b0000001834000000244c0fe70b000311c00000000000000008f834d28280002f943142aa000000575864151938780000000000000001fb91208700128000000560634808000080a000080e00000051cabb54ee7f625e233cce79141a5945800012010aa7183160622268000000c0e00000014f57aa000318000005300000018f12b73351bb554483f2aa941c0001e0000039a0000000000000b120000000000000000227800000065bdc70f6c00085324e0000244000195dafc00070000000014840cc3540001494000077800139a6d100000000000004bb000063800000006d04a41ec3568000fe4000000000000000061b877c0008738001ad0000000000000120200000000f80006c1800000000000020cf11000000057a000000053939d1e8d4a41160000000f3ab3300010300000000000000862000000041d66e00020d06309048fb00012e400000000000018c2b7414b00012ce0000002aa80000004488cec9b810021e800000000000009680006d30000000000b07000000145a0000000000000000000
  | 27 => 0x15834a80000000001128000000000000157c0000004bb800008800027a0000000740000000064e0fa422105d02e94800029d92e80000000000d2c3ab0e80ce00000002ad4000c2a0000ca9928000000592a77c3ca000000000000000000011b8000ba4000303c166000000182e0000004f800004ae81960280000000002a113b4000c330849910000bb20000000158a02581954a0000004a480013ca000000000000000032680000000000000000218bc7000000087687660980000000005670000000b7000018914ea0000000000000000000000000009d44a80014c0c116108f0c86c78625c0000194aef28906ff44a0000002fa428a55d0000fd50900000001edd406bb400003403771f1399a12515c0004198000000000002162c00000016b071cf9e00042680000000000000c2400000021200200000003a5dacc1bab873b000015210000000000000240000000000003cca300000003cb5d000000000003288d841103b0492000150200000000005d092f21024881eebfb26c05dc0000000001a7552a000000000000000000000000000004520000f4000000021ac270000000000062e00056a8000000bea0000000000a8b352908d0a82fe0a7800039c0000000000000000011a9611ce0004d6000074a1b900000000000000000000000b9100027980007010000000fce9700000000000641000160834b0002a02898d7300000000000001974c10000000af0290800175e0000000000775000000000000000000031e40000000000000fba0001de000000000000000001d1883000000000068157200000005130000000000000000000000000026d1cf400000043980000000001dc00000000000c980003aa9ff55f000000000000018c871e00035551c4000c1d3511d1400000016c0000000000000000000000000000000009563478c553b2b8a03380000268b400031e0000000000140c00000020f4000cccc218001f217740002df00000558b2073830d6a83d0ad100000000120d6f0c400000000024680009391001438efcc522ab00011e300000023481220004758000af80000002d14090a870001e485f8000545000120081519680000000001a293c8b1935c00000012f8c3816aa5288cc00000000000000005316988000000194140800000000000000000610bc2e7d7cab8d2918000248694c08000052632c03b00018de75a1d1aa582ea7191c8127860a13b00703a896200000000009ae000440959c1807b33910000e3c0df50f15e51d02ae000000000000000009d000a00010c925cb5c00000000000000000ab80000000000000000000806072a0e0b089104b400017c600000020a80002da2abac6c0000004638000d8400000000000002ec34b684cd94000000000000000053180009aaa6500000000007bc2fdc00000
  | 28 => 0xbf12c52434dd200020580000000090001fb56da8c61029f04d690ae4f930e8000028000220958400000005780000000000000000a5f000000090085c39b00000000000001a78e707b880016a36d42af01a9395580b461b2800000000000000006726d28000e8000084c367c00000000032f0f56000000000228d6980000000000c7952a00012e86a47a44680cacd98706434b0541b80000000000ec629d1ec09f00000000000000000000397a72d078c5800021e8ee61524a800000000000001760000000000097092661f00025fd3505a638e84e8000000000000013e096212a1de000000000000177ec190000e710767fc32a8dd0d0a000529aab55a023332d918000000000000000000000000fb4000558000000142807a5089bc490200000020088fe3624888000000000325b15400071a00000012509dc2d80000cea00054300017ce668d4298293d032a56a0000000000000000159200035a8000eab0005d28000a7c7df000000000034000001f40000000001ddc0000001720638e9200000014005c16f204ca47972676800013297b8000000000000000000003e00003de00018840768888000000f046ee0ef6d74000434232137c00086a3638000e4b991000000162cc1780000000000b11518000bd600044900015344f58e3c00035c37c0001fd025abfc38184f959e00034258d20005c700000016be00000000012ba00022c8000000173000283c000000000183c0000000000000000a086160000000c15c52a13cd262cb3b322b4000000337c000b0a62c4bf1a7cbc6000000000000099e511152cf1eadf00009bce88000000000169000000000014aa00000000006678510ec40017c24b737192989de0004a79e600008c30000914cd620f00000007d600025d80017aa23a00012500001b9a580000000000388015400000032e8000d4f0000000000000000000000000088f1c6000156803c53c0000000000070953c0004f90000000000aae000000000034321f208954e00003493c4e2a80c2ef000000046821300008b49360000ad80004960000c98d4c66d387800000000000000000000000000000000b5a474ac1051e6d639c80009ec9d3000000000000000005f8cc90004ef0000000728000314600000000000000008f30002f3d20c5b500008ca000000000000163400021980014a80780c295040000000000000000000000295d6120001211ec80000000001c5a00086de2d800000000000000016960001708000ef29b6125003c000000000165335e5dc0000000000000000010c00000027200017b603100014b400000043da18092a9f747f8000a863ac1a0800000000000006000004e34959e5c0009a00001f8c0000000000000b003a73a3ac090c800006445a810891600000000a06024eb80000000002a32f6899315000
  | 29 => 0xe90f540001cd6280001730052466168e7520000001c240000000000000000000039800000060a80000000d800000022e8000000000000000000000018f92d496f4d580009ac7c20001a320e20000d4000000074100000017040005bc800177a000000000000000000000000000002549c956529ba14608690ca3e80e0000006c97d9e9235b6fe22651910a0000000000017e000c5e00000012f200004a800000002431a11d54fe17c0001440cac00000014888142442b20000000000046c0000000001fb000130f000340655154a25d0001db80001f400000000005e441000000003240000000aca0001e6000000000000000000001193860000ac600000000015f600000000000000000000001224b2a0002fb40000000000000000000000285556c00000004500000005a49b0a00000000006f000000000000015060003a32c540000000000000000acb07a1ea00000004f8800031e10e000000000089a0000c4400067b8000000e9a5b40002a26fcc00000000011f806887ec00000095100003103ec4c1000000000000000000000000000002e980000005704550d8200000000000acadb80000000000000000000fb80000000000bf400000009b0c6600000016360000000000000000b7a0000000ca901d000000000000000000000006890000000d6c9c30001a3a000c770001864000000000265874fb351cd2230e8694e37100007be0005fa000189800034c80014b65440d18ea023c0004ea800000000000019c400076d11680e0b9a5dd00007c821e805000122ca130000002be800077f00000018ca35417900007550005e01a504460003c991450ac0f9800000000000000000015280004dc18ba00062a00000000003c11b920a400000047210780003fe33d03ad7e630236d151583661e41eb0783c28010000000ae40000000d740007e13d689391aaa690000e28000000000029cbd298f5e12a984120005fb80000000000002f74000000236000133a0002de0f806a172d00000000000000000000d63000000000037d00000000000002460930001670bd754bb08c0004e70001a48c346db154483800095800000000001c5831865973cb84000000091e0000b82af400000000009c8dde3341996274e30a8eaf284a00004ea01cad10504aac19115c453438556d800066c0000001b600009d65a10a4115ea3841312fc00026d000025c82c9e2000000033e000000000000075d13b000099a0005e0800000020b00021bce8f0000d607b400000000016780000005488000000000000246c00000054c917950598a0000000000b394fd80000000000000000c28a45014e9aa0000004e4800000092c1bd8fd0f2a0004d300000007650002428082a6e221b0bc75c6adb41cd240000000000000000000000000000000031e00000000002290a980
  | 30 => 0x8ac19b80000000000000000000000c5d202110585a2544391c3833db2662d2db00000003f811b4000000376c00036e2a92e780000001b200012f4c5b08c1c4c76ed9a000233875e33206a00000003b80ed59700000006ce80026240009bc00000012c6000349dc4501e00000013f81bca711f480009a0aec2c886d69120004760000000000000000000000000000000007eb000142800000000000000005d76350d9cd16b435ac82a96143e701fac8c000000373238460c4010000000000000000306000030f0001062000000194800000000000000000000000000001882000000126858a00057b1cc8000000000000000000000000001cc3af206967c642bf5176800000099a1320a844bec0a4229ed94f60004a2aae000068800030f93d427d000000000000046f000000000050e132c9e08070000db000081b03317203fab9b0520bd40000000001f2800060600019f91960003b588c108237d2bb15f80008b70000000cca2ab000000000000000000000007833ea000054bbd92b60e7301600028c317c000c403df80000000001ea000009e0002aca96800000009593d40000000000000000a1237007100000001ca01c0000bf637540000920001214000000000621800133861b41d165c000afc0000000c7496543cad80000a0100000011380003058000000c6e6159d400000000000000000000611158480600012c000000000000000017200b80c3a3f5838198461006800043c00000000000000002c7c000000073c000000000000000016c00000015384d460e000000000000012a800000044e00000005fe7a561f800000000002a12b92da65dbb082f00001b331d528134e0002f700003e500000000000000005ce88f850a8d6000000000004b32c05049e6c6300007b800054c3ef000000000000020900000001239454000506444a720cd300059d80006240000c696a8e940004d99b780009ef00023f8000ac10540000000b472dea6d0d87347000020400000020a8000c600003d780000008a10000000000565bad80000003cd00004180004a500022d8fee2b32e880007160000001d1a1d80001af293c2b2a9b17e874500800029380000003233f10c5113e9dd53528d55c068fa359d782345f0262147189e0000002dc40000004918000000000000000000000000014fc6f0ab30000c6817e0000001add680ada47c9af000000042f8000000000000000014f00000000006dc52000017a07b40002ce0000dc200000b8000e5132e00020503e0adc3ca0000000a480002eb83bc9ca00018960005c95d48000664b0562880000002c300006d4d0db83010aa49398a88bbe80000000000eec000000c3d2b72d3c5e2a6d58e1dc0d5e31350b000000087426a180c7c80000001b2200000000021f6000000000000011400034100000000005
  | 31 => 0x10406a02780000000000000000085185063381b8a206d03ef5ca8cd42c23d11daa5996ee190dde1dc8000b205a6a6340000000000000000c0030e80000001690000000000000000000000033f15c00006e2a0e2a9800000047657122a83392bc1c3a184000a2b0272b9d23800000018240005290dec0000007fe0fc0d4569c2f78c9230052a0003938f940000000b5800000014300011a49dc00000031420000004d68000000c32000000000000016a2ba000000006480001f684a3c0a6a827288053427d523a8ac0b38e5cce00003f28860ae072b80000014e61b4999969cd2bb0b0000240144000096000094e75600000006c60002638ef40001320002b140000004ca0000b238b137601ec0000001f104d4fa26a70001b9c9f00003890000b020000212711010899000204897c08200019d000000014f800000000025530a807a7f51e10000000000000000000071400000003d087e44da8400000005b28d08000000000000000052f6332f4ca2b70d17007188ae6792e64e906d20004d22c90c6d8fa00023700004b312da2ac22e4053e3800124e00000000000000002d888200005d50000000fd00000000000c551d80000000000b570a60000000600cbd301076ec760e40000000000167000054a00011a800000013d0f84c2c00067b00000007cc000223800000000000000000000002d19d3151c00000380000001101f80e98000000000000000000000000006a60000000000e2c0000a69ab80005091b9ab2825e30337b92480000000001c205540000000fe83560005df016400000000000000006cf1538000d7a1fb6341ded50d0000000000f801b18000000f200000000000000427000223857600000000008f691508a8000000a9300020340007bd47284dc0002a207d6025172031800000000000059100009d0000000000000000054ea1481c074b4bd8000c800000001ac45488b54f61bacd3917f8002660b3034e00000000000002f304b946c8752e3000000000000014dcbd4ae6520000000000034193fcdaa97d000000000017400000000000000000000000ab5233400000000014c00000003b645480018e0448256800119a00000000000006f300024b4cc60001b79950000c3b0000000fc80000002c358683f12259060a582e531a800000000045100000000002d21b975ae184000051c00000000000006e000028e9aa847e95c000318b7d845822a29e40000000000000cc3000000000000000003900000000001e000000006b380000015dc00013b9274000000095000000000000000000008f600020c4246b8002f71c8528000000000000000000000007360002cc87d4cabc490002410000b8c0322984d7c87137c0000c4426b064c00008e0000000c5895e0002c3000000000000000000000f23e4800024a0000000000
  | 32 => 0x4000000000211c00000000017c4000bb90000b100000001ab80000006f00000d3105e14e5e300c00000004c90000558134000000036c69b00000001ac00006980000000000dd98fca6400000018c200000000000004d206e2834be00000000000001530ac351f041000015c0000000d1c00000019140000000001cac0000005ae0000000000476a2600000000401cdc00000058a1fbccfe3a200008e442c0eabff8b300006a6889ada4000442000000000000016c80000000002d6000000000000000000000002559b4296810300000000000000eb0000dd00004fe1c80000791088800000000021b80000000000000000e3ea9c00000000000000001c140000000002c8498062f800000000085280000000000000000000b6e00061e00000000000000000f6250800000000000000000000000000000000000000000000012b400000000000be00063a8bbc00000028f000074900044a000084424c540191a4a000000008b98e200054246fc000984000035000087180000000000000558ae800000034dc00000000018eb021005b4142f26f400068a0000000000000000000000000000000bc000942000000000000014580012e61e651080000006a40c3000067c00000000010e90005412a100000000c4a2f400000000000000000000000000cdcb9c1900000000be45e18000000a8da465bc71ae0001b50000000b6f000289c0de00000004054d909b00024605d20603210000000000000036cc9c00010980006fd6b2000076cbb6229000130200095b51d075c9cc18349441f84c000048bab605bb00036900000007da33c6a3148229b0002b1800004680022f182e33d5c28000f42195a35293538a0004af8ab514e0358cf00000002210000000000000000072200068c0002760c4615a401a1a068c611142107c944af948580000000e910f6cb400000000000000000001190c40045ae50000000b9b0000002b20000000150074c5e0000131000000000048600c8dd400000010658281f1b12a68d5e24cc00b0000000816372267cae6775247200035a4b60df21750b2970d66934d8046b828d9d398c416d36a09eccde44c0fca54c00000052c800000000000000015640002e720848fc50b80019cc126000000000000061000005800000000000000000000000000000026e00014e826c11200000000007ba478804b1922920001bec6ec27100000003c867280010fc43600000000000000000000b4948eba13d62b1cb5e0005798e8400000000000000009da50bc5e4c6e00033642c80005c038cea811ee0000f39654000077334068966011d55400004c6995164e588000229800300400000000000000000000002b440005965e598e08aa2c1436ab8c1f89f925228a0c0733762a15a12100001bec00000078a00000000001cb00001e4000000
  | 33 => 0xc45330480000002b680015200000000bda000b6700000000000001640000c6200000000000000000000000000a6600007080000d100003b800000000000000000461a79a44d56a293eda5546be00000001700876774df80013c210b00022a0000832dbea5844ea0000002d7800000001a0000f38bc514b80001420000000000705000000000167ead60000000000000143800011aad900000000003b44d72d54496ba72089f80f4cc6c4431e783a467200030a40005ab12b23c09840000000000000439000000162e48ede500006020003989c32000734343a65c0000000002c740000000001f5508400016f2a84a7aaf72ba8368fae000219026800075c2fe2aa449a8d300013a471c71a80016304a201c4ac80016fc0000001e20ff000000000000009a91650001510a3b43c26e40000000001b1800000020000000000000002068c2e00055781d07020000a420f926a09400026c083a9203309b115ad9c134b8000000000552281000000010f9aa26da000217acd000000019800000000ad14500000005310001ea400000000000000000000002a340000b000000000006fe00000000000000002bc800000011a400179c0000000000a4c9330002e6400c0003cb0000000000000176800000000013f40000003402ce800000000000004fc5f23560000000000000000090a00000023bc0006ef800000165e00000000a57f0000000187079417d583308183e0000002fc8000000000249401a0000d080000006f562ba10c000b53525889d0566ce4fb09790506fa0deb12c5a200000000014360005ef000000000049320cf5bc00027d0000000056da50001848787000000000072a0000000e6a601000027811e00000000013e811c5880985562a9e3fd10200007260000c1000000000000004086625b9209c000000505800056236400023d000000002b9b460000000000eb40000000002dd80005fd4c1800000000000000014fa11f00000000000000000f20ba477419e0d5800084c8d480000004292c19324fd2653800000000000000000000d000000020600006270000000000723000240cd400004f20a0d1ccbab0000dd40000000f1188b09d50d59589e981200024f800049e00010f130c0007fb000000001400058c94940000001150000c9f0000000000a3e1210002aac5726120002c3d76a896000000081c00054f8af400000000000000000000000000e9f62d000000116616f2469cf144800000000000000000000000ae80000000000a3200026707240004025d800000000002fa031eb880002f7a4c80000031e28000000000276000000000000000000003ee4f71ee0e4d00000005c55ba2bf1842f9800093b0000000000649000000000059b5ff80006f239d00000000006360ce80013620005f58000000000215800000078d00020b
  | 34 => 0x17025cc6059b320000001aa9bfc0005045000cbc00076a0002990000450420000000013f385000005c033da817fccbe79a14700003170bd000000000000010e06ea00022b0000c340006070001e0056a3b331c80000000000001750d420004ea31200002f42d2c0007c600000008180000000001f3400015b483cd211ea0000003030083000000000000035a00000000000000001fcc000a4300000003c60005ca0000000be00f580000004cf0000000000a2f0000c780007c524d85e80000000000001022000000311800065900000000002df3cfa08d4d1a7231cd1012965bf0000f580002860000000011000000000000000043e8f8400000036b800150f0893b1004148cbef47130e4d1a41c62519b0e2720148fa8c40008500000000acc0004b621be5b8000000215c000000280a7009c246200003c00004d20000000b9617b36e2e5951e93e2249f0c2c8000000145000000021a9fe546800000000000000002b480000000e80000df88286905ab00010cc00000012a144000000000002fe14b0fd0000000000351838c00000016480001305900a11c6d86c00016680ccc303a397b23c80000005f70be80000c100000009300005e880005ce00000000015fc5d90dc20c80000000000000000a30237956d8a6830506a6ec000b1e00029ac000384000046c000163000000000000006cae3c0001c31e3978557e1d431d8000000000000000157600053a07cc000318000000000000061800000000000000000ea60005b980007fe86200014a0bfc91935bc000000986000000088a44a35d54d8aa82b013fab1038a000000268582000023b800000000045f000000000016ba17e5a900000000000000002d080000000000000808f4476c2a3800016a0000000bb800005d29220d303e5e3d2721fc2144616269c84aa25bebeb073cd5dbad00029b671a0000e508c56301aa0000994c862d357e800046c00047ccf181aeb323b88fdcda7000000012853c0b71068645194a5e3d9c0010b420a0000000360a170001f19110000000000149800032d00007000e200027f4ab483742f400000001e5e20000000b3600000016dca330000000dba0002f1000157410d026241cfa400026e81140000001c3000072c0182bf800000044429a80000006c90000ff40000000001024b17384b8b9970564645973101974449915568b847800062e0529182b3e00009c00000000002d8cc5000000000000000002c981d400045d0bb163c0000002fc0b193441ba081000000023433c00000000000000000000000000000000000023a00005ba94d000000000008600000000004133da000033885d80000000006470000001242000000000000065000016804220000000e24490224000058980e6bb19d278c0005490658000b700005b10000bf664
  | 35 => 0x13441fa54d0000000000000000000000096e00014c000000059400000000004500000000000000000059e1680000000000bd80000178c1a000000261c5d600003e0000000aa300580000000000000000000001000000000000040f26394b885507f800000000000000016ea0f100000000000003e9936d2c8a500001142000ae900030b80007420a3073a351682800199600000028d000026221000000000008c80002ac000000000000016f8000000000119c26700021cb0ce3d04fd170c7e69381989f40e90bac186212c53231f445a16d10a47a210800000053400018982787b50000000a223983c7192009a909800000000000002c2374a6619d800257817c6b9000000000000000000000000001e72dac000000000000000071f800000129800000000016c20000002be00000000ab07a800056f46c8000d8964a8720a70ac4c162dc80000003772a500015fe19b000000040668611b800120a6d021264fc14a1f7000000000055c00007f00000003042824d5200047189a0000bfd00028b000039e000000000094300003d896400015a2e201a48f780025ac88c2d000000000000000a48000000767000000000000c3ac000087006517d83080000000629eb928200033000000006858000000d0f1ef00000004f20000001b94fb287c9400000000000000000000056a00000000000000000efc3fe00039f000000000017525100000000842a24c5c000050e1188c6c6d0000000000000000145d2f047202059912627854ba90b400015d00000015a6000000297518a6b880000016c83dc598814571250f0c10d603238d80000000000c420000000b34000000000000000014680000009370000ee80000004e12ee0000bbb045a73c0b600000000000000002702830aa00003d3a500000000000000075400000000ad37c000000177c0000000002f314f83be4e8225c43a90e4f0068000071300000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x142d921d676d09400050da46401d165cc00183a801d241597300141b25d8299152cc00144d929957390b30006071d18315161cc00121f9260c54191300068684183150644c00142d921d764d0d300050b64875193434c00181c871915350d300050764c74191524c00141d931d764d09300050764c75193424c00141d931d464509300050765c54193324c00160d9215064cc9300050765c54191324c00103c9461476485300050da46401d165c800183a801d241597200141725d8399153c800506d9221d65d0f200051364e655ca43c800182c7460854587200048be4d821506448001a2a1060854191200050b64874191534800142d921d764d0d200050b64875193434800142d921d46450d200050764c75d93424800141d931d464d09200060b21c64549424800142d97150648c9200058364c54192324800142d97150644c920024b22598010d324800103c94614764c5200045c660109d365440015309404274d95100045ca60105cb65440014369190274d95100045c660105d764440011719804175991100045ca6010dd5644400156195043725911000558654101c964440011719804276951100061c605809da54440011729804076951100045ca60105ca54440015619204172951101445c66371dc2544417b93284dc770951100045c660105d662440011729804375589100054c65410dd162440015319504074589100055465410dcd62440015519504073589100050b648851d1624400182c746085458910006131cd8215162440011719804175189100054c654109d0624400142d9219574189100054c654105d062440015a192041741891000554654109cc624400144d92d95731891000513648655cc624400155195041731891000570648105cc624400188c845cd62189100045ca60109d952440011719804076549100061c605801d952440011719804074549100054c250101d1524400105d9321c64549100141b25d8219152440011719804373549101345c261715c15244001530945c570549100064c211715c152440011729804375d09100041764e87d97424400117198041759091000554654109ce424400144d92195739091000554654105ce42440015c19204173909100045ca6010dd542440011719804175109100045c660105d6324400153195042748c9100050b648655d2324400153195041748c91000568648105d2324400117198041754c9100061c218105d5324400117198041750c91000433261764c8324400148c945d9320c9100051365f654c832440014c8964c9700c9100054664c541d1304400117195a1f414c1100045c6548748530440019c0874c9214c110005b02593248530440015299215074481100045c65687d0520440011719521d31481100067021d324c520440016c0964c93148110
  | 1 => 0x20048725185042639080124c9460a7558e4200493e4987951639080130f9260f75d0e420051364c755db429080144e97a1563d0a4200583a528558f42908db60e94dd563d0a42004936607558f429086d60e941d563d0a423b60b5d182d4f635080143a909847454d420050da46601d1535080143a9098474549420050da46601d1525080183874a0241594420060d1d281901651080103c9461c10594420051364e655ca431080142d921537650c420060bdd982951431080141d932177650c420050b64885dd9431080182f7660b7550c42004c3e4d82dd5431080182f86dd57250c421b50ba5085dd9421080144d9321776508420050ba5353dd9421086d82c84ddb75508420048be5983951421080150d93953735084200623e1b7350d421080121f9260c759923200487649831d6648c80106c9760b53592320048b25d82d4d648c80182d64e0973952320050725d83991538c80142d92dd664d0e320050b64875993438c80142d921d564d0e320060721e6454d438c8db22e98dd564d0a321b48ba6075593428c80160d931d564d0a320050ba5f53593428c80106d9621d53d0a320048b6588454f428c80107b985c070595320050e251701c1654c801470915c070595320061c605701c1654c80183474a0640595320040f25187041654c8fd84d7260f52d91320060e21070595644c801834811d164549320060e20074591524c89d42d97d9152d09320051364c759db424c80144d961d673d09320060be1d65590424c80106f9761a54109320050be5d64950424c80148f9761b43109320054365f85d0c424c80160d96e17431093200543e5d65d0c424c801c0e7659743109320060d1d281901650c80103c9461c105943221c9366275dd9320c801a0e85a13764c8320068361684dd9320c801a0f95a13764c8320068325684dd9320c801a0e75a13764c8320051365c54dd9320c801a0e84153764c83221d1325f865d5320c80124e94e19754c8323b493a63765d5320c80160e94dd9754c83235d13a63765d5320c8ed84e98dd9754c83200703a53765d5320c801c0d94dd9754c83236453261755d1320c80184f865d5744c8324ef03191755d1320c80124f96614744c83228ca3a5087991320c8db60e94e16644c8321b583a5085991320c80124e989d6644c83200583a5275991320c80124c985d6644c83200613a1d75991320c80160c945d6644c832274a366374991320c801c0d75dd2644c8320051365c54991320c80124d96e1e544c83200493e5987951320c80160e94dda544c83200493e5985dc1320c80181c7460c54580320060b1d182151600c80148e94e1d325803200493660544c9600c801c0c7415132580320050764c401d9535000141d931d676d0d400050b648759db435000142d9210076549400050764c759db4250
  | 2 => 0x20428313f8453b8e515c6e00cf52c6002d4c19ae543d0932d878418ef374d837c2e2147f0006d00105000d680000000260000026400238002582a0e0f6000001ec071f84b02c0036c000010229d0739800090a50000032861000d211c001f400000872600000000000001c80e1aae327c012a60004cc00a453346812a2ae198bf9383d000003cc1d4001a040ff29909000902c4de2dc89188002ccd0024000fabd00065058b802a43100f234ce129000000421a400000333710400000404003420000000000aa000000005e000ed104000002d034e0000a91e800000f84302f1340017ad9324833309e1bc0032c9229a4a33400420c2a548a0000031c1122c00000220709d1603f09460168000601f2ac6317c00130000000008c8d304e9154f93a0d1000271b00040ce719cc3110c4350940180c3f4120841e1190b000b00a0641ac683d2ce064b91480a0c85c2b0753565db1297288cf2e8ea00000000003c02b29e91270372fc0005c00000000000000005120f100000000001c400230be218340006a2a0002ec361c0d623cbc00000308003b074368001242c2683e010a0000e431400000003e8a139a000000013c3c00000158d50000000000000af17476000000003a35cb42c8a306c001e4000ec00000510e4e200014000840c000000730005b1dc00000000000800088000bda08003dc00320fb000fc352002ea9b0d40031800000801f00000859140153ac002b40f010060006000040000004000301020020006810100201808000000058080002808061a0201802080500006010201000040000002010001420100980018000281c1400000183600000040009008440e01110140001000000004070080a060500002030800018000b01c000c020080183a74a0261d8a540060d9d281983629500105f985cc7358a5400507a52325cc645480105f985cc73191520058c64281104645480163191a0040191520048764c84040645480122d9221010191520061c5c5801876354801871815c060d8d520041de61711c763548018717160071d8d520041ee61701c36354801871815c070d8d520050e640611d16154801834811d163585520050d644601d16054801838801d1635815200417e61731cf65d080181e845cc73d97420060e9d2809c765d080183674a0670d974200607a11831d953d080182e846087654f425f54364e821d153d080143a909847454f420050da46601d153d080144d921da6354f4200417a607658d53d080181e8458f7254f420050ea42611d152d0801436919807454b4200686152809066390801a1454a064098e4
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x38000002caa60200000000027806e2b9a29800052401c300008180004000ac0412580a0024004300324000506340408e8b1ac2a9002831a12007458d6054801807bb726c16eaa188400903e9993953735084200606128c0ae0382ca9900240fa765b85d0c424c801806cbd082a6ec990649dc0366175dd2644c83200601b303a0a8992c019002432a6250109d36544001290d1128084e9b2a2000948291950407259110004265494c0203b4a888002130a4660105d6624400109952530084eca92200094468c940407454910004a43444a0203a2a488002510a4654109ce424400109852330082ea212200084c29198041754c9100040e35243020baa6488002130a4660105d432440010985232a43a42982200084c2919521d3148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x6
  | 3 => 0x94e
  | 4 => 0x3
  | 5 => 0x98a
  | 6 => 0x98e
  | 7 => 0x2
  | 8 => 0x4
  | 9 => 0x150a
  | 10 => 0x150e
  | 11 => 0x9ca
  | 12 => 0x9ce
  | 13 => 0x168a
  | 14 => 0x168e
  | 15 => 0xa0a
  | 16 => 0xa0e
  | 17 => 0x180a
  | 18 => 0x180e
  | 19 => 0x3c9
  | 20 => 0x3ce
  | 21 => 0xcc9
  | 22 => 0xcce
  | 23 => 0x15c9
  | 24 => 0x15ca
  | 25 => 0x15ce
  | 26 => 0x409
  | 27 => 0x40a
  | 28 => 0x40e
  | 29 => 0x188e
  | 30 => 0xd09
  | 31 => 0xd0a
  | 32 => 0xd0e
  | 33 => 0x1609
  | 34 => 0x160a
  | 35 => 0x160e
  | 36 => 0x1889
  | 37 => 0x188a
  | 38 => 0xd49
  | 39 => 0xd4a
  | 40 => 0x1949
  | 41 => 0x98956
  | 42 => 0x94996
  | 43 => 0x9c956
  | 44 => 0x949d6
  | 45 => 0x180956
  | 46 => 0x95816
  | 47 => 0x1a09
  | 48 => 0xd4c
  | 49 => 0x209
  | 50 => 0x1409
  | 51 => 0xb09
  | 52 => 0x1549
  | 53 => 0x128a
  | 54 => 0x194b
  | 55 => 0x749
  | 56 => 0x289
  | 57 => 0x1849
  | 58 => 0x1489
  | 59 => 0xb89
  | 60 => 0x130a
  | 61 => 0x14c9
  | 62 => 0x134a
  | 63 => 0x2c9
  | 64 => 0xcc996
  | 65 => 0x15c996
  | 66 => 0xec9
  | 67 => 0xecb
  | 68 => 0xeca
  | 69 => 0x1a49
  | 70 => 0x1709
  | 71 => 0x194a
  | 72 => 0x194c
  | 73 => 0x16ce
  | 74 => 0xb8e
  | 75 => 0x184e
  | 76 => 0xcd516
  | 77 => 0x58e
  | 78 => 0xe8b
  | 79 => 0xe8e
  | 80 => 0x178e
  | 81 => 0x18cb
  | 82 => 0x18ce
  | 83 => 0x16c9
  | 84 => 0xcc9d6
  | 85 => 0x1709d6
  | 86 => 0xe89
  | 87 => 0x18c9
  | 88 => 0x589
  | 89 => 0x1789
  | 90 => 0x154e
  | 91 => 0xb49
  | 92 => 0xcd696
  | 93 => 0xd0c
  | 94 => 0x188c
  | 95 => 0x180a16
  | 96 => 0x170e
  | 97 => 0xd0a16
  | 98 => 0x188a16
  | 99 => 0xe8a16
  | 100 => 0x18ca16
  | 101 => 0x130e
  | 102 => 0xd1816
  | 103 => 0x189816
  | 104 => 0xe9816
  | 105 => 0x18d816
  | 106 => 0xcc3d1
  | 107 => 0xcc3d6
  | 108 => 0x3ccd6
  | 109 => 0x74b
  | 110 => 0x40cd6
  | 111 => 0xcd896
  | 112 => 0x188cd6
  | 113 => 0x1895d6
  | 114 => 0xd0416
  | 115 => 0xd1896
  | 116 => 0xe8416
  | 117 => 0x18c416
  | 118 => 0x1a4b
  | 119 => 0x188d16
  | 120 => 0x178d16
  | 121 => 0x189616
  | 122 => 0x18d616
  | 123 => 0x128e
  | 124 => 0xb0e
  | 125 => 0x140e
  | 126 => 0x1a0c
  | 127 => 0x10e
  | 128 => 0x95296
  | 129 => 0x95416
  | 130 => 0x14a
  | 131 => 0x74c
  | 132 => 0x94116
  | 133 => 0x1a0a
  | 134 => 0x74a
  | 135 => 0x40751
  | 136 => 0x160751
  | 137 => 0x74411
  | 138 => 0x150cd6
  | 139 => 0x58751
  | 140 => 0x178751
  | 141 => 0x74591
  | 142 => 0x168cd6
  | 143 => 0x41316
  | 144 => 0x75611
  | 145 => 0x59316
  | 146 => 0x75791
  | 147 => 0xa0296
  | 148 => 0xa1896
  | 149 => 0xa18d6
  | 150 => 0x40116
  | 151 => 0x58116
  | 152 => 0x8e
  | 153 => 0xce
  | 154 => 0x18c40cde
  | 155 => 0x15ccd6
  | 156 => 0x1715d6
  | 157 => 0xece93
  | 158 => 0x15cb16
  | 159 => 0x15d716
  | 160 => 0x15d896
  | 161 => 0x41616
  | 162 => 0x41496
  | 163 => 0x40e96
  | 164 => 0x40d16
  | 165 => 0x188416
  | 166 => 0x161896
  | 167 => 0xd1856
  | 168 => 0xd0596
  | 169 => 0x160116
  | 170 => 0x160296
  | 171 => 0x1618d6
  | 172 => 0x20e
  | 173 => 0x148e
  | 174 => 0x41896
  | 175 => 0xe8ed3
  | 176 => 0x151296
  | 177 => 0x155416
  | 178 => 0x3d716
  | 179 => 0xccb16
  | 180 => 0x160d16
  | 181 => 0xa0116
  | 182 => 0x184116
  | 183 => 0x160416
  | 184 => 0x10416
  | 185 => 0x130416
  | 186 => 0x28416
  | 187 => 0x189856
  | 188 => 0x148416
  | 189 => 0x1849411e
  | 190 => 0x5988cde
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 38
  | 7 => 1266
  | 6 => 5082
  | 5 => 3194
  | 4 => 269
  | 3 => 24
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
  | 8 => packedAt gbK8 (1142+((h/22+packedAt gbK8 (988+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (52364+((h/502+packedAt gbK7 (46842+(h % 502)*11) 11) % 1809)*12) 12
  | 6 => packedAt gbK6 (269169+((h/1941+packedAt gbK6 (243936+(h % 1941)*13) 13) % 7687)*14) 14
  | 5 => packedAt gbK5 (203721+((h/1175+packedAt gbK5 (188446+(h % 1175)*13) 13) % 6815)*13) 13
  | 4 => packedAt gbK4 (19703+((h/97+packedAt gbK4 (18830+(h % 97)*9) 9) % 425)*10) 10
  | 3 => packedAt gbK3 (1992+((h/8+packedAt gbK3 (1944+(h % 8)*6) 6) % 49)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f0f03c3fc3ff0ff01ffc07f0b1d9cc19f673
  | 1 => 0xfc0f003fc3fc3ff0ffe03ff8015e2e70667b9c
  | 2 => 0xffffffc003ffc3ff00003ffffe60307f878c1f
  | 3 => 0xffffffc0003ffffffc0000f803f83f80fe0
  | 4 => 0xffffffffffc00000000000fffc003fff000
  | 5 => 0xfff0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2090200c04c06501904aa412a010c8c408b231
  | 1 => 0x2482001441442910a540a95020160a50225294
  | 2 => 0xcb255640022a82aa008112a546603029850c0a
  | 3 => 0x41099aa2a80002cc4a9500204b803502d00d40
  | 4 => 0x820eed3b33b31000030600c18deb40037fe000
  | 5 => 0xf3c00e02202220888c1823060ffdbffc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37203
namespace PEqualNP.Outside.L_meta_37203
open PEqualNP.Outside.L_meta_37203.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
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
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 1 := bs4_2_0
theorem alls4 : ∀ k ≤ 2, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 14 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 19 := block_range (n:=19) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 467 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 634 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 24 := bgb_3_0
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
theorem bgb_4_256 : Interval gbAtlas 4 256 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 269 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256))))
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
theorem bgb_5_3168 : Interval gbAtlas 5 3168 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3194 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))) (concat (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))) (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)))))) (concat (concat (concat (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)))) (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368))))) (concat (concat (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560))) (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)))) (concat (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944))) (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)))))))
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
theorem bgb_6_5056 : Interval gbAtlas 6 5056 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5082 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))))) (concat (concat (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)))) (concat (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))))))) (concat (concat (concat (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656))) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136))))) (concat (concat (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)))) (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)))))) (concat (concat (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416))))) (concat (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736)))) (concat (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))) (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))))))))
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
theorem bgb_8_32 : Interval gbAtlas 8 32 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 38 := (concat bgb_8_0 bgb_8_32)
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 3 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0feeeeee0fee8eee0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4276678368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37203.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,4]⟩,⟨.and,[4,5]⟩,⟨.or,[2,7]⟩,⟨.or,[3,8]⟩,⟨.and,[2,3]⟩,⟨.or,[6,9]⟩,⟨.and,[4,10]⟩,⟨.and,[1,9]⟩,⟨.or,[12,13]⟩,⟨.or,[0,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276678368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276678368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37203

open PEqualNP.Outside.L_meta_37203 in
theorem PEqualNP.Outside.L_meta_37203 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4276678368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4276678368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
