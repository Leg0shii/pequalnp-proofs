import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37085.Model
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


end PEqualNP.Outside.L_meta_37085.Model

namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
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

def SBf (j : Nat) : Nat := [7, 7, 3, 5, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37085

namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x160c080119334046a62c0c0213018800622151e1e00a1514480242ebc880040000000883b0009c02d3a145a836b9000129401f327000052015801c002c4800c2010116000062600000ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12590f00000000000092001c801400000000ee20090204c722a1ac8403000fc4a6d3d288c89e1f14c8c8d0c12814003f290c0653f8012a5f24275269f001343a5003a58f8000b0005c340003cb47b0d115040015111146a261a51c9044031363346200568314938ec13030002e002005142571e8d4e000190b4c43c4e198f227000452e023a870b85d059c4326f11a1c8e31279d0a2910692c5e5b448151e28218003e3620810d0844d20470860d9781c551d94874241b96130993c0000000318002aa3458000010371f4002c491580021308050a304a00000730019c446c000e010380060207801203800002800006020001840c80078102848d80050d04028c830088850280000a82840208850181070081018484cf54b439f28e873e50d0e7aa921ddd4543ba28a879f5350e7ea4a1edd45439e28a87b45150e68a2a1cf141439f2a0875e53d0abaa7a16794f429ea9e859d53d0a3aa7a14f947429f286853d5490a7ea6a16bd49429e28a853c5050a7ca8214f953329eaa6653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86195794f41aea9e833d539067aa520cf946419f284835f53506b8a6a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc7688398cfd52319e2a4639f438c73a8718e7d5231ce2a4639f428c73a8518d794631cf20c639c418c67ea898cf151319f2a0633d540c73e8618e750c31da208639e540c73aa818e7d0831cea10635e510c7aca218f5d0431cf208639c410c7a88218e5104319f2a6433d54c86bca790d754f219faa4433c54887a86310cfd51219e2a2435f53486b8a690f50c521bda824378504867ca810cf550219ea9c813d529027ca320678c640ce18c813e50902bca6205754c40cf298813d531033aa6204754c409ea90813e511033c6220670c4409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca9084f55210af29c215d53843a863084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a808750c410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x75c9500840294a00f2d000170000000200000000701c59700e80940028037008db2700bc0001200000004960c4c4d58662ed9181a0120000002000a88c801ca801a0640d803e440006a599a80021a00043d800380c140000e00080140040000001820004004c5d4c5150f1763145439518553d0a346154f42a518553d0b176154f428718553d0b146154f428518553d0a1d6314142a5185438cb1543946328758e544ca3461551328e181544ca946150c3287d8d529061d63942418b588548c69661d5231a3588548c696611523187997428c635651043187597420c6946150831a5986410c6976510431a5594410c6956210431a5980410c61d6315221c51503188714540c521d40c4504861d639502187d8d5290316510c6409518553102346154c40a518553103176154c408718553103146154c4085185531021f658c4408759431102946150f308d987548c21c6550d30a5185434c30d4314930c550c514c21d63953208758c548821d6395310c5950318421d63150108b5885404314540c410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x60800810c00000050000449c300283396c628a87051c5631414290ae5b288218c147158e540860b38ec6a9481411c54314930828e2b1ca9904147158c548820abb0a818821415c8540c410
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt s0K2 (505+((h/3+packedAt s0K2 (490+(h % 3)*5) 5) % 22)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 3 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1142108c48824810052ca8a25012915414b0b5
  | 2 => 0x24c52914392484a960556454b6412a0cca565c
  | 3 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x195a016000078ea640a0a803e389a9421c108445808a2e4159a0000c23180000f000128b1a002090c709244ea829b280c8953c004c1000c02c0146042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x490624002e221400006a7200006e5b25424f273900450b4d00031d093b54351f6521122a07576c2d3123081b2c00000000361c603e002851406f4317640f480c520070200011623456005e1e5971192602154c470038675f7400186600584e6d4a2f6101040e3d3a4133304b63503f05556816696b133c00105d0d29375c4600322b001a0073440000535a0a00020001878303810984808d0085050500000002018000800483871d81008380060200860c01965b94b43b6a96877651d0eeaa3a1d794f42aea9e857651d0aeaa3a15dd4532ba28a65cd320cabca7a0d754f41b7296836d52d06bea6a0d714d41b7a92836c52506f6a0a0de14141b7296636d52cc6bca318dbd4931b6292633e540c67aa818e795031ceaa0635e510c7aca218f590431eaa08635e53c86baa790f50c721b728c43ce31887986310d7d4d21ae29a433e540867aa810f50c421d72a043ad54086dca210f994421f320843e541087ce6210f38c421e618843e431087886210e78c640ce18c81ae219035843204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2206d54440cf188819c311035c42206b084409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206215e53842baa7085b94a10b6a9421d431843c843084fd51109e2a2215f53442b8a6885bd4910b629221d431043c842086e10010
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2c08c11242a5801ae70a92622850000001800e00069e8a04a00004ca2b1185320cac46250431b4181410c715540c421b118d41086e06050421b198631086a5640c421e19903108785640c421e19503108785540c421e10c421903155354440c9549511021d650c4408b5942110384310844099185520c2546154c20d194831843465308610e40c440043a02110010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x60200020000a0aeb3206210c85769503108682ba86210881815943108440
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (826+((h/15+packedAt s1K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s1K4 (3471+((h/39+packedAt s1K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s1K3 (952+((h/8+packedAt s1K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (200+((h/1+packedAt s1K2 (196+(h % 1)*4) 4) % 15)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 2 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 2 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
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
  | 0 => 0x5fc7ff3c7ffe03fc
  | 1 => 0xffffffffffffffffffffffeff8e7ff8e0ffccf
  | 3 => 0xfffffffffffffffffffffff7ff07fff00fff0f
  | 5 => 0x7bfff83ffff00ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2072404c1262615c
  | 1 => 0xffffffffffffffffffffff90960a1484a4a4c5
  | 3 => 0x920d42921494b0a
  | 5 => 0x60486b249818ea0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 43 s2Pos s2Neg, 0xeeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
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
  | 0 => 0xfe07ffffff01ff81fffff03fffffc07e7e3fc7
  | 1 => 0xfff80fe03ffe07fe0f81ffc1f80fff81b3ccf8
  | 2 => 0xfffff0003ffffffff001fffe000fffffc3f0ff
  | 4 => 0x3ffffffffffe0000000ffffffc00ff
  | 5 => 0xffffffffc00007fffffffffffff00001ffff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1230a145011c1180318a310a68e2ca2a1615c3
  | 1 => 0x5452628d5224739606a8d54971255aa8b2ccd8
  | 2 => 0x88a144d1a448a4aad04169ac2249a34d43706d
  | 4 => 0xd1c58b1e3891474d6b6c0c21448e3c71fc00b6
  | 5 => 0xe1060c1830e186718c718e3187003041e9aa00
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e00000eaeaeaeae0e00000eaeaeaeae0e00000eaeaeaeae0e00000eaeaeaeae0e00000eaeaeaeae0e00000eaeaeaeae0e00000eaeaeaeae0e00000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5e4402600fc0003ef859d42b89ab0019a0034a878012c519b5a000006a6002214340000000801005de39000190776a00000001c244a00c8328b003a0000e120a38f006e302332ca41156c218207a0002710020800608041800a041090a0c0810000081b7a92876c5250eeea2a1dd14543bda8287785050edca421db54843bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41b7294836d52906f4a120de54241b7a92636c524c67ca818cf55031b7290636d520c6f4a018de54031afa9a435c53486f4a010de54021b7a92816c52502bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc2dca5985b54b30b7294616d528c2eca3185d546309faa2413c54482eca2105d544209faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (731+((h/13+packedAt s4K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s4K4 (1875+((h/21+packedAt s4K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffe03ff8307fc3fe0fffff83fe0138fe7c
  | 1 => 0xf01f83ffc1ffff83fc3ff0780ffc1ffecf338f
  | 2 => 0xffe003fffe003ffc003fff800fffe0030fc3f0
  | 3 => 0x3ffffffffffffc000000ffffffff003ff
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x614510238411500cc04642a8e590aa2818563c
  | 1 => 0x24c214448ca11281441a523122948c984b3285
  | 2 => 0xc28b5a891875b5b4222d6b224b5ac8530dc3d0
  | 3 => 0x8b1463122144295aaa8108048c631163b0016a
  | 5 => 0xc18421c31862e6333318c4700420183e6a800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00eeeaeeeaec00ec00, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x15360000b4e283985894d29541001900010030a3d108008cb892458f263a7120120ac014043802d3e4c00c0c008a800846820900c80192001c10c1044ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fb20fe20fd20fc20f820ff10fe10fa10fd10f910fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xbc4d68f44400009c00006124f8000000c4000008d96058013c2001180138a0a46c007c015090000000e81430691c0078017530b8000000e50c1c058500007000015c014800242800000000000000ad34012099708c0000000084a880cd0940c180b400555564b0000c480038000000e040000095443558002c100000005064756d28000018897ced88fc00f05d2c003cd00000c8011178dc00d54d15040c000a02041c0004000a0804060804000200000002020802000e060204000404036f5250ed8a4a1ddd4543ba28a877b5050ef0a0a1de94043bca80877a50d0af2a1a14f94a42bda8285785050a7ca4216b948429f2a6653d54ccb5885995e94332bca86653f544ca78a8995dd4532ba28a657b504caf0a0996b10832b7294836d52906f4a120de54241bd280837950106f4a118de542319f2a0633d540c6dca418db54831bd2806379500c7588590cf952219eaa4437a50886f2a110cfd51219e2a2435f53486b8a690eb10921bda82437850486f4a010de54021b7a92816c52502eca3185d546309f2a0613d540c37485906e10b20bca8e413e548827aa9106b10a20bd284413f5448278a8906b10820bb288417551082f4a4107a94820f5a1041ba420837084107a10820d421041f251082f2a2107c54420b8a88417a52842f0a5086e90a10dc214217951842f4a4885e14910dd21221b842443e6a2887ccc510f818a21f221443e242885e94010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1c00028090021000439e4860008803000205800000a6614a1a2000020400f2842943329c58650ccb0c5310921ca108504862c6255030c910951082aa6290820e810a51083284254420e810951083634254420cc90951083304254420d810951083204254420ca14842843285210910b858831442706548510b418d21443a04248510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2806204258650ccb103288490a21a018c4248510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 157)*8) 8
  | 3 => packedAt s5K3 (840+((h/7+packedAt s5K3 (798+(h % 7)*6) 6) % 33)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81fff01fff0383f0f83f07ff0ffe02331e7c
  | 1 => 0xfffe03ffe07ffffc00fffff81ff07ffc3fe38f
  | 2 => 0xfffffffff8003ffff003fffffff8003c3fff0
  | 3 => 0xf00003ffffffffffffffc0001ffffffffc03ff
  | 4 => 0xfffffc00000003ffffffffffe0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa8ac2b11c512d780b83e0ba6ab4aea2a330e3c
  | 1 => 0x6104992243245194004a55aa85522c98176285
  | 2 => 0x421850448a0e18ad51002630d6630850c1b7d0
  | 3 => 0x885162891048824a6a948004188c516368016a
  | 4 => 0xc61830e1c70e3738ce738c700086183bed800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00fce0ec00, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x11152f029a7a3178f0001c0000d401e56010001285cb1580400a5c2c0263e183b06e21a363649533486513b06000322a0022d289403a5040b964660e0d263801d4e060468510380000a0c4800e08700263ca00027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4801fe52007f54809fc5201ffd0801fe42006f90801fd4201ff10801bc42007fcc801fe32007f4c801fc32027fd4405fe51007f54405fc5101ffd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21027fd4003fe50007f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a4000dfd9520004feca90027fe65480097f32a4000ff59520005faca90027fc65480097e32a4000df19520024f8ca90003ff64480017fb224000efd91200057ec890023fe64480077f3224000ff59120005fac890023fc64480077e3224000ef1912001d78c890027ff5448011ff2a24000ff55120047f8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c690027ff5348001ff29a4000ff54d2004ff8a690023ff4348001ff21a4000ff50d20047f88690006ff6248013ffa924000ff94920007dca490003fd5248001f6a924009ff14920047fe8490003fe4248001df2124000ff50920047f88490003bc4248001ff9924000ff8c920007fa6490003fc3248001ffb0a4000bfd852003ffcc29000afe6148001feb0a4007ff18520015f8c290027ff514800fff28a4000ff5452003ff8a290023ff414800fff20a4000ff5052003ff88290003ff314800fff18a4000ff4c52003ff86290003ff214800fff10a4000ff4852003ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024000fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff82090003ff65440017fb2a2000dfd9510004feca88017fe65440097f32a2000ff59510005faca88017fc65440097e32a2000df19510024f8ca88003ff64440017fb222006ff9911001dfcc888003fd64440017eb222006ff1911001df8c888017ff544400dff2a22000ff55110037f8a888003ff63440017fb1a2000ff98d10005fcc688003fd63440017eb1a2000ff18d10005f8c688017ff5344001ff29a2000ff54d1002ff8a68801bff4344001ff21a2000ff50d10037f88688003ff62440017fb122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488017ff5244001ff2922000ff5491002ff8a48801bff4244001ff2122000ef90910007fa848801bfc4244001de2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510007eaa28800bfc5144005ffa0a2002ff90510017fa828800bfc4144005ff98a2000fdcc510017fc628800bfd3144005fe18a2002fd0c510017fe428800bfe2144005fb10a2002ff48510007ea428800bfc21440037fb022001ffd411002ff6a088007fe5044003fea822001ff1411000ff0a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd31cc023fe18e6000ffc8730087fc4398003fd21cc021fe10e6001bf5833000ffea198007fe50cc003fea866001ff1433000ffe8198007fe40cc003fea066001ff1033000ffc6198007de30cc003fd1866001ff0c33000fb86198007fe20cc003fe1066001ffc433000ffc2198007fc10cc001ffb2a6000bfd953007ffcca98012fe654c001feb2a6000bf5953007ff8ca98012fc654c001ffb226000bfd9130077fcc89800efe644c001feb226000bf59130077f8c89800efc644c01fffaa2600eff95130007faa89803bfc544c0037fb1a600fffd4d30007fca698003de534c001fea9a6000f754d3007ff8a69803bff434c001ff21a6000ff50d30077f88698003ff624c0017fb126000ff98930007fac498003fc624c0017e312600fffd4930007fca498003fd524c01ffe292600effd0930007fc8498003be424c001fea12600eff10930007788498003ff324c001ff1926000ff4c930007f86498003ff614c0017fb0a600dff98530015fcc298003fd614c01bfe30a6002bf1853007ffea298037fe514c001fea8a600dff14530077fe8298037fe414c001fea0a600dff10530007fe6298037fe314c001fe98a600dff0c530007fe4298037fe214c001fe90a600dff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c001fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffc4098007fc204c003ff8826001ff8413000ff42098007fc104c001ffb2e4000bfd9720057fccb90012fe65c8001feb2e4000bf59720057f8cb90012fc65c8001ffb264000bfd9320067fcc99000efe64c8001feb264000bf59320067f8c99000efc64c8015ffaa6400cff95320007faa990033fc54c8001ffb1e4000bfd8f20007fcc790002fe63c8001feb1e4000bf58f20007f8c790002fc63c8015ffa9e4000ff94f20007faa79002bfc53c8019ffa1e4000ff90f20007fa8790033fc43c80037f316400affd4b20007fca590003ee52c8001fea964000fb54b20057f8a590033ff42c8001ff2164000ef90b20007fa8590033fc42c8001de2164000ffccb20007fc6590003fd32c8001fe1964000ffd872005ffcc39000afe61c8001feb0e4000bf5872005ff8c39000afc61c8015ffa8e400bff94720007faa39002ffc51c8019ffa0e400bff90720007fa839002ffc41c8001ff98e400bff8c720007fa639002ffc31c8001ff90e400bff88720007fa439002ffc21c80037eb064001ffd4320057f6a190007fe50c8003fea864001ff1432000ff0a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71064001fe8832000ff84190007ec20c8003ff8864001ff8432000ff82190003ff65480017fb
  | 2 => 0x50005f8c4a8013ff5254009ff292a004ff54950027f8a4a805fff4254001ff212a000ef90950007fa84a805ffc4254001de212a000ffcc950007fc64a8003fd3254001fe192a000ffd8550005fec2a805bfe61540057f30aa000ff585500b7f8c2a800afc6154009ffa8aa004ff94550027faa2a8013fc515402fffa0aa016ff90550007fa82a805bfc4154001ff98aa016ff8c550007fa62a805bfc3154001ff90aa016ff88550007fa42a805bfc21540037fb02a001ffd4150027f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff880a8007fe3054003fe182a001ff8815000ff840a8007ff1054003ff082a001ff04150007fecaa0002ff655002bff32a8004bf99540007facaa0002fd655002bfe32a8004bf1954000dfec8a000fff5450007ff2a28003ef9514001ffaa8a0003bd5450007fe2a28000ffd8d40005fec6a0003fe6350001feb1a8000ff18d40005f8c6a0057ff5350001ff29a8000ff54d400aff8a6a000fff4350007dfa1a8003ff90d4001ffa86a0003bd4350007fe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a0057ff5250001ff2928000ff549400aff8a4a000fff4250007ff2128000ef9094001ffa84a000ffc4250007de2128000ffcc940007fc64a0003fd3250001fe1928000ffd8540005fec2a0053fe61500057f30a8000ff585400a7f8c2a000afc615002bffa8a8014ff94540007faa2a0053fc5150007ffa0a8003ff9054001ffa82a000ffc4150001ff98a8014ff8c540007fa62a0053fc3150001ff90a8014ff88540007fa42a0053fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd014001ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff1828001ff0c14000ffc40a0007fc2050003ff8828001ff8414000ff820a0047ff65cc0017fb2e6013ff99730025fccb980037e65cc0093f32e6000ff59730005facb980037d65cc0013eb2e6011ff19730025f8cb98047ff64cc0017fb266012ff9933001dfcc998003fd64cc0017eb266011ff1933001df8c99804fff54cc025ff2a66000ff55330097f8a998006fe63cc027ffa9e6011ff94f30007bca798003fd53cc001eea9e6011ff14f30097fe8798047fe43cc001fea1e6011ff10f3008ffec598003fe62cc0017f3166000ff58b30005fac598047fc62cc027ffa966000ff94b30007faa59804ffc52cc025ffa166000ff90b300077c8598003fd42cc025fe2166000ef10b3008ffe6598003fe32cc001fe9966011ff0cb3008ffec398043fe61cc0057f30e6000ff58730005fac398047fc61cc0057e30e6013ffd4730087fca398003fd51cc021fe28e6012ffd0730087fc8398003fd41cc021fe20e6011ffcc730087fc639800
  | 3 => 0xeb2e4200bf597210eff8cb90812fc65c8401ffb264200bfd93210e7fcc99080efe64c8401feb264200bf593210e7f8c99080efc64c843bffaa6421cff95321007faa990873fc54c8401ffb1e4200bfd8f21007fcc790802fe63c8401feb1e4200bf58f21007f8c790802fc63c843bffa9e4200ff94f21007faa790877fc53c8439ffa1e4200ff90f21007fa8790873fc43c84057f316421dffd4b21007fca590803fd52c843bfe296421cffd0b21007fc8590803be42c8401fea16421cff10b21007788590803ff32c8401ff1964200fb8cb21007fa6590803ed32c8401fe1964202bf58721017fea39080bfe51c8405fea8e4202ff14721017fe839080bfe41c8405fea0e4202ff10721017fe6390803f731c8405ff18e4202ff4c721017f8639080bf431c8405ff10e4202fb88721017ec439080bfc21c8405f610e4200ffd83210dffcc190806fe60c8401feb064200bf583210dff8c190806fc60c843bffa86421bff943210dff8a190873ff40c8437ff206421bff103210dffc619086ffc30c8437ff106421bff08321017fe219080bfe10c8405fe0864200ffd9521005feca9086bfe65484097f32a4200ff59521005faca9086bfc65484097e32a4200ffd9121005fec890803bf64484015fb224219ff9912101dfcc890803fd64484017eb224219ff1912101df8c890803bc64484075e322421affd51210cffca890803fd5448433fe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a421affd4d21007fca690803fd5348435fe29a4219ffd0d21007fc8690803fd4348433fe21a4202bfd89210d7fea490803fe5248401fea92421aff149210cffe8490803fe4248401df2124200ff509210cff88490803bc4248401ff9924200ff8c921007dc6490803fd3248401f69924200ff0c921015fec29080bff5148405ff28a4202ff54521017f8a29080bff4148405ff20a4202ff50521017f8829080bff3148405ff18a4202ff4c521017f8629080bff2148401fb90a4202ff88521017dc429080bfc2148405f610a4202fd08521007fec090802ff6048431ff3024201bf98121007fac090863fc60484037e302421affd41210c7fca090863fc5048433ffa024218ff901210c7f88090863fe3048431fe1824218ff881210c7f8409080bff1048405fb8824202ff84121017f82090806ff6554001ffb22a000bfd91500bffcc8a800efe6454001feb22a017ff1915001df8c8a8013ff5454009ff2a2a004ff55150027f8a8a8003ff63540017fb1aa000ff98d50007fac6a8003fc63540017e31aa004ffd4d50027fca6a8013fd5354009fe29aa017ffd0d50007fc86a8003fd435402ffe21aa000ffd8950005fec4a8003fe6254001feb12a000ff189
  | 4 => 0x80ffd4250407fe2128203ef10941007fe64a0803fe3250401fe9928200ff0c941015fec2a080bff5150405ff28a8202ff54541017f8a2a080bff4150407fba0a8202ff905410177c82a080bfc4150405de20a8202fd10541017fc62a080bfc3150405ff10a8202ff08541007fec0a0802ff6050449ff3028201bf98141007fac0a0893fc60504037e3028225ffd4141127fca0a0893fc5050407ffa028203ff9014101ff880a0893fe3050449fe1828224ff88141127f840a080bff1050405ff0828202ff0414108ffecb98802ff65cc447ff32e6204bf99731007facb98802fd65cc423fe32e6204bf1973108ffec998802ff64cc445ff3266203bf99331007fac998802fd64cc423fe3266203bf1933111ffea99888bfe54cc401feaa66222ff15331015fcc79888fff53cc423ff29e6200ff54f3108ff8a79888bff43cc423ff21e6200ff50f3108ff88798847ff62cc401ff3166200bf98b31007fac598802fd62cc423fe3166223ffd4b31007fca598803fd52cc447fe2966222ffd0b31007fc8598803be42cc401fea166222ff10b31007788598847ff32cc401ff1966200ff4cb3108ff8659880afd61cc405ffa8e6202ff94731017faa39880bfc51cc405ffa0e6202ff90731017fa839880bfc41cc405ff18e6202f78c731017ec639880bfc31cc405ee18e6202ff88731017f8439880bf421cc423ffb066221ff9833100dfcc198803fd60cc4017eb066211ff1833100df8c19888fff50cc443ff2866221ff14331117fe8198887fe40cc443fe2066221ff8c33108ff86198887fe20cc443fe1066202ffc4331017ee219880bfe10cc405fe0866200ffd9531005feca98883fe654c4097f32a6200ff59531005faca98883fc654c4097e32a6200ffd9131005fec89887ffe644c4077f3226200ff59131005fac89887ffc644c4077e3226220ffd51310fffca898803fd544c43ffe2a26202bfd8d31107fea698803fe534c401fea9a6220ff14d310fffe8698803fe434c401fea1a621fff10d31007fec498802ff624c401ff3126200ff58931007f8c498802fc624c441ffa926200ff94931007faa498883fc524c43fffa126200ff909310077c8498803fd424c43ffe2126200ef10931007fe6498803fe324c401fe9926200ff0c931015fec29880bff514c405ff28a6202ff54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c401fb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fc429880bfc214c401ffb026200bfd81310f7fcc098806fe604c401feb02621eff1813100df8c098883ff504c43dff282621eff141310fffe809887bfe404c43dfe202621eff8c1310f7f8609887bfe204c43dfe1026202ffc4131017fc209880bfc104c401ffb2e4200bfd97210effccb90812fe65c8401f
  | 5 => 0x813216ffe20990b3fe104c859fe0826411ffd9432005feca190affe650c8097f3286400df99432024fcca19003fd650c8017eb286400df59432004faca19047fc650c8097e3286411ffd9032005fec8190abfe640c8077f3206400ff59032005fac819047fc640c8077e320642bffd5032157fca819003fd540c855fe2a06400bf98c3215ffea619047fe530c801fea986411ff14c32157fe8619047fe430c801fea186411ff10c32005fcc4190afff520c801ff2906400ff5483215ff8a4190abff420c801ff2106400ef90832007fa84190abfc420c801de2106411ffcc832007be6419003fe320c801f71906400ff4c832007ba6419003ed320c823ffb086429ff98432015fcc219003fd610c8017eb086411ff18432015f8c2190afff510c853ff2886429ff14432157fe82190a7fe410c853fe2086429ff8c43214fbc6219047fc310c853ee1886429ff8843214ff84219047ff600c851ff3006401bf98032007fac019002fd600c823fe3006401bf1803215ffea0190a3fe500c851fe280642affd0032147fc80190a3fc400c851ff1806411ff0c032147fc40190a3fc200c853ff8806428ff84032147f8201900aff6554401ffb22a200bfd915113ffcc8a880efe6454401feb22a227ff1915101df8c8a8813ff5454409ff2a2a204ff55151027f8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc63544017e31aa204ffd4d51026fea6a8813fe5354409fea9aa200df54d51027f8a6a889fff4354401ff21aa200ff50d5113ff886a8803ff62544017fb12a200ff98951007fac4a8803fc62544017e312a204ffd4951027fca4a8813fd5254409fe292a227ffd0951007fc84a8803be4254401fea12a227ff109510077884a8803ff3254401ff192a200ff4c951007f864a880aff6154405ffa8aa204fdd4551017fca2a880b7e5154405fe28aa202df14551017e8a2a880bff4154405ff20aa202ff10551017fc62a880bfc3154405ff10aa202ff08551007fec0a8802ff605444dff302a201bf98151007fac0a889bfc60544037e302a204ffd4151027fca0a8813fc505444fffa02a226ff90151137f880a889bfe305444dfe182a226ff88151137f840a880bff1054405fb882a202ff84151017f820a8803ff65504017fb2a8225ff99541025fccaa0803fd65504017eb2a8225ff19541025f8caa080aff6450407ffaa28203ff9514101f7ca8a080ffd5450401deaa28203ff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a0802fc635044bffa9a8200ff94d41007faa6a0897fc5350407ffa1a8203efd0d4101ffc86a080ffd4350401dea1a8203ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0802fc625044bffa928200ff94941007faa4a0897fc5250407ffa128203ff909410077c84a0
  | 6 => 0xdfe2a66437ffd4f3208ffca799003fd53cc823fe29e6436ffd0f3208ffc8799003fd43cc823fe21e6437ffd4b32007fca599003fd52cc86ffe2966436ffd0b32007fc8599003be42cc801fea166436ff10b32007788599047ff61cc86bff30e6402bf98732007fac399002fd61cc823fe30e6402bf187321bffea3990d7fe51cc86bfe28e6436ffd07321affc83990d7fc41cc86bff18e6411ff0c7321affc43990d7fc21cc823ffb066434ff9833200dfcc199003fd60cc8017eb066411ff1833200df8c1990dfff50cc869ff2866434ff143321b7fe81990d3fe40cc869fe2066434ff8c33208ff861990d3fe20cc869fe1066435ffc43321a7fc21990d3fc10cc801ffb2c6400bfd963219ffccb19012fe658c801feb2c6400bf5963219ff8cb19012fc658c801ffb246400bfd9232197fcc91900efe648c801feb246400bf59232197f8c91900efc648c867ffaa46432ff95232007faa9190cbfc548c8017eb1c6433ffd4e32007fca719003fd538c867fe29c6432ffd0e32007fc8719003fd438c865fe21c6400bf98a3219ffea519003fe528c801fea946433ff14a32197fe8519003fe428c801df2146400ff50a32197f88519003bc428c801ff9946400f7cca32007de6519003ff618c863ff30c6402bf98632007fac319002fd618c863fe30c6402bf1863219ffea3190c7fe518c863fe28c6432ffd063218ffc83190c7fc418c863ff18c6431f78c63218ff863190c7dc318c863ff10c6431ff08632007fec1190c3fe608c8037f3046400ff58232005fac1190c3fc608c8037e3046433ffd4232187fca1190c3fc508c865ffa046430ff90232187f881190c3fe308c861fe1846430ff88232187f841190c7ff108c861ff0846430ff04232007feca99002ff654c85fff32a6404bf99532007faca99002fd654c85ffe32a6404bf19532007fec899002ff644c801dfb226400afd9132177fcc89900efe644c801feb226400bf59132177f8c89900efc644c801de3226403af1913217ffea8990bbfe544c801feaa2642eff1513217ffea699003fe534c801fea9a642fff14d32177fe8699003fe434c801fea1a642eff10d3217ffea499003fe524c801fea92642fff14932177fe8499003fe424c801df2126400ff50932177f88499003bc424c801ff9926400fbcc932007fc6499003de324c801ffb0a6400bfd8532007eec299002f7614c85bff30a6402bf98532007fac2990b7fc614c8057e30a6400fd18532015e8c2990bfff514c85bff28a642dff14532177fe82990b7fe414c85bfe20a642dff8c53216ff862990b7fe214c85bfe10a6400ffd8132005fec0990b3fe604c8037f3026400ff58132167f8c099006fc604c85fffa82642cff94132167f8a0990bbff404c859ff202642cff10132167fc60990b3fc304c859ff102642cff0
  | 7 => 0x210fffc5190807ffa0c8403efd064201ffc83210ffbe4190807fe20c8403ef106421fffc63210fffc319087fff10c843fff08642007fec1210fbfe60908037f3048400ff58242005fac1210fbfc60908037e3048440ffd42421f7fca1210fbfc5090807ffa048403efd024201ffc81210fbbe4090807fe2048403ef102421f7fc61210fbfc309087dff104843eff082421fffe21210fbfe109087dfe0848400efd96422077ccb21003bd6590881de32c8400efd8e420077cc721003bd6390801de31c8440efd4e420077ca721003bd5390881de29c8403af98a422077ea521003be5290801dea948440ef14a420077ec3210ffbe6190801deb0c843fef186422077ea3210ffbe519087fde28c843fef8c6421ff7863210ffbe219087fde10c8400efd82421f77cc121003bd609087dde3048440efd42421f77ca1210fbbc509087ddf184843eef0c2421f77c41210fbbc209087fdf884843eef842421f7782121003ff65508017fb2a843dff99542025fccaa1003fd65508017eb2a843dff19542025f8caa100eff6450807ffaa28403ff9514201ffaa8a100ffc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8400bf18d421effea6a1003fe5350801fea9a843dff14d4201ffe86a100ffe4350807fea1a8403ff10d4201dfec4a10f7ff5250801ff2928400ff549421eff8a4a100fff4250807f7a128403ff909420077c84a100ffc4250807de2128403fb10942007fec2a1002ff6150879ff30a8402bf98542007fac2a10f3fc61508057e30a843dffd45421e7fca2a10f3fc5150807ffa0a8403ff9054201ff882a10f3fe3150879fe18a843cff885421e7f842a1003ff60508017fb02843bff9814200dfcc0a1003fd6050877fe3028401bf181421effea0a10effe5050877fe2828403ffd014201ffc80a100ffc4050877ff182843bff0c1421dffc40a10effc2050879ff882843bff841421dff820a100fbf6510807df3288403cf9944201f7aca2100f3d6510807de3288403efd8c4201f7cc62100fbd6310807de318843aefd4c420077ca621003bd5310875de2988403ef988420057cc42100fae6210875dfa908400ef948420077aa4210ebbc5210807dfb088403ef9844201f7ac22100fbc6110875dfa888439ef944421cf78a2210e7be3110873de1888439ef884421cf78422100fbf6010807df3008403ef5804201f78c0210ebbf5010871df2808438ef140421c77c60210e3bc3010871df1008438ef080421cf7e20210e3be1010871de0808411ffd9732005fecb990dffe65cc8097f32e6400ff59732005facb99047fc65cc8097e32e6411ffd9332005fec9990dbfe64cc8077f3266400ef9933201d7cc999003fd64cc8017eb266400ef593320057ac999047fc64cc8077e3266437ffd53321b7fca999003fd54cc86
  | 8 => 0xf9014301ff880a191ffe3050c8ffe1828647ff8814323ff840a1923ff1050c8fff0828647ff04143025facb29003ff649488dff324a403bf99252007fac929002fd649488dfe324a403bf19252027fea929013fe5494809feaa4a404ff15252007fec729003fe63948017f31ca400ff58e52005fac729003fc6394809ffa9ca404ff94e52027faa729013fc539488dffa1ca400ff90e52007fa872911bfc43948097f314a404ffd4a52026fea529013ef5294809b7a94a404ff14a52027d8a52911bff429488dfe214a400ffd865222ffcc32900afe6194801feb0ca400bf5865222ff8c32900afc6194809ffa8ca404ff94652027f8a32911bff419488bff20ca445ff1065222ffc6329117fc319488bff10ca445ff08652007fec129113fe60948037f304a400ff58252005fac129113fc60948037e304a404ffd4252027fca1291137e5094809fe284a404df14252237fe8129113fe4094889fe204a444ff8c252227f86129113fe2094889fe104a445ffc4252227fc2129113fc10948097fb2aa400ffd9152005fec8a9003bf64548015fb22a443ff9915201dfcc8a9003fd6454887fe322a403bf1915200778c8a900ebc6454809ffaa2a404dfd5152027fca8a9013fd5454801beaa2a404ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9002fc6354809ffa9aa404dfd4d52027fca6a9013fd5354801bea9aa404ff14d5221ffe86a9003fe4354801fea1aa443ff10d52025fec4a9013ff5254809f7a92a404ff94952006fca4a9013fc5254809be292a404fb1495221ffe84a910ffc4254801ffb0aa400bfd8552217fcc2a900afe6154801feb0aa442ff18552015f8c2a9013ff5154809ff28aa404ff1455221ffe82a910bfe4154885fe20aa442ff8c552217f862a910bfe2154885fe10aa400ffd8152005fec0a9003fb60548017db02a441ff9815200dfcc0a9003fd6054883fe302a401bf18152007f0c0a9006f86054809ffa82a404ff94152027f8a0a910fff4054883ff202a441ff1015220ffc60a9107fc3054883ff102a441ff08152217fe20a9107fe1054883fe082a400ffd9642005fecb21103fe65908097f32c8400ff59642005facb21103fc65908097e32c8403bf5924201ffea921103bf5490807ff2a48403ef9524201ffaa921003bd5490807fe2a48403ef15242007fec721003fe63908017f31c8400ff58e42005fac721003fc6390881ffa9c8400ff94e42007faa721103fc5390807ffa1c8403efd0e4201ffc8721003be4390807fea1c8400ef50e4201ff8872100fbc43908077f3148440ffd4a42007fca521003fd5290881fe2948403ffd0a4201f7e852100fef4290807fe2148403fb10a42007fec3210fffe61908057f30c8400ff58642005fac3210fffc61908057e30c8440ffd46421fffca3
  | 9 => 0xca1ff204a650ff10253287fc6129847fc3094ca1ff104a650ff0825328ffe2129943fe1094ca1fe084a604bfd9553007fec8a9802ff6454c9fff322a603bf99153007fac8a993ffc6454c077e322a604ffd5153027fca8a9813fd5454c09fe2a2a604bfd8d53027fea6a9813df5354c09ff29aa600df94d53027f8a6a98137c5354c09ee29aa64fffd0d5327ff886a9803ff6254c017fb12a600ff98953007fac4a9803fc6254c017e312a604ffd4953026fea4a9813fc5254c9fffa12a64fff10953007fec2a9802ff6154c9dff30aa602bf98553007fac2a993bfc6154c057e30aa604ffd4553026fea2a9813fe5154c09fe28aa64fffd0553277fc82a993bfc4154c9dff18aa64eff0c553277fc42a993bfc2154c01ffb02a600bfd815326ffcc0a9806fe6054c01feb02a64dff1815300df8c0a9813ff5054c09ff282a64ddf94153027f8a0a98137c5054c9fffa02a64dff9015326ff880a9937fe3054c9bfe182a64dff8815326ff840a993bff1054c9bff082a64dff0415308ffecb21802ff6590c99ff32c8604bf99643007facb21802fd6590c23fe32c8604bf1964301dfac92180fff5490c07ff2a48603ef9524301ffaa921803bd5490c07fe2a48603bf98e43267fea721847fe5390c01fea9c8611ff14e4301ffe872180fbf4390c07efa1c8611ff10e4301fb88721847ff6290c01ff3148600bf98a43007fac521802fd6290c23fe314864cffd4a43267f8a52180fff4290c07fe2148603ef10a4308ffec32192ffe6190c057f30c8600ff58643005fac321847fc6190c057e30c864cffd464325ffca32192ffc5190c07ffa0c8603ff9064301ff8832192ffe3190c23fe18c864bff8864325ff84321847ff6090c95ff3048601bf98243007fac121802fd6090c23fe3048601bf18243267fea12192bfe5090c95fe2848603ffd024301ffc812180ffc4090c95ff1848611ff0c243257fc412192bfc2090c97ff884864aff84243257f82121803ff6550c017fb2a8649ff99543025fccaa1803fd6550c017eb2a8649ff19543025f8caa180eff6450c07ffaa28603ff9514301ffaa8a180ffc5450c077fb1a8649ffd4d43007fca6a1803fd5350c93fe29a8603ffd0d4301fbe86a180ffe4350c01df21a8603ff10d4301f7886a180fdc4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128600bf1894324ffea4a1927fc5250c07ffa128603ff1094301f7884a1803ff6150c017fb0a8648ff98543015fcc2a1803fd6150c91fe30a8602bf1854324ffea2a1923fe5150c91fe28a8603ffd054301f7e82a180ffe4150c07fe20a8648ff8c543247f862a1923fe2150c91fe10a8600ffd8143005fec0a191ffe6050c037f3028600ff5814323ff8c0a1806fc6050c93ffa828647ff9414323ff8a0a180fff4050c07dfa028603f
  | 10 => 0x400400000001802401400803c01000400c01400c00000000000000000c01000000803c00803402400c00804c00002c00000802800406400000c0080400000140a403401002c00400c00800000001c00006000804002c0000100640040040800480000000140000a003400000000401c00c01400800400801001000402400000c00002c23400c08003400405000403000000c05000c00400004800004401c00006400006001000400000806800800c00000000400815804001003000c00800403c00005005000002c00800c00c00000c02c01c00401800401000400802801403800000004001400800c00000c02401400000000400804001803000802c00000005003000000800000400000000800802000408000002800400400003401401000801802000400000009000c05c0080040000000640b80100040680080180100000100ec03801000802c00800000000000c02c00000406c02401c00401400c01401400400803401400400400000000401400c00804000002000000001801002400001000000400000400000802c0300080000b00080040000000180b0008077fb2aa803bfd915401ffea8aa013bf5455007ff2a2a803df9515401ff8a8aa00f7c5455007de2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d54005f8c6aa013ff5355009fe29aa803ffd0d5401ff886aa00fbc4355001ffb12a800bfd8954007fcc4aa003fd6255001fe312a800bf18954027fea4aa0137f5255009fe292a803ffd095401ff884aa00fbc4255001ffb0aa800bfd85542a7fcc2aa00afe6155001feb0aa854ff18554015f8c2aa013ff5155009ff28aa804ff1455401ffe82aa00fbf4155007ff20aa803ff105542a7fc62aa153fc31550a9ff10aa854ff08554007fec0aa002ff60550a7ff302a801bf98154007fac0aa14ffc60550037e302a804ffd4154027fca0aa14f7e5055009fe282a804df1415401ffe80aa00fbf4055007ff202a803ff1015429ffc60aa14ffc30550a7ff102a853ff081542a7fe20aa14ffe10550a7fe082a804bf5965308ffec92994bfe6494c077f324a600ff59253005fac929847fc6494c077e324a604ffd5253027fca929813fd5494c09fe2a4a604bf98e53027fea7298137f5394c09efa9ca604d7d4e5308ff8a729813dc5394ca5ffa1ca611ff10e5308ffec529803fe6294c017f314a600ff58a53005fac529847fc6294c09ffa94a604ff14a53297fe852994bfc4294c23ffb0ca651ff98653015fcc329803fd6194c017eb0ca611ff18653015f8c329813ff5194c09ff28ca604ff14653297fe8329947fe4194ca3fe20ca651ff8c65308ff86329947fe2194ca3fe10ca611ffd8253287fcc129806fe6094c01feb04a600bf5825308ff8c129806fc6094c09ffa84a604ff94253027f8a12994bff4094
  | 11 => 0xa9225928f844078e0001319e703627a80568cac0005f639093d4fd060d41687e08e26962e00f20b0281820c81e908849924b8a6cfe07b522902f82ce16935696b876833a29a9f700001dc2d50e2c9e800029f80000002f41d40000644000106800088a00000005ac0007d54391b590b81432279644fe44d11a9142c1ac65346981600004a40a80510c8e0003a40000bc65342a10dd00000e80000c840000001d1000069a794000000000000026480000006312eb12cc31c20b21d22704400004131e2816c58e0000720a9400031a84004380001618f8013600002721304d64bd36414940000fc456240026e3340b080000000004070ee869400042d8000efc0003f307890d64cf065001c00800401402800003400800800001c00c00406400400c00000400000400001000400002800401800001801400803000000800000801c01000402c05800400800000003000001800c00007400c0080080080040b001004801000c00004c00400001801002800002004801000c00004807400800800c01c00800800001406000800000802c0040600f400001800009800802400c00802400001807801001c01801001800c01c04000000008c01c00404803404000000c00004400000c01800400c06800c00001404800c01400001c0040080040100000140a400c02800002c02801c04400401800000001402c00400000002000001c01402000001400403001000001401800401007401003805400802000000c00c00005402405403406400802000001000000002400402000000000800400006c00800400400400001400401000000402003404c00407000c03003c00002004000400c00c06001000402807c00000400000401400000000400801400000002000400400400000800c01c00003804000000000c00000400c00c0180180a401002c01400001c01800000c00000800001001c00002400000c00800000000c00003802c00c04c00002801c07801800800001000402c00c03800000808000803402c00800000c00800004401800c00000800c01406003804000800402800005c01400001400000000803c00402c00400000004001000400400400400c00803400002801800004800c08c00c03c02802801009000000000800001c00007000804400801001401000402400805001800800000400803000002000c01c00000400400805004401002400c02400400800400001807c00800800403800400400400000c01400001000000003000401000409c00c0080a400006c0000040000040040f000006002808801c00c05406800804000003001400c00809c07000001c02c00800c00804801003801c03401000400000400801400000400000c00000002400000000000000002804004000806000003800403c00c01001800403403800001c000008024018
  | 12 => 0x1c01b44dc26a600019285420003a013e4eda62345ca1a076a23c00000000005462a7151106835914480000000003e88000000000000243c00000025280000002a80f29bb00007cb000162c00040a4529664350000189800049c189000205c0000000000000e480000eb800000030800000000002413b1849855e8e344c8000c32000478229110c5a33370454d94235406847834c7af06421bc97c4183ae1b78adc8b20bd90490da0000000fec4ca74c0188ca09c45d90000d8ccac0d704f97c4e2228408d00003a42542218a50b0a0da0001e4445e19b2448b5c00082b45d00005c6460087899000024f2b49bc018c78f000000092c5d102f000039e0003b7000073e00004619f48a88932e1008072c8531a31438984000000000051e0000002300000194000034913c6da4200924a2c0c12b1000004271b48f1c5805e0000920ba47b863336491cc9608d50b200005183df22724640000000499ed80000002ba219805469a0a31bf49ee20f0e310950022f215f002092614e108053434048c2a8172c65835621da2ec0128370770868b084c320e0a5d1048101a7838800006307d02ec54a30d3d591a0dc800048893c4a9044b000239874a75611d12081bc0000000000d1a0000df82a473451d0aa000d01e30b0dda274ecc67201e0d2493c0000000d54fb2010040000000011c00000009b664e42310c471c01111fa39409800038d09f0d0c4e829810f81686110000c508802fd07988506ea6a513c07340008ab1f09a4c27660749103d03ba3b00f682f46b88d1457128cfda0002ea998c9b4573380000047a0002e4a424fe620516880010e274125d80008b2000070800084274430700006367680000354fca0003e7815ca4428a20b8000afc7c60ce13c90ae43400000005ac32600000043cc71f000000000079319b9ca455a7d246e88a4000000000000000066f0000000000000000000090a00033a80009a818542700000007fd0000360ef241a11690a8e505f208698b4e741d833b923c95c2b237c8fb876e2a23d70d5048e092411196c31e77437c1a3c80e122036800052a51524223dd17a61f01498587220c91432090fee5292700c7cf3e2da2da1cbce620c21738dacbbc742194a0a91fa8fb3af987095265a1860c390ea5f903799a0b6644c1b080000007c938e800100e85e32914704102b60b308e07fc0e72b30d888cc8c937a000094c3850002304e445eb34c1774ce02ce00000005688c41ec0000c4411926995b4382000461a1240007b836303905fc207206029c0003b23b219400c8780000039924a00012902f0be65f50d282582a203a000000085a2330899f40ca80002728ecc05a84111d842c1167ee11f08c091c35a0fa8dbc68a7b113f2484e121390249ba0000692000115c0008921c505682ca5d718e191003c0000a790b0
  | 13 => 0xe466ab02d8adcfbe1ef32f9c546227703501e9458e60411a185c3c60e92210000d062090000a9c2283a92ca0ea8aae5c42131c1c1a68874188fd116c7b20000da412888909985491687101b980ac4865e23e099540002d2325800800090b0ae00009b03da08f8000cc438747f914c09069f1500000d6a0730c98acd07681f284067c0007a62ec0e20ffc878199935cad409d02302811f031942817a4eb000000010b8b0433c0d916f8df617c0000338000000000235c7d000023c8d208c43f30cb02385940000000f645fe0d029d940cc900000118000a6c5b6000049c0000003249bcc2ac00000020e00000002a1949c0006880001aa40003f500000004dc88d00000000007c00001c9800050000000011200000a2800000068028c8eec00034e2e3982456a0600000000d7810600009406c87250000000ac65760000ec40009131918e903ec7ac42e8d5c43a3d237511690d8924154a0fc95000032c19801fa84f0000c5800049a00018b00000002d28c2523031229c9e6049a13e02a9b300001e01c480008283f60000000e680000ea176d12c00032b9dfcb4216f0000bb09280000001e3800000038614bc8bc8803010000d8a2eb000000030e00000000000005872b880000008161c2000039c3ef2ed000000029114e93b8b528c700000000006f614e13b0f4818843101a4f0c87711900010148b81459e580001a70000884d225fd08915f07a22820a423bc0001012480000000000056000029485609600fd14000000000003d02c534e13f03e20ab10b1e1007c00046c8c680000000bd000000000007b15a11a42cb0000350a2e00031e0000600806166a318d7077819d851d20617500011444800001f598ec23041f00000008b86f722312e8e7c00000006bc0006140000a8ce780c700000000001b90729fa85f0000000144506a0a13f4a0780005320001dc80000000b910f0c842e604f000105c000212222ca46000000036503283c3a280009785613361798e0666a3cd00004d29170ec80012501ff2101c4c65a50913b05b851022a1b91d9ca6281a19f8d108f634c0000f006145bb2049ea8bde0002f68b5017417e245a12000024643986cc24257a42c80000000002ae014800000000000001a20000001e200000a614b1d680002c201c970c0005591992160d280000000690000842000000000000000000003be70f3dd80004de4650000e5c0000003601dec0006eb1e489c03f80f53190b18c1e1ca0131a2480c8d602b2050ea062b0c114f812069e0b113c02bc84d3fe1d348462622cb10044260183f6173cb9a5a23bd0f281ba00000b9b4c0000f204307308000003f392709ac643213800033060a0001f6c9565e83e70000aa482134080011d63a730180002640000c685c08664b70f212d400006a47d08090961f929616310f6190
  | 14 => 0x100422b33999b50b41c721c800119c0000000b6c8fc6ba0db0ed8ff40000af8000000000000143ccce5fc15d800040037800007b8b7e5f040a8ef90d213d3f2126c0000000ca9df09d2000230897cc7000036a8bf0f120002708fc00002370000000dc40000001e9d1da3ed35b845c7f00002f508d800046e00014a822c00026696551147e13b0173855c81c000025c73a00037e00b8b1a4d21e684a83421bd33207f44e60773091730b368ad20b200c2e84de1e70000ce874300001e40005ac00396001024c00b18b24c2a0003ab8000024676000000000000035891584ae4a73d118d107c38200019340006d822aa2980005b7000186c00027a45997e0f6015800000000000003510db40c26f22ba9f74d0e1d327d1d64352000482021c3566cb2081b0800001925118e400000000016400000001780000aa238f310956c91439c3e19a5cebc38146285fc3f46080f0810c6045f42018928b0c72c3a7951c4624f62909480ee629039704946a21683980000c4c26600022a524e84a23d00010ce35026284441b650c1cf041d0360000000bccb385413100000a0a19d3de1978bc229e01209680000000c5174c000000183000000003443e1c1892289f000000000054f45f9b7400037b0ed0228000554438000043653c03404fc8d245015c8618aac0fb41193f80000001de9bbc000000000000000000000016f44220ef1e78000f248fc00021a80000b53ce81341e090e16e8c0c0005d01f900007a000036700008b600000000001880001ea95fc66275402e18945606d92890d2cb128df28d9be8ab000000014982aa0003c60e6119e1bc00004a0e0437a00017280004320238a64db88b0366800110635d26e0b0122c6842b380010220003a495e0e243650228000b6a000096800028067c0000914bee0cd4738000fec4ca36f93a90ca27915f9ffc80a00022f82651544e42c400000002dc01907cc9fe00030280000008a20678b40a967be16f8000bfe0000001c3800000000004d03a23382d8000083c0003ada220b4e0002850a981080000002450e6c0003590f9002a1c010b8b7878a8a129c1b1113449800011f464e5ad3d4a0f4bc861d23204c40be0f73951bb8060098031137c5304a012b17209e60131471f7887068a0daa418da40823f782340002b839da18c4960220c197500000000000000e3217726a9ce04fa0001e323a90ec825204182c0888610000000f904860001b40d5c65c000026860a66941612a80661de0b60000ea491f2f609c81b847c37393ac81a78310f1dac2e28043969b8c6086b340498f8bbe7651b611d41fc74703a020c96c1cb20aa3709707c703e0b600ea0000000050fac1e72b2001029291b28819940fa31500013ec0188052cf80002786821e9a34000055e2ce80000004223dc8978a800c30c5800
  | 15 => 0x1a4000000012c0000cba0000fa0c80f943a3000149081601b0dc09802da00034d82250fc3ff00024090f401c0c6000000029a35d960c00017d38e21f4a305e029e9bb448805430985cc0000053540fe400080c46da3cc5c00c003b127c000253090033000c22c3f5a3886be0001881e805ea27500000000002f9000193c000000000211425e0002f286d0f3c63600023d90f200000012342d43770e29220d6c463000248c2ba6f544c1a840007cd0a593b40000000000cd882254d00015ac8ec0000c0a2140b200037480000001532ad0ef09fa0a215e80000002241ca00d47321362c99f0892a76900000008e44872509dc40000b70278000aee0000000bb51c012b08216bc0006e0000202c0005a04148000b823db23b934057800012e24547d41804931410742317494a38441c00044781940003c30001af4d2a00045e136498c1f0076a180c8c46f46108a0b3073d1ac0ba078832e2020efc0fc20a28694dc3ac00000680a0ff244930822dd05e4803e99eb44461d500002b8c5e20c1b381004303793200b9420669d26381ec0e278200503ac1f05e703622c4000000000002ccd62cf1ef0ee4fc64303520a148d47203260a4c0002924408d080002252be82a05984ce0828000d7285f3ba8000f8a00038280000764e639397b886e8af1ea000087a7990761a8d20e42f3aa8eb08906513f0096cb8c0000000810b5619117d1aa814a19a000056400000001c00006e01083c0938c1c03ec33d8000fea0003b09ab0c6e0003e211fc0000000000000b7822622500000006591288000d869201928000bfc0000000000f2e2d50001a145b212e00016900000002cd10a51bc1e91fb80002c076c0001c7800062800017703a000036ba334648751207800000034110f800000000019a803800060603f95bd23a39b0000a901fe8320079ad12384b139911c10662e22d422f837411d31204a440652b2c7855cec41aa183a2302ec70b4868bec21837d04a8d0c4da28d06f95ecae4318016066521800004885047ae02700013bc00005a27c23c4000000000186800000000023d0a8a2aa0d80530a0489420100000000001af22a063c51e01b08645ec43537307dc30838c265828d19400038503e47ac00013ba144d6000009a81988502c81b30e34f36376135076c0004e70629f68f6e00037f817400026c0000ff400069900000005dc0001f19f6000000000000000000002dca1b8000000000157400000041c800049887f48287c8aa63fa00000000000000001c5000033d29982e000079000001410860002208000e943902d9242863a0002569594f4673f2369a385060000000000d18830198019c0e430148d00010003e63389f88988000000090800004125602c00000003ea23b8b246be0001ce51980000001c211fc00000019e800000
  | 16 => 0x3700000000000002390a7452e1171c104ba5072cb8fc514e7373c687b0e6a10e2098854c7455512aa3d4a0c3fc0a1190487e8742578a1c83a4441708e0cefa8c83fc01c09823922b604c000001a479064811029f000000033c2ac0000000000000000000112a00000018787ce000000000000063d000000089a78542a98b8f2a7531240000000000000056c8f00003b50000246492000070cd8e6301d6a244e8c91246d1d38d4e7bd1389c5c7c41fe23611d05e26270000da80002ea000000000000019f14b44727771e59d2c00000019c80011d80533e6202070c11b0d70f3039266624e9dbccfe0002bc8a002745282e280746c004a2338f940006f105f832cf684b21720df0ae01c208480000000002418d1cdca51328d07ec0001b72a60000cfc46b11386b000060128082cc4d004b00000001540002e910386d085446c00007264bf000116007a6183228c3c000000360980000000020d96785ee0003d0a11c0001c422e82bc0004cc2dc000065e36e00000004fe222133a14806e3e937f02904e877633c2238740102367a3506b67f40000000f0e78b00008040004dd40e8818c540001dc00006548b51d7068c5821ad2fd1d745a60e314083a875e63f3f8800000070100016c513600005c80002f209c1a98000000000413a0d80003dd13085e00000510f580012204471589628f741ea314807c000000000240442400034580010740004320dc472a5ba0788bbc6fe0004421efc8560000df000000000040980000006bf33c80000000850358eac0006db000183002c0b2155958011e3c147480946fc7fb16201e11464b90000000e300003308428bf672b1e11ecc00000000000000006d42af800034481200004e104027b0000e991d073315d00001621972640d0086c9082d3232cd5e7d702112d11f2897240a0a0a2870d00000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa704c91008cff760c910004fe760c910004fd760c91008cfc760c91002d7e750c9100057d750c9100067f650c91015e7c650c910006df630c91008edc630c910006ef620c910006ec620c910015f6710c910005f5710c91014fd4310c91000dfa700c910005f9700c91000df47654510026f4765451000cf47654510015f77554510017777554510007776554510026f66554510026f4655451002f746554510005f4735451002f775354510007755354510005f77254510007b64254510007b44254510007f3705451000df6705451000df47054510137f07054510016f76054510017f3605451002ff35054510137f05054510137f23054510137f2205451000df676cc51010ef676cc51000cf676cc510005f775cc510005f575cc5100077765cc5100077465cc510015f673cc510017d673cc510006f763cc510007d763cc510006f563cc510007d463cc510005f572cc510006f662cc510006f462cc510007b642cc510007b442cc51000df670cc51010ff270cc510007f170cc51000df470cc510016f760cc510017f360cc5102b7f350cc51010ff050cc51010ff230cc51010ff220cc51000df476485100c6f4764851000cf47648510005f77548510005f57548510007776548510007746548510007b77448510007b47448510007d77348510005f67348510005f47348510007d47348510005d47348510015f77248510017e77248510007e76248510006f66248510006f46248510007e46248510007b64248510007b44248510007e63248510007e53248510007f3704851000df6704851000df470485100c7f07048510016f76048510017f360485102aff350485100c7f050485100c7f230485100c7f22048510015f8764c11006ef8764c110014f8764c11002dfa754c11002df8754c1100077b654c11000778654c11000dfb734c11000fdb734c110007db634c11008efa634c11008ef8634c110007d8634c110007da534c110007d9534c110005fb724c110007ba424c110007b8424c110007f3714c110015fa714c110015f8714c11006ff0714c11000efb614c11000ff3614c11006ff2514c110007f1514c110007f3314c11006ff0314c11006ff2214c110007f1214c110015f8764811003ef87648110014f876481100077b754811002dfa754811002df8754811000778754811002d7875481100077b6548110007786548110007bb7448110007b87448110005fb7348110005f9734811000dfb724811000feb7248110007eb6248110006fa6248110006f86248110007e86248110007ea5248110007e95248110007ba4248110007b84248110007f37148110015fa7148110015f8714811003ff0714811000efb614811000ff3614811003ff25148110007f15148110007f3314811003ff0314811003ff22148110007f12148110
  | 1 => 0x8910014fd70189102d6f9701891000cfc7018910006fb50189102cef850189102ceef20189102cefa20189102ceed2018910004ff7694910004fe7694910004fd7694910004fc76949100067f65949100267c659491002f6f5294910015f67194910005f5719491000dfa7094910005f97094910227785094910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100267c6554910005bf7454910035bc7454910015f67154910005fb705491000df87054910004ff7690910004fe7690910004fd7690910004fc76909100067f65909102067c6590910006bf649091001ebe6490910006bd649091001ebc6490910015f67190910005f5719091000dfa7090910005f97090910006bf7690910006be7690910006bd7690910006bc7690910006bf65909100073f65909100063f6590910206be6590910006bd6590910206bc65909100073c65909102063c6590910006bf6390910006be6390910006bd6390910006bc63909101c5be7290910006bf6290910006be6290910006bd6290910006bc62909101ffb67190910007b571909101f6bf61909101ffb651909101ffb431909101ffb621909101f7ba7090910007b970909101f6bf60909102c7bb50909101f7b850909101f7ba30909101f7ba20909101ffbb10909101f7b610909101f7b410909101f7b81090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101ee7c655091001ebf7610910036be7610910036bd761091001ebc76109100373e75109100373d7510910006bf65109100073f65109100063f65109101d6be6510910006bd65109101d6bc65109100073c65109101d63c6510910006bf6310910006be6310910006bd6310910006bc63109101f5be7210910037ae7210910006bf6210910007af6210910006af6210910006be6210910006bd6210910006bc6210910007ac6210910006ac62109101cfb67110910037b571109101c6bf61109101cfb651109101cfb431109101cfb621109101c7ba7010910037b970109101c6bf60109102bfbb50109101c7b850109101c7ba30109101c7ba20109101cfbb10109101c7b610109101c7b410109101c7b8101091008cff76cc910004fe76cc910004fd76cc91008cfc76cc9100067f65cc9101be7c65cc910035be74cc910005bd74cc910006ef62cc910006ec62cc910015f471cc91000dfa70cc910005f970cc910004ff768c910004fe768c910004fd768c910004fc768c9100067f658c91019e7c658c910006df638c910006dc638c910015f6718c910005f5718c91018fd4318c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91017e7c654c910005bf744c910035bc744c910005f7714c910015f4714c91000df
  | 2 => 0xcfd7118d10014fc7118d1008edf3118d102f6dd3118d10014ff7018d1000cfe7018d10014fd7018d1008ef97018d1000cfc7018d1008edf3018d1008efa3018d102eedd3018d1008cff7694d10004fe7694d10004fd7694d1008cfc7694d100067f6594d100267c6594d1002f5f5394d10015f47194d1000dfa7094d10005f97094d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10005f77154d10015f47154d10005fb7054d1000df87054d1026f785054d1008cff7690d10004fe7690d10004fd7690d1008cfc7690d100067f6590d102667c6590d10006bf6490d1001ebc6490d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1024e7c6550d1001ebe6450d10006bd6450d10005f77150d10015f47150d100067f65d89100067c65d8910035be74d8910005bd74d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910006be74d891001cbe74d8910004fd74d8910006bd74d8910004bd74d891001cfc74d891008cfe73d8910004fd73d8910006ef42d8910006ec42d891000cff71d891000cfd71d89102e6ef21d89102e6ed21d8910014ff70d8910014fd70d89102deef20d89102deed20d89100c4fd769891002d7e75989100057d75989100067f65989100067c6598910006ef62989100c5f5719891003df97098910024fe75989100067e75989100247e7598910004fd75989100067d75989100047d7598910024fc759891001cfe7498910004fd749891001cfc749891008cfe7398910004fd73989102ccfe72989100c4fd7198910006f5719891005ef4319891005ef621989100dcfd7098910006f97098910006fb50989100def850989100defa20989100057f755891002d7c75589100067f65589100067c6558910005bf7458910035bc7458910005df7358910005dc73589100ddf7715891005dfb7058910004ff75589100067f75589100047f7558910024fe7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df735891008cfc7358910006dc7358910004dc7358910006ef72589100dcff7158910006f771589100c4ff7058910006fb70589102dcfe76189100067f65189100067c6518910006ed6218910024fe7518910004fd7518910024fc751891001cfe7418910004fd741891001cfc741891008cfe7318910004fd73189100dcfe7218910006ee7218910006ef4218910006ec421891000cff7118910014fe711891000cfd71189102cef57118910014fc71189102d6f431189102d6ef21189102d6f621189102d6ed2118910014ff701891000cfe701
  | 3 => 0xf71d9110014fe71d911000cfd71d9110014fc71d9110326bf41d9110326bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110316bf40d9110316bd40d911001cff76591100057f755911002d7c75591100067f65591100067c6559110036bc6459110005df7359110005dc7359110005ef7259110005ec725911030df7715911031dfb7059110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c7559110314ff7459110006bf7459110036be5459110004ff7359110006df7359110004df735911008cfc7359110006dc7359110004dc7359110036bf4359110004ff7259110006ef7259110004ef7259110004fc7259110006ec7259110004ec7259110036bc425911030cff7159110006f77159110124ff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100267c655511001ebe6455110006bd6455110005fb705511000df8705511029f7850551100067f65d8d100067c65d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d10004fe72d8d10004fd72d8d1000cff71d8d1000cfd71d8d102fef571d8d10306df31d8d10306dd31d8d10306f431d8d10014ff70d8d10014fd70d8d102fedf30d8d102fedd30d8d100f4fd7698d1002d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100f5f57198d1006df97098d10024fe7598d1008e7e7598d100247e7598d10004fd7598d1008e7d7598d100047d7598d1008cfc7598d1001cfe7498d10004fd7498d1008cfc7498d1008cfe7398d10004fe7298d10004fd7298d100f4fd7198d1008ef57198d1010cfd7098d1008ef97098d1008efa3098d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10035bc7458d10005ef7258d10005ec7258d1010df77158d10085fb7058d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d1001cfc7458d10006bc7458d1001cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10004fc7258d10006ec7258d10004ec7258d1010cff7158d10006f77158d1006ef43158d100f4ff7058d10006fb7058d102fcfe7618d100067f6518d100067c6518d10035be7418d10005bd7418d10006dd6318d10024fe7518d10004fd7518d1008cfc7518d1001cfe7418d1008ebe7418d1001cbe7418d10004fd7418d1008ebd7418d10004bd7418d1008cfc7418d1008cfe7318d1008ede7318d10006df4318d1008edc4318d10004fe7218d10004fd7218d1000cff7118d10014fe7118d10
  | 4 => 0x8120007bb64c8120007b864c812000dfa72c812000fea72c812000efb62c812000feb62c8120007ea52c8120007e952c8120007ba42c8120007b842c8120005f971c8120024fe76d951002e7e65d951000dfa70d9510015f970d951002f7b50d9510134fd75d951001cfe74d9510004fd74d951001cfc74d951002e7f54d95100067e54d951002e7c54d951008cfe73d9510004fd73d951002e7f53d951002e7c53d9510004fe72d9510004fd72d951002e7f52d951002e7c52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95103567f51d95103567d51d9510014ff70d951000cfe70d9510014fd70d9510356f970d9510014f970d951000cfc70d951033e7f50d951002efb50d951033e7d50d951033ef850d951032d7e76d95100247e76d95100067e64d95100067c64d951033f7771d951033f7471d95103577431d95103577621d951033f7a70d95103577970d951033f7a30d951033f7a20d95103577b10d951033f7610d951033f7410d951033f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d951033e7f71d95103567e71d951033e7d71d951033e7c71d95103567f41d95103567e41d95103567d41d95103567c41d95103567f31d95103567e31d95103567d31d95103567c31d95103567f21d95103567e21d95103567d21d95103567c21d951033e7f70d951033e7e70d951033e7a70d951033e7d70d95103567970d951033e7c70d951033e7f40d951033e7e40d951033e7d40d951033e7c40d951033e7f30d951033e7e30d951033e7d30d951033e7c30d951033e7f20d951033e7e20d951033e7d20d951033e7c20d951033e7f10d951033e7e10d951033e7c10d9510024ff765951002e7c6559510345f7715951034dfb705951033cff75595100067f7559510004ff745951001cfe745951001cfc7459510004ff735951008cfc7359510004ff7259510004fc7259510344ff7159510006f77159510134ff7059510006fb705951002efb5059510136f8505951033d7e761951002e7e761951033c7e761951002f3e741951002f3d74195100067e64195100067c641951033776711951032f75711951032e7f61195103377431195103377621195103377b701951032f78701951032e7f601951032f7a301951032f7a20195103377b101951032f76101951032f74101951032f78101951001cfe76d91100067f65d91100067c65d9110036be64d9110024fe75d9110004fd75d9110024fc75d9110124fd74d911008cfe73d9110004fd73d9110036bc43d9110004fe72d9110004fd72d9110036bc42d911000cf
  | 5 => 0xcfc76509200067f65509201ee7c6550920006bf645092001ebc6450920005fb705092000df870509201f5be7610920046be76109201f4be76109200473e75109200473d7510920006bf65109200073f65109200063f65109201d6be6510920006bd65109201d6bc65109200073c65109201d63c6510920006bf6310920006be6310920006bd6310920006bc63109201f5be7210920047ae72109201c6bf6210920007ae5210920007ad52109201cebe61109201cebc61109201c6bf60109201c7ae20109201c7ac20109201c7b820109201c7ba101092000cfe76cc92000cfc76cc9200067f65cc9201be7c65cc920045be74cc920005bd74cc920006bf64cc9201b6bc64cc920006df63cc92008edc63cc920007ac42cc92000dfa70cc920005f970cc920144fe768c9200067f658c92019e7c658c920006bf648c920196bc648c92008cff764c92000cfe764c920164fd764c92000cfc764c9200067f654c92017e7c654c920005bf744c920045bc744c920006bf644c920176bc644c920006df634c920006dc634c920005f7714c92003df4714c920005fb704c92000df8704c920184fe760c92004d7e750c9200057d750c9200067f650c92015e7c650c920006bf640c920156bc640c920007ac420c920014fe76d85200067f65d85200067c65d8520006bf64d8520006bc64d852003ef661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d852008cfe73d8520004fd73d852000cfd72d8520014fc72d8520006be42d8520006bc42d852003ef431d852003ef621d852000cfe70d852000cfc70d85200def710d85200057f755852004d7c75585200067f65585200067c6558520005bf7458520045bc7458520006bf6458520006bc6458520005df7358520005dc735852003ef46158520004ff7654520004fe7654520004fc76545200067f65545200267c6554520006bf645452013ebc6454520004ff7650520004fe7650520004fc76505200067f655052012e7c6550520006bf645052001ebc6450520004fe76cc520004fd76cc52008cfc76cc5200067f65cc52011e7c65cc520006bf64cc520116bc64cc520006f761cc520016f461cc520004ff764c520004fe764c520004fc764c5200067f654c5201067c654c520006bf644c5200febc644c5202ccfe76c85200067f65c85200ee7c65c8520006bf64c85200e6bc64c8520007ac42c852000df870c852000cfc76485200067f65485200d67c6548520005bf7448520045bc7448520006bf64485200cebc6448520005df7348520005dc7348520007ac4248520006f76148520016f46148520005fb704852000df8704852000dfa76c812000efa76c812000cfa76c81200077b65c8120056fa65c8120056f865c81200077865c81200567865c
  | 6 => 0xf7458d20004bf7458d2001cfe7458d2001cfc7458d20006bc7458d2001cbc7458d20006df7358d201a4ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d20014fe7158d20014fc7158d20006f47158d20014f47158d20164ff7058d20006fb7058d20166fa1058d20184fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d20006dd6318d20024fe7518d20004fd7518d2008cfc7518d2001cfe7418d20004fd7418d2008cfc7418d2008ede7318d20184fe7218d2008cfc7218d20014fe7118d20004fd7118d20014fc7118d20006de3118d2008edc3118d2008cff7018d20144fd7018d2008edf3018d20146dd3018d2008cff7694d20004fe7694d20004fd7694d2008cfc7694d200067f6594d200267c6594d20006bf6494d20296bc6494d2004f5f5394d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200267c6554d20006bf6454d2027ebc6454d2008cff7690d20004fe7690d20004fd7690d2008cfc7690d200067f6590d202667c6590d20006bf6490d2001ebc6490d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2024e7c6550d20006bf6450d2001ebc6450d20005ef7250d20005ec7250d20364fe76949202267f65949200267c6594920006bf6494920236bc649492004f6f5294920365ee769492035eee769492020ded75949202276f6594920026ee6594920026ec659492004f6c65949200266c6594920007af6494920007ac649492000dee709492000dec7094920226ef60949202276e50949202276c5094920227ea1094920024ff765492000cfe765492020cfd765492000cfc76549200067f65549200267c6554920005bf7454920045bc7454920006bf645492021ebc6454920005fb705492000df8705492000dec7654920026ec765492000cec7654920225ef75549200076f75549200076f6554920026ee6554920026ec655492004f6c6554920007af7454920007ac7454920007af6454920007ac645492004f6f54549200076d545492004f6f53549200076d5354920007eb705492000dee705492000dec705492020fe8705492020eef605492020fea10549201c4fe76909200067f65909202067c65909201f6bf649092001ebe6490920006bd649092001ebc64909201c5be7690920006be76909201c4be7690920006bf65909200073f65909200063f6590920206be6590920006bd6590920206bc65909200073c65909202063c6590920006bf6390920006be6390920006bd6390920006bc63909201c5be72909201f6bf6290920007ae5290920007ad52909201febe61909201febc61909201f6bf60909201f7ae20909201f7ac20909201f7b820909201f7ba109092001cff765092000cfe76509201dcfd7650920
  | 7 => 0x9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d91201f6bf72d9120046be72d912001cbe72d91201f6bd72d912001cbc72d9120006bf52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d91201f6bf70d91201f6be70d91201f6bd70d91201f6bc70d91201f6bf50d91201f6be50d91201f6bd50d91201f6bc50d91201f6bf30d91201f6be30d91201f6bd30d91201f6bc30d91201f6bf20d91201f6be20d91201f6bc20d91201f6bf10d91201f6be10d91201f6bd10d91201f6bc10d91200057f755912004d7c75591200067f65591200067c6559120046bc645912036def7259120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c75591201f4ff7459120006bf7459120004ff735912008cfc735912036cff7259120006ef7259120046bc4259120004ff7159120014fe7159120014fc71591201dcff7059120006fb70591201f5be7619120046be76191201f4be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c65191201c6bf6219120006be6119120006bc61191201c6bf60191201c7ae20191201c7ac20191201c7b820191201c7ba1019120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200267c6555120006bf645512001ebc64551200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d20184ff70d8d20184fd70d8d20186df30d8d20186dd30d8d20186fa10d8d2004d7e7598d200057d7598d200067f6598d200067c6598d20045be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d20165ed7298d20024fe7598d2008e7e7598d200247e7598d20004fd7598d2008e7d7598d200047d7598d2008cfc7598d2001cfe7498d2008ebe7498d2001cbe7498d20004fd7498d2008ebd7498d20004bd7498d2008cfc7498d2008cfe7398d20164fd7298d2008eed7298d20014fe7198d20004fd7198d20014fc7198d201a4fd7098d2008ef97098d200057f7558d2004d7c7558d200067f6558d200067c6558d20005bf7458d20045bc7458d20006bf6458d20006bc6458d201a5ef7258d20005f77158d2003df47158d20004ff7558d200067f7558d200047f7558d20024fe7558d20024fc7558d200067c7558d200247c7558d20004ff7458d20006b
  | 8 => 0x5f970c87202dcff7648720005bf7448720065bc7448720005df7348720005dc7348720007ac4248720016f46148720024fe76d952004e7e65d952001cfe74d9520004fd74d952001cfc74d952004e7f54d95200067e54d952004e7c54d952008cfe73d9520004fd73d952004e7f53d952004e7c53d9520024fe72d952000cfd72d9520024fc72d952004e7f52d9520014fe71d9520004fd71d9520014fc71d952004e7f51d95200067e51d952004e7c51d9520224ff70d9520224fd70d95202267f50d95202267d50d95203657e76d95200247e76d95200067e64d95200067c64d95202276f72d95200067e61d95200067c61d95202276e20d95202276c20d95202277820d95202277a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067c43d95202267f72d952004e7e72d95202267d72d95200067f42d95200067c42d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067e31d95200067c31d95200067e21d95200067c21d95202267f70d95202267e70d95202267d70d95202267c70d95202267f40d95202267e40d95202267d40d95202267c40d95202267f30d95202267e30d95202267d30d95202267c30d95202267f20d95202267e20d95202267c20d95202267f10d95202267e10d95202267d10d95202267c10d952004e7c6559520005bf7459520045bc7459520375ef7259520224ff75595200067f7559520004ff7459520006bf7459520004bf745952001cfe745952001cfc7459520006bc745952001cbc7459520004ff735952008cfc7359520374ff7259520006ef7259520004ff7159520014fe7159520014fc715952020cff7059520006fb7059520054fb70595202257e761952004e7e76195202247e76195200067e64195200067c64195203676d72195203667f62195200067e61195200067c61195203667f60195203676e20195203676c20195203677820195203677a101952001cfe76d91200067f65d91200067c65d9120046be64d9120024fe75d9120004fd75d9120024fc75d9120006bf54d9120046be54d9120046bc54d912008cfe73d9120004fd73d9120046bf43d9120046bc43d912001cfe72d912000cfd72d912001cfc72d9120046bf42d9120014fe71d9120004fd71d9120014fc71d9120046bf41d9120006be41d9120046bc41d91201f4ff70d91201f4fd70d91201f6bf40d91201f6bd40d91201c5be76d912001cbe76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006be61d9120006bc61d91201f7ae20d91201f7ac20d91201f7b820d91201f7ba10d
  | 9 => 0xf5294b2000dfa7094b20005f97094b20227785094b20227ea2094b2000ded7694b20026ed7694b2000ced7694b20026ee6594b200576e6594b200266e6594b200076d6594b20026ec6594b2000dee7094b20227ea7094b20007e97094b2000dec7094b20057eb5094b202276e5094b202276c5094b20227e85094b20227685094b20374ff7654b20005bf7454b20065bc7454b20055fb7054b2000df87054b2020fea2054b20375ef7654b2038eef7654b200076f7554b20026ee6554b20026ec6554b20007af7454b20007ac7454b200576f5454b200076d5454b200576f5354b200076d5354b20057eb7054b2000dee7054b2000dec7054b2020fe87054b2000de87054b20057eb5054b2020fe85054b2000cff7690b2001cfe7690b2000cfd7690b2001ebe6490b20006bd6490b2000dfa7090b20005f97090b201f6bf7690b2001ebe7690b2001ebd7690b201f6bc7690b20006bf6590b20206be6590b20006bd6590b20206bc6590b20006bf6390b20006be6390b20006bd6390b20006bc6390b201f6be6290b20007ae5290b20007ad5290b201febe6190b201febc6190b201f7ba7090b20007b97090b20387bb5090b201f7b85090b201f7ae2090b201f7ba2090b201f7ac2090b2036cff7650b2001ebf7610b20066be7610b201c6bd7610b2001ebc7610b200673e7510b200673d7510b20006bf6510b201d6be6510b20006bd6510b201d6bc6510b20006bf6310b20006be6310b20006bd6310b20006bc6310b20067ae7210b201c6be6210b20007ae5210b20007ad5210b201cebe6110b201cebc6110b201c7ba7010b20067b97010b2037fbb5010b201c7b85010b201c7ae2010b201c7ba2010b201c7ac2010b20164fd76ccb20065be74ccb20005bd74ccb20007ac42ccb2000cff768cb2000cfd768cb20006de638cb20006dd638cb2000dfa708cb20005f9708cb201a4ff764cb20005bf744cb20065bc744cb20005f7714cb2005df4714cb2000cff760cb2000cfd760cb200557e750cb200057d750cb2008ede630cb20006dd630cb20007ac420cb2000dfa700cb20005f9700cb200557e75d87200057d75d872005ef661d8720014ff765872005ef46158720004ff7558720024fe7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff735872008cfc7358720014fd725872000cfc7258720006be4258720006bc425872005ef42158720006fb50587200c6f850587200c6fa20587200c6f71058720004ff7654720004fd7654720004fc7654720005fb705472000df87054720004ff7650720004fd7650720004fc765072008cff76cc720004fe76cc720004fd76cc720016f461cc720004ff764c720004fd764c720004fc764c72000cfd76c8720007ac42c8720016f661c8720006f561c872000dfa70c8720
  | 10 => 0x972008cfc73597200567f5359720024ff7259720024fd725972000cfc72597200567c5259720004ff7159720014fe7159720014fc71597200067e51597200567c5159720056fb705972020e7f5059720056fb50597200567b505972020e7d505972020ef85059720066be64d93201c5ee72d9320024fe75d9320004fd75d9320024fc75d93201dcfd74d9320066be54d932008cfe73d9320004fd73d9320066bf43d93201c4fe72d9320006ee72d9320014fe71d9320004fd71d9320014fc71d9320006f970d93201f6be40d93201f6bc40d932001cff7659320066bc6459320004ff7559320024fe7559320024fc7559320006bf7459320004ff735932008cfc735932001cff725932001cfd725932000cfc7259320066bc4259320004ff7159320014fe7159320014fc71593201debf40593201debd4059320004ff7655320004fe7655320004fd7655320004fc76553200267e65553200067d6555320006bf645532001ebc6455320005fb705532000df8705532029f785055320145ee72d8f20024fe75d8f20004fd75d8f20024fc75d8f2001cfe74d8f20004fd74d8f2001cfc74d8f20144fe72d8f20006ee72d8f20014fe71d8f20004fd71d8f20014fc71d8f20006f970d8f20164fd7698f20065be7498f20005bd7498f20006df6398f20024fe7598f20004fd7598f2008cfc7598f2001cfe7498f2008ebe7498f2001cbe7498f20004fd7498f2008ebd7498f20004bd7498f2008cfc7498f20014fe7198f20004fd7198f20014fc7198f2008edf3098f201a6dd3098f20005f77158f2005df47158f20004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f20006df7358f2008cff7258f20164fd7258f20004ff7158f20006f77158f20004f77158f20014fe7158f20014fc7158f20006f47158f20014f47158f20166df3058f20166dd3058f200557e7518f200057d7518f20006dd6318f20185ee7218f20024fe7518f2008e7e7518f200247e7518f20004fd7518f2008e7d7518f200047d7518f2008cfc7518f2001cfe7418f20004fd7418f2008cfc7418f2008cfe7318f2008ede7318f20184fe7218f2008eee7218f20014fe7118f20004fd7118f20014fc7118f2008ef97018f2008cff7694f20004fe7694f20004fd7694f2008cfc7694f200575f5394f2000dfa7094f20005f97094f20004ff7654f20004fe7654f20004fd7654f20004fc7654f200267e6554f200067d6554f20005fb7054f2000df87054f2026f785054f2008cff7690f20004fe7690f20004fd7690f2008cfc7690f20004ff7650f20004fe7650f20004fd7650f20004fc7650f20006bf6450f2001ebc6450f20005ef7250f20005ec7250f2000cff7694b20024fe7694b2000cfd7694b200267e6594b200067d6594b200576
  | 11 => 0x4fd7690930004fc7690930006bf649093001ebe6490930006bd649093001ebc6490930006bf7690930006be7690930006bd7690930006bc7690930006bf6590930206be6590930006bd6590930206bc65909301f6bf63909300079e53909300079d53909301c5be7290930006bf6290930006bc62909301febe61909301febc61909301f6bf60909301f79e30909301f79c30909301f7b830909301f7ba1090930004ff7650930004fe7650930004fc765093001ebf7610930076be7610930076bd761093001ebc76109300773e75109300773d7510930006bf65109301d6be6510930006bd65109301d6bc65109300779e73109300779d73109301c6bf63109300079e53109300079d53109301f5be7210930077ae7210930006bf6210930006bc62109301cebe61109301cebc61109301c7ba7010930077b970109301c6bf60109301c79e30109301c79c30109301c7b830109301c7ba1010930144fe76cc930075be74cc930005bd74cc93000cfe768c930006ef628c930006ec628c93000dfa708c930005f9708c93000cfc764c930005bf744c930075bc744c930006ef624c930006ec624c930005f7714c93006df4714c930005fb704c93000df8704c9301a4fe760c93007d7e750c9300057d750c930014fe76d853006ef661d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853000cfd73d8530014fc73d8530004fe72d8530004fd72d8530006be42d8530006bc42d853006ef631d853006ef421d853010ef710d85300057f755853007d7c7558530005bf7458530075bc7458530005ef7258530005ec725853006ef46158530004ff7654530004fe7654530004fc76545300075d5354530004ff7650530004fe7650530004fc76505302ecfe76cc530016f661cc53000df870cc53000cfc764c530006f7614c530016f4614c530005fb704c53000df8704c530004fe76c8530004fd76c8530004fc76c8530006f761c8530016f461c8530004ff7648530004fe7648530004fc7648530005bf7448530075bc7448530005df7348530005dc734853000dfa76cc13000efa76cc13008f7a75cc13008f7975cc13000dfa73cc13000fda73cc13000efb63cc13000fdb63cc13008fda53cc130007d953cc130007ba42cc130007b842cc130005f971cc1300567e65d9720365ee72d97202277850d972020cfd75d972001cfe74d9720004fd74d972001cfc74d972008cfe73d9720004fd73d9720364fe72d9720006ee72d9720014fe71d9720004fd71d9720014fc71d9720006f970d9720056fb50d97202267e50d97202267c50d9720226f850d9720024ff76597200567c655972000df870597200577b50597200067f7559720004ff745972001cfe745972001cfc74597200567f5459720004ff735
  | 12 => 0xc51d953008cff70d9530284fd70d95302867f50d95302867d50d953007e7c65595303b5df7359530284ff75595300067f7559530004ff745953001cfe745953001cfc74595303b4ff7359530006df7359530004ff7259530004fc7259530004ff7159530014fe7159530014fc715953026cff7059530006fb705953026e7e505953026e7c505953001cfe76d9130076be64d9130024fe75d9130004fd75d9130024fc75d9130076be54d913008cfe73d913000cfd73d913008cfc73d9130076bf43d9130004fe72d9130004fd72d9130076bc42d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130076bc41d913008cff70d9130254fd70d9130256bf40d9130256bd40d9130076bc64591303addf7359130004ff7559130024fe7559130024fc7559130254ff7459130006bf74591303acff7359130006df7359130004ff7259130004fc7259130076bc4259130004ff7159130014fe7159130014fc715913023cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300267c6555130006bf645513001ebc64551303a4fe7694d3007f5f5394d303a5de7694d3039ede7694d3026ddd7594d30026de6594d30026dc6594d3000dde7094d3000ddc7094d3008edf6094d30287da1094d30024ff7654d3000cfe7654d3026cfd7654d3000cfc7654d300067f6554d300267c6554d30005fb7054d3000df87054d3000ddc7654d30026dc7654d3000cdc7654d30285df7554d300075f7554d300075f6554d30026de6554d30026dc6554d3007f5c6554d3007f5f5254d3007f5f5154d30007db7054d3000dde7054d3000ddc7054d3026fd87054d3026edf6054d3026f5e5054d3026f5c5054d3026fda1054d30394fe7690d3001cff7650d3000cfe7650d3023cfd7650d3000cfc7650d30006bf6450d3001ebc6450d30005fb7050d3000df87050d30075be74d8930005bd74d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930006be74d893001cbe74d8930004fd74d8930006bd74d8930004bd74d893001cfc74d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d89301a6ef20d89301a6fa10d8930006ef62989300057f755893007d7c7558930005bf7458930075bc7458930005f7715893006df47158930006ed6218930024fe7518930004fd7518930024fc751893001cfe7418930004fd741893001cfc7418930014fe7118930004fd7118930014fc7118930006ee2118930006ec2118930146ed2018930004fe7694930004fd7694930004fc76949300067f65949300267c659493007f6f5294930004ff7654930004fe7654930004fc7654930005bf7454930075bc74549300075d5354930005fb705493000df87054930004fe7690930
  | 13 => 0x8b3008eef3258b3008eec3258b30004ff7158b30014fe7158b30014fc7158b30166ef2058b30004ff7694b3008cfe7694b30004fd7694b300267e6594b300067d6594b3009f6f5294b30004ff7654b30004fd7654b3008cfc7654b300267e6554b300067d6554b30005bf7454b30095bc7454b300075d5354b30005fb7054b3000df87054b30004ff7690b3008cfe7690b30004fd7690b302067e6590b300067d6590b30006bf6490b3001ebe6490b30006bd6490b3001ebc6490b30006bf7690b30006be7690b30006bd7690b30006bc7690b30006bf6590b30206be6590b300073e6590b302063e6590b30006bd6590b300073d6590b300063d6590b30206bc6590b301f6be6390b300079e5390b300079d5390b30006be6290b30006bd6290b301febe6190b301febc6190b301f79e3090b301f7ba3090b301f79c3090b30004ff7650b30004fd7650b3008cfc7650b301ee7e6550b300067d6550b3001ebf7610b30096be7610b30096bd7610b3001ebc7610b300973e7510b300973d7510b30006bf6510b301d6be6510b300073e6510b301d63e6510b30006bd6510b300073d6510b300063d6510b301d6bc6510b300979e7310b300979d7310b301c6be6310b300079e5310b300079d5310b30097ae7210b30006be6210b30007ae6210b30006ae6210b30006bd6210b30007ad6210b30006ad6210b301cebe6110b301cebc6110b301c79e3010b301c7ba3010b301c79c3010b30164fd768cb3019e7e658cb300067d658cb30184ff764cb3017e7e654cb300067d654cb30005bf744cb30095bc744cb30005f7714cb30085f4714cb30014ff76587300067e65587300067d655873008ef46158730004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc7458730014fd735873000cfc7358730004ff7258730004fc7258730006be4258730006bc425873008ef7315873008ef431587300f6fa30587300f6f71058730004ff7654730004fd765473008cfc76547300267e65547300067d65547300075d5354730004ff7650730004fd765073008cfc765073012e7e65507300067d655073001ebe6450730006bd64507302fcff764c7301067e654c7300067d654c730004ff76c873008cfe76c8730004fd76c87300ee7e65c87300067d65c8730006ee62c8730006ed62c8730004ff7648730004fd764873008cfc76487300d67e65487300067d6548730005bf7448730095bc7448730005df734873008ddc7348730006ee6248730006ed6248730024fe76d953007e7e65d953001cfe74d9530004fd74d953001cfc74d953007e7f54d953008cfe73d953000cfd73d953008cfc73d953007e7f53d9530004fe72d9530004fd72d953007e7c52d9530014fe71d9530004fd71d9530014fc71d95300067e51d953007e7
  | 14 => 0x8e7c73597300067f435973008e7e435973008e7c43597300067f72597300067e72597300067d72597300067c72597300067f42597300067c425973008e7f325973008e7c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067e41597300067c415973008e7f31597300067e315973008e7c31597300067e21597300067c215973026e7f705973026e7e705973026e7d705973026e7c705973026e7f405973026e7e405973026e7d405973026e7c405973008e7f305973026e7e305973026e7d305973008e7c305973026e7f205973026e7e205973026e7d205973026e7c205973026e7f105973026e7e105973026e7d105973026e7c1059730024fe75d933008e7e75d93300247e75d9330004fd75d933008e7d75d93300047d75d933008cfc75d933023cfd74d9330096be54d933008cfe73d933008ede73d933008ebf43d9330004fe72d933008eee72d9330004ee72d9330004fd72d933008eed72d9330004ed72d9330096bc42d9330014fe71d9330004fd71d9330014fc71d933008ef970d933001cff76593300067e65593300067d655933008ebc6459330004ff7559330024fe7559330024fc755933008ebf745933001cff735933000cfe735933001cfd735933000cfc735933008ebe435933008ebc4359330004ff7259330004fc7259330096bc4259330004ff7159330014fe7159330014fc7159330096bf415933023ebf405933023ebd4059330004ff765533008cfe7655330004fd765533008cfc76553300267e65553300067d6555330006bf645533001ebc6455330005fb705533000df8705533000ddd7694f3008edd7694f3000cdd7694f30026de6594f3008f5e6594f300265e6594f3008f5d6594f3008edc6594f3000dde7094f3008fda7094f3008fd97094f3000ddc7094f303b4ff7654f300267e6554f3026e7d6554f3026fda3054f303b5df7654f303bedf7654f3008f5f7554f30026de6554f3009f5e6554f300265e6554f3026f5d6554f30026dc6554f3009f5f5254f3009f5f5154f3000dde7054f3000ddc7054f3026f5e5054f3026f5c5054f303acff7650f3024e7e6550f300067d6550f3008ebf6450f3008ebc6450f300067e6598b300067d6598b3008eef6298b30024fe7598b30004fd7598b30024fc7598b3001cfe7498b30004fd7498b3001cfc7498b3000cfe7398b30006ef4298b30006ec4298b3008eef3298b3008eec3298b30014fe7198b30004fd7198b30014fc7198b30186ed2098b300067e6558b300067d6558b30005bf7458b30095bc7458b3008eec6258b30004ff7558b30024fe7558b30024fc7558b30004ff7458b30006bf7458b30004bf7458b3001cfe7458b3001cfc7458b30006bc7458b3001cbc7458b3000cfc7358b30006ef4258b30006ec425
  | 15 => 0xe7290940006bf6290940007af6290940006bc6290940007ac6290940006ac62909401febe61909401febc619094000dbe70909401f7ba7090940007b9709094000dbc709094001ebf609094001fbb6090940004fe76cc940004fd76cc94008cfc76cc94001dbe74cc940005bd74cc940004fe768c940004fd768c940004fc768c940005bf748c94001dbc748c940006ef628c940006ec628c940004ff764c940004fe764c940004fc764c940005bf744c94001dbc744c940006ef624c940006ec624c940005f7714c9400a5f4714c940004fe760c940004fd760c94008cfc760c9400ad7e750c9400057d750c94001dbe740c940005bd740c94000dfa700c940005f9700c940014fe76d85400a6f661d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540014fc74d85403cebe54d8540006bd54d854008cfe73d8540004fd73d85403cebf43d8540006bd43d8540004fe72d8540004fd72d8540006be42d85403cebc42d85400a6f641d85403cef541d854001cfd70d854030ef710d85400057f75585400ad7c7558540005df7358540005dc7358540005ef7258540005ec72585400a6f461585403c5fb7058540004ff7654540004fe7654540004fc7654540004fe76cc540004fd76cc54008cfc76cc54001dbe74cc540005bd74cc540004ff764c540004fe764c540004fc764c540004fe76c8540004fd76c8540004fc76c8540004ff7648540004fe7648540004fc7648540005bf744854001dbc7448540005df7348540005dc734854026cfd75d973001cfe74d9730004fd74d973008cfc74d973008cfe73d973008ede73d9730004fe72d9730004fd72d9730014fe71d9730004fd71d9730014fc71d973008ef970d973026c7d769973009f3e749973009f3d749973008e7f64997300067e649973008e7c649973008f5e739973008e7e639973008e7f629973008e7c629973008e7f61997300067e619973008e7c61997303b67d60997303b75e309973008f7a309973008f5c3099730024ff765973008e7c655973008e7f7559730004ff745973001cfe745973001cfc745973009e7f54597300067e545973009e7c5459730024ff735973000cfe7359730024fd735973000cfc735973008e7e535973008e7c5359730004ff7259730004fc725973009e7f525973009e7c5259730004ff7159730014fe7159730014fc715973009e7f51597300067e515973009e7c515973026e7f505973026e7d505973008d7f765973009e7f76597300247f765973008e7f64597300067e645973008e7c645973008f5e735973008e7f625973008e7c625973008e7f61597300067e615973008e7c615973026f5e305973008f7a305973008f5c30597300067f74597300067e74597300067d74597300067c745973009e7f735973008e7e7359730
  | 16 => 0x51400073f6555140026be6555140026bc65551400af3c6555140005bf7355140005bc72551400af3f5255140007bb705514000dbe705514000dbc705514029fb8705514001ebf605514001fbb605514029f3e505514029f3c5055140024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d403eede43d8d403eedd43d8d40004fe72d8d40004fd72d8d403eebc42d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d4001cfd70d8d403aedf30d8d400ad7e7598d400057d7598d40006df6398d40005ee7298d40005ed7298d40075f97098d40095fb7058d40006dd6318d40024fe7518d40004fd7518d4008cfc7518d4000cfd7418d4008ebd7418d403e6be5418d40006bd5418d4008ebf4318d4008ede4318d403e6dd4318d40004fe7218d40004fd7218d403e6bc4218d40014fe7118d40004fd7118d40014fc7118d40006de3118d4008edc3118d4008cff7018d4001cfd7018d4008edf3018d40396dd3018d40004fe7694d40004fd7694d4008cfc7694d4001dbe7494d40005bd7494d400af5f5394d4000dfa7094d40005f97094d40004ff7654d40004fe7654d40004fc7654d400067f6554d400267c6554d4001dbe7454d4000dbc7650d4023ebc7650d4000cbc7650d40005bf7550d40005bd7550d4001dbf7350d4001f9f7350d400079f6350d4008ebc6350d400079c6350d40005bc7250d40007bb7050d4000dbe7050d4000dbc7050d4023fb87050d4001ebf6050d4001fbb6050d40024fe75d8940004fd75d8940024fc75d894000cfd74d894036ebd74d894008cfe73d8940004fd73d8940006ef52d8940006ec52d89403deee42d89403deed42d89403debc42d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d894001cfd70d894036eef20d8940006ef6298940045f970989400057f75589400ad7c7558940065fb7058940006ed6218940024fe7518940004fd7518940024fc75189401c6bf741894000cfd74189403d6be5418940006bd541894008cfe7318940004fd73189403d6bf4318940006bd4318940006ef5218940006ec52189403d6ee42189403d6ed42189401c6bc4218940014fe7118940004fd7118940014fc7118940006ee2118940006ec211894001cfd70189401c6be40189401c6bc40189401c6ed2018940004fe7694940004fd7694940004fc76949400067f65949400267c659494001dbc74949400af6f5294940004ff7654940004fe7654940004fc7654940005bf745494001dbc74549400073d5454940005fb705494000df8705494000dbe76909401f6be769094000cbe7690940005bf7590940005bd7590940006bf6590940206be6590940006bd6590940206bc6590940005bd7390940006bf6390940006bc639094001dbe729094001fa
  | 17 => 0x38efb50189503667e50189503667c5018950366f85018950366ed2018950004fe7690950004fd7690950004fc7690950006bf649095001ebe649095001ebc6490950006bf7690950006be7690950006bd7690950006bc76909501f6bf6590950006bf6390950006bc63909501c5be7290950006bf6290950006bc62909501febe61909501febc61909501f6bf6090950207bb50909501f73e50909501f73c50909501f7b85090950004ff7650950004fe7650950004fc765095001ebf76109500bebe76109500bebd761095001ebc76109500bf3e75109500bf3d75109501c6bf6510950006bf6310950006bc63109501f5be72109500bfae7210950006bf6210950007af6210950006af6210950006bc6210950007ac6210950006ac62109501cebe61109501cebc61109501c6bf60109501d7bb50109501c73e50109501c73c50109501c7b85010950004fe76cc950004fd76cc95008cfc76cc9500bdbe74cc950005bd74cc950004fe768c950004fd768c950004fc768c950004ff764c950004fe764c950004fc764c950005bf744c9500bdbc744c950005f7714c9500b5f4714c950004fe760c950004fd760c95008cfc760c9500257e750c9500057d750c950014fe76d85500b6f661d855000cfd75d8550014fc75d855001cfe74d8550004fd74d855001cfc74d855008cfe73d8550004fd73d8550004fe72d8550004fd72d8550006be42d8550006bc42d85500b6f651d855041ef551d8550024fd70d855041efb50d8550346f850d8550346f710d85500b6f46158550415fb7058550004ff7650550004fe7650550004fc7650550004fe76cc550004fd76cc55008cfc76cc550004ff764c550004fe764c550004fc764c550004fe76c8550004fd76c8550004fc76c8550004ff7648550004fe7648550004fc7648550005bf74485500bdbc7448550005df7348550005dc7348550024fe76d95400ae7e65d954029cfd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d954040e7f54d954040e7d54d954008cfe73d9540004fd73d95400ae7f53d9540004fe72d9540004fd72d95400ae7c52d954040ebc42d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400ae7c51d954001cff70d954001cfd70d95403fe7f50d95403fe7d50d9540024ff76595400ae7c65595403f5bf7459540005ef7259540005ec7259540405fb70595403fcff75595400067f75595403f4ff7459540006bf7459540004ff735954008cfc7359540004ff7259540006ef7259540004ef7259540004fc7259540006ec7259540004ec72595400bebc4259540004ff7159540014fe7159540014fc715954029cff7059540006fb705954029e7e505954029e7c505954000dbc7655140026bc765514000cbc765514001dbf755514001f3f755
  | 18 => 0xf734c921007cf634c92108eee634c92108eec634c921007cc634c921007e7714c921015ee714c921015ec714c92116fe4714c92116eef614c92116fe7104c92118cfe760c9210d57e750c9210057d750c921006bf640c921156bc640c921006df630c92108edc630c92118dee720c921007b764c8521007b464c8521007d763c8521006f663c8521006f463c8521007d463c8521006d463c8521015f672c8521017e672c8521016f762c8521017e762c8521007b642c8521007b442c8521007e632c8521007e532c8521005f570c852100cfe76d8121006bf64d8121006bc64d8121006df63d8121006dc63d81210c6fa60d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d812108cfe73d8121004fd73d8121014fd72d8121006be42d8121006bc42d812100cfc71d8121006fb50d81210c6f850d81210c6fa20d81210c6fa10d81210057f75581210d57c7558121005bf74581210cdbc7458121006bf6458121006bc6458121005df7358121005dc7358121006df6358121006dc63581210c6f8605812101cfe76d91500bebe64d915000cfd75d915001cfc75d91500bebe54d915042ebd54d915008cfe73d9150004fd73d9150004fe72d9150004fd72d91500bebc42d9150014fe71d9150004fd71d9150014fc71d9150024fd70d91503f67e50d91503f67c50d91503f6bf40d91500bebc6459150005ef7259150005ec7259150425fb705915000cfd75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d5039ede53d8d5039edd53d8d50004fe72d8d50004fd72d8d50014fe71d8d50004fd71d8d50014fc71d8d50024fd70d8d503b67e50d8d503b67c50d8d503b6df30d8d50006df6398d5007df97098d5009dfb7058d50006dd6318d5000cfd7518d5001cfe7418d50004fd7418d5008cfc7418d5008ede5318d503bedd5318d50004fe7218d50004fd7218d50014fe7118d50004fd7118d50014fc7118d5008cff7018d50024fd7018d5008edf3018d503a6dd3018d50004fe7690d50004fd7690d5008cfc7690d50004ff7650d50004fe7650d50004fc7650d500bdbe74d8950005bd74d895000cfd75d895001cfe74d8950006be74d895001cbe74d8950004fd74d8950006bd74d8950004bd74d895001cfc74d895008cfe73d8950004fd73d895035eee52d895035eed52d8950006ef42d8950006ec42d8950014fe71d8950004fd71d8950014fc71d8950024fd70d8950376ef20d8950006ef629895004df97098950005bf74589500bdbc7458950055fb7058950006ed621895000cfd751895001cfe7418950004fd741895001cfc741895008cfe7318950004fd731895038eee521895038eed5218950006ef4218950006ec4218950014fe7118950004fd7118950014fc7118950024fd7018950
  | 19 => 0x4d2127ebc6454d21006df6354d21006dc6354d2108cff7690d21004fe7690d21004fd7690d2108cfc7690d21006bf6490d2101ebc6490d21006df6390d2108edc6390d21005ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d2101ebc6450d21006df6350d21006dc6350d2143cfe7694921006bf6494921236bc6494921006df6394921006dc63949210d76f529492122fe42194921024ff7654921014fe7654921214fd7654921014fc76549210067f65549210267c6554921005bf74549210cdbc7454921006bf645492121ebc6454921006df6354921006dc6354921005f77154921015f47154921217e42154921005fb70549210c5f870549211ccfe76909211febf649092101ebe6490921006bd649092101ebc6490921006df6390921006dc63909211cdbe7690921006be76909211ccbe7690921006bf6590921206be6590921006bd6590921206bc6590921006bf63909210079f63909210069f6390921006be6390921006bd6390921006bc63909210079c63909210069c63909211cdbe72909211febf62909211febf61909211ffae21909211ffac21909211ffb421909211f6be60909211f6bc60909211ffb7109092101cff7650921014fe76509211e4fd7650921014fc7650921006bf645092101ebc6450921006df6350921006dc63509210cfac4250921005f77150921015f471509211fdbe76109210cebe76109211fcbe76109210cf3e75109210cf3d7510921006bf65109211d6be6510921006bd65109211d6bc6510921006bf63109210079f63109210069f6310921006be6310921006bd6310921006bc63109210079c63109210069c63109211fdbe72109210cfae72109211cebf6210921437af5210921437ac52109211cebf61109211cfae21109211cfac21109211cfb421109211c6be60109211c6bc60109211cfb71010921014fe76cc921014fc76cc9210cdbe74cc921005bd74cc921006bf64cc9211b6bc64cc921006df63cc92108edc63cc921015f671cc921005f571cc92114cfe768c921006bf648c921196bc648c92118edf638c921006dc638c921007ae428c921007ac428c92114dee768c921006ee768c921007af648c921007ac648c92116ded738c92118fcf638c92108eee638c92108eec638c921007cc638c921006cc638c921015ee718c921015ec718c92118eef618c92118fce318c92118fcc318c92118fe7108c92108cff764c921014fe764c92116cfd764c921014fc764c921005bf744c9210cdbc744c921006bf644c921176bc644c921006df634c921006dc634c921007ae424c921007ac424c921005f7714c921015f4714c921015ec764c92116eec764c921014ec764c921007af744c921007ac744c921007af644c921007ac644c921007c
  | 20 => 0x8ebe7498d2101cbe7498d21004fd7498d2108ebd7498d21004bd7498d2108cfc7498d2108cfe7398d2114cde7398d2116cfd7298d2108eed7298d211acfd7198d2108ef57198d211aef42198d2100cfe7098d21004fd7098d2100cfc7098d211aef71098d21005bf7458d210cdbc7458d21006bf6458d21006bc6458d211adef7258d21004ff7558d21024fe7558d21024fc7558d21004ff7458d21006bf7458d21004bf7458d2101cfe7458d2101cfc7458d21006bc7458d2101cbc7458d21006df7358d211acff7258d21006ef7258d2116cff7158d21006f77158d21004f77158d21004ff7058d2100cfe7058d2100cfc7058d2118cfe7618d210d57e7518d210057d7518d21006bf6418d21006bc6418d21006dd6318d21024fe7518d2108e7e7518d210247e7518d21004fd7518d2108e7d7518d210047d7518d2108cfc7518d2101cfe7418d21004fd7418d2108cfc7418d2108ede7318d21006df5318d2108edc5318d21006df4318d2108edc4318d2108eed7218d2108cff7118d2114cfd7118d2108edf3118d2114edd3118d2114ef42118d2100cfe7018d21004fd7018d2100cfc7018d21006de3018d2108edc3018d2114ef71018d2118dde7618d21006de7618d2118cde7618d210075e7518d210075d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d2114fcd7218d2114fce2118d2114fcc2118d2114fd42118d21006de6018d21006dc6018d2114fd71018d2108edf7518d21006de7518d210065e7518d21006dd7518d210065d7518d2108edc7518d2108edf7418d21006de7418d21006dd7418d2108edc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d2108edf7218d2114edd7218d2114ecd7218d21006df5218d21006dc5218d21006df4218d21006dc4218d2108edf7118d2114ede7118d2114edd7118d2108edc7118d2114edf5118d2114ede5118d2114edd5118d2114edc5118d2114edf4118d2114ede4118d2114edd4118d2114edc4118d2114edf2118d2114ede2118d2114edd2118d2114edc2118d2114ed42118d2108edf7018d21006de7018d21006dd7018d2108edc7018d21006df5018d21006de5018d21006dc5018d21006df4018d21006de4018d21006dc4018d21006de2018d21006dc2018d2114edf1018d2114ed71018d2114ede1018d2114edd1018d2114edc1018d2108cff7694d21004fe7694d21004fd7694d2108cfc7694d21006bf6494d21296bc6494d21006df6394d2108edc6394d210d75f5394d21005ee7294d21005ed7294d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210267e6554d210067d6554d21006bf645
  | 21 => 0xf51d91211febe51d91211febd51d91211febc51d91211febf31d91211febe31d91211febd31d91211febc31d91211febf21d91211febe21d91211febc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bc50d9121006be30d9121006bc30d9121006be20d9121006bc20d91211febf10d91211febe10d91211febd10d91211febc10d91210cebc6459121005df7359121005dc7359121445ef7259121004ff7559121024fe7559121024fc75591211fcff7459121006bf7459121004ff7359121006df7359121004df735912108cfc7359121006dc7359121004dc7359121444ff7259121006ef72591210cebc42591211e4ff7159121006f77159121004ff705912100cfe705912100cfc70591211fdbe76191210cebe76191211fcbe7619121006bf6519121006be6519121006bd6519121006bc65191211cebf62191211cebf61191211cfae21191211cfac21191211cfb42119121006be6019121006bc60191211cfb71019121004ff7655121004fe7655121004fd7655121004fc7655121006bf645512101ebc6455121005ef7255121005ec7255121006bf64d8d21006bc64d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d21006dc53d8d21006df43d8d21006dc43d8d2118cff71d8d2118cfd71d8d2118edf31d8d2118edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d210069c64d8d2118fcf72d8d2118fce21d8d2118fcc21d8d2118fd421d8d21006de60d8d21006dc60d8d2118fd710d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d2118edf72d8d2118edd72d8d21006df52d8d21006dc52d8d21006df42d8d21006dc42d8d2118edf71d8d2118ede71d8d2118edd71d8d2118edc71d8d2118edf51d8d2118ede51d8d2118edd51d8d2118edc51d8d2118edf41d8d2118ede41d8d2118edd41d8d2118edc41d8d2118edf21d8d2118ede21d8d2118edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dc50d8d21006df40d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d2118edf10d8d2118ede10d8d2118edd10d8d2118edc10d8d210cdbe7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d2116ded7298d21024fe7598d21004fd7598d2108cfc7598d2101cfe7498d21
  | 22 => 0xcb211adef764cb21006ef764cb21007af744cb21007ac744cb21007cf734cb2108eee634cb2108eec634cb21007e7714cb21015ee714cb21015ec714cb2116fe4714cb21015e4714cb2116fe4314cb21014ff760cb21014fd760cb210ed7e750cb210057d750cb2108ede630cb21006dd630cb21015f6710cb21005f5710cb2114fd4310cb21005f576cc721006f576cc721015f673cc721017d673cc721006f763cc721007d663cc721006f563cc721007d563cc721007e672cc721005f572cc721007e572cc721016f662cc721017e662cc721007b642cc721007b442cc721007e632cc721007e532cc7210ed7e75d83210057d75d83210defa60d832100cff76583210def86058321004ff7558321024fe7558321024fc7558321004ff745832101cfe745832101cfc7458321004ff735832108cfc7358321014fc7258321006be4258321006bc4258321006f7315832103ef4315832103ef621583210def820583210defa1058321024fe76d95210d67e65d952101cfe74d9521004fd74d952101cfc74d952108cfe73d9521004fd73d9521014fd72d95210d67f52d952122cff71d952122cfd71d952122e7f51d952122e7d51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210d67c50d952122ef710d95210d67c6559521005bf74595210cdbc7459521005df7359521005dc735952144def7259521005fb70595210c5f8705952122cff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc7459521004ff7359521006df7359521004df735952108cfc7359521006dc7359521004dc73595210d67f535952144cff7259521006ef7259521214ff7159521006f77159521004ff7059521006fb7059521004fb705952100cfe705952100cfc7059521006f8705952100cf87059521216f7105952101cfe76d91210cebe64d9121024fe75d9121004fd75d9121024fc75d9121006bf54d91210cebe54d91210cebc54d912108cfe73d9121004fd73d91210cebf43d91210cebc43d9121014fd72d91210cebf42d91211fcff71d91211fcfd71d91211febf41d91211febd41d912100cfe70d9121004fd70d912100cfc70d91210cebf40d9121006be40d91210cebc40d91211cdbe76d912101cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d91211ffae21d91211ffac21d91211ffb421d9121006be60d9121006bc60d91211ffb710d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006bc53d91211febf72d91210cebe72d91211febd72d9121006bf52d9121006bc52d91211febf71d91211febe71d91211febd71d91211febc71d91211feb
  | 23 => 0x24fc7558f21004ff7458f2101cfe7458f2101cfc7458f21006df7358f21006f77158f2116edf3158f2116edd3158f2116ef43158f21004ff7058f2100cfe7058f2100cfc7058f210ed7e7518f210057d7518f21006dd6318f2118dee7218f2114fd43118f21024fe7518f2108e7e7518f210247e7518f21004fd7518f2108e7d7518f210047d7518f2108cfc7518f2101cfe7418f21004fd7418f2108cfc7418f2108cfe7318f2108ede7318f2118cfe7218f2108eee7218f2108ef57118f2114ede3118f2108edc3118f2100cfe7018f21004fd7018f2100cfc7018f2108cff7694f21004fe7694f21004fd7694f2108cfc7694f210ef5f5394f21005ee7294f21005ed7294f21004ff7654f21004fe7654f21004fd7654f21004fc7654f210267e6554f210067d6554f21005f77154f21015f47154f2108cff7690f21004fe7690f21004fd7690f2108cfc7690f21005ee7290f21005ed7290f21004ff7650f21004fe7650f21004fd7650f21004fc7650f21006bf6450f2101ebc6450f21005f77150f21015f47150f21014ff7694b21024fe7694b21014fd7694b210267e6594b210067d6594b210ef6f5294b21015f67194b21005f57194b2122fe62194b2144cff7654b21005bf7454b210e5bc7454b21217e62154b21005fb7054b210ddf87054b21014ff7690b2101cfe7690b21014fd7690b2101ebe6490b21006bd6490b21015f67190b21005f57190b211febf7690b2101ebe7690b2101ebd7690b211febc7690b21006bf6590b21206be6590b21006bd6590b21206bc6590b21006bf6390b21006be6390b21006bd6390b21006bc6390b211febe6290b211ffb67190b21007b57190b211ffb43190b211ffae2190b211ffb62190b211ffac2190b211f6be6090b211f6bc6090b21444ff7650b210e7ac4250b2101ebf7610b210e6be7610b211cebd7610b2101ebc7610b210e73e7510b210e73d7510b21006bf6510b211d6be6510b21006bd6510b211d6bc6510b21006bf6310b21006be6310b21006bd6310b21006bc6310b210e7ae7210b211cebe6210b21457af5210b21457ac5210b211cfb67110b210e7b57110b211cfb43110b211cfae2110b211cfb62110b211cfac2110b211c6be6010b211c6bc6010b2116cfd76ccb210e5be74ccb21005bd74ccb21015f471ccb21014ff768cb21014fd768cb21006de638cb21006dd638cb21007ae428cb21007ac428cb21015f6718cb21005f5718cb2118fd4318cb21015ed768cb2118eed768cb21014ed768cb2108eee638cb21007ce638cb21007cd638cb2108eec638cb21015ee718cb2118fe6718cb21007e5718cb21015ec718cb2118fce318cb2118fcc318cb2118fe4318cb2118fc4318cb211acff764cb21005bf744cb210e5bc744cb21007ae424cb21007ac424cb21015f4714
  | 24 => 0xe768c93118edf638c931006ef628c931006ec628c931015f6718c931005f5718c93118fd4318c931014fc764c931005bf744c9310fdbc744c931006ef624c931006ec624c931005f7714c931015f4714c9311acfe760c9311057e750c9310057d750c93114edf630c93108fd4310c931015f673cc531017d673cc531016f763cc531017d763cc531006f462cc531007b642cc531007b442cc53100cfe76d81310f6fa60d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d8131014fd73d8131004fe72d8131004fd72d8131006be42d8131006bc42d8131006f731d8131086f431d81310f6fa30d81310f6fa10d81310057f75581311057c7558131005bf74581310fdbc7458131005ef7258131005ec72581310f6f860581310ee7e65d972143dee72d9721214fd75d972101cfe74d9721004fd74d972101cfc74d972108cfe73d9721004fd73d972143cfe72d9721006ee72d9721006f571d972100cfe70d9721004fd70d972100cfc70d9721024ff76597210ee7c6559721005fb70597210ddf870597210067f7559721004ff745972101cfe745972101cfc74597210ee7f5459721004ff735972108cfc73597210ee7f5359721014fc72597210ee7c52597212167f51597212167d5159721004ff7059721006fb7059721004fb705972100cfe705972100cfc7059721006f8705972100cf870597210067e50597210ee7c50597210e6be64d93211cdee72d9321024fe75d9321004fd75d9321024fc75d93211e4fd74d93210e6be54d932108cfe73d9321004fd73d93210e6bf43d93211ccfe72d9321006ee72d9321006f571d93211febe41d93211febc41d932100cfe70d9321004fd70d932100cfc70d932101cff76593210e6bc6459321004ff7559321024fe7559321024fc7559321006bf7459321004ff735932108cfc7359321014fc72593210e6bc42593211e6bf41593211e6bd4159321004ff705932100cfe705932100cfc7059321004ff7655321004fe7655321004fd7655321004fc76553210267e65553210067d6555321006bf645532101ebc6455321005ef7255321005ec725532114dee72d8f2118fd431d8f21024fe75d8f21004fd75d8f21024fc75d8f2101cfe74d8f21004fd74d8f2101cfc74d8f2114cfe72d8f21006ee72d8f21006f571d8f2118ede31d8f2118edc31d8f2118ef431d8f2100cfe70d8f21004fd70d8f2100cfc70d8f2116cfd7698f210e5be7498f21005bd7498f21006df6398f21024fe7598f21004fd7598f2108cfc7598f2101cfe7498f2108ebe7498f2101cbe7498f21004fd7498f2108ebd7498f21004bd7498f2108cfc7498f2108eee7298f2108edf3198f211aedd3198f2100cfe7098f21004fd7098f2100cfc7098f21004ff7558f21024fe7558f21
  | 25 => 0x9131006be40d91310febc40d91310febc645913146ddf7359131005ef7259131005ec7259131004ff7559131024fe7559131024fc755913125cff7459131006bf745913146cff7359131006df7359131004ff7259131006ef7259131004ef7259131004fc7259131006ec7259131004ec72591310febc4259131244ff7159131006f77159131004ff705913100cfe705913100cfc7059131004ff7655131004fe7655131004fd7655131004fc7655131006bf645513101ebc6455131464fe7694d311075f5394d3108fd43194d31024ff7654d31014fe7654d31274fd7654d31014fc7654d310067f6554d310267c6554d31005f77154d31015f47154d31277d43154d3145cfe7690d3108fd43190d3101cff7650d31014fe7650d31244fd7650d31014fc7650d31006bf6450d3101ebc6450d31005f77150d31015f47150d31247d43150d310fdbe74d8931005bd74d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931006be74d893101cbe74d8931004fd74d8931006bd74d8931004bd74d893101cfc74d8931006ef42d8931006ec42d89311aeef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931006ef6298931005bf74589310fdbc7458931006ed6218931024fe7518931004fd7518931024fc751893101cfe7418931004fd741893101cfc7418931006ef4218931006ec421893114ede311893114edc311893114ef4311893114eed211893100cfe7018931004fd701893100cfc7018931006ee2018931006ec2018931004fe7694931004fd7694931004fc7694931006ef6294931006ec62949311076f5294931004ff7654931004fe7654931004fc7654931005bf74549310fdbc7454931006ef6254931006ec6254931005fb70549310f5f87054931004fe7690931004fd7690931004fc7690931006bf649093101ebe6490931006bd649093101ebc6490931006bf7690931006be7690931006bd7690931006bc7690931006bf6590931206be6590931006bd6590931206bc65909311febf63909311cdbe7290931006bf6290931006bc62909311febf61909311ff9e31909311ff9c31909311ffb431909311f6be60909311f6bc6090931004ff7650931004fe7650931004fc765093101ebf76109310febe76109310febd761093101ebc76109310ff3e75109310ff3d7510931006bf65109311d6be6510931006bd65109311d6bc65109310ff9e73109310ff9d73109311cebf63109311fdbe72109310ffae7210931006bf6210931007af6210931006af6210931006bc6210931007ac6210931006ac62109311cfb671109310ffb571109311cebf61109311cf9e31109311cf9c31109311cfb431109311c6be60109311c6bc601093114cfe76cc9310fdbe74cc931005bd74cc931014f
  | 26 => 0x18edc3198b3118eed2198b3100cfe7098b31004fd7098b3100cfc7098b31005bf7458b31115bc7458b3108eec6258b31004ff7558b31024fe7558b31024fc7558b31004ff7458b31006bf7458b31004bf7458b3101cfe7458b3101cfc7458b31006bc7458b3101cbc7458b31014fc7358b3108eef3258b3108eec3258b31006f77158b3116eef2158b3116ef42158b31004ff7058b3100cfe7058b3100cfc7058b3116ef71058b31004ff7694b3108cfe7694b31004fd7694b3111f6f5294b31004ff7654b31004fd7654b3108cfc7654b310267e6554b310067d6554b31005bf7454b31115bc7454b31005f77154b31015f47154b31005fb7054b3110df87054b31004ff7690b3108cfe7690b31004fd7690b31006bf6490b3101ebe6490b31006bd6490b3101ebc6490b31006bf7690b31006be7690b31006bd7690b31006bc7690b31006bf6590b31206be6590b31006bd6590b31206bc6590b311febe6390b31006be6290b31006bd6290b311ff9e3190b311ffb63190b311ff9c3190b311ffb42190b311f6be6090b311f6bc6090b311ffb71090b31004ff7650b31004fd7650b3108cfc7650b31005f77150b31015f47150b3101ebf7610b31116be7610b31116bd7610b3101ebc7610b311173e7510b311173d7510b31006bf6510b311d6be6510b31006bd6510b311d6bc6510b311179e7310b311179d7310b311cebe6310b31117ae7210b31006be6210b31006bd6210b311cf9e3110b311cfb63110b311cf9c3110b311cfb42110b311c6be6010b311c6bc6010b311cfb71010b3116cfd768cb3118ede638cb31015f4718cb3118cff764cb31005bf744cb31115bc744cb31015f4714cb3100cff765833108ef86058331004ff7558331024fe7558331024fc7558331004ff745833101cfe745833101cfc7458331014fc7358331004ff7258331004fc7258331006be4258331006bc425833108efb305833108ef8305833110efa1058331024fe76d95311067e65d953101cfe74d9531004fd74d953101cfc74d9531014fd73d95311067f53d9531004fe72d9531004fd72d953108cff71d953128cfd71d953128e7f51d953128e7d51d953100cfe70d9531004fd70d953100cfc70d95310067e50d95311067c50d95311067c6559531475df735953128cff75595310067f7559531004ff745953101cfe745953101cfc7459531474ff7359531006df7359531004ff7259531004fc7259531274ff7159531006f77159531004ff705953100cfe705953100cfc705953101cfe76d91310febe64d9131024fe75d9131004fd75d9131024fc75d91310febe54d9131014fd73d91310febf43d9131004fe72d9131004fd72d91310febc42d913108cff71d913125cfd71d913125ebf41d913125ebd41d913100cfe70d9131004fd70d913100cfc70d
  | 27 => 0xe729094101fae7290941006bf6290941007af6290941006bc6290941007ac6290941006ac6290941015be71909411ffb67190941007b57190941015bc719094101ebf619094101fb761909411f6be60909411f6bc6090941004fe76cc941004fd76cc94108cfc76cc94101dbe74cc941005bd74cc941006ef62cc941006ec62cc941004fe768c941004fd768c941004fc768c941005bf748c94101dbc748c941006df638c941006dc638c941004ff764c941004fe764c941004fc764c941005bf744c94101dbc744c941005f7714c941015f4714c941004fe760c941004fd760c94108cfc760c94112d7e750c9410057d750c94101dbe740c941005bd740c941006df630c94108edc630c941006ef620c941006ec620c941015f6710c941005f5710c94100cfe76d8141126fa60d8141024fe75d8141004fd75d8141024fc75d8141014fd74d814100cfc74d81413c6be54d8141006bd54d814108cfe73d8141004fd73d81413c6bf43d8141006bd43d8141004fe72d8141004fd72d8141006be42d81413c6bc42d814101cfd71d8141126fa40d8141126fa10d81410057f755814112d7c7558141005df7358141005dc7358141005ef7258141005ec7258141126f86058141274fd75d973101cfe74d9731004fd74d973108cfc74d973108cfe73d973108ede73d973108e7f53d9731004fe72d9731004fd72d973108ef571d973100cfe70d9731004fd70d973100cfc70d973128ef710d9731024ff765973108e7c655973108e7f7559731004ff745973101cfe745973101cfc7459731014fe7359731014fc735973108e7e535973108e7c5359731004ff7259731004fc725973111e7f52597312767f51597312767d5159731004ff705973100cfe705973100cfc70597310067e505973111e7c5059731276f71059731024fe75d9331004fd75d933108cfc75d9331244fd74d9331116be54d933108cfe73d933108ede73d933108ebf43d9331004fe72d9331004fd72d9331116bc42d933108ef571d933100cfe70d9331004fd70d933100cfc70d933101cff765933108ebc6459331004ff7559331024fe7559331024fc755933108ebf7459331014fe7359331014fc735933108ebe435933108ebc4359331004ff7259331004fc7259331116bc4259331246bf4159331246bd4159331004ff705933100cfe705933100cfc7059331116bf4059331004ff765533108cfe7655331004fd765533108cfc7655331006bf645533101ebc6455331005f77155331015f47155331474ff7654f3108e7f6554f3108e7c6554f31277d63154f3146cff7650f3108ebf6450f3108ebc6450f3108eef6298b31024fe7598b31004fd7598b31024fc7598b3101cfe7498b31004fd7498b3101cfc7498b31014fe7398b3108eef3298b3108eec3298b3118ede3198b31
  | 28 => 0x5141026bc7655141014bc765514101dbf755514101f3f75551410073f6555141026be6555141026bc655514112f3c6555141005bf7355141005bc725514112f3f5255141007b77155141015be7155141015bc71551412a7b4715514101ebf615514101fb7615514149f3e505514112f3c5055141024fe75d8d41004fd75d8d41024fc75d8d41014fd74d8d41496de43d8d41496dd43d8d41004fe72d8d41004fd72d8d41496bc42d8d4101cfd71d8d4146edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d41006df6398d410fdf57198d41005ef7258d41005ec7258d41115f77158d41006dd6318d41024fe7518d41004fd7518d4108cfc7518d41014fd7418d4108ebd7418d4148ebe5418d41006bd5418d4108ebf4318d4108ede4318d4148edd4318d41004fe7218d41004fd7218d4148ebc4218d4108cff7118d4101cfd7118d4108edf3118d4145edd3118d4100cfe7018d41004fd7018d4100cfc7018d41006de3018d4108edc3018d41004fe7694d41004fd7694d4108cfc7694d4101dbe7494d41005bd7494d41006df6394d4108edc6394d4112f5f5394d41004ff7654d41004fe7654d41004fc7654d4101dbe7454d41006df6354d41006dc6354d41015bc7650d41246bc7650d41014bc7650d41005bf7550d41005bd7550d4101dbf7350d4101f9f7350d410079f6350d4108ebc6350d410079c6350d410069c6350d41005bc7250d41007b77150d41015be7150d41015bc7150d41247b47150d4101ebf6150d4101fb76150d41024fe75d8941004fd75d8941024fc75d8941014fd74d8941446bd74d894108cfe73d8941004fd73d8941486ee42d8941486ed42d8941486bc42d894101cfd71d8941446ef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d8941006ef62989410cdf57198941005df7358941005dc73589410e5f77158941006ed6218941024fe7518941004fd7518941024fc75189411cebf7418941014fd741894147ebe5418941006bd541894108cfe7318941004fd731894147ebf4318941006bd431894147eee421894147eed42189411cebc421894101cfd71189411cebe41189411cebc41189411ceed211894100cfe7018941004fd701894100cfc7018941006ee2018941006ec2018941004fe7694941004fd7694941004fc769494101dbc7494941006ef6294941006ec629494112f6f5294941004ff7654941004fe7654941004fc7654941005bf745494101dbc74549410073d5454941006ef6254941006ec6254941005fb7054941125f87054941015be76909411febe7690941014be7690941005bf7590941005bd7590941006bf6590941206be6590941006bd6590941206bc6590941005bd7390941006bf6390941006bc639094101db
  | 29 => 0x8cfe73d8951004fd73d89514ce7f53d89510067d53d89514ceee52d89514ceed52d8951024fd71d895144eef21d895100cfe70d8951004fd70d895100cfc70d895144ef710d8951006ef62989510d5f57198951005bf745895113dbc7458951005df7358951005dc73589510edf77158951005fb7058951135f87058951006ed6218951014fd751895101cfe7418951004fd741895101cfc741895108cfe7318951004fd73189514c6ee52189514c6ed5218951024fd711895143eed211895100cfe7018951004fd701895100cfc7018951004fe7690951004fd7690951004fc7690951006bf649095101ebe649095101ebc6490951006bf7690951006be7690951006bd7690951006bc76909511febf6590951006bf6390951006bc63909512073f53909510073d53909511cdbe7290951006bf6290951006bc62909511febf6190951207b751909511ff3e51909511ff3c51909511ffb451909511f6be60909511f6bc60909511ffb71090951004ff7650951004fe7650951004fc765095101ebf761095113ebe761095113ebd761095101ebc761095113f3e751095113f3d75109511cebf6510951006bf6310951006bc63109511d73f53109510073d53109511fdbe721095113fae7210951006bf6210951006bc62109511cebf61109511d7b751109511cf3e51109511cf3c51109511cfb451109511c6be60109511c6bc60109511cfb71010951004fe76cc951004fd76cc95108cfc76cc9510257e75cc9510057d75cc95113dbe74cc951005bd74cc951004fe768c951004fd768c951004fc768c951006df638c951006dc638c951004ff764c951004fe764c951004fc764c951005bf744c95113dbc744c951005f7714c951015f4714c951004fe760c951004fd760c95108cfc760c9510257e750c9510057d750c951006df630c95108edc630c95100cfe76d8151136fa60d8151014fd75d815100cfc75d815101cfe74d8151004fd74d815101cfc74d815108cfe73d8151004fd73d8151004fe72d8151004fd72d8151006be42d8151006bc42d8151024fd71d8151136fa50d8151136f820d8151136fa10d8151136f86058151024fe76d954112e7e65d95412a4fd75d9541014ff74d9541014fd74d95414be7f54d95414be7d54d954108cfe73d9541004fd73d9541004fe72d9541004fd72d95414bebc42d954101cff71d954101cfd71d95414ae7f51d95414ae7d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d954112e7c50d9541024ff765954112e7c65595414a5bf74595414b5f771595414acff75595410067f75595414a4ff7459541006bf7459541004ff735954108cfc7359541004ff7259541004fc725954113ebc42595412a4ff7159541006f77159541004ff705954100cfe705954100cfc7059541015bc765
  | 30 => 0xf744c832155bc744c832007ae424c832007ac424c832005f7714c83214df4714c832005df764c832006df764c832004df764c8320075e654c8320075d654c8320079f744c8320079c744c83208ddf724c832006de624c832007ce524c832007cd524c8320079e424c8320079c424c832007d7714c83214dde714c83214ddc714c832007d4714c83214dd4714c83208def764c832006ef764c832004ef764c83208f6e654c83208f6d654c832007af744c832007ac744c83208def734c832007cf734c83208eee634c83208fce634c83208fce534c832007cd534c832007e7714c832007e4714c832014ff76584320067e65584320067d655843208ef4615843208fd43158432004ff7558432024fe7558432024fc7558432004ff745843201cfe745843201cfc7458432006be4258432006bc4258432006ee3258432006ed325843214ef6415843208ef7315843214ede315843214edc315843208ef4315843214ef42158432004ff705843200cfe705843200cfc705843214ef7105843200cff76580320067e65580320067d655803208ef86058032004ff7558032024fe7558032024fc7558032004ff745803201cfe745803201cfc7458032006be4258032006bc4258032004ff7158032014fe7158032014fc7158032146fa405803208efb305803208ef83058032146f82058032146fa105803201cfe76d915113ebe64d9151014fd75d915113ebe54d91514eebd54d915108cfe73d9151004fd73d9151004fe72d9151004fd72d915113ebc42d9151024fd71d91514a6bf41d915100cfe70d9151004fd70d915100cfc70d915113ebc64591514e5f77159151014fd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d514dede53d8d514dedd53d8d51004fe72d8d51004fd72d8d51024fd71d8d51476df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006df6398d51105f57198d5111df77158d51006dd6318d51014fd7518d5108e7d7518d5101cfe7418d51004fd7418d5108cfc7418d5108e7f5318d5108ede5318d514d6dd5318d51004fe7218d51004fd7218d5108cff7118d51024fd7118d5108edf3118d51466dd3118d5100cfe7018d51004fd7018d5100cfc7018d51466f71018d510157c7654d512767c7654d510147c7654d510257f7354d510275f7354d510075f6354d5108e7c6354d510075c6354d51007777154d510157e7154d510157c7154d51277747154d510267f6154d51027776154d5126e7e6054d5126e7c6054d51277771054d51004fe7690d51004fd7690d5108cfc7690d510257e7590d510057d7590d51004ff7650d51004fe7650d51004fc7650d5113dbe74d8951005bd74d8951014fd75d895101cfe74d8951006be74d895101cbe74d8951004fd74d8951006bd74d8951004bd74d895101cfc74d8951
  | 31 => 0x9032004fd70d903200cfc70d903201cff76590320067e65590320067d655903208ebc6459032004ff7559032024fe7559032024fc755903208ebf745903208cfc735903208ebe435903208ebc4359032154fc7259032156bc4259032004ff7159032014fe7159032014fc7159032156bf4159032004ff705903200cfe705903200cfc7059032156bf4059032004ff765503208cfe7655032004fd765503208cfc76550320267e65550320067d6555032006bf645503201ebc6455032005ef7255032005ec725503208cff7598c32024fe7598c321bcfd7598c3208cfc7598c3208cff7498c3201cfe7498c3208ebe7498c3201cbe7498c321b4fd7498c3208ebd7498c32004bd7498c3208cfc7498c32014fe7198c3200cfe7098c321bcff7654c320267e6554c320067d6554c321b4ff7650c3224e7e6550c320067d6550c3208ebf6450c3208ebc6450c32024fe759883219cfd7598832024fc759883201cfe7498832194fd749883201cfc7498832014fe719883200cfe709883219cff769483208cfe7694832024fd769483208cfc76948320267e65948320067d659483208dde7394832005dd739483215f6f529483219cff76548320267e65548320067d6554832005bf7454832155bc7454832005fb7054832145f87054832194ff769083208cfe769083201cfd769083208cfc76908322067e65908320067d659083201ebe6490832006bd649083208dde7390832005dd7390832006bf769083201ebe769083201ebd7690832006bc7690832006bf6590832206be65908320073e65908322063e6590832006bd65908320073d65908320063d6590832206bc65908320079e73908320079d7390832006be6390832155be7290832006be62908321febe61908321febc619083250f9e319083250f9c31908321f6be60908321f6bc6090832194ff76508321ee7e65508320067d6550832157ac425083201ebf7610832156be7610832156bd761083201ebc76108321573e75108321573d7510832006bf65108321d6be65108320073e65108321d63e6510832006bd65108320073d65108320063d65108321d6bc65108321579e73108321579d73108321b6be6310832005be7210832157ae7210832196be6210832507af5210832507ac52108321cebe61108321cebc61108324ff9e31108324ff9c31108324ffae21108324ffac21108321c6be60108321c6bc601083208f5e65cc83208f5d65cc83208f9e74cc83208f9d74cc8320079e42cc8320079c42cc83214dde71cc83208ddc71cc83219e7e658c8320067d658c832005dd738c832006de638c832007ae428c832007ac428c83208f6e658c83208f6d658c83208ded738c83208eee638c83208fce638c8324f7ce318c83208fcc318c832004ff764c83217e7e654c8320067d654c832005b
  | 32 => 0x7b64218532007b44218532007e73218532007d6321853216ff2701853216ff17018532006f66018532006f4601853200cfe76d8132006bf64d8132006bc64d8132006f761d8132006f461d8132166fa60d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d8132006be42d8132006bc42d8132014fe71d8132004fd71d8132014fc71d8132006fb50d8132166f850d8132166fa30d8132166fa20d81320057f755813217d7c7558132005bf7458132175bc7458132006bf6458132006bc6458132005f7715813216df47158132006f76158132006f46158132166f8605813215cfd75d943201cfe74d9432004fd74d943208cfc74d943208cfe73d943208ede73d943219cfe72d943208eee72d9432014fe71d9432004fd71d9432014fc71d943200cfe70d9432004fd70d943200cfc70d94320047d769943215f3e749943215f3d749943208e7f64994320067e649943208e7c649943208e7e639943208e7f61994320067e619943208e7c61994320075e319943208f5c319943208e7f60994320067e609943208e7c6099432024ff765943208e7c655943208e7f7559432004ff745943201cfe745943201cfc745943215e7f54594320067e545943215e7c545943208cfc735943208e7e535943208e7c535943215cfc725943215e7c5259432004ff7159432014fe7159432014fc715943215e7f51594320067e515943215e7c5159432004ff705943200cfe705943200cfc705943215e7f50594320067e505943215e7c505943208d7f765943215e7f76594320247f765943208e7f64594320067e645943208e7c645943208e7f61594320067e615943208e7c61594320075e315943208f5c315943208e7f60594320067e605943208e7c60594320067f74594320067e74594320067d74594320067c745943215e7f735943208e7e735943208e7c73594320067f435943208e7e435943208e7c435943215e7f72594320067e72594320067c72594320067f42594320067c425943208e7f325943208e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067c415943208e7f31594320067e315943208e7c31594320067e21594320067c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067c405943208e7f30594320067e305943208e7c30594320067e20594320067c20594320067f10594320067e10594320067c1059432024fe75d903208e7e75d90320247e75d9032004fd75d903208e7d75d90320047d75d903208cfc75d9032154fd74d9032156be54d903208cfe73d903208ede73d903208ebf43d9032194fe72d903208eee72d9032014fe71d9032004fd71d9032014fc71d903200cfe70d
  | 33 => 0x461909321f6be60909321f6bc609093201cff7650932174fd765093201cfc7650932006bf645093201ebc6450932005df7350932005dc73509321e6f46150932005be7610932176be7610932004be76109321773e75109321773d7510932006bf65109321d6be6510932006bd65109321d6bc6510932005be7210932177ae7210932007ae5210932007ad52109321cebe61109321cebc61109321ceb461109321c6be60109321c6bc6010932517ae2010932517ac2010932175be74cc932005bd74cc932006bf64cc9321b6bc64cc932007ae42cc932007ac42cc93208fae74cc93208fad74cc932007af64cc932007ac64cc932005ed71cc932006bf648c932196bc648c9320079f648c9320079c648c932007cf628c9320079e428c9320079c428c93218ede618c93218edc618c932014fe76d8532006bf64d8532006bc64d853216ef661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532006be42d8532006bc42d8532006f751d853216ef651d853216ef451d8532006f741d853216ef641d853216ef441d853216ef631d853216ef621d853200cfe70d8532004fd70d853200cfc70d853216ef710d8532006f610d853216ef410d853216df676d8532014f676d8532006f765d8532006f665d8532006f565d8532006f465d8532006f764d8532007b764d8532006b764d8532006f664d8532006f564d8532006f464d8532007b464d8532006b464d8532007e772d8532007b642d8532007b442d8532007e732d8532007d632d8532006f660d8532006f460d8532006f775d8532006f675d8532006f575d8532006f475d8532006f774d8532006f674d8532006f574d8532006f474d8532006f754d8532006f654d8532006f554d8532006f454d8532006f773d853216ef673d8532006f753d8532006f653d8532006f553d8532006f453d8532006f743d8532006f643d8532006f543d8532006f443d8532006f772d853216ef672d8532006f752d8532006f652d8532006f552d8532006f452d8532006f742d8532006f642d8532006b642d8532006f542d8532006f442d8532006b442d8532006f732d8532006f632d8532006f770d8532006f670d8532006f570d8532006f470d8532006f750d8532006f650d8532006f450d8532006f740d8532006f640d8532006f440d8532006f630d8532006f430d8532006f620d8532006f420d8532005bf7458532175bc7458532006bf6458532006bc645853216ef46158532005f6761853216ef67618532006f76518532006f66518532006f56518532006f46518532006f76418532007b76418532006b76418532006f66418532006f56418532006f46418532007b46418532006b4641853218ef7631853218ed7631853216fe572185321aef76218532
  | 34 => 0x9132004fd75d9132024fc75d9132006bf54d9132176be54d9132176bc54d9132174fd73d9132176bf43d9132174fd72d9132176bf42d9132014fe71d9132004fd71d9132014fc71d9132176bf41d9132006be41d9132176bc41d913200cfe70d9132004fd70d913200cfc70d9132176bf40d9132006be40d9132176bc40d9132175be76d913201cbe76d9132006bf65d9132006be65d9132006bd65d9132006bc65d9132006be61d9132006bc61d9132006be60d9132006bc60d9132006bf75d9132006be75d9132006bd75d9132006bc75d9132006bf73d9132176be73d9132006bd73d9132006bf53d9132006bc53d9132006bf72d9132176be72d9132006bd72d9132006bf52d9132006bc52d9132006bf71d9132006be71d9132006bd71d9132006bc71d9132006bf51d9132006be51d9132006bc51d9132006be31d9132006bc31d9132006be21d9132006bc21d9132006bf70d9132006be70d9132006bd70d9132006bc70d9132006bf50d9132006be50d9132006bc50d9132006be30d9132006bc30d9132006be20d9132006bc20d9132006bf10d9132006be10d9132006bc10d9132176bc6459132005f7715913216df47159132004ff7559132024fe7559132024fc7559132174ff7459132006bf7459132194ff7359132006df73591321b4ff7259132006ef7259132176bc4259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff705913200cfe705913200cfc7059132005be7619132176be7619132004be7619132006bf6519132006be6519132006bd6519132006bc6519132006be6119132006bc6119132006be6019132006bc6019132004ff7655132004fe7655132004fd7655132004fc7655132006bf645513201ebc64551322a6f4615513219cfe7694d32006bf6494d32296bc6494d3217f5f5394d3228ef46194d32024fc7654d320067f6554d320267c6554d32006bf6454d3227ebc6454d32005ef7254d32005ec7254d32276f46154d32194fe7690d32006bf6490d3201ebc6490d3225ef46190d3201cfc7650d32006bf6450d3201ebc6450d321779c4350d32005ef7250d32005ec7250d32246f46150d321bcfe7694932006bf6494932236bc649493217f6f529493222ef46194932024ff765493217cfd7654932024fc76549320067f65549320267c6554932005bf7454932175bc7454932006bf645493221ebc6454932005df7354932005dc7354932216f46154932005fb7054932165f870549321b4fe7690932006bf649093201ebe6490932006bd649093201ebc64909321fef46190932005be7690932006be7690932004be7690932006bf6590932206be6590932006bd6590932206bc6590932175be72909321febe61909321febc61909321feb
  | 35 => 0x24fd7694a320267e6594a320067d6594a32005de7394a32005dd7394a3219f6f5294a3215cff7654a320067f6554a320267c6554a32005bf7454a32195bc7454a32005fb7054a32185f87054a3201cfd7690a3201ebe6490a32006bd6490a32005de7390a32005dd7390a3201ebe7690a3201ebd7690a32006bf6590a32206be6590a32006bd6590a32206bc6590a320079e7390a320079d7390a321febe6190a321febc6190a3252f9e3190a3252f9c3190a321f6be6090a321f6bc6090a32154ff7650a32196be7610a32196bd7610a321973e7510a321973d7510a32006bf6510a321d6be6510a32006bd6510a321d6bc6510a321979e7310a321979d7310a32197ae7210a32007ae5210a32007ad5210a321cebe6110a321cebc6110a325279e3110a325279c3110a321c6be6010a321c6bc6010a3251fae2010a3251fac2010a32195be74cca32005bd74cca32007ae42cca32007ac42cca32005dd76cca32006dd76cca320079e74cca320079d74cca32007ce52cca32007cd52cca320079e42cca320079c42cca3218dde71cca3218ddc71cca32005ed76cca3208eed76cca3208fae74cca3208fad74cca3208fce53cca32007cd53cca32005ed71cca3218ef661d863218fd431d863218ef4615863218fd63158632004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc7458632006be4258632006bc425863218ede315863218ef6315863218edc315863218ef42158632004ff705863200cfe705863200cfc705863218ef71058632186fa60d82320057f755823219d7c7558232186f86058232004ff75582320067f75582320047f7558232024fe7558232024fc75582320067c75582320247c7558232004ff745823201cfe745823201cfc7458232006be4258232006bc4258232004ff7158232014fe7158232014fc7158232186fa3058232186f82058232186fa1058232024fe76d953217e7e65d953201cfe74d9532004fd74d953201cfc74d953217cfd73d953217e7f53d953217cfd72d953217e7f52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95320067e50d953217e7c50d953217e7c6559532005bf7459532175bc7459532005f7715953216df47159532005fb7059532165f8705953217cff75595320067f7559532004ff7459532006bf7459532004bf745953201cfe745953201cfc7459532006bc745953201cbc745953219cff7359532006df73595321bcff7259532006ef7259532004ff7159532006f77159532004f77159532014fe7159532014fc7159532006f47159532014f47159532004ff7059532006fb7059532004fb705953200cfe705953200cfc7059532006f8705953200cf8705953201cfe76d9132176be64d9132024fe75d
  | 36 => 0xe6494b32006bd6494b321bf6f5294b32024ff7654b320267e6554b320067d6554b32005bf7454b321b5bc7454b3221ebe6454b32006bd6454b32005df7354b3208ddc7354b32005fb7054b321a5f87054b32174fd7690b32006bf6490b3201ebe6490b32006bd6490b3201ebc6490b32005bd7690b32006bd7690b32006bf6590b32206be6590b32006bd6590b32206bc6590b321febe6190b321febc6190b321f6be6090b321f6bc6090b3201cff7650b3201ebe6450b32006bd6450b32005df7350b3208ddc7350b321b7ac4250b32005bd7610b321b6bd7610b321b73e7510b321b73d7510b32006bf6510b321d6be6510b32006bd6510b321d6bc6510b321b7ae7210b3253faf5210b3253fac5210b321cebe6110b321cebc6110b32537ae2110b32537ac2110b321c6be6010b321c6bc6010b32006be6458732006bd645873208ef46158732004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc7458732006be4258732006bc425873208ef7315873208ef431587321aef62158732004ff705873200cfe705873200cfc7058732006be6458332006bd645833208ef86058332004ff7558332024fe7558332024fc7558332004ff745833201cfe745833201cfc7458332006be4258332006bc4258332004ff7158332014fe7158332014fc7158332006fb50583321a6f8505833208efb305833208ef830583321a6fa20583321a6fa105833219e7e65d963201cfe74d9632004fd74d963201cfc74d9632006dd73d9632006ee72d963219e7f52d9632014fe71d9632004fd71d9632014fc71d963200cfe70d9632004fd70d963200cfc70d96320067e50d963219e7c50d963219e7c65596320067f7559632004ff745963201cfe745963201cfc745963219e7f545963219e7f535963219e7c5259632004ff7159632014fe7159632014fc7159632004ff705963200cfe705963200cfc7059632196be64d9232024fe75d9232004fd75d9232024fc75d9232006dd73d9232196bc43d9232006ee72d9232014fe71d9232004fd71d9232014fc71d9232196bf41d923200cfe70d9232004fd70d923200cfc70d9232196bf40d9232196bc6459232004ff7559232024fe7559232024fc7559232006bf7459232196be5459232196bf4359232196bc4259232004ff7159232014fe7159232014fc7159232004ff705923200cfe705923200cfc7059232004ff7655232004fe7655232004fd7655232004fc76552320267e65552320067d655523201ebe6455232006bd645523217cfd7694e3219f5f5394e32024ff7654e320267e6554e320067d6554e32005ef7254e32005ec7254e32174fd7690e32006bf6490e3201ebc6490e3201cff7650e3201ebe6450e32006bd6450e32005ef7250e32005ec7250e3208edc3198a32
  | 37 => 0x48420073e52548421d73c52548421d7ac5254842005bf71548421cdbe71548421cdbc7154842547ae2154842547ac2154842005bf7054842007bb7054842005bb70548421c5be70548421c5bc7054842007b870548421c5b8705484201cfe74d973208ebe74d973201cbe74d9732004fd74d973208ebd74d9732004bd74d973208cfc74d973208ede73d973208e7f53d973208eed72d9732014fe71d9732004fd71d9732014fc71d973200cfe70d973208efa70d973200cfa70d9732004fd70d973208ef970d9732004f970d973200cfc70d973208e7c655973208e7f7559732004ff745973201cfe745973201cfc745973208e7e535973208e7c53597321be7f5259732004ff7159732014fe7159732014fc71597321be7f5159732004ff705973200cfe705973200cfc70597320067e50597321be7c5059732024fe75d9332004fd75d933208cfc75d933208ede73d933208eed72d93321b6bc42d9332014fe71d9332004fd71d9332014fc71d933200cfe70d9332004fd70d933200cfc70d933208ebf6599332006be6599332006bd659933208ebc659933208ebe639933208ebf6199332006be619933208ebc619933208ebf6099332006be609933208ebc609933208ebc6459332004ff7559332024fe7559332024fc755933208ebf7459332006bf54593321b6be54593321b6bc545933208ebe435933208ebc43593321b6bf4259332004ff7159332014fe7159332014fc71593321b6bf4159332006be41593321b6bc4159332004ff705933200cfe705933200cfc70593321b6bf4059332006be40593321b6bc40593321b6bf765933208ebf6559332006be6559332006bd655933208ebc655933208ebf6159332006be615933208ebc615933208ebf6059332006be605933208ebc6059332006bf7559332006be7559332006bd7559332006bc75593321b6bf735933208ebe735933208ebc7359332006bf535933208ebe535933208ebc5359332006bf7259332006bd72593321b6bc7259332006bf5259332006bc525933208ebc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bc515933208ebf3159332006be315933208ebc3159332006be2159332006bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bc505933208ebf3059332006be305933208ebc3059332006be2059332006bc2059332006bf1059332006be1059332006bc1059332004ff765533208cfe7655332004fd765533208cfc765533201ebe6455332006bd6455332005ef7255332005ec725533215cff7654f3208e7f6554f3208e7c6554f3227ebe6454f32006bd6454f32154ff7650f3201ebe6450f32006bd6450f3208f9c4350f3217cfd7694b32236b
  | 38 => 0x67f65549420267c6554942005bf745494201dbc745494221fac4254942005fb70549421ddf87054942006bf6590942206be6590942006bd6590942206bc6590942006bf6390942006bc639094201dbe729094201fae729094201ebf629094201faf62909421febe61909421febc61909421f6be60909421f6bc6090942014fe76d85421e6f661d8542024fe75d8542004fd75d8542024fc75d854208cfe73d8542004fd73d854201cfd72d8542006be42d85420e6bc42d85421e6f641d85421e6f431d85421e6f621d854200cfe70d8542004fd70d854200cfc70d8542005df7358542005dc73585421e6f4615854200cfe76d81421defa60d8142024fe75d8142004fd75d8142024fc75d814208cfe73d8142004fd73d814201cfd72d8142006be42d8142066bc42d8142014fe71d8142004fd71d8142014fc71d8142006fb50d81421def850d81421defa40d81421defa20d81420057f75581421ed7c75581421def86058142295bf7694c4201dbe7694c42295bd7694c4201dbc7694c4227dbd7594c422973e6594c422973d6594c4257dbe7394c421d73f5394c421d79f5394c421d71f5394c421d79c5394c42005be7294c42005bd7294c42297ae6294c421cdbe7194c42005bd7194c421cdbc7194c421c5be7094c42005bd7094c421c5bc7094c4227dbf7654c4201dbe7654c4227dbd7654c4201dbc7654c42295bf7554c4227f3e6554c4227f3d6554c42575bf7354c421d79f5354c420073e5354c421d73c5354c421d79c5354c42005bf7254c42007af7254c42005af7254c42005bc7254c42007ac7254c42005ac7254c4227fae6254c421d73f5254c42005bf7154c421cdbe7154c421cdbc7154c421d73f5154c42005bf7054c421c5be7054c421c5bc7054c4256f3e5054c421d73c5054c42206bf7598842206be7598842206bd7598842206bc7598842006be7398842006bd7398842206bf5398842206be5398842206bd5398842206bc539884201ebe729884201eae7298842206bf5298842206bc52988421febe71988421febd71988421febc51988421f6be70988421f6bd70988421f6bc50988421f6bc1098842235bf769484201dbe7694842235bd769484201dbc769484221dbd75948422373e65948422373d6594842005be7394842005bd7394842565be7294842206be6294842237ae62948421d73f52948421d7af52948421d72f52948421d7ac52948421cdbe7194842005bd71948421cdbc719484255fae219484255fac21948421c5be7094842005bd70948421c5bc70948425573e50948421d73c509484221dbf7654842206bf7654842204bf7654842235bf755484221f3e655484221f3d6554842005bf7354842005bc73548421d73f53548420073d535484254dbf7254842206be625484221fae62548421d7af525
  | 39 => 0xe75d8642005bd75d8642205bc75d8642006bf65d8642006bd65d8642005be73d8642005bd73d8642006bf63d8642006bd63d8642007ae72d86420e7ae62d86421febe61d86421ffb661d86421febc61d86421f5be70d8642005bd70d86421f5bc70d8642005bf7558642205be7558642205bc7558642006bf6558642006bd6558642005bf7358642005bc7358642006bf6358642006bd635864201dbc72586420cebe62586420cfae6258642007b761586421febe61586421febc61586421ffb461586421ffb42158642005bf70586421f5be70586421f5bc70586421ffb71058642205be75d8242005bd75d8242205bc75d8242006bf65d8242006bd65d8242005be73d8242005bd73d8242006bf63d8242006bd63d8242007ae72d8242067ae62d82421fdbe71d8242005bd71d82421fdbc71d82421f6be60d82421f7ba60d82421f6bc60d8242005bf75582420073f75582420053f7558242205be7558242205bc75582420073c75582422053c7558242006bf6558242006bd6558242005bf7358242005bc7358242006bf6358242006bd635824201dbc7258242046be6258242047ae6258242005bf71582421fdbe71582421fdbc7158242007bb60582421f6be60582421f6bc60582421f7b860582421f7b820582421f7ba1058242024fe76d95421ee7e65d9542234ff74d9542234fd74d95422367f54d95422367d54d954208cfe73d9542004fd73d954201cfd72d95421ee7f52d9542236bc42d9542014fe71d9542004fd71d9542014fc71d954200cfe70d9542004fd70d954200cfc70d95420067e50d95421ee7c50d95421ee7c655954254def7259542005fb70595421ddf87059542234ff75595420067f755954221cff7459542006bf7459542204bf7459542004ff735954208cfc735954254cff7259542006ef725954221ebc4259542004ff7159542014fe7159542014fc7159542004ff7059542006fb7059542004fb705954200cfe705954200cfc7059542006f8705954200cf87059542024fe75d8d42004fd75d8d42024fc75d8d42196de43d8d42196dd43d8d42196bc42d8d42014fe71d8d42004fd71d8d42014fc71d8d42006de31d8d42006dc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d42175ed7298d421b5ef7258d42005f77158d421e5f47158d42006dd6318d42024fe7518d42004fd7518d4208cfc7518d4208ede4318d42156dd4318d42156bc4218d42014fe7118d42004fd7118d42014fc7118d42006de3118d4208edc3118d4200cfe7018d42004fd7018d4200cfc7018d42004fe7694d42004fd7694d4208cfc7694d421ef5f5394d42004ff7654d42004fe7654d42004fc7654d42564fe76949421ef6f5294942237ac4294942024ff765494201cfe765494221cfd765494201cfc7654942
  | 40 => 0x9642005bd70d96421f5bc70d96420073e50d96422073c50d96420073f6559642206be6559642206bc65596422073c65596422063c6559642005bf7359642005bc73596422073f535964201dbc725964221ebe625964221fae62596422073c5259642005bf71596421fdbe71596421fdbc7159642005bf70596421f5be70596421f5bc7059642205be75d8e42005bd75d8e42205bc75d8e42005be72d8e42007ae72d8e42005ae72d8e42197ae62d8e421fdbe71d8e42005bd71d8e421fdbc71d8e421f5be70d8e42005bd70d8e421f5bc70d8e42205be7598e42005bd7598e42205bc7598e42006bf6598e42006bd6598e42006bf6398e420079f6398e420069f6398e421b6be6298e421b7ae6298e421fdbe7198e42005bd7198e421fdbc7198e421f5be7098e42005bd7098e421f5bc7098e42005bf7558e42205be7558e42205bc7558e420079f6358e42006be6358e42176be6258e42177ae6258e42005bf7158e421fdbe7158e421fdbc7158e42005bf7058e421f5be7058e421f5bc7058e42205be7518e420073e7518e422053e7518e42005bd7518e420073d7518e420053d7518e42205bc7518e42006bf6518e42006bd6518e42006bf6318e420079e6318e42006bd6318e420079d6318e42005be7218e42007ae7218e42005ae7218e42157ae6218e421fdbe7118e42005bd7118e421fdbc7118e421f5be7018e42005bd7018e421f5bc7018e42005bf7694e42005be7694e42005bd7694e42005bc7694e420079e6394e420079d6394e422073f5394e422079f5394e422071f5394e422079c5394e42005be7294e42005bd7294e421fdbe7194e42005bd7194e421fdbc7194e421f5be7094e42005bd7094e421f5bc7094e42005bf7654e42005be7654e42005bd7654e42005bc7654e422073e6554e420073d6554e420079e6354e420079d6354e422079f5354e420073e5354e422073c5354e422079c5354e42005bf7254e42005bc7254e422073f5254e42005bf7154e421fdbe7154e421fdbc7154e422073f5154e42005bf7054e421f5be7054e421f5bc7054e4258f3e5054e422073c5054e4201dbf7694a4201dbd7694a422073e6594a420073d6594a42005be7394a42005bd7394a422073f5294a42207af5294a422072f5294a42207ac5294a421fdbe7194a42005bd7194a421fdbc7194a421f5be7094a42005bd7094a421f5bc7094a425873e5094a422073c5094a42005bf7654a421d6bf7654a421d4bf7654a420073f6554a422073c6554a42005bf7354a42005bc7354a422073f5354a420073d5354a42207af5254a420073e5254a422073c5254a42207ac5254a42005bf7154a421fdbe7154a421fdbc7154a42005bf7054a42007bb7054a42005bb7054a421f5be7054a421f5bc7054a42007b87054a421f5b87054a42205b
  | 41 => 0x4fd7198e42014fc7198e4200cfe7098e42004fd7098e4200cfc7098e42004ff7558e42024fe7558e42024fc7558e42176de4358e42176dd4358e42176bc4358e42004ff7158e42014fe7158e42014fc7158e42176bf4158e42004ff7058e4200cfe7058e4200cfc7058e42176bf4058e422057e7518e420057d7518e42006dd6318e42195ee7218e4208cff7694e42004fe7694e42004fd7694e4201dbe7494e42005bd7494e4201dbc7494e4208ede6394e42006dd6394e422075f5394e42004ff7654e42004fd7654e42004fc7654e420267e6554e420067d6554e42005bf7454e4201dbe7454e4201dbc7454e42006de6354e42006dd6354e42005bf7590e42205be7590e42005bd7590e42205bc7590e42006bf6590e42006bd6590e4201dbe7390e4201f9e7390e420079e6390e42006bd6390e420079d6390e42007ae7290e42005bd7290e42007ad7290e4201ebe6290e4201fae6290e421fdbe7190e42005bd7190e421fdbc7190e421f5be7090e42005bd7090e421f5bc7090e42005bf7550e42205be7550e42005bd7550e42205bc7550e4201dbf7350e4201f9f7350e4208ebe6350e420079e6350e420069e6350e420079d6350e42005bf7250e42007af7250e42007ac7250e4201ebe6250e4201fae6250e42005bf7150e421fdbe7150e421fdbc7150e42005bf7050e421f5be7050e421f5bc7050e4201cff7694a42024fe7694a4201cfd7694a420267e6594a420067d6594a4201dbe7494a42005bd7494a422076f5294a42237af4294a4254cff7654a420067f6554a420267c6554a42205bf7454a4201dbe7454a4201dbc7454a422073f5454a420073d5454a4221faf4254a42005fb7054a421f5f87054a421fef661d8642014ff765864201dbc74586421fef461586421ffb64158642004ff7558642024fe7558642024fc75586420cebe5458642006bd5458642004ff735864208cfc73586420cebf4358642006bd435864201cfc72586421febe41586421fef641586421febc41586421fef42158642004ff705864200cfe705864200cfc70586421fef710586421f6fa60d824200cff76582420057f75582422057c755824201dbc74582421f6f860582421f7ba4058242004ff75582420067f75582420047f7558242024fe7558242024fc75582420067c75582420247c7558242046be5458242006bd5458242004ff735824208cfc7358242046bf4358242006bd435824201cfc7258242004ff7158242014fe7158242014fc71582421f6be40582421f6fa40582421f6bc40582421f6f820582421f6fa1058242206be65d96422073e65d9642206bc65d9642005be73d9642005bd73d9642005be72d9642007ae72d9642005ae72d9642237ae62d96422073f52d96421fdbe71d9642005bd71d96421fdbc71d96421f5be70d
  | 42 => 0x852d8152006fb61d8152006fa61d8152006f961d8152006f861d8152056fb75d815220efa75d8152056f875d8152006fb74d8152006fa74d8152006f974d8152006f874d8152056fb54d8152056fa54d8152056f954d8152056f854d8152006fb73d8152006fa73d8152006f973d8152006f873d8152056fb53d8152056fa53d8152056f953d8152056f853d8152006fb43d8152006fa43d8152006f943d8152006f843d8152056fb72d815220efa72d8152056f972d8152056fb52d8152056fa52d8152056f852d8152006fb42d8152006f842d8152006fb71d8152006fa71d8152006f971d8152006f871d8152056fb51d8152056fa51d8152056f951d8152056f851d8152006fb41d8152006fa41d8152006f841d8152006fa31d8152006f831d8152006fa21d8152006f821d8152005bf745815221dbc7458152006bf6458152006bc645815220ef86058152055fa761815220efa7618152226fb65181522267b6518152006fb6418152007bb6418152006bb6418152006fa6418152006f96418152006f86418152007b86418152006b8641815238f7b5418152007795418152006fb6318152006fa6318152006f96318152006f8631815238f7b531815200779531815220fe97218152376fb621815238feb52181520077a521815238f78521815238fe8521815220ff2711815220ff17118152006fb6118152006fa6118152006f96118152006f861181522067e65d9642565ee72d964221cfd75d9642006bd74d9642206bf54d9642236bc54d964208cfe73d9642004fd73d9642236bc43d9642564fe72d9642006ee72d96422067f52d9642014fe71d9642004fd71d9642014fc71d9642236bf41d964200cfe70d9642004fd70d964200cfc70d96420067e50d96422067c50d9642236bf40d9642024ff76596422067c655964201dbc74596422073f54596420067f7559642206bf745964221e7f5459642206bf54596422063f545964221e7d545964221ebc5459642004ff735964208cfc73596422067f535964221ebc435964201cfc72596422067c5259642004ff7159642014fe7159642014fc715964221ebf4159642004ff705964200cfe705964200cfc705964221ebf4059642205bf7655242026bf7655242024bf765524201dbf755524201f3f7555242026be65552422073e65552420073d6555242026bc6555242005bf7355242005bc7355242005bf7255242007af7255242007ac725524201ebe625524201fae62552422073f5255242005bf71552421fdbe71552421fdbc7155242005bf70552421f5be70552421f5bc70552425973e50552422073c5055242155ee72d8e42006df6398e42024fe7598e42004fd7598e4208cfc7598e421b6be5498e42006bd5498e4208ebf4398e4208ede4398e421b6dd4398e42014fe7198e42
  | 43 => 0x515229e7c605515229e78605515221f3f4055152006bf64d8d52006bc64d8d5201cfe74d8d52004fd74d8d5201cfc74d8d5219ede53d8d5219edd53d8d52014fe71d8d52004fd71d8d52014fc71d8d52006de31d8d52006dc31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5221dbe7498d52005bd7498d52006bf6498d52006bc6498d52006df6398d5217ded7298d5220dfa7098d52005f97098d52005bf7458d5221dbc7458d52006bf6458d52006bc6458d521bdef7258d52005f77158d52215f47158d52005fb7058d5220df87058d52006bf6418d52006bc6418d52006dd6318d5201cfe7418d52004fd7418d5208cfc7418d5208e7f5318d5208ede5318d5215edd5318d52014fe7118d52004fd7118d52014fc7118d52006de3118d5208edc3118d5200cfe7018d52004fd7018d5200cfc7018d520057f7454d520073f6454d520073c6454d520257f7354d520275f7354d520075f6354d5208e7c6354d520075c6354d520076f7254d520057c7254d520076c7254d520267f6254d520276f6254d5226e7e6054d5226e7c6054d5226e786054d52004fe7690d52004fd7690d5208cfc7690d520257e7590d520057d7590d52006bf6490d5201ebc6490d520073d5490d52005ee7290d52005ed7290d52256f86090d52004ff7650d52004fe7650d52004fc7650d520257e7550d520057d7550d52006bf6450d5201ebc6450d5223ef86050d520057d74949520073f64949520073c64949520057d73949520257e72949520276e72949520267f62949520276f62949520266f62949522267e60949522267c6094952014fe76d8552006bf64d8552006bc64d8552216f661d855201cfe74d8552004fd74d855201cfc74d855208cfe73d8552004fd73d85520ee7f53d85520067d53d8552024fd72d8552216f651d8552216f431d8552216f621d855200cfe70d8552004fd70d855200cfc70d8552005bf745855221dbc7458552006bf6458552006bc6458552005df7358552005dc7358552216f46158552005fb705855220df8705855200cfe76d8152006bf64d8152006bc64d815220efa60d815201cfe74d8152004fd74d815201cfc74d815208cfe73d8152004fd73d8152024fd72d8152014fe71d8152004fd71d8152014fc71d815220efa50d8152006fb40d815220efa40d815220ef840d815220efa30d815220ef830d815220efa20d8152006fb10d815220efa10d815220ef810d815220dfa76d815200cfa76d8152006fb64d8152007bb64d8152006bb64d8152006fa64d8152006f964d8152006f864d8152007b864d8152006b864d81520577b54d81520077954d8152006fb63d8152006fa63d8152006f963d8152006f863d81520577b53d81520077953d8152057eb72d8152057eb52d81520077a52d81520577852d8152057e
  | 44 => 0x67e5058e5217e7c5058e52006dd6318e5219dee7218e5215f6f5218e5208cff7690e52004fe7690e52004fd7690e5201ebc6490e52005ee7290e52005ed7290e522676f5290e52004ff7650e52004fd7650e52004fc7650e5224f6f5250e520ef6f52d865222ef661d8652014ff76586520d76f525865222ef46158652004ff745865201cfe745865201cfc7458652004ff735865208cfc7358652024fc725865222ef6515865222ef42158652004ff705865200cfe705865200cfc705865222ef710586520576f52d8252226fa60d82522277850d825200cff76582520257c755825204f6f5258252226f860582522277a5058252004ff745825201cfe745825201cfc7458252004ff735825208cfc7358252024fc7258252004ff7158252014fe7158252014fc71582522267e5058252226fa50582522267a50582522267c5058252226f82058252226fa105825201cfe76d915221ebe64d915221ebe54d9152206bd54d915208cfe73d9152004fd73d915221ebf43d915221ebc43d9152024fd72d915221ebf42d9152014fe71d9152004fd71d9152014fc71d915221ebf41d9152006be41d915221ebc41d915200cfe70d9152004fd70d915200cfc70d915221ebf40d9152006be40d915221ebc40d915221dbe76d915201cbe76d91520073f75d91522073c75d91522073f53d9152207af52d91522073c52d9152207ac52d9152006be61d9152006bc61d9152006be60d9152006bc60d9152206bf75d915221ebe75d9152206bc75d9152006bf73d9152006be73d9152006bd73d9152006bc73d9152206bf53d9152206be53d9152206bd53d9152206bc53d9152206bf72d915221ebe72d9152206bd72d9152206bf52d9152206be52d9152206bc52d9152006bf71d9152006be71d9152006bd71d9152006bc71d9152206bf51d9152206be51d9152206bd51d9152206bc51d9152006be31d9152006bc31d9152006be21d9152006bc21d9152006bf70d9152006be70d9152006bd70d9152006bc70d9152206bf50d9152206be50d9152206bd50d9152206bc50d9152006be30d9152006bc30d9152006be20d9152006bc20d9152006bf10d9152006be10d9152006bc10d915221ebc645915259def7259152005fb705915220df87059152205be761915221ebe761915221f3e751915221f3d7519152236bf65191521d73f531915254ebf62191521d7af52191521d73c52191521d7ac5219152006be6119152006bc6119152006be6019152006bc601915221d7c765515201e7c765515201c7c76551520257f74551520273f74551520073f645515201e7e645515201e7c645515221f3c64551520057f735515221f3c43551520076f72551520057c72551520076c72551520267f62551520276f625515221f3c425515221f3f415515229e7e605
  | 45 => 0xe705954300cfc7059543006f8705954300cf870595430067e505954324e7c505954327ebf405954357cfe7694d4324f5f5394d4308f9c4394d43024ff7654d4301cfe7654d4327cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d4327f9c4354d43006bf6590d43006bd6590d4308dbe7390d4308f9e7390d4308ebf6390d4301f9f6390d43005be7290d43005bd7190d43005bd7090d43024fe75d8943004fd75d8943024fc75d8943006ef52d8943006ec52d89431b6ee42d89431b6bc42d8943014fe71d8943004fd71d8943014fc71d8943006ee21d8943006ec21d894300cfe70d8943004fd70d894300cfc70d8943006ef6298943005f77158943245f4715894324d7e75189430057d7518943006ed6218943024fe75189430067e75189430247e7518943004fd75189430067d75189430047d7518943024fc7518943006bf7418943006be4318943156bc4318943006ef5218943006ec5218943156ed4218943014fe7118943004fd7118943014fc7118943156bf4118943006ee2118943006ec211894300cfe7018943004fd701894300cfc7018943156bf4018943014fe76d8543246f661d8543024fe75d8543004fd75d8543024fc75d854301cfd73d8543004fe72d8543004fd72d8543116bc42d8543006f751d8543246f451d8543246f641d8543246f631d8543246f421d854300cfe70d8543004fd70d854300cfc70d8543246f710d8543005ef7258543005ec7258543246f4615854300cfe76d814324d7e75d81430057d75d814323efa60d8143024fe75d81430067e75d81430247e75d8143004fd75d81430067d75d81430047d75d8143024fc75d814301cfd73d8143004fe72d8143004fd72d8143096bc42d8143014fe71d8143004fd71d8143014fc71d8143006fb50d814323ef850d814323efa40d814323efa30d814323ef86058143236be64d92521d5ee72d92522076f52d925201cff7659252236bc64592521ef6f5259252236be54592521eebd5459252004ff735925208cfc7359252024fc72592521ee7f5259252236bc4259252004ff7159252014fe7159252014fc7159252004ff705925200cfe705925200cfc70592520067e50592521ee7c505925215dee72d8e5219f6f52d8e52006df6398e521bf6f5298e5201cfe7498e52004fd7498e5208cfc7498e5208ede5398e521bedd5398e52014fe7198e52004fd7198e52014fc7198e5200cfe7098e52004fd7098e5200cfc7098e52005bf7458e52235bc7458e5217f6f5258e52004ff7458e52006bf7458e52004bf7458e5201cfe7458e5201cfc7458e52006bc7458e5201cbc7458e5217ede5358e5217edd5358e5217e7f5258e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e5200cfc7058e52
  | 46 => 0x964308e7c655964308e7f755964327e7f545964327e7d545964308cfe735964308cfc735964308e7e535964308e7c5359643004ff7259643004fc72596432667f525964327ebc4259643004ff7159643014fe7159643014fc71596432667f5159643004ff705964300cfe705964300cfc70596430067e50596432667c5059643265bf7655243026bf7655243024bf765524301dbf755524301f3f7555243026be65552432673e65552430073d6555243026bc6555243005bf73552430079f73552430079c735524301ebe635524301f9e6355243005bc72552432673f52552435a73e50552432673c5055243574ff7654e4301dbe7454e4327f9f4354e4308eef6298a43024fe7598a43004fd7598a43024fc7598a43006bf7498a43196be5498a43006bd5498a4308cfe7398a43196bf4398a43196ed4298a4308eef3298a4308eec3298a43014fe7198a43004fd7198a43014fc7198a4300cfe7098a43004fd7098a4300cfc7098a43006ee2098a43006ec2098a4308eec6258a43004ff7558a43024fe7558a43024fc7558a4308cfc7358a43176ee4258a43176bc4258a4308eef3258a4308eec3258a43004ff7158a43014fe7158a43014fc7158a43004ff7058a4300cfe7058a4300cfc7058a43006ee2058a43006ec2058a43014ff765864308ef46158643004ff7558643024fe7558643024fc75586430febe5458643006bd545864308cfc73586430febf4358643004ff7258643004fc72586430febc425864325ef6415864308ef7315864308ef43158643004ff705864300cfe705864300cfc705864300cff765824308ef86058243004ff7558243024fe7558243024fc7558243076be5458243006bd545824308cfc7358243076bf4358243004ff7258243004fc7258243076bc4258243004ff7158243014fe7158243014fc7158243256fa405824308efb305824308ef83058243256fa1058243024fe76d954324e7e65d954308cff74d9543294fd74d95432967f54d95432967d54d954301cfd73d954324e7f53d9543296bc43d9543004fe72d9543004fd72d9543296bc42d9543014fe71d9543004fd71d9543014fc71d9543296bf41d954300cfe70d9543004fd70d954300cfc70d9543296bf40d954324e7c6559543575df7359543005ef7259543005ec7259543005f77159543245f47159543005fb705954323df87059543294ff75595430067f755954327cff7459543006bf7459543574ff7359543006df735954327ebc4359543004ff7259543006ef7259543004ef7259543004fc7259543006ec7259543004ec725954324e7f525954327ebc4259543004ff7159543006f77159543004f77159543014fe7159543014fc7159543006f47159543014f4715954327ebf4159543004ff7059543006fb7059543004fb705954300cf
  | 47 => 0x8eec3258a53004ff7158a53014fe7158a53014fc7158a53004ff7058a5300cfe7058a5300cfc7058a53014ff76586531075f535865308ef46158653004ff745865301cfe745865301cfc745865308cfc73586531067f5358653004ff7258653004fc725865328ef6515865308ef7315865308ef43158653004ff705865300cfe705865300cfc705865300cff765825307f5f535825308ef86058253004ff745825301cfe745825301cfc745825308cfc7358253004ff7258253004fc7258253004ff7158253014fe7158253014fc7158253286fa5058253286fa405825308efb305825308ef83058253286f82058253286fa105825301cfe76d915327ebe64d915327ebe54d9153266bd54d9153024fd73d915327ebf43d9153004fe72d9153004fd72d91532667f52d915327ebc42d9153014fe71d9153004fd71d9153014fc71d915300cfe70d9153004fd70d915300cfc70d91530067e50d91532667c50d915327ebc64591535addf7359153005ef7259153005ec7259153005f77159153275f47159153005fb705915326df8705915308d7e7394d5308f5e7394d5308e7f6394d530275f6394d530265f6394d530057d7294d530057d7194d5326d7e7094d5308d7c7094d5327dbe74d8953005bd74d895301cfe74d8953006be74d895301cbe74d8953004fd74d8953006bd74d8953004bd74d895301cfc74d89531beee52d8953006ef42d8953006ec42d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d8953006ef6298953005bf745895327dbc7458953005f77158953275f47158953005fb705895326df87058953006ed621895301cfe7418953004fd741895301cfc741895315e7f521895315eed5218953006ef4218953006ec4218953014fe7118953004fd7118953014fc711895300cfe7018953004fd701895300cfc70189530067e501895315e7c5018953014fe76d8553276f661d855301cfe74d8553004fd74d855301cfc74d8553024fd73d8553004fe72d8553004fd72d8553276f651d8553006f741d8553276f441d8553276f631d8553276f421d855300cfe70d8553004fd70d855300cfc70d8553276f710d8553276f4615855300cfe76d81530257e75d815326efa60d815326f7a50d815301cfe74d8153004fd74d815301cfc74d8153024fd73d8153004fe72d8153004fd72d8153014fe71d8153004fd71d8153014fc71d815326e7e50d815326efa50d815326e7c50d8153006fb40d815326ef840d815326efa30d815326ef820d815326efa10d815326ef8605815327cfd75d964308ebd74d964308cfe73d964308ede73d9643004fe72d9643004fd72d9643296bc42d9643014fe71d9643004fd71d9643014fc71d964300cfe70d9643004fd70d964300cfc70d9643024ff765
  | 48 => 0xe71d8d54004fd71d8d54014fc71d8d54576bf41d8d5400cfe70d8d54004fd70d8d5400cfc70d8d540067e50d8d545ae7c50d8d54576bf40d8d54006df6398d54005ef7258d54005ec7258d54005f77158d542a5f47158d54005fb7058d5429df87058d54006dd6318d5401cfd7518d54024fd7418d5408ede5318d545b6dd5318d5408ede4318d5457edd4318d54004fe7218d54004fd7218d5457ebc4218d54014fe7118d54004fd7118d54014fc7118d5400cfe7018d54004fd7018d5400cfc7018d5401cfd75d8954024fd74d895459ebd74d895408cfe73d8954004fd73d895459eee52d895454eee42d895454ebc42d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d8954006ee20d8954006ec20d8954006ef6298954005fb705895429df87058954006ed621895401cfd75189545667d75189541d6bf7418954024fd74189541d6bf5418954566bc541895408cfe7318954004fd7318954566bc43189541d67f52189541d6ed5218954566ed4218954566bc4218954014fe7118954004fd7118954014fc7118954566bf411895400cfe7018954004fd701895400cfc70189540067e50189541d67c5018954566bf4018954006ee2018954006ec2018954014fe76d85542a6f661d855401cfd75d8554024fd74d855408cfe73d8554004fd73d8554004fe72d8554004fd72d85544b6bc42d85542a6f651d85542a6f641d85542a6f431d855400cfe70d8554004fd70d855400cfc70d85542a6f4615855400cfe76d81540257e75d815401d7d75d815429efa60d815429f7a50d815401cfd75d815429e7d75d815401c7d75d8154024fd74d815408cfe73d8154004fd73d8154004fe72d8154004fd72d8154406bc42d8154014fe71d8154004fd71d8154014fc71d815429e7e50d815429efa50d815429e7c50d815429efa40d815429ef830d815429ef820d815429efa10d8154005ef7258154005ec725815429ef8605815401cff765925308ebc645925324f5f5359253296be545925324ebd545925308cfe735925308cfc735925308ebe435925308ebc4359253004ff7259253004fc7259253296bc4259253004ff7159253014fe7159253014fc7159253296bf4159253004ff705925300cfe705925300cfc7059253296bf405925319f5f5398a5308eef6298a5301cfe7498a53004fd7498a5301cfc7498a5308cfe7398a5319eed5298a5308eef3298a5308eec3298a53014fe7198a53004fd7198a53014fc7198a5300cfe7098a53004fd7098a5300cfc7098a53005bf7458a53295bc7458a5317f5f5358a5308eec6258a53004ff7458a53006bf7458a53004bf7458a5301cfe7458a5301cfc7458a53006bc7458a5301cbc7458a5308cfc7358a5317e7f5358a5317eee5258a5308eef3258a53
  | 49 => 0x18000000400000140020008002000c00100240030030000000000200180020014001000c0000000001000800000100060004009000800100000000010002001000600040010008000000801100000030034000000c00200000050004003002c0070024002000400100080000000001000000000000110004006000c000000000100140150000002000800100000020050001000000000000030020013000800200000040000000001000000500050000000001400400000040000002000000b000400200180010000002000c001001000500000010010003000400300000010000015000000300400000000000000c002000800500080010014000000400200000050090000000c001000000000040000000004002800000040000004000002000000040010000001000000100100070004003000000000140020020001005c00000080090004000001400e001c00300740010000000000c00400080160008002005c0010008003000000600000010000000000000000180020040000000800000380030000000001800500040060000002000400300000000018009004c00000000010000000000c0030044000002400600000060010002001000000340000000000000000000000030000001000c004002400e001c00100000000010004000c001000400000040020000000001c001002c0000000001000000100340000000001000800d000c0040038001000401a000400000040070000000002c000000c00100000040000010000400000000020000000000800300000060008000008c004002800700000000000003001000000100000000002000400000280000004002000400100180000034000000400300040000008000000c0020050001000c000000c009001800e00000030000003001000400000000000001005c006000400800140000000002000000c00000040000000002000200000030040000000800000000000000003000c00900280000004003000000000000010000000000c000001800100040070000002000400e000000000080010004002000000400000000000002000000100040020004000001c005000000000000050004001002c009001000100040020008001003c01b001800500000000004004000400000000000004002000000200180000004003000000900140000000001000000000040020008003000000100000050008005000c004000c0000000000000c0000008002000000300000000000002001400300280020000001000000200a800900180010000001001800000080000018003000000100000000018002001800400000020034004000800201cfd75d8d54024fd74d8d545aebd74d8d545aede53d8d54576de43d8d54576bc43d8d54004fe72d8d54004fd72d8d545ae7f52d8d54576bc42d8d54014f
  | 50 => 0x30000000000000080040008001000000000040000000000000c000001400000000150008000000400300000050000000000800300100050000000000000100040060004000000000400040020014002002c008000000100000080000002000000100080040000000000400000000020004002002000c0000003001c00200000040000002000c002000000200100000004003001800300040020000004001000d0004002000000400100020050000001000000000250000000000800400200030000001000c003000400000240040000007002c0020008004000001800000020000004000000000040040000002000801f000400000040080004006000000000200020014007003c003000000d00000050004004001c00300000000024008000000a0000000000001f000c003000c0070008001000c0010028000001400800040000000009000c00000080090044005000c008000800400040010008000000c0040000008001000500000010000002000800100080010008000002c0000050000006c001001000200000000000000000c0000000002000c000000c001000000600000010050000001c000000c002001c008000c0000008000000000c000c00500500030004006000c005000800100280000020004000c000000400400040050000002003000000000020004000001400000040000004007000000000080000000004000000100000090010005000c0000038000002400000640020000000001000b0000005000c0000018009001c0010000000000800400080020014001000000f000c00100000020028000000c00000140040028001000c000000400100100000014001001400700040020008001000c008000c00c00000000000001004c0010000008000000900180010004004002000300000010014004000000b00100050004000007800a00100000004000001400d000400200000060000001000000300100000010003000400e00500050000000000000400040000004000000800000000000000002003000300000020010002000000000000000010003000400200280060020000000c000000403500180090018000000c004001000500040120008001000000200300030000001000000c00040070014000000800a000000100300000004000002400000100000004000001400000040010004007000000c0088004004000200080000020002000c0000024002000000a00340000060000000c0000000000000c0020004003000000000000000000002000000000000030004000001800a00000000000001000000300000010008005000000000000000008000000000000040000000011000400000040020004000000800f001000300080000000000000001a002400200080020008000000400100000070008000002c0070
  | 51 => 0x10000001400200040040004000002c00000180000000001000400d000800700000050000004001c0060020007001400f000400100000040004000001800200040000020000000000200240000000004002400000000010004002000c004001400000100000000000001000300140010004000000000000080030040005001400800040000018000000000000000000004004000400000000000030000004000500140000000001000000000000000008000000c000001000000080020008000002c0060008007000000100040030000008000c00000500110000001004000200100070024006000400100140000018005000c0020000002001c00a00080010010005000c00200080000000000000c00100100010004001000400400280000000003005c0030028001000400000080000000002001400400040070000004000c0000000000001000f000c00100000030004000001401800140000050007000c0000000002000000000080000000004000c0000014000002c0000004000000400200000000004003001c002004800800000050004000000000000040060004004001c004001000c0000001000c001000000500000020000000000000c0038000000400400000000004005000c00100040070064000001000000000020004007000800400000040004002000c006000000d001000b000401a000c001001c00000000000000001000c000000c00300000000000006000400300100020000008000000a001000000140000008005000000d00100000004000004400000240000018001003400800000020004009002800100040060014001001c00400000000010007000000100580000004001000800a00100000000006001000900400080008000000401100040060008000001000100000050018008000000000000040004000003c0080004002000000000040000000000000c0000000001000000e00000060000001001400700080010004006000400700180000008003000800b0028001000400000180040004002000000a0008000000000000240010010000000800500000010004000002800900080060038002002c00a0000002000000000340030008006001c00400040000004009000c00000040010000000000400000640010050000000000000000020000000000c00500440000000008000000700000010020002000800a0004005003800000000000020002000c00400000020000000002c0050020002004000400040040000001000c00200080050004003000000600080010008006001800c000000400100000014001000000000000020004000000c000003c0000000005002400000240050010002005800100000200000001002000400240000000009002c0000000005000000b0014000000000c0000000000400e0014
  | 52 => 0x1c007000c001001000100440000034002000000300040000004000000800000000070000003000c00200000030008000000c0010004006001c000000400400000000004000000c00500000010000004000000200000090000005002c00000000100008001000c00100440010008008000000400000030000000000800300100020044006001c0000010001000400400240040000002000c0080004004000c0000000000000800200000000000000000c0020004006002800100040010000010000400300000000000000000000f0010006001800000040000000005001000a00140010014004000c00100040000018000005c002001000100280070024003001000000080010000000000401d0000002002c00d00080030008001000000100180010000000001400200000000014007003c0000000000000c00200100020000000000400f0014000001000100000030000003000000b00040000050003000400100080030008000000000a000400a000401100000010010000000c0000010000000400000000070010000001c00200040040000000002c0000000001000800500040000000000000000100180000034002000000b001400000000010004002000000700040180000002000c0010010013000c00000040010000001000000100000020004000005401b0008001000c000000c000000000f00040040008003001801e002400000080000014002000400000000000008001000400000000000008003000c0080014002001c00000000050018002000400100000070004005000400100000050004006000000000040010044000001c0140000000000800100080030000002000400000140000000006000400300000060000014000000c00000010000003001c0000004001000000000100180000000000000400140010000000000c00700100020000007002800d004c001000c00400040000004000000c01500000030000000001400200180030034020000000300040010000000000c009000000000040030014000000001a00280020000001000000000040050000011000000100080000008004003400100200030000002000000000000000004013000000000000010000000001000100040040000006000c00400000010014004000c00c0000002000c00000000040000001000400000000060000005002400000180000008000000000e004800c000000200000000008008001800000000040000025001c00000000010004000000c00000080000008005000400900100040028000001000900040090008001000000000080020000000000000300000000000001000000000080020000004000c003000c0070000002000c006001c009001800200000030000007000c001000c00000080150014001000800000080000004004
  | 53 => 0x1f732252000000012fc000000000001cbc00000000000204426d8000033b91760000000000000002d7a0000000035100006d70ee500000a984e6502612902dd05d38f29800000004e08000046a25f40000000080c000000001cc0d3126d246c45a616460aa81038cdf8fa008787468000000000000d40675915010241c104d7935a09ac36e4000000001a824c80000000000000000000000000000000000000033470b4df4000013ec000097d80010000002003800400140000024008000000300000030018002003c0000000006000400000000070000004000800100000000004004004c0010000001002401100040010004006000c00f00140030000000000000600040010000004000c001003400100000000000000000c000000400800000020008001000000d000000000140010000000000400000400010004000000400300000010000000000000000480030034006000400100000050000002000400100600000020000000800400380140008000001400300180010000002000800f0004002000c000000000300080060000005001000300200000000001000c00000040000000000000800200080000008004000c000000c00300140020018000000c0000004001000000100000000000000001400200100020000005002400b00000010028003000000100080020000008000800100100090000001000000200040010008007000c000000800000080020014000000800b002c003000001400180030000023001400000040030008001000000100100000028000001800100080030008001000000400080000000000000c00d000000000000000010000000400e000400000000000024001001000300340000004000000000100240000014001000000700080000000000000400000000020000004001000600080020004004000400000000060010001001c0050008000001000e000000400080060000000000800900000010000004001c002001c006000800200140000044003006c000001c00800080010008006002000000000000000002000000000440030004002000c00d000c000000c000000000200040000004003000000400080020024000000401200340030000007000000000040000004000000000000140030000000004c0020000006000c0000004002000000000000090054004003400100380020010012000400200140050008000000c0010000000001800600080000024000000000000100170004000000400100080030000000000c003000c0070008005005000200000020000000000c00000100070000001000000100040050004000000400000100010000005000c005000000000040020010000000000100040020004005000000100040000008004000000200600040004001000c0080004005000c001000
  | 54 => 0x3a20000000000000001b98d1400002d300000000000030060000bac01ba18a60000f6316243768343005e01de21e25c18d1791481b4e68d00d3203a00002f4cf65800000000000b6912c240124af49fb9f652d0650000000f342a3a75c00000000000027f80000c1519ba563cb0919fa27ac268047288d9232c5f8ca7280b8000038ace200cec00d002e8ea2800000003e2c4cd0caa000000000000913118c1448f641d54000014280000000021c4de80000000209c443054d08011ce4000000002ff00000000000059534aa3724000000000004b280000000399600000000000411853cc000015b2ba2355cba38e9b00004f4c0000000000000001e7016f36fc765c0000000000021740620000091a0000000000032266bd8dc400000000000000005c20000273800000002be4541c000000000000000967010c3fbc2f80000006f000082340c51cfb00004bd0f5c00002e1e00000000155000041bcd1e062d3b500000000000000001e1471481440000384c43d00001404015019b80002bfa12d816a00000000043c5878000201e0000083000000000000000000000000000f2a100e000017c493380003f380000000138e08a83c7804c0000112e20f8000000000000d480001323093231800001592000000000001755055a511c0000000000000002e418a300001bd40000000415c00005768000047044c0f6d987f00002f303a603950d9028b4a208000218864c4d261ce923881cb8000138700000000e41809b3c743c4ce3c000000000000c7901470000514c0ae800032b40000cde00002f5e0000109189a0f3e5e5885b8000000000007891d4f1f8c6508000177d0000634461d84bc2e24227cd8b1031382203c4ae2204f333066041dc175f197c00006ec1adc224e7184eb20f4802d062889aa99a3226466700b70d70204a29fce62000000002ee43f9000029aa0000a93986f0000000000000000000000065720ad10f25ae4ec28000000000000001a3f00fe819000000002ae400000000000000000007230000000081f00000ec300000000d61000008522bfc34796c1000037d8000191b0ab80a04000186428e05d20fe50457095c8090e889e7c30b865500d10f2e13b65410e2d1f4f079628ec802035c00000000000000000003ab8ab715ba047c00000000b3200000b2c5498cca000000000001b2f00000000783000d276c6c08aa980003848221c0d919cc00000000ba6015806ee2ba4dd28b3d039e00007e78e9c2d2e00001068000000000000000219262640587ba19e535be46102ae97622f342f6ce03977e28e60000fc9830f1a1e1134c9e000019143d4050e88b127465340a1b81f0000062e00a280000b66707c4d51cb600000000b5a8aa626b24034986800037be4a14acc1f5219446080f581b14000000000000000000000000
  | 55 => 0x1c4000000000f1f00000000000000009d60000c5e203e00003a80000000027f60000c8e1ea60e1e16d40001927295a3224fd09ee414c05ed03b8143d155200003521a0b00002f9c09b81ae0a2200004e880000000191c00005b10c7a436c390930c137c7e185a308810000637828c83ba07f4242ca1b116500001fdc00015a12b08000022d9aba00003a580000e2a29b803005af839a00003da000019882dd6000086f9f4400000000000037400000000000000004c40000000153a00000000d6d011f1e827f2c000000011e60000f8780000000698c0000000000033c4d701fff00000000e76000011be00000b684f103b659fca79194900005d4ce5d000024be677c00008a70000000000000002e6c0000000124e22ba0000000156205ae27b87419b2719f264142b28e22373a000072c018832686ca4718075a3cee2850bae9cd3000e79989a1085e22986994bd01189019621bc00210190db8000000012001d9c65e40000000000031ec35e00003a14626c4371ab70f9880a86c20dfe2ca45dd407209d4000000000fa966c000000008c9000000006f1800011b8130e35d8fcf0324408a748c59a10800ffa312800000000000000000000002d864f3cce68a2518082590000000000005ab855684621a665c407e4800034ea47d8cc7020f00000000b210000000000000000f3a00001f58be70efc0c0a04f48c0a0692a54798c000000000005c94fca8201000040540001f8e0b2e53b40001ff82cf80e0cda790a7180029c40000d3f00000000e9b80002bf000010210a9c016017f800000001bae000000007b81be850a4ca18000093600001488000000000000b515c506ce7898e0600003a7c000047780000000000000000001b84000000015ea409c77745fe089e160a6c800002085394200000001a85110c2760a718b61316035ec0fd0000102c0000000000000000000cc48000000044600001a69270660850318c4b000000000000516000000000001f940a8a75384700000020e28cc00000000f4c00000001a762984000000000002aa47924000000012745074ce500000c180000633096600005b2c0000e39000070d092b800012c23734e279a0500005e9c6a41499074e30ac82c072810cc33f08e4893f207425104ff888a0e0a81e8d108000104659144f79c2e2c283620000184200006f1c00015a015780000e0d80002084805c07600e3075019bced6090111c2000035d000010b00000981895d00000000aa3169915c0264ccff800000000000a4e99290000820c0000000000030582429a88068c000000020a0000012400000409000000001a3988a38ca56b80000857314e3004a8691c10cd61d9c20b02ed0bf627dc7a003b137f46ec0ebc03f501065a14e6304890000000000000000000000000000000000013823b1af80
  | 56 => 0x24de00000001c1607d600000000000000000000001177000000000000000000015981510000180c00000000c91248c4cd8e4f1465004c6d74acb89040000704c6ef8c7d288838e8fae000009ae562c9c88000265654e0bf11644000000000000000000050440000372000000b04ad0000242c0000f7d037a00000000000000000000000000036116dc17400000000000026e40000e9d02fa792082f8000015e0001032800000000000000000000007cdc01792b32f78000025484e5000000000139b6100000000ef200002a50316c00015eb010200000000b3500000000bd9000037640000df70000000000000000c0501280000000123f15603d6c94f1c0314fc53f400000001672701000000292f361c0c5711b70000063d0416166200006044000000000006db40001855000041f477381e6116600000000000000064acfaa80000000414caed976400000000000000000000000000000000005c6041700003f10000000000001ef200000000000000000004d28000130000006be800025867a9012c00000000011889f8000000064040000fb93e2e15f8d9e836b1ef85450c7207c2000008009740eee235e77fcd4a8e283bae046827517720228281ccf5800037d81da0cd280001d30390862e14fe3c841db40c680002d606fa43b19e7014187380c8a0e1f196201f807900003aa00000000000014b80e0432600000000000000000000000000000001f80000000000013e2000027587b388670bcc55080000e01200000006f3000035f40000aab079924586b48c16074f3a101a74798203c00000000eda0e0a0000013cf55993605a44040df81b50321a5abc8dd8d0400002220d171f7700000f3400000003c36000000014812688725405281f72e7c000000012790182000042c9fc23ec00a24ea6800000000000053000032da000000019c70000000000000000000491c000000000004be433182ef0000000000008c73b30618c0e9122903f6000000000001096000104aa02e2dc06c302c6800000003209017945619f06c94f59893038f6107903a86a910886210a1e01460c5e00000000b8700000000000000000000000f01000019387a4cb6893f134da59c00fc9d6900005dcc7a991cc0000228c000000000001b1c61700000000000000000000000000071d82450000603cfc080002846000076c932214ba00007070000000000008a70bc33c243c94624890034587e9813a1f2b00006ca0ccc808703b036e8000147d18a40000d460fab0100404c8380c370bda69901e08e5e33500000ad684663fb43488000155a186846cc000036c0ba473146548e86211217cc2008bf2340265704668000000010900001f6400004b8c00000002bf40000f3d98e70000220c5998000000076ec69700862f8800700000000000000000318fe400000000
  | 57 => 0x57340c04ce48e4000000005f48b621ae23ea06e7c00000002f7a2fdc0000000000000003c5167300006e1479b853a28307d3400000000bb204800000000329425fce9d15cd3dfe7bf43341ddc1c803dcc0001c4100ee4578000000b31ae7fe85738d6221065f34000019200000000e6e0d0030282a4400005b222fc4a5006f171d0c687040ae78f3100004144e72000012e400005ad000000000000eb0800000000000000000000004ca8a52800015ee00007db1e7d00004ebd00d80002fd815c4646a05100000000000000000003754c3380000b2063e0752842d000076a400000000000096c000000000007214d651a2b25263a2400006f92e260000abe169d33ac0000ffe80001366000000017be2a8229188911c713eb400000001ec412a86134000162d04ca0000ec8091f1ce800004128000096e00008ff8d1d000081c809900003b960fdc0000000000000000001cd1242600002859f0d3c380fb4f5f1567387e2f440001e7200003cfc000068000000e14b9f9734000000005620a1600006c7082a8da8299a000000000000000000000000000000318400013ef40a62bd02f507aa2ef80cc4e970e970f80000000000003ae2266000003880000803091d1b3810826b6c3aa9c29050e8250000000032e2000052c092400000000cdf1bd914aa00005e7190e02d2000000019f700000000000186600007cd8f3a0d6b2cee0fb89b296282c3c6e84e2c800007a25e1c2841abc000000000001739000033940001eb7253677002f400000d024050e5784e834b838d00000e9200000000e3786a80000000098f039100000000ec51d0e000055d41eb8000384c000000006c300000000000000000000000729000000000000000156a00007d84aa600003cae000083c8eb800000000df9015436d02310e1b9fd5393e71a484f831419fe4020cd38fe8061836f4e958fba03e2317c0000000039a42a8000050900000714910034f00000be100e03c32a00000000000001b2045e800000001c187834d120edf320600000000690211c6698f1500000e3600000000aba0000318c0001cff000c31d0e10000015186f80000000000000000000150a15d863b4abe86dd37626f487db88a2175800001468d163dea6928000000000001c88c22111506ec2240e6d0bda12b60cd400011ba2b006ab834200000d3c443c00000eb0000790000000000e8277e8f69145f00005664c70873f089c3c5cfa18b9e1d2048c825a848419c45f78f42998d00000000c19995f23387f5032a88bc1fea0000bf88fd30ad01a8ce191ee7000000007c8997f1ec65614998983135a65e5c07ba080239a0000e708ab400000000000000000d40000000011535ca049ceed8ff3073e0000000166d000080604bc1dfd2576811836c058c07785694000128e00004a240000000
  | 58 => 0xc81899d76013e579cdb9886130b070c0f73159616a23078e3b00003ecc2a1856a1ae437e23d38a9808cb00000000000000000000c2000008a840b4000000000000b965cd4bae000040b6000000008f02a182fa420a07b62c5643b4a8b8ca50f02287ca9a9786117a000000000000000000000000000000000000000002c5c4aa80000d0d00005ec400000003bea0000000031e00cc7ce4b9900003698000000003ac000059a0785800019e850d43538000000000004d48379000027a059e079e41388048d190000000000005db0d8e00000000000000030824130c701d4c2fb024ec0001de60bdc2ce078380003744662c00000003c2800000001928000000002529a1601107dd840700000000473c0000000128a4e180000000000012f48cb80000000612ced80a5e006e58b0edc000013b481dccac000035c60000dd21b45000000007f91986000053f044b1d473fe8000090f8000000008103849a8716f8000000000000000000000000001e5678f800000003b5e0d8027618c600000000000000003fc2fc0ff08d4f34e600004f3823f26be00000000da6000062a468518f305fc04643d10000232a5654ca7800000000000a3004b201346dec3d89a5b3b921e48799821e00487a649cb9ece2d7453ecea9207b2c7c6480b1b0ef6000045bc00019721174600400000002a4a6220ab400b20ce0182c000021c00005e049fa0bdd3f205390840800008d6000000011e000003af0a0391ee1e720000000182a0f500000a201fa81db82fc4c7b992314820000000000031183c600001b3214c45c5400018451c2a6f880710b66090e6158208800011b4136043a817114d40cc885c89a126de00003651cb72fac535c06700000000000000000000000685000000000000468838e82302b544db8000000000006f54bc00000000049ac5e114383f5c00006078000000071e8e1e8000000000000000000298078bc0000000372e6f34de2000009940000b52000019e641249db800000000000166000000000000000000000000f14000000000000000f67883b32dc36b800009d93220127029f9e3b0a9022b4e60000000004c6800004ce00000000e779dd9315a000000000000000000059580000a9c1780000000000000000e788d1e136c08401848e2619166678000000000002c4438806c5036200000000000000055380000000000015b83ff17ca23ac511487a13813f6e000071c0f720000000097b9b0e0000000000000000000000000014aa1e9a0000222022111900000000000023c8000060e8000390229303241cd700000c88f0317f52bc00000d0800001f2a73345258a5900000000bea1b1b1ed661e433a8000210445f0000000022962e50000000000000000f4d1a43305c000000000002d4000007cc16790000000040000000a1e000
  | 59 => 0x1ab2364800004d60000403e1d200000000059c0188398117b000000005fd80002d84000004a8000000000007e09f1840143bf8b4a801500002870d1d9bb806e65d8cc59800000003f48c0c85772604708400000003dd222e0e0e8000142200000000c090000000064d0d2934fe31c800000000c200000000065a0000000000002562d260000000000e19b048bc0f09aea1b5e2e40e9b00083a3637c4af70f2309761c4c08982a50000000078605da3a4e0000bed80001d46223d02c865d00003f888df1f7e000053d045f039900000000b7200000000000000000001bb62cc0000000009102a28f11152e37de0000000000000000000000000000000000000000000001c18000200400002fd8000137900000000000033422d6000000013d01a300000ec980000000000014b00002a520000a0c800027527ea4b9004a13b906cfc32908bb35961244000203f04143a98d1b97540a8c47e0255000000005cf438697083eb606100001b621ee0568c00000001d88000085c00003bb40000000118a1c340000cee9b1119183218439884a14003aa42720358043a20b495a9e6f00000500778116a3af8365055d91102f8a7bf80000b1300004b44ddf0b631e8a12fc0000000000075740000000048e2aa8000197500000000eca10722a9e0000eb7193b14ac000000000003f320000b708e0f2aae5930e0e193f12d80000e0316ad000000000000e1900002c2c5ee000037840b1c8d6800000005c501271dbc3c6637843dc8000012403200c582e313060000000000032440000ead0fb82ece08bc9b90933044a0000107077f2c7844141d100ff2558000045b1c7f1fee000013a800021d8000000000000464455c35d8f8d2b1a2778993000000004ccc0001da42c1e4924b3396ee0000756ce250000000055981421aaf2b280000000138f0000000073a80ae00004af0000074426220f4800003c62fc2755400001ce3ea85ecc92612a9000065d8faf8000354a7f60000045323640000000000000000000b7d82fb11800000000165e0000000000000000000721879c00003e50131419f1eca2792246c00005691f780000000000000007120000000000000000000026d1c5c00000000aea2bba1d6c25a021100001ae00000000000042c800008a11640000011016041fba00002ce8000345a45183b094043234824c0000000388e0000eb797bf17fe0000000000000005f080000000000016d0dfc000000002c84f6614221ba43dbcbc9829200002aac8fa13491f6008500000f2c151c48dc0001a46000000004f284db000048f8000000030f0592090e800010900000209877132aa49fc1d517c813e80d8c62b00ab00001bf40001d6a00000000825998c000053ac0001afb228e3ff44581e92011a2c200001e8c402a1a5c375161717c45a7ca05000
  | 60 => 0x61a4966133e24c0000000000000c364a98cd8800012705794fbc952f39dc3570d6786f627c80000ae196963254446471b828e16462264fe3168a01ea3a9c000100337560000000149a16e47b7000014083b5621e08f0800040423c24a0f80002820000000011c6000072c000008762f145e4505207c510346dfc8579c933752162ccf18000057e23a03b4800000002648000000000004b14000157600000000a0f0000403c000000018a80000000000000000000000000006ec000000000000000114c3e98a92000023ba8074000000000000000adb1aa2000000008dc8865304a3150c238000000000006108bbf2fce7dec0bf1a960000132477502c9000008b40000a22000010d00001cbb2ad60000000000000000000988000000007814000000000007d040001ebb37f20000ea314a13700000000013d53cd6000045293730bca49b00000000172a2b98695080d236a28904f599d836dc72b016880000c9400003728000260c79fcf7c800000003e9438e0f9200004348000003a0eb21a140110ea225b00000d2f924425aa000069a81fc00000000022150f12d04ec8f9f037100005ce0ee1800000000000455800040b000000000aac1838489c1af9a9e00002cec2ff800029702a6037f8a6e000045fcb860af031901584ee801dc0a800f906d0179031d20e3487d0000000000006660c6e2d444080c4f1f21311e00000000bb835702c1c5a1125c00000000112000000000000000000000000000d869e550edc11300001f530172277087a80000000000012516053bf272b88ee013e370623f88f790290bc82df405481b43fae000000000000000000000000002664718cb67800000001e8c0000e5000001614265800000001a31048914027141c200000562088c37a80001095178c0000e4a027c2ea4000064f0a0937c20000000000025fe2cb49f4964902e400001f500000000133cadd8009252e566cf8f800000004838000000039bc324000000002e165138d518310000000001db82c20000067c4ea800000000000d95800000000000acf8000000020e87c600000000000012b80000000481068c84773796000069d102f00000000bcc90a939f00000000000029441870000000000005fa40000000234e0000f5c939b1c9e789c0001774164c60dc3190b270e16524803c0a3f1fa81724cf980000000000000000000000000058200000e92000069a0000225a000057c18da0000575ccc288292cbe0000a2105ba0a52000061180001bdc3f6400013da00006c887910000000000000000000401c000000000003cf00000886800000000a7d024800000000000c381163391c1f24681023300004060518800002520000ef8968c10627fc0cbd8a3724181b3c0000000000078e0d21111c000074e40000e6d3376577ce908aa41b2e00
  | 61 => 0x6182810000000000000000000000029080000000000003600000000000000000000000000048b800000001dcc0000c190a6f2668102cd2a1eac254077d00001a86000007304459a3d00007afcfb80efb233a1a080000207320c06c00000000000000001de80002918557c00019d7139680a4f3a96c8115482c84a185fa1aaa6ed8de500003f2468a45e2800000003f2c63894b5124400000001f29000000005590000000000000c8800000006eb0000000000000000b870f1400002f2cff618f5000000004e21ba83d68506c73e153c0c12194cd4d8a9e1212415862307660dae7ff02579bbc000000005de98ea121a2c74e881c382e3e0bacb63907427ce4fe4ed01de70820418cca7061400004b780001f8339906d180001d6232a000000000d8b00004dc4577800004ce45cc00007cf3cfc5a6c000000000004f848048000000000000ef8f1a00000000000000030480000ff68000084c19d8000035e00004ec0000003e310a000000000001860000081e04e3000000000000acc00007244000000023864c84dff1ef03efe0000200000000000000517800000007fb800000000000000000000004004316500004a6000000000001b573ef8000053b0a7300006f148cd9b72000000008e98cc81ac023548c3800000002014d0200000000262083680003b4a56b0c0614053ba260ec000000000007b5c000172200823b041c917cb1b124b3cf9199a9000000007e88d71000000003f410a111f84b7c000042700003ed4a51800017747c5081f80fe09fc000082c9c6600001efc3c41cb200002d40ab68e25000030343b5842117162d242e705bd35ee1f5049b8e790000688c6ea00003c96000058a0bf92fae0000f3208d605d271b0c8c0000249e00000000b29000000000001fd0088211540000cea2a266420d0905fc16120a8000009a80000567037b8000000000000000b651022065c0000000000000000000ab5053a037c657800000000000000167d00000000da38a29087653888cc800039d41450f6d06212c40078c0000000389a00006179f040000000053200003b104bb093d00003f5a45d0b4780003176593cd2b12da172468287270000216251ec6fd1b922a3c1ffc934819435327474000000026983e0c4759776000022d421501c1000053048118fc400000000000141300005f7c000000000004c48ac31cfd0000000015603442f6a1fe8000105c3f14000000000003a380000b3c1b6a1b526008dbe80002d70000000000000000000000013c3102e0000ac1066d3a860000cb407c8381e000070580001e76000000000003034000000003e900000000000038b19f40000ed1145a09e85a40e000f7d3a62206cd01000018ea614800019a4000047e8000000026fe00004e48000198e50b8000000000000000000208921a8000000000
  | 62 => 0x5f800000000000131800000000000000000000000000522805c160600006fe800000003fd90389e2500006c10000000000000000000023a13f05330000086d04f200000000000000003680000000000034846a380002c5232980000000314018f0000000022626d60f1709200d2849d4b850000366e23c4000057f00007a7cf8e80003c880000000000034064fc0ca00d2d320025e86c0091700006f3c000176900001fc00000fe700003c647451721000021541e78000222c5fa0c6688cc351e000000000001fca621ca6880000000000102e8000000050a0688209236c80000c3295b000005ccc48e12e036ac00000000a440000000000000003a9600009809c1e00000000f8080000ff800002f38000263655105c9a0a112045298a310ee8331e3fc498381e203e87fbc6c50b3a38a20000b7f0ac20000285421c800000005f9814c91201818000095408852b7200007ba89ea3d62000030995792d5270a00f400233e1643446f994de000049a8033a06b05ac2070da89d581fd800008010f9c04a600000000e493b0c73c043b94e030c029843b9800025b651786e70b8600006754f740000000000003999dea000000000000cb0334200006198000000032fcc2480001b040000000051c4058370c6c880000000000000000003bc266743f394503328537c20e84451eb26a34735800034c40000d9189ec39685068207800006824cdc0001d0300005aa893c000000000000ab6163116c450ac047000035c25574b058e023e660000fe7000014300000fd9151a00000000000053000000000000000021ba159c0000000087a6ea86918a520f4e6f5c000000012fa2608d7711d4000000000000eb4195600000b18000026a00000000ddc351440b4919810b055c000000000000000048c00000002c3000000780000000034bc4d5800030240000000000000002c54000014300000000000000028680290aff0a492f2472740000000219e67e4cd90000335600003470000116e79582d48c3f121c7124f0d000024e275642c90390088607b4f34126e233c660c43600000000000000000003e943860000000014947e8c7c71fb400003d54bad87f916fe2f1c000000000000394cb01e8b02f800000001cd40000000087f128416e06c78eb58000056000003c4800040722adcc2b974532224e209cf000000003b88ca8800038a46cd4ffd99e800002e2800000003c3a12689bf000000006fac90487ae18e6541885700003e4a38c81c4867909e40224622837500f8524c34b139a260a000000003f8000000000000c1f00002d042f800000ccc49c000001a400000000b3a00000000000000002a100007458000026b000014b866e000000000000ae606314146211c00015510b464f3093d92301cca00005681d02000000000001f6d00003
  | 63 => 0x6e08f279abe17080000523829b3cd2130c00020b4000000004f9877700005ce80001075000053e047a069331c4263cdbc01770654226c00008d0147202b06f103f2147c0000a0b9ad604aa68c424119ee36c60000c93164334e85a249f702a33fee405c0000000000051d89ef150501c200000000c870000000031c80000bd262c441a9de9181c28d04c5000037140000c30861900000cacc311b8d0ebc5e38016800007a60000bb4000005ce7a000000000089e00000000baf016e3f7c8759c963326381cc2501123c7832900001d9528285e549ef9d0f1db63744f8e182721782fe008f0b1c3e980fcc66b1eb63f76285c1678000092e529cb6e8c64272a000000000000a2a0000ce412553ce682bcf471c0e00c857fc00000001be448140001b3100007510d7780001e5224ac9c600001680300800011901706062457d960c2a427b780001702066c2f78f1485520eac00000000ede3dd6000000000001cfe45685669c0200002158a4f84dd3e640000e650f6c06ac0000b001eed00000000c340000245a0000000000000000000d5a0000000000000000000207a4dd400008d7398e54dcba4899d0f762140ecc8fe0138e789020d854f000061c8e45155b3b02061cef8012c0318490c4d90db6311a7f9800020ac0e4a455086700000000000000000000000035c0000000000000000000625000042e8000000000002e38cd68000207200000a104d30000000000000002ac00d5cf8818402db209a47138aa726f60c18565029800260bc8464826a00000000185800000000bd0fde8000194e7e08000000018d478380000a3d000433785970000000000000001ccf1faa000000006a0000081546d29f26342268680db067c00000000b468a79000064f46bf801400000000000000000005250000000000003eec79e0000100c494004b204d2b684358bb80d9c16de317809b1a6600000000f0580000000000072a0b6b00000ebc000000000001e1865d80002050000000000000a1a00000000e4a05c01a346b394b600060000000044a341a614c0000000000001ac6f58c841c463f8c00000001d964e805a58000351c724000017ab0f0e00005df000012ea00000000be60cdc81704940c1834c00014c7f0c7a00000000000000012540000000113a0000000032c96df000000004cc8c6d00000000d508ffa2dfe5fc80000dc816fc3a00e6fa043231c71a8d599d2604c859e89589a6a0c5403d014e0000169400006a680000fd823a400000000e7a0000cc800001dd8000000000003930000067918d30000358cef001f62ae87a5c000000000001d1c968000027940000ff18836000001f4d22000015b27a4456b000032ca0000b40800000000000806161a089000000000d9e1dfa00000000000000032c8b6811641e9800008458d6c10c800000000
  | 64 => 0x195b032a74d0dcf0000000082780001854285a00001721fe70afa5cf0d890525415400f4fc618bf2ac66c14b2012f2112a0000af9815c0000160c915810a3f4e0000000060e3d743300eba8de4000076e80000f780000000000000003d40000019e000034f86f240000e510000050400000000000000000009ae1b1e0858b3181313d081620cfa80000be8000092c800038be27d47fc0ebb000070cc061173b32a6000000017c0000050e4000000026c8313c000000000001d2c00000000a3e000100b1ef302780000000000000000c04000123c018c80f46d19022086442ac9be9dbe0000000003083be12781608af310bd22926408e501e4c20ee7cec18c80001a86492c00016d5126a00007719c3a000031607e397fe176a6c984c696fc39ba0bd4000000000000000c5b1578261241e829006e9042665dc1a981a30b1e0980b071b8700000000000000000000000a2a00002e0a0000e8900002a2c0c1c8770000000000000000000000047f00000000000010ac38100000000412821980003b1c72f50009dc43b82000097e9203000018a400006740000000094e80000b600180000080700000000f3d014f1c4200000000a82000000000000c0b000059ecfb6160d136281580911a7900002be4abd00ef0000000000010a820fe00003b618e600004438a5d02d800000000c9c80001a2e2f0448282721f1000001981fb613280c347bf052c0000463c000000000000000d621f12000056a07e680003ed66a98a5794b728ba81d00000000000000000000764000000002ee8000340c51e4139957e00001cc80de07be0c405c34000162239ac2af415b9a7d24160194000000032e810d86271a532f120000bfd163900000114000059b00001228ba7800000000eb5045000000007f648979be6000064f800000000000761cfa580002be04a040000544021a000034488b904042a84a6d00003d3800003f0072a29a86a24bbf9bd60e4c00000000000000000000000000000047ec000000020f60000000172d2cca000053680001c385dc45da19b928b03fa4b2d8a850bee39c067b1f1611840000000000000000000810966e21fa00003a707191d8e07a8cc11368000000002d703ab00001a2ce6d991e000000006ae800002c000000000000000077e00000000000000009de01b50000000000000003b540000000000008fc000016080000000000000010611bd2000000000d9000035a4000000000000000000000000000000000000012340000fa111cb0a9200002988059144c00008600000000000009ee98f91cc857204b01238000067b400004f822c26e50b2816190d660984b9617f436762a889009d7428d20000de08a963c6243c840f952d34ae4fd89aa08e42baa70b03ba000000006f380001511185a054031d095e353e5fb4bd60bd0375e
  | 65 => 0x13f000000000ad4000072d800000000c8c0000a5305ba5ee8ce311f72d783eb008e8843103c27f49268fa1219a4cf47900a0b000000000001319085016681579abf2c4e14041389ea336b470e40000c8100004fcc3e893f5100829f1025062418240d88a358a2b00002b0029305811394000000001741f986e58000069919ee0000000000000001e4c0000fde0000000000018f6000010b890695260000578c000000000000000d4587ca0000068400002b609f608140001043198c31c000012ae230a6b384a900000000569c000091138ce467c49b000000000000088947500004a0c00009761bc60000d3f000000002a1cc87991d0b70242103f94f7000019e0b7d181e00007e3400014f100a60000000145c0f9c00000001c0b000000000000000000000003690bb700142bb85480000000033683ca000000000000ba8800035ea33bc21d00000000346c23f94c93aae00008640a5b36141c6000016470f1633f400f800025822e5800910ef1426000000011600000790c000052a0000822c9d3855000006838000105a00003758e04800000007a0424594c6311274c8000019d000041f07f680000000335479098b23aee3c100001bf71ae800000000000000000008ea8ab91744000000006b927c05470862997a3f881b2c00000000840000000000000000000000010c7000072b46a980000000552800000001a92000000000001e880000000056400000000ae70a2c000001080001676087c65f000000003a6000008a1056b049a1d48edc98770fdc5db07eb1bfb269c6d0c024950e00002d5cd4d06cc07fa79604cf11df0fc40a68c279ce323ea19cc00000002eb4058476107d31732454c4819de2037e515c00003bb3af458041b30000346c00000000000200a43fc0000000000000000d999da0000000000008a00548000020c000012b073c8ca30776060015bc0001bfd2ca24ae0000000000000000000136d3ada666c47600001d6a0a5c0bd80001aa26d783248ae813481b90c3617f73de802447c4861a380219709bb0c0a1ae681e0b8d99de18883c70000000022e41618f44073c1c2c1378afb12fe09840b841da9241000000000000000144200000001ad5000000007ad0adb2fb80000000181617aa00006cc13c138e6106497c1bbd09580400000161003380e280001f4523fa00000000000000015d0a541c8b09e638f801c000019dc567874d023d07f20000ba09eae000000007df919831b805d89df8000075200000000000000000007650f1d0000000000016b7000000000000000024c0000f43800014a275f475fa03216ee73483a293ed219834f80000000000036d469211e70000000092d00cc0000156c0001340000000000001c250000448c0000000394c0000e7a9ec100005b5ceda97da00006764105835a0ef200008f1
  | 66 => 0x91740000000000000f9a2d640000909098100000000b9886a611941b1800007ac1bee7f3c46f16cc2ff21c8c27d196a3a440000000000000003c080000000000022383e300000000000000000001b3471146518a0a1a8c34048d700001ffe11e83e180001c2277f8cd0047c2b06664400000000fa4270c9c6863821ec7c140001ead0e28071c00019382b220000fae98e834b24b2064400000000000000000002e9662384520ed0000000004a703960f3631a4e21800032742494e6480000000328000000000000000000000000fde80d8000031700007eb000013041cc43d7c000000021d2352c0001810303e00007bb12d300006374d559fba139862b8294209b2a466a5105293780d4a4090e738b751ee21914d6e9e3923ca428cc3a866519324ae4b649b4b00005c9003696e72730686091082ca30da13a45bb123b40d400000001fb90000000000005ac0dc06ed47fa003c0000000075800000e4e645c00001861f44000000007a040cc0000620005a00005b4c00012682806000051414a021945e100478bec11ba06a40000000108a0000000087b1c100000000000000000000000209d000081cc48600000000000097491000000000000015731a261070dc3000020cc0000000032c3722338c1cf0000115c0000000000000000000193000000005790000000015bc00007d7834e0000000000000000000171ca9a14ae2dd200006cb08933dc63040000000000000000fcb000007f60000a4399c21af2000004296a72ef600000000000004a1bec00015e141501388000000014f42ff85ae9d18000000008500b5e2fd60000000000000006aec00000000000000000014ac000067a46819bae00000ffc3ce00000000000000000001ada00000000000000000000000000000006ac0000000000000000000bbb2d9c000080f0492000000000000f94000013e40000000227078788239ec52d9426f05ac8199000058ecf52a0b3042a574c27f943a047825a46af000010a817104a103b302603274a190f513c9a41b072405b7356c503cf9500000dd622c848380001eda0000ac9800011b60000a1511ab0000000000000003c320000000000000007af009d80000000791c0001d7b30e6000000007d71cee3c9c9ff8c9b0000487000000003554000086e00001b963eb504c9f7d03a80aa0b0b108a315e0c2803886f801f0010ca268f3d3e3c0af064ba05e1e501d28000000000002fcc00006fe3abe3d2c00000003e5e1b0437992f30000000000000003e4003b47bd000003265fbca1f800005c44cb8b35000013c400000e304640dda00000000000000000000000000136a000000000933f4405900de80000000750800000000000214872c93dc3f34000048f0635000000004058000000017340000000000000000000a84000000000000000000
  | 67 => 0x1400001e40000404c00d44f3146304f05e0898e874308807938d038d0b387c11e0aa80797051000006e016131ad00000f9e179813c07e24ff8871e28d818340001fe0000000000000052091e00000001b673eb2213d01a989d129469242e1a02519660000726883907c01bc48ba83c700007b4c84e00000a6800001060840000035844a31bfc000073cc10d0715225c0b94efe103438f24114e479b690d840000000091d000000000000000000000002c0051003e435a80000d75000059700001a3900000000000079a00007ef09a780000b540544000000000007a9cdaa9df700007b6400000000aa6230cc978ffe00003d908729fe832e6000000016cd00008210f8603540436478c000000000000000770800027f474a8000000000000000dc9903b000004a003a10ad05b800001870422000000000000b6010301e740001a0900003db8000000028925a08be18ba800000000000110724307bb012a00000fb85f182708fda0b7e0c6012f8227045455002211d01000045e4000000022aa7cc4000179c00007cc0d11000000007494000000000000000000000000005f24dca933c000037b4ac09ef7000025ec5729b0800002b84da0800019884f6400006b600007da80000000000047c903b00000000000000000001ec400000001c971cfa60c008d84f60000150cb6f1f671f2c268c00002c4030631acc218000000060ac5ec0c9f00002fd02e280000000512ca9e9a9819720240000172f00005a000000ef436000000000000000000000398800000000000fd00000091838c400000001562000000000003df069480000000000059a41d70626132000000000000000000000001933000000007028eed0000000000002c800000000000000000000000000000022080000f8c9fab0f5a7e9013b80002c540000000000000007610b2b8f8000000000000000009ea0e3035685ca39b2150411b8000163c67f80000000370200008d000000f8234a021b8d1c23004074a321a4d0000000013d0c9421600000000000033b8000000000003188620483c15af0000000000000000000552400000000fd2000082e8000000000000001a7706520000b970473000024b8000000000003fa862100001e647594b0180002c9a24185b686512e060ad00e01bf628a400003f20ef806060000ae5083c124e000000000a10000204cf0c000024203a7c00007eb000000000001b9a0bb649cc000000000005fc01ae8ee927fc424479f1e0800000000f70191622b0338000000001a2841045bd00003f301544000169c29d20f24ea00b253a78000000006bf31545ad810c0c2414a000000000cad16a60000000204123d00000000085c1b7043cc668169e2e2e57b0edf8f8a00004148000128b27d87e1c58308dc0df45b009ae1d5631a819580001a7232c83da8ce
  | 68 => 0x751037000000005a180000000000036c98c5000078f429591ca00003e643d5807031b61e58fd88a8d1b26323c72d125d2f421818af7906b196803a85f70dfc330e39e0a1080000d140ee4000197e0b50108cb7c008c00000000000000000003bad03e800000000ae0000042f029c754c0000d1f00000000b1b909000000000cbc17f80aac00000c700fd1ebc2da80000000000000000001c620000295094c000000000a500000000000000000001cd50000000000006b000002e0000000003a9000009a4014c01a4000000000000000542470a00003a3240b0a650000000000007e8171c1c201ce45e78447267e0000f021fcd307a52d000019ac0d1070d4c3f00002cc20000852831c1b8246f0000128a063a38f069e1a780000000000000000ede0001014000000002c90c77839b296000009ce800021a02d5400000000000777c00018930000000054400a306fa0000db58e41000030a4c0495b3138c42ec0001141000000000001e6e3fbe6a9c000170000000000000000000000534fdf948b000019b0367164e1764821800000000000249896306ae000075b0000000029900000f811ca92ef230f8f099a80279a596000000001a4a7b7c000194b1dee705400000000e685ca442d9d8900002ec0849000025ca40c8bb78f16258e30c8fa489963c2e5d84c028072208c143000019702c4c000000001a800005e90000098400000000b7686bd0000701469b9287055670f09b187e33c186dbc13f982300005128668870e1f464d4400003ec36e221d000012ee1fe019c417b1896000075f8ff906423e9000449a3000000006b0c00000001762000094788f91b76802000018b9039400006af8918000035040001ac725742e808c300b3000062d013b057526523b31008103e00001a48b5f8000329855142189638000000003f291c700000000922864e198a000000000000000426000005930000685c1731a270b4a000000000001acc0000e30113e0b0818747b2824900000000d74864b00007b3462685071b0e00000001fa500000000e230000332e00000001cfa174a73ac4bf062e292e263800016b4000049504e81f2c000000000000000106400000ba8000305a0ae8a960da4328800000000000000000000000000000021f495805be15002234a05834339501b6c48a084e187a6de40000742000045a000000000000546cf1080000000000000006611eac0000e358a0126ac76b8674812517300578000000032a460d4ab8125200003f14000000000007208e221dcd000057083d496f5000000000000e8101623ae4000003b0000000041e87541b6e0000e2da01a20b6169891c902b38a009ec0001b343cbc5200000000020ca4cb000014771f84000048a800002f420acf1408272fdc12b4569800028600000000000000000000bc620232b
  | 69 => 0xef600000500fca000051a09da1ab000000000ab780000000000000000000000730cf96800000004190bfe1bd300001ad015500b619da19eca880000000000000000a04359a5c9830f00000000000044c0000000000009a2949c38c80d6409789e100000000000073700000b3400000003c644380000000000004808d7f800031ac10480000000000000006d98000121e641c10f8fdc2be81978d2020ab1844000099d082f38140a98a1d834200000e985c786af3396000000001c93fa64d0ce3b80003fa200006780c95083e6ac400000000000764400010e800006cb08f31a6818580000601814936ca0000000161c00006484e4d9ae726b060d0142882800006f3070b8000212869ecd37800000000dec000000000000000daf800000000000e2f00000000000000000000cce00008da0000000000740001ad900000000000000000001a7c02a80003e000000469800000006034000000010b40000dc2052f1984000000000000000000000020033a48691400002c5180e17441b78000000000004a096352a4039cc0000eaa22ce1b500001efb1262454868280001ecc000000000002f5c00001d81ea20000321424e8000000069c4b2d0ed22d8c31040000f57000074ccbab19e13400000029212060000000000f1686369a6ad4bdd931534ba7e7c1fe00000960576089b07001b64000000011f300000000000036a140a2028a04876000002878cd70000000079b0000144c0000000009680002d1628d800002221b5848908e9000024cc3e1830b0000092a59640000000377251e000009d300002b3ccf5000034a2000023a809e152a571891e980400006db0154800000002decdce154737c8000028d8b1f0000000088b9b33000003e4000147c0e4020882828ed62ebc7c2827e96f702e0184875085592410823834e1518374076c463103b40c7e2200a2c86e814ca5154c281ae605667b610110407224c236024c12f0000065580000000000000000000000000000003ba8000000000001df95020c3e0000b041a3e000000000000d0723fc0000fbc000026c4697800002d9300e7f30d8999b6100600000001882360c26e0000000000000000669800000000000025993702f21a68f3c8ad2341e00000001f84098e00009f180990000060400007ba00003c54c6c800000000000000000000000000000000000000000cc21df600000000000000000000000095800000000000e89800023ae5e2c000000000000000000000002b4760000003491862811c5d481bb096671f0000028204de4984bdc03d02cba679c29c800000004bd854c8b8911c45f1c0000000030a38fc6bb8a403f2e000015d990b0aae4928c1c8ce10000311c00b89ad000000000000000000019349a09cb8405a670c6ec9c0806700a28e8319fd0000000064013b3352e70501
  | 70 => 0xcf300002988000000000000000000060c80002d08351000000003d7a0000000000000000000b438ffb250071c0a3d13e633c40000000000014d200000001a1b218c0000aef000000000974a91000000000000000034000007858000187b0000582430014a9204e3d7429e000008e27160000097027283a1c57b0f9f13f414603e38000000034ac000081901a0000025202d000000000000000000000000f4e80000daa63e80000000060a00000000000274838cd00983a03dc200001341ffe32d600000000bb32bf200009189106000026e80000ce62b8e423c1ed80002bc470a80001c572774476c756067a3e0c39a000004a200004101002801825a4000000013e53ed03b90c5e899b00600000000197d394e2e840001011000012005270ad700005f4c30c005137b049941b6858e000015b000019d30000523c29696721f1e000010418f000007c440000000000000000001af2035e6250000000000003ab40000e692bb200000001c4b03d80000e7f022c28e4784494c9e900b0e066ca63800038465dace83946e04fc2e9800000000000496012e01821ce21f780001488000000000000fef0950000063c8637319200005869b0f0000000093e1d350000453c2938b2f0000671400000002db4000036d000030e80000f4f0e843baa16843a98add0d36000059f0493062c6e6400018c0000019180000000296412e400000000000238c0001a3512683878d49800035f800000000eb32484767468486c0000000000000669290c304c4041286158a52e4000000033805a9800000003090000051a813400007ad40000000000076f4000036810d600005c280002ecc33ecce700001a0c0000c0711ed00000000fb7882a00000000c4c854a2f6e7f940000b8d196a3be45080118000081b8747968e3b1807bc000000040de2eb80001eea0000000000000003482000000000000000559000018fb00000ca0c508000166e3614b1f80001c58780082f000011ec6430cab8716000000000000c760d564a7c87e0000363a03f00001f85309c00fc83391692f1e699cf8d12c02bd24bbc000109b2e9a708800000002c6443dcd2d02fc2e84000061c810523225bc0000087e349c1f7c383800029d423f497212c910e265b0000064f00002fa8000000000000000ded000000000000ac7123531fe09f40001f0900000000ebf8dbe2920000006e886939c40904cf81093411e000032b9c9a3dac00001600dad304443c00450b440000000000000003a0a360c00004d5000000000eb08e719062b7c00000a240a000000000b9f168e24f836b000005202e2086a800000000000870800007846ffc4e79a833c6000002ef8000000004e0000000000006eec00000003fb657a0c5b82e831ca4e889b59cbe31c656886e7813a129a44cca74049f22123a3800005551
  | 71 => 0x15400000835000019b61ed050d0e120000532cb3880003606000101580001f4e590455f85961c5a00000000000200e52ecf680a8326144d9870181e90572309c33108fa3fb85374237840d399c00000000000165000006bd17ff00002d58a6c918c09b8000040100f325cc0000589080f20e644e4000000038ea0a30000000000001b880000000000080dc000000022e2000000000001d7a0000f25189f000000003431fb01aa800002d7800018ca802c84200000000769890a80000a4448d00000000000000000001096206678805ba163a32de794090d81dd00005db8b540644339e51d000015153c12741000001ee000000000001aa82b6213400000000000002d071b1e6215820210779102a209042d0000026e00000000000095725043ca80000a7001a208ac00000000000000079a8cc11cc60ff8280000026ee3f98f9f9d2900003800000000000000000e51105700003974a0e102e26a40000987161f3e2a80d07b00b5200000000000000000002484283000000000000a06094c00004b74000066a39186b24000000039f21cb04560e880c860000b0d9dce317c8150ef7000016ce054c0000000000015e40000110197848285a78000000000005a7162f303600004a79d1f0000022c50180003ae42de4eb0000000004b108279588076c65882eb800000004390000097428585c8c0db88143d8e0000e9f99e406fe74a00000000000019fc74a0bfa1e9e404843f80001dba0d90737194500007ac800010302fe6000009716024022000050700000000000095f9a7039626f0c00000001bf667506c080210fa0290c4a580001f2e524400006b10000000000006ef000014e06b28b1a3eae61e80000a6b0490000000000001d9200000f98000000000006890000000000006b20000000030508b10000000000000000c500000356400000002be23d182b0134b25180000996934a189000000000000000000000000000000000001928ea436344608b7500002e600000e55800000002f3449604c81db47a2800015dc20ec188888a1dd338347f140001c361d1827482dc99321f8600000000000128e0000a9d8a08000058d0df280002444430468a80003f9000002ea800000005c780000000000000008f5800015020000ee61415414e0000000000007480000ecf800026c00000000095513c60000f0800000000421c9be00002f0a1e600000000069616acc38917836b635f000000001636030cc528a0d3d4204a8d50033d196e44080000000000000000001dfb00001cec000097c32ba12049739da3104c5cdc13815122eda5724f0396e500004c7c39f10860000812c21a96a313e2391c7bb85d4323e0000000000000005ea400016a10000620c0001f4015507ee000003d83cec827c0000b9d1a6c000023c82b500000000aae0000167e0000
  | 72 => 0x4000096f00000000000096d152e0000d7e85c1369054d870d9eaf0a6400009488ab83ba856dc118907100000000865800027d040e04b1805b0a764e8427319f2016a246400093ae389c6b44784016637d44378e2e13bd00004274e139361000000000001f8f00000000000000040d000001fb0dc40000536058080001810148410b8c8e329a16905bc05ad00007948d1804ab241e6654e7280cd24c61fb400004a032c21c7c637845d40be0000e680599297a6e4000000002aaa0000e660000274a000031180003eac6c642a69bba000035146a7203301aa31f8000199f06f86d24e9787d900002dcc0000acb00000000218000008b86a04c37019607c200000000b36000029a013314ec00002d90c6380000000169c0000dda256e14f80000000000057f0000000017d020c000000000000569054f8000000000000000eba23b00000000000000000000000000000001bb8d151471000000000000e7a0000038000010d8000000005b49a4b000034e00001d2020025f64510000030a273980000b710000000000000000ee46d100000758000000004a49240000082c43be9694172e2654bce875f1c88588c0078a2e2f46570039a805f20880d3062d0a1200000000b71935b000075cc2e7800033880000e2e8000000000000001ad000000000000000000007ea84210dbc0000449066c974624c872641a299b7130c3f6c8b61c84255600004ac8f8104b20000c2f00362a3277087c998f1110800009cf97aa01ce54f82a104863d122570408189507bc286498b8fd700007450ec112ed1e8e5398e2988c51bf2000025c00001124157800016f400005d5c000055800007430ff2108d1aa4820876788200642762c21f800012a237801f2895610f81478c1f122800006d386e380000000000105103e609821ecc25892d931d60000c7e00000d9252acdbb9cf40e9a306c000000031203ea4000199600000000000185f000025000bc1e2c064e44041f198b500001f98b3796e23a9261689d5183a02064e24ba194f907ba0000000134705f42818000000000004768ffb127d07466df00001e3407421650d7400000dc6696000000003590430879b0809348e00000000000050c1df87818ec51a1c00000000c1a000027f0837181800002b1c8e88b0a00005090bea800007b406a8ec789b000ea4bd4b0502da0ba61809030980b006227a4262000027b04f50e5a862c05fa21804750fa408d24c903ca985d3bd6151c93f0397264a2f2899c09a204846830ba21de80a2600e40000000015a72fc0000000281a7cd4fa896923a2a0f500000000000000000001b8c0000430cb129c3102ac6354000000020360c0836200000000000000014e7000037d4bc68000000000008d3187c00005c10f77800000000000e368aaf000007105ad84d900002ad86d08000
  | 73 => 0x1a640000000005800003ad800000000f1a00009579a1d27f86aa45e006d3225413c00001c87365a045c00000002c227290368800000001f6c00018cc00001c44000000000000000f118d0835e67974d35878e184c35607cd800000000000997800000000bdc62a87b5022c004051e00003300000090880004130705c000040540da0000bb5034a3520000033e896200002c40f3680001ea87d187968f2412903b189d880000af6000018f98c1000000000000159216c2c3047b908c000025ccef78ef119304c3c00c840c2fba7060787800000000000460989c000068e8eef00000000000000000000000118400005e10000000044100000be400002bb0e06000000000000d6f27840ac89ab93f206dc6a74f4d9efc404e1028ddb8f851f7a7578000138035b08188946800000004f100000000080860fc557002b0fc20000f41000000000000000007a24bc00010360000000045b40140000012e1ab086c80002f5000000000000000000006ad961529360000aeb0baa1ba63a2c00000fa37bc352841f93ac2f980c80634000000003730000031a00005234bd68000000000000000000000027040000e9e000000000001e37000000000000000000000005448494162e00000000000000000000001df300001adc000170700000000d199ef117ca0001003a0a900004d9cdb318592d581334871075c29a4763504b9b9b21b400000000000182e552000000000000750498b083815d604ccc7600000000000002b800000684ab40000452041272948e11891000027b40fe80002dfa000000000000000000048b000000000000000000037a00000000078200007f1c52d182907b811b4f3395cb0ef634e418219fc203e000000009122568000000003d62e220000000000000000000cf89f633c7e000000014fa23e25aecf3286de07ce5bbc0001f1321585ca8a19824c29ec4a208c694843c1e7aa036699e0024206e00770a7725a876d8000000016a867ecd7f0a7403960000c980000000055c40550000335e56d4a10138424ac0e0078082931746389000000000000000000011452c0e2eac00000000000421422580004032764830b8fb100006b30000000018ae2b388db9b3021445420fee91a115a24a883300ccf15283e107d999b408ce533846a0000000011ec00003931daa0000ba806e700001a60000000000000000000000035d6487800000002c60000000d8b9a292c0410eb1800028ce3f005b40000002c7108303925b0000199000000001a9836acc530c6c000029ec0000000000000003ea80001b62299ca5e1c0d17b20000000000027260be45910bd428247ecc2de06a120c00c54000069518f80000000000000005de03ee9de5033c00000f5980a38247c9c72b865f0000000043800001986295c0000d8d160459f8a3f80003fa44cd
  | 74 => 0x600398000204c1d74000000000000000ed68463000011c00000000000000008280e531c5e766c936800000000df8df687af2432536c37a0cfe00004eac454800000000000000000029040000650800000005b6c000132736ec74b0a288000046a0000000000000000000000000000002998cda85e3000070ec0000000337051bc549004a02ca0000000000000000000dbd0e603ed236540001f2220380ce8fe09b103e48518463380002c3a100c00006f217042134ee3000000000000158845f000024bc32d82db15b418c074117fb000000002538000000000006df8d9d00003d0c0000000375a79c4000000000003c6cf7100000000659cf9e9dc739f828c84a81431000000002ad1edd000004706a1000007e243e04460db00d061cb43b2980600001670000142600005290000022e00006bb00000048220652cc2db00000abe0000355000000000000000000000006880ded8000000060a01ad800023d4498805f0000243428e000000000000354000009c80000267c0ea9af1000046f4000000000004b587ce80002660055c000000000007fe4000154b314867bc00005a008e80f30ab28abe019e175800000000000000000006fc00345564e550000000000000000000000000000f0000000000000000000003000d9400000003ebc0000c1b0000288c000000000000000796c2f58ec023e000005de072b318600005f780003f3a0000ad480003d1a218888f07f13e1c8204000000001947e008310000304c00000001d9c0000000014782d31db06054000196909a234b08888f1006aa000035a8000000004e4e5c99aa284e0000000000029620000000000000000000a7f800000000000074000000003174000000000000000c458eb1000000005fa80000000000000013c83b4200000001fb500006e3c00013500c50509434897b6000000002661f030000000000000000c2a42988cd09d713763f2085f01e529a66074a7a80002d343ea0fc88000109836482b9032e03ae2f481968d9b35380c6c09f8fb424e829205391ad7297e3d089d695fb3c8238745648000267675e473389bd297c00006e300002b1200000000d2700000000000000000000000000086a000000009490108245454fc0361ade287c39d83f99ec32aee0000e448c380000000000018d812dc7dd4a679b210810605c8ef000014362274b2a000000000000000000000000000a450000000023380000c5100000fd00001151144e00005c880003e0e2be8cc900000000796400000000000000000000002eca24283d0901a000067d08d200000fb42e71048106808b4000000008b40000171803487363654000091281ff410e094000017ea00004e98000159a0a7a425c3a3000000000a0c00008ff2a62000047c05ef24e46d4c63f92b600000000000000000000000000000
  | 75 => 0x5600000b781c30de7000021c8000000000000000c3500003ca2029c010000000000000c848af14110651cce480003a3c1828000110b00006260000000000000000000000032cc558428b8000362a00000000000401a0de0000038e06e0000054d9d2d3d2c3688000038f00001624000000029de2a8c064800038fa7dc4cc505fd08586f50b19939c2fa0450c72598df254a313038d1db320a81ce830403840480540446883ef07be5698c359be7122026fc429918b03306e2c785135e008e599052f88912caa24f40a90dc508ca000089090ea13164b34518207025c4652028e90fb2a168018000000022b8742cfac0f110000000056a8b5800002118e6080000ed40000c678496328244f0a78000034a0451030201e42a56435c00000821ff86e8cb588ccb0000090c75782ee17d600002b80000097c570415f00002c94488c281800000005e9847a8000000000000000000278e00008648a231d6e35c800011120ea21b40e7b03ca3d5468640df08e6000000005a68000000029e0ff49dd60000367c000131c2ec02b70d9b04e022fa35b866a183c23d266cc0001b8e3d0c6c04ad58c43226a2bf026a1f1b03b400000001c550000267012900001a760640f2f800000002bc8000148300000000000032f31840000d6a05043a7024a4f6111d02bb46c5c94e07f439d04dd00000f260cb0000000000002dec00002a5957b2b7e656444d1c190e5260bc8e000001d6400000001c8d0000000000013921d320000a9c800000000000000000000007ce8000045e000000004918000000078ac378000000007b543e212e11bbc23c802f09710384000000013d7000044943088740018e0000782800000003da4c8508d200000000dcc05a2000003a4b8c8e6f0000000030097fd009a7bb8c97205239b01e30000000021320000ace9e350fea62e80000000000000000000000139a000039209b42f6071c8e3f1f7a04683824000078f00001ef0000155e00000000000000000007d8800000000e147e2c00009f9344c73dc7ac089400005b50c3b0000000017300000c3500540b0c0000e45279600001458d40315869e826f8b6c343820d0894116600f6177000016062aa80314d83859f2d2267b0a0312a42e3400007350bc933ec63f493b8000000012380001919276a4a845079c88098c42d4c920e851cf609104c48f9000003b9411d800000007a5424f0402000078d82768f9e07aa44b02ef04581c1a5ddc0000000000021442c880000000189ca178ee000007e6c0000000000016ec000000000000000000000000f200005151e9836e8500439c15ed38980000ae81e153b6e6f70e49130b27d600000000e6c00004f18000000017be798069e96f9084a0000bf01c8009dc50583db82c61be0494c8440ccd3938000015e9e610452819c49c800028b65b
  | 76 => 0x12883391d2a076400000001f0e3f840c7800026300000f00800000000000abf848300000fa100a1ded0000000028d00001eb846b000018cb000000001a4000000001ac8f7280000d440e70000077c3c066ae4000174a195826301c101c80bb034982bc0000040c0000d490000106e2cc48a50000000073b40000a6300000000000000011386f0000000000000091800005f60000513cddf911f000000008af805d1da20000698000000000000000085f376604900000f2f000009682cc029e00002f5889b81a720fc8258f3500001af05c9c8b71b521e000588bbd122600007fccf2e1ed136ea00005458c360b3c000027b8bfd0000398400000000000000000000002d4a1e4029b000000005bc4a628ddd00002084000000000001e10000000000000000000000000002a740000df800000000c0e036900003b50000000000006d089df1688310064b05e411d913f6803c95199b026002cb045792ea00ec5748e8b8c923582815cdfa0ae31066000000019d03b34277cb558000235200005f217d1337a0000d859d5100007b00ee78000279c7308000000000002b1836f8000232800004c88701000052380000000239c32f406b1fea406244ac6ad1ac036c07ef8dc4898536800000080860300007f0c9ae8641000000002370ea81ccc00002690ed700002ca8ce88e352db8089805d80000000000000000003f9240d80000000000044ec0001a6100000000000043815fa3ef8d8c0de500000f10000000000006578f6a0f49000041a4000000000000000d0f8000000026dcb108000342678b400000003e5c00000001c68029647e40001904049623ec0001fc017da5278702147e12a64b2cf2300001dfe00009788f7f223474f488500000000000077d170900001d88ee29569252a14d4000111d168a00000001e9404d84fa8000009c3e681c4901d8ad823542d2000013c500000c44f479248000071d0eae000002d80000ed39df20f607bd8a449a15000039f8d7a0000000000000001a841fb000003e691a335041e442b1800000005254000151f0000621800000000000000000009dd067e4ee10240468242e19c80000e433ad00000d9f0ec807280000d9e07a405be000000005e21cac0000000175912ca08d884d1ac62428000000000002166604c88d800007641d4022b0050000000009dd8000054e000007b0cf51fdc80c0ad90c250000494420b8312000033240001ef23ba400000000c770000000089a0dd0192c4ee4564166b40f200008c18997000000000000000000008a000019153ee800000000000000000000000cd200000a54d278000197400001ce8223134c0000000184c000000000001fd600006f2000000000000000000001ad000000004e1000013e0000000000002f060408000000027f07a0cdfa953226404bac0001c
  | 77 => 0x231057d40848000000000004bb9466000059800000dca3c8a0000a070000000051200000cb62f3e00000001c2b00007d3853e87cb1f545f3c000057c000018f88db00001a220398000046c000000000000000229a782896e15bc000000006d500002986000000019c101b630a8bd29d9e00003480ffa8d99217e3f38dd313850c800000000072f08c00000eb394d62f1000000001a1e000040d400002032b0e000091b00000dc24ea0ac619ba02be00000000000326a000072a8bc4000053b90580000000000004e2909e3a1254cc000000017ae0000b6b0feb319c23b4c3e88492c7a00b872f89c0261037b000000000c6c51a8000033b238a7c2000000001de62c64e51806e0000000000000002de6000080580000000760c5f1800014ea00000000f4a000000000001a083b64000000007ea237e0e1c0000ff917367b2446790a42d6603705870000000017b000000d327a2778c66f800000000b540000aa51bfe0e946ab1d960cfc0000000071731a01e943bd017f0bea3ec889e97b90000540cc6519db00002c58b79000005e018ec8699bd12e50592cd7c85f810483e080b982393bd860e05ae1bdd0000000068d00001e1c293466b80000000634817612073fc4000000017c10000000063c115b09ce4f480000afe2b7c80e01e01d660e1805208d412a700000000a3680000000553400002f10000000000004500000000072613db0ada0bcc8840000262821a0e5980002dd80100d5213700c6600000001f38000023b800000001da606b08b80ecd1970000074688bf4080510c000199a00005008000003338dc000000013c027fa0000fd780000000000078688890ff61f6087c824f000011f4d1c180032c66a447559aac25345cac0000c3c1630259c6670ab309800000d628b8c2e2c106840a97010000787c4d38af502d611440000ae4257c000000000001afc17e40000fae3a0068940a5000000005af86088000000056404b5155807b24e4026d000000001fd83de800012be5f90c2d8db400000000000000000000000fb9057a00003a440001193000062ac000004c0000000020a8b8104bc0000000000032243d840e180000000101849680000000829840e80002ba800300000000367400000e80a8f21ce6ab400000000000112400010e300005384674047200007fac80505c03344324c000202000003630adc000002ce0000bca000024ec67e000007f80000339cafb80000000000000012b200002bcc2871abd37c661180000000013a4564000166600006c24ade8e5c209a000000000000000000000000000000000000000000000000000000000f007760000000036a8000052780003e8e00005d2165600000000000000000000000c96877801506bc0000134d00000000000062b1d7c0000c040ef51586000000017a223d80
  | 78 => 0x13c86d640000a3a000030801a69d0d3672074c3d906be21cc5e7814014981bd01d5cd8f9ba70c1e14cc02b00002360000061400000000000000001b917c20000fb70687000029b04319675000014dc0001a4800007aa40000000034a4018000000000000000000000013e425aca4293530340128c32a000000001164000000000000000aa180000000000000000001c7a00000000ba700000000bfb16c51bde6494df9800007c400009cb165300005b98d970000000063b8d370e93265025e48899b4a00007150e17800041347968d360000000062488d2a07e0a4600001f8065035da4b5c3c180000000000000004ef000000000000eef22ac079c9b5138b175a752894b0000000012e8000189700005f942c500bd3a7600000000ca80000339000000000000000061d00001600000019980fb1ea400000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f7815d932440051e9023b264880030f1d3654c9103563a38eca9922000c3f65dd13244001878cbba264880063da1b714c9100063bb2ee29922000c7465dc532440090f90b3b064880021fe15760c9100243e42aec19220008bf845d8324400717908bb064880463720d760c9100043e432ea192200087f87d9432440010fb0fb2864880023b61c620c9105bf62188c419220018f4865c432440239a8c6b88648800a3e219700c91008e6c31ae01922067c7476d9551440033e50039aa28800a5d21d53545100263a3b2a6a8a203ecb4769095144071968ec212a2880063da1b75cc51000cf8402eb98a2056d70505d731440cf8ecedb2e62881971d9d865cc51006c7ac3ec798a2000e5765d8f31440031ef0eb1e6288002b920963cc5100047ac3cc598a203ecb67690b314407196cec2166288003a918842cc51000cf9406ea90a2055d7050dd521440031e90cbaa42880027520d754851033e3a3b6ca90a2065c74761952144001968edba242880032d1d874485100066a3b6e690a20018f6869cd21440533ad0739a42880025d614734851000cf9400e690a2000dd2301cd21440019a8ec39a428800365dd07348510006ca3a0e690a2000d56851cd2144001aab0a39a428800355d947348510006aa328e690a2029dc5821cd2144001ba50039a428800374600734851014e6bb00e690a2029dd3601cd2144001ba6a039a4288003741407348510006e9100e690a2000dc473d8921440031ed0f3124288003351ce624851005c7b438c490a2000cd4731892144001cceca3124288003711cc62485101ccdb43c8490a203ecb4769092144001b28e72124288003a918a42485101fcdb4388490a2038cb4761092144001b28e62124288003711ce3248510014f243a6490a2000ae4864c92144001ba0e7b8242881ab1e1db654c1103363c3b0ca9822000e586518d30440033b10ea9a6088002b6219534c110006f110ee4982203fcb8769093044073970ec21260880027c21d514c110007a8a9aa2982205d9f287cc530440017a10690a60881b25ea1f75481100063c3b6ea9022000c78761d520440012f50fb2a40881ab1e1db6548110334bc438ca9022066c78761952044001970edba240880034e1d774481100065c3b0e89022000d38751d120440053e503b9a4088003740c773481100147c432e69022005978855cd20440051f50f31240880031e1d662481100dc7d438c49022000c7875189204400bad0eb29240880067a21d52481101c4dd43c84902203fcb87690920440b1a70eb21240880fa6ea1c42481101ce5c3b0849022057d38751092044001ae0ebb8a40880175c1d55148110016783b6629022056d7075cc520440035e10c90a408800b3c1d921481102aeb83aa429022000bd0834852044001dc0c490a4088003e81092148110
  | 1 => 0xb07bb484880023ba0b76909100043fc2aed212200487c855da424400147f0ab2484881028f21564909100054fc1ac92122000a9c8359242440031e90cb8c848800a3e219709091002cbc42ae12122040a3e85dda424400147b0bbb48488002a7a0f76909100054ec1eed2122000aae82dda424400195ce53b484880028fe1576909102051e42aed2122000aae821da424407f57301b2c84881028fa1b65909105ff1d406cb21220c0e3980d96424408147d0b31c84880028f61663909100045fc3ac721220008bc8758e424400147f0ab1c84881028f215639091000557c12c72122000aac8258e424400117d0e31c84880022f61c63909102051f42cc52122000a3d8598a424400147f0ab1484881028f21562909100054fc1ac52122000a9c8358a424407d5690cb8c84880feae21970909102c59c42ae1212200487e85dd942440010fb0bbb284880022f61276509100043fc2aeca12200487c855d9424400117f08bb2848800237e0d765091008c6e41aeca1220008ef825d9424407357301b2884880ea8fa1b65109100051fc3eca2122000a3d87d94424417f87ce5b2884880038b9cb65109105f71d406ca21220bde3980d94424400155f04b288488002ab20965109100049ec38ca21220bca3e86194424407547d0b31884880028f616631091000557414c62122000aad8298c424400117f0eb18848800e2f21d63109100051fc2ac6212203aa3c8558c424400155f04b188488002ab209631091001c5f438c621220008bd8718c424400117b0fb1084880038bd9762109100071632ec42122000aad87d88424400195b0fb1084880038b9d7621091000716baec4212203aa3e85988424400147b0b31084882eeaba0a62109100045fc3ac42122000a3f8558842440754790ab108488002a7e0d62109100054e41ac421220baaae861884244001c5eca31084880038b194621091000557c38c42122000aad871884244001c5cea31084880038b5d462109105cf53408c421220b8ea5811884244173d4ce23108488003a95c462109105cf52188c421220b8eaa801884244173d530031084882e3aa9c0621091000754b80c42122000eab501884244171d50a031084880021fe1576cc9100243e42aed9922000c3e74d97324400187ecaba664880030f19574cc910006573a6c59922000cae7418b32440051f10cb8664880031e19570cc9100243f42eed192200087d85dda324400717d09bb464880022f613768c91001c5f424ed19220008bd849da32440010ff0abb464880121f215768c91000c7a432e319220028f8865c2324400b2f10ab8464880121fa17764c9100043ec2eec99220038be849d9324400117b093b264880021fe15764c9100243e42aec99220008bf845d9324400717908bb2648800237e0d764c91000477c12ec9922000
  | 2 => 0x37258d1000656c26e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c9634400195f08392c6880032b2107258d1000672188e4b1a2000ce472dc5634400187ce9b28c6880030f9d06518d100061fb2ae831a2000c3c655d063440011bf0eb18c688002a72116318d1000566412c631a20118dc835d0634402393906ba0c6880022f2097418d100064eba68631a20008bf845c8634400717908b90c6880029760f6594d1033e3d386cb29a20028f8865c253440018f6cab84a6880021fe157654d100045fc22eca9a20038bc845d953440011df04bb2a6880023b2097654d1001c5f420eca9a20008bd841d953440230fd0fb2aa6881ab1d1c76554d1033e3c386caa9a20018f686dc553440018eecbb8aa68800a3ea1b7054d100043fc2aed21a200487c855da43440051f10cb8486880121fa177650d100043ec2eeca1a200087f855d943440090f90abb286880022fe117650d100046fc1aeca1a20008ef825d943440011d904bb286880462f21d6450d1008d4e41ac8a1a2000aac8259143440031ed0db8a86880031d1977150d100061f3a6cbb122000c3e74197624400187ecaba6c4880030f19574d891001c5fc3ae9b122000caf825d3624400195ae8216c4880121fe1d75989100063dc02eb3122000c78805d662440011f30fa84c4880031e5d7509891033c3e436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab1220c1c7b70195624400187ecbba2c4880030f19774589100062fb2ee6b122000c5c65dcd62440018beca39ac4880031719473589100243f43eeab1220038be87dd1624400187eebba2c4880030f1d7745891001c5f416e8b1220038bc82dd1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d07358910006563a6e4b122000ccc73dc962440019a8e7b8ac4880031e1d7705891000477c3ac43122000aac84588624400159906b10c4880022fe11731891001c5e422e631220018ed879c862440015cb02210c4880073c5c7501891001c5f424ed29220008bd849da52440018f0a03b4a4880029b60b65949103563b38ecb2922067c7a70d9652440031e90cb8ca4880031dd9571949100147c432e12922000c7b655c2524400717d093b2a4880022f61276549100043fc2aeca9220008bf845d9524400717908bb2a48800237e0d765491008c6e41aeca9220008fb805d952440090f90a3b2a4880063e20076549100043f43ecaa922000c3c74d9552440cf8f0e1b2aa4880030fd9774549102061e32ee8a9220028fa86dc152440158f0cbb82a4880121fa1776909100043ec2eed21220118de83dda42440011b
  | 3 => 0x690a4000c9c64dcd21480018beca39a42900031719473485200064fb20e690a4000c9c641cd21480539a8c239a42900e32b1d84248520437163288490a4000d8c7310921480019a8e7b0a42900031e19770485203653d436cb9024044c7a76d972048089cd6c5b2e40900131e9d865c81201f65d3b6c99024000e3865d932048007974ec32640900038e19464c81200573432ca59024001ae88654b2048015cd0caa9640900e2aea1a42c81203871c32c85902403eaba8610b20480dfc70ca21640900031e19571c81200061eba4a9b2a2000a7980953654400117f08b9eca8800e2f21173d95100045fc22e5b2a20038bc845cb65440d54f301ba6ca880030f5d074d951033d3d400e9b2a206aa79801d365440cf4eb03b9eca881aa9e60373d95100051fc22e7b2a2000a3c845cf654400147d0839eca880028f61073d95100062eb98e7b2a206aa79801cf654400147d09b96ca880028f61372d95103553cc06e5b2a2000c7a709cb654400147f08b96ca880028f21172d951000636b90e5b2a2067a75811cb65440d54f300396ca880021fa1c42d95100043ec3885b2a20038be84dc9654400117b09b92ca8830b1ddd771595100243f42ce5b22200087d859cb64440010fd0fb2ac8880021fa1c65591100062fb2ee6b222000c5c65dcd64440018beca39ac8880031719473591100064e320e6b222000c6f65dc964440018d8cbb92c8880031bd94725911000636328e4b222000cac641c964440090fd0fbaac8880030f10b75591100062fbaee6b222000c5c75dcd644400193885b9ac88800317dd473591100062e3a8e6b222000c9f741cd644402393d0839ac8880032795073591100064e210e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000cae84dc964440018deea392c8880031b1d4725911000657ba0e4b222000ccf731c96444001998e6392c8880032be107259110006572a0e4b222000caf431c964440010ff0abb2a88800237e0d765511008c6e41aecaa220008ef825d954440011d904bb2a88800e1fa1f655511033e3c386caaa220048bc87591544400153906b22a888002ab20964551100147d436e0aa2200487e859cb63440010fb0b396c6880022fe1172d8d1001c5e422e5b1a20008bf845ca634400717908b94c6880021fa1f6558d100061e3a6cab1a200087e871956344001878e832ac6880030fd977458d100061e32ee8b1a2000c6f65dc963440018d8cbb92c6880031bd947258d1000636328e4b1a200487e87dd5634400717d0fba2c6880030fdd77458d100061e3aee8b1a20008be82dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a20038be84dc9634400117b09b92c6880031bdd77258d10006363aee4b1a2000caf74dc96344001958e9b92c6880032ba1
  | 4 => 0x248001b50e03a2a4900fb2b1db64549201c6563b0c8a924000e2c6519152480014d90caa2a4900131b1d95454920026363b2a6a924041ce876dc1524800317f0eb2484900028fe1564909202051e42ac92124003aac829da424808147d0db2c84902ab0f9db65909200045fc3acb2124070abb80596424818987cec32c84900022f61e63909202051f42cc72124000a3d8598e424800117f0eb1c84900028fe1563909202051e42ac72124000ab78158e424807f56902b1c84901038b19652909201f556432a5212403ecb870d9142480018f0cbb8284900032ed9370509201d51f436ca21240b0c3e76d94424800147f0fb2884900028f61f65109205861f396ca2124000e2e72d94424800117f0eb28849031eabe09651092037d5dc02ca21240c6a3e86194424818b87cec32884903138bd8865109200045ec3cc6212403aa3e8598c424800147b0b318849028aab60a63109200045fc3ac62124000a3f8558c42480754790ab188490002ade0563109201cd5a40ac621240c3aae869484248075c58cb29084900e2ab21952109201d71632aa42124038ba880548424800187ce9b2e64900e22f21974cc9200061fb2ae99924000c3c655d3324807d17f0fb2664900022f61f64cc9201c6573b08599240a7e2c6510b3248071b54e021664900031e19570cc9200061e3a6ca9924000c7471d95324807117d0dba264900030fd97744c9200061e32ee899240008be87d91324807d1790fb2264900032d1c7644c9200066a38ec69924000cd47118d32480018eecbb8a64900031d197714c9200065bb26e29924000cb464dc532480018f0cbb8264900ae1f219750c9200061e322ea192400087f87d9432480130fb0fb2864900030f9d7640c9200061ebaec819240a3cae761083248001a5aea21064902838b194420c9203663c380cbb0a40018f8805d761480010fd0fb2ac2900030f1d365585200043f438cab0a4000c3c74195614800187ecbba2c2900030f19774585200045f43ec8b0a4000c3f75d916148001878ebb22c2900022fa1c64585200061fba8c8b0a4000c3c75191614817595ee4322c29000317d9773585200062e32ee6b0a4000c9f64dcd6148001938c9b9ac29000317d9473585200062e328e6b0a4000c9f641cd6148001938c839ac29000335184735852001c5f426eca8a40008bd84dd951480050fd0fb2aa2900121fa1776505200043ec2eeca0a40028be87d9141480010ff0abb662900121f21576cc5200045fc22ed98a40038bc845db31480090fd0bbb262900021f617764c52001c5f426ec98a40008bd84dd9314817795cec216429022b8b19442c85200061e3a6ca90a40388be86dd1214800187ecbba242900030f19774485201cc5f43ec890a403e8bc87d9121480018becbb9a42900031719773485200064fb26e
  | 5 => 0x22f61c31d91200051f42863b224000a3d850c7644800155d0418ec890002ab60831d91201f55d40063b224000ab9800c7644807d17d0f10ec8900022f61e21d91201f55d40043b224000c3c64dd564480010fd0fb2ac8900021fa1c655912064637b90cab22400487e87dd5644800187885baac8900030fdd774591200061e3aee8b224000c6c75dc964480018f0ebb82c8902c30f9db65191200045ec3cca32240c3a3e85994644800117f0eb28c89031eabe0965191206351f430ca32240c5c3e761946448189c5b04328c8903138b880651912062716100ca32240c4e38201946448189c7420328c8900028fa1661191200051ec2cc2322400087f855d9544800117f08bb2a8900023be0976551200047dc02ecaa2400387e87d95544800917d0fb22a890002b360831d8d200056cc0063b1a4000c3e74d96634800187ce832cc6900030fd957498d200061e32ae931a4000c3e75d92634800187aebb24c6900030f9d46498d200061eba8c931a40a2cad7219263480010fd0fb2ac6900030f1d36558d200063a38ecab1a400087e871956348001878e832ac6900031d1c46558d200061fb2ee8b1a4000c3c65dd1634800117d0fb22c6900030fdd76458d200061e3aec8b1a4000cb471d91634800117d0e322c6900030fdd46458d200061e3a8c8b1a4000cb47119163480018eecbb8ac6900031d1977158d200065bb26e2b1a4000cb464dc563480090fd0fbaac69000e2fa1f7458d200061fbaee8b1a4000c3c75dd1634800187eea3a2c6900030f1d47458d200147b43ee2b1a4000c7775dc563480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac6900031e1d77058d200046fc3ac631a4000ad48158c634800117f08bb4a69000e2f2117694d200052ec1ecb29a4000e1f53d92534800717d09bb2a6900022f6137654d200043fc2aeca9a40008bf845d9534800717908bb2a6900023de057654d200147a40aeca9a40008fb805d953480230fd0fb2aa6900021fe157690d200243e42aed21a400487e85dd943480010fb0bbb286900021fe157650d200243e42aeca1a40008bf845d943480011ef02bb2869000a3d2057650d2008c5f43ec8a1a40018ee86dc943480018d8cbb9286900025b6147250d2000636328e4a1a4000caf641c94348001c5ea5b24a4900038b197649492061e573b0c92924000e2c651925248001878e9b2aa4901131e1c365549201c45f436e8a924000c3f65dd15248081878cbba2a4900ea2fa1f64549201f45e43ec8a92403ecb870d9152480158f0cbb82a4900032ed9370549200065c326e0a924004c6c76dd55248089ad0e1baaa4901131b1db6554920206563b6e8a92403acac761d15
  | 6 => 0x6d57416e8b2640008ee829d954c80070f90eb2aa9900122fa1f64553200063cb2ee0aa640389ac825d263c807117904ba4c79000a3da1f7158f200046fc3ac631e40118fb865c253c800717d09bb2a7900022f6137654f200047bc0aeca9e40028f4815d953c80230f90eb2aa7900031e5977054f200047bc0aeca1e40028f4815d943c80090fd0a3b287900021f6147650f2008c5f43ec8a1e4011a9e83d9143c80031db0c39287900025b6147250f2000657b20e4a1e4004a6f8259652c80018f2cab84a5900129be196594b20225b442ae12964071c6f76dd552c8089ad0e1baaa5900036a1c37454b2066657bb0e8a964000da8701d152c80a7ad0e0aa2a5901375a1c15354b201f556412c9216400a978855c242c8197c76a0b2c85900fa2fa1e6390b201745ec3cc72164000ab78158e42c807f56902b1c85901028fa146390b200051ec28c7216403eaad8694a42c8081c5ccb29485902c3ca1425290b201f5d4402a52164070b38855c242c818755d05b28859032b8ed416510b2001c5f43cc621640008bd8798c42c800156f02b1885900e6ad2056310b201d51f428c62164000a3d8518c42c814755d0431885900e2ab61a5210b201d71732ca421640aaf285094842c818f55f0ca9085900e2ea2015210b2051656bb0859964031ad48158e32c80152f10ab8465900a6b5205630cb201c656bb0841964000d2d7510832c807195aec21643900a73518473487205d657bb08490e4000d8c7310921c800187ae92a6ca900022fe1173d952001c5e422e7b2a4000a3e84987654800147b0930eca900030f5d074d95200051fc22e7b2a4000a3c845cf65480018bae639eca900021fa1c42d952004c3ec3885b2a4000a3e849c7654800147b0938eca901129ea0071d95200053cc00e3b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4000a6e820c765480014db0418eca901129ea0031d95200053cc0063b2a4000a3e84887654800147b0910eca901129ea0021d95200061e32ee8b2a40038be87dd1654800187eebba2ca900030fdd4745952064e37baee4b2a4000cac74dc96548001976e9b82ca900032e1d370595200053cc04c832a4000a3e84984654800147b09308ca900029e60261195200061ebaea9b224000aad82d5364480015730120ec8903178b60865d912062f1c100cbb2240c5e3a10197644800147d0b30ec8900028f61661d91200061eba8ebb224000a9e831d7644800153b063aec890002aba0875d91201f556c10ebb22403eaad82dcf644800117d0fa9ec8900022f61f53d91201f45f43ea5b2240008bd87d4b644800155d0438ec8900faab60871d91201f55d400e3b224000ab9801c7644807d5750128ec890002ae60251d91200045f438a3b2240008bd87147644800117d0e18ec89
  | 7 => 0xae82d9154cc0018f2cbb82a9980463b61c4298b300061e3a4cab166000c3c7459562cc00187ccbba2c5980030f5977458b3001c5f43ee8b166000cad82dd162cc0231dd0fa12c5980032bdd04258b300045fc22ed29660038bc845da52cc0014df04b2ca5980022fe117654b3001c5e422eca966000c3c7459552cc09b8f0e0b2aa5981030f9977454b300061eb2ee8a966000c5f7654d52cc09bab0e0a9aa59802b1e9977054b300063cb2ee0a966040a3e85d9242cc00147b0bb248598002aba0b7690b302051f42ced2166000a3d859da42cc00195ce4bb485981028fa147690b300051ec28ed2166000aae821da42cc08147f0cb2c85980faa761a5390b302070f32ca72166040e1e6554e42cc00117f08bb28598002aba0b6510b3000556c16ca216600093d8799442cc19f47b0d32885980ea8fe196510b300051fc3aca2166000a3d8759442cc16387ce4b2885980038b9c96510b301c54ec34a6216603ae1e6594c42cc075c3ccaa9885980038b9966210b3000716b2cc42166000aaf8798842cc00155b0f31085980038b9d66210b3000716bacc42166000e8e7398842cc001d1ae731085980038b9956210b3000716b2ac42166000aaf8758842cc00195f0eb1085980038b9d56210b3000716baac42166000c3c7459532cc0018e8e2b2a65980030f997744cb300061eb2ee89966000c7665dc532cc0018eacbb8a659800e2fa1372587300045ec26e4b0e601187c85dd951cc0050f90eb2aa39800317dd953547300145e43ac8a0e60028ed8798b21cc00117f08bb2439800e2f211764873018c6fc1aec90e60018dc835d921cc001878e8b2a4398047171cd65487300061f32ee890e6000c3d65dd121cc0018bccbb9a4398003175977348730006563a4c490e6011ccc7398921cc0051d90eb1243980032b1d1624873008e6639ac490e60008bf845cb654c00717908b96ca9833b17dd7735953001c5f426e4b2a60008bd84dc9654c0011df04bb2a8980023b20976551300047bc0aecaa260028f4815d9544c0011f700bb2a89800e1fa1f65551300245f43ec8aa260038bf875d3624c0015d30010ec4980023be1d62189300057240ac431260008bf845c4624c00717908b88c4980022fe11769493001c5e422ed2926000a6d82d96524c00717d093b2a4980022f612765493026eac382a6a92600087f855da424c0090f90abb48498002aba0b76909300051fc2aed2126040a3c855da424c00155d043b484980faa721953909300045ec24eca126000aaf82594424c00155904b2884980e2a721953109300067238ec49926000ce471189324c0031f501396c2980022fe1172d853001c5e422e5b0a6000ce4611c9614c00717d093b242980022f612764853008c6e418ec90a60018de86dcd214c0012bb0a39a42980029e60251597206
  | 8 => 0xabb484a80032b9ca76909500051fc2aed212a000aae821da425400155b0fb1084a80032b61f621095069f173aec4212a000e2d75d88425400155f0e31084a834b8b9d4621095000716ba8c4212a0d2eab501884254189c5ca031084a83138b140621095062754280c4212a00087f855da325400717d093b264a80022f612764c9500147b40cec992a0008f5819d932540230f90b3b064a80061f219750c9500045fc22e5b0aa0038bc845cb615400717d093b242a80022f612764855008c6f41cec90aa0008dd839d9215400717908b9ecaa000e2f21172d954000636328e4b2a80d1c3f75dd1655000195d09b92caa00032b613725954000637ba8e4b2a8000caf741c9655000195f08392caa00032b210725954000637280e4b2a8000c6c501c965500019d0e5b82caa00032b10a72d8d4000656212e5b1a8000a9d840c763500015b30018ec6a000237e1d6318d4000c5e432e929a80118f8865c253500031790cbaa86a00026b2097550d400049ec28e4a1a8000c6d75d4b625000155b09a96c4a0002ba60021d894000477c3ac43128000a6c8558862501a155f08b10c4a00e22f21d54189400261f3aaa83128000aac82550625000155b09a90c4a00038b553521894000556c20a431280008df835c462500231b906b88c4a0002ab612211894000574c00423128000a6d82d965250007179083b2a4a00062fa1b745494001c9e43aa8a928000c3c7655152500a7a70e0aa2a4a000e3ea1b705494000c5f436eb21280008bf87596425000155904b2c84a00222f61f62909403d557436c52128000cad7318a42501a1d54e031484a0003aa189709094008c5e424ed99280018bc865d332500010ff0abb464a00121f215768c94000c5f436e91928000caf7418a32500051ed033b264a00023d606764c94001c5e420ec99280018be86dd132500019c8e3b1264a00032bdd0624c94000672388c499280018bc865d032500231f10cb8064a000a2f21172d854000c5e432e998a80118de839d921500011bb073b242a000e2f210764854000c5f436e890a80008bf845cb65cc00717908b96cb980461fa1e54597300061fba4a8b2e60038be84dc965cc00117b09b92cb980029e60251597300061fba4e8b2e6000a7b805d165cc00147d09b92cb980028f613725973000637b94e4b2e6000a3f845c965cc00147908b92cb980029ee0172597300043f43884b2e600087d8710965cc09b4f50138acb980029e60271597300051f420e2b2e6000a3d841c565cc00147d0910acb980028f612215973026d3d40042b2e6000a798008565cc00187884baec9980032be1272d9330006572a4e5b266011caf439cb64cc02395a87396c9980032b21172d93300243f428e4b26600087d851c964cc0230f90eb2aa9981371e1c165553300245f43ec8aa66000a
  | 9 => 0x65109210054e41aca2124200abb80594424847157100b288490b73279db63109210070f3aec62124200e1d75d8c42485b993ce5b188490803a39cb63109210045ec3cc6212429fa9e8398c424840117f0eb188490a9aabe0963109210055bc0ac6212423aa3e8518c424840147b0a3188490a92a7a1863109216de4f3b0c62124200e1e8518c4248401c3b0a3188490803879d463109210070eba8c621242dae8d8218c42485b793ce43188490803a39c8631092100747a90c62124200e8c5218c42485b5d1c423188490b6ba308463109216d74a108c621242dae971018c42484731790cba664908472718d74cc9211fc5fc3ec999242008bd87d93324840193ce9b1e6490803275d363cc92108e6a31ae39924200e8c6390a324853f95cec2146490803a318c428c92108d6641ced192429fcae761923248401d1ec831c6490803a3190638c92108f27428c71924211e4d8518e32485b3d8e2031c64908e62fa1b744c9210045f43ec8992423f8bc87d91324847f968e3b22649080327dd3634c9210064e3a6c69924231cd471d8d324840193ee831a6490803271d0634c92114e6a388c6992423fcac769093248473958ec2126490803a318c424c9211ced2388849924200cb764dc53248401968c9b8a64908033518f714c921006563b6e89924200cac761d13248401b48e23a264908ff2b1db644c9211ce563b0c89924231ccc76dcd3248463b88e3b9a64908c7331db634c92108e663b0c69924200e8c6418d324845b9c8edb8a64908030f191750c92108e2e31aea1924200c3e75d90324840187aebb206490803179d7630c9210062ebaec6192422d8f58798f21484535ad0731e4290803a5d9063c85210074a320c790a4200e568518f2148401cab0a31e42908a7b160863c852114e6b390c790a4229ec67218f214847356d0d2164290803a518e42c85211fd5b4308590a4200e946310b2148401d88c7196429080ab921932c85210076231a6590a4200cd4635c321484031e902b9ec0908fe2f21b74581210045f43ec8b024200c3f75d916048401878ebb22c0908022fa1c64581210061fba8c8b024200c3c7519160485b195ee4322c09080327d9373581210064e326e6b024200c9f641cd6048401938c839ac09080237a1f63581210062fbaec6b024200c5c75d8d604840193ee9b1ac090803271d363581210046f438c6b024200c5f7518d60484018b8ea31ac09080327dd063581210064e3a0c6b0242d7ccf7218d60484070fd0b396c8a80032b19072591500045fc22e5b1aa0038bc845cb63541ad8baebb1cc6a800237e1d6318d500045fc22e431aa0038bc845c863540010fb0bbb286a800e2fe1d74d895000536c2885b12a000cad7410b62540011df0eb10c4a83569be15621895000556422c4312a0d4aeb8058862540010ff
  | 10 => 0x31a4200e1d75190634853fd1ae4320c690a7fa38846418d214ff46108c831a429fe9421190634853fd2e20320c690802a7a126018d210054ec24c031a4211c5f759d4634840153d093a8c690802a76127518d2108d2ec3cea31a4200e1e849d46348401c3b093a8c690847935ca7518d210072a10cea31a4200e57109d463484234bf0eba8c69080317e1d7518d2108f26b92ea31a4200e54215d463484238bee0ba8c69080395c417518d210070faa4a831a4200acf82550634840159904aa0c690802a7a135218d210054ec26a431a4229ad681d4863484015ab03a90c6908a6b5a074218d210056ac0e8431a4200a5e8510863484014bb0a210c6908a6b5a067018d210056ac0ce031a4200c5d755c063484535ad03280c690802b56065018d2108c6f438a031a42008dd87140634840153d08280c690802a76105018d2100567410a031a4200acd8214063484535ad02280c690802b56045018d210052f42e8031a4200a5d85d00634840159d05200c690802b360a4018d2114d6b40c8031a4200ad58190063484535ad02200c690802b56044018d210054f4244031a4200a9d8488063484535ad03100c690802b56062018d2114d6b4084031a42008bf845da534840717908bb4a6908463720d7694d210070fa9ec929a4211ccc639ca53484051d90cb94a69080e2fa137654d210045ec26eca9a42008bf845d9534840717908bb2a69080237e0d7654d210047bc0aeca9a42008fb805d953484031f100bb2a6908461f21d6554d2126d3c402caa9a42048de87d8d53484094bd0a31aa6908463720d7690d2100657b24e521a4211ccc639ca43484051d90cb9486908473318d7290d210045fc22eca1a42008df835d943484011df04bb286908023de057650d2108c5f43ec8a1a42038de87d8d4348401c5ea5b24a49080393d4b639492100727a90c729242e0ec42118e52484018f0e1b2aa4908e62fa1b74549211d45f43ec8a92423f8bc87d915248401970e1b22a49080327dd363549210064e3a6c6a924200cd870d8d524840193ee831aa490803271d0635492114e6a388c6a9242dfec42118d52484019b0e031aa4908033518f71549210065db26e0a924200cb864dc152484019b6c7b82a4908033618f70549210145fc3ac92124200a9f83592424840153906b2484908022fe1d65909210054fc1acb2124200a9c83596424840157700b2c84908faae20165909216f64f3b6c721242008bd8798e424840117f0eb1c8490802ade0563909212051f428c72124200a3d8518e42485b593cec31c849080387a1463909210070ec28c721242dbe8d8218e42485b7d284231c8490b6fa5c4063909211fe5a38ec8a124200e8c4218d42484539a8e231a84908033518f71509211cd56c16ca21242dde2f52d94424840117f0eb288490802a7e0d
  | 11 => 0x4840156b02386c8908022fa1c50d91210045ec38a1b224200a9e83143644840153b06286c890802aba0850d912100556c10a1b22423fab681143644840156b02286c8908feada0630d91210055ac0c61b2242008be870c3644840117b0e186c8908fe2fa1e20d91210045ec3c41b22423fab6810836448401938c9b9ac8908032719073591210064fba6e6b224200c9c42dcd644840193ee839ac8908032710873591210066639ee4b224200cd473dc5644840117b0f328c890802a7a0e65191210054ec1cca32242e2aad82994644840117f0eb28c890802a7e0d65191210054e41aca3224200abb80594644840157100b28c890802a7a0e60191210054ec1cc032242118de83dd954484011bb07bb2a8908022fe1176551210046fc1aecaa242118dc835d954484011f700bb2a8908063e20176551210245f43ec8aa242028ee86dc9544840195ec8392a890803175d753d8d210054f426a7b1a4200a9d84d4f63484010ff0ab86c6908121f21570d8d210054f42061b1a4200a9d840c3634840153d0932ec690802a761265d8d210054fc22cbb1a4200a9c8459763484015b700b2ec690802b620165d8d210054f424c1b1a4200a9d8498363484018baea3aec690802a7a1075d8d210054ec20ebb1a4200e1f54953634840153d09a96c690802a761352d8d210052f42885b1a4200a5d8510b634840153d09386c690802a761270d8d210052fc2ae1b1a4200a5c855c363484635ad02386c690802b560470d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d2100567410a1b1a4200acd8214363484635ad02286c690802b560450d8d210052f42e81b1a4200a5d85d03634840153d09106c690802a761220d8d2118d6b40841b1a4211c9c635d2634840193ce9b1cc690803275d36398d210045f43ec8b1a42008be87191634854d95ee4322c69080e2fa1f7458d210064fba6e6b1a4200c9c74dcd6348401958e9b92c6908032ddd37158d210065a3a6e2b1a4200c3e75d90634840187aebb20c6908030f9d46418d210061eba8c831a42008df8758c634840153f08b18c690802a72116318d2108c6e41aea31a4211c5c835d463484238be60ba8c6908031dc417518d2108c6e41ae831a4200c5d75d4c634840153d09a98c690802a76135318d210056ac0c6031a4200c5e769d463484018bcecba8c6908023761e6518d210054f424ca31a4200a9d8499463485bf59b05328c69080237e1d6518d210054fc22ca31a4200a9c8459463484015b700b28c690802b62016518d2152e4f3b6c831a4200e1e75d906348401c3aebb20c690a87a35cb6418d2150f4a10ec831a42a1e9710d9063484011bb0f320c690b6aa7a126418d210046fc3ac831a42e1acf8259063485b753d0c320c690a93279d86418d210070f3a8c8
  | 12 => 0x802ab209651093100556c3ec42126200cad87d88424c401c5cebb1084988038b5d7621093100557c38c42126200aad87188424c401c5cea31084988038b5d4621093100747398c42126200e8d73188424c5b5d4ce23108498803a95c462109316d747188c421262dae8c31188424c5b5d48623108498b67b10c4628c931006563a6c49926200cac74189324c4019c8c5b8a6498847550c5750c931007523108598a62018f6819cb604c40117f08b96c09880e2f21172d813100c7d43ee0b2e4200c7a85dc165c84090fd0bb82c9908021f61770593210047dc02ecaa642018f8805d954c84070f90eb2aa99094e9e20165553210245f43ec8aa642028ed861c954c840195ec8392a9908e62f2097498f210243f42ee0b1e420087d85dc163c84011bf0eb18c79080a3b61a7294f2101c5f426eca9e42008bd84dd953c84011f700bb2a7908063e2017654f2108c3e43acaa9e424da788059553c84018eacbb8aa79080a3b61a7290f2100477414eca1e420487e851d943c84010fb0a3b287908462fa1f6450f2108d4f41ec8a1e4244a788059652c84018eacab8ca5908feab2096490b210055dc02cb216423eab88059642c847f17d0f31c85908ba2f61e6390b212051f428c72164200a3d8518e42c847355904b288590802aee016510b211c55c402ca216429faae82d8c42c840717d0f31885908022f61e6310b211d51f428c62164200a3d8518c42c847f95aed2146590a97e10c6428cb211ce56bb0851964239da67110a32c8549f086221465908ff691c6424cb2153657bb0849964239da47110932c8401b48e3ba265908032bdd8744cb21006d2388e89964231dc471dcd32c84053cd0fb8a659080339ddb714cb2118c7bc3ac798e42319d78758f31c8463b8ce739663908d63de1972cc72116cf2c3c6598e4231dc6738cb31c84633cf0e9966390803350c773583210045fc22e7b2a42038bc845cf654840717d0fba2ca9080327dd373595210064e3a6e6b2a4200c9f741cd6548401938e839aca9084717a1473595210066b880e6b2a42e3c6f75dc965484019a8e7b8aca908063ea1f70595210065dba6e0b2a4200cb874dc165484019b6e7b82ca90803361cf70595210063dba8e0b2a4200cbb741c16548401970e8382ca9080336dcc70595210066c398e0b2a4200c3d75d5364484010ff0ab86c8908121f21570d91210054f41ccbb224200a9d83997644840153f06b2ec890802a720d65d91210055dc02cbb224200ab880597644840153d07306c890802a760e60d91211fd56c16ebb224200c3d751d7644840147d0a39ec8908028f61473d91211fd56c10e7b2242008be87d4f644840117b0fa9ec8908fe2fa1f52d91210045ec3ea5b224200a3f855c364484014790ab86c890802aba0870d91211fd56c10e1b22423fab6811c364
  | 13 => 0x49ec28e4a1a8200c9c631c943504015cb02106c4a08023be1d621894172d57c22c43128200acc8358862504731790eaa0c4a08130f9d554189410055641286312820087f855c062504090f90ab80c4a0802ab612201894100572c084031282008df835da52504231b906bb4a4a08123b61c629494102537428c529282018fa809d952504011f3013b2a4a080a2fa1b745494101c9e43aa8a928293d387055152504091dd0fb12a4a08033a1c3625494100657ba0c4a928200e2d5418952504019d0e0312a4a080a2fa1b75909410045fc3acb2128200aac82596425043317b0fb1484a0a3eaba1b629094100657ba8c52128200cad7518a42505cbd4ce231484a0803a918971909410145e432e99928200cad7418b325040517d0dba464a080327dd0638c9410145f436e899282038f686dc532504238b8c6ba864a080a2f219740c94108e4e31ae81928200c5d75d8c32504018daebb1064a08031b5d4620c94108c7a432e21928204c3e75553605040317908b96c0a08022fe1172d973101c5e422e5b2e62038be84dc965cc40117b09b92cb988029d60650597310243f428e4b26620087d851c964cc4090fd0bb82c9988021f617705933100477c12ecaa662008ec825d954cc4011f700bb2a9988063e20176553310245f43ec8aa6620087f855c262cc4090f90ab84c59880e2fa1f7458b310065bba6e2b166200cb474dc562cc40117f08bb4a59880e2f2117694b310045fc22eca9662038bc845d952cc4011f700bb2a5988063e2017654b310063c382caa966200c7565dc552cc40155d05bb485989028fa147690b310051ec28ed2166200aae821da42cc40117f08bb28598802abe096510b3100556412ca21662038be84dc960cc40117b09b92c1988022fe1172d953101c5e422e5b2a62e4c5f75dcd654c40717d09b92ca988022f61372595310043fc2ae1b22620487c855c3644c401958c8392c8988032ba13725913100657ba0e4b226200ccf731c9644c40195f08392c898803391cb715913100477c12ecaa262008ec825d9544c4011ef02bb2a8988023ee01765513100c7c402ecaa262048be87d91544c40717f0eba6c4988032be0974d893100536c2885b126200cad7410b624c40155d09106c498802b960420d893100477c3ac43126200aac84588624c5b359f06b10c4988029b61442189310043fc2ae0312620487c855c0624c40117f08b80c49880e2f2117018931005574244031262008bf845da524c40717908bb4a4988123b61c629493102537428c529262038be849d9524c40117b093b2a4988063ea0276549310047cc04eca9262048ee87d89524c401958e9b12a4988033a1c36254931006563a0c4a926200ce870189524c40155d05bb484988032b9ca769093100557410ed21262008bd849d9424c40155f04b288498
  | 14 => 0xe83841650c8014bb07082ca190030f10975d90320243f42ee0b20640087d85dc1640c8011f700bb2a8190063e201765503208c3e43acaaa064048be87d91540c8018dacbb92a8190023b618725503200636b28e4aa06400caf641c9540c8018bacab9ca4190030f1d165548320063c382caa906440c3e65dd1520c80187acbba2a41902b1e99770548320063cb2ee0a906411c5e73596420c82393ce6b24841900317595739083215557416ed2106440a3e851da420c80147b0a3b484190caaba0876908320064fbb4e72106400e1d659ce420c801c3acab9c84190ba2f61e639083200716212caa10640093d87994420c80147b0d3288419282ab209651083274f16292ca210643aa3f86594420c80147f0eb2884190028f61d651083274f17c12ca2106400e2c82594420c801c5ce4b2884190038b88565108320071610aca2106440c3e659c8420c80187acb390841904793cc9658c8320046ec3cc71906400e2d6510a320c801878e8b2a64190031d1c5654c8320061f32ee89906400c3d65dd1320c80195eed21264190032bdd8424c83200716b2884990649fda471109320c8018eccbb8a64190031d597714c8320062fbb4ca9906400d5471995320c8018beecb2a6419003551c5654c8320064fbb6e89906400c9f761d1320c8639a8e3312641900333dda524c832746e238ca49906400ccf76549320c9cfb88e2a92641900267a1e424c8320064fbb48499064a1d9471909320c80133d0e212641900327dd8424c8324feca3888499064299d687dc5320c8019aeedb8a641900335dd8714c832006cbba0e29906400d94741c5320c82399ca7bb264190032bddb744c83200657bb0e89906400ccf7654d320c8019ceedb8a641900339dd8714c832006d23a0e299064d9dc7731c5320c8238b8e732ac219047950c5655843208f6218c64b08646a87f855c364544070f90ab86c8a88022fe1172d8d5101c5e422e5b1aa26a87f855c363544011bf0eb18c6a88022fe117218d5101c5e422e431aa20287c865d6435440717f0eba6c4a88023be1d62189513543fc2ae0312a200aae821da425447f4790ca9c84a8802aba08631095100556c10c6212a239a3c8654c42544050f90cbae64a880e2fa12764c9510045ec24ec992a2048f686dc532544050f90cba864a8803175d7630c9510045fc22e5b02a2038bc845cb605440195885396caa0b9b0fdd774595410043fc2ae1b1a820487c855c3635040153b08186c6a080237e1d6318d4100566412c631a8200cac429c863504015ab03180c6a08463720d7694d4100477c12ed29a82008ec825da53504051790cba4a6a08472718d7494d410246f43ec6a9a82028bc865d5435040135904baa86a0846a7a1b6350d411154f438c6a1a8211c9e8718d435040193eea31a86a0803275d46350d4100
  | 15 => 0x9a96c29900399d4a52d85320055bc22a5b0a6400ab48454b614c8015e700a96c299002bc20152d85320053b42885b0a6400a758510b614c801c6d0a216c2990038d61442d85320075341085b0a6400ab684ccb614c80156b09996c2990029da1770d85320053ac2ee1b0a64008f687143614c8011eb0e286c299002ada1050d85320055ac20a1b0a6400ad683143614c8015ab06286c299002b9a0850d853200572c10a1b0a6400a7685d03614c8014eb0ba06c2990023d61e30d85320055b42061b0a6400ab5840c3614c80156d09106c299002ad61220d85320047b43841b0a642d8f587083614c801968c3ba2c2990022fa1f64585320045f438c8b0a64008f587994614c80156d09328c299002ad61265185320056ac1cca30a6400ae582994614c8011ef0eb28c299002ade1165185320055a422ca30a6400ad783594614c8015e700b28c299002bc20165185320065b3b6c830a6400ea572d90614c801d64e1b20c299003ac5c364185320047ac3cc830a6400ab684990614c8015ab07320c2990023de1d64185320056bc1ac830a6400ae782590614c80156d0c320c2990032d9d864185321fd5b410c830a6439ab482190614c801d4ae4320c299003ac9c0641853200758b80c830a6400ab686908614c94bd2ec7210c299002ada1842185325274bb188430a64a6ea762108614c801d48c9990c299003a5d9232185320074a3246430a6400ab684980614c80156b09300c299002b560e60185325175510085b026400c7975d43604c85d1790dba2c0990022fa1f64581320061fbaec8b026400c3c75d91604c801968e3b22c0990022fa1c64581320061fba8c8b026400c3c75191604c801968e2322c0990032dd9371581320065a326e2b0264008f687d85604c8018eeebb0ac0990031d1d761581320065bba6c2b026400cb474d85604c8011ed0e30ac0990031ddd461581320063a3a8c2b026400cb774185604c801968e830ac0990461fa1e54594320061fba4a8b286400a7a80945650c8014f30128aca190029761a31594320061fba4e8b286400a6c825d1650c8014f700ba2ca190029e20174594320043f43884b28640087d87109650c8014f50138aca190029e602715943208d2e41ae2b286400a3e841c5650c80147b0838aca190028fa1221594320051ec2442b286411a5e83085650c8014bb0610aca190029ea0021594320053cc0042b286400a3e841c1650c80147b08382ca1904697a0c705943215d2ec18e0b286400a6e821c1650c8574db04382ca190029da0470594320053ac08e0b28640087e87d01650c8010fb0fa02ca190029ba0a405943200536c1480b286400a76818c1650c8014eb03182ca190028fa1220594320051ec2440b286411a5e83081650c8014bb06102ca190029da0420594320053ac0840b286411a5
  | 16 => 0x5d913200556c10ebb2264008be87d4f644c80117b0fa9ec8990022fa1f52d91320045ec3ea5b226400aae821c7644c80155b0438ec899002aea0071d91320055cc00e3b226400aba80947644c8015730128ec8990022fa1c51d91320045ec38a3b2264008be870c7644c85d17b0e18ec8990028fa1431d91320051ec2863b226400aae820c7644c8015750018ec899002ae60031d91320045ec3c43b226400aba80087644c8015730010ec899002ab60b70d91320051fc2ae1b226400a3c855c3644c80117d0e286c8990022f61c50d91320054f418a1b226400a9d83143644c80155d04286c899002ab60850d91320055b408a1b226400ab581143644c80156d03186c899002ad60630d91320045f43861b22642e8bd870c3644c80117b0f106c899002ada0420d91320055ac0841b226400cb464dc5644c8051ed0fb8ac8990032ddd371591320065a216e2b226400cb7741c5644c8019aee638ac89900339dc871591320045ec3cca3226400ab681994644c80156b03328c8990022fe1d65191320055bc0aca3226400ab481594644c80157700b28c899002ae20165191320055d400c23226400ab980184644c80155b05300c899002ada0660191320055ac0cc032264028f681dd9544c8011eb03bb2a8990022fe11765513200477c12ecaa264008f7815d9544c8051e902bb2a8990023ee01765513200c7c402ecaa264048be87d91544c801c3ea7b24a6990031bd977254d3200656326e4a9a6400cac641c9534c80195ec83928699003391847250d3200717a96c92926400c7870d95524c80117d0dba2a4990032d18774549321d45f43ec8a9264408bc87d91524c801970e1b22a49900317d9773549320066a308e6a926400cbb64dc1524c801970c9b82a4990033c187705493208c5fc3ac92126400ab781592424c87f56902b2484990022fe1d65909320055bc0acb212643fab481596424c80157700b2c84990faae20165909320064fb20e6a126400cd4611cd424c80117f0eb28849929eabe0965109320055bc0aca2126439ab481594424c80157700b2884990e2ae201651093253d57434a421264abea461948424c8755590ca9084992a3a91855210932515d4402a421264368bc865d3324c801968c2ba66499002a7a1a428c9320054f4308519264008fb805d7614c8031f100baec2990031d5d751d85320055b424cbb0a6400ab584997614c80156f08b2ec299002ad21165d853200579c02cbb0a6400af080597614c80156d0d216c299002ada1842d85320055b424c1b0a6400ab584983614c80156d093aec299002ad61275d853200579c02ebb0a6400af0805d7614c8018eaea3aec2990038dd5254d85320055b426a7b0a6400ab584d4f614c801caea729ec299002ada1372d85320055ac26e5b0a6400ab684d4b614c80156b0
  | 17 => 0x90843a9ad82dc552108713750fb82a42132f2eddb70548426569d32ee0a908400d3965dc15210801b54c5b82a4213af2edd870548426369dba8e0a9084c7dab721c1521080156d03304c999002ad606609933208c5f43ea8b266400c3f75d5164cc82353d07aa2c9990121fa1770593320043ec2ee0b266400ab68198164cc80156b03302c9990030fdd6755933208d4f41ceab266400a9d839d564cc80155f04baac9990da2fa1f53593320045ec3ea6b266411e1e53d4d64cc80156f02b92c999002ad20572593320045f43ea4b2664008bd87d4964cc80155f04b8ac999002aea0251593320055cc04a2b2664008be8714564cc80117b0e28ac9990022fa1e21593320055d40042b266400ab98008564cc80147d0bb82c9990028f617705933200557414e0b266400aad829c164cc80156d03382c999002ad60670593320045f438a0b2664008bd8714164cc82353d06282c999002a760c505933200557410a0b266400aad8214164cc80156d02282c999002ad60450593320055b40c60b266400ab5818c164cc80117d0f102c999002ada0420593320055ac0840b2664118bc8759154cc80195ac8392a999046a720d6450f3200717a92c92966400c787059552cc80117b0dba2a5991022fa1d6454b321d45e43ac8a966400cb87059152cc801974c9b82a5990032e5937054b320045ec3ecb216643eaba80d9642cc80157301b2c8599003275937350b320045ec3eca2166438aba80d9442cc80157301b2885993ab8bd496510b3200c7d406eab0e64008f980dd561cc8018f2e1286cb190021fe1570d92320243e42ae1b2464028f6819d9548c8011eb033b2a9190063ea0276552320047cc04ecaa4640387c87595548c8091790eb22a9190032b5907250e320062eb2ae7294641187e87d95528c8018f0e1b2aa5190eaab61a5210a321d71732ca421464a0aaf86548428c94775100a908519003275da74cca320064ebb2e9994640487e87dd5608c80187eeb212c1191030f1d642582320061fba884b04643ac3c75109608c8018f2e1286ca9900e2fa1f7459532006563a6e4b2a64028f687dc5654c80196ee9b8aca990032d1d371595320065bba0e2b2a6400cb4741c5654c8019aee638aca990063ea1f70595320065dba6e0b2a6400cb874dc1654c8019e6e3b82ca990033c1c770595320063dba8e0b2a6400cbb741c1654c801970e8382ca990033cdc4705953200678388e0b2a6400c3d75d53644c80153b07aa6c899002ab60b54d91320043fc2ae1b22640487c855c3644c80156d0332ec899002ad60665d91320055bc0acbb226400ab481597644c80157700b2ec899002ae20165d91320055d400c3b226400ab980187644c80156d03306c899002ad60660d91320061eba8ebb226400a9e831d7644c80153b063aec899002aba087
  | 18 => 0x959a5b0b396cb213bb4b99672d964277696284e5b2c8400a3d869436590801a5ce5286cb210034e5c250d964200597416cab2c844093e859cb639080127b0b396c7210034ba1672d8e4200696c2ce5b1c840093f855c363908812790ab86c721002aba0b6598e422045fc3acb31c8440c3e75596639080153f06b2cc721002e3a0b6398e420054ec3ec731c8400c9d87d8e639080153b0bb1cc721002a7a0b6398e4200747416c731c8400b8e82d8d6390801a5cc4ba8c7211030f9d56518e420068ebacc631c84008bf8758c639080133f0eb18c721003475d56318e42006973ace431c8400d2d759c8639080195ecb390c7210032b5967218e42006c731ce431c8400d8d639c8639087d37501bb4a7210026e6037694e42004d7414ed29c84009ae821da539088133b0f31ca721003279da6394e422058f42cc729c8400cae62dd9539080135d053b2a7210fe6da067654e42004dac0ceca9c843e9ba809d95390801373013b2a7210026ba087654e420061e3b2caa9c8400c9e7698d5390801c3acb31aa7211026721d6354e422068fb9ca6a9c8440c3e76596529086d17f0cb9ca5211022f2197394a425869d282e1294843ac3c65dd9529080727d0fb2aa5210030fddb6554a4200597416caa948400d3870d95529087587eeca9aa5212c74e1c15354a421d61fbb4a4a948440d2f72949529087d3750fb82a52132b2eddb7054a426965dbb0e0a9484edd3b751c1529087f17b0fb2ec321003279cf63d864200557416cab0c843f8bc875956190881878eab2ac3211024fa1473586420049ec28e6b0c84329ae821cd619087f1790eb1ac3210fa2f61f65d82420064f39ec7b04844093e87dd5609080187cc5baac1210034b98b75582422061e3aecab04843e8bc875956090881878eab2ac121002aba0b63582421f45e43ac6b048400c797094365509d98deebb92caa10063ea1f70595420065dba6e0b2a8400cb842dc165508018f6ea382caa10032edd0705954200675b90e0b2a8400a9d840c7635080159b0418ec6a10021fe1570d8d420243e42ae1b1a84008df8758c63508015a902b18c6a10031e1c365549420061fb2ee8a928440c3c65dd1525080917f0eb2c84a1002aee0165909421f55c402cb21284008fb805d761508031f100baec2a10033518473585420047bc0ae7b0284028f4815cf60508018f2eba86c0a10026be097194c42004d6412e3298843ad1f7394d531080135b0db92a6210032b61b7254c427569732ee4a988400d2d65dc9531080135f0c392a6210026b6187254c4274e97428e4a9884e9d2e651c95310801a5aca392a6210034b9407254c4274e96280e4a9884008bf865ce52108071790cb9ca4210ea6b20971948425569d282e12908440c3f7654d521095ba70e0a9aa4211030fdda52548421d697b94a4a
  | 19 => 0x32ed9370585520065c326e0b0aa4008f7815cf60548051e902b9ec0a90029e61740d815237f1d428c9b02a400e398519360548a78f4ecaa6c0a9002aea1263d81520055cc24c7b02a400abb8458f605480157108b1ec0a9002bce0563d81520057840ac7b02a44dc7a7654f60548834f50d296c0a91131e9da52d815205735b14a5b02a400aba8498760548015730930ec0a9002aee1161d81520055c422c3b02a400adb8358760548015b106b0ec0a902a9ea1474d81520053cc28e9b02a400aba849cf60548015730939ec0a9002bce0573d81520057840ae7b02a400a79851cf60548154f50a216c0a90029e61442d81520053cc2ee3b02a4008fa870c760548011f30e18ec0a902a9ea1431d81520053cc2863b02a400aba840c760548015730818ec0a9002baa0831d815200574c1063b02a400aba8488760548015730910ec0a90023ea1c21d815220c7cc3843b02a4438bc86dd16054801970c1ba2c0a90022fa1f64581520045f438c8b02a4f1caf7219160548e1974edb20c0a90038ee1764181527871c42ec8302a4f0e3b53d9060549e1d52e5b20c0a93c38e14b64181520075938ec8302a400eb171d9060548011f30f320c0a90029e61664181526955d424c8302a4008fb8759060549df5d704b20c0a91fa9ea14641815275d5d430c8302a46fcba761906054999c750a320c0a90038e61464181526671da98c8302a4ccea9721906054999d56a4320c0a93338e148641815266754290c8302a400eb2711906054801d62e2320c0a90029e21954181520071db22a8302a400e386455060548011f30f318c0a9002aea1263181520055cc24c6302a4008fb8758c605480157708b18c0a9002ae211631815200579c0ac6302a400af08158c60548ed4f50a318c0a90038ed9153181520071c322a6302a400e5b6354c6054801c76c9290c0a90038e192521815238f35b14a4302a4008f98798460548014f30b308c0a9002aea1261181520055cc24c2302a4008fb87584605480157708b08c0a9002ae21161181520056dc1ac2302a400ad88358460548018f2e1286cb2110e2f61b7255242564d743ee4aa4840393d85dc154908238bcc6ba8c72100237e1d6318e420062ebaac631c84118de839da539082393cc6ba4a7210030f5977454e420246e43ac6a9c8440c3e75596439086517f0eb1c87210da2fe197290e42004dbc0aeaa1c843f9b4815d5439080137700baa87210fa6e2017550e421554f43cc6a1c8411c9e8798d439080193eeb31a8721003275d66350e421745ec36e4a1c844093e85dc1439080127b0bb8287210030f5957494a42234d6412e9294840387e87d9552908018f0e1b2aa5212a70fdd95454a425969c382a8a94840487e87dd5609080187ee9baac1210030fdd075582420261e3aaa8b0484eed2e859cb659
  | 20 => 0x3fc3aea3128600c3f845d46250c0187908ba8c4a18030f10d751894300636412ea3128600c3f415d46250c018f700ba8c4a18031e20175189430061fa02ea3128600c3d75dd06250c0187aeb218c4a1802aba0a431894300636baea43128600aad84d486250c0155b09108c4a1802ab610211894300574c004231286008fb805d76150c031f100baec2a18031d5d751d854300672308e4b0a860487f875d76050c0187884baec0a18031ee0175d81430063c402ebb028600cac429cb6050c0195884b96c0a18031e5d750d81431d4d7416e8b1ca400d2f52dd1639480717d0fba2c7290ea2fa0b7458e520061fa96e8b1ca400c3c50dd1639480187ee9282c72900237e1d6318e5208c76c34e521ca40496e859ca43948015750130ec8a9002ae60261d91520055b408c1b22a400ab581183645480193ee739ec8a90028f61473d915220556c10e7b22a440aad82dc7645480117d0e18ec8a90022f61c31d91522051f42863b22a400a3d850c7645480155d0418ec8a9002ab60831d91520055d40063b22a400ab9800c7645488117d0f10ec8a90022f61e21d91520055d40043b22a400ab980087645480147f0ab86c8a910e8f21570d915200557410e1b22a440aad821c3645480156d02386c8a9002ad60470d91520055b40c61b22a400ab5818c3645480117d0e186c8a90022f61c30d91522045f43c41b22a4008bd87883645480156d02106c8a9002ad60420d91520065c326e0b22a486aad82984645480157501308c8a9002ae60261191520055b408c0322a400ab5811806454887878edb22a8a90031e183735515200734306e4aa2a44087e861c954548018f0c0392a8a90eb4bdd0725515200734300e4aa2a400a5d850c7635480159b0418ec6a90032e9c36498d520065d380c931aa400cbb645c26354801970c8b84c6a90022fa1f6458d520065a38ec8b1aa400cb870d91635480117d0e322c6a929f2bdc86458d520065a388c8b1aa400cb870191635480196ec9b8ac6a90032d1937158d520065db26e0b1aa400cb864dc163548011bf0eb18c6a9002b52056318d520063c306e8a9aa43387e861c953548018f0c0392a6a90023ee017690d5200c7c402ed21aa400c78605d6435488187cebb2486a90030f5d76490d520249fc3aa921aa403a3c86552435480187cecaa486a92d38e1815490d5200657b24e521aa400d2d549ca43548019d0c139486a90463b2197290d5200674302e521aa4018fa80dd943548011f301bb286a90031e1817550d5208d4f41ec8a1aa400c78605d25254881c5ec5b24a4a90eb8bd8864949520049fc22e7292a400c78605ce525480117d0fb22c2a90032e1c364585520045f438c8b0aa400cb870191615480193ec9b9ac2a90032719373585520064fb20e6b0aa400c9c641cd61548019a8c239ac2a90
  | 21 => 0x804c00000a000801001a001002800800200600080040000000048000002001000000801000300080140020000000004002008002000c00a0040070038000001000802400400900300000040000008008000000000000000000000000000000000038000000004000800c00800000400080060080000000006003000800001a0170000008000002004800400a006000000000000000300140020000000028006000001801c002001005800c002000000800000200b000000800200000000080000000010000004000001800000000a0008010008000001801000001e0010000026006000800400400100180080000050010008006003000800c0000030000000006000000800400001500000040160030008000000003001001000c006000000c000003002800800000b00000040000020008038002002006801c0060040000000002000000803400000500000140080000028000002002003800000000000080040000030018000004006000001801c004000800000400000000000020010010000000006003800c00200300000100000000261eba4a1b1aa8008df8758c635500195885390c6aa002b960420d895400477c3ac4312a8eeaaf8458862550015d100b10c4aa0032710d73189540047bc0ae6312a8028f4815cc625500155b09100c4aa002b960420189546973428040312a800cac429cb61550011ef02b9ec0aa00a3d20573d815400674300e4b02a800d1f53dd16294c0717d0fba2c52980e2fa1372586530045ec26e4b0ca6038be84dc96094c0117b09b92c1298032b190725915301c5fc3ae9b12a600a6d8510b6254c0195ae8216c4a98023be1d621895300556422c4312a6008bf845cb6154c0717908b96c2a98022fe1172d815301c5e422e5b02a600a7985d036054c0195884392cb2193e2f61b73552430261f3aaa9314860087f855c26290c090f90ab84c521802ab6122098a4300572c08413148600ae5810816290c0195884392c3218130f1d554582437962fbaee6b2a8600cae84dc96550c0195b09b92caa18032bdd0725954300637428e4b2a8600caf841c96550c0195886392caa18032bd04725954300636280e4b2a8600caf401c96550c051ed0fb8acaa180339dcb715954300672396e2b2a8600cb442dc56550c019cee438acaa1803391c8715954300c7d43ee0b2a8600ceb72dc16550c019d0e5b82caa18033cdc770595430067838ee0b2a8600c7a85dc16550c0197085b82caa18033adc8705954300674390e0b2a8600cf3711c16550c019e0e2382caa18031b1ca50595433563a38ca0b2a8600c3f65dd15350c0917f0eb2c86a1802ab2096590d4300636baea5b128600aad84d4b6250c015d30010ec4a18023be1d62189430057240ac4312863ac3c749d46250c011f700ba8c4a18063e2017518943024
  | 22 => 0x2007000000000c000002801c00000100180000060000000004006008000000400000200000040020000000034000001000800400a0000008000010001000800000c00b0008000002000000000c002001003800400a0000038008000000007800400200c001004400600000e00000000040040024010009001001c012000000800800400a005000000000000280000040040028004000004000000000c004005800000800900080100020210008000006001001800800800600280000000020000004000004001000c000000002800000a009006802400000000080000020000020014004000001000000e001000800400000000080000080010000020000000000801c0000000008000000000000000002c001002800000200f0010000008005003000401000300600000160060088000002000000000400000300200080000000058000018002000000000000200000080100050000034004000000006005000e0018008002000000002c0080080000004000002000800001600200380040200040000008000001003000000000600000000020000000004002007002000000000300080000000010008000000000001001400600300380000000030008020018003000000000000000080000060030018000000007001800800600500c80040000040000000008000007800000400000680000000000000024004003002000800a003000000001000300180000000000000000000002002804400000100000100040000008008000002000003c0000080010020000001003001000000000200000000000008014006008006800c004000000000800800d004800c00000c000000000400000000040020030018000004001001804c00200300b002800400700280000000000008008002001004000002600300b8010006004000001800000000080540000000008000002007004000c0060000010008002005000803800000000a800000a00000100080020000000024000002000001c0400000000000002002000802401a00000480000020040078030000000000001c000004002000000000000580080160030018010006001001800400a00e00580000000000000000000011000800c00a0040018008000005000000c00400900180180020000000010002002000800c000003007000400000000580040000000000000018006003001001c00000080000000010000020000002000000000000f001000800a00000000040000020028010000001001000001c000001003800000000400040020000038008002003001000000e00200100000000040000004016002000801401c0010008004010000000002c00c002001000400000000c0000000010000000000c00000000000080000010004004006000001000000000080080000040030020012000
  | 23 => 0x614c9e11257923d8000000395800000000017d00009183281a51b186c28891f002bd56082639b0000b4e0000002d2c0000000dc2bac00000000000003160000de84c4178a0f3b7800164e0000e48c4892279a2671ca40000000001a6416a4ab3d800000000000000000000000000000000021b0000dd8000000000005c0000000000910000a1d00000005c2ae33399e9d05c71100001b060402900027e136a00000018dc0000001611cf531682045b80000000000000d3000000000000000000000000000ad60001bf2028a9400000016a96122b5000028c0001e825e18e40006ce000000000000000000000000001060e181de6a64350a594c00000000000b3a6aa1d6ace8196000000078d6889850000000b76bab31621a53a04701c60234000000011004006c53c19587b41621290d5a0c85b43d40fc13b054a06a4d918e800035157e036860c5661b013fc05441800026380009ec52705651f23d95210facc7a809000064d1d6000000011d50c1370c7000000000000016095ba3810000050000000047ad1d39831524a9f041c8a303df9ee9766b2f1fb8f8cad2000007800000034800000000000003cd80000003095a18000fd839b22180002280003681a7c0000000000ef800059300004b45b866313d0000f9e3275109a7951e03a03086fd76e000360895461e3ef00000000002f64b20000000839000000000071700003f80000000000d3c5967560171fdd540b46280126cc4e6804718268aba4eb40e9d2173a49e0bc8b440007682408f080000004fd9be46b013302c26e053400042b0001162000565800000029711d99282fa5803261df515200017a00015225ef18a29b8f140000001fb4ae60001260000000000000113800000016a800155673b00000012cc18f343a7195007e63d28188d8800010f9a51082000000227c17a000000000072400033080000000002538bf06480000000000000000149135800036b0002ad03b80000000f1d4101a814095e80000000000000bb00ce57a24916460000ae000017c0000000000000b0100007fce44b904b681648489f336e8a14f2a64915487440000002a7800142c0000001324a5e2175832380000000203a16800052c0000000a4261b0fa00000009134a7a5d8000000000800e000000801c0000000000008006000001001c00000b0000000002005004800400200100080140020050000000014004000001c000000000001c01400c008000000c001000000c00200000080040120060000004004001002800000601500000040040010008000000026000000c0000010050004012003002000000e003000000c002008000000c00200a000800000c00600000000000090020000000002000001800c0080000014000000001801800e002001000c01c001006800400c009000800
  | 24 => 0x11a58d50aba307911cdca000000000096a0005c2136c3e000000027ac0001c2000000127c8115768000000000000000082e6b5000000163e000000258952e43700025f4bd6000390800063c0005bc2ca0a8a00000d0000fba48e35705f89a00fc0ec0000000a885651ffc0000004750000bac55c27488a000000000000000008ca00027080000df0e297f96a00002d2187c0008d738e0000a6e0000002738000aa80e580000002130000ce000000000013bc0007fb32581cd09e5093d8a068000000000174c2aa4f50869344b5eb4927e0454b9c0004a0ad70e6291c0001c98ca6000000000056e00019d800063200000008852a82ea000000055ab800001181578a5c53da9b02a02af0e706889ecbaa00012d00004d300024c137465000000000000000000fa41940001d30000aca7be50200000003c30000000302bb10af1704c760b017480000000004bd854ce1665a5158000000b2a0000fe800000013180000005420000ac418400000000010e20000000e080005f80dd2c2176a9e527380008100001728de0000ad724d0590ccc00018e00000000004fd04ec9740dc00000c000000000011a96d600024e81f14ee330000000000006f0000000aac5430001c6567600003820f80000002361860ae000811ea4a40009750001eb8ab6a1100000002b00005c185b40000004f180000000000000000e8ca002ed00000000000000000000000013088000000055600000000003219e400006a239703cc0000000002c2c34c4d70000acd4860e80002214cae7f9356816c46e5b91da000014000000025b02f86280000000c0600006300000000000002e4427877a0909a200000000532d2800000015900007e283f2bb22d80004f30000000d4a00000008017525635bd0908000a1f0000000036b29384800000007a0001bad4e49e2022154000000000008b40001a11a98000000000066800130e61300014e0000af700000000000002fa800000084621780000000001c2208c0001cc0002264244b6f03190e8000bad39e2e20e9a37f59681a4000000000000000000000000000000004042544bca136461000000000000010280004860d2084911800000023dc00075312f1bf85e669812300008f283c0001de424c00025ba70c0006d9126a8a8000b51000000000000000000000000000002d7804e00000002c80000904618000000000450061c1ee00014c002400056e06980001d400000006408183a92a380000004cb0001c6c00017400020a400000004218000005f30001144000000101a1f800000038380000000000002784000a3332728a400023900017b57440002000000000000199915000064d000116090488800000001549da55ea4d4e0c1ec0c529340003f857f00001bcb6e50507b8000a38000000172e3f51b800000000ac000000000
  | 25 => 0xbc6c833610808b68f4000079021871000000009fa000456000000000041819640008792b5150000028a391aa78102a9d0fb23a072a93d15a10f15e620e3b717016e044d00000000000000000000ab400033b06b44120001a2852d1b88c80e9934922a7b527098d16680001fe0e90200b8a530a50cd462830001d3890e0002d30f680007ab00015b50b2ac71662b8400002d3f5250098665c00011ac8da870598164403a266000274c98a9774f889f00005fb4849f2c30808a21c2cfc0000002c29e60000b56592000000000022625e89cc000000286c0004fe0000000000b7c0000000aa4ae71d10a8cce86bf3f98000b020002a080000007350002994f460001b396100789cf51f23ecc185780a50aecd7800000019c000000000000012a439824c19440008450002cdc2263d0162ac7853a2480002b1400064200005d475600000019880000002108000000000000222c0006142cd8158a160000001c214d43992fb91f0fc00000b989b49700002a9800023e88e00029744ec2e6409228d2fc346000133c0000000002c580002ca00000003863e10000000000000000000000083554a07a83c000000019d43064013d21be000000000000000001bc3d50000766967000196000000000029000003a53738f44000a514c499b4000226000000000000035819ac9e80004de8a08e2a00000000000008fe0fc800000000000010d95b80000428000d26000000146ce5800008180006ba0000fd20880008e43012b04000000284167cd040000000bec8b24a800000016ae0a90000000000b9e00000000964464510000c5e5920b79f7000000051d000000000000004455aa0000001a140000000000de974a00000000013080000001b6079600000000001ce0003bf000043c2d95480000d566c7468abe0e868070000ff485c00000000005b08951859f350c27f2000000157e000480a60400000024b8ed800055400015c529896500021f43ae54e4c5217435e0553d125c00008f540e12940000005572bec89445f02e80000000000198000a3263200000000000002862a312dc000000000000000023900015a8000537a9fc00000006b8f9416c0000000840b840000000fa1050000059aa1cf947c30620000000000000000000093c453999cd420324f829c11b226800011e8b6000036780000000b45132e984ba05141ea21886068349b268800009900000002382b91a481e0f980000000000ae84e44ff04396007c013f00000009795991a180000000000000000000581035121a8f055c877c00063011183980004a90001e58cd21860000af43643ee00000000003f4222000077230000000000f600030200000000ab0830000000b4c2f884e4b8c0002a40014000b6a000000174600000019540000000fd80010a89691088d68b4054b1960c7c00031119
  | 26 => 0x23593d0000000000000011e5c480002a29205822a840000002d080000000000002e6800045700000015e284044e00006c600001a8bf57043ba0950e9d01c8811371438926000000000108e000000000021eaee48d8f487ac2df00021610c80004d40f383340372de8000000b4e000143c0005dd000000144e0005bb05fc40e2ee0a20000dfa0000b28a4d14a0000002a68c8c35c0001f8c4825602f80a880000000000d1102816600000016ce56c30d2cac51819b2d422e4e546fb18283412b035225f90e41982604d4aa6c474b2043d800000094d0ca2878e0aa7826300b007200421f08cc0700243562a7c85a9bf33fa5f069c492288045c0002c3467871800000001f0000eecad200000002c400020b178870a0005ce00010080000001688f520000002e4c33c00039900000000003091a10000b310001e64c2a000000058c00004f3ba07953be3ed4f3a42ca2e2251d880014e89fc2702c742b600045a88b8b0632f2e6aa916be000008800121c0f615b25ac94600000000013d400025c800000040e2ac8460e4a9323c5a9f400098f4af0c8d3880004ff90a4e020645ae80591ba6250000cc4ec22315ca000123a3a30000f9d13c6644e28d6d67a1692ac1b5cde041d05380000000001822d34b120004581d548ba0b851d921071273f47e296105e0e200022b800085c2592a24000a141ab8d008cc4055a78f052d4a1546f01400000c345d9460b744cc1aa1ae42400130d9a2980006314a41e1c000aa71380000f8a8d3406254c38853600000000000000002c5c770b7e000280c0000000002340ee090300000012c05774488000f1001c0c4000013a5a51561e38e4800048012b44ea00043c2d8c18000050628140000000001a540000000002ae14b200000025c800013e000000003c2560002cd80000000000000000000292000000000056797d8c126b30000940e3e17001f800000000059280000005d91fb100928eb053bb800000010743302a08342640768cf80008db319a98c00014814a88bd2584c11b600003ee9a140ca5709b40001e280011b00003c68f880000002152b7d46225a05d88d41aa00000000000000000001948a88a99492aac8df82a700000000000000a4a3cc00001520995840000000eb137839039a05224280000000000f90d1c0002f480005a40762ea80004be20235b8000000000000000051016b58397700002e000018040008ab0002d6d54c2ec28e0000092a67012a7340000002df92280000000000000000968311aa8cea4a320fea6192182be00008e00000000001b802d49b6000000000000000003800000ee4b993a85f01b55ba83f566600000000012107390f48888a8c58e443979cb6200046faa945d6000000000000000000023300006785b8a6b4000ad03409cb400000000028349768171a39a9ce
  | 27 => 0xc447f547d2678edaae015d0000000b8136029d80000001401821006abe06496acad00003b38ddd6fa805000282430000000014ec000b5a3899750e6036600000000000005a98e2ccdeb220000e1d52c7df000264000027f0000c600000000001480f026e80d60859478ac626c96f80005b8000034948c00019e800018e00b0f091ec00080d00000002b4000000191000070351680014680000000854000a202ab80001040f4272a5246b21eb03f8180000a8d27c000000040300012845829f4000000000000000000015f48940002d900da00014d8000d9a0003d62a88428ac31af0000000b1126e04bd4b60000002e304ae000000231c99400000000014722f000029f924e0864e4000051a9de08c8f7c000590000000000051d12e2e6d49673441614690569d151a86613303750ea1050ed295a05d138c01c05f02600f4c1c0004958d2c0001d95b980007e61a70001654256a983c022e84b200005f800168400700000000005ae00000305de05c00f80000001ca50c068c0000000000fed11406e1af85e0d169120000000fdc000119000000070049d9d30dda000000260c0000001621cdd32a60a0db165d59260600c8000d7a0793b22e653f22de52080004029593dea3948b80d81eea58d2be1b042200000000000001ae00004ae0000000000000000253800000000010accf68ad1950000126a6935d12cc00093100009500001fe067800000000000002245081a914800000000ec3ec00010ca80b000000048642700000000003bc00000013628570000200a0200000009011cc24e4d78f4c00063615c2da029800000027bcd3691151b0000000000302836c79eb92000127c00091f0000b40e289613f124609be2c61898060b86a4700000014e624b0a68dd0bd0000186893c2580000000000f2e00007a8574e042ff00000000004e21a699e525c8000018000000267098008d47a27723fa48488a19f0000aa053c1bb47709e01f20c102a0518f9047618384d083e61647e80000004341db8cb4fb20004ec80000004732cb0000b1e5794d39dfd3369970ed8000fb60000002db4000aec0000000000000000000000000015f800028e9b91710000bb693919f8c5833891615e19740000ff204a62000026100000000001d023c04106189ab000119c000000000207906800034d199499a27b315961d40200036a97796d26e64e48d413e40920ab2540cac5a32f08b5c0000000000000000a2513622fc9629bc0001410f5a0005c7000059c00027685e80000f2000274932c00000011a4f641381ef1b780001dd51b8000000000000010c0000004151e9825048b476a79820404220f18e00004623c10a2400000000000000000001d7000000000014700015ec0001b78001366b10199106d1f038d00027b444ea8b413a69950667e19e09ccda88480
  | 28 => 0xc925193467161931628c0e0001c8154533211646aa1ccecc22a24c800000000000013e4e9400018d80000000004998000890ab70000000c2268d00000000000000001d2c3cc0003b5800000052e0000000f6e0000000944000b45135101834aa5f000266915e0000002d5464270d1050000000a9216b1e48ec03c42aa8a4551498d08e8b208a40e123080000005324ec000029c94542129c4ae49a00b609480006d336e0000ffc00017b800060600037716dd36800000011bc0005e031e2bbc4d20001cf00006e6718000276c4ca00021326701720002c580012843f92fe00004a6000000149d0fe000000000037c5b458926940005644319ef084a000000000000086f0000000000abb00000000002f500006d0be85ad4828768ebe15f000000143867a4098ec0a72747000000167c00057a8000f284b647884040fc43d37200000000002419f9c000b3c00023880000005d3a4a00001cf4ada864fec9f53719168de60460000000000000000167951c738000000005007d0000ba12707583938001424a6813929280e20570100fc80905f90000000000ae500018a80009175a00cd149e0002e290cca505fa00010c90ea2862a49d7400000000000acfd68923d00000b88196418a3146400003bd97a95a22c0000216d18867c208a6b80e4000000000119600020e00010940000001f84a9a1612560000c902291558de4d620e93a02b086da2d400000005e4a7c5420e4400062e0000f980004683450000a6a0000000000a5689341b80000000000000001632000000000014a8760f3800000043b21f800000000a000000000092f403000000000029ea3c911e91937a0000000000025000054066e2930f0000051400000013faa241582968a3c00034791dc00060d0f11d149403d538e80000000000000000b9e00034600000000d11458fc000041549b82b40008d43e2179045863f04a24b4f6c07506b06dc0000000002c4d3a800000022f46d21f11be2e3400000032f8220004b6251600000029824f200008588ef0001fbc00079c00000001c682d1ed8000dec3710338000f5000d31327009f4b2e18e8424afa0002020ffd0ee9f759c22402dc8430c68048e742d300322f894494b30596195c4a7a25521f15b681b0000ebc000000000074800094400013ec0000000572954000a6652f1dcd00251211b1e747d46be000000114878f0c89ee48e2000564037400000026a2e3c0003725d09fc513ab77574ab313826bb3389fe02169e92f30eb0f3e3cd4371b2421441000010d56386900001da87509922ccae2c00079e53a825c0000000000000e08000082800170e00032a00008bcb6600000000005e323a00000000000002c3c0007d600026f9348b9512489e49e0b031359d648c83370a29f940628aa143913d10085f1eba31952a85111f1b68
  | 29 => 0x40007d1000159d3180000001f380007841ee0960f0a96f17f0000db6a2800027550d80000f98000000000310800000000000000007fc095000110005e6a93f418780000000000000000000000000000000044b00012fea130002e80f70a8204c0e2945e6c336fac983048a80438ca4e180000001ff40000001679d7000008c5ba0d040001255bd8e395bc06600027715380000001c480000000000000000000152177c0000000359bc901e2a10000000f8e0003a4a6ec47e9cb107abf576400027700000004850000aa96b244145c2de40b440b5602bfc0008620000b24ee20c5511a81c000b9820793210426a023728b9098974283a5e112e0d90000138eae0000000000c2e5160991fc02d07f40001a7472c6c55d200000000401e529ac00047e29f00000009560001f5d180000260000000047d00000015f239c5ac00000007af1238000000000473800000067d3e90000dde33900024fcc524c25072d955260000d52060000a54000000008200001da8195b229428f8ab80005110341fe8b18455163850813863e14ca14d4880eb1e4a1a0b8e1b9247ab340006410000000b3058d59a80000000002db000000012400000000003252400b7427a00024824680000003b1000000079120680002865d031693555d46f532d80000007da04b1a900003ec1cb912cb780fa102a20c000000585115800024a42900000000000000da06c4000322a98800000000000015e000000007f156c75a450800161c000032a57524418c35780005ce6b23c4a12400000000000000000000000f1871053036887c92685ca00020ec6743bb0001cbc00084e0002d80000000339000176880204f16b00000005cf8000d12000483175c00000013a00000009aa375000000000000000000009801b2a34822036e27885c479800010e12584c40002af90c400042354080000004a43a08cb80000004811ccd24c13a2f60c20f6678c00021d00004bd00021340000000000000000b1b000083532200048800016420002ca19a029ea104649b2895e00000000000009d61de80000000005059720000000000000116628f37d241c00000000005d950a0000002ac513400000000008c600000006b8000000093a3b11c2000048848ce4000000016a4faa48d00000000e81770a00be55888da0002d84a444c7000144caf84f22a61c297605b24258000f060001c0000000087241b00005da0000000000000bac0000000fa6000000122000087a00000000001c152480000000004c9a728b38b1510c0000000ad31be8d90000a1734b800000066a29680000001670000000000000000000000000058d0a993ae00000000003bc000000158970c59a40f90882e41c0050ad0432a53100000000000b7366000119c3c829f98916a434229a0000fa80000aba48d4aead635b0000a5430a
  | 30 => 0x70f00014a55cc00000000016580002da800000000007d800000000026c03c05e200027b9f0936000044c000073e0000001124dee93a3492990bdc90f0001bb104a00012d9bc55d027d0000000000a5214e000041600007c0000b1057f58a0c69066aaf078800000075b00022c80004e80001d3ca0423c1b519dc66c29f0000000aea6400000000000000000000000000000000014ac77c09f94e88504c438f20e13dc5c900021805b69045aa008400061d09a80000000002998000cbc5033e826740009b71031fa40000005b6014c0006203b90000ba421a0b01b846027282f90000ecab961a180000002300001ba543439300024500000004ee8000000a790002c607281cd000000008a00000016cc0000000000000000ab538d0000000000000148c9127fc0000001020ba80002ab40000004aa800000000039f141413e97123a9ed0d840770002aa4340ae4000046c21000041200005c80004ab81784568164f0172d18269c25f09bc740000000000000004d0000000362494526145400009b2831744f761992b780008ca0000970000dc4000000071d6e47c600000000000002af2234bfe0000002334c200004d608748a638f0000e8513600038715f86ac00042a9dd5490ad8495294147e6d62212b380003170a0891548a0005db065d75c9f61040000d960003302aa859a00000028880003b52fe9f2400064740a8e0c0a47783f22ebd1d2189000220800037b3aa217800061900000009ba00059c822c00000000000000000000000000ea030e442000093800000000013287de00000000000000000000000000000142800000008d29b4f0c0002bd8000000b8547fadfd618450112000073a0000000cd4a4a17b0470000000000138a1ac000b0d000000000099f0001bfcf424a600022f000000000005503aa8b4428219c0006d25a40ec80000003a89a44e840000000000c3800000000000000001ec1d8c33a635171832077e74400000000006b40000000000419000020c000a0200017315b44b000007d523c0004e380000000a22868000000000000000006883a0000000000000000104862000052980000000001aa80000002040000548000000000252800000011a1e4c0002193b60ea956686d0f7839
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2a240d8976c75e80429083f36a5333008c3803000a0060d4000382c08944792ab5cf000064150347029f16321138e1e08680007c0000054d2f76b49b7502062c0c45cba0100181810430006041c485200c1190004304006981418108062550018688220175189431d40fe6175dd06250c0182d75a0a43189430050b64850dd163948e38398418373551526970add0601c95454801c29541827290d520060ee10605ce5254801ca1725c76418152007285c971190605480121d95a0b6398e4200523a4a7698d539080192a821c36554a42007285c970d90614c801ca1725c064185320048b249841c5650c801629900856510832007091c565109320c80148c925d46350d4100607614631c9435040122d9520943189410070a550701895250401c0d759cc6210931007095d571188424c401c85735c46210931004a3249849d4634840160c926127518d2100594640219d46348401651900857518d210050765e8518c42485b568691d4863109216d7211c46310932484015a1901c4744c9210040f6607499562cc00142d979966210b300060b61d7598842cc001c0d759ce6210b300050b65e6558842cc00106d981947250d2000568644701d1524814142c965d4420c9200070319473109214800141d9510873591100042b249841d9534400103d989d065d89100050b65c65d88424400142d9719462109100060b61d751884244001c25755c462109100070a5d570188424400195185600734851000474660501cd21440015c192140734851000711d947318921441738a68718a4248510007211cc6290921440013519520d214c1100057064831dcd20440d9871811d4624811014e341d88348520440019507520d214811079f481d4424852044001b80831092148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xe401d4831092148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94e
  | 6 => 0x94d
  | 7 => 0x98a
  | 8 => 0x98d
  | 9 => 0x98e
  | 10 => 0x150e
  | 11 => 0x150a
  | 12 => 0x150d
  | 13 => 0x9ca
  | 14 => 0x9cd
  | 15 => 0x9ce
  | 16 => 0x168a
  | 17 => 0x4
  | 18 => 0x168d
  | 19 => 0x168e
  | 20 => 0xa0a
  | 21 => 0xa0e
  | 22 => 0xa4a
  | 23 => 0xa4d
  | 24 => 0xb09
  | 25 => 0xb0d
  | 26 => 0xb0e
  | 27 => 0x1549
  | 28 => 0x154d
  | 29 => 0x154e
  | 30 => 0xb49
  | 31 => 0xb4d
  | 32 => 0xb4e
  | 33 => 0x16c9
  | 34 => 0x16cd
  | 35 => 0x16ce
  | 36 => 0xb89
  | 37 => 0xb8e
  | 38 => 0xbc9
  | 39 => 0xbcd
  | 40 => 0x3c9
  | 41 => 0x3ca
  | 42 => 0x3cd
  | 43 => 0x3ce
  | 44 => 0xcc9
  | 45 => 0xcca
  | 46 => 0xccd
  | 47 => 0xcce
  | 48 => 0x15c9
  | 49 => 0x15ca
  | 50 => 0x15cd
  | 51 => 0x15ce
  | 52 => 0x1709
  | 53 => 0x170a
  | 54 => 0x170d
  | 55 => 0x170e
  | 56 => 0x409
  | 57 => 0x40a
  | 58 => 0x40e
  | 59 => 0xd09
  | 60 => 0xd0a
  | 61 => 0xd0e
  | 62 => 0x1609
  | 63 => 0x160a
  | 64 => 0x160e
  | 65 => 0xd49
  | 66 => 0xd4a
  | 67 => 0xd4d
  | 68 => 0x1649
  | 69 => 0x164a
  | 70 => 0x164d
  | 71 => 0xe89
  | 72 => 0xe8a
  | 73 => 0xe8e
  | 74 => 0x1789
  | 75 => 0x178a
  | 76 => 0x178e
  | 77 => 0xec9
  | 78 => 0xeca
  | 79 => 0xecd
  | 80 => 0x17c9
  | 81 => 0x17ca
  | 82 => 0x17cd
  | 83 => 0x1049
  | 84 => 0x104a
  | 85 => 0xb0956
  | 86 => 0x16c956
  | 87 => 0x40956
  | 88 => 0x160956
  | 89 => 0x209
  | 90 => 0x8a
  | 91 => 0x1409
  | 92 => 0x128a
  | 93 => 0x249
  | 94 => 0xca
  | 95 => 0x1449
  | 96 => 0x12ca
  | 97 => 0x1849
  | 98 => 0x1489
  | 99 => 0x180a
  | 100 => 0x130a
  | 101 => 0x2c9
  | 102 => 0x14a
  | 103 => 0x14c9
  | 104 => 0x19c9
  | 105 => 0x198a
  | 106 => 0x134a
  | 107 => 0x128e
  | 108 => 0x449
  | 109 => 0x1889
  | 110 => 0x1a09
  | 111 => 0x41516
  | 112 => 0x161516
  | 113 => 0x8e
  | 114 => 0x589
  | 115 => 0x12ce
  | 116 => 0x5c9
  | 117 => 0x18c9
  | 118 => 0x1a49
  | 119 => 0xce
  | 120 => 0x138d
  | 121 => 0x124d
  | 122 => 0x8d
  | 123 => 0x128d
  | 124 => 0xcd
  | 125 => 0x12cd
  | 126 => 0x1a89
  | 127 => 0x1949
  | 128 => 0x198d
  | 129 => 0x134d
  | 130 => 0x138e
  | 131 => 0x124e
  | 132 => 0x180e
  | 133 => 0x130e
  | 134 => 0x40b16
  | 135 => 0x44a
  | 136 => 0x188a
  | 137 => 0x1a0a
  | 138 => 0x41556
  | 139 => 0x58a
  | 140 => 0x5ca
  | 141 => 0x18ca
  | 142 => 0x1a4a
  | 143 => 0x20d
  | 144 => 0x140d
  | 145 => 0x24d
  | 146 => 0x144d
  | 147 => 0x104b91
  | 148 => 0x1a8a
  | 149 => 0x194a
  | 150 => 0x19cd
  | 151 => 0x14cd
  | 152 => 0x20e
  | 153 => 0x140e
  | 154 => 0x24e
  | 155 => 0x144e
  | 156 => 0x184e
  | 157 => 0x148e
  | 158 => 0x15c3d2
  | 159 => 0x403d2
  | 160 => 0x403d6
  | 161 => 0x1603d2
  | 162 => 0x40cd1
  | 163 => 0x415d1
  | 164 => 0x415d2
  | 165 => 0x1615d2
  | 166 => 0x41712
  | 167 => 0x41716
  | 168 => 0xd4412
  | 169 => 0x1a0d
  | 170 => 0x164411
  | 171 => 0x164412
  | 172 => 0x44d
  | 173 => 0xec411
  | 174 => 0x1a4d
  | 175 => 0x5cd
  | 176 => 0x165611
  | 177 => 0xed611
  | 178 => 0x105611
  | 179 => 0x188e
  | 180 => 0x105791
  | 181 => 0x18ce
  | 182 => 0x58e
  | 183 => 0x83d2
  | 184 => 0x20411
  | 185 => 0x8412
  | 186 => 0x41411
  | 187 => 0x40211
  | 188 => 0x414d1
  | 189 => 0x134412
  | 190 => 0x14c411
  | 191 => 0x14d611
  | 192 => 0x135612
  | 193 => 0x15512
  | 194 => 0x19d4d1
  | 195 => 0x40451
  | 196 => 0x44411
  | 197 => 0x45611
  | 198 => 0x41651
  | 199 => 0x41a11
  | 200 => 0x45891
  | 201 => 0x1a1651
  | 202 => 0x150416
  | 203 => 0x151616
  | 204 => 0x40096
  | 205 => 0xd0411
  | 206 => 0x1a57d1
  | 207 => 0x40ed1
  | 208 => 0x41611
  | 209 => 0x1a9951
  | 210 => 0x8416
  | 211 => 0x128416
  | 212 => 0x9516
  | 213 => 0x45651
  | 214 => 0x1a4ed1
  | 215 => 0x3d292
  | 216 => 0x41292
  | 217 => 0x3d5d2
  | 218 => 0x3c412
  | 219 => 0x3d612
  | 220 => 0x15d612
  | 221 => 0xb0416
  | 222 => 0x15c412
  | 223 => 0x3cd52
  | 224 => 0x3d652
  | 225 => 0x3d892
  | 226 => 0x40d52
  | 227 => 0x1a1652
  | 228 => 0x1a57d2
  | 229 => 0x41612
  | 230 => 0x1a9952
  | 231 => 0xd43d2
  | 232 => 0x1643d2
  | 233 => 0x3c416
  | 234 => 0x170416
  | 235 => 0x9616
  | 236 => 0x1a1655
  | 237 => 0x161651
  | 238 => 0x41616
  | 239 => 0x9896
  | 240 => 0x160096
  | 241 => 0x41296
  | 242 => 0x1a57d5
  | 243 => 0x40b095e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2346
  | 6 => 8373
  | 5 => 3000
  | 4 => 64
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (96186+((h/782+packedAt gbK7 (86802+(h % 782)*12) 12) % 3097)*13) 13
  | 6 => packedAt gbK6 (440978+((h/2791+packedAt gbK6 (401904+(h % 2791)*14) 14) % 13372)*15) 15
  | 5 => packedAt gbK5 (190000+((h/1000+packedAt gbK5 (177000+(h % 1000)*13) 13) % 4792)*13) 13
  | 4 => packedAt gbK4 (4627+((h/21+packedAt gbK4 (4480+(h % 21)*7) 7) % 77)*7) 7
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0fc07c07e03ffc1ffe00067d38fe331e7c
  | 1 => 0xe00ff0007fffffc07fe07fff19b2cf303fe38f
  | 2 => 0xfffff8007ffffffff8000e1c30fc3c3fff0
  | 3 => 0xffffffff800007ffffffffe03f003fc03ff
  | 4 => 0xfffffffffffff80000000fffc0003fffc00
  | 5 => 0xfff000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa1ee02c41cc1651aac8aea0a02141856330e3c
  | 1 => 0xc2265000254aad4a14a22ca608b04b30176285
  | 2 => 0x8442b5588004d1a35ad3081461430dc0c1b7d0
  | 3 => 0x88929ad4a900010631c5158b603b00368016a
  | 4 => 0x110dce3673e71e3c00086060dffc0003bed800
  | 5 => 0x1e0000380300182002100180fdebe6a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37085
namespace PEqualNP.Outside.L_meta_37085
open PEqualNP.Outside.L_meta_37085.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
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
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 64 := (concat bs4_4_0 bs4_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 40 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
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
theorem allgb_4 : Interval gbAtlas 4 0 64 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2976 : Interval gbAtlas 5 2976 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3000 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632))) (concat (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728)) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)))) (concat (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016))) (concat (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208))))) (concat (concat (concat (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)) (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400))) (concat (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)) (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)))) (concat (concat (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)) (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784))) (concat (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)) (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)))))))
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
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8192 : Interval gbAtlas 6 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8224 : Interval gbAtlas 6 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8288 : Interval gbAtlas 6 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8320 : Interval gbAtlas 6 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8373 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))))))) (concat (concat (concat (concat (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560)))) (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816))) (concat (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)) (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)))))) (concat (concat (concat (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360))) (concat (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)))) (concat (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928))) (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056)) (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 bgb_6_5184))))) (concat (concat (concat (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 bgb_6_5312)) (concat (concat bgb_6_5344 bgb_6_5376) (concat bgb_6_5408 bgb_6_5440))) (concat (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568)) (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696)))) (concat (concat (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824)) (concat (concat bgb_6_5856 bgb_6_5888) (concat bgb_6_5920 bgb_6_5952))) (concat (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080)) (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 (concat bgb_6_6208 bgb_6_6240))))))) (concat (concat (concat (concat (concat (concat bgb_6_6272 bgb_6_6304) (concat bgb_6_6336 bgb_6_6368)) (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496))) (concat (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624)) (concat (concat bgb_6_6656 bgb_6_6688) (concat bgb_6_6720 bgb_6_6752)))) (concat (concat (concat (concat bgb_6_6784 bgb_6_6816) (concat bgb_6_6848 bgb_6_6880)) (concat (concat bgb_6_6912 bgb_6_6944) (concat bgb_6_6976 bgb_6_7008))) (concat (concat (concat bgb_6_7040 bgb_6_7072) (concat bgb_6_7104 bgb_6_7136)) (concat (concat bgb_6_7168 bgb_6_7200) (concat bgb_6_7232 (concat bgb_6_7264 bgb_6_7296)))))) (concat (concat (concat (concat (concat bgb_6_7328 bgb_6_7360) (concat bgb_6_7392 bgb_6_7424)) (concat (concat bgb_6_7456 bgb_6_7488) (concat bgb_6_7520 bgb_6_7552))) (concat (concat (concat bgb_6_7584 bgb_6_7616) (concat bgb_6_7648 bgb_6_7680)) (concat (concat bgb_6_7712 bgb_6_7744) (concat bgb_6_7776 bgb_6_7808)))) (concat (concat (concat (concat bgb_6_7840 bgb_6_7872) (concat bgb_6_7904 bgb_6_7936)) (concat (concat bgb_6_7968 bgb_6_8000) (concat bgb_6_8032 bgb_6_8064))) (concat (concat (concat bgb_6_8096 bgb_6_8128) (concat bgb_6_8160 bgb_6_8192)) (concat (concat bgb_6_8224 bgb_6_8256) (concat bgb_6_8288 (concat bgb_6_8320 bgb_6_8352)))))))))
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
theorem bgb_7_2336 : Interval gbAtlas 7 2336 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2346 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)))))) (concat (concat (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440)))) (concat (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 bgb_7_1568)) (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 (concat bgb_7_1696 bgb_7_1728))))) (concat (concat (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 bgb_7_1856)) (concat (concat bgb_7_1888 bgb_7_1920) (concat bgb_7_1952 (concat bgb_7_1984 bgb_7_2016)))) (concat (concat (concat bgb_7_2048 bgb_7_2080) (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176))) (concat (concat bgb_7_2208 bgb_7_2240) (concat bgb_7_2272 (concat bgb_7_2304 bgb_7_2336)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00feeaeeeafce0ec00
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4242598912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37085.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.and,[2,4]⟩,⟨.or,[0,2]⟩,⟨.and,[5,8]⟩,⟨.or,[3,7]⟩,⟨.or,[1,2]⟩,⟨.and,[10,11]⟩,⟨.or,[0,1]⟩,⟨.or,[6,13]⟩,⟨.or,[9,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242598912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242598912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37085

open PEqualNP.Outside.L_meta_37085 in
theorem PEqualNP.Outside.L_meta_37085 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242598912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242598912) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
