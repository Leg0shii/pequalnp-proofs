import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37151.Model
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


end PEqualNP.Outside.L_meta_37151.Model

namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
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

def SBf (j : Nat) : Nat := [6, 3, 7, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37151

namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x19030000000000001408020000000458071a2a048038001e000018000005000bf43de43bd43dd439d43be42bc42de32dc32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x51c001812c4000101440598040c00147552438e292871f5150e38a0a1c754c428faa4651d540ca3aa7a0c7553318eaa2631d531023ea9184755030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x200098086983548ca0c625513186181544c60e62d5230
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
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
  | 4 => packedAt s0K4 (302+((h/5+packedAt s0K4 (272+(h % 5)*6) 6) % 40)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 2 => 0xe0ffffe0fffffffe07ffe0fffc1fffff9e3c7f
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x421888c428905040594c09498129212c28d1b1
  | 2 => 0x882111024122208a0291209224124a50922446
  | 3 => 0x444a22481a440314a8265204ca409505454a98
  | 4 => 0x96b3c4929076b5e734c318c7739c0619f80f60
  | 5 => 0x18c3871ce38739f9c73b9ce063181861ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0fcc0fcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x5fc7ff3c7ffe03fc
  | 2 => 0xffffffffffffffffffffffeff8e7ff8e0ffccf
  | 3 => 0xfffffffffffffffffffffff7ff07fff00fff0f
  | 4 => 0x7bfff83ffff00ff0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2072404c1262615c
  | 2 => 0xffffffffffffffffffffff90960a1484a4a4c5
  | 3 => 0x920d42921494b0a
  | 4 => 0x60486b249818ea0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 29 s1Pos s1Neg, 0xfaaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000faaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xb0011124007c01012515953c3d48c2644d2d380000000480024c1c40d2c5c01b323852730a831d40a02a14ab0001068c011003000483213000049112ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc7c01394d58284400008494385cec804900000000ac64fc011800006cb988008d609d28213c017d20343c7400b104980890e40000c8f4115cbc013430cc016d30b4590d7168a4002c04c400014000a0015174dcd04c6984e818e088501524c1544078a91d64005424f80109441c00d47178f0d91180000001480000000060012d141c0006020400060202060812003800020a0200000a0a020400060e0e0c12020c033e51d0e7aa921e7d4d439e28a873e5410eeea2a15d145429f2a6653d54ccaeca3995d547329f2a0653d540cadca5a0db54b419ea9c833e51906dea4a0db14941af298835d531073ca620cf54c41cea98831d531067ca220ed944419f2a6633d54cc73a8798db94b31b6a96633f548c678a918cfd51319e2a2639d434c6dea498db14931bda826378504c67ca818cf550319f2a6433d54c87688390ebd0e21d6a1c436e518875c8310eb106219faa2433c54487688210ebd0c21d6a18436e51087cca210f9d0421d720843ac41087c88210e910421f318843e531086bca7a05754f40b7290816d521027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a4213d54842dca5085b54a10f210c213f5444278a88857d4d10ae29a216f52442d8a4887908410
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xe3d11c508300904a0000104c848c2d400600434d0000f4821c6550d31c650c504c6956310721a358c41886956310421a918543086a66190421a358c41086c56310421e198c41086a56310421e158c41086856310421a919231086a4644c421e150d31086e0604c42199185521031543544308758e54843265408610
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x4084847650d3108740a18c098843415ce5408610
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 4 => packedAt s2K4 (2937+((h/33+packedAt s2K4 (2673+(h % 33)*8) 8) % 130)*8) 8
  | 3 => packedAt s2K3 (833+((h/7+packedAt s2K3 (798+(h % 7)*5) 5) % 26)*6) 6
  | 2 => packedAt s2K2 (150+((h/1+packedAt s2K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xfffffff01fc0fffe0f81ffffffc1e03f27fe67
  | 3 => 0xff81ffffe000fffff001ffe0fffe003fc78f87
  | 4 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x530444624488208052925909181229a44c30ab
  | 1 => 0x851888a1c911491605a0aa326a41428921d665
  | 3 => 0xa2d514483aa92aab0513548b4b40532c68b86
  | 4 => 0x2c51a20912301b4d29640610c7299603b00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06311823ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaacc88eeaa8800eeaacc88eeaa8800eeaacc88eeaa8800eeaacc88eeaa8800eeaacc88eeaa8800eeaacc88eeaa8800eeaacc88eeaa8800eeaacc88eeaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
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
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 2 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 2 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d0a50fa85610d1700980ac4035280522892f44004ae046c00000a800348753933258880300118e103c61c161c01520010863c00010438321d402040100006ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fa20fd20f920fc20ff10fb10fe10fd10fc10f810
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xc41f941883f083106e10620fd98c41fa31883f263107e0c620fd90c41fa21883f243107e08620bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20dfa1241bd42482fea2905f14520df20a41bc41483f680907e90120fca0241f840483f660907e8c120fc98241f830483f640907b88120fdaa241fa54483f2a8907e15120fda9a41fa53483f2a6907e14d20fda1a41fa43483f286907e10d20fda9241eb52483f684906ed0920fd21241f9424837284907e10920fd99241fa32483f264907e0c920fda8a41fa51483f2a2907e14520bc28a41fb41483f482906e90520fca0a41f8414837082907ecc520fd18a41f931483f062907ec8520fd10a41f921483f042905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf298417d53082f8a6105f94820dfa1041bd42082fca2105f54420df20841bc41082fca0105e94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c437c83886f10710fda0621fa40c43f281887e10310fd98621fa30c43f261887e0c310fd90621fa20c43f241887e08310fdaa621fa54c43f2a9887e15310fda9e21fa53c43f2a7887e14f10fda1e21fa43c43f287887e10f10fda96217b52c43f4a5887e54b10bca9621f852c43f685886ed0b10fd21621f942c437285887e10b10fd99621fa32c43f265887e0cb10fda0e21fa41c437483887e50710fc20e21b841c43f663887e8c710fc98e21f831c43f643887e88710fc90e21f821c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10bea8c21be418437883085f94210bd28421fa20843f241087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221bf424437a84886f90510de20a21fa20443f240887ec4110fb082217f54042fca8085f55010be2a0217f53042fca6085f54c10be298217f52042fca4085f54810be29021bf420437a84085f94410df20821bc41042fca0087ed0010fd20021f940043f080087ecc010fd18021f930043f060087ec8010fd10021f920043f040087dc4010fd08021f510043f220087ed5010fd2a021f954043f0a8087ed4c10fd29821f953043f0a6087ed0c10fd21821f943043f086087ed4810bda9021fa52043f2a4085e54810fc29021fb420437684087e90810fca1021b942043f084087ecc810fd19021f932043f064087e94410bd28821f251043f682087e90410dd20821f941043f082086e10410fd98821fa31043f262087e0c410fd90821fa21043f242087e08410
  | 1 => 0xf548877ea910cfd5221bf2a4437d54886f8a910ef152219e2a4437f53886fca710df54e21be29c437d528877e8510ef50a21f799443ec32886fca310ef90621de20c43f631887ea6310fbc8621fb90c43fb50886fca110df54221fc284437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53487bea690d7d4d21bf29a437d53486f8a690f714d21ae29a43bf424877a8490ef90521de20a43f631487ea6290fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821dfa1043bd42087de6410fb0c821bf28843be41087788210fbc8421fb10843ed21087ea4210df94021fd280437a50086faa010fe54021bca80437e53d02faa7a06fd0f40dea1e817e52d02faa5a06fd0b40dea16817e51d02faa3a06f90740de20e817d54902fca7205f54e40df21c81bc43902fca5205f54a40dfa1481bd42902fca3205f54640df20c81bc41902fca1206fd0240fda04817f53502f8a6a06fd0d40dea1a817f52502f8a4a06fd0940dea12817f51502f8a2a06f90540de20a81fb405037c80a05f95040bf298817d531037c86206f10c40bf290817d521037e84206f50840bf288817d511037c82206f10440bf28081bf40103f480206f50040fca0081b940102fea9985f95330beaa6617c54cc2fca5985f54b30dfa1661bd42cc2fca3985f54730df20e61bc41cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5186fd0a30dea14617e518c2faa3186f90630de20c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930dfa1261bd424c2fea2985f14530df20a61bc414c3f480987e50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830bea9061bf420c37a84185f94430bea8861be410c37882185f94030fda0061f8400c3be60187e8c030ee98061f9300c2fea9905f95320df2a6413e54c82faa9906f553209eaa6417c54c82fea7905f94f20bea9e417c53c837e85906f50b20bf28e417d51c837c83906f10720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441bf428837a85105f94620bea8c41be418837883105f94220fda0441fa40883f281107e10220fd98441fa30883f261107e0c220f790441fb20883f6a9107e95220fcaa441f854883f6a7107e94e20fca9c41f853883f687107e90e20fca1c41f843882f2a5107ed0a20dda1441fa42883f285106e50a20fc21441fb32883f465107e4ca20fc19441fb51883f4a3105e94620fca8c41f851883f683107e90620dd20
  | 2 => 0xb7aa0a16f14142bf2a0853e5410afca6215f54c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042fd280857a5010afaa0217e54042bca80857f54ccafca9995f55332be2a665bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465bf428cb7a851977cca32f7994657e518cafaa3195f94232fd284657a508cafaa1197e54232bca84657f544cafca8995f55132be2a265bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca4196fd0832dea1065df320cbdc6419774c832f6990657e510cbeca2195d94432bea8865f5510caeaa2195f94032fd280657a500cafaa0197e54032bca80657e53d06faa7a0df94b41bea9683bf42d077a85a0df94341fd286837a50d06faa1a0fe54341bca86837d54906fca720df54e41dfa1c83be439077a8720ef10e41bf294837d529077e8520ef90a41dea1483bc42906fca320efd0641fba0c837e50906faa120efd4e41df29c83bd5390778a720efd4a41df29483bd529067aa520ef14a41df99483be329077a6520ef0ca419f28c83bf509077ca120ef54241de284837f53506f8a6a0dfd4941be29283bf425077a84a0fdd0541df20a837f50507f6a0a0ded4141be28283f850506f0a0a0df95041bf298837d531077e8620ef90c41dea1883bc43106fca420df54841dfa1083be421077a8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020efd4c41df29883bd5310778a620efd4841df29083bd521067aa420ef14841df99083be321077a6420ef0c841df288833e511076ca220efd4041df28083bd5010778a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31bea9663bf42cc77a8598f7ccb31ee99663be41cc7788398df94331fd286637a50cc6faa198fe54331bca86637f548c6fca918df55231be2a4637d538c6fca518df54a31dfa1463bd428c7bc6518f70ca31bf28c63be418c7788318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898dfd4931f7a92636f524c6f8a498fb14931b629263bf424c77a8498f7cc931ee99263be414c7788298fdcc531ef18a637f504c7f6a098ded4131be28263f8504c6f0a098dfd5031bf2a0637d540c6f8a818df94c31bf290637d520c77e8418ef50831ef19063dc320c6fca218ef90431de20863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e437d53c86f8a790efd0b21dea1643be41c87788390df94321fd286437a50c86faa190fe54321bca86437
  | 3 => 0x984532c39aebcda2da1e6314778f47ee10c00000140288d4800000001d803e00094c000910000257900106a090c08006b24f9283267e6b258222f050635a82f148477471bb257edbc001fb7348ec0333e2bc000b9000000501673e569ed486d3c06666ec002026e0059112a959ed35b108600045400000492071a213700088cae30a3349e93309d39031180800676e65d09eb58ee8d7a0a5000000e3936000001aa8e900043d5100049c190001022b0001b59007c0945892d87ba498003aa0005a8000f5000004014020010000080180000000801000000000000000280000080b0000080080100c0000080000a0000180f0080000300d00202400002004018000000000040000100200000802000008010000100000283b00003c048010000200000000e0040180200200000003000000010000340540280100602c00003000008038000000040000401004804800010034008060000040100000800801010004000000090080000280400a008000030060680081300000000806000000038040000140000a004004038020000000000000a028000050080000500000c034008030020000080100400002007004010080000000000000501008c008010140000100300c0000200401601c0000200200c0080000a0180080600806c03000022008038030000040300200800400002038008000020000040000001a004008010060000701701003c0180902800006002002000028020120100000200600000002004004008040020040000000400000001000020078000020b00181000c000008000000040480003e0000080000c0000480000400c0480600a0040300000c000048090040680000000603c0680300c0040e00600a0000000b00600c098010000000080000a0540200502000c000030000040000400e000005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ff6a0a1ded4143be28287f85050ef0a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a14f94742dea8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242fd284857a5090afaa1217e54242bca84857f5350af8a6a16fd0d42df21a85bd4350b7886a17bd0942df212857f5150af8a2a15fd4142be28285bf5350b7ca6a16f54d42de29a85bf5250b5ea4a16fd4542df28a85bd5150b78a2a14f14542dfa8285be505
  | 4 => 0x4e5dd63f1358ab8003d9000a81b437a634000508000008b51501823c260de0000005ac001b8384000002ea6942a473945000640000f930c474198423929898bb5c01c0019492d0340000015974ebac00125196001eabca1128c8a82ab118044000000001500004e000b51cda7672abe5519f417c000000df0005f4000001fc000d6a2b182f912312155e008000003504a9e293c63c969d43cc6bc000003b34740010000000058925800506e894119153ef3d1e0a8626648fb8fc40ea181e2ad2ec7b5041807ec074bf88f0002b19500020256d60a2e5b6bf5d8b3000030ddc000000b3000008570980a4a330000001b2f30987d4000211d0658759dc046901cf1986dab55e18b43168603797a520048f12f05dc121f83da000e2026b79000000baa750004fc00000000bd9e40000ba584a1b47452349a58c941c8ddf613453ccb51099c31e12c0021a000000c3a7b008b9d1fb0b34a2ccc21c60e8fac973c225660d6107d5fc0b07706e408b142c89c124684de8a410a32102800000000d907c16c590f81d000016c0036c000c951b10b684001458c2000000f8800594000001f65c64209a9ff224359de25b000964400007ce0006a9886b61d80000069800000000000a700000000000069a2506e9a8988153d8cb9c71ab194a48d887f48abfd538006b06f90897c5d000133b657b0eb8f702a47c000578aa7c2581ef0005be00126800000000e89d32225511a8264e60007b09b000391de8000000ad8100039c4514d8db6c20004680005ad1855a99214000000000000f40005336a000000000006081f829000000002cd000cc40000c75aa294730f682000003bf460534000005a600191a740000000015337e97c681d600007c9c927590d98e5268000000b60002ac4115a1ef530a1555000000954000000005c5dc80000000124270562000002b20d043400000000001348f1000001498000c6268000006188b16e1d400053c002ac3aa2e9528ec0000000003a12c0009933641400000328000749b48003b6a343b9e417e15cdc8ad3d0fb8a5b7801e001762786220017c00043e5b40014e000379069e70000000007a0001b000014000cc9ee00069c88031193726bf18fa172f6000d51f34a4c641792f642e70000007de1295e24312e6552b25c5ae17cf90006e4000000000da1cc0027d5c22b85db81332cdc000001a2f50003a53f42655f000000000002fb234ed0e2bf45c4000002d11f49904800006000112000000001d4800000adcc5000000504000006ae000000000000016e8005220000000000000002800000001e800043a431d03d36f6e7c001e3108f10b18000001e54400042a0017a80020ed0c9e8002bad800026d0002dd1ca0b1f60018c3963cc2c58019e08ea10679b7298f5dbf0ff72246dc80f0198ac0fc878714975f91781fa6
  | 5 => 0x240000000002889ac83000450f440029431c55c001fc1647a40017404af180017966841400280246001c609403229dae8d733e83193bed690b0d8aa27258705d5800044394a8a6c336765c6a775de5a59f81b2846b8003c7000f249c3f5542374003636b4d59bb800312000b380000e02800000468b79251097069c98305057ab9186b4517a85000000000300000003969055d98c172171a98006786bc00384000488473cd53a4a0e780000000182b71000001408006920003000040c00192110000000eb800000e507c000000b41f48001020000004f4c29fc003850000359c8ce000118188a66f8ad5883c177600173055000001f326f000471598002ca00000148000000000000005cc00000000e24001b0072318000b51a8c6d9e8512a400000058266730000000000015313b0009e5c337f0005f800117000b48d1b38000000000c71da1ec0028f432000411a770400000000092000001e5000edd13040000fa8000000007859d000000001018005f4001b5000000c518e03862c24d4d0130a400c2b00028e0003385e374000fea652dc0ed6b1df00095c0015a3d4b00000000001143f0e0260c74003be05ce60002896e8000000614bcf8c0007272400089b084020000000017800195800424f3922254000ed80014a388700000200000000000000000138bb552e36572a631c2ae52616610e361ba80065e70c3800000057c002e0000001dd3d23bc000b40000000000019d068871eb000000df4fc0f7000000aa9e00000003480000000000000000000329a45ee0000591f0000010835f00000000000518e1c4f82756c51892197426b19a8800000000002954b004123b22640334001a017086c0030979622c8cb8b000fa00000070020c8c00016028dbb13a73a9b800000000d9c7306a588000388000002200000000000104b40000000ed0000000000001e6c88e1279fe6dc001658000009f0000006e6254000000000000000050ecd40000041e001818750000000000061c6515404100005c6e1d85b28f5d30005da9f87917730a279d2000088a5918ae93444a400000000878190000d6000331b62de001fc00071e0008b307366d50000e2000f88b810e1d4a9081bdb000f7d0b05a57
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2544427960951109ed81544423e65151108f588544423e61151108f184544423e6494d108f59253442796094d108fd91534423c6454d109bd89534426c6254d109ed81534423e64949108f592524427960949108fd91524423c645491097d8d524425c63549109ed81524423e64149108f590524427a60149108f997424423c65d09108f995424423c65509108f996414423e65105109e996204433b5488110ce15220442786548110ced5120443385448110dad49204433b54c4110ce153104425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520427960548108f990520423d64148109798c520425d63148109e980520432e5250810cb54942042b461508108f992500423d64940109e596400433854500109e594400433954100109e59630042bb644c010ae1913004279650c010ae99030042b9640c010d654c300427965c8010ae99320042b964c80109e596200436952880109e59420042ba6408010ae59020042796584010ae99210042b964840109dd95100427b6544010aed9110042b86444010bc98754043395415010b698c54042d96315010ba98854042e96215010bc98454042f261d4c10aed9153042b86454c10ae99053042b96414c10d654c53042ea6214c10ba58853042f26114c10bc98643042f16190c109ed9543042786550c109e99443042796510c10bc987520427a61d4810dc98752042796594810ae99252042b96494810dad8952042ba6414810ae59052042da6314810b658c52042f26114810ced4b420433952d0810ae987420427a65908109e59642042b96490810da54a42043695250810bcd8542042f06150810ead89420433b5250810ea94942043395250810ea54942043295250810ecd8542042b86150810ec18542042b061508109e99442042796510810ae990420427a658c8109e59632042ba648c810ae5923204369528c810da54932042f3614c810bc185320427a650c8109e59432042ba640c810ae59032042f2610c810bc58432042796294410ced0a51043394294410dc98651042f16594410dc59651043b34294410ec50a510427965d0410ae58a410433b5290410ce54a41042ba6190410ce94641043b251904109ed9541042b96210410ced4841043395210410ae98441043b26110410ce94441043b251104109e59731042ba64cc410ae59331043b0418c4109ed9531042bb644c410ae19131042eb624c410ba18931043b0414c410f44c4310427965c8410ae99321042b964c8410ec107210427b6588410aed9221042b86488410da54a210427b6548410aed9121042b86448410b6d8d21042d863484109e99421042796508410ae99021042b96408410b698c21042d96308410da54821043b04108410
  | 1 => 0x83ab5290520ae986414833851905209ed9541482786550520ba98841482e96210520dc14441483aa6210520ae58841483a96210520aa58841483ab5210520ae98441483b26110520ecd4441483385110520ec144414833051105209e997314827965cc520ae99331482b964cc520dc147314827b654c5209e19531482bb644c520ae19131482eb624c520ba18931482ea620c520ba5883148370510c5209e99721482ba64c8520ae59321483a942c8520aed9221482b86488520dc14621482bb6448520ae19121482db6348520b618d21483a94248520dc145214827a6508520ae99021482b96408520b698c21482d963085209e983540823d65950208f986540823f62550208f589540823c61550208f990540827a60150208f993530823d64d4c209e983530823e6414c208f59053082766114c209d584530827a6014c208f992520823d64948208f597420823f65508208fd91510823c64544208fd96410823d65904208fd94410823d6510420ced0a50083394294020ce90650083384194020ce952200833954880209bd95200836a50480209ed95200833a5448020ce551200825e63d53109758f54c423e64d4f108f59353c423e6494f108f59253c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c433a5450310ced5040c42bb644c310ae19130c435a534c310ae99030c42b9640c310ae99320c42b964c8310da54920c42ba6408310ae59020c42da63d5310b658f54c42f261d5310ced5254c42f26115310ae99353c42b964d4f10bc98753c42ba6494f10ae59253c435b5394f10bc98453c427b6550f109e19543c427a6510f109e59443c42f261d4b10dc98752c42ba6494b10ae59252c436b6254b10ae99052c42b96414b10b698c52c42d96314b10bc98452c433b52d0b10ce54b42c42ba61d0b109e99642c42796590b10ead8942c433b5250b10ce54942c42b86150b109e99442c42796510b109e99632c4279658cb10ae99232c42b9648cb109e99432c4279650cb10ae99032c42b9640cb10bc98432c42f1610cb10ae58a41c433b5290710ce54a41c42b96210710ced4841c43395210710ec98441c42ba64cc710ae59331c42bb644c710ae19131c42eb624c710ba18931c42ba64c8710ae59321c42bb6488710ae19221c43695288710aed9121c42b86448710b6d8d21c42d86348710ae99021c42b96408710b698c21c42d96308710da54821c423d62952108fd89548423e64d4e108f593538426e62d4e109b58b538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528423e6414a108f590528423f65d0a108f597428423f6550a108f59542842b46150a10ce95220843395488210da54a208433a5448210ce551208433a54c4210ce553108423d62d51108f99
  | 2 => 0x65105308f194414c27a6590130ce152404c2786550130ce151404c33854cc1308f596540c23d62950308f986540c23f62550308f185540c33860550308f990540c27a60150308f992520c23d64948308fd97420c23d65d08308fd95420c23d65508308fd91510c23c64544308fd96410c23d65904308fd94410c23d65104309e597400c33954d00309e594400c3395410030ce552300c25f654c0309ed95300c2b8644c030ce551300c23e61953208f18554c823e64d4f208f59353c823e6414f208f59053c82766114f209d58453c823f64547208f19151c823f65907208f59641c823f65107208f59441c82ad62107209798c548825d63152208fd91538823c6454e208f990538823d6414e208fd91518823c6454620ce15140883395410220aed9130882b8644c220ae99030882b9640c220d654c30882ba64c8220ae59320882e962d5220ce55054882da6315220b658c54882e96215220ba58b53882bb6454e20ae19153882ba6414e20ae59053883595314e20ba588538827b6550e209e195438827a6510e209e59443882ba61d0a20ead8942882b86150a20ae99232882b9648ca20ae99032882b9640ca20bc98432882f1610ca20ae99351882b964d4620b698f51882d963d4620ced0a51883394294620aed9151882b864546209e997418827965d0620ae58a418833a51906209ed9541882786550620ae58841883b26110620ce944418827a65cc6209e59731882ba64cc620ae593318827b654c6209e19531882bb644c620ae19131882eb624c620ba18931882ba64c8620ae59321882bb6488620ae19221883725188620aed9121882b86448620b6d8d21882d86348620dc94521882ba6408620ae59021882da6308620b658c218825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534823e64d45208f59351482ad6210520cdd44414833451105209e99740482786550120ce151404833954101209e9973048278654c120aed9130482b8644c120d614d30482ba640c120ae59030482ba64c8120ae59320482e96295120b6d8d54482d86355120bad8954482f36155120bc18554483395415120ba58a53482bb6454d20ae19153482eb6254d20bcd8553482f06154d20ae99053482b96414d20d654c53482ea62d0d20ba58b434827b6550d209e195434827a6510d209e59443483ab52d0920ae987424827a6590920ae59242483ab6250920ead4942482b861509209e99442482ba6410920ea50b324827a658c920ae99232482b9648c9209e99432482ba640c920ae59032483a9420c920f24c832482f2610c920bc58432482ba64d4520ae59351482bb6454520ae19151482db6354520b618d514833b4214520ce508514827a65d05209e597414837051d0520ae58a414
  | 3 => 0x2218f992538863d6494e219e98253886796094e218fd91538863c6454e219ed8153886786054e21ad98742886b46150a21b958432886ad6290621ab58841887c4328c621b918931887c7324c621ced53508873854d42218f992508863d64942218fd91508863c6454221ced50508873854142218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219ed8153486786054d2197994534871f5414d21c715053487556114d218f997424871f53d0921c714f42486b661d09218f195424871f5350921c714d42486b461509218f996414871f5390521c714e414863e6510521c7d4c414871c5310521d514e3148674654c521d314e214873b54d4121ce153504875b53d4121d614f504873b42d4121ce50b504873a41d4121ce107504873b5414121ce150504875b5314121d614c504873b4214121ce508504873a4114121ce104504865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d3189530863e6414c218f590530865e6314c219d984530867a6014c219e580530863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420874d53cc8219b594320863f65904218f596410871e5390421c754e41086ad62904218fd94410863d6510421c794c410871d5310421ab588410875553884219bd9521086cc63484219dd9521087555348421ce95250087395494021d694e50087595394021ced0a50087394294021ce90650087384194021ce95150087395454021d694d50087595354021ced0950087394254021ce90550087384154021ae18143d032d52d0b40cd94441d02b96010e40cb549429033651906408f99743502b86050d40cbd4942502b86050940cd14641502ba60905408f59643102b96010c40cb54b42102b960d0840cd94441102b96010440ae592401023f65500409ed9540102bb6550040ced9540102b86350040ce54d40102bb6250040ce54940102b86150040ce945401027661d53309d58754cc23e6494b308f59252cc23f64547308f19151cc3365110730cd54441cc33b54103309b988548c26d62152308f992528c23d6494a30cb949428c32d5250a308fd91518c23c6454630ce151408c23d62d51308f987544c23e64951309ed81544c23e65151308f588544c23e6115130ce580544c23e64149308f590524c23e65d09308f197424c23e65509308f195424c23e64d45308f593514c23e65905308f196414c23e
  | 4 => 0xed8143106b86050c41c754c43106ba6010c41ae580431067a60948419e582521072d52d08418f59642106ba6090841ae58242106ba6010841ae58042106ba60d0441ae583411063f6550441aed8141106b860504419dd9541106b661d4c41aed8153106b86054c41c754c53106ae6214c41ab58853106b66114c41ae98053106b96014c41ad98752106ba6094841ae582521069e6314841a758c52106b66114841ae98052106b960148418f996321063d658c841cb54a32106ba608c841ae582321072d524c841add8532106b4614c8418f994321063d650c841ad98432106b5610c841ae98032106b9600c841cd986511069e6314041a758c50106ae6214041ab588501073950140419e98354cc67960d53318f58a54cc63f62553319e98054cc67960153318f99252cc63d6494b319e98252cc6796094b318fd9742cc63d65d0b318fd9542cc63d6550b31ad18542cc73a5494331ce55250cc6796294331ced0a50cc7394294331ce90650cc7384194331ce95150cc73954543319ed8950cc73b4254331ce50950cc73a4154331ce10550cc67a60d52319e583548c67a60952319e582548c63e6494a318f592528c67a6094a319e582528c6d5610ca318f992508c63d64942318f58b544c63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c63d6215131cbd53524c72c54d4931cbd93524c72c64d4931dad83524c76860d49318f990524c63d64149319e980524c6796014931cbd50524c72c5414931cb990524c72d6414931d9584524c76a6014931da580524c63e65d09318f197424c72f52d0931cb14b424c63e65509318f195424c72f5250931cb149424c65e65cc931d314b324c74c524c9318f996414c72f5290531cb14a414c63e6510531cbd48414c72c5210531d314a314c73b54d4131ce153504c76b52d4131da14b504c67962d4131ced0b504c73942d4131ce907504c73841d4131ced50504c7385414131dad48504c76852141319e588504c73b4214131ce508504c73a4114131ce104504c67b60550319e181540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63e64948318f592520c67a60948319e582520c72e5250831cb549420c6b4615083197596320c6d5610c83197d95310c6cc624c431e5105310c677654c4318fd91500c63c64540319e98354c867960d53219e98054c867960153218f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219e98053c86796014f21ce95250c87395494321ced0a50c87394294321ce90650c87384194321ce95150c87395454321ced0950c87394254321ce90550c87384154321cb58b548873661d52219e982548867960952219ed8154886786055221cb58854887366115
  | 5 => 0x51d0a9e6314342a758c50d0b3950143429ed815190a786054642ced0a5090a7a6194242ced095090a7861542429e9805350a796014d42c714d4350abb6050d42ae1814350aba6010d42ae5804350aba6090942ae5824250a7a60d45429e5835150aad6294d42abd895350ab76154d42ad1855350abb6054d42ae1815350b1d5314d42ae9805350ab96014d42ae9835150ab960d4542a7d8d5150a9c6354542aed815150ab86054542a7d8d5050a9c6354142add855050ab46154142ce5405050a3f65508429bd954210b2e54508429ed815110a786054442ced0a5010b3942940429e9865010b3b4254042ce5095010a7861540429ed8154cca7860553329e98054cca7960153328fd9151cca3c64547329ed8151cca7860547328fd9150cca3c64543329e983548ca7960d52328f986548ca3c61552329e980548ca7960152328fd91518ca3c64546329ed81518ca786054632ce952508cb395494232ced0a508cb3942942329e986508cb3a5454232ce551508cb3b4254232ce509508ca7861542329dd85544ca7461551329ed81544ca7860551329e980544ca7960151328f993514ca3d64d45329e983514ca7960d45328f990504ca3d64141329d987540ca7561d50329e983540ca7960d50328f596540ca3e61950328f185540ca3e64150329d984540ca7561150329e980540ca7960150328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb365494432cd552510cb376494432cd192510cb374294432cd50a510cb736094432dc182510ca3f64544328f191510ca7b60544329e181510cb365454432cd551510cb376454432cd191510cb374254432cd509510cb573254432d54c9510cb736054432dc181510cb3a5494032ce552500cb725194032dc546500cb3b4294032ce50a500ca7a6194032ce951500cb395454032dc945500cb715154032ced09500cb3942540329e185500ca7a6094b419e58252d072d52d0b419e58a50d073b4294341ce50a50d067b6254341ced0950d073942543419e98253906796094e41c794d43906bb6050e41ae18143906ba6010e41ae580439067a6094a419e58252906ba6090a41ae582429072d5250a41ae98042906b96010a41ae98341906b960d0641ad98753906ba60d4e41ae583539071f5394e41ae98253906b96094e41ad98453906b661d4a41ae98252906b96094a41a798c529069d6314a41ad98452906ba6014a41ae580529063e658ca418f59632906ba608ca41ae582329063e650ca418f59432906b6610ca41ad58432906ba600ca41ae580329069e63d4241a758f509073b50942419e980525067960149418f997425072f52509419e58b505073b42d4141ce50b505073a41d41419e588505073b4214141ce508505073a41141419ed8153106786054c41a
  | 6 => 0x16a000069a5303d8000002130000569e902ca7d00022b9ca8e48001c50d60000e5a6b8000000000000c88002488000000001688000000000c70001c81df8c22419df0da8001e20fd05b86695f8a30878fe8f980000000000000000000000004d9d680009e9759d78001b9801002800000000800003003000400401c00402000000400000000000000404000c00801800800000c00000001000800800001001400401400800000000400001000000400000400001000800800800001800800000401400000403404001000000c00001000000001400002800003000800000001000c03000000000000000000000001000000c00c00002000002400800800001c01c00800000000000402400001000000400000400000c00001800000800000401001000000000000400400002002401000400000400800c03c00800001c00003800c00400000000000401400000000000000400000c00000800000c00000000000000001c01000801800400800001400000400802000000400802000400401400c00c00000400405000000000801000401800001800800001402400401400000800800800400002c00801400400400000c00400400002800001001400000400000802000401000800000805000000400c00401c00000000801401800000403805c02800000c02800000403001c00c00000000400000000401000800002400000000800400800800000400000001c00400800000001c00000000800400401002800000802400400000401400000002003801001001000000000000000401c00000400801000001000001400000001000001400403400400c02000400000802c0000000200080080100000140100200000200000000040080140fc02002000400400001400000000000800800800000400000800800001000000800000801000001800002000c00400004c00c00401c01803800c00000000400400000001000c00400800000800000000c00c00000400000000403000800001000c00000000800c00800000802c01800c00003400002400801801400400000800c07800000000400800400400002400c00c0027a6094b439e58252d0e7b60547439e18151d0e7a6094a439e5825290e7b60546439e1815190e7a60149439e5805250e7a60d45439e5835150e7962d41439e9875050f3a43141439e5885050e7a61141438fd954310eb86050c4397d954310e7a60948439e5825210e7b60544439e1815110e7962940439e9865010f3b4354043ce50d5010e7b62540439e1855010e7b6054f429e18153d0abb6050f42ae18143d0b1d5310f42ae98043d0ab96010f429ed8151d0a786054742ab58b53d0abb6054f42ae18153d0b1d5314f42ab58853d0aba6014f42ae58053d0a9e63d4742a758f51d0aba60d4742ae58351d0abb6054742ae181
  | 7 => 0x2850592511f325700018091280007000000010ea8924e19d8000e51c00df109838a28a1927821d19f8351078b41298b01d9a878ec26200000000000001a9ed9620c422d103a8d80b8000f002b04626fa128000ac1d0086000025a639d18a21de27411c9650fc0049eba800520000000001f900000011a0a68000002431899a3a280dc170000296000000214977a6a0000000e20001ba9ae0001290000e786a0499b780e0640000d382189c8c31998000000000000000001cba0888d8001cd23c8000000000002070000000002939258000001dd1858998000001220001919f013a88800000000013386590894b0689ad9090000458002180311d286b00ca420f126e9161a795815e9f480d0320f89ac01d8440721c320a12a1d300001c81b00026580000000000000080007a8000000a501e15700000000000016f18480027e800266a020000000730570000000970b08798000001750100000000ee17286da2f0088000a980023010d97b0800229232328000001d09ce1ce965a7508b08698404728f0128130d5a9d015a900001be8000000001bb8000000000001e60000000000000000bb00000029522a0bf0000000000768000000000000001d900013715a0000b20001c98002601f68ce83683a06e14f8000001e28361cc18b84f85d8000000002548000000000000d48000000000a92290be80000024b8ac91509408e15100000000012e800000000000000080a8180000009e14c01b8580002888000000000000e000000000019c00000019890c85e0000000000001fd00000008c13e022249187861a84a9980000000000000027b80019b82a9460000c920aa0f28e16d2120000001b812d0b48002409ae80f8f6a749769c08109e40a38001e483c034000000000110a2c1062150000001c895f1bc0000000000000001170000002048000000001f60078000000000000de00005d0000001eca5a92c0208000000000fa00019080000000000008f1958502399c7a919200000911db1710001b613324d8fb8dd00009880009c1ee08a0aa94d00000005880020191b00000000000000022693b0000000000000000c000000000029b8f18c50000e280011819680000005603180000013488a90680024c05b00011f9f7a4980002500020780021da968000f7a470ee80924280020b00025980003f80000000024821f80027e000000160222a688000000000001a892c8000b180000002300000000000000009b0001498000000000002340af1d892429f80015b193235832a410d20000001af8002298740000001d38000000150000030000001b184887a03b1cf25780000000016400004e89500000021a80000000000027c80000000000000000007d1da0000000a48060001d501e85e8001191aa23a2910000000000920000000001a9a2181f09080
  | 8 => 0x11e80000000000005a94e9f41798000000001980530000000788000002440001b0942a94a7783f13e918a1b0001960000000001d60000001452400000000000000cd25e10582880000000000000028f9b00002580fb00000006ca730000aea0c00000010500721380017da2080000021580023e93d0000e38990431ee9541001b20120000b620e00008500000000022500011e00007c0ef00005ca671cca050000002111850000c080000000000000015c00006d00010480000026412b000205a7f0002010000000000000248059ed11380000000025a00015d9490da00000004b80000021e8080ed07ba24250a5b969a550001c3a2f8000ec9280000000001c40ef8cf93927a99a80000000025f9a8246a6900000000022aa8c18a88986789d00000000000026d88d29c00007600000000000000002e18c00000000000000000002780000000012e0e900000028a0820cca36a30a2e0001198d300027a0000870000000000002648bda650e986f0000000002920e195a8000000001868001418000a70000000000000410000001528001738bb8c780000000013299a1e71880888cb0c81bf232157800000000000197a168002610000000f598f10186113611d09a2330001270001ff19c9fb80011aa6b00015180206f974a8e8000000b917ba3d00000000000000016700000028c9f38a80178419ef20ea0680010121f0001bb1301470001810000d89d583980000011400007395e2439d70000019910000281f2a820000000000000c629e9668000ad0511168b5a9a1e99bca0f98b0dc80020d0b30d1a6e0001ea05186812b9e581d0000ab80010820c8d90c10ca8000ed8000000002558000000000000000000000000000000000000be00000000019d00c25b27580002c0000001be1d215c80000020021a1ac8001770000000000000d08f29870d70000000000000000000000000348bc115a3f29c80000000000000000000016c00012280003810c06719380000013f81c0000000002981a426196ea8d17d1538000002930001120002258001cd8001760001e19a625223da1c8000000000c28000309a4a7b00009b8948ea00000000001805481a0cf0000000818002660aa26f00000000024f80016800000000010e07d8000000bf8000001f100000000000002d98e8000f400000000000000000014e14b8000000000ad84d18e1430000000000000000cc00003e28b8001389bd1dc0001b70000000002008718e08b805c0960000000b28db9b58001e006304000022c8001c580000000011da769fe1ba00025c06600020d983a73a3c23e1ad0000000000b10000000000000001f70a18001148000558468000000001029e7a248000828002448830000000e827092f29a95ba3700000008913a0000001731b28000262880000001b3800
  | 9 => 0x628400018c9448000000000001860199380000000001250dd8b500006928680000009f0000000000000000000000000000000000002760000000038000000000000000000002808000002478000b6a271c4a450841f8214221000000000161171a9082b88580005380018886000000008ba23a390000000001a28000000cb8140000000550001fa8000002680000000f49638001d100024600000019f0000000000000c48e1297a1980018293c92601623b1f50a40979268001399358001b48000000000000000001408000000b7000000000145a160000000001fea790000001c680000000000000000003d1a100000000000019b17c89a86200000000000010a0001100330000002380001a204a8001d40509819a09c918d8000eb818a7d87803718f96d88125d88e827154a7224c936a560000c38000000000000e40000000268ba0c580025000023780009f95983b8000599c100000000000000028b00014696b00000000000010b00000028628710f269a9e07b02e86b9591132098000001921fc11780f14f1588001b880000027121c0a10449a90000000001e893509d96a8210148fc8d10d698d292970a2d8f506e837a318a59a01a500da040bca63285a4b17901f8ff0ba92480011b9eb0000000000001f5a59000000000252aa00000a7a568490001508000000000001c600000000000006280018200000000007e0000000000001b69288000000001ef9890e6a4f0000000001fb11f00000000019e00000000027894792da8280005f00023880016187c9071e39c28000a2a810001f09a300007514400000002d0d40000919fd8000b981900993d95682399414d8ae00006508399280006480000017f9e10000ff8000298000a605a00000014a842a9d80022e8001008001ab0000ea80004e00029b00000000000000000029700025ea991b50010b383e8de8000af9559bd9218001660002080000001b10000790001520001ca00000020304521700004800000001180000004c0001530001cf9e08000fe0000000000001648728000000002360240c19a70002608db0578000001900002958000001b30000000000001311041a180008f8000000391830b79f993f05f8778001c200026d0000001a587f80500003a80027f9ff8931110001021cb127a4d04c8f914806c2178a012091185400016e1411239c18000f209580017e8028980709bf97a1e697c0000002338000000478000759e300010aa091678000d780015d00000019497f14ca4a00000b00019e8000eb00e80025421b92a80017880000000007e8d000003588ca20000000234800000040a6ca6a8d98c680000000025f0000000000000001991e52278301690000000000000001fa26797200a80022b27716327280000000000000000023f82a2718000000000000000938000
  | 10 => 0x2838002221341608000ab0000848000000000000000000000000000000000000000000cd93780000014014884f21882f15613220b8001da9c700000013c2988001319950ce07496f8f72260001f19742519210e60000001aa96b8000001970290000f300000022300015505293b8d82108ca06aa700c9a62a89a53a8a9031628000001af1de8f08710df863a5d01700000000000012f80014394a0a08040608969d80f81fc98027c0000001d48000000000000000002350000000001db8000001421a680024e89004a0000000000000000000000e70e30000000000000a88000d2a459501eaa1e1dd8002060000000d50001f8a5c90f9b900a0f38001ec2039aba9425884380001397800018a21023123b8200169b402f9dc84200000004b00010d0fa8001e82798000000000e880007726c0000bd23a80013080021191c0110928fd80024a8002830b883397a80680000000007f00000000000017e16c80000000010ba9f2028001f203c8f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x98003018004a4e00086a00a0700000000000660000b400340000002e00001c0000004c00000000000000d65abe0000c800000000000090006e000e0064004484b00080004004009276c20012501488000000007e9c00000000d8002c0000dc006cc6d48e1e0000cc463800000000000000000078000000020c000052720000009e00b28ac46000006206000000aade009400000074ac10da008668282400d0000000000000007c00005e0000000000d2000026a6002254363e0096000000bc483c0a0000000000320000000000002ab6582042a45c1a00a2aec0ba7a56a8ca9a000082008c3a0016b8ce03010602060000010100070000000406060303000001020102010000070003000008000206c32a6b0087a16195358053d0b0cb1aa0286858614c6050d42a28e2a98a6a15187054c5350a54b94c029a85461cd5014142a60e2a80a0a1705424c9510cb14b1285286838694c6050e41a34e1a9ca720d1a73d42509070ca9ac0218832c9c76054c41c1aa6b10a620e1953580531065838ac1290838a549608c841960e2b046420e19635405010714b12a0280838a5894294331a60e2a14a198e8462105310c6633b66498c438514c6150921a60e2a10a090e0d535884108694b9082a80438ad895250040c60c328a802053271d5040cc294b90a8a04610b5c86510530868e2b2a841843876551300c28cb98a8a044186591530c220c32a8b18a9106196454c5388312b10a220a41461cd5410120a60e2aa080906186414d304828c39aa82a2414c1c55415120952e5320a6905187454c53482a838aa629a411c1c56510d20d4284b0864906c132584324829838a8428a41985885110520d42c5a888290629621444148350b10a220a41c89885110520c62c42888290721621444148310b10a220a412a5ca64cc520c64c828e62906306414621482543b28490a41a218d4248520b40e2a124290630641452148328318a290a41c85085148520a34e7aa081886186494d30c428d39ea92a621469d35394f10c52c5a908388529729512084312a90c2a1021465cc5450010a52e42a280086196454c300430caa2c62a0218a5516215010964e3b22a6086196454c5304324a9ac4298211a5c86550c10960e2b24a408661521854204294baca4a1021c854b6150810c52a430a8408721521854204319a90c2a1021a89486150810c62a430a84086a1521854204310a90c2a10212c1c5648c810c52c8a9464086296254841043503108298821701c9310c410c56c8a944208629645482104324b1aa4108212c5d84108410c62ca20842086916310421042d0b908210821c85484108410
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x71800640009280400102100c21521c5608c841c21621c54294331a218299051cc520c80631c54248520e00635085148520a2081591528c810c21655c84108410c81635c84108410c21765484108410e01635484108410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s4K6 (864+((h/16+packedAt s4K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s4K5 (31188+((h/339+packedAt s4K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s4K4 (56486+((h/448+packedAt s4K4 (51110+(h % 448)*12) 12) % 2362)*12) 12
  | 3 => packedAt s4K3 (5784+((h/37+packedAt s4K3 (5488+(h % 37)*8) 8) % 235)*8) 8
  | 2 => packedAt s4K2 (612+((h/3+packedAt s4K2 (600+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe07ff80fc1ffc30f83f0f87fc7c0ff0322767c
  | 1 => 0xfffffff001fffff003fffffff800fffc3ff87f
  | 2 => 0xff81fffffe0ffffffc00ff83ffff0fffc38f8f
  | 3 => 0x1fffffff003ffffff0003fffff003fc0ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2b0d88e2b262a703e0b83c65c646991b22363c
  | 1 => 0x45101121848500300151488a480822680cd855
  | 2 => 0x8224a24410282144a400952092920c9143028a
  | 3 => 0x1459448921018a994a6a0043252cc022b40d60
  | 5 => 0x1861870e39ce33ee738ce670063088c3fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0fcc8fcc8f8c0f8c0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437d53486f8a690f714d21ae29a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f799043ec32086fca210fdcc421fa18843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e817e52d02faa5a05f94740bea8e817d54902fca7205f54e40df21c81bc43902fca5205f54a40dfa1481bd42902fca3205f54640df20c81bc41902fca1206fd0240fda04817f53502f8a6a05fd4940be292817f51502f8a2a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081bd42102fca2207d94440bb288817d51103eaa2205d54440df20881bc41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fda0441f840883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920bfa8a417c51483f680907e10120fd18241f930483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43f681887e10310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f680087e10010fb88021fa10043ea20087e44010
  | 1 => 0x402018060080100c0d0000800000030010040100002004020080b0040e0000d0040400c0e0100d0000103000008020380c04c0100800040000102803004004190400100809002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1217e94242bd284857d5090bf2a1215e54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2197d94432bb288657d510cbeaa2195d54432bf28065fa500caf4a0195f54032fca806579500cafca7a0df54f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0df14941dfa1283bd42507ee82a0ef90541bfa8283fb50506f6a0a0df14141fc282837850506fca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea9063de320c7b86418df94431ef98863f6310c7ba6218fd4c431ea988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fdcc721fa18e437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21f799443ec32886fca310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53487bea690d7d4d21bf29
  | 2 => 0x38bd43e000d98004007f4001560006b4648822822950c8102520000002e0004b0ac8002940b4859442506d48488c1205c06b8000000011d05b04c000e0000000844910b709831c00000000224000c633a0f09a1c500027800184000094001030007dc4188f4463480017f08a2e83c9f20000000000016c000000002fa0809e914000000f703b0007f8f48870007650d000000000af8ff1844480011f00075c0017a31e738311c6000360921c913a134f38dd15c1442e9c4022744122372e807c7a8702dc7bc8423f26c160dda312420149387d0d6000b2a2230c0500006c2de000000004162840003020e000cd83a1e433cc29de1e8688d5800042060011e23307d06595a35e0009a8d943c39c1b1662ec000ad9824500009b8231265880524934e000001153be58ceb06a0001dc7e0a323c7804a0003a4694e79f042c8b4ee91a426150b09b62028ec5892638417d139bc084000bb9131e26f4001501ee8f8001990f8004001e132a0003fa020001584691141c000761ac0ea000000000002b4ea0fe4425f800035114298bc000000000a387b0004f8ed9a610a2105501e0003a80012e2700000012f062860fb0000000000000009e4f0e08b82328b80b16835c46c002060000000009f1480000000028033039000424000c49aa4823f4038c1302310060614022f0c40742543a0f6a250000010223c0521691900b43a648000df4561f8068000b8000001b01c63ccb00914201986199f1da0b0259c72e43002a8da3b0770a11731ca23850067000000b899a000148c589c00037864243322870318ab1667d482080436124458bf0504fc079e40006e4f515d00014c000ee2b8578001540000000a80029a0fc7200000054c241fb412138000862ce000218764723581c8693003351b1430128d01ea2a2147a0099b81768cce51b431c3880000000083c191b72d68d4c19942906f83d10e2f2380e41062640a8d1800000000590000082d4000000bc000a7800000000001300000011e80000048c0000045e0004906e2ea91cb6a460380cc5a2381a6000110003d6258548e1000000d20402a43e4780a7000000001970f0000000970c87e8f981b342000000a22a26780e80037e000000002402f9148ef42a2684c1902b0834f88fb31411c0010508c350a59f80001bd2410f1f0820001cb2ae000fe14915801c0b00c00018000040300c03004010000604c0100805000050080001c0102c0200c090000b000000080000804000080140400c030000400400064030000100404010020080100001000010281f01005004020000f02805000020a00f01404068030080200c2a004000081c0240d00817000010000100c0300c030680e01c010741c0280405c00000020000d0180000802028010180a11002044170000800c000200003c0000800038000000200
  | 3 => 0xc505e398d90950946a4389a811045ce80e924a0e0e689b32c1407d1e60ca8c0e992d3400ace1834406038578000002e4001311b60010294e256000f611d4882c0000000005b00010200061c001550000f8002204480009d000000340a300037400000110000634b4a172388b1210063f281c998f61b82a0000000ae000800ca418530672260001808c000000110689b12f60489d899034914000193265900ba400da4e48b20a21a000be00006e0008600000002001800398164ff8d528a794f198c0d05a8000730003ac40800000754ce0414287681
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1530874c6254c21d5185530863e6414c218f590530865e6314c219d984530867a6014c219e580530874d53cc8219b594320867565cc421d554f31087c732cc4219d5943108755530c421f10c8310875553884219bd9521086cc63484219dd9521086d46348421d554d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087586054c40c754e43102b96010c40d394e521034d5394840da982521034e5354840d354d521031d53d0840ae583421031d5350840cb94942103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103374254440cd50951103706054440cd54641102b96010440ae592401023f65500409ed9540102bb6550040ced9540102b86350040e694d40103995350040aed8940103aa5250040ea54940102b86150040ec94540103b151500409d98754cc27561d5330b618143cc33b5410330b658c40cc39a43103309b988548c26d62152309d984548c27561152308f992528c23d6494a308f992544c27b60551308f994544c31d6315130c7152434c25c6550d30ce153304c25e63150309b988540c26d62150309d984540c27561150309e594400c339541003097d95300c27b654c030ae191300c32e62953208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20cb95142c825e63152209758c548827661152209d584548827661d4e209d58753883395410220b658c40882f16110220ae19130882ba64c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d20ba982424826c65509209e99740483395410120b658c40482ea6210120ea50840482f161101209e19530482b8644c120ae993204827a60d50209798c540825d63150209b988540827661150209d584540823e6414c208f59053082766114c209d584530827a6014c208f992520823d64948209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108f99052c423d6414b109798c52c425d6314b10bc18141c433b5410310bc58440c43b241103109798c548425d63152109b988548426d62152109b98b538426d62d4e109798f528425d63d4a108f992528423d6494a108f992544427b60551108f994544433561151108f992534423d6494d108fd91534423c6454d109bd89534426c6254d108f992524423d64949108fd91524423c645491097d8d524425c6354910cd15241442746550510ce15220442786548110ce151204433854c41109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b588530423e64148108f590520425e63148109758c520427a60148109e594400433954100109e596100427765440109ed9510042b86444010
  | 1 => 0x589500079a80001b43c0aa0000000000000000c0001013e03800119f2b98006d832000001c87e000007e800001f80000053800028003b1de259c69e800000d23d0000005c5a07a4c000000b6960003e8008406000194001364d0190240100801008040240700421030030480600000000000080200c0701c000000001c000b4120040000001010090540804407004040000501402000020040001c0200c0100c0300400000020140d0000000003000040000b010000000000400024020800006801008000100c0000f00402000000000302007014020580100400034020040000c000040300c010340001801054000140f020010040103e7a6094b439e58252d0f3a43141438fd954310eb86050c4397d954310eb86050f42ced0a5090ab86050d42ae9824250a3f65508429bd954210a7b60553329e18154cca3f64543328f19150cca7a60d52329e583548ca7661951329d586544ca7761551329d185544ca7b60551329e181544cb673214532d58c8514ca7661d50329d587540ca7a60d50329e583540ca3d65950328f990540ca7661150329d584540ca7a60150329e580540ca5f654c832b5185320ca6f654c832b9185320cb365494432cd552510cb365454432cd551510cb573254432d54c9510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500ca7a6094b419e58252d073b4214141ce508505073a41141418fd9541106b860504419dd95411067a60d53319e58354cc6d4614cb319e983548c67960d5231b5584328c66e62951319b58a544c66f62551319b189544c67b60551319e181544c63e64149318f590524c67a60149319e580524c72e6414931cb590524c7656114931da980524c769601493197997324c74c52cc931d3149324c6d4614c931d914b314c74c528c5319ed81540c67860550319b988540c66d62150319e980540c679601503197596320c6d5610c831b558e310c65f654c431b3189310c677654c431b9189310c6d7654c431d5d95310c7c7624c431b5189310c7c4624c431b1189310c755524c4318fd91500c63c64540319e98354c867960d53218f99053c863d6414f219e98053c86796014f21d5d4c31c867b60552219e18154886e5610ca21f10ca3188754534c621b918931887c7324c6218fd91508863c64542219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d219dd85534865e6514d21d55845348676658c521d514e3148674654c521d514d31486e4624c521d514f214874c53885219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755
  | 2 => 0x10c0000000000001fe450a64488437800908008ba92859f600034002a00019827000669f4b21aa00000641ae1691c7009a140ce4183e6219e78880000000000000000000b282000ba000601960008a000008d000b80000025a590c468278a600000000000000000000000001dc00000a2a7c000ac9aab0002be06a0c61800112a66f8e4319785ea360002600206000f8220000019c580004614648866860f210a4aaf2468a83c9883621a908e1b8071ccab81e98104428e60a8f6ad950559ea5c9089b0da4816ab721e5c1ce4c80056a82848ca00000a6800158000590e0404e958000004c00070000928f2700000052a303a8a201a207a11eaa0cc8707c4a9001e18e04a94bd000000000000000000690006c0001a2e22e2c2b52662ba0e00000a929e12000000d4002b4290000000000000001f080800189e4710a8000009d00000000008001900094a960000064916b69d0608fe9d9ca5b000708084b8c25120468a8c00124b594c0a13c91000aa8226c8044b0e026228000001d8740e80000000002ec0000000140b324e002d80000088984001e0978d88b2e417aba208383426e562b846a8ea2248371da628000000c000b46b2326a000750002fa680000000000239d859a40000baaca725f0e2890005493a232641b02e000001a8000000000000000fcab0000b000851fc93000002265727e00000b18d6001d6002de5d286152f0b2ac000000970002805252102b409e082a25f8b01bac4a116212a3e8e91057a0a090bcb38c086a9c74aee7b890061a6000ee4e1ba7b1266f1c8b4af2000c8baa50000000517650a005518c3a0002516e4a
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x91429c4a83880a600c120000600a8000000058000078000000002240601a28d0000012314b22c029263915d4624c431d0ce83126218e8574189310c761380c498863b05c0624c431c88a63126310cc676cc93188722298c498a43911886154c21c8acb9966210d45750c8310862a3b2a690843c254d5250040e22a6a8a802072152545401029938ea820661461cd5410120a60e2aa08090689635084048350a12c220241469cf5410310
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1080c05755d0624c431c41755c0624c431c81745c0624c431
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
  | 5 => packedAt s5K5 (17772+((h/195+packedAt s5K5 (15822+(h % 195)*10) 10) % 774)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 550)*10) 10
  | 3 => packedAt s5K3 (1120+((h/7+packedAt s5K3 (1078+(h % 7)*6) 6) % 40)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83ffff01f1ff01e3e3f8ffff8e07e0033f67c
  | 1 => 0x7fc1f8ffe01fffe03fc7f1c07f007ff9ccc87f
  | 2 => 0x7ffe00ffffe1ffffc007fe007fff8ffe0f0f8f
  | 3 => 0x800000fffffe01fffff800007ffff007f00ff0
  | 4 => 0xffffff00000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x98c3011c2242206060982473823123011563c
  | 1 => 0x129441224648c0601a429089490424d0c4c855
  | 2 => 0x210092448805008a40052412124909220b028a
  | 3 => 0x629648914106534ac90002464964045700d60
  | 4 => 0x4431800e189989d93126493800180187aea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0feeaf8c0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x169598070d1a890e8187811d9704800a1502088d9e82899ba0189d131280939f1c0400119900001e1b030580050019800b16038f1c80081120948b9a1f8c178e140a8612068f8c900000000010800000078112081020200a0c0a4c40a001c8061808180017fd50057f54017f95005fd54015f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd48077f5200ff94807fd52005f54803fc52017fd0803fe42017f50803fc42007fcc803fe32007f4c803fc3201ffd4407fe51005f94407fd5101ff144077c51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff48210007f24108013fc2084009ff8842004fdc4210007f6210802fff65440177fb2a2000dfd9510004feca8802ffe65440077f32a200bff5951005dfaca8802ffc65440077e32a200bdf1951001cf8ca8802bff64440157fb222000efd91100057ec88802bfe64440057f322200aff59110055fac88802bfc64440057e322200aef1911001578c88802bff5444015bfaa2200aff95110057faa88802b7d5444015fe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a200bffd4d1005ffca68802ffd5344017fe29a200affd0d10057fc868802bfd4344015fe21a2000ffd8910005fec488027fe62440037f3122000ff58910005fac488027fc62440037e312200bffd491005efea488027fe5244017fea922000df5491004ff8a48802bff4244013ff212200aff5091004ff88488003ff3244013ff1922000ff4c91004ff8648802fff5144017ff28a2000df9451005ffaa28802ffc5144017be28a200affd0510057fc828802bf64144015fea0a200afd50510057f88288003ff3144001ff18a2000ff4c510007f86288027ff2144001ff10a2000ff4851004ff8428802fff5044009ff282200bff54110027f8a08802bff4044009ff202200aff50110027f88088003ff3044009ff1822000ff4c110027f86088027ff2044009ff1022000fe88110007fa4088003f92044009fe1022000ffc4110007f62088013fe1044009fb0822004ffd9410025feca08013fe65040077f3282004ff5941003dfaca08013fc65040097e3282004ffd9010025fec808013fe64040057f3202004ff5901002dfac808013fc64040097e3202005ffd501002efea808017fe540400bfeaa02005df5501002ff8a808013ff63040097fb182004ff98c10005fcc608013fd63040017eb182004ff18c10025f8c60801fff530400fff2982007ff54c1003ff8a608017ff430400bff2182005ff50c1002ff88608013ff62040097fb102004ff9881000dfcc408013fd62040017eb102004ff18810025f8c40801fff520400fbfa902006ff9481003ffaa4080037d520400dfe2902005ffd0810037fc8408017fd420400dfe2102000ffcc810037fc6408003fd320400dfe1902008bf9841003ffea20801ffe5104001bf2882007ff5441003ff8a20801f7c510400bffa082005ff9041002ffa8208017fc4104001ff9882000ff8c410007fa6208003fc310400dff9082000ff88410007fa420801bfc21040097f3002004ffd4010027fca008013fd5004009fe2802004ffd001002ff68008013fe4004009fea002004ff10010027f08008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x7fc21480037fb024012ffd4120027fca09004bfd5048009fe2824011ffd012008ff68090013fe4048023fea024004ff1012008ff08090003ff3048009ff1824000fe8c120007fa6090003f93048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048021ffb2e2010bfd9710087fccb8800efe65c4021feb2e2010bf59710087f8cb8800efc65c4011ffb262008bfd9310047fcc98800afe64c4011feb262008bf59310047f8c98800afc64c4011ffaa62008dfd5310047fca988023fd54c4011beaa62008ff15310007fec788002ff63c4001ff31e2000bf98f10007fac788002fd63c4001fe31e2000bf18f10087fea788043fe53c4021fea9e2010ff14f10047fe8788023fe43c4011fea1e2008ff10f10007fec588002ff62c401fff3162001bf98b10007fac588002fd62c401ffe3162001bf18b10087fea5880437f52c401fff2962010ff54b10006faa58803ffc52c4011ffa16200fff90b10047fa858803ffc42c4001ff996200fff8cb10007fa658803ffc32c4021ffa8e2010ff94710006fca388043fd51c4021fe28e2010df14710047fe8388023fe41c4011fb20e2008ff50710047ea8388023fc41c4001ff98e2000ff8c710007fa6388003fc31c401fff90e2000ff88710007fa438803ffc21c4021ffa862004ff94310087faa188013fc50c4011ffa062008fed0310027fc8188023fd40c4009fe2062008fe10310007fe6188013fe30c4001fe9862004ff0c31007ffe4188013fe20c4001fe9062004ff08310027fecb08012ff6584009ff32c2003bf99610026fccb0800e7e6584009feb2c200ebf59610026facb080027d6584009fe32c2004bf19610027fec908012ff6484009ff3242002bf99210027fac908036fd6484009fe3242004bf1921006ffea9080377f548401bff2a4200dff5521006efaa908037fc5484009ffb1c2004bfd8e10027fcc708002fe6384009feb1c2000bf58e10027f8c708012fc638401dffa9c200eff94e10077faa70803bfc538401bffa1c200dff90e1006ffa8708037fc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc628401dffa94200edfd4a10067fca50803bfd5284001bea94200cff14a1006ffe8508033fe428401bfea14200cff10a10007fe6508033fe3284001fe994200cff0ca10055fac30803bff518401dff28c2000df94610077faa30803bfc518401dbe28c200dffd061006ffc8308037fd418401bfe20c2000ffcc610007fc6308003fd3184001fe18c200cffc8610007fc4308003fd2184019fe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea042004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fd1
  | 2 => 0x30007fa641805bfc320c009ffb086004ff98430005fcc218013fd610c0017eb086004ff184300c7fea218063fe510c001bf2886018ff544300c7f8a2180637c510c02fffa086017ff904300bffa821805ffc410c02dff9886000ff8c430007fa621805bfc310c02bff9086000ff88430007fa4218057fc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba6018003f9300c009ff9006004ff08030027fecb10012ff6588009ff32c4003bf99620027facb10052fd6588009fe32c4004bf19620027fec910012ff6488009ff3244002bf99220027fac91004efd6488009fe3244004bf1922009ffea91004f7f5488027ff2a44013ff5522009efaa91004ffc5488009ffb1c4004bfd8e20027fcc710002fe6388009feb1c4000bf58e20027f8c710012fc6388029ffa9c4014ff94e200a7faa710053fc5388027ffa1c4013ff90e2009ffa871004ffc43880037eb144001ffd4a2000efea510007fe5288003fea944001df54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510013ff6188009ff30c4000bf98620027fac310002fd6188009fe30c4014ffd46200a7fca3100037e5188029fea8c4014ff146200a6f8a31004fff4188027ff20c4013ff5062009ff88310003ff3188001ff18c4000ff4c620007f86310007ff2188003ff10c4001ff4862000ff84310012fe6088009ffa844004ff94220027faa110013fc5088009ffa044013fed0220027fc8110013fd4088009fe2044004fe10220027fe6110013fe3088009fd1844004ff4c220007f26110013fc3088009ff9044004fbc822000ff64110013fc2088009fc1044012ffd9520095feca9004bfe65480077f32a4012ff59520095faca9004bfc65480077e32a4011ffd912008dfec890047fe64480057f3224011ff5912008dfac890047fc64480057e3224011ffd512008efea890047fe5448023feaa24011df5512008ff8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c69004bff5348025ff29a4012ff54d20097f8a690047ff4348023ff21a4011ff50d2008ff88690012ff6248003ffa924001dfd492000ffca490007fd5248003bea924001ff1492000ffe8490007fe4248003f72124001ff5092008fda8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf18520097fea29004bfe5148001bf28a4012ff54520097f8a29004b7c5148023ffa0a4011ff9052008ffa8290047fc4148001ff98a4000ff8c520007fa6290003fc3148003ff90a4001ff8852000ffa429000
  | 3 => 0xe2a4601bbf58e300fffea71807ffe538c03ffea9c601fff14e300f7fe871807bfe438c03dfea1c601eff10e30027fec518013fe628c0037f3146004ff58a30005fac518013fc628c0097e314601fffd4a300fefea518077fe528c03ffea946000df54a300eff8a51807bff428c03bff214601eff50a300eff88518003ff328c03bff1946000ff4ca300eff86518013ff618c009ff30c6000bf98630027fac318002fd618c009fe30c601fffd46300fffca3180037e518c03ffea8c601fff146300fef8a31807bff418c03dff20c601eff506300f7f88318003ff318c001ff18c6000ff4c630007f86318077ff218c001ff10c6000ff486300eff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230007f66118013ff208c009fe104601cffd95300e5feca980037f654c0013fb2a601cff9953001dfcca98073fd654c0397eb2a601cff1953001df8ca980737c654c0073e32a601bffd91300ddfec898003bf644c0015fb22601bff99130015fcc89806ffd644c0377eb22601bff19130015f8c89806fbc644c0055e322601bffd51300defea89806ffe544c037feaa2601bdf551300dff8a898073ff534c039ff29a601cff54d300e7f8a69806fff434c037ff21a601bf790d300dffa869806fdd434c037fe21a6000ffd8930005fec49806bfe624c0037f3126000ff589300d7f8c498006fc624c039ffa92601cdfd49300d7fca498073fd524c001bea92601aff149300dffe849806bfe424c037fea12601aff10930007fe649806bfe324c001fe992601aff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c039ffa8a601cff94530006fca298073fd514c039fe28a601cdf145300dffe829806ffe414c037fea0a601bff10530007fe6298003fe314c001fe98a6000ff0c5300d7fe4298003fe214c001fe90a601aff085300e7fea098013fe504c039fea826004ff141300dffe8098013fe404c037fea026004ff10130007fe6098003fb304c009ff1826004f78c1300d7fe4098013fc204c009ffb286004bfd9430027fcca1800efe650c009bf32860039f99430027faca18062fd650c009beb2860009f59430027f8ca18012fc650c009ffb206004bfd9030027fcc81800afe640c009feb206017bf59030027f8c818012fc640c02fffaa06017dfd50300bffca81805ffd540c02fbeaa06017ff150300cdfcc618063ff530c02dff2986018ff54c300b7f8a61805fff430c02dff2186017ff50c300b7f88618013ff620c009ff3106001bf98830027fac418002fd620c009fe3106004bf188300c7fea4180637f520c02bff2906018ff54830006faa418057fc520c02fffa106015ff908300bffa8418057fc420c02dff9906015ff8c8
  | 4 => 0x802fd6088401fe3044225ffd422112ffca110897fd508844bfe2844224ffd0221127fc8110893fd4088449fe2044201ffc822100ff8411088fff65484477fb2a4200dfd9521004feca9088ffe65484077f32a4223ff5952111dfaca9088ffc65484077e32a4223df1952101cf8ca9088bff64484457fb224222ff99121015fcc89088bfd64484457eb224222ff19121015f8c89088bff5448445bfaa24222ff95121117faa89088b7d5448445fe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a4223ffd4d2111ffca69088ffd5348447fe29a4222ffd0d21117fc869088bfd4348445fe21a4201bfd892100ffea4908077f5248403ff2924201ff5492100efaa490807fc5248403ffa124201ff9092100ffa8490807fc4248403ff9924201ff8c92100ffa6490807fc32484037fb0a4223ffd452111ffca2908037e5148447fea8a4223ff1452111ef8a29088bff4148445ff20a4222ff50521117f88290803ff3148401ff18a4200fd8c521007fa6290803f53148401fe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf1812111ffea09088ffe5048447fea824223ff14121117fe809088bfe4048445fea024222ff1012100ffe4090807fc204842dffb2e6021bfd973010ffccb9800efe65cc043feb2e6021bf597300b7f8cb9800efc65cc02dffb266019bfd93300cffcc99800afe64cc033feb266019bf593300b7f8c99800afc64cc033ffaa66019dfd53300cffca998067fd54cc033beaa66019ff1533010ffea79805bfe53cc043fea9e6016ff14f300cffe879805bfe43cc033ef21e6019ff50f300cfba879805bfc43cc02dffb166020ff98b3000dfcc598003fd62cc0017eb166016ff18b3000df8c598087ff52cc043bfa966020ff94b3010ffaa5980037d52cc041fe2966019ffd0b30107fc8598067fd42cc041fe2166016ffccb30107fc6598003fd32cc02dfe1966016ffd8730007fcc398002fe61cc001feb0e6000bf587300b7f8c398087ff51cc043ff28e6000df9473010ffaa398087fc51cc043be28e6019ffd07300cffc8398067fd41cc033fe20e6016ffcc730007fc6398003fd31cc02dfe18e6020ffc8730007fc4398003fd21cc041fe10e6021ffd4330027fca198087fd50cc009fe2866019ffd0330027fc8198067fd40cc009fe2066020ffc8330027f84198013ff658c0097fb2c6004ff9963001dfccb18013fd658c03f7eb2c6004ff19630025f8cb18013ff648c0097fb246004ff99230015fcc918013fd648c03d7eb246004ff19230025f8c91807bff548c03dbfaa4601eff952300f7faa91807b7d548c03df
  | 5 => 0x493115ffca4988b7fd524c401bea92622bff14931167fe84988affe424c459fea12622bff10931007fe6498803df324c457ff1926200ff4c931007ba64988affc324c45bffa8a622dff94531006fca2988b7fd514c45bfe28a622ddf14531167fe82988b3fe414c459fea0a622cff10531007fe6298803f7314c401ff18a6200f78c53115ffe42988affc214c401ffb026200bfd8131007fcc098803fd604c401fe3026204bf1813116ffea0988b7fe504c45bfea82622dff14131167fe80988b3fe404c459fea02622cff1013115ffe40988affc204c42dffb286228bfd9431147fcca1880efe650c451feb286228bf594310b7f8ca1880efc650c42dffb206227bfd903113ffcc81880afe640c44ffeb206227bf590310b7f8c81880afc640c44fffaa06227dfd503113ffca81889ffd540c44fbeaa06227ff15031155fcc6188a3ff530c42dff2986228ff54c310b7f8a61889fff430c42dff2186227ff50c310b7f8861885bff620c44dff3106201bf98831007fac418802fd620c42dfe3106201bf18831147fea4188a37f520c44dff2906228ff54831006faa41889bfc520c44fffa106226ff9083113ffa841889bfc420c42dff9906226ff8c831137bc6418803fd320c42dfe1906226f70c83114dfcc2188a3ff510c451ff2886200df94431147faa2188a3fc510c451be2886227ffd043113ffc821889ffd410c44ffe2086216ffcc431007be6218803fe310c401fb1886200ff4c431007ba6218803f5310c44dff9086226ff084310b7fec018803fe600c4097f3006200ff58031005fac01885bfc600c451ffa806228ff94031147faa0188a3fc500c44fffa006227ff9003113ffa801889ffc400c44dff9006226ff0803112ffecb10896ff6588401bfb2c42009fd962112ffccb1080efe658844bfeb2c4225bf5962112ff8cb1080efc658844bbe32c42039f19621127fec910892ff6488449ff3244202bf99221127fac910892fd6488449fe3244202bf19221127fea9108937f5488449ff2a44224ff55221126faa910893fc5488401ffb1c4200bfd8e21007fcc710802fe6388401feb1c4200bf58e21007f8c710802fc638844bffa9c4225ff94e2112ffaa710897fc5388449ffa1c4224ff90e21127fa8710893fc43884037eb144201ffd4a2100efea510807fe5288403fea944201df54a2100ff8a510807ff4288403ff2144201ff50a2100ff88510807ff3288401f79944201ff8ca2100ffa6510807fc3288403f61944201bf9862112ffea310897fe5188401bf28c4225ff5462112ff8a3108977c5188449ffa0c4224ff90621127fa8310893fc4188401ff98c4200ff8c621007ec6310803fd3188401fa98c4200ff0c62100ffe4310807ef2188403fb90c4201ff0862100fe84310803ff6088401ff3044204bf98221007fac110
  | 6 => 0x7bea04a233df10251196fe41288cb7c209442dffb2e6231bfd973118ffccb9880efe65cc463bf32e62039f9973118ffacb988c6fd65cc401beb2e62009f597310b7f8cb9880efc65cc42dffb26622abfd9331157fcc99880afe64cc455feb26622abf593310b7f8c99880afc64cc455ffaa6622adfd5331157fca9988abfd54cc455beaa6622aff1533118ffea79885bfe53cc463fea9e6216ff14f31157fe879885bfe43cc455fea1e6216ff10f310b7fec5988c3fe62cc4037f3166200ff58b31005fac59885bfc62cc4037e3166231ffd4b3118efea5988c3fe52cc463fea966200df54b31187f8a5988abff42cc461ff216622aff50b31187f8859885bff32cc401ef9966230ff8cb31007fa6598803dd32cc42dfe1966231ffd473118ffca3988037e51cc463fea8e6231ff1473118ef8a3988abff41cc455ff20e622aff50731157f883988c3ff21cc461fe10e6216ffd8331007fcc198812fe60cc401feb066200bf583310b7f8c1988c7ff50cc463ff2866231ff5433118ff8a1988abff40cc455ff206622aff50331157f881988c3ff20cc461fe106622fffd963117dfecb188bffe658c4077f32c622fff5963117dfacb188bffc658c4077e32c6229ffd923114dfec9188a7fe648c4057f3246229ff5923114dfac9188a7fc648c4057e3246229ffd523114efea9188a7fe548c453feaa46229df5523114ff8a9188b2fd638c45fffa9c622fff94e3117ffaa7188bffc538c453ffa1c6229ff90e3114ffa87188a7fc438c401ffb14622eff98a3100dfcc518803fd628c4017eb14622eff18a3100df8c5188bfff528c45fbfa94622eff94a3117ffaa5188037d528c45dfe2946229ffd0a31177fc85188a7fd428c45dfe2146200ffcca31177fc65188bbde328c401fe994622eff0ca31177b8651889efe618c45fffa8c622fff94631006fca3188bffd518c45ffe28c622fdf1463114ffe83188a7fe418c453fea0c6229ff10631007fe6318803df318c401fb98c622effc8631177f84318803ff608c401ff3046204bf98231007fac118802fd608c401fe304622fffd423117ffca1188bffd508c45ffe2846229ffd023114ffc81188a7fd408c453fe204622effc8231177f841188b7ff654c45b7fb2a6200dfd9531004feca988b7fe654c4077f32a622dff5953116dfaca988b7fc654c4077e32a622ddf1953101cf8ca988b3ff644c4597fb22622cff99131015fcc8988b3fd644c4597eb22622cff19131015f8c8988b3ff544c459bfaa2622cff95131167faa8988b37d544c459fe2a2622dffd4d3116ffca6988b7fd534c45bfe29a622cffd0d31167fc86988b3fd434c459fe21a6200ffd8931005fec498803ef624c40177b12622bff9893100dfcc498803fd624c457fe3126201bf18931007d8c498806ec624c45bffa92622ddfd
  | 7 => 0xa90e37f4154871bf20aa438df505521c6f882a90077f2154803be10aa400dfd8152006fcc0a90037d6054801be302a438dfd01521c6fc80a90e37d4054871be202a401dfc815200ef840a905bff65cc86f7fb2e6437ff9973201dfccb990dffd65cc86f7eb2e6416ff1973201df8cb9905bff64cc86d7fb266436ff99332015fcc9990dbfd64cc86d7eb266416ff19332015f8c9990dbff54cc86dbfaa66436ff953321b7faa9990db7d54cc86dfe2a66401bf98f321bffea79905bfe53cc86ffea9e6416ff14f321b7fe879905bfe43cc86dfea1e6416ff10f3200dfac599007ff52cc803bfa966401ff94b3200ffaa5990077d52cc803fe2966401ffd0b3200ffc8599007fd42cc803fe2166401ff8cb3200fbc6599007ee32cc803fe1966401f70cb320b7fec399003fe61cc8017f30e6400ff58732005fac39905bfc61cc86fffa8e6437ff947321bffaa3990dffc51cc86fbe28e6436ffd07321b7fc83990dbfd41cc86dfe20e6401ffc873200ff84399007ec21cc82dffb066400ff98332025fcc199003fd60cc8017eb066416ff183321bffea1990dffe50cc86ffea866437ff143321b7fe81990dbfe40cc86dfea066436ff1033200ffe4199007fc20cc86bffb2a6435bfd95321affcca9900efe654c86bfeb2a6435bf595321aff8ca9900efc654c869ffb226434bfd91321a7fcc89900afe644c869feb226434bf591321a7f8c89900afc644c869ffaa26434dfd51321a7fca8990d3fd544c869beaa26434ff1513200dfec6990d7ff534c86bff29a6435ff54d321aff8a6990d3ff434c869ff21a6434ff50d321a7f88699006ff624c803ffa926401dfd493200ffca499007fd524c803bea926401ff1493200ffe8499007fe424c803fea126401ff1093200ffe6499003ef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003fe614c801feb0a6400ff18532005f8c2990d7ff514c86bff28a6435ff545321aff8a2990d77c514c869ffa0a6434ff905321a7fa82990d3fc414c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c86bffa826435ff941321affaa0990d7fc504c869ffa026434ff901321a7fa80990d3fc404c803ff9026401ff0813219efec9288ce7f6494467bf324a233df5925119cfac9288cf7c6494401bfb1ca200df98e51006fac7288037c6394467bfa1ca233df90e5119efa87288cf7c4394401bfb14a232df98a51006fac5288027d6294465be314a233dfd0a51196fc85288cf7d4294465be214a200dfcca51196fc65288037d3294465be194a203df9865101cfcc32880f766194467bfa0ca233df9065119efa83288cf7c4194465bf90ca232df08651006fec1288037e6094401beb04a200df1825119efe81288cf7e409446
  | 8 => 0x100800080000100600080580480000c80e80280d80100b80000100080900a00300500300a80000380580000080000480200280580000301700400000000080280080080000000080401000000180280c80080880200280600103d00180b00080280d80080180100480000280080000180080300280000880d80700000080480080681580180000000180080080080080880000380100100480000200000100080000280580000000100100080100100480e80f00000500000a80500000100180080900700400000000400000000700380000400100280480180000080080180100400380b00000000080280400300680280480000500580700000080100a00a00080180a80400000000200000480600480000a80000080000080000000000200101000081c80200480280080280000000480200001f80c00380000000500080a80180380e80000800080380000300280180080700280300100a80000080000000000800100380001081500000480300000100500000400000000000100000280d00200000400a80080100080580680080400000000000000480080000300300080000200000c80000c00200300980080100700d00080000080000100101200200100401000380480100281300000080880000480280001300080000200380000380280900000200180300000200080180180000080180000000000180280180100000380180080980080000280500880000000100000280280200480280000000400181200080180500880000400080d80580100380400400000000000100080080000180000100500080680200980000180800180000200700000580000100280000480180a80200200080000100000281680080200180180000000000081400380100180180600180200200000200380600001700200000600480000080600000b00000001200380c00580c00000180180400580980300a80100080080000080200b00300a00480680300000280080580000000380400000600000000080180480d80100000100800c80000280300200000080f00000080180000600300000180200a00000000000100180080080000200000000580380000280600000080480000080000000000000280500100580280780100780080080180080400000680000000280080000000000100580400180180100f8010000028010008010010008000150000030008000008000000010038008008010000150030000020030e37f64548713fb22a438df991521c6fac8a90e27d6454871be322a400dfd8d52006fcc6a90037d6354801be31aa438dfd0d521c6fc86a90e37d4354871be21aa401dfd895200cfec4a900f6f6254803bfa12a401df9095200efa84a90077c4254803bf192a401df0c952006fec2a90037e6154801beb0aa400df18552004f8c2
  | 9 => 0x3b0005436fa06255400000000000041c64e1690000005bb51e5b11230007062da0ff06a2972a13f833b04a0740001226622735473246382a517a3f93f53230ea54950c65164c0710000000006832fd2f031b36300e6776bf3b40b31092c621c55c60648763660f14a08931c66b41220b07957b69c4d13395f52d924028b5444803f35a54711a90e91a418621b00002f1da6e848c39a5266df0006cb10c3455f91c605e3ca6f71ca6ed0375976d51c45b007b3000005e10000000000002711f606000001844900000000060259b2433ce69a18c4ab40b4151e36ec0000003d06b55c30000e73a32d70000005250001af0000250f30004f300000000065f2cb4cb0002192e226800000030c52e00000000050b19a00004222503a3cb6ee26e0be4890001924040000002690000006b800045d5ea19f5751bb1304ec44113100000051b0004f60005630d80002090003255aa32600059000000000000000000005a6a200000053163b3dd0000000004543075b76af16315b00038201c5650c100053c4761d50001462ee0003af30818a2ef2f136600017d25e0000000000000220000000000001765583b70661ed1813043945160a200025f0ab62d01a1b10000005a426d00036f4845ad3d400061567445e0005e55fb14200017834202d3813a00d900002c0001454c83430770d61133651335331124901325184e45395120640c54a53ba7026fb1f14920005910001f346870429202b4dd0000004e800005430e00015c02165811914b0015222df0f040961a0000000005da35f0000006dd3e000024900003262e4280000005ab00048557e2e00005460f122200000052100004b0006e33625c13344b42662233972673e304714e5ee0002c303d61e5175cd47c0310c94ac52935849a39d66c6042c405250f4704c22fc0cd26c5983882f30006ab29c1083c32f228a39528e5f450037e6705f21f06426ac4fc54168b4ae47928823f49961c67a0023ad1912b73875281e409a10b1c945034c65518401768848a6bb2f55614244961ad1010000366d82ab2ff38a31d5ef0c43a631e5d54573cd0002a423824200037d4656f50000002021e80af2bb00000008452d39c00000001664b67e00063c00000050a0000004512c90000006003b20fa2952e94462452c14f138940727f1ab5d40dc50d0bb0bd0394100003e208f50e0003d222c0b74030000000001a60003c83b142c00000063e4010000005090005510140000004300003a85301c36104df5be0005dd1b229917e0004530b05fe0000206792116a46b341968a05b5594a31ff0a606b6a10765885ca6a86c800000019769f0000002ca4620000004e20001493932bf1b55071890000000002760004581eb0000000000000005e03b60050003aa0676bc59c51546e0000000005f71d90951fb20f000004
  | 10 => 0x5b60d52d43ed6250000e41551b41885790706353eb0004360004147050000002800001564020000002156b05824750004470001c038e00047e46600000000000032f46a3306280002860000004646b70294e645a49126a6930001a227e00016e00013641700d13712d62442148812c3f23de0004b90440005fa35e2966da6440006a038000000000026b3440000720000484a14bb0000000003720000000003cc2bc6cd4b20b600069b26f2b551f54b00000016728f6ba69855018517100000053e0ec00000421828500c0006dc6eb3771073f61ee3863795d92fb5b537f0cc5420004d629b5010095cb53666e5cf5532e123e34d4b74fd08a3ff6492525c936b0c342959e5f31610236e13290122533f431114140a32a4d90f211c2af0d047229a5236274ce0003c15e80003a424c69d3730002502243850000002ea1f23174a41be36a0153fe12a3151bd57f5195061280fb5c01e63352540c04cf49f23240825144a25a3c407306125800056042e55b00066425509922d06d6ad4c665927b2333c908d0000005bf11d09136900064340f67b00061f08b31200029f3592c70bc6326375086f45a76a56db27a0d72b33610a50e324d0582d36675725b46c633d6950a91dc0006896e95d648e41d21300000040e5563dc00000000000000043738f6190000000006b239e5380002a267f30600034a6f92f600064f00010267305d54a0003050004130002fe0a365c5b80006d93ec1d30eb6c00800003646b12391df27805f2db00043510a0000003ea00055e0000d320328421d0000000000000003912644f42411d757c0000005870f855f3fc2e71c749814300057800000057610d5a226522a0960003410000453e932d00046904132e5350c85f06920003010002a66974b600000065353b47f0002310006166b659615d5f60002440000000004160000003d14830100783471ac0002de0006145574cc00000033f53f0000591746914a90006cc0000000000003bc3e761d6130000000003576b96de0004180000000ef0000000002e46d63fd4a20000004526fd1440003505041aa2002210005320000f50b93272d01ec4bf0db0d230a00016c3760652dc3285ce44b46c68646368f0ed0002275e92f46c465a4fe3461401002061a058444221f4f86221641600001d00001fc35c01300014818f5ed67d3563f715e6396842370000633c60002ae0000000004943144d407544d4eb5e42ed3706210342810fe04917c6ae12749d56235b38d0f40b22572820692e36803512301050a75d25b96304fa54c4c529056c4a82f92264a71241a81984ef4934c919512501f6094e119d4c309052b62615323c1042c533c5c80881fa00000011a30f0aa56b5fd0005940000573df00029e6122f800059f0000550004e30510280ae00000000000000024a3600002
  | 11 => 0x5bc19c0002c86f21db2c035a00047d56f0000002dd6786766bd0ee7036aa4393f162f11e64515f11f5806505df4260004555e26c10003b551d4d022035400060d0002341e90001bf37c00033700045917357307d4b163443d3e64002f75ba0b42b957d66a44067205c4d810309c5a023554d1f72a93b86e40c73843ae1f51c843c69e00023a4f55866030004c43a755256d2be00000312100049e00007c3e837b00003f0680002d517500055a0e500068e1540000001200003750000000004db00058500009f00059a1ea21600000000065d4f200000000000056938315a3a20001ae0006d20006900004811a504d00007a00015266664100045b12e25c3d356a59325d16612f0000002cd1a13135b24325110d17012ad0852aa1266d003b45c33364d0000000006e00005673a94c10000001d400016525600000a5e60001ce18d00013c6690003ef58a27513d0000006540001b834e2046ca1de49b5a60501596d34b819e0001c536d00050300047762b56629365700000016b4f946d4cd0002d25951ef0000001990004430000b10003ab0000000c25af37100058d4345eb00016a0004ff0004c05c600018048b1e100047a46f4ca0004970000000fc4ed64a2eb27d00041b00000054f0002d10000e256400070000022e0006a930b1176a64d30005e32bd33865b2120001bc11b6876483d94dc31003324706c4254fb3e461717b02a20146760e00b6053480c620c1506be29d24b0076945db0264e70241386854d20006fc16f37438c0ac0195de0e13ac5fc3f01396f633a1c20000000566521ba1e221068c0de4b336851c0822b167560800f0e628314f5205d300004352a4220835023fa2e56111871d11d20f666043f2d66815a900058f66156e6e64b051a0001722b821722843b2b60000006ef0ca5480000004d728c00036762953d66f6d14bd0001cb0000000ce4da1f460100009b5cc14d2d80e801b1c100000000037a0005ae0004af00041100000000000015821a0002b249c0001d80000006cf0006ce0005550000000006403c00002741933a100042a3cf0000941d663338b3b319b41f09e0303183fb5370001e74a65990000000006b439f3a512b0000000005926654ad5700000000000002a80000003be5f85ac42f3bb5ff01151443125b2984be55d6c240500004063f1145273c208e4486561151dd06f27c4de00066818b3db26000054e2a000062c0001b73021cf0b83031a736e2363d713a4f70006c75c253442000028913b1fd1776a35896c926104e00017900050500000000039600060c00000000000048663d0003360000000530000001b60a12070002a300003c0000000005812cc1351342a700030d0000006c343824e00011858c0004335e70001e05c40001cc00064600017f00000040c3b024854524f1966960003ee00
  | 12 => 0xdd4e543a0002051a332100032b32232c0005100a400039200000000000060b00046b07e5a13325a348f09d4950003b957a6f13194aa0d431a00043e1f846140d0000002b44b50004270000000000003530000003d808c00000000000000010e59d6e247400000014c00010f67c0005c70003905c56310000000060000000a01b93e539b2cf6ea65e0df4736ff0b51fe5a866d00016d4820005d11f93c500000000000020d0004ba0000000000006f835229400004f00013e0465831100006d713f1110000cb00063a1826470005f100000029168d5b315701d2080000005d000000008128d4781e500000000056844f42d01e62353a27218e35d60a4d545658b5401cd04c2ac5d83310cf08734b44506e19003e00000016234f45f61842307f0002b044e0003491b05130003785770000350002c20932ec0bf6fe5d76c56e736c4e95ec4bc44462a3bf3d56e526248d33e27058e0e01832ce20e14731f4060da1062fa21e3200002e647b61b6f04e06822632e80f96a74ee09220a52c0fd4f00ba12923d4c702e0f722b6d422f0380866633162772870003bd5bd0a80006f344c2290003c700034069909800025942b41a1683094601160000003984ea5dc41e4a06072141b32ba57135552467102752f2461941510000000083d63e10ad0972793da399574000170000620
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7458810004fd7458810014fc74588100067f54588100067d5458810004ff73588100b4fc7358810026ef72588100367f5258810036ee5258810006ed5258810036ee4258810006ed4258810036ee325881000cff715881000cfd7158810034fc71588100067c5158810036ec2158810024ff7058810024fe7058810024fd7058810024fc7058810006fb4058810026f84058810026ee2058810026ec2058810026fa10588100067f76548102067e76548100067d76548102067c765481021d7f745481021d7d74548102067f64548101c67e645481020e7d64548102067c64548102067f63548100067e63548100067d63548102067c63548102157f725481003f6f72548102067f625481000e7e62548102076e625481000e6e62548100367d62548102076d62548100066d625481000e7c62548100057c715481007e7e61548102067e605481020f7b40548102077840548102077710548102077a10548102077510548100b4ff76cc810024fe76cc810004fd76cc810024fc76cc8100b6de63cc810006dd63cc810004ff764c810024fe764c810004fd764c810024fc764c810006de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c8100867f769441001e7e769441001e7d76944101e67c76944101fd7f74944101fd7d74944101e67f649441019e7e64944101ee7d64944101e67c64944101e67f63944100067e63944100067d63944101e67c63944100057d72944101e67f62944101967e62944100067d62944101e67c62944101f57e719441003f7671944100867e61944101e77a70944100077970944101e67e60944101ef7b40944101e77840944101e77710944101e77a10944101e7751094410004fd76cc41003d7e75cc4100057d75cc410004ff768c410004fd768c410006de638c410006dd638c410025fa708c410005f9708c410004ff764c4100057f754c41003d7c754c410005ef724c410035ec724c4100b4ff760c410024fe760c410004fd760c410024fc760c4100b6de630c410006dd630c410007d5310c410025fa700c410005f9700c41007cff7688410024fe768841000cfd7688410024fc76884100057f758841003d7c758841000eee6288410006ed6288410025fa7088410005f9708841007cff76484100057f754841003d7c7548410005df7348410005dc7348410025fb7644010006fb7644010004fb76440100077b75440101cf787544010007bb744401002dfa744401002df874440101dfb8744401002db874440101df7b54440101df795444010026fb6244010006f962440101cf7b5244010007795244010025fb7144010027f371440101d6fa6144010027f261440100077a51440101cff251440100077251440101cff151440101cf785144010007f23144010007f13144010
  | 1 => 0xc1100e67c654c110005bf744c110055bc744c110006bf644c1100debc644c110006df634c110006dc634c110005f7714c110005f4714c110027d8304c110027f0104c110005fa7688110026fa76881100077b658811024f786588110007bb648811009efa648811009ef86488110247b8648811009eb864881102477b5488110247795488110006fb6388110006f9638811004df9728811000efa628811000ef8628811004f7b528811004f795288110005fa7188110026fb6188110027f361881100077a518811024f785188110247f24188110247f1418811000cff764811004cfd764811000cfc76481100067f65481100967c6548110006bf644811008ebc6448110006ef624811000eec6248110005f77148110005f4714811004df8764811000ef8764811000cf876481100077b654811023f786548110007bb644811008efa644811008ef86448110237b8644811008eb864481102377b5448110237795448110006fb6348110006f96348110025fb7248110027eb7248110007eb624811000efa624811000ef8624811004fe8624811004f7b524811004f79524811004fea4248110237e94248110007f37148110005f87148110007f07148110026fb6148110027f361481100077a514811023f785148110237f24148110237f141481100067f65c41100867c65c4110006bf64c4110046bc64c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c411022f7865c4110007bb64c4110046fa64c4110046f864c4110227b864c4110046b864c41102277b54c41102277954c4110005fb72c4110005f972c411022f7b52c41100077952c4110025fa71c4110026fb61c4110027f361c41100077a51c411022f7851c4110227f241c4110227f141c41100b4ff7598c1001cfe7598c10004fd7598c100b4fc7598c100b4ff7498c10014fe7498c10004fd7498c100b4fc7498c100067f5498c100067d5498c10026de7398c100b6de5398c10006dd5398c100b6de4398c10006dd4398c1000cfe7298c10004fd7298c1000cfc7298c100067f5298c100067c5198c10024fe7098c10024fc7098c10026de3098c10026dc3098c10004ff7558c100067f7558c100047f7558c1001cfe7558c10004fd7558c1001cfc7558c100067c7558c1001c7c7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10026df7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c1000cfc7258c100067f5258c100b4ff7158c1015cfd7158c100067c5158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014f
  | 2 => 0x1c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df73589100b4fc7358910006dc7358910004dc735891004cff7258910006ef725891004e7f5258910064ff7158910006f771589100067c515891007cff7058910006fb70589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c765491026d7f745491026d7d74549102667f64549100073f64549100063f64549101c67e64549102667d64549101c67c64549102673c64549101c63c64549100067f63549100067e63549100067d63549100067c635491004d7f725491005f6f725491004e7f625491000e7e625491004e7d625491000e7c62549100057c71549102677641549102677541549102077610549100b4ff76cc910004fe76cc910004fd76cc9100b4fc76cc9100067f65cc9101be7c65cc910006bf64cc9101b6bc64cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101ae7c654c910006bf644c9101a6bc644c9100057e76945100767e76945100747e769451025d7f749451025d7d74945102567f64945100073f64945100063f649451019e7e64945102567d649451019e7c64945102573c649451019e3c64945100067f63945100067e63945100067d63945100067c63945100057d72945100067f62945101967e62945100067d62945101967c629451005d7e719451005f7671945102577641945102577541945101e7761094510024fe76cc51005d7e75cc5100057d75cc5100067f65cc51018e7c65cc510006bf64cc510156bc64cc510006df63cc5100b6dc63cc510025fa70cc510005f970cc510004fe768c5100067f658c51017e7c658c510006bf648c51014ebc648c510024fc764c5100057f754c51005d7c754c5100067f654c51016e7c654c510006bf644c510166bc644c510006df634c510006dc634c510005ef724c51004dec724c510005fb704c510025f8704c510004fe760c5100067f650c5101467c650c510006bf640c51013ebc640c510064fe76885100057f758851005d7c75885100067f658851012e7c6588510006bf6488510126bc6488510024fc76485100057f754851005d7c75485100067f654851011e7c6548510006bf6448510116bc6448510005df7348510005dc7348510006ef624851000eec6248510005fb7048510025f87048510004fe76cc1100067f65cc11010e7c65cc110006bf64cc1100cebc64cc110006df63cc1100b6dc63cc110005f671cc110005f571cc1100b4ff764c110004fd764c110004fc764c1100057f754c11005d7c754c1100067f654
  | 3 => 0xf74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d10006de32d8d10006dc32d8d100067c51d8d1005d7e7598d100057d7598d100067f6598d100067c6598d10055be7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d100b4ff7598d1001cfe7598d100b67e7598d1001c7e7598d10004fd7598d100b67d7598d100047d7598d100b4fc7598d100b4ff7498d10014fe7498d100b6be7498d10014be7498d10004fd7498d100b6bd7498d10004bd7498d100b4fc7498d100067f5498d100067d5498d100b4fe7398d1000cfe7298d10004fd7298d1000cfc7298d100067f5298d10004fd7198d100b6f57198d100067c5198d10004fd7098d100b6f97098d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10055bc7458d10006bf6458d10006bc6458d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d10004ff7158d10006f77158d100067c5158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d10006dd6318d100b4ff7518d1001cfe7518d10004fd7518d100b4fc7518d100b4ff7418d10014fe7418d10004fd7418d100b4fc7418d100067f5418d100067d5418d100b6de7318d1000cfe7218d10004fd7218d1000cfc7218d100067f5218d10006de3218d100b6dc3218d10174fe7118d100b4fc7118d100067c5118d10024fe7018d10024fc7018d1000cfe76d891005d7c75d89100067f65d89100067c65d8910006bf64d8910006bc64d891004eee62d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d89100067c75d891001c7c75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d89100b4fe73d8910004fd73d891004e7f52d891004eec32d891000cfe71d8910024fd71d891000cfc71d89100067c51d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d89100057f755891005d7c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df7358910005dc735891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c7558910
  | 4 => 0x82100077a514821028f785148210025f976c4210006f976c42100277a65c42100277965c4210046fa64c4210026f864c42102877b54c42102877954c4210005fb72c4210005f972c421027f7b52c42100077952c4210027f271c42100077a51c421027f7851c421005d7e76d951005e7e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057d72d95100067e62d95100067c62d951005d7c71d95100077641d95100077541d95101e77610d95101e77410d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95101e67f71d951005e7e71d951001c7e71d951005e7d71d951005e7c71d951001c7c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067c21d95100067f70d95101e67e70d951005e7d70d95101e67c70d95100067f40d95101e67e40d95100067d40d95101e67c40d95101e67e30d95101e67c30d95100067f20d95101e67e20d95101e67c20d95101e67e10d951005e7d10d95101e67c10d9510055be76d9110056be76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d91100073f52d9110277b771d9110057b471d91100073c51d9110277b610d9110277b410d9110006bf75d91100063f75d9110006be75d9110006bd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d9110276bf71d9110056be71d9110056bd71d9110056bc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d91100063c51d9110006bf21d9110006bc21d9110006bf70d9110276be70d9110056bd70d9110276bc70d9110006bf50d9110276be50d9110006bd50d9110276bc50d9110276be30d9110276bc30d9110006bf20d9110276be20d9110276bc20d9110276be10d9110056bd10d9110276bc10d91100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004f
  | 5 => 0x14fe7458e10004fd7458e10014fc7458e100067f5458e100067d5458e10026df7358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e100067f5258e10006de3258e10006dc3258e100067c5158e10024fc7058e10026de3058e10026dc3058e10026fa2058e10004ff7558a1001cfe7558a100067e7558a1001c7e7558a10004fd7558a100067d7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a100b4fc7358a10026ef7258a100667f5258a10066ee4258a10006ed4258a10066ec3258a100067c5158a10066ef2158a10024fc7058a10026ee2058a10026ec2058a102057f7654a100067f7654a100047f7654a102067e7654a102057d7654a100067d7654a100047d7654a102067c7654a102b57f7454a102b57d7454a102067f6454a101c67e6454a102ae7d6454a102067c6454a102067f6354a100067e6354a100067d6354a102067c6354a102157f7254a100776f7254a102067f6254a1000e7e6254a100667d6254a1000e7c6254a100057c7154a1004e7d6154a102067e6054a102077a2054a10207771054a100b4ff76cca10024fe76cca10004fd76cca10024fc76cca101be7e65cca100067d65cca1000eee62cca10006ed62cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca101ae7e654ca100067d654ca10005f7714ca10005f4714ca101e57d769461005e7d769461005c7d76946102a57f74946102a57d74946101e67f649461019e7e649461029e7d64946101e67c64946101e67f63946100067e63946100067d63946101e67c63946100057d72946101e67f62946101967e62946100067d62946101e67c62946101f57e71946100777671946101e67e60946101e77a20946101e77710946100757e75cc6100057d75cc61018e7e65cc6100067d65cc6100b6de63cc610006dd63cc610025fa70cc610005f970cc61017e7e658c6100067d658c6100057f754c6100757c754c61016e7e654c6100067d654c610006de634c610006dd634c610005ef724c610065ec724c610005fb704c610025f8704c6101467e650c6100067d650c610007d5310c61004cfd76886100057f75886100757c758861012e7e65886100067d6588610025f8708861000cff7648610024fc76486100057f75486100757c754861011e7e65486100067d6548610005df7348610005dc734861000eee6248610006ed6248610005fb7048610025f87048610025fb7648210036fb76482100277a654821002779654821008efa6448210026f864482102977b5448210297795448210026fb6348210006f96348210027eb724821000efa6248210026f862482100677b5248210067795248210067ea4248210297e94248210005f8714
  | 6 => 0xc7154b102cf764154b102cf754154b102cf7b4054b102cf784054b100b4ff76ccb10004fe76ccb10004fd76ccb100b4fc76ccb100b6de63ccb10006dd63ccb10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006de634cb10006dd634cb1001e7e769471001e7d76947102c57f74947102c57d74947102be7f649471019e7e64947102be7d649471019e7c64947100067f63947100067e63947100067d63947100067c63947100057d72947100067f62947101967e62947100067d62947101967c62947100857e71947100877671947102bf7641947102bf7541947100077a70947100077970947102bf7b40947102bf7840947100857e75cc7100057d75cc710024fd768c710006de638c710006dd638c710025fa708c710005f9708c7100057f754c7100857c754c710005ef724c71007dec724c710024fd760c7100b6de630c710006dd630c710025fa700c710005f9700c710024fd76887100057f75887100857c758871000eee6288710006ed6288710025fa7088710005f97088710034ff76487100057f75487100857c7548710005df7348710005dc73487100b6de63cc310006dd63cc310005f671cc310005f571cc3100057f754c3100857c754c310005bf744c310045bc744c310006de634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc764831000eee6248310006ed6248310005f77148310005f471483100067f74596100047f74596100067e74596100067d74596100047d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100047f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067d42596100067c42596100067e32596100067c32596100767f71596100767e71596100067d71596100767c71596100067f41596100067e41596100067d41596100067c41596100067f21596100067c21596100267f70596100267e70596100267d70596100267c70596100267f40596100267e40596100267d40596100267c40596100267f30596100267e30596100267d30596100267c30596100267f20596100267e20596100267d20596100267c20596100267f10596100267e10596100267d10596100267c10596100b4ff7598e1001cfe7598e10004fd7598e100b4fc7598e100b4ff7498e10014fe7498e10004fd7498e100b4fc7498e100067f5498e100067d5498e10026de7398e100b6de4398e10006dd4398e1000cfe7298e10004fd7298e1000cfc7298e100067f5298e10006de3298e100b6dc3298e100067c5198e10024fe7098e10026de3098e10026dc3098e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10
  | 7 => 0xc120027db734c120007db634c1200b6fa634c1200b6f8634c120007d8634c1202e7da434c1202e7d9434c120007eb724c12000dfa724c12000df8724c1200d7e8724c120026fb624c120027eb624c1200d77b524c1200d779524c1200d7ea424c1202e7e9424c120005fb714c1200077a514c1202df78514c1200857e75d8f100057d75d8f10045be74d8f10005bd74d8f10004ff75d8f1001cfe75d8f100067e75d8f1001c7e75d8f10004fd75d8f100067d75d8f100047d75d8f1001cfc75d8f10004ff74d8f10014fe74d8f10006be74d8f10014be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10014fc74d8f100067f54d8f100067d54d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f10006f671d8f100067c51d8f10006f970d8f10004fd7698f100857e7598f100057d7598f10006df6398f100b4ff7598f1001cfe7598f100b67e7598f1001c7e7598f10004fd7598f100b67d7598f100047d7598f100b4fc7598f100b4ff7498f10014fe7498f10004fd7498f100b4fc7498f100067f5498f100067d5498f1000cfe7298f10004fd7298f1000cfc7298f100067f5298f100067c5198f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f100067f5458f100067d5458f10006df7358f10004ff7258f1000cfe7258f1000cfc7258f100067f5258f100067c5158f10006dd6318f100b4ff7518f1001cfe7518f10004fd7518f100b4fc7518f100b4ff7418f10014fe7418f10004fd7418f100b4fc7418f100067f5418f100067d5418f100b4fe7318f100b6de7318f1000cfe7218f10004fd7218f1000cfc7218f100067f5218f100b6f67118f100067c5118f100b6f97018f1007eee62d8b10004ff75d8b1001cfe75d8b10004fd75d8b1001cfc75d8b10004ff74d8b10014fe74d8b10004fd74d8b10014fc74d8b100067f54d8b100067d54d8b100b4fe73d8b10004fd73d8b1007cfd72d8b1007e7f52d8b10006f671d8b100067c51d8b10006f970d8b10006fb40d8b10006f840d8b1000cff7658b1007eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b100b4fc7358b10006ef7258b1007e7f5258b10024fc7158b100067c5158b1007eec2158b10006fb4058b10006f84058b1007eef2058b100067f7654b100067e7654b100067d7654b100067c7654b102d57f7454b102d57d7454b102ce7f6454b101c67e6454b102ce7d6454b101c67c6454b100067f6354b100067e6354b100067d6354b100067c6354b1007d7f7254b100876f7254b1007e7f6254b1000e7e6254b1007e7d6254b1000e7c6254b100057
  | 8 => 0x1cfe75d85200067e75d852001c7e75d8520004fd75d85200067d75d85200047d75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d85200b4fe73d8520004fd73d8520024fd72d85200667f52d85200667d52d85200067c51d8520066f621d8520066f521d8520006f7619852004df970985200057f75585200957c7558520005bf745852008dbc7458520005df7358520005dc735852007dfb7058520006f56118520004ff751852001cfe7518520004fd751852001cfc7518520004ff7418520014fe7418520004fd7418520014fc74185200067f54185200067d54185200b4fe7318520004fd7318520024fd72185200367f52185200367d52185200067c5118520036f62118520036f52118520024fe7018520036f97018520024fc7018520006fb4018520006f840185200067f76945200067e76945200067d76945200067c769452030d7f749452030d7d74945202fe7f649452019e7e64945202fe7d649452019e7c64945200067f63945200067e63945200067d63945200067c63945201957f72945201957d72945201e67f62945201976e42945202ff6d42945203057e71945200977671945200067f61945200067c61945200077a70945200077970945201967f60945202ff7b40945202ff7840945201977b20945201e76e20945201e76c2094520197782094520004fe76cc520004fd76cc5200b4fc76cc5200957e75cc5200057d75cc520006f761cc520006f461cc520025fa70cc520005f970cc520004fe768c520004fd768c520004fc768c520006df638c520006dc638c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c520005ef724c52000dec724c520004fe760c520004fd760c5200b4fc760c520006df630c5200b6dc630c52000dee720c520005ed720c520006f7610c520006f4610c520025fa700c520005f9700c52000cfe76cc12000cfc76cc120006df63cc1200b6dc63cc12000dee72cc120005ed72cc1200adfa768c120026fa768c12008dfa748c120025f8748c1202f77b548c1202f779548c1200d5f9738c1200b6fa638c1200b6f8638c12000dfa728c120025f8728c120026fb628c120027eb628c1200ef7b528c1200ef79528c1200efea428c1202f7e9428c120005f9718c1200077a518c1202ef78518c1200b4ff764c12000cfe764c1200d4fd764c12000cfc764c1200057f754c1200957c754c120005bf744c12008dbc744c120006df634c120006dc634c120005ef724c12000dec724c12000df8764c1200d6f8764c12000cf8764c1200077b754c1202df78754c120007bb744c12008dfa744c12008df8744c1202e7b8744c12008db8744c1202e77b544c1202e779544c120025fb734
  | 9 => 0x840946201e77a30946201e76f20946201977b20946201e77820946200b4ff76cc620024fe76cc620004fd76cc6200a57e75cc6200057d75cc620025fa70cc620005f970cc620004ff768c620024fe768c620004fd768c620006de638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c6200057f754c6200a57c754c620005ef724c62000dec724c620025fa704c6200b4ff760c620024fe760c620004fd760c6200b6de630c620006dd630c620025fa700c620005f9700c620025fb764c220006fb764c2200077b754c22031778754c220007bb744c22009dfa744c22009df8744c22031fb8744c22009db8744c22031f7b544c22031f79544c220027db734c2200b6fa634c220026f8634c22031fda434c22031fd9434c22000dfa724c22000df8724c2200d77b524c2200d779524c220005fb714c2200077a514c22031778514c220004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d20024ff72d8d20024fd72d8d200ee7f52d8d200ee7d52d8d200eedf32d8d200eedd32d8d20004fe71d8d20004fd71d8d200067c51d8d20006df6398d200d5f97098d200b4ff7598d2001cfe7598d20004fd7598d200b4fc7598d200b4ff7498d20014fe7498d20004fd7498d200b4fc7498d200067f5498d200067d5498d200b4fe7398d20104fd7298d200b6ed7298d201067f5298d201067d5298d20004fe7198d20004fd7198d200067c5198d200d4fd7098d200b6f97098d200057f7558d200957c7558d20005bf7458d2008dbc7458d20005f77158d20005f47158d20105fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d200067f5458d200067d5458d20006df7358d200d4ff7258d20006ef7258d200d67f5258d200d67d5258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d200067c5158d20104ff7058d20006fb7058d200ecfe7618d200957e7518d200057d7518d20006dd6318d200b4ff7518d2001cfe7518d200b67e7518d2001c7e7518d20004fd7518d200b67d7518d200047d7518d200b4fc7518d200b4ff7418d20014fe7418d20004fd7418d200b4fc7418d200067f5418d200067d5418d200b6de7318d20024ff7218d2000cfe7218d20024fd7218d2000cfc7218d200ae7f5218d200ae7d5218d200b6df3218d200aedd3218d20004fe7118d20004fd7118d200067c5118d200b6f97018d200957e75d85200057d75d8520004ff75d8520
  | 10 => 0x84300067d6548430005df73484300b5dc734843000eee6248430006ed6248430006f66148430006f56148430025fb764c030006fb764c030004fb764c0300077b754c03033778754c0300277a654c03002779654c030007bb744c03033fb8744c03033f7b544c03033f79544c030025fb734c030027db734c0300b6fa634c030027da634c0300b7da534c030337d9534c030006f9624c0303377b524c03000779524c0300077a514c03033778514c0300b7db314c030007d9314c0300b4ff7598e2001cfe7598e20004fd7598e200b4fc7598e200b4ff7498e20014fe7498e20004fd7498e200b4fc7498e200067f5498e200067d5498e20026de7398e200b6de5398e20006dd5398e200b6de4398e20006dd4398e201067f5298e201067d5298e200b6df3298e20106dd3298e20004fe7198e20004fd7198e200067c5198e20024fe7098e20026fa7098e20024fa7098e20024fc7098e20026de3098e20026fa3098e20026dc3098e20004ff7558e200067f7558e200047f7558e2001cfe7558e20004fd7558e2001cfc7558e200067c7558e2001c7c7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e20026df7358e20006de5358e20006dd5358e20006de4358e20006dd4358e200d67f5258e200d67d5258e200d6df3258e200d6dd3258e20004ff7158e20004fc7158e200067c5158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20004ff759862001cfe7598620004fd759862001cfc7598620004ff7498620014fe7498620004fd7498620014fc74986200067f54986200067d54986200b4fe7398620004fd739862007e7f529862007e7d5298620026f671986200067c5198620006f64198620006f5419862007ef6219862007ef52198620024fe7098620026fa7098620024fa7098620006fb4098620026f84098620026f61098620026fa1098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620014fe7458620004fd7458620014fc74586200067f54586200067d5458620004ff73586200b4fc735862004e7f525862004e7d5258620026f771586200067c5158620006f64158620006f5415862004ef6215862004ef52158620024fc7058620026f61058620026f410586200067f76946201e67e76946200067d76946201e67c769462032d7f749462032d7d74946201e67f649462019e7e64946203267d64946201e67c64946201e67f63946200067e63946200067d63946201e67c63946201957f72946201957d72946201967d62946201f57e71946200a77671946200067e61946200067d61946201e77a70946200077970946201e67e60946203277b40946201e77
  | 11 => 0x267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430004ff755883001cfe75588300067e755883001c7e7558830004fd75588300067d755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc74588300067f54588300067d545883000cfd7358830026ef72588300ae7f52588300aeee4258830006ed42588300b6ef32588300b6ec3258830004ff7158830004fc71588300067c51588300aeef2158830024fc7058830026fa3058830026ee2058830026ec20588302057f76548300067f76548300047f76548302067e76548302057d76548300067d76548300047d76548302067c765483035d7f745483035d7d74548302067f64548301c67e64548303567d64548302067c64548301067e63548302157f72548300c76f72548302067f625483000e7e62548300ae7d625483000e7c62548300057c71548302067e60548302075f30548302077a30548302075d3054830104ff764c8301ae7e654c8300067d654c830004ff75984300067f759843001cfe7598430004fd759843001cfc75984300067c759843001c7c7598430004ff7498430014fe7498430004fd7498430014fc74984300067f54984300067d549843000cfe7298430004fd729843000cfc72984300067f52984300067d5298430026f671984300067c5198430006f64198430006f541984300b6f731984300b6f43198430026f61098430026f41098430004ff75584300067f75584300047f755843001cfe7558430004fd755843001cfc75584300067c755843001c7c7558430004ff7458430014fe7458430004fd7458430014fc74584300067f54584300067d5458430004ff725843000cfe725843000cfc72584300067f52584300067d5258430026f771584300067c5158430006f64158430006f541584300b6f731584300b6f43158430026f61058430026f410584301e57f76944300067f76944300047f76944301e67e76944301e57d76944300067d76944300047d76944301e67c769443034d7f749443034d7d74944301e67f649443019e7e64944303467d64944301e67c649443010e7e63944300057d72944301967e62944300067d62944301e67c62944301f57e71944300c77671944300067e61944300067d61944301e67e60944301e75f30944301e77a30944301e75d3094430004fd768c43017e7e658c4300067d658c430004ff764c4300057f754c4300c57c754c43016e7e654c4300067d654c430005ef724c4300adec724c4300b7d4314c430004ff7688430024fe7688430004fd76884300057f75884300c57c758843012e7e65884300067d6588430006f66188430006f56188430004ff7648430004fd7648430024fc76484300057f75484300c57c754843011e7e654
  | 12 => 0xe7418530004fd7418530014fc74185300067f54185300067d541853000cfe7218530004fd721853000cfc72185300067f52185300067d52185300067c5118530006f72118530006f421185300067f76945300057e76945300067e76945300047e76945300067d76945300057c76945300067c76945300047c769453037d7f749453037d7d74945303767f64945300073f64945300063f649453019e7e64945303767d649453019e7c64945303773c649453019e3c64945303775e43945303775d43945300057d72945300067f62945301967e62945301967c62945300e57e71945300e77671945300067f61945300067c61945301e75e3094530004fe76cc5300e57e75cc5300057d75cc5300067f65cc53018e7c65cc530006bf64cc530156bc64cc530024fe768c5300067f658c53017e7c658c530006bf648c53014ebc648c530006f7618c530006f4618c530025fa708c530005f9708c530024fc764c5300057f754c5300e57c754c5300067f654c53016e7c654c530006bf644c530166bc644c530005ef724c5300d5ec724c530006f7614c530006f4614c530005fb704c530025f8704c530004fe760c5300067f650c5301467c650c530006bf640c53013ebc640c530004fe7688530004fd7688530004fc76885300057f75885300e57c75885300067f658853012e7c6588530006bf6488530126bc6488530006ef628853000eec6288530004ff7648530004fe7648530004fc76485300057f75485300e57c75485300067f654853011e7c6548530006bf6448530116bc6448530005df7348530005dc73485300067f65cc13010e7c65cc130006bf64cc1300cebc64cc130025de73cc130026df63cc1300077b65cc1303677865cc130007bb64cc13036fb864cc13036f7b54cc13036f7954cc130025fa73cc130026fb63cc130027db63cc1300b7da43cc13036fd943cc130005f972cc1303677b52cc1300077952cc1300077a51cc1303677851cc1300067f74594300047f74594300067e74594300067d74594300047d74594300067c74594300c67f73594300b67e73594300c67d73594300b67c73594300067f43594300b67e43594300067d43594300b67c43594300067f72594300047f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c42594300b67f32594300067e32594300b67c32594300067f71594300067e71594300067d71594300067c71594300047c71594300067f41594300067e41594300067d41594300067c41594300b67f31594300b67c31594300067f21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300267e30594300267d30594300267c3059430
  | 13 => 0x9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91300063c51d9130006bf21d9130006bc21d9130006bf70d9130396be70d91300debd70d9130396bc70d9130006bf50d9130396be50d9130006bd50d9130396bc50d9130396be30d91300debd30d9130396bc30d9130006bf20d9130396be20d9130396bc20d9130396be10d9130396bc10d913000cfe76d89300e57c75d89300067f65d89300067c65d8930006bf64d8930006bc64d89300d6ee62d8930004ff75d89300067f75d893001cfe75d8930004fd75d893001cfc75d89300067c75d893001c7c75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d8930024fd73d893000cfc73d89300d67f52d89300d6ee32d8930004fe71d8930004fd71d89300067c51d89300d6ec21d89300d6ef20d89300057f75589300e57c75589300067f65589300067c6558930005bf74589300ddbc7458930006bf6458930006bc64589300d6ec6258930005f77158930005f471589300067f76549300057e76549300067e76549300047e76549300067d76549300057c76549300067c76549300047c765493038d7f745493038d7d74549303867f64549300073f64549300063f64549301c67e64549303867d64549301c67c64549303873c64549301c63c64549303875e43549303875d43549300d57f72549300e76f72549300d67f625493000e7e625493000e7c62549300057c71549302075e30549300ecfe76cc9300067f65cc9301be7c65cc930006bf64cc9301b6bc64cc930024fc764c9300067f654c9301ae7c654c930006bf644c9301a6bc644c930006ef624c93000eec624c9300d7cc324c930005fb704c930025f8704c9300e57e75d85300057d75d85300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d853001cfe75d85300067e75d853001c7e75d8530004fd75d85300067d75d85300047d75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d85300067c51d8530006f721d8530006f421d85300e57e75985300057d75985300067f65985300067c65985300ddbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530006bf6458530006bc6458530005ef72585300d5ec72585300e57c75185300067f65185300067c6518530006bf6418530006bc6418530006f56118530004ff75185300067f751853001cfe7518530004fd751853001cfc75185300067c751853001c7c7518530004ff7418530014f
  | 14 => 0x3b67d64946301e67c64946300e67d63946300057d72946301967e62946300067d62946301e67c62946301f57e71946300ff7671946300067e61946300067d61946301e67e60946301e75f30946300fd7e75cc6300057d75cc630006f6618c630006f5618c630025fa708c630005f9708c6300057f754c6300fd7c754c630005ef724c6300edec724c630006f6614c630006f5614c630005fb704c630025f8704c630007d5310c630004ff7688630024fe7688630004fd76886300057f75886300fd7c758863000eee6288630006ed6288630004ff7648630004fd7648630024fc76486300057f75486300fd7c7548630005df7348630005dc7348630025f976cc2300b6f976cc2303af7b54cc2303af7954cc230027da73cc2300b7da53cc2303a7d953cc230005f972cc2303a77b52cc2300077952cc2300077a51cc2303a77851cc2300e57e76d95300e67e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d95300057d72d95300067e62d95300067c62d95300057e71d953039f5e30d953039f5c30d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d953039e7f73d95300e67e73d95300e67d73d95300e67c73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067e32d95300067c32d95300067f71d95300067e71d95300047e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f21d95300067c21d95300067f70d953039e7e70d95300e67d70d953039e7c70d95300067f40d953039e7e40d95300067d40d953039e7c40d953039e7e30d95300e67d30d953039e7c30d95300067f20d953039e7e20d953039e7c20d953039e7e10d953039e7c10d95300ddbe76d91300debe76d9130014be76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91303979f73d91300df9c73d9130006be62d9130006bc62d91300073f52d91300073c51d91303979e30d91303979c30d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d9130396bf73d91300debe73d91300debd73d91300debc73d9130006bf53d9130006be53d9130006bd53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d9130006bc52d9130006be32d9130006bc32d
  | 15 => 0xe7558730004fd755873001cfc75587300067c755873001c7c7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d5458730024fc7358730004ff725873000cfe725873000cfc72587300067f52587300067d52587300067c51587300b6f731587300b6f431587300067f76947300067e76947300067d76947300067c76947303dd7f74947303dd7d74947303d67f649473019e7e64947303d67d649473019e7c64947303d75e43947303d75d43947300057d72947301967e62947300067d62947301967c629473010d7e719473010f7671947300067e61947300067d61947300057f754c73010d7c754c730005ef724c730105ec724c730004ff76887300b4fe7688730004fd76887300057f758873010d7c7588730006f66188730006f56188730004ff7648730004fd76487300b4fc76487300057f754873010d7c7548730005df73487300b5dc7348730006f66148730006f56148730004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a300067f5458a300067d5458a30026ef7258a300ee7f5258a300eeee5258a30006ed5258a300eeee4258a30006ed4258a300eeee3258a30004ff7158a30004fc7158a300067c5158a300eeec2158a30024fc7058a30026ee2058a30026ec2058a300067f7654a302067e7654a300067d7654a302067c7654a303cd7f7454a303cd7d7454a302067f6454a301c67e6454a303c67d6454a302067c6454a300d67d6354a302157f7254a300ff6f7254a302067f6254a3000e7e6254a302076e6254a3000e6e6254a300ee7d6254a302076d6254a300066d6254a3000e7c6254a300057c7154a302067e6054a302075f3054a302077a2054a300d4fd76cca30025f870cca3000cff764ca3000eee624ca30006ed624ca30005fb704ca30025f8704ca30004ff759863001cfe7598630004fd759863001cfc7598630004ff7498630014fe7498630004fd7498630014fc74986300067f54986300067d549863000cfe7298630004fd729863000cfc72986300067f52986300067d5298630026f671986300067c5198630006f64198630006f54198630026f61098630026f41098630004ff75586300067f75586300047f755863001cfe7558630004fd755863001cfc75586300067c755863001c7c7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d5458630004ff725863000cfe725863000cfc72586300067f52586300067d5258630026f771586300067c5158630006f64158630006f54158630026fa2058630026f61058630026f410586300067f76946301e67e76946300067d76946301e67c76946303bd7f74946303bd7d74946301e67f649463019e7e6494630
  | 16 => 0xc52116e7c654c521006df634c521006dc634c521005ef724c52100dec724c52100776514c52140f74514c52100df4764c52115ef4764c52100cf4764c52100777754c52140f74754c52100777654c52140f74654c52140777544c52140775544c521007d7734c521007d7634c5210b6f6634c5210b6f4634c521007d4634c521007e7724c52100df6724c52100df4724c52115fe4724c52115ef7624c52115f77524c52115f75524c52115fd7324c52115fd5324c521174fe760c5210067f650c5211467c650c521006df630c5210b6dc630c521175f6710c521007d5310c5210076f75885213f76c75885210076f65885213f76c65885213ff6f54885213ff6d5488521007cf6388521006ee6388521006ec6388521007cc6388521006cc638852100dee718852100fe6718852100eef618852100fe761885210076e51885213f76c5188521007e63188521007e531885210067f65d81210067c65d8121006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d81210b4fe73d8121004fd73d812107e7f52d812107e7d52d81210067e51d81210067c51d8121006fb40d8121006f840d812107efa20d812111d7e75981210057d75981210067f65981210067c6598121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f755812111d7c75581210067f65581210067c6558121005bf7458121115bc7458121005df7358121005dc7358121006df6358121006dc63581210067f65181210067c6518121006df6318121006dc6318121026fa6018121006f9601812100cff7658b300b6ec6258b30004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b300067f5458b300067d5458b30024fc7358b301067f5258b300b6ef3258b300b6ec3258b30004ff7158b30004fc7158b300067c5158b30106ef2058b300067f7654b300067e7654b300067d7654b300067c7654b303ed7f7454b303ed7d7454b303e67f6454b301c67e6454b303e67d6454b301c67c6454b303e75e4354b303e75d4354b301057f7254b3010f6f7254b3000e7e6254b301067d6254b3000e7c6254b300057c7154b300acff764cb300b7cc324cb300b6f76198730004ff759873001cfe7598730004fd759873001cfc7598730004ff7498730014fe7498730004fd7498730014fc74987300067f54987300067d5498730024fe739873000cfe7298730004fd729873000cfc72987300067f52987300067d52987300067c51987300b6f731987300b6f431987300057f755873010d7c75587300b6f46158730004ff75587300067f75587300047f755873001cf
  | 17 => 0xb6dc5318d21006df4318d210b6de4318d21006dd4318d210b6dc4318d210b4ff7218d21134fd7218d211367f5218d211367d5218d210b6df3218d21136dd3218d210b6f57118d210067c5118d21136ec2118d21024fe7018d21004fd7018d21175de7618d21006de7618d21174de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d211375f5218d211375d5218d21137d57118d210075c5118d21137d72118d21137cc2118d21137d42118d210b6df7518d21006de7518d21006dd7518d210b6dc7518d210b6df7418d21006de7418d21006dd7418d210b6dc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d210b6df7218d21136de7218d21136dd7218d210b6dc7218d21136df5218d211365f5218d21136de5218d21136dd5218d211365d5218d21136dc5218d21136df4218d21136de4218d21136dd4218d21136dc4218d210b6df7118d21136dd7118d21136d57118d21006df5118d21006de5118d21006dd5118d21006dc5118d210065c5118d21006df4118d21006de4118d21006dd4118d21006dc4118d21136df2118d21136de2118d21136dd2118d21136dc2118d21136cc2118d210b6df7018d21006de7018d21006dd7018d210b6dc7018d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d21136df2018d21136de2018d21136dd2018d21136dc2018d213057e76945214367e76945213047e769452142d7f749452142d7d74945214267f649452119e7e64945214267d649452119e7c64945210067f63945210075f63945210065f63945210067e63945210067d63945210067c63945210075c63945210065c63945211957f72945211957d72945211967f62945213057e719452111f7671945211967f61945211977721945211976c21945211977421945211e67c609452100cfe76cc52100cfc76cc52111d7e75cc5210057d75cc5210067f65cc52118e7c65cc521006df63cc5210b6dc63cc52100dee72cc521005ed72cc521134fe768c5210067f658c52117e7c658c521176df638c521006dc638c52100776518c52141f74518c521135f6768c521006f6768c52100777658c52141f74658c52141777548c52141775548c52115df5738c521177d7638c5210b6f6638c5210b6f4638c521007d4638c521006d4638c52100df6728c52100df4728c521176f7628c52117777528c52117775528c521177d6328c521177d4328c5210b4ff764c52100cfe764c52115cfd764c52100cfc764c5210057f754c52111d7c754c5210067f654
  | 18 => 0xe43d8d21006dd43d8d21006dc43d8d21174ff72d8d21174fd72d8d211767f52d8d211767d52d8d21176df32d8d21176dd32d8d210067c51d8d21024fe70d8d21004fd70d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d211775f52d8d211775d52d8d21177d771d8d210075c51d8d21177d721d8d21177cc21d8d21177d421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d21176df72d8d21176de72d8d21176dd72d8d21176dc72d8d21176df52d8d211765f52d8d21176de52d8d21176dd52d8d211765d52d8d21176dc52d8d21176df42d8d21176de42d8d21176dd42d8d21176dc42d8d21176df71d8d21176dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d210065c51d8d21006df41d8d21006de41d8d21006dd41d8d21006dc41d8d21176df21d8d21176de21d8d21176dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21176df20d8d21176de20d8d21176dd20d8d21176dc20d8d2111d7e7598d210057d7598d210067f6598d210067c6598d21006df6398d2115df57198d210b4ff7598d2101cfe7598d210b67e7598d2101c7e7598d21004fd7598d210b67d7598d210047d7598d210b4fc7598d210b4ff7498d21014fe7498d21004fd7498d210b4fc7498d210067f5498d210067d5498d210b4fe7398d21134de7398d21184fd7298d210b6ed7298d211867f5298d211867d5298d2115cfd7198d210b6f57198d210067c5198d21186ec2198d21024fe7098d21004fd7098d210057f7558d2111d7c7558d210067f6558d210067c6558d21185f77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21006df7358d2115cff7258d21006ef7258d21004ef7258d2115e7f5258d2115e7d5258d21184ff7158d21006f77158d210067c5158d21004ff7058d21024fc7058d21174fe7618d210067f6518d210067c6518d21006dd6318d210b4ff7518d2101cfe7518d21004fd7518d210b4fc7518d210b4ff7418d21014fe7418d21004fd7418d210b4fc7418d210067f5418d210067d5418d210b6de7318d21006df5318d210b6de5318d21006dd5318d21
  | 19 => 0xc6210057f754c62112d7c754c6210067f654c62116e7c654c621006df634c621006dc634c621005ef724c62100dec724c621007cf324c62100776514c62144774514c621185f7764c621006f7764c62100777754c62144774754c62100777654c62144774654c62143f77544c62143f75544c621007d7734c621007d7634c6210b6f6634c6210b6f4634c621007d4634c621007e7724c62100df6724c62100df4724c62115fe4724c62100de4724c62115f77524c62115f75524c62115fd7324c621007e7324c621007c7324c62115fd5324c62115fe4324c62100cff760c62100cfd760c6210067f650c6211467c650c6210b6de630c621006dd630c62100dee720c621005ed720c621137cc320c621007d5310c6210067f65d82210067c65d822112d7e75982210057d75982210067f65982210067c6598221006fb60982210057f755822112d7c75582210067f65582210067c6558221005bf7458221125bc7458221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221006bf7458221004bf7458221014fe7458221004fd7458221014fc7458221006bc7458221014bc74582210067f54582210067d5458221004ff73582210b4fc735822104e7f525822104e7d52582210067e51582210067c515822104efa20582210067f65182210067c6518221026fa6018221006f960182213057e76d952111e7e76d952101c7e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d95211957c71d95211977721d95211976c21d95211977421d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95211967f72d95211947f72d95211967e72d95211967d72d95211947d72d95211967c72d95211967f42d95211967e42d95211967d42d95211967c42d95211967f32d95211967e32d95211967d32d95211967c32d95211967f71d952111e7e71d95211967d71d95211967c71d95210067f41d95210067e41d95210067d41d95210067c41d95211967f21d95211967e21d95211967d21d95211967c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95211967f20d95211967e20d95211967d20d95211967c20d95210067f65d8d210067c65d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006d
  | 20 => 0x67f6598e210067c6598e21006df6398e210b4ff7598e2101cfe7598e210b67e7598e2101c7e7598e21004fd7598e210b67d7598e210047d7598e210b4fc7598e210b4ff7498e21014fe7498e21004fd7498e210b4fc7498e210067f5498e210067d5498e211867f5298e211867d5298e210b6df3298e21186dd3298e210b6f67198e210067c5198e21024fe7098e21004fd7098e210057f7558e2112d7c7558e210067f6558e210067c6558e21004ff7558e210067f7558e210047f7558e2101cfe7558e21004fd7558e2101cfc7558e210067c7558e2101c7c7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21006df7358e21006ef7258e2115e7f5258e2115e7d5258e2115edf3258e2115edd3258e2115eec3258e210067c5158e21004ff7058e21024fc7058e210067f6518e210067c6518e21006dd6318e21137cc3218e21175f67118e210b4ff7518e2101cfe7518e21004fd7518e210b4fc7518e210b4ff7418e21014fe7418e21004fd7418e210b4fc7418e210067f5418e210067d5418e210b4fe7318e210b6de7318e210b6ed7218e211367f5218e211367d5218e21136de3218e210b6dc3218e21174fe7118e210b6f67118e210067c5118e21024fe7018e21004fd7018e21006ed76cca210076f65cca2146f6c65cca214776f54cca214776d54cca2100dee73cca2100fce73cca21006ef63cca21007ce63cca21006ed63cca21007cd63cca21007e671cca21005ed71cca21007e571cca2100eee61cca2100fe661cca2146f6c51cca211967f76946213057e769462101e7e769462101c7e769462101e7d76946211967c76946214657f74946214657d749462145e7f649462119e7e649462145e7d649462119e7c64946210067f63946210067e63946210067d63946210067c63946211957f72946211976e72946211957d72946210076d72946210056d72946210076f32946211976c32946213057e719462112f7671946211967e61946211976f21946211977721946211976721946211977421946211e67e609462115cfd76cc62112d7e75cc6210057d75cc6210067f65cc62118e7c65cc621006df63cc6210b6dc63cc62100dec72cc621007cf32cc62100cff768c62100cfd768c6210067f658c62117e7c658c621006de638c621006dd638c62100dee728c621005ed728c621177cc328c62100776518c62145774518c62100df5768c621176f5768c62100cf5768c62100777658c62145774658c62144f77548c62144f75548c6210b6f6638c621007d6638c621007d5638c6210b6f4638c62100df6728c621177e6728c621007e5728c62100df4728c62117777528c62117775528c621007e7328c621177d6328c621177d4328c621177e4328c621177c4328c621184ff764
  | 21 => 0x4514c431005df764c431006df764c431004df764c4310075f754c43147f5c754c4314875f544c4314875d544c431007cf724c431135de724c431135dc724c431007cc724c431135cc724c431006dd624c43147f5f524c4310075d524c4310b5df714c43148ede614c43147fd7514c4310075e514c43147f5c514c43147fd4514c43147f54514c431487d6414c431487d5414c4310b5f7764c431006f7764c431004f7764c43100777754c43147f74754c43148777544c43148775544c4310b5f7734c431007d7734c4310b6f6634c4310b7d6634c43147fd7534c4310b7d4534c4310b7d6434c431487d5434c431007e7724c431007e4724c431006f5624c43147f77524c43100775524c4310b7d7324c431007d5324c4310b6fb6098031026f860980310057f75580311457c7558031005bf745803113dbc74580310b6f86058031004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc74580310067f54580310067d5458031004ff725803100cfe725803100cfc72580310067f52580310067d52580310067e51580310067c5158031006fa5058031006f95058031006fa4058031006f940580310b6fb30580310b6f8305803112e7e76d96210057f74d96210057d74d96210067f64d96210067e64d96210067d64d96210067c64d96210076d72d96211976c32d96213057e71d96210077671d96213057671d96211976f21d96211977721d96211977421d96210067f74d96210047f74d96210067e74d96210067d74d96210047d74d96210067c74d96210067f73d96210067e73d96210067d73d96210067c73d96210067f43d96210067e43d96210067d43d96210067c43d96211967d72d96210066d72d96211967f42d96211967e42d96211967d42d96211967c42d96211967f32d96211967e32d96211967d32d96211967c32d96210067e71d96213047e71d96210067671d96210067f41d96210067e41d96210067d41d96210067c41d96211967f21d96211967c21d96210067f70d96210067e70d96210067d70d96210067c70d96210067f40d96210067e40d96210067d40d96210067c40d96211967f20d96211967c20d96210067f65d8e210067c65d8e21177cc32d8e21135f671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e21004ff74d8e21014fe74d8e21004fd74d8e21014fc74d8e210067f54d8e210067d54d8e21006ed72d8e211767f52d8e211767d52d8e21176de32d8e21176dc32d8e21176ec32d8e21134fe71d8e21006f671d8e210067c51d8e21024fe70d8e21004fd70d8e2115cfd7698e2112d7e7598e210057d7598e21
  | 22 => 0xc531007cc628c531176cc628c5314f75f528c5310075d528c531007d7618c5310075e518c5314f75c518c5310067f65d81310067c65d8131006ef62d8131006ec62d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d81310067e51d81310067c51d8131006fb40d8131006f840d813116d7e75981310057d75981310067f65981310067c659813115dee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f755813116d7c75581310067f65581310067c6558131005bf7458131165bc7458131005ef725813115dec7258131006ef6258131006ec62581310067f65181310067c6518131006ef6218131006ec6218131026fa6018131006f9601813100cff76588310b6ec62588310b7cc3258831004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc74588310067f54588310067d54588311367f5258831136ee5258831006ed5258831136ee4258831006ed42588310b6ef3258831136de3258831136dc32588310b6ec32588310067c5158831136ec2158831004ff7058831024fc7058831136ef20588310067f76548310067e76548310067d76548310067c76548314ed7f74548314ed7d74548314e67f64548311c67e64548314e67d64548311c67c64548310075f73548310075c73548311867e63548311357f72548311476f725483100e7e62548311376e625483100e6e62548311367d62548310076d62548310066d625483100e7c62548311375e32548311375c32548310077771548310057c71548310077471548310057471548311767e61548312067e6054831184ff764c831135df734c831186de634c8310b7cc324c83117e7f769443101e7e769443101e7d76944311467c76944314dd7f74944314dd7d74944314d67f649443119e7e64944314d67d649443119e7c64944310075e73944310075d739443118e7e63944310057d72944311967e62944310067d62944311967c62944314cf5e32944314cf5c32944311457e719443114776719443117e7e61944311e67e60944310b75e75cc4310b75d75cc4314c75f54cc4314c75d54cc431135de72cc4310b5dc72cc431006dd62cc4314bf5f52cc4310075d52cc4310075e51cc4314bf5c51cc4314b5dd738c4314aede638c43100776518c43149f74518c4314a777548c4314a775548c4310b5f5738c4310b6f6638c4310b7d6638c431006f5628c43149f77528c43100775528c431497d6328c4310b7d4328c431004ff764c4310057f754c4311457c754c431005ef724c431135ec724c43100776514c43147f7
  | 23 => 0x6ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d89310057f755893116d7c75589310067f65589310067c655893115eec6258931005ee761893115eee761893115f6e751893115f6d7518931006ef65189310076f65189310066f6518931006ee6518931006ed6518931006ec65189310076c65189310066c651893115fae741893115fad7418931006ef6418931006ee6418931006ed6418931006ec64189310076f54189310076d541893115fcd731893115fe571189310076c511893115fea701893115fe970189310067f76549310057e76549310067e76549310047e76549310067d76549310057c76549310067c76549310047c765493154d7f745493154d7d74549315467f64549311c67e64549315467d64549311c67c645493115d7f725493116f6f725493115e7f62549310076f62549310066f625493100e7e625493100e7c625493115f6c625493100e6c62549310057c71549312067c6054931174fe76cc9310067f65cc9311be7c65cc93100eec62cc931005de76cc931176de76cc931174de76cc9310075f65cc9315375c65cc93153f5f54cc93153f5d54cc93115ddd72cc931007cf62cc93100ede62cc93100edc62cc93115fcc62cc93100ecc62cc93115f5f52cc93115f5d52cc9310b7d771cc931005de71cc9310b7d471cc9310b6df61cc9315375c51cc93115fcc21cc93100cfc764c9310067f654c9311ae7c654c931006ef624c93100eec624c931005f7714c931005f4714c93115ddc764c93100edc764c93100cdc764c9310075f654c9315275c654c93152f5f544c93152f5d544c93115ddf724c931007cf724c931007cf624c93100ede624c93100edc624c93115fcc624c93100ecc624c93115f5f524c93115f5d524c931007d7714c931005dc714c931007d4714c9315275c514c9310057e769453118e7e769453118c7e769453151d7f749453151d7d74945315167f649453119e7e64945315167d649453119e7c64945310057d72945310067f62945310076f62945310066f62945311967e62945311967c62945310076c62945311966c62945310075f32945310075d329453116d7e719453116f7671945311e67c609453116d7e75cc5310057d75cc5310067f65cc53118e7c65cc531006ef62cc531186ec62cc5310077651cc5315077451cc5310b77675cc5310b77575cc5310077765cc5315077465cc53150f7754cc53150f7554cc531005f572cc531007e762cc531007e462cc5315077752cc5310077552cc5310b7d732cc531007d532cc5310067f658c53117e7c658c531006ef628c531176ec628c5310075f658c5314f75c658c5314ff5f548c5314ff5d548c531005dd728c531007cf628c531176de628c531176dc628
  | 24 => 0xe7458231004fd7458231014fc74582310067f54582310067d5458231004ff725823100cfe725823100cfc72582310067f52582310067d52582310067e51582310067c5158231026fa6018231006f9601823116d7e76d953116e7e76d953101c7e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d95310057d72d95310067e62d95310067c62d953116d7c71d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d95310067f73d953116e7e73d953116e7d73d953116e7c73d95310067f43d95310067e43d95310067d43d95310067c43d95310067f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95310067e32d95310067c32d95310067f71d953116e7e71d953116e7d71d953116e7c71d95310067f41d95310067e41d95310067d41d95310067c41d953116e7d31d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95310067f20d95310067c20d953100cfe76d893116d7c75d89310067f65d89310067c65d893115eee62d89310076f52d8931004ff75d89310067f75d893101cfe75d8931004fd75d893101cfc75d89310067c75d893101c7c75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d893115e7f52d8931006ef52d89310066f52d893115eee52d8931006ed52d893115eec52d8931006ef42d893115eee42d8931006ed42d893115eec42d893115eee32d89310067c51d893115eef21d8931024fe70d8931004fd70d893115eef20d893115eec20d893115dee76d893100cee76d89310076f75d89310076c75d8931006ef65d89310076f65d89310066f65d8931006ee65d8931006ed65d8931006ec65d89310076c65d89310066c65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310076f54d89310076d54d8931007cf73d8931007e771d89310076c51d8931006ef75d89310066f75d8931006ee75d8931006ed75d8931006ec75d89310066c75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d89310066f54d8931006ee54d8931006ed54d89310066d54d8931006ec54d8931006ef73d893115eee73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d893115eee71d8931006ed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d89310066c51d8931006ef41d8931006ee41d8931006ed41d8931006ec41d8931006ef70d8931006ee70d8931006ed70d8931
  | 25 => 0xcb3100edc624cb311875f524cb311875d524cb31005dc714cb3159f5c514cb310057d769473116e7d769473116c7d76947315957f74947315957d749473158e7f649473119e7e649473158e7d649473119e7c64947310057d72947311967e62947310067d62947311967c62947310075f32947310075d329473118d7e719473118f7671947311e67e60947310067e65983310067d65983310b6fb6098331026f860983310067e65583310067d65583310b6f86058331004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331004ff725833100cfe725833100cfc72583310067f52583310067d52583310067e51583310067c5158331006fb4058331006f840583310b6fb30583310b6f83058331176ee62d8a31177cc32d8a3100cff7658a31176ec6258a31177ce3258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a311767f5258a31176de3258a31176ee3258a31176dc3258a310067c5158a31176ec2158a31004ff7058a31024fc7058a310067f7654a310067e7654a310067d7654a310067c7654a315857f7454a315857d7454a3157e7f6454a311c67e6454a3157e7d6454a311c67c6454a310075f7354a310075c7354a3115e7d6354a311757f7254a3117f6f7254a3100e7e6254a311767d6254a3100e7c6254a311775e3254a311775c3254a310057c7154a311367e6154a312067e6054a3115cfd76cca31175de73cca3100eec62cca3100cff764ca31175df734ca3100eee624ca31006ed624ca31177cc324ca31005f7714ca31005f4714ca3101e7e769463101e7d76946315757f74946315757d749463156e7f649463119e7e649463156e7d649463119e7c64946310075e73946310075d73946310057d72946311967e62946310067d62946311967c62946315675e32946315675c329463117d7e719463117f7671946311467e61946311e67e609463117d7e75cc6310057d75cc6310077651cc6315577451cc631005dd76cc631006dd76cc6315575e75cc6310075d75cc63155f5f54cc63155f5d54cc631175de72cc631175dc72cc631006dd62cc6315575f52cc6310075d52cc6310075e51cc631557d651cc6310075651cc631557d551cc6315575c51cc631005f576cc6310b6f576cc6310b77675cc6310b77575cc63155f7754cc63155f7554cc6310b7d653cc631557d553cc631005f572cc6315577752cc6310077552cc63117d7e75d82310057d75d823114dbe74d8231005bd74d823117d7e75982310057d7598231006fb6098231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014f
  | 26 => 0x77b60582511e67e60582511e57f741825119d7e74182510057d74182511e57c74182510067f64182510067d64182510057e73182510057d73182510067e63182510067c63182511957e72182510057d72182511e57c72182510067f62182510067d62182510857e71182511e77671182510857671182511f67e611825103f7661182511e57e70182511e67f60182511e77a60182511e67d60182510077960182510b57f765973118e7f765973101c7f76597310057f74597310057d74597310b67f64597310067e64597310067d64597310b67c64597310057f72597310b67f62597310067e62597310b67c62597310b67f60597310b67c60597310067f74597310047f74597310067e74597310067d74597310047d74597310067c745973118e7f73597310b67e735973118e7d73597310b67c73597310067f43597310b67e43597310067d43597310b67c43597310067f72597310047f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067d42597310067c42597310b67f32597310067e32597310b67c325973118e7f715973118e7e71597310067d715973118e7c71597310067f41597310067e41597310067d41597310067c41597310b67f31597310b67c31597310067f21597310067c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c40597310b67f30597310b67c30597310067f20597310067c205973100cff7658b3118d7e7558b310067e6558b310067d6558b310b6ec6258b31004ff7558b3101cfe7558b310067e7558b3101c7e7558b31004fd7558b310067d7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b310067f5458b310067d5458b311867f5258b310b6ef3258b310b6ec3258b310067c5158b31186ef2158b31004ff7058b31024fc7058b310057f7654b310067f7654b310047f7654b310067e7654b310057d7654b310067d7654b310047d7654b310067c7654b315c57f7454b315c57d7454b315be7f6454b311c67e6454b315be7d6454b311c67c6454b311857f7254b3118f6f7254b3100e7e6254b311867d6254b3100e7c6254b31007777154b310057c7154b31007747154b31005747154b312067e6054b310b5dd76ccb3100edd76ccb3100cdd76ccb310b75e65ccb310b75d65ccb315b75f54ccb315b75d54ccb3100ede62ccb310b7ce62ccb310b7cd62ccb3100edc62ccb311875f52ccb311875d52ccb31005de71ccb310b7d671ccb310b7d571ccb315af5c51ccb31187cc21ccb31134ff764cb311ae7e654cb310067d654cb31005df764cb31136df764cb31134df764cb3159f5e654cb310075d654cb315a75f544cb315a75d544cb310b7cf724cb3100ede624
  | 27 => 0xf6458a510067e6458a510067d6458a510067c6458a510057f7358a510057c7358a510067f6358a510067e6358a510067d6358a510067c6358a510076f6258a511967e6258a511967c6258a511976c6258a5101d7c7158a5111e7e6158a5111f766158a511976c2158a510057f7058a511e57c7058a510067f7458a510047f7458a510067e7458a510067d7458a510047d7458a510067c7458a510067f7358a510067e7358a510067d7358a510067c7358a510067f4358a510067e4358a510067d4358a510067c4358a511967f4258a511967e4258a511967d4258a511967c4258a511967e3258a511967c3258a5111e7e7158a511967c7158a5101c7c7158a510067f4158a510067e4158a510067d4158a510067c4158a511967f2158a511967c2158a511966c2158a510067f7058a510067e7058a510067d7058a510067c7058a510067f4058a510067e4058a510067d4058a510067c4058a511967f2058a511967c2058a510057f76cca510057e76cca510057d76cca510057c76cca515e57f74cca5119d7e74cca515e57d74cca5119d7c74cca515de7f64cca515de7d64cca511957e73cca510075e63cca510075d63cca511957d72cca511967d62cca511975e32cca511976e32cca511975c32cca510057e71cca510057d71cca513067e61cca511bf7661cca511976c21cca511e57e70cca510057d70cca510057f764ca510057e764ca510057d764ca510057c764ca515d57f744ca5119d7e744ca515d57d744ca5119d7c744ca515ce7f644ca515ce7d644ca511957f734ca510075e634ca510075d634ca511957f724ca511967d624ca510076f324ca511975e324ca511975c324ca511976c324ca510057f714ca510057c714ca513067e614ca511af76614ca510057f704ca511e57c704ca510057f74d825119d7e74d82510057d74d825119d7c74d82510067f64d82510067d64d82510057e73d82510057d73d82510067f63d82510067d63d82511957e72d82510057d72d82511957c72d82510067f62d82510067d62d825103d7e71d82510077671d825103d7671d82510867e61d82510877661d825105d7d76982511e57f749825119d7e74982510057d74982511e57c74982510067f64982510067d64982510057e73982510057d73982510067e63982510067c63982511957e72982510057d72982511e57c72982510067f62982510067d62982511f67e61982510777661982511e67f60982510077b60982510057f74582510073f74582510053f745825119d7e74582510057d745825119d7c74582510073c745825119d3c74582510067f64582510067d64582510057f73582510057c73582510067f63582510067d63582510057f72582511957e72582511957c72582510067f62582510067d625825105e7e615825105f766158251
  | 28 => 0x85320067f54d85320067d54d85321867f52d85321867d52d8532006f751d85320067c51d8532006f451d85320067451d8532006f641d8532006f541d8532186f621d8532024fe70d8532004fd70d8532006f761985320057f75585321ad7c7558532006f56118532007745118532004ff751853201cfe7518532004fd751853201cfc7518532004ff7418532014fe7418532004fd7418532014fc74185320067f54185320067d5418532136dd73185321367f52185321367d5218532006ef3218532136de3218532136dc3218532136ec3218532006f751185320067c5118532006f45118532006745118532006f64118532006f54118532136f52118532024fe7018532004fd7018532004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d81321067f52d81321067d52d8132004fe71d8132004fd71d81320067c51d8132106fa20d8132006fb60981320057f75581321ad7c7558132005bf74581321a5bc7458132005f77158132005f471581321ad7e75181320057d7518132026fa6018132006f960181320057f74d8e5119d7e74d8e510057d74d8e5119d7c74d8e510067f64d8e510067d64d8e511957e72d8e510057d72d8e511957c72d8e511457e71d8e510077671d8e511457671d8e5117e7e61d8e5117f7661d8e511e57e70d8e510057d70d8e5116d7d7698e510057f7498e5119d7e7498e510057d7498e5119d7c7498e510067f6498e510067d6498e510067f6398e510075f6398e511957e7298e510057d7298e511957c7298e5118e7e6198e5118f766198e511e57e7098e510057d7098e510057f7458e5119d7e7458e510057d7458e5119d7c7458e510067f6458e510067d6458e510075f6358e510067e6358e510057f7258e511957e7258e511957c7258e5116e7e6158e5116f766158e510057f7058e511e57c7058e510057f7418e5119d7e7418e510057d7418e5119d7c7418e510067f6418e510067d6418e5118d7e7318e510067f6318e510075e6318e510067d6318e510075d6318e510065d6318e511957e7218e510057d7218e511957c7218e5117d7e7118e51007767118e5117d767118e511467e6118e51147766118e511e57e7018e510057d7018e510057f74d8a5119d7e74d8a510057d74d8a5119d7c74d8a510067f64d8a510067e64d8a510067d64d8a510067c64d8a510057e73d8a510057d73d8a510067f63d8a510067e63d8a510067d63d8a510067c63d8a511957d72d8a511967e62d8a511976e62d8a511967c62d8a515ed7e71d8a510077671d8a515ed7671d8a5112e7e61d8a5112f7661d8a511e57e70d8a510057d70d8a511957f7658a510057f7458a5119d7e7458a510057d7458a5119d7c7458a510067
  | 29 => 0x57e73981520057d73981520067e63981520067c63981526257d72981522076d72981520956d72981522167f62981520a76f62981520057e71981520057d71981520067e61981520067c61981522057e70981522067f60981520077b60981520057f74581521c57e74581520057d74581521c57c74581520067f64581520067d64581520057f73581520057c73581520067f63581520067d635815261d7f72581520076f72581520a56f725815261e7f62581520976f62581520057f71581520057c71581520067e61581520067c61581520077b60581522067e60581526157e76181522057f74181521c57e74181520057d74181522057c74181520067f64181520067d64181520057e73181520057d73181520067e63181520067c631815201d7f721815200d7e721815201d7d721815200d7c72181522167f621815260f6f62181520057e71181520057d71181520067e61181520067c61181522057e70181522067f60181522077a60181522067d60181520077960181522077a20181526077920181520b6f76198732004ff759873201cfe7598732004fd759873201cfc7598732004ff7498732014fe7498732004fd7498732014fc74987320067f54987320067d549873200cfe7398732176de73987321767f52987321767d5298732176de3298732176dc32987320067c51987320b6f731987320b6f43198732176f52198732024fe7098732004fd70987320057f75587321bd7c75587320b6f46158732004ff75587320067f75587320047f755873201cfe7558732004fd755873201cfc75587320067c755873201c7c7558732004ff7458732014fe7458732004fd7458732014fc74587320067f54587320067d545873200cfc735873215e7f525873215e7d52587320067c51587320b6f731587320b6f4315873215ef6215873215eec2158732004ff7058732024fc70587320b6fb6098332026f860983320057f75583321bd7c7558332005bf74583321b5bc74583320b6f86058332004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff7458332006bf7458332004bf7458332014fe7458332004fd7458332014fc7458332006bc7458332014bc74583320067f54583320067d545833200cfc73583320d67f52583320d67d5258332004ff7158332004fc71583320067c51583320b6fb30583320b6f830583320d6fa20583325ff6f54cc9325ff6d54cc93200dee73cc93200fce73cc93200eef63cc93200fcf63cc9325f76c51cc9321ad7e75d85320057d75d85320077451d8532004ff75d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d
  | 30 => 0xf64d85520067d64d85520057e73d85520057d73d855201d7f72d855201d7d72d85526367f62d85524376f62d85526377621d85526377521d85522057e70d85520057d70d855263d7d76985520057f74985521c57e74985520057d74985521c57c74985520067f64985520067e64985520067d64985520067c64985520057e73985520057d73985520067f63985520067e63985520067d63985520067c63985521957d72985520076d729855211d6d72985521967f629855212f6f62985523057e71985520067f61985520077761985522057e70985520057d70985520057f74585521c57e74585520057d74585521c57c74585520067f64585520067d64585520057f73585520075f73585520055f73585520057c73585520075c73585520055c735855263d7f72585520076f725855212d6f725855263e7f625855211f6f62585520077761585520067e61585520057f70585522057c70585526357e76185520057f74185521c57e74185520073e74185521c53e74185520057d74185520073d74185520053d74185521c57c74185520067f64185520067e64185520067d64185520067c64185520057e73185520057d73185520067f63185520067e63185520067d63185520067c631855201d7f721855200d7e721855201d7d721855200d7c72185523067f62185525ef6f62185521957e71185520067f61185520077661185520067d61185520077561185523077621185523077521185522057e70185520057d70185520067f74185520047f74185520067e74185520063e74185520067d74185520047d74185520063d74185520043d74185520067c74185520067f73185520067e73185520067d73185520067c73185520067f43185520067e43185520067d43185520067c43185523067f72185523067d721855201c7d72185523067f42185523067e42185523067d42185523067c42185523067f32185523067e32185523067d32185523067c32185520067f41185520067e41185520067d41185520067c41185523067f21185523067d21185523067521185523067c21185520067f70185520067e70185520067d70185520067c70185520067f40185520067e40185520067d40185520067c40185523067f20185523067e20185523067d20185523067c20185520057f74d81521c57e74d81520073e74d81521c53e74d81520057d74d81520073d74d81520053d74d81521c57c74d81520067f64d81520067d64d81520057e73d81520057d73d81520067f63d81520067d63d815201d7f72d815201d7d72d81526167f62d815262f6f62d81520057e71d81520057d71d81520067e61d81520067c61d81526177a20d81526177920d815261d7d76981522057f74981521c57e74981520057d74981522057c74981520067f64981520067d6498152
  | 31 => 0x80040080020008000000000000000000002600000000000100040004000006004801400c000003001400a0010000000000000002002800600a001002401e0000040010008000000000401c001004801400600100000180040010000008010008010804c0080000050014000001000001400600b0010008000001001800400800600280080000010040078004000000805801c0030000020000003001800401a0190000028004007000000001a00a00100680240060028024000003000006c00000a00280040000170020000000003000002c00200000000040060060018004040000001805c00002d0000044002002004000802c003002802800a00000300340080000000000000012000000000400b00000180000050008040032014003800c000001007000000800a00000400140050000000020000002802c00800000300000080140050008000002000001402600100080000040040068028006000012002c0000030018000000001019000400c000001800c00200001e0014008004000003c004000000001002200900b001801a0010000000000006000001c00a00d002800402e004004002001200600080000040030208010000002001801c00a0030050010010020000805c00400100d801c0000040070000000008002000c00400500080380040020000018006012000000004a00d007803002200100000380040140057f74d8d521c57e74d8d520057d74d8d521c57c74d8d520067f64d8d520067d64d8d5201d7f72d8d5201d7d72d8d5265e7f62d8d5266f6f62d8d5265f5f32d8d5265f5d32d8d520057e71d8d520057d71d8d522057e70d8d520057d70d8d526657d7698d520057f7498d521c57e7498d520057d7498d521c57c7498d520067f6498d520067d6498d526457e7398d520067f6398d520075f6398d520065f6398d526557d7298d520076d7298d521ad6d7298d526567f6298d521bf6f6298d520057e7198d520057d7198d522057e7098d520057d7098d520057f7458d521c57e7458d520057d7458d521c57c7458d520067f6458d520067d6458d520075f6358d520067e6358d526657f7258d520076f7258d521bd6f7258d526667f6258d521af6f6258d520057f7158d52007777158d52005777158d520057c7158d52007747158d52005747158d520057f7058d522057c7058d5265d7e7618d520057f7418d521c57e7418d520057d7418d521c57c7418d520067f6418d520067d6418d526557e7318d520067f6318d520075e6318d520067d6318d520075d6318d5201d7f7218d5200d7e7218d5201d7d7218d5200d7c7218d526467f6218d5264f6f6218d526475f3218d526475d3218d520057e7118d520057d7118d522057e7018d520057d7018d520057f74d85521c57e74d85520057d74d85521c57c74d85520067
  | 32 => 0xc00200000080000000118000004000018000c006017000008c008004000000c00000900c000c004000000009c004005006800c002001000001400600700000080000000008008004000001000800000500000100140000008004000008002000400600000180600240020020024004001004801400800200800180060010068000008000005005c0000010008000006004004801000a0010058014006009002002801000201c000400a003004000001200000b000400000800f80ac0040040000000002003004800001c000000001c00200a000000401e003004800401e0050000004004000004800800c0120038000000002001800000400e001000c0020010028008002001000002801000e0000000008001002000000000600180040000020018024084001002801c00200200700100000010008068002000001000400400100000200240010000008014002003000c006002004001c032007009000c0000000038018000002010002400000e00000280000120078028034002001800c000020001008001c0000018004000000001000801a001000001c0140070060000000004000000c0020020028078000001000000000e012000000000000100a000000000500100040020010008004016015007001c032001001800c000030000001800400f00600000080030010018004000000003801a014003003004e00300600a400a00400d0000028008000000801e0080000070000000000001801c00a000000c0000060008004006001000002400200300380040140070028060000001000006800200a000800401600a0000000002003000000000c0000000000002007003810800a00000080000000160008008024004002801400200000900040020020038004004000001002000a00f0000028022000001000400201a0060008002000006803002a00b00a0000000000007006800200300000000220000000000014001004800400001100600140000010028000000001000000c0000000098070012001000008801000a00080000000060018014014004000800000801d002000c002004004003800000400300040080000040014000012000001400200300080200020030048000000009004800800400b0000000006008002001800c003003003000600a005001401200a00880040060000020000006008001800401a00700300440080180058014002000002800401a0000050020008005000805400600e00180040060030020000002001000000800a000002002800600c00100440040000010000012024000800000200100000040000010000000010000003000800000000280140000110000000000030000000000600b0108000016003000002000001a00300140160000008018002007002000c01000300780200000010068018004000000
  | 33 => 0x38000006001000c00c00c005001401401000300040120010010000004040001800000001f0030000012005000800c00e0020030000002003001002c0000000068024004002000800000a006000000000a000000002c00600000e8000048004000800c03e001000001401800000080340040000008020014002000000404c00500400080020000028008004005009005800c001000800000000000e800004402600000040020160020000010003001800c002001002003c00a00d000800c0000010000000000007008000000000d009000000a008000804801200000e001000200c0000000002005000000400c002001802c000002000000000200b000800008c00300280740040010010004004003005801c00601e003000400c021000800c012004000000000000000c000400e010000000400400700000600020000000020002001004800c002002006000000000200080000040050018010004001002807000000d009800c00000400e8000002000001000001000000100100040000000018004013005001c00200200080040000020008010000004000800000200c004800800a0010020008000001000009400a004002000c00000200b003400400000000200120020018050008002001000000000a00080100320060018000000003004000c006000018004800c00a00e8000004013002000401601200300280300020010000014007006000c004000002803c00e021002000000400000e00000020040000054006006001002802e0010010000008003011000c02600000300080080000000000000022006802000000c00000300020040060000004007000000800e003001800000200d009800800600100080000100040060000002009002000001a00000300040020070000004004001001001400200800000040000000000010090022002001400c00100080480000010008018002000000800000a002003801000400000380340120140040008000006002002000600000380d000801a00b004000402d00280140000070000008018000001000800e01900b801000000600180100120000010000000000002001000801a005800401c00a000000c00600e0030008004000004000808a00100b00040000010010000002000004801806c004005003001e0010008028010006000004000200600200080020030018008020003005800c02a00100180040020000010004006002009001403200e00000000000200010010000000001801000c00000000140060020028008000002000800003e001002001c0140000028008000000001803800e00c000800400401b0000008020000000003c024011003001c018000002805c002000009805401000300800140160000048014002008000802000a000001800000000000d8004002001018000000
  | 34 => 0x1eb08326218dd01d50eb69f91f2e5fe80ee69b1b0e35a80000a49f3200000003b10000a520dcc000246c00006e8377857a000000036924e6791970675400000001c4e000000000012fe00000006df1b9e7d51e04000178c00027720000d300008000000194c70a9c6a0001e8e12e057ea3aa4be7f6092852f137080100000000a680001904000280e51f93843aea130a439e002f819e00c9a3fa765000019e193a16aa6484bb8dfa6dca5680339bee149293000025027ab08dc000087800000004150b4a7c39f9622e00003cb00000000d265430000000000021395982fc8af45a702f800010105c91be0329947459d0298a720238916176618f871025f00000001fe878187cc4fe95926de00000000000000000000000007849f6c9b620ac651912a4f60f3274380004ea808090003867d10000000000013580000000bc200010387fd240a5ca024c01e216c00008ec1938e1841b01e8000045c9c3951600008e89fe8d4a0001ec099490663520c145b6a02400025904279f8e4018c089c282889ea257e00010460000000000000092500005e604667722236312811c29d83ae05821aea189db847c228a43187f218b9f1c7110ace00b06be96a1c9e6082536374952a4c101983c728ec00008a48a08c302bb1e1a09c00009310b9022a1968000000000000000000000a6180002198d44151067200010b0000294485522c854b000098f000052c918a00005a801926c859a0bdc2c207e498d16d416303fc62012166bb0a6657a90789d2800000011a8a651cf600009dc000000000011be387a7da7c90000886800042fa59a000000008e9bf6a0c1dd219c174800000000000b982ae00006b810226c00b28000290c992a69ca3e20b05f50cfc8991a2852b827c01589fe2eb1cc645e0e5a0000e5e28f064000797ea190941e793a47e23292d0001002401400300000180720020100004014005007802400200c00100cc002003002001400200000a003400001300c8048002000001000c00e003001000c000001002000001400e015801402e01a00b003c002004000002c00c010000000c00600e00d006c028000005806800000900180080040020020008000000005000c000000008004400000000000180020000018000004000000000400201a017800c00a0000008010004003000800800a0010028058018031003000c00c0020000004004001000000c00800100d0044018015018800402c001006000000800400000440160050008004008001000800c01800e0000004002004007804002a00d00180340020020018004042000007801c00a00300000140020000000008004004001002000600000000000040000008038026000005800802c0000030004000000000000800000100000000120010010008002005004003400000000000a400c00200
  | 35 => 0x1c3684d14283c30000000000000000000000000303820a8cba27200001842458000000173045b9624000066027982e200014862cd82460000000896819a9da0000000092683d1f3a0000e880002766113a5ea2df2666000153a662102c00015fe0000000905800000024e8000000013c216000000008ba800025f9b1e36d800000016f2000150e67693329d91e8aa6c80003c38000000081c38b82ec9a400001bb000079a80000509a4e5a68ad67f2299a0f99ca685a25180000be284504127e4886e02e096842915d82d8239c3609790000237c0dd9d5473f92b8270800000000005b21ed40af80000000af89e00000477800000002b49031bd8192976e6f008be00000005bb0000000025200016ea1798000a2f8b2e9bf06668f111bc55b217c1aa0a8c3e2144800016164d58000000260000000001bf29367a522a84db800035f86302d524ce2dca3e47c51c286ac01100e91c8ea5a868610722e0209a69e81d030e4990e065f382fa000000063f80009a9026a68417088ff13fe000000050b80001e7133c8771fb0a11009068c8c9400008f8000024a03d06844419fb8000000000003c4000158807220bc000000000003cca27214e72a9e142dd1b500000ed417128e29c600003a6a2407072498479800000000006642304418092c339a19874a13687b424ee75d205e443219e72e8000000125c7b69906a109d44a170000000000006c8256000000000025c200000007e2862228904ac9e7897a4cc27cc0001de29e81ea2000000c8629ef03761412203a9927e509ea1338704521160683e0b0463e1c920fa803e7d886126198cc0697917c4712872000088c2a6186e58c00000000fec7efa9ec0000330000000000000007609d24000000083296f601b0f581c99ade54c000064300006e107e6988a3083d5816639204069c10d026b08cca1b58cbea3319143d729466871a0e6d78c3a0000e284b8800082787a65d312e08558000a5b1b8227404d481384e45cd89502ad21fe2bf0ece0002854000223479b00003550000360010a0000000413183c2fb80006c9865200000000000000000000000023a608b00002dea9226d006c29b79cac7f41f3600000002c9233a000046c0000000000000032aa55678a0e603eb951207087565ef80000000000000005a6e5099600016ae2c2800054a126a8d18ac2735021e000034c00023e841210a60001f76565800076c1dc48eb000000000006fc15868ef0aa855821044dda6ac70e85be8d5880082a800041c00001a8922a13b800093609d200000000f0000003980000001b520000b6295904720dc000000011e0000000000000000820000000000015316dc88010528e58a20983805462f039c43a0dec06d93827c297dc72c0f2a23001a873a05a492b156206aa0de00000002410000000261643629ee
  | 36 => 0xe70c28a49d523de2061fb256da91833a1f9855112ec6308df09fc82b853612c4959a61e74d970a5fd845e5d681b420d96aa3469c4877e054e1f7298265688086718dc8626a1107f90adea34198a3d7a398000194a33ba3fe00024383880d120002610778000000013d2000196e2fda46217a9a8c00006248d98000000000000000009cd00265e0921a00000000000bfa00000009090000000000000000007ae98e82239ac61db17608d6191206ba47238aa1ee0000a4c52f800063703f0728a66857826c410600008910000000129497929980001dee85ba7402bc0eb467d1a060458000000000000008740000000000000000014e400002e00001e8c80a8c2450d800039500000000000155a95a000164449596862c888308f482000001f6800001f60000000a5ea65c41393008709c5aa2107860df1b24089843e000000063b1166000218c0000e3800026304f4116c40ca4460001ede3f798ce9c225d01faa9f643d800058a800069a1a840001bb200020a6000201a0000c92876886a353a47800029548ac1cf22481ab233110a88f68dc0a6c1fea0000a0a271a65884b09a894f13de53f2542972a9380001e706ff24021141ea64eb0340872000060712ba000095e495052241c9fd40a50bf419a93ee1d1000070196b018ca73277c2066489a4c0632036227c28a61478fe20000ada000133e000000047d99947c0a0b25ec8000000062650d00003cf9ee244817f486c19342e5800071180000001682a4416e2409866c2c300001d6a3ca00025a48578d380e015f20b70f9056a028c287a2900002898000000000000000c1800000026d6a73000000003a2000012e000102e0fa000056f139c85695c253c1f6000000000001b0200009f800000000000000699800000002a42a9222867495780e519b01978c8648389328b100008b394b657914c69c411965c58000838a6ce1f0821424f99cc000000000015f00001d420000000010241a00000008fa9100437800003214e83a6000044b00004bd80009610426816082c820800082d896421696906ce1d069281c6e9ae989256c20380000000345000038c00000001b4e04e17cc74004d800024809ad8da80001ba60000000508853a9881f4c8bf80001e104a61d4891065c1aaa2581db2000000009f99c00001850a0280008600f4200029021b4083e067000000000008c7216a657254c9d3010255d8dda757800040483e47bc86a41229a3a3c900006c20a92595800088b1518000009c0ac12729f200002f99b62a5c038c0001118020800000007de000000069c28064a919dc17f287a3bb99bc1278000077000057700003df80004c22322810199a0478c5400028c42088000832049617f800080c96423fd800029c166e90d000000012a20000000a16000000017521a0130a1a098c08f42204000
  | 37 => 0xe8e4e64b1d9827000340000ca80001afa41b863a2dd80000001bdc44e96641dba39a8cb25a04d1800013c80006de80000001bd22c09e7a3a51dec59700000001028000022e7d40ed03841a8017e060a4759f5c28d272c94e12d462380f82818bc814e284a43b8ebe27d93064c61afe37f9ab69e90000022a0ec0000000a6a800051385b62cd0d065cfa6b000001e059b03d625d290a0750e0a6f42636000237e1d7000000000005e7a52a0d10f52a2c231a00000000001ce0000047c2ca8a6093d00009fc04da000119400006cc00006c000022088d38a487218de290e80003cb8e1402621946a583de00007160000000000025897021a25720eca1a510ae7481404000033200000005de8586742076a4b0a28c000280806599aa0000f9c43800006e8800087c0f6a5030000000024819188d001221cc98b826013d143000000006da25467f691a60b69f38395935246a96de20a8c385af800021d80000001e7c4f9909c000256255400000000000000274400000008b580000000000000000000000004ac061c75b0870230a9f800026027308b1808f8cfe6a706dc0bb94407c1a9fe732119a8c0949e9e31bae1e004ea78f1c4a0ca1e54815942c89784c81ea202854419d0019a7c242327268da95ae4ca8000739953491d1538008293467ba0d0895903439480000000aaa00002200001b2a07e00009ca800000027d83900c663930a528548b4c3402278052925e35712b483a0000115800046380000001f40a2ca48800000008c4000000000004a61e32000000000020940000a560f8164c0000da07c0226210428228228ebc58216a6a559896502191e8fba45c8ec0000488029c7ad9080654822a3baa68a0000ea200000000001e6010a0ea492993a20000000000283c83186280001500000067a2ab00003db9770587899e0d50232971167e1b11c40a76068e09a143e000000000000003dc2784000095ca458e6212ea38c4ce8c6298b145e5a8141065380005230000034000054991b28921d7a744000051400000ee06060b328ee803a5be82612700000dc28409c242da11404c509e222d977e05300007e100000000d2817a0f501420f169b2831a1e092e81ca04e80000000000000000000469f109f495800940da883c83697402ff23e2498003643c0ac680225242f5a2ba217a59c0c9020279c88406851e781ec81fc83d85520979814000082e4fa959e0fb91446038d8c787870e09013985fb9e400000a547c321581561ad6029000076b8f367941eb269e80000d09fa0000056423980006ee8ba289391fc123a6ea00024b8764800038492d86a288da26ea78e60d9cf80ce04d03fd1a160018ba600013be6b880004058000773a360a698a7a00000000001d8c0000a9a0000ff80000c5200022d400000000001ae66508000000283a000122
  | 38 => 0x3481c0afa4770ba81c4a9801010696372977c95b9dda000076640f8e7e95da8aa7390e8e26f23cc40293025359b56028a9f000000005248000000193e38f00003b980000000d602260000000145aa3200002f2a6f000005287190ff00000ec27ca00007fe000000006e400000001e29d323e686202d198b853709ce686a32875287969dd82aa9d4132e5ad105e4c48bba32b1672684a7d6373a6062040c262058e9c5c319541b68ed62ed26b845d0dfc07b00000001b1873780001851b34000088a979a84c39196847d1800000000000001322000000022a9808a1da1c652519ce74d12de23b9fc40001c1e61813a463d213e851106a6c117fe2cea9b48668000516294a0c123067b4a77e0a1838293400006e1a8d4000229a2f006e056328827dea1f8a7d000030480000bd9978219268216d178075d9d68583a3e66d11c884c5a95228982e443125c64128f8098a8c503aa1042000293284ba88600006d4359a592a5d0a400000e926f995b85c990b4456a91e1bd83ec130981836125bc2e2976c61f9360084a50aa5384b0a3d97b83c00778751a93c24886086331fb67888c04a23955a00001240000a12846252836f1e2e000270654510209a500001031a567858fa06920388828263a29e00006968130168800049425522a111fe50522e640a80000000636a10000063f00005e590d00000ee2569a3302b321920a681a236e96141e3a71a1a4a7fe23482c09630d3e32602763358a7260a04787ba048c0d28d4600022f02fc0264509a7127ea18300312178670934202c204808580000f70e9600000768e4949600023b465d93f028080005ed217e5f01188a4b000051900000000000213160a87e80b258d809a51199f08b88000677805016299c8169967674114d25628ab200004ae199294286c909a922800039f1d583830194000000000007f61c300003ce223805da1320001bf21d21fdc63624fa687a6b20001dd600000001261a420001fa200019a807027420001a243008a3878c0000000015850611769a6a1862e49c4262c9efc40100003ae25fc76f10861508b5c7a7905c00028d614f051c3f80000000036600019a200005ba59f13f2a401ed643589b20000000000000071e0ed800000000001dac2c59a206111f344dc99440000bb20001d800001a26000000028c9e3464d9a022248c3223327ee5a219385cb000000018625d90000667a66c365a0005f0924c52c29763670ca2442269600000000c4182631b048242486042e31074a2d00000001fb4a0a13103f580083ef0fb68880fca000090a55202bc83f80001ad9746000000000000003ea9d3c000000097e06f291a97c6530010e11f938002a8e6e25610448ea05d29d5a93e176079e0f8a9a82ce295e16c1fe282f80000001842000249200000000000c061dfa01c808244e28
  | 39 => 0x800000000000099c07b48fc927849d85782129ad02e8185a0000000246800061727fc4a295f60000a860711de61b995e6000290837a0a6c4ec836c546943c0ce8a287b901465c617a852982d0017133827b097234386024e5a23091900581100b1058325dc45a900231728c6081130e76691149e899e200000002a5a9b68e5102400000003c600007c996e87ae094c73f032a77a8000a59027a1129a865039b9078300006d08c1800006f492a800000021248de22a660780e21da22a000000005d59bc80b507c4141266a1bfa43600000001802672000245e000207c00000007ff00007a580003839b9251e9f084c306c8586800074ba9c2355a0b418680008e1a53a2140000227800000003aa45700007b1000000005ae00013280001db48528b329a88638320800000000000000fa2000000040725b62649da20000e784d111ca00000002b21b3c00009420000a4600017146121ffe598138c27c94241a698f0a3f90084b71dba0000d0c8db80005b383f848612c8405264e8468f96000000096d0e6c2518a622c81c8292418d457121b40691374704000021e91b000024cc3f1180c00000008330eb000b80002d6a3c8000138a869800096b8d744aa800044d953c017921c5f2a2241ec16eea23221c2f19ab40c48988859281a4e49aca2c729be87f1a2e972297c88f22b81ee16b88b905e44f8000003f193273d205a4af1c228ee0000000186c00004621cda3c6011000000000001e8090600005c23470000902135e8749ece000103a00028020461b5c0000000000202200000fe00000000000c720001bc2479286c090923c3940d2268c0280000218833212580000f5a6d310c2560a84e45803ac11da100a3e86ce6930402013920c61294ea775258e32e8c7880ba03e97380005b29baa00000008b71cb60500702946a9d00c7956655a87c86a3a06806825aa0c5000044a081e2fa23e058f92349c91b66a501e4c55e80000fe800055b8000000041a5dd04463fa00000001d5214d9d880000eec0002788573911079717923e60000000000000013c80000f7872c800004a88483bc06d200005ac000074e4bca53e0000b128af000066b00007c1055e6f5a166776000050a8ce07f488fe803225c83aa30c94503487448f940619db61b6007a00000000001f9e55026aa5cf1fcc07a98b662816d81328dc44900c6408d015e92c276a5a5a838a0711262750308668212857e09d81459d6a39c000039e8f4821f85ee4d40e048e2233639d913ca56100052b16c6a3392e62bd8dbe0f423404ba80000418d62251126896981003c51c96910000080d9c8a025a98c000173a00012860ac946000008382479e0226e00006488fdc214800000028e067d9f420001e62000000000007d000000000001bec00020445d780000000000227000022f28d88a487
  | 40 => 0x7326eda3ec00000f60a80d641a98000a75854038d86b212ca60c2610d763ec945494c8510937800000014f61b1a60a0001a2a6a98f840b9800000020a41e5248234d9ebc05e04fa87a01540000cb836c0fa621125869f5056a322839009e0ffe9b01b0a9cf0c5e000000015f2316000056c00000000621af42ada7e084f08621f69d26796296e48894784670c1e03711a00001a6aa25265661a1fc6344196c463087c00028a2000018c0bc00ae0000000596800024509780000000654072000000001d40eda7998108a0b1ce25f785cc33926243ff0cec2549a521cc1cb86cda60872f844c8a608203ab964a0b298900f388b096c18e60b0950278fa35a4069c5210d801881b00c289525f0418880476a01bc0769692001000000c91560451c7081d9bcc000285640f16f458125ec23a9152285292e8de9adc6319a6220480526bf0d2c6b68a5878e279227328e61e49a3810792a6000000017e9ba87870d9294599b686094c4916801a8dd000081e18040ab84e09be80000000c2800000002c680001f28000000000000000006091e2a0000000000157e000000000000008be800000000000001c349418aae00f1620660a4ec46e80005570e640001a744e1800043d0000000000000000008bb000012f24d48729d62461a0c065020cea0790cc000000061d968a000279a41d8ef86c80f3451b889a8e88f4c000000031221b61670c586b512ca60f8f2802f1f660000000842a4143f48000000268891c014e0000ab097300003f902ea0000b648fd8a1815712ac32204f6178946c56e8be436a8cd4336a7ea73c000091a04a460e04fc9c8000093f800052280007b2929e8b313ae5ae8000709800090111c82b28f3a00011f800021d46220000610000065911f42bc9400000274e30810aa975800000008f675f000041e800088499167ad133607419c40000000000000066495065b90000342800000000000000210962a6dc35f081a0000000000230a16687ce82217f2000000000009aa0bf840e000289a1a3000000000ea9b9294c526961c9ee18744810c7a2c7800076380005378000000000000018822e080007c499984df871c1e88b2c9b4944451c1de80001702198a0145c8078c49200007f800e08d221e47131d6e6901faa2670a74034a63e000246600000f2000000073a8c3c00000003dd898c00016020f5000089e800038b000000022f2093990a8798000870018a55180000000000000000000000000000000000068a3db29c06ec00000000b840000ec86c4a42e64c1206000257a47b9af843c853e6f500002460000000000074c000080617e44fb14a46bc80000d783b00000000000000078d8dd4923a22a00000003c79eb07bd80000000000a71800047e8000000123288300000001e5644280b60000d9821a00002e0299000017a22
  | 41 => 0x4a8180a00004600520d6c4e980000001f5a0001262702909400007fa00013c4320000090c29fa38921d896e9c1899328bc86421d662c0e0821600002a88c4600005607b717725f11ec806988d88af9bea077800064a800044e00006c58000000000000016fc2401e0a9eb80009af23c2000031c00016323a311ec029a78a286800052a8a1c00023907741b2c61300009359f725be0ecc0e8256a1f584f8a6e00ba457970e49d03d28f38e325689b3075216660f60518a5a0cd880580008ea833c0541d6000004485af2202000114889b925a000018e8c811d28b1883a62f8ce24daa32481c8f9293a9e248929214524062c8d0a8f0746a972000093835ca51e00000001a728f200000005e71da082196cc0002368827000000018a808f19e4000136406c08c800020900001f88949970000906faa2b0c9a6baa44a85e81204999902a308ef64e399d638684526a2121242b03969fb247a45ea55a9cf9e5a726073a29b8ff276a80687fc1a9e98691d89c58fea0dc8000a2598de3929524812800000022325a7a5725ef00000601aa471d17b63e195847fb10984b30e3e5788896000081468009569ca1fd61aa8c76000178630d00005800000000299e32f0e901fe00000002116553199c6639b6070394e607c99e875389700000000a7a920a0000000a4528004281d16a1b968e63c9a725600ae07f2843477f289e4b38b7841a000045c00005d28000927000048e000042280007428676000000056380006b019ec968a50875912922d086ac08a00005eb2574000028ea4809b6934a3769fd8000000000028393e21ca820ca7f2138000201e0c2a7ce000248c2f3212a7a429d45d096a28cc852c7cf8d2e955012c8878f047c603c64191f229cd859e1fb23a04db0df859a8b5686a1f8c98601fe6b926a67371f6469fa242a0d254849389ca7f002ac91f0170416a3141640a649111d4c89f1116998907e035964662787aa1400fd8801a8e41768efc99100e8733a4424d980005b016521eba5b8276873e22c848097ca2ca54b8eaa33c9f58a03271400000004e40d3a34d279866000001ed800053e00003870ea60001e768a18000000000079080000000000000114aa180000450866e0001c9c63580000000c9600000003278000000026e229944a4a08000a2a000000029a019a000097505846421f7ca329b1c8eda9265590000a4480000001c047ba9b6461e1b7071e80002f48baa00009ee0d8051a0000a08638a22e66c90ec2e904923de8000a4721509511ca48aa800000000007670a04000123687780be0000000156810c3c20d9098e05c000013249f1a38e000000000c0000000000060d09801fb88463340f640f28d7800e1e9283f18aa5f81eaa0000a2e000164e5e2976a4690de09a00db299f800065228ae4f514ba1910de46599c663cc0
  | 42 => 0x1c844d6073c1971b6a29717eca4a80000000fa4000203400020e02e688ce8d120d28f7000015c8420717840028c00007a18b300000c7000000000e280008a2079a0000000164800005b80001c7a8689ef98a481807884768994782268694429e24f3172a0000fac91d99104d3804c2551e80552911e21b114c4de110272b88ba5ad80006310bc4907282a11123647d5835605e9a5802824e400007980569198369a3b2000214200018e0a6b800008c0000904a6a00001b1a00022b22c3a13a93c0b5e23f24bc1050c4271595b437d000000015be4a394a04a005f60448fa8000025a1ae02ce9f70d161719acc2eb9d6656905668d413c600000e4000000000000009019cda2b483649ad0000000000000012847e0000098c9da4a09800058e80003501e640000cf43c280009c320b80000000000000026906ae00020520000bb80001d5600000004648ae20000000000000043000007e189026f900c00000000000000000021f60000000000000000000000001960000000062109a29448f728e01dc600000000218000802995809982723a0971078413dc2af00001450aee8430c1c17590d240c261c8a780006eb04ec0ec89ae65f94683ac92d2a6f18e401ba26a0001ff60001aa046004b4000000093e00000001d4000006f05731e265f60fb88589c900d4182e2f680000b58bde4a427ac99e80001ef00000002484000288855593203bf8f8a42e1572634962c8ef896a36e015c064a5da00000000000000102000065f0000000123083600009b18d9e0ed1c8033d9b8a10c18560001dcc000254a756a68c00029c40000f3c619000055085985e825005068d1871807c650819962c9836867f000005f9f10000000005b03be05c8236000000009426da63e905866d0f4a85ca52c9d688de5d39c1a89320468948e26023a7620000cce5d101e4000000011511cc46b9a606bc1fee000255e65c879000003a82032120055800000027a604a17fc027a7f87b9981a8c4a42a3efa03c5c7276c00000003112222300221453ca34c53e9dde649016a000000055c016823d019035400000000806000000030b2962000000000000005b4000018413f828406565fa1f484c7a276823069836683525aa18989131e4804e94da3ba0b7e69409400db97547348d860000adc00019182ba1b580e78df660595ac9bb912423c122808189be000062a898060c8e10a3e6f3945c102a6f47488fc886f94a20001f8251a9f3c43526f2108a83668d000051585744c683b67df8e9e66fa65aa1f91d03a01cd88780000883905637c8ca48478000a41800030b877001f220a8d480006810000000000056a83165329fde49f9aba0f0a318604a2d82daa2de0089a0a60a8000000000063280005ce000000025f46f68bec835800000001f06498fdaa7c9d9e1221ea886106e2
  | 43 => 0x1b5a6f1000014c8000a739c0c2ba9f2c6928c6a1b7a7e8700137a576a43c00022a415280000b201be9a10000350a7001950b6c82a2928470267c2e780cc67628fc63da1ea44b8658a4ea5408d8a2f408682822d9979a96788a0151a0fa210800037b87762b92650000226c45c9d868109b6c914859600000ac83723829ee800073406ba0000a4aa0fa6f8a5f9c623688a4e000266484184bea79127c0000fc630f8000000000000007fc7049750000116807d1b3269524fc00016fe3d88ccc90a1f5257a0000000189c00009480000b6e2a097226a4800044482d200025880000a8e586161200000002b6000000000002668ffa000000095f11ac0001d2a0001c2e8dca04c00029a4128800049e8384165121012a0ede00029ca14aa1ac00000000cd82a26f7800026411ea5e500002f5168c000000007e80003f51fa600000006e599744a584d21c50e6a9320a0c15d876452e01322e3814400000c6220800000000002d3a07e769915871700002391f6a000000000024224718dc69a6000031fa1f400028b60000000000077a2528000000001400017326ab8e3a5ec038e02a067e4751ba00c81dfa41f233424302840000c220798e1600027b20000d086d228320bca8188c0288019680004b900000000ad43d01c9a7a7190e3e7987293880005c7a44834915a07a920027f0a050953800045400008238e5c95e155274f93b63ec000085208c41ffa9d26e3a3ae821065013fa86600004e61d080000ef0d1e30a9f1a761058200014d455a233e2b4116275f8aa091410e68f51dc2909992e3c40a5a906048690426cca34a6d49811b9c380250c990279400000004b003f46aa1348000000000003221bb9d0c2b011905b4926e0000000a0900da8b0800000014b45940fee18f00008a392ae9ef24a47de1aac0001c38a190000000148031000000de8000857245660420ae57d1e3a12682de3d5029e000000081aa9843629c022aea0f2480a5d89f0147c00000000ff938861193f44a70490000000003c249e96b0000000085468d922c68b241e75c1c0845f8e3407300009cb800031d21968098b8868f0d3c81900006c1807200002b6931a7b44ea096279a1242396188a51d9694174150446e1ec2072a1f29ec00008a10e741c2048400006f858422e842f26e000000000000000202910ea2808d620080000002092000000000000000000f4e7a609360000772991800000024a89038000403000017c800000000001f50000000000060b000000000005f5800010ba904000043800000006e0093c7d7a0127e924c218381e204980008db12445e3a796024a6786a513fc000131c926877c337911c34800003bd092e0000a5000018a63b71a6e00020809659c7600021d031f064c43f1e5207616283d126746f8844292c80000211432000
  | 44 => 0x996808860fcc57e97121ef9e0e2ed985e9c729daa621e2073b830222b95c052709c866e0502000186a6fea19c0000a2c000000003512525ea95eca0b80000001ed8467a65e36b9bbc5e2000000000007d3a9aca65a816363800024200009661416000000067c835c92d2626095002833e1cbc714235e6c8a57063418ee3a1946247c87220038cea27a21a494b855427921e22c5076285d032c10b242c519a4e03281bb443ea1703531ef495627740000000000253400017a65ab032ea5424dc25d85506470dea00019fa9de1f2a00582d866101c620d173432c25f69f796225d8807e575852639a00001c6800026b0570000000003607e89fd07e29e19b545f4000074618322fe1d8a00000002bf800000025de0000f8235a0d6e50e23ba172800040d876056c81d600029a24aa043a2cf04e22979c14a2285483da13629ea8b9c59c0000000015293d8000000250e36d0000000000000000007d2a0d400004a010a80008998a805a61ac4000277a623056e1fd1af6000047a547a70278b01ac7911bb861480008fc08f20de011a5dd861600000004890c6e000006091800008710588000000000013c04d300007dd26a834a82a66b38ef27770c5600000002091fce33c1a7c7a2249630400004fd924600715d4000123e56516e080c000000016fa00000002c001344591ae800000001330fc29c7995e7b31fba7be8fd043286ca4be83a68918000000000068fa7e64f691b69b080007b826be11d214c11a9d7209100000cf800000022583411d1e2cf84dc61c1df4337000029129e00001dc026980009e40000984967a6009fe65b58000615002a00019a44f288804e805f047a00001439bc60001cb43b818224f5a6920c014d000022d00000000000000029080007e68b524878d70244a86a92da3c0522000023805de9b8987a2538c0c4ed031816c8b488518cb495b1ebe24a9a464bf108827e851227f13ba1f800004489a6400000000ae9fbc05f0cfa00020a270c9ad272500006bb8f6600008e200001ba5d60f221680cd200018948e91a9000009300000c164339ac8948a6ae53200002a70d5a96c800000000002a205620000bd00000000215a7b679ba5fa7310dd679f896e4b589a09d61d1c9328b863c9858e2218f20000275c3770aa619f133477294c201883f650ea33c73b0ea057f25d25f6983a43925e023186a04af818206788900001b746c40a229e080000000000a6e9a18000052e7bf80004f9227e32b813c2e516f000000006ff800000028500000000000000002300000fc8000000234a403800000000003138dac0000000526045a0000000000126c85d80006d2a1aa44d29e61d1837493680009bb22103560000000000000011040001e740000f7c566800072a00000000000414022400005e0a04000000000000001f6e000000
  | 45 => 0x8c22b26d039ca98e21c913e9ba000043700000aa02961c628dc00010c89bf8000a081ad81c91ffa0ba1bf82289bca47095ee3e300002599ab8000074a5560000000000066e90b200029240000000000000000000005aca37070f06ea02d00000e61cd65b0801200000009608000628846800000001dd0c5a94c00009ce000088180000001ff26a6196200001d29d21f90058a9dc09d1c2c0df800029f12f41cb82f440796488c78f6000028120001d5c691003a000046e18d12089db80000000000a1d000000013ce3ed0e8a45500006e9134014c000001d22fc00019860b11c6867525800001b9a00028520f699280001be81f486b4451a454000210e6cea84803b243242427709bd9634142800000010fe00000009df000000017ba0000000000049c73ea2c0000148e1ce0a9e7bb91ce3210000137800081b99e64a696a45338b440002216a5e19ca000180600000004ad94a85fe00005cb800000000000000000000000053b00003c193bc1c280000000cc26e225944d7214054c8a2a000043258f03469f299f869e1fae6401f16a2ea0c4000196a8f626e662e9d78421153624d14026a69e9a00000002a40000000020e6830a16088800054800002b100008fe273a1d300003dd14429a39472235289253d22ac43e239e00003ba77d90968bb8abe022061e8ab84165741eec555287c8ad0000260800015a285a636800000000004cb000065e8000000165e804026c8268a8a00024f295700006d184c6037893a646992044c920074e9f2004880fa7be05ec8ad8bd812504b65670f8e61f1f308170ec078618ea460937c4ee0000000000026617e26dd8c904789c2086f1e5ea17a4862a5068800021a023e94fe57284c01a40b5089c1ca01a78e4226d22d232d9b3e0d6013e32c967851325ee62d235c26c1abe6ef94520000000000089400026287a816c40041b7e67a800000000008a580005c6a814928924a985250400000000000000256a72277912c650292da8f59c6c8420924a599b8c58e0ee45330ed270f940621729608b6800062b0000331a9de688a2261f0184e1c00c9c25b075e6c3035a5fc17041fc157c35e804a2c1975c00000000001d96a571b6e83b800000000004e692f089a18586002752948159087397e699d939e99080000001dbe000139400000004ec0000000000000021369d18000000279c8ce00003620c1a80b07d8507000000000003b196629f48bbc391082801c00008a891b44d680008fd162e5e116e671ca0c20d3898e3798b581d00d3291b9ccc52087a4663043c31328de098a75e542a43e2711c7e5de15de87b0bfe5eb84641ac0f125951b9855d1cc057185ce2f38e840000b408390f46277888801aa11c43a8e0274e132697f8b70538954e22d1d2c1861f1e5da29e8109134a8189faca2e230e3238d5e8c
  | 46 => 0x1cca2fa800048e85206a0a51c89421260411a76764090e275a7604239b147e7232a6cba8da5f4a8c09cc030c0e6a84600000001ee8e6666b8000000000000021ba323064897a039243685340001d020000a36000193c0cd072ca0113543f98c0a2ef800000001b877c80ca42e800005d22f66698000000298a0000000000229c1c1a65417d22940001abc00000000001f70000075811c1e4a000155e0000efa002a87054f8458547291a420828a04da35419d00003eea420000299c00000000bf28f4000000000004c400011302b980000a417c800000004be1bf438881ce0001c580000fc00001e8477f8000548800000003c85898000000000099812b20b1a66ea1e0c6016e11843f39aa254218ae000000080e9c5400015d20000000000000000005809f8800059019fe16f0000000000008610b630d9d149f428e817213e846885060001c1688e800082e928836519561430000218000053b80003c090a253801644f08a7e00024ba07b9a086ca0000000088400020f05e91e8231a1eae0000000261904026280008e2911a000000035480000001658839914e09710e200009e0000207a00024ae4a321221770042815255071f00008258000087211289d21b8978a23e00028903ab06bc1750f1a69704aa8be218e2ec091c8a010180001ec629a9c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3c64dd530440e7ae021baa60880021fa1f654c1100043e43eca9822000c3c74d953044079cb061b2a60880022fa1b744c1100061fb2ee89822000c3c65dd1304400117d0fb2260880022f21f644c1100061fbaec89822000c3c75d913044001970c93b440880038e19365881106855d436c91022013ab88458e20440035d104b1c40880123ea1a71881100065c324e3102203ea7a8694620440c9c70c928c40880031e1db65481100071c326ca9022000e6862d9520440235750db2240880032e1db644811000c7c43ac69022011ab88458d2044001d50c9b1240880032e190714811028d3d434a29022032c787694520440bfc70c928a40880035c1c651481101e63d3b6cb8822000e3864d9710440115750db26208813b2e9db64c411000c7d436e58822000cb864dcb1044001970c8b9620880071e9d952c41102cf1c322a5882204fa7a8694710440078f4ed28e208815f8e19251c41100051ec20a3318200387e87dd563040010fb09baac6080021f60b7558c100043f40eeab18207387e871d563040010ff0aba2c60800e1f2157458c100247c402e8b18200087e87d5163040070f90faa2c6080021fa1d5458c100043e43aa8b182003c5c7594d63040091b90ea9ac6080123721d4358c100256c40286b18200087e87d4963040070f90fa92c6080021fa1c5158c100051ec20a2b1820018f980dd162040091f100ba2c4080029b60b545881069f1c202a8b1020048ec8754962040091d90ea12c40834baa10142588100051ec20a2b102000a6d8214562040034d905bb2a4080029be0976548100043fc3ac6a90200087c8758d52040074dd0eb12a40800e9b21d625481000637ba2c4a902000c6d745895204001cd680b12a4081039a101625481020735082c4a90200093d841c552040c18dcc438aa4080031b58871548100043fc2aed990200387c855db32040010ff0abb2640800e1f215764c8100246e43ac699020048ec8758932040011eb0c38a64080c61fe1d63944101ed9c422e1288200387e85dda31040010fb0bbb4620800a2fa13768c4100045ec26ed1882004cda7058e31040010ff0abb0620800e1f215760c41068de24126218820059b8845c031040658dcc5bac42080123be1d628841000637baac510820008fb865c2210400b37108b8442080031e1d776440100065c3a6ec8802000c7b54dd910040018f2a9bb220080031ed4b76440100063c28eec8802000c7b76dd51004001a70e9baa20080f2dc2077544010684dd43ee88802000cbb76dd11004001970e8b1220080031edd9524401020e9c3a2a48802000e6962549100407d2f50f28a20080031edda51440101ee9c3a4a2880203eb7287945100419fae50f28a20080f35cdda514401000739bb4a28802000f3374945100419de60e928a2008002dce153144010
  | 1 => 0xd09bb2a4880028f61376549100043f434eca922000c3c649d952440014db053b2a4880021fe1276549100043ec24eca92200087d829d952440018db053b2a4880028fe1176549101c51e422eca922000a5f835d952440014b906bb2a4880029be0976549100043f430eca922000c3c641d952440010ff083b2a4880021f610765491001c3fc10eca92200387d821d952440c10f9023b2a4880031e88076549100063c900eca922038a3e86d91524400187cedb22a4880030f1db64549100061fc3ec8a922000c3c87d9152441ab87ee5b22a4880038bdcb64549100043f43cc6a92200087d8798d524407147d0931aa4880028f61263549100043fc3ac6a92200087c8758d524400147f08b1aa4880e28f211635491000537c12c6a922001a6c8258d52440010fd0c38aa4880024f61071549100061fb20e2a922000c3c641c552440010ff0abb6648800e1f21576cc9100045fc22ed99220028bc845db32440070fd0bbb264880021f617764c9100145f426ec99220008bd84dd932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011bf06bb264880023de05764c9100061e324ed28a2033a3e86d92514400187cedb24a2880030fe1f649451025e1e43ec928a20d4c3e71d925144001c6ce3b24a2880021f61e639451019d1f424c728a2000a3d8498e51440010ff0eb1ca2880028fe11639451019d1e422c728a2000a6f8258e51440654d904b1ca2880ca1f21972945100061fb22e528a2000c3c645ca51440658d8c4b94a2880021fe1f629451000636b96c528a200087f8758a514400147f08b14a2880ce8f21162945100052fc1ac528a2000a5c8358a514407d0f90cbae62880030f19175cc5101e43fc3ecb98a200087d87d97314400187cebb2662880030f5d764cc5100065c322e198a203e87e86dd53144001878c9baa62880021fa1f654c5101e43e43eca98a2000c6c72d95314400187eebb2262880030f1d7644c51000656396c898a2000ccc72d8d3144001998e431a62880031bd97724c5100063632ee498a2000caf64dc93144001958c9b9262880032e193704c5100043f436eb10a2000c3c64dd621440070fd0fb2c42880ca1f21f65885100061fbaec910a2000c3c75d92214407d0fd0dbaa42880030f19375485103043f43eca90a203c87c87d95214400187eebb2242880030f1d764485100062fb2ee690a2000c5c65dcd214400193ec9b9a42880032719373485100062fb28e690a2000c5c651cd214400193ec839a428800327190734851013666310e690a2000ccc73d892144001970c9b82428805b3518d71cc1100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d930440070f90a3b2608800a2f210764c1100043f436ea9822000
  | 2 => 0x47458d100043f43ea8b1a200387c87d51634400187ee9aa2c68800b0f1d35458d106ce36396a8b1a200087e8755163440010f90eaa2c6880030fdd15458d100161e3a2a8b1a20d8c6c7255163440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018df0bb92c6880031b2177258d1000637aa6e4b1a2000c6d54dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d1001c3e43ea4b1a2000c3f74d4963441af878e9a92c6880031bdcb5258d1000e36396a4b1a200387e85dc563440010fb0bb8ac688003391cb7158d100043f438a2b1a2000a3d84145634400187ee828ac68835b0f1d05158d1000637b90a2b1a2060c6c721456344001970e9b82c68800237e1d6318d1000566412c631a2000a3d841446344001878ebb26c4880030f1d464d891000536c16ebb122000a6d821d762440010ff0aba6c48800e1f21574d89100047dc02e9b1220048f8805d362440010fd0faa6c48800e1f21f54d89100043e43aa9b12200087f855cf62440070f90ab9ec4880021fa1c51d89100051ec20a3b122000a6d8214762440070fd0dbaac4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac48800a2fa1b74589100061fb2ee8b122000c3c65dd1624400117d0fb22c4880030fdd764589100061e3aec8b1220008be87191624400187eea322c4880030f1d464589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100062fb28e6b122000c5c651cd624400193ec839ac48800327190735891000666310e6b12200387e87dd562440010fb09baac48800e1fa0775589100045fc22eab1220028bc845d562440011bf06baac48805a3720d75589100043f438eab1220028be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd1624400187ea5ba2c4880030f54b74589100043fc2ae8b12200387c855d162440011bf06ba2c48805a3720d74589100047dc02e8b1220008be871d1624400187eea3a2c4880030f1d474589100043f43ea8b12200387c87d51624400187ee9aa2c48800b0f1d354589100043f43aa8b12200087c87551624400187ee8aa2c48800b0f1d154589100b46f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317d4b73589100062ea96e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000c5f541cd62440018baa839ac48800317d4873589100062ea90e6b122000ccc73dc962440019a8e7b8ac4880021fa1c51589100051ec20a2b122000c3f7414562441ad878e828ac48800317dcc51589100062e398a2b122000cb874dc1624407147
  | 3 => 0x5b222000a3e86d4b64441af87ceda96c8880024fa1c51d91100051f430a3b2220d6c3e76147644400147b05baec8883528fa0775d91100061fb8eebb222000c3d71dd7644400187ce1baec8880030f1c375d91100051f42cebb222000c3d751d7644400147d0e3aec8880030fa1c75d91100051ec10ebb22204ba3e811d7644400147d0b39ec8880028f61673d91100051fc2ae7b222000a3c855cf6444001c3ea729ec8880028fa1672d91100051ec2ce5b222000a3f855cb64440014790ab96c8880028fa1472d91100051ec28e5b22204eaba801cb644400157300396c8880028fa1f52d91100051e43ea5b222000a3e81d4b644409b47b0b296c8880028fa1632d91100051ec2c65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000ab6810cb644400156b02196c88813aaea0032d91100055cc0065b2220008be87147644401517b0e28ec8880028fa1c51d91100061f438a3b22200083e8714764441b587b0e28ec8883528f21c51d91100051ec10a3b22204ba3e81147644400147d0b90ec8880028f61721d91100045f43843b22200a8bd87087644400147d0a10ec8880028f61421d91100054f41843b222000a9d83087644409d5750010ec8880eeada0770d91100045f43ea1b2220008bd87d43644400117d0f906c8880022f61f20d91100051f42e41b222000a3d85c8364440015ab02196c688002b660032d8d100051ec20a3b1a2000c3e74d96634400187ce832cc6880030fd957498d100061e32ae931a2000c3e75d92634400187aebb24c6880030f9d46498d100061eba8c931a200087f845d663440010ff04bacc6880030fa157498d100061ec2ae931a200387f87d5263440010fb0faa4c68800b0f9d35498d100061eba6a931a200087f8755263440010fb0eaa4c68800b0f9d15498d100061eba2a931a200387f87d4a63440010fb0fa94c68835f0f9d35298d100061eba6a531a200087f855c663440070f90ab8cc6880021f61c5198d100051ec20a331a20d6c3e74146634400187ae828cc6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a2000c3f65dd16344001878cbba2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880021f6137558d100043ec16eab1a20008bf845d5634400517908baac6880023be097558d1000c76412eab1a2000c3f75dd16344001878ebba2c6880030fe177458d100061e42ee8b1a200087f855d163440070f90aba2c6880023be097458d1000c76412e8b1a20008fb805d1634400187eea3a2c6880030f1d
  | 4 => 0x2840070fb05bb2a5081031e8837654a100063c906eca942000a6f825d952840010ff08bb2a5080021f6117654a102143fc12eca942000c6f825d9528400127b0838aa5080123be1d62cca100063b32ee29942000c76651c532840650ff0cb94a3080cb1b98972946100043ec3ac528c2000c6d7258a51840010ff0cbae63080021fe1d65cc6100043ec36ea98c200087c8759531840018d8e4b2a6308003331ca634c61000666392c698c2000c6e65dc931840018dacbb92630823f95995310c6106e5e24126218c200087d86dd521840650fd0eb2a43081821f21d65486100062f32ee690c2000c5d65dcd21840018bcca39a430800317594734861013667310e690c2000ccc73589218408f4f30d28a41081169e61a51c42100043f436e9b2a200387f87d93654400187ae9b26ca880021f61e64d95100043fc3ac9b2a200b87d87193654400187ae8326ca880030f61c64d95100071ac08c9b2a2000c3c645cb654400147d09316ca880028f61262d951005c3ec38c5b2a2000c6d7218b6544001c68c920eca880f29d21941d95100069bba283b2a2000e346450765440010fb05ba6ca8835a1fa0774d95100043ec3ce9b2a2000c3f845d365440010ff04ba6ca8800e1f20574d95100043f438e9b2a2000c3d741d365441b74ed023a6ca880f29d60474d95100062eb98e7b2a200087e87d0f65440010fb0fa1eca880021fa1c43d95100043ec3887b2a200087f845cb65440070f902b96ca880f29ea0072d95100053cc00e5b2a200087e87d0b65440010fb0fa16ca880021fa1e42d95100043ec3c85b2a203ca7a8090b65440014f301216ca880021f61d42d95100043f43885b2a200087d8710b65440010fd0f196ca880021f61e32d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb65440794f500196ca880029e60032d95101e43f43e83b2a200087d87d07654400187ee9a0eca8800e1fe1e41d951019c3e43c83b2a20d687f8750765440790f90ea0eca880030fdd141d95100053dc0283b2a203ca788050765440010fd0e20eca8802e1f61c41d95101e43f43e43b2a200087d87c8765440010fd0e10eca8802e1f61c21d95100051f42043b2a2000a3d8408765440014bd0610eca880029760c21d95101e53d40043b2a2039a7681dc365440010fd0fa06ca880021f61f40d95100043f43e41b2a200087d87c83654400147d09906ca880028f61320d95100051f436ebb222000c3e76dd76444001a6ee3baec8880028fa1875d91100061f3b0ebb222000c3e76d97644400147b05b2ec8880022f61e65d91100051f42ccbb2220008bf87597644400147d0c32ec8880030f9d865d91100051ec10cbb222000a3e8598b644400147b0b316c8880028fa1462d91100051ec28c
  | 5 => 0x80e28fa107654b100051ec20eca96200087e87d8d52c40010fb0fb1aa5880e28fa136354b100051ec26c6a96200087e8798d52c40010fb0f31aa5880029be096354b1000d36412c6a962001a6e8218d52c40014db0431aa5880024f6107154b1001c3f42ced996200087d859db32c400517d093b665880022f61276ccb1000c6f41ced996200387e85dd932c40010fb0bbb2658800e1fa16764cb100043ec2cec99620028be849d932c400117b093b265880063721d634cb1000d66412c6996200387d87d8e51c406747d09b1ca3880028f61363947101e43f43cc728e202d87d8798e51c40af67108b84a3880226e211700c7100b66d31ae018e20089b8845c221c40019aac638a61880021f60b745961069c3ec3ce8b2c2000c3f749d1658400187f08ba2cb080021fe09745961069e1f202e8b2c20d3c3c405d165841bf0fd0e3a2cb080030f5d074596100062fb9ce6b2c200087e87d0d65840010fb0fa1acb080021fa1c43596100043ec3886b2c200087d84dc9658400147d09392cb080028f61272596100253d404e4b2c20dea79809c965840010fd0fa12cb080021f61f42596100061fba684b2c200087e8790965840010fb0f212cb080129ea0242596100053cc0484b2c200087e87509658400187ee8a12cb080021fa1c42596100043ec3884b2c200087e878c965840010fb0f192cb080021fa1c32596100043ec3864b2c2000a3e840c9658400147b08192cb080029da0432596100053ac0864b2c2004a7a800c965840014f300192cb080028fe1171596100051e422e2b2c20dda7b805c565840010fd0fa0acb080021f61f41596100061eba682b2c2000c3f7490565840670ff0ea0acb0835a1f21d41596100061eba282b2c2000a7b8050565840094f100a0acb0803a1fa1c41596100043ec3882b2c2000c3f7410565840010fd0f90acb080021f61f21596100743f43842b2c200087d87085658400147d0810acb080028f61021596100052f41842b2c2000a5d8308565840094f50010acb080029e60021596100161f3a2a931c2000c3d7455263840091b906b94c7080028f6105198e100061fba2a8b1c2002c3c7455163840091b90ea1ac70801237a1e3258e100054ec2064b1c2000ad5810c963840095b500192c7080028f6105158e102043ec3ceab142000a3d849d562840814db053aac50810a9be097558a1001c3f42ee8b14200087d85dd162840091f501ba2c50800e1fe1f5458a100043ec3ea8b14200087f87551628400187ee8aa2c50800b0f1d15458a1001c3f42ee6b14200087d85dcd62840091d90ea12c5080021f61c5158a100051ec20a2b142000a6d82145628407147d09bb2a5080028f6137654a100043fc26eca942000c3e84dd952840010fb09bb2a5080030f6137654a100041ec26eca94200387f82dd95
  | 6 => 0x1c3fc3ea831a400087d87d5063481b38f2e1aa0c6900021fe1d5418d200043ec3aa831a40d8c797055063480010ff0ab88c69000e1f2157118d2001c3fc38a231a400087d87144634800147b08288c6901831e5c05118d200051ec24ebb0a400387f875d761480010ff08baec29000e1fa1774d85200043ec2ee9b0a40018f980dd361480070ff0faa6c2900021f61f54d85200043fc3aa9b0a400087d87553614800187ee8aa6c29000b0f1d154d85200053a40aa9b0a4000a3d8414761480011ef0eb08c290002b520d611852000c7cc06ea30a40018f980dd061480091f100ba0c2903671e5c354185200161f3a2a830a4000c3d7455061480014e902aa0c2903631e5c154185200043fc2ae630a400387c855cc614800147b08288c2900029b60851185203063cb80a230a40008f9871006148001c72a8200c2900029da0776945200051fc22ed28a4033a3c845da51480014ed023b4a2900021fe1d63945200043e43ac728a4000a3f8458e514806747908b1ca2900029de0563945200053a40ac728a400087e8718e51480010fb0e31ca2900ca9e21970945202fd9c422e128a40018f8865c331480070fd0b3b462900021f616768c52000c7c432e118a400387e859d931480010fb0b3b262900063b208764c5200043fc2aec18a400387c855d8314800117f08bb0629000a2f211760c52000c7c432e018a40119b8845c0314802d9b0c6b8062900033c185700c5200063c3b6ea9824000d3874dd53048001ad0e5baa60900466ea1f744c1200065c3b6e89824000da874dc930480012f50f28a60900cb1e1da514c1202fe9c3a4a298240028be84dd763c400117b09baec7880021fe1175d8f100043fc12ebb1e200387e85dd363c40010fb0bba6c7880030f9d674d8f100061ebace9b1e2000c3e755d363c400187aeaba6c7880030fa1574d8f100061ec2ae9b1e200387f87d5363c40010fb0faa6c78800b0f9d354d8f100061eba6a9b1e200087f8755363c40010fb0eaa6c78800b0f9d154d8f100061eba2a9b1e200387f87d4b63c40010fb0fa96c78835f0f9d352d8f100061eba6a5b1e2000a3d8414763c41ad87ce828ec7880030f5d051d8f100043fc22eb31e200087f825d663c407d0f902bacc78800e1fe1f5498f100043ec3ea931e200087f8755263c40010fb0eaa4c78800e1fe1f5298f100043ec3ea531e200387f8714663c40010fb0e28cc7880028f6105198f100051ec20a2b1e20008df8758c63c400587ce8aa0c7880030f5d15418f100051ec20a231e2002c3e7455362c400187ae8aa6c5880028f61051d8b1000536c10a3b162000ab8845c362c4001c72a8206c588002bc60440d8b1001c3f42ee6b16200087d85dcd62c400147b0828ac5880038e5504058b1000578c0880b162000a6d829d952c40014df04bb2a58
  | 7 => 0xd88050d63880070fd0bb8ac7100021f6177158e200043f438a2b1c400387c87145638800147b0828ac7100123ea0375986200247d406e930c40dfc7a70d52618800587ce8aa4c3100030f5d1549862069e3d382a930c40d3e3840552618800147b0828cc3100fb1e9c051986200247ac3c8330c404eeb0409066188001c6aa8a0cc310012bc20141986200047cc3e8130c400387e87dd561880010fb09baac3100021fe15745862001c3e42ae8b0c40088fb805d161880091f100ba2c3100021fa1f545862001c3e43ea8b0c400087e8755161880010f90eaa2c3100f21fa1c51586200051ec20a2b0c40048f4875056188001c6aa8a0ac310012bc20141586200053b40eed28c403ca7a80dda51880794f50131ca3100021fe1d63946200043e43ac728c403ca7a80986518807d0ff0eb0ca310192ce211709462001c3f42eed18c400087d85dda318800517d09bb463100022f613768c6200247d406ed18c4004cda7058e31880091f501bb263100021fe15764c62001c3e42aec98c400087f855d831880070f90abb0631004e6e211700c6200069c3a6ea98440e09ba87dd130880012f50f28a61101934e1d2514c22000c7cc06e9b1a400087f855c763480070f90ab8ec6900028f61051d8d2000536c10a3b1a4002c3e74552634800187ae8aa4c6900021fe157198d2001c3e42ae331a4000a3d8414663480070fd0fbaac6900021f6137558d200043fc16eab1a400087d82dd563480010fd03baac6900022fe117558d200145e422eab1a40008f7815d563480011e902baac6900021fa1c7558d200145f43ee8b1a4000c3f75dd16348001878ebba2c6900030fe177458d200061e42ee8b1a4000c3f52dd1634800187aa5ba2c6900021fe157458d2001c3e42ae8b1a40008f7815d163480011e902ba2c6900022fa1c7458d200061fba8e8b1a4000c3c751d163480010fd0faa2c69000e1f21f5458d200061fba6a8b1a4002c3c74d5163480010fd0eaa2c6900021f21d5458d200061fba2a8b1a4002c3c7455163480070fd0bb8ac6900021f6177158d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063b42ee2b1a4000c7585dc563480018eea9b8ac6900031d5537158d200063ba96e2b1a4000c7552dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200063bc28e2b1a4000c74851c563480018eea838ac6900031d5507158d200063ba90e2b1a4000c75521c563480010fd0e28ac69000e1f21c5158d200051ec20a2b1a4000c3f7414563481ad878e828ac6900029b6085158d200063bb88a2b1a4000c747114563480011bf0eb18c690002b52056318d200043fc22ea31a404287f825d463480810fb04ba8c6900021f2057518d200
  | 8 => 0xeaa2c4180123b21d425883001c3f42ee2b10600087d85dc5620c0070fd0a38ac4180021f61471588300145f420e2b1060008bd841c5620c0031bb0638ac4180021f61c51588300051ec20a2b106000a6d82145620c0010ff09bb2a4180021f613765483001c3fc16eca90600387d82dd9520c0010fd03bb2a4180029be0976548300043fc22eca90600087d845d9520c0018df04bb2a4180021f20576548300043ec30e2a90600093d841c5520c07d4ed03bacc2180028f61075984301e53b408eb308600087f855d2610c0070f90aba4c2180021fa1f549843001c3e43ea9308600087c87552610c00587ce8aa4c2180030f5d154984300043fc2ae5308600387c855ca610c0010fd0fa94c2180021f21d52984300051ec20a330860048f587906610c001c6aa8a0cc218012bc201419843001c3f43eeab08600087d84dd5610c0010fb05baac2180021fe15745843001c3e42ae8b08600087e87d51610c0070f90faa2c2180021fa1d54584300043e43aa8b08600087e87d49610c0070f90fa92c2180021fa1d52584300043e43aa4b08603c87e87145610c00147b0828ac2180123d21d41584300071aaa282b086004af080505610c0014ed03bb4a2180021fe1376944300043ec26ed288600087d82dda510c0018ed03bb4a2180021fe1176944300043ec22ed288600087f825da510c0070f902bb4a2180021fe19729443019637312e5288600087d8758a510c0018dae4b14a2180fa1fe1d619443001c3e42eec988602d87d86dd5310c0010fd0eb2a62180621f21d654c43000636392ca9886000c6e65dc9310c0018dacbb92621800e1f21776884300043fc2aed108600387c855da210c0010fb0dbac42180021fa1d65884300043e43acb10860048f587986210c0070f90bbb242180021fe15764843001c3e42aec908602e8df835d9210c0010fb0dbaa42180021fa1d65484300043e43aca9086016c5c73595210c0018bccbb9a42180031759773484300b66639ac49086016cd473985210c0091e90eb0a42180031e1d7764c0300065c3a6ec9806000c7b85dd9300c0018f10bbb260180031ed53764c0300063caa6ec9806016cda53dd9300c0019b2a7bb260180031ed4b764c0300063c28eec9806000c7b76dd5300c001976edba260180031edd9524c0300063dbb4a29806000b5b854c5300c1bf8f4e1aa4c71000b0f9d15498e200061eba2a931c40d3c7a7055263880010ff0ab8cc71000e1f2157198e200b66a18ae331c4000a3d84146638807d8f4e028cc71000e1fa1f7558e200043ec26eab1c400087e81dd563880e70fd0e3aac7100021fe157458e2001c3e42ae8b1c40048f8805d163880010fd0faa2c71000e1f21f5458e200043f43aa8b1c400087c8755163880078b8eb29ac7100123721d5358e200246e43a86b1c4004a
  | 9 => 0x76945300043fc20ed28a600087d841da514c0010fb043b4a2980031da04769453019d1f436c928a6000c3e76d92514c001878edb24a2980030fe1f64945300061e43ec928a60e3c3e71d92514c001c6ce3b24a2980021f21972945300061fb22e528a6000c3c645ca514c0010ff0fb14a29800e1f21676cc53018c3e432eb98a6000c3c645d7314c02dab060bae62980021fe1f65cc5300e43ec3ecb98a6000c3e75d93314c00187aebb26629838a1fa1b754c5300061e326ea98a600087e87d95314c0018d8e5b2a62980030fdd7644c5300061e3aec898a6000cac72d91314c0018decbb9262980031b197724c53000657b26e498a6000cac64dc9314c0019c8e5b0a6298003391c8614c5300065c326e098a600387e859da214c0010fb0b3b442980021fe15768853001c3e42aed10a60008bf845da214c00517908bb4429800e1f21476885300043f436eb10a6000c3c64dd6214c0010fd0fb2c42980021f21f65885300061fbaec910a6000c3c75d92214c0070fd0bbb242980021f61776485300145f426ec90a60008bd84dd9214c0070fd0b3b242980021f616764853001c3e428ec90a60168dc831d9214c0010fd0dbaa42980030f19375485300043f43eca90a600087c87d95214c00187eebb2242980030f1d764485300062fb2ee690a6000c5c65dcd214c00193ec9b9a42980032719373485300062fb28e690a6000c5c651cd214c00193ec839a429800327190734853039e3d3b6cb9826073e5b63d97304c0e5974edb2660980021f60b74594300043f40ee8b2860d387d879d1650c00187ee93a2ca183869ee0174594300253c402e8b286000c3f845d1650c0010ff04ba2ca180021f20574594300063dc02e8b2860d3c78805d1650c1a787c80ba2ca1834f0f10174594306fc3f438e8b28601887e87d0d650c0010fb0fa1aca180021f61372594300043f40ee4b28600087e87d09650c0010fb0fa12ca180021fa1e42594300043ec3c84b286004a7a80909650c0014f301212ca180021fa1d42594300043f43884b28600087d87109650c0310fd0f192ca180021f61e32594300051f420e2b286000a3d841c5650c00187d0838aca180021f61071594300061ec20e2b28600083d841c5650c0010fb0438aca180021fa1f41594300043ec3e82b286000c3d74d05650c0010f90f20aca180021fe1d41594300043e43a82b286000c3d74505650c0014f700a0aca180129e20141594300043f43882b28600087d87105650c0010fd0f90aca180021f61f21594300043f43842b28600087d87085650c00147d0810aca180028f61021594300b52f41842b286000a5d83085650c0094f50010aca180029e600215943020536c14eab106042a6f825d5620c0070fd0bba2c4180021f617745883001c3fc3ea8b10600087d87d51620c0010ff
  | 10 => 0xb126000c7765dc5624c0018e8cbb8ac4980032dd9371589300065a326e2b126000c77651c5624c0018e8ca38ac4980032dd9071589300065a320e2b126000ce4621c5624c07147d09bb2a4980028f61376549300043f434eca926000c3c649d9524c0014db053b2a4980021fe1276549300043ec24eca926000c6d829d9524c0010fd033b2a4980028fe1176549301c51e422eca926000a6f825d9524c0014ef02bb2a4980029d20576549300061e320eca92600087f841d9524c0010fb083b2a49800e1fe08765493001c3ec10eca92600087e811d9524c0018f4403b2a4980031e48076549301c51f436c8a926000c3e76d91524c001878edb22a4980030fe1f64549300061e43ec8a9260e4c3f72d91524c001c5ee5b22a4980021fa1871549300049ec20e2a926000c3f641c5524c001878c838aa498003930cb654c93000746196c8992601c87d87d97614c0014ed03b2ec2980029da0465d85300061f3aec9b0a6000c3d75d93614c00187cea326c2980030f5d464d85300051ec24ebb0a600087f845d7614c0010ff04baec29800e1fa1774d85300043ec2ee9b0a60168f980dd3614c0070ff0faa6c2980021f61f54d85300043fc3aa9b0a600087d87553614c00187ee8aa6c29800b0f1d154d853001c3fc3ea5b0a600087d87d4b614c0014ed03a96c2980021fe1d52d85300043ec3aa5b0a6000a748154b614c00147b0828ec298002b560c21d853000578c0043b0a6000c3e74d96614c00187ce832cc2980030fd9574985300061e32ae930a6000c3e75d92614c00187aebb24c2980030f9d464985300061eba8c930a600387e86dd5614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c865585300145f436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c001958e4322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980030f1d764185300061e3a8c830a60008f787584614c0015c904b08c2980029da0775185300051ec20ea30a6000a6d821d4614c0014ed023a8c2980021fe15741853001c3e42ae830a600087e87d50614c0070f90faa0c2980021f21d54185300161f3a2a830a6000c3d74550614c0010ff0ab90c29800e1f21572185300043f43ea430a6000a7681d48614c0010f90ea90c2980071b9c9521853000636b92a430a6000a7481548614c00147b08288c298002b560c211853019d1f426ed28a6000a3d84dda514c0014ed03bb4a2980030f19276945300043fc24ed28a600087d849da514c0010fb053b4a2980028fe11769453019d1e422ed28a600087e861da514c001878c83b4a2980029da04
  | 11 => 0x4c00147d0810eca980028f61021d95300052f41843b2a6000a5d83087654c0e74f50010eca980029e60021d95303352f41ee1b2a600087e87d03654c0010fb0fa06ca980021fa1f20d95300043ec3e41b2a6000a3e84c83654c00147b09906ca980028fa1b75d91300061f3b6ebb226000a3e861d7644c00187cec3aec8980030f9db65d91300051ec16cbb226000a3e81d97644c00117b0f32ec8980028fa1665d91300045fc3acbb226000a3e86197644c00187cec32ec8980028f60865d91300051f408cbb226000a3e8598b644c00147b0b316c8980028fa1462d91300051ec28c5b226000a3e86d4b644c1af87ceda96c8980024fa1c51d91300051f430a3b2260d6c3e76147644c00147b05baec8980028fa0775d91300061f386ebb226000c3c70dd7644c00147d0b3aec8980030f5d475d91303955d400ebb226000ab9801d7644c00147d0e3aec8980030fa1c75d91300051ec10ebb226000a3e811d7644c001c75003aec8980038e60075d91300070fa9ca7b226000a3e859cb644c00147b0b396c8980028fe1572d91300051e42ae5b226000a3e851cb644c00147b0a396c8981caaea0072d91300055cc00e5b226000a3e87d4b644c0014790fa96c8980028fa0752d913038d1ec2ca5b226000a3e858cb644c00147b0b196c8980022fa1c32d91300dc5ec3865b226000a3e850cb644c00147b0a196c898002ada0432d91300055ac0865b226072aba800cb644c00147d0bb8ec8980028f61771d91300061fbaee3b226072aba80dc7644c00157301b8ec8980028fa1671d91300051ec2ce3b226000a3f855c7644c0014790ab8ec8980030fdd571d91300045f438a3b2260008bd87147644c00147d0e28ec8980030fa1c51d91300041f438a3b226000c3d87147644c0014790e28ec8980028f60851d913037d1f408a3b226000a3e85c87644c00147b0b90ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec898002a7a0c21d91300054ec1843b226072aba80087644c0015730010ec89819ea7a0f70d91300045f43ea1b2260008bd87d43644c0e5c74a1a86c8980022fa1f20d91300045ec3e41b226000a3e85c83644c00147b0b906c8980030f1d764d89300061e3a8c9b126000a6d82dd7624c0014db043aec4980021fe1574d893001c3e42ae9b12600087e87d53624c0070f90faa6c4980021f21d54d893001c3f42ce3b12600087d859c7624c00517d0938ec4980022f61271d893000c6f41ce3b12600087f855c7624c0070f90ab8ec4980021fa1c51d89300051ec20a3b12600087e87d95624c001878e9b2ac4980021fa1c65589300061e3a0cab126000c3f65dd1624c001878cbba2c4980022fa1f64589300061fbaec8b126000c3c75d91624c00117d0e322c4980030fdd464589300061e3a8c8
  | 12 => 0x29da07769473019d1f424ed28e6000a3d849da51cc0014ed023b4a3980021fe15768873001c3e42aed10e60018f58798621cc0010ff0abb2439800e1f21576487300b66a39cc290e60018f48758521cc02d9a8e6b0a43980029b60b5458a300247643aa4b1460048ec87509628c0070fd0bb8ac5180021f6177158a300051ec20a2b146000a6d82145628c0034d905bb2a5180029be097654a3001d3743ac4a946003a6c87589528c0018dee8b12a5180031b5d16254a300049ec20e2a946060c6e621c5528c0018dac438aa51800b0f9d154986300061eba2a930c6000a748154a618c00147b0828cc3180123d61e41986300071aaa28330c6004af080506618c0070fd0fbaac3180021f61375586300043ec16eab0c600087f855d1618c0070f90aba2c3180123e20174586300043f43ea8b0c600387c87d51618c0010fd0eaa2c3180021f21d54586300043f43ea4b0c600387c87d49618c0010fd0ea92c3180021f21d52586300053a40aa4b0c603c87e87145618c00147b0828ac3180123d21d41586300071aaa282b0c6000a7681dda518c07d0ff0eb0ca3180021fe15768863001c3e42aed10c6032c6e62dd6218c0018deeab1443180021fe15764863001c3e42aec90c600087e86dd3654c0070ff0fb26ca980030f5d364d95300043ec3cc9b2a600087f87593654c0390fb0e326ca980030f5d064d95300061ec38c9b2a6000e1d83193654c001c38c921eca981ce9721943d95300070e32287b2a6000c3c645cb654c00147d09316ca980028f61262d95300e43ec38c5b2a6000c6d7218b654c00127b0938eca980030f19271d95300043ec16e9b2a600087e81dd3654c0010fb0f3a6ca980030fe1174d95300043fc12e9b2a600087c815d3654c0010fd0e3a6ca980030f5d074d953072d2f418e9b2a6073a5d831d3654c0e70fd0fa1eca980021f61f43d95300043f43887b2a601c87d8710f654c0010ff08b96ca980021f20572d953000636b90e5b2a6073a7a801cb654c0014f300396ca980021fa1f42d95300043ec3e85b2a600087e8790b654c0010fb0f216ca981ce9ea0242d95300053cc0485b2a600087d8750b654c0010fd0e216ca980021f61c42d95300043ec3c65b2a600087e870cb654c0390fb0e196ca980028fa1032d95300051ec2065b2a6000a76810cb654c0014eb02196ca981ce9ea0032d95300051f424e3b2a6000a3d849c7654c00187d0938eca980021f61271d95300061ec24e3b2a600083d849c7654c0010fb0538eca980021fa1f41d95300043ec3e83b2a6000c3f74d07654c0010ff0f20eca980021fe1d41d95300043e43a83b2a6000c3f74507654c0014f700a0eca981ce9e20141d95300043f43883b2a600087d87107654c0010fd0f90eca980021f61f21d95300043f43843b2a600087d8708765
  | 13 => 0x62fba0c728a4200c5d7418e51485cf8bee431ca290b9f175c8639452173f2ac08c728a42e8c5e7118e5148401cace231ca290b9f9308463945213043e432eb98a4216c5c635d731484650ff0fb2e62908021f61f65cc5210062f3aec798a4200c5d75d8f314842d998c6b96629080395144638c5210072a31ca318a4216ad4839da3148401caeca31c629080395194638c5210072baa0c718a4200e555418e31485cdcaea431c6290b9b95548638c5213043f436ea98a420087e87d9531484650f90fb2a62908cb1b1cb654c5210062fbaec698a4200c5c75d8d314845d998e5b1a629080317dd4634c5210062e3a8c698a4226ccc7218d3148401ca8a231a62908031bd97724c5210063632ee498a4200ccc63dc931484658e8ed28a62908031d1db754c5211963a3b6ca98a422ecd476dcd314845db88e5b9a62908bb351db634c5210b66a3b0c698a4200e546518d31484579c8edb92629085ab5219310c52147f2a32a6218a4260a6e86dd621484c16cd03bac42908cb99d87658852115c76c3cc710a4226ace8398e2148401c9eca31c429080393194638852100727ba8c710a4200e4c7518e2148401c9ea831c429080393550638852113762c08c710a4226cce7118e214844dd8ce231c429080393144638852130537434a310a4200e4c639462148465ccec328c4290803b118e318852100d724326310a4200ec4634c6214840587ce8aa6c0908030f5d154d81210051ec20a3b024200e395410360484015d304206c090802bc60440d81210062fb2ce73024200c5c659ce60484018becab9cc0908031719573981210062f3aec73024200c5d75d8e60484018bcea31cc090803175d4639812101c3f436eab02423287c86dd560484010fd0fb2ac0908030f1d365581210043f438cab024200c3c74195604840187ecbba2c0908030f19774581210062fb2ee6b024200c5c65dcd60484018beca39ac0908031719473581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d60485b99aee231ac0908023ee1d60181210055c422c0302420387e85dc562cc0010fb0bb8ac5980028f6105158b3000536c10a2b166000a6d829d952cc0014df04bb2a5980e28fa107654b300051ec20eca96600093d841c552cc00587ce8aa4c3980030f5d154987300053a40aa930e6000a3d8414661cc0010fb09baac3980021f60b75587300051ec20eab0e600087f855d161cc0070f90aba2c3980021fa1f545873001c3e43ea8b0e600087e8755161cc0010f90eaa2c39800b0f9d154587300061eba2a8b0e6000a748155161cc0010fd0fa92c39800e1f21f52587300043f43aa4b0e600087c8754961cc00147b0828ac398
  | 14 => 0x77114563484c18eae2328c69080237e1d6318d210052fc2ac631a4200a5c8558c634842d1b906ba8c69085a3720d7418d216ce3ab8ea831a4202c3e74550634840187ae8aa0c690b631d5c55418d210b62fbaea631a4200a5e85d0c63484014bb0ba18c6908028f6105118d213063ab88a231a420087f855c063484070f90ab80c6908022fe117018d210145e422e031a42acc5e76d9463484014bb09b28c690a67955c76518d214cf2610eca31a42008dd8799463485d14bd0b328c69080237e1d6518d217b56bc0aca31a42e7a5e8619463485eb8bcec328c690802976106518d2176f2ab88ca31a42ede572119463485dbc9842328c690bb7950846518d210046ec3cc831a4200a5e8599063484014bb0b320c690bd2b56066418d210046fc3ac831a4200a5f8559063484014b90ab20c690802b6e016418d210056c402c831a4200a5e8519063484014bb0a320c69080297a1b5418d210052e436a831a42f3c5e76d5063484014bd0caa0c690802972195418d217962f3b2a831a42e7a5e86144634840163b08288c69085b17dd67518d210052f42ce831a4200a5d859d063485dd4bf05aa0c690bba9760b5418d210052f40ea831a42f1e5571d5063485e3c9843aa0c690bc2976165418d210070faa4a831a4200e1f845506348401c3ce8aa0c690803875d15418d217852fc12a831a42f0a5d8255063484014b902aa0c690bbf955c55418d2177f2610aa831a42eea5e85150634844d59d05a88c690802b360b5118d2100567c12a231a4226acc82544634840153d08288c690802a76105118d210070f420a231a4200a5d841446348401c3b08288c690802876105118d217452fc10a231a42e8a5d8214463485dbcaae2288c690bb795c845118d2176f26108a231a42ede542114463484014bd0ba08c690802976174118d210070eaa68231a4226ace82d04634840159b05a08c690802972164118d217676210c8231a4200a5f8550463484014b90aa08c690803875514118d2100567c128231a4226acc8250463485d7d8842a08c690802b6e014118d210056c4028231a4200a5e8510463484014bb0a208c69080297e157018d210052e42ae031a4200a9f845c0634840153908b80c690802a7a135018d210054ec26a031a4226ace82140634840159b04280c69080297a174018d210052ec2e8031a4200e1d54900634842d1bd0e200c6908023761c4018d210052f4288031a4200a5d851006348401c3aa8200c69089ab3a084018d2100566c108031a4200ad68110063484015ab02200c690ba7179db63945210062fba6c728a4200c5d74d8e51485d58bee5b1ca290bab175cb639452174e2f38ec728a4200e5671d8e51484010fb0f31ca290a6697a0e63945210043fc3ac728a4200a6f8258e51485594bd0c31ca290ba3179d8639452100
  | 15 => 0xe20eca9088e1f61c41d95210051fc22e1b2a4200a3c845c365484010fd0fa06ca908021f61f40d95210061fba481b2a420087e8710365484010fb0e206ca908030fdd040d95210052f41881b2a4200a5d8310365484654dd04206ca908029b60840d95210053b40881b2a4200a758110365484018baeba9ec69080f171d653d8d2101c6fc3aa7b1a4200a5e85d0f63484014bb0ba1ec69080a37e1d43d8d210052f42887b1a4200a5d8510f634840147b0828ec6908029761365d8d210052ec20cbb1a4200a5e8599363484014bb0b326c69080297e1564d8d210052e42ac9b1a4200adb8059363484015b100b26c69080297a1464d8d210052ec28c9b1a4200a5e86d5363484014b90daa6c69080297a1954d8d210052e432a9b1a42eaa5e86147634840163b0828ec690803175d475d8d210052f42ce9b1a4200a5d859d363484014bd0a3a6c6908029761474d8d217cd2fc16a9b1a42f9a5d82d5363484014bd03aa6c69080387d5254d8d210070fc22a9b1a42f8a5f8255363485f14bb04aa6c6908029720554d8d210072ba8ca3b1a4200a9e84147634840153b0828ec69080387a1051d8d210052ec20a3b1a4200e1d84147634840143b0828ec690ba697e0851d8d2174d2ec10a3b1a4200a5e85d0763484014bb0ba0ec6908038755341d8d210052e42c83b1a4200a5f8550763484014b90aa0ec6908038755141d8d210056dc0283b1a4200ad88050763484014bd0a20ec6908029761441d8d210052f42ee1b1a4200a5d85dc3634840153d09b86c690802a761370d8d210052f42ce1b1a4200a5d859c3634840153d09a86c690802a761350d8d210052f42e81b1a4200a5d85d036348401c3aa9206c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c6908038755040d8d211756741081b1a4200acd8210363484015ad02206c690802b560440d8d210b62e31aeb31a4200c5e75d8e63484018baebb1cc6908021fe117598d210043fc12eb31a420087d825d663484070ff0faa4c6908021f61f5498d210043fc3aa931a420087d8755263484010fb0e28cc6908028f6105198d210043f43ecab1a420087e8719563485ef8eee232ac69080e1fa1f7558d210043ec26eab1a420087f82dd563484010fb05baac69080237e0d7558d2100477c12eab1a42008f7815d563484010fd0e3aac6908021fe157458d2101c3e42ae8b1a42008df835d163484011df04ba2c6908023ee017458d210247c402e8b1a420087e87d5163484070f90faa2c6908021fa1d5458d210043e43aa8b1a4200c5f75dcd63484018b8ebb9ac6908031bdd77258d21006363aee4b1a4200c6f85dc963484018d90bb92c6908031bd537258d2100636aa6e4b1a4200c7475dc563484010fd0e28ac6908028f6105158d2100637b90a2b1a42f7c7
  | 16 => 0x18c6210072b31ca318c4232d66729463188559e886528c63108cb1d5db658c621005b2c16cb18c42acf4432d963188401caecb31c63108ae7961f328c621175e341e6518c420087e87d9531884658d8e5b2a63108bb331cb634c6210046f438c698c4226ccc7218d3188401ca8a231a63108031bd97724c6210063632ee498c422e9ce87cc9318846199eed9926310bf3d1147324c621196b2394a298c4200f473294531884018e8ebbb26310803591cb754c621004bb43eca98c4200b6582d953188465ac8e5b2a63108bb711cb734c62100ceb43ec698c4200bc582d8d318845db88e5b1a631080275a1c634c6210072a328c698c4226dc47218d31884033cd0fb92631080339ddb724c62115de241ee498c422e9e687cc9318840178d0f99263108bb71a1f324c621174e343e6498c4230dc776cc93188401d8eed9926310803d1dd7324c6217e7a23ae6498c4200f4765cc931885f9e88cb9926310befd1d53324c6217dfa2aa66498c4232c6e72d9431885d14ed03b28631080237e1d630c62100637b2ae418c428fe54654c4318844d789049886310803715c9310c6210051ec20cbb044200a3d8419660884010fd0fb2ac1108030f1d365582210043f438cab044200a3d841956088401878e832ac1108030fd9774582210061e32ee8b04420387e87dd560884010fb09baac1109821fa0775582210045fc22eab0442028bc845d5608840517d0fba2c1108030fdd774582210061e3aee8b044200c3f85dd160884018790bba2c1108030fd4b74582210061ea96e8b04420087f855d160884070f90aba2c1108030fdd474582210061e3a8e8b04420087e87d5160884070f90faa2c1108030fdd354582210161e3a6a8b04420087e8755160884010f90eaa2c1108030fdd154582210161e3a2a8b04420e87e8794560884650f90f28ac1108030fdd2515822119e1e3a4a2b04420087e8714560884070f90e28ac1108028f61051582210061fba0a2b0442d6c3c7414560884014db0428ac1108028f61065182210047dc3ac03044200ab88458060884010fd0dba6ca9080e1fe1f64d95210061eba6c9b2a420087d8799365484014bd07326ca908029760e64d95210043fc3ac9b2a4200a5f8359365484014b906b26ca908029ee0164d95210053c402c9b2a422387d87193654840187ae8326ca908021fe0b74d95210043ec16e9b2a420087d879d3654840187f08ba6ca908021fe0974d95210043ec12e9b2a420087e871d3654840187ae83a6ca90803175cc73d95217d53b408e7b2a4232a75811cf65484010fd0fa1eca908021f61f43d95210043f43887b2a420087d8710f65484650fd0fa0eca908021f61f41d95210061fba683b2a42d687f8750765484650f90ea0eca908030fdd141d95210053dc0283b2a4200a788050765484010fd0
  | 17 => 0x2c4200c3d741936588401acae538ecb108029b60b74d96210053b40ee9b2c4200c6d82dd365884010fd03ba6cb108031da0774d96210043ec3ce9b2c4200c3f749d3658840187f08ba6cb108030fd0974d96210061ea12e9b2c4200c3d741d365884014db043a6cb108029da0474d962100536c16e7b2c4200a7681dcf65884018bae639ecb108029b60873d96210053b408e7b2c420087e87d0f65884010fb0fa1ecb108021fa1c43d96210043ec3887b2c4200a3e849c7658840147b0938ecb10bff1b5ca71d96210071b424e3b2c4200e35849c765884018ece738ecb108031d1ce71d96217f63ab94e3b2c4200e65729c765884010fb0fa0ecb108030fdd341d96210043fc3c83b2c4200c3d7490765884010ff0ea0ecb108030fdd141d96210053dc0283b2c4200a788050765884010fb0e20ecb108030f5d041d962100536c16e1b2c4200a7681dc3658840147f08b86cb108028f21170d962100536c10e1b2c4200a76811c365884010fd0fa06cb108021f61f40d96210061fba481b2c420087e8710365884010fb0e206cb108030fdd040d96210052f41881b2c4200a5d8310365884654dd04206cb108029b60840d96210053b40881b2c4200a75811036588559c9865b2ec7108028f61065d8e2176e3b388cbb1c42008f681dd7638840587ce8aa6c7108030f5d154d8e210051ec20a3b1c4200a6d8214763885db8ece228ec710bf69da076598e210051ec20cb31c4260c767119663884010ff08bacc7109821f2057598e2101c3fc3ea931c420087d87d5263885b38ece3aa4c7108021fe1d5498e210043ec3aa931c42d8c767155263884070ff0e28cc7108021f61c5198e210051ec20a331c4260c767114663884c12ed03baac7108021fa1f6558e210043f438cab1c4200a3d8419563884070fd0fbaac7108021f6137558e213043f40eeab1c420087e871d563884010ff0aba2c71080e1f2157458e210047dc02e8b1c42048f8805d163884010fd0faa2c71080e1f21f5458e210043f43aa8b1c420087c8755163884018deebb92c7108031b1d77258e210043f438a2b1c420387c87145638840147b0828ac7108029b6085158e217453b40eca31c4200a3d8419463884011bf0eb18c71080b0f9d15418e210061eba2a831c4200a3d8414463884010ff0ab80c71080e1f2157018e210045fc22e031c42028bc845c063884c16cd03b2e65108ba3be1d63cca21174e7c3ac79944200e4f6558f328845db8ce738e65108c23be1971cca211943f43cc728c422d87d8798e51884630ff0eb1ca3108ca1f21d639462119637c32e528c4232c6c865ca5188465acf02b94a3108cb5920572946211963730ae528c4232d66615ca51884016cb03994a3108025be0975cc6210043ec3ecb98c42fda7681d97318845799aed99663108cb1d5da5
  | 18 => 0xc4014df04bb2a4188e28fa1076548310051ec20eca906240a7a801d9520c4014f3003b2a418803179db73548310052ec30e6a906201a6f86589520c4074dd0eb12a41880e9b21d625483100637ba2c4a906200c6d74589520c44dc9f06b12a41889b9320d625483100727b9ac4a906200e4c73589520c401ccac5b8aa4188024f610715483130637310e2a906200c6d621c5520c4014eb0c38aa41880355dcc7154831006aa398e2a906200e65621c5520c4018eb0c38aa4188034da1071548310069ac20e2a906200d56831c5520c401aab0638aa418bb759988715483176e3ab10e2a906200d65621c5520c5dbaac6438aa418bb7550c8715483147e2e3b2e7288628fd56715ce510c44d1bf0eb16621889b339c962cc431004afc3aa59886200e4d6254b310c4016a902a966218c0a5761e51cc43180f2b31ca31886216ec43258a310c401ccac4a9462188031d147764c4310063bbb4a29886200d5451dd9310c4018b8ebbb2621880395147764c4310062faa6ec9886200c5d54dd9310c4018bea5bb2621880317147764c4310062fbb6ea98862269ce87dc9310c40199eedb926218803d1147724c43100667bb0e49886200d4f751c9310c401a98ea3926218803d1144724c4311346e43ac49886226ccc72589310c401ca8a2b1262188025721d524c4310062fbb2a49886226d4c72549310c401c9ac4a926218802d5205524c431804af43ca29886200c5f76945310c533a98e528a6218a3ed5a06514c4310063a3aeec9886200c7754dd9310c4018eaa9bb262188031dd4b764c4310063bbb6ea9886200ce776dc9310c4019ceec3926218803591d4724c431736e3b98e49886216ec732589310c4012e90ea9262188031ddd9524c43100732b12a4988620087d84dd5600c4010fb05baac0188022fe1175580310145e422eab006200c3f75dd1600c401878ebba2c0188030fe1774580310061e42ee8b00620087f855d1600c4070f90aba2c0188030fdd474580310061e3a8e8b00620087e87d51600c4070f90faa2c0188030fdd354580310161e3a6a8b00620087e87551600c4010f90eaa2c0188030fdd154580310161e3a2a8b00620087e87d49600c4070f90fa92c0188030fdd352580316be1e3a6a4b00620087e87549600c4010f90ea92c0188030fdd152580311c61e3a2a4b00620e87e87945600c40187ee928ac0188cf0f1d251580310043f438a2b006200a3d84145600c40187ee828ac018b5b0f1d0515803101e3c3aca0b0062168f887541600c405970e9202c0188038e55240580310b47c43a80b00620087e86dd365884012db05ba6cb108025da0774d962101c3fc3ec9b2c4200c3d74d9365884010fb0f326cb108030fdd264d96210043fc3ac9b2c4200c3f7459365884014f700b26cb108029e20164d962112c3ec38c9b
  | 19 => 0x29b614641893100537436a83126200a6c86d50624c5e7c9ec7aa0c4988029ba19541893100536432a831262f2e4f63550624c4014dd0c288c498802cb61051189317af27b18a231262f7e6761144624c4010fd0d3b2a4988031b18a765493100536c14eca926200c6f729d9524c4010ff093b2a4988021f612765493100636c14eca926200a5f835d9524c4014df04bb2a4988029de05765493100637b90eca92620087f841d9524c4010fb083b2a49880e1fe08765493100637c10eca92620387d821d9524c4018d9043b2a49880317cc876549310062e990eca926200c76211d9524c4018ea423b2a4988069ba1b6254931006363b6c4a926203a6e87d89524c4074d90fb12a4988031bdd3625493100636ba6c4a92620093d841c5524c4018dec438aa4989831b18871549310062e32ced992622eccc629db324c4018bcedb2e64988039318b65cc93100d67436c59926200cce76d8b324c45d998c538e64988031d197714c9310063a328e29926200ce7621c5324c4018b8edb2a64988039318b654c93117567436e49926201ccc76dc9324c40359d0db1264988af331db624c93113666310e29926200d54511c5324c401b8ee438a64988ca1f219729453119636312e528a620087f87d8a514c4018dae5b14a2988ca9ba1b6294531006373b6c528a6200c6f87d8a514c4018dee9b14a2988031b5d362945310073338ec528a6200c6e7618a514c5594bd0d994a298ad7179db3294531197263166528a6232a5c864ca514c5678bcec994a2988cb93189329453118c3e432eb98a6200c6c625d7314c45b0fb0fb2e62988031b9d762cc53100636baec598a6216dc7325cb314c401cc8ca31662988029d21952cc5311746e432e518a622eccc625ca314c45d59d0db14629880393d94628c53100726328c518a6200a5c8654a314c45dc98c4a94629880395d97618c53180d2f434a318a62ace4c62946314c40587ce8aa6c0988030f5d154d81310051ec20a3b026200e3954103604c4015b306206c098802bc60440d813100637396cb3026200c6e72196604c4018decab94c0988031b1957298131006373aec53026200c6d75d8a604c4018dcea314c0988031b5d4629813101c3f436eab02622d87c86dd5604c4010fd0fb2ac0988030f1d3655813100636396cab02620087e87195604c401878e832ac0988031b1c865581310061fb2ee8b026200c3c65dd1604c4018decbb92c0988031b19772581310047743ec4b026200c6f75d89604c4018d8ebb12c0988032bdd36258131006563a6c4b0262008ee87189604c4018deea312c0988031b1d4625813100657ba0c4b026200cac74189604c4011f70eb00c098802ae211601813100536c16a8b1062168ec87549620c42d1d90ea12c4188028f610515883100536c10a2b106200a6d829d9520
  | 20 => 0x77c3a85b126200a6e8550b624c4010fd0e28ec4988028f61051d893100536c10a3b12620087f855c3624c4070f90ab86c4988022fe1170d89310145e422e1b126200a6e861d7624c4014db09b2ec4988029b61065d89310053742cc9b126200a6d85993624c4014df0ab26c4988029b21564d893100575c02c9b126200ae880593624c4014dd0a326c4988029b61464d893100537436a9b126200a6c86d53624c5b38dcedaa6c4988029ba1954d893100536432a9b1262d8c6e76553624c4014dd0c28ec498802cb61051d893100536c26ebb126200c6e871d7624c4014db083aec4988029ba0475d89310053742ce9b126200a6d859d3624c4014df0aba6c4988029b21574d893100575c02e9b126200ae8805d3624c4014dd0a3a6c4988029b61474d89310053743ea9b126200a6c87d53624c4014dd03aa6c4988038bd5254d89310053743aa9b126200a6c87553624c401c5f08aa6c4988029b20554d893100727a9ca7b126200a6e85d0f624c4014db0ba1ec4988029ba1443d893100536c2887b126200a6e85dc7624c4014db0bb8ec4988029be1571d89310053642ae3b126200e6751947624c40155d0828ec498802ab61051d893100537438a3b126200e2e84147624c4014db0828ec4988038b61051d893100516c20a3b126200a6e85d07624c4014db0ba0ec4988038b55341d89310053642c83b126200a6f85507624c4014d90aa0ec4988038b55141d893100575c0283b126200ae880507624c4014dd0a20ec4988029b61441d89310053742ce1b126200a6d859c3624c4014df0ab86c4988029b21570d893100557c22e1b126200aac845c3624c40155d09a86c498802ab61350d89310053742e81b126200a6d85d03624c401c5aa9206c4988023ba1c40d893100476c3881b126200a6e85103624c4014db0a206c4988038b55040d89310056741881b126200acd83103624c4015cd02206c498802b960440d893100636316eab12620087e87d95624c4010fd0e32ac4988031b9db651893100536c3eca3126200a6d84d94624c401c5ce9b28c4988038b5d3651893100726b9eca3126200e6571d94624c401cd4e1b28c4988039a5c3651893100476c3cca3126200a6e85994624c40159b07328c4988023be1d651893100567c1aca3126200ae781594624c4014dd0c328c4988031b9d8651893100537c38ca3126200a6d84194624c401c5ce8328c4988038b5d0651893100727398ca3126200e4d73194624c4c14d902328c498803999c4651893100732b88ca3126200e6a70194624c401cd2e0328c4988023b61e64189310053742cc83126200a6d85990624c40159b07320c498802b9606641893100477c3ac83126200a6f85590624c4014d90ab20c498802b3e0d641893100575c02c83126200ae880590624c4014dd0a320c4988
  | 21 => 0x84dc1628c4014db053b2a5188029be097654a311c51f420eca946200a3d841d9528c4018baedb9aa5188024f6107154a31736e2190e29946200c5e755db318c4018baecbae63188ba37e1d62cc63117667392c598c620095f8754b318c53d2bb0f28e6318802d561e51cc6314f6aac3ca398c6200d5576947318c401caaed28e63188030fdd154582310161e3a2a8b046200a3d84145608c4011f70eb00c1188021fa1b74d953101c3fc3ec9b2a6200c3d74d93654c4010fb0f326ca988029ba0a64d953100536c14c9b2a620087f87593654c4014df04b26ca988029b20964d95310053dc02c9b2a6200a7880593654c45b0fb0e326ca988030f5d064d953116c3ec38c5b2a6200a3e8418b654c40147b08316ca988031b5c862d95310053d400c5b2a6200a798018b654c4010fb05ba6ca988021f61e74d95310061fc22e9b2a620087f825d3654c4010fd0e3a6ca988030f5d074d953147d3b40ee7b2a620087e87d0f654c4010fb0fa1eca988021fa1c43d953116c3ec3887b2a6200e1d4310f654c4010ff08b96ca988028fa1072d95310051ec20e5b2a6303a5e831cb654c4014bb06396ca98a229da0472d95310053ac08e5b2a6200a7a801cb654c4014f300396ca988021fa1f42d95310043ec3e85b2a6200c3d74d0b654c4010fd0f216ca988021f61e42d95310053d40485b2a6200a798090b654c4010fb0ea16ca988030f5d142d95310043f43885b2a620087d8710b654c4010fb0f196ca988021fa1c32d953116c3ec3865b2a6200a3e840cb654c40147b08196ca988029da0432d95310053d40065b2a6200a79800cb654c51f4bd07b8eca988021fa1f41d95310043ec3e83b2a6200c3f74d07654c5ad0ff0ea0eca988ce1f21d41d95310061fba283b2a6200a7b80507654c4014f100a0eca988021fa1c41d953116c3ec3883b2a6200e3541107654c4010fd0f90eca988021f61f21d95310043f43843b2a622d87d87087654c40147d0810eca988028f61021d95310052f41843b2a6200a7a80087654c4014f30010eca988028fe1170d95310051e422e1b2a620087e87d03654c4010fb0fa06ca988030fdd240d95310043f43881b2a620087d87103654c40187ee8206ca9880297a0c40d95310052ec1881b2a6200a6e82103654c4014db04206ca988029da0440d95310053ac0881b2a620087e87c83654c4010fb0f906ca988028fa1320d95310051ec2641b2a620087e87083654c4010fb0e106ca988071b9db52d893100536c16ebb126200a6d821d7624c4010ff0aba6c49880e1f21574d89310047dc02e9b1262048f8805d3624c4010fd0faa6c49880e1f21f54d893100536c16a9b12620087c87553624c4014df04aa6c4988031b61f52d893100536c26a5b1262038ef8754b624c4014dd0ba16c4988029b61742d8931014
  | 22 => 0x322cb988030fdd2645973101c3f43ac8b2e6200c3f7459165cc4630fd0f312cb988031bdca62597310b727994c4b2e620087d82dd165cc4010fb0f3a2cb988030fdd274597310061fc22e8b2e620087f825d165cc4010fd0e3a2cb988c61fa1f43597310043ec3e86b2e6216e1c4350d65cc4010fb09b92cb9885a97a0e725973182d2ec1ce4b2e6200a77815c965cc6094e902b92cb988021fa1f42597310043ec3e84b2e620087e8790965cc4010fb0f212cb988029ea0242597310053cc0484b2e620087e8750965cc4010fd0e212cb988021f61c425973118c3f43c64b2e620087d878c965cc5554bf06b8acb988029be09715973100536412e2b2e620087e87d0565cc4010fb0fa0acb988030f5d3415973119c3fc3a82b2e62d687c8750565cc40187ae8a0acb988029ee0141597310053c40282b2e623187e8710565cc4010fb0e20acb988021fa1f21597310043ec3e42b2e623187e8708565cc4010fb0e10acb988028fa1021597310051ec2042b2e6216a5e8308565cc4014bb0610acb988031bdc821597310053d40042b2e6200a798008565cc40147d09b82cb988028f61370597310043f43e80b2e620087d87d0165cc40187ae9202cb988021fa1c40597310043ec3880b2e6200c3d7410165cc42d4bd06202cb988029760c40597310053741080b2e6200a6d8210165cc4014ed02202cb988029d60440597310043f43e40b2e620087d87c8165cc40147d09902cb988028f61320597310043f43840b2e620087d8708165cc4014db053aac5988029be097558b3101c3f42ee8b16620087d85dd162cc4091f501ba2c5988023e6037458b3101c3fc3ea8b16620087d87d5162cc4010ff0eaa2c5988021f61c5158b310051ec20a2b166200a6d8214562cc4070fd0bb82c5988021f6177058b310145f426e0b1662008bd84dc162cc4010ff09bb2a5988021f6137654b3101c3fc16eca96620387d82dd952cc4018be65bb2a598803174cb7654b3100536c14eca966200a6f825d952cc4010ff08bb2a5988021f6117654b3100637c12eca966200c77815d952cc4010fd0e3b2a5988031d5db7154b310049ec20e2a966200c75761c552cc4012eb0c38aa5988031d6187154b310069b420e2a966200d35841c552cc5ef8eec438aa598bdf1d5887154b317beab990e2a9662f7d55321c552cc4018bccbbb2659880317dd9654cb31006aa288e2996623287f865ca51cc4658dcc4b94a3988021f61d629473100636b92c528e6232a5d86cca51cc54d8baed994a398802d5a0732947314cd2fc326528e62a4c5d764ca51cc40187ee8aa2c19880b0f1d154583310051ec20a2b066200e395410160cc42d5b506202c198802ba608405833100578c0880b066200a3d84145628c4070fd0bb82c5188021f6177058a310145f426e0b1462008bd
  | 23 => 0x58a510061fba4c8b14a232a6e8299162944650f90eb22c5288030fdd16458a5119e1e3a2c8b14a20087e87191629445f2ed0239ac5288ca1fa1e6358a5119537414c6b14a23287c8758d62944018b8e6b1ac528bea9da046358a51865b340ec4b14a200c3f42dd1629440187a85ba2c528c2e1fa077458a510061fba4e8b14a200a6d829d162944014df04ba2c5288030fe117458a5100637c12e8b14a20387c815d162944010fd0e3a2c5288030f5d07458a5100536c14e6b14a200a6f825cd62944018bae639ac528bea9da047358a511953ac08e6b14a20087e87d0d62944010fb0fa1ac5288021fa1c4358a510043ec3886b14a232a6e8210d62944014db0421ac5288ca1fa1f4158a510043ec3e82b14a200c3f74d0562944654dd05a0ac5288029b60b4158a518543e43c82b14a20087f8750562944650f90ea0ac5288030fdd14158a5100537c1282b14a232a6c8250562944014f700a0ac5288029e2014158a510043f43882b14a22387d8710562944014bd07382c5288029760e7058a510051fc22e0b14a200a3c845c162944010fd0fa02c5288021f61f4058a510061fba480b14a20087e8710162944010fb0e202c5288030fdd04058a510052f41880b14a200a5d8310162944654dd04202c5288029b6084058a510053b40880b14a200a758110162944012ed033b665288025da0476cca51194aec3cc7994a200c5c7658f32944010ff0cb8665288021f21970cca510049fc22e1994a23393c845c332944018ecc3bb265288025da06764ca51004bb408ec994a200c76611d932944652b90eb1a6528803171d9634ca51195a6412c6994a20095e83dd360944012bb07ba6c1288025da0774d82511e43ec3ec9b04a233c3e74d93609440187ae9b26c1288f29ea0364d82511e43ec3ec5b04a200c3f74d926094467878e9b24c1288ce1fe1d649825119e1f3a2c9304a200c3d7459260944014f700b24c128803175ce63982510053cc04c7304a23287f8758a60944658dce4b14c1288031b5c9629825184db940ec1304a23393e87dd1609440187f0dba2c1288030f98774582510069b30ee8b04a200c3e60dd16094401878c1ba2c1288024fa1c74582510061fba6c8b04a233c3c74d9160944790f90eb22c1288030fdd1645825119e1e3a2c8b04a20087e87d8d609440187ee9b1ac1288f21f21d63582510061fba2c6b04a200c5c7358d609440187ee9b12c1288030f1d362582511e43e43ac4b04a200c3f745896094401878e8b12c1288031bdc962582511cdb940ec0b04a23387d865d060944670fb0fb20c1288cf0f9d364182510061eba6c8304a308c7671d90609460f8ece2b20c1288021f61e63182510062eb98c6304a200a798018c60944658dce5b10c1288025ee1d6018251836b938ac0304a20087f865d165cc4630fd0f
  | 24 => 0x6640387e85dc560cc8010fb0bb8ac1990021fa1c515833201c3e438a2b066400a3d8414560cc80187ee828ac19935b0f1d051583320059ac20a3b0a6400b6582147614c8070ff0ebaec2990021fe1175d85320063bc0aebb0a640387e85dd3614c8010fb0bba6c2990123ea0374d85320047cc06e9b0a640387f87d53614c8010fb0faa6c2990021fe1d54d85320043ec3aa9b0a6400a7481553614c8018eaeba8ec2990028f61051d85320063aba8a3b0a6400ab584147614c8014eb0e28ec2990031d61c51d85320071b420a3b0a6400a7584147614c801c6b0828ec2990028d61051d85327ed3bc10a3b0a64fda7582147614c8014e90b20ec29900a3de1d41d85320053a42a83b0a6400e3554507614c8015e100a0ec2990023de1d61185320053a42ac230a64e6ad783584614c80166b08288c299002d9608511853200c6ec1eea30a64018dd83dd0614c9b38bae7aa0c29900b0f9d154185320061eba2a830a64d8c5d73550614c8014e902aa0c2990028f61051185323062eb98a230a6400a6d82144614c80156b08288c2990031d61c51185320071b420a230a6400a7584144614c801c6b08288c2990028d61051185320072b418a230a6400e5583144614c9dbcaae6288c2993b799a0851185327453ac10a230a6400e6582144614c801cce64288c2993b7958c8511853276f2a190a230a64ede6432144614c8051eb0f208c2990029d21641185320053a42a8230a6400e3554504614c8015e100a08c2990021fe15701853201c3e42ae030a64008bf845c0614c80517908b80c29900b0f9d154d81320061eba2a9b02640087f855c7604c8070f90ab8ec0990028f61051d813200536c10a3b0264008fb87580604c8012ed03ba6c7288f25ea0374d8e51004bcc06e9b1ca23387d87d93639446787ce9b26c7288030f5d364d8e510052f41ec9b1ca23c97a80dd263944012f301ba4c7288ce1fe1d6498e5119e1f3a2c931ca200c3d7459263944014bf06b24c728a5ed5a076398e5119c3e43ac8b1ca200c3f745916394467878e8b22c7288029720d6458e5147dab40ec6b1ca20097681dd063944670fb0fb20c7288cf0f9d36418e510061eba6c831ca200a5d83d9063944010ff0eb18c72880257e1d6318e5187eab38ac631ca28fe566158c63944014bf0eb18c72880317e1d6318e5187e2f38ac631ca200c5d635c86394603aace7388c7288039558e7118e510049fc22e031ca23393c845c063944012ed03ba6c5288ca1f61f64d8a5119e1f3a6c9b14a200c3d74d9362944010fb0f326c5288030fdd264d8a510061fba2c9b14a233c3c7459362944650fb0e326c5288030f5d064d8a518263b38cc7b14a200c5d7318f62944654dd0431ec528c3a9da0463d8a5186e3b388c7b14a20093f845c3629446727908b86c5288ca1fa1e64
  | 25 => 0x8010fb0e218c2a90030f5d043185520061eba68230aa400c3d74904615480187ae8a08c2a90029ee0141185520053c4028230aa400c3d74104615480147d09b80c2a90028f61370185520061eba6e030aa400c3d749c0615480187ae8b80c2a90028fa1070185520051ec20e030aa400c3d741c061548014bd06380c2a90029760c70185525ed36c10e030aa40087e87d0061548010fb0fa00c2a90030f5d340185520061eba48030aa400c3d7450061548014ef02a00c2a90029d20540185520043f4388030aa40087d87100615480187ae8200c2a900297a0c40185520052ec188030aa460a6e8210061548014db04200c2a90029da0440185520053ac088030aa40093d879d3605487127f0eba6c0a90030fa1974d81520061fb12e9b02a400d2f625d3605480187cc0ba6c0a90030f18174d81522043ec3ec9b02a438c3e74d93605480187ae9b26c0a90e30f9d164d81520061eba2c9b02a43796f825cf60548810fb0fb1ec0a90030f5d363d81520062f39ec7b02a400c3d7458f60548014e902b1ec0a908e5b60a71d81520061f3a4c3b02a400c3d7498760548810fb0e30ec0a90028f61061d81520061f3a0c3b02a400c3d7418760548018ece230ec0a94531b5cb64981521c43fc3ac9302a400c3d745926054a278dae4b24c0a9003175ce63981520053cc04c7302a400a3d841866054a25ad2e5b04c0a93661f21b7458152004afc1ae8b02a40095c835d160548012df04ba2c0a90025de057458152004ba40ae8b02a44087c87591605480187ee8b22c0a90e30f1d164581522053c402c8b02a40087e87d8d60548014e902b1ac0a90031ddc661581520051ec20c2b02a511d6b72d8160549b10fb0cba0c0a90e21f61f64181521c61f3a6c8302a400c3d74d9060548014f301b20c0a90030fdd164181520043ec3cc6302a400c5d7318c605480147b08308c0a90031d9c46118152004bdc3ac0302a510b6b8258060548031bd07bacc39900637a0f74987326ce2f39ea930e6402c3e7455261cc80187ae8aa4c399363179cd54987320051ec20a330e6460c5e7314661cc8070fd0fbaac3990021f61375587320043fc2ae8b0e640387c855d161cc8011f700ba2c3990123e20174587320043f43ea8b0e640387c87d5161cc8010fd0eaa2c3990021f21d54587320051ec20a2b0e640387e87dd560cc8010fb09baac1990021fa0775583320045fc22eab0664028bc845d560cc80517d0fba2c1990030fdd774583320061e3aee8b066400c3f85dd160cc8018790bba2c1990030fd4b74583320061ea96e8b06640087f855d160cc8070f90aba2c1990030fdd474583320061e3a8e8b06640087e87d5160cc8070f90faa2c1990030fdd354583320161e3a6a8b06640087e8755160cc8010f90eaa2c1990030fdd154583320161e3a2a8b0
  | 26 => 0x29d60663985528dd37c12c730aa51ad6572d86615480127f08b84c2a90e24f21170985520043fc32e8b0aa40095f835d161548012b906ba2c2a90025be097458552004bdc02e8b0aa440978805d161548010fd0fb22c2a90e21f21d64585520061fba2c8b0aa400c5f64dcd61548018bac9b9ac2a900317d8b7358552006a7b16e6b0aa400c5f641cd61548018bac839ac2a900317d887358552006a7b10e6b0aa400d4f73dc96154801a98e7b92c2a9003551cf61585528ceb3b96c2b0aa400c5f7398561548018b8e730ac2a90024f61e74185521c49fc3ae830aa400c3e865d061548018790cba0c2a90030fd89741855200697b12e830aa43887d87d90615487187ce9b20c2a90030f5d364185520043ec3cc830aa400c3d74990615487187ce8b20c2a90030f5d164185520043ec38c830aa400c3d74190615486f2df04b98c2a90030f5d363185520062f39ec630aa400a7581d8c615480187ae9318c2a90030f5d163185528ad37c12c630aa400a778158c615480187ae8318c2a90030f5d361185527fdb2c14c230aa40087f87584615480187ae8b08c2a900297e0d61185520052e41ac230aa4009778758461549fd4ef0cb08c2a9002d520d61185528c5b3c12c230aa400a7681dd061548070fb05ba0c2a90031da0774185520043ec3ce830aa400c3f749d0615480147b0f3a0c2a90020f61e74185520061fb94e830aa400c3d729d06154801c6c433a0c2a90038d48674185520061fc22e830aa51787f825d06154a2d0fb04ba0c2a90030fd0974185520061f212e830aa400c3d425d0615480187884ba0c2a90030fe1d74185520061fb92e830aa400c3d725d06154801c6c42ba0c2a90038d48574185520061fc1ae830aa400c3e835d0615480187b06ba0c2a90030f20d74185520061fc12e830aa400c3e825d0615480187b04ba0c2a90030f20974185520061f992e830aa400c3e325d0615480187a64ba0c2a90030f0c974185520061f40ae830aa400c3c815d0615480187e42ba0c2a90030f88574185520061e90ae830aa400c3c215d0615480187f00ba0c2a90030fa0174185520061ec02e830aa400c3c805d0615480187e40ba0c2a90030f88174185520061e902e830aa400c3c205d0615480147d083a0c2a90030f5d074185520053b408e830aa400a3e84dcc615480147b09b98c2a90030f5d373185520053b40ee630aa400c3d749cc61548018bee7398c2a90030f5d173185528ad37c12e630aa400a3e841cc615480147b08398c2a90030f5d073185525ed36c10e630aa400a76811cc61548014f500398c2a90029e60073185520043f43e8630aa40087d87d0c615480187ae9a18c2a90029da0743185520053ac0e8630aa400c3d7490c615480187ae8a18c2a90029de0543185520053a40a8630aa40087e8710c6154
  | 27 => 0x40150010024000002001802c00000000000140180020008000000005000805000000b00180380020000040000008002001000c05400100000200000000018000000000000801c01c00300c80000020290000008016000004000000000e0068008002010000800000c008000800400800800180140020030020010002003001800c002025000000000200d0068000004000005000000a0050010000006001000000000400200000000060040030004002001000000000a000001000000a016002002800a00f00080040100000008004006009004005800e00000500000000120008004002000002000c0300090000014002001009000400400000000200000000010030004005000800000400300100000000040020040002001001001c0040020000004002003001800400400f000003803600c00280580100020068000000002000000001e001000000c0000050048010002004002000400a0070010000028009001804000c00600080100020020008010000008000000c000001001001c00a0000000000018000008000800e0000000004000004000800000a001001800800a001005000002e0000000024000000000000002c006001000000000d000000800001a0000020012000003001001200200000000040020078000000009000007401400000100300020000048034000004000800000200000000240080000008004000003000000000e00000080000060001c43ec3ec9b1aa438c3e74d93635480187ae9b26c6a900297a0f64d8d5211cb6c14e3b1aa40096d82dd263548710ff0eb24c6a90030f5d16498d520052fc1ac931aa521d4d72d8e63548014bb0fb1cc6a90031761f6398d529062eb96c731aa400e4f635ca63548018bec738cc6a90024fe117098d521c49e422e131aa40096f825d163548012ef02ba2c6a90025d2057458d52004bdc02e8b1aa440978805d163548710f90eb22c6a90030fdd16458d520052e41ac8b1aa51fd4f73dc96354801acee5b8ac6a90031dd937158d520063ab26e2b1aa400c7762dc56354801acec5b8ac6a900359dc87158d520063bc30e2b1aa400c77641c563548018eac838ac6a900355d8c7158d520063b318e2b1aa400c77621c56354801acec438ac6a91025ea037418d52004bcc06e831aa43887d87d90635487187ce9b20c6a90030f5d36418d520052ec1ec831aa51ec5e7698c6354a3b69b05318c6a90021fe1d6318d520053a40ac631aa40095f8758c6354a3969f04b18c6a9002d52056318d5212cb7c12e231aa44097a80dd361548012f301ba6c2a90e21f61f64d85521c61f3a6c9b0aa400c3d74d93615480187ee8b26c2a90d65b60a73d8552004b6c16e930aa400c3d7499261548014eb03324c2a90e21fe1d64985521c61f3a2c930aa400c3d7459261548018bae731cc2a900
  | 28 => 0x8004000004000800000c0010028000000002000006c00a003001000000c0080000008014006000001800000a0000004006001000000c0000000018028008003000001c00000300b0008006006000800403c004000000000e001000800400000d0008024004018000803800e0000060000008004000801c0040020008004002004000007c006000001801c002001000800000c0030000058008000004802c0040040118004000002001800000401100100000020050008024000007000000400e00200280540080050040010048003004800c01801300c800000000300100140060000018000002000004002801c0100000000000000003801c004000001000000a000000801001800b0008008006006003800002600b0008000004002000800000000100480840040010000010010002000000003c008000000400800000000080080090028000000000002800c03e004001000c0060000000018000000009800400200000080080000020098000000000000000000600000c8000000000001000001c0010010010000004001800c0000010020000016003000001400000e000801c00200b000000001e00200380200060020000000006001000000800200000980400000000018000010022003000000000d0010004000002003800c00200c000800401c001001000000400100000040020050008000012001000000c0000000048004000000000004c03a0010018024010000003800800a00000000040060020030018008003001800400000100000000120050028004002000001000c0040040080010006002004000c01c0020008034000001000800800a0070000000014001001002000000000100000000060000000000001000001c00000000000000020040058000000000000003000000200080000000070020000000003001000402a00d00200080020110018010002000001800000200000080080240000020000000001004002400e0060008000004005007800400400000000540060000000008010005000000000400000300100060000030000004015009002000a010000800c002006001000400200f0058008000007001804001e001002804000000000080000040040080018000000001800c002000000000c00200d001001800e0000000000000000003000000200300000000000010008040000006000000c000004004002002c000000800001600600400100000040010004000000000800800201300600140080080018008010001001800400a00e00000000080050028040008000005000000a0000000014018001007002c000001001002000e0030000004008003001001801c001000000401000e002801c01a011001000000001e000000001200100200080000020070024012001000000000001b006001c00600200000040
  | 29 => 0x4540000000000000000aac0001f18c54bbe0000001422e3d42f0e856ea06300000006a69860000000b9a0006a480000000006b82b6400000000004f00000002428b940008d90000001376cae0002e9c0004dd000049000000000000000009ef49080016f800000033980000000708000000000000262c0146240000000b7a03d00037100c400000027405a8af10000001a862205622884a868fc0000001bf689951f00384940003d318d5d9eeba53500013b099a158324d56a0000000000d226f43bb1d3448663b58280000005af67a13dd9587462bf006dc72a593031e1802e0934018be858639d00014c8f269e36d392eca6e0000001c99bee5846783a3800035c0001e640000004028000ec63f50000000b240001938000a62d7b28e366977ed9d0001f7000047600015714444301328c28000e5d0469ba8bf05793f7b33162460d18e16401a60000000001bf8b6d5c931058de567735298926e67f6b28000762ec75f300010d8000421000090e0000d380000000005d6b84cdd61d01e40001b646d212e1ed800000000000003da47258a000000094a0000130000000000000142418c68bb6f00007d623980c0d60d3f0003111a2c0001e7000000000000023849a8e9a6a710600004b0472aae000027d44aacd800000038906f02e228f76432289965565538181a1c76a71f8d9113447b5f1ad10c240000001d44000002000000200e000000000a001002800000600103200000000000058004004001001800403a000005802800200e00000180000000030008008001000801401a000001800c0000080008000002000002802c0180000008000002000000000000e0010070000000001000001000400b012800000400000280000000000008010000003001802001200000000040040090008004002000006003c008005006800000e007002000400000100700000020020010000000004001800000200a00080080080020018010002006001000c00200b0040008000001005000800a00500600140020000008000008004003000800800100800400080000008040000012000002400000100000280180000050000000000001800400c0040030010000001000000000e005005800000a000000802400c005003802c020002000800400200d003000001e007000800800000f0020000012000000000c000000000002000000e0048004012001001001800a003001002800000200080240080070008008000000003800000001000080000000000038000008012003800c00c00000500000060000008000000005002802800400f000001400200a000800000000a002802c008002002003000000d000003c0280000020020000027000801000000200980000080150010024000003000800000200c0008010020009002801800200600280000000000
  | 30 => 0x27381209b66d68840000b6206cb4f0d107a84b32358e5aaa27410ff011e5182a9003400012943300013ce5b96c197e528e50c297b980000e2038a0f9917c0205d612659d43345b71f550820db288aec400080d566000035824100000014960000002f780007e60001905652eb2459800140cb400001fc907c60523721a00000001f580000008a975b00000008cf64080000001a9000000103a00057100000e0a1a04d80019f063d00021113ec8010001e400b463f0ea0ec142836a1c182c1b581e5473319970c000000275db620003ed989ce0605638597ec0009d349d93547803420000001a4a587000000135842529603b4ea0bed63114d49f042700026c41a49494f8924ce70da60000308000c190000d7d5687680000000ce20006fa02dcdc6c885d1000000092c00000000000b535c873d8080c658a850851cdb0000000159c0000000000242000000000000087836d1881852a7c5f0800000023c2cc00015c07ff05ca20c00000019e8264ba04a05462d3921ea265c89b8109c0001ea304437600000011c55b40000fa817015cdec54b95c80a42ec3e0a16c27a3fb5f7800189605338635419c89dc04c04ac3b200018d0000d68b1d1cc9cc510c8d70dbaf3c0948817710000000000246108c15a000545144c0000002f8a66d040de12ef0b7463e3f267880000000004dfb97d4a0cb115c246c5c6c351c52b400000004390000fd000000011040f80000000ab10d6bc858b0b1c00093f471a8b0bb6b533721045bc8b6b5f8a160af628a0003a188624fe00020f46765a80000d48e928a40001af0af80000000c0c950ee500000008d4e273f810bc000b4c1128001326b8c000074847619300000000004e701da2815d69ec10489d4000000536aa588127ce40300008b623d6ff9ac85982f955915b8f0a96346932f4d402445af80cc9446c21241a4144e0006a232ecee815b4973488eaadb313b03f8d44261722ba8daa8ec64f728b587ee142b83a4c000191091800017657f1e485d8000c565e03a282b0d9057b149800000035d05208a00001199fe899cba630729acf42e7d4aaa258c5aa9f31a2b1c00000000000000007e328a9b1cc92976000131c00044c76d966825800035c30952da0000001ee09f260a0cf15316700000002b843f223053f000000000067194f93d400000000000003d100018c400000000003355aec1c000000000000006c24c40001ee5ec9eb00008b8000000000011b6baaf15346b665e6ac31c1e71700013940003ba46f06580000000000001ce600000039b0000000000199c0003810002f700220292df800122200000031f8000e7636501551c84745c99ab44fc29f60d8001314d321e50f4185a0122a400001aa0000003b84c2e0004468001be000000008bc000000000000000000000000017a86160003
  | 31 => 0x1626000057ae205e0990552ad296de7981cf98d828a2a527811b1a7207165f2ca8b740003f280000000002af3624b004b13e1982400000062f800000000000006e00009190000000000006000000000065300000013be8820000000c0eea81c229057502011b4a17c3d00000000001a82aa01da8470000b72659388c9303ee2d2bafc3a62b774a00000001223a58001d2a3301d121e400090b024800198cc166bd1075d24e490001e448841b21dfa57c00000068c0dfcb4665907280000000003d78c1800035600005acb5abb57238730534a7b4d7b735d30e790bd21355269ae24e0ca9b44b433308f04c963a50d89cf44f627716e123d61cbbb3902784000cc275a2814000000000000000089b2cab7684c6e66738800000025523433c9a22000518176127ce5551c800155ece81fb0dcc000c23000000184e0006708b6d16a000633b5c4000ad30000001d803316639a90d12867354a2498dc8c11aca6e0000c370eeb5b52a28f95ec00009fe00000002f40000000001895dbe2c1000000000000076d1451a5e45400001d99a8000000000000057547505b5bfc0000001dbc00024b236800045a1db54f151c0000000f1922828c00045e887c00017e0003130528116745a6890c683663c3a0d23e74700000013529c92d519b95d049a17d8a746400000000001220e54000047949cc0e3ada4a8a0ae750002ef4a8a0000000ce846ea7549c00e0ab200000022f0000da100037200000006f00000000a5838238851e40006ca000058c0005b8ae280005a14ea2b001a02d32fea430cde74e16b1eacdb609221e8af52e4aef22b8001b8eb63000164c5c800075532ac74c912295b9216147e26ca93b8016a3c3e685759086cf000000006ce3069180004a6a740cc1ac5b1479f59a8ba00189480000001db800023596d00005b60002595280baa14ca925d3eeb942300912e06f833919c1cc223805e0de864c30f55680015ea52800000000001c600033400005d15c7866ccbc3f816c8000e504ec72e20c18b2722000085486c60829d9d4907eba103425a59ae8b61440300f123050208884bdc16f53ba4f027ccce46c363497a7f434601dd9800183cda3dc00013a6c7000111c53606f80014986c400000003fc000000000155400000033800120005a30e3c94200000000018429fa063b0f9cae3bd61db73c68241c0000c846580003ba956c00051700000003d6000000358905a00022017201680003feb6adb960e82f4ab740000003cb147400098504b8000d0200000034110a07ad49033b8000214000097d13ab9d045aa500000000000000f7c1694c00000b8200038805cc0009f92e70b78c5ecf718f16f98aa53d0000f7800007420b10ed1d8b7e000030d88e0003dba9593fa55711f8ac8fd247904a1ce8000c05269ad840009cf2790001502
  | 32 => 0xe2070000000000db900033d400000042400014320003e2800000024500000000006fc22a80000007652820769462c75537880c1f8c2657f00008662501923174000d6644e25f400027c18a35fc0000002ee87b0bd40005e20000000c3c26230c00006ff3bb8ed80000006e8000020c43467e25885f80002e9231c3ec01d0500f09d92af01b3a5cc00000032887a4b8400027500012fc95700003881a89290f2263c000599511800000092b0e5a2300002a30902d8000036f20fb965d182c000000001b42f748190d529687d13380001c00004f2800127a0000000000bdaaec43a8f6404c2790f780000aebb700000000000002f00000e360000000000000000000000122c47e0002d3c0000002278950848e4b0ef0000000ea000026f000000000000008728ac70b32595be00000000000000003d72e25d560000000d2c00000000034711980006b39039be2e5e32421903b803c0002c34062000000150421200060f046000000000030ccc42e7239500000000000b1a50451a21d00020d0dea4ac088a1952643be00000018620004ba8000a8400000028e9b8600000012e855e00062290980009612e48c640086542660001c9898700000005126c904385dc47400030d067501ee514110000c1834700024b51129740001ff00000000002d440004ca5be9f2181e8740002ad8150e746a2b3a543036d44b80008b22280fe1d806007c21611d5992800000001e88cc7784f11ba16003da0001e9c000d0d0feac79d78bf223027b54803103fc95d96429841891d70f961c90001c245742970003519a3cc8f0000000cd400032c36715d40000a48000000945000071ca52000000000093e0000001a1c7dad5a2ed1840ee44cf2b1297800000058b80004a47250000000000a860000001bf00000e28000272217380045c0006cb0001f240c20000000000000afc0000001560000579000000000000013a59aa6770002099c7847c0a5ba89644b7701caf243741017013a5c08a8ff639a4940006d700018e40007ed0002cf0fae0000000001ba662e0000000cca00059d857c62e18352a8000df4bfb026ab6036cc760000000cbac7a3008001b16baf62499e81ae0006ae8140a120a52893b5800045d7599c3400000000023752380007688000c7c2cf1eaafd0000a84000000000000000000000000000001e000000000000000b7800000015e151ed690001b5879812a61537b4e805b2458232926600057b8000e602271088ed057651e099a0100009351aaa174d30da000038c44b400044c22fc5dccd1000332d48a0004d2044d1c40001d793e8ddaa544e691943ce56000000016d0c4312100003862a60000c2d5300002053009ad4a6e00031f10e0b646aaafacf400001a0102036809a00000005686a76a4286c000afb000000071605d16c00012687435bc
  | 33 => 0x512ac00000000033b400000068c800097e00000020cd96a6c154a983c94600000000000003c366f0000cb4650000342dc88d7638f80acb4e4d80ff92d0382ee644f0000f62ae67070f8c87c00016905b8cda00000000000000002e2010008853c09c17f00000000002b2800080a000001c000e360000001196c8c41d80012b81800000000000b020d734d400000005d228c0100000001aa031200035f00004e8503397b2140008b9750800000000000000002c20000003b740000100002be80005395fb00557640000001249b7a22401f00011748ae000000123a76d72311440001080000000cf00004cba5e9774d422690000000c824e226cc00000055d902da24e436b98cf06021f4601bb4c4685513629dc0118e5a30e0dec6e49715aa26244804c14288c35a2610705f80018faa6815727fc72442116fb8a400077926680014c283c0001b7c4fe7d02b22a00ed6ae9291a7c89f60000001218000000000251116242e1558c594e421203eac8c4ac7690111d742989fe2a30685108b27772120cad4a700001c443941f83f8a96c0000004910654000bee4e1904149095d0a0101170e2934c18f3c4e026e64c8000ab00720800000b3e44b6d429a400000057f88780004e8417800000090722e37d89fab3e0000b989bccdb5dc80000003372e02f2c28890e0002b2430c0000440b5522eaf93398001bf40005d49c2827682a473800000095872113c471a18b6642a4596ee9b35d8a9c9c4bc756f00007fa00012b83dc00000076727dc9783ef70185a82bc0000000000736ba420d8e60000e1c00000019fedee00000015908086489b8592400016503c07c8b2b7310c450967b370231381f0b5607b21013f0000053aa2069216624100006643e856100000006640002c400000510001cc94fa40164f000000074c00003bc000000519173c92210500000000000001db80000001c40000000000e5319780001540000000e4040c00027b12500000002e1b1082944c5000269c0006925e7000050a0002880000444923000000000000026880003aa956539afa4000000523800096c00014c07011e2cd959633e400000000000000000001dc9d3cd56ca945911682c43ad3ce86cd95ed6f00020b8000ae471a37000008735a91ea8000a785388000000cda64da721c9a00000000000000000001368000b4d0758001612000000206800000051a3aec4d6000000000178600034d000186c000445935874e00000000000007df00003a9690e0874218e87ae00009439f000035a000354c05077f4b525b893635d2cf1e396d24b3651184da707293ec986550e358366a7648508ef1adadcdd0255f68fa758a743880bebb6466a6dc70c8000000000000000000063203980000000002b40001176bb4599a9180009e40001df400060465000000000000000000eb
  | 34 => 0xe628613337e40000005efb774c8e000000093c5fa0000000000efc4e627027f00000f91cb8000000000000000114a0002ffa5f0000bd2000068c0007f755889443722e7017b764644c0c70e95cd1a645306e8b20796d3700034000003dc5ed087045250743fbadda5c0000001989ab8500479b0b0c98e9c0daaf90c6e0ab57ebb612ee9c64d0a8310c442c0351aa98508530000b35bfab500001db85eabca00000000009f5509800008e192708a1d80000000001064e30df5000042800014d0b938c91a017f00f0ea0ec80000002250a7ed2800000000004c22709d7841cd6000011387780000000001c5044a5ce27751000006e887c102a6a66ab000176c7443a40c55188ce25773b05dc66fb3ad0bcd2108ad04fb7480000000561b6400065f5988cb8000000696893136454e0000001d8610c4ea800000000000000085a0cdf0001bf93402ff5c222a1d2c52164fa838f084640000a10f0e1e20002590f388095d738e1684de50000218000674526913400012f000000000061575f1e680020003b9ae2dd5c0005d81e09a9ad3432a9f9000000035b800187a00300011f504eb3f49b16b01fae2b0002cf4000d7d000000094c323159b724d864dc1f4800000000000000000007c70000d808f4b7900001fc0006e9000000000050651a800154209d34e0358916b202d026c00ca1126bc3374d3c00000000000000000001178000ca800000000004a7000000115e000021901d0d2979554a6f52a008a74381bcb044677060000138c7f00020506fc3465f1089818264439b3b2946c0b10138a00bc2ecb0002058000000000091c00000054e000000000000000000000000000b14000000599016c0001100000000ada37d52135c9062d6c00031a8c00000000007c00087e00028e185cd7e66180011fae5600000000000000000000ecc00042380000000000000000000a9b0003728032d2a00035640000006d78de16d8e07202881000000003a8e240000000549b952868872c309388e00000e7361000000015f00018169b4000333d7060003fdad2cb1680e6758b2c348a0f34038ed73286f4060864b6ed094618000c300000000000000bfa4001cb839098c00011d445800022f83e8064d9900032f13d0cb82c4800021c33f0000000000000727a63400003716b8000cc6ae70f99850000444346b9e800000034981ac0a835718daa3800000000018f1c2448872814c0a100000002240000bd35ba0ecc00075812c000000052a19c3890c041643d4a995214a032ef8bbc00087c6af3878bc4dc60c3b82c000a7f6e737154c04453598000000b410002f9dc14d5748c0239a140000002c2000036b626a975bd04fc4e8a321daaa2a45119a4000000000000000000015880014a430c0002ee0000797658175935a7ec41480000000007153ae000000015
  | 35 => 0xb231845e2c770ab900065a3ac449a5656080f52a008ac29e0003ac89e8b1ce4162d0000bae5ca00000000000006799d5c02838c51f80000000004868000000059244800172a00000011184340005d99dc5d0009e672800133801c5f605d47d8b07410a42436042d000000000042228d8c393e800050fa664f1a406067a1dc2e87bb0b42d6d6341671a22060f944174c89b38d6a39a53d00d4c567a41a803383c26523c199d99a462945588b832e3a0301b56109267e50084747e67e16a78eacb3a68e2061f01476e1f102b56d5a4b5d3ed36ed82818e0aaba94f7acaa48f368c6dcd5f5ff8fd108aa5a0a9ae780008102a499e442c269414020d7fab1c35e92bc16465718220c878a2a90b61b9d6d450f01d2fcc3c01544a12650d086ac0970ba9d1a4971f00ccce48cf663584c93980001c289b40000003cf0d398c80006b4042cb10000000088d5a2bd02c627ed0949c06be21681c6e0900028217ead0f0002859912d6b341b76c7760000ad2a2400000000003248accd60000001b5c0000000e540004d700036140001a637600000000005fb80010ae3764219fa80ccb986c300008d27dd0000001a0605800000000000000000f1ce560004c700000000790002a746ccdc200010e0b760000002cd067c0000000000c9c000369ad64f7e28272900007ce5c50001cec00a9a8662a3156061515f4083da564f363d93ac0267b03d92cb8d425b511f1594d5e28c08796881128190002b7000083955f8000fdc00058780006a23c400000000000000000000a406f9769256c2a000014b0069adc00004b0ffc4b26d80932799b980000000000fa25dc000271c00095400000000005b1000000026c000000253c000c5c000341c0000000001f10704a5764b8d5164800051200014a20003b3b98d72870825f2a354cc4db65a000163e091175800000065b00000012fe000264000000097b14590340000000000000dec85670b8a440009680d020e0cfa80b36e8d200000000000000000aed55e3585a6000031428ad0f60007030000328cfb00023b486e40f07d8a0c00052d0001628890686000137c1e63cd14381b16ce94d608256805c8eb6232490400b852100001a0aed02ea8e45494c8e3da9ce40009264c40000000000000000157a0006a58d2871c00023f95e8f2a8354f033618e434c3519c04000000065829800096c5668000384e772b880000004320d280005c2403335b4c565e1ea40131d0000ee000024a0cd851a05f08c8e8251900000000000004450001b2e000571832800000000017d932469b0ec00000002f4000039000049020d0000d2c3d367d08d5aa2c1720f0d3dce0d1d63289e1c7cb450000000a1c6f70000b385d200008196a5a663630370000000d9e0002244000da536f0bf800000076a3531dae3e50eb97185022a43d10058b
  | 36 => 0x40887a62f0dd19886d40400fddc20c873b0819c31e394000000024a31d3c50001a424133e7b29c00000000012a40000002c693b4f2800000000000000000000000000000529ace8104c9a1d50001b4800060ea97d24ea990790000bcc0006ea017c3be9042fb8000000a900000548ab490100000004e2cc90000f61bde50b4b0158c000715000393800000000000016bc02a4e504500d2000000000053682456b0000000e7e000000132a023666b8b800000030f8434166a920001bc400000000000017ae4a427a293c00057454599580000000002ff89a07cc65b00009c8af30320000764a673bd30e0000d4a2f3800057e60b0d5910cf028f04e097b0000bf8237b9018d20003ef36d03ccb0b00039fc05a02100003a5cda3700002acdc361606bc8254ac272c61a017865643a5ee8c202081470c6b01800000040e11dd5b604b0000fc106e2ad0003120000d9242780000000000002748000e0d000399000064a0000688f1e00069f2eac1a23e14e2ac0565ac8b38739b8964d9b2e397c8672b96541188ce3cc390002b5000000010590f00000000000f497b6e6700000000000000001b5400000042c96cd7820000001ef0ffc0006f9227d53420a000000129800070aa3448926662dc313ca88de20000000000000271ae68bdec8d58db5dc00056f3879df0fd600033e307c0000000001c700004520000000000c570001c6875cc714f800000000000001a9540e7421d180000000000002f81d4c00006200019720001b283b860e5eb39f12d44b6dd6466b151d9aea75220001c5895336824e5c74328184b6e98a40a21ba80000000000001d14ec413011cb49c0000003aa06f8000aba1ef8000000000000000000086a00021b496e8250000de4000c8300032e80005a600038cc0000006c79ded7f800000000003ac00000028a10a4000648000111e0004093779a20d0660480005245274bc06fd8404ad7479e48572c680003899a401782ce1e2132cd3a390bb090c254d30f27ac4c4ec54ed154c5440250e880fc000b8237eab14000e5b00000000000005608001074202000208c302000000000000000074494351a850100017508c20000760000a48000192a1b80000007428000000000000118cb2e0002b489c9c440002bb8001d3c1432a5000097036800023d51fce0531994b8e94b7f0000000540a1c00000012a4675442a8a534c9de3782d68bc68f60000bd800000075aacdc9727f835f88a981a00000019099000ff4eda400000d240cc800000061146000000005cc2fa31001cc48d1ee800000073c542adec0004951bbaaad58c0000628d3533cb815830000000b8d0000001d58b5524eb861a8e4c9000000000081e00030e925e6e20161889bb0e6b5a3a8359306b6027af54262c014831e9546682b609093545e7355c03af43f4c9d6
  | 37 => 0x2fd2ae4c800006c41555b22c1300000000000006f5123830a8547569c4c0000000d5000000064f00034f54b83362ec861072c57d2010df0000aa80810000314000000000000000060a986c0000006db8000000190000000143a0002cb000085256600010a9b82bd14df32fdb180001d48f180847a32d700016ecd6329136a88f04622d8000119c706734367c0000000c12f098e0e90762365846229012e8ee16cad081b0aa98000e4a73c0621bc6c6345380011dc0005128001d2265c2600000000db611b000000058355b8fe801e55438297d4a9e17942614d00003430000000000000000259c0003860002e5c0000000001bcc00041262d80019660000000e78000b904301fd84bc00034a3770542d8204092041e242b39a00011b8da900000003f69b70001934fce0001ce1054000c2b2ae84680008a174c9f50000b5700009a8000c9c0003144000b3900000011c06c656580000009a54c0aca068a90200039940000000001d4c0002c468100000000001af17c000000003698e0000d404f4ab941700001c0377c00000000000005b43fe00012a9a3473700012788b068f000000037a0000001c9c2680003dc8fe4d3262c3b636d40000000ae06b448c6ee47a26610e200003c32b40008b722380011aaaa30d4169000000058c3798f7481300013d4c3ad1b15b17f84e6dd50ac9c08908d93489a85cb2850a66e05f185ea2058c80000009c200038b40002606120f580005e85678001a020003f9a2202f6000758a6a9a5204e000000129c00000000011f68b40000001948ede00000000007d30000f8800000036000000005915930e4c08c4a50002854000aae0001c580000003ec300000000059807dc0000004a336f81980002a82a0d94a000179163d92a8c663caf30142af41b60ca400020d24b000052ac1a0000001cde1700000a780004ae06e34b1bce81769b0000000ca15ac3a20a4a1270001919864268345966cc4c51633d86bc000eaf3c580d000054b4ceb4ec148a2e0002fc0b5600000022a800085c0000000e4621b766000098ca09096b8d533ec86277a3685a2e00464b1415480002402e958c007e000191400000000000000000000000000000000000000000000034aabe1dcea0b09aa87870e37162c290dcf62ed69336fd22ad0c532302000000017c0558090e370000000828bc6408800039a0006ba1c6427ede9000000114c2c94741b2087ec0a47d0000000000677b9a40000003411cfc000000000000000000009b8000d3e2494dc8000a705cb0001c740000002b6000000000008a8ad40000004dd1e30a3e6ae0f916150aae580002dc1c5eb9f46133b0c860000000f6cc600000000000000000660800000000040d9a281e87b4000000146e11f0001b454200b66698000000ad500006706c4b9b3428001404c4a588a415
  | 38 => 0x1b005e56368000000000261bac00000003730af0cc02e00002fe53e6ea45a483785c4c5300000000000005360c0829c00036600007e29ab53b0c600000001040c4d2de8f870d301c00053300036e000000000000000f658137924519fa00010600019ce00056180000000004748504bc80000002e38000b5c136000000070751e8595c020006c080000008075d1800000000000026d40001f16cc25adaa40004af375dbd68db6f9afa8fc093a0cd207cfa4be5754a6087d42a810995ac33e0c868a0000d2e0000001ccd9fc82c000332974093053c8000ba6b256c389bd1be11965324687480000000000000e9d26c8a714147f50002af800000004214094c600065180000000000000000d3abbc042839c0002640001bbccd00000000000146218712af59396a0060c31b16f4c22
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401a15546044018d21005856505118e314840161594144634c52176f111c85118d31485d164691dd46388521005836507518e21485cf646911d46388521005836505118e2148401a315460440d812101c0f2617455161cc00103d9421d52587300060b989841c5528c00182d845887154a300048d6508154a618c1a7a308055141986300048d65081549618c00103d9819271d95300050d64670dd7644c00183a80dd771d91300048b64887147644c00103d94a0676549300040f259841c5524c00103f98d9071549300040f660641c5524c00103d989d464d853001c0fa6374553614c00103d94e1d52d85300040fa6075d90614c00142d921d764185300040f66075190614c00142d921d464185300041b64887550614c00703c985d154185300040f65087548614c00103d94a1f65885300040fa6075d92214c00144d9219473485300060ee41841c5650c0018389061071594300040f26174505650c1a7838805d141594300041d245845d9520c00103d94205765483001c0f26174552610c00103d9421d529843069e8c20154506610c1a7a308055141584300040f65087596210c00143994147764c0300060e9c184146638800103d94a077558e200060e9c18414661881a7a3080551419862069e8c20154505618800103d94a077558d200050d65285dc56348001435942147158d2000519648851c5634800103c976105158d200040fe6374145634800706c976085158d200060d613711456348001835841c45158d200061960871145634800103d942057518d200060e5c184144634800703e98dd154d852069d0e2417455061480012659220554185200060e5c18414461480c18697060851185200060e61d5410061480016309155040185200040fe5d8414763c4001a315460440d8b100068c5518110162c400103f985d0745961069e0e20174505658400103d98dd0415961001c0fa637455162841a743a90dd15458a100040f66284dd9528400143594997714ca100050d652651c5328400103f9461d62946100040f653865d7318400103f9461b754c6100050b65265dc9318400103f9461b75486100050765265dcd218400141d94994734861001c0fa637450765441ad03e96a1c51d91100040f66371dd7644400143a90dc775d91100050d64670dd764441ad03f976105198d100040f6617414663441ad03c976105158d100060b1c984145634400103f98dd05158d100060b6137214563441ad03c9761051589100040fe6374145624400181d84dcc51589100060761073145624400103f98d9071549100040f660641c5524400103e981d764885100040f65281dd56304001464915d162548100070a10174589520400182e6261071548100060b611621c552040014399414776440100070a1d1625491004001c3376dd25144010
  | 1 => 0x2006075cd84144614c8c184d7360851185320060d61d84144614c801a26826105118532006855cd84144614c801a16326105118532006850c984144614c801a243261051185320068561283144614c801a158460c51185320068961182144614c801a458360851185320068961332144614c801a315420141185320040fe6174193629440103f985d07458a510060edd080505629440182f746084058a510060ddd18110162944018397420141597310060d5d18110165cc40144d92997764cb3100545650511c532cc401a315460440583310060edd080507654c4018377460440d95310060b9d984147624c401a295420141d89310068955181103624c401c29745c365189310070a5d170194624c401a0f63610511893100689d8584144624c401c47328847654931007114c9211d9524c40182c6261071549310060b613621c5524c40151594144714c93100551648511c5324c5dbc4462144714c93173531a5b721c5324c401a315460440d81310060b989841c5520c40182d845887154831007111cd621c5520c40183586610715483100645611831c5520c40184f8758952cc431006915888154b310c40143594147764c4310054565051dd9310c40145697147764c4310058565051dd9310c40141d94147764c431005c165051dc9310c5d1544911d4724c431005c1650511c9310c5db85487145624c4310058565051589310c40164592145624c43176f111c851589310c44d44c97589524c4310061321d62549310c40131594205524c43176e511c881549310c40186487589524c4310040f25d84145600c40103f98dd051580310050e25d54901600c40703e98dd164d96210060edd080593658840103f985d064d96210040fe61741d3658840103e98dd141d96210060edd080507658840103f985d041d96210060ddd18110365884018367161065d8e210060d9c5841476388401836716106598e210060d9c584146638855984f87d9563cca21005856505118d31885dbc4472144634c6210050b65065dc9318855954697cca514c6211945925d82d95318845d1c49760b634c621005856506518d31885dbc4472194634c621006511d687cc93188401c4475ddb324c62100651a1f75cc9318840154697d97324c62156651a1f65cc9318844d1c4985c9310c6210040f66074195608840103e9819774582210040f25d84145608840103f98dd051582210060edd08050765484018377460440d952100686550805076348401a155460440d8d210060ddc584145634840182d84dc85158d210060d5c584144634840181e766105118d21006855c5841446348401a17216105118d2100683085841446348401a14216105118d2100487261545046348645e04215514118d210068655080504634840124d922157018d210060761d541006348
  | 2 => 0xd6520a2802206819c428863b8b09289c059ee000924d08a000c80006e648da241cc2098e1d0e41910e01852668f67a81e00254820e8781088e98630a481f906161ac93000000fa0e09a4a9bc9117a7d8000814a5a8008d8008689e000001f250001aa411b854184051800006a4b8002f0007891a000009480a64000000004926209000968003b118001445d800720000c0f04e0000011e0000072800000dc001281000000000000000a1546d1121500057000000026d8001593e338000f000001ec3402e841be000be1c0b28097c00000002408497000000000007695a1387a4ea426e85c1222479162660000b0000025c129d00000000000000ca00000002380000037800000000001a001c234a1604008080002000000f01000120501800060a048301a01008500a0800800020003000000200000000001004080e0b000020100004200a0200400000201802060102c120b000040003038180000028000205060100804000040004000080200010180216068000a01018080a030201414070381401454935907158d520050ea4374593615480143a90a1974185520050e642865d0615480183574e056318552006075d383584615480181d7420d61185520058524d219d0615480143a9090974185520050e642425d061548016149348574185520050be49835d0615480142c9260d74185520050d245835d0615480143b9060d74185520050e241835d0615480143591a0974185520050ea42825d0615480143990a0974185520050de45325d06154801434914c974185520040fa60325d0615480103d980c97418552007034c8325d06154801436910c974185520050d644325d0615480143a900c974185520050e640325d0615480142d92a05741855200507e4d215d0615480141c9348574185520040fa60215d0615480141e9308574185520050764c215d0615480143a9008574185520050e640215d0615480143491601741855200507a4c805d0615480141d9320174185520050ba48805d0615480142d9220174185520050da44805d061548018398020174185520040fa63205d0615480103d98c8174185520050da44205d061548014359108174185520040fe61741d0615480182d825d073185520060e5d2801cc61548018397460073185520060d5d38150c615480183974e0141185520060e5d080504615480182d825d07018552006075d2831c0615480181d7460c70185520060d5d381500615480182e825d04018552006075d283100615480181d7460c40185520060b5d182100615480183574a0440185520060d5d18110061548018357420563d81520040f662741876054801835849c46118152006079cd8414661cc80103d94a0775583320040f25d8414560cc80103f98dd051583320068c55080507614c9dba4763608511853
  | 3 => 0x1f40a9de8707697a2653260001668b196001820014238140000ba6a03e8d04c440005498c7c9262e08c2a00c000000000055800430000012200000001dc001b21800000032039d87fa140720c258ae679f85e158040e28fa2862932620ea811fc2d20a6b94e691607e82200130000e64b046238cc5f9f01ca5800044918c07510269868701e64011c000340e800451ce3d0500022a1b0f200000001747a20e0480035000000005c80071206000005a000002561680000146000d68f000000fc2b16e0d9c6002184595e480c4878040013c290003609800062000180022e8c8a02500000222020001093631800210260024e59000000002a800000003e000179a20026465230000880000000000000b629866748003f8005b0786c000201
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa3b06d02485300400016808a03900160250a64192e830aa400a0c285802017418552006808c4ca0a238a6498ba2444a6648511c5324c40188343b2828ee49886200d011c994145624c4317448894ec90a2b1262188031047265081549310c401a0239328288c698c4200d011c994194634c62100502b4e10b08288c690803404726505118d3148401310d1122aa08030a4000d08244405d16254810
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4b
  | 7 => 0x4e
  | 8 => 0x138d
  | 9 => 0x94b
  | 10 => 0x94d
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124d
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138e
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0xcb
  | 22 => 0x4
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x168d
  | 26 => 0x9cb
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12cb
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168b
  | 33 => 0x168e
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x24b
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0x144d
  | 42 => 0x16cd
  | 43 => 0xb4b
  | 44 => 0xb4d
  | 45 => 0xb4e
  | 46 => 0x144b
  | 47 => 0x144e
  | 48 => 0x16cb
  | 49 => 0x16ce
  | 50 => 0x14cb
  | 51 => 0x14cd
  | 52 => 0xccd
  | 53 => 0xcce
  | 54 => 0x170d
  | 55 => 0x170e
  | 56 => 0xd4d
  | 57 => 0x94056
  | 58 => 0x95395
  | 59 => 0x94055
  | 60 => 0x14c9
  | 61 => 0x14c055
  | 62 => 0x2c9
  | 63 => 0x54d5
  | 64 => 0xd49
  | 65 => 0xd4055
  | 66 => 0x1a09
  | 67 => 0x4d55
  | 68 => 0x138955
  | 69 => 0x138956
  | 70 => 0x98955
  | 71 => 0x98956
  | 72 => 0x128955
  | 73 => 0x128956
  | 74 => 0x14c955
  | 75 => 0x954d5
  | 76 => 0xd4955
  | 77 => 0x94d55
  | 78 => 0x1489
  | 79 => 0x139256
  | 80 => 0x139255
  | 81 => 0x99256
  | 82 => 0x99255
  | 83 => 0x14d255
  | 84 => 0x1254d5
  | 85 => 0xd5255
  | 86 => 0x124d55
  | 87 => 0x14d395
  | 88 => 0x1394d5
  | 89 => 0xd5395
  | 90 => 0x138d55
  | 91 => 0x9c996
  | 92 => 0x9c995
  | 93 => 0x12c996
  | 94 => 0x12c995
  | 95 => 0x14c995
  | 96 => 0x2cb
  | 97 => 0x994d5
  | 98 => 0x9d296
  | 99 => 0x9d295
  | 100 => 0x14d295
  | 101 => 0x1294d5
  | 102 => 0x9c0d6
  | 103 => 0x9c0d5
  | 104 => 0x14c0d5
  | 105 => 0xd4d5
  | 106 => 0xd40d5
  | 107 => 0xcd55
  | 108 => 0x1689d6
  | 109 => 0x1689d5
  | 110 => 0x14c9d5
  | 111 => 0x9d4d5
  | 112 => 0xd49d5
  | 113 => 0x9cd55
  | 114 => 0x1789
  | 115 => 0x17c9
  | 116 => 0x1692d6
  | 117 => 0x1692d5
  | 118 => 0x14d2d5
  | 119 => 0x12d4d5
  | 120 => 0xd52d5
  | 121 => 0x12cd55
  | 122 => 0x14d695
  | 123 => 0x1694d5
  | 124 => 0xd5695
  | 125 => 0x168d55
  | 126 => 0x140b16
  | 127 => 0x140b15
  | 128 => 0xb4b15
  | 129 => 0xb4b16
  | 130 => 0x144b15
  | 131 => 0x144b16
  | 132 => 0x14cb15
  | 133 => 0xb14d5
  | 134 => 0x154e
  | 135 => 0xb5415
  | 136 => 0xb5416
  | 137 => 0x145415
  | 138 => 0x145416
  | 139 => 0x14d415
  | 140 => 0x1414d5
  | 141 => 0x171416
  | 142 => 0x171415
  | 143 => 0xb4256
  | 144 => 0xb4255
  | 145 => 0xb5455
  | 146 => 0x144253
  | 147 => 0x144256
  | 148 => 0x144255
  | 149 => 0x1456d5
  | 150 => 0x24b55
  | 151 => 0x16c256
  | 152 => 0x16c255
  | 153 => 0x14c253
  | 154 => 0x14c255
  | 155 => 0x254d5
  | 156 => 0xd4255
  | 157 => 0x24d55
  | 158 => 0x144b56
  | 159 => 0x144b55
  | 160 => 0x16cb56
  | 161 => 0x16cb55
  | 162 => 0x14cb55
  | 163 => 0xb54d5
  | 164 => 0xccb56
  | 165 => 0xccb55
  | 166 => 0x170b56
  | 167 => 0x170b55
  | 168 => 0xd4b55
  | 169 => 0xb4d55
  | 170 => 0x16d456
  | 171 => 0x16d455
  | 172 => 0x14d453
  | 173 => 0x14d455
  | 174 => 0x1454d5
  | 175 => 0xd5455
  | 176 => 0x144d55
  | 177 => 0x14d6d5
  | 178 => 0x16d4d5
  | 179 => 0xcd6d6
  | 180 => 0xcd6d5
  | 181 => 0x1716d6
  | 182 => 0x1716d5
  | 183 => 0xd56d5
  | 184 => 0x16cd55
  | 185 => 0xcd4d5
  | 186 => 0x14ccd5
  | 187 => 0x1714d5
  | 188 => 0x14d715
  | 189 => 0x20e
  | 190 => 0x170cd6
  | 191 => 0x170cd5
  | 192 => 0x14b
  | 193 => 0x8e
  | 194 => 0x198b
  | 195 => 0xa4b
  | 196 => 0x134b
  | 197 => 0x150e
  | 198 => 0x19cb
  | 199 => 0xbcb
  | 200 => 0x5cb
  | 201 => 0x3ce
  | 202 => 0x17cb
  | 203 => 0x1a4b
  | 204 => 0xecb
  | 205 => 0x15ce
  | 206 => 0x14c9405d
  | 207 => 0x5256
  | 208 => 0x289
  | 209 => 0x24053
  | 210 => 0xd09
  | 211 => 0x1049
  | 212 => 0x942d5
  | 213 => 0x95a15
  | 214 => 0x2cd
  | 215 => 0x1a0d
  | 216 => 0x104b
  | 217 => 0x1a8b
  | 218 => 0x2c955
  | 219 => 0x95496
  | 220 => 0x25253
  | 221 => 0x125396
  | 222 => 0x124996
  | 223 => 0x1a89
  | 224 => 0x589
  | 225 => 0xd816
  | 226 => 0x5c9
  | 227 => 0x9c2d5
  | 228 => 0x9da15
  | 229 => 0x9d796
  | 230 => 0x25453
  | 231 => 0x254d3
  | 232 => 0x242d3
  | 233 => 0x1442d3
  | 234 => 0x1454d3
  | 235 => 0xb8253
  | 236 => 0x148253
  | 237 => 0x2c253
  | 238 => 0x25a93
  | 239 => 0x104253
  | 240 => 0x25053
  | 241 => 0x1a8253
  | 242 => 0x105453
  | 243 => 0x1a9453
  | 244 => 0x24b93
  | 245 => 0x2d453
  | 246 => 0x259d3
  | 247 => 0x2d6d3
  | 248 => 0x145053
  | 249 => 0x145a93
  | 250 => 0xb1456
  | 251 => 0x170b541d
  | 252 => 0x170b541e
  | 253 => 0x16c2d3
  | 254 => 0x2d4d3
  | 255 => 0x20b16
  | 256 => 0x256d6
  | 257 => 0x1456d6
  | 258 => 0x24b56
  | 259 => 0xb5716
  | 260 => 0x16c216
  | 261 => 0x16ccd6
  | 262 => 0x95396
  | 263 => 0xb9396
  | 264 => 0x149396
  | 265 => 0x124056
  | 266 => 0x148e
  | 267 => 0x28e
  | 268 => 0xb0216
  | 269 => 0x24216
  | 270 => 0x141456
  | 271 => 0xb5456
  | 272 => 0x9296
  | 273 => 0x151296
  | 274 => 0x150996
  | 275 => 0xd0996
  | 276 => 0x160996
  | 277 => 0x21716
  | 278 => 0xd0e
  | 279 => 0x188e
  | 280 => 0x21416
  | 281 => 0x155416
  | 282 => 0x154b16
  | 283 => 0x141716
  | 284 => 0x3d716
  | 285 => 0x3ccd6
  | 286 => 0x17da53
  | 287 => 0x1715d6
  | 288 => 0x1a57d3
  | 289 => 0x15ccd6
  | 290 => 0x104b825b
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1799
  | 6 => 5376
  | 5 => 3816
  | 4 => 307
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (73751+((h/599+packedAt gbK7 (66563+(h % 599)*12) 12) % 2374)*12) 12
  | 6 => packedAt gbK6 (281344+((h/1792+packedAt gbK6 (258048+(h % 1792)*13) 13) % 7097)*14) 14
  | 5 => packedAt gbK5 (241680+((h/1272+packedAt gbK5 (225144+(h % 1272)*13) 13) % 5541)*13) 13
  | 4 => packedAt gbK4 (22408+((h/102+packedAt gbK4 (21490+(h % 102)*9) 9) % 445)*10) 10
  | 3 => packedAt gbK3 (1154+((h/4+packedAt gbK3 (1134+(h % 4)*5) 5) % 18)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7e1e0f83fe0fffffc7c03fc0033f913833f67c
  | 1 => 0xffe00ffc1ff07803f8003fffccc81ff9ccc87f
  | 2 => 0x81fff0001fff8003ffffc3fff0f1e1c60f0f8f
  | 3 => 0x1ffffffe0000003fffffc003f01fe07f00ff0
  | 4 => 0x1fffffffffffffc000000003ffe0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x3206018126048a39c641a6418113911811563c
  | 1 => 0xc46006a40a90504a4802089684480668c4c855
  | 2 => 0x108a9000152d00909294832910b0a1820b028a
  | 3 => 0x21352b4b40000123252b30022b015a05700d60
  | 4 => 0x41d9cc7299ca65c0000c000c3eec0007aea000
  | 5 => 0x78018063018c4600063022303ffffdf0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37151
namespace PEqualNP.Outside.L_meta_37151
open PEqualNP.Outside.L_meta_37151.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
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
theorem bs4_3_96 : Interval s4Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 112 := (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96))
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
theorem bs4_4_1344 : Interval s4Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992)))) (concat (concat (concat bs4_4_1024 bs4_4_1056) (concat bs4_4_1088 (concat bs4_4_1120 bs4_4_1152))) (concat (concat bs4_4_1184 (concat bs4_4_1216 bs4_4_1248)) (concat bs4_4_1280 (concat bs4_4_1312 bs4_4_1344))))))
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
theorem bs4_5_992 : Interval s4Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 bs4_5_992)))))
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
theorem bgb_4_288 : Interval gbAtlas 4 288 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 307 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288))))
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
theorem bgb_5_3808 : Interval gbAtlas 5 3808 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3816 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)))))) (concat (concat (concat (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112))) (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368)))) (concat (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592))) (concat (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848))))) (concat (concat (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072))) (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328)))) (concat (concat (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)) (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552))) (concat (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680)) (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 5376 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)))))) (concat (concat (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))))) (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656))))))) (concat (concat (concat (concat (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136))) (concat (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))))) (concat (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488))) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)))) (concat (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808))) (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)))))) (concat (concat (concat (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)))) (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))) (concat (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))))) (concat (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))) (concat (concat bgb_6_4864 bgb_6_4896) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152))) (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))))))))
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
theorem bgb_7_1792 : Interval gbAtlas 7 1792 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1799 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0feeafcc8feeaf8c0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813000 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37151.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,5]⟩,⟨.and,[0,4]⟩,⟨.or,[4,6]⟩,⟨.and,[3,8]⟩,⟨.and,[0,5]⟩,⟨.or,[9,10]⟩,⟨.or,[1,3]⟩,⟨.and,[2,12]⟩,⟨.and,[1,11]⟩,⟨.or,[13,14]⟩,⟨.or,[7,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37151

open PEqualNP.Outside.L_meta_37151 in
theorem PEqualNP.Outside.L_meta_37151 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
