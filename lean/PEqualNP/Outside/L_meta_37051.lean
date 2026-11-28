import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37051.Model
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


end PEqualNP.Outside.L_meta_37051.Model

namespace PEqualNP.Outside.L_meta_37051
open PEqualNP.Outside.L_meta_37051.Model
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

def mirrorSteps : List Move := [swapRows 33,swapRows 67]

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

end PEqualNP.Outside.L_meta_37051

namespace PEqualNP.Outside.L_meta_37051
open PEqualNP.Outside.L_meta_37051.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x60001d401c78000039a0e32009aa56202125866008c2db95f028ae404f10d29d4125855e000b2c0041040201018fe43fd43fc43ff41fe41fd41fc41ff31fe31fd31fc31fe21fd21fc21ff30fe30fd30fc30ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x861ff410c3fc82187f50430fe20861ff310c3fc6218778c430fe98861fc310c3b862187fc8430ff10861fd210c3f842185f94030ffa0061fe400c3fa80187f10030ff98061df300c3fc60187e8c030fe98061dd300c3f260187fd5310bfaa621fe54c42fca9887f55310beaa621fc54c42f8a9887fd4f10bfa9e21fe53c42fca7887f54f10bea9e21fc53c42f8a7887fd0f10ff21e21fd43c43f887887fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fe98e21fc31c43fe43887f88710fe90e21fc21c43fe81887f90310fea0621fc40c43fe61887f8c310fe98621fc30c43fe41887ec8310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21f741843fc83087f50610fe20c21f441843fe63087dcc610ff18c21fd31843f863087d0c610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa9a217f53443bea68857d4d10ff29a217e53443faa6885f54d10fe29a217c53443b8a6885714d10ffa1a21fe43443fa86887f10d10ffa92217f52443dea4885bd4910ff292217e52443faa4885f54910fe292217c52443d8a4885b14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff98a21fe31443fa62887f0c510ff90a21fe21443fa42887f08510ffa0221fe40443fa80887f10110ff98221fe30443fa60887f0c110ff90221fe20443fa40887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8087f55010beaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821f741043fc82087f50410fe20821f441043fe62087dcc410ff18821fd31043f862087d0c410ff90821f721043fc42087f48410fe10821f421042fca0087fd0010ff20021fd40043f880087fcc010ff18021fd30043f860087fc8010fd90021fe20043fa40087f08010fc10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21fe99443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43fd31887f86310ffc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd4d21bfa9a43df53486bea690ff94d21bf29a43fd53486faa690ff14d21be29a43dc53486b8a690ff90d21fea1a43fc43487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fc4290fb88521ffa82437f50487f6a090ded4121ff28243fd50487f8a090df14121fc282437850487fea610dfd4c21ff298437e53087faa610df54c21fe298437c53087fc8610ff50c21fe218437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fc4210fd88421fe90843f521087ca4210ffd4021ff280437e50087faa010df54021fe28043ff54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3bc87987f50f30eea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2faa7187fd0e30efa1c61fe438c3fa87187f10e30ee21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61de318c3fa63187f0c630ee18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230ff98461df308c3f661187fd5130bfaa261bf544c27ea8987f95130bf2a261fd544c2faa8987f15130be2a261bc544c278a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987bd4930b7a9261fe524c3faa4987f14930be29261ec524c2d8a4987fd0930ff21261fd424c3f884987fcc930ff19261fd324c3f864987fd4530bfa8a61f7514c2eea2987f94530fea8a61fc514c2f8a2987d14530ba28a61ff414c3fc82987f50530fe20a61ff314c3fc62987f4c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030df2a0613e540c3faa8185f55030deaa0613d540c3f8a8185f15030bf29861ff430c3be86187f90c30fea1861fc430c3b886187fd4830ff290617e520c3faa4185f54830fe29061ff420c3fc84187f50830fe21061ff320c3fc6418778c830fe99061fc320c3b864187fd4430ff288617e510c3faa2185f54430fe28
  | 2 => 0x7faa7a0df54f41eea9e835d53d07f8a7a0ffd0f41ff21e83fd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff32d07fea1a0ff94341bf28683fd50d06faa1a0ff14341beaa483ff53907fca720df94e41fea9c837d53907f8a720ffd0e41dfa1c83fe43907fa8720ef50e41fe21c83ff52907fca520df94a41fea94837d52907f8a520ffcca41ff194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4d41bfa9a83fe53507faa6a0ff14d41be29a83ff43507fc86a0ff50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffcc941ff19283fd32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41dfa1883fe43107fa8620ef50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663be54cc67ca998ff55331beaa663bd54cc67aa998ff15331be2a663ff43cc7fc8798ff50f31fe21e63ff52cc7fca598df94b31fea96637d52cc7f8a598ffd0b31ff99663fe32cc7fa6598ff0cb31ffa0e63fe41cc7fa8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63de438c7fa8718f750e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463ff328c7fc6518f78ca31fe99463fc328c7b86518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7fc8698ff50d31fe21a63ff524c6fea498ff94931fea9263fc524c6f8a498ffd0931ff21263fd424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618f790c31fea1863dd430c7f88618ffd4831ff290637e520c7faa418df54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418f78c831fe99063fc320c7b86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a443ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43f
  | 3 => 0xf9c700019a0000207c4332292200038c4cc000168d6000001ad3dcc4408d91143dbe003c7000000000000000000002314db9124809208000724908980000000000000143400000824000002da0019700000004a00000752000002568000003608949e53c000309452b8bc63da750ec611094cc3f062859000826440444667d15e4c080000000364800001270584a90005d0003e5aa84d06dc00810060206b4001ce4000d4bd4ddeff80000000000000000003224a7e680000000100980080480000580100000080000000280000680100000080280180000300100380000080100000080000180080080080100100300180000200080080080980100000080000200000000000880000280080200000000000700080080000300080080000100080000400080080480080000480080000280000080180280000200080000300000000080000300000100100100000100080000000180180280000100000000100380180080400000200000000100080180180180000a00000280080080180000680000100180280480000300080600180080800480100180280100000780000300100000680200080000000000280000400480100000000200200780000380000000100000200500000000480080280300500100380000080480000000180180380180000100000000000000280100200000300000000100000000000280080100080000280180080180100100100000000000280080180480380800000000580100100000400400000180000400280380300280080400580000000580d805001800000000801000001000801000006800803001002802001000000808002800800002808000800000800000000000800801800001004800000002000000801800000000000000001000005000001800000800002000000808000000800000002800002000001801000000000004800800002000001800006000800800808000000802802800000002000002801000002000800000000002003800000801803004800004803000008000000003801001800001802802802003800001003800800002000800000000801002000000000800002800800801001800004803006001000001802001004800000803006800003000001004000002800df55243bf29c87ff4390fbe8721ffd4a43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487fe4350f7c86a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df94c43ff21887de4310ffa8621f750c43cea1887ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff53d07fca7a0df94f41ef29e835e53d
  | 4 => 0xa194000000000000023b000671d800000050400377000c15d740038f00000350b4ee5881325094265d840b1307a2842d847d001154d13d0ba8000000000011bc00000000000003a5000c7000000000000002c1a44f34cb3f057a00000000a1800122a3f48dd70002adef809b3480084c000005cb000888004238c2f332c668000e7b6b3cb8220fa2d800000d31246c8000f58000000b39b36f50e585a68bcbbe0003b79728600086809e9e9b5261f3e34000003ba000d2099000415000b1179800371e305250b0009df33e6a66cd01baf41098dd23840296600121f0857e00174000f04cc28570200553800166e0c00052aefe6141cce6b6001d30000004e600210d143900014e75a000000000004df1ded74dee01b19472ed00106c000d13b000382525000000005fdf146501005c90400018000001cfa6b20ad1cd2189334ca2002360356237ec7fd080c4556e01381a0cf839d4ccc9788d863c322580004f0c558400061a00000000000000d58000000016d800000000000f28000000000000013c000000008ac001300007f0ebaba56c9c8d52b2710000000d0000074001a31ae921ce1c3e26cfc3fa1a06cbdc0000000098cc42de02e8be00000698794824001ce001d24001c2000000f704aa6800000000000003030000010dd5100012e495ca082f00000007888fe0011e048a2c000000000006a4000002dce832fceeee4001ef000000948005300010b80000011c0020b09c000ae800000000f522cc738e8001bc800a0d2e2066460555606bc1f144750000000010e39d027000b2800000191558001479c1b01ae1cc12c551e168fb3dd1e5c8000000036200000000000000000780004ece1c000000000009400000000000180000001883460000003f0001de0003ca22000a24000a4000000003a41eb00000113000e64040786ec0019f000086832000000a64f10340000046c91000000028000c85b32f0002ce000000001e4a1600000235c40001640003fc00000000000a350c00000000000160587b5e893923685e99794c2b61f2003280000000022d53c7641776975630d5a5f7b45b28002e48002f40010e000ccc6b100000000002c317d0000011a24c55125800000608193a30008085100000000000000711033414a1242000001c8000001e2f014b10009682900019c5d89cb6600080c002c66f542575800610000000004dab627b000cec6035572264ccb15f64e0154b52c4d400000226170001c9800271001069690000009280000000150000000e880003c319be9c80005f9984000002d052a4f80000071d5700000000000370d8ac1921af938b8a572800682108c280020c6bc000004f416aea0db4aee3dba9a9000876f3c00615000000f22e2000002600000002405b000d9560c004530000000000075445918000e15bf3ab800a
  | 5 => 0x12e8001c6829cd400000000002fb0aa64e712b400034c000000009f80000000018c00210000724fc8f40000000025e9d300046800000d014b8000009f400000192000000000006947c986000ec6000000000000020f0002308f9e0000664000000000001a0002e400000343000b85820b20006d5ba0005ac062003310fb380a30000290000015e27400000000439116000a4d4a25c0039b951000001ebed8000000000000016ac000000000f19212c6f80018d30e500a2c007646ec1b8000005e000000000862c0a3ca76c1d6f80021ec480002a5feba0b71b14a00008140000c00041ad528a0000002d8000000011d0bc000000000000000011c000f0db50822f29565ec17800848000002720002f9de000d399591dcc4a2a15c0014f8baae3ac0000005181c48eabc5dde44254f8000ff0000000002f0005f29f42a9822bc0b12f2ee3acb9add3fa5097b0fa7286d2001971027b4200bad80000002fe5707577a000232000be1cb1003cd680000dd0000000036d0013a2450004e1800000008d2fb8d216c7fc0027570c000000003910006d400504d252dab35ce564f884d4aa1f58cab7481641513394e631d23e0e8006a0232c720e0007c1f0790001c6a5be4f001948000004d0068001aa0000000059a3e3660000008ebca800000000542c952c0012b000140c9bab0be436dfc0038c00000043800000000002812a6f08072cb55d58b0ade275b5614d924dcc084430075e4dc11705dbb416f2fe3f584436001273e9eb32a1bf71600181000000d4c0029940a0000029c77e000000006a4afa003a7092965d0a1e000c30001373ece1b1a0ad65400000000714000001641bc6e2000000000000021d4e229c5a8e7da6aa4d0baa2b4168e697e4f83966f9500d97011b62147a000bb0000000000000007018800000527001072fd000173a59a20003b5908000000005a28006fe80fa86a800d649e9898000014a80000002e0000000051e00000000000001570000000000061ec7db6e150001a600318032000e60002fe000fd0f6800ce0bdb6e000b739d3306bc5bda1308b64001341c26a239b0b73c00006d34b78000001120000007aa000000002547a61918c774001c4800a514f8005638c4001100ae0017180038a35079c945d5cb42ea427629291386d000000002da6d9ad52d00aa96cdc00366000dc8000006e2a3800000000000002b9636c7000257ca60004da034be000000006ae0a6002289d00000037c6b845c00000513000678000000000003a0004a801a7f17300089c0000099e000001d2000000002f7000300006f6000002110000009efbb306745519d3da80f21105c000d847daef06a00039a582ccb64d9d6b45019865eec32a820001f24a2000001160e43655de320004fda2b245b800118dce00079c002bc172000001c14c
  | 6 => 0x3858000019308f5e6000378005dc4d8770ac00000029c0000078d5e80000023800240262e8a00000526000d61ec000000001f32ea0f45f800000c38000f7800d4a2b29894caa10a291f6a40c002fc4dc0011b8000004818b11448c0000021f000db40014a000000002d6800001a518780051a9aad8800e760001b9ba63c860001b4001a82658002af900006d709dcda3e62800149144000edd621a0b186774e800004a91beae8800000ec31d60fc2985fb34580005289356700066000000000ce800000000000000008d4a489d71200000399924000002670660000000000086a0d0000000018b800388001d40002a4ab58592b0006e0fda6c000001aa0588001844f1b9d033f8000001620010b0000006df50bbd44ad2200135b3fde974a79000948788144465f41d4000001a4b3ac6372ebd76859988ebea40504180008f6f0f3d00037cc9df00a169039000de44895df6870ddc02c3a6454001b5dc40007162bbd2240002640000015f800000000c5949b6e9b6002d10007a76d65e0000000014d000c240006e000001cf2f000000016a1790abacde0e3ebe000000000005c000000000ed8000001f3000002bb0000011c9b01ca04958884000558aa87b022d10000003aca200003f454a3c0033d0007480034f8f41dcc5331d200ac001b620200000207152a3105f680000007a8000ec8c0003675111d4181dc000ac3b9800000000000000009341f3bc25c2ac3a0000bf8f00017aeba0000002f88aabeeda2f0a84f2cf3b29fa1c5d28001ecb040010a01e2fe000005c7001296b0000000b51946611c11c758
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x2210427f6548410afd9121042bc6448410b7d8d21042dc6348410bed81210427f65084109f594210436e5208410db54821043e52108410be98021042f96008410dd59421042756508410bd99021042f46408410bd98c21042f46308410bd98821043e66208410ddd4821043e65208410dd54821043e55208410d954821043f26008410bd58021043f160084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043774194010dd10650043773194010dd0c650043772194010dd086500427d65d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010ed106400427f6550010b7d8d40042dc6350010bbd8940042ec6250010bdd8540042f461500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010bd98440042f56110010ed104400427d65cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010f50c6300427f654c010afd9130042bc644c010bbd8930042ec624c010bdd8530042f4614c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010d794c300435d530c010bd98430042f5610c010f50c4300427d65c8010be597200437965c8010ded4b200437952c8010fcd8720042f961c8010fc187200437a51c8010fcd0720043f041c8010fccc720043f031c8010fcc8720043f021c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f908620042fa60880109fd9520042bf6448010af19120042df6348010b718d20042f76148010bd185200427e65080109f594200427c6508010bd98420042f56108010f9084200437965080109e59420043f26108010be58420043f16108010de94420043f34108010fc10420043f33108010fc0c420043ea2108010fc08420043e02108010dd59710042f664c4010bd19310042f663c4010bd18f10042f662c4010bd18b10043f320c4010fc08310042f56184010dd94610042f96584010de59610042796584010be98a10042f86284010be586100437a5184010fc94610043f34184010fc10610043f33184010fc0c610043f32184010fc086100427f6544010afd9110042bc6444010b7d8d10042dc6344010bbd8910042ec6244010bdd95100437765440109dd9510043b76444010bd99110042f46444010ed19110042b46444010f5d8d10042f66344010bd18d10043d46344010b518d10043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010fcc8110043f02044010bed95100437b65440109ed9510043bb6444010ee19110043db6344010f618d10043eb6244010be98910042f86244010fa18910042e86244010bed8510043f36144010de94510043f25144010fcc8510043f02144010
  | 1 => 0x435c63548109718d520436f62548109fd85520427d6154810dd18552043786054810af99052042bd6414810b798c52042dd6314810db548520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf55342042de63d0810b758f42042f661d0810bd58742042fa60d0810be583420427f65908109f996420427d6590810cfd52420433c5490810db94a420436d5290810bd98642042f561908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420433f5410810cf150420427f65cc8109f997320427d65cc8109f19732042be64cc810af593320435e53cc810d754f32042f661cc810bd58732042fa60cc810be583320427f658c8109f996320427d658c8109f196320435f538c810d714e320436e528c810db54a32042f6618c810bd586320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320435f530c810d714c320427e64944109f592510427e63944109f58e510427d62944109f59741042de63d0410b758f41042f565d0410dd597410437754d0410dd55341042f663d0410f598f41042d663d0410f558f41042f662d0410bd583410427f65904109f596410433e5490410cf55241042f66190410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041043b54110410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410bd98c41043b74310410ed50c41042f66210410ed90841043b44210410fc98041042f56010410fc580410427d65cc410af99331042bd64cc410bd597310437565cc410bd99331043b664cc410ad99331043b564cc410bd193310437753cc410dd54f31042f662cc410bd583310427f658c4109f596310435e538c410d754e31042f6618c410be98231042f9608c4109fd95310427f650c4109f594310435e530c410d754c31043d5310c410be98031042f9600c410dd5943104275650c410bd99031042f4640c410bd98c31043d6630c410ddd4c31043d6530c410dd54c31043d5530c410f590c31043d5430c410bd98831043d6320c410f50c831043f2600c410bd58031043f1600c4109f59721042f565c8410dd59721042f664c8410bd19321042f663c8410bd18f210437752c8410dd54b21043f360c8410bd58321043f060c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be58
  | 2 => 0x540c110d7d4c304435c530c110dbd48304436c520c1109f997204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204433f5488110cf152204435f5388110d714e204436f5288110db14a204427d65481109f19520442df6348110b718d204435f5348110d714d20442f76148110bd185204433f54c4110cf153104435f53c4110d714f104436f52c4110db14b10443bb54c4110ee15310443db53c4110f614f10443eb52c4110de94b104437852c4110fa14b104436852c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443765484110dd15210443b45484110cd15210443d75384110dd94e10443745384110f514e10443545384110f9d4a10443765284110dd14a10443e45284110d914a10443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f58554043746155010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c10dd185530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10bd98743042f561d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c10bd98643042f56190c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c430427e64d48109f593520427e63d48109f58f520437661d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e52042bf6454810af19152042df6354810b718d520427f6454810cfd91520423f64548109f191520433c64548108f191520427f6354810d7d8d520425f63548109f18d520
  | 3 => 0x910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c9109f997414433f54d0510cf15341442de63d0510b758f414435f53d0510d714f414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c52905109f195414433f5450510cf151414435f5350510d714d414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510d7d4c414435c5310510dbd48414436c52105109f99731442be64cc510af593314433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f195314433f544c510cf151314435f534c510d714d314436f524c510db14931442fb604c510be181314427e650c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c510cfd53214433c54c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a21442bf6448510af191214433f5448510cf15121442df6348510b718d214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510cfd50214433c5408510d7d4c214435c5308510dbd4821443e521085109f997404433f54d0110cf153404435f53d0110d714f404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433c5490110d7d4e404435c5390110dbd4a404436c52901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d404435f5350110d714d40442ef6250110bb189404436f5250110db14940442f76150110bd185404427e6510110cfd50404433c5410110b798c40442dd6310110d7d4c404435c5310110dbd48404436c52101109f997304433f54cc110cf153304435f53cc110d714f304436f52cc110db14b30442f661cc110bd587304427e658c110cfd52304433c548c110d7d4e304435c538c110dbd4a304436c528c1109fd95304427d654c1109f19530442bf644c110af191304433f544c110cf151304435f534c110d714d30442ef624c110bb189304436f524c110db14930442f7614c110bd185304427e650c110af99030442bd640c110cfd50304433c
  | 4 => 0x7588534435c6214d10d7d84534435d6114d10d7d80534435d6014d10d7440534427f65d0d109f997434427d65d0d109f197434433f54d0d10cf153434435f53d0d10d714f434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435f5390d10d714e434427f6550d109f995434427d6550d109f195434433f5450d10cf151434435f5350d10d714d434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e52443756194910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6354910d7d8d524425f63549109f18d524435c63549109718d524437761549109fd81524437b60549109ed81524427e6514910cfd50524433c5414910d7d4c524435c5314910db548524427e64149109f590524427e63149109f58c524436e62149109f18452442ee6514910db994524426e6514910dbd5052443af5414910cbd50524436e5414910db550524436c5414910eb150524432c5414910dbd4c52443cf5314910d3d4c524436e5314910db54c524436c5314910f314c524434c5314910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436f6014910db580524436d10149109f997424427d65d09109f197424433f54d0910cf15342442de63d0910b758f424435f53d0910d714f424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424435f5390910d714e424436f5290910db14a424427f65509109f995424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910bd98442442f561109109fd97324427e65cc9109f597324427c65cc910af99332442bd64cc
  | 5 => 0x30842ec624c210bdd8530842f4614c210af99030842bd640c210d794c308435d530c210bd98430842f5610c210f50c430842f66188210bd58620843e42188210bd597108437565c4210bd99310842f464c4210bd98f10842f463c4210bd98b10842f462c4210be597108437965c4210de94b108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f18454442be6515110cf994544423e6515110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cfd80544433d6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7953534435d54d4d10d7153534439c54d4d10c7153534435f64d4d10d7993534435d64d4d10d7193534435f62d4d10d798b534435d62d4d10d718b534435f61d4d10d7587534435f60d4d10d758353442be6494d10af592534433f5494d10cf152534435f5394d10bb98a53442ed6294d109f992534433e6494d108f992534427d6494d10cf592534423d6494d109f98e534425e6394d109f98a534436e6294d109b98a534427d6294d10db58a534426d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd51534433c5454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd8553442776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f18053442de6514d10d7994534425e6514d10d7d50534439f5414d10c7d50534435e5414d10d7550534435c5414d10e7150534431c5414d10d7d90534435e6414d10d7590534435c6414d10d7d88534435e6214d10d
  | 6 => 0x35e63d4a109798f528427d63d4a10d758f528425d63d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a109fd91528427c6454a109fd8d528427c6354a10dbd89528436d5214a109fd97428427e65d0a109f59742842de63d0a10b758f42842f661d0a10bd587428427f6590a109f996428427d6590a10cf952428433d5490a10bd98642842f56190a109fd95428427d6550a109f19542842f76150a10bd185428427f6510a109f994428427d6510a10cf950428433d5410a109fd97328427e65cca109f597328427c65cca10af99332842bd64cca10bd98732842f561cca109fd96328427e658ca109f596328435e538ca10d754e32842f6618ca10bd586328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca10d794c328435d530ca10cf953418433d54d0610b798f41842dd63d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed55341842f663d0610f598f41842d663d0610f558f41842f662d0610fc98341842f560d0610fc583418433f5490610cf152418433e5450610cf55141842fb6050610be181418433f5410610cf15041843b54110610bd59441843756510610ed99041843775410610edd5041843755410610ed15041842f66310610edd0c41843b54310610bd98841843b64210610ed10841842f56010610af99331842bd64cc610d794f318435d53cc610be98331842f960cc610dd59731842f664cc610ed99331842b664cc610ed59331842f464cc610ddd4f31843d653cc610dd54f31843d553cc610bd98b31843f260cc610bd58331843f160cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610d7d4c318435c530c610f54c431842f5650c610dd59431842f6640c610bd19031843d6630c610ddd4c31843d7530c610dd54c31843d4530c610f590c31843d5430c610bd98831843d6320c610f50c831842f5600c610db94b218436d52c8610be98321842f960c8610bd99321842f464c8610bd98f21842f463c8610f994b218437552c8610f954b21843f260c8610bd58321843f160c8610dbd4a21842bf6448610af19121842df6348610b718d218436e5248610db54921842fb6048610be18121843e52108610bd59421843756508610bd99021842f46408610bd98c21842f46308610f998821843775208610f9d4821843675208610dd54821843e45208610bd580218433e5490210cf55240842f66190210bd58640843b44190210b7d8d40842dc6350210bbd8940842ec6250210bdd8540842f46150210cf950408433d5410210b798c40842dd6310210bd98440842f56110210ed104408435e538c210d754e30842f6618c210bd58630843d4318c210afd9130842bc644c210bbd89
  | 7 => 0x550b10bed8142c42f86050b109fd9442c427e6510b109f59442c433e5410b10cf55042c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb10af99332c42bd64ccb10db94b32c436d52ccb10be98332c42f960ccb109fd9632c427e658cb109f59632c427c658cb10d794e32c435d538cb109fd9532c427d654cb109f19532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c436e520cb10db54832c42f6610cb10bd58432c42de63d0710b758f41c433e5490710cf55241c42fa6090710be58241c433e5410710cf55041c42fa6010710be58041c42be64cc710af59331c435e538c710d754e31c42fa608c710be58231c435e530c710d754c31c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c42bf6448710af19121c42df6348710b718d21c42f86048710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c433f5490310cf15240c433e5450310cf55140c42df6350310b718d40c42ef6250310bb18940c42f76150310bd18540c433f5410310cf15040c42de6310310b758c40c435e53cc310d754f30c42f661cc310bd58730c435f538c310d714e30c42bf644c310af19130c435e534c310d754d30c42ef624c310bb18930c42f7614c310bd18530c42be640c310af59030c435f530c310d714c30c42f661c8310bd58720c437965c8310fc98720c42f961c8310fc58720c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f18954843776155210cf55054842de6315210b758c548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538427f6454e109f191538435f6354e109fd89538427c6254e10ddd8553842be6414e10af590538435d5314e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf55343842f661d0e10bd587438427f6590e109f996438427d6590e109f196438435e5390e10d754e43842f66190e10bd586438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d43842f76150e10bd185438427f6510e109f994438427d6510e109f194438439d4310e10af99352842bd64d4a10b798f52842dd63d4a109f98f5284
  | 8 => 0x30cf552300c2dd638c030d794e300c3ba548c030ee552300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030f68ca300c3d8328c030f68c6300c3d8318c0309fd95300c2bf644c030af191300c33e544c030cf551300c2ef624c030bb189300c2f7614c030bd185300c2df654c030d7d95300c25f654c030e7d91300c2de644c030b7191300c39c644c030a7191300c35f544c030e7951300c35d544c030e7551300c31d544c030f3d89300c2dc624c030f3189300c2cc624c030f5d85300c2dc614c030f5185300c2d4614c030b7d81300c35e504c030bed95300c37b654c0309ed95300c3bb644c030ee191300c3ba544c030ee551300c2fb634c030f6d8d300c37a534c030f694d300c3eb624c030fa189300c3f3614c030fc185300c2de63d5310b758f54c42ee62d5310bb58b54c427e63d5310d798f54c425e63d53109f58f54c435d63d53109758f54c427e62d5310db98b54c426e62d53109f58b54c436d62d53109b58b54c437661d5310de58354c433f5495310b798e54c42dd63953109f98e54c435e63953109798e54c427d6395310d758e54c425d63953109f98a54c427d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c42ee62d4f10bb58b53c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f10db98b53c426e62d4f109f58b53c436d62d4f109b58b53c437661d4f10de58353c42be6494f10af59253c435f5394f109f99253c433e6494f108f99253c427d6494f10cf59253c423d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c433f54d0f10cf15343c435e53d0f10d754f43c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c435f5390f10d714e43c427f6550f109f99543c427d6550f109f19543c433f5450f10cf15143c435f5350f10d714d43c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c433e5410f10cf55043c435e5310f10d754c43c439d4310f10af99352c42bd64d4b10b798f52c42dd63d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c437b6054b10db54852c427e6314b109f58c52c43766114b10de58052c427f65d0b109f99742c427d65d0b10b798f42c42dd63d0b10db94b42c436d52d0b10be98342c42f960d0b109fd9642c427e6590b109f59642c433e5490b10cf55242c427f6550b109f59542c427c6
  | 9 => 0x548320c3cd320c830be980320c2f9600c830b7990320c2dc640c830d7d50320c39e540c830d7550320c39d540c830c7550320c2de620c830f3988320c3ce520c830d7548320c3cd520c830b7984320c3da600c830b7580320c3d9600c830af993510c2bd64d4430cf953510c33d54d4430cf952510c33d5494430ddd46510c27e64944309f592510c27e62944309f58a510c35e3294430d70ca510c33e5454430cf551510c27f64544309f191510c27f62544309f189510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c27f65904309f996410c27d6590430cf952410c33d5490430b798e410c2dd6390430e7d0e410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430bed81410c2f860504309fd94410c27e65104309f594410c33e5410430cf550410c39f4310430af993310c2bd64cc430cf953310c33d54cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c2dd658c430d7596310c2de648c430b7192310c35f548c430e7952310c35d548c430e7552310c31d548c430b798a310c35e528c430b7986310c35d518c430b7582310c27f654c430cf951310c33d544c430cf950310c33d540c430dd944310c375510c430f54c4310c2fa600c430be580310c2de640c430b7190310c35f540c430e7950310c35d540c430e7550310c31d540c430b7988310c35e520c430b7984310c3d6610c430f5944310c35d510c430f5544310c3da600c430b7580310c3d9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c2de63c8430b758f210c36e52c8430db54b210c27f65884309f996210c27d6588430cf952210c33d5488430b798e210c2dd6388430dd946210c37551884309fd95210c27d65484309f195210c2bf6448430af191210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c2fb6048430be181210c27f65084309f994210c27d6508430cf950210c33d5408430b7d8c210c2dc6308430f9484210c27e64940309f592500c35f4394030d710e500c35e3294030d70ca500c35e3194030d70c6500c27d65d0030cf953400c33d54d0030e7d0f400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c39c43900309fd95400c33e5450030cf551400c2df6350030b718d400c39f4350030bbd89400c2ec6250030bdd85400c2f461500309f994400c27d65100309f194400c2de6310030b758c400c39c4310030cf953300c33d54cc030b7993300c2dc64cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c2de62cc030b7987300c33e548c0
  | 10 => 0x4c3f351cc130fc147304c33f548c130cf152304c36f528c130db14a304c377518c130dd146304c2df648c130b7592304c39f548c130d7952304c35c548c130e7152304c31c548c130f3d4a304c35c528c130f314a304c34c528c130f5d46304c35c518c130f5146304c354518c130f6d42304c35e63d50309f98b540c27d62d50309f987540c27d61d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030e718e540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d6355030d718d540c27f62550309f189540c27f61550309f185540c33f6555030e718d540c33e6355030cf18d540c31c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c27e6315030d798c540c25e63150309f984540c27d61150309f980540c37a60150309f592530c27d65d0c30cf953430c33d54d0c30b7597430c35d65d0c3097597430c35f54d0c30e7953430c35d54d0c30e7553430c31d54d0c30b798b430c2de61d0c30b7583430c27f6590c309f596430c33e5490c30cf552430c2de6390c30d794e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c39d4310c30be980430c2f96010c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c39e5410c30d7550430c39d5410c30c7550430c2de6210c30b7984430c3da6010c30b7580430c3d96010c30af993520c2bd64d4830cf953520c33d54d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c33e5454830cf551520c27f64548309f191520c27f61548309f185520c2be6414830af590520c33e5414830cf550520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c2de63d0830b758f420c27f65908309f996420c27d6590830cf952420c33d5490830b798e420c2dd6390830e7d0e420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830bed81420c2f860508309fd94420c27e65108309f594420c33e5410830cf550420c39f4310830af993320c2bd64cc830cf953320c33d54cc830db94b320c36d52cc830be983320c2f960cc8309f596320c33e548c830cf552320c2dd658c830d7596320c2de648c830b7192320c35f548c830e7952320c35d548c830e7552320c31d548c830b798a320c35d528c830b7986320c2dd608c8309fd95320c33e544c830cf551320c33e540c830cf550320c36e520c830db
  | 11 => 0xef6254530bb189514c36f5254530db149514c33f5414530cf150514c36f5214530db148514c37551145309f990514c27d6414530d790c514c35d43145309f988514c27d6214530bd994514c3766514530ddd50514c3b75414530cdd50514c3765414530dd550514c3745414530ed150514c3345414530f590c514c3d54314530ddd48514c3e75214530d9d48514c3765214530dd548514c3745214530f9148514c3645214530ddd90514c3766414530dd590514c3746414530ddd8c514c3774314530dd90c514c3564314530dd50c514c3554314530dd10c514c3776214530dd988514c3756214530dd188514c3774214530dd908514c3754214530dd108514c3773214530dd8c8514c3753214530dd0c8514c3776014530dd580514c37530145309f997414c27d65d05309f197414c33f54d0530cf153414c2de63d0530b758f414c36f52d0530db14b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530e750e414c36f5290530db14a414c3775190530dd146414c27f65505309f995414c27c6550530cfd51414c33c5450530dbd49414c36c5250530ddd45414c37451505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c39d4310530dbd48414c36c5210530ddd44414c37451105309f997314c2be64cc530af593314c33f54cc530cf153314c36f52cc530db14b314c37451cc530cfd52314c33c548c530dbd4a314c36c528c530ddd46314c374518c530be982314c2f9608c530cfd51314c33c544c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c5309f994314c33f540c530cf150314c36f520c530db148314c377510c5309f997214c27d65c85309f197214c33f54c8530cf153214c36f52c8530db14b214c37751c8530dd147214c27e65885309f596214c27c6588530cfd52214c33c5488530dbd4a214c36c5288530ddd46214c37451885309fd95214c27e65485309f195214c2bf6448530af191214c33f5448530cf151214c2df6348530b718d214c36f5248530db149214c3775148530dd145214c2fb6048530be181214c27e65085309f594214c27c6508530cfd50214c33c5408530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530f9484214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c36f52d0130db14b404c37751d0130dd147404c33f5490130cf152404c39e4390130dbd4a404c36c5290130ddd46404c37451901309f595404c27c6550130b7d8d404c2dc6350130e750d404c2f76150130bd185404c3775150130dd145404c33f54cc130cf153304c36f52cc130db14b304c37751cc130dd147304c3bb54cc130ee153304c3da43cc130f650f304c3eb52cc130fa14b3
  | 12 => 0x50d30be181434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30c7151434c3db6050d30b7181434c3d86050d309f994434c33f5410d30b798c434c39d4310d30cfd53524c33c54d49309f993524c27d64d49309f987524c27d61d4930dbd53524c3af54d4930cbd53524c36e54d4930db553524c36c54d4930eb153524c32c54d4930f390f524c3cd43d4930dbd93524c36e64d4930db593524c36c64d4930dbd8f524c36f43d4930db90f524c36d43d4930db10f524c36f61d4930db987524c36d61d4930db187524c36f60d4930db583524c2be6494930af592524c33f5494930cf152524c36f5294930bd986524c2f56194930afd91524c2bc6454930cfd51524c33c5454930bdd85524c2f46154930cfd50524c33c5414930db548524c27e64149309f590524c35e4314930d750c524c27e61149309f584524c2ee6514930db994524c36f5414930ebd50524c32f5414930db950524c36d5414930db150524c3ac5414930cb150524c3ce4314930f350c524c36f6414930db990524c36d6414930db190524c36f6314930dbd0c524c36e4314930d390c524c36d4314930d350c524c36c4314930dbd84524c36e6114930db584524c36c6114930dbd80524c36d6014930db4c0524c27e65d09309f597424c27c65d0930cfd53424c33c54d0930b798f424c2dd63d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c39d4390930dbd4a424c36c52909309fd95424c27e65509309f195424c33f5450930cf151424c36f5250930db149424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930e750c424c36f5210930db148424c27e65cc930af993324c2bd64cc930cfd53324c33c54cc930db14b324c33f548c930cf152324c36f528c930db14a324c2fa608c930be582324c33f544c930cf151324c36f524c930db149324c2fb604c930be181324c27e650c930cfd50324c33c540c930dbd48324c33f54d4530cf153514c36f52d4530db14b514c27e64d45309f593514c27e62d45309f58b514c37754d4530edd53514c33754d4530dd953514c37554d4530dd153514c3b454d4530cd153514c3d643d4530f550f514c37752d4530f9d4b514c36752d4530dd94b514c37552d4530dd14b514c3e452d4530d914b514c37764d4530dd993514c37564d4530dd193514c37763d4530ddd0f514c37643d4530dd50f514c37443d4530ddd8b514c37662d4530dd58b514c37462d4530ddd0b514c37642d4530dd50b514c37442d4530ddccb514c37632d4530dd4cb514c37432d4530ddd83514c37560d4530af992514c2bd6494530cfd52514c33c5494530bb98a514c2ed6294530dbd4a514c36c5294530ddd46514c2bf6454530af191514c33f5454530cf151514c2
  | 13 => 0xb7190328c35d540ca30f3988328c3cf520ca30d7548328c3cc520ca30b7984328c2dd600ca30ddd46518c27e64946309f592518c27e62946309f58a518c35e3294630d70ca518c2bf6454630af191518c27f6454630cfd91518c23f64546309f191518c33c64546308f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c2de63d0630b758f418c27f65906309f996418c27d6590630cfd52418c2de6390630b758e418c39f43906309fd95418c27d65506309f195418c2df6350630b718d418c27f65106309f994418c27d6510630cfd50418c39f4310630af993318c2bd64cc630dd946318c375518c630be982318c2f9608c630b7992318c2dc648c630d7d52318c35d548c630b798a318c35e528c630f5946318c35d518c630f5546318c3da608c630b7582318c3d9608c630dd945318c375514c630bed81318c2f8604c630f54c4318c2dd650c630d7594318c2de640c630b7190318c35f540c630d7550318c2de620c630d7948318c3d6610c630f5d44318c35d510c630f5144318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c27f65886309f996218c27d6588630b798e218c2dd63886309fd95218c27d65486309f195218c2bf6448630af191218c2df6348630b718d218c2fb6048630be181218c27f65086309f994218c27d6508630b7d8c218c2dc6308630f9484218c39f43d0230b798e408c2dd6390230e710e408c2dd65cc230d7597308c2de64cc230b7193308c35f54cc230d7553308c2de62cc230b7987308c2f965cc230de597308c27e62d51309f58b544c27e61d51309f587544c39f63d5130cfd8f544c33d63d5130cfd8b544c33e62d5130cf58b544c33c62d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c2ee6295130bb58a544c2f66195130bd586544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c37661951309d986544c27d6195130dd586544c2756195130de582544c2ef6255130bb189544c2f76155130bd185544c35f63551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c39d6315130cfd8c544c33f6215130cf988544c33d6215130cf188544c33f6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d3015130cfd53434c33c54d0d30be983434c2f960d0d309f996434c33f5490d30cf152434c2de6590d30d7996434c25e6590d30b7592434c39f5490d30d7952434c35c5490d30e7152434c31c5490d30b7982434c33f5450d30cf151434c2fb60
  | 14 => 0x5242cc39d4390b309fd9542cc27d6550b309f19542cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30cf95042cc33d5410b30b798c42cc2dd6310b30e750c42cc36e5210b30db54842cc2be64ccb30af59332cc36e52ccb30db54b32cc2fa60ccb30be58332cc36e520cb30db54832cc2fa600cb30be58032cc2be64d4730af59351cc2ee62d4730bb58b51cc37751947309f99251cc27d6494730d790e51cc35d43947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d0730dd94741cc37551d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc39d43907309fd9541cc27d65507309f19541cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730e750c41cc3765110730dd54441cc2be64cc730af59331cc37651cc730dd54731cc2fa60cc730be58331cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730dd94721cc37551c87309fd9621cc27e65887309f59621cc36e5288730db54a21cc27f65487309f59521cc27c6548730afd9121cc2bc6448730b7d8d21cc2dc6348730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc36e5208730db54821cc3765108730dd54421cc3e52108730b798f40cc2dd63d0330e750f40cc27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c33e54d0e30cf553438c2fa60d0e30be583438c39e54d0e30d7553438c39d54d0e30b798b438c2de61d0e30f6983438c2dd60d0e30f6583438c33f5490e30cf951438c33d5450e30bed81438c2f86050e30e750c438c2dd6510e30d7594438c39e6410e30d7d50438c39f5410e30c7d50438c35d5410e30e7150438c2de6210e30b7984438c2dd6010e30dbd4a528c27e6494a309f592528c27e6194a309f586528c2bf6454a30af191528c27f6454a30cfd91528c23f6454a309f191528c33c6454a308f191528c27f6154a309f185528c36d5214a309fd97428c27e65d0a309f597428c2de63d0a30b758f428c27f6590a309f996428c27d6590a30b798e428c2dd6390a30e7d0e428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a309fd94428c27e6510a309f594428c39f4310a30af993328c2bd64cca30db94a328c36d528ca30be982328c2f9608ca30b7992328c2dc648ca30d7552328c3ce528ca30d754a328c3cd528ca30b7986328c3da608ca30b7582328c3d9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c2dd650ca30d7594328c2de640ca3
  | 15 => 0x867e6414c219f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c219f580530867f6590c219f996430867d6590c219f196430873e5490c21cf552430875f5390c21d714e430867f6550c219f995430867d6550c219f195430875f5350c21d714d43086f76150c21bd185430867f6510c219f994430867d6510c219f194430875e5310c21d754c430879d4310c219f992510867d64944219f98e510867d63944219f59741086de63d0421b758f410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867d6510421cf950410873d5410421bb98841086ed62104219f59731086be64cc421af593310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421bd58a21086e56288421dd94a21087e65288421bd982210867f6548421b7d8d21086dc6348421bed8121086f86048421bdd95210877765484219dd9521087b76448421ed19121087d76348421f518d21086f76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9cc921087e63248421f94c921087e43248421fcd8121086f46048421fc18121086f06048421f9d9521086e76548421d9d9521087e76348421f1d8d21087e66348421f958d21087e46348421f118d21087e75348421f994d21087e55348421f914d21087e64348421f950d21087e44348421f9d8121087e36048421f998121087e56048421f918121086e46048421f818121086e06048421f948750087e52194021ded42500867e63940219f58e50086df6354021b718d50087e521540219fd8d500875f635402197d8d500867c6354021d718d500865c6354021b798c50086dd6314021f948450087795014021bb98b54cc2ed62d5330bd98754cc2f561d5330cfd5254cc27e62953309f58a54cc27e61953309f58654cc27f62553309f18954cc27f61553309f18554cc33d5415330d798c54cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30d795243cc39e5490f30e755243cc35c5490f30b798243cc3da6090f30f658243cc2df6550f30d7d9543cc39f6450f30e7d5143cc35e5450f30d715143cc39c5450f30c715143cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc2be64d4b30af59352cc2f661d4b30bd58752cc36f5294b309f99252cc27d6494b30d790e52cc35d4394b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b30db94b42cc36d52d0b309fd9642cc27e6590b309f59642cc33e5490b30cf5
  | 16 => 0xf5414d21d7950534875d5414d21d7150534879c5414d21c7150534875f6414d21d7990534875d6414d21d7190534875f6214d21d7588534875f6114d21d7584534875d2114d21d7d80534875e6014d21d7580534875c6014d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d21d7d4e434875c5390d21bb98a43486ed6290d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21d7d4c434875c5310d21e750c434867e65d0521cfd53414873c54d0521b798f41486dd63d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414873f5490521cf152414875f5390521d714e414867c6550521cfd51414873c5450521d7d4d414875c5350521bbd8941486ec62505219f994414873f5410521cf150414875f5310521d714c41487b541105219f99731486be64cc521af593314873f54cc521cf153314875f53cc521d714f31486ee62cc521bb58b314867e658c521cfd52314873c548c521d7d4e314875c538c5219fd95314867d654c5219f195314873f544c521cf151314875f534c521d714d31486ef624c521bb189314867e650c521cfd50314873c540c521d7d4c314875c530c521f54c4314873f5488521cf152214875f5388521d714e21487af5488521eb15221487cf5388521f314e21487e75188521d7d4f504875c53d41219f98f504867d63d4121ded4f50487db53d4121d6d4f504877a53d4121de54f504877853d4121f614f504875853d4121fa887504877b63d4121de98f504877963d4121de18f504877a43d4121de50f504877843d4121ded87504877b41d4121de907504877941d4121de107504877b31d4121de8c7504877931d4121de0c7504877a21d4121b798e50486dd6394121d7d4e504875c5394121ded4250486df6354121b718d504875f5354121d714d504875f5314121d714c504877950141219f98c504867d6314121db88450486fa6514121de994504877b5314121f6d4c504875b5314121de94c50487795314121de14c50487d85314121d614c50487ea2114121ded8c504877a6314121de58c50487786314121de90c50487794314121de10c504877b6114121ded04504877a4114121de50450487784114121decc4504877a3114121de4c450487783114121de884504876a2114121de48450486be64d4c21af593530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21af99253086bd6494c21d7d4e530867e6494c21cf992530863e6494c219f592530873d6494c218f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21d754c53
  | 17 => 0x5221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f18153886be6414e21af590538875d5314e219f990538873e6414e218f990538867d6414e21cf590538863d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438873e54d0e21cf55343886f661d0e21bd587438867f6590e219f996438867d6590e219f196438875e5390e21d754e43886f66190e21bd586438867f6550e219f995438867d6550e219f195438873e5450e21cf551438875e5350e21d754d43886ef6250e21bb189438867f6510e219f994438867d6510e219f194438879d4310e21cf953428873d54d0a21b798f42886dd63d0a21bd98742886f561d0a21cfd52428873c5490a21cf951428873d5450a21bdd8542886f46150a21cfd50428873c5410a21af99332886bd64cca21d794f328875d53cca21bd98732886f561cca21d7d4e328875c538ca21d794d328875d534ca21bdd8532886f4614ca21d7d4c328875c530ca21b798f41886dd63d0621cf952418873d5490621bb98a41886ed6290621cf950418873d5410621bb98841886ed6210621ed50441886be64cc621af593318875e538c621d754e31886ee628c621bb58a318875e530c621d754c31886ee620c621bb58831887d5310c621bd597218877565c8621af99350886bd64d4221b798f50886dd63d4221ded42508867e64942219f592508867e63942219f58e508877721942219fd91508867c64542219fd8d508867c6354221de540508867e64d4d219f593534867e60d4d219f583534875f54d4d21e7d53534871f54d4d21d7d93534875e64d4d21d7593534875c64d4d21d7d8b534875d62d4d21d7d87534875d61d4d21d7d83534875e60d4d21d7583534875c60d4d21af99253486bd6494d21cfd52534875f5394d21be98253486f96094d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534865e6394d219f58a534876d6294d219f58653487756194d219f982534877a6094d219e982534867d6094d21de58253486796094d21afd9153486bc6454d21cfd5153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534873f5414d21d754c534867e6414d219f590534875e6314d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21e7d50534871
  | 18 => 0xe7d91430c79f5450c31d7951430c75c5450c31e7151430c71c5450c31b7189430c6df6150c31b7181430c67f6510c319f594430c73e5410c31cf550430c6de6310c31e750c430c6f66110c31bd584430c6be64d4831af593520c76f52948319f992520c67d6494831d790e520c75d43948319f982520c67d60948319fd91520c67c64548319fd81520c67c6054831db548520c67f65d08319f997420c67d65d0831b798f420c6dd63d0831db94b420c76d52d08319fd96420c67e65908319f596420c73e5490831cf552420c79d43908319fd95420c67d65508319f195420c6df6350831b718d420c6f76150831bd185420c67e65108319f594420c6de6310831b758c420c79d4310831bd984420c6f56110831af993320c6bd64cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c6dd658c831d7596320c6df648c831b7592320c75f548c831d7552320c6de628c831d754a320c6dd618c831b7982320c67f654c831db948320c76d520c831bd984320c6f5610c831b7d90320c6dd640c831d7d50320c75d540c831b7988320c7ce620c831f3948320c75d520c831f3548320c74d520c831f5984320c6dd610c831f5584320c6d5610c831b7980320c67e64944319f592510c75e4394431d750e510c75e3294431d70ca510c67d65d0431b798f410c6dd63d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431e750e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431e750c410c7b54110431af993310c6bd64cc431b7d93310c79e64cc431b7593310c79d64cc431a7593310c6de62cc431b7983310c6dd638c431d794e310c6f5638c431dd94e310c7d6538c431f590e310c7d5438c431f58ca310c7d4328c431bd982310c67f654c431b7d95310c75f654c43197d95310c6df644c431b7591310c6dc624c431b7d85310c75e514c431f5d05310c7d4414c431b7181310c6f7654c431ddd95310c677654c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7d4434c431f5cc9310c7d5324c431bd181310c77b50940319f992500c67d64940319f98a500c67d6294031d78ca500c75c3294031afd91500c6bc6454031bbd89500c6ec62540319fd91500c73f64540318fd91500c67c6454031cf191500c63c6454031d790d500c75d43540319fd89500c76f62540319bd89500c67c6254031db189500c66c6254031af990500c6bd6414031bb988500c6ed6214031de540500c67e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221b798c54886dd6315221cf990548867e631
  | 19 => 0x9508c67c6254231de540508c67e62d51319f58b544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c65d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31e750c434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931b798f424c6dd63d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c6f66190931bd586424c67e65509319f195424c67e65cc931af993324c6bd64cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c7cd320c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e6590531cf952414c73d54905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531cf950414c73d5410531af993314c6bd64cc531ed993314c7b564cc531d7d52314c75d548c531d714a314c7d7518c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d64141319f988504c67d6214131ddcc4504c75e3114131bb98b540c6ed62d50319f98f540c75e63d50319f98b540c76e62d50319b98b540c67d62d5031db58b540c66d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f5495031d798e540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c67e6415031cf990540c67e6315031d798c540c67e62150319f588540c67e6115031dd984540c67e60150319f580540c67e6494c31cf992530c63e6494c319f592530c73d6494c318f592530c67d65d0c31cfd53430c73c54d0c319fd96430c67d6590c31cf952430c73d5490c31bd986430c6f56190c31d7596430c65d6590c31b7592430c75e5490c31e7952430c79d5490c31d7152430c6de6290c31f5986430c6dd6190c31f5586430c6d56190c31b7982430c67f6550c31cfd51430c73c5450c31b7d95430c75f6550c31
  | 20 => 0xc6f661ccb31bd58732cc73e548cb31cf55232cc73e544cb31cf55132cc73e540cb31cf55032cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95241cc73d5490731cf95141cc73d5450731b7d8d41cc6dc6350731cf95041cc73d5410731ed50441cc6be64d4331af59350cc73e54d4331cf55350cc6ee62d4331bb58b50cc73e5494331cf55250cc77b50943319f99250cc67d64943319f98a50cc67d6294331cf95150cc73d54543319fd9150cc67c64543319fd8950cc67c6254331af99050cc6bd6414331cf95050cc73d5414331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f5495231d758e548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c62552319fd81548c67c6055231cf550548c6ee6215231bb588548c73e6415231d758c548c67e6215231db988548c66e62152319f588548c76d62152319b588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31b7596438c75d6590e31d7952438c75c5490e31b798a438c6dd6190e31b7982438c73e5450e31cf551438c6f76150e31bd185438c75f6550e31e7d91438c75e5450e31e7951438c71e5450e31e7551438c75c5450e31b7189438c6df6150e31f5d85438c7d46150e31b7181438c79d4310e31dbd4a528c67e6494a319f592528c75e4394a31d750e528c67e6094a319f582528c6bf6454a31af191528c67f6454a31cfd91528c63f6454a319f191528c73c6454a318f191528c67f6054a319f181528c6be6414a31af590528c76d5214a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c6de63d0a31b758f428c67e6590a319f596428c79d4390a31bd986428c6f56190a31af993328c6bd64cca31db94a328c76d528ca31bd986328c6f5618ca31b7d92328c6dd648ca31d7d52328c75d548ca31f394a328c75d528ca31f354a328c7d6618ca31b7586328c7d5618ca31b7982328c76e524ca31db549328c6f7614ca31bd185328c6dd650ca31d7594328c6df640ca31b7590328c75f540ca31d7550328c7ce620ca31d7548328c6dd610ca31b7980328c6de63d0631b758f418c73e5490631cf552418c6de6390631b758e418c79d4390631cf950418c73d5410631b798c418c6dd6310631e750c418c6be64cc631af593318c6dd65cc631d7597318c6df64cc631e7993318c6dd64cc631e7593318c69d64cc631b798b318c6de60cc631bd597318c77565cc631ed993318c7b564cc631af993508c6bd64d4231bb98b508c6ed62d4231ded42508c67e64942319f592508c67e62942319f58a508c75e3294231d70ca508c77731942319fd91508c67c6454231d790d508c75d43542319fd8
  | 21 => 0x6550c41e7d8d431079f5350c41cf94d431079c5350c41af18943106bf6150c41af18143106be6410c41d794c431075d5310c41e750c43106f66110c41bd58443106de63d4841b758f521076f52948419f98e521067d6394841cfd0e521073d43948419f982521067d60948419fd8d521067c63548419fd81521067c6054841db548521067f65cc8419f997321067d65cc841af99332106bd64cc841db94b321076d52cc8419fd96321067e658c8419f596321075e538c841d754e321079d438c8419fd95321067d654c8419f19532106bf644c841af19132106f7614c841bd185321067e650c8419f594321075e530c841d754c321079d430c841bd98432106f5610c841cfd0e511073d4394441b798f41106dd63d0441e798f41106bd63d0441e758f411069d63d0441af98b41106be60d0441af592411073e5490441bd59241107765490441ed95241107b74390441ed50e41106f660904419fd9541106bf6550441cfd95411063f6550441afd8d41106bc6250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441ed90d41107b44350441bd181411077b50940419f98e501067d63940419f98a501067d6294041b7d8d50106dc6354041bbd8950106ec62540419fd8d501075f635404197d8d501067c6354041d718d501065c6354041cfd0d501073d43540419fd89501076f62540419bd89501067c6254041db189501066c6254041b798c50106dd6314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cf98e54cc73c6395331cfd8a54cc73e6295331cf58a54cc73c6295331cfd8654cc73d6195331cfd8254cc73e6095331cf58254cc73c6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73f6555331cf98d54cc73c6355331cfd8954cc73e6255331cf58954cc73c6255331cfd8554cc73d6155331cfd8154cc73e6055331cf58154cc73c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cf95343cc73d54d0f31cf95243cc73d5490f31bd98643cc6f56190f31cf95143cc73d5450f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc6be64d4b31af59352cc73e54d4b31cf55352cc6fa60d4b31be58352cc73e5494b31cf55252cc76f5294b319f99252cc67d6494b319f98252cc67d6094b31cf95152cc73d5454b319fd9152cc67c6454b319fd8152cc67c6054b31af99052cc6bd6414b31cf95052cc73d5414b31db54852cc67e65d0b319f59742cc6de63d0b31b758f42cc6be64ccb31af59332cc73e54ccb31cf55332cc76e52ccb31db54b32c
  | 22 => 0x341b758c50d075e5314341d754c50d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98853906ed6214e41af597439073d65d0e41cf94f43906be62d0e41af58743906be60d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e7d8d439073e5350e41e794d439071e5350e41e754d43906bc6250e41afd8543907b76150e41ed18543906bc6050e41e750c439076f5294a419f98e529067d6394a41cfd0e529073d4394a419f982529067d6094a41b7d8d52906dc6354a419fd8d529075f6354a4197d8d529067c6354a41d718d529065c6354a419fd81529067c6054a41b798c52906dd6314a41db548529067f65cca419f997329067d65cca41af99332906bd64cca41d794f329075d53cca419f996329067d658ca41e750e32906f6618ca41bd58632906de63d0641b758f41906bd65d0641cf597419079e63d0641af58f419079d63d0641a758f41906be62d0641af98341906f565d0641dd59741907d663d0641f558f41906de63d4241b758f50906ee62d4241bb58b509077b50942419f98e509067d63942419f98a509067d6294241ddd06509067f63542419f18d509073f4354241cf50d509067f62542419f189509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c435067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65cc9419f597325067c65cc941af99332506bd64cc941dbd4b325076c52cc9419f996325067d658c9419f19632506be648c941af592325075f538c941d714e32506f6618c941bd586325067e654c9419f19532506de63d0541b758f41507d663d0541f558f415073f5390541cf14a41507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141ddd04505073e4114141d798e541075d6395041bb98b53106ed62d4c41d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41d794f431075d53d0c41bd98743106f561d0c41cf94f431079e53d0c41e754f43106be62d0c41ed98743106bd61d0c41ed58743106b561d0c41af983431067d6590c41af592431067f6550c41afd95431073f
  | 23 => 0xfd815290e7c6054a43db5485290ef66114a43bd5845290f775194643cfd0e5190e7e62946439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190eee6214643bb5885190f755114643bb98b5090eed62d4243bd9875090ef561d4243ded425090f5f43942439f98a5090e7d62942439f9865090e7d6194243cfd0d5090e7f62542439f1895090e7f61542439f1855090f795014243e7d4e4350ebe6290d43af9864350ebd6090d439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f9875050e7d61d4143ded425050ef76154143bd1855050f795014143cf90c5050e7e61141439f5845050edd6490c43a75924310f5e5490c43e79524310ede6090c439fd954310edf6550c43d7d954310e5f6550c43b7d914310f5e5450c43e79514310edc6050c43e7d954310e9f6550c43c7d954310f9f6150c43e79854310f9d6150c43e71854310f9f6050c43e79814310f9d6050c43e71814310e9c6050c43e750f5110f9d4394443ddd465110f3f4394443d790e5110f3d4394443d750e5110f1d43944439f98a5110e7d62944439f9825110e7d6094443e750d5110e7f62544439f1895110e7f60544439f1815110f9d4314443dd5445110f9d43d4043e750e5010f7b50940439f9865010e7d6194043e750d5010ef76154043bd1855010f5e4354043d750d5010f1d43540439fd855010f7761540439dd855010e7c6154043dd1855010e746154043e750c5010f795014043d7d4e53d067e6294f419f58a53d067e6094f419f58253d075c6494f41d7d8a53d075e6294f41d758a53d075c6294f41d7d8653d075d6194f41d7d8253d075e6094f41d758253d075c6094f419fd8953d067c6254f419fd8153d067c6054f41d7d9553d075e6454f41d7d8953d075e6254f41d758953d075c6254f41d7d8553d075d6154f41d7d8153d075e6054f41d758153d075c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d075d5390f41d794d43d075e5310f41d754c43d079d4310f41bd98443d06f56110f41b798f52d06dd63d4b41d794f52d075d53d4b41be98352d06f960d4b41d794e52d075d5394b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d075e5354b41d754d52d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d075e5314b41d754c52d076d5214b419f99732d067d65ccb41d794f32d075d53ccb41b798f50d06dd63d4341d794f50d075d53d4341bb98b50d06ed62d4341d794e50d075d5394341ded4250d067e63943419f58e50d067e62943419f58a50d075e5354341d754d50d067f63543419f18d50d067f62543419f18950d06de6314
  | 24 => 0xc0070004002001c002000000400100000000000007c02100240000014000000801d0000001000c0030074008000000b000400400080020000003000400a002c001000000000000020000002000c03100040010000004000800100000090040007003801c00040030028009000000d000c001001c0020010010001c000000c00000000000010007005c000003400f00340070014002001400300a8000001400000040110024006001c000000c000005401200000000004001001400000200010010000000000100040080014004003000800200000014000001c0050004003001c006000400a000c01e0008002000000000100000000001000800000140000010000000c0390008003000400100000030084006000000e000c010000c0050008005000c0040030004000400d000800000100010044001000800e000c00500000310038003000c023002c0050000006000000000000000094020000c003000c00c0044004000002300000050034001006c000000400d000001b000000d000400300d80010000004004c0020004006001000100300010008000002401300bc000000c0010000000000000100280020088007001000000000120004004000c0070028001002400700100000008000000400b004c0040004001002c001000000100000110004000007c0000000000000400c001001400040000008000002c0030000000001800e001c0000000004000c0100000000001800d00000000014003005800200000030018018000001f0028007000c00300100030038006000400000040060010002000800001500030004001002c000000c000000001800080020004000000801f0024002000c01c0034008000c000008800e013801600040060004005001000a0010004003c00000040030078001000000600240040018003000c0000008000001c00101c80010008004001c019000000500180010000001001c0000000012000001300080160000000000c000001c0000000002000000900000020044003000002f001c00700040070018000000c0000000002000400000000080004000000000100080000000004006000b008000000000000034003000c00000380000018001000c000000000b00080030004000003400900300010018004000400100080020008007001000000040010000001001000200000040004000000c000001400b000000400040010018002000400c00000000004000003801900040030018000005c005001400000300000014000000000500fc000004002700340030000003000400000040130044000001400f00040150000000001401800a40000000001000c008000400300000080040000b75974390f5d65d0e43dbd4a5290f3f4394a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439
  | 25 => 0x1000c007009c01000100150004001000c000001000100280010094019001400100000000000003000000800200040010001000400e0000000000400400380130000001000800200380010000000003000d005c016000800500000090000012000c00000040000008005000400000000020004003000000900000010004003001c00a0020017001000700c8001000000e00000020008008003c006001800000140000074019000000100040000050001000000000000030008001002800600100010000000000c01000280010000003000401d0004001001c0030004000002800000340120000001001c00b001800200080010058008000c00a0000008003c00200240060104009000000c0008004007c00600fc001004402300a800e000c0040000002002800700000000010002000000d007400f00080010004004000000300080010000001004801c000c01000000020030004000000600340000034002001800400380050000000000000800000000090000001400000640000044003000c0000014028001c0010044001001001f000800d0008000000003000000060000003000c005001c00100080000018000002000500080000014003000400b0010004005c0000000000010c010000000b0004000000000000000100040003001c000000800300340200034001001400100000360020004001c000000400400000000008000003000500000340040003000c0010070025002c004000000000000000004000000000000040040020004000000400000090010007006c010000800e000000000100000014002000400300000000018002000000800340050000003000000100a8000000c0010008001000000c000400f00080130000001000c0080024000002800e003400100000020000009003c018000000000a00070000005004400f00000240024004000400a002c0000008010000c00100100070000000002001d001800100500060008005000000200000030000004000000c000400300140020014011000000300c400200040000000001000000c00840020014000007400000000000004009000c00100540000014001000000000080010010001000400f00000000004002002000600000010014009000000400040070090000004000100040080008003000800100140010054006000c00000040040000001000000b001001a00800000044003001c0030010021000800000040040000001000000400080000010001002c003006000000580080010008000401900240150124002001802c00040030024007000800500000040004001002c001003800500040000008003000400300440000008018001c007000c0080000007000001600080030040002001400500040150000002000400a003c00200000040000000005400a00180000
  | 26 => 0xc0028009003c00000a0002000400c0000000003c005000000e000c00000100000008000001800100040010000002001400c001800a0018000000400100540010000000002c00500040020064009001000c00440040000002000000d000800700200010038000002c000000800a001000a00080280000016001000200000020088007004400000000070004003000001700500000010001001400300300030044003000800700200000018014001402f000000000000000000000000c0350004000000c009000800000940000004000000400a002c0000004000000c001000801500040090024002000000300280140000002001c0040000000002c006000c00400000140020000002c00000000000038008001401f00040000020000002c000001800200040030000001000400800080000000002004c0060024026000000000000000024002001801000080040000000000400000000110018000000400f000000100040020010015000402f0008001000001c003401300040370004002001c002000400f001c004000000b0004006000400000040050000027000800c003c002000c00500a00030000005006c001001000000140020000002000c00600000130004002001c00100300000000001000c00100100030094009003c006000400000000030028000009000c000400b002c00f00100020000000000400200000100000001001400400380040050000000802e000c001000800300200130024001004800400000050010000000800000000020000000000c00100000000014000000400600380010010008001000000200000034006002c00300000020050000000800c00400030018002000c00f00000030004000000001a0000007000400c0010004001c003001c00400100000000029002800200000040000000000400b00c0001001401400240030000006001000700600160028001006c001000c0030000003000c0130000008001000a002c0020000007002c00a000800d001000200100010000002000c003004801e000c005000801a000800100300040064010000800200040190040007000c0080000000000000300000040030000000c002008801b0008000003402100000080014005000000100440080018010000000300000000000010000000300000030004002000000a0034002009800200000040000005001c00100000000050000002000100000030020016002800000000040094003000c000008c017002000000000020010001000000e00000070000000001800000000040014002002800400b4001001400100000050098006001c000000c000001800200000010000001000c00700280000044002002c0110000000000c00100040070030001000800100000020020001004c00500240000030032000c0010004
  | 27 => 0x10d068c4c50fcb2cb86c600022a00000a4b2eb000020c990e00001a9000019359983417ed10d882794e355495060e15a687d25bc812b0e1c3bea115000044e165a5d44d8a2d46a2e247000000057313b445622aa0001c0a32f1e725f04b7672f80004c00c300001ed073a9c731a5800000006a41809256564801802ea1941b7c7b8545a5fa9739e6c67220ec9f3d82f000117e0001b2600000665e78000000274a0000ee2000000059c000094523825ae4fb04aae71c00020e11281f68766d7fc5620ff6177598e6fdc0006ab107446910d26418caa25cc9c673780f1128a6ae94b1bf816c9e125b0800000000ad36455602eb80000220895000224558048181c18bd20000f577eb03c0676c0005e905ec37b800000025d6353a3646824000001800800240000000000000800e0000000002801000080050008000000000a00280010018002000c0120000005000c001008800100080000004001001000500000030000002002c00400100070000000000000400000000004002000400d0004002000800000000000004000002801900040150070000000000000100010004000000800000100000010004001000800040060000005005000e0000007005c003000000000440040074027001000600000040034009000c01a008400400180090038000000800000080000000001000400200080000008001001c0020014000002001400040000004000003400e0000002000c025002400e0004000000c00300340340014000000400d0000000000800100100010020008000c00300580010000005000c0000038024000000300080000024008002c004000001200000020000001000800b00040000000001001c0010004000000800000100010004007005c004001c0020004005000000300080010018009001c0040010009001800d001c00a002c00b001400500640020008010000c00c000c00000080000004001000c0000018003001800a001400100040000010000000c000000001700000010000000000001000040020010006001000b00140050004007001800100000220018000002c000000000d001401b0030005000c0010054005000800500080000000009001c001006c008008c0070008001001800000240040004003000401d000800d0028029000000800000000030000001000100100000044000007000100000080000001001000000300000000001007400500000050020005003c0080010006000c00100100170004001001000000300010010002000000a00000030004001008c0050000000001c00200280000008000005800400200080044003001c00900d4000000000400480000000000010002100000040018003000000600140020008004000400b00040070004000009800200740010004002000400200140040004006
  | 28 => 0x75d487623d680246ed5609489049e5eeda74546139e5b123ba7d5660e76c54e62d6d1c7759849874f1026101592b9a38af30c600767ce000000024b31579958492867a063081429a5bd22f2222a83c504000001bc065df615dc80000cb200674a192e00010d6761871f00d000000018ac9de429226d04d0378c301000000000000004c72184a0b94e432c87f00000fde5540bba00000003d182f200000bc4f880007c900000000a906d1d912099000041980b60001b8a428000045f186600000005790000532e308000285402503b26c080007fb5f892c3a59512e800000000009fec9cc4139a4a00000000614000102cae86bda076000000000001b471085388c9060a53040001b2000098088a00d3a6967a182b0200085456726a600000000bf119d729cdcf986814224d8b8000000008ff9e2273d000000011f86242864635172a9be882280596e848216e25ae21428e182723de2718000162448ba0362be80469a4866a43322743a8a15c13d1cd226595a486b0dd510900000000c6403786f8000000061a96e083d80000000000995280458e1fd66ec0fb4000000014b00000341deb000203d000124e00000009b224af69986dc9b7800068a40005719d902ac9ad51b08eb07579f7a7f300005a9857a50d16840bf9e7e9b680000da1ddb6ef47aa00009e485980007cc0000950895010a15d53d6db7d8530ef685349041448000000048300002535a70b8e0b915c000021ee00008827a7800004180b46bf03a461d8ca62f91adc46200000c38bda1598000080000069480ca6fbdd723e592ae433e4364bda63646b112e2d280008a5055a13a19ce2d80fd86f600f29b9587f4949cae2b0800029b237264c220700005c900000002fac000231800080c000000000000000bc60001d4476f8a8276e89c034100a45cf1f4721fa4527f8c0000000a527ed93824f2000000017db0000d160271008666039f776a40075da1e043f800080800005f0a2e80cec74e0000d40000114d2040cca44d4dfa00020cb0000000886d11c296d28a00011a55f140000000b626144cf327280007e800008ed82f800009203578e4c968000000014b40001737338590c814000054b236e0000cae0001b9507e9bc1000000025885a500015000410000000000000019b28f89c9c78c80009fd8c820000000000000081f1306699000021c8000000202e2b88000927800000010b60000da86dddb447fc863c2b80000633a21f00016a900020fd0000000071407f00003306fd9dbb55c94c6882a3f259f839c7ddd06253b9f3e70a178f3e0df8585d9d8a000000000007026391fe26eed13480a254c5eac11c6a7ca2800007380001e1e00000000002226000095937c00002c9000035f095f04f8ff03c98f561ef000000003c700000000000cdd553959a064008e3d346d0211
  | 29 => 0x2229c389a65a703179c43456d891c993a103149683b412c3d4e19a38ba64c13c0a3b25001de4aa94206784a45878924c0000cf54dc800006924501cd013700024a852a236c9fdd2d268d89a000000007d0987e00000006c6dac3000256c054549a20b51320a6000017300009604000000000017a15d816aa0d68cca32a00003a666403138469ce35de9ab6167078a5d28a472e504385490e4a0c45f620a311a85c2a866198881e12c894222a18b07dd26395b581d2001800075a257843919dd02320b28a49ba600000008838000121000022a800000002ce02a8b041440e7e61b8b0a82d80008e40000000228f0000ce772d97ba5098d5628816c993680003ded69e8df800000011101ec01c0498800063c81ee040176025a0572298d3a20fd8c706e1047f3728c0a067234c300a84259aa4d409f887019523f400000007ac95f62650d946b9a62a6be0000685c0000000d460001c6a000000000000008cf909c35b14400000e5d31b41541c30000000000000000000000ad4a0a14d600000f406ae4420001a0c5b9966200000000000000000000056e800077825f47210f363d10000072c00041f9ba80001240263000000000004f900007940a4c0001e300000000955194c000142a5d580006ebcd5273fde520a9a81a9d3906c7f191fa25112883c5a41659120311cfa25292b491c42d0e8e2da110e0728b904efa41a00019e846582bb5f79b2e2e5985e8fe471149aa35e9d30f60047994842c66708fe213a4b627e22d48000000022ca14a5a238127ce6fe80002d60546066585c98e0436286000069780000dfa2484b09828185a6f006a857f08e63d2000000000008d49b0144800006e2147000060c800000026e773300006bd120987c03240000fda0000000000000000027b90001b3000c1f1a42dc0009fb400043c013a46250ac05b000000027ac67c1b4e000093e000025890ea0da7ec5ff61c898d0080968a9e4c00035f81e210722626a6c320009a2c803187a436901763b30d796c68a3416117ce7f0920c35b8f9a68e54823758e9a9cb20d40001dc06fa27f200000001384f0828f158a6b3056900008b813e27830ac91563bd09ec6931fa4544253a76509c273512cc4da8d70339400043e9ce29800ac84b8021479e000048f400000000003c81b8707e000069e00008c51dad0000000000038200005f634cc000000279a20b9cfc287041400023ec4dc000000025877c881696b96259988115a1af0c9347c09f281203042a600006a4507229e51a260889987038288324a22e0d31b7a00000003d30170739076c923000001a8a8d72ad22254959df706a42e95aa41c00006a000000006659a418af0d7417f9ae26f31bb2a0399669d126a20001f3a00009bf000000083b80e75b51ed402e5cf270509e259e10ba41e16fa65c16ee69d9f6
  | 30 => 0x8692c87f60000a89000000000003450001726000012600000000e100000000000000216859f0000888c6ea00014f4671a50c92b008114a00005570000000000001486d8667a62d4a580001f705b937491f414d175e2248a8009bd7c475427cc8d34196000049c9df40001d0a37152b1daf19408423fa160a48a0b1c35e038c8a080000d080005a88cc85b6800054c881c0b580001abc00000018b800025c000020e2757000005cde1843218640001ca677e149896d9514560910c25900f07338000000044235459ec5c4a4825680a3d2170000000000009a018e0b8800000005003a312b46cd00004b78cc90001f8f70b26bc617d6e3479d1da295258c129a4a3000000066096880001e1688489d27fc1b76335c3d24449bbc18d40000001dbd0000000000262c0c95b7c92680007cbc0000001b085a4400013102b70e18da2589e3d05ab129a9c89e381f480006dfd6a80000000000000006e00006a000000000000a1a1c24650610d66e1a601d5a72f7dc5b8f6e7a61e64fa54809c5b994b2ce2438d120a64200000730000000000057591db6f5164a00000000001a90733c0000001baa000200800000005e603ac000000098c1225000047e10185b87a505b3000000088327029d8a1ec02f57d40001c0639598a66e0211c3c688466ed20ca21799fc45291fe81054d91f912ba557989a1d48cde5151f5f2de8d122c765884500a0e7efcf1e5eb1dc30b3d780288875d04fc0f8a0b1d80101126037109e69486180839825e1e7283c0000000052c8f06a3028e061800082c0048000000047ca63a859000000000003291a3d565181d350800098b88a48f59c500000e1614085da0000000000285000000001ae22a496f014d77480009fb080453f0000769e86c6e387806dc141263212825bf588871596147e35cb2000000002d59ae5cba1ba76d4148000000000003365fb87de0e780007b58000727c000000089100022ec0481c8a00017b27ff8bca00013d44d48612803000091519c27ec000060580007a48eb660f8c786ee85d600000002fc80009a10966000095a7a3000033e000000026747b3202c2ec0000000000000000001e0d2d177780009e3818f0001b5029ed7763590924372e2f849a1b793f80ba12ca80000c009eea0c8000665000033c80007f3a7205e09034000197b8cd1716580224e51800001b303802a807641a21a6c6f011c81aa83a2884554658b10642da9c2a463997837f00009f91a3e15bdbf169f000091fa6601d71e3c5fa07850c5c0000000c0b41292f80001c1e5481a009e0a87a5ad9d96790244a1af8000541090c94815c90001ab29248000000000000010306d3cab6a188000017a4f08578a9c584000010680003fd00003ce51bc000277400018f00001450000000089b000063d894525bc50c1e05e2e7fb20381e
  | 31 => 0x3f8062648964e42027a04579fd05018000000084a690191850c800000027c266d9f2c6760bfc2e6e4cf41b9f3c0001e08000000002b1ece2240000000000000009c831b00005b485309820acc34900001a6e5a8000203c0000df40000eec0a7a08e1e300006e897e00ab000015aa4c674e813303e9b009940399000159e00000004aa000056b00c900000003214e588c32770434178c000000060f0000000000000021d0000025a688800031600007d0c000450c0003220c22000000000000001f00a3a636000096600007d3a32600005ee02a20be84013cc786a5124ef1e8471fa5687261b0667e000000000000000c2e000158c97a980887a038a203850300026683ae9de44498000422a7162ed166e60dd93350500007829a8a3a080a50e226124060000312000075d0000497a5461ed83bc000281e3c927fe435521a9479b900001290256000073b0e486e6c97500020c89898d76890c00000000000a1197a0970000000000037914de5db94be34684f700000000000000214943e6cf20552fa064080e81a699fdcd6332e6ce035c8568b69d56000000017e00005325f80000000072ec2160b556f8000000000000008bc000000000007b280000001230000000070585801e61f4a00011a000000001ad082911302ca00000000000ea0679000027d86f18b2993634aa3470f6899033300008a18e928440179071e4869aa207430a0dc84d2244600022e4051a5fc771842a00007e84fa0c4e13d461c17500005f25b86444c908679c8d819709d07dba4744c381980ae043222180009e70000000000047140000000000338c29600012d69fd0bf800000000000000643c0000001dd17340b0298fc9025b212c053a198353090f48a605790ee1a209cf0cd40000a16000132e4f02484888087846e8a035f1854c1df9c961b0dc1223298462270e1807c90fc00000009fe00000000000326a2cc027d21b0001dbc1c98000360800094ca7925b0c66696c814161698540000a484b1800029ae1b6000013b77d45fa72a8000818104602e0000869206a0cfc55f63f0b7000000000001dd400021fc0001a16394069c00008bc162846300000006dbd9158879b5802099fe7cb5a7199a9ae06955bd73a016a008e800c86c08933a7a1172e3210e718136451881bb4a3179544240007e55a0b45ca1a892b8000000085914224b890aa59a8a780003c2800000015ae0001bc229d99720002693000134c8bd13320a000008cb0ddb000048e0001249479151f00016fc1f08000013181406568013c39218756075e3f28c6a000198c3db9cfe000000095824320000b6b3a3400000008fc0001aaf6080d38830000060480005f64b440000fe600000001e7a35f82280006efc1e434009f40001c1c36da50300019ac364cc9600000c46c54a869ff5f1f54a800001c90
  | 32 => 0xa68528c9902c0000000285600000006dc47362c3d12a00000003c119aa4fc000000000002c4a4765c0000000012ee64c81839c10b784a899ee2cd400030502c089019d51fe8d4c0000bce0000cd100026f60001bd9100e3496a922ce00000003aa94e76618000000129496480008daa754209a0126dd000072c173e7ea59213b6000000000005588b3e000252b9ca0718049c000676a67263026eb13b80000001a720001d246c78cbe3111b7200014a47c4965e684c53a2eae58d106084e54d0cc16f948be0e4166c5aad5ee399156a706e7cd77583ba3d55b36000000076810323699d1c3888a6f7b1965c4840cee4d99cba29603b6985000077b12b208705b00f5267a7c1a2fc60700007cec000000000035a8000000001400000005df0000590022e000000022c940468f000000013408da4000218000082202c8704ca6088dd50c532800080615ea1c712b96989efc3998bc100026341dd9a708518496621009b99b814748ea24da1022e289719af10b86728a4107a58ed5d000000003ba80007dc1e6e06495ca8adcd50380961e00021a263813d6000196291b119889e92120000130000000000000000000000000000015740002268000000000080c80002aa80000c5092c64515e60001574675c000a17062e1735c9e0000000000000099180003481ab50000000000012f000011a0001bfd07d17c8000000097e1264763847c5d3d42e0001f5b246a8144d124e00001b9c6e81c0033a031f91ba5dc3d9005a04382df00024c800000004d58b7e9910a3e000000007a0d3d00004a833727a45339b7894e1e445baa3ee2c81db79f6e5aa24a00007198000000223e765413211e96323ee127a9c3221828ad5ce00000008e6a1c20000d4d60018be6c720ce9aaa18a1cb9fd870412ed753a87e3b81dfa721a6e4482d47a744921c00000001605b3b000045c00000000c8902c8e48000709830c00000000000f6588b1f2e000224a8d382780000fab0001da37ae1308978a14e00000002d087c89e7400000012ea4180d0e40b80002dc9bbe0b600028ef0000000223c00017f256413f24238000000202433d04088d20e7425857240b1c2429ec0000000287467e8d717664d8c000045467aca04606c0000001a473648c530001f520000d4a5c79eb092d45de3799f4834de0aa20201e69de8a0670200003b68d6082115d29e2981e34b9a2f7bc11928d110c449f8f8444cc00050d800000003f40a967bd00007784bd061800005c40000000137c2b6000148e33b4a4359d1f8277a80000001a2a0f3400000012757a99dfe94211d821b254060462009b106d25e1e75e20f8cb806f40001ef868e89ba4c56648000086224f68eca4a74da06896b19e36971b6100000008a980e4000000000000000001e0c0000d8628cc65e00aa71226700001c9257a3
  | 33 => 0x88c228a0000de278180000000e6a352000015b800076fd2380000000000021e0000000000000067b400046ae42673280006b01718423000000000007e8e1887e6cbe085500007e108200d22242677243850e99a65ee4c1c4795f637968664781c52a3a5a0e800000007418ad21a0979469240008f1a17a0000000000000000015c46aa464a0001686000111e23fa47826025d04d61170027912d02a5946269836c1ba01d00eb812a3e61ca227a852604e0000000174800116268ad80000c996466f0dc5204b58fa303994278fa5b08aa0f8715d0000a0c2312610672a68a030554d9e8895424805c3256431706762a78175849282228c1a5445b244c4c8014a833266200003021330d894611cda432c1c417997ca3391ed80cdd88579e8dec3848a723fc9afe0001cfb1ac000000001800598000083800047a400000008367309fbc67a40005ad000000023a433f1cb425e53386c3025055f264013f9150945881d6a4c00030c8f7a95b96987399da240a8baa517153c024cb5619b832876b94563b2831c0000000756800000000000000000000075a88fd3126d809fa0000bfb9cae72e38a14d82dfc9a419bd0b067c95da4e9019a76b163c5388bbe2c7a6d617600000b4c7486b3d556031de980000000000074c95f045029b8d75842082c57b1164702ca7d1e499646f158702e981c96e681609e418a423e0fbe9290c427ff1a9c00015dc82b21ae4ea8bf085686f454c0000929de62000000000000009721b323a900009ea000024e22b0000105a728c000000148a00022720001db600000000001aec4a8e3de37e08f400023360c6d84500019ba8f711de00000993ad1b103a19200000102405547660001ca0051000044fc0006938000282000094f80000000614000000000000000001ffa55f9eae9ba1f4ba1d80002ec80bb0000e1a00003067e7932c44520bc141265e01082b43ee976c0421127a1c83a08ec80009418b4e9df9de67a284da2289694707ca3100013283cd194e726ca8c5e89e82150855626e26b83ca960e6a0919b000203e97091836eac00066c582570e974e5860cda7bf878704d423288a50967061a574ec8830606995177b900e78a24a02bb11b929e05b40bc4bc386e28466bea5b449b1e64470254e88d00108481f99184211204e538688e27ae43a268c830859f72006488c08000473205e73600007fcc0009609b249588cc32e80dd48dae7da9b306a27b784922fb833a7e3860068b61600a68ea64aa5b8901714f849b8b6908f01942c3162a238a1906f80f3a5bd9fc46b692ac59422a2a1f15486ca8ba2889daa052c0aa24fb186c4ed83382e704372ae0e4e03217065219a0f0611db211922dc6108a00293a2e00d6000058d064c000000000000000001ad32a2c6247fa135c082221326d881667301b2728400089c0
  | 34 => 0x4000000000027c0d0c057400000009ba0000000812400062a193b00000000001e104fd012e2898af483c072a00021580fe1df44d2909400014d42f01ca5194a53493e8dbc000211b0f580200dc925c253a81c0001368686c20c662c97a5f5c0006a19fd20001efa7ef80002d50000810039331f150e83e80003d3cedc000000000018240000c183240c266f3d61a767c6ee7cc910580d265254b80003d2227669184fa48e55b09df1cc00000b6d32d15d4158896a092d3ba0000efe00022665210fc027a00000001a7f87f92460dd15b43ef0000000000000007d000000000000000000000051b80005a08dac20e228e2d0119f1a6000800004db00010f928a84652fb0c7e62ca4d03f880006038000169a38e1d113ee00024f4000000000022846219ba41cf09346a489ac98108b6593206e6b500002c01ae44389021000059800004ae00009e08188000000101c654800097600e39a5533e00000000000000000145866902ec4088378223110a35980000000f5025b823040302382300276000000074780003cc011232e96525f4561c405984c8c680ea54148627c01a7a0bd97e30d482f40001dcf53b000000000000000000000131a1e7d4da8218dc60000f06744016221d09bc2988000000000000021bc000183f46990b302fce88000000081c800071640001c000cb63780fe4e59d8c00e00000001d8400007086d08fb65889dc80000000000093c000000000020fe000000070758ca000000000010cd6288000879813c0001ee8000179b3349f3900001140000cf000012141e589aa60b00005a6844000019576fb97780000c74000163091e98e60000ebc3499b5753c00000001f6b0000d5f460400025d80000001a183308bd557e8a8e000060c00026fe49e24a65f300000001326000088e26180005ef88ae00000000001b3e000091e896057e00000007e985d234d000021f0f028cb81ec745800070087305e740007e19fdc68b0cd07da80008ab8f4b726912801c40003ab99600001f18000001c63a0ce6555205200012fc0bb98405f99cc44e70000000000093f872819c65e84304e3209f248e00018ea8f28f6a21218c400019345f0cc0f05707ca9bd031277a223a744c63800004aa0f407a01bb0d8547a00005da267e95f5b9d65d82609f200006ffcbef8c6183593498fe0000000000269e00018da00000000f7051e000000000000e041f0fa87c51ed22d2debc738035a64e155a5b3a4c000021b23b58000034431a32fcac600027b40000188939085a52f00000b10000000000060a54881af5da42f98000944c06829f063600004704db80000000000475883d60e8000000096000022ba4550b8a7ca92323faa5be0000dfb0efa23968668121a1116e668800013a80001f98fad5fe9a388840a0512e076a4e000008c583608130220
  | 35 => 0xe00024140001be1000121e00000003dfc00032440001b7800092416580f19cb95a490bc0e580005c68000614800044680004c6000033885b50001c290000d770d9000062e9eba7db176494713242d7462200019ea23202223cdc6ca5708c2423a166006e678166d1c7404da76c000052e4f385c600006570aa4b369bb18dca0a80da5d99dce662983077109845d6243c441a78d5428ace091255e341800000000008b05fca000269c578c256559119000020f5000259416421c86ae23f0025c0fc80509d600013ae000251b000023e42400008871a155688d530002428028a710000192a00001be9d9280a01ea38014c80006b18fd00aa8d27901a1f88ac800023b000000008285af000076e68606a8400083e22ee6490a9139a25fe54e031090323e684d80cd00000e51bc084c00017a947526d090400006f710e59da80001e240005ea15b2000000073e800050219281b1e3662d5dd6e3d44cac000000000002486d740001b2478e2461a818e71f9600002f3356400083357202f1400068951080b082a47e746b6380d17634780a111d1f98819858f83a940c7d789165d100000000eee9b8112c8e509a800003ec0001bc72d2078b02604488520000858a3503b104dd36612b8956000000022ac1300af50000000000119c0000000344149e0000774173800003d84266468930000000074c9b9f3bc227c790d1970000000061c5a22f093a8000188c0000000000285a00027d10b4611e87e80dd3ff80005aa8687135d5fe51d9fb93e9838e0001e348d4946c609c0004364ec06e961742488dba0000000695800093f00006551b880001b4000000000000000448273600026ea6848a74957230a0001d2c621cb510000000984284ca099f448f3a6882f88ff884ee40e3dac67e0b6c05800015c849410002b281501451f781da0db40ae868372e246a23712a083ad23495c96413030134507138a00025b82959b214a98ee452ca6754531e8e237921f5ab9abc6a58ca80a725ee6c4848113516725e286c42b02300828a738964225122610505639d4c51a00002d78000000202a7134c0829082e031319004b718803762740142a7cb00000000000e0e61a60587c21af08e8000070354ef4651c38711045829a2287216105630f80008808dc156f94d26700aa884a17f600c9b5b5d520020a7dc8e0549e583e713601a18eac0001be236694ff0000d900c5800000011d09ec80006a3c000965c0009f593d2334ca947c640007241c828c39e4890202da7ee81ce2ac00007e2c00076d1faa000000000000007eba1d26458210763d6b76cdc82a47981c81ff816876996cf451433e7c318048e89ee474c103a00006fc3d510f268ea586540839554f8d0213a618c6d4589278d8fee52406ac1b9186544f800048f1784148800000000000001dff1708000176
  | 36 => 0xa1d354a3816e93f57d070cdc40108000099725520001fa16224f5999d930756a08644279ef61ce9d219b48634764a01e03b229a42e06ce159c00000000000000d8865a048a03703921ee967a8c414bb83bcfcd69f917425f868a4041882000033d0000000365817100000000000000875994030813d069208502bd8bc431b8000000040e76a800065d165494980003150000536c0007428e6c3d14a5a89a21569659d9d31697da73dddfb37a9ef87d596b00ec6566280809090880000af8340028c3700000efc0001d1400026569b18e94490a6dc7b0800a3ae146458e8000000017a000000022e80009d980004490000000015a5ce18bca1380000000ebe5b44000a0d80003d9c0006aba4cc8ae1868590898e36760c65061b626160000430800013c90881dc0000a1ba40a5b28d9c00000008639db802ddab315dc00000000005b900004080000773000000b88f6511800067991ed0000a6d0000ddd9ad23687668000317a0f21d005ea6d04e5aa0f890092e8000000009a3211ea88b9871933b05e48eb01da0000177839225a5a920000001bae0000000000000000018480359428716dc4a2bf800000003e20d0e1962b400005aed1680002206502926607343514b286080f146585810568642886e3ea9a840001e200151bd13dd8bf4000219893fd5f07db595e82e14c70001bf0000105400020a63f541678d5a12c267d3942bb91aa1d4020a854cc8a654e5c40d98000510a192652800051100005c4024c95680000001d70000000077d8e6e8458d8b3781f5d36289ae54e9d0e8d800d51111d7800000007d602bd00019856e9c00057c8000992000000026f24e680006eb400013797b82ba8c666d8cc2c682a0c400028009259f0e0ff8b88839e6a00af2584625160700000004ba0d445efcdef6cf50389859ca443b9d0096b80003e493e60000fc20000000000236d64a43ad1aac41291205a3012a79655b8db2762154436c149c49c8bb61ea01828071092a0184b6a091f202ef098a025672635c9cf616b92da2890cd92ce177027111c3645e77200006db60d9e3707094ba2381c321fb9b5584149d44b105a08281f948248a1a4de0cce0000cc4433800000000000001730036df02000000010f201f152270a5b4182d5821ac50f82784139905e16ea04e9469e141f313c2799997d972a47c83620a875f8f9729c27a21461dd00491d422101f795f90fae98edcc97f2031d6e040006b08000328848063e24f27370000300df923c40000411123e4f6139047b133a3d88dae6f10a4f2e7a7ee5230f2245710ea0b7174040d92202ca17cf0d792d09fa85861b2d1e00949a272a3dc7a08ec6462c68afc00001ba5448714000257e8728000000000009c27e053221aa60363045a000008b4a6ca000000012f0b345fc22910001e2c2201cee8de22f
  | 37 => 0x1198daa5ea80008ff000000000000000000000262849205fc1898c80712000098fa86a1a7a7e66fd4d58000000000000000aa00ce79385c80760000000000005140006ba41ea00006fa9eea37400007105a30b1485fa4948981b1457ddf57717030b000019115915800000000459a52e00000004de883c3ce233c000000029700000000128304231c7588000606000044080003d49f0462780000000f7c687564d5d09b045f967d0a11007e00000000001bc6592029342a80a089a9298330206450005e046d02e967513b8276a41e0811c3c22124b471313541db9cc80a8a45e748030997917222a586da2b6800063185446d689dc000055090b0b4f9ee089e9398ad89be00001c682e72f624ea0000000301863a30e80008460bc701e5a9a0c78a3905a80007b70000158197c01f24ce853e4bc365c8d617294a255c239e6d9c00051c1b9114d9c234bfc8ee5d702e8358800060192ec591d5a677c07f2634800019a26ee0719be36940d7a053086835953046540a2e91027502f6dc2b99e012b61d10b59190000742033474b858e904a2de8c79aad0d28c8f68095e02311c544ada3ea96e848c05f18345ed987d0001a9494a834639ca77b000259c29a8000000000072308946524b7c0002502000112170880007518d2c00000008ba800000000009e2d0140001ca826f97b70000a4452e000032500005a40000990800000023c800026c21eb80000001cf80000c986c580001f8257f00024ca0002216000176252d8ec8000000068440008c1a4ec8dc0dbe68d0cb000025ec71c000068b8a418e9818a0000f9342c8dff5c0a4d34260e40690904288cdd826edd25a20180005d404e08b0285e2e3e8023ff03a86cfe2c20001c7828301221371bde595c0007f0228c24e800063b80e27ea1645000000068521b400003fa1358ed498710dc0a1a6948e61ff49490dde3ba137e67115fc7d8210c4858e38627e34a0000ca00001c46000000000017858ea23400000000000000000003760000000683462a3318593000000087100002008000713ca7a089000055e0e1e2e34000a05955884c992c00016e94a19b6519080005e4cc9c00009cf1c1400000000000000a816baa5d201dcbd000006e00ea8f4e7c405705168d638502288068df7e2c6e66638e9508545657091624d668d451a370a45c00003d18d75abe29011f6323801a37400003359a3f46199a028bd1ad463182a000000084100006388000000000074980e8129061e37392d4310004e39d9ea4716274296004c89a680c27af8bde58162468270fce1e88c727ad9b4960992be6868000000000028505619768d369e5000002b800044ea6a400000000000000852e0de945c0009060000a12800058f80000001e9c38d824e37f800000000003df5c756e4a54a00027246fa9c6213d8b6658
  | 38 => 0xcb1984840cedea060abc05acb9866200000bb538e8290c003e147a64b2510400019376e080000ba80006d21bb640484949260f82164a6640000bd60000000000260a0be871200016c701d1ad2000026c373281000005716aa04fc4c401d43568c4615600000000000684099a0001d6c48a8000000000045aa18611b82262e74a3711ee63c2db154c0001e04336c0000000410000083986f80007f80a8a000000000000000000f6141d80005daa3e08821c2e6db009226484e47908e984170000854800042899f41c7a4d800020dc0000000473827466724e21d1a870716817e0000000697c00073a07d41981eec0000000000032f7eec00000027484fe078200002cb83940000d1028d50b20e06fb270e6d6552228ca7f349c0357176c1780cc815675a9c5e8d522fa436a16e3df80ee01421917660c9e057a5362d18478603056c1e1237c4b3441659d9eea53c9ec470d58385ed02954719ac43315db0030478d483a6e66fcdfef34510f757a422a40f1f5c39700d9474944a00011ea0000000649c000612846a000000000000000000000841950d52a9a060000fac000129204a5da58230c62020c000000003e000088a46c8f1825e00009f0000000012c882003e62338040451000076a0c563525f1c2c89f9300003f039e00007f6800000013dc0000c16000262b0000000000264a92f80003b3a0269699a3033a80001571a374148cc700024f64a7c86a867199d30a800016f8ceb00014a67d506d6538206c85b06921f194c000000005e9c000644000000000007c29c9279ccd3c5e6860e00012e202bc4304ac14725831c8800024020fa800053d8b26000130200012742bc97a05c12101249a04409992ce287987800011255b3104c115494a00011381de9d1a5bd00007b68b827b98b84367c5b6000000052b9d183fe80000000234005a1815b700009ac17a10001d2a8ce0b5300021718ad00000000f8e0b780004ca400000000000a41b357a800002f2673e70d1c766db9da9646dd6446c049a07c0bf6754800036390703dc80000a9dc7b284877c7b211c292740005af88e4244000006b92bd50796204b9c67c3e04ccf28e040917c80009939d5483fd6ba9f180001009b5c88c87ac71a16f257764604cc151a9da24c2022a19e36940003b190d37fd4d54514974604f407085107541349b8b6e30f437899cf547ac8b09110b109d69dc56d7c00002006303e20594770890e00000003fd4de83f51a6a6b6125800003b034fa1a08a00000614000092aa7b60000000000186255e8f5e13b12544520aac584800028b4da02991f1b4fa80001f580007ee09f10000a669bf2787000173a579439489780007ab15f800027f112180009de151c000048241a008f95d9d340000b2c8ca23d49ec46fe448800000000004d400000000c1e091800062d00
  | 39 => 0x47110f858080004d39add3d291238b604c60000000464e7a7000000000000001168e7a17705a40000c3c1d61b6a04417b063d238413cc000943982e80289fc2e0dc394160000000000000000008fea01a5bfa7145c5019f7d01fe44a71c2056aa7301501d9e890432e02122562551b66877248a075a0ba7a896966e604356b463ae2d317fe65a98ae2dba878000072c42fc6ae89e0000441c8884cd80004fe814f79c190495112f2833da9e5b78866439ddf3825815b0de84e23b49d605a3a7582685f4c10e9b390000d18891000051d1b43136064e00000008d602123cf9728a1200000000906864daaa000003c000000000000007dd400042680001c065046ff24884af15686c3800000d8c042b11b0a1b0171c15480782dc5b94a161cf034ca3c22c600008488b8600003c23701b5e8ef84768fa10c61e400005b94000683911134fce702b71896000209400000009188000000000028fc000000026107040002e911bf23e913c3a29ee26c74c8c3e30000566000020d275625dc3ce592c0003da03508b10b8701b11f59961a8d92c000087511623fb0f6f64440000000f707e0c000174272d552958600012fa0000af8284253ca17c0005c38dfd000000000004720000000000267c1e840004d08000000079a00000008ed28032a4c0005331b38860988e18109461a98a7e6fd199a56f259b5e39c452f302825cc9c3e71c9aca03494220f78e208a15d8d10880005eb873200011ee092a51953700000001a6d7139df22d963bb87c80001ed036a2ff99de000024096287600001b6497c19ca00018cc5ef1b2200002b35992589000122606d881a9168e4446d9fee000063e973211419e164300011468b19d4809461e400000000c840000d5130100000000b300005fe000000000006180e0c133809d000046c00021f6000019e2924c8690d00000001a9d0001bce00000007919e740002556801000000013ca93e000074100004f1000000000008f00fa01c59aee4911a0434207948769b2868cca0a5e7c4616158000000000076700000c29f366559e5e647167167d80000001136674861a00011a10000000000000049f0000000000014f80004a114308f691be2678000777234619cc8d25281b7e812a2359d1800098192d353f858238f8ae400002283be22d0376930c80882e60688446055e83374305ac9ea8f2e000059e764d2361b98f428f91f26000080c577a35b3d8e518035111d306919900027069e18fa212d24661bd9e5496911e2732cb5a824026a00010a85cb17e22398fcc691237a6600524000187c84f125500000002a993fc889238c83492028d882069270d8481fa1785969f469fc1ace88264e800018c200001f600005830000e0a2ea1a1c42118319e7a4309a61dca5068000000268200480006d48cd82fe90489798f0c3
  | 40 => 0x9a22530b7568c87d888ee7b5257052000000007b800000002222000000000019d06d3275c9c7827a3ebd7e93d980220001c492984f74a1e5aa68d9dac17890b30078269000018b63e400000a8017438b02d443b000071f0e9c91c000000009ce0fb800000014784e100006f58fc80ef5fa2067400074e09fe9c6800000000000000ec26e58000435037c5dd070e10e635a6d15b3a2a903ca25c9f884298b110590df252515d11a01c8707f1eb400000007aa80009ef000007700003e51a24000000000000000000e520000fa4000000000000001dc80007e400003600fe42c140be458000010b24bd0bc1a8e2d90000611070f000000034a6225000186171c40005e48096000000066f07204d6a4b13dd58aa81e00005009e6a99b40000000a501d2835c000000035a00002f2d8a0719087a00027007f51ab0000078679f00000001abf513217000000009fe8f1c70dc0000e74f8a2ee000065fe24c3d6000000000000000bd400017907250000153945e94c17a550593880000000780a09a53aa172000000000014c43e1890a7cd00567dc80006b784560001e0034e800060411dc0d880001fa9bb19a1975a45ea4b600028089e458985dfa342453800097816c62e963aa00027768719b56000000000001163b4283a00026ba6f6a7d9581a6b24461dcb003987a7e326334b9954000000b225c21026ba17361f886a863b251070c27bf6c625f243800007d1458c0000e7c00003c44d793de000195a1ac93f68e9e0d0000036e333400012407b200022f231d951788757880bd49526e344620001185000259e00000000000000000232078390e66478ea800000001afc69a6ae8932574cc3400021c00001fe6000238a2a692fe56e03fc82ba13e77f080a117800000023c459597ec4cf101e85a902820902940001dc74cd13c616a000000016d342099262a100007e719e006cc00068c5f9aa0e0f1276ac66c4eb00001fe15961668e5e18b04b00001ff8000000000024a100007fc0b4a6323e780002049c36102978683f000000010c010794e5928988a81e85bc8ee27dd00000003dcc00000008b47f78b06797000000000002f70000000000040180005858000000000000000006da400000012a566f8fb200015426a6457c913845200017d82a4800000000005d300000430000000032b9335f5a000184e47f00008aec60609b814384c0d22007a4b72d700000000df617005060001ab4000250084d00004dd03cc1c29137810892a635a2286961c2d9f1067054991ca5198fc400000004c58000988800000000000001a6e00000001a5d56600021cc0000000740800049da396561220d0000b3251a800069cd1150f61e9a509195c00000008c89c6c0000000000189c778a468000162e0001be48f300000500d30000194415e000081680000a6c
  | 41 => 0xa50b698d7080c8e834000203300000009af80009e00fdc29dc0008e21ef42a5e3f60c227de2ae8ce000001b027e0000356e52d0000ad6795922c9e3140e5e99a5a88d80009c2000000b2098000221a9fd4e1415da0546f296b57a40ae687a81a820e90be8b58ddf040a4dc00011785f7d03e72f1f8aa0303e400008765bc11160b8c5e2000057d5f014bd24b8fc64ca996c7d40000000251f8f60e081de42ae0fa26ac57a051612f993c57cc8f2152884d51f9fea600a5f6033136c9cd24de901043e4ff81ac437a6d4192dbfe4bc07ce3f49f7c42b80006ee40860000e0675f09749ff1576255a789854000006800006878000971800089409b29dfc00000000000001c9d2299f647cde4ee0cf120606fdb930a8d18a2d422be1f6a52277609a3000048800012a125b000000027d400018330001af271b800043286947bba5741180d0a6d1a73a00e901a4d18c4a0e25b4a6e167be9f7c000534050e16211ae4df26e29a28b8500002dd5fa8339314000028b0f000002010000205600009bd0000000777c00022580009d48c600000f808ec16b2401164900000008a5956c6d4c0008ce800088540c06b5e10a79a01fe90914924679ad0876100a7215f810e69cac84a800000012e43e653765478e2a2e486744402798086806e0001d9100012eb0a0400099b27d843ac4ca0111a080001d3e45096ec26c2456000235c986000000007f42e7e20400026b60e622f634a0c972620b9a000026294740280d4da6f1fb000000000005c8c000000250a4c793e00000000000018d00000000000c125ed4c3675e800008d9a2b64e400000021ce3918a886758e1059a17f494a5f2800012806764a46000147c2449b680001bd02af825f00000006d51ec0648000000019e20000000000000000021a625794381b508ac1a4000000007c428d800081706564e6276001900006bb658e5f7000000022547c599a80398644000000000000000000000000000000000000000000000000000000000001c010fc80000000000245160f00020707928b3a400811844c191968985c73ca06f26a226913d001582dd237646697d26028a7f0b406288779e60477d41065b8d1c2e5c0000000c680000000619cd5c000000000013226aace006b20a5e8015902731a60c30e191f8cc11529db85f40ca979638c13a6711c4c2368600e89fa49f7c78e905f347d12f5cab418801724e813da6a88ef26c80eb231e85f023a930a2dbe6245789e2a931000000022b54608f140000025481044a73f55b67dd89487528f3c0000000374e2642cf148043d94fa000173446e00000000f6c85f20b4a0804686b5855433d87040b180d84a918790ed00009f480000f200003771c044a790f582085958d1465a41a99b02b79b7b79d8000398212e9f28e540000ee62609bb3000035603ac000
  | 42 => 0x9b600004601d408851b2c000000000027a66a60000000000018c80000002126136643e3d716368118d9e2faa42012fce4247440000001ae39a01ba950f0000000197e00000000a2800083d139209511a7037c0002c5885d92a51956dcd38c2309e4c2c21d223a1010a33ea5de6eb00007d9a0f70bdcf3227610a40001be67ec88da6fc9e3a2bc0cb66ee13b00001ef23f58000000053c9cc8000000000084e1e1c7a0000066ce52829648d000009de000088f10000000000b3787d0000000000036e00000001e96513897c61c92c75b000603988000562cc052aba7e83148d3b000014e00015f40001f9f00000006e5c0009f706ba47048cc325400054a182338f278800000005f5
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x857175d83210421f3a6cb108210f5d365884108bce7b2c420845d73d9621042b2b8aa410821359ce64084108eaea32042084b67498c210423aba8c610821595d66208410acaeb29042084777654821042b3bb2a41082199dd95208410e4ee8a9042087247454821043a3b9aa410821d11cd5208410ec0e0a90420847775580210425a3a2c010821351cd600841087ee8b0ca00843c74586500422fb9ac328021171cd6194010aace7a0ca00853674cc6500426a39ac3200214d5d441900108eee3b2a800845e73d94400422eb9eca20021179cc65100108bae6328800846e721944004236b90ca20021879516310010c3aa8b18800853575104400434ab1882200216c5c04110010968e8b0c6008555750c6300423bb8eca980210f9d3650c01087ae9b28600843e74194300421eba0ca180211b9c8650c0108dae4328600861d6494c300430eb22a618021555d4310c010d2ac818860085d1700c430042b8baec3900216c9d361c8010ba4e7b0e40084797694720042e939e8390021789c841c8010b64e998e40085e2720c720043b0a904390021179cf65880108bae7b2c400852c7454a20042a639aa5100219954a6188010cceca10c400847771d95200422f398ca10021175cc6508010968e8b0840084d4735842004332b284210021785c021080108f6eab0840085b07458420042e839ac210021749cf4108010bc4e5a0840085b274cc420042f13966210021f00c83108010cd2cb10840085e2718842004338b284210021d85942108010cc2ca10840085e27308420042f03984210021359ce64c40108eaea32620084b67498f100423aba8c7880211d5d462c4010dc4c590620086e062083100423abb4a3080211e5d462840108f2ed28c20085d273d0610042d93a66308021b898b2184010dc0c410c200863765d91100423abacc8880212d9d264440109ace732220084e672991100431bb28c88802195d976344010d28c9b1a20084757598d100425b3a4c688021359ce63440109cce531a20086576518d100434bb20c688021a51906344010ccecbb1220086a464d89100436231ec4880211d5d6624401096ce931220084d6739891004273394c48802199d946244010d4ec831220086a4641891004363b18c488021b118c6244010dc6e0312200863464941100432a31ca0880219918a5044010d60c990220086d063c8110043703164088021ac1902044010da0c610220086e062081100431db2ec8880218ed946444010cb6cbb1a200865b6518d100434c320c6880219ad9762440108f2eb31220084ea729891004335b28c488021aad906244010d50c831220086cb631891004364318c488021b8dc46244010d60c9b0a20086d063d851004370316c2880211e9da5144010cd0c528a20086e06294510043703164288021b81882144010
  | 1 => 0x5404317322c42a0219398d6215010c9ac6b10a80866562984540421fba2c5a98210f1d162d4c1087ce9b0aa60843d74d85530421fba2c0a98210f1d16054c108beeca98a60861d6454c5304326a9ac429821875926314c10c5cc9310a60862d649885304317322c4298218b5916214c10c9cc6b10a608665629845304237390cba18211b5c865d0c108eaeb30e860846e721964304236b90cb218211d5d66190c108dee4b2a860846c725954304237390caa18211b5c86550c10a38e6aa2860851c7454d430423aba8c2a18218d5506150c10caaa630a8608479751814304237390ca218211b5c86510c10c3ecaa18860861d6550c43042cc3828621821179ce64948108bae7324a40843e7498e520421eba4c7290218b5c86454810c3ec9b1aa40861c64d8d520430fb20c6a9021871906354810c9ae431aa40845f73585520422e39ac2a90218dd906154810c68c830aa40865763185520432a318c2a90218ed906054810c70c8302a40865b63181520432c318c0a90219c18460548108deeca90a40862d645485204326b1aa429021879926314810c3cc8b18a40861d6458c520431ab24c2290219558e61148108bce7b2e840845d73d97420422f398cba1021175cc65d0810c3ca8b1e840861d5458f420423abacc3a1021475cc5490810a5ae42a4840852c7454a420426a39ac3210210fdd165508108bee6b2a840845c73595420422f398caa1021175cc655081087ced2a28408475751854204332a90c2a10210f5db541081087aec2a0840851d731504204296b90a8210210f9d365cc81087ae9b2e640843e74197320421eba0cb990218759253cc810c3ac8a9e640847575987320423cbacc1990210f9d0658c81087ae832c640851d7414e32042a6b90a719021531cd528c810968e8b0c640843f74595320421e3a2ca9902117dcd654c81087ce832a640843d74195320422f3b4a6990211d5d4614c810ccaa430a640847975181320421f3a0ca190210f5d0650c8108baeda98640845d7614c320428eba0a619021535c8530c8108bce7324a20845d73992510421f3a4c7288210f5d263944108bce7b2c820845d73d964104237396cb208211b5cb65904109d0e4b00820859573990410423bbb2a8208214d5d74310410c6acba1882086356550c41042d838286208214d5d442104108eeeab0082084d4735804104272392c020821781c9601041087ce9b2c620843d74d963104237396cb188211b5cb658c4109d0e4b006208475751903104278b80c8188212d9d2630c410b2ae931862084777654c310426abb48618821555d6430c410caacb21862086556550c310434a3228618821741c1430c410aaaea190620847775580310425a3a2c018821391c9600c410bc0e4b00620847575193210426b398c9908211d5d463c841096ce831e42
  | 2 => 0xc6a02218715063501108bceda9a808845c76d4d404422f3b0a6a0221171d853501108dcebb12808862f54d8940443162a6c4a022193d4f6250110c98a7b12808846e751894044317aa0c4a02218b1506250110c9ea6312808864c5318940442373b6a4a02211b1db5250110c9ec7a92808864c63d4940442373b0a4a022193d8c5250110c98c6292808863454d85404432ba9ec2a02219514f6150110ccea5b0a808866452d85404431baa0c2a02218d1506150110caea630a8088654531854044333a90c2a0221991486150110c3ea9318808861c5498c404430faa2c6202218715163101108beeda98808845d76d4c404422fbb0a620221175d85310110c9cc7a90808864d63d484044327318a4202219358c5210110c68a930e6088654539873044332294c3982218d15161cc110ca8a6b0e608866452587304421f3a6ca982210f5d3654c1108dae5b2a608843f74595304421e3a2ca982211bdc9654c11087cebb22608843e75191304421f3b6a8982210f1db544c11087cec2a2608843c76151304430fb26a69822187193534c110c3ec829a608861c6414d30442373aec4982218bd53624c110c58a9b12608864f53d89304432629ec4982211b9d4624c110c5ea8312608862c541893044327a98c4982219314c624c1108dceda92608846c76d493044317b26a4982218b193524c1108dcec292608862f641493044316320a4982218dd53614c110c68a9b0a608865453d853044333a96c2982219914b614c110c6ea830a608863454185304432ba98c2982219514c614c110ccea430a608866452185304421fbb6a8182210f5db540c11087eec2a0608843d76150304430f326a61822187593530c110c3cc8298608861d6414c3044317326a4182218b593520c110c5cc8290608862d64148304431a2a4c3902219514e61c8110cc8a530e408863454587204432a29ac3902219914961c81108bee6b2a408845c73595204422f3aec69022187d5363481108bcea31a408861f5418d204430e2a0c690221179db53481108b8eda9a408861f64d4d204422f3b0a690221171d85348110c3ec829a408861c6414d204431baa6c2902218d1536148110caea7b0a408865453d85204431baa0c2902218d1506148110caea630a4088654531852044333a90c290221991486148110e30a829e208872b5414b10443942a0a588221d2d4c52c4110e90a629620885567395210442b3394a908221c51535384110a6ce929c20885667294e104438baa0a708221c51505384110e48a9a94208874453d4a104429b3a4a508221559ce5284110e4ea829420887245414a10443a3a98a508221d114c52841108bee6b16a80845c7358b540422f39ec2aa021175cf615501087eecaa0a80861d5458c5404316aa2c42a021879916315010c9cc7310a80864d63988
  | 3 => 0xdb53d09108baeda9e848845f7614f424422ebb0a7a12219398f52d0910c9ac7a96848864e6314b4244326b18a5a1221179cf65909108bae7b2c848845f73596424422e39acb21221179cf65509108bae7b2a848845e73d94424422eb9eca2122117dcd65109108b8e6b28848847675984424431a2a4c2212219514e6110910cc8a5308848863454584424432a29ac22122199149611091087ce9b2e648843d74d97324423cb86cb992210fdd165cc910878e8b2e648843e74197324421eba0cb992210f9d664cc910878eab26648843f76d53324421ebb6a9992210fdd854cc91087aec2a6648861e64d4f324430eb26a7992218799053cc910c3ac829e648862e64d4b3244316b26a5992218b99052cc910c5ac8296648843e74d96324421eba6cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210fdd1654c910878e8b2a648847b70595324421f3a6ca192210f5d3650c91087ee8b28648843c74594324423b3acc2192218d152610c910ca8a7308648866452984324431a2a2c2192219514d610c910cc8a4b08648845e7598f414430faa4c7a0a218715263d05108b8eab1e828861f5458f414430e2a2c7a0a2117ddb53d05108baeda9e828845f7614f414422ebb0a7a0a219398f52d0510c9ac7a96828864e6314b4144326b18a5a0a218e15260d0510cd0a5306828866852583414432c29ec0a0a219a14b6050510c76a83028288658531814144334290c0a0a210f9d664cc510878eab26628843f76d53314421ebb6a998a210fdd854cc51087aec2a6628861e64d4f314430eb26a798a218799053cc510c3ac829e628862e64d4b3144316b26a598a218b99052cc510c5ac82966288658539833144334294c198a219a14960cc510c70a9b02628866852d81314431c2a0c098a2196d4c604c510cd0a43026288668529832144334292c190a210f9d7644851087cea322428843e76d51214421f3b0a890a21179d76348510c3ea9b1a428861c54d8d214422f3a8c690a2187d506348510c38a831a428845e76d4d214430fb26a690a218719353485108bcec29a428861f6414d214430e320a690a218bd935248510c58c9a92428864f63d49214432631ea490a218bd905248510c58c8292428864f631492144326318a490a218ed536048510c70a9b02428865b53d81214432c29ec090a219a14b6048510c76a8302428863854181214432da98c090a219614c6048510cd6a430242887275448421443922a24210a21d1d4d2108510e88a690842885e070484214431a2a4c3a02219514e61d0110cc8a530e808863454587404432a29ac3a02219914961d01108bce7b2a808845d73d954044236b96caa022117dcd65501108b8e6b2a808846f72595404422f3aec6a022187d536350110c38a9b1a808845e7518d404430faa0
  | 4 => 0xbeecaa0a68854f7255053442a6392a829a21879945414d10c3ac8320a68851e74d88534428eba6c429a21555c46214d10a3ce9b08a68851d74d84534428fba2c029a21471d16014d10a9ee4b00a68854c72580534428fba22029a21471d11014d108dce5b2e868846d72d97434423ab8ecba1a211bdc965d0d108d8e4b2e868846e72d964344236b96cb21a211d5c76590d108dee4b2c868846c725964344237396caa1a211b5cb6550d108dee4b2a868846c72595434423bb8acaa1a211edc16550d10a3ce7aa2868851e74d4d4344237396ca21a211b5cb6510d108dee4b28868846c72594434423bb8aca21a21475cc5410d10a3ae8298868851e7550c434428e3aa8621a21879954310d10c38caa18868854e7395352442a6b9ca9a922153dcd54d4910a98e6aa6a48870f54d4f52443862a6a7a92214b9d253d4910a5ae929ea48852f7454f52442963a2a7a9221c3d5053d4910e18a829ea48854e7319352442a6b98c9a92214b9d063d4910a5ae831ea48870d4310f52442973a6c3a92214b5d361d4910a9ce7b0ea48854d73d8752442973a6c1a92214b5d360d4910a9ce7b06a48854d73d83524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c3cc829ca48861d6414e5244317326a5292218b5935294910c9cc7a94a48864d63d4a524430f324c729221875926394910c3cc8b1ca48861d6458e524431b322c3292219598d619491087cedaa2a48843e76151524430faa6c6a9221871536354910c3ea831aa48861c5418d524422f3b6a6a922187d935354910c38c9a9aa48845e7614d524430fb20a6a9221871905354910c3ec9b1aa48861f6418d524430e320c6a92218dd936154910c68c9b0aa48865763d85524432a31ec2a922196d8f6054910cb0c7b02a48846f765485244297ba2a4292214b1d15214910a9ee6a90a48854c73548524422f39cc829221175ce641491087ce9318a48843d7498c52442973a4c4292214b5d26214910a9ce7310a48854d73988524431732ea8292211b5da5414910a9ce72a0a48854d739505244237bb2a82922153dcd5414910a98e6aa0a48862e65150524432732ea629221c3d535314910e18a9a98a48846d7694c52442973a4a6292214b5d253149108deeca98a48852f7454c52442963a2a629221939945314910e1ea8298a48870c5414c52442a739cc829221535ce6414910acae2320a48852e7498c5244296ba4c629221595c46314910e1a86218a48852f7458052442963a2c02922153dcd6014910a98e6b00a48852f7444052442963a2202922153dcd1014910a98e6880a48845f73597424422e39acba1221179cc65d09108bae632e848845e7598f424430faa4c7a12218715263d09108b8eab1e848861f5458f424430e2a2c7a122117d
  | 5 => 0x861d6494f318430eb22a798c218d59664cc610c6acab2663086b264983318428eba0a718c21179da534c6108baeda98630851d7414c31842caba4c618c211d5db530c6109aaeda9863085d270d4c31842caba0a618c21749c0530c610aaceb21863086946450c31842ab3a86418c212d1d1600c6109c8e4b0063084d673193218425b3a0c790c219a9486048610cd2a430243084d673990218425b3a4c610c211d5db52086109caeda9043085e270d4821842b2bb6a410c21995db5208610e8ce7a90430874573d4821843b1386a410c21789c05208610968e8b0043084d473580218426a39ac320421879516310210c3aa8b18810869563104408425a3a2c31842187592530c210c3ac8a986108695640c4308426b39cc9884212d9d263c42108bee6b16a88845c7358b544430fb1cc7aa22147dcd62d5110a38e6b16a88851f73587544428e39ac3aa221479cf60d5110a3ae7b06a88852e72d835444296b96c1aa22187d526395110c3ea8b1ca88862f5498a5444317aa2c52a2219398e6295110c9ac7314a88864e6358a5444326b1ac52a2219598d6195110cccc4b0ca88866a62582544430fb26c6aa22187d906355110c5ec9b12a88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432bb1ec2aa2219518f6155110ccec5b0aa88866462d85544432c31ec0aa2219a18b605511087eecaa0a88851f73550544428e39aa82a2214bdc95415110a58e4aa0a88851e73990544428eb9cc82a2214b9ca6415110a5ae5320a88861d6318c544428f39ec42a221475cf6215110a6ae2310a88851e73d84544428eb9ec22a22147dcd6015110a38e6b00a88852f725805444296392c02a2210fdd162d4d10878e8b16a68854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a68861f64993534428fba2c5a9a21471d162d4d10a3ee8b0ea68851c74587534428f3a6c1a9a21475d360d4d10a9ce5b06a68854d72d83534430f326a729a21875935394d10c5ea9314a68862c5498a5344327a9cc529a218bd516294d10c58a8b14a68864f5358a5344317324c529a218b5926294d10c5cc8b14a68862d6458a534431b322c329a21999896194d10cd4c4b04a68843e76d51534421f3b0a8a9a218bd536254d10c58a9b12a68862f5418953443162a0c4a9a2187d936354d10c38c9b1aa68862f64d895344316326c4a9a2193d8f6254d10c5ec8312a68862c641895344327b18c4a9a218dd936154d10c68c9b0aa68866762d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428fba2a629a21471d15314d10a9ee4a98a68854c7254c534428f3a4c629a21475d26314d10a9ce5318a68854d7298c534421f3a0c029a210f5d06014d10c3ccbaa0a68845d7695053442a7394a829a21535ca5414d108
  | 6 => 0x3c428eba4c629e211b9c865d0f108dae432e878851e73d5343c4297396a9a1e21475d253d0f108dce432c878846d7219643c428eb9ca921e21479d35390f10a9ce5a9c878846e7299543c4236b94caa1e21479cf5450f10a5ce5aa2878843e7615143c428f3a6a6a1e21539cb5350f108bcec29a878846e7299443c4236b94ca21e21475ce5410f1087eecaa0878851d7494c43c422fbb2a621e2147dd54310f10a3aeaa18878861e6550c43c430e32a8621e21661c14310f10a5ce9a94a58854e73d4a52c4237bb2a4296210f9d26314b1087ae9318a58845e73d9742c422eb9ecba16219398e52d0b10c9cc6a96858851d7395242c422f39eca21621175cf6510b108bce7328858845d7399442c428eb9ca8216210f9d365ccb1087ae9b2e658862e6494b32c4317322a5996210f9d0658cb1087ae832c658851d7494e32c421f3a6ca196210f5d3650cb1087ce9328658843d7499432c428eba4a619621475ce5490710a3ae72a083884e87258041c428eba4a718e21475d2530c7109d0e4b0063885e07048421c428eb9ca9a0621479cf5490310a5ce5aa4818843e7695140c428eb9ca8a0621879506350310c3aa831a818862e5418940c4316aa0c4a06218d9506150310c6aa830a818843d76d5040c428f39ea8206214b9cb5410310c3ea8b18818861c5458c40c428eba4a798621479d3538c310a9ce5a9c618845e7694d30c428eba4a69862187192534c310c38c8a9a618864e5318930c4326a98c4986219594c614c310caaa630a618845d76d4c30c428f3a6a61862187593530c310a9ce5a98618861d6414c30c422f39ec4aa421175cf625521087eecaa0a90861d5458c548430f322c62a4210f9d36254e1087ae9b12a70845f7654c538430eb22a629c21875926314e108dce5b2e870846d72d97438431b2a2c3a1c211b9cb6590e108dae5b2c8708656535864384237394caa1c211b5ca6550e10a38e6aa2870851c7454d438430fb2a8621c21875954310e10c3cc931ea50861e6458f528430eb22c7a94219698e60d4a10cb2c7306a50845e73992528422eb9cc9294210f9d26394a1087ae931ca50846f76548528422f39ecba1421175cf65d0a108bce7b2c850845d73d96428422f39ccb21421175ce6590a109a8e6b0c850852d72950428421f3a6cb994210f5d365cca1087ce832e650843d74197328421f3a6cb194210f5d3658ca1087ce932c650843d74996328425a3a2c3194210f9d2654ca1087ae932a650854d7294c328430f2a2c7a0c218755163d0610caacb31e83086556558f418436931cc1a0c21475cc549061087ced2a2830843d76d50418428eb98a820c21655ce64106108eaedaa083084b576d5041842d9386a820c21655cc5410610b64e02a0830853675d0c418429b3a88420c21351cd60106109c8e4b00830
  | 7 => 0x908619a5486048430ce4a2302421867151181210c21f3a4ca108610f5d265084308baebb18421849e74d8c210c30eaa6c610861875506308430cceca908421866565484210c3932a24210861c95512108430bc0e0908421845d7610e500c28ebae87a00618759743d0030c3aa931c801845f7558e400c30eaa2c72006187d944390030c3ca9b1a801861d54d8d400c30f2a0c6a006187550635003093ceda1a801851d75d0d400c30fb2e86a00618b9536250030c5aa9b12801862e54189400c316aa0c4a0061a3d0c6250030c6ca9b0a801863554d85400c31b2a0c2a00618d5506150030d2e8630a801861e5458c400c30eaa2c620061875944310030b32e0218801845f76553300c30f322a99806187dd954cc030c38ecaa6601861d5498b300c30eaa4c398061175da538c0308f2ed29c601843e76951300c21e3b4a8980610f9d9544c030c5ca9b12601862d54d89300c3172a0c4980618b550624c030c6ca9b0a601863554d85300c31b2a0c2980618d550614c030c3ee9b2a601861c74d95300c30fb2ec898061175d6644c03093ce932260184ce72991300c26b38cc89806187d94644c030c3aea322601845e76d51300c30e326a898061271da544c030a3aeb2a2601861f65951300c22e3b2a89806187191544c030938ecaa2601861f65551300c30fbb2a898061479d9544c030a38ecaa2601861c76551300c20e3b2a89806193d97624c030d18c9b12601870d54d89300c30eaa0c49806193d94624c030d1ec8312601868c64189300c386aa0c49806193d50624c030d1ca8312601864d54189300c346aa0c49806183550624c030caecbb0a601869464d85300c38aaa6c298061b118b614c030c3aa830a601865765185300c34bb20c298061a5190614c030e2aa830a60186c762185300c362310c29806195d50614c030d2ca830a601865554185300c34aaa0c29806185550614c030c3aa9b02601861c64941300c31dba6ca980618e1d3654c030c76cbb22601863b65191300c31db2ca8980618ed95544c030d30c9b1a60187195494d300c335b2ec4980619ad94624c030d50c831260186cb63189300c339b2ec2980619cd94614c030d60c830a60186d363185300c370310c2980619398e62d5310c9ac7316a98864e6358b54c4326b1ac5aa6219598e61d5310caac730ea9886666298754c4332b14c3aa621479cf5495310a5ce5aa4a98861f5458e54c428f39ec8aa6214b9cb64553108bce7b12a98845d73d8954c421fbb2a82a621475ce6415310c3ae7326a78862e6498b53c4316b24c5a9e218b99162d4f10c5ac8b16a7886366498753c431ab24c3a9e219998a61d4f10ccac530ea78851e74d4e53c430eb26a729e21539cb5394f10c38e6b24a78851e74d8d53c42a7396c6a9e210f9d36254f1087ae9b12a78845f7654c5
  | 8 => 0x95415030c3ce8b2e861861d65953430c30eaa4c5a18618755261d0c30c3aa8b06861863954582430c28eb9aa82186187d954310c30c3acaa18861863a54580430c28ebacc821861875966410c30a3aeb2a0861845f76550430c30f322a82186147dd95410c30c3eecaa0861861d54988430c30eaa4c22186117dd56010c30c3aa8b0086184cc72580430c26a38ac021861a69916010c3087ee8b0ca41843c74586520c21ebb4a8290610fdd954148308deeca90a41863654984520c31aaa4c2290618d9516114830c6aa8b08a41866552584520c30eaa4c7a10618795163d0830c3aa8b1e841861d5498e420c30eaa2c721061475d743908308eee2b2a841847471595420c296392a8a1061875536350830c3aa831a841863954d81420c296b94a821061475d74310830c3acba18841843d75993320c21fbaac9990610f5da54cc83087eecaa6641845d75192320c26b388c91906117dd9548c830c3cc8aa4641861d65552320c30fbb2a919061871d9548c830e1ee4aa4641870c72552320c30eaa4c31906187551608c830e1ca8990641845d75990320c2a6b96a819061475d6540c830c3cc8aa0641861c64550320c30fbb2a819061871d9540c830c3aa9310641870d54988320c386aa4a419061c3951520c830c3aa9308641849c74580320c30eaa2c019061351c5600c83087ee8b14a21843c7458a510c21ebb4a8288610fdd95414430c5ca9310a21862d54988510c3172a2c4288618b55162144308eeeca88a21866562544510c30eaa4c7a08618795163d0430c3aa8b1e821861d5498e410c30eaa2c720861475d743904308dee4b2a821846c72595410c29a38aa8a0861875536350430c3aa831a821863954d81410c29ab8ca820861475d74310430c3acba18821843d75993310c21fbaac9988610f5da54cc43087eecaa6621845d75192310c267390c91886117dd9548c430c3cc8aa4621861d65552310c30fbb2a918861871d9548c430e2ee2aa4621871471552310c30eaa4c51886187551608c430e2ca8988621845d75990310c2aab8ea818861475d6540c430c3cc8aa0621861c64550310c30fbb2a818861871d9540c430c3aa9310621861d54984310c38aaa4c218861c5552510c430e2ca8a88621849c74580310c30eaa2c018861331c9600c43087ce932e421843d74997210c30eaa4c7908618755163c843087ce932c421843d74996210c30eaa4c71086187551638843087ee8b2a421843c74595210c21f3a0ca908610f5d0654843087aebb22421843d75191210c21f3b4a8908610f1da544843087cecaa2421843c76551210c30f2a6c690861875536348430c3ca831a421861d5418d210c32631ca490861591c55248430ca8c728a421856472545210c31d2a6c0908618e5536048430c74a8302421863954181210c335290c
  | 9 => 0xcc6290829864d63148414c386a18a420a619598c5110530caac6288829871543144414c21fbb6a998a610f5db54cc53087eec2a6629862e64d4b314c316b26a598a618b99052cc530c5ac8296629863664147314c31ab20a398a619c146608c530c70a9b02629866852d81314c31c2a0c098a619a148604c530ce6a2302629843f74597214c21e3a2cb90a610fdd16588530878e8b2c429843e74d95214c21eba6ca90a610f9d2654853087ae932a429843e75d91214c21f3a8c890a610f9db5448530878edaa2429843e76151214c21e3b0a890a6187d536348530c38a9b1a429861f5418d214c30e2a0c690a618bd935248530c58c9a92429864f63d49214c32631ea490a61599c75248530c5ec8292429862c64149214c327b18a490a619318c5248530c6ec9a8a429863464d45214c32bb1ea290a619518f5148530acce5a8a429863764145214c31a320a290a6195d8c5148530ca8c628a429863b54d81214c31c2a6c090a619a14b6048530ce0a3b02429863b54181214c31c2a0c090a619ad486048530cd0a4302429867351181214c338288c090a610fdd16508530878e8b28429845e7598c214c24eba4c610a61871526308530c38a8b18429864e63148214c326b18a410a61595c45208530cacc6288429865563144214c2b2b90a210a61599d52108530ac8ea908429866665484214c33232a4210a61c9d512108530e48a890842985e070484214c30e2a4c7a02618715163d0130c9cc6296809864d6314b404c386a18a5a02619598c51d0130caac628e809871543147404c28f3ac8720261c390c5290130e2c8628c809861f5418d404c30e2a0c6a0261871954350130b30e0a1a809847675d85404c31baa6c2a02618d1536150130ccea5b0a809847675185404c31baa0c2a02618d1506150130d2a8630a809866752185404c332290c2a02611d9db5150130caec7a8a809865463d45404c333b16a2a02611d9d85150130caec628a809865463145404c38aa18a2a026199d885150130cc8c428a80987285414b304c3982a0a398261d814851cc130a9ce52a4609855671952304c30eb20a918261875d8548c130e18a9a94609870f5414a304c3862a0a51826193d90528c130c9ac8294609871454d46304c3a2296a318261c5d50518c130e28a828c609874752146304c3a2290a31826195d90518c130caac828c609851e73d8a540c316b10c52a061479cf6195030c6ac230ca81852e7298d540c296b94c6aa0614d9c66355030a6ae331aa81851e7218d540c28f388c6aa061479cf6255030a3ce7312a81851c73589540c29bb8ac4aa0614d1c56255030a70e0b12a81862d62189540c28f39ec2aa061479ce6155030a38e6b0aa81852f72585540c296392c2aa0614e1c16155030c6ac230aa81861c63981540c30e318c0aa0610fdd
  | 10 => 0x70d43148424c21fbb6a9992610f5db54cc93087eec2a6649862e6414b324c316b20a5992619a14a608c930c70a9b02649863854181324c335a90c099261599ca54d4530acae52a6a29856772553514c2b2392a9a8a61c55cc54d4530aaceb21ea2987145490f514c38a2a287a8a61c9d5352d4530e48a9a96a2985367494b514c29aba4a5a8a614ddd152d4530a68e8a96a2987275414b514c3922a0a5a8a61d190c52d4530e8a86296a29855573193514c38aa1887a8a614d9d362d4530a6ae9b16a29855573d8b514c2b8b86c5a8a6199d8a62d4530aace7a16a29855573d0b514c29b3a665a8a614d5d332d4530a6ce9b06a29853574d83514c2b3396c1a8a61595cb60d4530c5ea9314a29862c5498a514c317aa2c528a618b1516294530c5cc9a94a29862d64d4a514c317320a528a618b5905294530c6cc9a8ca29863564d46514c333316a328a619958b519453087cedaa2a29843e76151514c317aa6c4a8a618b1536254530c5ea8312a29862c54189514c2373b6a4a8a618bd935254530c58c9a92a29846e76149514c317b20a4a8a618b19052545308eeeca88a29853774544514c29a3a2a228a6159dc95114530ac8e4a88a29843f74588514c21e3a2c428a618d9975414530e2ee7aa0a29847576950514c2b3394a828a61595ca54145308eeecaa0a29856772550514c2b2392a828a618d9945414530e2ae62a0a2985567590c514c38baa48628a61c51524314530e2ea8a18a2987145450c514c33332ea428a61c9d535214530e48a9a90a29874643d48514c3a2a1ea428a611d5da5214530a6ce9290a29853574948514c23bbb2a428a614ddd15214530a68e8a90a29866665148514c393aa0a428a61c91505214530e8c86290a29874543148514c2aab9cc828a61555cc6414530aace1218a2985737050c514c2b83828628a61c5dd14314530e2ec8a18a2987146450c514c3a9b828628a61551c14314530ea0e0a18a2987154310c514c29bba2c428a614d1d16214530aaee6b10a29857370588514c2aab98c428a61995886214530aace7a10a29855573d08514c38aa1c8428a61559cc4214530aaae6210a29871543108514c29b3a66428a614d5d33214530ae6e0990a298570704c8514c29bba2c028a614d1d16014530acee4b00a29856472580514c29bba26028a614d1d13014530acee4980a298564724c0514c237b92cba0a611b1c965d0530c3ea931e829861c5498f414c30faa2c7a0a618715163d0530c9cc7a96829864d63d4b414c327318a5a0a619358c52d0530cacc7a8e829865663147414c32ab18a3a0a611bdc965905308d8e4b2c829861e6550e414c386a18a520a61c550c51905308dce5b2a829846d72d95414c237b92ca20a611b1c965105308bceb318829861c5498c414c30e2a2c620a61871954310530c9
  | 11 => 0x8c21fba2ca10c610f1d1650863093ce9b1843185e070484218c24e3a2cb9846147dd165cc230c38c9aa6611861e64553308c28fb9ac5aa26147dcd61d5130a5ce5b06a89852d72d83544c29b38ec1aa2614d5c760d5130c5ea9314a89862f5458a544c31baa4c32a2618dd516195130c9ac7314a89865563986544c333314c32a2619958a6195130cccc4b0ca89866562586544c31bb26c2aa26195d8f6155130ccec5b0aa89863764185544c32bb18c2aa26199d886155130cc8c430aa89867061d81544c21fbb2a82a2614bdc95415130a58e4aa0a89853771550544c29a38aa82a2614b9ca6415130a5ae5320a89853671990544c29ab8cc82a261475cf6215130a3ae6310a89851d73d84544c28eb98c22a2614bdc96015130a58e4b00a89853771580544c29a38ac02a2618e15260d0d30c3ee932c869861e65d52434c2a7394a921a61559c65490d30c38a9304869863b54181434c28f3aec8a1a61539ca5450d30aace32a2869845e76151434c28f3b0a8a1a61879d85450d30a3ce42a2869851e71151434c34db20c0a1a61599c654d4930acae32a6a49856771553524c2b238aa9a9261c35cc54d4930a9ceb21ea49870c5490f524c3862a287a9261535cc64d4930e1a8621ea49852e74d87524c296ba6c3a9261535cf61d4930ad2e1b0ea49866761987524c2973a6c1a92614b5d360d4930acce3b06a49856571d83524c317326a5292618b5935294930c6ea930ca49863454986524c333a94c3292618dd516194930c68a8b0ca49866752586524c21f3b6a8a92610f9d85454930c6ea9b0aa49863454d85524c31baa0c2a92618d15061549308deeca90a49852f74548524c2963a2a42926159dc55214930ac8e2a90a49843f74584524c21e3a2c2292618b9975414930e1ee7aa0a49846d76950524c2b338ca829261595c654149308deecaa0a49856771550524c2b238aa8292618b9945414930e1ae62a0a49854e7590c524c387aa48629261c31524314930e1ea8a18a49870c5450c524c2a6b9cc829261535cc6414930a9ce1218a49856b7050c524c2b43828629261c3dd14314930e1ec8a18a49870c6450c524c3a5b828629261531c14314930e90e0a18a49870d4310c524c297ba2c2292614b1d16114930a9ee6b08a49856b70584524c2a6b98c229261995846114930a5ee8b00a49852c74580524c2b3b8ac029261591c56014930a5ee8980a49852c744c0524c23bb8acba12611d1c565d0930c3ea931e849861c5498f424c30faa2c7a12618715163d0930c9cc7a96849864e6314b424c326b18a5a12611ddc565909308e8e2b2c849861e6550e424c386a18a5212611d9c765509308eae3b2a849847771594424c23a38aca21261179d66310930c38a9318849861c5458c424c30e32a86212619398c5210930c9ac62908498
  | 12 => 0x90843f018f6048421acaeb3024210dc67398121086e2b9cc090843b1d8e6048421d88c73024210de27098121086b3baac09084371dcd6048421b88e6b024210ec7631812108762318c090843b85806048421bc4ec3024210ee2761812108771b28c090843d8d946048421dc6c63024210fc3631812108761b18c090843b898c6048421dc2c63024210ee06318121087e0318c090843b018c6048421dc6ea3024210ee1751812108771b98c090843b89cc6048421dc2e63024210ee0731812108771a98c090843b894c6048421dc2a63024210ee0531812108771218c090843b850c6048421dc0863024210ce77648750086f038243a8043391d92194021bc0e090ca010c3f7458e500861e3a2c728043391d92154021d8ec690aa010ec46348550086f038242a804387d936354021c3ec831aa010e1c6418d5008673bb24228043b198d2114021d8ac6908a010de070484500863dbb2a0280434b9cb5495330a6ce3aa4a99843f7655054cc2c7396a8a1e61659c75450f30b32e1aa2879845e7615143cc24f3b0a8a1e61479d85450f30c3cec2a2879851e7115143cc38cb80a8a1e61871506050f30d3286b00879852e74d4a52cc2b338ea529661879914394b3087ee8b0ca59843c7458652cc237bb2a4296619398e52d0b30c9cc6a96859861e6550e42cc23b38eca216611d5c76510b308ece332885984757199442cc386a1ca4216618b99252ccb30c5cc8a96659853674d4651cc2b3396a328e6187991439473087ee8b14a39843c7458a51cc23bbb2a228e619598e51d0730cacc6a8e839861e6550e41cc237396ca20e611b5cb65107308dce5328839846d7299441cc38aa1ca220e618d99251cc730c6cc8a8e639843f7459521cc21e3a2ca90e610f9d3650873087ae9b28439843e7499421cc21eba4ca10e61275d26308730acae329043985657294421cc2b3baa4210e61595d52108730bc0e0908439843f76550548c22ebb6a821c61275db5410e30b34e1aa0871851d76d50438c30ebb6a821c61c69c35410e30b34e02a0871861f54984438c30faa2c021c61331c96010e309a8e2b00871846f76548528c23b38ecb214611d5c76590a308baeb32465184d671192328c28fba2a519461271d1650ca30a3ee8b28651854f72550328c266bb6a419461729c3520ca30a3ee8a9065185ca70148328c24e3a2c019461351c5600ca30c9ac4194a31847776544518c237396cb20c611b5cb6590630c3ea931c831845d75992318c267390c918c6187993548c630a3ee8a8c631849c74594318c28fba2ca18c6187193540c630aaee2aa0631855571948318c26abb6a218c61749c3510c630a3ee8a8863185d270144318c24e3a2c018c61331c9600c63087ce9b2e431843d74d97218c21f3a6cb10c610f5d3658863087ee8b2a431843c7459521
  | 13 => 0x5094121cb2c7a84a090c5e76d4d504870fb26a6a82438719353541218bcec29aa090e1f6414d504870e320a6a82431edd95014121ab6e6a80a090d5873540504861fba2c6282430f1d16314121cb4cba98a090f1b54d4c504863cbb4a6282434e9d25314121a72e9298a090c7b7654c504869dba2a6282434e1d15314121cb4ca298a090f1b5414c504878c2a0a628243cad522114121e50a9108a090f4b5388450487a429c42282434edd16314121a70e8b18a090d6b7258c50486b9b8ac6282434e9d06314121a72e8318a090d697218c50486b8b88c6282435a9ca4314121ad2e5218a090d727190c50486b8b8c8628243c650c4314121ab4e7a08a090d5973d0450486b539682282435a5cb4114121ad6e4a08a090d68725045048798a0882282434e9d33114121a72e9988a090d6a72cc450486b4b9662282435adc93114121ad0e4988a090f51310c450486adb9a4228243561cd2114121c5ac9316a610e3564987530868f3a6a729843875935394c21c38e6b24a610d1e74d8d530861f3a0c0a98430f5d06054c218beeca98a610d1d7498c530861fba2c0298430f1d16014c218dce432c8610c7671196430868eb9ca921843479d35390c218f6e0b2a8610c7870595430862f3b6a6a1843479d35350c218bcec29a8610c75751854308672b90c2a1843179cf6510c218f4e03288610c7970194430868eba4a62184317dd95310c21a3eeaa188610d1d7550c430870f32a8621843871954310c21a3ae72a48210e2d5498a410862f39eca20843175cf6510421a3ae72a08210d1d7494e3108726a9cc5188430f9d3650c42187ae9b286210c3e74994310861eba4ca18843475d2530c4218eaed2944210e3765d91210871bb28c89084395d976348421caeca31a4210e946418d21086e339e8490843715cf4248421b4ce99924210da574cc92108739b2ec0908439cd946048421d66c83024210eb0641812108769b18c090843b418c6048421dc6e43024210ee2521812108771a10c090843b89086048421dc2843024210ee0421812108771990c090843b88c86048421dc2643024210ee0321812108732baeca90843399c36548421cccedb2a4210ec765d8d21087a3b2ec690843e1d936348421acaeb31a4210da67498d21086d2ba4c690843719ce6348421bc4e131a4210de17098d21086b3baac69084369dd16348421b48e8b1a4210de37058d21086f0382c690843719d86348421d8cec31a4210ec76518d21087a3b28c690843e1d906348421d8cc831a4210ec46418d21087c2320c690843a119063484219cceda9a4210da674d4d21086d2ba6a690843699d25348421b4ae929a4210ce67614d21087a2a98a690843599d64348421acaeb21a4210ce77650d21086723b28690843e150c4348421dc6cbb024210f6365d8121087e1b1ec0
  | 14 => 0xe8b16a690d1c7458b534868fba2c3a9a43471d161d4d21a3ce9b06a690d1d74d8353486a6b96c1a9a43555c760d4d21a3ce9306a690d1d74983534870f326a729a43875935394d21c76a9304a690e5b53982534871daa2c129a4396d4d6094d21c74c9304a690e39649825348734b14c129a439c5866094d21c74c8b04a690e3964582534871daa6c0a9a438ed506054d21c3ec9b1aa690e1c64d8d5348716326c4a9a438d1936154d21c76c9b02a690e3864d81534872db1ec0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd846054d218beeca98a690d1f7454c534868e3a2a629a4356dc15314d21ab0e0a98a690d1e7498c534868eba4c629a43569c26314d21ab2e1318a690c3f74580534861e3a2c029a43879975414d218baed2a0a690d5a7095053486acb84a829a4317dd95414d21ab6e0aa0a690d587055053486a6b96c829a43555c76414d21c3ac8320a690d1e74d88534868eba6c429a43479d36114d21a3ae9b08a690d1f74484534868e3a24229a4347dd16014d21a38e8b00a690d4f7258053486abb8ac029a43479d06014d21a3ae8300a690d4d7218053486aab88c029a431e9c36590d218f2e1b2c8690c7b70596434863c382cb21a438bd526290d21c98a73148690c6c7558a434872629ac521a43391c56290d21c6ea930c8690e5453986434863a3aac321a439514d6190d219c8e4b0c8690c7a70d95434863cb86caa1a431ddc56550d218f6e0b2a8690c7870595434868f3a6a6a1a431e9c36510d218f2e1b288690c7b70594434863c382ca21a43475d05310d21a3ceaa188690d1c7550c434870f32a8621a43871954310d218bceb31e8290e1f5498f414870e2a4c7a0a43171d563d0521c3ea8b1e8290e1c5458f414862fbb6a7a0a43175db53d05218beec29e8290c5d7614f41487162a4c5a0a439314f6250521c5ea83128290e4c53189414869a3aa8220a43c514d4110521b48e4a088290c3e75993314861e3aac998a430fddb54cc52187aedaa66290c3f76153314861ebb0a998a438799353cc521c3ac9a9e6290e1e6414f314870eb20a798a439314e62cc52187ce9b2a6290c3d74d95314861fba2ca98a430f1d1654c521c58a9b126290e2c541893148727a98c498a43551d5310c521e28a89886290dc4724c431487862a0a710a430f9d263d412187ae931ea090f1b54d4f504869d3a4a7a82434e5d253d4121a76e8a9ea090d387454f504878daa0a7a8243c615053d4121a74e9b1ea090d3974d8f50486b4b96c7a82435c5c763d4121a74e931ea090d397498f504878ca1887a82434e9d361d4121a72e9b0ea090d5a73d8750486acb9ec3a8243569cf41d4121ab2e7a0ea090d3a74cc7504869cba663a8243879935394121c3ac9a9ca090e1e6414e504870eb20a7282439698f
  | 15 => 0x6f72580544c636392c02a2638d15161d0d31c3ccaa188698c6f76548524c6963a2a4292635a1c1521493187ee8b00a498c3c74580524c66a38ac7a12639358c52d09318bceb31c8498e1f5458f414c70e2a2c7a0a63475ce5490531a58e4aa48298d3870552414c61f3b0a8a0a63475ce5410531a6ae32a08298c3f76550414c696392a820a634e1c15410531a98e4aa46298d5870552314c63dbb2a0282634e1d15014131ad0e4a80a098c6f72590504c636392c8282630fdd16214131878e8b10a098e4e6358b540c72639ac5aa0639958a61d5031a5ce5aa4a818d2e72d91540c61fbb2a82a0631bdc960150318d8e4b00a818d2e72d53430c62fbaac32186335dd56190c31caeeab0c8618cd470586430c68f39ea8a18634b9cb5450c3187cec2a28618d8e72d51430c6cb38ea8a1863179d85450c3193cec2a28618d1e76151430c70f3b0a8a1863479c85450c31a3ce22a28618f1671151430c68eb80a8a1863355c46250c31c38a83028618c3f76550430c74aa1cc2218634b9d35294831c3cc8a1ca418c6f76548520c66ab8cc7a10639398e52d0831c9cc6a968418e1e6550e420c63db82caa10631e1c16550831d2a873088418e2e6494b320c717322a599063175d7648c8319aee2b246418c5d76d52320c6a6b96a91906327dd1618c8319aae3b206418d4d72d50320c6a6bacc41906353dd9520c831c9eeca906418d4c70548320c66bbaac21906395dd5610c8319a8e0b086418e1e6450e510c70eaa4c7208638719543104318baed29c6218d1d7494e310c63abb4a718863655d2538c4318beeab226218ccc72591310c66c382c898863275d3614c4319aceda0a6218e9564105310c6cb3a4a698863359d8434c4319aced9926218d9674cc9310c637b92c9280631b1c9649403187ee8b14a018c3c7458a500c70f398c8a8063875cc64540318bced21aa018e1c6490d500c70e32286a80638bd936254031c58c9b12a018e2f64189500c716320c4a80639390c6254031c9a86312a018c7b76540500c732b14c3aa44317dcd60952218b8e6b04a910c3f76550548870eaa2c62a443879916315221c9cc6b10a910e65629845488732b14c3a9c430fdd16094e21878e8b04a710c5f7654c538870eb22a629c43875926314e21c5cc8b10a710e6562984538863d384caa1c431e5c26550e21a38e6aa28710d1c7454d438870fb2a8621c43875954310e21c3ca8b1e8510e1d5458f428868eb98a9214430f9da5450a2187aedaa08510d1d73150428870eb24a7994438759153cca21a3ae829c6510c5e7694d328862ebb6a619443475d0530ca21c5ca8b108310e4e53588318862f398c8a8443175cc645422187ce831aa110c3d7418d508863dbb2a0284430f9d260d4d2187ae9306a690e1f6499353486a6b90c9a9a43555c464d4d21a3e
  | 16 => 0x716b20a5992831edd95014141ab0e6a80a0a0d68725405050637b92c6282831b1c963141418bee6b10a0a0c5c7358850506a7396a72988317dd95314c4196eeab0e8620e3775587431065a382c3a1883639cb5350c41b2ce3a9a8620c9e7614d431065ab88c4a1883a550e6110c41a9ce7a94a420e1e6350e5210637bb2a4290832d5c664cc841c5cc92966420e2e6454b321070f32a87190831edc1654c8418f0e0b2a6420e9543984321061ebb4a9208831d5da5490441b2ae72a48220d9673951411065b3b086a08831bdc963940418d8e4b1ca020c5f7358a501062e39ac528083879d06354041c3ae831aa020c3e76d0d501070e31e86a80838718d4354041c9ec7b12a020e4c63d895010727b18c4a80839318c6254041c5e86312a020e2d43189501063dbb2a0280839598d61d53318dee4b04a998c6c7258254cc68f39ec52a6638b5886295331a6ae2314a998d3571d8254cc68e39ac12a6634bdc96095331a58e4b04a998d377158254cc68f398c12a6634b9ca6355331a5ae531aa998d1e73d8954cc68f39cc4aa6634ddc56255331c5ac4312a998d2f7258554cc696392c2aa6634edc16155331a70e0b0aa998d1c7358154cc697b92c0aa6634b1c96055331a6ee2b02a998d1e7318154cc61fbb2a82a6638d5526190f31c6ca93088798e3a5498352cc71caa4c1a96638e95160d4b31c72a8b06a598d6a70d4a52cc61fba2c1296630f1d16094b3187aed2a0a598c3f7655052cc637bb2a4296638795263d0b31c3ca8b1e8598e1d5458f42cc61ebacc9996630fdd564ccb3187aed2a66598c3f7655332cc7872a264196638d952610cb31c6ca8b086598e1d5498f41cc70f2a2c7a0e638755163d0731c3aa9b1a8398e1d5418d41cc7172a4c5a86638b55262d4331c5ca8b16a198e2d5458b50cc6b5396a1286630fdd16294331878e8b14a198c3d7695050cc61fbb2a8286631edd95014331caac730ea918c6f72582548c636392c12a4630fdd95415231c5aa8b10a918e4d63988548c717322c42a4639958a6115231a9ce42a48718e3554185438c62f3b4a8a1c63479da5450e31c3ced2a28718d1e72951438c68eb84a8a1c63539c85450e31c3ca83028718c3f74582528c61e3a2c1294638b5c86454a318deeca90a518e2d64548528c70f2a2c7a14638755163d0a31c3acaa1c8518e9543986428c66a39ac32146347dd1528ca3193ee8b0c6518cd571d90328c62ebb6a81946353dc9540ca31a3ee8a906518e1e5458c418c70eb2cc998c638759564cc631c6acb3266318e3565593318c62e3b286a84631edd95014231c5ec8312a898e4f63189544c732316c2aa2639ad8b6055131cd0c5b02a898e3b64181544c72db18c0aa2639ad886055131cd0c4302a898e7361181544c61fbb2a82a2634b1c95415131a70e0aa0a898c
  | 17 => 0x80011ddc56094a438e8e2b04a521c6f765485290f32a92c2294871bdc960946438d8e4b04a321c77765445190f32b12a228c874e9c343542438f6eca80a121c77765445150eb2392a228a875c1c151145438f6e0b10a2a1c78705885150e37b92c028a871b1c960145438f6eca80a0a1d70715405050e9cb8486282871bdc961141438d8e4b08a0a1c5d769524310f0ebaecaa1887279c36550c43c3cedb2a8621d1e71d954310e8eb86caa1887475d66150c43a3eeab0a8621d8f725854310ec6392c2a188766dc16150c43b30e0b0a8621e95611854310e8ebacc0a188747dd56050c43b2ee2b028621d94715814310f0eba8c0a188727dd943d4443c3eeca1ca221e1c7650e5110f8bb8a8728887c51c54394443a38e0a1ca221e1d4398a5110f0ea1ac12888727dd943144438eeeca88a221c9f7650f5010e4e3b28728087661c14394043938eca1aa021d987050d5010f4aa1ec2a8087a550c6154043ab4e121aa021d587050d5010f0fbb286a8087471d94354043c38eca1aa021f1b7050d5010e8e38286a8087c61c14354043a30e0a1aa021f1543d855010f33b16c2a80878750c6154043e2a8630aa021e67621855010f32310c2a80878dd0c6154043cac8630aa021e35431855010f2aa18c2a80878550c615404393eeca18a021c7b765405010e37b92c129e831b1c96094f41a3ce9b14a7a0e4d6218a53d06aab88c529e83555c76094f41a38e8b04a7a0d4f7258253d06a6392c129e8355dc56094f41a3ce8304a7a0d4e7299153d06a6b94c8a9e83479d36254f41a3ce9312a7a0d577158953d0726b10c4a9e8353dc96154f41a98e4b0aa7a0d5b7058553d06ac382c2a9e83471d16054f41a9ee4b02a7a0d4c7258153d06abb8ac0a9e83479d06054f418beeca98a7a0e555398743d072b29cc221e839694e60d4b41cb2a7306a5a0e5a5358352d072ca9ac1a96835a9c35294b418bee6b04a5a0c5c7358252d062ebb4a62968317dd95314b418deeca90a5a0e1e6494f32d070f322a7996838759153ccb41c9ca7316a1a0e4d5398b50d072729ac5a86839354d62d4341ad4e5a84a1a0c5f7358a50d062e39ac528683175da53143418beeca98a1a0c7b7654050d0637b92c129c831b1c96094e418beeca98a720e4d53588539068f3b4a6a1c83879da5350e41a3ce529a8720d1d7094d439070f298c0a1c8317dcd6094a418b8e6b04a520c6f765485290726b1aa4294838759253cca41c3ac8a9e6520e1d6550e329074aa1cc3194832d1d1618ca41c3acb31e8320e1d6558f419072ab2cc7a0c839559563d0641878eca1aa120c7b76540509062fbb2a629a83531c95314d41ab0e0a98a6a0c6f725805350636392c029a83879954310d418deeca90a4a0d4c7354852506b4382a42928317dcd60149418b8e6b00a4a0cb471593325
  | 18 => 0xe003000c000019000000001c000004803400c001001000c00001d005800400801b006002c008001001000000403c000000005200600c0008014011000004c0000060018000000008000000800000100000000000010008000000000008006801c0050078014008007000802400a09c000805400802e001000c000000000021800802f001800800200a004800802600b005807c00002d002804000c035003809c00000200000b4000000000804000e0060040000006000003000000a03d002006405400100180000c0001000000800c023000006000a000001001400801a000000000000000380040080010090060000035004801400200b0008038010002006000c008017014801000e0000008068010009007800401a000003000003200c000800000400000200040020220030000002000003801001a017000000002800300b800801a0090058010000015002002800e0020048000004009001800801c00d001802400a009004803c0a2000009800000400d0098040000002001000800001b00100100240030060020016002000007800000300080540000020030008044002000002000000d000000005c002003000c002014009005002a00000d00340120030160004002000016800c0240010020004004004001004c00a0030050018006002000000003e0070198070000000004002000600300e805800200800100040040040018000002000005001c04e00600000000040000010030002005003005001000400580100020070000004000000003800c00c000004002001600700300200000000000004024001001801c000001000003000200600f0018014000001002400c00100000a4006002004006400e00e001000806e000000800001200f001001c01800c0000000000004006000801001500080000000030018010000005012801001600200f800801c008000800c004006004800800600100180000000000008008002004003002400a002002800c00200200b000000600c0008000002010002800001000200000f0016000009801400e00a010800400003300000800a8004012000000c00c011801c00001600f8084002008001800002600f000006001e00a00f000800400b009801c0040000000144000058000000000600100380b802e0000020004008008003000406c000000000800001301d00b802c00e001007000c01200080080000000030000000000001000400601c0000000000034002800000e00101b8018026024000000403c0030018000010005001802800000b003000000400f00b8014000004000000800a001000801402a00201b0070000007002800000c01f004000002001f000000800c00300480600240050048004006000000001c01600400880280180020030000000000004000803000000c806000a00c002001
  | 19 => 0x14f8928a7b4a811ac7f612f4c9292cf3401887200007fc590cd50de8eba3e70002ac12176075a19a9149e51f373a3bcaae48402121aae18a91401816073989443480005b84eb59b212152a0900000000000560c1f4000000000000000000033f00023d8be6611d971758e0c48b00014a00000000898000000000000000000090e00240040070028034038000004000c000000003001401e0020118000030002000005000a02e0020014000007000000001e06301a00100000020020010032004004800000e015011800c000000000000401400601e801800200000580b000e007001000000200a0060008074001002000400400300100080c80020008114016013002000000600501280080e20000048090002000012805800000500300080020170020014012003001002800601000c805c014000005000010800000b800003c003002801401e002000003c0000020000008006011001800001e0010020000024000002800000200200a80000060000020008006002000000c00002600a807000000d006800402a00b015009c00000000080040060010020024000003000000001800f001006800000e000000000c006000000000e02d0000014012007000005400000400500700080000038004006002001000c0000070058078016000002003403200301a000400000c00080b0006001003800000800300000000020010068018010000000001000000100200000000050048020022008000800000001b001000800c003000005000a00100e801000200400d8004008002006000c00600000100380040060000000008007014800c00001700380080620020008000000000009800002400a0020054012000002000400800b0190000002002001801801c00b008000c00a003000801802e01c00180140140000030008002001000000c008002003000000e011000002800000800380000000010060008000013000006000a009006004401600200000b0006000000801400e0080048008000038004803c00801300a80380780020058054002004002800407e0000008000000000009000c000015001002000600e00c003c0000450010000000013010801001c005005800800200100a80000000000000008036036005800800200000100000100050090070000003000006400600b007000401e0130098004018005000004c00c00f00c8048000000006000000200e001802c00e001007809800800600480fc00600001c000000000c016001400a00000880180220000018008002007000004401c000005004400c000000000000400300400040080010060000002000000804c01c0110010004000001000000000a01a001001c01c003003004c00202301b002c00000a00180200540060000058000004001000001e00e0030000000000004002400203
  | 20 => 0x5a126000223d110a5d0006960a6433c1c78a008027801031dad1c48a50c15ea54ac8bf2af1584a4e1160baa9c00ca41a2bc182511c7c733423774846b649cc20e0f096d41d05c24ac0002a302f35105bd17b80017714d134c0c744b81eb1dea4e914610753506e144a3695c18a0456694646e082543e9ec4972a8509f63e42da5069325f544086c4f4fa3c04d167422838559f0a4559e6f958997fcfe66f43d18cf49f62235df0b9ce586d9425cee4e5900055d818e61c33615d1b2c44a72726e26755de3a951e8326a08ae41cd5b313d2894c860264b6a4be03ec00116ebaa0001328f444fd17d8ae0dc400014910c545e7fb4da26849616ff1a39da00005162be1f4a54e89d4cca17a3f6a5111489e461a3f612080013f2b3c063a1a605ca8403346f6c6826515caecd3c86b1217a45d0560000ae9625068519db707c16f740756d973d1040f33329084c540c30000000cb41590e9623a53659f12a49441ec98e0d486e2d204e023328709bc000431a2d838a0843a4003c000a4a0822ed4000000029559572a055308899c0ee0000478988cc486780024c800000000000005b2afe8000d607ae0390001ccc060b3a498272cec0000455a6002868f724923b84a6000191286200034b1bd887cd060000002df33ae4c42e8e8a0c9200056a000092e95dc54067840b000023c00118201c47f8800ae635700023e40000c04b105cc79218f2018000c2810b2618e6e2ecb56c0fa710e0248d4128000cbc37d0002c300000cf5ab0000e2074203f2380b9a5c500001d8000a404a780004d456f00021953710003bea040d9026347309840000f24cbdfd97182904b0a4764843e027e07951600621082544000947800000045400000002eb4d28072d4e6a4d080001cf00000bc55900006f222a14d401c0007225880c290814ec3b6dada7653b08fc2634550cb8000073216f45c0560b10880b5224a20589dce986eb077ae2865e62406363a83a14e71c208cc48a14231a860005000006f80ecb6e7041a9174a4cc06631058817523030346bfc5b0a851d016b819f6b258728c8be232b06963ed5d61825431aa9186b768001d2e00000036e800105e33e000090a914179000246a0d9b1c41f03dc00058200000012f214f4fc0766ba054800026c08889448525462b223cbc5a0fb489216d5bfa0d866299343605b129678904684675e04f704e88e4538a1852191f11944592f788dc00000000026606c87cc00026aca7a10b8002a4365b18e0b000003aa8909909910c0686d41b8a8cde2476bde47514c499558a14209620002ea6c98a3f68c1558c3d12e0364f3a7e73be000000014c3748eb2d68ff0f8c9681590af1091a4d00211083fb9a5411a7ca82f8394918280e0439db6a9a84fae0d041722cd05d9671cd90f11eaa3e2741258bfa1e10dfd07489d90a25
  | 21 => 0x1d3d0de4b22eb9b6d526334314ecb0fd60000001b8133678c00000000001210002754693000430c0000000fd800147a0008d01ec9fd0b3800020884011daa7a5980426da4a08314864121e0d0800000070c91f2aa80011b00003c79cf02c84ae20fa5092ea00037f2ac9708ac12a6826c0001c713a07ba1c400b0e100014ee3df5965b384fc2df43d0df87a24c81b1035c2140f3854a2cf2026d710195689d4000000044439e4a310f2cb41a3463000000086a67e3f86070d1a7963ef1add0bb746168a138fb67c5042e6cd60c2edaa528bb0320ae0f494e4a4aa341a425003669352eda2b200000024418c86dead50008078cba8b8dc82be88eb73ed0884ed7022731d0a56678642e1011e0c6661e4cab9d5073a8d31aa2808b3120b29c03ec96a64017100f86ac9c757e80016c049a0fc252b6090af08442a6000a69bd39fa914e748b4e10f9250a5c4a6a36d08e178c4392886382134f316a14200bdbcf0da0fda40c5c394349e23bc5b10f0a00073535ca2a7190146d4740001f8375000044200024092c800025b3a30000000c3b49e23d1d78c5e4ac0000a0d46e00030728e08e931918000000000000c09aa097a7522fb8f400009bb3e41faf335298000119c00025200021ed7280000000a58eb400006600001ad87215600000006990001350054b093b399092789431e68000044ae95dd881ab864dd07e5f005689c95c7112d23605bdd627d9730917aae9eb47208dfc602d9d77a9b900000003829748da000052871433320689b6b88d135b352ba65300023a0aa83e94a60124b5864e2af8b1c6b2a27862214526c22c42a211e1d28778d79918bcc09c00005c092052b4e4638d52477918b0d9800004c89100009dab78385879c000088800076c9e85258ed1119520a6752917810b28ae8002c7c000b610001bd970430c2ac076056e305075a4a2ca0755446a2e964812b18514ec7f71445ba66a07563a430c235c0002db27481f482c97400022e719671b58a8ce16f51885da2254f307e12098a641edadf0ca0000000000000017cef880011b0fe41ce66053fac840000004fe239e82e852445895d21284b16ea538346b6d177100808b2f85be046d2f700001b800119376c4b62cc4a9eb71000026b3460000002df800000000000010848d60000e011380003dd25940003fa80018414aa5b401680590c861254d951cb8e9834cb8fb60de1c0800224684a7b823518750605caa286b100007900a2c4a081e792171a01493e9042fc036d17a9ff22893641261062ebc1e22b603b8b393b6d4cace0d58000bb238a5560001424aa728b8f10d011ce3cbacbc383000401403a7b044d009065ceae0a28002455550b9123d8ed03f472e22c17742aa13c44966dc85a694514c6593da73b0ba66663eb7f042fd3bc8d899a0ae25fc1a753a237028d0
  | 22 => 0x3bb4aa4e889196041379e7400000002000000000526f550494650011b617480e82969e04d698000007260001b15432000000000068a7e5270a9f8da26f00002b810b80004bf00012978c70001dcce8087abd98000a1d00002840002d0b6500000012909520001b8414b40d1e4524c1840004e0aee1188ad023a08eca448a780986b4a5e0000000838dde0000b715a0000000029263b30192609c2a7488272d3a4ed5d39e4725cd64880bb9f45728dccb3445342996888c02303f11064ac9751150075881778a03e2890ffc2dbaf496149020d322e07ea8c832453a013eddc069804137d3de8ce0d02da03f84274571284006b0d9a607d914c2ef0414c9922613f0b6d2cc398871127a8041e0aae1358be468c0b61269274f7503f0b2acad07ab18476db683d857008d0e9d466785426278cec21245c59e5059c05d4b213cc789aa01322eb88ae60533d1b2810306bbca9dc800000041da762c947b68000000d5e1d10740a8819b4823b88f485a40a096d1e6f1b487542210d07243d6a80936842e61bc920bc8b96ab949face01ac00001e11bc3bcaf52a8028f51823f1609a2c8249341e3086d4de3d33a18b28e729763790aa0b97929422825930c0fe1ee8e352f36c928a6552c9e05ed55874cf941343ea129d0521f25391786a4c0341b50c7c9ca85e28818e01aaaf825ba3a5454a642b880004fa62d184907828900000017b826a7c3000179d5a63a635c23e07a828e36197f16c6af6238827e6346911cba3ab7444773898dc44783ea5a0247b2e4a1b9728c5ce34a9f3e0ade897034441892555e66862c21878664562313449c030112137216ac6249b0224e7c86e1ea14219ac9f00003109ad079e8cb80009fc0001ac4ef01041090002a8971016200020300000ea00042c0434652a8100028a22d6a681039fe95e41492f901849e0a9c44305dcd3c0dab2b23c0edc44a000135968206956d01d17320000002818000907000064c11089900020610e59ce55185df242249000000000000033e9de8334000000060c5140002802ec563419103427ec0000000001c780000000000000bb00003c8800000000023c1648d0e5e826b986851a0002d90fd0e923f7080c0016d4a3a3d300013ac95f3568a7946373dbfd4ab600000000000000f2682263010e8fca2740100000005ba0fe67c82a417d045000124b42c1f587ef2820002772abc1199cc0bae1f2faa4b639e80000000003f414cc0000004c381567628c21c58ed40980000000000ca4a4e4218cb975088c1a48000b067031362b702e30000002a9419298a0000000000000318e4e0000910000014174e3cac875a9421c348800000000007b36f17b4846b03c95113d14800000000000000853ce69b946f6ac00000016544ce289da0169e9c346aac8c5aa06329a95a57640003ec2e24c4e2da8
  | 23 => 0x4ee9d1c97467543020292f8b0513345d11ad0ea5d2a95024085f234ace56d675c00017241ea00043c03191f14fe1bb000000077e000046400000043100002983c228720cc1f00000002e154d12f0048a95c0007843f46578c503f033b00000009e15a89ca56eea445a48000e7474e3a5111ac4aba00000b992f611e2c7ae74dca3100360a1c02e45422000012760000b3000057a3b73b1944415000007069681d3a3b85b8ea00004185991f755b200021511b56de2fa00002d12c68d78a400000004d338501da2c2507375171940a34005e0e88000a13390800157a8af4b4954c8d064800010112b269d044a6d477c98c49b8f8c9ea05b520a0911a900000000003300005a404400008f32bf00003424d81c6144ae5175f39f89d91ce1a455fca952415762de12bedd2a5e50b22bf249019193920c26c03131d1e8161683833480000003f3c5e17e55e2a8346f6ed811c0aa456dc1c6da9a8c901b00b4c0001574000442b3b2d7ad080004911430000f9a8a10000000007000392df41406000226028800000000029e50b962b45512907306c1117405eecc7c4140de74c8200000006d4e6ea0c0000eb10e98c643722880000000002c480009bc536941a45c0000bdd3e96336a713a8556c0266f282ab8c83614a00000000008e1418649c0000d10f19dbc00044f8000d4519a7be3fea4796208f24a52ee43c000000000007a54f908d4abd61761f36e0c1902e0970ff1bf4598075d160bf54e648e5752a616b244755989501c71450a80bd003e00046f00006aa350000029cb4a98f0aa6ebcfa4250336959cbc2325ca289396c825e037164af518a000003851c81010528aed15702580012188e000023e8bfcd765d32dda470c2164b45913b0e382d9d6b84a53bd0000001ea90cb5d3a9054244f02d43ee0cb21233a500005a93fc6df528048c2fd7a4af187192e65f1a460000b510000000204000000072a3956b8228511e01002a000004a4354490000a0a18567e393000146844e617000000000068e39400011e80b50001c74794a8e1dd23de66e11c224c000e220f44a38000e688762b0186c00000034491745bdbad00001346085230000000afa0001892bec03a8930675dc120a7f49a51114b5469700008056030000002b001c0659000000000000000000000000000000de49507c21b1818062600000013554b64e6351810d1d85fa00019e4ce80000001ad43dc8b925747e2580a9e42780000000004ea0001358a80000000064a000161ad789ec2113f90000000b3d5aa800135c1c455214fd2301f545948140008984afc4c80000000028ea80000000002078000a2248000000001ded0b8b140000003d094610d168a10e6c74e1a00000000000000dc0a98144000000000000158438e54c52bd34c6e65d1800059261c9551f4c2f8866bfb82fd
  | 24 => 0x8cf60002b615580002f502a4b5c004000546ed740000005bead2c01c2cd0000df159054c3b2a5270e71ff8001d10c3280822d276d76e000496a32b61301b51d8d844b69ba5a30848e9a1a609baa2a3be418b7424f40e4b75487c7896404b0183a19d23a9ea0001d58658a1a566282937e6ab45d80013c1a301760f70caa0003e1c0011221bf000000000069a5aa2268fde5c22ae298556874b00003b40009840f40000000b01545d9cd0800000000c790f376d00028acd7c382493667c885383013a248c0cb1b55e12fc0000000000000a8aa8d08f8ec80567810001eac00066a01200000426714f980016e000053617d80d48501a0aa1d48a1bebda87dc272053d45938d6b487881e917924a3c132f96912b07b43c995b95c24cd33b9700c2a35e3dc41268a52e11ca1e6d7600ac4192ba0de698b2ca0b72b601ae2b8642010d3ad43e8d4ccce00030b2b740003990b789604c02d309f08f4f5e9e3b5804a8d8e34f48101d31207f525a258774d58628e1bf1694025096a3155d80641ae83aa9c81cd4139d896ec3de3f2475cc8a78e4a44670e1e521454a1586e831841f88296a419d4a96e4898e95a262a9247acafe22fa5805da07f3f4870c80a7824f11fcacf89f5000000002250b10229ad5745950002b451a87bf022021eb0e000359a5e0f7ba312b9000101a224125833228c18d285e5981138c7d8184e8e5e0000c5ae6eb82a1b4098250be081b098a1a00000005af9b4c3940002b695114420475998b3c190a0f34fa0256881c81f10170000a4c00000002f0a59017a22572d8be4db2d26a921c028503f4ac6731450d9609767d11812aa51b39eb3d91d6c210807adfa1540af58b4269c5c3081c93829184ee830b1fb69996fdab5301221056c12a953237d15a9bd208072d1454bc1ca96340003f300015385b18dd5c6a0048ac7180000830abd00028e9afcd1e29a00022dad40007200ebd0e5697a28d80725d438730214803de4292fa000162c13300009a52e20b00000f43022134800000098f21ba7f9fc49df30821ca25886600000000000000000000e054285980358de090e1925a9946efbe90b2cbdc485d923e03800b023a485439af0078f0c55850fe081cae2053caf810c7bc4ee14a214c05c8c603341669030001c3856a28f028e69132db9b51b27c482889e5df856927c0778c50a4cfc876a432457c8ea10928915a94f820844e46a937c95b42b92603fa0000002644f359fa2dc84082f4a825d2000000082c000000132800058219fd4c0a2324482f80b427b18ede7131a4385b31a14a549a241d443c1b404f0ee17cb01309dac525581e258e2ed0ebc76c9f74230ab493814702b6c650542950002c9c11b48f31e0a5cbfc65b5731ca87b6a3f1924f38000aa0bf0000133789f5ce1c5484c04b3bb22ea7de6630d342844aa5b6
  | 25 => 0xe02015dc0004c900013049725524c090f413c5ca00b5f2487429f19c9f3879097723ca16632a81422a98d8df027215720d4b2c00052f8ecc11644bcd882908a485a138012b4e23f7b13254d44c8b143e2b2547204ddb605ed0d41479742de34ca1b68d38a2d2de52e10e209f36112c4aa9a0462a57b1631a883ba2180bf00011b20383d880000003cb3718b401003435b9a524b393724b5867c6635750d28364ec844e0dc8c052621d88d1141824b3ee5b48fd4f484000a889c4cdcad83bda6203fe2324419f6800026f4b70000fd892f5c300014009219b294b04f892c000001827a9e557c8930c760002f62c34c389ca000000119e0000490118b20ac63381c25312130597c00173e33a5910000ad60000002ca010e00000015e90e364334a8b5e0005420e8000116a87f39c09a03e64cc286055d0fc00019a80015dc064b3c281c0002a400027a0d8c60c1c49b3c0005d24276afcdda6574032d1d4a625285ca3491879f00dba5a8064564551207430c0d200018863a43cc3c6ac213907860af2182e838b839106a0dc8a943841bb0f1615800014ae00000050700001fe531000000089091bbd818f46ee00057381652475a03dc86648104c0000000161e2434aa00310509b234d80015bc7b63ac2e687d83f232894a6e4054b0a000009a0a38d5b02ace469c25184000000aa62ea00000000d400000009c40d81dd909102aa200862c001305e52916de4c5c927c3ee4320000003ac80000000003d61b600009060000efc0002f10270dc159491937b8000b4600000005c8fb233000013496220bd5d580013dc000000182020641a80028d56f67690f8a26cf509704fe9188864afc1e2e4e522c78706e96cc08a000405a834e320004d38ffd43a000000000162e9a01cd0000ff2ac700003e80000001b008500ce000039800000000000012ac0007fc0c38000f858c93198000000000447c00076b00011a80015ee0ce000000000000018d800000075005f4f900002f3420823b2b853600010a0000000165ae000000003eb1d4d0d6073a1128b4fe347327bc874e645dc14e993139a6610002918ef02472d8956c0000000002e4e09400009700006be8120000000baab89a4000000460004be80008560005cba64163c911136ae5875c00018a2038ff014a856a1dc0000b2514aa64e951170df0b10df60000001e7d48e7438000000000b455569a4c0cf53730582e898432a252a2b037a0bfae880357749d200500980201e40d8178a24a28938005c4a6021a04614916682852792330af20e35a8159842c4152df24ac5041e99d3cac557043b04a8f990178800002920ce4b1a9eaee8552c741000205845e0002280764c65a0b05d99b110a6c43dce2a2da0000000102865a000000000056036e45bc1207b4a0441080015a40002d097ec95b5403f3287
  | 26 => 0x28181f26d88a68000000d78000000000000000000000000002c84cf1b5130a73655b983c69a58c144145a41e189561a0de4808c1dd74b791fa0002d39ef40000000000dfcb985bb8659454e6093300001507ca0ec0002d607e2788000000078eba63f18000a782fc0001eec00059b309800000000031118b0ae85d68000000542aed5de0b90c8e59700008890445410001b593310004332714c1a000047c8e94fa0001f09ae80000711e00000e4877541e000104c39c3e58d704705e400022aa00080f3611e944680ee5948d6c1374360419a58b9045b4efc0001b93c500015fc36427a1cb2a24e7ca1531180682d284954d2e3c94c5df4a223128ca23142e861f1fc4cf31f90c172600023f8d380005ea04100504881bb1d80f4e30735a12421af0e04cb0b19f9c44c2191b5adc8a260ca105c8548129820000000000a8f28100011f400054b8000000b0721f9be80b51bc0ab079800063000002e0b3261ac644a300ae22b2cf28ae00071f00000000f499643a1f3cd52aaa558800013e00019180000000000000d9c0007ae0001e647d041c28a16ad234b250001af4182320566a5fa887b4c5c40c4569a5b834427001bc22d4e998dc00099c25480008862bf00007b489158100000011d90001c400000002f612ea98c000abe32a1d1522477708287fab2611828794a40009141a11c955141f42f58834cc80000002b2ca3cb3531c897cb009c65a72cdd11406d38b26bc0fd32842516f6a685c8d3a85fc00052d4e80ff45d680c4615e7a8ec6920000f54f6e77f1dc17385fc0000000202c9a2d617000007f4b7400000011a22c24adc31e6768793050aa53b48f10001ab8000ad63ffa726a865de53c00cc06a1f95cf20803365e21d4453958a25a4dc03e495a7e
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x6348421ac28099063484218a4865d253484218e280dd94348421a848650c4348421e806418f6048421c867418e6048421ac3835806048421ac0835806048421e8364d8c6048421aa28498c6048421aa18498c6048421ac28398c6048421a638558c6048421aa38458c6048421aa08458c6048421ac28618c6048421e436518c6048421e836418c6048421e806418c6048421ac3835d46048421ac0835d46048421a63855cc6048421aa3845cc6048421aa0845cc6048421a61851cc6048421aa2841cc6048421aa1841cc6048421aa284d4c6048421aa184d4c6048421aa28494c6048421aa18494c6048421e415314c6048421a628590c6048421a618590c6048421e814310c6048421cc3631c12154021cc0631c12154021cc2631c12114021cc1631c12114021c1a765c05450f30c19769c35410e30c17541c56010e30a1a85d906050d30d0b741c14314930d13741c14314530a6281d486048530a6282d446048530a0d8498c5208530a158498c5108530c62651c12108530c60651c12108530d23541c12108530d20541c12108530a908050c6150130e05431486150130b108050c5150130e05431885150130a24815886255030a28805886255030a24825846155030a30805846155030c0d541c96010c30c15541c56010c30a19859916010c30a16811d9548c830c15541c5600c830a0e821d9548c43081c87551600c430c0d541c9600c430a60815486048430a6082544604843081f875536308430924875512108430c63651c12108430c61651c12108430d22541c12108430d21541c1210843081f87d974350030a0d85d0c6250030a1585d0c6150030c19655c04310030990815c04310030a0e82dd9544c030a1681dd9544c03081e869d9544c030a0c86553624c030a0e86550624c030a0c86550624c030a1486553614c030e055418b614c030a1686550614c030a1486550614c030e0554d88614c030e0554188614c030a0e82d516395310c0d649cb5394f1081e879954310f10a0e829954310f10c1a651c14310f10a0d839506250310a15839506150310a0e82d51631031081d87192534c310a0d8494c624c310a158494c614c31081f87593530c310c0d649cb530c310d06749cf5208610c61769c35208610d42739c35208610d41739c35208610d23541c12108510d20541c12108510d43531c12108510d40531c12108510c19651c14310c108e0825c0640c410a1585191430c410a9180191430c410c90641c1430c410d04741cd5208410d23741c15208410d20741c15208410d43731c15208410d40731c15208410c157558c4110010990835c04110010c91635c041100109a0825c04110010c1575590310c010990845c0310c010c91645c0310c0109c0825c0310c0109c0835c021080109a2849cc2108010a61851882184010
  | 1 => 0x20000c27d00c00cc00572a600ad000002a1b55d780000000005840a554a6c0000270ed0034000007880000007652000e694002346e00131cec739d088472981f80000000300ade000013d4e005280cb0694fa8a00b400239041ac180118120681426a308945588bc31ece248402aca1431715000002f52cee25a31d288001b47c7414590003c0024c01491d0400014b08e01c0000112b600a1800000000381deb69a000b464042249d4d350ce2cfe5917aa81800001ac00300000052230780015501418d10b10004a789e481f132a3ba05d368a802251e8a000089200320f9083b501d4da8100130687ca68e2000056400000000274dc72000688e09af9388aa904aa2ae5a1c2330a604d65856184ba4960aa80174000000038f20041606846a12a260f878000016b1d42bc00932080566202a8a94464998222c9125148fc9ed318832782b25400240021c6253404000065315e8c30033840d83d2e046030000402000180c340600000160a0980804010000000000280c00160400428040100c0a0600040001b000081007030000e17018bc1c01020080c00000041000000240c000380c220d00028000e010040200070000202a84825846150c43a90805846150c43a0e821d94394443a908050c6154043a1681dd9435404391a861c14354043c1a861c14354043a148650f6154043b108050f6154043a188050c6154043a148650c6154043b108050c6154043e0543d886154043e05431886154043a308050c6154043a508050c6154043e138050c6154043a148050c6154043e108050c6154043a108050c615404390c825c25350e41a198094c6050e418b0805c46250c4190c825c25450e31a19809506050e3190c825c05450c318d0805c46250c31a19801506050c31a8482590414c431a9080590414c431d04531c94110521d04541c9310c521960815ca4314121960825c64314121b20825044114121b40824c431141218e0805c86150c21918805d54310c2181e879954310c21a19801954310c21ac283d086048421ac183d086048421aa284cc86048421aa184cc86048421a868499
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xa38018816c27132600012a218010400058024143d886154043b0048286310c2a808720892602531814390641124c04a83028718c82249801506050c31b0048286290c2a02616009050c62145404c281525328e0a1887884a024980191430c410a08ca8c8382861882188163209701044004212130b22e01886008620590825c0310c010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 22
  | 6 => 969
  | 5 => 5184
  | 4 => 3009
  | 3 => 181
  | 2 => 13
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
  | 7 => packedAt gbK7 (430+((h/13+packedAt gbK7 (352+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (31287+((h/427+packedAt gbK6 (26163+(h % 427)*12) 12) % 2049)*11) 11
  | 5 => packedAt gbK5 (227064+((h/2148+packedAt gbK5 (196992+(h % 2148)*14) 14) % 8509)*14) 14
  | 4 => packedAt gbK4 (162807+((h/1182+packedAt gbK4 (147441+(h % 1182)*13) 13) % 4256)*13) 13
  | 3 => packedAt gbK3 (11562+((h/78+packedAt gbK3 (10860+(h % 78)*9) 9) % 309)*9) 9
  | 2 => packedAt gbK2 (948+((h/5+packedAt gbK2 (923+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffffffffff03ffffffffffffe1fffff
  | 1 => 0x7fff01fffc07fffffc0fff03ffc0fffe71e3f
  | 2 => 0xf80fffe03fff80ffffff03ffc0fff03ff9e3c7
  | 3 => 0xfff000003fffff01fffffc0000ffffc1fe03f8
  | 4 => 0xffffffffc0000001ffffffffff000001fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x812114288491224400b2cb4512d14420a6cdb
  | 1 => 0x42a4a4c514872448b2c055522a548ab4e5162d
  | 2 => 0x5688c289a5120e913555026a889aa23971a346
  | 3 => 0x64ce8b163a24481dd9a6980c30e3cf11be03b0
  | 4 => 0x870f0c183c3870e1ee38e38f3c030c21dfd800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xe8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880e8a8a880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37051
namespace PEqualNP.Outside.L_meta_37051
open PEqualNP.Outside.L_meta_37051.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 13 := bgb_2_0
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
theorem bgb_3_160 : Interval gbAtlas 3 160 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 181 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat bgb_3_96 (concat bgb_3_128 bgb_3_160)))
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
theorem bgb_4_3008 : Interval gbAtlas 4 3008 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3009 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 (concat bgb_4_384 bgb_4_416)) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512))) (concat (concat bgb_4_544 (concat bgb_4_576 bgb_4_608)) (concat bgb_4_640 (concat bgb_4_672 bgb_4_704))))) (concat (concat (concat (concat bgb_4_736 (concat bgb_4_768 bgb_4_800)) (concat bgb_4_832 (concat bgb_4_864 bgb_4_896))) (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat bgb_4_1024 (concat bgb_4_1056 bgb_4_1088)))) (concat (concat (concat bgb_4_1120 (concat bgb_4_1152 bgb_4_1184)) (concat bgb_4_1216 (concat bgb_4_1248 bgb_4_1280))) (concat (concat bgb_4_1312 (concat bgb_4_1344 bgb_4_1376)) (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)))))) (concat (concat (concat (concat (concat bgb_4_1504 (concat bgb_4_1536 bgb_4_1568)) (concat bgb_4_1600 (concat bgb_4_1632 bgb_4_1664))) (concat (concat bgb_4_1696 (concat bgb_4_1728 bgb_4_1760)) (concat bgb_4_1792 (concat bgb_4_1824 bgb_4_1856)))) (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat bgb_4_1984 (concat bgb_4_2016 bgb_4_2048))) (concat (concat bgb_4_2080 (concat bgb_4_2112 bgb_4_2144)) (concat bgb_4_2176 (concat bgb_4_2208 bgb_4_2240))))) (concat (concat (concat (concat bgb_4_2272 (concat bgb_4_2304 bgb_4_2336)) (concat bgb_4_2368 (concat bgb_4_2400 bgb_4_2432))) (concat (concat bgb_4_2464 (concat bgb_4_2496 bgb_4_2528)) (concat bgb_4_2560 (concat bgb_4_2592 bgb_4_2624)))) (concat (concat (concat bgb_4_2656 (concat bgb_4_2688 bgb_4_2720)) (concat bgb_4_2752 (concat bgb_4_2784 bgb_4_2816))) (concat (concat bgb_4_2848 (concat bgb_4_2880 bgb_4_2912)) (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)))))))
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
theorem allgb_5 : Interval gbAtlas 5 0 5184 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560))))))) (concat (concat (concat (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720))) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)))) (concat (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040))) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200))))) (concat (concat (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360))) (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 (concat bgb_5_3488 bgb_5_3520)))) (concat (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)))))) (concat (concat (concat (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000))) (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)))) (concat (concat (concat bgb_5_4192 bgb_5_4224) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 bgb_5_4384) (concat bgb_5_4416 (concat bgb_5_4448 bgb_5_4480))))) (concat (concat (concat (concat bgb_5_4512 bgb_5_4544) (concat bgb_5_4576 (concat bgb_5_4608 bgb_5_4640))) (concat (concat bgb_5_4672 bgb_5_4704) (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)))) (concat (concat (concat bgb_5_4832 bgb_5_4864) (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960))) (concat (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))))))))
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
theorem bgb_6_960 : Interval gbAtlas 6 960 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 969 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 22 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xffffffffe8a8a880ffffffffe8a8a880ffffffffe8a8a880ffffffffe8a8a880ffffffffe8a8a880ffffffffe8a8a880ffffffffe8a8a880ffffffffe8a8a880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,0,32)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,0,32)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37051.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.or,[4,5]⟩,⟨.or,[1,6]⟩,⟨.and,[2,8]⟩,⟨.and,[3,9]⟩,⟨.or,[0,10]⟩,⟨.or,[0,9]⟩,⟨.or,[3,12]⟩,⟨.and,[1,7]⟩,⟨.and,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37051

open PEqualNP.Outside.L_meta_37051 in
theorem PEqualNP.Outside.L_meta_37051 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008372906) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
