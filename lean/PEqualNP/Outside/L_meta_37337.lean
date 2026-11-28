import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, children closed at the parent by
-- restriction pools (closeChild of the model), and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37337.Model
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


end PEqualNP.Outside.L_meta_37337.Model

namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Atlas := Nat × List Decor × Sig × (Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → Nat) × (Nat → Nat → Nat) × List BoundPool

def top (g : Atlas) := g.1
def first (g : Atlas) := g.2.1
def target (g : Atlas) := g.2.2.1
def count (g : Atlas) := g.2.2.2.1
def record (g : Atlas) := g.2.2.2.2.1
def tip (g : Atlas) := g.2.2.2.2.2.1
def locate (g : Atlas) := g.2.2.2.2.2.2.1
def apools (g : Atlas) := g.2.2.2.2.2.2.2
def items (g : Atlas) (k i : Nat) : List Decor :=
  let d := top g-k
  let v := record g k i
  selectLive (v >>> (10*d)) (decodeBank d v (first g))
def vals (g : Atlas) (k i : Nat) := (items g k i).map Prod.fst
def roots (g : Atlas) := (first g).map Prod.fst

def SBf (j : Nat) : Nat := [6, 5, 7, 7, 5, 9].getD j 0

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
      testAll (k,ws.length,ws,preCov true ws,apools g,links g (k-1)) ws)

def Ready (g : Atlas) (r s : Fin 152 → Row) :=
  properPairs (target g) r s ∧ (∀ p ∈ apools g, ValidPool true (roots g) (target g) p) ∧
    (∀ a ∈ first g, faithful r s a) ∧
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
        exact decode_faithful _ _ _ _ _ ready.2.2.1 _ ((selectLive_sub _ _).subset ha)
      · exact ready.2.1
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
      exact poolCut_sound (ready.2.2.2 k i hi hn) _ he h.1.1 hc

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

end PEqualNP.Outside.L_meta_37337

namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x70b00001031dc30be43bf42fb30bd42bf41bc40de30bc43d830bd41be40f830
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8004003801e650430cda08613551d0ab4a11866d0830cc2a0619b540c3328418669003096a968398430c33486186610030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x100a2588540c29161d0830a4584540c28962d0430
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s0K4 (208+(h % 11)*4) 4) % 13)
  | 3 => 2*((h/11+packedAt s0K3 (351+(h % 11)*4) 4) % 13)
  | 2 => 2*((h/8+packedAt s0K2 (152+(h % 8)*2) 2) % 4)
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
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000fcccf000fcc0f000, s0N, s0R, (fun _ _ => 0), s0I, []⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x9d43
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
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 2 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 2 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0, s1N, s1R, (fun _ _ => 0), s1I, []⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x101a20300600100440500811a0800c2001341011001fc32fd43fd40fc30fe31fc40fe20fd30ed20fe41fc41ff30ee42fd31ef20fe30ff10fd20fc42ff40ec21fc21ff41ef32fd21fc10fc31fd32ff31fe32fe40ff32fe42fc20fe10fc43ff43ee21ff20ec32ed42fd10fe43ff42fd41ff21fd42fe21
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x165e0400074400004008004f87c29842c09704c9c01543814013c481c4c0c1c0028006004101c000c11240ca80000344c006802d8a7905b94432b728e655e531027ca810db94642ba28a616d52d06dca610cf15110b7296872d540875aa8195d547439eaa0616e52042d8a2a15b54a30bba8a616c524c6dca5a0db551209f2a663ad421027aa8087394c329f2a0616d52103cca210db94720b6a90873f544c2dca518db94e21bb28e876e520c2daa0195d94430d6a12836d52106d8a2905b14d42b6aa6416f52442daa9215bd5320b7aa0432d540cadca420dbd4931b7aa4436d528c67aa8195b14e21b6a96876f524c2dea5885b54a10b7a92836d54ccadca310dd944409f2a021ad42902d8a4885b94b40b7294216f540cb5ca8197ad4120b6a80436e52082eaa2205bd5120b6a94416e5210edca6195b14943b6a8443d5310c6d8a4a0d794c10d7aa2856d52042daa5205b54242d6a1a856e510867ea8884f95032aea9e836e52cc6daa810cf95320af29e836d50cca7aa998db948429eaa4636e53c82dca7215b94d20b6aa0656c524c2dca5185714d10b729081ad42d06dca5196b95320d6aa641ae54086baa62057d4d10d6aa043af4350a7ca918dbd4142b6296216d520c2daa910cf15130b6298436f54ccadea4a1db94a40b6a96632d54c827aa9904f55021baa88616d52d02d8a6905754c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x130025302a05840190000800a08bd9150ccb0c5350d428b59052c42696014c218b590534822d64947328b592520822f64542219998754cca2d6494e218b596540cb0d5350b418b592528c22d6414f208b590514832542544409398f548864c6355120a9185425062d6494a108b59053086a561d0d428b59654086646155120c354d421022d6414931
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s2K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/51+packedAt s2K4 (3618+(h % 51)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s2K3 (988+(h % 22)*5) 5) % 26)
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
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888eeeeaaaaeeaa8888, s2N, s2R, (fun _ _ => 0), s2I, []⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x11600702a0051021c0100b0000b1d8fc32fd42fe41fe43fd43fc43fe20fc10fd41ff30fc40fc30ff40fc20ff32ff20fc42ee42ff21fd40fd30fd10fe21fd32ff41ff42fc41fc31fe40fc21fe10fe31bd42fd31fe30ad42ff43fd21fe32ed42ff10fd20ff31bf42fe42
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x9800795828002008501880480af801505000082800a80000500800d800000808b04000080000000020c0200000000001205003d04000686808304840417051680000100010383080002170107005b548109f2a4657651d0f5ea6a14f550329eaa6416f524c35ea4a15794f219e2a2613d5408678a8886b50b30d6a1683ae5050b5a8590eb50930aea98216d521067aa9196b50b10aea9e435d53082b8a6886b50830d628a856e5210b5a85194f55242b7290616d52cc75a84106b10d42d729a856e52102eaa3194b55242d6a1665ad429075a84a0db548439f2a0216e5210edaa4185d54420d6a16636d52d02eca2186b50931af298216c524c358a0a15b94b31b6aa485ae4350b58a6a16b50842d6a1a85af5050adca5a1cf55030af29841ad428c35e86a15754c40afa9a216d52d06eaa2204f95020af29e833f544c35a84995b149109eaa0213e54086eaa3a1cf95331bb28c65af5150b5ca2a16b50910bb2888177514c2dca4086b50a21b729681ad424835a8420eb50831d6a14413e540cb5a84194f55231d6a9a857651082dca420cf953219eaa6633d54c875a8490eb50821baa8861ad425035a85a05794c40d6a102174514c27ca9904f95231d6a14216f52442daa518db94a31d6a8a856e52d075a85905b54840d6a14813f54442daa5a1eb54142aea9e833d540835a8518f54c4319f2a085ad421035ea8a14f95030
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x400003c00000000000c0058016000016e2800000002021e041080200681040410112202032a040980000001a398c5050a2e6550910c3d4d42442a66194d42a3d8d5050a2f6550a31c394d42c870d5350840c9509510c22d6215130c950b514c30c5350910e1509310c72542145308b195424430d53508108b59252cc68d63945428bd9542cc70d5314d42c9509510822d6550810a99845050aa661d0d428b58a548c68d63d45428b195424c3254254440a95874350aa56194d42a9d855050b0e5350820c95445150aa56114142c394d42d07254294440c394d421030d53508208b588544430e5350810a358c5050a2d6550a31c9509518cb2542946328bd95420c2a461541428b592528c62d65508308bd95420422d6295030c354d42d062e6550930c950a510822d62953318b592520428e6394542c950a510c22d64948308b59542cc68e63d45428b58a540428c63541428b589540830d5350b218b590524c2a661d4d428b59052442a561d4d42
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s3K5 (720+(h % 22)*6) 6) % 45)
  | 4 => 2*((h/78+packedAt s3K4 (3483+(h % 78)*8) 8) % 129)
  | 3 => 2*((h/50+packedAt s3K3 (2584+(h % 50)*7) 7) % 68)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffc3fffffff03f07fffff07fffff23f1ff
  | 1 => 0xf83e0ffc1f0f83ffc7f870787f870f0fdd4e93
  | 2 => 0xffc00fffe00ffc3ff8007f807ff80ff0e18f1c
  | 4 => 0xffffff0003fffff80007ffff000fe0fe0
  | 5 => 0xfffff0000000003fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8000040000000000000808800090100001025
  | 1 => 0x128c9488ca152612c348345134822a2e4d4692
  | 2 => 0xa195ad1146aa627558c45d425d504ce2e18b18
  | 4 => 0x85294a22948348a9ad9508046a64e044b60dc0
  | 5 => 0xc6318c3b18cc733e36e66e670c408888fbe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8eeeeaaaaeaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I, []⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb541
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | 3 => packedAt s4K3 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s4K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffff83e0fffff0707ffffff8381ffff0ff27f
  | 1 => 0xfc1ffc00ff87ff807870f83fc01fe1fc94c73
  | 2 => 0xf001fffff0ff83fff807f003fffe1fe0f18f9c
  | 3 => 0x1ffffff0003fffff80003ffffe000fe0fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x41000880101000010088108900882284021225
  | 1 => 0xa2b3910da664e338c3438d12e415545ac94c52
  | 2 => 0x2494a2148284254a4805a420a9241942518498
  | 3 => 0x4b2944a908314a9595d0084b5259808cae0b60
  | 5 => 0x8c318731ccc673e6e666ce7060611110fde000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfaaafaaaf8a8f8a8faaafaaaf8a8f8a8faaafaaaf8a8f8a8faaafaaaf8a8f8a8faaafaaaf8a8f8a8faaafaaaf8a8f8a8faaafaaaf8a8f8a8faaafaaaf8a8f8a8, s4N, s4R, (fun _ _ => 0), s4I, []⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def s5K8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K7 : Nat → Nat
  | 0 => 0x440000020000021c10c00000c0055044057202fe30ff31fd10fd32fc31fd30fd41dd30ff40fc40ff42fc32ff32df30fc21fd20fc20fe21ff30ff20fc43fe32fe42fe40fd21fc10fd42ff43fe10ff10fe43fc30fd43ff21fc41fe41ff41fe31fc42fd40fe20fd31
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x241f7418437a8520f70c831ff29e43fe42502fea7887fd0140ffa0863ff540c7f88410efd0b40ff28a61fd42042fea8185f15232ff196837c53507f882a07fd4041fe98c217d54c43fe80207fd0c32fe2a4437d50c87fea7907f54031bfa9821fe42883fea2187fd0220fe29487fd42087fa40887f0ca30ee10e617d5090fbaa7105f94c32fba0c83fd21903fa64887f8c621ffa1a83fb20883ea20087fcc020ff28e657d5210efca0197fc8020fea8463ff42cc3bc63985f95230ff28a65ff42c83fe43987f10210bea9c21ff21c83fa83187fd4b30bea9c617d50d0ffaa5085f14d20ff21a65ff5050b7aa8197fd4241fe21c437e5210ffc8298ff10c31ff08221ff324c2fea9986f90942ffa8e81fe328c7bea4987f94331ffaa221fc528c77a8420ff4c920ff20881fe434c6fca820df94440bf28e417c53c837a85a07e44010ff98e61fe21042fca7907b90920ff294617c514cbfca1217fd0530fe29483f551083b887987f48210fe21641fc42cc3faa6a0ff90510ffa9663ff31c83fc862077cc010feaa461df320caf8a9187fccb41ff29421fc43d0bf887197f88421ef29c21ff53842faa690ff90030fe18821ff508c7fa65085f14530fe28083fc514c3ba82987f50b30fea16417c54483fc64087f94e42ffa86637d52d03ba42987f90520fe28465fd5250ff8a118ff14e42fe188437c54887fc8498ff50e40bb28c85fe5310bfc86217794c40be29621fd438cbfea2197f90d10ff19043f541c43fca4a07fd4c21ffa9421fe52c42fca218ff8c530fe20a63fe510cbfaa1a0ff4ca41ffa02417f54083fe86a1ff54620ffa1a43fd218c27ea8887f50832bea9883fa10043faa420ffcca31fe21a61fd504c6f8a998ffd4c10ff28c65ff53486f8a090ff90d20bea8c85fc504cbbaa5985f54430ff20c21dc328c7fc84207f15220ff28083fe424cafaa018ff14740ffa0221fe42443f864107f10440bf28487ff53d03fe84197f94d41ff212417c548c7fe8318ffd4a43ff206217e50843f882887f90140fe196437e5390ffc43987d54642bea9885fe21c83fe86187f90e10ff180617f53083fea890ffcc821fea8a87fc43ccbfa60087f50420ef29661fe40882fca7217fcc810ef98641ff42507fca898fec8120fe10a61fd41c87f8a32177d4730ff29e21ff314c7f882907f0c730ff196617d520c3f863905f94f42dfa0c837c5050ffa87187f54742fe99681fc43d07faa3187d10410f719065dc430cbfc65907f14141bf2a643fc420cbfa6420df54f40fe196637e518cbbe8721ff54843fe98863dc524c3fc85087fd0410fe280637e540cafca5a0fd48710ff21c837f5050bfa8398ffd0210ffa8263fc41843fa63207f15320dfa1e85bf41d03fea2107f94241fe212837f548c3fe8210df94331ffa9c43ff53907fa81187f14321
  | 1 => 0xe53902fca8085fd5130ff21065ff54c83fa8418ff90d41bf28643dc42cc2faa89977d0530bea96637f5150bfc60085f94432ff98863dd42cc3fc81907f95330fa90843fd43103f88418ff14743ee21c65fd50c87fe8621ffd4e40ff20661fe32cc7fe84985fd5331fe21465fe5110fea6218ef10640fea9481fe524c3ec42887f50d10ff20861fd428cbfa43085f14543bf29043fd320c3fa62a07f50740ffa1665fc30483f8a010ffd5310ff282437e50883bc43987f54740ffa1843ff53483fa86997f14a30ff90a617d50106fca8217e4c220ffa8085ff52507f843187fd4a41bfa9287fd53103faa8087f48310fe29087ed52103faa610f78c530bf298637e54482fca418efd0e43fe2a2217d5190ffa85997f50040fe18421fc42d07fea3907f50e10fe90e81fc42ccafca6907f0c621bf2a663df53487ee20085fd5031fe20621fc54c43fa80885f94732fe21261fd544c3fea199770c730ff882217c54083fe82107fd4c42ffaa461fc504c7faa8907f94c21bf28841fc40883fe8390fbc8421ff21243fe5190afaa7107f90d21fe28c817e5290bb886987f8ca21ff98a61fe20443fa84987f50120bea9841ff308c3ba60087f55110ff99663fe30c83f886217fd4141fe280877d544c3fa65885f94c20fe28065ef328cafaa9217f55321fe29a43fe5010ff883107f90c30efa1a87fe52907fa65107f50b41fea1c83fc51d0bfca9907708530ffaa241fd32503fc40907f14910ef19661fc52043fa81085f54910bf2a263ff43cc3fc62106fd0a41beaa463ff41cc7fe87907f95110ff190633c54443fca8087fd0a31ee19261fe20843fc6390ff10521ffa0061ff42043fa87217f14f10ff884217e52d03f8a3197f14830beaa6437d54083fca098f7d4130fe2a465fe4350efca321ffd4532ff29283fd32103de43907fd5020bea8c81fd5290ffca4185f94f40fea9621fe52d0ff840087fd4620fe28881ff50886eaa2197bc8020ff21061fc410c3f8a6a07fd4a40ff28a87fc43083fa628877ccb30fe21e43fd51d0efca8187d94440ff20a81fe41c43faa4205f94421fe10841ff53083f865205f94743ff28c81ff318c7fe4210ffc8410fe21463bf41503fa8518df94042ff29287fe214c2bca7107f90620fe98881ff51d0afca318ffcca21fea1e815e530c3fea8197f54032ffa10437f53883fa62907f50640fea18837e51887ba61907fcc831bf286657c54c83fca7a17f15130fe18a617d508c7e88310ff10710ffa8c817f53087fc87885f94832ffa9e837e544cbf260907fd0310ff28665bf42107fc64987714b30ff21c41fd548c7fe8310ff10f31ff99465fe54c86faa7217f90b10ff98821fc40443f886a17f54a30fe21021fd5310bbea99877d0730ff29263ff31086f8a8987fd5131f6a1641bf4290bfc6218ff15032fe20
  | 2 => 0x83f8a898df94343fea86853e540cbfea421ff50b31faa8881ff520c3faa3217f90720ff21843dc424c3be62985794c20bea8c41fe54842faa720df94b10ff29021fd540c7f4a0197f10f40be2a0637e548c7fca190fb54810bfa8283df308c3fea3a1df54241fe21c85fe328c3fe41087fcc210fe20821ff42cc6baa7105fd5321ffa1041dd544c3fc840877d0f30fea9841ff40043fa86187750930ffa1c43fc51483f8a790df54b43fe90e21fc5090bf861885fd5320fd10041fd218837ca8107795330ff10c61de320c7fe8590ff54b31fe20843fe42086f8a9107fc8420ffa9a85fd21502f8a2a17dd0541be29a21fd54487fe8618ff0c931ff99481fe41cc2fca221fe8c120bf280817d5090bfea998ff4c740ff2a6637e52443f863187f90130fe2a6617d53087fea5a1dfd4520fea0a21fd41483fe6390fbc8621fe29c41fc52502faa0197f94520ff988417e53c42faa1a1764c120bea9683ff420c6fca7087f54f40fe19081fd5350bf88598ff94420ff298417c54c87fa82207f90f30ff29087fc54083fea5187f0c910ffa0c81fc42083fe84217f90f20ee18a61fc438c3fe85197f94031fea9483df318c7f8a221df94840fe21643fc41c83f861107f94442fea1e21fd53c82faa7207f50820dea1a857d54842fca521ef50f42fe29683ff4250bbca2986fd0240fea8865ff53442fea8197f50b21fea9021fc32483f8a3185f54a31fb10e21fd52d07faa4a05f14d42f690a41fc52d0ffa87107f54c10fe29287fe42cc3fc85907ed0240ffa06617e5410ffca918fb88120ffa0641fc50907fa64197f10730ef19261fe319037a8621df95320ff18261ff434c3be65195f95220ff28a81f741486fca0187fcca30ef90e617f544cbfe87997f95230bf28885fc32843faa8105fd4910ffa1683dc544c3fc6590ff4c941beaa063fd4210af8a2a05f14142fea14437d51082fea09977d0c32fea06217d540437e84a07fd4540bea9a417d51103fca9887f54343aea9c213d540cbfc41885f15032beaa2637f53487fa83087f4c521bf29663fd51503fa81107fd0f41bfaa2437751502fca6207f88420fea1a41ff418c3f86520ffd0a21fe980417e500c7ea6310ffd5130ffaa421be41903f8a1a1ff4c430ffa8465ff21887fa422077cc020be28283fd32487f8a91877d0b30ff20021fd21443fc86195754e30fb18a43f9300c3fea4a077d4b30fe29481fc31083fc84a0ff14a10fe20061ff50d0bfaa910fe48020ff190417e508cbf86390ff54930bfa9a85ff438c7f843207fd4f42bfa9e417c540c3be64986d50441fea9463fd540c3bc6518ff4c710ee28a617e5010ffa63107f94620ff99643fe41487fca418ff0c110dea1281fe5010bf88510cf95020be29021ff31887fe86087f8c630beaa443ff32083be63985fd4143fe90a417
  | 3 => 0xa6a0ffd0440bf28443fc53482fca810ff4c120ffa98817f54087fe64907f14432ff992657f53c86bca7085fd4a10ffa8a616e52042fca620f790f30fe29841fd324c3fca6087fcc310fe21a655d53902faa7a0ff94e40ee20e61fe42887fc8618ff8c531ef298415c5350bec8220ff8c440fea8e61ff42903fea990ff4c210ff19083fc54042f8a7887f15120bf28021fc50cc7fe829057d4d21fea9c217f544437ca8195f15021ef21661ff32843fca7a07fd4a31be29a81f441843fc65a07754c10beaa061fd40cc3fe41887f14532fba08217d52c43be81987fd4b40fe99683dd320cbf460187b4c832ff98441fe53883bc60987f0c740ff21063ff548cbfc628877d0d30ff20041fd53d0bf88218ff10d31fe28685fc32487fc85197f4c410fe21c837e518c3fe43207f90530ff28861ff418437ea8885f15330bf28483ff41907fe6520ff94343fe21a417d5010ffaa7215f94c21ff20a83ff50c86faa418ff90d30fe21881fd41486fca3a17fd0a30fea9883fd31087fc62905f14132df20881fd41107fa8698ffd4d40fe29681fc32107f8a990ff90f32fe20021fc32d03b8a690fdc8521fe108817e54103fa6518ff10d10fe28a85fc320c2bca6207fd0c20bf2a661fd10043f881984f55321fe288617e52043fe63207f10a40fe29c83ff404c2fca5205f94842af29c817f548c7f842887f14142afa9a857d53c83f8a9997f8c610b6a9021fd430cbf660987754930fea0861fd53c43fe8790df94830ffa9621fa30883faa2987f10631fa28a81fd42903f887087f48010ffa84877f548cbfea2215f14d21bf28c837e54ccafaa4087fd0f42ff21261df544c3fa64087f90f41ff18041fc21482fea4a0fb94810fe99263fe42ccbf882987f14643fea8e65fe54ccbfa8298ffc8630ffaa043fe418c6faa3997fd4c41ff08021de214c3f887207dcc531fea9e83fe54087faa2105f94e41dfa0081fd32086fca1a17fd4841fe98e61fd43503fe8798ffd4931fe2a063fc32503f865887f54640ef98863fd31c83fc85a0ef90140ff98241fd54883f843a07f14d42fea0061ff41d03dc859077d0930ff28e87fc32883fe8220f790330ec98441fc21843fe86217794930fe2a043fd41503fca3987f90e31be29c21ff318c3baa6207f90410ff98221ff51103fa83887f10a30bea9a21fc40c83faa4a0ff88640ffa1a85fc52cc7f8a6217fd4043ffaa463dd30083fa65987f54b40fe28e61ff20443faa021df94740fea0c41ff50487f88620ff14e40ffa8a87fd428c3f8a90877c8530ff20843ef4250af8a8994f95321fe908617f504c7faa0a0ff0c640ff29a216e52103f8a498ff14620ff18e81fe428c7fa8690df14c20ff21887fc51083fe87197f8ca40feaa6617d53043fca598ffd5220fe99641ff20483fca121ff90c10ff21a815d530
  | 4 => 0xdf14e20fe990637d5490fec83887f50d30ffa9c41f741887fa64107fc85209f2a021ff31103dc84215f54630deaa021f7318c6fca118ffd0540fe21081dc414c3de85217fd4f21bf29885fc50ccafaa1997ec4210ff98a41fe51d03fa6590ff10910ffa0861ff53c43fca6907fc8610fea02617d52106faa8907f8c521efa0261bd41107fa84207f54443bf28821bf4310ffaa198df15110b6a90817d53103f885087f50e31bea8e61fd42443fa87a0ff14c21ff99281bd41d03fa4390774c730ae29a43db504c3faa1995f94021bea9e43fc42483f8a4a0f790930ff29a85fe324c7faa110ff14c10fe28487fd518cbf865987f55320ee20661fc32c83fc82107f4cb31ff19265fd30c43f884997fd0a41ff99621fd42483f2a0197fcca20fe90821bc54443da43905f94020fe20e437c5250ffaa4887f8c430fe21a43fe51d0afaa8887fd4810fe98c437e54c42fca9197fcc610ff992637e54443fea321df94e21fe18021fd424ca7aa8107f10731fe282877d538c6faa710ff50c43bea9e85fe535037aa990ff48421be28263fe43082faa4207d8c621ffa0e21ef324cbfe85217f90f42be29221fc430c2f8a710ff50a10ff28463fe21103fca110f790c43fe29e857f514cbfa86087f90f21be2a665fe31503fe83107f14732ff10a21dc5350bbca3987f90731ff18e21fc5110afca6087f54b43fe18881fe54887fc64887f95032fb08221f6310c7f680a077cc110fea8c87fd53902faa3195f94242bf288837d54cc2baa6087f90f31fe18a21fe32103fea1a0ff90820fe10861fd42906fca3107f48730ff20461ff40083fc42907f14b10fe20841fd520c3fca890ffd0b40bf28083be54043fc8590ffd0841ff90e81df30482eca2207fcc841bd28065fd5090bfaa020ff54532bea8443ff31d02faa0217f4ca21be2a021f621087fe87207f8c620ee99661fc31483fca8907d90510bf28481be4350ffa86a0ff10f10ff19241ff518cbfa62987755330ff21a85ff32103fc43087bc8220bea9441fe32843bc83985fd5310bea86637e51cc3fea018df54432ef98421fe53487f842a07f94342fea0021fe42cc7f88420ff10b40fe21a81fe544cbf863087f90842ff880217f53887faa8197fd0531bf2a261fe51102f8a9887f08710ff28043ff54ccb7ca990ff10130ffa1c61fe50507f887105d54642ff28265f6510cbfca0a1ff90621bea9421fe20043fa85a07fcc910ff21285fc32507fca321ffd4542fea1083df5350bfa60885f54610ff98061fe438cbfe65a05f14f21fe18641fc50486fea4a07f90e21fe2a243df438cbfe82885fd4e10fe10c41fe508cbfc8218ff95130ee2a661de404c3fa81905f95221bfa8a61ff20883faa498f754c20fea9063fd43cc3fca5a05fd5332ff194837d538cafea898ff54720bf29421fd43c83fe
  | 5 => 0xf21fa98a43fd43083fca4887f90640ff29881fd4310afaa890ff8c941fea0863fe53907fa8610df15131ffa9287ed21087fea2905fd4d41fea1243fe40483ee4310dfd5010ffa0481fd50087fca4205d14540bf28c817f52c42faa7885f54a41ff29083ff310c3f8a3907f94f41fea8483fd5110afca2187f14f41ffa9261fd32903fe8698ff8c720fe21061fc31502fea2a1ff90210bf29083f521443fe42a07f54121fe298815e53043fe84207f50830be29283fd414c3f8a418f754e40dea00817d54883fe86887fd0940ffa1621dd4310ffe86205f55230fea1e63fc53506fea4987f08310fea0041fe500cbfe85107f54440ff21461fe540c7fe40085f94a32fe204617d54c83f887907f8c110ff90e21fd548cbfe43107f54143beaa065fd544c7fc40107fcc010fea1a85fc324c3fea910f74c530fe20c617d548cbfea1a1ffcc832bf28461fd508cbfca7085d94432fea9e43fb308c3f8a110ff8c120ee90e61fe32503fc4290df54a30faa08837d54906fea6887fd4910ffa1a41fc21cc2fca518dfd5220ef19265fc21c83fa8498ffd0d32fe21281ff31c43fe64a0ff50b10fe21621ff31503f86290df14c21fea8285fd328c3f865a0efd0842bea8e85ff500cafea9087f8c921feaa0437c52843fe63107fd4242ffa8c61fe43903f88310f710130ffa1c21ff544cbfc43a07b48020f790a417e528c3faa6a07f55210fe21441fc524c3fc42187f95030fea1281fe30842fca621ffd0541ffa8c85fd5150bf480207f50720fb28c857f54482faa3a077cc030bf2a063dd30442faa510ff0c430deaa041fd51483fc64187f54e20fea1441fd52cc3fa8710df95020be29261fc40082faa221f795130ff214817e5190bfa6390ffd5010fea9a41fd54c42faa1197754e10bb28841fe518c3ba87987f0ca31dea1085dc51cc3fa8618ff10640ff29661fd544cbf88520f74c120ff98641fe5290fbea2987794c10fea8265ff21103fc83186f90541ff29c433d54042faa998df14940ffaa061fe548caf8a6087f54243fe98841de53903fca518ff50631fe21865dd324c2fea2a07f54e21ffa12637f52043faa0215f54720ffa1421de314c7fa42987e50040beaa665fe41c87fc42a07f88710fe10421fd41cc3fe8721ffd0910ff99243bc41103fea3987ec4110ee98421fc32043da84907fd4132eea8e617f50487fc43107f55332ef98621ff21443fc87187790530ef98441dd40cc2faa9207f14840ffa1265fc20443f8a710fd10521ffa1883f710843faa2187f0c710fe21a83de53882faa2217f0c821ff19621ff4390bfa82087fd0521ef21a617d5290fbaa2985fd4d20ffa1241ff31443fea418ff10931fe980617e52907fc65107f0c620ffa8887fd43ccbfe64187f4c220ffa1e81fe52903da84217fd0230fea0843fd20083faa690
  | 6 => 0x80b0020140200e02c0102502306a0280880000a0a00095301e0881882823000006000004000010320160a0000010022b40b08c04e0040400f2e40902500201e0340080212e004260010820100680203c040010b91a808c01ce600205801000002154230040044a40280400a00c608450060293600000021c000070d00a0300050121c48000005c0081609f01a0000780000614818805036010048100020041c80109634c2303602606004014006008008010ce00c031410560a00502300001c0082b0ae02c0a01701400d13000070004001e90020040000b192098078063fc058000040dc0ec0700400c020019e400400027000410014e90010580402e8db0040d00582001433c0182b0b036800000006030790220000245c8070004281b88700605400012020158b9811000000040881ba07c08806000024010160080243c80002e00c0801726c030000010082887581c08006000002018014009ea0000300000400c11c00007000024020070001200281f12eb740280c0700b0005080020700e84c3560180295a03a00c0d0000000000700347c0081e80c0000e800838036124110000c2068000060280040023f3ec0a0008010000970104a0009045d0272880b80481400e01c1681c98603cad8d301e018000f800401c0281760a04400002da826c028030062883305c0061540100a074258000040003fc4085137c000058430160081b81400004c0588300815c0980300205000000004020878170069143d003040028000030600007282c00614c0180303c1040d801000034068330080e41580869a0b401002014288020180300500000354fff43c43fca620ff15030fea9a217f524c6fca890ffd0e41ee98061fe41106faa5985f54a40bf29e43ff43503dca4207f48420ff18843dd434c3fc83a07d94420bf29c41fd42507fc62087f8c310bf2a421fe42906faa1a0ff14841fe21c637e53487b865987fccb20fe2a463ff43882f8a890ff14f40fe28085fe54883eaa2197f8c220aea98817e530c3fe8490df94b30ffa804379500cafca4107f95020fe2a6637c54843fea3997f94142ff98261fc51503ea82885f55021bf28683fe43d03f8a8997fd4b41fe986417d51d0ffe65987fc8521dfa0883bd41503fa63187f0c831ff29683fe4390bfea9987fd4143fe218217551103f8a5987fd0720fe298837551083fc8620df94d10fea1e85fd53907fe84187f0ca21dfa1a85fe51c83f88490ffd0730eea0261fe53c83f8a7907f55331f710a43fc53843ba61885fd5221fe180417d50087fca2a17f8c832fe286837f53503fc85a07fd4840ff200817c51483fe6290ff94341ee98863fc43087fa8310df94f41ff908617e52d0ffc8088774c220be29263fc5150ff842087f14d10ffa9c85fe31cc3fc8420ff10740eea0e61fc43cc3eea2a07f50
  | 7 => 0x360e8490440260a4028760000900002a000164008000001880500001c0015a0090100500107800404c008e8944124000280aa0080283f0000680400500602c6200b0280603e003012098138120043c864801048048018680020100082c00a0040001606c0ac1f02f40a0d40d02601e0580400013000c0704d0081108b81c0000180b80b004030010100040140f8050840200904944a004028e20020045981d4840081b81b00406000800000000000000000000000d000058009d10680040104e0000480302000802011053000004230000240a80080100201c4200c16403c188a20300143808f0080200f8020180340981000a0100e80c0340080100d04c3e402000002018cc0070080140581600218c0001600406c0580d12a0141c8510540300e80400002c0f0f514200c0000002e0f4000000020040100004c0040b0030061dc0481208e0407900000a00c11
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x328427f65c8640bd584204435d53880109f99054042f66110d109f18d54083555354440f358e20483ba5490040e750f42cc36d6215221dd4ca510833c1055010f514f414873e54104109758c50487cf2108530bbd89314873d6590440dbd5120082de6390431bd584208435f53cc510cf951420c3d9434c220db98d520427f6154032d794c32d067e6015030f610d304833f6455032f658052cc39e5450c43cf55242c839f4110530a7d91514c35f538c941b798c304833d544c0109fd95428c75a534c030b7d8d42cc6de6410530b798e404433e63151109f59631c827d65906209f99721442b664c8521b7583430ca7d6194e40b7191524c3755108420bd5864210abd640c821af992514cb6d4394840b718d21c827e6294231bd984328839e6414930cf98e54c86fa60d0c40b798e408433c54501209f9845350bd941d41309f98e520833c54d0210d799253843d553d0410dd587528433c5410d10dd14431502de6408530dd18e51083ad4210921cf55343c835e63940418f99053c877661d5021f64c0304827e63150218f99053c827d6215131de58353c42f560d0610ded91500ca7d6295230d754c53d0add65509309f18d519039e42509309f98a538433e54d0c329f1855390b5e53d0440b758443cc35d650ca31d794d20083795014043bb58a31c833554d0410cf988544427c6055232db58e520427f6254241be983438c35e3214532fc18121443cf624c320d754c535073f6395020af99050487db6050d309f59443486da6008530af58b415035c53c8521d5584534876f52c8110d715252cc27e6510d20b798b434c3cf6348421b7591214c37561d5232e7d0d424c27f6354720cf95241106df6250d309f58252907d8544c120af99051083e452485109f98354cc6ec624c1209f597400833c540c110d794c219027d6590b30cfd53420867e60d5321b7995404c33c5450a319f980530834d524c010d755343cc2ee6210421dd951414433c6355010cf553300836d5250040fa949401033d54900109fd94210435e534c7219f98e54c436e6094810b758c420cb5d53d0a40b718554cc27f65908219f18d5010aee6214630af99321c42de65d0530be58321c83756194910dd547411033d5410b21dd58652d067a60d5032af59351cc3d72148530d754e511033c54109309f592510833f54d0b10cf99054c42ed6210f21d7d4e53d067c65508319f990530827f6154a30be58053c867d6115230cf552210436f524c930dd984548c75d5390410b7185524c35e5310830cf55143c827d6214143bb98a300827d6494821f698e401033d5490521d758c548437532145409f997424cb5e6294c40d794d21843e63148520f694b504c23c6454d10b7992314c33e5490631b758c414c2be6414031e790440cc2de60901309fd8154c875e6314f20
  | 1 => 0x75e6194e20f9106214867c63548409bd95210876e4354840d7d8d53042f7614ca219fd95314827e6294440dd54451d0afa60d0920cfd52314433c6295010de540504ca7d6414a108f191534833d54908209f59740042df644c9309f592528435c5394121b7185404c3766294440b7d8d54c83d860cc930dd947300833c54d02209f595310827f65cc841db98552102f46155120af590328c75d5310c419f58f524427d62d4540b7d95404c35e530c920cd185540427f6548730ded425090efa608c63097596530435e5455130b798a4310f5e5388410d7d95300833d6355321cf951420cb3c54d0931af98342d035e538c640d754d41043d66190b30cf553430835d53cca20bb58b530433e5410f219fd895110e7d6015332af992528c67e65d0a31db949400437453d45409f59543842de65509309f594310879f5495130be982425037451105309f9875350a7f6590a10bd98754c827f654c841cf953428c2de6390730e7906404c27e61d4d209f58653487db434c220e7d0f42cc27d6295210d7553304427e63d45409f59642cc77752c4010d7585539027d65d0c30bd181214427d6548640ddd4c515035c6354b10f394f200835c52cc110dd94921c435d538c421af994544435e6494e20fac85304833e64153309f98e50d06f56290710f588730c427c6354041ee191100427e65cca40af993210c2be64d4c20b718941cc39f4290b30d78cb504cb5f6114d21cf553100437760944329f997430427e62d51309fd97438873f5484110f6d01404c3b941d01409f18d544433d6295010cfd50214427f6550c30cf95042042dd6288530dd94e51083da424c2209f98a51902dc6550930bd984325067d6550b31cf153428c75e530ca20dd546310835d63d4a10bd586424827e61d51329f195428c7b45490510db58a54486dd6215130ddd0b515035d518c730bd98a31886ee6214c40db54a42843f13144010dd10650886f5618c841bdd85324c76c51c8520dd545211027f65d0b30a799351cc37a4254032bed81424836d52d0b419f59250c872d52d0040edd5341486fa60c8720d714f324837463d4540d754a32cc35e534c4109f592528c67e65cc510be583318836c6254d10cf55143083776154d20dbd4a528427e65cc910d7185530827c6055132de58053c873e5490832e750d424c27f6255030d794d211027f6510d209f58e54886f46150330dbd4b214436f6255121db59642c827d6194b409f98652d02dd6315210ddd95310c76c5454810d7d53434c376510c420dbd0e52102bd640c910d794d52102ed62cc7219f594329037943540329f58251cca7e6508440d718d540ca7d6014931d7d95214c27c6054d21d7949300427f6254f109f588544427e654c5409f59743442dc6350b40af590508cb3e5450b30bed8121d02bd64c8520af59
  | 2 => 0x61d5232d794e320cabd60d0f42cf18e54c87775454432f614d304827f6590820be58243cc39d54cc010dbc85500867d62951309f195321036f6454810db58b538827e64d4d10bb99642483746294642de98354cc75d63152209f994310867d6015331bbd9521c83766194b10b719742cc3d553c42109f593514c2f46154d40cf55054c43b454505109758c54083e73148421cf950420835f64d4d219fd9152cc6be64d4810bd584320867e61953329f99632486de65d0930b7997214c2df6350820f518d510ca7f6054643a799052cc27e6214d40cf55030042be64d4032af993510cb7a6014e20af997425035e5354a109f994414867f65d0c10dd50e51083b742106219f58a53102be6410940cf15243482dd6290f30d758e50d0b6f6354810cf59353043766194e21be181438c27d61d4f209758e500867d6510d10ddd4e511027f6510030db54b400435e60d4d42d754e329035d51cc220db54b21103d952d4130f6509308836e520cb30bd587430873d5410c30bbd92204823d65904409f195310833c54d0821d794d43906dd63081109f9865210f9f4190730af991215027e6590c219f596428c7f221c41108f593530427f65d06309f197414833f6550740d754c53d075c53145429f997314c27d6294d209f98054043f13044010eb50d42c82f7614c810d794d30043794254032f6982314c2dd6590b30db94b428c75e63942219718d54c833f6455321b798032cc27e65d0d42db549428433d54d0a30dd58753c87774314540f318d210867d6494e20b758c208427c6154e209f990540835c52cc310dd90851502f6618cb21af590524c27f6154c10cfd8154c873e5410420e7d8d43d0b5d5314810dbd4a5250edf6350b329f19442442f661d5020cf553428435d6154e109f18d511027d60d49439fd81518ca6c6255130cf553520437553544209f98253086f96010d20d754c511033c52d0940be98031cc3db424c120be580218c33d53d0842db94821c42fa60d5032d794f30c82dd6510930f6582424c2dd62d0130b758a514c2f4648c621dd94731103d960085309f58f52c427d6594810afd85429067e61d5230af59221d03ad5250a41d7d875350add63880209f9885050e7d6590c20cf951200436d52508309f59251cc3d730c40109fd954310f9e544c020dd98652106ef6250521be580210827e6588630bb988314833d6494d10ed58542106bd6290140cf153424435f5194730b798043cc35d53084209f58c505067e6194f42d754852cc3f360485109f191520c36f6254d10b798754cc36d52908309f195404427e6414d219fd9432902de64cc730af990528c27f60546429f18553d0b3e5410e21e550441cc3e65210410d794e400439e40503309798e501076d5214b319fd8d544c76c5248210f3cc320082f4624c621ed0c9411
  | 3 => 0x410d798f540427d6115020cf55140c837632d45409f19643482de64cc832d754930842df63508409fd9543087b954440109f99432482be6414a10bb58a5150edf6548730dd586544cafa600ca318f990530875c6254c109f594400435f5394d20d754c418437543145409fd95320427e65d0d309f189539067c65909109f5953290775514c4209f19421502dc614cb30bb988500c6be640c940ee55210043775410410b7988404c2ee65c8520b7d85310c76d54948109f596430ca7e6510720bd982411067e61d5332d794d519033c6454d20d718f504875c544c310bd984530827e6550520b758732cc27f6510d109f983540c37751cc520d7549300c37b5094041b7d9543cc2f76154142db54a511039f54cc110ebd8942d035d6194e10e795054cc3b74254642b598432cc36e52c8010b798c414c27d64947329f99730482ed62d4f41bd984510ca7c65cc910e7d91434c35c538c910be98032842bc644cb41dd50851503d76348421cf95120082de6394542b759743cc27e62d4131ebd9142c827c6354720d754f40102ee62d0f20cf953428877661d5310b6583214c36f52909409fd9743087d832cc1308f59050486de62d4530bd586434866e62152109f980548ca7f6590b30cf95342c86ed6214640dd9465090a7e6494010d7d8d53c82fa600c910cf55053043345484110ed953100433d5490f319f597420829f6454930d794e521027e61d53209f582510cabd6494931bbd8943c87b54150110d718353486de63141219f59432506fa6090b20be5805110f7561153319f189518c27d65c8640dd54431cc2f561d0e319f19521cc27e65cc920bd586544cbd6328c431db941200837b5494032d7547308c36f52509409fd9540102df65d0b30dd94a214435f5294b30e795142cc27c6548540d755054cc2df6348740d754e529035c5494e10eb952320cb6e4394810b7584424c33e5450330af990508867c6454c10bb58840c83774394420dd90a510827f6454c10fa58a30882dd6210e329758c540437561d53219f58e50107da608c930d7945300835c5450d309fd8953d075e54cc0109f996428c3f25144010db94a420c33d5450820f9d8521c82bf644c941bd584324435f5354142af990508c7745494432d754c408835d6315231cfd8654c87e531485209f583540c7db6054530bd584328426d6215031be980320867d6510c109fd9642c42fa6010d10dd583515035e53c40109f58e50d06f661909409fd9540482ed62140419d584524c3765254440b798c509076e52508409f59731c82ed6448720fc946100427d6315110ebd0d42c83b854c4110af59051082f561d0d109f58e5010afa6010e10edd0841042f8604c630be58031cc33c5494910b798c530435d538c220e7d0b404c35f538ca21cf55043042f560c8521cfd5254cca7d
  | 4 => 0x7d8d538873f62151109f993538827e6510920b7d8c21cc35f6214d42db94a328c6dd65cca329f594434833d5350a41af59032887e96090b20bdd9141106f66110020d715130842dc6350a41bd98642c827d6590a30be582310427e6294743d7d5330c827c6014910d7d46314c26f65480209f595420433d4254241ce551500caed62d03209e98054086f960ccb30e7d0940cc33d51d0240d394d521035c5394542bd58642cc7ae54c8020b798e404c27d6550120f54ca510cbe73248421d794e318433e5490f30f394832cc3d9404c220fc546401025e63d5010cf55041087cc6350920dd15121442f86050a20d714e5050b775388510cf189540833e5490c30b758c50c87cf2188530b7d8d428c2de6010730dd54421102df62501309f982540ca7d650c520d794c41882ee6290520ddd4b41506dd61d0b30af99031d02f560d0410be580325027c6550921d794c430433d61d51109b588505075d538c420d7d5254cc27c650ca109f19643c82bd640ca409f582518cb5e6254c40d7d46514c3ba41900409f98e510827c6590e109f986540835e53d4440dd54741d03d76150130d714f32c82f66194b40d798f54cc3756494432cd505501067c6054443cf553420427e60d4d42db58d52043775410621bd58652d02dc6550530dd546400833f5495030bdd8d310c73d54cc721dd50a510827e6508110ed50a41c439d64d4730d794c300427f6254730db949401035d5310a10f698b504c33e64d4810ed50841487655254440f948520c43d7538c521b798e10442f4644c521bd98753d0b6e5250830cf15353443755188420d794f310c2756194b43d754b300427e6294010f318d4210b796095110eb94b42d027f6255110dd55341842df6510530bb98850d0f5e63d5020bdd9521c427d6014e21db949218c35e63141419f195424cb5e53cc4209fd815290f5e6054c40cfd53428cb3c5490610d798e50043ac52509409f590534435d528ca31d7d8d548cb7b5094343cf94b42d033c6454d10b658351cc3f260907109f996438427f65d0810e7509404c2f66110e21f3d4e21486dd6010730d798e501027f6254c209758e5090bf06150040b7d8d41cc3773294440d7d4d31c42dd6390832d7153504c39e5415130cf95350c875e53886409fd9150cc67e60d53329f19153086766114c21b6983214c2ee62106219bd89544c35e63d5032b7d85424c35e5494c209f58c520433d54d0830ddd4e5190b6e5248420fa8c9500cb756394420af181411073e65d0540d754c320427e650c530be982324c2df64c8730bd987424437561152109f593504caf560d06219f592510c27c6590931d794c21842ed65c8220dd54d21c43d763485109fd95424c67f658c4219f596438427e6194f20b759251cc2ed62d50109f195438835e53d4810d7945308836e52c8
  | 5 => 0x304827e658ca41bd592411067d6094e41b798e204835e6154c20d694d30882bc6050940e7d0a414c27d6510520d7949300c27c65d0c10e795253042df6050930dd546311035e53cc820d754530c82d960951309f59642c42dc65d07309fd8d50887d8604c530cfd0a5110ade618cb30d794c431067d6510a10af59032c433e54cc410d794e311027f65504319f18d548437b5094221f694d30882f66114440cf95232c87d6610cb30e7d914310f5d530cb20bdd85525027e650cb41dd50051503766590510be58221882de60d09309f594210427d65d0810cf951520427d6215331dd947310c2f56108310b758e304427d65950219f59643086dc65501309fd8553d0ad9600ca319f98e51d02f56108010edd4541503d553440109f18954042f76150d21ed944411035f6254c40dd987530427d63d5121eb951320cbb75450710afd9110043bb43500409f18d5110b7560946429f596438875e504c0109f18054442f9608c710be181544876c528c931d795330842f561d5020d794f521027e6510c219f98a5110fda5344010f554431cc3b554944209e583540ca7c6054742ddd53418433c5490620d7d4e53d0adc6548730de18e500cb6f54548109f988504c7da5384010b798c404427d65d0c20dd14851503776354420b7588514c2df640c930b798e40c427c654c740d7587534867d61d5030bb189430835e654c110f3cc2204827c6155020b718d428833e5490c329f980534439f5350d42f6101300432d5290440d7d4d43506dd64c8730bd984408c2be60d0a41cd551100433d54500209f18d5090bb76150740ddd495110375514c0209f58a53486f561102109f58e52906de6310210be582314c35e6314c10d7153308c33e5250841dd945418c36e6094840e795140cc27f62542439f58a538427e65cc420ebd89429075e650c530c7951530435d534c420cfd52214433e54900409f196430875f6550f30d754b308c27d654c740f9545200835e534c640d7948514c35d530c640cd55151082de6514930cf550420875e54cc1209f992520c2ef6150b20dd151210879d5350040d7d954310f9f6454930cf151424876d5394810f698031cc35e6294e40dd5475090ade63d08319f99253442dc6348740de597308c33d5414432d754d20843d951d4130d794c428827e65149109fd97329035d65d0f30af590320435d5314c21f5984320c75c6194c109f597420c2ee6215031ee50d40102de63d0932cfd5240442df6510930bd584404427d64d4810b3588404c35f6014d42b7d8d525067c6510e21d794c21102dd608c9329f99631c83d9600c730f5147414c37b43540329f596400c3da324c1209f983548ca7f6550440cf15141c435c6254e10f6900404c2dd61d4130b798e400439f64545309fd815310add608c831af587421073f544c510d
  | 6 => 0x33c544c910e795243cc3b95454032d7151308833f5350940bd58e310c7755294440be980328865e6314810cf985540cb5d54cc1209fd9743c867f6510a31db54b218427f6550f10be983320c27e6508520b7d91514c35e54cc0209f99532503d841d41309f58e548827c6510c219f18154486dd62d4530f5d4d314875f5390521d7945310c67e65cc921d759440cc35e548ca31bd58642cca7c654c5109f195204427f6154c20db548524427d63145209f99732d067e6294c419f592520cb795348020bd9864250a3c6454910dd54e5190bd930c8220de58054c433d65d0a429f99253c43cd6210c32c7551530836e52c8440dd90e5190ade63c8530bd98642c873d5490c20f598431cc27e6414f209f59431c82df6254730b9586424827e6414f21cf55241887755114632d7d9053486dc6050730bd98740c4379528c0309fd9731082f9600cb209fd9643843e552d0410bd58432886be64d4c10bdd8553482f66115020dd94540082dd6210f30bd58754cc27e65c8740d754d300836d52c8430b758c200439f4350a329f984548ca7e64d4530d7548320c67e6414132f590441cc37651906309f987535027e62d5230af592524427e62d4f10dd55341043776054642bb98840c827f654cb40dd586534427e6015221cf55332c873d53d0a42b758c529039f53d0d429f9962110377510c540d3949300427c6354742cd152214435d5314840bd18121c42f661d4c209f185544c27e65cca41ab593214827e61d50219f59742cc2dc65c85309f196214c3da434c220ce952500ca7d658c520d794b308427c6510931eb50940c827e6015132b798c50886f661cc8319f98e534439e5490c43b7d8d42d06fa600c931d759631cc35d5348620bb588505075c540c831ddd825190b5e53cc830b798c53082f7604c6219f594438873f6395010cfd53104439e5310640af592321075d6254e40d754f328867e60d4c10f3d0a424c27e658ca40a7990524c37a4354032cf152324435d65d0e43f54c621cc37532d4540f914921c435b654c220d794f42042da60909309f5865010bd4538c521ded4250d0bcd21cc320f610130c42f664c85219dd95210875e65cc120f518d214425e6314142db548511027f654c832af590324c2df6388730cfd53424c67d6095132f9d49214427c6454d10d754e21082dc6350941db54a41042be6190440b7d93314c2fa60cc430b758e40cc2de610c530cfd5130443365454432dd195314876c6154840db94a21c436f6354840f6d95308827e6590e20de98d500caf56114c40db90e52102df6590b30b7592214c3db324c030af99032c82dd63085309fd85531035f5394e10fa181424835d5390020f518d21087d96014930d7d4d5150b9f5390942b798f42cc3d964d4130de98354882f66110f10bed8121882de6314a10be58e
  | 7 => 0x4cc110b798f52043765248421be181324835d6395131d794d51882f5610ca409718d54483d46150330b798b318c67f6548540fcd8540102ee62cc1209f997414c2be6410d42cf548411027d62953319f593514836f5354810d7147304835d5350e40be582435036e52944409fd95431027e62d5331d794e32c867f6154042cfd5043442d66190930f5d06414c27f65887309fd81534875e5388610d754c41042f561d0f10b798e50486f9600c5409798f540835e53100309f19150cc73e5250842b7595214c33d5410521ed18941106f46150320b758c51902ed628c220d7d8f504ca6d6594810db54941042bd64c86309f586548837753d4540cf953320427c6054b41db9095010adf63486209fd96430c33e5454032d7d50430ca7d6395210d754451cc27d6494e21cfd8a540435c534c220b5185544c27d6295110be980324c37461550109fd95421074d520c8319f588515036e6214a109f98e50086f56190e10de146500ca7d6588420d794e300c2bf6550841bb58a430cb4d5214b30dd54451d027d6194c42be980320427f65507209f99053c435c3254031b758b31cc2f6610c8419f58454c837561d5331d7997434c37b6055120b758c20c42bd62d0740d798c52042f66114a30cf95331082f661d0a21bd584324c27d65950319f986520c27e6494431d754e411027e6414e219f18553483db634c0309f59731083d842d41309f59643042fa600c54097d95300c33d5410c329f595434835f6254e40d794c400835e534c610d7d4d30842dd628c730dd90c51503d74394432d794f43d0b5f654c832bb58b4310b9f4090330dd54641883d751c8530b7d8d52d02de60d0f30af5924350bd8314c120bbd8940c82be6414c20ed508418435e530c821f5d85544c25e63942219f595410c27f6454f20db949328c67f62546409f594300427e6314542d7d4b304427d65cc620dd10d510836c5494810f954721c837551144329f185528c36d52d0040dd185544835f5394c419fd91528c73d54d4c209f98c52c42be64d46329f992510835d6510e329fd97210c2f5610c8109f1815310bda61d4130cf150314427c6254341cf953510cb6e520cb41af590320c27561d50329f587534835f4354232db148324435e538c020ed504414827e650c440fa4c9500cb3d548c810b7987434c27c61540329f984540caf56190820e7990328c67c6550920f354d200827e65d0620ad19110043d9324c120af593210836e62d52319f98a50906dd63d52219f98c54042f86050510be98032903db214c220b75973084375510c020b798c300827e6415021be181218833d54c8020b7984524c35b654c120b759021cc3795014121f3148214c33e5410421dd5445110a7d6214d409f98b540ca7e6590d30b7d8d42486f86050610be583540caf9600cb21db54a2004
  | 8 => 0x419f99732106dd631043197594430cb3e4194040dd545418833c5450d10ddd09510835d5310c209fd8552cc27f654c020dd94d51102bd64d44209f195414833f54d0a31db94a208435d53946209fd95329067d62d41419f98c525076e52c84309f19532d02dd65d0b30cf55054ccaf6610c920d754d42902dd6008730f514d31486df6548530dd945211033f5450821b7593324c27f65cc620b7994514c27d6154810be58043103bb64440109d584548c35d530cb21eb58b43d0bd76348710e7993214c27d6590440d754f318433f540c1109f593530437753944209f58854c427d62151309f98b540c2f66114a43cf54540102de608c730bd185329075c6294c40db54a429067c6454732b5185524c3d4328c5219f189544c6be64140219f99732042b664c8621d714e41486de640c530d794e320437743d4540cfd5142c43755114732edd5241442df6255330dd947200829e640c930cf992528c76d6215332cf95043ccb6e52d00109fd9151c833c6195032d798f52042de6190b309f98853842f661148409f58354cc75e6394021d754c300836d4254042d794f42903d72188530b758e314c27f65ccb109fd9431d035d5214930bd587540ca7565d04109f595414867f6155010cf950428c67f65d07209f58b53503ad5250040bd5875090b3c5450d31db94b42106ef61484219f185520c3776550710b799351cc35f6194c20b718d420cbe8624c120b798e424c3b45150740cf546419027d62152309f988520427d6510030de54050c86de6384010eb94b421073d54c8420d7591538427d6395120b759232cc37b6054910de98052043b65454432be98032c435f6214d21cf951438c35e6514d219fd9732d027f6550d20d7d4f5150a7f6548430cf95031c87db514c220d7152434c2ee6214231bb588310867f6550b10d754c32d076d5214810bd98742c435d5310810de5405090fac6250d42d794d31103764394420dd94741103555394420af99331103755190630b758f540427f62543419f59721103db604c1209fd94430877b50942418fd91534435d5390a40d70c8514c27f6550d219f196320427d6414d21b7987324c35d534c841ed50540c433d6115110ddd4b41842ef624c320dbd8952842df65d0930bd58642102de61d4930cf98d540ca766590510afd85411067e6394442cf95020042dd6310220af593211035c6054c209f98b548c73e6414930cf98a54c86ed62d0d20f550441cc3d66110330cf95132c875c53cc1109f18151d0f5e6315021b798e400c2ee62d4f41d794d529037543d4540d794e439076c524c931d7952324c35d60d4d219f19153482df61501309fd9153842f5610cb10be58343d027e6094e41db94b320c77a5450040f6580328c75e5390210dd54531103746454432ed58141107786454032bd586428c33c5
  | 9 => 0x98b30482f661140438f59053042de6188530b798c424c67e658c920d794f108427e62d5110d794f410827d6414121db548320437542d4540de58354cc6df6250f30e754f43d0b4d52cc010c755130083b454d0521be980414c25d60d4d21bd98752103555394440f6d0d30482f66190b40bd58440c43db40503309d58652d036d5250a41ddd46515035e6254e40be58b304c27e6315321de10e500ca7d60953329f99250ccaee6210f42dd545418c35d6294e20cf550548c6dd6550130b758e30043d65114530dd546401037751d0520bdd85438435d6510f30be980410427a60150319f195434c7766254420dd10d510cade64147309f58b53c427d65d0f20cf153404827e6394b10b798b43cc37563544409f58252d0e7e6494732cf986540833e54106319f99442cc73d54d0e30f5144214c27d6315321b798f41cc7d9608c930bdd89414436d5214a41cf550310433e54d0840af990540827e64d4c219f5845050e5f6355120b3988404c2de648c7309f185548c3756114e10be980320c3bb54c4110d794f318837b6055121bd587404427d6295120b798c404c3765288710be98341d027c6550e10f6909304839f5455330e750d42cc35f6294c40b718d218837a6014a10dd58454082de63100109fd81540867d6215210cfd8954042f66195132af99121d02df6454930f5d05414c25e6514d21cfd5342442dd640c730cfd52544c2f56484110bd58442c87776544010d6195304833c5490910fc983418427e6314540cf153434427e6494e10dd94e314867e6394a10ee58341d027d64948309f594424c2bd6494b10be58331482de60101309f597428c75c528c531b758c5010b3d544c8109fd95311035e6314e21b7d8d51c839f63509409f993504867f6255330f6153504c3da514c1209719542cc2de61d5130be58041042f565c4210bd584320c3746354420b758c501067c60550329f594410439f5455130cf551438c2de6290f30cfd8d54082f66114e42af191534827f6255230ded42508c67f65501309798c54842dd63d4620b758c41cc27e6394821ee952500cade6190d30be980430c2de6408730e7106404c33e54cc820bd584404c2de6414b30cf950400437950142419f98a53103764154041d798c534427d6315121b7984214c3b662504419f1895110f3d54d0832d394e521025f6550930db152424827e6550930fc545500cadd65cc631bd58440042be64c8730d754d200435e534c2109f595218c27d6294f41ddd955190a7c65cc940dd947210827d6508730cf953438c3d9434c120cf191524433c54d0d31cf54b409027e6395320cf550428cb3c5150540dd147215027661d5330d794e211035e6094e20b758c42cc6fa60d084097195434c33e548c010dd152104435e53900409f195424c35d51cc0309f996428c7b751905
  | 10 => 0x10c35f5394d40b718c214c3746155220db548520c2fa6090c10bd986430c76e528c841cf55054cc6f86050640b718131cc3795454032d714c32887cc5288530db9524210b7463946429f58b548433f54d0d31dbd8e52042dd6390140cf55340c82bd62d0641ed50841886ed6214440af99032d035f53d4142cf551428427d65ccb409f191528c35c5454e209758f548435c538c5209f995434427e65108109f58654ccb9e640c930db14a424c67f6354a40cf15142443756114931b758e50d0a7f65d0430d7d4c324873f5450521af593518cad46150130de14e30882fa6014f21d754e52842dd6510e32b7580424c2df6550530be98241502dd63143429fd89501073d54d0721b758e204427f658c6409f597320433e54100209f58252d07e93088120dd54451d0e7d6114d20cf149425033e61950329f587548c2fb6050d40d7592538436d5248310cf95341cc79d42d0130b7990524c3b54154041b7d81320cbd463487109f987540cadd6388210f394e320cb3d5350842d718d52d03ad64c8421cf95343c867d60d5121be98041c42d661d5330d794b30042fb6055121d794f410c35f5354121e7d935350b3e5490b219f99642487d46154930edd8d411073e548c0209798e53486ee62d0520be181314435e514c010dd946500cbcf2108730ded81534435f6254e20cf950500ca7e6550b10dd589511027f6154a43d794c30842dd60cc631f5146314c27f6550e219f59441082fa6090e40cf151424c75d53d0820d758a530c33f5494910f554f100435c5350521ed50740442f66115030bd583218867d6394720cf55330042f8604c610bdd92104433f5450d31db54a429036d520cb309f58f54883756454642b758841cc27e65cc720d994951102f76150e319f5825390a7e65c8530d7d92530c35d5308620f3d4f4250add6448730d7544514c37751485209f195420c2dd6508730cf55142882bc6250f42d754f41882f4614c941af18543d0b3e5450a30cf95340cc25f63549109f185540ca7c6355220b798c40c427d65d06209f58454cc27e6590120edd50418427e65151329f997435067f6454a309f597428c37a60d5020d7553438cb3554c40109fd91528436e63948409f997424c36e52cca419f596420cb6c5450920e790942cc27c658c520af191329027e6510620b7597214c27e6114810cfd95540cbb754505109fd91534875e63943419f19543087796094d20be580540c73d6155321dd986544caec6250d219f596325067d654c7209758f52842f965d0240dd544518c36e5214440be58041c427e6414c219f982520c75d6494e20f5c8521cc33e5450f21f5185304427f6054b43f3d4a524c27f6155120f34c1200833c5494d10e7d0d42cc3b564c8521d7951538427e6314c10b7d9621cc3d5434c4319fd8154886bf6150841f3
  | 11 => 0x7e6590d32bb98b530433e5494810bd994515023e6414930f658b504c27e6395010d7186531027d6294c419f99621cc2de6388020f5984524c33d54d0c10af5834350add6010e329f586548c27c6550530cfd5232442dd638c030d7d4e32c427c6054f429f98b515039e54cc020b7d8d428c77a6014f21e7d0b40cc27c6154c20ad58742106f960d0b409f99731483755388710cf550530833d54908109d98754c839d53d0040dd54a310c73e5450b21dbd4a52cc67f6055121b7d8d42442f464c85219f994415035e5310c40dd9445090b3e54d0410db18252043746494440f6d0130882fa6014442dbd5252043db31cc130b758b40cc2f56190c10bd98752d0ede6310030f654f208833f54d4d10d610d500ca7f6550831bb588408826f654c832db54852d027f61552309fd91520c27c6454430db548524c76c52509319f19743c42ed620c621f6580324c3da6384010d715130482bf65500409f597420c7e66190842cf990544c36d5250a40cf9524310ebe6414b319f98e5010be55244010b7d93324c33e5410210ed50841043e55288710d7d95310c67d6194332d7182538432e5454810be58032d03755444010f398e204833e5450c42bb98b539067c6548740cf15342c833e54d0b32ed946419033d5494f21f6509304835e5454c10d794f328835f524c010d719353486df644cb309f58f50487775194620dd14b51502dc6150330b758a414c27e6590810d794c310435f528c930d5945300837b42940329fd85540caf665d0521dd94521902f66588510d7953504c2dd64d4930dd181510833d548c832dd989511035f654c0109f584540caf46150d21eb151424835d538c821cf95150c876e52d0040f6d4d30882dc64cc8329f987520427d6294010d7d5343cc35d5314e40ddd4651d0b775194732b7d8552cc27e6094841e795253083795014032b798c424c3763254420cf551430427d6194c20b7d8d428435c534c710af59741906f86050530e7551530439e41903309f9845250f755454420cf152414827e65d0d20d758e50d07765294440ed98742106dd62d05309f58354086f7654c431b7d91214c2dc6050f30ddd09510cadf654c0109f997321027f6510410af592425035d53082109f988540827e62d4530de186500cbb954880209f992530827c65507208fd9153483ac4350842cf593530827d654ca10b798f21cc2f56190e219f98c540c65e6394242d714c325075d538c6209f195324833c5450821d794e32902de6550530d7597308835d53d0c419fd9632d075e534c810cf94d4310f756054432d794c43842bd6010440dd94441c837665d0521f34c832cc7b54194041cf551428c35f5390d41b75974390fb541107319f191528c73e6415232d754f32843b56190942d794d210836d5290440be582324c33d6414f20d794d2
  | 12 => 0x94630cf951428875e5310220cf58e54c873e5250b40af990520437742544409f994420cbd8614c220b758840cc3ea42c8120bb98b540427f658c410be18142482dd6110b30d795130883ba60d0b409f19152443d930840109f98252cc75e538c220f354832cc3d4514c5309f9825190f5d53548109f18d520435f63551319fd89534827e6015131cfd05501073d5415320b718d4210b5c6054e10bd984424435d538c820f994b41043776454420dbd4832442dd6390320f5905304427b6544010cfd95411067c6114910d7d8d53c875d5454c209fd81544827e64d4e10b7583320cb3e6155010dd14740502df6150b30edcc9411073d5290640d754f310435d5314e20fc946200837551145429d584540831d5494c10dbd89524427c65cc810b718d421067d6315210eb9514210b6d5250440ed109411072d54c8020fc946401033f6454d20eb94940102bd64140219f59653087765448710ed984411027e64d4931cfd5254883e74188521b7593314c3745488510b798c410c77a5494032f3d49524c2bd6510640b7997324c3da404c1109fd94410c27f6550c41afd8143d0ab460504419f98b5050f5c534c010bd984420867e63d50309f19743c835e53d0a10ed181411075c654c3109b195424827f6590c31d714c324867e658c5209f595430433d5450830cfd51428ca7d6194d10b798a314c2ef6250e20d954a511037451d0530d7d4e539072d5210440cfd91534427e6510510bd98432cc67c61540429fd91520c6ee6214640bd19131887da404c2109f59643482dc6354720cf95250c86fb6450040f9986424827c6548430d714d504875e3294431cf951210436e5290410db94a210867d6015131db54852c435f6354910be583510cabf6454620dd945210c3765110730be983434c27e61d5120d754d51083b84190040d7947300835e5450d309f99743082f86048520dd951510ca7c6155030b758454cc3da53c4210cfd8554c873d54d4032f658352cc27c60546439f99632043793254032db548520c76f6394840d794d32107ae54908429fd9541cc2dd65cc020b7191320cb5d5310210e795340cc2f56194940dbd95200827e6194a40ddd8554842de62cc5309fd9543842dd63941429fd94428425f63553209fd89544827f6550c20e7550544c2ed6210c32b7181324c27e6510d42be58042082ef6448720d794f300427f6510010db14920442fa6090f109f58254cc65f6354841b798f528433d6155020dd54721c835d530c840de983538436d5354840cf15041843af6250841bd58632d07da6054e208f99252c435d5410d30ddd06508867e6394642b798e434c27e6590d31d794e510827d6510f21f698043cc33d54d0020db5485210edf63508219fd8554ccb5d538c210b7197424c33451505409f997218c2f960105309759730042
  | 13 => 0x1b7192324c2ed6290720dd98452c42de6588730be580210435d510c730dd54431082f96088520f6d53504c35e544c030db949410435d5314d40d78c7504c73f6455210cfd9154083776054432bdd85430435c54cc310e7d8d4350a7d62d50319f197214c2ef654c832edd4441902f76150d31d798c540827e6550e10d798e54cc2dd63942219fd9542103d84354032d7191530436e62d5321e6500404c33d544c832db548410427f6355021cf951210827e6014d41eed81425027c6254643cf55141cc7595388020bd18542486dd6190130f948421443345450710db588540c2f56110030dd4c9510827e60d4c21f6ccb304c3d930c4110d754d318835f6454c109f592510873e5490730cf583544435c65509309f19642c42f563c8521bd58754c826d6215210bd99321886fb60485209f59053c435e530c640f64c3108437643d45409f19152cc73e5494c10dd947400827e64d4a10be982310427e61d49409f98453442dc6350920e750940cc2bd6414b30db98853083ce534c832dd8c9510cade6410930d794d430427c65501309f59532c42de6210330e7d08414c36e6215020f6189308837565106109f597424427f6355220be98331cc35d6294c109f996314867d6394620d794e420435d52cc210d794f43042de6448530d794730882f66190a41d754f219033e5450b32dd587548425e6394342be982430c2de61d0e32bed9530883e74254642e7553320cbe942c8120bdd9510042f96008640d794c4310adc624c530b7987404c37b5094121ddd925190a7f6154840cf551510cadc648c530dd597418873d5410621f34c832082bc6050b40bb586204835e534ca40d7d9530c427c6510d10eb99321c82ed64c85209fd95424439e544c0109fd94400837764d4540db94b32cc37661d50319f586524435e53d0840db949321067e6214c20af98342106de6310730eb50b40c83745394420cf95241486f76150e21db19252102f46444010db182521027d62d51319fd8152106f661d0f219fd95200433d5450810cfd0a511079f6450f309f189531073c5410620bd58f41487796584010cf151404427d6590020d7991530435d52cc030cf95341082f76284110de58054087b54110420d714e31c835e6510130d7d8f504c67d61d41439f586500427d6510c21be580421036e6494810de580524c2f56110c419f58a501077b6055110be582425023f64546208fd9541107d9404c120dd152210866e62d5231db94a20042f661101109f992520c7cf4290b30af99252442dd62901309f98e519027d6590930bd5875090f5f5415330bb58853102ef64c8520b7d85324c27e6510d329e980540cb5d6314a10d758653083d93044010d7d8a538427e6590110cfd8c54443746294432bd984408435e6494c20dd944211027e6395021be580428c27d62
  | 14 => 0x88540c27d65d0720b718d544833f4254242ddd47214c27d61d5330f6d42304c37a60150329f59732c42df6350a40d794e32843d930c81209f584504cb5d544c320dd996214427c6254243b798c20443cf4250b30d7952320c6df6050b309fd95430cbe562d0521f5d4551cc39f41107309f5805150af761551309f58a50d0eee62cc721d7d4b504c27c654ca41d754d30883d4614c3109f99421cc2df64cc7309f58e54042df6350a21b758c21cc2de6308210bed8d300c2dd63d0b32dd547300827f658c0109fd9153c873c54c8110d794f43106de640c930ddd85534875f61d4d21b758e200435d53d0610ddd85544c2dd63906319f996318833c61950109f995438876d520c840db548528435e5350810bb98a430ca7c6454321be58021c42cd6210330be181314c39f5390d43d754f320437754d0410f594441cc2f76148110cf55241c837554c4210f690d304827e63d5321e710440cc3f16088710be98332cc27e6214543ddd06509075f534c510f34c8328c37b5388020be982314c27e6510830d7586530c35f53105219758c52842f66114a40bd984428c67d62d5231b7d9541cc27e6114930d794c21082f76250710dd546410c3da4010330cfd5031442df6354b109f98f520436e6214810d754e318875e524c110d754c32482fa628c220d7153308427f65904209f596410c67d6194a30b7987328cb5c534c120cf153424cb6c52085309f98b535027e6215230f3c8621cc33c5490d10dd58454c87d55148530eb59321887773294432be181328c3b54110630af19151482de63903309f58c52506f66114343af990329079d4290530be181434c27c6254f109f191520c73d4294442dd547500cabd64148309f582548c6f66190a20bd58740c435e6394241ddd4721503d5414c1109f99252cc3db654c120cfd50434827f6454d10b7d8940cc37950141439f59632d027d6394342af99221503cd214c120be98231c435f5394c42db54842042dd6315021bd984430c67d62d4530cfd51324437653544209f58f5150b5d53902209f59432c4375524c4319f189509075e5254930b7596424c3b54110440dd59710843cf42509309f588514c37a32940329b588548c35c5214530de94a200839d6414b309f592508cb5c6355121f5d8540cc33d54150209f997420435d5388620edd9141442be64d43319f996434833e54d06109f18151ccb9f42109309f992518c2ed62d07209f58454883db604c0209f995420434d5214930cf18a54c865f6354b40b7993504c2dd610ca31bdd8540c833e5450620ed18540102bd640c831cfd51408427e62d51319f59653082f960085309f98e540836f5394810af5974290b7660944209f18954cc67e6294d10d754c31086be64c8540cf94541d026e6214810d7d9153843b65490710b718d404c3b6541062
  | 15 => 0xc27e65d0f219f98e50042be640c941bd98432102de6110d30d754e3004376514c440cf981540427e6094e21ee95140103da60d0d309f195315033e5490e21d754530083db3294032db98152102be64c8720dd4c9510cb5e53d0e40e795241cc33e52d0a41bb98840882df63485209fd89548435d5314c41af59321486dd64887309f58f54042dd6414730d794e429035f6554c20db548521036e52d0b40cf55231c87745494420d794e32103775194440cf95243c873d54904209d984540cb7752944409f99443c877443544409f59051483ce52ccb309fd97428c73e60550209f590524435d53504409f98f540ca7d6294243d794e310c2ed620c220bd984328c35e63d5221b798f52906ee628c720bd986408433d5450c32bd58642443f06050510db98853c867e6314940d754d430873d51d0040bd58642842f66110931dd9455090afa6010b20cf182540427e658c4409fd895190e7d658c421af59052042f46150e109f197428427f65d0d20ed54d4110776518c440dd546211037543544209f59731503765288421d715330882db60551309e98053086dd65885309f98a544427f6254343f694e401035e52cc030b7594328c75e6590d309f99250086746155130f590d310c79d5390440bb58b30483745354642ed55041042dd6388310cf98e540435e53d0620d754c42102df6350930d754c310827f6155110db54832cc79f4290730d754d320833f6455330dd545410c2bd64c8510f6d51308835d51cc320dbd4a324c73d54d4420cfd954210bad52d0040cf99050487763254440b7583414c35d5348610b7d8d420435c5414930f690530883ac5450b20cfd53424827d6590420d79845350ade60d0b30f554d511027f6055131b718d54486bd64c86109f983524c6dd6015330b798c304427f6054e21d794d43902f56190821dd952411067d61d5320ed50740c427d6510730db949429027f6454b309f994434435e538c420d7d4c42486be640ca209f58f548867f6510a30f6c85304833f54cc110d7943300435d53104409d987540867f6510e21bb9885010f7b50943419f59532442f9600ca41cf592524433d5450010b798243cc2fa6015032b758e50907db5010130af593210877754c4210cfd91540c3b654904419f98a518c36e6215010cf951410c27d65d0c329f58f525027d6015321db54e52103d960cc730cf952510827f65cc910db94a42902df640cb30af59032cc36d5248010cf153214435d53080109fd9432d07d96090f30d799730c427f650c020f594e31886be60d0540f2909304835f5410f30be58242c82f761503309f58f540835c6114d42bd98642506dc6590b309f58c548835f4394a43af58e4250ade6394241d7cc9500cb6e5290440d794c210c33f54953319f584530835d64d4d219f98e54842f6610c820bb9
  | 16 => 0xc654c320cd58454442de6508730dd98d511027e6015110dd94e51102fa6010f30d7d4f30843b65450441be580325067e6394b41de985500cb3d5490a319f98353c875f5394f40ded4250087d9414c2209f18d54042f664c42109d98652d02bd6590440b6d81524c27d65c8540b5d85404c27e6515121d794d400427d650c740d7d9532cc3775194542cf55243043d8654c120cf54f42d027e65d05209f597328435d530c2209b988540833f5490910d718253082dc60509309fd9721cc36c63948109f189539027d65c80109f996418c2df65909309758e50906de62901309fd94321035e53486209fd9631082bd6414630d754e439037751944209f987544c33e5444010cfd5343443665294440d7d4e530875c6454e20be181439035e5394a40db54842107b55490710b7d8d521067e61d50319f18d528435d534ca40d7d8d53482f5618c821cf106501037651900409798e50906de61d0f30cfd91544c2dd62d0c329f18550ccb7563d4540dd946211033e54840109f984524435d53d46409fd9421903775494420f6cc3208835f63d4121b799252cc3b451d0540d7d53430caf9600ca20de980548836e52504409f18554ccb5e6154c409718d52106f56194d409f99743087355410521db98a54c837642d4540cf552200827c65d0c20afd8941503755114520b758c404827e6195232cf950210427e658c7409fd95214c2fa600c8319f984534835c5310d20d714c41487766454420be58043443b56250441dd553100439d4310d41d754c51882bc6050a41bd987420c67e60d4943d7d8653882f6610c210bb5884310a7e6550d20f5586328c7e552c4010cf551438c67f65c8740b7d81414c2f960cc440ddd0d510827d658cb10dd146415033d5490c309f988540427f6254c109798e54487d4328c621cf550544c6bd6414432cf553430ca7d6494c32b7181214c3c9424c1209f58e51d039f6350b40bb18931c875e6354331cf552420cb3e64948219f997414435f3154031bd586428c67e64d49109f197315037a6254032de4ca500cb4e52cc010d754f30083da624c2209f58053086f96010e109f59353482dd6315020cf18254c86f5610c8319f58a5190f3d51106409fd8553442de62d4730f5105214c2f46150e31cf950410c6df6350b10cfd51434427d6588740db948320427d65d0c109f98853042746154d20f314b424c3764254420db54a20842d66114930d754c40043ce424c3209f990540c6ee6295131db54b219023e6415032ded42500caf960d0a209f590530427d6394a10b7988324c3b741485409f995424c76e52ccb419f99731102f561142328f593538875d63942419f59421503d73254432d7551300835d5314c40db58e521027d6154c109fd95310c27e64947209f990524c67c64540219f987524c35f534c1109f59632
  | 17 => 0xa10cf990540cb7654485109f5963284374518c530b7995214c2de63d5210bd98440c42f66115032d754d528433d5414420d7996404c3eb21c8120b6582424c33f5450910e7953438cadd6090530ddd8c515027d65cc440dd4c9511027d654c440b7582214c33e54084209e580540cabf644c840dbd49324c67d6014d42d7952434c35e534c4209fd9521d027d6095121bd185304427d6194232b798e42cc35e538c5109f590514ca7e6295030f994910042dd610c9309f59253482f561d0841d754f409027e6548540d758953842df654cb30d7181530433c5350d42d719053487d6414c310f314a324c39d6414930cf952510cadf6048530b718d214827d65c8530af99353c867c64544329f58853442df61503309fd9632d035d544c220b758c511027d63d4141d7d4c4350b6c52cc910d754f43082dd61d0d30ed593218867c6550120f6d81524c2df63545209f98a539031c544c110d754e42082de61ccb30f34c8324876c61948409f98c52843e76248510b7d8d420c2f66110b10d754f31c86f5618ca31dbd4a52c437b50941329f59743c42bc6150040dd19251083766510521f5c8621cc23e6414c10b7592514c3766115220cfd83544433f64552209f587535033d54c8410b7d9152cc27f6454f10cf551420caed6210520be58f208827d60d53219fd94418c2df6054530b798c428cb3551500409f982544cb2e54948109f194310876f5294930b759441cc36e5454810d7d44314c2dc6510530f6181434c35e530c610af1854350a7f6155121eb95242c83d741907308f596540835f6194c40db548428c67e62150319f595404c27c6454a10cfd5253443cd424c320de580540c75d6315130b598642cc33e6415221dd94731cc3b54110521bd185408837542544209f58153042bd6414a10bd986420cb3e5414f219fd9732103786055121bd58432cc3765190420f6d93504c378538c120be98032cc3cf5210930b7580534876d6214141d714f30882f76150a41cf553200433f5450a319f195414875c5310921be59610042de6548730d7d4e5350b3d5450420eb551520437661d4f10bd984404c2ee62d4440b718d42cc7e76248421d7d4d41486dd61d5330f594c41042f66110010dd94d31486ed6210d20fa486304827e64d4b10cf58d54083cc5388521d794d32842de63152209f593504863d6494d10d754d43082dd63d07319f987530863d6414c219f197430875d5394640b7d8d544833e548c410dd144214c2dd6314221d794d429027d6550b30f694e300c36d62d5231d754c438827e6550c21bd9822144278654c120cf950420867d65cc421d6941300835d4354043bd586324427f6454d20d7147314c37552104109f98c540c25e63150209f18953102ee620c421eb50a41c827e65cc620cf553438c67f64540219f992534875
  | 18 => 0x9fd9151883cf624c120b798c200435c32947309fd94311037751d0140b7d9721cc27c6154e40f6589308827c6590c10d798c50486ec6254d10d754d420835e53900309f983540ca7d650c810f394d52042766114810bb18121c835c5454e109fd89544c7e66210621af593218875e53c8010bb98a41086f56110330af1894350ace6210330db986520436e520c840f910521c827e6508010e710640cc3da54d4130dd18e511027e6494b109f58f525075d5494c10ddd9051503bb41d0140f954951103765150420de90a500cb5c538cb10a7993214c33e5450e3297195214c3b764507109f997424875e5350e429fd95300427d650c0209f58a544873d5450620b798f404c27e6094a31db54b310436d520c830bd181411067e6590c20b7986314c36d54c8020d7d8d53c436c53548409f593524c35e53946209f596438827e63d4542af58b411075d53d0410cf952310835d53d0a209f98e529027e61951329f596424c6dd64ccb30bdd85425067f6054443dd185534833d54151329f988548c6de6210d30a799032cc36d5210440de151500ca5f6355121bd586424c7774354432b799031cc27e6294043bd185434c7e52108710db5974290b5e530c440bd986321063f64549109f59431083764254432bd98652d0e7d6548440b6980424c27e6014532d794e43042de6590130bb58b539067e6494b31cf55043cc2fa600c620ddd46518cbb55454420dd50d510cb5d63d52309f9805350ade62105309f995414c35e5388420d794e40083765190620bd984520c2dd6190330bd98432d06de6190f30db98e520436d5214b41f5584534879e64c8730de945500cb79524c0309f997410c2fb6050420be583411027f65484209798c54882ed6290f32dd94d5190b3f64551319f59742c427d6294031afd91534827e64149309f59643c83745490710b759631cc25d6395121cf98254082d9600c831cf182540827d6194f209f5865390a7e6194c42db54720082dd6314121db14a214c2be64150329f58c525034d5354810b758e214c37b5094143cf58e540427c6155132b7591324c3593254032d794d310c2de6414530d7d47504c27c6590e20bb58a3148375510c440af99020442dc6448530cfd5254c42ef6548020de50e500ca7e62153309fd95414c35c5494930d794d32102dd6314242ddd4621483e63188521cf990548427c6510c20dd58453082fa6014432af99020842dd63905309fd8d510837565c4010d794f30842dd63d4810cf95142102bd6494a319f9865290e5c6354910bd584529027f6454b10dd946200827d6394640dd951411076f5248110f358b30482756510410b7987424c37752c4210d795153882ee620c2209dd8554482dd638c431bd58443cc67e63d4520bb58a200839d4150130f6d07504c2dd6590530cf14f4350af4615
  | 19 => 0x4310439d5454c209f59252042dd64d4b30d794f51903765150620bb58b41c873e6415132b7d96214c2ee620c621e7d8d42906f56114043e7d51434c2dc6350731be9805310a6e6215230d754f311027d64943319f594428c6fb60508109f98b53086f66190010cf55131c867d6115332b7584404c2f56190930f6d0130483af6450842b758e324c35e6315010d758e500425e6315021dbd48325035c5354142cf95243ccaee6214341cfd9154886dd61d4930bd586420433d5415130dd15141c436e52c8640ed50750107755150020be580540caf46150c10d714851cc3cf30480209fd85544cb5c548ca319fd91538867e63151109f997424435e63d5030d754c52902dd6384110b758042cc2de6308310dd50d511033c54d01109f18c544c27d60d4c21bbd8953443775444010f694d40102dc63508209f980548c63e64d4e219f99431082bd64c8530ed94d41106bc64546209f191518c39e640c831bd982414433c541031097d8d51c82ee62d0c42af593219027e6314910cf59252c42fa6088620ddd53418867c62540419fd97211027d6394321dd509510cb3d540c820eb94b401035e53d0e10d714b324c3d921d4130cf951310436f65484219f98e54c875e5390a10af59321043796194032cf15141487d8324c220d7d4f314875e534c030cf994544431d54cc0209f59442042dd6314840dd984524c3766114810bd988418875d6214d42f3588404c3e5628c621dd14541502ec6050b209f98854442f76148310dd10e51102dc6308730f594731cc27d6494e10b798c300427e6508640d794d511037561d5121e7951320cb5d54d41309f982540c67e6314121f394d200835d5308610fc54540103b860505409f98a540435d63d4810ed192511027e650c5109fd9632c425e63d5221ee55120082fb6050a40cf546411035d5348410d714c43c82f56190a40af582415075e6314f21de580540caf86048440bd5845010bd74150730d794d300827c6014d109f988544c7d5414c310d794f210436e5148720b759542cc35d538c710be58031882fb6050630dd946219035f53d0942b798e405027c63542219f197424c3ce5354840de0c9500cbad5290440bd984400c35e5388430af99331902f46150e21be582438827c6454e20e7990430ca7d61951219f59743843db514c120dd988515033e6395020b7980214c27d65d0e20db94a328c27e60149439f992538876e62150219f19150ccbad548c832b658052cc31d5494c20cf953438cb3d6055321db54842103d653106109f596320873e5454c209f99254482bf65504419fd9541106f96014c219fd96430ca7e650c6409f99432906f6610c921b7d9121cc35e5350e109f98c540cb3e5490a32bd991314875c3254231cf150414833d5454c10d7597430cade644c930d7d4e53c835d5394810
  | 20 => 0x439f54d0d30ddd0a511036e520c8309f99251cc3756194b43af99253443d46394432ded4250ccb6d52ccb30b7990434c27f6550410d794e439023c6454620d794c43d027d6550b10b798c42cc35d65cc210e755043cc27e6395120cf15343ccbf25148020d7990534873f6455230cf950414876f2154221d7553434c3cc62551309f59732d073e544c010cf55054042be64c87409fd94410c73f6455310b758b41cc3cb214c120d718d544833f61d5110d794e42102f5610ca31d794c329077b5154032bb58a544c76f64948109798e50d077a60d5010d794930c435e5350a10af99054043d8614c120b7592434c2f561d0d31d758553882ee62d0521eb14942d033f5495230f94c6214876e6454810bb59121482fb6050b10be580424427c6550f109f58253443af4350920bd586324c6fb6048440db54b320435c5494e20be98243cc35f524c310cf95140c43af64509209f983544ca7d650c821d794a51cc2fa6010b40b718d42103565394420be189308833f5450931be580428427e650cb40cf98d540827f6154d21f5105308433e6415321de50a500cadc6350a30d794d43102de63881109f592518c2de62cc4319f99742482df6350931bd984300433d5210640cfd9152442bd640c931dd144414827f6510620d6d0d500cb6e5210810d798f540c7b454485109f59543086f56190b109f189540c75d6315230db988530877a60d4c20bed81318c3765488710f9d8521483d9600c831d754c438876e6215031be98232c827e6194840bd584540c33e5490431be586100427e62d4e10cf550410c79e640cb30b798e208427e6095321cf15143ccb5f6554c10eb50d4248374514c530bb98b434827d6414c21dd0c8515039d42d03309f59251c827e6494020edd8540102bd64c8710d795232cc3756115230bed8510043b741502109f185529027f6510832af59053c82de63144209fd95310c6dd6394542bd98441442bf6250740e7d52424c37642544409f5964104374538c621cf952400436f5290931b7595414c2bd648c540b798854cc2bd640c940ded0e500cb6d54c82209f181544c75c538c940a759351cc2d461503309e58053c86756115032f64c9500cabe640cb21dd5845050b5e6315031bd586428875c6354910be583328835f6194e109f98a548435d538c610cf952210427d62152319f181518ca7c6510a10cf147415033d54d0b30d794730042ed62101209fd85548cbba60d0740d794c218833c5450b209f98653d03cc524c930c7551300433f5450110dd946210c26d62d5231dbd8953482df6350130afd9132d077950141429fd9443c877b5094043bdd9221443db60cc9309f997324c27d6494c31f3988328c7d94010130ed553418427c650c010d7d8d544c27c650cb10af990508cb6e52104109f58354ccaf464c86219fd9
  | 21 => 0x658c910be980218c35e6194e409fd9432c433c54d0710d790d5010f3f6454620e7953430caf5618cb10bb58a30082df6408530dd54721082bd640cb219f9875250edf6348420af98341d02bc6454d109f988505076d528c010ed504414425d6394341d7592530437a60d50329f594328427e6394321cf992524435f544c310cf153434cb5e5350840bd98221c437651d0720d754f32103d75154530b7d95310c66e62150109f19743c87756115032bd586420c3755348510f3c8530c827e6588430ed50441842f564905109fd96210c2df6350a329fd97328435d6194c409f99252842f565d0621cf50a511075e530cb20f914521c83d13044010bd9864210af5610c940b718d52c433f5490d10bb58a214827e6394d209f595321033e5490020bb98843c875e63153329f58a53d03da53c8220bb189504c73d65d0a41d794c430c26e6214c109f197325067f65cca419fd815110a7c650c910db54842d02de6110e32cf95221082dd60c85309f99743487b54110421cfd53408433e54c4010b7d81300c3ea3294032dd18b51502f563c8621b7597308c35e53c8640a7590524c37551c8020b7996214c27d65c84109f58251d0a7d6394221dd9825190a7d63d5321f554e51082f46150a21af593210c27e6494c30d7d95304435f6354e10d754f529027561951329f597434876f52509319f98253487775354420eb551320ca7f65ccb4197d954310ebf6250842cf95041cc33e5450f209f587538827e6590f10dbd89534867e65ccb109f99642cc75d5390640d794e318827c6354b418f593530827d6510c309fd95400c27e64150309f58c54c82de63d46409f58c515033d5490c32db949200427f6354b10dd0ca51083d9600cb30af58041902be64887409fd95324436e524ca30cf151434cade65905309f98f525035e530c020d714f314865d6314141bb98843c836d64548109f59731d027d65d0f219fd9741883cf63487209f58a53442de6390320d7d8b53487d9614c2209e98053c86fa6014841dd594418875e5414b30bd58732cc67c6354420b798b31cc33e6415030ed98d41106bd6414121d7153304835d5390c21d794f43102df64ccb30b758c50506dd6290730f98c9510caee62107209f984548c2fa60084209f58a519037a5144010d758d508c7b55250441d594730083756354642dd98d510cb7643544209f99742503766115031af99042106de63d50209f99432042de63d4a40d7150324c27d6494d21b7988424c2dc604cb30db14a425027d650c910de94610042bf6050d42d554d510827c61552209fd89540836d5208010eb98b43d0b5d538ca20bd58f41886f664c4010e7d0f420cb7541540419f994314835d5350020db19252042f96014b31cf951310827e6215331af59353c877b509433197d9521cc27f6550521d7d4b300
  | 22 => 0x4329f590504cbcf6350b209f99632c427d62d4c10bb189514c3755410521cf98a54043d821d4130d754d318427f6355132d7d4c5050b9e54cc010d7d85538427e6294730d794d408439d640ca319b988540c75e53d08209f596215035d6394042bbd8542482dd60d4730b7d8d211027d65d04219fd8951d035c5354542de98054082fa60d4432cf950300433e63550109f984540c67e6590d10f6d0d500ca7e6394041b5584328c76f5250941e714f4350aee6290621b7d8d544867e6094c41cf55042c827c6254730db948411027f65cc740e714e4250bda51d4130d754e430836c52d09309f1815210f6c5394840b7983214c2dc624c730edd4741502ed6210f32ddd4641502dc648cb309d58454882df6348630f6d8130442df614cb309fd8d5190add6290330e7151434c374534c621cf952408425c6354720f6980214c2dd6014d42af59740902dd6490930b7197404c3776214540d7552538436d5214a40cf950420cb9d42109309719521cc27d65d0d20d7591530435f53ccb20ded425010afa628c120d7d8d54487e652c4010f6cc110043db604c2109f994438835f6014d21d719730443655210410d755153882dd6490c43f6cc210043db644c220bd986424827d654c640d7d4e324427e65d0e109f5845250eef6254131bd584540cb5e54cc220d758b53487d641cc110d7152530435f6554e10ded4d20082ed62d01209f58053487cf6255130b758e408835e53d0c42dd18951102be648c940eb95120082fb604ca20b798740cc3d55188530de14d30882dd6310931be580430c37a538c030cfd53214435e6314e20de98253883e76248710d7d86539036c52485109758e501077a5248020cf582540cb6c5250940cf953520435f6294c10db58b54887395494032b7994324c39c5350d42cdd9541106f561d0b319f19153c827e6415032cf95153c867d65887309f58c524427f654c7209fd9442c433e544c020e755342cc33d54107209f58e50082f4614c310bb18941486ed62d0c219f58e52442d96014730b758c40082f661d5032db185520437654841109fd85508cabe6408010b658354cc27d6195032b758d214c27d65c87409758e5010b74538c5219f59642042dd64cc730d714f30043db52d4130cf553400427b654c030cd55041886be640c841dbd4a52107766114e219f593538867d6550e21ddd0d51103754254440de5405090adc6508730dbd4a42506ed6215010b798a31cc2f46150810ed504418c6dd60cc431d754c51903d8624c120b7984544c36d5210010e7508414c27f65481109f582528c6be6414830af59032c827661d50329f98252d0efa600c940cfd5320443595348020cf95242c83744354642b7189310c7d961d4130cf55043c873e5410f31b798c40cc33e54d0f20bd58454883355454432d794c430827e
  | 23 => 0xfd91508c67c65d09109fd9431c835d63943219fd8554082f56110f41d755130843d541cc1109f98c54c43774254642be58331442f662d0521cf550420839d4290730fa4ca500cadc6350330b718d424875c53cc1209f58e5190a7f6055110cd952510827e63d4a10f6582544c3ba54840109fd81510cbb74188540d754832cc37661d4c21bb58b51d0e7c6510f21d794f400435d534c2109fd9532d075f5394e42be58321082f960cc610cf986540437651487309d58453082dd6384010dd596318877a64940329f19541cc3796454032be9835190edc62501309fd96434827d6314542d754c31882f46154d209f98f54482de63d4440db94a420827561d5330f3988324c27e61940439f586521036f52c8710d7151304435f5494e10d7d85531036e6215210b718d210835e6494c30de90e500cb5e53d0830bed8f208827d65cc840e7d0842cc33f5495232d754d100435c6294e109f592508879e54107309f990530427e64149109f59420042f661905219fd8151ccb5e54cc030dd545401036e5494810d754e10043d8424c2209f98e51d0b755190640f94c9510ca7e65d04209f196420427d60d50329fd81548c6de63140429f980540873e5414c109f59742cc7db604c530db54b311027e6214d20dd98453043da414c120b718d52106be640c920d754f210827e64d4d21db58b538873d5410420bb588530427d6595020af5824250b3d5454032b718d42d075e6154c10bbd9521086dd62d4730de109500cadd6510530b6982324c27e658c510f5d44414c33d5450310b798f414c75d534ca209d984524c2f76150220d7d4c325067d6494d10bd984324433c5490510f6cc3104436c6194810d754f20083764354432ddd52510cbad5494810b7191314c27e6514d10f394e52103db30c4210eb94a411035e534c620e754c411027d6395320bd986439065d6314810db54a420c6dd6190d30d754c21042f6610ca10db14921c427e658cb41eb508425035c53cc921f9d452148376538c6219f59531883d8414c220e7152424c3d55394440d754e408427e61d4e20db948421039c54d0d30cfd5141c436c6354840e7551300827d60951109f98353486de648c130d754e21843b74294642b799251cc2bf6550f42d7d8d530835c6094c10db94b20c42fa6014c41bd58753103e65254440e7d0841cc25e65d0d30dd98753886d960d4b30dd54451903cc6348720d714c31483b45110640d7d8d54482f9600c841b758c408c27c650c540b799121cc35d5350640b7185320cb756115110de597208827d6494820f68c7304c35c534c920cf950430436e5208210bd584548c33e63d5110dd98151082be6408310d754d30c42df624c530dd945218c27c6548510f354b32cc27d65885309f18950d0ef6610c821b719231cc33c5450932d7192531033d54d4
  | 24 => 0x53c43d5610ca31be5805310af56190c31af593520433c54505109f19532d076f6554810d7181531027e64d4e219fd8153443795014341f34c8324c79d41d0130b798a51cc36e52cc4109f582548ca7f6590910cf990544835e53c82109fd96418c2fa60cc740b758341cc2de64c8530eb90d4210bd753c8521b7982424c2de6510130af99050c867c65486409f59053883d96010f30af590508c67e6510d21be983210835e5390e429f194414c2dd6588730d794e408827e65ccb40db54821c42f76488710db949420833d5448020f5945300835d6354232ed15210443d7518c531d794d51083776548421dbd48424c2de63d0530cfd52418437661d5330af191504c75e534c220cf95043083795014343eb50841c82f960c8630d754d521035e5450f30bd58743c875d63543439fd9152442ee6215210b718d218c2f56110d219f5865010f5c4394832dd14d314875e54149309f197434833c60950329f996219027d65cc410ddd83515036d52d04109fd9631d03e4624c521dd108515033f5495221ddd8d5190bdb30c8120cf953420433c5450531f510530042dd6095130db548528c75f62d4d42cd547401027f6154243d794e438436d5250831ed504414c75c5350d40b798e20042df6150d30cf95241c86df6350831f654f409035d54cc320d7182531034d5394810db58b548835d53c4210db548525075f5415130f698930483d6414c431b6582514c3d93088120edd0540043715194032bb189438ca7f6354620a7590324c35d53cc220ddd53100433d54d0b219f98a54cc2dc6510930b758e50506de640cb30dd98151103b55454432bd98241c42de6348530cf951418c2fa600cb21ee552500cb3e540c020be58342482dd6394021d794f32886bc64541219f59532903796014c219fd94320833c5488110b7592404c35f5394e21d554530082bf6550c43af59050886ac6250d42bb588531076d52ccb31ee58241902f8654c120bd582314867561d5320b7d89414c27d65100209dd85544437a6094a30d759640cc36e5290a30cf55350c875d538ca41de980538427d65cc940db991521027c60552319f99543c82dd6310930f3988404c27e62d5020d794d40102dc64085309f19643082fa600cb20b7587404c2bc6050841dd8ca511035f6494c10d758c52042dd63d0a319fd89510c2f5610cb20d710153103f16010410d794b30443775150540de18a500cb6f52cc910ddd465190bcd21cc120cf949429075e5388620dd59441042f763c8521dd98d5190b6f53548409fd96218c33f5450920cfd51408827d6214d41b7d8d424cbba5444010cf95342cc75d538c410bd58432c87b74148740bb98840483d56190930eb509404835f6354841e7d51404c33e5414321cfd4a41506ef62545309f18152cc75f6355132b7592304c3d441885309
  | 25 => 0xbd651487309f589530827e6294f10b7d91314c37a60d50309f19542042f56114032b7580328c75d53d0e20b719541cc27e6215310b798c521077551c8440b7983414c2df60507309f997324c6de6310d309f988540875d53d0440d754c4310af960d0510f510521cc27e6510f20d754e428827d6194a40afd91514827f6354341bb588400827e6014941b558754cc3b54110530be580424c27c6354b40b7994424c2f960d06109f59541882dc6048730d754c308427d6294430cf55232c86de62d0130b758f548833d5490410dd181510cb7654885109f992544867d6394421d794e320c3b54110410d714c31c82de6550b309f99421443db51d41309f984540c2ed60d0a42af98341907ce42cc320d755330082f86050540b7588430cb7442944209e58054087db544c120bd984508ca7e65c85409f99442cc2fa60c8630d754c53c435f654c1209f9865010abe6414c21dd94d318867f650c4209fd8d52d06f963c81209f99741c839e54d0930bd58440c82dc6348440d714f434827e64145309f1855090b755154032d7551300c3f15188020af99321883d931cc130bbd8930482df624c8329f191538427d6494f20d7d4f324867f6508740dd14921442ed6214430ded8153483ad4210b219f59642106f46150120d7d4f304427d6095131af59241502df640c5309f994218c3b860509408f992544427e65d0d319f596410873e6415110f6191308827c658c940dd59741042ee60c87209f98652d0edc6354520d7d4c328875f53d0521d754c5390add64d4730db54b321037b5194032bb98a43ccb7451cc520d7d4451cc2f5611084197d95320ca7e65c81109f99351482de64885309f592500836d5248410bdd8554482f76154930b798e20c43b66110640d754d438827e65d0110d794e519027c6254f41db588548c35e5254b30bdd855050f3e5450320cf18f54442df6155130d71805350b3d5350b40ddd4651d0f6c528c930d698d500ca7d65906309f98e51883b54110640bb189318835e6054c10ed146405035e538c820dd90d511035d530ca409f58f520433d6494a319f58b54042d9638c120d794f21842ed6290220d714e31c875d5494c20d754730083ad4210b20cfd9154043ce5394810cf590524c27c6590f109fd8d5010a7e6314141d7952324cb3d54506309fd9731103b54110621cfd8d54043766114f209f595424cb3d5450610b718951cc27f6254c41cf952500ca7c654ca409f586544c75d54d4d21dd58453c875f544c030b7d8d42cc3f26010410dd94741cc37b6550040f6980424c2ef6250120f650530483765190410c7d51304427f60549109fd91510835f654c220db949428c27d6195330dd944410835c53d4542ded425090b766115221d758f548835f544c210b798443cc37551506409f597319027d65905309f593
  | 26 => 0x50510d794c43882de620c831be982420827f6590e20f350b30c827f65c8630bd98432902f661c81109fd8153042dd6390431b758353487d963840109f583535075d5414d219f59643106ed6214043cfd09501067d63d4142b798c50c86da600c930db58a544835f5494c10db94b320427d6550d21f218930483d661d5330d794c30882f86048610bed8141842f860485109f99432442f66110330d7d8953043da600ca31dd5445190f5d63152329fd9543c86ef624c721be982435027e6014d21cf551410c27e62d4543b7d97414c27f65907209fd815390b7661d53209fd8d54442bf6448440f90c521087765150410b7584320c67e63d5310bb189434ca7f6454732bd5845310b9d640c930f6d8130042ed6210230f514f214877761552209758f54882dc6050b30b5584324c27c6550c20d7548328c6de64cc930d7d4e4250b7651d4242dd14921c433d5488010bb588540c3d9514c2209f59352843b46150a419f590524c7745354420dd545218827d6494632d719730482f9638c030cfd51414c67c64546209f98452502de6208530bbd89430833e6415332e7151404c2fa600c5209f5835150f7551cc4309f595210c27e6548530dd547400835c534cb20d7597438cade628c130ed50441c42bd640cb40dd591510827c6054c21d754d310433d64d48109f980520427e6314c20b798a54cc25e6394021d754d211027d6294730fc546500cb5e53d0240dd4ca511027e650c941de983548435e53d4a10dd94421c835c530c910bd98643506d761503309fd95424cb6e5354810de583540cb3d5415120db548329073f54d0b20dd0cb51502de6314442be1815150a7e6215032cfd91548c67d6194d209f9875050b5e5314620b798a40cc23e6494821ed55341042bc6454530be98054086f66444010b7d81310c76d520cb41dd94520083e56190b20dd94431102dd62d51309798c54043365494432d794f211027e6590130db588530436e62d5020cf58254c867d6394b10cf550500cab461500409f59521d035e524c020d7d4d300827f650c910d7d4e325027c6454e21b799453486dd620c530dd58753082f6610c931f354930042de6310320f6d42404c35d544c010b798c50d06f565d0641dd548418435c6294c209f184534427d6214f109f58c540867d6590c309f1895010e7e65c8640e718d425027d61d5132d7d8f5050e7d650c440f6887504c27f60547429f98b534435d5310e109f59352c436d52486309f593514caed62d0e21be181324c33e6415131bd9845090adf6508530b7190314c27d6315221f594741cc3d4328c431f310e320cb3e54d0820cfd51404833e5450721bd586428cbd5414c431eb55320082f561150209fd8954042dc65905309f59541c833e5490621db5485250f5d6590f30ded95500cb755114540d7d4d4350
  | 27 => 0x20be58032cc67e61952209f98a51042de6510b30d714f43c82de61949309f99620443775194443b798742cc35d53d0020bd984324c35d2114d21af191524c2fa600cb41b7586328c73f54951319f58d540c2dd63d0930bb98850106776550441d794c310837441940109f992510ca7d6550d10b7d8d50486dd6388730dd18a510837552d0410af59351c82ed60d09429e580540c6f561cc921d7cc5508c67d64d4c20b758e50c86dc63508219fd8d54c875f524c210be982428c35e534c820be18141c835c1054c10b798a544c2dd63941219fd95310833d54d4c10cfd53434c2dd6414930dd50e51102de6514d429f197438433f5490d20dd592510827d658ca41d794731cc27f65484109f986528c35d5314c20b7984404c2f960d0c40b719121cc27f64540328f99353c873f54d0521d7952538839f6350841d7d4f3248377510c520ddd95411067e63d4121d7d50438cadd6508530cf18d540cb6e52cc4409f980524c7d953c4210b718f214c35e6054c20bdd8532907b76550441e750540cc3d954d4130af997415033e54d0310d794e31086de6494530de94e308827e6295310f6d8130c435c53d4142d7d4e534427c6254031b7d95320cbd8324c1209d986544cb6c524c9309fd8d544c27d6588630f650130443b46155010f954a51102dd6090730be59240102f960d0e30dd984530863d6595010f9947200837551486309b988505075e53904109f185531027e6294041b759132cc33f6455121b7984424c3da6354032db949218435e5394440bd984320427e6294341bb58843486f9600c520cf15152442dd610cb30d718653082dc6590730e750c43cc6dd61d0f309f99532c42f96090d20f6501308427e6195320db948200427c6354321fc94540103766054432af59350c86f5658c621b759730883b741d0210cf551410435c53d0521bb59721886f9608cb209fd9541883d66114b30bd98630842dc6488530af99032cc6bd6414f21bbd8941c875e6394321d7590534867d61d4930bb988505073c62550329fd9442cc3755110730b7d8121cc35d5390010f6545304827f6254e41b7584544c27d60d4e21bd18542907d8604c930cfd51434c3d641cc310bb5974290b3c540c910c7153304435d54cc220bd98642cc6bd648c740d754c31887d9624c120d754e21043d741485309fd97428c3cc53d0942dc945500cb5d65cc3109f584538827c65505109f19151c835d5350a20bd5845050add6195330db5485290fd95388020d754d328875e52ccb309f58253c87ad5210440fad42204837765544409f997438873d5110440bd584521033e548c810bdd95210873f54d01109f597329075f5394e409f19531486f6610ca41d9547200836e520cb31cf953428436c4054840cf18d540835e6454c40dbd954210bbb5090140bb18940c82fb6
  | 28 => 0x98032d027f654c110bd584434435c528c530bb98853106f56190831dbd4e52103b464440109f983540c7e64248421d7d48524c33f6550b409f98a53d033e62550209f997325077743944409f18d540867d6510931ed504410c2ee6290220d7950328c67e65905309f59532d075c548cb30d7952524c2dd6394042de98053083565354440e7593214c27d62d4131bb58b511035d5394840db145214827e60d4e21dd580515027f6254e40b6580414c33451d0540d758f544c27e6194c20be18930482f86050d409f58e54c439d5410c32f694d300c27f658c8419fd96420c67e6395220b798021cc33d64d4e21b718d428435d61d4d429f191520427d6014f219f98854483d541cc310f3484214c2dd6294730bb98b40c82fa6010f40f3988430ca7c60550219f18954c42bc6454910af99051882dd61d4b30bb58831c833e63950329f595428c39e41505309f587530835e53cc020bd58432d02de644cb309fd97410833e54102209f99052c433f6455320db54a21c435f6154e40de582544827e6588530de94e30483745454420afd9132902d56110130af59353042f96008540db58b530427e6015031bb98b51d0f5d5350e41b718d428c6dc65085309f19532c433d5450b30ed90440442bd64cc440d7192530433d6414f21b758221cc36d62d5010cf95232082ed62cc521bd98642082dd61d5130fc98221c42be61d0040ed952510ca7e6394841d7992530427d6508440cfd95540826d62d4c10b758e501075d53c40109f18d52c42de6314021b798841cc36e528c010b798f40cc33e6055321eb949429067e65d0e20be583324835e53d0a20d794e20043755114032ddd5151083db60d49309f58a530427c61543439f98454cca7e6494632ed152214433e540cb21b758851cc29e64c8730d754c53442ec6255130b719721cc3795494032d794c310c35c5294530cf55331082ed62d4c40dd946318c36e5210010dd90a511027e6510a319f592530836c62551309f996420c2f661cc110b7591314c2f661d52329f18d51d03d7614c5309fd9443c43b74290441bd98432c43f241c4110b7d914310e7f6590730bed8121442de6210f30dbd49214433d5414810d719530482dc6350910bb588548c35f4394832edd51214425f654c02097195424c33d544cb21bed81314439f6350842cfd86540caf6644c621b7583424c27d60d52219f594428c27f6590430dbd4a52902fb60486109fd9621043db314c220dd94631c83755110720af59350cc7cd320c830b758e424c2f66190b32cd54641102b76550441b758f51082fa6088520d754d300437561d5032d794c529027f6590c21bed8131842f561d0b41d794d320c3755454432cf951510827d65d0430b758e41cc2f4614c921f594f41042bd640cb41f64c9300c35d53d0a10f318930c827f6154f
  | 29 => 0x210b754294440ded42508cbc93088120dbd89544c2ef6255130d7d91538835c6454c20d759253083e53294432bd98642102df63509409f19532442766115230dd10a510cb5c544c010b758c428cb756094432d794f529023f6550842bb588300827d6414b10d718d52106746155220de980540433e6414c21dd947310835e53d0210d7d5153082ef6448520d794f43d03f141c41109f589540839f4350832db48550086be6414432d794e419033d65d06419f98f54842fa658c120d754f438873f54909309f194438827f65508329f994324c35d530c010f698e500ca7c6454730d754f511037b5094131de546500ca7e6590f219f997414c75e5314810bd583419067f658ca41d794c51103744394432ded86500cbe74148720cf950310433d540c721dc545500cb6d5244010d715052cc33f6550f42d754d30c837b6154032dd54e2144376514c720cf550320435d5310a409f99442c43775194520bd58642cc2be648cb40b7d8d40cc31d54cc010cf950400c3765114032cf191518835f6554e20cfd81540cb795014041dd584528436e52cc840d794c43d076d52840109f984544c3d94010330f6582524c23e64d4810cf151534435f514c120bd984320c2ee6090b209f98f5050b5e5350c209f18d54c867d654c5219f9943048376510c430ddd04505077652145409f59053886bd6490841db54b320c36d52d0440f6187504c2be640c820db94b218c33e6095032bd584524c2e662d05219fd8d52907d9614c1209f19542cc75c6254c20f6d4d304827d65cc841cf951320433c5190140edd08515034d520cb30cb94942906fa60cc6209fd9432907d55110730edd4d41106dd65d09309f994404427f60547439f993504c76e5210b419f99441086f665905109f181540c6f66190a309f19532503f25154032d754c419036d52084109f586531033d5410c31ddd92510cb5d53d4810bd59441842f56114242b758440cc3af6250d42bd987431067e62952309f594438437551144409f99441cc35d5350220f698243cc35e6314e10db18d52042f6618cb41d7d4e530436e52c8420db98b53082df6510b309f18554c82f56010521d794c51902ec6250e42bdd85535027f65904109f996414827d6194032af59321cc2dd63150109f58e51083755410621dd14731502fa60d0440ddd4d210875e6094e10bd98442d063d64149309798c53043d843cc130bb58850906da60105309f58b53507ae64c85209f58252443b44350441bdd8532506f66114b30f358840cc36f5294940dd58453c8378534c1209f18d54c43e6628c621cf55054cc27e63d5220ddd855344277654c431f5584324c2f46155220b7d92324c33d5415232bd58742486d962d4130f6980324c3e9214c1209fd8d540c2f66510521d794d410427e654c520ddd46518c33e54cc832be
  | 30 => 0xae5210440d754f52102f96010740b758f414c73d54d0831bb58b43d0b3d54d0731eb50b404826d62d5010de986500cb756194842d794f401035c534c020f654d100433f54d0220ddd0d5190b3f4354a43f510d510ca7d65106208f59353c867f6454630d794e328833c2055020cf951320833d5490631bb988408c35f5114530ddd44414c35c63d4142be983328837442d45409f583525075d658cb30b758c404436e52d0410f6181414c3d953840109fd89508c67e65d0830d7d4e314867e6495131d7145314c27e6294031b7583438ca7d6395321b759440cc25d6314142f6d9130482f66114c42cf152424c35c534c210b798e408836d5210b41cf55140cc33c6355321b758c40842f960d46439fd96329027d6015232b798f540439d5450b309f5964310b7462145409f987540c2df6350842cfd5241443ad4210b40dbd9521c835f5394f10e718d4210b6e5450842bb58850d067e64940309f58754cca7c6154c42d7950324c35f654c730bed81324833d54d0f21bd597218867f60553328f59053c833d5490b21bb98843ccb6d65cca32bed81419039f54d0130dd547401027d6494620d7d4d435027e60d4d41dbd4b32502dd640c930d798653083db42d4130b758e404827c6254440b7986404c36c5490b20d794f430c2dc6350b32d754c211027e6214d419f58e520433c5490310d794e420c35c4354032d754c530427e60d5131cf95330043ad4210b32dbd4b20842de600c5309d587548ca7c654c7209fd8953486d86050530bb1894350a7d63944109f586548cb746454420be58021c82df6348510b7d9641cc2df648c530d7550438cb5d6395130b798c54082de6390a32d794c32c86dd6190930d7d8f5050b3e5410a32f5987304427e6294331d758f540835e530c510f64c220082dc6150d309f992508cb754354642b7d8d218432d5448020ddd89511037950142329f586544ca7f6255132cf18e540cb775110540cf989540ca7d60151329fd9532903766115032cf553320835f52cc310db54852d0f6f5294843af990328c39e5410c32be580320833d54d0310d798f54cc75e5490f30d7949320cb76514c630cfd8d54c867e65d0b30b798c519027d6588010db548208433e64d4c20af590329074d5354840d754c43d0bd95390040cf151434c2dc65d0530b6582524c3e542484219f181539075e5350c30decc9500cb9d6390140d794b30c435c5454c20d798c54843766194a31f6cc930883765494420afd91534435e53d0c209fd9743c83755190420d754e328427f6510c30cf55143c86df6348421be58043cc36d5248440d794e420827e654c941d714e43503af5450b20f5107308435d5310c109f984538827e6094432d74c5500c6ee6210020be583310c3d653d0610db54a310427e65c87309f18951903b74250441af5924
  | 31 => 0x50530b719151cc2dc6250d30dd984540876e5210a31b7d8d42c827e65d0a308f992528c67d6550f20b718d42902dd6190f30bed8f204827c65d0d109758c548433e64d4e21d754f510827d6114d42d718a530427d65905209f18552d02df648c130be5805110a7c6590a10cf95242042de65d0130b718d210867c65504309f58154043b441484409d195214427f6255121d754c31c427d6195020f354a328c67e6510a309f982548cb3d5450b21be98041d03774294432cf15042442cd6210c32e795153042bd640c941dd548515027e6495110f5484214c37651500409798f540c3d65148530bd58231886dd6348730d7d8d52d033d5410020bd98b41886bf6250441d794d420c27e60150329f98b535076e52cc830bd98720c427f6454730dd545410827d65d0e21ed9864250bb75190140ddd5041486de6088530db15142c827f6154b40b7586324c27c6354021e750841cc2ed6210421bd58452cc27c6510421cf98954c867d6195110bdd85404835e544c3109f5875350a7e650c940cfd5220442ed6290520d754e41082f560d0541d794c320435f5390d429f58f514827c6454221d754f218833e5494c20d7180534867d6494030bb58b41482be640c840d754f42043776155120cf552300827e6094f219f582540c73c6155020d798c54cc2f860508109798e5010af763c86219f58e500435e6394042d794a514c2ed6214443bd586208427e6590b109fd95100436e5248410db94a420c73e54d06209f58a54c43bb42d0140cf95143043d8404c220bd986300427e6510c20edd07400433e5490710f3c8730c827d65104309f986508cb7960951309f592500427e6550e209f19543042f46150020f5d8d314867e63d4141cf150414435c654c110d7d5330c437451d0520d794d41903b554440109f189548435e538c710bed815150af96014841f610530483d84394032db988548c27c65d0e20bb98852102f960d0840d794d420833d5454321ed19151103d7414c210d798153882ef634c8329f59442082f9600c840d754e311027d6494b30f558452cc27d6510f10975835350b9d5415330d754f208827e650c620b758321cc2de63085309f98a54cc67d6590910b7592314c3db634c220f34c3208835e6314c21b7990404c2f86050a40be580328c3d451c85309f195434cb3f54501309f994434c6be62d0f42f994a51103766114142cf950310835e514c030dbd89544835f65cc110d7d935350b5f52949309f594414c2de6394321ddcc851503755114720dd182510ca7f654c521b7193214c27c6355121d7d905350b5f544c110edd0621d039e53d0f42af590328835f534c220cf94741d02de6315210d754e43883da64d4130dd946218c27d6494031cf990548c6ef6250d21dd546200827d61141429f59632502dc63509319f58754483
  | 32 => 0x9f996424433f42145409fd9150ccadc6350b109f987540836e62d4f21cfd5340482f661cc310f3908424c33f54d09329fd96420cade6314620cfd5254443776394642b798e50886f4614ca31f694f409033d5415030fad89304835d6014d42cf953424c2dc64cc5309f19632c42dd63c85309f58b544c36f65548409fd85529039d5450330dd549100427d658ca40b798a524c2ee628c520f3885214c35e538cb41d7953308c35c6194e40d758f540427d6014532b7993328ca7d62d50309f185548cb3e5450c20b758f529067d6510b319fd85544c2f66194943a759052cc35d5410c32be580520c73e5410b21d7552538836e5250831d798c53482df64087309f992520875e65cc530dd14951102f66190921d7d4852cc3776155110d754c31843ce620c831d794e32482dd6315220be980329071e5494c10d714e31486dc61509309f997425075e6254c20dd54731cc35f654c320cf990528427e61942429f992510867e6515131b718d424c39e5350040db996424835d53cc310b7d8931cc2f96090410be58221042f560106109f99431c833e5410621db94e52042f965c8220de597409039d40101309fd9742c427c65d0e219f597300835d63d5221bd984510827f6454e209fd9531d033e5450b31b758f54842ed6214031e755253082f56190942edd81411067c6510f20bd584329075d5388020bd185401023d6595032cf953410c27f6354740cf55250c87ce524c010e75905350a7f6590010db549310427d6294043dd546318c37654944329f58452503d631485309fd9432d027c6510930d754d32842df6350b21cfd5041843cf634c832b798c501067f6254043bd584438867d6094c21be583214433c5448110dd544510833e5450440b798321cc2f46150230b798f521033d5490f30b718d428863e6515110d719153842f5618c210bed81314c33e62950329fd8554cc33e54d4f219f983540835d528c831d7152320c6dc6348510bd185328427e6510630cfd5141442ee620c020bd1855050a7e6510130f3d48214c33e54d0320d7192530c33e5410721be18142c43755114642b799721cc27e65100309f195434827e6394020b718d21842df6354910b718d420427c650c810b7d8d41cc67f650ca10b758f414c27c6454d21eb59321c83345490510be583218435f6454c20edd52104427d6590c31e750842cc37761551319fd81539073e54cc020cf54f421067f6550b30d798a530435f538c720be582419027f6054f41dd98e51082db654c220ed8c941106de6194530b799742cc2f66190b419fd95320c2fa6014b31af58a4350e7f650c841cf953430427f61551319f582544c2de6510730dd944410867d6195030ed54540102dd63d4a10bd98641043795014231f548530443d8424c120ddcca51083745148520cfd5254cc2fb60
  | 33 => 0x8632086bd6090440d5547300837651c8440e7951424c27d62950309f58a544c6f96014c41b798e54487f151480209f997211033d54907109f994300827f6355310dd0c9510835d6314141f618b504c2f5610c941d754c51082f76154132b719021cc27f6550630f9d4921c42df6250730bdd95411075e53500309f99542843ce424c120dd584534875f53885219f990504c6fa6008530f5185544c37762944409fd91518cade648c9309f18152106dd61d03309f99353c873e64d4f21be58032d065e63d4810b719131cc36c10548109f195434867f6054810af191211025d63d5020f6191304836d524c010d79805350afa60084109fd94420c2f56110f10dd5815190a7d6550730bd99231486ee6210c329f58e54442df654c210fa54a40102fa60d0f40bd98442c875e538c621db95242c833e6414f20e7153404c35d53cc210b798c521035c5450f30f510621cc27f6550c10d794c329035d54cc210cd15141442f66110320dd14a21443775210410bb58e320cabe640c9219f596540427c6054e42b75824310f5f60d4d21cfd86540836e52d04409f58253486be64d4720d758e501075c6355320cf55041042f96090710dd48550086f56290441b7d9151cc33d5415032cf993530427f654c6209758c548835c54cc1109f194410c76e6214f209f996214427e6214f10b6580214c35e5390610e7553424c3ce620cb309f196414c37554d0521cf590530827d6590010b7992524c25d63943429f19532487d6618ca31dd587538427b6548020cf552510cb5e5350020af983411076552d04109fd8152cc73e65d0d429f191508c6fa60c8510cf953430825d6594c209f580548c6dc62503309f596434876d52d4440d7d95300c39d4310f41b758c509075c544c0209f98c544c27d65d0420d71835350b765448421b798f52d06de63487309f98e511033e54908208f99353043796015330dd90e51102fa60c8610be58221c437651100209f58e540827d6094f42ed90440c427f65884409f98b54cc33d65d0e439fd9530483ce6210330be980219035f534c5219f596540c36e6215032db58b54cca7e62d4c10cf550408835c544c320bb58642c835d6315021d794d328827e6094442d754d410833f4294642b798c529027e6094642bd584328827e65109309f98a53d06fa6010e20db54a400435e5314840b798c52043766394440bb58b438ca7d6494332d7591530835e6454e20cf951420437763d4540fa94a200835f544c020dd545210c3d56190b30bd9875390b3d62d5110d758c504867e65cc940dd94621cc39c6350b40e75533008376518c020db54a21043775194740d754f518835d5314e41bd58742443da32cc130af99032d06bd64d4032f594d100433c5414910d794c52842bf64541319fd95430c76e52d0b41af992329073d541511
  | 34 => 0xcc2dc6350530b7d8d21042de6110530dd98453c42dd6310130dbd4a528c2dc6510b30db54a311033f5490620d754c43d06be65d0d42f5d47414c35653544209f99353c436e5450b209f5964208274654c5219f189548c35d53d0e10b758c400433d5448420f54c5214c2ec6250f21d710c524c35d5390a109f992500ca7d63d5320d754f4310b5d5388440cf55120043e74294642cf15342c42f563105218f990528427f65cc640cf94f43d0bd74188530dd992510827c6255330d7d9253882de6488730f3d0e320caf46154940fc14740502bd64d4c20d794f308827d6550830cf951420833d62151109f58a548c6fa6094d419fd9150c87765314540f994921087d960105309fd94410873d43548439f993504cbe521c8110ded9510043d6538c431f5947300835e6314a10ed504410c74d5394840af99351cc27d61151309f99421d0375514c630c7d53304427e63d51109d984540c37562d45409f980530867d6508630bd597410427e6114c209f195418c3d55310610b7d92214c35e6054e40bb98b43086f965c4210d7597300837651d4032b7d8d214c35e5390440dd58851502de6090530bd98453c827d6115132d754e439076d62152209f59621102dd6010c32bb58840443d55354420b798242cc39d41d0330bd18141443b53250441bd986324427e61d4132e755243cc36d6215210ddd465150ef66410521be98021c42df6054930d7594430cadc6388530dd54621882ed62102109f986539036f6154840d754d31103b652504419f5825190b6d52486109fd9421cc376538c431f9d8931486dd6590330d714930842ee62d4c40db54b100435f54cc030d718953102f9658c220dd14a21c43e52108720d7d4e53c873f5454910cf94d43d0b6e5290a41b7d81544c35e53882109f191500cafa600c941de94d300c2de63d0730bed81425035d544c310d7d4c32c42f561909409e980530833e6255010dd54d51102dd6390a32d7d51300439f5490530bb988548c2766194b43db94921102df65503309f58a539073d4254041b759632cc2de620c530cf55341082df6550b30f594e51083d441cc010dd546411027f65d0d10afd91514c35e63d4a109f58c504867f6550821d7d52544c2de6394142cf99054c827d6494c21f3508424c27e62d50109f995328436e62d50329f988540c3ad52d0b409f994410c67e62d4c20f6d05308836d5208440d7553308c3795014221d7d48324c2df6150f309f98254ccb5f54d4d21af59321503ea628c220db549210c33c54501309f58b54cc73c3255032af99321482dc6250c43d754f319035e6094c10d794c318827d60149419f98a540c7d651887309f19543c829d640cb30b5d85544c2be64d4321d798f54cca7f6154810cf55042042dc6350531d754e320435d530c821e7d5254cc2df6348640bd9
  | 35 => 0xf6355020cf981540ca7f6510730cf990548c35d6394221cf95243cc6f66190f31f354b30042f5618c010dd90d5190adc6354542b798f42ccb5d53900409f18d54c836d5148020f354f208835e5390c30cf95241c82df6154930b7987430cb9e6414b30db58a544cabd6414c10dd19541442dc640c7309f587544c35f53cc020d7d8d538835e52cc020edd0b515037651d04209f18152d0f7a51940329f18552102ed6288421db949100439d54d0e32cf580544427f65508429fd8d50d0b7451d0540b718d21902fa6010620db548300435c5388521cf553418835e53c8420d7553300427d6294740dd98e5190b3d5490821bd185328875e654c120edd52214435e504c0209f181510cb6e5284010b718d504875f32542329f58e544cbce5214b30d794e428835e5310810db94821043775194720d794f20082dd6550730dd151510caf561cca21af590528c27f6590d109fd85520c2dd620c7309f584540c3ad42905209f99352042dd6310310dd94b515027d6510b109fd8d5110ade62d0330ed95041043786154032fcd81414433e5450a10db94942906ed62152109f19530483745148540d798e50d0b3d5410e21dd987530827e62951308f59252c43ad42109419fd8d521033f62d51109fd9743882de60d07309fd855010f7a60152109f196434867e65d0d329f595414c7b54110730dd546218c27a60d53319f98a5190eed6210621ddd95510ca7e6294e41e7590320c6de6310220d7986530436e62149109f19532507776454432d754c32083b94010230b798b54cc2ee62d5231d7d4e530827c6454f21cf153434c3d7414c0109f992530cb746094642f658054cc2dd60d0d439f596420c27e6414d20bb18930c836e6215320b758c42cc35f544c220f658e20082ed62d0d32fa181214827d6194e209f996328427f654c410ebd4942d027f6588010b759252cc2de6214730d794d43883d95348020bd586200435d54cc030b7d8554cc33f43548439f5865210f3e5450010d7d9730482f76550710dbd89520433d5450c21cfd9554c867d6414930be580418827d6594c109f98251d0e7d6194b30ddd4731503b960d0b40dd586544c67e61d5220b7d8d21c427d6508530d794c410427c6054f219f195428c2dc64cc9309798e50043cd424c120bd98732cc7da6010530e7551320cb5f6554c409f984540433f6455331d794d41843f04184010bd185324c75e534c310d794e430835d5350e10b718d420c3d661cc310cfd5142c82df648cb30bbd8931882df6550930d714d314873f54953219fd94320867e61d4f20ddd46519037651107409f583548cb5c53cc510bd584408835f54cc2109758f540427f61543429758f548873d63d5110cfd50324427e6510e21f554731cc35c32944319f191508cbd66384110f6991308836f5294b41b7d9031
  | 36 => 0x5132b7580320c67f650c620af590530873e5490c109fd8554c83775354642b7987320cafa6090e20ed94741d027e6494231ddd4e21086dc6255330cf590504865e6314a10bb98831c835e544c110cf982540436d6214e21db98b53087da544c120ed50a41106dc6488730b799321cc3e95244010f5d0521cc27f654c421d718153902f561d0a21d7d5053487d932cc130fa90a304833f6455021dd14e5190abf6454930f548530c427d6395021cf58654082f56190e41d7d4c434867e6510910cf58c54443af54509209f196434437960d4f20fa54a100437960d5320cf551438cadd63d0831bd580410433654544209f59432d027d6315010cf99253443eb60485209f59053c82f661908219f5865290e7f61549109d58753082f76150921b7189514c27d6510e20d794a31cc2bd61d0940d7d4d30043cf5288530cf550548c2fa60140329f597424c2dd6395121de99630483e631487209f592530433d5415121b758c510835d530c410f358b438cb755114620cfd52414833f5454d10be98341443cd434c832be98341842dd6314a109f994210c37960d5330e7d05404c2df6348430b7582424c27d63d4540b7d814310e746550510b758e40082f56190b219f59643c87e441485209758153042df6508730d7d53438cabf6448640b758f424caf960c85309f590504c77a60d5230bb18121482bc6454132d794d200427e650c841d714c31c876c5354810b7597430ca7f6510c20d795130c82d66110130d7591538835e5154530b718d21042f561909329f596210c2dc6348530dd945210827e65d0831bd185204435d534c810dd58754c82f56110b419f58254482dd6490530e718e540ca7e6590931ed98542106f6610c831ed50d41107743254432bd18532042f66114142db949210c27f6590f21dd991511036d5448020d794f210c39d4110530b558432cc33d54d0c21be597308c33c54d05219f58c540835c65485309f580540cbdb314c120f60c7304c33e6415220cf59252087d9538c220f54c2104425e63150309f58e511027c6154f409f587540827d61943439fd9532c433d5494420b7d95300c27f658ca10db94a31042f56190b20af99052cc3b76444010dd58e51102de64ccb30d754f408835c53d0942d594e511036e62d50219f18d50d0b5d5350a10af59321c82bf64541219f98a510c2dd63d4b41ed10440842f56010621d794d41102df65c8530ed553100435e52cc2309f5835150b796494032bb58a31887b55410521cf18854443753294432b7191324c27e6114f20d7d4e43503355110440d754e32c837854940329fd91508875e53d0e20dd94d310c7d960ccb30db10d520427e6115330cf94541107d9214c220cf55243c873c54cc5109f594424425f6548530d754f329027c6508530ddd85544867c6454f10dbd53200827
  | 37 => 0xafd9542d033e5490821be9805110ebd6414430db948421075e5154730db54a401033f6455332bb592204833c54cc910ed50851503ea5290040fa50a304833f6395321d7d4c43c83db43cc130d79945350abe640ca10bd58632c867e6014542bb588540c7da42d4130e7152414c2f561d0b10d7d9530843d73294432db54a21103da600c831dd8ca510ca7f6054a419f98754043d653c40109f59431883766114c209f595428c67f65500109fd9742cc6de6550730bed89200827c65d0530bd986328c67e65d05219f594410c6dd60d0b30b7597300435e6314f109f98753082df6350b409f185544839d54d0c32f5584320c67d64d4f21cf59353c86dd6014b30dd54b515027c60553319f994404835d534c721be58032487d5514c020dd94521882de6388530cf55340cc2fa60c8530afd954210add6390b30f64ca500cadd644c7309f18951d0e7f6355210dd54b10042f66110c419f58e5090bad4210832be58331cc2de6394341d7182539033f65500409f197424c73e54c84109f98f540876f54c8220cfd05509067e6315120d794c41902be640c821ed990414876d524c440db94b51102f76150020cf55053c876e52ccb31f94c521c82fa60cc520dd15121c435e540c831ebd4942502df62545309f994410835e3254031b758f42cc27f6055232bd58b318c67e6115021db54b42042de6110330b798e5010b7551942429f98e521027f65d07309f18154886dd63d4640cf951430877663d4540bd986428c73f5410310b758e40102dd6194b309fd97428435e538c821db98b54042fb604ca30f3948524c35f52cc210d7991530835f6154e20dd98c515027d60d4d42d7585531035d53cc010be980530867c6510010f650f304c35e530ca109fd8554882f5610c210bb988511033451901409ed9540102df644c730f54c9510cabc644c9419f99432842de6390832bd587521027e6115020cf58654c877732d45408f59053c87766115010c714f4350b3e54c8010f594d310c67d6394840e754f409023d6494910b758e408c35d5310c40b718f21cc35d3254032edd0d411075d5314f20b758c400c3b65494420eb951520436d52cca41e718d429073d5490a32b718d21c42de60109309f584535027f6588740cfd91544cb5e63d5210be9805390a7d6494b31d718d54cc39d640cb30cf95331c867f6354a108f990504873f65550109f98f52443d65114730f3909320caf6610cb30d7149300435e53d0f41cf553428865d6014d42f694530883cf624c930bb18142482f6618c931d7d4e314827d6394820d754e31442f661909109f98251d0b5f6550b30cf951400835e5350a20db14b208433d54d0e32b798442cc37552d0610dd982510caf56114c20d7d51304835e5490c439fd97320427e6590a10b798a414c27f6508630bd986428435d639
  | 38 => 0xe31c875d53d0f42dd98654c436e528c440b7583328cafa60cc920dd54741c836c520c940cfd50424435d53908109f18154ccb795014342d754e32c869d64c8530f64c220443da614c220bb988434835e64d4d219f995434875d53d0c10f5d8d318875f51cc120cf950408c33c54d4910b798e404827c654c1109f59543882f9600c910bd58b314c76e62d4c10cf55021083774194010bb98841483d930882109fd8d520433d5410631e790541cc27c6054a419f994215027e62d5210d795253042f7654c621f658354cc2f76150040cf953200835d6254c40b7996424c33e5454c109f195218c3b551d00409f18954442dd63943419b98b53042be64148319f596434427d65504209fd81540436f5294840af99252c427d65108309f982529079e6390140d715243cc27d6494431be580328433d6414c10b798a324c27e6314c219f597325076e524c410be582420827c6550f219fd8d54487b66410610d7d9521cc33f54105109f98253d073f5495210d714c43487da600cb30db98d521033c5414d10af9864250b3e6355321dd90a510cb7b54540329f19531882ed6210130e7552530427e6114c10db997214835d524c110bb588400437651d0040cf581540cbd8214c220f558432cc2dc6350a32f6d87504c35d63d5231f64c120083db624c220cf952428c77441141219f99454442ee6210210e759321cc37451c85309f98652cc2dd65d0530be58032086f56448510b718d210c2f56114f20cf55152042dd63d0130cf953438c67e6414e10f6d01300433d5410832cf55331042de644c5309f181528c67e63d50109f98c54c835d538cb41ded92500cabd6414321bd586435075d654c1209f597210c2be640ca319f194300836e5288020d954910042de6214530cf55043ccb5f5314542cf150204435d65cca32cf952430827f658c020d7d4f424875e3214530dd109510835d5350c10cfd52544cabd64d4a31dbd4a528c67d6590720cf951438c6de6114b30db94d521027d6214543c7951530837661d5020b558440cc35d60d4d42d719253082dc640c930d754d408427d6294f10b798454cc33e6295020dd15241442be6414930db98b548ca7f65d0831db948211035d6394021cf950430c6bc6050540b7984324c35e54d4d21bb9884310b3d6395020dd54441082be640c9109f992528c7b54250441ddd465110abd65d0e43ddd95318873f5495032b7d9441cc31d54d0c32f5d8531cc27f6590431af98743d0a7e6014c10d755153843db324c12097d9530043b64250441dd992510cbdb40901309fd91510c27d61942439fd89511037551d0730dd0c951103755354642b7592524c3754394432c7551530433e54d0c21d794c42902bd640c841cfd53404c27f650c010f348421cc27d65d0821bb988509067d6595032ddd80515027e6494620
  | 39 => 0x827f6154e20bd98450d0bdb3088020be982424c33f65508419f9865390adc6150f30db94930043d6214c1109f594319035f5454e20af59240102dd6190b30f694e20082f66190931de980540c33d54d0b329f984548833e5490220ed945401027f6154e42d754e43842ee6214810bd18540843ad52d08419f5825110bb942d01409fd9542843d8514c120af987409027d6510c32d754c42082f6610c521d754e418827f6590a30dbd48214c27d60d4532dd15141443d74354432db58552103cf6350842cf953420c7745188520f318d42c83754294432e755340cc33d548c420ded9530882ee62907209fd8553d03756114910f594f108437451085409b98b54043d7518c530ed10621103b641901108f990520427d65cc821bb58843d0b3f5448110d794c438867e6590831de582534433f5450d3297d95310c67f63540419f195438867d62d5230db94521086be62d0d429f582534833d54102309f191518cadf65d0730cf550408427c654c5209f58e544c67c6054c419f59353883d864d4130be982429027d6548730e7d00404c35e6315032ddd48515027c65c8540af191311027e6295131dd94e5190bd651885309f594310427e65d0130f610130482ee628c2209f98c5050a7f654c941f5d8530442f96090a309f59432d067e61943429fd96400c35c54cc010dd18554886be64c84209fd9632102dc6354b40cf95353083da314c220de597108439c544c1109758e50c87e521c83109f99353042f56288510dd9815190b7a508c020f5d44214c3d62108530f3c85304825e63141219f997315026d6295131bb189310839e64d4730f6d8d30482ed6210310bdd85439073c5410110bb58a400835e530c8409f99630443db404c3109f98053c876e52900109f996325075d5350e42d754c41082bd64cc6409fd9442086bd6408540d754f421033e54ccb219f594420ca7f65d08309f596310c3bb6050540cf551420c6f46050710d758a539035c5314142db94a210427f62546309f98650ccafa6010820f58ca314867e62d5031d798d50ccafb6544010af59020443b56115110d7d0d500cb774394432af590324833d5350841cf152304433d5410a31bdd85408c3775348710d754f321077554d0621f5d46514c2f56288421b7994214c2f9600ca319fd96430435e53cc7219f997314879e53d0040cf550540867e6550f21af59020842bd6494d108f590530835d53cc3209f19443c43374294642f3509320cb7551480209f986544827e60d4810f615130883d9544c120d798c5050a7f6454810f3d8d21482d56190930d794d408837551487309f189508c7d942d4130cf953210827e6494410bb988404433f5495021bd98632c43755348421b759052cc3e75188521bb98b43886ec6254143d7d51538433e54107109f986540caed628c421d7d4
  | 40 => 0x2154021b7d96414c3da6094e209f98e524427e6494f20bd594418873c54d0130bd584420867f65d0e10afd91311025d6394221b798e430ca7c6510020f5d4c41487d8534c2209f99353c833d5408010b718d424cb3d5415220cf99054043755188430f554521cc27d6494831cf553424c2dd60d5330f5d07308435f53141219fd9642cc76e5248310de10a500cbb561d0841b798c21cc35f538c9219f18d544836d528ca30ded95200837662546429fd95300c2f661082109f98f54c835e53d00309f196438875f534c120af99232106f66108110d759530443cc6348520be181525067e6094b419e18154487756195110cf98554083745294440dd109510cb6c4354840d7947300c37661150309fd8953103766254432e754e41903b452504419f19153082de6194b3097d8d52c435d6394020cf952400c35c538ca21dd94f515035e5390e20bd58752d0ef561d0c41db94b100427f658c8109f1815290edd60d0e439f59532042de6314440d754d20083cf6350920d7d4f308835f54cc110ee982419035d5310f409f58b54c427e6494221cfd954310f3d6414c21b759032cc27e65100209fd9442083775194643bdd85428435d53c86109f58e50087cf30c8220db54b428c75c53cc0209f597420cbcd5214930f3d4b424c2f76150d41bb588400c33d54153218f993530833f54d09219fd8d50086df6350a419f99631082dd618c831f54c1100433f5495121de94d30483f16090710bbd895050e7e658c540d7983534877a60d4c109f5875250f6d6215120d794f400835f6294e209f19542c427d6094643add89411067e6314810ed15141c427c6510520dd94421082bd648c940bbd914210b3d54cc810be980321067c654c640af993218c2dc64c8730db588538827f65504219f191500c67e6114143dbd4a5290fe551c80209f98e529067f6510c31cf990520435f5394542cfd5052442f661d0841be980421027c62544309f997434426e6215030dbd8952c433f54d0d32d798253903b54110540f58c6214c33f64551109f58252cc6bd64d4432ed104400431e544c010f6d0e500ca756114142d79514310ede61903309f597414827c61540439dd95100435d5314d429f582540877561d53309f9875050e7d63d5021b798b504c35c53cc210db54b421075c65487309f58e520873c6055010db54b32d075c53d0921d754f419027d650c820b7994414c35d5350810b7584524c33d5454c209f59441086f661d0f41d719253842de6195130d798c53082f5610c841db18152042de6310832d794f31042dc6354910dd597318c67f6054843d794d52042de600c730db54a320437a534c2208f997415027e6014543b7d9231cc27f6254743bd996314875e5414d21cfd5341c42f461501109f58e51d0b5e6315220db98850506de63943429f58453c
  | 41 => 0x1109f99443503b56414540bd984325039f41d01309f99621d03775194532cfd52414c27d658c810dd18251102bd64d4e219f986500ca7f6054d20db94e320cb6e520c010cf15341442f56110a319fd9431086fa60d0b409f58a50d06f66188210cf18954042f96010f40f388521cc27e6294243dd14d51102f464c4210be980324827e6214c21bd98642c43d960d4730be5805390add6548730cf508515035e5310a10d794c310875d53d4a10cf550400427f61542429fd9420042f661cc921b958642c83db614c2209f584548cb6c5290941b759231cc27e65100109f58a54cc2be648c540ddd45215036c6394840ddd47414c3d9314c220d6982538827e6414e20bb58b414867661d5020ce951500cb76518c4209f983540427e64141219f592510431e544c020d7147504c2f66190930bd58430042dd62d0d309f593524c7755394420cf55230043775194430bd58642d027c6590f219dd85544c3766094440cf55041c435d53506209fd81544c2f9600c931d794530c82ed6490842f5487304433c6395020d754d21902ee6210920edd4541d027e6494d20b7993524c33c54d05319f5825110e7f6355010af990215025d63940209f59353842ad64c8720f994a21c437a6014c219f59252c42f6648c6219fd95218c37561d5020b718943cc33f6095321d7d835350b5f54cc230cf550400c27c6054642b7d95300835e53c86209f995320436f5294810b7d9531cc2f56194b43f98ca510ca5d6014d21f6d81544c2bd640c540af990328873e54509309f98f540835c530cb10b7983314c33e54d0630db94931102de6315021afd9152442fa6014843b7193328ca7d6510f209fd96418833d5250040be583434c27e6590b30dd586544867d6590f109f18552cc2dc65107309f597430867f6550b31bd58432482df6350a209e58354cc67e6494f21cf990530836f5294910dd984548c35c524c930cf990540867e6494832d758053487f351d0140bd584424426f6550842cf55241cc2de6088730be98043483d551d0730d794c41843d521087309f9825110ef46155130b758e5090add618cb30de582524427c62550309f58c52c435e54cc310f6d41404c2f96010b20db58a544c6f96094d41d714e32507ea5248020bed81438c33f4254042d754e321027e60d4941f5d87534873c5410d20cdd5041842f56310621b718d420c77565d0610bd18520c4376510c7309f99630483755114543af990324c6f66190810db548320c67d6590831af993528c73d62550109f98e508867e6394720be980428c25e6394321dd185544c2bd64c8740d754f20843b76250441b798e418c7d530c4210d794f20883b66050441d7586539027e6414a10cf552500cb7661d5032bd98642902dd6014730db54852cc37661d5231af993211035f53941429f98454c8376
  | 42 => 0x6591308827e62d5310fa94a100427c6354642d7153300835f5310d20d798d500c67e63951109f994428427d64d4c21b7582514c35c61d4d42de195304835e540cb30f95864210b7651d04219f588538427f65900209f98e54887e64148421d794c411027c6354341bb98b30c83765454420d754c538867e65d0f10de192500cb5d6314142d714c325035c5494c20af59032cc6f9600c810b7983324c35e6254e10dd98454082de61d4130d754c534835c5350d42cf99054cc67f6550c42db548310427e60d5231ed99041042ee62d0f42d7153534873c54d0920b758352cc27c65ccb10af99032c436f52948309f583534867d65d07309f9825210f5c54cc320f6485304827e650c7409fd8954cc7e65288421dd547310827e6315210bb988404c2de63d5221f6d8b504c2be640ca409fd94430cb5d6194e209f195434c27d6590730ed546419033d5488420bb588518c36c5394810d714b504c2ed6290e42db592520435c544c0309f19151083d53188530f554c41042ee62100109f596428435c538c921b719331cc3b664106219f594430c6de6190530d794f518833c54485109fd91500c67e6590920eb50f4250b9d5450930dd54521903776354440dd10951103d65354440dbd4a52cc35e5348210bd986434867f6454c20ddd53414875e6154e40f3548320c67e650c921ed993214867d61943429fd9631c827d658c440d7d4e535073d54d06309f98e51042be6410540ed90d411073f6455232d794c200435c548c932db98852c435e53cc640db54b421035e6315030db94e521035f5494c20ed54641102ed6490920db58854043d561d53309f986534833f54106209f582521067d6194f42cf55153c867f6055331fac8630483da214c220db549320423d6414810eb50841482ed62d5231cf55043cc7756354420d7d0d5090ef9600ca40db58d52102f46154930bd58e314867e6115110ed14d411075f6354720d7d4f504867e6115132d718a53903b541107209f59732902dc6150b30cd550410427f6510420e750c434c67e65cc740dd99451503755110440ddd92510836c4394810dd14631502f9600ca21ded4250c877565907109f583524c67f6055032e750040cc33e54d001097d8d544cacc6254530d754d40042fa6014a43d794f320436e52884409fd95400833d54d0610f5d45314c2dd63d07309f993514cbce434c832f6d05304833e5414432b758452cc2ee62cc521af990324c36e52900409f98054c867d65886409f58854cc2dc6350b30cd552510cb3d544c4209fd96410876e6215232cfd51424ca7e65c8430b7994544c2be640c810b7189544c2bd6414032de54050086df6350941dbd4a524c73f6455031b7593504c3ce52cc010b7982324c35c520c5309f19532843cd53c8020d794531cc3d631487309f9845050af56284
  | 43 => 0x500cb5e538c431f9586424827965840109f593534427d60150219f18153d073f4294740bd98754cc2766115010ddd4651cc27f6550420f34c832c867e60d4532d794f51082f6610cb20bb597328ca7d6095321bd58720442dd638c1209fd9541482dc6590930cf95253c86fa6010520d794c31c435f54cc0109f58253d067d6155010ee951500ca7e6414520f350842cc2de60907309f196315035d5410f30d754e43043d93088310b759740cc2de64d4b309fd8552d0f3d54d04308f992524435d530c4409f98e5090abd64904419f58c54c435d534c8409f196325067e63145209f185508cb7651504409f987548cade620c730de145500cb5f43149309f58c5050aed6290d42f514c414867f6354910db94b42042df62551309f99252083765044010d754c32882dd63146209f99742c42f561d5232bd99041042ec624c521d710e52cc33e5410720b758a54cc35d63d5232d7986531035c6254e40cf953400833e5410c30e755241cc27c6054e21af58742d02de6310120dd945310833e5410f30db549219027f6510c109f197328435d6254e20d7150328c67c6550931ebd4a4250a7e6495132e7901404c2dd60d4d42dbd4a214c2de62d0530ed105219027f658c910dd54421c839e5390440b718552cc27d63d4a10f6c87504c2de6590b30dd10e5190af56114e42af99053043745190140d7d8d54c827d65509109fd81528c75e5310010f6982424c2df63545429fd94420c67e6510831d7d5330083e75148720cf55130082bd64080109f19541882f96010520de58352c427d6494910d7d4c314873f54d05319f19632443ae54948109f59053c87d93088010db54b300435f53cc7109fd85534833e5414c209f58854043745188540f390b30482ee6210310cf15142c43b752504419f997424c75f6354c21fc8c110042bd65d0a41f698331cc27e60149109fd95321027e658c640d714e4250a7e6510932f594431cc35e538c010f6d8130c82f56110120b798f518833f54cc510cf550540c67f6550930eb993210876c5250941d754f43d06f56448710f6901308827d658cb419fd94438833d5490c319f181520c67e6494c10db549328c3b454106109f99442486dd6195130f354852cc3da644c120bd986420c27f658c820d954b100427f63551209f587504cbd561101309f99721482ed62d0f20dd54e511035f4314943d7d4d32486ee62900209f5805150e7e64948109d98453083ad4210920ee952200839e4110130db54a328c6ee60c8520ebd0f4250bd960d0d30b798a424c3ea5244010bd984408833e54d0721dd5445090af66110f31bd587304427d65d0a109f98a50d0ebe6414f209f98253d0be651c8720cf590520439e6410d30b799232cc35d524c310f3d4a324c37551940329798f528427f63552219f597430c75d65cc230f
  | 44 => 0x27c6354620d794e20083355494420b719542cc2de6495130f5986424c27561d5020cf95042c83774294642bd58432cc73c62d5110db98552042de6390020f6145308827d64940329fd95420c36c4394840e7150414c2dc6588730b7195214c3746294440be580320c2fa608ca309f98e510867e658c841bd18543906dc6355320b758c500876d52d0b40dbd8652102f56190a419fd89500c76e62d4f209718d52d036d5290810dbd0d520437561152209f98054082de63142429fd9543c837662d4540f5d0621cc2766114f20cf553320cb764394432de54050ccadd6215330bb988400c35f530c9109f58b544433c5490530b5d85524c27e64d4d209f99443c42d96010930dd59741906f661d0c21ed95341842f76150810cdd08515027f6254e10db59721887655148020cf55341043cd53548409f997328427d64d4131ddcc9510827d6214c10d718d51c82de6390530af582419035e53cc310be980540c67c65080109f195428439f4150330f3d4a52cc35d53c84109f18d529035d5308640b758c40cc33d5494810f588530c42fa60cc440dd99631486dc63507309f195434433d65d0240d75085350b6e51c8720e7d0f424c27561150309f595428435f54cc220af993214875d544c110e7d0a424c27e6590932dc946500cb9c6350841d7149304435e5494b30f9505210867f6550e209f99454483d56114930f54c521cc2dd6590730d794e410c36d4354810b7189414c27c65d0b109758f520437752d0410d7d4d32c827e650cb109f98b540875e6294e10edd0a41442f6610cb21d795153083cf528c9329798c505067d6550f109f986548c3776394420dd94640082ef6254d40cf552408835e53cca409f59643102be6414f219fd95404433f5410520ed90640c42bf61509409f984504ca7e6590620db94d320cb5d6114d21d7186538827f654ca109f594329067f6454c21d754f31082df6350832dd987540433e5410c32dd9452104375518c720dd544510c3d96390040b7984430caf661d4c40d7d50434c2de6314141b7d9221cc27e6590d219f58f54843b55494432b7988544c2f9600cb10dd59621c427e6094a43f5d8530c427f6354841cf153428cb2d54548109f996414c75c5314121ed50b51502be64d4e219f58e529027e650c1109f58a509073e54d0a20d754f200435d5390e42bdd8542887cd53548109f99632d027d6550c20bd584424c67e6494031bd592214427c6254d10dd145315039d43d0930d759730c827e650c010bb18940482f66115230d714f50486f46150130af990320c2dc6388730d755153043746054642d7d9553902f66114843bd185400435d54cc310d794e410835c52cc210af59020c427e65d0120cf585540cb7553145409f58b538426e6295131bb18943883b56350441eb55120082fa608c820d798d
  | 45 => 0x90c10db54a428c27d65cc910d795330c827d6215030dd945500cb5e5455330e750441cc27f654c6409f58e544c375518c020dd94741d02f56114343d7182538827d658c620be98031c433f5414d10ed504501075d658c831fa98242c82de6314142bb98b41c86dc644cb30cf953420cb6e6194840b7584434c3d73084110bd19310042f96090e40cfd84544439e5410f30bd98420043d960945309f99441482df63487309f990520427d654c120f394f208827d658c910e7d50424c2df64c8530ed54741d02f9608c630bed81428827c6354241d754e324827b6055121bd586428833f5408110d754d511027d658c841b798e408c35e6510d309fd9643c435f5390921e794f409027f6355320d7943300833f5495010db988540c35d538c6409fd95320825e6314c20db181521033c6295020db54b20c43795014131f6583214c3765190430cf551428876e5490920b718d5050a776155220bed81415035f5394e209f194420cb9f4190530d798053486bd64c8620bed81525075c5350d41cf55043082bd6414031d7d4f434874e5354810d794d41082ee62d0720d714930c42f9600c640d7545308827d6094a43bd98420c437752d45409fd8550ccafa600c640f3189304827e60d5021cfd5254082de600c930bdd85548827e61953309f59353c835f530c720bbd89438cb5f6294e40af990510c33c6155010d7195434c2dd6414530ddd46510ca7e6114c21d799730c827f6454432db94842d027c6454b109758c540867d65d06309fd95420827f6254d109fd8d51903e921c8120b798f428c77651886209fd95414c7745488710afd91504ca7d65cc010bd984500cb9c5410930d794d30c837a5490040d7d0f5050f3f6095032db549328c67d6414e10db588540c67f650c640be98354cc7d55114530de58354c427d6194242cf550300825e65901309f582520c67d6494a30b759741cc36e6295131b758a434c27e6550c10bb982424837463546429f58e52107d553d06109f983548867d6094843cfd53324435e53cc841be98032cc6dc6454b30d754f40842ee62d0e32d7550544c3d8434c220db19152042f661d0d10de10d500ca7d658c640bd98742cc75e6354243f64c030883d530c40109f59053082bd640c820b719332cc3d6610ca31b7993314c35c534c921b7980434c35f5350d21bd587320c6fa600c410f3148424c27f6510f20d7185531033c6295032f34c32008376514c020cf55121043da63880209f982548c6bc6050740dd946419033f60151109f59631083d95350040f5d0730043e65148020e5504414c2f46150310b7582328c6fa6090d20b758e40443eb6050920f9145214836f52948319f195321075d6154c20ded425050b3e54d0830b758e408427e6510d41f398b30c836d524c841d754c538436d528c8409fd942110
  | 46 => 0x30dd944300823e6414c209f988514c2f56190210d7081530837551cc440bed95200837661d5221ddd44214c3775194530bb988214833c6395010bb98a31087d65354420cf95220042dc614c930d7d4f43c835f5350921cf953510827c6550910d714d43486f76248421d754c329067d6394442dd54b108435d6114d429f1855290ef4624c521c718d540ca7f6590a31be58031c43da614c120b798042cc33c5484110cb54940102f96014a43db951424835f6354d21f6d0930882f66190e10f6983214c35f6494e109fd9432042de62d5130e7d5130442f7614c9219f98251cca7c6590520be58054086f96090f10fc946500cad6610c9309fd8d52d03746494432dd54531c82f7614c110f90c9210875c52cc010d794d210435e63d5220af9874350bd8214c120b718d425033c6255321d7d5330483bb6450040cfd5040443da60ccb30d754f431037b4254032de585500ca7e6590720dd081510833e54d0b30db54a321073c5408510dd54441d037552d0641de991500ca7f6055031ddd46315027e64d4c209f18154c86de6290730f6d89304827e658c840dd5455090a7d650c8419f994424c6f76250441d7d4f30043795014141dbd95320ca7f6508430dd54621cc27d61151209d984540835e54cc1109f194438435d53cc8209f580540c67665d0521af590321033f548c110f6582314c2746155120ebd89425027c6254f40dd94541902f661d0e31f548730c42f46150d41dd182510836e52d0840f3d8932cc2dd618c130f394a328c6f561d0831bd58642507b654d0410cf151408435d6394242f58ca318867d6550630be98342883d761549309f194325067d62141319f996430427e6214540f694e308835e53d02209fd81544cb3d5490020be58043882fa6088410f5587304427c6254c10b7d8d414c73e6414c109f1855210fe662d0521d794c510833e5450731bb588314827d63d5110d794e520427f6510d21cf952410437554106109f994214c27f6590e21d794c318876e528c8108f59252087744314540d794f318427d60d5132ddd4421502f96288020be181425027e65d0d40bdd85408433e6415020d794f41042f76150110b598440cc27f65908309f587548833d5450721d795130042ee62d0120cfd5352442f6628c521dd0ca51103765490710dd591510ca5f6054c109f996410c27d6508640be58042d02f56110b10cf552530427c6214d20dbd4a525075d62d4d42af59021d039d544c010dd54440082de63d4742f5d4651cc33d5415210d7d845350abd640ca30bd98620043766454432d794d328867e6590930be580310427f6054f42d754e421027e6588540cf590528427e63152219d98753083f34184010bd185400c35e6395121b718d21cc27e65d0540db549420427d6548110d794d410c2f96014843cf99742502f96
  | 47 => 0x58e544877b5094031be980424427f6510b31de98352042be64c8421dd94721c827d60d4f21dbd4b424c3774214540de980530439f4250130b7d8d5050b7565c86219f58653d035f544c320d7d92539035c5454c109f586520c2df63c8530ed95041487da43cc1309fd9532502ef6550842cfd52548c67d65cc820ddd9521c42dd63d4840bbd89434caf56184010d794c32082f561cc310fc48710442dd6194930de951500ca7d650c540dd58e5190b5d534c6409fd8d50c86de618c130a7191514c2dc640cb30b718d52502ee62150109f59442cc2de610cb308f592528c6de644c832b7980414c27d62942319f98f544875d5310020b798c50d0afa6010a109f994414c75e6454e109f994414c27e6494331b3d89514c35e544c020dd946310873c5450220f694d20083b94010130b798654cc2dd62d41308f990540425c6354b109f982540875f5394c40dd95141c427d658c8209f58b5150f5c53d0d42dd987520427f6154843b798e50086dd61d09309f986538833e54d4c10bb98b434caec62507219f99431503796014d20f3189514c2ee6214c10d754c41882be60d0940b3189544c2ed64c8720af59232d033d54d0b31e7d50414c27e61951309f197434867d6394b40f6d0240cc2de63d52209f59631d035d5350840b798c314c36c52c8510db548524c27e60151219f99053442f76448510ddd85524427d6494021ed55041887da314c120d758a531035d524c010af990518c2dd64c8530d7597300435d538c020dd987548cb3c6195020d714f434867f654c540dd952210875e5494e10ad9864250af661152209f596320c6f66190a32cf951410433e6414f21f6951308836d520c440b7d8d414c33e54904209f58c54483cf6254530af587429075e5390c219f194314835f6550930db94a42842dd6010530f350b304836f6550b20e795342cc33d6510640bd58432082de6394242f9d05214833c548c510b598452cc3b54110721f554730083775410610cf55342082f661085109f58a511027e63d4b10b758e320cb6d65c82209fd95410c3775354440db94921903795388020decca500ca7f6590c20ed106408427e6015331cf18c54443756294440db549321035e53cc440be98030483766354420bd987500cabc6448640f64c1204436c52c8110ed50441d03765150430a7191524c35f6354b10d7d8d53442dd62d53309f994438437a60d4e20dbd89544ca7e6394342dd18d51102f4648c521b758f54083ae64c8621be98221c43744394420be582415027d60947439f5825310b77518c530b758b438cbd451105309f584524c27e6494e20b798e21cc37553884219f995424433d1015110afd81401037732544329f597414c35c6054e209f98a530427d6494432ddd4e21c43b764d4540f64c120843b651d0040cf586540cb4c524c9
  | 48 => 0x34c2f960cc830b758f21cc33d5408410d798d5010fce62d0e32d7d92530837a60d4a10ddd4531502f66114c40b7986324c2dd63d0330be98241042f56488710b798752cc2dd6388120b7d8c214c2dd6090b30f5984324c27d6588410bed81434c26d6215010be980321027d62d4143b798c42cc73e5450420d714d424875d5314d21de54050cc6f6610cb40af990500cb5c534c510ded81544c2f661d4242b7582524c35d5390610bd986535027f65886409fd94438435f6154c20de540500c67f6054c21db948310427d65106309d987548ca7f65cc7209798f54843cd53948409fd8953d035c6550b30de58053c43cd3088120f390842cc27e63d49419f994410c2756114f20dd552510ca3f6550c43bd185425075e5214730b718d42c833e6494b10dd544514caf561c8310be980215027e6510940dd547410827d6294331b558642cc2be648c740bd586420cbb74290710d7d4e534867d6194b43d794f438875e544c210cf553428836d5250a30fa54940102bd640c740b758a544c27e61950309fd9521903e960c8720b7994434c33f5490310f554e31886dd63106319f994329035d63940409f58b53442de65cc5309798f54883ea424c1209f99543c436c52c87109f994324c75e6154e20b798e505067e62d4141db9493204379658c220dd18151103765184010a759321cc39d5310640d794c20843ad5490b20cf505501067d64148109f19621502f66110f41f954841043795014042cf95231c867e6394810bd584321027e6414532bd5845290edd658c831d754e21903d7634c431cf55142ccafa6090640cf950520433d540cb21db549511027f6255231dd550410435d5314a10d794f41902f56114843de58054c835e530c830db98b54c833e548c832cf58d54042d56114930d714e4350add61cc930be980310c2dd628c130be582430c3db3048020cf951420c73c6055032bed81439027c650c9409f983544867d6095221af99021d03765248510f248530482766115220b798e50106fa6010c409f58a544caf5610ca30bed8141c827f6590d21db547208827e6214d10cf54b40102df6350841be980320823d6414a10d7951304827d654c1109fd97430827e6514d20af59052cc6be64c8510d754b304436d5250010dd14c515033e5488020bd987434c6be64d4420ded95300c27f654c821dd58c51502ed6210330b758c5050a7d65d0030f6d43404c27c654c8109f19442c435d5354640d794e528436f52482109f19731482ef64c8720f654d30882f9600c430d794f328435d5310a20b7593514c2dd63d47429f583548c67e650c521b7192304c3cf524c930d759730482de628c831dbd4a529067d65c87309f593524427d65108319f58c528436e5250a10d7553430cabd64885409f98650d0ef56194943af99321843e66190b20d7
  | 49 => 0x7d654c841f64c5304827c6354841afd9541d036d6294d20cf952408c3796014f20dd14e51102f561d4c209fd97424436d5290840b7588414c2f661909329f992524427f6054c41d514e31486f661d0f109f996410827e60d45429f98e54487755114730d714c31486dd65c8730db14b32502dd638c0209f582538875e6294c309f99641cc37a6015021d794d430875c5294730b7990430cb3e5450610b758e40c42ed62904219f59253c437463145409f98a51d02bd6448740f554621cc2ec6254d40af591215036e4354810d7d52538833c544c510cf552310433e41141419f984535035e5310840cf5095010be9424c120dd195214426c6254d109f59432102fa6090710ddd46405027c6550420f5984314c33d548c8209f18552d0ecf6255130bd987328871e54cc010b758f51103d64110530bd984421075d5388210d754c31443d852d4130cf95032042df6550c43d7d4c314833d5450930bb988510c37753485109f982544873e5414420ddd0450486dc6050530bb98a5150f5e5390620dbd0d521033d5414321cf18154c87775188540d794c408427e6094c42bb58a418875e524c210b798c40082dd6210d30cf94b42106d96015330bb98a4390a7c6255130db94b30043d621cc110ddd45314c2f56290510cfd5143ccb9c6454530cf551100427c6510c10af5903248774510c520b7d8d424837752440109f994544c27f6154e409f59642102f66110d21b798e401035d53d0f409f98753043ea60c8720bd58643cc67d65d0431b798c324c3b461950109f992528c33e54d0440cfd50414c2ed60885219f58b54cc33d5490e21bed81324c2f960cc7409f594430827e61151209f19152cc27d6508430bd5875390b5e6315331d758c540435e6294c20d754d401027f6354242b7d8e214c35e538c2109f983530835f534c920cf953500cb6d6194840dd5445110e7c6550b309f98054ccb5e5348640d78ca51cc33d53d0a41cf552100427e6550c20db948320c7cd214c3209f982518ca7c654c440db50d52103da324c220bbd89310837b5094141d7d4c32502dd6314810bd984524c3b76150a419fd95428c35d6294e10cfd53414435e3254231e7990438ca7c6354a41ddd0a510827e65d0730bd58440083766115310f6147504c39f4010330cf153424875e53cc840d794932cc2de650c530eb59321482de644c730cfd5254c82dd6390130db94a321027f6548421de8c9500ca7f6254331e7153304427e654c910d754f400433f5450921ddcc9511035d6454e40bb988434873d54544209f592530c2dd63143418f990540833e6415121d794831cc33d5410730f3c8730482bd6414831b798f424c35b3254032b718d42c867e63151219f993524c2dd6390010f588421cc27d658c010cfd09509079c63550329f99743c839c6454930b79824
  | 50 => 0x44010b558452cc27f6510910af592329067e6510d30bd587500cbf36144010d7185539035e53840109f58752502bd6414620bd586400433d5490230bd98643042f9608c820f658051cc27f6154c42bdd8540c427d62944439f98e52d027e6194c40bd987404435d53484209f1815110af561d0f41cf98b544436d4394810de545500cafa60104409fd96420427d650c9409f59053482ed62142319f98f548873e6095321cf185540cadc6348540d7941300c2ee6290d42bb98a318873d5415221bd98642cc3db614c120cf552408439f43d0a32db98854c86f96090a40db548525033f5448510b7d9530883d9544c2209d9845050b5e6054e10f3948320c6f46154132bb586424837651104409f596410c26f6254d10be980418c27d60149439fd9521103776554420cf951320cb9e5310440c7952530827c6510810f6580424c27e6590521d794c21043d730c4210fad89200827e64944309fd8d511035d5350610f690130482dd62cc530b798c53103755188640be58b308c2bd6494532f6d81324c3db6050530dbd4a324c39f4090130d7d4e434875d5354620d754c53c8775510c430cf15221442dd628c5309f98053886be6110440af586405025d6394010bb58b30c83d653944409f58a54043756115030f6885304827e65109419f18854483d56384110d7597318c76d52148419f99643c833c54901109f58a510436d52c8410de941300827e6315020d7597304435e6394020bd9875090fb65190440afd8d4310e7e6590e21dd10a511027d64d4d21dbd4a52d02be640c540be580411035c6494e20b798c408c2fa60148319f58054887b96010440d7d4f304836e6214c10de980548c35f524c1109fd8954c42ef6250e42bd986438879e54cc832f354e52042db60505309fd8550d0f766194b439f596420867d61d5032bdd85404c3e56210621f558730c42f960106309fd9643c83b664c86219f59630082df6348540cf181540839e53906409f997304427f6155030d798c534875d53d0420dd8c8515023f6550040f58c621cc3756194d21dd101511027e6095131b718d525073542145409b588530427d61951309f58e509067d658c410be98021c827d6215031d714f31c42dd6408530af191319027d6550831dd54f51503b55110440db55152042f76150010b798f51082fb654c0309f99742cc73f54d0f32cb552520427e6514d21d7150534867f658c821cfd50424c36d52c8010af5924310f5c534c110b758b43cc27e63942419f184544427e6494c21bd58341487b65454420d714e42487796014b109f195211027e6215210d718553043775210610edd0841486f56110230b7d8d525027c6255231d7551304827c6154f209f997418c33f61550209f59632103d730440109f582540cadd6510b309f194400c27c6154342cfd5254482
  | 51 => 0x1be18132883cd320ca20f3d4952cc3755254440cf9524210a7e6294910cf551320833e54904219fd81520c6bf644c640dd95241442dd63144429f595404427d63d5120f510e510cbe52108520af191321027e6394d21be980324867d6294743db54b320c67f6255031f60c530882796014c21f64c120c427c6154243cfd8f54442f661d0921bd19531487766194b40f5d4f414875f53d0d209f5875050b3f6455120d394e520427d63d53109f58850506de64d4530dd58652d027d65107209fd95420423e6494d10d794c41083da41d4130be580320c67d60d5131cf153104427d6395121bd986420c7d9324c220be582328c27d654cb40d754f21102ef6250d429f58654c82be640cb30bed95401035d63d5210e7d0740cc27e6215130fcd4210443754394642db98152042f56114830ed504418827c65909309f580544867e6095331db54d52042be64c8640d7947308c23d64d4810b758c40c827e62952319fd9743c437762d4540bd1855050e7e6094e42bd597318c6f561d4f429759730082dc6155130af990320c79e5454c20f5984404c33e54544329718d54486df63487209f586544827c6354910b798a514c27e6315220ddd4441482f7614ca31d794e32c836e520c440c795330082de608c530b798232cc3b74210610d754e43102db6054530af993218867c6254740d7d4c31c867d6094c41fa8c220483b7645044197994404c27e60d45439fd9631102f7614c3109f9865090edc64545309f994430435f6254e10fc8c5100436f5248710edd87544435e6094c40b799741cc27d60548109f98254887f160d0610d794e310427e6590510d7d4f214867d65d0931ed95110042ef6550b20ddd8e51102bf6150b409fd96318827e65cc640be582424c35e5310f42b7592324c26d6215030db19542483b76150540d7592530c2f960d0740d754c43903b44190010cd151214425f6550b30db54b218c35c514c1209f194434865e6394020d798e5090b7661d4b10db949321035d6254c109fd97434867d6494f21d794730c82f7604c521d7d0e52cc27f654c831bd98440483d9644c120b7983434c35c548c930be181410827d6014d41cf15142483d54110530f6cc9500cb9d5410730ed106219033d54904219f592508c6f56114a30d754c53d03ba60104409f59421d035e650c930d794d41882ee6214443d7989530433f53d0940f64c120042f661d0b41cf95131c8776514c4219fd89544c3763294420d714e435073e540c820d794e32907ba5448020b798331cc27f64542329f18554cc2dd63900309f59731483755494420d794d100427d658c5409fd94420436d6294d21f5185404c33c544c110bb58850d0f6e5290810bdd85328436d5214a30dbd0e520427f6550d10cfd52540c73e50500409f189538435c4354232ed18d41106bc64
  | 52 => 0x100050425c004000d001c00f0060001000c06a000c000019c00000d4002003803400440000028070002c329004c0000214000001001904440db0024003059809e023c094000000c0000001000000010b004c00441a101640120000001002808c002800400000700e70015003800e0284005000c0280000002015c012008400000cc02c022d8e2004c0020148010003401200ac01a00cc000000401900ec0030058028003c00500600aa091008b0164000002801308f40020020000002000400040100000008004c00d003c0050098004005c02d02fc014006401900000f4001c00514400230004004001817301fc17b00200130004003005c01a007400001780290000000000400101400220054006003800e028000400a000200080010014000001800302ec01c007400300000040b9400400e006500e000001680030054000000000101200900054004000000c0e835d530ca10cf951430cbdb604c220bd58432d075c6154e20bdd8110042de63106319f994321035d52cc310bd98652502dc604c5309f194434839e6410f309f992530c67e65d0a10eb50842d073d5494c20bb58841c83755114530bd586421073c5450a32db94951102ef6048020bd9845010a7d65c8630b7582314c6f9600cb30d7588534875f53941219fd9441c83cd62cc320ad59241106f56114342d7997324c27f6054b41b798b41cc35e65cc110dd10f515033e5450a20d714e43486f860487409f597410435d53cc620cf990540c7d56110330db94b218427c6254331b798332cc33d540c420ed50a414435f54d4130b7590314c2e4624c521cf50a51d027e64951309f590514c2be6494931be580510cb3c5410530d7986530c2bd6414c20d758c540827e658c940d754d52903746394432f9485204433d5490030cf55353c867d6295031be58354cc67e61d5330cf55142cc73d5410721b7181434c2dd6008530bdd9121c42ee62103309fd8d51d0b9c4110130bd988414867c6548530d794f418427f63542419f19742042f76150030b7588404c35e5310820ddd0e5190adf63c8730dd9865210ade6290d309f99250c86ed6210f209f58e52d06de6590d30af993214c3b45150540cf55243ccb6e5250810b798c540436c5210930d794c410c35f5454c10cf55131042f56110c319fd95200827c6550531b7196214c33d5290440b758c521075d5394420b7986424c27f6054f21d7545300c33d5490721d7153300c3cb624c120d79875350abe64c8410cfd85540ca7e63d5031db948329067c6355221be98331443756114930d754c5310a7c658ca109f59543c86dd63d4a40d715032cc33e54d0c42be181418c33e5490c31dd94621042776154d20b799641cc35e6094c20cf552410c7d55114730dbd4a52d0e7d6294e40be98331842fa6010930de980540c67d651082
  | 53 => 0x3e002c03d0038000009800103ec01a306817c00100ce002802b03cc016032c003000002900445da000812c00b000100cc003019003a000800a00000000030000153800900280f70008023000c000001c0002a700070030000000c012005401805240310094003001c00c1608000002830000080270000045011c00e0044001003802302c4016000c034003c003002c0350074005005c01c00180170014013009000f006c191000007f00240000a2c000017c000013000a0038002008800200040ed000c285001c022000c00b001800100000cb00000000064023001007800f8034003c00700006ba0034000003c00000340bc0368001002c011000000c0008014000000b01603e401c8005007c00000000110000000009800500100200004000000405d006800301ec04d379401400100ef00340090000000005c09e00140460c200f5002400302d00030000013007403000140050028012036c002000003f007c04f03c800c000404d12941da0014012000800702880900060001000001900c401402b400b0084004015c0010338056000402800200080000011001c01f003633b023804e0004003001005f01140a5007011b000000801d4000024800400080050094000005001300f043200600a30008c8d021c0220000008001c048001c001038400202c0029007401100000100030010000401f0004000000c005000801300040040000029022000400c8004019c0010000000001c00d010c00803ec01303a40010000aa3006000901bc064002007600b800600fc00a000c003001000e0068045000004e004c001002000d0008563006c06f0110004014c05a000000603240be0014007001400000100a300000be02d80d40028002009c00f006800700ac000006007c003c000001800000f001000f800300380000010003501c1030008018000803000a80070008001002c008009400000ac001012800b0008000111c025000001000080030044004000029f0040027024c0060008000000003a00a000000000130000019553000d003408402f000100740c300040b601d80010000000000000a0f041a8001000001600050138007000000000f0025000400000400330ac8000007c02a000c0800048000054c024000400d001c00e00040fc008000300080c20040002006000400f4035000c00b00800000580940001c04600140520000013005005500000220040015000c0e70258001001009c004c00006d0014002800606380102d88032001400400100050000009001c05a00f400200fc05a007000200ec08b2b1403800482c3000c03d001403e00fc0001328009002800b001403f000800100003190040001006c00800000020059c6200c40900008000000000120cdd4519d000000000090234003000c0950244002006400100000210124
  | 54 => 0x5a0000005000004402000240168017000000b002c000001401c010000d00e00000000662000480200040150028022000800900100090f680270068008000406b00e80d60004003130c055050400500000000890000001001e001c0020534000010000108dc0440574004000000006ec0a70000004000802f00f000503dc0670034008039c06b004c01f001000e00102ab1b0c0040f7c00e00300bc0130098000419d000002300a8001049000c00c0000000001f007c02e005400e0000000003c00c0000036010400000180210000006263c009000002e003000100000410044004001c00500dc012000037900100070030001003c00400000010000030005800301240000020002000000810f4242060c03b0008015000001b0010001028c03c001802a0008002144c04a00b055c013800300300030000000012800200201cc000002c0024000008010900740011b60008001000f00441f90000002005c00500840560010004000000700ac00100b0004001401b001c00001d400800000350228000027c00146640140020000009c08e00040f9001c014001c00400180030078038002000300000010264022000000130fc033048c01c01600170174046014402f004c021000000002d8000006804f03340140058001000005f00040050134015093483f009c7fd0020014008c0030008000001c076003806401940db0020000000000e00000010070037000405000b400300108a20f7403800180010308002139401d01e001e0a2c014001c00b0d00029005c00b01c000400000000000038000c000000405b004000c05a400000b003a001402e000071a000001e002c00c0060022004006904180700000012008c22200200510000001000400c000002f0000004000000400c400d031000000a43ed001001300480150004011004406c0034000000005a00080000004033000c043101c0170018009000002e0140005001c0000040001001c00001ec0000298298007402a00000012f2000400000111c5c00a02500813a1c00200d406200040080004070000000b000022c0010014002800f000002600100ee00d0098001c0370004003007c0ba000032e014c0b2009403a0400000013800a0000000169802e000001500280b70100014000000a001c01500d00000008016253c02d000000c00000000010000009c0000034172010800500c80000020010007c05a002404800240ae000800900300030014001354c04a000000000cc3150134000007400000702be000c001002c00000401160000004005c05002cc01f0040acb00000920000000004800000241cb000001700040060014001002000b006c0fe006800000000150354023005c01000480070008008001802a69cc0030018004000015c011c01200040030060000000000d00280100004025
  | 55 => 0x7001800a01900010878000002401b001800702180c5000000b02980bd0388019039801101400040014000053c00200500000034001001d6e8001800b0000006000c00300005f90000813002001d004401a002800b001008800f8037000c3090094012004800501c8000000000b02e8008001c0060130012001c000089800e00180030028009004800c204000400081f2000005a007002e025842b001800400ac00200080030000002222c008001000600000020010000007800100000ba000001100a4027000000500fc0020048008000c0a0000400300000de000400600e800f050014e0000002204000a000401b0070010003002600900270014b3c10fc00d04f40020000000005801c00080000004020005001e0000011000c01303480000014006001802a002800004fc01800802a8000406200000123800000008c00c00100080f14002000000200000070068005002400100680ad00043b10000000009002b053000000500050008002004c0120010000000800a001401a00a8002037400300fc000000000101140180048008011c00312acecd0004018001800a000002400300ab17c403800a8002001000b000000300d00080000008002000e005803f000000d0048001000842d0010008001c075000401b109400000100000378024000001e00000640000000002c02214e000c003001f0248238003800003480b3000c25b00403d5005804c000c00001a4008000001600a000a00180000000073000000600181470000000000c0070de405f0020151017400902e40020000014009813d0008514001001b0364000000000000e40e400d804b0000034004800600080020010019009c1050034002006801300040110000015013000000500090018000000000d01cc022001811e00000a1000c006002447c001402e00103470024027019c07400d8072070400d00300060000002000002d00040010000003015002a0000119000401100041120000000000008a0074002004803100800000114000003c000000c1180068004025085a000001100dc3970000009001407a001000000d4003000000403980000098002003c020003c13e0008003000400c000000000342fc00100010000f96006000a0058001008800e003000e0018000002c0741cb000502340000010000004002a002c00f00200010264012002c000005400400480110004001046009d0084017000000900000000014167002c0da00001060000009004001b056000a001c030001c0c1000000200180360674009011c00b004c0b90028006007003813a814d003004a00a0026018400a00000002fb80001db0000000800b0220000002c1b500040930028024000012d00ec040000c09f000801300300080008310000001b00284b200b400100c80580000004000c00b00f8000000
  | 56 => 0xf40fa0000025000000e0000000a810002004c05a01540550bb401a0024023012c000001801b00f40080510001000005e000004e01140700004009346400b0060181000000002100160094000005006400040011500015006c000026c000000805300800000008025019000c000800800400000100017001402200f8b45087400100bc01c0124001000c00100dc0030000002007400000ac2b100980000068015001000f0028013003802f007403c05c0001000001000a0076003000e006407c049032d00000460130002000400000800000064005026003700880000f000d3006400000086cf01880090000000000000000840251ab8000000037500d000500281d1003800600080080038001000400600d4253001400b0ee8000009c00000bc00a0000000007400104d4009000c05300b0021001c001005c0021f3c0110000000091800200140000001ae100200030000002006004c0028019001400b001800700c000700bc09302580010004128001c000000008c005c00201a000000380030b3c00f013c00901c80270018007002c73f005400100340110180000000000100080320008024022800201dc001004000000b4001026463f00c09ea00bc0890000002001400c00200011f7c28d0a7800c008800129b8007001c0282d900170018584013400b000000a0000026001c014032c140000802e0048099000000b0050095005400f0000023053000015600050030005000419900000010020009005400b003400b005801702cc074000c006000800000140a8000002800140020000224000000100a8090000403600340010004000001403900e007e00820510074024002c00702083fd00040040050012000000528d80ff000003100180040170008004c004049c00c000006900040110014018139c0f7000800101ec01400c8003001c075000c00e001800d014403a00000170040002002015000000230158000000000500dc00001f4152044c000000000c002000900000510004000000006b01040350014000004c08304300000000000002437b008000002b40f4000c0090048021000437b0074000002c002010800300000270000a1412c804822e8000000000b000c19f000c000002c01c000000100740a9000001000004e40298001045c00203b0000000801a001000000140100000079046000209e00bc002400c00240040100032001000000300000008034003c001007000a00ac00d00345d20154002007c0860048005034801500440300040002001c0000178002050002b005c36c002443f00c800800b0007002804a04100000008000002c762161c0360028001ad740000118004012800f008400000b404a000000000000291a9801f01d400b004d32c01d80006e38009000c000006c0060ab800a01680140058000000c072000001
  | 57 => 0x400200190074000001c0000020000000000010f401600ec0010000021000000b0078000008801b0040040002459c00fc033000000300081f700400250ef400700040080138001000c304016c000000400102c0002004000001fc000008017d0000000027c010000c029003000800500410008399016009d0000020008400000800000000260000c0020004003006001b0000288000400100380e600102d1002c005000000002cc001001800000000080234000002802800080010040000000c02e0db80a21da80250028001006400400082490010005015c049003c077005c0862914bd80000026002c000008c00000c80170034001000908e005805c002c003018400002ac002012801d0000000008400b00000330000002009004a00081cb00fc0020010037000012600000200abc00000100000078000001c0050140011002803900140000000004000000306bc03500c0001000cf3a05381951c4c000000001c004803d001c024003c00000607dd006c0000088051021c08e000000002e4011000000000bc0050004009000c022021c001000024a00380be001801f0004010003c02a02045ed00600190170005000000709500f1000c0010288014007c000000801600080000038001000805024b0000275000400be26d009004a049402e00c00000010076001802c017c03000000dc002009c00b400900e801f003c00f0000000002000503f40d2000400201040fb01d40080050006000404f0004016000400c00b80dd01dc0221eac00000ba7970018004001c012000805200400000010029001000101d00000004026000018000f400000000020068002000c0000380038004c00600f800a17740010008003003400000041bc29fc2ad00680310030000075800b009800f000802400b003d000000147d0001023c027001404d000800e0000000004c01b0008003010400177ac000005c027032400a0014083000000000100350020000004000400ac241000400904c00410000013000c053023800000040000900023000007c5c58064004c0c500240180079d4d0000000000000000000000010026000800c00001b600341f2023c05c0004007026402c00f8027000000018c400d00a800300100ec00000000084004001c1b3000400800040b10018000001800b000000c006400e01500b30370016000c0020098006008000101fc00a00a0021000c0020084010009401100200220000004000025200ac0260020007009c0120014000000001d0098001003c000000000501b8008002400600240000054004004801605543ec00000af000000d00801b4000c018002400800080010000000000000a006c00d007000602b80140028008002400b005800d00200090040022012001a0000000001000b02b001c160002500000150000015001401601
  | 58 => 0xa340250054007001000a017800a00ac0060088018006000501a8019002c00b0010000002c041002c002003800200cc0000038015000400a013c06b0060011000013e001c006001000005400000010006000401d0014028002000800000010000d6e00080180028000002c00002dc0010088001001801e00001320018019000c00049a80280000008053c000002401000f40000080039001c02e0038022002800c001c02200880700004043000800400e4009007c0210054000002000a4a3002a0014056000c00f000800000980080000048001000e000808f00140a208a04fb00080250004003000c029002800d002800200e000b00780000198001090000000200100014004008c0600000009021400200e400000180000064000007800e000c10a00f4048000001f0019803000400500240020004944003000c00a63420b3c000003008300100003a0000301100010008002002000000a404800b40472ad0099013c00e0000001001800400f00030004038007c00300000000004002015000000243b3005802e000c08501bc00001dc03d0000026007807000f0037002803f006802a006000f012802c005400001d805174c4000004800000700000058001004c032021c04803d40280090049000c0210010000000400000bc1010004029000400200040040014029001c000002c34a004400a001400800006e000c400c0004f20000002d002005102a4033000000002203b700000000008025017002000a82e90000005630c01700d4001004800703bc070006400000340cb02a0009000c0ad000000300a00000efc008000000e001c00122e803000500654bf01000048007003400000240030000018002c00100000230028011004c024006c0850020006005000200000000000006002401c007400001bc010000066e00cc05a0158004000001e03dc003005c0040008004135002d114400000390000004012001c00400500090008000001400e000000300e41e42570000000003f001800d05b00180084016000403600080090038574001402200cc02e0170ccf011400b13bc0da0090006003400000080000000017003400000040000044001007800e00040000004986002402f000c003004000b000400a004006802d804e00300090040000000807f00000040040007001400800e800d00c002901bc000001001d0030017002c0000014000005801d1cbc0210004286004000000a40d0005a99d00340c000080140070000000800005e4002022c002000c002008c03407c001b0fc000300040000014001000001b000406e000000238860ba00f000000886b800041be034c044007007501dc000018402a000003d000800200b8004006020801c401f000405d004004a0290000049800b0080101006c02600a4003000c00b000446d015800a00900
  | 59 => 0x480010024004003022e0038005000003a003c023039005f00100db0010004009c011003000f000c05700040980018024000c01300d800503e401200180020040003003001c000401302b40090198014000c000000000000780120000002002401208f000b007c00e02f8004000004500f0b550000086008804f000001100fc015000400700100050008020004c000089003b0000007000006b000000700440070004c5d0000016000000e007820f13b016409f0079000000200240070254045002000c00000000008007001801e0018059022000301cc002022400000280010214054118403b002400f00560b10004011002c27600005a80000003002c00f029407700080140004002824000300880010014000000000e00100000000027000000100700000090013143c0050
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1961d6454c320878aaa661880219358d5214841c5ac5208a0a0c3d74d9731882ccba0a2984414d5d06094420caac6a88a1217175454c418424eba4c528e610fdd95414f21cb2a7300841045e7614d314431ab20a218a811d9d83214540ae0e0b12a2205d071551304830f2a6c6a1461179cc6510020a68e8b0ea50869b76500404c2aabae60880211ddd9541062187ce9b2c6410e4d6354840042ad3a8c4982414d1d94154041a5ae831aa40863565d07400434aa0ac020e618d5526190a31e8aa7294a22061e6498c540821fbb2a829821565c354d0c32a3ae829a600864d53588400830f2a4c7200614e5c36455032c74a9300a790e377655041886e8b88a5a82614d9d03254440cb6c7b02a890e36549864204369a8ec0a8a6187d96544c832caea7b0aa0a1475769445090b2729ac4204214d1c55410220c68a930e86886385418121442ab38ea729841171cd629464087aeb3068420e6652584321021eba4cb10e6153dc965cc110c9ca6b1080084b5760c9411071a2a2c520a219554e6114a40ce4a2b00822056872591500cb2aa9ac3180219518e5148420a5ce9b12a40863454984324431b2a4c3a1e43175ce6550810c6cc2a8e812055573d90515023bb8ecaa00219554e61908408dce532860084db72582544c326a9cc429881355c6644c930d92a4b006418e2c72590524c26b388c0a16613a1c16448720ce0a330482a06365498432c868f39ec8aa0215c5c04254420c6ac828c42a043e741963284326b10a5a826136dc16550530c9cc7296a22045d7694e200832731ca41002117dcd6194a40a68e2aa2831865853580325038a2a282986214d5d43250441a6ce3b22a81053471551410822fbb4a720021c695343540328f4eda8aa0194d970d96414c2a6392a9a82614b5d060948108f6eca80a12145e7599121cc36828ac010a614b1d1635484087aed2a0a61046e72194434421eba0c4a8063725cb414c120cccc4a8c601065a75982424c21f3a6cb19621559ce6054420acee4a9ea2a053674d46510831a3b282a80838bd96544c832e32a8a9a40106d161580324c22eb9cc02902174dc15114530c3ca831a841852c75508414831b2a2c3a16631ddd95410521a6ae9b1ca32143d7498b53c432632ec6a12419559653106109b4eb30082984747654d2144297396c32a065879516310010c9aa631261905b3705894110672b90c0a0a21969cd6014c21ccaa4b0880086565358432d06acb82a690021c69513048020ca8a7308a0a165553185408423abb48528841271d16508530b36e0aa6849868d63508420cb8aaa66088021665c35495330f14c4a00809865a53582439026cb80c910a615c9c75494032ab2e118ea098d577155330482aab8ea998641c99495110440a68eaa08831071b544c1204422ebacc7200211bdd95214830
  | 1 => 0x210831a2a2c3a12211e5c065d0c2187ae9b28650843e7498b504c62eb9cc12a0438d9915114420ccaa4b08410855a7590130442aab88a99844117dd562107309b4eb306429864e6354852042b8b80a928865745c25114530e8ca7292a220572700c8515021f3a0c0a8865599c84354432a6ceaa08829867151980510ca9b3a6ca90e2117dd95314620ce2a2b00a21946e72d9741cc29d3a6a1280651d5d66190c10cacc7308a81056572d90515022ebb0a8194631b5ca6550c108b8e6b24a41045f7358652102ab388c529c8156dd843540328baeca9c801051d7018d540ca9ab8cc4aa041565d6644c220a3ae9b16a690c5e761513004332b12a228861475d0654c320c6ecb2a2200863461545401030f32e8120261399d4624c521ab4e0312a70861d6458c520422ebaec6a1421531c96454c20d2cc8b08a49862d5458840842aab9ea328881acd046048740c9ac6a94802047676d51510cacc3828220a610f9d0658c810c98e6b10a818e2f6554940102a73aec499261871915354620a6ce829ca2106cb7648530482aab9cc0a8c85729d9424c120ab2eda1aa0196655298640043a4a92c01966117dcd6494a10b94ec31260905c97210130c4332a94c321021179cc6054442aace2312a60873270d50418432ba9cc22828587991530c840a6ce92924288634549863244333312c229841551c55454e20aaaeb98620087155494d100422fbaac7200411b9c86154043a3ae7304a81065a53582430422eb9cc3a828547dcd6215110b8ae3212641953674951414422eb98ca90c81c55534394432cb0cb992609054f76548320c78d2a264a8065c65515344010c72a9300a01964d539884084368b0ac019063b4d8750501308f2ed29c601845d7694e40082b9386a328c878d1506150220e2ca831aa21974952580524c327b28c690e410f1d161940328dce4302a918c6e7614921c4272b90c0a0e212d5db5410610c9aa4b00a5986a7529864250b1b2a4c3196430f9db5454d10aaae2306a690f3154946500cb1ab26a328a654ddc96115110ea0e6a8ca01970d64548524c2b3390c0a8c85961cf6055121c6ca9b0a80105727190a500cb52322a488021b45856090930ab2e1992a019719544c9500cb0eaa2c7286435c5c75094032caaca288829852e74041520431baa2c32a265479cc6095032b94e532260906c762d85544c23bbb2a228c87d498e5154032d96ec984409069b42580424c272b88c0a124187d96544c020da6a2b00429859772504414c316aa2c420041179d85454e20c3ca9318a40870d5454d520432bb1aa2908811d9c46590c21b88e29906490cda70d93314c23d380c4a9883551d52108530a9ce6202a420476719974308769b0ec0aa261555c46094e20a6ae9190a2a05c57190930c829bb8ac12a065365c265107308eae2322a0
  | 2 => 0xa4908218dd944190010c6ac928ea01964d639885408334a92c1a10819658d5014021aaae3b24a6185397015142086a7396a998021c95525244010aaae3b24a72069a64583214c266b90ca20a614d1d15348510c76ca32220084da70190214c2a6b96a698021591c56354810b18e4a1a849853474546418829cba0c52806517dd9544c1208bae6328800849d74197214c26d380c498a611b5c86510c10b28e2a00809861e5498f510828eb9cc0aa021275d36588530a6ae22a0831051f7458553882ab39840a88418dd506150110caaa6b0865107315454520082aab88c5298418bd5162951318bae1b2a641945e7654d421022ebb6a998041179cf650801099ae4302839856870591520432a29ac3212850f5d3658c8218f2e032c8790e956458452cc3a2b88a499261c354d52d0040ab4eb312609065653586429030eba0caa1661475d36354c10ccac5308a80872552547401023b38cc52a261665d032cc130e2ca929aa21063654185400838aaa4a788021271d95450930c58a8b16869945d7518d42882cc3a2c298241a5d9361549308eaea32620086d351582514c332a96c299021c554d41106108bce732a85885357195041cc22f39ecaa0a4335dc565501308ecedaa2200845d70d95310c636bacc420021879915314810ba4e3b26a09862e64548320429ab88c0aa643175ce60d5121c6ac930ea40843f76d53214421eba4c7a9221c515121cc110ce2c3306a81961d5498c200422f39ccaa1021555c4538c720cacc7308a808667655491004316b22a4190619398d6295121c3ac92a065985347158d5404339b8ecaa0081a55904148730a6ae2318a88869564584328c6ab388a898021d454d5148020a98e4b22a7205647254d21c421fbb2a82a0418d5916114a108baed29881085cb70548524c23d380ca990831d1c564d49308eae3b22a5986355418540c421f3a4c5a9e21535c854cc0108bae7b2e839056672d4e51102ab398c128c85749c4624c120caea730c8490e94635854210637bb2a4294814d9c46055020ccac4a88a32065953d814184297396a8a1463471d1524c1108dae4328870845e73980540423b388c0aa065599c4535484095ae830243905ca70c853048386aa26419643359c76590930d9484b0084984cf76484214c32a31aa2908814d9c75495330d1ec9b12a29845f7654c5350a5bbb2822808393d953048020acee4a98a2a052c7258d540822fbb2a829a43879536348410c9ac4314a72054e72153308c31cb22c029e430f5d06214d20b8ae2294429865a73980540caadbaa86984414d5c36550441c3ca8b1c811872562d08515022eb84c72a2438d9526190832e18e8a90a49845f76550430ca2fbb2a228e611e9c0650c810ec2a530082084d771595424c23cb80ca19283a659260c8530b2ce990a439867151583
  | 3 => 0x861503308bae7b0aa1a154e72d4e531028eb9cc12a0218b5536250721c5aa8b10800854c75508424c32b29cc321c21995895110020c3cc8b18a508659539804110237bb2a4296639594e610ca40b60e0a0aa020d5571d92538423b388cba18214b1d54250120c6cc9308a79072552d084104326b1cc5aa463741c5644c12087ae9b2a648845e73d97424422f39cc02a0431d5c66510c2095ae43028220c5d7614b300423d3b6a8a8065335cb648c730cb2a6b00a610d35741825190b92aa4a5880215c9c042544208baeb31881107195454e10042ab388ca98641179ce60d5020caca6b0ea42047771593524c2aa39aa318e414d1c554d06208beeca98a6084ad741893048317aa4c4202219358d6215220caca6b0c850859574144414c32c2a2c0194639594d6190810a9ae421aa01965553586420832729cc428c816c9c032504419b2e132a8398655635465090a3b3aec910a218d5905488510c5ac9316a60845e73994428432d31ac02a06396595538c220968e8b0c40085d371589308823ab88ca21a411b5cb65d0d219d2e43028390572710c9500cb8aaa086a8865275d06508530c3ac929e432056675d0521c822ebb4a7188639998961152108beeab22439849e7499521cc22f3b6a6a82434e5d06154032aaae2294629863562147415034bb1ac2a10839514e6110d21c6ac8a88a2185647250d5190b1bbb2a820821535c86114d42ca8a730c8490e5b53d815150aac382a9a9a431b5c8654c440e30a8984408845e75d92214c236b96cba0e6196d4c6054542c9ccb31080985cb74c8530482d338ea8a16411edd95014142caac7308a0a14da73181414c31ab24a390881479d065cc1208f2e032a8418d3676151414430f326a6192438d99151cc440caacab0881984d571194424c33930ac029e214e1d15014121cb4e031aa5a051c7459530482ab38ea8986418e15260d05109b2e1b2c849846d769524210a66b90c818e61669d3214c220caca7308a52063454984204431a2a4c3a0221175d76350810cb0ca30a609045c7359521d025ab88c0a1681e25d3214c120ccaa4b0c852061e5418d21042a6b9cc0a9081535c843149309aae232c849861d6494f210c26cb80cb10e61c9dc954105218bce630aa0215c876c85304821e3a2c328465651c554d0930b36e8b12609063664947210823ab88ca9908117dd95308210da0c3a82809851e74d86538821eba4c5288214d9c75495232ad2e021aa4205667218251102adbaac298441179d66550930c9ac7310a91962d65593218872b29ac321061b84856008710ae2e3212a01953671d53428cb2b29cc2190611d5da54904419aae3b2c859861d5418d42c86aa38ac8a9821635d3214c3208bae7300a4a0d2e7218e54c86aa39a85288654b9cb5450b109b0eca8a60906365418540cc327b1a
  | 4 => 0xd2a5300820865a63580540862fbb2a6288411bdd95214a43e28a8b0e608863454181214436930ac0292618795163880208bae7300a48843d74195210c32da9ac0192836a5c35250b4087eecaa0810847676d4d210869ab8aa8208219a58960150318deeca90a5a0e5563144414c3653b0c498241175cc6054742c5ac929643084da70988314c31ab24a2280658e1d365440108bee6b24a40851c73585540ca5b3a6c299283ac1913044010c3ea8b1c40886595358032d07172a2c42982127dd94010130aa8e6a88a29068c64d49524c22eba8c690c410f5d0650c910d2cc930864986355418543042cc38282a02614b5d06054810ab4ea19260904797694a200822eb9cc12a443595c46094840c9aa6b1080085377254441102ac382a829a43539ce6094810b2ce62928220c7571993504cb1aaa2c228065595c75354840d2ae63028220c3e76d515244358326c28802187990530c92199ce5b2e829861d6454f210831db2ca890041565d6314c220a38eaa10849861d6494f210432cbaac019063b4191304401096aed208808878a74189304830eb24a790c211d1d95444010a6ae8304a219694539864250a2f39cc029021c99495150040a3ce929661885357418b515031a2a2c3a1243555cf64d4540aace3a9a601043d7695032c86b2b96a72888196194314c120caaa6b0c85205577350a510ca2fbb2a598621565c06354841caca7308640845f7558e40042b3388c6a90218e5516090c108bce7300a81043e76151428c6aab9ea928841b298b5010130f24a8982200852e72182540421f3a0ca990218b59152c8640b88e4a8a429845f76548524c2ad380c5298219394d6210220e48e2aa2a40855673d90515029a38aa8a0c41479d3534c010acce231ca42043d7419532042a7396a929821ac50560106308bce7306a2a1731548c1100430eaa6c6a1643d154d5254440a9ce5302a72043d74994300826ab8ec9196614d9d26294440a6ceba10830865653d8540082ac3aa8298241179cf64542218beeab1c810866652586428438da1e84a80652d9d85450710ce2a2b00a221c3e74d8552cc31d322c029e411d9db53544208f2e032a6420d1d75951300833930cc0298419394d621444087cec2a2a48854d72153308c2e53b642982419594d619084087aedaa0849845d7518d420423ab8ecb21c418d14660d05408ece2312a021ec571189514c3a2a968298021535c85494c108f0eab00648861f64d4d5048637390c02a2218e551600cb21a3ce6302a8196d16158052cc32631aa4908210f5d84194040c9aa7316a22071554105300432d2a2c019463365c06550b30b92e421aa0196347654540102373b6a6a90814b5d362548109cae2302859045e76d51308426cb84ca90e614d9d060944328baebb1a4308670515803148296b90a821221a5d
  | 5 => 0x94767198a54cc22f398c0a8c85a55874010130a68e2aa2821843d759903204333b2ca2900411b9c865d0e10a3ce6310a88873370508515034da12c020a614d5c45450220ba6e2aa260905c8769093048266b96cb20a610f5db5408110b34e8296a09853574d8c515030f2a2c6288411d9d7644851096ae3b2a85a058c72553424c2aa39a85288418d1526088510d28c9a8aa29865953580410431bb22a2908810f9d06354810ad4e031ca40861d6494c3208316b24c5a9841b2197624c120aace2296600855a70149300423b38cc52a46174dc15148530b28e8a88a29845e7694d219034a30e82a0261c355252cc010b28e0a08829855975985308822eb9cc02a043c595251cc0208f4ec29a6090557715513088266b90ca20e611d9da4254432a74e1a0aa120c5d731974284237bb2a429463a5d4e6190942c3cc8a9e422055671151300c32cb1aa028485659d361d4d21c6ac430aa808638549804344267390c818e61e4dc14110530c9aa7310a32065a7398354cc72ca9ac0298838715163101108ece232864084da7610b504c22eb9ecb10021335ca61d0c328ece3314a8186b361181415030eb26a6282431b9c86510010cd4a4b00842052d70949429070eb22a790c818d9916115230d1ac5208809843f7655054c822f398cba1421c55515344010c6ca9308a610718705513004333a92c3212831e5c36590d21b2ce3b26a6a16366454721103a4a9aa52008136dc16590530c68a8b0880884d875580414c2ac38a64a80658d9516110210c68cbb22828845d7518d21842cb38c84a16618dd954110630c3ec829aa090e9141580414c2e43aa8498241e450441d4130cb6cb98220086566358454082aab88c129c814b5d65448020a5ae5b08a88845f7058c540869a38aa8a14410fdda540c82087aed2a0a40856472581510cb63a9cc5a0a43179cc6055121e22a8982200854c72585538432aa9cc2194818b9916215031ba6e2b22611047671197430822fbb2a628881175cc6054b41e32a82a260904d671991320ca8f3a0c529881179cc6590a10cccc5308a81054d721835350a2f398caa1421555cc62946428deeca90a4985357195041486b8b868228283555ce6094420a9ee4b22a71045c7358a544832b29cc219421179d8524c010ccca4b0c84086567118d52c43e0a926088021365ce60d0a20caaa7308641061d6494f211031aaa4c219041665c254d093096aed208818854e73152520428eba0a698041595c463948408bee6b2a8290e2d54588400c2aab8ec9a9a851d1c56095032b62e0208800855571153300c24e3a2ca90a61365c36510530a9ce429260084d970988414c30eb2ac81946333dd942cc120c70a9306628863554586420832b29cc219081c555151cc020cb4a6b04871045e76151300834ab24c229261279da5450930c
  | 6 => 0x14c32629cc521a858e59150140219b2e1310a8984e972181418c2aa38aa629a412b5d0624c3208beeca9260887295258041102cdbb28020261d498e51940329a8e2b28849869542185404c2e4b96a898441471d15214930c5cc8a96420853870505501062ebacc7100211ddd951145209b2e032c83986d261580328c68eba0c229a8572dc9614c120cacc6b08a8185c9731812148256b90c0a0a81591c953d45408bcea31a8490cda70192314c267394c898e619659653c42108f0e0b2a8690e5b6594d100431ab2a8220c615c5c34194241d32c8b00659847976952401021ebb4a921887e2591424c1209cee2b24409046f765485210e6d380c818a6193588521453093ee8b0ea4986c45398b414862f3b6a498421369c3640c930dc2c2b04859045c73595428422fbaac4218658b553624c721ae4e029aa32153475504414c326a9cc518441171d9514c3208b8ecaa2619062c64549100422f3aec910e619558d61152208f6eca80a198ed351583214c26d380c8192611d5c665d0b3096ae930c6420cda70189414c32b31ca3200419654f604c610b4ee4aa08290cd571d96424c34a30a82a0261475cc6215110da0a2b06429845d75d8d420c32aa9ac2194211edd950142329ace3b2c859863954580540ca2ebb4a9218874d9c342145408beeca98a788656535843004317322c42a42196196644c120b92e420a609056a7018d52042e4392c89824136dd9424c2209b2e1b2e849852c74548524c23c3aac021221361d9424c220a3ce9a9e601061e5458c50c876890ac010a61595d65244010a9ae5302a72056671d91520421fbb2a82a663365c264d4930ae0e2b22a0194d870592214c38aaa2a7880219359652cc010c3ac9318a50851e74180534871bb2a8220841175ce65086408dee4b2a868846e72995430862f39cca20c415c9c26354440aace22a6611046d72993504c72b298c2a0041c65c0544c110b60e0a08821064f63189544c38aaa2a6a88418d1526110d10a6ae3b22a8194d97099721cc23b388c8a80655c5c03294420d4ae43028220d9974189308823bb8ac02a2654d5c45410530ab2e1b1ea090f4a424c9500cb0fb28c6a10834d9c76550b40c68a930c84887276454910042ccb86a8aa661c55533254432c72a9b02840847a701943250696b90a920c210f9d85454d10e8aa420e60084797019443c86e8b806518c43535cb5394c40c3eca31a85a045d73d9641c830eb24a8292614ddc5605503287ce8302a31965463d4521482973a6c3290818d9526190b21e48a9a92428863454185404c333322a588021749c4404c2208b8eab22439851d73181540422fbb2a629a219998961d5020a98e8a90a4985a672181411072ba9ac321285725c8644c120ba2e1a8aa39845d731942004316b24a590821179d85354142aa8e6b02a21
  | 7 => 0x6a9021565cb654c12087ae8328400847776544514c278382c890e21275d363887308eae3314a81866652586420c29cba0a2a8065475d35394c20a70e0aa48290cda70185424c21fba2c1288655c5c45494032ae2e0192a22062d5418943c866ab88ca21661359c66550b30d2cc8b08659846c7259530443873a0a4992619598d5190040a88e2a90a498719544c2200828f3a6c6a98418d594418844099eeca16619051e74d4b3004266b96cba0a61179ce6014941d2ac8b0864986546318554482e8b84a290a610f5d3650c810c6aa9308a21045e7398251d0a3b3b0a8a0a21e2991424c1209aae2324609852e72d9154042abb9ac428a810f5d9540c810a9ae42a06498666625845408333312c22a4619554d6190810a5ae4302a80857171192500caa6b90a8a9821175ce6510a10b90ec90a609052d7414d520422e39acaa02418d9506150310da4c2b04849872552d074004317aa0c4a9a21c39915214b309e0e0b22428866a62580540c69aba0a7288419a58a60150318f6e0b2a84886715158331102aa3aa8398221d194d521041087eecaa0a81962e54588430caca39ac4a0883175ce6508010caca6b0c851064e53988400830eb20a628243555c46254e40e1aa929ca40854d7218053486acb80c6a962193dd9520c831c38a9b1a428853474544518829a38aa82a4418d9926114930cb2a6b00a7216726158354cc21fbaac3a1681565c343d4143c6aa830a8510c7b765405050eb9386a928865555c4654c320ae2e1aa2a21957270152510ca8ebaca8980211d9c66510c20ccac4a88a221e3954583510cb6830ec0a92614d5d35194432c3cc9a9e4290d34745895110338b88c0aa2435add53254032e2ae7aa0830864c5358b304831aaa2c3210214d5d54110720e4a84212a21963554986430431a322a2908812d9d85350441aa8ea90a608851e73d91540831ab2ca320881c6151404c2108eeecaa6210845f7558c20042e238aa4292618b5516215010a3ae9b0ca72064e6354852103a2a92c2292611b5c861540438dce4302a221e366458653442aa39a84a88810fdd1654c910caac7288a12147575984321038b2a2a298041175cc65d0810ccaa5b02200865653984200431b320a310a8147dd542d03308f0e0b2c64a0f2754484214432aa9cc228841171da5348410caca730841086365498642c82a739ea5294838b9926214c108beeca98a50847671d97434821fbb2a990821175cc6454021b30e8b12611061d5498c540426d384c5a1a6117dd56388210a6eeca88822049d7690440cc29aba4a2208431d9db54544208daed290a2205577350a51083a2a94c2190638e5926014f219cae33168710e6662584540ca8eba6cb98221b114c624c521a6aea20c800847776544500cb1bb28c888021275d06308730aaae22a4a710697765044
  | 8 => 0x9530c2108eaec194a21061d6594e411030f32aa920e61599c85394440c5ac929642184767119643082b2392a628a819594e610ca20a6ce3b22a99854c7254c534431d2a2c019021175da53902109ace331686985577155130442ccba480202618dd51610c910ab4eb30a6090656535844004346392c829261969d5600c831caca6b088108671615405010f1aaa2c3a984172dc9314c220b2aeaa08839847576d4841042e4ba64298241171cd6550810a9ce42a6601854e72d4d300422e3b2a690c81655ce60504418bce7b28800845f7558c4008296b90a820c211d9c665d0c209b0e0b2262986555398432042e83824298221531c954d0d30c6aa830a81986366498753082e8b8c84982410fdd854c8510c38a831a428843d74189530428eba4a598221171da53484209ace232885986366458453c831b3b0a8a0e219594e6190830cb6cb29a401046c7259531902b23aa42902211d5c46354840a68eaa08828855571d8d5308363a98c498a43725ca644c120c3ac8a9e420869553185401034a3266088021179db535414287eecaa0a910f6152546401032cb1ea1282835c1c14214540c98a6b108690e3564547210832a29cc3212859954861500408bee0b1ea910e4f63189534422fbaac5a06619654d600c8409a8eca8a429853474581510ca3b3b485288811d9d9515004087ae9b0aa59856575cc5210870eb24a790c41559cc6054432a9ce5aa2a60853574d4910042e4392a3a8261369c262105309b4ed90ea09852c72581540cba839aa2a80658d5486150040c3ca931860084597018d52106ad386c329c411d5d8321454087aed2a484216595398032842b8b848628a813c5c46050b10e4aa4a10830855571d4f300829ab8cc52a0411e9c06590c21c6aa93086408714548853044236392ca20a615c9c45494032cb2a7306421069754185404c368b0ac1aa661ac9916010410caca730ea42045d739825110ae8b80829842187950635081099ce5b2c839866562d465150eacbacc2982418ed906055121c6ac82a2438872754149214432aa9cc228881599c46094840e28a920e608861d6555330042adbaa64a8065ca5523254032cd6cb29220086c66298440cc23b3b4a890a210f5d0650ca10c6cc8aa0820872654545200828fb9ac4aa021275d063c853093ce9b2c43985977650441cc32ca98c0a0c219358d521444087ced2a2831046e7299543c4334a96c090881a950861501209b2e1b28849871873551500cacb3a64310a61595cb5194440caae232a42986c562984404c28eba6c329c21d410e51540328eaed2944210d2c7255142cc716b22a4190810f9d0650c010c9ac4314a7087165454e510821eba0cb99021d41ce5154032992e4302829855573d8b515022f398caa0c419558e5190020a3ee8b12a71062c72592528c6373b0a
  | 9 => 0xce7306a810c7a701944308727b18a510a61725c35294b30c3ca831a84196d051580414c29a3b2a888021e41913044010da6a2b008298536740ca511032629ac421a41565c06414d219b4e1b26429845f7654c53886ab39ea8a8841f0145214c12087aedaa083106946494d100431bb2aa2a00818d551611021096cec28a83a066452586424c69c382a82a243879516308010c3ca931c20086ca70988404c38a2a282982218d9526190821b92e9b12609053772505501068eb98a9a10439c5466014032c9ca6b16a2205367194942d02b3b8aa990441559ce6094432c6aa8b08600861e6494c320c2e8b88809862195d4e6190942cb0a6302a2a174953d89200832cb2ac708021995896115230c68a8b1420886575358432442a7baa60900411b9c86510c1087eecaa0838846d72d9743c42a6b90a99842187d536354910c3cc8a9841085d1710cb304c23b3b0a698a43175d46350a10c68a9b0a4088476711944308762316c2aa2619658d50140418dcedaa2a40872552105219022fbb2a629a834ddd56350441e1ca8a92600856672182510ca6cbb043a82619a549600c810a6ae2302a81962e751894350b2731aa5200218799253d4810c3ea8b1c208854d72152538432b31ca220041665d3214c120caecb98220084da75982324c32b31cc229841175db530c721acae5aa0820845c73593504866b38ec919661359c46590b30c3ca9b1a84084db70596214c29aba6a5880219954a618c01087eecaa0a88871454987304428fba2cb982219654d6090820a6eeca10a2a0477765445110b26b1ac5aa021359c7640c930a3ae8306a690c5d73997219021f3b0a8a164117dcd6548110878e8b04a21956775505210864f3a6c790a6199549610c8308b8eab16809845c73595204432ca9ac1214819954a6110010c6aa8b08801063551582411022fbaac6200214d9d641101108dcec2a2859055673101511031aaa2c0208218b5536048020cb0a6b0064a0cb574181214422e3b2a6a1021559cc6094432c3ea831aa4884747558443486e9b8aa8984415c9c64254032c68e9b2a20084b674d8f218872c2a2c02966156dd5414c220caca730c852063654584320822f3aec9992610fdd95415031c9ecbb1a4210e655258432d0637bb2a429083c594d411042087eecaa0a21951c74589531021fbb2a82a2419998961d52328b8e6b14a80869964980324c32731aa418021c6550404c0108eaec2a4428861e6458c520432d31ac1aa06587d974350832caaa6b08801070d5494d200832d29ac019641535ca530ca10b94ea31260906b36418540102ab38ec9a9a856a5d3214c12087ee8b00a29962e5458b530424f3a4c528e6195d97414c0108eae2b28640855773509511030f2a4c7200218d59151cc4408eae3328642064c6354942042b9380c528c8517dd
  | 10 => 0x64d63948400429ab96a820c218ddd2659051093ae9b1e429843d7499631c822ebacc720421555d4414c0108bae6328801043e7615140883a9b2a60880219558e6115220ab4ea20a609061e6458c540832aa9cc3214818b5516215210c74a9300641047a7019432443a8a9ca3100419398e6215030a74e828aa01961c64d4d504870eaa2c6200414e1c15410521a6ce9a8ca31951f7454b304430f2a6c6a1065d45453088020cb6caa9a200854e73041520431daa4c0192214d5d251107308f6eca80a0195ca728c5304830f324c6282439594e61908409b2e1316a8986d361d81524c316aa0c498e43179ce6590420c3ca931880086c962d4b504c31aaa4c321041d4cca5154032c6cc928e439063454987204426d3b6a298441935886254e108eae232a8610719544c22004392a92a3208814b9d352948109a8e2b26a49855771591538824f3a4c528a6136dc16488530c3ca8b1c800852e74d85521031dba6ca8802187d9553500408f0eab04869055a73d91500ca3ab8eca99281535c860d4d21aace7302a21945d7518d42903a4a926088021745c35194730a6ee2a90832045d73195418831aaa4c21002117dd95314c219cae2312609064d6354820042f0b8c84982418d55161908328ecec196a2a064e6354a100431caa2c1210418d5906454420ce4c2b00a818cd671d9152cc316aa6c4a1841871506350920c76a8302828854e72182539032da9ac01924317dd95314c41caec728a431845f7654c534864ebb4c81926136dd9214c22087ce9b2e439846c7558843482acb8086a8065175cc6510b10c9eeca90659861e65906404c24f3a0c610e611b9d85450920c9aa7b12861064f6518d210866d380c610a619954b61500408bae632c85085667218c51503932a2a5a08210f5d6640c820c3cc929865204d970d97414c25b38ec899283a59cc6050441c58c8312a68843d7419632042cb3aa8220a619594e6190a10c76caaa220087465394a5110346b108220261559ce609442087eecaa085905d3754c1100425b3b064a08839354d6210220b94e530a609065863d81544870f2a4c629821999496110010c9ec6a92840845f7058e544872d3a8c0a0a619514e61d0921a74e8192a019725525044110392322a4a88811e9c06510d21cccc4b0ca898c5d73994400432bb1ca290881b84856008720caaa730c841055975d013004334a94c018821b45853088010ab0e9992a019554715973048335314c02a0635cdc142145408eae332a861065653986420432a29cc218a432d5d06048710d66c8302828863671596411031b2a4c3a8065171d95348610a3ae6314a990c3e76951418429aba4a220841e250b404c120a5ce5b08a88845d76152320c61fba2ca98c41359c66550130d2ac6a0ca020e55639465090a6c382c890e6195d9441487308b
  | 11 => 0xcc369b0cc3a82614d5c76395321aa8e2a9c649045f7654c408431ab20a390a812d5c46050a418baed29c801866b65549401022ebb4a628c811d9d85248510a6ce9a8ca39855a758c9304822f3b6a8a9c41175db54cc2108eeecaa6200845f7694c2004386a9aa520881335ca644c530a6aeaa10820854d73182520423b38cc7a9281179ce60d5010aace6304a21045c76551304824eba6cb90e61a35516210c32c5ca9310a40862c6454932102e5394c498241595c75294840cccc8a92200861e6454c320832a31ca29088199d496190931c6aa930c400874a75c853048237b92caa1a41369c363c8530a9ee4b0aa7106595358032c823abb6a420c21551cd6454432a6ae32a082106646454b1004334a92c0196618ddd954105218bae632a840847571197438830eb24a628841179d8534c210c3cc9298642071553547401030eaa2c7a8841175d76348640acce5b20a2a055a75991304821eba6cb99221e41c14110530878e8b28648845f7650d5010eca3a2a290a619614d600c921a3ce6302a8087147155330042d9380a220c81369c06488530e8aa6a90820871754105308422eb98caa0841559c45494e20d1ac4a00809847a76d4d200828eba4a4986218d59064944208eae3b28652065953580418823abb08328443355c765d0b30c3ee6b24a518c3e74d96310864fbb28220e618dd9741500108b8e6b10a8884d776504414c2ab388c4a9c814d1d54150110e2aa929ca21045e731815290726b1ac42a021535c8540c831c68e8b08a0a16595358032c8726b1ca5a8881179cc65104218dae532880085c974485304832ca9ac0214219c9866014c21c9ac6a9480085717010d511030faa0c6a1241871d5640cb308b8eca9a851046e7219430043982a6c090a21c955152104109c8e4b188290e2d64588530432aa9ac2298859554e61080108bae732a858852e74d4d520421ebb2a990821a91925244010c38c829aa090c3c74594314828eba6a598021f0105214c120c6aa9308a21955970d97304821fbb4a8100218e55260d4432b92e3b12609053674d4d510831a326c2a92218b9516210f21cd2a5300641845d73194420423ab8ecba1e41279d2628c730e1aa8a9ca40856475487204422f39cc1290838bd516210310a74e1aa4a998f2654547200830f324a619021c954a51d0040a98e4a9c628863564987538870f324a619421555cc4254432a3ce8296610862d64548200432b31ca310041a358b4010330caacb29e210873370505501070eaa4c62884195d9653440108bce632e840866562986544cae938864982414d9d252487109b2e1326a2987145458e104432731aa4200210f5d854c8510da2c33006518c5d73195211026b38cc52a2614d1c14154041e94ea312609045d7694e400431bbb282a808347dd1514c220ab2eb3226090
  | 12 => 0xa9c21175d6631001087ce9b2a40885557115153883a4a9261080211d5c76590830a3ae9302a7084d97018d21042b3390c0a88659658e60150218dce4302a818c5f764c5500c74a2a0c2a026117dd95314c40c3aa8b18800851f74585539032ab1aa2200414d5c462d5110caac6a88a22155975d0d3088338b0cc0298418b992520c810c3cc929e632055573d49511022fb9ac528881179cc6055021b4ae4288832045c7654d218838d2a6c09804193d8e5248410caaa6b08800855b70d953004347322c42186553dd530c8020c3cc8b18a810d4d7214f30043a4b96ca982411e9d85454032bc2e3216409063a64540500ca3bbb2a2288878759253d4810b1ae990e609066952580521072b29ac2190418e15160cc510cb2c6a80a02152d7494920c4358324608802187593530c941a6cebb22828845f76550434c22ebacc899065955966110330ca8cbb1a6290d5a73d86500cb0f320a790a439598d5194242a6ce2304a81961d65d0f420cb62b12c2206614d5c6625503293ae8328439869a64983214c21f3a0c0a9063595c86314540e36a9b02608843f76150204432b31ac32a2438d990518c5408f4ec28aa0195c672d0521cc26d380c990a6174dc5404c220acce5a8ca220475760ca511032b29ac2204418d1906154d208bae7b2e858851d74d4d30082b23aa6290a41d194d5148020d3684b048498559708cb504cae2b8c859824172dc954d4130c9eca31a85906b041181211022ebacc710421875536348420c68a8b0e408849d76d50424c26c3aac010a6199548614c810b88e498a439851c74585538423dbb2a02848333dd952149308ece232c849870e64548524c2a7390a8980418d9d85488510a9ce42a6610855671d92538829c382c2aa0418d99151c8720998eca12609065765945300832ab1cc32a2655a9c861540329aee2b26a49853675d062150333b2ca488021995496190a308eaea30a840861e6454f510830f324a6294211d5c66295330ccacab0c859061e6458c504868f3a0c4a9c219398e52144408f4ed28a200845e739825110b0f2a0c6a1663479ce609532199ee4b06861951e7414f300834ab22c2190631d5d83254440c6aa8b08800843e7499621cc22f39cca21021661c14250130f10a8a12609058d7418930482e8b88c4984414b5c85450210caac6a8c802043e741805244386aa4a7900419998a61152308bced29a6510d3471551424c22eb9cc1a8a85655cc6050441cccc5308a8186595258052cc22f3a8c810a61745c32148530c9cc7310a40846d7299743042d9386a220c81d49453048020caac7308a810637719974150352a10c2a06410f9d261d413287ee8b0ca00861d6498c53086e539686982412bdd161881208eeeca98a2a061d5498c50c870f322a619481b4985600c930a5ce831aa42049d7418121
  | 13 => 0x6510010c6cc928e422062d6498853087a8a9aa3200812e1c16448540a9ce42a2600866552584200426cb80c6a108187152630c110d28c8a9a200872454d89214432ab1ac2294219c9856015032aace229a601069561904404c23dbb2a028263355c46050b30d1cc4a14839863a54580420834d322c019463b4985600c831e18c72928520d1e740415304237390ca20a619c5856015032c3acb2a686195a57218141107c53a64298241279d06510930c3cc931ea408690644c110042aab9cc1288814d9c66295020ea2a228a611047675991314863dbb2a0286870d1d954440109b2e131682986c876485304831a2a4c3a1221875506348420ba2e2202609043d7498b530866cb84c3a92619a58a6014c10caac6b08a91847471580544cab2b90a210a810f5da540c820a98e4b1aa1a1e4d6214851cc21fbb2a82a243365ce6088520acae231aa42061e5498e200430f2a0c6a1643e25894010130da2c2b00659851c7454c534830f322a6298411d1c56510d20b2ae3a10829862d5458a430cb8d2a4c728065c9549511044093ce832843987c27118930482d4ba643902419319621485308eae3b28642046f765485250e2f3b6a8980618d5516115030a9aeb3106418c5f7694c400832aa9ac3214418799153d4810c6aa930c80084db70596424c34b31a822808355dcd6454642e88a428842984da70988434c31bb20c2aa261951d5610c930a9ae42a46418c5d7318154c8733292c321481699d351487208ecec29aa32165463d85544822fb9ac5288218759654cc0208deed29080084da70d90214c2d838a8020261335cb65907309cae2312619061d6494c32906373b6a8900415c5c05454432d4ac4a08a020e7261580530872ab88c6a8e41c55c4544c110c3ac8a98a50847571997430822f3b0a698e210fdd954150308f2e0312a620da870509404830f32883202618d9516108010c6aa8b08801852e7418e5210237390caa086117dcd61d4142c6aec2a2428852d7414b424c23b3b064a888117dd95390220c9cc6b16a80859574904414c32ca9ac190c2195d4c614c9218ece232884084e672991314872db2a60900418d9926115020c5ac8a9643185727014e5190a4f3b682a0261175d95308010c5ac929642204ae729874350a1ebb6a819221565c34354243d90c5b02a2984757198f52502acb80c7a82431bdd95214b308eeeca88a3a1e1e6494c518829a38aa92044156dd5614c1208baeb31840086366550a414428f39cc12a06556dc1544c110e28e2aa4a608555711835350a2ebb4a7104211d1d56190910aace62a4a2105677150d520421ebb4a8286438b59664c8621a3ce8314a70862d5458840882e838a8020261e2d51424c1208bced29a421870e5354b401029aba4c4a88414d5c754950209b2e1b28429847671d94321028fba2c4
  | 14 => 0xe829e600851e73981540822ebb2a6200418715363509108ecea3246290e5465d8d214432ba9ac2282850f5d664c84208b8e6b2a8290c5e73997219032bb2aa68802187992530ca20b28eaa08829843e74d9432442e9388a5a8261595c453948408ece232886104b77655041486abb8ac4a9c81175cc605444296ae23028420c5e739875050a3cb84cba1663c69504354032a6ce8192a21043f76550548cb1b320a390a61171cd65486408bce6328829065652185524c2ccba064984419658e60d5210b8ae32166190659539804284326b2a641904165dc94110730a9ae52986520638545804348338b0ac1aa06593d4c6250d21cb2e031aa5a055673d4651082b8b80a910843365c06548730d92c5996609858c74548524c31bba6ca880218d1936154d2087eecaa0a89943c74595304421f3a6ca99221539d8524c930a38eaa16809871a544c1200426cbb643a826117dd95390010a6ce3aa6859047471592508ca2f398caa1021479ce6095010a9ae6082a408555739825190a2fb9acaa1221559c460d4d42caacaa98830863554d85320422fbb2a4296610f9d06254e109aae3322659869864d81524c2acb9086a8065c515141cc310c3ecb2a2600843d74181520c70e32aa8a1261171da5350810e8ca6a92a2204cf72595414c30e2a0c6a12218e151600c910a98e6b0ca42059b74545308823b38cc52a0210fdd56408010c38a931c808872471552520430eb24a8192619558d61150208beeca9c401046c725954344296392a8a12618795263d4810e30a9202608870e5414b424c22fbb2a618021725ca214c120a74e1aa4a8195b17098d41106ab398c0a8c85479ce6155032a9ae4304a708656539864288332a92c219081565c06354b409b6eca0ea09863554986420423b388c4a9821539c85494e10ca8a6b08a0a164e6354b5110296ba6a5290219398d5288010c6ecaaa220086716158053c861fbb2a82a6654e9c06295321c3cc929e43205ca769093048335312c02a0658759153c8620c74a8b006590c5c7359441c821f3a0cb90a618b5496010440c9cc6b10a60846e72993504c71ab20a290a81c35513048020acae321aa40869742986424c30f324a790861995885110520a6cebb0a82a0474755843244296ba020a9021179cf6588010c68c9282200853471581540ca2eb9ec4a84831bdd95214a30c6ca8b08a6104d870587424c31a2a2c221221c5dcd5410521caaa7308651064e63988540422fb9ac52a0219554e6190810c74c9300a81943c74580514cb0eaa4c6290218d15261101108f6e0b2a8690e566354451082d2b90a6a08838d9916114f21e8aa6a94a2205c971189304821fbb4a99082155dc565cc1208bae732e82106365458442c8732b14c22a4611d1d56190940c98c7292420852e741825204333294c219081179ce
  | 15 => 0x7a7018d521069d3a6a328065875506348410c5ec8312a89861e5498c5308236b90c0a88871d5d46150c10c38a9318808847a70194424c6e4b96a698441175ce65d081087ee8b0ca11951d74197304826b388c918261179d85454c10c3cc929e422051f7550a41cc2863a2a4292615cdc164546428b8eca92618859b7458530482cdba2a5a82618e5926014c10b60e0a0ca020c3d74d94200426db82c890a6155dc554d4130a9ee4b0aa72066552d854004267bb24210e6187d526308110c6aa8b08a910636645531084333314a22004166dc15450930d32c2a00809863561186540ca3cb80ca21843479d06294c10cace231aa420c5e73997428428eba6c029a85275d26294530a9eeca90a4985597594d200823b388caa10614e5c06315110c6cc8b08a5084db70590514c38d2a2a690041635d321cc320acce5b24a21949f74595214c36590ac010a61369d841d4130da2c3200809859874547504c21f3a0c0a94639c54560d04409ace3b2e8498474755844244296392c6aa643179ce60d5221b1ae83126190474715953290332a92c2290619954a610ca41c6cc8b08a81045d73194414826cb80c6a1441d4544514c120e8aa4986200855471589530422fbb2a5982210f5d2650c010ccec430aa8985a674d46214871ab08c32a041a5186405013099ce5b24629862d6494b219032a29ac221a439554f6150040998eca12619045c7654d21082ab398a4a8881f09493044010c3ecaaa2641943f74595328425a3a2cb884218b54a61d00408eae3b2c851869564106214c38c2a280984414b1d54350b20a6eeaa08839065553185438423abacc3a1843955c46354b10c38a931c208851d74d84534861f3a0ca100216c9c35410610e92a4982400874653547200825b3b6a4a08838d5926194b10c38a8b18408863454d85304430f322a7908418719253440108bceca9a432062c6454931103933a2a420821741c5404c2208f6eca80a020e1e6454c32042cbbaa8220e619694d600cb21ba2e020a429862f65551320cb0f324a790821475cc6095321a6ae8194a21063964980530872aa9ec299021171d95350a40e32a9a1aa01945d7694c528426cb80c810a61179ce6510420e34a931aa01943c75590324429d386c8aa6638799253c8610e8aa4982200843f7459530483b1192a2a80659318f5248510c9aa6b10810857070591510831a2a0c29822193d95524c010c6ca9b0a800870f6394942906a739ec4a9021179db544c220c98a6b106390749524c120c42b4b9086a80654e1c16255010ab2e1b2e608863664d47214c22ebaec6a14818d95161d4032ab4eb212609062e5498b53042b8b8ea928065c354d5210440a68e0aa08290e1e54d8d42c870e32ca8a12614bdd151c82209b6eca0080985d271909304830eaa6c690821655c45410530a3a
  | 16 => 0xc2ad3ae4298241895486150040c6ac8a88a318564754c521c82ab388a9298419598e51900408eae3316a6a05e170105214832d29ac1988814d9c75495032b28e2a00819866552584528c346298c4a1a85e4504414c220c5cc8b10a81874671149324c26cb98c090c41a958a4110110cb0cbb02609047576908515029db82c2aa6434d5d74254642c9ac4312a72045d7398054082cd3a6c3a8261d15453048020caaa630a802078b745093048316324a4880214d5c4605502087ae932a64086356498453c823a3aac321a434d5d25110720c6aca20a42207497298d500cacdba2a298241a5584411013087cec2a2810855571d52530822f39cc129483561cd4254032e1aa898640105547358a511030eb22a7a9021179ce65d06209b4e032043986365458443cc64f3a6c710a610fdd95415131d34caa00809855a70d92530422e3b2a690821871cd6414930caec7a8a42a043d74997320434b324c229261175cc6510a108eeeab0864104cc72594414c317324a590821339c865107308eeeca88a39855571d805348769b18c090a21569cc42540328f0eab00869072671548411029b38ea92a0418dd516010610a6ee2b04a990e2f6454931102ab388a9980214b9cb5495231ce6cb28a401047676d49100430eb24a628c41965c06548730a6ce8196a2a054e72d4e53d078aaa4a298041531cd528c84187aec2a064885a574949210870eb24c629821d1549610cb30cb4a6b06651054f7258553842e838aa9a8261c95484110010cb4a6b06630851e75901404c327b2e6090041179da534c7219aeec90842985b070504414c267396cb20a618b9954290720cb2a7b02651051c7454b304422f3b6a8a98219394d620c0209aeeca88a2986556354451102e838ac4982418e5916014f20a3ae8314a72043f76d50204430f322a790c8187591530c840a3ae8292600869b64993504c2e4b9080980210f5d0650c520acce3a94a42043d74997310821f3a6ca982211e5c3650c9108dce53288608537755814110667bb28421261479d0534c010e2aa9a0a60085367198a540cb8c2a26188221595d74254642ac8e4a9c42887155418d510ca2fb9ac428a810f9d365cc620bc2e1a8a439055970d50430cb2a328c690a211d9d852487108eae3b2e86905677250d510826cbb083a82611ddc5650c940a98e4b2a608853671d5254c826d384c518a61175cf6590010c38a8b1c8088659639805408365292c029661725c06348520c9ac6a90a4205b070505404422eb98c0aa4431d9c46510930ba0e0a08829845d73d97424422eba8c690881179cc6014910a6ae9a9ca21062e7694942906cd3a06498241b4586600c930f128520a609052d7494b20c423bb8aca21a41475cf61d5110e66e0aa08290c5c7358b505061eba6ca192214d5d03254440aaae3b16a6a14
  | 17 => 0x12818d1c765500408dae432886884d57119642cc32b29cc220021625d3214c120aaae3302a71046e76149208432a31ea290a814d5c45410520ab2e0294a398476765454008296ba0a729021569ce504c020cb2e031aa420e3a54980510cb2b31ac2298418e1516010d1087eecaa0a918e5563984548c327320a49926117dd95314f40ccaa430a80084d97318142882e0b8c84982418d590518c5408eee2b2a871051e749815388237bb2a429681179da5350a10cccea3126290e556398452042aa38aa898441369c0648c930c5aa8b10a6084d571190324c2a639aa429221b45c06150130c9ecaa9a40105367414d510825b3a4c518a4393d4c624c521e52a8992a01972772508515023bb8ac928465565c0531414287ae9b2e43186356415121443172a2c4200419619530481109cae3316809054e72d4e53906d2b8ec8a10851d9da4254420c5aa8b108118659539804104317aa2c4202211b9ca65cc440b34e8312611061d6498f520431b2a4c32146556dc1654c110ab6ea98a61106c942580424c2abb9a85288811d9c46590810a9ae42a0659847576106500426cb84cba0e618d99754905108beec992a019566721015110392aa4a290041175cc6054841cd2a5300642046d72180544428e3a2cb982411d9c4654c840f86c390a60906356559321886e4b96ca98241179cf6590720a68e2aa0a89843d76950530430f322c62a021475ce6055321aa8e2b1aa1195e17190a3048332b14c3a9821179d85354542e1aa6a9280207c061c85304823b38eca196818e5916014c21aace22a2a71046f7654852c428f3a0c129c419318e52484309a8ec98a429845d73983525063b38ccb19081969c06354b1087ce9b286410f0d544c8320823abacc2200418b591520c8108bae7300a80853474546218829aba0c0a8841e45513044010a9ce7a94a4207255254540102ab388cb98241969cd60150318f6eca80a0a0d1d74182538432d29ac019481c69533254032a5ce831ca4085347550a41442a6392a228a619c58550140428baec2a6611045d75d8d428831a2a2c3a1a21c51c55454c108beeca98a40869b54d81544c2a6b9cc1290218e5916014930a6ee8b04a21965465105214c26ab8cc5a0261475cf6455020c6ae2322a3106726158053c8332a94c219063175cc6590810a38e8a8a611047a70d9432d06ad386c3298818d95061500108eeecaa0820874952d01300438daa08098621935945210930b52e990c60905ca76485304823b38ccaa1841699c85350441a6aedaa0830843f74597324428eba0a5a82614d5d74210410ae2e0194a22062d6594a41102adbb2a710041179d8534c020a3ce9b0ea690d8c7250d42cc32ab1ca3100418d9945488510a9ae5a9e600864e65588404c31aaa4c321065cc1c1415404193eeca10849859a74d41404
  | 18 => 0x24c930a3ae9b0ea690f0d6454852cc32aa9cc219421e2508414c12093eeca00819845e76d4d5150a37b92ca98221665c04110130cb4a8b006418e355498642c823dbb2a02808747dd54210730e8aa5308a598634545842044335292c019483a594c61500408bae7b2a8290c7776544400823dbb2a028243e2d92424c12087ae932c640845e73996211034d322c0192611d9db5348710c72a8b00641065a73580540872ab2883980218755263900208baeb318810853676551100432ab1ca320081369db544c220b8ae421aa21946d751894308327b28a5a1261d25c843540329aae332a859854d72151300c26cb80c690a8156dcd4254032cb4a6b00642063564587530829a3a2a2a0c41559c753cc0208eae3316a0a1e59535805310b2bb18a290a81539cc6054840ab2e1992a1195b07050a41c429b38cc4aa065a31906254530b18e4aa285984b572181411068eba0a798041175cc6054a41c74c9300a610c5d7694c40043643b28498241179cc6054841ab4ebb02608871954101308821f3b4a8a06219598e5194242c6cc8a8e421065553584408823b388caa1021479d353cc0108eeeab0864206cb765093048332a94c2290819554e6110020c68caa0a808845e7318154c862e39ac528821479ce6055010c6aa9308801063964540500cb1b322a3a80659594e6114440c3ca831a8418c7571181540cb643126498441ca54a6010440f2283a02618853575951100429b3a06428a814d9d8515054087eecaa0a9084ae751894350a2fbb2a61844136dc161d4930a9ae5a9ca6086557119521cc32ca9ac0190410fdd9540c810c98c7a9284a062e5498840042a6b98a8a90219554d6190a108deeca9080086555398432906acb8662a806387552630c02087eecaa6421064c5398b414872d29ac019421951cd6114930aa8e2a9864904b670d95411071a2a2c221a219694d600c810e8aa41946218c3d74d9621cc3a2a968398021365ca6010530ccaa4b0c800861d6494f311022eb9cc1aa043551cd6214540c3aa831a841069942580424c32731ac5aa443875516315021e2aa820e60084777159542442e5390c2982418d9964190110c9aa6b10a60861d64d4c324866cb80ca20e611d5c765909108eaed29c6218e5b6554d308832b29cc22042117dcd6494820a68e8a8a821045e7319521102ab388c5298211ddd95114543c6cc8aa6200867151d81211029b3aa8420c21c3591520cb30e96a498241086a56290440c4347a98c4a1a85475d06254c20a3ce7b0ca81945d7318154486e2b88c498241551c56454e2087ee8b0ca01955a70d5130082a6392a618a219354e62148408f4e1b286520f4a7094930042ab38ea998641475d06014d42c98c72928520ec962d40404c2abb8ac8a9c81359c4640c930d96e1b12a29853b74586500ca5ab88c0a
  | 19 => 0x7b0a20084b67198b43d0aa7390a698021a61936054530ab2e02a46418e3a54580510cb1ab08a3202812d9c36250441a6ee8b2e210863564984520434a30e82a06611b5c86054743e4aa528c822045d7398354c872bb18c2a9a411e5c3650cb418bae6302a32165463145215022eb9eca20021d194d52d0410caaa73086410e5553986428832ab1cc22a0431d9c7654c940c3ccba9e86a14db70595404c38aaa4a620821a55854010130b90e4b0a611061d65150414c2b8b86a928865965c36550930cb6cab12611079141580414c23b388c4a9881475d02054c20c3ac9298400861d6494c20842a6b94a61924155dc554cc220c3cc9318a5084b5768c941107872a4a4980218d5954110430c6ca8b0e8790f3254945500cb16aa2c42a06336dc96010530aaae7aa2a21047671d94329028eba0c4a9c81a6d516010930acce231ca4086ca70588404c28eb9cc12a643871d5640c930c3ac8a98a61071553546411022eb9cca90a81a5592610c9308beeca98a62164e6394a40042a639ac929021279d06048530a6ae3a12a020f45514c3200828f3a0c4a98818759253d442087aebb224220557754c1100422fbb2a629a41b2d8b60551308bce6302a3a1570715405050b0f2a2c710021711c95148730ce2c3300a790d3571d8c54442e5b92a3a8261175d95310010c3cc8a9e42085c9729853048333294c2200218dd516110310a5ce9a94a518e4d62148314c2aab98c128841559c454cc0308bce6302a5a0d367198954082adbaac898241d254a600cb3087ae9b2c648861c6454d100432aa9ac219683875536350820aaae22a4a61064d6398b540422f3b0a69844117dd954cc120c3ac82986490e2d5458a400832ab0ac029a4317dcd6548640a9ae6302a42043d74987504cb65b86c4aa261555cc5448421ae2e3214a019476711815210f1a2a0c2a024117dd95310220d92c4296a09863554986430c61f3aec2a1281995966190b20c3acb29e812051c7454e3248393322a4208219318e52508108eceb30c84a05597018f5050b1aaa6c088021b2d496008530d2ac3a00819845d7615330082ad380a69804193594624c120e2aa6a08822064e63948300430e2a4c7102218bd536254d10ab4e6322a0195967318141106b8b80a6a8c851d1c5658c9408bae031aa890e1e6454c5188296392a6a10838b99162d4c108bee6b10a9886c93258032882a6392a699481171cd61d414287ae9b2c658869a6458351cc22ebacc720041c51915354440c3cc9298a21066662544511021f3a4c528c619654d600ca40ad4e4324a01953775504410862f398ca214218b5915214a10c6ecb28a802045e73997211025b3b464a0883d25496014b30ab2ea20260085c872553504c34b324c219661569c06114d42c3cc929e43104d875582424c30eb22a790c21931905
  | 20 => 0x571d964344332b10c428a81995496190830ab4e0312a60861f6594d401029cba6a2a8065995496114840a68e2b04a81962d64548520c68f3a8a8982214d5d54210521c5cc9310a8086546354521cc2acb8662a84636c1c14110720e4ca8a92200867365545401022fb9aca20e41a51906154930ab2eba1aa0195ca72109304832db2aa6a0081535ce6054810cb2e1b2a42985b070589411074a30a82a066127dd95415330c3cc8a98651057071592500cb26b1cc4282834e9d061540329cae3316819067061d8154482e9b8ac498241359c46590930d34a8b00a99866b525803244346b1482206618d1536150110c9aa7b1262105d071551308832da9ac0194438d5516010621b30e8a8a6110634715905048636b90ca200219398e5284010ae4e120aa020e4e53988520431ab2a8220c41479d0544c020a98e4aa0a89864d6394820042ad386c829a85595cb54d041087ce9314a21847676151210871aaa4c3a9841551c5544c1208eeeca88a2185c97210e500cb24a92c0296611d5c56590810c74c8b00a610c5e7319440043e130a42982418dd506150120aace3b1aa61043e74996310832cb9acb08021365c06550730c6ca8b0c841049d7418f21cc30f2a2c6290214d9d25448510c5ecaaa2401062e54588408831a2a4c221221179d66548530c6cc9a8e42a05947050441cc392a9284208218e9916015031a5ce5b22a918e5a53580430c31a2a6c4a0e21969cd60d50328e8e2b2e64a045d7694c520434d322c019063b2d8a624c120aaeea986200854f7654852cc28eba6c229a856c5c354507109b4e1314829855671d525308297390c62a2219c58660d5331acce3b24a40846e7219743082b3390c128c85559cf64d4540c3ac8a98a60845c7694d4208267b92caa02618755263100208dce432a831866a52580320429b3a4a49084372dc5424c12087ce8328650845d739964204326a92c0190639358d5288010a74e1a0aa020c5f7654c400821eba4c528e6172dd1214c120aaae2300a6a164f639494204326a9cc428881c955251c8020aaaeba0a6008745320c9510821fbb2a82a4414d1d13254440ab2e0192a018c3d76d5041842ca38aa8a12614b5d643508428e8eab0e84884e572181411072d29ac198c410f9d263d4910c72a93006590eca72181414c26cb80c990a614d5c46095020a58e4aa0a89865753584325078c2a26090221c95494110410d9264b006590d597510530482ad3aec098241475ce60550209b2e031aa420c3f7559032082e4b908698241561d5644c120a74e131aa80859a74c85304828f3a6a72982117dda5388010ce4a3300a01962d64948208423bbb2a228a654ddc565d024087aed2a642105597014e31c863b388c6a90814d5d36214540a9ae5aa2600864f63949211032b31cc22828536dc96094530ba2e
  | 21 => 0xa2f39cc12a4432ddd941d40418b8ecaa660907265454b100431d322c029e43179db5350921998eca12641955571153308c2733b0a490e218d5856015110ba4e2196609851f7550940cc3a2294a310a619318e5250830f22c2a00809845e73994211021fba2cb19221355c662d0d30c38cb2a2859847771582540ca6cb84cb21661599ca6454432d92c4a00809866552d85420438a2a261082219694d600c821c3aa931c8218e2d5458b530432d29ac021c219358c52085309b2e7306849045f7654c539068f39ec8aa4431ddd951144408bee6b2a840862d5498a410866b38ccba16616c1c54010230e9284992a01961d5458e40082aab88cb982411e5c36590d108beeca9c2008475711944308392a908310881a5d50615513099ce430282985547548730442e8b8c85a8261555c7544c020b36e0aa0a89843f75590320428f3a6a729c439554e6108210c72a8b00640843d74d85520421f3a6ca19041c394d5290440a3ce7302a8195d17010530042c6ba0a5a12618d19152440108bae7b2c8210e1d5498e400432b31aa320041559c4544c020ce2c3300a81043e74997310823cbacc019021179d85454c20a6ceb20c808843d75990200423b3b0a698c43479d06254c10da482b00829851e749493044365a92c129261369ce6010530cb2c7300a80846e72d9743c430f322c7a90219358e5290010a5ce9a9ca40843d7695053c871aaa4c3180219359653c8220d2ac8b08659845d73980544866b38ecba16618d5526110010c6aea30a802062c64d8953443a2a94c229261569c06294e408bceda9260085367494a2144332b12c22a0611d9d6610c940a6ceba10a2a063654984500cb8da1a84a8065c5d4d4110521cacc7308a81847671194324433928ac0108419954960d0410c9cc7290800855875505308831b2a4c219041569c06194e40cb2a730042106a94258042d0316aa6c4988411b9ca6510010878eab26428843d74185500cb8a39aa8a88655c5c06294642c98c7292422045c73586529030eaa0c6a10218d55161102208bce6328858863754984324422fb9acaa14211d9c7658cb40c3ce831aa420e977650441cc32729ac4200419659553c4210ccaa530c8520d5471589538830eaa4c6180218b5925208010da2a2b00a39864d63548520432d398c0aa243c595151cc020aaae7a94a22064d5398a310878a39a8428a811ddd95114732cb6c6302a890e646454910042733acc5a0a438d5916114f20ccecaa8a401072554948410422f3b2a6908814b9d06354810b8ae2312619055473509510821ebb6a990a21179cf65d0b108daeca9080085d1710c9308834aa10c2a06619a54960884108b8e6b24a50845c73595424423dbb2a028665555c452947309b2e7300831045e7614930842573b0a4a1681365c261d5130aa8e6a14a22047
  | 22 => 0x281175ce6550a10c98c72928418ec962189308831ab22c229261369c36308530ccac4a8c80105557118a53843c92088098621665d0624c1208eae232e861054e72d4f3004316b24a590c619398d62152108deeca90a4a0e3564986528c733292c2104219594d6190c10a6ae829aa21064c65d09424c392aa464a88658b5516215230e2ce7aa0830845c735952110335a92c01928117dd56308210ab4e0314a6204da7614d308830f3a0c6a96819654e60c8610e4aa5288822059974c87504c26d384c5a0a61d854a5144010ccaa530c8418c777159632502b93806528841631c95450930ccca4b0c85184d671194214c2aab88a5a8261555cc5494420d4ac4208810849e74197214c3a4a92c019063369ce6090930ab2e0192a118cda75980214c30eaa2c6100216c1c16150841d1ac420881987155354441102b2b8ea89004153dc96454e10ce6c2302a890d1d7318154c862ebb4a7204411b1d562d0d20e32a898220086546554521cc23bbb2a710a219594d610801087ce9314a20861d5498e10042d4ba0c4982419594d6108210e2ca8a9aa2106355498643886aab88a6980411d5c7650cb40c6ce8b2e820845c7654930442ad380c929c219598d61152108beecaa087985d171d93504c2b8b8064a8841369d66090930c6cc828e42a043e74d97324429b38ea8a1465535cb6354c10acceba0a429043f76150324434cb12802026195d974148730b32e12a28498557754c9510cb0eaa6c6a1021745c0328c43199eec90e609053671989540421fbb2a819643725d0624c120cb2a6b00640871453504414869abacc2208814d1d16094432c3ac8a98a3106a94258042c823b388caa1841c954b4150010ab4e1a9a601045d7398054c862e39ac3290812ddd561d0841f10c9212609047675d85434861f3a0ca90c61c515221cc110c9acb310819845d7399441882573b0a8a1641331c96550530c5ccaa14829070d5454930043c4a1280982414d9c46055032c6acba10820865a5358043102abb9a84a8841359c662d0130a3ce7b0ca990c5f7358854442cd3a0c5a82611b5c8650c540c68c8a8a62206565398440882c838a8020261659d3218873099ce4328829855a71cc9500cb32310c2aa261ac5056010620aaee6a96a2a070f74548524c2373aec4a1a43475d06014d21cb4a6b00651064f531894350b0e324a4a92618e552600c410cb2a7300432045d76153300422f39cc02a4438d5915114432ea686a8aa01961e5458f520422eb9cc1290831d5c76590b308eaed298a2a069b41580414c354b128020261275d2628c530e4ae2a90822062d6454b210c333312a3a0e419614d600cb108eae332c8610567754c9510cb1caa4c010841559d6328c521f1286a1260906716158053c832aa9cc22002174dc5644c120e62a8a8aa01953b74585500c
  | 23 => 0x10440d96c8984409051d74d4d3004335292c019683179d8544c220a3ce9b1aa6085557115130083162a4c420221565c2524c110ad4e121aa4086375498420442b2b90a6a8881559c75394f428bce7b2c8210d717118a500ca3d386cb21c438d59064944328baec296610861d6454c200431b324c2298411b9ca6590c108f2ed28c200874a705493004332a92c3214212d1d94194041aaae3a9ca62045f7654c32c82ab39ea328e85179db544c020d30a8b0084986655298430042b3388c0a90819394d620c621b30e8b12609045c7654d21102a6b90a8a9c2172dc9644c220c68ecaa620084d876485308829abae83a0021999896115321a3ce829260084db70594424c3a2a92c229661d154d52d0410d96a4b0084987465354a511029a3aa8220a419a949600c831b2ae62928220f0e5454b300438aaa2a62082147dd1654c120a58e4a9a85a055b7055353486aab98c428a814d5d06314540a74e8314a0195987454530482ad3a664a8065879974010130d36a8b04a89861d6454c530870eaa4c7100411d9db53546429cae13168290d1c7358a540431b2a0c2a0641359c7640cb30da0c3b02a89863b65d9110043992a2a3280658d951610c810c6eeca88822043e74194214c21ebb4a828865c5150614c1109b4e7300849853575d0a5190aab398a5288815c5c032d45409ace3316879862e54588408c393a928428a81369c064485308bcedaa2a70865663d464050317b20c4a9a21c51cd5410521c3aa8b1c800845e73994400826d39cc010a618d9916115220a6ee2a10a2a065563546400838caa2a7100410f5d0654c42087aed2a064084db76509304821fbb2a828841471d54290530cb2a4b006518d1d74182538838a2a6c298221555cc2054420c68a830a808851e73d525408237bb2a410e21879526314321a3ce6304a80869664d47214c24f3a6c790e6153dd9520cb308eeeab0e8610e5953980418829a3a2a710a21175d46348640ae2e2322a01952e7414d52042e938880982411d1d56110d10c6cc2a8e80204ad7498a3148326318a4a12814d9c754508218dce432862a049d7499621cc316aa0c4a1841c61cd5494032a92e421aa01964d63988540870eba0c6a9083535d73048020caaa6b0881084d87650930482abb8aa9982218d15161cc110cacc6a88801047b705963250792aa2a5a08211bdd95214940c5ca8b108310e1d5498c5304338b0ac029261175db5410e329ace2328849856575d0a5190b0eaa4c6200218e1536048510aa8e6a16a2a064e6398b540423ab88c4a98810fdd95410a32a98e4aa0869861d6498c520428e3a2ca98221a51936154930f86e290a60904e57198b434828f3a6c6a9c43d84c95154032d3282b00829861e5418d42cca6db82c22a261175cf6454221cd2a4b00620854d73d89520432da9ac019
  | 24 => 0xb28849859973d91401032b29ec2a00814ddd53250441c3ac8b1ea40864d6354a100434b320a390a61559c7544c020ab6ea992601863554987500caabb8aa929c41179ce65d0420b2ce73028220d35740ca511029b38ec8aa4658dd91514c4408bae7304a520d5a7498d500ca9b3a064a8865355c76454b30b96e4aa2609061e6454f218823bbb2a22848517dd5639003087ce932860104d875580424c30eaa0c6a1065565c35314121aaee6a16a2a06c762185544c326a9ac429881471d16354232a9ae6304a42047671d9642cc2adb82a829a439a58a601503087ae9b28658855771589538828f3a6ca98221655c65410730ea4a3b02601051d73d52540430e39ac829e418b59152c8610c72a9300420855671d92530c2ab39884a8865355c765d0930a3ce9b16a690e5465945214c22fbb2a629c219954861508108e8e2b24a01953574144414829aba040a8841475d053d0f208ece3b2c871061c5458c414c30fb2aa8980411d9c465d0810ea264a8aa01943d74196328431aba8c88802187592530c830a6ce2304a81055671d92539038caa260900418b5926214c20d3284b00829869b54580414c2b938064a8881531c95314d40ab6eab22611043f76550408832d3acc021261b2589300c220b94eb212609065653d85408438729aa42088136dc16508530caaa730c850855970d4c5050a3cb80ca212639594f6150010b60e0a08831856575948410432aa9ec2a0041175cc6254041c6aa830a640843e7615141c428eba0a498421c95485250441ab2e0a9c4008476711895090e3ab88cb2184195596610ca31c9cc7294400855671d905350a8e39aa82a2411d5c46590f208bced29a851046f76548521032b29ac321041175d76348620ab4e6324a01945d76d53300431a2a2c319221539cb5394c10c68a9b14208845d7694c408826a38acaa0261c695130880208e8e2b2864a054f70548524c22f3b4a6a10218755263100308f6eca80a09968f54189544c32b31ac3aa041f0d05214c120ccaa4b0864085c972185304829bbb2a820c43879516384010aaee6a90a2a06a942580414822f39cc128c85471cd6155321c6ca8b0c6590c5d76d4c3288717b14c5aa221531cd6454810a6eecaa08290d1e7398154c86e53948298241555c66054e40caecbb1a4210cce72d9741cc23ab88c4a9c811b9ca650c440ab4e0312a7206cb62d81514c31b2a4c2288418b59152148108eaeda96200864f6514a214c2aab88c4a9841365c2659073087eecaa087995a572950414862f3b4a690c21365c365505308ece3b2c869066652584200438a2a283982211d5da5114032c5aa9310a40871b544c22044236b90ca21e215c9c75454032c5aa9310601063776551100429cba0a3280654b1d543509208deeca90a4884d671991324c2b5baa65280659a54960
  | 25 => 0x76d0540842ad380c929c41569c36494e2099ae5b2e839861f6418d524432731aa4288811edd95014243c5aa8312621055a7018a53843172a4c429821c954a5150040caacb28e60105d370546214c2b239286a8841c594f511064087ce832e64086556554f108431aaa2c2204618d9915114432c9ac4190a29856571d532008332a92c321081565c06114d42c3ac9298652066562987538862ebb4a628881535d730c8020c9ac6290849859471550544c21e3a2c3a92619554f6150c10a98eaa12609046f76548529072a31ca290861b4945601473099eec90e619071653547401030eb268629261b158a6110330c6cc9308a81965563d46405026c3aac190a618d9516110020c6ecbb0a802065953980210434b2a0c2a0661475d252cc31093ce831e429847571594400425a3b2a888021479cc60950208bce7b28801071553545401030eaa6c6a1065559c76494c10c3ec8a9a62204da70d92324c26ab8ec819261559cc6294642a38e8a98649071754107308431a2a0c0a0e21959956110130aace6310a2a065a53580438832da9ac0196218d9905108540c3ae832a84986395458053c872ab1cc22a0214b9c860953218baed29c6419571700c85150332b12c22a441d45493044010aaceb20a608846d7598b430870eb24a7908410fdd95415010c74a9300640857170d46510ca1fbb2a82a0439594e610c820d92e0312a89861c65909424c3952a2a4a00818d5526190a32d32c8b00a49845e7399641883a529260900210f5d365c8430ae2e029ca32153470550418872a32ea698a431d9da51500208e8eab0c648843f7654740102a6b9ea8a90218e1936054910a3ce8314a61064d539885204237396cb18e81711c95188530c6ee2b20a090d3775504410822fb9aca20a4147dd16154e108e8e2b2a87106576518d21086a739ea529021551cd4214540c3ec9b1aa48843d74194310861eba4c5a9a214b5d05248210c6ac230aa81962f64549321031a32e8290a81d854930440108dce532a860861f6418d544831b322c22a065875966410c3287cec2a28290e3554d8543042e8b88809802193d96524c010b20e0a08829843e7499532042b8382a820a431b5da538c8328dee4b2a870863654587530826d3b0a29844199d89514c420c38a8b1c408865663584540ca2f3a8c810e611d5c46054b43a98e2a90a49865953980321023cb80ca21c438b9516210030ca8c628a429049d74d8f21cc22fbb4a620021c39525354810aaaea20e60086c9614c2204821eba6ca982218b99262d4c108f4e03288710d5b754ca500ca3ab88ca19281a9d8a5250441a72e8192a01955573149511031aaa6c2a0041659c7549533087ae9328621047b765405010b26b1aa5a8881179d95350820e32a8984200845f7654730c822fb9ac5a82831bdd952082108eee2
  | 26 => 0x9a3aa64a08831d9c76590a30a6ee8a9083084767119443c822fbaac420a615c5c063145408bce7b12a120f155494d510836930ac0196618b9916214c108bae6300a88855771551304822eb9cc12a2439398e52900409ace2302849854e72153300838baa4a620c21531d52108530a3ae62a28410d357550441cc31ab10a320281565c0530c721cccc4a88601064f63149424c70eb22a6194811d1c56550d20998e4b2a809866662587530832bb9ac2292619a949600c840ccae3314a898f8b43509304831d2a4c0280652d9d26444010e18a6a108490dd271189308834caa2c02a6618e5965484010c5ac8a964220715544c110042e838a80982210f9d36588730a72e0314a990e1e6454c3284332a92c310021179cf65d0720a3ae8082a60847776548515021fbb2a820a431bdd95214440cb0cba1a609063762145415028eba6a7980419954a610c840a6ae9a90820843d74d95204422eb9cc028a85179cc65109108bee6b2a422045e73d8950d072aa9ac2100219a5895014031c6acb2a6820861d6494c3210272b8cc5a1e418755163102309b2e0328439866652984511032aa98c2a00419594c6150210caca630a800861f7559032cc2e53ae4298241c31505210930c6cedb2a8220d3970d52540ca973a0c0a90218dd905448510aaae3aa2619046d72d9440042aab88c829a434e5c06215110cacc6a8c401065a73980540869b3a6a328865279d36154b308baeb31c8110634549844144368b0cc12126196195324c120b96ec98440904cd7299131cc32a31ec2a9221c91c654548108b8e6b0ca48847671995430864f3b682a06618e9926014f218b8e6b14a90864c53588314830faa2c620221175d6630821096ae33246420e3762185540430eaa4c710021c919152440108dae432e870865663146405021eba0c6a9021d454d5188020ca8ca29a6290ed161d40404c237390c0a8e879398e6214141a38eaa10829863554586430434d322c0296619694d600cb41c98c7292842045f7654c324833828cc018a814b5cb54950109b4eda8280986c862d81544c23bbaac2200411d5c46510f208b8eab2242984767118152d0e2f39cc12a243365c265d0b30c9eeab10861965963580540861eba6cb18843a59926114b30ccac530ea8084e472586434868eba6c3a9a8555dcd421454087ce93284008634715935204334a94c01902117dd56310220ab4e02a260104d97018d2188347b18c4a1a85875526315020caaa6b086590c5f7654e20042acb86c7a82859994b6150010ab0eaa02609061d6454c320830eb24a61942187592530c810c6ea8b08808851d7418a5384237390ca21843a35894010330a5ce5aa68518c5e7399542842ca39aa4a0883c914942d4540ae0e0a88a2a163554584200438c39ca8a8065175ce65084408bcebb1a8490cb6
  | 27 => 0x41599ca5448510ea2a29824010635659932188786aa660900418d5536150010b62e01928220e5953580328834ab0c8220661999486150010ec2a4a8a80205597010d508cb26a9ac518041479d052d4130c68a830a408845f7654e208428f398c0aa64347dd151cc2208bae732c4320477755864004364b90c0a0a615c5c04254440d32c8b06a39864e53988408422f39ec2a86858b9954210941caca7308a21055b7050d5010e1f3a6cb19221d254d5250040b32e12a0a89847576946100431b3b0a8a0a21179ce6015121ea2a728a401043f74595304432729cc4200212d9da5250441e2ca929ca21062e64548200426db82caa12618dd976444010c5aa9316a60851d741835350acab8e8420e61c554f51106408bce7300a2a145d7399641882d9380a4a08838dd9461500409b2e0312829854d73982521026cb80c6a12214d5d35194420c3ca8b18801045e75991214c327b1ca4a1081871955450b30a5ce4302a990cd970988514c38aaa26188021369d8544c220b94e121260905c97018d424832729cc4184411ddd95114540a9ee4b2a608864e639885484353290c2a0081cc55151880208eeeca88a3a05d27190b504c2b238ac8a9021c594d4110430c6cc9308a40861c64d8d534821ebb0a8102219314e6210d21a6ae2304a81956671d4a52d0eb5380c6a9081d2d493048110e32a8982400863664544500ca9d3a0a3280659554e61148408bae7b28400864d6554f2088334b2aa50802195d95514c0208eceda9aa22045f7558c400c316b24a419021175da5314840e92a4984410871a54d81300423b38ec8a9661661d1614c220e2ae22a660884a57218141106a6b96c3a9a858bd915244010ccac5308a60861e64d4c504874db18c0a128196d9730480208b8eab10829854c73585521022ebaec910a619558c5190140c3ca9318a21063564104504870f2a2c7a8841b4d953044010ab4e0320a690c5e73194200429ab8cc82a265c6550544c220c6aa830a801053970153420863ab8ccb990814ddc56055321c3aa931ea408637541854088297396a8a1221d294930483108bcedaa260085947350941106cdba2c498441561d5404c110c3ecaaa2600861d5498f510823b388cb212218dd5261909109b6ec90a609063754986424c32a32ca290e61745c251885308bae031aa420dd17018d21c4316b26a419281569d4424c120ccacaa96820845d739964108316b24a4194839a58950140418dce432886104d676945214c32b298c2a0081c95d15210410c3cc8a98a5085357598d411062ebb6a5980210fdd165085309b4ec10ea0984767614d510822ebb4a71002196d4e600c9218bae7304a5a0e3654986420832b328a620a43175cc651091099ced21a64194d97098b514c2ab3a86518a438dd954110430a9ce6302a40869541580414c2
  | 28 => 0x4c40a68e2aa0a89045d73980548862ebb4a6294811ddd95114630a6ce331aa80854d7215130042aab8ea729841359db41485309b2e032043986c852580214c23d386ca19083745c4624c120c6ca8b086590e3454986424c392a90832002199549618c010e28a890a60885657210d510cb2a32e4290a61d154b304401087eecaa0a40851e73d5254042d9380a820c210fdd16548110a3ce7b08a8885c9728c5304831ab20c8a8865339cb648c7308eaeb308641071653504410432631aa4a14834d1c554d0a20e52a9292401063964540500c71b2a2c220441c554d4110420e2ca6a08830843e741943108667390c9182618e9916015021c6ac8a88a3104b476951100435930ac0208814b5d052c8210cb2a7b0282105c970d4952cc25a3b4a2a008117dd95314f218dce5b2c839859674c85214c22f39ccba10219518e5148730ce0a330042a051f7358a540428e3a2c4a9c41875955310640b34e8196609843f76550548c2b2b88a6a9081475d36194e20aace22a661187455298432cc30eb2ca620c8135dd94110730aa8e6b22a3217c161485304832db2aa690041785c4624c120c9ca7310a42061f73590524c32aa9ec2a0021b4986600c9308bced29a852061e6414c50486aab88a8984411b5ca61d41438e8ed28a801047775586320868f3a6a729841559c66054e40a9ae6302a40862d5458a300828f39ea92a443539cb6354c10da442b00429862e64588548c353b1284a0883c65526394032d2e8530c859845f73585520423aba8c299021965ce6015021ab4e8992a0195367198a5404386b22a419063a6591600ca31b2ee6a128220e2e6454832d072a3aac2196610f5d46050a41b18e4aa0a898666629845404236bb4a42002196995600c930b32e9b0ea09845d7519021cc2cdba2a3a82618b552621002087ce9314a39863a64580524c326b1ac428283365c06448530d8cc4b0880984757198a544c316aa4c520e4187d536348510c3ca9b1a421054e72151538425ab8cc8190839c1c76550040968eca0aa020c9d74d97214c256ba4c518e411bdd95214831c58a8b10818865653d85408822e39acaa1621a5991610ca318bae7b12a1a0d4d7315252042973b4a4a14831e5d46050810e92a5b0260085347458d511031abb6a820c21b4d046050530cb0a73006490d567114f30082ab39ec5a8a81179ce6590810ce4c3306a81966562987548c61f3a0c429a41559cc54544208bcec2a260184777558642082a7398c129021c394d52500408ece232c879051d74d8d53082a7390a9980218d15261cc1108ece232864a064d5398840082aab98c0a8c859598e61d5020c58a8312a6885d071591308831b320a218a81171cd62145408ece2312a7204d970d90214c32aa9cc2204414d9c7645532087ceb32642884d97098a414c21fbb2a8298
  | 29 => 0xa40884d97018d428432db2ec498441179da5348440b4ce9b0a429068c64d89514c23abacc321065c598c5190140c6ec830aa8905997018d42d0333b10c2a9a41729cb414c120ccac5288801043e74d94328421f3a0ca908614e9d35094331ccac5308a91071554d0d510cb1a2a6c4a0a21559c66054e208beeca98a72049d74988214c38b29aa320881471d54250130a6ae9310a2a065553584521023dbb2a028063cc150604851099ae4320629845e7398354c871ab24c22984136dc161d0930a6ce931aa22061d6498c504866b388c610a6187592530ca20b2ce9a8aa39863554587500ca3ab8ecba16611d5da5214540e2ca6a08822045d76150324c30e2a2c70822117dd95314d40a9ae42a0a49864f63949218c38bb9a8428a811d1d5610c940e60e0a10a2a04cc7648530482ab38ea7298818795063484209b4e031e429865553984531021eba4ca100218d5926114c10aaae7302a2207195410d500ca6dbb28020661875526390730e2aa6a08832054e72d5130042a7398c129081a55904188730d28c3202819861d6494c32086b338ea6a908174dc5404c120b32e121284985667118d5210316aa4c5200414d5c6621511087eecaa0a89872954549100421f3a4c5a98439398d62150108e8eca8a801046d72181540c72b29ac2200419554e6114c208b8e6b0aa40854e72152530425b3b084a08839554d610c840aaee2b12a70867261540500ca9ab8cc52a065875516388020c74c9300a6105c97215130882b3388a7290814d5d03254420c9ca7316a22067365945401025a38ac8192831bdd5621001099ae4302829870d5454d200838a324a6a8881951974148530c9cc6b10a818fc13148530482e53906298241c6553404c010cb2a7b02832066952580329070eaa4c7286438719543509308f4ec29a611061f5418d214426b38cc52a66117dd95415130a58eaa16809043e7499631c830e2a6c6a9221561d13254032ab6eaa0a60904777654451082a739ea8a90210f9d2654cb10a3ce8312a61043d7599032c871abb0a910a21995496114843cb4e7300a818d3574181510ca2eb9ccba0c410f9d36508010e4ca4a8e80204d57199742cc2acba88298441871506354910f82e3212609063564987530832d384c728643355c665501308eaeb30c841069854580414c31ab20a210a818ed955448020ae4e2322a01963954d8141082d8b80a6a0883965d5600ca31c72a9300a81970e5454d520422f398c8a8043741c552d41308deeca90a5a1e9564105214c326b1ca5200814e9c36455032aace7a94a2204e67614521c8392322a5288819c5456014442ba0e2a0261085367498951102ab39cc0a88818d151610c910cb2a6b008420745530c92108732312a298841539ce6054810acce4302a22062f659494010237390cba1821471d1615
  | 30 => 0x358854882a6b9ea529081a258940101309aaeda8842985cb72585308832d39ac02a06535dd92108730b30e0a0e809847771595329031c2a4c0192219618c60551218bae1b1aa890d367494a21c4386aa661900419559741cc010b32e8192609062e64548520431ab20a908221175ce65c844099ae4324609843d7419432c422fb9acaa162196195624c120ae4e1a8ca2196547358652d0fa2a8e6090041355c7648c930cb4a6b0063205577155153882e8b9c6088021479d2524c310c3eca31a842145c76d4d424865a3a2c3104219a549600c831aaae2194a398565750c9210862f3b0a6a12439594e6190820ae4e0212a22043e74d97218c32cb1cc1aa0419314d62d052187ae9314a21865a73983540cb16b2aa520881745c0328c521b94e5a02609046e72d944004272b80c498a43399ca648c5218baed298801861d64d4c3250296ba6a6a90218e1c164141219aae3316819845c7694d21902e239a8490843179ce6095021a6ce3aa68410e3554986420861f3b0a8a10438e5526014f218eeeab088410f25544c9510cad8b86a2a0e810f9d0650c0208bce732a84886555318540043c9b226088021d2dc15214930a5ce5302a990ec462185544c22eb9ecb10e814d1d15114520972e830243a04cf7650842cc392b90a910a21939506255130a3ae8296600847b7654050d0792a90829088187952630801099ae5b24629861e6498c52042e4392c898441969cd60d5331aace2304a72045e7614d504878b29a8220c81a95904148520c48c8a92200855970d0d500cb0eb2aa7a04819614f6054542a3ce829e600851e73d8b544438aaa4a3980418d1935244010c6cc8b08a81861d5458c510830e2a6c6a1265c555341cc010c5ac9290641863554586400422eb84c7aa44393d9463508428eae232a851854c72597304424f3a0ca10a61ac5854010130ad4e4322a0194777559221c430f2a2c6210650f5d954080108dae432a860859671d5154cc326b1ca51002153dcd6494810caca630a811066562d04505072b31ac22a66336dc16510530e8ca6a92200845e76151308432c32ec098221c99494110410a6ee8b04a3214767198b53502733b68290a41569cf6494032da2c2a00809845d7654e400430eaa2c62a0219318d5250831c3ec929aa31074953549100421eba6cb90e61725cc60509209b6e0b2e42984da75d81414c22eb9cc1aa443785c03248421cacc6b08a50871a7410d500ca5b3a6c790a431b5ca6590c10cb2cb29e812045e7654d42042b2bac84908430fdd95410a31c3ac8a9864087195498d500cb1aaa4c229841b498560d5330cb4eb300429855a71d0d500cb1b2a2c2280658d5506150010e8aa5986200861e6454f218432729cc428881479d0654c320a6aeb3028220c3d74996310826db82c890e61aa5894010230e48a89
  | 31 => 0xfb2ec6a10850f9d0650cb10ce6caa8a401054e73d4a52d061f3a6cb18e415c5c432540328bae7306a80856572d53100423bb8aca992216c9c05350441e52a8a94200861d6494c520431a3b2a888021879926314c10a9ee6b0aa42056571d4e521034ab22c2292611d5c662952309aae2320659845e73996428428f39ec3aa22117dcd62946408dce432887085d271d81304429b38ec8aa065555c76494e20a3ce8304a7084d97019742cc36830a6090221555c4544c0308b8eca96608854d7310152103a2a9ca4a88819354e6210010e2aa929e820871563146405038caa68728065171d56210730a98e4b0aa61046d72195418c2acb80a6282435a9c06394840a6ce3aa2859043d7498a518c2abb8ac8a9c219394e62102208f4e032e8610c5d7694e300c30e320c6a9221c5551514c020cb4a6b00620853574d4d510838aaa2a7288415a9c04354840a60e0a0aa020e557118d521072ca9cc021081475d06294c10cb2e032a859846f76548528431a308c0aa021d89495148020ab2e02a06418f2662d0851502ccb808320261e450660105308f6eca80a1a16956110440cc2ad38cc6a80650f5da5490441cb4c6b00a610ed161580524c30eb22c6294211ddd95114632b4ae42a083086395458241042c4ba0c498241725c25214930cb2caa9e81206355498432c86ab39ea328881999895110020e1cc8a906418c777654451c828fb9ac2aa643555c46014d21aa8e6a12a21964f620c9508c7e1a8a42982419558e61152318b8e6b2a839066462d85534421f3a0ca98841555c45294530c6ec830aa69056472544514c22ebb4a919661471cd621511087eecaa0a990dd0715013048327b2ec6a10858e952600cb21c6ac230aa81043e7599032442ad380c329c41d194d52c4010c6ca93088590e1c6454d329022f39ecb200418b592520c8318eae3b2c65a06955418540cc29aba065a8a81721d9424c120c3ac8b18a090d9671909424c31aaa2c2196439358e621481087eeab206590d5a73d85500ca2ebb4a610421871936354910d2e8430a8098554715533088316b26a5292638b58862151108eeeca88a32161e5458e50c866d3a8c0a0a6117dd953148408f6eca80a110e2d54988400432731aa4100214d1d95150040a3ce6314a990e5952580320c71ab2a8220841561cd6454032b8ae421ca21945f7654c30082b3396a290a819514e61cc92193eeca108598565721015110327bb2a4296611b5c8650c010e2aa8992a21979261500404c32db2ca6a0081595cb5444010ab2e5a1aa01949d74d8552cc22eb98ca20843a59916114b3095ae9310429063464d53108423bbb2a228865a61913044010878ecaa2200869b54582424c24f3a6c710e611d9c465d0e20ad0e4b0aa01976152580410431ab22a3a80651d5c460552328d8eab108690e4e6
  | 32 => 0x5535cf5294810cb2c6a80a190d3675d0521503922a24390221471cd54d0f20ad4e421aa0194ad7218141d02aab9cc0a8841179ce60953218eae3b2e8690e5a75982324c31bb8ecaa00818dd954110410aaae6304a22062d54988540423b3b0a4a88814e5d35094032da4c3304849871854d813044237390ca98881d1548414c0108eae232887107155314d41106d33a6c290e41c594d5110440c98c7b12a89063954980510ca1fbb2a8210434b5d252d0a31e2aa6a08820843e74d94320422f3b2a690821965cc6055121e64a8a8aa01945d73997428422ebb2a710021171da5350840a6ae3aa4a8195ca7210130482acb9c84a80659694d600ca41e4aa8a8a40104cc7648530c834d322c019661a5d52619093087ce8312a198c7576909511023d380caa184335dd921cc110b34e990ea09862d6498b53c862e3b2a6a10411ddd56010410b64e131a8220e5953580328429abacc4a088317dd56390220a3ce9a9c6510cb67654941106d338ec8a12415c9c45454032aaee6a12a21945e7318950106e8b8c8498441a3191424c832878e8b28429843f7655054c423d386cb21a438d99251d40328beeab18810870d5454f200831b322c229841c594d4110620e8aa6a8a40107495354a100423b388ca21c419594e610c210e4aa5b0a802072942109500cae9b8aa5a8261171cd6215310ab6e0b2a6090655539863084368382c220261361d9544c1208bce6328840865553984408430eaa0c6a14439354d6214c41d1ec8312a29843d74181510cb16b24c429821559c4524c0108bceca9a421045f7654c400431d322c02a0658dd954110620e2ca928a60106666254640082ac39ac2a8065c3552524c01096ae9b2a438862e5458b41c8667390c818a619659653c8220878e8b0ca00851c745473088338a8ec0a084196d4d6094d41c3ccb20880984d67119032cc22ebb4a829a43179cf6590010caac6a8c401047671195428c26cb96c0aa261875516388010cd2a530662205d171151308823a3aac890a21f08c5214c120ba2e190c429866552986421032ca9ac019483c9151424842187ce9b0aa40865a63580540ca36b96cb20e614b9cb5450821c9aa631287105357195041c82b8b88a8a80650fdd95414321e32a9992a01963654584400c23b38ccb21841369c06250d308dcec29aa42055a76941300831d2a2c1a886536dc165d0930c3ca8b188318c6f725953190332b12a3180419654d60d0c40ae0e0a0aa020e5653584329028e3a2c2a9c4187992530c8208dae532c622065b654c1100429b3a6a328e414d5c454d02208bcec29a600863554185438c72cb1cc029021e4d07404c010c5ca8b1080086c921580214c237b92ca20a611edd5608c820b28e8a8c4298656635445090bc8a0a8098221725ca544c120c38a9b1a8498e1d6454c510830
  | 33 => 0xc21e8aa3986401047b7654050c86b3396a6a88818dd906155220caac6b0ea81045f7654c53d06acb8486a8087175d76348440f8242982408854e7214f300431a326a8880211b5da52884218baeb3188010657631855448333b16c2aa261175ce6550910c6aa9b0a840864c5398b314874ab24c2196614e1d16194032cb2a730484106366458753c872b29ac2190611ddd951145428bcec29a64904db70595214c22fb9acaa02418d551610c82087ae8302a518e4d63588548422fbb2a629c411d1da5150040e1ca9296600865653584321028eb9ec5aa2211bdd9521493193ce8302439847676151510ca4ebb482202619598d6114142b52e1aa2859045e7319421502aab98a528881d29413048020ae4e3a84a01945d73194215031aba8c0a08835c9c03294440e28e6aa4a2194d973181214822eb86caa1887275d06308530caaa6b08641072554549100423b388ca21a419698e6015021ab2eb982401045e73181548872b31ac22a441e4504414c1209b2e132a8598479759824304364292c021261cc9515150040aaae3a9a601055a73909500cb92aa4a5a082117dd9530c510c9ec6a92422043c7459732442b2b90a728881729c8414c120a6ce329685a054e721515304316b24c4290214ddd13254440a72e1208a0a0ed061d01404c2ccba64298441c6151404c120cb2ca984400847771597325026bbb243986218e9516010410c9cc7310a81056870585521022eb9cca20041279d365c8730c6ccb208808879341501308434cb22c019261475d3654c110cb2a6b006410d957494441cc2b2392c6a8c85531c96154e40c6aa8b06820861d5458c5204317322a419081749c4324c220c9aca290429863564947210831a2a2c3a1621171d8535092196cec2928220ecb52d81524c2ac39a85280659a9896014c218bce732c432061e64550430caa6b90c129c810f5d0650c0108eceda92a22065563584548432ca9ac029e435a5c24354810968e0b0e8420e3665d47415032ca9ac0108419558d5114420a5ce829ca40843e74d97210c352b208290e41559cf6494432a5ae831ca40861d5418d420c6a6b94c0a9c21a5991610c930caca6b08640855671182538822ebacc890e61365c06590b30c38c8a9a632065973580540863cb80caa18438d59151140328bce7306a890e9964583214c32ca9ac0208818d1915444010a6cea1928220c5d739944204237390cb218214ddc95410521e96e4992a01966652586420828f3a6a6980410fdd95408010c72a8b00a810d4d72153300c3b0a9460880218799253d4420ab2e1b20a6a166652d85401022ebb6a9984411d5d66444010d92e0312a29865653584328434db26c0a8a61555cc60544408eeeab0c400854d721805350a5a3a2c219283559c4544c2208dceda9aa40853772550410421f3b0a8a146
  | 34 => 0xa802043d76550320822fb9ac9a82431b9ca658c440a9ae429864a0d3974186500cacbbb28220a6117dcd62951208dce4328878845d76153308431baa4c22022117dd9530c710d8ec63126290c5c73592520432731ac42a061351c56550930e62a928a20086c662984404c23abb6a9880218755163d4810c3ea831a848866952d8142042acbb086a8065475d06254e10a3ae9292608863954580540c62ebb4a6200411e9c263d4941f2483202608863954580510cb2a32aa290a619654e600c820c68a8302828869b64d81524c267394c898a61555d741cc010f824298241885997418b504c21e3a2ca90221969cd6584010c98c6a92422047671181548cb2bbaac21966155dd53294432e28a920a60884d97690b504c24f3a4cb10e619558d6114142c6cec2a2428864c52185324c2b9b8ac928065359c7648c9308dae432a821861e5498c3008236b96cb18e81659d35194730d92a4b00a59849d74d8e214c335292c01082174dc554d41308eaebb0a840851e74d493004236bb4a510041875925414b30cb2a6302821064d63988548c29c3a2c2a80658b592520c84087aed2a0a21045c73589540829d3a0c328065595c86054440c5ec9b12a68861f5498c30442b2b88a510a61879506350820a3ae7aa4a8107255454b1004392a90c2a00811ddc56550d20c9cc6b10a0a0e5953982429031ab24c229843d4d0e51540328beeca9c801054d7215130842adb9a8528065c99c854885108bce732843205557118a53903a2a9aa4880210f9d06254c10caccb308809864e53588519031b320a290a81175ce60d4810c6aa8b008290e666258753c8698382a820a4359dd53294432c68a930482884d970d95214c32db9ec0aa2439554d61d4840a3ae6304a80851e7498153842ab39cc1288811d5db54106108baed298a31066652584320430fb22a6990818e5516008420a9ee6b0ca4206366498652c4316a90c2a0081599cb5194743d2ac2a00819866562544511028e3a2c4a9c2117dd95314f42c3cc9318a610789741893048398aa4a2a806553dc954d4130ea6a4982200863664584524c22fbb2a228a619598d5114440c68a8b0e8698d35740c85150316b24a5908411b5c865d0c1087ae9b28641061d6454c208424e3a2c3a92610f1da5444010caaa7b0a811049d7499521cc236b94ca188810f5db5410310a9ae52a06518e5753185434863abb6a5a08214d9d23214540c72c9300a40855a75d01304823bb8acaa1a21669d0624c1208dae4302a918c767198b5050f1b322c329221d05493044010cd2a4b00820847775586420ca6bb8aca21261595c86094440ab4e630aa01955970d84534866cb80c6a1681871974350930c68a830a810845d7399642842b238a86a90211b9c86550c10ccaa4b086598e595358021902a6b96a9980211e5c06590
  | 35 => 0x58954083a8a9aa2a008187591531481087ae8328429862e6454b311032b29ac229481871526308110aa8e2aa660904d970d97214c326b2ac420661f0484214c120d30a8b04849861d6454c3288236b90ca20a611d5d832d4540e2ca6a8a802065b5358032442a7398a8a902199d49610c910ccaa4b0c840857270151510cb39b2ec2a0081535d6524c010c3cc8a98a60861e54d8d420830f324a7908414b9cb5495010caea630aa0a163554984300426cb84ca10e619559653d04108eaeb30c84087155454f410423b38ccaa1e4195d946348710c98c7b12a48855671153300832a32a6290a61725c6424c120b94e410a609062e6458854042b3b9286a8c858d5916114f21e94eb21260906345458740443a931aa328065551cd6254440d2cc6a0ca020e7261580540872d39ac029e43c955151c8020f84e3212609045f7654c530830f2a4c7200419654d608c8208eae2312a121c5d75d8d210c2a6392a6994218b1516210520cd2a4b0065a0d3575990410421eba4ca996218ddd561d0841c3ea9b1a848865553984321031aaa0c2a064117dd95308010cb0a8b006418cd671d90214c2e9388c5a82614d5c46215110d4ac4208800843e7499432042aab8ea998041179da5350820ea26528aa0195997414b504c2a6b9ea9290211d5c465109308bce7300a88861d5458c540831caa4c01904155dcd6294440c9aa6b10a22046d7299430042d338ec8a1641539c8544c030da4c3a80809864d6398a544c62f3b0a8a1e610f9da5444010c9ac7290a2206555318532842aabae86a8865365c36588530aaae3b20a690e1e65104404c32ca98c0a0c81c3991520cb30cb4a6b00631055a7110d500ca2eb98caa14211ddc56494032cb4a8b00a5986d161580328c70eba0c6a9681555cc6094642d32c8b006418c3d74197214c3a22946310a6117dd95314f20c6ac8a88a21074552584320c61e3a2cb19221725c86050530c9cc7310a60854d72d5253042a7390c129c21479d0544c010aace7aa4a21049f74594214c2a6b90a8296619598d51d0730a3ce9296608845f7654c519022e39aca20a414d5d44110010aa8eaa0a608843f7695032043a2a9aa390041939d8524c930c6ca8b0c840870e5494e520432d384c728043879926315010c6ac8a8e42207455354b10042b2392c6a8841a519130440108f2e0b2864085c9729053048326b1ca5080218dd936154d20c6aec28c80a063a54580320831ab20a910e21a6992600c9308eae332e8790639545803104317b2ca8900414d9d85450710ccca430a802072552984411026ab8cc52a6610f9d0650c520c72c9300a61047a701944204326a98c498c41ac50560107108bce7b2c43a0654531855050a3abacc2190218d9526110020c3ca831a859863b54580324421eba0ca90c6187d526390110a6ceca8
  | 36 => 0xb9ac3296878b5915214a30ea4c6a8aa01963654584408c31b2a4c3a9841555c75454c20a9ee6b22a4085c9720c5304822e3b4a6a1421175cc6154042aace2314a62045d7694c200421eba0c0a8c654ddd56150841ac8e4a9a428845e7398352506aa39aa5a8a81969d660c8530aa8e2aa4a7105567114b504c332b14c22a0638d5506150810e2aa9a988290c3e7499430042ab398c1288814d9d353944208eae232c849852c7255142cc22ebb6a598421551c5654c120c5ac8a90a41854d7214c32c4316b22a5908210f1d1654ca10c3ea8b1c808845d73d9640082a739cc0a90819599753d052195ae031286a173070550414866cb80c2a1261725cb434c120cb0a6b00648847970d94321070eaa2c6286438b5954210832ccac4a88a31865a7018d521072b29ac219441c515363485108bce7326a090d557114f300821eba0c029221a69916014930ccaa530864084cf75588430cba821aa2a8065749c4544c220cccc8a90820861c6494d518831caa2c0108212d5cb6550441ccae2312a68845e73180544433930cc02a065361c16448530a3ae8312a6086ca52580320c70f2a4c620041999d662d0521c6ca8b0c841961f5498e10442e4392c2982414d5d654104108f0eab0086884797098f525065aba4c2190831bdd952148108f6eca80a118d3574144414c23d384cba1663995496114a40ba2e020c429861f5498c404434b326a790a4353dc96454e408dae53288608658651913048386aa2a59802199d8a62d4540c6aa9308a01945d7098c5408667390c0a0e61279d0640c930ae4e2324a01943d74d9631c832aa98c2a0441559c46014d42cb4c6b06a998e3561d805444334a92c0290870f9d0650c9109ace331681986d2644c1100421eba0ca1804153dd5320c830a9ce7304a42046d72191500c6cc3a2a5a82618d551610c810a98e4b22a70856671d4e5210338b0cc02a065531c96354231c3acb2a660084d57198a544c2e4ba4849824195d95304401087ae9328640874471548524c297390c12a065c5153308411087ce932e640845c7358a511030f324a6104219554d619084093ae9314639865953d8143902adb8264a80659958a6115030c3ac8a9e422063a5458053c868fba2ca982211d9d85454420cb2cb31c200855a75183324c30e39ac929463879925308010c5aa9b128790d1c73589540422f3b4a6a1061d49453088020aaae7b24a32149e74d97214c2b338c86a90219659653840108bae6300a48864d5358851902d8382842082156dd5624c120a3ce8102a61053774581510ca6cb84ca21661365cb60545309b2e6302849073254946500cb64b22611024187d516308110b94e432260904d57198b43cc22eb9cc1aa0418e5526090c10acae5a9aa220636549843204334a94c0208815c9c35454432c3ec929a200845f73
  | 37 => 0x96595600ca3187ee8b0ea4985557118a53102d2ba064908430f5da54c841087ee8b2862904d67199132cc29bbaa8220e619cd9461500408bce632a432074952101300423b38ecba1e410fdd95415330a3ae8314a61051e7414b300432b328a7a0a430fdd95414032e1aa929aa40855973109500ca9ab8ec8aa04127dd95415130e28a831a4288753544c1100422fbb2a629c8533dd95214b30caca7308a42064d63588548c31ab24c22926127dd94110530c3acaaa6601062d54189438ca3b388ca218214d1c554d0930c6cc8b0ea61055571189531032aa9ac229481365ce6088620ba2e2192609051d74981538822fb9aca90e815c5c06214540c6aa9308a810657651053004237394c3a828747dd165cc1209b2e1b26429845d7399441082ac3aac298241c515263841108bae7304a3a151e7414930843a4b80a499261a599053c8521d2ac6a08a020c6e76151520422fbb2a82a6619a5965284010ac8e4a8a439867161980540c22fb9acaa0e41365c36550930c3ec8a9aa31049e7419721cc21f3a4c5a9a21279d36588530a72e9a8ca01979371500404c237baac5200410f5d06254331ab2e1192a018d34755074044386ba0a4992614ddd56250441c98c6292428862c54588404428eb9ec8aa0219558e61d5020cd2e4302a890e2e6494820042b8382a9a0a43595c460548408eeeca88a3205387058554c872ba9cc2192439959652d04108f4e032c8790c7a70195420c6e0b88c4982418e9916094d10cb0cbb12609062e6454b211031caa4c1218619354e6210220a38e8b2e608864d63988540432aa9ac2298810fdd564c8420c9ec7292851843e7615143ccb17b24a488021555c43254231e30a8a02608843e76951424c31b2a4c2288654d5d54110420d28a930c849843d76952401021eba0c4a9c219c9856014930e4ca4a08822047571d964348316326c4a9a411d5da42d4540d6282b00829867161540500cb38b0cc029c2199949610c830c70a9300848871954d81300823abb48528865879516390020e62a89822008537745815190b2632ac5982419698d6014f21da282b00829854c73548525025a3b2a2a00819654d60084109b2e031a432043c74595304828fba2a4982219a5895014043c74a9306a21963461981540431b32e8520a21d254a600c831aace22a2a61062e6458b53886b8382c8a8c858d99441886408bce7304a5a0e2d64548329066db82c9a9261c3d0c52d093087ae8328640846e72d97434425b38cc5a1a85175ce6015110c6aec2a4208843e74194320423b38cc9a8265279d06308530ea2a8982200864d6554b300431aaa4c3216431d9c4658c810a5ce530aa81961d5458e100432aa9ac2104219554d610c810c5aa8b10601063654986428c733a92c32928756dc13154031878e8b2a64885727118a500cb2b
  | 38 => 0x2087ce9b2865884d972d81414c236b94cb98881a65916014b309b6e0b2e82984d97018d21c4333312c22a0615c9c03254420ab4e02a2600843d76950200426d39cc190a615c9c750942438f6eca80a010d4e72981538422e3b4a6908819554f6150210aaae3b20a6a147970d96438862fbb2a9986419694d600c820b96e4a1a611062d54588540c316b22a419063355c7640cb3096aeda8883204767615141c4358a0ac020a419654e600c810aace7b24a32151d73181540834ab24c229661479d365cc110caccba9c6290e3554584530830eb20a790a43535c86414d21a6ae9a96820871a544c2200421eba6ca19043729c8434c120acce431ca3215567118a530822f39cc02a643479cc60953218bae7304a32147571195420c296b96c8aa0218b5526214c10e62a8a8ca01955471553504c332a92c2180219594e6110020e4ca4a8c822045d75991214c23d380ca21e438d952610801093ae83024298635545862004334a92c1988810f9d2658c810c98c528aa29845e7654d42842ab398c0a888165dcd6250441ab4e1b08a690d3474545418c32cb2aa7904414d9d06054420c5ac8b16a608658658c5304826cb9cc020a41969c26394020aaae2312a70861e6454c32d063abb4a220041275d065c87308bced29a421074952cc9300c2e2b8c8498241175c36354841a6ce9312a2197155414c4148726b1cc42a421531d5320c921a6aeba0a80087254210b51502aab8ec9a9a43175ce64d4121a3ce8306a690c757199632103a9baa60880218b9516210210e2aa6a088310656639445090a2fbb2a6294818755160d0c32ae2e02a24210dc672d05214c327b2ca690041a39516210c32caaa6b08652053674181510ca36b94caa1e218d5916114c20c3ccaa00809851d7414b308431db2ca888021555cc5454420ca8a730c8690dd171101308821eba4c5a8263535cb64d4d21a68e8a88a29863954980320429abb68428a819654e608c820caac7288801047776544518838a38aa898021559c46254c408ece332864206c752185524c24f3a4c518a618d5944110010d52c8b06439063564987530431ab2cc8208212d1c565d0240c5ec8a92422065953582310426cb84cb10e61ac5854010230c5aa9314601043d76950500ca96392a9a1261c91925254440a68e8a8a431045f7654e40842cd3a0a298441475d353cc010a5ae42a681084b67498a318872b31cc22a4411e5c06354841ca8cb18a42985367418251082963aa8520a41d294b604c010caaa6b08a61055a70189531028f39cc12a0419654e600ca40ccaa4b00820855571153300828eba6a4980211ddc564d4910c6cc9308a610c5e7614d32c822fbb4a7200419654d6010820f1284212609045d7694c510826d3acc021261551c56254e40a5ae4318a88851e73181540821f3a0c2a8065
  | 39 => 0x20086c66258440cc28eb9ec22a221531d542cc120caacaa9e820863564d04504872b29ac229081e4106404c21087cecaa2200861d6454c32906b5390c328065365c065d07309d2e4302829865953d892008316b22a4104218b1915248440ae4e1218a2a045e7694d2104256ba0c090a4199589510c0208bce7300a48847571d94324426a3b24298221711c95114530aace7304a3215b170149411062ebaec910e619cd446050540d88c5a8aa29861d6554e411032ba9ac219621875516390832a6ae8192a21951d73d8654c874bb20c2a9261361d941d413093ce831e439851e74d84534862eb9ccb10881b49856014b30c92a4b006418f1a5454e200822f39cca90a818759153d4420aace32a4649947671d9742cc32c3288698241599ca60546428ecec192a210479701944348673394c898c43d29c843540328b8eca9a850863676145415034d208c0a0a6195d8f6155120caaa730ea4204d97610b504c3c838a8020261995896115210aaae7a8ca21055473548515032cb80c6a9621741c1414c310a68e2b12a80847671997321023b3b0a6a88815c5c75454032a6ce8102a210556759073044346b168020261369c26290d30e92a498440086a662504501063ab8aca100218e5955484010c6aebb2a8220d357418851502e23926290a619954a61080108bcedaa2a6106a76254941106a6b90a698021661c54010130c6acaa1082086585358032886ad398c328065635d3214c1208bced29a431055571151530821fbb6a8192218dd516108110c98a6b10879053571d08515030eb26a790a43479d3530ca21ca8a73086490c5e739835204398b80a8a0e21479d0534c0208ece332e879069161500404c353390c0a0883539cf5494810aaae62a44210c7471594424c28eba6a729821175cf6510020c9aa7310a60865663984520430f322a62884135dd95114730d8ac4b08809854d72d51530430f324a6290219c54660cc44096ceda0a800846c72595438431bbb2a3a0081c395153948108bce632c840875332545500ca8eb98c12a0418ddd954c401087ee8b28648847a701944304333292c2196830f9d06254031ab4ea10a609055b764c9500ca1e3a2ca98c41559c754cc020aace3b16a6a14767695121c43162a6c4a9a218d9926194a31aace7a92a22053470508515026cb80cb90e6117dcd61949108f4e032c861066b65949401023ab8ccaa1e415cdc56454032a38e6b02a819637745845050a97390c0aa0659c145600c540cd4c4b00a810e6b65549100431d2a2c021e61539c8544c210ba0e0a0a608847a7019443083a3b8aa4292618d59541104108baea32042985567318151083932a2a4208214d5d06054642c5cc4a14a3a055671189530831a326c2a9a21879506350a21ba4e3212611066962980540426cb80ca21661569d4414c2
  | 40 => 0x7a0008002018000000001f002000801c01607d80140007fd59300021140520038044002002122802c0860c60bd0098002074002001800e00900180c406c64400b805400609c00a8094002094025000400a06a007816c00604e000026c00000900080c00020001b400000602950b1000000607001b037000a03102281e1c2800f005004c0660007c401140020610080184192000002800001c00000000000100070175ee000005e018e3754185404c22f398caa08411ddd95114742c5aa4b0482205557318151082aa38ac8a9c818b9926214810c6aa8b0c600863554584540823ab88c0a90878d1526108510a5ae9a9ca40851e74d86531024eba6cb10e61351d9214c310a6ae22a4831061d5418d42cc22eb9cc12a643175da5384010a5ae4304a80845e739942004327bb2a429261e4104404c010a5ce4302a80871a65500404c32731ac42a665599c853544408dce4322a018de170d4921c429d3a6a2a80658d9516190b21d1cc4a14829853675504414831a2a2c3212214b5ca6415131a3ce92a260884d876485304826ab88c0a12610fdd9540c820d6282b0083a06556554730083a8a8ec098041179d66348530a6eecaa0820843e759912150334a92c0290639a549600c840ccaa530c40085367494a2108726a9ac5a8881559c75454c20ca8a6b0e8490ea552185401030eaa4c629841b258a4010130cb4a6b0486185cb72591304824f3a4c410a61969d6601053099ee4b28829843e7499431082e838ac4984411b5c86590c10d9264b006490e1d6454c328431aaa2c22a46165dcd5250441c6aa8b08a81963554984540cae8b88c5a82619514f6154142c6cec2a4208847970d94329072731aa5200819654d60c8420cc8c5b0aa89864c6518d42482ab39cc0a8c854d5d262544328bee6b14a90851e74d86538425b3b6a6a08839c98560d5032aaee2b2a609065963980528423abb68228243f05c4624c1208bcec2a286986566554741cc237394cba18211d9d832944409b2e4302829845f7558e2004236b96cba1a21a95894290441ae4e021aa22063654584400432bb1ca2908411d1d561d0d10acce52a2438845e76151538430eb24a629421369da42d4130b34e8192611052c74585521029ab8ec42a221175cc6055021cb4ec32a609055573101511023b38ecb21061559ce6454432ccac5308a910d357118254c86abb9ac4a8881965955384010aa8e2a90a498572700cb5150332a94c2288811d9c665d0b30c6cc9288a01961e6454c200438caa6c0980218b5926214a10970e0b2243a061d6498c530830f2a4c71004117dd56448530b60e0aa08290d3674989510829a3a2a2a0861591c552149308eae2312a021d9b74585308829b3a06528841879526394321c3ea931c408851f74589539026d384c598a618b59152cc440c3ec8a9a
  | 41 => 0x440011b90060012004001804800302e004801801616200100180e600e02d008400000c00600ac00000806a81f80000020048008022005000808c00000800881e80d2000018014800002700300000241c200280401f4014000000c02800320a010800a00000780f8004036018805400000000a000000601f000003d82c0020130000008001004004000000000600e83ae003006801c0f000000281ec14612d02100608d8000010000000a05001a800006e01e004802801a0310010024000005015809401c063003000000c0040010008050206000000c0a200000b001801204c00280080460050a8804809201f012800000c06a027000000200e03f01ac03394a0000004030000010831801e041000024001a00100200c800028a024003401c01406a816800000000880100ce14103b830401200400100d80de003001012400806f00600a40ee00f026003802403a031809003406305f808417400b00004d007e1c4000002404406500000b000200b00000040340020008024172027016001400000a00c002000c00000300e839010b00d005400200a0cc8004046000000804403400e010004409c01300b001c06600b0028000006026000800d3c8004006825800012400280000000000010668036007006803c00e00507702d00000010200b7c31001805682e00084ef012800400003c002801c0dc03e003004801e000001000000000701a8080008000008800001002500001800840040040108002004003000420e03f007b17000e02000600040180020010008066077005005c0100005de804800013200000740020280480028042010007001408805f03d8038000001003819c04e05d009801000801d008802000213200a001c06401700400000ee00086b80201ce00100000100e8000000000801c02a00300240011b805200f8054001032810c016010017800400026200380c400609f000000061216600b807c004000006805400200200d808406a062008803c01400000e804800201e000571c00800000300a000e000078008405a02b06b000002602a00c0098012023003800d0fa000006009c03e03900b80380880000050000000000224842401404d000000410200b00b0bb40020d300c80000420da01a809401e000008901010600000080a400201300280340040090030044010034000000000a00001286d000e1bd0008b9853608600580500020140000028026004010026801459e029000400e00f000002402a01300180516560050038028dd60080100004038002003801402e002000009000800000600200050520000090042000004800000001a002000409200000a82d803811037c812883600d028800003a00000000180280c500001cc0380530000010004027016800409400502f007402025e000008c0086140100
  | 42 => 0x160018048002024002001803000f00b006000000000c8000012000002014800002b00e80080060c70068084004007001800401605d000801004c18700500000000040d6804c030004000812c0d200805737a803605a000015c002000006813892000001181dc0000280028a2002c009000000007089e079004c020003000002405e025000059000e4ba010006804e00c0048084004412000000002202e00000100fe03d00b800000400f02a011c01e005006806410c06104380c409604e001801c05c00e16b00c4006025000805c01a23f00880cc070002000003400001500f001400a05d005800403800800500343b604501d812000a8a900e006c01200c001000404601900080980ee01300000a8000000002806000a08e000000c0b20030030000002276027800809600e0128aa800401c001885002800f004800000c01c00000b0066000039025800000100a800400200101700080300050000028012006000004000400700000040360660018018006006079002c002000000004421800e01e00d802005101c3e1c0360100000078004000000000006202e01001840000000030004014000000000000c01d001800025c0d9002000c12000200201ac05a010007000000000c01f01f403c00f030001000001c01880100000040088060002702066005000405b003800001605200a80c804012b001d76c000000000800806203d009001807a03b04f01dc002012008008c0c205500280f4000001050800001a00200d000000000400005a401e000018000803800504a031001202f01d002008e0d6011001400c00004880141120020030020000025008002c00609000000080b405e004008007a000005066c00003a0488160002379000800003800601e004000c00000000001c0007004800400000b0040084000014014841573e00d000002001603501380100000010188044386000001000002722300280000760ff00780e400003900c884005c00900500a8f22010000007802001e006006800c00028b008c0000bd039829c00e000004800c002004002002401a00500b001002e00200500a400e0db000006c0011a500201ddf5001c004000002e002059005400602d00582ac00c04c0020088000001000004000006200a039c11800a00280040e408d00600600b00cb00e801802e02100604040020090ff8220014002000003c02c087000802800a0150018178000035000000996400e03e051400001501d802803a00603c80cc558003001803000c0140008014000014007801002c021005002000409900380780782cc00280300000060030000042024002001400a002050801402c000000026400200000180b8048001000806801c014004019c000076002804c0040060010011aaa000011800001001600900d000c000002000c002
  | 43 => 0xa005406c0cf002800c0220010080b3408c0dc047803003e00000200300040a700380200a8002000c1d801800800e0024050015000809000a010000020017800a004000001200e000007801c009000800001403e042808800002e01c80002e201301100583a80310138164010002000000809002700c005001400b0148008000071001801004c00001601040000040213fa403602200100f8040001010811c00000500380043be005000807001801800003d8004002005816000400600103d403e01701eb4e0118051061805d56201501d80400e2009012000004005a00480d404800000c801c0f200f006811c0be00a003004008202d000018c262028013810407233e007811808001a0140058000003005000800f0d5000803000a02800380101260010000004000006004010c014005094007000000400b866400004e1030004000000000001c0040a7023bff800402b0a101d800001000000580d00270041cf800003000681d402c004005801c00601500082cc6e801a005805c50000000580440240110010154000013005001c01e033077000000000000200b40040aa0020000000034002000002a03a0178010016000007016000e2bd005003c02c04d010800406e0f100b85ac2c60010000010004009000800403000004385ac03a003000001800001300881f4086006000800c020096023019c08a004000802c01401b011002530a000001802c03600f74b8760000006000027800002700a80003200010430154000018002002000a004000000400603b00080a800e00001700ac00800001401300340000000000146086067000c06e01802680040141160510000144001022002c000011000000801e00200c00340a6010000000402e010000033c0ae03200000040f40b5001800c00409c0000bf401602700d804024a304097002c09a04e0088028b7a003018001408e041001800019e001001858c150030000001400401200000080fc00300a819c004030007800415a12701700080140dd00481100280df003010403e00100001e80000c6000005403e01007d00d80c201900080b40f209400a000000600875f006800402a0000038026f7800000002e01d801281fc006035057050814000600500c00660020190000022021025000800800200b804804c00100380200097760018a1403a006000000c0ce02101b814c002003001800815208b066a40000600001400dc04400400d000000001700680100ec013001000026201800100cc04e00a03d80080a800500e81e806a001002809805e006076803809800100100f802e004011800c006046008b605966171003805016a00600801cc01a02900a82d40000000108000040036001003801a001020802c01c099000005802c00000000041c200003f3ef400e00100c00000f000502e
  | 44 => 0xf600c21e800000005a02d80200b07190050020000022000006004e00f00187f400c00003380080a200500d806c000004000000002000200082c800c001006800003e7080a280400ca0145970000000000015800400e02700d803017404201c80240460080150054036192000008c02c5d2000002002000104f811001003a000800027600b00c00880a80020008014002053059000c0b2041123800001e001000008000801600a805002e000000001400204f033010c00000a002000002c021079806000400e00c2f5800007f015047c07a0640066194024074007800c0a8002019000812800f00cd3f803600100000c4036024008039002404c00000440d000000e802001600607d804812a0700198144018014014003002005401200140b401f00400a800c000004001c000050009810800000003f800400000f017001c00002a16c008c00000300305d801c011025000000201004302ec016039000000000200200587880000350018034020098001018401e00300000a8000025000800403802601380001da02003e000000c0050428084012000000001c1ac013009800419e001014017400e01709d004c0360890060098004c7701c810403a00100400001544f9001000c13400409e801000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x54010130d12831c14154041d09545c8544c220c91631c14194041e42645493044010d11831c15410521e11545853088010c18655c24250930929801c95350841ac3815913088120b1184d493044010ac0814c9600c921b058315142484218b1861c14290710c92651c54010130a30805886155010e09645496014930ca1645c04148520a108655130440109c1821c1414c310a1886550544c120d10541c5404c120c52715c06354b10b40815496014930d12831c15410521d05735084254432f0152d07404c010c52715c06354841c53655c06348710d0a545c84354032b41819093254032a90805904188530a498294d600ca409a1821c14110720ac081588624c220a90805056010730944875496114930b1081550544c2208b0805da3250441a49829d8654c120a3285d846050540a24865525244010c85735c86050441d11545c4404c010a17855904148730a24865515244010961821c14154041d1175104404c010951801cd6214540c17751913044010ca1621c54010130d057454c3248421c8b765894010130f00544853048110c93631c161508419c1819cb434c120c48655c8614c120a92849913044010a938650441d4130d05535c85350441c48655c8434c120c8876591424c120e20645493044010d10541c1414c310991801cd5250441c15759cc6050441a30805d85448510d1174544514c220d21525c05250441a17855086150330c91621c54010130b0982151404c21098b845c7624c120e05535486150040e41525856014b30c86735c86050441d09545c8404c010e10645493044010c177615121cc110c48655c8314c120985821c14110730d82821c14110530990875066010530925821c14154041c0c759894290530a9087505601053094987548404c010921821c14154041a92855056010530981821c14110530a24869515244010a14865533044010a0c845945208530b1084544514c220d08745093254032d13731c142145409c1819cb404c12098a87991424c120b41859493044010a49801cd6215031a3080551601052194b825db4354032c1476151214c110a89809894290530e8162dc54010130a91841456010530d82745c4624c120b09821c1544c010b20805d15210410e13751913044010d06641c55214930f01549493044010990875854010130b1085504414c220d10541c1214c110a18855096010930e82625854010130f01545493044010d8172904404c310d05735485250441c19545c06348410d05745c4524c930e21529856010440a44815945210930d09745c0524c930a90865513044010919801cd6215110b048454a6114930c0c651c94350930a498214d600c941931821c14154041a31859916010410c89729046050530d21821c14154041c24545c860505109c1811da424c120c16751864050130
  | 1 => 0x951801cd4254440c44651c95148530c0d735886215110b4182d513044010c90631c16150841e1054d8c6048510d11539c35110640931801d53250441c91861c14110530b08845496014930e046494d5244010a8884588624c220ac1821c16110130834875954110620a9281d9264d4130e0a64549600c831c50655c32148530d09735084254032949829c74354032d10541c5404c220e4152985600c831a518014d6114142c45735886214540a0c825945410530990875056010530a90875854010130aa0805904148720e0a645496014b30b8084585214c120e1064d493044010ca1625c04110010e08541496010930cc1621c54010130c93751913044010a25865484110010d0b545c8404c3108c8865d1214c120c61625c06214540a4982151600c831d82621c54010130a49821516014b30c25755884110010c14651d15148530c89625c04110130c48655c06350920d22821c14154041989849ca614c120a30865523044010a0e84d8c5288530e40645493044010a908550560105309a1821c14150110ca1621c54010230b1185104404c010c19745c06354841e206454a3044010d81821c14110530a30805905448710a44815886254e40a4b865496014930b0885591424c120b1181151404c220a498294d600ca10a518018c5148540931851c14210410c1a745c063548419a1811c14250120d13545c0414c210b1185d07404c010a51801965148730b8284dc5214c120a30865513044010990805c74210530b11859513044010e06535486150040d1075505404c110c18545c06350910a48854856008530a91811516010530a488550960109309a1821c14110630d04741c55214930c31651c14110420e04645493044010a90805086150130d10541c5404c110b8281dd1424c120d11831c14154041e09645496014b30c92741875050130c19645c05314121d81749c4624c120834875516188010c91645c04188530c25759c86050441c14659c64250930d81745c4624c120c93875056010530a19801965450b30a44825945110530b8081591424c120d11545c4404c220d05641c55214930c90875854010130c0c651c95450930e046454d5244010a24815516210220e0564549610cb30c14659d32148530c50651c5624c120932861c14154041989849c8214c120b21821c14154041c267558a4110110d10549c7604c110f00645493044010d10731c15410521cc172d0460505309c1819ca644c1209c0874853048110d11531c14110420f0152104404c010e81621c54010130e81625854010130c14651c55450930a0c84594624c120c15755cc6050441a0c845886254e10d05545c84354432991821c14110530a26849915244010a30805846155020b1084544514c120a30855056010530c25721846055010e41525856014930c91861c
  | 2 => 0x496114b30c90875056010530c31861c15410521c15751933044010e22645496010410b418210d5154032c24745496188010a9183d906150040e4152585600c831989821c14150130a14865525344010d09545c84354032e81629854010130c29625c06215110b1081550404c220a50854856008530c49735c860551219c1821c1414c110c147654d5150040b0484549611493098887591424c1208a5821d941940419c1809cb4148530d0a745c84354032a9181d096010530991841c1214c110c32861c14154041c24645cb5444010c85621c54010330a5086551304401099287d05404c210c31651c14110630e0964549600c831e09544c9600cb21d81621c540101309c287d05214c120d11535c05350441c91645c04148530e046454b3044010c90645cf6144010a90805056010530c4b625c03254231d21525c04110010b20805c55210440b21801514248421b1280d515310610859801cd6215110d41535c03248421b81821c14110530989821c141d0130c1b655c06350b40e05645496114930a1586d5041cc210952819d13254032d1175504414c220e11535056010620cc076585214c120e80649493044010c31769c354106109448754a61149309c1821c14110530d10541c1414c110a30805516010621e80645493044010a4681d9452d0930cc076dc5214c12090c879915214930a4982951600ca31b12865513044010c247654a5150040e10865513044010a90845853088010c18651d1624c120c8876dd1424c120d8174105214c120a30805906454420a8b845853088120d13731c15410521c44651c93148530b4085585214c120b11831c14154041c31655c04110010c147694d5150040a498018d524841090c875915214930a89801c96414930f036454930440109c287985214c120b1285906404c110c44659cb4148530a14865513044010d12851c14110530cc1715c06254530a14855904148530d07741c55214930c89621c54010130b418210e5154032a4681990524c930b10805505310521f02545493044010a0e84d945288530c48655c8644c1208e1801c96310521b09849493048310b1085504414c120e08645493044010c51715c06354841992851c141105309a1821c14194041d41525c0328c431c24545c86050710e13865513044010c1a745c06354b40a14865515344010c24769495150040b1081550544c120d1275906404c110a1686d50414c210d11715c0544c110d41525c0414c010929821c14154041c85621c54010130a90805904148530d41715c0524c930a498214d600cb10835871506048510e40521456008530e43655493044010a30855056010620d13545c4404c310836869d95444010b108655130440109a1821c14110530a25821506150210c32765c05450710c16651c54010130985821c1411053
  | 3 => 0x1e00e184a7224008a00c2703000020202018020d52804195912850040001834221d0a0088c0709ce458220a040621a780600e1239804b2000484750490200c0cde44b80087b260041a001b0241600160740a980b02002000280036071e8c81400090049c0321084a201089c000001c0642c2a030029a1008860b002010007001159180c370081814840800814dd26c52a01d00048082005814000e0f004e8080300000b60000c7811011900e77028140200070000a00b10805535310521990879854010130a5086544514c120e11851913044010b1085505404c110930805c74254041e0964549600cb30a93825056010530c25755c86050441e0564549610c831a1485508615013099187904404c310d10711c1544c010a30855056010520e41525853088010a4481594624c120c267654b4150010a92875854010130d81421c5404c120d11545c0414c010d8172104404c010e10541853048110b0885509404c120e00645493044010c81621c54010130e4152585600cb30989849ca314c120a90805904148730e41529856014b309c3815d3624c120991811c14250130a8886509404c120a18865513044010a9284d8661d4130c24765495150040d10541c5404c21083787d974150010d12651c54010130a1a84d4d600ca21d1175d07404c010989841db214c120d11739c354106109a1821c14154041d11545c4544c220a318598560104409c087585214c1208b187d046048740835871935244010a3285d906050510e1064d513044010d21821c15410521a90869513044010e0a64549600cb30d0474dc55214930d41525c4404c010e4152985600cb30989821c14110530e05645
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x96219408c10400000040c08020000208048260228018609a1000003e40151821c1414c110a404b28438a8098241281922014158041cc30430cc10e0aa08290e20619821c14110530b004a2a4b0ac0292618118660c7055041487200a8c10e0a0a6188460648875066010530c80c1b04382a820a439018360870505501064252d432a8982200862021d629854010130888cc0a8382429822188076a077450930483100ec40ac8a1260906021d5809894290530a80cbaa420880980218216560870504418c32030ab9082202600860121d645496114930908cc0c9a92608802160096552524c110043100ec422c290a6090580259545493044010c403b509b8a4298241a0084549614c220042c0529322a4982200864021c5448530481109084c2a8b0a61100212409854961580524c3402c840aa4b00a49862058d821c14194041c8141b0438282a80832089859152580524c31030d410e0a08829862021d625854010130c80c10e2382a89802150091551721513088222130baa8220a611052025974105214c120a094b6a8b808298421501921507150130843080ec42ac290a609062021e6258540101309024c2c8a92c2292614109559170105214c25032440282b008298610195809cb4148530a10cb2a4b808220021a006460b544c110043010ec42ac8a12609058025a545493044010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6827
  | 3 => 467
  | 2 => 53
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt s5K8 (i*5) 5
  | 7 => packedAt s5K7 (i*16) 16
  | 6 => packedAt s5K6 (i*27) 27
  | 5 => packedAt s5K5 (i*38) 38
  | 4 => packedAt s5K4 (i*49) 49
  | 3 => packedAt s5K3 (i*60) 60
  | 2 => packedAt s5K2 (i*71) 71
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 8 => 2*((h/1+packedAt s5K8 (5+(h % 1)*1) 1) % 1)
  | 7 => 2*((h/28+packedAt s5K7 (672+(h % 28)*6) 6) % 42)
  | 6 => 2*((h/677+packedAt s5K6 (52569+(h % 677)*11) 11) % 1947)
  | 5 => 2*((h/3876+packedAt s5K5 (431490+(h % 3876)*14) 14) % 11355)
  | 4 => 2*((h/2282+packedAt s5K4 (334523+(h % 2282)*13) 13) % 6827)
  | 3 => 2*((h/162+packedAt s5K3 (28020+(h % 162)*9) 9) % 467)
  | 2 => 2*((h/38+packedAt s5K2 (3763+(h % 38)*6) 6) % 53)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7f8ffffc1f1fffc1c78fc7ffe381fffc18f27f
  | 1 => 0x87f07e3fe01ff1fe07f1f8e0fc01f87ce74c73
  | 2 => 0x7ff803fffe1fe3ff801ff00fffe3f83078f9c
  | 3 => 0xf800003ffffe003ffffe0000ffffc003f80fe0
  | 4 => 0xffffffc00000003fffffffff00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x820804402020004082012240884a10081225
  | 1 => 0x31251448864cc20e0310c844a4149168634c52
  | 2 => 0x420124910a0500528801520829242509058498
  | 3 => 0x106a5922541064a555a40012d2590232b80b60
  | 4 => 0x644c600398998939a649a49c00600443d6e000
  | _ => 0
def s5Atlas : Atlas := ⟨8,rawDecor 31 s5Pos s5Neg, 0xfeeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8feeaf8a8, s5N, s5R, (fun _ _ => 0), s5I, []⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff8383c1fc1fffe0e01ffffc2443fc18f27f
  | 1 => 0x83e07c03fe1fe1c0ff001fe0fcdbb250e74c73
  | 2 => 0xfc007ffc001ffe00ffffe1ff031c3c63078f9c
  | 3 => 0x7fffffe00000fffffe0003e03f83f80fe0
  | 4 => 0x7fffffffffff0000000003ffc003fff000
  | 5 => 0xffff8000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4210080402002424020822410000084081225
  | 1 => 0xa3421c01920d2084b9015542e849b250634c52
  | 2 => 0xe9042524001754082a4a419a091c1461058498
  | 3 => 0x2094acaf5400012d495980432e02b82b80b60
  | 4 => 0x40107373299a993c0006000843b6c003d6e000
  | 5 => 0x739e0060310310201818111083ff7f78000000
  | _ => 0
def gbRaw : List Sig := (rawDecor 63 gbPos gbNeg).map Prod.fst
def gbPools : List BoundPool := [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 7, 0, gbRaw),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 7, 0, gbRaw),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff, 9, 0, gbRaw)]
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8, gbN, gbR, gbH, gbI, gbPools⟩
end PEqualNP.Outside.L_meta_37337
namespace PEqualNP.Outside.L_meta_37337
open PEqualNP.Outside.L_meta_37337.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := bs2_5_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 68 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 33 := block_range (n:=33) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 129 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 45 := bs3_5_0
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 53 := block_range (n:=53) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 53 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 83 := block_range (n:=83) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 467 := (concat (concat bs5_3_0 bs5_3_96) (concat bs5_3_192 (concat bs5_3_288 bs5_3_384)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1824 : Interval s5Atlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1920 : Interval s5Atlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2016 : Interval s5Atlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2112 : Interval s5Atlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2208 : Interval s5Atlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2304 : Interval s5Atlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2400 : Interval s5Atlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2496 : Interval s5Atlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2592 : Interval s5Atlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2688 : Interval s5Atlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2784 : Interval s5Atlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2880 : Interval s5Atlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_2976 : Interval s5Atlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3072 : Interval s5Atlas 4 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3168 : Interval s5Atlas 4 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3264 : Interval s5Atlas 4 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3360 : Interval s5Atlas 4 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3456 : Interval s5Atlas 4 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3552 : Interval s5Atlas 4 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3648 : Interval s5Atlas 4 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3744 : Interval s5Atlas 4 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3840 : Interval s5Atlas 4 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_3936 : Interval s5Atlas 4 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4032 : Interval s5Atlas 4 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4128 : Interval s5Atlas 4 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4224 : Interval s5Atlas 4 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4320 : Interval s5Atlas 4 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4416 : Interval s5Atlas 4 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4512 : Interval s5Atlas 4 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4608 : Interval s5Atlas 4 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4704 : Interval s5Atlas 4 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4800 : Interval s5Atlas 4 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4896 : Interval s5Atlas 4 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_4992 : Interval s5Atlas 4 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5088 : Interval s5Atlas 4 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5184 : Interval s5Atlas 4 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5280 : Interval s5Atlas 4 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5376 : Interval s5Atlas 4 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5472 : Interval s5Atlas 4 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5568 : Interval s5Atlas 4 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5664 : Interval s5Atlas 4 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5760 : Interval s5Atlas 4 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5856 : Interval s5Atlas 4 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_5952 : Interval s5Atlas 4 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6048 : Interval s5Atlas 4 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6144 : Interval s5Atlas 4 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6240 : Interval s5Atlas 4 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6336 : Interval s5Atlas 4 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6432 : Interval s5Atlas 4 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6528 : Interval s5Atlas 4 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6624 : Interval s5Atlas 4 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6720 : Interval s5Atlas 4 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_6816 : Interval s5Atlas 4 6816 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6827 := (concat (concat (concat (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768)))) (concat (concat (concat bs5_4_864 bs5_4_960) (concat bs5_4_1056 bs5_4_1152)) (concat (concat bs5_4_1248 bs5_4_1344) (concat bs5_4_1440 (concat bs5_4_1536 bs5_4_1632))))) (concat (concat (concat (concat bs5_4_1728 bs5_4_1824) (concat bs5_4_1920 bs5_4_2016)) (concat (concat bs5_4_2112 bs5_4_2208) (concat bs5_4_2304 (concat bs5_4_2400 bs5_4_2496)))) (concat (concat (concat bs5_4_2592 bs5_4_2688) (concat bs5_4_2784 bs5_4_2880)) (concat (concat bs5_4_2976 bs5_4_3072) (concat bs5_4_3168 (concat bs5_4_3264 bs5_4_3360)))))) (concat (concat (concat (concat (concat bs5_4_3456 bs5_4_3552) (concat bs5_4_3648 bs5_4_3744)) (concat (concat bs5_4_3840 bs5_4_3936) (concat bs5_4_4032 (concat bs5_4_4128 bs5_4_4224)))) (concat (concat (concat bs5_4_4320 bs5_4_4416) (concat bs5_4_4512 bs5_4_4608)) (concat (concat bs5_4_4704 bs5_4_4800) (concat bs5_4_4896 (concat bs5_4_4992 bs5_4_5088))))) (concat (concat (concat (concat bs5_4_5184 bs5_4_5280) (concat bs5_4_5376 bs5_4_5472)) (concat (concat bs5_4_5568 bs5_4_5664) (concat bs5_4_5760 (concat bs5_4_5856 bs5_4_5952)))) (concat (concat (concat bs5_4_6048 bs5_4_6144) (concat bs5_4_6240 bs5_4_6336)) (concat (concat bs5_4_6432 bs5_4_6528) (concat bs5_4_6624 (concat bs5_4_6720 bs5_4_6816)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1056 : Interval s5Atlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1152 : Interval s5Atlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1248 : Interval s5Atlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1344 : Interval s5Atlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1440 : Interval s5Atlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1536 : Interval s5Atlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1632 : Interval s5Atlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1728 : Interval s5Atlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1824 : Interval s5Atlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_1920 : Interval s5Atlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2016 : Interval s5Atlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2112 : Interval s5Atlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2208 : Interval s5Atlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2304 : Interval s5Atlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2400 : Interval s5Atlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2496 : Interval s5Atlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2592 : Interval s5Atlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2688 : Interval s5Atlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2784 : Interval s5Atlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2880 : Interval s5Atlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_2976 : Interval s5Atlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3072 : Interval s5Atlas 5 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3168 : Interval s5Atlas 5 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3264 : Interval s5Atlas 5 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3360 : Interval s5Atlas 5 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3456 : Interval s5Atlas 5 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3552 : Interval s5Atlas 5 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3648 : Interval s5Atlas 5 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3744 : Interval s5Atlas 5 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3840 : Interval s5Atlas 5 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_3936 : Interval s5Atlas 5 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4032 : Interval s5Atlas 5 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4128 : Interval s5Atlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4224 : Interval s5Atlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4320 : Interval s5Atlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4416 : Interval s5Atlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4512 : Interval s5Atlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4608 : Interval s5Atlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4704 : Interval s5Atlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4800 : Interval s5Atlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4896 : Interval s5Atlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_4992 : Interval s5Atlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5088 : Interval s5Atlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5184 : Interval s5Atlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5280 : Interval s5Atlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5376 : Interval s5Atlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5472 : Interval s5Atlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5568 : Interval s5Atlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5664 : Interval s5Atlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5760 : Interval s5Atlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5856 : Interval s5Atlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_5952 : Interval s5Atlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6048 : Interval s5Atlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6144 : Interval s5Atlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6240 : Interval s5Atlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6336 : Interval s5Atlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6432 : Interval s5Atlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6528 : Interval s5Atlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6624 : Interval s5Atlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6720 : Interval s5Atlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6816 : Interval s5Atlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_6912 : Interval s5Atlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7008 : Interval s5Atlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7104 : Interval s5Atlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7200 : Interval s5Atlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7296 : Interval s5Atlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7392 : Interval s5Atlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7488 : Interval s5Atlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7584 : Interval s5Atlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7680 : Interval s5Atlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7776 : Interval s5Atlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7872 : Interval s5Atlas 5 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_7968 : Interval s5Atlas 5 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8064 : Interval s5Atlas 5 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8160 : Interval s5Atlas 5 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8256 : Interval s5Atlas 5 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8352 : Interval s5Atlas 5 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8448 : Interval s5Atlas 5 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8544 : Interval s5Atlas 5 8544 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8640 : Interval s5Atlas 5 8640 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8736 : Interval s5Atlas 5 8736 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8832 : Interval s5Atlas 5 8832 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_8928 : Interval s5Atlas 5 8928 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9024 : Interval s5Atlas 5 9024 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9120 : Interval s5Atlas 5 9120 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9216 : Interval s5Atlas 5 9216 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9312 : Interval s5Atlas 5 9312 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9408 : Interval s5Atlas 5 9408 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9504 : Interval s5Atlas 5 9504 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9600 : Interval s5Atlas 5 9600 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9696 : Interval s5Atlas 5 9696 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9792 : Interval s5Atlas 5 9792 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9888 : Interval s5Atlas 5 9888 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_9984 : Interval s5Atlas 5 9984 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10080 : Interval s5Atlas 5 10080 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10176 : Interval s5Atlas 5 10176 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10272 : Interval s5Atlas 5 10272 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10368 : Interval s5Atlas 5 10368 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10464 : Interval s5Atlas 5 10464 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10560 : Interval s5Atlas 5 10560 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10656 : Interval s5Atlas 5 10656 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10752 : Interval s5Atlas 5 10752 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10848 : Interval s5Atlas 5 10848 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_10944 : Interval s5Atlas 5 10944 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11040 : Interval s5Atlas 5 11040 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11136 : Interval s5Atlas 5 11136 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11232 : Interval s5Atlas 5 11232 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_11328 : Interval s5Atlas 5 11328 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 11355 := (concat (concat (concat (concat (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576))) (concat (concat bs5_5_672 (concat bs5_5_768 bs5_5_864)) (concat (concat bs5_5_960 bs5_5_1056) (concat bs5_5_1152 bs5_5_1248)))) (concat (concat (concat bs5_5_1344 (concat bs5_5_1440 bs5_5_1536)) (concat (concat bs5_5_1632 bs5_5_1728) (concat bs5_5_1824 bs5_5_1920))) (concat (concat (concat bs5_5_2016 bs5_5_2112) (concat bs5_5_2208 bs5_5_2304)) (concat (concat bs5_5_2400 bs5_5_2496) (concat bs5_5_2592 bs5_5_2688))))) (concat (concat (concat (concat bs5_5_2784 (concat bs5_5_2880 bs5_5_2976)) (concat (concat bs5_5_3072 bs5_5_3168) (concat bs5_5_3264 bs5_5_3360))) (concat (concat (concat bs5_5_3456 bs5_5_3552) (concat bs5_5_3648 bs5_5_3744)) (concat (concat bs5_5_3840 bs5_5_3936) (concat bs5_5_4032 bs5_5_4128)))) (concat (concat (concat bs5_5_4224 (concat bs5_5_4320 bs5_5_4416)) (concat (concat bs5_5_4512 bs5_5_4608) (concat bs5_5_4704 bs5_5_4800))) (concat (concat (concat bs5_5_4896 bs5_5_4992) (concat bs5_5_5088 bs5_5_5184)) (concat (concat bs5_5_5280 bs5_5_5376) (concat bs5_5_5472 bs5_5_5568)))))) (concat (concat (concat (concat (concat bs5_5_5664 (concat bs5_5_5760 bs5_5_5856)) (concat (concat bs5_5_5952 bs5_5_6048) (concat bs5_5_6144 bs5_5_6240))) (concat (concat (concat bs5_5_6336 bs5_5_6432) (concat bs5_5_6528 bs5_5_6624)) (concat (concat bs5_5_6720 bs5_5_6816) (concat bs5_5_6912 bs5_5_7008)))) (concat (concat (concat bs5_5_7104 (concat bs5_5_7200 bs5_5_7296)) (concat (concat bs5_5_7392 bs5_5_7488) (concat bs5_5_7584 bs5_5_7680))) (concat (concat (concat bs5_5_7776 bs5_5_7872) (concat bs5_5_7968 bs5_5_8064)) (concat (concat bs5_5_8160 bs5_5_8256) (concat bs5_5_8352 bs5_5_8448))))) (concat (concat (concat (concat bs5_5_8544 (concat bs5_5_8640 bs5_5_8736)) (concat (concat bs5_5_8832 bs5_5_8928) (concat bs5_5_9024 bs5_5_9120))) (concat (concat (concat bs5_5_9216 bs5_5_9312) (concat bs5_5_9408 bs5_5_9504)) (concat (concat bs5_5_9600 bs5_5_9696) (concat bs5_5_9792 bs5_5_9888)))) (concat (concat (concat bs5_5_9984 (concat bs5_5_10080 bs5_5_10176)) (concat (concat bs5_5_10272 bs5_5_10368) (concat bs5_5_10464 bs5_5_10560))) (concat (concat (concat bs5_5_10656 bs5_5_10752) (concat bs5_5_10848 bs5_5_10944)) (concat (concat bs5_5_11040 bs5_5_11136) (concat bs5_5_11232 bs5_5_11328)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_96 : Interval s5Atlas 6 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_192 : Interval s5Atlas 6 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_288 : Interval s5Atlas 6 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_384 : Interval s5Atlas 6 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_480 : Interval s5Atlas 6 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_576 : Interval s5Atlas 6 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_672 : Interval s5Atlas 6 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_768 : Interval s5Atlas 6 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_864 : Interval s5Atlas 6 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_960 : Interval s5Atlas 6 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1056 : Interval s5Atlas 6 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1152 : Interval s5Atlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1248 : Interval s5Atlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1344 : Interval s5Atlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1440 : Interval s5Atlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1536 : Interval s5Atlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1632 : Interval s5Atlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1728 : Interval s5Atlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1824 : Interval s5Atlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_1920 : Interval s5Atlas 6 1920 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1947 := (concat (concat (concat (concat bs5_6_0 bs5_6_96) (concat bs5_6_192 (concat bs5_6_288 bs5_6_384))) (concat (concat bs5_6_480 bs5_6_576) (concat bs5_6_672 (concat bs5_6_768 bs5_6_864)))) (concat (concat (concat bs5_6_960 bs5_6_1056) (concat bs5_6_1152 (concat bs5_6_1248 bs5_6_1344))) (concat (concat bs5_6_1440 (concat bs5_6_1536 bs5_6_1632)) (concat bs5_6_1728 (concat bs5_6_1824 bs5_6_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 42 := bs5_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_8_0 : Interval s5Atlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_8 : Interval s5Atlas 8 0 1 := bs5_8_0
theorem alls5 : ∀ k ≤ 8, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
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
  · exact alls5_8 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 9 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact fun p hp => (List.not_mem_nil (show p ∈ ([] : List BoundPool) from hp)).elim
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) (pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · exact pv
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8feeefaaafeeaf8a8
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
  have q0 : Slice true (roots gbAtlas) (target gbAtlas) (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f : Sig) 7 :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have q1 : Slice true (roots gbAtlas) (target gbAtlas) (0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff : Sig) 7 :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have q2 : Slice true (roots gbAtlas) (target gbAtlas) (0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff : Sig) 9 :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have pv : ∀ p ∈ apools gbAtlas, ValidPool true (roots gbAtlas) (target gbAtlas) p :=
    List.forall_iff_forall_mem.1 (show List.Forall (fun p => ValidPool true (roots gbAtlas) (target gbAtlas) p) gbPools from ⟨build_valid q0 [] rfl, build_valid q1 [] rfl, build_valid q2 [] rfl⟩)
  have low := boundgb certgb allCuts pv
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074602 * 2 ^ 32 + 4276811944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37337.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.or,[4,6]⟩,⟨.or,[5,7]⟩,⟨.and,[1,4]⟩,⟨.or,[3,5]⟩,⟨.and,[9,10]⟩,⟨.or,[3,9]⟩,⟨.and,[2,12]⟩,⟨.or,[11,13]⟩,⟨.or,[0,14]⟩,⟨.and,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4276811944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4276811944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37337

open PEqualNP.Outside.L_meta_37337 in
theorem PEqualNP.Outside.L_meta_37337 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074602 * 2 ^ 32 + 4276811944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074602 * 2 ^ 32 + 4276811944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
