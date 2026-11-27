import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_33392.Model
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

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

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
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
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

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
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
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
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
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
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


end PEqualNP.Outside.L_meta_33392.Model

namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 7, 8].getD j 0

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

def checkRow (g : Atlas) (k i : Nat) : Bool :=
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

def blockOK (g : Atlas) (k start n : Nat) := segment (checkRow g k) start n

theorem block_range {g k a n} (h : blockOK g k a n=true) (i : Nat)
    (lo : a ≤ i) (hi : i<a+n) : checkRow g k i=true := segmentRange h i lo hi

def Interval (g : Atlas) (k start n : Nat) := ∀ i : Nat, start ≤ i → i < start+n → checkRow g k i=true
theorem concat {g k a m n} (x : Interval g k a m) (y : Interval g k (a+m) n) :
    Interval g k a (m+n) := by
  intro i lo hi
  by_cases mid : i<a+m
  · exact x i lo mid
  · exact y i (Nat.le_of_not_gt mid) (Nat.add_assoc a m n ▸ hi)

end PEqualNP.Outside.L_meta_33392

namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2424e8d1c00f062ea40234a6822a2604008561521900005003e08610406141106553943684022005930f00005873804300018400018304f241ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x530a0e4f2b0015002113352800003e015800540f00020c48003025002e003d474129081f07560300003300102c55262419573c37431d120d34444b32364a2d18453f00405017062038002f005204091e1a14314c4923002a0051393a1b115a421c0b5900224e460027003b054d160e020808d02286010000281063828b200c10000141800600090033e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x24000b8e00001c09a280b30788a8602802241462600030000400002001648000004010903255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc0500081445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2667+((h/30+packedAt s0K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s0K2 (249+((h/1+packedAt s0K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 2 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x40118004220208008204820901304088105045
  | 2 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0fffffcc0fcccfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x340088028000004600a8038000000000ba9141800000491243a9c0003e084000001580000068100110800064d901e0c00050000000001280002c60500a8000001c00000600003c00026004c00e0058020000000012000010000002000608000000c000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x594a0c551e281b2f3c3733002154044445343632490f29083f2d43404c27382318170322525000000e1553310726190a5a42120905165100002b010646004e00393a4d112c1a004b004f003b200000001d2a3e000b1f580d0010000000020048351347003d41142e30561c25245704002ca040000285100000216080020c1c00312085800648132013e5390e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110f6aa221ee940439ea8087b95010e72a021d794e42aea9c859c43ccaeca3995d547329f2a4653d548ca7ea8994f15132ce21a655e53906baa720e710f31b7296636d52cc67ca918cf552319faa2633c544c7388698cf950219eaa0435e53086baa610f948421bd2804379500867ca7a04f55240afa9a815c535033ea6a04f14d40ce29a811c5350376a0a04f950409faa6613c54cc27ca9184f55230ce21c61b9408c27ea8984f15130dca02613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a4413d54882eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9084f55210b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1640452603030e000706a800000202004ac28200000000090000001e62e0006a2a0d0000400000b255254443ca9495010f295254043cc9455010f315154043a658043ccb144354732a6580434ca996010f31c310d52cc6996010d31d8485500870e6214d40c358853503166114d40c558453503196014d40a6580438c29863502308e195404c21d6510c30c310d520c31443544308718d548821c6355210
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4800c01001445c04354732a12e021aa598e05625845350304b12c029a81845856014d40
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2667+((h/30+packedAt s1K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s1K3 (998+((h/8+packedAt s1K3 (950+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf8f0ffc7fffc7e1c71c0e3fc7ffc1fe10f3cf
  | 2 => 0xf00ff1ff878ff8fe07e00fc7f8e1fe1e633d33
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40118004220208008204820901304088105045
  | 2 => 0x52228891414810a0521244248449414612512
  | 3 => 0xaa444512412900354802489092092941828a28
  | 4 => 0x230064a01101924651486000e48c0c44a40f80
  | 5 => 0xcc088903664e2499a6938f24001031995bf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0fffffaa0faaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x700b42000c0159f38896244e0cf2a3a40ca518017140a000174c3478052a0c20028519b265810b34444005e2490e145400000900000000043080149940109ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x640a9f4f410261bc02000b0a0ce001d1a87a0211800e67e2f83088660500c9e682e0ec8c1c18104e0120880000793a16c006e001889c3800000002c241844200290140c574185064273b074b418300dc006d000f0008712160aa2a0c98d00204302000420d17462000005c80001a888a67c000007e0d0d878962e03800fe4a2196412001b144000b00134721f001e10404409acac3e098004c342483d0a2f00000d8452f1ec56003911cea713b9405a69149501c25420ccca09010a01060001000f060d370c0600070003000b440207002904020a100303020f010000000104020a010b2102b7294876d5290e7ca721eb94a43d6a94873d5190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010e7aa021ee540439ca80875e5390abaa7216710f329f2a4653d548cb5ca9196b55232b6a9c65ae438cb5887194fd51329e2a2659c434cb5ea8996b15132e7a9a65cf434cb5c86996b10d32e621a658c434cadca4194f94f41d719683ad32d067aa1a0cf552419e29a83ae325075a64a0edd45419fa82833e541067ea998cf15331b7296636d52cc79a6598cf952319eaa463b5418c67ea898cf15131e699263b5414c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d548867ca810cf55021af298435d53086f4a010de540219f29e81ae32d035a65a04f547409eaa4813c535035c64a06b4c9409fa8a81bb505027ca8204fd53309e2a6616e52cc2daa598734cb309f2a4613d548c37281184fd51309e2a261cd324c37280984f950309eaa0616e520c2daa4185d94430baa88613e548827aa9104f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa8885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1618000000101c003552d000002c002808028c49220000c1f00a070000940163c0002900003844e2488048009a12ab881d34658232e30d885e141ab043d30000240000e0608000180d100181c218a358a5310f265254443c95495110f315194043ca9495010f295254043cc9455010f315154043a558443cca996010f32a9584438caa96010e32a5584434ca996010d32a3993534ca2e6590d32a398e434ca2e6510d32a9584434caa96010d32b1584434cac96010d32a3994434cb0e6510d32e1984434ca8d6110d32e1584434ca856110d32e2980434ca8d6010d32e2580434ca896010d328e580535070c534c9418e58054cc70c544cb31c3151324c6346550531e14c9414c6356114d40c314d32502356115330c315132cc30c544c9308e195404c38932501308718d544424d6314910d454d10043615244010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x680082600005390603a05866010d32d04c2b00869968161580434ca84b80a699283425c0544cb31c08ca9928298d057114d3250282b88a899661821953250130
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s2K5 (864+((h/16+packedAt s2K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s2K4 (4032+((h/45+packedAt s2K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s2K3 (2012+((h/16+packedAt s2K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s2K2 (453+((h/3+packedAt s2K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1e1e3c7fc7f1fe3f1c63838fe3f1f87f10f4cf
  | 1 => 0x1fe03f8ff8fe3fc7e07c03f1fc7e3f87233b33
  | 3 => 0xe0003ff3ff003ff8ff8003fe3f803ff8c3cc3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x42804600424208400820908240910822105045
  | 1 => 0x84088840908050084044211084281204212112
  | 3 => 0x15511292424a401b4804a242904a550c28c28
  | 4 => 0x8440122002004922509080032448110440e80
  | 5 => 0xd198224836c93924da7273c900090666bbf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffee88eeeeee88ffffee88eeeeee88ffffee88eeeeee88ffffee88eeeeee88ffffee88eeeeee88ffffee88eeeeee88ffffee88eeeeee88ffffee88eeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6205c0281e3531454bc0991c0010b0060b251024d91408c51a000002d487839d00b0015064c29c4e0092b3e1060052011215c000003400082032140010004ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4a00050022d0003c2e400a9f044000914d061b000080000170007e00001a0ce00048e800662f18400643482d0200020006482131bcb05f0b1090084040dd0a6c179f4b62b229ece447371d47052199e8a0392e0b0c06d0f96898713595c2273001a848071e8405046318f8460022000000c0f13c14033c0d8ba7e0e1fca800380948243431e400300d138e8002c8a43a0e1081890000c9440a001a89c00000018862760684cac0000000ee3424954303c1521c404b1d934ca09040206040001110117000e17040008130b000404010414270404021704000200010500050104002700090d01b7294876d5290e7ca721eb94a43d6a94873d5190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010e7aa021ee540439ca80875e5390abaa7216710f329f2a4653d548cb5ca9196b55232b6a9c65ae438cb5887194fd51329e2a2659c434cb5ea8996b15132e7a9a65cf434cb5c86996b10d32e621a658c434cadca4194f94f41d719683ad32d067aa1a0cf552419e29a83ae325075a64a0edd45419fa82833e541067ea998cf15331b7296636d52cc79a6598cf952319eaa463b5418c67ea898cf15131e699263b5414c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d548867ca810cf55021af298435d53086f4a010de540219f29e81ae32d035a65a04f547409eaa4813c535035c64a06b4c9409fa8a81bb505027ca8204fd53309e2a6616e52cc2daa598734cb309f2a4613d548c37281184fd51309e2a261cd324c37280984f950309eaa0616e520c2daa4185d94430baa88613e548827aa9104f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa8885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xa00625d2a6003c280242c001566448e40340000000f025800522483139d0058a9a2260300520c99f001080042bc38036016b050b802a008c008380214482000811a20000020000084a358a5310f265254443c95495110f315194043ca9495010f295254043cc9455010f315154043a558443cca996010f32a9584438caa96010e32a5584434ca996010d32a3993534ca2e6590d32a398e434ca2e6510d32a9584434caa96010d32b1584434cac96010d32a3994434cb0e6510d32e1984434ca8d6110d32e1584434ca856110d32e2980434ca8d6010d32e2580434ca896010d328e580535070c534c9418e58054cc70c544cb31c3151324c6346550531e14c9414c6356114d40c314d32502356115330c315132cc30c544c9308e195404c38932501308718d544424d6314910d454d10043615244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x83400413000029c461a05866010d32d04c2b00869968161580434ca84b80a699283425c0544cb31c08ca9928298d057114d3250282b88a899661821953250130
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s3K5 (864+((h/16+packedAt s3K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s3K4 (4032+((h/45+packedAt s3K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s3K3 (2012+((h/16+packedAt s3K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1e1e3c7fc7f1fe3f1c63838fe3f1f87f10f4cf
  | 1 => 0x1fe03f8ff8fe3fc7e07c03f1fc7e3f87233b33
  | 2 => 0xe0003ff3ff003ff8ff8003fe3f803ff8c3cc3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x42804600424208400820908240910822105045
  | 1 => 0x84088840908050084044211084281204212112
  | 2 => 0x15511292424a401b4804a242904a550c28c28
  | 4 => 0x8440122002004922509080032448110440e80
  | 5 => 0xd198224836c93924da7273c900090666bbf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8eeeee8e8ffffe8e8eeeee8e8ffffe8e8eeeee8e8ffffe8e8eeeee8e8ffffe8e8eeeee8e8ffffe8e8eeeee8e8ffffe8e8eeeee8e8ffffe8e8eeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def s4K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x1c300b00a9001250800a8ae59a1000009a000000000e7989060000a8003004040006fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8040000000241e040081c0e04028000c0d0280404000c000020f010080c2600808001002020020abe41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414caf10532bf404caf10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432f6410cad90432bd410cbd50432b5410caf90032fa400cae90032bd400cbe50032b9400caf90b31bd42cc77ccb31dd32cc6f90331bd40cc6f50e31be428c6f50a31be418c77cc631f7318c6f90231bd408c6fd0931bc424c77cc931dd324c7dcc531de314c6fd0131bc404c6f90c31be420c7b90831ae420c6f50831ed420c6b50831be410c77cc431f6310c774c431f5310c754c431be400c7e90031ba400c6f50031f9400c6e50031bf43c86f90f21bd43c86f10f21ee32c87b4cb21be40c86f50321bf43886f90e21bd43886f10e21bd42886f90621f631887d4c621ef21887dc8621be40886f50221bf43486f90d21bd43486f10d21ee32487b4c921f631487d4c521f721487b88521bf40486f10121bf43086f90c21de43086790c21bd43087750c219d43086f10c21be42086f90421ef21087d88421ed21087d48421e521086f90021fa40086e90021bd40087e50021b940086f90b30bd42cc37ccb30dd32cc2f90730bd41cc37cc730dd31cc2f50e30be428c2f50a30be418c2f50630be408c37cc230fb308c2fd0930bc424c37cc930dd324c2fd0530bc414c37cc530dd314c3ecc130de304c2f90c30be420c3b90830ae420c2f50830ed420c2b50830be410c3d90430b6410c2f50430f5410c2d50430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20ee32c83b4cb20be41c82f50720ef21c83b48720bf43882f90e20bd43882f10e20bd42882f90620bd41882f90220fa30883e4c220ef20883ec8220bf43482f90d20bd43482f10d20ee32483b4c920bf41482f10520ef21483b48520fa30483e4c120fb20483b88120bf43082f90c20de43082790c20bd43083750c209d43082f10c20be42082f90420f641082d90420bd41083d50420b541082f90020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43d8c710f531c43d88710f521c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610be40843e8c210f930843e88210f920843dc4210fb10842fd0d10be43442f50d10bc43442fd0910be42442f50910bc42443d8c510f531443d88510f521443e8c110f930443e88110f920443ec4110f610442fd0c10be43043790c109e43042f50c10dd43042750c10bc43042fd0810be42043b90810ae42042f50810ed42042b50810bc42042f90410be40043dc4010fa10043d44010f910043c44010
  | 1 => 0x989a000d49584c731d4000200000000000359be000f8790fc321c42300019116050627c9a658924571967f87e000000d0a00019c4b9541e2460015a1d9c8962540f9800001a00136001228904000000001b85a0003a86c0a1081e8503081e2520c6c0226f22a6e84e500f2111c21a9da2aa367f1a83b12a4c97a0000000244801d0758588823a81100000d87e0005c23c521e036992838ce5818e2c12080966868482902c668f4530f0000001d10a11a5000178610a800068001dc340000011e2e800002282e03c922065d9f0000007a88a430845b810630bc261ae00150001e212a14000002ba4c73a348c836438327d1ec389a47a23e90816629527e82a51988841d20014a5b1280e09e508b209000000006c830650fe8291800198001022d000860000021e00208948de0000004808001c65123093800329f64f0dc418040008e1b80044056798006080007186060521680c240020016a1805c8b0543b9646d9aa2099e641122980039800199264c1347611a0ba122d93e000960013a001b4218f67b8003ea1c17974560ac8e25a2fa4a000e8539de0380000000109c08892c01a2e3317e001560009c00138728c66b2265f072000000280000000000004511c5c8000007c00000000000003a0000000000301a23100000000000d200070381a03915e2208028800859040024000092008080001000101a030200800040100802090000802030000406090203000000080002000002404010000400070f030040801800020c06808041500064060701820081108014
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x63b13150031c898a8018ce94043c8672a021e438c434cb219d2808710ce54043887288698c433b5050d219c2828690ce9404348672a021a432c544c921c621a6490d91453248668a898a4394434c521b22926290f14c9314863ca6202431d53101219d2868610ce543430863aa9218431e5310c21972908610cd9444308674a021843395010c21c6a1e4210e550e21086caa5108432f5448421c6a1a4210cdd51210872a8690843675448421d3aa24210e9d0d210878c8690843a54348421e2a1a4210e150d21087348720043994390021f090c8010e9485400873486a0043994350021f090a8010eac85400876442a0043a92150021d890a8010e8485400866ca221261355110930c6212649856141324c25ca420a612d5210530ca20a629856141314c34c8520861a54290430d3212821869509410c31a85980619541cc030aca9c60186a50a300c36283180611f544c030c6a12601865505300c276a898061a9424c030d8a0a601856d51300c336a898061ca424c030cca12601872509300c3128498061d2414c030cca0a601874505300c3228298061365110f209aa8887906310d32c826ca221c41355110e20cc21a61104dd454348268a2a1a41365110d209aa8886904b1513248318869924168504c9208f29882904754c41483488290a416850485209c2a260906610d30482d0a498241c9324c1209b28e86104d547430823aa9218411e5310c209729086104d944430826aa2218413a5010c20cb21c82106550e410832c86a0841954350420c6a1e40106950720083328710041695288020d8a0c40104bd51200831a8690041a541480209daa240106650d200836282900416b5448020d5aa240106ad0d20083948690041a94348020e4a1a40106250d20083c48290041a94148020f0a0a401068505200825ca421e212d5210f108f29885884754c42c43288698e21a442487109729087084b548438423ca6214211d5310a10cc21a61086a109208425ea4a1a212c5250d109729086884b548434423ea6a12211c53509108f29884884754c4244268a898a2194434c510b828262884d15121443488490a217050485109c2a260886610d30442e0a298221d1314c1109c2a240886a10920442e0a290221e121481109729686084b54b430423aa9218211e5310c109729086084b548430426ca2218213a5010c108f29e84084754f420425aa9210218e4390810c6a1c84086390d420431a86a10211e53108108ea9884084b948420426ca2210213a5010810caa1e20086950b1004272a908021994384010d4a1420085c546100426ea888021954344010d2a1220084ed5110043328688021a94244010b9aa220086cd5110043668688021d24344010d8a1a20087450d10043228688021b34244010f121220086c50910043c28488021a14244010
  | 1 => 0x2c0a8498a65f8346c8d80f98811000002162510e321d21b800359aa591c2300e81f97c3b2188098a2317a8106467800608fe000000006c61a1253a1a241ee3704a381fa290382497800000479021f1e87a9b4001e46980000000009cc5282c001c84f0ac00120078c26c22a000002c8000000083930341fe258604c99041042061de0003a6b0d27d8ce4d22c0490a5b962001e2570405c0008990c1582403196001724520036912540ea0b8007593e5782041800889d0000a24d9a84a15a000460001a83138001c61e8b8229da0a8a0149f48299408848461ba3781635198000807c8141c12a6f0b43b9c4268880d8b65109e1a008671565081c3da28780aa4b110150265821e700841384c5a8003e9ce038ca3918c89146000005503c3112268000818623f1ca6e0f8001ae001d80017653116400ba00152040784e91a688f27b08202948820cc691dc00158170e27980000030000741a8bc6d8000011c3c0500a2100c89c5999a871808808e500e664872639081d866219743d0067e1680000000000750000000000214611f031898168be5b12e001fc2b8000005e16004491be030343631080200c4702820321c0080800000002406060081c000202010180b010080601000440011010000e04000080406000080000088100e06008600004008100412080300c140001c000d0083c14020000002000180c260e000042a0a048002c000000c080000ce940414ca72a020a653651101329aa8880995354e320ca3ea8990652f544c832a7aa2641963d51320cb8a65208658d3250432e2992821965cc9410cb4c64a0865953250432d29928219614c9410cb926520065b24190032d8a0c8019634c9400cb9264a0065b24150032d8a0a801966cc9400cb5464a0065993250032d49928019624c9400ca74a021263395010931c62126498d5145324c65ca4202632d5210131c6a166218d554e310c74a85188631f544c431c6a126218cdd51310c74a849886357544c431cbaa26218f1909310c72a8498863c5424c431c2a126218ea90a400c7528520063d13190031ca98a8018ea909400c75284a0063d13150031cd98a8018ec8c5400c73262a
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x59019811b0f8c00000880161700020d8e9589000b00181100000800002000001e9e07989200000000000d049a108b80001280000e0f1c80001787138601941d06830a80001c11949f000020801f9a8c9900001b9d80150000040016930080038982850000000a00000000040020e04080060c08602105800614084e04c94190032e04ca4150032e04c94150032a2580424c93194580514c931e05093190031e09093150031e05093150031a2580434cb21a4580434c621a2580434c92198580514c921a4580434c52198580524c521a1191324c521c1151324c521a85834348421a15924348421e050d2190021e090d2150021e050d2150021a1584424c93094584504c930a1588414c53092588504c530e050a414c030e0909414c030e0509414c030a1584434cb20a4584434c220a1584434c92098584504c920a158c41485209258c5048520a4584434c12098584524c120a2191324c120c2151324c120a85874348020a25924348020e050e4148020e090d4148020e050d4148020a1588434c710a158c4248710a2588434c210a258c4248210a1588434c51098588504c510a158c42485109458c5048510a2588434c11098588514c110a4191314c110c4151314c110a258c42481109458c5148110a81912148110c81512148110a858b4344010a45924344010a458f4244010a85924244010e050e4244010e090d4244010e050d4244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*4) 4
  | 5 => packedAt s4K5 (i*15) 15
  | 4 => packedAt s4K4 (i*26) 26
  | 3 => packedAt s4K3 (i*37) 37
  | 2 => packedAt s4K2 (i*48) 48
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (5+((h/1+packedAt s4K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (408+((h/8+packedAt s4K5 (360+(h % 8)*6) 6) % 37)*6) 6
  | 4 => packedAt s4K4 (8752+((h/100+packedAt s4K4 (7852+(h % 100)*9) 9) % 399)*10) 10
  | 3 => packedAt s4K3 (11160+((h/93+packedAt s4K3 (10323+(h % 93)*9) 9) % 335)*10) 10
  | 2 => packedAt s4K2 (3322+((h/22+packedAt s4K2 (3168+(h % 22)*7) 7) % 105)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfd273c777b0cf
  | 1 => 0xffffffffffffffffffffffffefe39cf87bd333
  | 2 => 0x77fc1f3f83ec3c
  | 3 => 0x7bffe03ffc0fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa0448401108045
  | 1 => 0x10882108210112
  | 2 => 0x9014052020428
  | 3 => 0x6000aa4400a80
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 15 s4Pos s4Neg, 0xfee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x4009000630004855201080264078a063401f4a8c01c1c88d0022000142e1c9013c8151d1864002169ca8800995800058d80500800c22800462ce082041ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6613d54cc2f8a9986fd0f30ef21e61bd43cc3ba87986750f30bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7186fd0e30dea1c617e528c2faa5186fd0a30dea14617e518c2faa3185f94230ef98461fb308c2fea8985f95130beaa2617c544c37e86987790d30dea1a61dd434c33a86985fd4930be29261bf424c37a849877cc930ee992617f514c2f8a29877cc530ee98a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30dfa1861bd430c2fca4187b94830b7290617d520c3daa4185b54830dfa1061bd420c2fca2187d94430bb288617d510c3eaa2185d54430bf28061df300c3f46018774c030fc980617f54c82fca9906f953209f2a6417d54c837aa9904f55320be2a6417f53c82fca7905f54f20be29e41bf43c837a87906fd0b20f721641bd42c83da85906b50b20f719641ed32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea9441bf428837a85105f94620bea8c417e50883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e86906f50d20dfa1241ee424837a84907b50920d6a1241ee32483da64905fd4520be28a41ef21483da42907e8c120fc98241fb20483dc40905fd5020bf2a041be540827ca8105f55020deaa0413d54082f8a8105fd4c20bf29841de53082bca6105f54c20eea98415d53082f8a6106fd0c20dea18417e520837e84106f50820bf28841f651082eca2105f54420faa88417551082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7886fd0f10dea1e217f52c42fca5885f54b10be29621bf42c437a85887d90710faa0e21f631c43ea63887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5086fd0a10dea14217d51842fca1087e90210fca0421fa30843f261087e88210fc90421f710843f621085fd5110dfaa2213f54442fca8885f55110be2a221bc5444278a8885fd4d10bf29a217d53442f8a6886fd0d10dea1a217f52442fca4885f54910be29221bf424437a84887d90510faa0a21f631443ea62887d88510fa90a21fa40443f280887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be29821bf430437a86085fd4810bf29021ee52042dca4085f54810f6a90216d52042f8a4086fd0810dea10217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xe50906faa120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf29083ee52106dca420df54841f6a90836d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63bd43cc7ba8798e750f31bf296637d52cc77e8598ef50b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c77a8718df94a31bea9463bf428c77a8518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131dfa1a63de434c77a8698f750d31cea1a637f524c6f8a498efd0931dea1263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31dfa1863bd430c6fca418fb94831b7290637d520c7daa418db54831dfa1063bd420c6fca218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790efd0b21f721643bd42c87da8590eb50b21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21dfa1c43bd43886faa510efd0a21dea14437e51887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1a43bd434877e8490fb90921dea1243ed424875a8490fb8c921f699243f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610efd0c21dea18437e520877e8410ef50821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f50e40bf294817d529037e85206f50a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40dfa1881bd43102fca4207b94840b7290817d52103daa4205b54840dfa1081bd42102fca2207d94440bb288817d51103eaa2205d54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa
  | 2 => 0x20000000200000c0100200000c008000040000001200a0100880c0000080601500400c0000900c0200700200001400002004008000010000180100e0260100100000400000800000030048000000000301900c00002000bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0f7ea5a1ef94b43d729687bd52d0e7aa5a1eb54b4396a9687bc52d0f7ea3a1ef94743dea8e87bc51d0f7ea1a1ef94343dea8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd49439fa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0bbca7a15794f42bea9e85dd53d0abaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e859e53d0b7aa7a14f54f42cea9e851d53d0b78a7a16fd4742df28e85bd51d0b78a3a16fd4342df28685bd50d0b78a1a15f552429eaa4857e5390afaa7216fd0e42dea1c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a853f5350b7ca6a16f54d42de29a85bf5250b5ea4a16fd4542df28a85bd5150b78a2a16fd4142df28285bd5050b78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665ee42ccb7a85997b50b32d6a16657e51ccafaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cb7e87197790e32dea1c65dd438cb3a87195f94a32dfa1465bd428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cb7ca8994f95132beaa265bd544ca7aa8995f15132dfa1a65bd434cb7e84996f50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6196fd0c32ef21865bd430cbba86196750c32bf29065bf420cbdc84196f50832f6a1065ad420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837
  | 3 => 0x64a0015e15f50e354000002282c9361a71203b0239ab276ad429b5c000cbce100000000000000000000000fa19e17800117000cc43480000066cc48002ac7e4002510005ed5300037a7b95f0436c2dac0018b0909d08b00056c6080d226368b687c8002645b4b40284966ec74b2a21e9593b8204b26fcd200039c748a430f00000082a126447ec3fa0e124a8d503010365bc00000272000941e100085c0013e4445dc002d200061c0f8e2006be06e98a3b00004bb086aa9f94780007a000002540e000032aba0d4001a58383d4418c686c2fcb50eb8d72ae5b8660413e69fd0f03f3964a4939594082c10fade2e4578109da19a5cc6d1035de29917a5b062c28f40064126b8002150b05098701607800176a1a2968512ba02000d481a0d91ccc5cb82476a2cf0ce14415e21d09afe5d8138cd0461f690890a11000481230811de000002d00007a40016332a0008f000000000ae29a0463b43b0835f25015f8003520017bb263260014f8132fe00000000000440001fe0de0000000000000000000000001120000003204c9aa000c6d650000007d00022c2f46c91b975224000b30005822b0c832d0002f4000001d400000131000000000006c45494f10d2d2000fe0005320000023a1c6000001bc3a0324000fe000001461492c0230002963805b0e89be6008f8ac2a124c2342c8003de0244d2273c012899abb4bca5c00000000c084eb45000b59510000e623c0030503ad7c002c2462000d2b65298000003430000a87f81960ea603333e1447ada50221e69499029b6cc4889b87c0001908536c038d003595a69c00156a8d4de000aa8003e42a4000322ba0000021634c000001ec6982707b24a466675b82c66680c0a191d3a6224001db06e970b58565f4828821cc32c13ca50000489010c9d60000000000003cb1473a492822f00010e3860015c80059e0a4bc2b20e20005d9611803600007d0003b98a0006ae4d40280000700a01c0880d0000040080d00e02800807002024000060000000300200a004000010080000000000200c0000500000000801000000010020000b00000000001c14001000034000000060240000000e0080000000201800813008004018030020040100501a0000402900c000000000000040002800a00006001002004000020020140b8000220000080701602c000000040240380d0000140000000000000000000010010010000040100301a00c000040000000000100600400808014010010100000000000b00600c00006034000030020020280101500a0880400d00401403004000014000010020000000301000c000000020340580400000400802002018008000100180100000401c0000000601c000000000140280400000004800012010028000020100180200001409800000008010030020140000
  | 4 => 0xdc504001458000000008e000000da5688042ec894440003ec000000de168c7c000000005c4a805a59ada800289000000002655928a8d81012f2aa800000000b60002102120000000200000135a452480004c000258000000001880007e054000b9911ae23f0550000006500000024f00000000119000a45a111f1d6001898ab000000e41e2000b70589c100000078000000cfc000000007e8e48000000000000041aac00034f4c403000000268710000003b20d40018400000133953000000a88000000000033a00013000344000a4d418f8306001708151d00011f8a10005a852800528000003181360000000032e000ba04233c001a800000081c281150000cd908b565cd75368144e4add992410e8acd0e8b728ea544b0b90aa8f06803e30c8f43c000000d91383090ae9213e80064e00000045088754c28004a08b92c09e62417400000410d8c860000f212c000c215c2a00024e00000000000000a94039910000018e0000000000029c5e0000092b126c000b10006d0001ad0000ea9e1821a1000aad1826918ab2d859d4634bf00007a166cd9b718e6ac409728006521015203617ca9d8184d186dbc9291a0ee8ac002cc000a20952fd0d041c072903fa000001456c018c000004d09e4633355e8c4485ac40da2291b3730000000013f000000dc000658c30800cb03000174b3701aad00002767a0bc2e0006da000001234720000012f3ea8b5670004c6a108db480fc000002db5c000039253000b5c0b8001a40009c2f657a000d78d400099800000146a74000db46800000000000184f8000000000cfac7000244003063ca0018c80000029000000000000f235400068d370b64be680001ac000000b20bf05a29c000d6000000000003b860138ac81c8254ca20c0166a00009335a001738b80000017580000016c12800324149a3a80402000792750000019980036e000000001ea3440000001444d3b0c13bc77c8c00829a17da99ed61a000e50265706d8339b538e8140008631e000000005020004f8396bc62008b415523d0d118c5c673c0002b1be00191800442798000000000004283a4ba71903200450251a6b245dcce47b93a514870a31b34aa6e85525a6b018000a8e62a7fd7d8a048859c0000068c860000004c8b4c002320a24207e95b4d4bc95624d000b900000000090c00229058cec001f74f6ba97992b63c5389e80025ca14000006b2000dc800000594002dd4f8000002af000000000000005f53d0ca09233901a3b5b29cd602df1e20017fa0b1746c52614f0200007080000000045ae8586a48003672223955722038acac37130000000000005e22098b0000004b5431e30c48d40021b00034c0018111c000000003ce0017a87b0000000037141e20000338000000001f1108664638005aad258ea3805cdc800000000000be000
  | 5 => 0x1e2b4002613bac409e33039a00154000330000000000000ec000001c0d6d300
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2528423d6494a108f990528423d6414a109798c528425d6314a10a758f428432e5250a10cb5494284399434c210ea509208423d63d51108f58b544423e64951109798c544425d63151109b988544426d62151108f994544429d6315110ab588544431e63151108f58c544431d63151108758c544432e62151108f588544432d62151108b58854443356115110ce580544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442ad62d0d108f995434423c6550d10c794d434431d5350d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910a758f424423e65509108f195424432e5250910cb549424433454905109d19541442f060505109d1953144395434c510bc18131442746548510e950921442f06048510ce15240443b241901109e19540442f06150110ec5054044278654c110e650d30442f0614c110f44c530442786548110ea50920442f06148110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10c7952530431d5494c10c7992530431d6494c10c7951530431d5454c10c7991530431d6454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f43042ad62d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810a758f420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb549420433554c4010d554f100436552c40109e59610043395484010d654e10043695284010bc58610042776544010cd55110043555344010d9549100427b6544010ce55110043595344010da54910042f36544010dcd9510043b36444010ec19110043735444010ec95110043715444010ec55110043315444010dcd4d10043d25344010dc54d10043d15344010d454d10043b34344010ec50d10043735244010f894910043715244010f854910043615244010ecd0910043b14244010
  | 1 => 0x829d6395320c798e54c823d6395320c758e54c821d6395320cb98a54c823f63553208f99353c823d64d4f208f99253c823d6494f208f99053c823d6414f209d98453c82756114f208fd9743c823d65d0f20ab58b43c823f6550f208f59543c831f5350f20c714d43c829d63d0b20cb95142c82af6550b20cbd9542c82af6350b20cb94d42c832c5350b20ab59232c838d438cb20ab59132c834c534cb20cb50951c82ad64c8720cb55321c832d54487209798c548825d63152209d984548827561152208f992538823d6494e208f990538823d6414e209d98453882756114e20ab58b438831e5350e20c754d438829d63d0a208fd91518823c6454620e650d308825e63951209758e544823e6494d208f592534823e6414d208f59053482766114d209d58453482ad62d0d20c7d4d434831c5350d20a758f42482ad64909209b19542482e86050920cbd95424832c6550920abd8d424832e5350920cb14d42483ab6050920ea18142482ad648c920e350e324826c654c920ab591324834c534c920cb50b514823e64145208f590514825e63145209758c51482ad64c8520ea50a3048278654c120e650d30483a9424c120f24c930483a942c81209798f540825d63d50209d987540827561d50208f596540823d63950208fd8d540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530823e6494c208f592530825d6594c20c7952530831d5494c20c7992530831d6494c20c7951530831d5454c20c7991530831d6454c208f990530823d6414c209798c530826e6214c209d98453082756114c209e980530823f65d0c208f597430831e53d0c20c754f43082ad62d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420829d63d0820c794f420831d53d08208fd95420831e5350820c754d420832e5250820cd95251083355494420d594e51083555394420cdd0e51083354394420cdd0a51083354294420cd95151083355454420d594d51083555354420cdd0d51083354354420cdd0951083354254420cb553200834d53c8020d954720083595388020dc546200826f6548020cb551200834d5348020d9545200827b6548020d654d20083ab4248020dc545200825e63153109758c54c426e62153109b58854c423e6494f108f59253c423e6414f108f59053c426e6214f109b58853c42ad62d0f10c794d43c431d5350f108f99252c423d6494b108f99052c423d6414b109798c52c425d6314b10a758f42c432e5250b10cb54942c4395434c710e950921c425e63152109758c548426e62152109b588548423e6494e108f592538423e6414e108f590538426e6214e109b58853842ad62d0e10c794d438431d5350e108f99
  | 2 => 0x5250a40cb549429029d6310640ab58841902b96010640ab58b435031f5350d40a758f425032f52509409798c515025d63145409b988515026d62145408f997415031e6454c40c754f43102ad62d0c40c794d431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032e6454840cbd0d521032d4354840a758f421031e53d0840c754f421032d52d0840c794d421031d5350840cb94942103565394440d554e51103665294440d954a51103374394440cd50e51103374294440cd50a51103565354440d554d51103665254440d954951103374354440cd50d51103374254440cd509511023d6590440c754e411032d5290440cd546411029d6310440c754c41102ad6210440cb54841103355110440ae580411031d53d0040cb54b401033551d0040dc546401023f6550040c754d401032d5250040cd545401027b6550040dc545401026e62953309b58a54cc2ad6295330c798e54cc32e62953308f58a54cc32d62953308b58a54cc23f6255330ab58b43cc31e5450f30a7d9543cc31f6550f30a7d8943cc23e6494b308f59252cc31d4394b308fd9742cc23d65d0b30a758f42cc23f6550b308f59542cc29d64ccb30e350b32cc29d644cb30c750d51cc29d64cc730c755331cc31d544c7309b988548c26d62152309d984548c2756115230ab58b438c23e6494a308f592528c29d63d0a30cb949428c32d5250a308fd91518c23c64546309b98a544c26d6295130ab58b434c29d6490d3097195434c2d86050d30c7d95434c31c6550d30a7d89434c39b6050d30e6181434c23e64149308f590524c31d43149309d984524c2756114930a758f424c32f5250930cb149424c29d64cc930e350b324c29d644c930d3149324c31d43d45308f990514c23d64145309b988514c26d6214530a7593314c39943cc1309b98b540c26d62d50309d987540c27561d50308f596540c23d62950308fd8d540c23d63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23d65d0c30ab58b430c23f6550c30c794d430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c29d63d0830cb94b420c32d52d08308fd95420c23d6550830cb949420c32d5250830cd952510c3355494430d994a510c3655294430cdd0e510c3354394430cdd0a510c3354294430cd951510c3355454430d9949510c3655254430cdd0d510c3354354430cdd09510c3354254430c7553300c34d52cc030d5547300c369528c030dc546300c25f654c030c7551300c34d524c030d5545300c27b654c030e6d0d300c369524c030dc545300c25e63953209758e54c
  | 3 => 0x8318fd95420c63d6550831cb949420c72d5250831c7553310c74d52cc431d954a310c65f654c431c7551310c74d524c4319dd95310c797434c431d9549310c73a5494031ce552500c76a5294031da54a500c73b4394031ce50e500c73b4294031ce50a500c73a5454031ce551500c76a5254031da549500c73b4354031ce50d500c73b4254031ce509500c75b3154031dc8c5500c7593154031dc4c5500c65e63953219758e54c869d6395321c798e54c863d6395321c758e54c861d6395321cb98a54c863f63553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ab58b43c863f6550f218f59543c871f5350f21c714d43c869d63d0b21cb95142c86af6550b21cbd9542c86af6350b21cb94d42c872c5350b21ab59232c878d438cb21ab59132c874c534cb21cb50950c865e63152219758c548867a60152219e580548863e6494e218f592538863e6414e218f590538867a6014e219e58053886ad62d0e21c794d438871d5350e21a758f4288795434c6218fd91508863c64542219798e544865d63951218f992534863d6494d218f990534863d6414d219e98053486796014d21ab58b434871f5350d21c714d434869d63d0921ab592424866c6550921b9185424872f6550921cb19542486af6350921cb94d424872c5350921e9d8542487a46150921ab592324878d438c9219b19532486ad644c921d314d32487a5428c5219d1953148795434c521e950931487c5324c521e950b214872d42d41218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863d63950218fd8d540863e64150219798c540865d63150219b988540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086ad62d0c218fd95430863d6550c21c794d430871d5350c218f992520863d64948218f597420869d63d0821c794f420871d53d08218fd95420871e5350821c754d420872e5250821cb553210874d53c8421d554e210866f6548421cb551210874d53484219dd9521087555348421e9d09210873a5494021ce552500875a5394021d654e500873b4394021ce50e500873b4294021ce50a500873a5454021ce551500875a5354021d654d500873b4354021ce50d500873b4254021ce509500876b2154021dc88550087692154021dc485500871d53d0f40ab58b43d029d63d0b40cb54b42d02ad62d0e40c794d439031d5350e40a758f429032e
  | 4 => 0x550d510cb374254432d9909510cb354254432d9509510cb254254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cb994394032ea50a500cbc93294032dc946500cb715194032ced0e500cb394394032ced0a500cb394294032c750d500cb2d4254032d34c9500cb3a5454032ce551500cb994354032ea509500cbc93254032dc945500cb715154032ced0d500cb5a4354032ce50d500cb594354032c650d500cb3b4254032da909500cb394254032da509500cb294254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41ab58b43d069d63d0b41cb54b42d06ad62d0e41c794d439071d5350e41a758f429072e5250a41cb54942906ad62d0d41c7d4d435069d63d0941cbd49425065e63141419758c505066e62141419b588505071e6454c41c754f43106ad62d0c41c794d431074e5394841d354e521072f4394841cb50e521074e5354841d354d521072e6454841cbd0d521072d4354841a758f421071e53d0841c754f421072d52d0841c794d421071d5350841cb949421071d53d0441cb54b411063f6550441c754d411072d52504419dd95411075a5394041d654e501076a5294041da54a501073b4394041ce50e501073b4294041ce50a501075a5354041d654d501076a5254041da549501073b4354041ce50d501073b4254041ce509501073b4154041dc90550107394154041dc505501066e62953319b58a54cc6ad6295331c798e54cc72e62953318f58a54cc72d62953318b58a54cc63f6255331ab58b43cc71e5450f31a7d9543cc71f6550f31a7d8943cc63e6494b318f59252cc71d4394b318fd9742cc63d65d0b31a758f42cc63f6550b318f59542cc69d64ccb31e350b32cc69d644cb31c750d50cc66e62152319b588548c67a60152319e580548c6ad62d0e318f992528c63d6494a31a758f428c72e5250a31cb549428c63f64542318f191508c66e62951319b58a544c6ad62d0d31a7592434c65c6550d31b5185434c71f6550d31c7195434c69f6250d31e5d85434c7946150d318f990524c63d6414931c750c524c67a60149319e580524c69d63d0931cbd49424c72c5250931a7593324c78d42cc931a7591324c74c524c931e550f314c71d43d41318f990504c63d64141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c63d62950318fd89540c63e64150319798c540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c31ab58b430c63f6550c31c794d430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c69d63d0831cb94b420c72d52d0
  | 5 => 0x53d0b1d5314f42ab58853d0a9e63d4742a758f51d0b1d53d4742c754e51d0b1d5354742a798c51d0a9d6314742c754c51d0aba6014742ae58051d0a9e63d4342a758f50d0b1d53d4342c754e50d0b1d5354342a798c50d0a9d6314342c754c50d0ab66114342ad58450d0aad62d0e42c754d4390a9d63d0a42b398f4290aae62d0d42c7d4d4350b1c5350d42ab1894350a3e6510d42b398f4250a5e63145429758c5150a7a60145429e5805150a5e63141429758c5050a7661141429d5845050b2d62d4d42ab58a5350aaf6254d42c754c5350a9e63d4942a758f5250aae63d4942e398f5250a8e63d4942e358f5250aad61d4942ab5835250a9e6314542a758c5150aba6014542ae5805150a9e6314142a758c5050ab66114142ad5845050b1e6395042c758e5410b1d53d0c42ab58b4310a3f6550c42a758f4210a3f65508429bd954210b2e5450842cb58a54cca9d63d0b32cb95242cca9f6350b32abd9542ccb2f6550b32cb19542ccaaf6350b32e3d8d42ccb8c6350b32cb50951ccb2d4254332c758e548caad62d0e32c7952438caaf6250e32c7d95438cb1c6550e32a7d89438cb8f6250e32e3189438ca9d63d0a32a7593328cb2d54cca32c750d518cb1d43542329758e544ca6d62951328f58e544cb1d63951328758e544ca3d6295132cb58a544ca2d62951328fd8d544cb1f63551328fd89544cb2f6255132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f6350932cb553324cb1d548c9328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540cb1e6395032cb98a540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430caad62d0c3297596430ca9d6490c32b358a430ca3f6550c32c7951430ca9f6550c32c7d95430ca9f6250c32e3989430cb8d6250c328f992520ca3d6494832c750e520ca3d65d0832a758f420ca6d6590832ab592420cacd6390832e350e420ca3f6550832cb951420cb8e4350832e350d420caaf6550832cbd95420caaf6350832e398d420cb8d6350832cb94d420ca9d64cc832e350b320caad648c832b358e320cb8d438c83297d95320ca9d644c832e3d09320cb8d424c8329bd95320caad644c832e3d0d320cb8d434c832b3d95320cb4f654c832b3d91320cb8e644c832b3591320cb8d644c832a3591320cb8e544c832e3551320cb365494432cd552510cb954394432e950a510cbc53294432cdd0e510cb354394432cdd0a510cb354294432c750d510cb2d4254432d34c9510cb365454432cd551510cb954354432e9509510cbc53254432cdd0d510cb564354432cd50d510cb554354432c
  | 6 => 0xda868030050380040382809c0000182b00209c00003044024008160080040580e0240001680204c000060080000080a0230060000a81902c07c0081400600c0500601200003800000014010060260100401200604400000048000008010000400380d03a0100380e0200080080002605c0000400601c0300c06e0980100303c02002000016008008020180200481c00001c0400000a010068060240080080b0240001100f0040000000000405400000014000028110100040200202c0080000100200007803012020000000000280200001c00c13801006004008520000000880000004c018000100940200200000000018006004020020060a000800008000000030000001d806004000018010020000080000601c0c803000028078010160000000c0000101180c01e0001f02300401c02800006014000000060280e0010000040300b01e00c0000a0080b4000120000000000d0020000100700c0480080e034000008020060001000900a0180000000003c0281700e0000380700400c0100100002803801006034010080060140181900c000088010260201202100001c040030000040300900604c1400b0000b40000600a0841000400a000030000060240200a00203c000010260080380102c054030010100000280601a0040300600c028000000060040e0000100140b00f0020040c008002010028390000040000201200000001034000008050060080200203801c010020020000101100e04c008010000000080a00000006000000000028250400040480501a0440b80b00c01001800018028018080080100580c00a03c050060a4000120000000280b007004024000030061281200a00605c018000000000002702200002000cb99152d0f2f6554b43cb58d52d0f2f6154b43cb98552d0f2d6154b43cb18552d0f2f6054b43cb98152d0f2d6054b43cb18152d0f2d5214b43ab98b51d0ead62d4743cb54b51d0f2d5294743cb54951d0eae6214743ab58851d0f2d5214743ae98051d0eb96014743ab98b50d0ead62d4343cb54b50d0f2d5294343cb54950d0eae6214343ab58850d0f2d5214343ad98450d0eb56114343ab58b4390ece62d0e43b398b4350e6e62145439b5885150e7a60145439e5805150e6e62141439b5885050e7661141439d5845050eae62d4d43ab58b5350e9e62d4d43e398b5350e8e62d4d43e358b5350e9d61d4d43a75835350f2d5214943ab9885150ead6214543ae9805150eb96014543ab9885050ead6214143ad9845050eb56114143cb98a5410f2d6295043ab58b4310e3f6550c4397d954310f1e5450c43c799153d0b1d53d0f42c754e43d0b1e5350f42c754c43d0aad62d4f42c7d9553d0b1f6254f42c758953d0b1f6154f42c798553d0b1d6154f42c718553d0b1f6054f42c798153d0b1d6054f42c7181
  | 7 => 0x1d3872a8988013786308787b80280002586d0b484e9cd8531542560ae1960dda8d16502524790c9151ff8fb9cc9899a0063a4486010f9a503c0a60000e900029f00010e8d71498190d1a6b2592329359a1832270a14a2c0b29bc0c48b500d8c40b086a15b882a3218a00001697a87122300918b0540790572001c328c0ba89392227588a1b99c28f5077076279a772512629201529060fe07e105a8880016e8b215b00009b139000238204800022800246904a2400000012e13027daa5a698dc800018a7d2038001538001749bc819a619930000550ee99c1459f69e32811558000000f494e8e6143821a7789c909163800285a369bb1ed00028b9feaa929b06b03a028a138900000061190468001d82aa9110ab0f79ec886a08a7612295c0689c1a028bd8ea932a9e00000983489d2a425686e10e064144a8703111f12e8249e6891a718d092686d8e89a3aac883046066a1f0000e826c9cf2220e013ea950000d52948000408d307d25ea420002900750000ab9549351d30000b30682a30000000001368a3800208206a539b00000ef9000001dc0000000000000970000001a88af00ba678851798000cb97008b0ba0001238001041ce96100018b8000000002921c48bc1a99cc0fa1790748a401c8298002880001848e69eb127a4616598380000026500026316695f80026d9b70b41ec1b58002830b88b70e4873806a801e004209487a8e597403d9b1a9388c04c1b2a3f12a1afa8216480584900213ba6892400fa1c9c5a020232a71ac27e948250a2022e8cd0bb23194900120099a0c7aaba750d683b80020522d89fa8517185388b89a0318341e99751b824408d9512a50d408381f21310d8fd8c204f94a13327f0ad29a11b0e30f09ba8001d0a3d9c821780087c92d249aa290280000023e0950a126a22ca1900011e10a967aaa04880014780000027389592b9b08000000001292550000c600002b8002140ae8000000000d9a181aaa269ae24b80000002611611d80027b233a968001831870a2823a3b0bf9f800022d00005a91c9fa8ecaa099791490a0f38bf1d51860390e215f0001f9a6600025b2588fd0f920d89916e1a70001078de2379298998001de2ad88e2091f79b391e8371a20d88120dc22524ea4a2111f1a4f8cf0ac9c11cfa5195e17308401b814a849e91db87f1501012429f400023123426680008a80000017c92f07004815d92c83e1770000000d79f121f80018d9ba0ef1e88001ef03b0f101605214fa0a15706f1e10000d20000002700f896c02226e0718a09d210b239a0c95a100884a28259a839bfa941a08f582c9ae9fb14410390f1f727e00e81d14f0dd24b0f18608858018b5a71220838255a4a83088928e93ca6a9178aa00022e010181021042800216800199a9300019387404c9050e2956a621ee9d7996a1592
  | 8 => 0xc20648f81ca11319d0b98000d4a959672099a10000001f5260a3aa4d88984d000000075a7911817f25b8000f9a5299b0981531588d607ea6eaa784b80025c99297c1800002300b11c881b21195500880001a28b17b0ed96b92a8001ed80300d1578e994111b8001d884e1f4a8da570c015819016d9472492079690001aa25f1fb8d5a8a8d9097a8c9869888930001f02a000007d9ab29719821ea411520a49b48da854a5e14e11c06c9e218a96a2102ab00a8458f281729d160a1b05910213825d849a7ca451fd8c90559c70f023b8bd2ae15ea4001ea019e797d97680011994083001308880c09119fa9d9288b387994a96a81f91a07c25a21297b9560cb0ce85d0c518195922922999b80399e07f8000a811424c1e60000f621c22a280aa980006700029a8478df8000c39e0800221a1da418000c595a8000000002638b60001de8398001df9ca80000000000011680005191d03ea8a23ca818002af82f8c6aaf04f0111518ee02e8ce04120b06513d2271ee00486b97e8079be82790b8001852691f9159a2b80000000027c0000001739a60000fb0ec0001b6a9c0000002a10002989918000000a020f061a722358000c09311e51489778181119912991628500000000709388000001b881e0561bd00022b11580029123729802805e99099412f9d19b40001272501c500000009ba9613fa4ca5405d8908081a90a184a9e38001070001660001e19762531a49170e10000000c71821af1dc97f8e70448000cc1d70000780000c105998091a83fa8f0a727899da0e1e485a0961640eb1949188a90000000f32610c30860001c61d58000001dd81386c06f9248001418002580820001c994d1988ca97d0cca1d1360001fc92b0118de86600028627b89d9508128000000002520001430000b8130a8e00b2ad1d9800000170a8400026f00011380018f9d40c80969be0000679b78002248001f39ac9c40ff94280012080019917e0002a1a6ba4828f93c06216300021e07a1fe110057a010a518ca600b19b3248a0a9aba0e8ad84da1628786a8000509d68331a303f0201ea85e03685812504b0698ff069210841982a2f8050c1a459318000001a68000f68329e28001399f20a79ff09200007685f856a7305f010a548e403c9082059890d009e94c22620f9d1168a6413e08ca5d29ca2384721b8000f219707b1d00bba6c1338001920001b513b0a20000cf9da84a20700010180000000010c1fa00000002f0000d81b926fa0b88720600023080a0000000000c280000000003a8a89211c0a9b94b80016f0ed00023882b00000000000021980019ea6d1b100011225a8001ef80027f8db1da1780929450881d294b16fa2f0fe8000b682d86e98e0000b00940001f88290000359bba2aa9ea4f29780424d2289a82782351c01ad9fd00000023a0000bc8da
  | 9 => 0x264a7a18580009a8000be1882a8a25a670ea20313d8402470389e70af8fc0c88808d12331e809e13419f02a8e18e789f0e0a22877aa394c83381400026599517594d9699f0a1a85c02e1c91df0eba72909a7415c82680017118f0b782a0001eb9cd1a58000ac25f9729ea0c980023c0001468001d618792816b12196816007885296d00001d9d90000438000d38000001088001e5a120a69d4a43aa603d0db8002998f400008f0000df1a28e380025c00019a8faa1a0000b90612210721cb9cb134a3905b25782c00000f0be9c38fca188000378000000000000989420000158242a48ca18420c00001c19597223d2a800010300023f93708107311fa90800035020a9f80023600c9bd8000a5858a27aae8000a99e40001bf1ce0002409b2081aa218c0000002892431260270f72ac00010d11085b85100014008f96224e0cda0d1c6a91a3e93f00e1c78000151230361f60000001db282862a0405c88ea151788001a78179128000441f316c8aa88d26829282d0d299c94618eaa692c000043161906a7a93a2749f59ad17a1fc0a31b613223495d01a9dd00718d09c1259a4276a170450001f28e506593a9
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x9850e72d9543cc216b90c8a8c61325c86050d309a2e2302869850e72d95434c2c4b90c0a1a61645c46050d30c2a86b08a49852571149424c306b20a499261515c4524c93085aeda1aa41860d6394b420c306b1aa5a1061495cb4394430a2ae7a14a21852572d0d510c28ab9e84a8861465d7434c030b12e5a1a601870b43549300c389a1aa2980618358e6295320a2ae229a879050e7395142c8246b9ecaa1641439cf6550b2085ced29a85905257114d42c8306b20a699641515c4534cb2083ae6322a3105157114d4348264b98c0a1241385c46050920a1ce7b2a849042e7694d4248292b88a6a1241625cc6050920b42e2302849060d6414d32482a2b88a69924186195434c120c50caa126090648654c930482c4ba26498241075cf625502085ae4b2e861060e5358b4308306a9ac5a1841075ce649482083aed29e841041d7654f4208292b968728841455cf4294420a4ae5a1aa21051573d095108294bae8490041625cf4248020e12a7a124010723425452008216b94c929e21075ce6494b1085ae5324a70841d739925284217b92c7aa22107dcd62d5110c1ac7310a88860e635885444306b1ac42a2218558d6115110c4ac4b08a888619635805444314b12c02a2218c585601511085ae5324a68842d721974344216b90caa1a21071d95350d10a18e4a9a868841d73992524420eb98cba1221075cc6550910858eca92848850c735494244268b98c0a0a21385c86050510a28eaa1a62884b1741813144270b90c098a21491d54248510962e830242884d1731812144268b98c2a0221385c86150110a30eaa1a60884b1741853044270b90c2982214a1d54248110962e830a40884d1731852044216b96c6aa021075cf625501085ae5324a60850d729925304286b94c8a98210b5cb65d0c1085eeab16860860e5358b4304306a9ac5a1821075ce6494810a1ae7324a40842d76d0e5204286b9cc8a90210b5db435481083ae7b2e840841f7558f420420ebb4a7a1021075d953d0810c1ac7296840860d6354b42042c8b98c888021685c86444010aa2e7aa2200856172d511004298baca8880214c9d95444010a60ecaa22008533735511004299b92a8880214c5d35344010ac2e5a9a20085517594d1004388aa4a688021c49515344010e22a8a9a20087127454d1004388ba2a688021c4d915344010e20c8a9a200853175d0d1004388a9e8688021685cb4344010a62eaa1a20087115350d1004298ba6a488021545cf5244010ac2eb29220087215494910043a0a9ca488021c89515244010e42a8a9220087425354910043a0a9aa488021c89d15244010e42e8a922008723645491004390322a488021c8d0d5244010e4286a92200853175d0910042c8b9e8488021c454f4244010e42a5a122008531755091004388a9a8488021c85494244010
  | 1 => 0x510cb832a264a8865c15513254432a4ae5a1aa2195457290d510ca8bb9286a8865c19c94354432e0ae4a1aa21951573d09510caa2b9c84a8865c150e4254432e0c86a12a21970543509510ca93b9a84a8865c19cd4254432e0ae6a12a21951574cc9510cb82a1664a8865495d23254432e0a87192a219515744c9510cb83a1264a8865c15093254432a4ae8992a219707434c9510cb82a1a64a886551dd13254432e0ce8992a219545744c9510cb82ba264a8865415d13254432b12e8994a01971143546500cb90a12a328065d04c95194032a52e5a1ca01951973d0a500ca86ba264a806546dd54354032a56eaa12a019589744c9500cb852a264a8065c25513254032e228728aa01972142945500cba0994a2a8065c450d5154032e4284a8aa01974132545500ca94b9686a8065525ca4354032a36e4a1aa01970a7250d500cb84b9286a8065465cf4254032a92e7212a01970943909500cb8521a84a8065c250d4254032a56e6a12a01970a73509500cb84b9a84a8065465d33254032e1285992a019529748c9500cb84a1c64a8065465d13254032e1684992a019709424c9500ca94ba264a8065c2d0d3254032e1286992a01954b744c9500cb853a264a8065525d13254032e12e8992a019509744c9500ca86b94c8a98838354d62d0c4185aeda1ca420d0d73991521060ebb4a7a10838358d52d0841a52e5a1ca020d1973d0a5010694b9686a8083465cf4254041c1cc6b14a998d0e7295143cc646b96caa1e63439cb6550f3185ae4322a118cc572185434c668b80c2a1a63439cb6550d31b0ae430a8698d9170185434c70ca1ac0292634a5c05250931c1ac82926498d4970149324c616bb686a90638358e52d0831c1ac6a968418d1575d0d310c6c2b968698863c1d0d524c431a52e5a1ca018d1973d0a500c694b9686a8063465cf4254031e268698aa018e0d6398a54c868cb80a6a1e43439ce5450b2191ae7b2a8590d0e73d9542c86173b4a6a16434a5c05350b21c1ac829a6590d497014d32c860eb98c8a8443465c05350d2198ae630a8490ce170185424868739ecaa12430b9da5350921a52e029a8490d857318542486d0b80c2a124383590534c921a92e029a6490e146550d314871232a8498a4391195324c521b0ae89926290e0e5358b4308706a9ac5a1843075ce649482183aed29e8410c1d7654f4208692bae8490843615cf4248421e0aa7a124210d2972d0e500868cb9e85280434a5cb4354021a32e7a12a010f23424855008686b94c8a98818354d62d0c4085aeda1ca42050d73991521020ebb4a7a10818358d52d0840a4ae5a1ca22051573d0a5110292b9686a8881455cf4254440c1aa6b10822060d63548411030ab1aa220881895895110440c32a6b00822062952580411030731ac52a661439ca5450f3091ae5b2a87
  | 2 => 0xf4000003054000000444000007e000005cc0000000000000ac00000004180001400224000d000000c5591561f4001e92600000000004b0b9000293f400449334acb300000568000000000015330953cc6627cbc000ca518b60ec2200000310a8000000000c0004100000028801a40000000000230c49a238004156a09ca22280000000001484d4000000700000218000005d1f1180000017c644b8550011f0000000153000cd0e0000a000540000b8b8118704683615c000004516800000970000024000000000f49b0000e4c972000000014241c8200012000f602c4b33800300004852807000370000003a000b03e0fb38d6c24811000be2b4530016f598320f0d8410fc0d400000164517533c005785b55400000f20000028c00000000003f5dc48398a715800580215c094354000000000000000e800000000c348c590000054545000004f0ac000000dc992dcea170004bc6f1a0004f8f73840000000000000002d000521116550485000001e0d9000da19d62001172a4c951c652787f43800000000000000000000753f88d000a6101100015f0680200006000d2184185b8d70000022c0044c00001192c8004a8ed205680014d1ec0053000000334b4543c000550623bcbb28000000934ec0056c0034d4b258000000029000000000004a00000000885b40000000000004e1490015c490423a4e5511714e4f1000031e53021c6a479675d8f50bd780903e0511d4346d494bf000e4309631cc0000000000004dc005494331d0a46c00000001c4741d94a00116488981ad00408ba1353a02158025612ac5e42c8f4a4250c1092b8011804e10d36140d62742a2bcb4010008020000004002000080080006802000380500a000020000000000040040000800006010000080001000008020000200004038000080a018100180200000028020c0020000000800000000080c008060001a028000180e010120300004006000000080603804060100780c020020282005802000140000800838008160185000014010020000c04800038000080401004000020080a0000000019435cc6154b43c4ac230aa5a1d2a7018552d0e94b80c2a9687435cc6054b43a4ce2302a5a1d257118152d0f14b00c0a96878a54a6014743c52a4b00a3a1e255298450d0f12a92c228687435c86154f42c2ac230aa7a151a7018553d0a8cb80c2a9e85435c86054f42a2ce2302a7a15157118153d0b0cb00c0a9e858654e6014742c32a6b00a3a16155398450d0b0aa9ac22868543dd56250c32c1acaa1c841950d7598d420ca87baac6a106507dd5644c83285eeab22641948d74d95320ca86bacc89906543dd5644c83291eeab22641960f75591320ca46bb2a899065615d13294432a4ae5a1ca21951573d0a510ca86ba264a886545dd54354432a4eeaa12a219585744c9
  | 3 => 0x1d36d150006338800480df2c410470003e8cb5740f53c842f4e71c84f3e45101000000474f50c000000b00003400000d1285694200055d311306c0008c2a8d0000eb0000005c00000390001e31800001340010f5acee0001b49c0000019161594fc6e20c00098dd2d4e00000000013294ff40c000009c000ec001740000035049000de404c800020538910000007c7700
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1e0102a00006a8240048b2c4c0193018000020c000008470c0020d004c9001e145428200002000000a002e70e91004001f4e8c0000094380526d10000100018126080010008000c05735846154b43c21615c06154b43c09735806054b43c21715806054b43c05725846154f42c11615c06154f42c09725806054f42c11715806054f42b01844c95194032b01844ca5154032b01844c95154032c09645c0524c93190587d0d524c431b0182d0d3154031c09645c0534cb21c09645c0534c921c04655d1324c5219058754f4248421b0183d092154021c05645c4524c93090987d0d524c030b0182d0d514c030c05645c4534cb20c05645c4534c920c08655d1324c1209098754f4248020b0183d095148020905821d5434c510905831d54248510909821d5434c110909831d5424811092182dcd544401091183dc95444010b01829d15344010911871915344010b01821915344010d01535cb4344010b01839d15244010921871915244010b0183191524401092187d0d52440109118754f4244010d017354b4244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 884
  | 4 => 1376
  | 3 => 377
  | 2 => 43
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (27102+((h/294+packedAt s5K5 (23868+(h % 294)*11) 11) % 1283)*11) 11
  | 4 => packedAt s5K4 (57326+((h/458+packedAt s5K4 (52288+(h % 458)*11) 11) % 1652)*12) 12
  | 3 => packedAt s5K3 (19723+((h/125+packedAt s5K3 (18473+(h % 125)*10) 10) % 601)*10) 10
  | 2 => packedAt s5K2 (2678+((h/14+packedAt s5K2 (2580+(h % 14)*7) 7) % 68)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x77c3de7e7c7f1c63e3f311e3f1c71cf9c530cf
  | 1 => 0xbbfc1f9f9f8fe07c7c7c1e3c7e381f3e4ac333
  | 2 => 0x3cffe01fe00fff807f8fe03f803fe03fb30c3c
  | 3 => 0xc0ffffe0000fffff800fffc0003fffc03c0fc0
  | 4 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4202008100840400004090010408001045
  | 1 => 0x40404001201008080020420080810004112
  | 2 => 0xc1488148092448094015202904924025130428
  | 3 => 0x1e91080152489040092a5480092492802c0a80
  | 4 => 0xefe211515800da52524f99324d80c2853fa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8feeefee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x169118800e088900018981179d9a878b1613821311848a9b801f9d14008e94829904001c171e001f1e83059b050000000c0003901c99800820920d9a158d200f150b86128c9080068700000f80000a180e0108087020200601202c48700003041608000037fd500bfe5402df9500dfd5402ff1500b7c54037fd4c09fe53037f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52037f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd440d7f51017f9440dfd51005f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd400d7f5000ff9400dfd50005f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x224000bfd912006ffcc890016fe6448001feb224000bf5912006ff8c890016fc644801dffaa2400dff9512006efca89003bfd544801bfe2a2400ddf15120007fec690002ff6348019ff31a4004bf98d20007fac690002fd6348019fe31a4004bf18d20077fea690033fe534801dfea9a400cff14d2006ffe8690033fe4348001fea1a400cff10d2000dfec49000fff5248007ff2924003ff5492001ff8a49000fff4248007ff2124003fb9092001ffa8490003ed4248007fe2124003ffcc92001ffc649000fee3248007fe9924000fb4c92001ff86490003ff61480017fb0a400bff98520015fcc290003fd6148017fe30a4002bf18520077fea29003b7f5148017ff28a400eff54520006faa29002ffc514801bffa0a400bff90520007fa829002ffc4148019ff98a400bff8c520007fa629002ffc3148007ff90a4003fbc852001ffc429000ffd2148001f690a4003ff0852000dfec090007ff5048003bfa824001ff9412000ffaa0900077d5048003fe2824001ffd012000ffc8090007fd4048003fe2024001ffcc12000ffc6090007fa3048003fe9824000fe4c12000ff86090007ff2048007fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120057feca8802aff6544015ff32a2006bf99510056fcca8801a7e6544015feb2a200abf59510006faca880027d6544015fe32a2006bf19510007fec888002ff6444013ff3222005bf99110007fac888002fd6444013fe3222005bf19110057fea888027fe5444013bf2a2200aff5511004ff8a8880277c5444001ffb1a2000bfd8d10047fcc688012fe6344001feb1a2000bf58d10047f8c688012fc6344015ffa9a2008ff94d10057faa688023fc5344013ffa1a2008ff90d10007fa8688023fc4344001ffb122000bfd891003ffcc48800efe6244001feb122000bf5891003ff8c48800efc6244015ffa922007ff94910057faa48801ffc5244013ffa122007ff90910007fa848801ffc4244011ff9922007ff8c910007fa648801ffc32440037fb0a2002ffd4510016fea28800bfe5144005fea8a2002df54510017f8a28800bff4144005ff20a2002fd90510017fa8288003f54144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea0880077f5044003ff2822001ff5411000efaa088007fc5044003ffa022001ff9011000ff48088007fd4044001fca022001ff1011000ffe6088007fe3044003fd1822001ff4c110007f26088007fc3044003ff9022001ff8811000ff44088007fd2044001fc9022001ff0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0xafe6550027feb2a8013bf5954009ff8caa001afc6550027be32a80069f1954000dfec8a0017ff545000bff2a28005df9514002ffaa8a0017fc545000bbe2a28000ffd8d40005fec6a005bfe63500097f31a8000ff58d400b7f8c6a0012fc6350027ffa9a8016ff94d4009ffaa6a005bfc535000bffa1a8005efd0d4002ffc86a0017fd4350001dea1a8005ff10d40007fec4a0002ff625002bff3128003bf98940007fac4a0057fc62500077e3128013ffd49400affca4a004ffd525002bfe2928005ffd094002f7e84a0017fe425000bfea128000ef5094002ff884a005bff325002bff1928000ff4c9400aff864a0003ff61500017fb0a8014ff98540015fcc2a0003fd6150029fe30a8002bf1854009ffea2a004f7f5150029ff28a8013ff54540006faa2a0053fc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400b7fe62a0053fe3150001fe98a8014ff0c5400affe42a0053fe2150001fe90a8014ff0854000dfec0a0007ff5050003bfa828001ff9414000ff4a0a0007fd5050003bea828013fe54140006f2a0a0007fc5050003ffa028005fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001ff0c14000ffe40a0007fe2050003fe1028001ffc414000ffc20a0007fa1050003fe0828012ffd9530095feca9804bfe654c00d7f32a6012ff59530095faca9804bfc654c00d7e32a6000ffd9130005fec898047fe644c00b7f3226000ff59130005fac898047fc644c00b7e3226012ffd513008ffca8980477e544c025feaa26011ff1513008ef8a898006ff634c009ffa9a6004ff94d30027faa698013fc534c009ffa1a6004ff90d30027bc8698013fd434c001eea1a6004ff10d30007fec498002ff624c021ff3126003bf98930007fac498043fc624c0077e3126012ffd4930087fca49804bfd524c021fe2926011ffd0930087fc8498003fd424c021fe2126004ffcc930027be6498013fe324c009fe9926000f74c930027f86498003ff614c0017fb0a600fff98530015fcc298003fd614c01ffe30a6002bf18530097fea29804b7f514c01fff28a6012ff54530006faa29803ffc514c023ffa0a600fff90530007fa829803ffc414c009ff98a6004f7cc530027fc6298013fd314c001ee98a6004ff0c530087fe429803ffe214c001fe90a600fff0853000dfec098007ff504c003bfa826001ff9413000ffaa0980077d504c003fe2826001ffd013000ffc8098007fd404c003fe2026001ffcc130027f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff44098007fc204c003ff8826001ff8413000ff42098007fc104c01dffb2a400ebfd9520077fcca9001afe654801dfeb2a400ebf59520077f8ca9001afc6548001ffb
  | 2 => 0x31027fc6498813fd324c401ee9926204ff0c931015fec29880bff514c405bfa8a6202ff94531017faa29880b7d514c405fe28a6202ffd0531017fc829880bfd414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017ec429880bfc214c401ffb026200bfd81310fffcc098806fe604c401feb02621fff1813100df8c09888bff504c445bfa82621fff94131117faa09887ffc504c443ffa02621fff901310fff88098813ff304c409ef9826204ff8c131027f86098883ff204c43fff102621fff08131017fe209880bf7104c405ff0826202ff041310f7feca9087aff654843dff32a4206bf995210f7faca9087afd654843dfe32a4206bf19521007fec890802ff644843bff3224205bf99121007fac890802fd644843bfe3224205bf191210f7fea890877fe544843bbf2a2421eff551210eff8a8908777c5448401ffb1a4200bfd8d210e7fcc690812fe6348401feb1a4200bf58d210e7f8c690812fc634843dffa9a421cff94d210f7faa690873fc534843bffa1a421cff90d21007fa8690873fc43484057fb124203ffd492101ffca49080ffd5248407fe2924203ffd092101ffc849080fee4248407fea124200fb5092101ff8849080fff3248407ff1924203fb8c92101ffa6490803ed3248407fe1924202bfd8521017fea29080b7f5148405ff28a4202ff54521016faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017ec629080bfd3148401fa98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421edfd41210dffca09087bfd5048437fe282421dffd01210dffc809086ffc4048439ff982421bff8c1210dff8609080fff2048407f79024203ff8812101ff8409080bff1048405fb8824202ff84121017f820908037f6454035bf322a0059f99150006fac8a806b7c645400b3e322a000dfd8d500cefcc6a80037d6354033be31aa01adfd0d500cefc86a80037d4354033be21aa000dfd89500c6fcc4a80037d6254031be312a01adfd09500c6fc84a80037d4254031be212a019dfcc9500c6fc64a80037d3254031be192a000dfd8550004fec2a805f7e6154001beb0aa017df185500d6fe82a805f7e4154001bea0aa017df105500cefe62a805f7e3154001be98aa017df0c5500c6fe42a805f7e2154001be90aa017df0855000efec0a80067f605400dbdb02a001dfd015000efc80a80077a4054003be202a001dfcc15000efc60a80077c3054003bf902a001df8815000ef840a80077f1054003bf082a001df0415009ffecaa004eff6550001bfb2a80009fd954009ffccaa001
  | 3 => 0xf9826404ff8c132027f8609900fff204c807f79026403ff8813201ff840990b3ff104c857ff082642bff04132006fec8a88ab7e645440b3f322a200df59151156f8c8a88167c6454401bfb1aa229df98d51006fac6a88a77c6354455bfa1aa229df90d51006fa86a88a77c4354401bfb12a228df98951006fac4a88a37c6254455bfa12a228df90951006fa84a88a37c4254453bf992a228df8c951006fa64a88a37c3254405bfb0aa2029fd8551036eec2a880b7f4154405bf20aa202dd90551016f882a880b7f3154405bf18aa202df0c551016fe42a880b7e2154405be10aa200dfd8151004fec0a889f7e6054401beb02a227df18151156fe80a889f7e405444fbe202a229dfcc15113efc60a889f7c3054451bf902a227df8815113ef840a880b7f1054405bf082a202df04151137fecaa089aff6550401bfb2a82009fd9541137fccaa081afe655044dfeb2a8226bf59541137f8caa081afc655044dbe32a82069f19541015fec8a0817ff545040bff2a28205df9514102ffaa8a0817fc545040bbe2a28200ffd8d41005fec6a0897fe63504097f31a8200ff58d4112ff8c6a0812fc635044dffa9a8225ff94d41137faa6a0897fc535040bffa1a8205efd0d4102ffc86a0817fd4350401dea1a8205ff10d41007fec4a0802ff6250449ff3128203bf98941007fac4a0893fc62504077e3128226ffd4941127fca4a089bfd5250449fe2928205ffd094102f7e84a0817fe425040bfea128200ef5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202dfd4541017fca2a080bf65150405fea8a8202df54541137eaa2a0803755150405fe28a8202ffd054102fee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff98a8202ff8c541017f862a080bff2150405ff10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd4141136fea0a088ffe505044dfea828223ff1414102ffe80a0817bf405040bff2028205ff1014112ffe60a088ffe3050447fe1828224ffc814111ffc40a088ffc2050405ff8828202fdc4141017fc20a080bfc1050445ffb2a6222bfd9531117fcca9881afe654c445feb2a6222bf59531117f8ca9881afc654c401ffb226200bfd913110ffcc898816fe644c401feb226200bf5913110ff8c898816fc644c445ffaa26221ff9513110efca89888bfd544c443fe2a26221df15131015fec698813ff534c409ff29a6204ff54d31027f8a698813ff434c409ff21a6204f790d31027fa8698803dd434c409fe21a6200ffd8931005fec498883fe624c4077f3126200ff58931107f8c49880efc624c445ffa926220ff94931117faa498883fc524c443ffa126220ff90931007fa8498883fc424c409ff9926204f7cc9
  | 4 => 0x8d3fc2150c01ffb028600bfd814319ffcc0a1806fe6050c01feb028633ff1814300df8c0a18dbff5050c6dbfa828633ff941431b7faa0a18cffc5050c0bffa028605efd014302ffc80a1817fc4050c09ff9828604f7cc143027fc60a1813fc3050c6bff9028633ff8814319ff840a18d3ff1050c67ff0828633ff04143197fecaa10caff6550801bfb2a84009fd9542197fccaa101afe6550865feb2a8432bf59542197f8caa101afc6550865be32a84069f1954201dfec8a1017ff5450865dfaa28405ff9514202efca8a1017fd545080bfe2a28405df1514202f78a8a10173c5450801ffb1a8400bfd8d4218ffcc6a1012fe6350801feb1a8431ff18d42025f8c6a10cbff5350863ff29a8432ff54d4218ff8a6a1017ff435080bdfa1a8405ff90d4202ffa86a1003bd435080bfe21a8403bfd894201ffea4a100ffe5250807f72928403ff54942197daa4a100ffc5250807ffa128405fbd094201ffc84a100fbe4250807fe2128403ef1094201fd884a100fff3250863f79928403ff8c94201ff864a100fec3250801ffb0a8400bfd8542187fcc2a100afe6150801feb0a8430ff18542015f8c2a10cbff5150865bfa8a8430ff94542197faa2a10c3fc515080bffa0a8405efd054202ffc82a1017fc4150863ff98a8430ff8c542187f862a100fff2150807f790a8403ff8854201ff842a1003ff60508017fb02842fff9814200dfcc0a1003fd605085ffe3028401bf18142197fea0a10cb7f505085fff2828432ff5414217ff8a0a1017ff405080bdfa028405ff9014202ff880a10c7ff305085fff182842fff0c14201ffe40a100fef2050807ff1028403ff08142187fe20a10bffe105085ffe082842effd9532175feca990bbfe654c80d7f32a642eff59532175faca990bbfc654c80d7e32a6400ffd9132005fec8990b7fe644c80b7f3226400ff59132005fac8990b7fc644c80b7e322642effd513216ffca8990b77e544c85dfeaa2642dff1513216ef8a89900eff634c809ffa9a6404ff94d32027faa699013fc534c809ffa1a6404ff90d32027fa8699013fc434c8077fb126403ffd493201ffca49900ffd524c807fe2926403ffd093201ffc849900ffd424c807fe2126403ffcc932027de649900ffe324c807ef1926403ff0c93201fb8649900fec324c807e61926400ffd8532005fec2990b3fe614c8057f30a6400ff58532167f8c29900afc614c85dffa8a642edfd4532167fca2990bbfd514c859fe28a642dffd0532167fc82990b3fc414c809ff98a6404f7cc532027fc6299013fc314c807ff90a6403fbc853201ffc429900ffc214c801ffb026400bfd813215ffcc099006fe604c801feb02642bff1813200df8c0990bbff504c85dbfa82642bff94132177faa0990affc504c85bffa02642bff9013215ff88099013ff304c809e
  | 5 => 0x8d01c780019a8308111fe00a80010614399d07b1bc9a918b8151421c112d8810539510920678d69ee0990bb1ab8d407a10aa1b80014899a0d1000172a468001821890fc16fa2695682993da06169922834a420c21449d49d10002029c99ce00000b00013e845812a3f0b61ca01024f22915700003202797d00180000e014028070020000100000c0040280000a0180600000c01802001006008028000000080200200e00000804026008000050020140200a00a00c060030040080000801e01400014000000068080000000080102a054018020000040780000401401800002038000000040000080901e0080100000a000020060000000000b018018010060040a00381a00e0a40180200202801006000000078010000300280002000003004016038020050020180400200200c0200100202c0280000c0100000001403008002002000008020000000180b00201c000000080000500c0000c41000300401800803000000020020040080501700c0040000300801c01009000004058010060300100000002802801006008088010020580081002001801004002004000040080a003800042008060010000041000100e0080280003400c0100000a018000050000680c02401a0000980301e00002800000000000150020001300100e004008000080500100100c0000680300e0280d00a0000080401401c0000082d0000140001300a0240000400200c0280300000c0000100002c0100100c02003806000000000030280000000600001c00000000070000000020040501002000c010000080040000101e040000000020080d80000200004003000014018060040380180a0060080880b00801c01011002084048000020040000000000000002002060008010160000800500a0000181a0060000000901c00c0d80002836ffd95431b5fecaa18037f6550c013fb2a8636ff99543035fccaa18dbfd6550c6d7eb2a8636ff19543035f8caa18db7c6550c0d3e32a8604bfd914302ffea8a18dbbf5450c0bff2a28605df9514302ffaa8a1817fc5450c0bbe2a28605ef1514302e78a8a1812ff6350c09ffa9a8604ff94d43027bca6a1813fd5350c6deea9a8604ff14d43027fe86a1817df4350c09ff21a8604ef90d43027f886a1813bc4350c09ee21a8600ffd8943005fec4a18d7fe6250c077f3128600ff589431aff8c4a180efc6250c6dffa928635ff949431b7faa4a18d7fc5250c0bffa128605efd094302ffc84a1817fc4250c09ff9928604ff8c9431afbc64a1813fc3250c09ee1928600ffd8543005fec2a18d3fe6150c057f30a8600ff585431a7f8c2a180afc6150c6dffa8a8636dfd45431a7fca2a18dbfd5150c69fe28a8605ffd054302f7e82a1817fe4150c0bfe20a8604ffcc543027be62a1813fe3150c09fe18a8635ffc85431a7fc42a1
  | 6 => 0x3e1a401705b00007780016d89c8001518ee80003c9550000961b80df8b01f19b01191368002170ab8001ba2438001cc98c95f00023e9dd9a595d22880f0000000001390001b08e580000000002c8000000bb8000dc0f5000212a2d133a4a83f146115a1e8b09c20579f503d1b102a84187193c0000001f322b90385b9070cb0001c192393f89512f03c22280000000003f9ba97580014718d1009708d38c48e285e843026a2f89b1398078be8789bd18a0520511cb142a338000a22360481ec8001af1c814f9b700209d8c892408580014d2390ed0f49258b803a990979987a2a8001ef0a49180000bf0010a30e608000024c18b11200020d14c12b8ba0cf9268081f29bd91606fa3b240a3024f8401f10000cd901043a1682f22c9a50178ce8291720c79a986a0f180007380015b8000000001d50000000d087700010e99623808d1d28001040000002418000000000002260000000108000ea0d48000da80000000000000006b12d0001901ad9148000e711895800006c02c02d8ce0750b88000de8000000f798688d87417d87814000011c99e8ec16720a94e8730008469dd1558d221609116593710e16880023f8002440001d980020b88712e0028f803da1203591518098e1650938ee07580405088815300002612011101d16607e0c30070000000b50000001d792a1f39839788b997a8018c41b216d01f9779ff047920a3da2c206a251d41c39a38948ea9bb03a15b0220000000518e680017000001a8ad8198000f680000e8059632198dc85a87605e00000000000000889f9b40398d907911f14e1431791870a19171e6167a499fc1692210f124b10f0000000000001220001610000fa9929e80ef8c18a28e78eba3a9ff8ca1d18aea4e80906998f00614c9e70af0001ea0001419dc8000000000000988000000001090311e6a1483b85400000000010d20712c00002d0001609d39620d70fb90695621923408c9f91c58d587c9491109f99179d09de9ee80000000018fa470000749e00628000000c00030b784b9fb96c0e48000450001860868001649668001e495e22a0351d2000000138141178060a5005d23b80d01c8440000001298000000710000000000000002118001fd8000d50001e887d92f85c1ad0878001ea8038000001078191ca83299584aa1400016c8f88b490311e22200009300017a0390000000908dd0122248e98000001830001e28fb15400008f8550000cb8471bc0f01b8a3480e17f8d28000690000000fd13501a0000000979458218000001a2a449278001fe80000000000000016f1fd0cc00013881f0a405c90d85f94a89f12484e0001b1a3284b00000000009d1ed86f2058000000000001920000001c603b2018000799c09480001e7a4024d9f894b98e8ef1e40000000000000001b923e05a00014f09b80019b
  | 7 => 0x724ca0d97f0000a601191a20f8ae12c8b405985290b9d719b01805622e9da0fca3a22415fa2f07b8000898f095d80015c86680000b8001a70e18e09c001e80005d8000000e00e317c9310000000000cc9c68a70f304d23317b00000002b8000ab0000342009bf064a2700003306121305721a85316aa460ac91e93781c21e0388002080000d88000ff87f9508fe082a1f84f06e9168000001019cd20f1f6248a03800000000000000000000000000152a4e00c11a8fd8000619750000000000959ab025a0ea429de0001859302010001c280000000000011d95a8fe9131988001140241058768e21c41991940e39e58860580000001408002201521681d621a1bb9cb8b11718b208404d9770aa00007c00008e1fb0000a80000002230000000bc80006021d06300000015986d96ba158000000188068001b580010000000022e1dc08f231a238000001021ec0888f588b80c93a9df9cc0001c49290490001ce97e9e90000140b317b8928bd80004e9590239d688213c8589a323d1af9828a59a01601f80c923999e0891ac80003681e0c58ed97380000001b0000000000000000000e109a0671a780017c08500002b23703800000002100000000006a9fc9898138001978baa1084c0a69760000000001be98505f12310489a9640002459e981b9889819cf8379f78d98d80280ff21887018a912a02044a4d00024800001680010a0f60000251da9ed0000720000000f28db0000002100000000001fa16388308a91d0000000288001251710001ac0002280d1a001981a486510515a0df1ae945068898113a432299579618a109c12b1262050b715384ca2782e9e38cf18818c0c80ad1199a21aa8000499a60b19f58c119380000001480023880000022080000000013f16e0001fa87f0b580008482700000020a09682302a08e9f70a780010c0000c60ca800048a181629db97480017e0001db2090001a88001a08001d91288558000001cd80010f8d30b280020b0000000360d78e91a186b80000f8000a00160f40000f70660e401d99f0c71cf0f9a478001c313424b86c993131a3786393294a0000940b69359218b906400019713d1a815006e0fa07a9f085683714d90c95e93218422b11c24a00016a18da358319b2a089df11f8cd0421029848000c500000000000020ca3c000146a2594780013313a0000000a51b391b24513e1e19e51b789e022a36a0300a0001d01b98000da1b69a119c8001911349a68eb1309f68819ef8f38428048000000e882e0bf8001d31f21b60000de10802f99f8001731f01e080023086808a00004f9c8a179280000000620000001d59360001c906d0001768f20af9be00015c0002411e31aa2150130a083e8051969bf91ba219499b30000db9100c284a0e522d9089eb8bc0f907e96b0000001f480000020785488b0
  | 8 => 0x12e9c502087087283380990980021113b8001801b50000a900007d0000408000000000002040d612a80009e80000020e000191a139c71998000eca310001949d800019519c10b00023c80000000005921b00019d9e20000659548000a989180008398123200d8248aa8c09588b38809d89b48c38ac0000e800003004117420c05021da1c88c1270dd94b111a3500021f1210c68c98a8899a0996e8be0461f40901e11ae2490158200a3a1c20494413b0bd1eb09
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x704c51000df0704c510016f7604c510017f3604c5100ff77504c5100ff75504c5100fff2404c5100ffd7304c5100fff2304c5100ffd5304c5100fff2204c51000df4764851001ef4764851000cf476485101ef766548510007756548510005f77448510005f574485101e77654485101e7745448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003fe64248510007e5424851003fe63248510007e53248510007f3704851000df6704851000df470485100dff0704851000df07048510016f76048510017f360485100df7750485100df7550485100dff240485100dff230485100dfe720485100dff220485100dfe52048510015f8765011002ef87650110014f876501100077b75501101df7875501101defb65501101df7a65501101def9655011000779655011000679655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011004f7a545011004f785450110005fb735011004fbb4350110007b94350110005fb725011004fbb4250110007b94250110007f37150110015fa7150110015f871501100a7f07150110015f0715011000efb615011000ff361501100a77b51501100a77951501100a7bb41501100a7f241501100a7b9415011004ff14150110007b141501100a7f23150110007f131501100a7f22150110007f12150110015f8764c110026f8764c110014f8764c1101d77a654c11000779654c110005fb744c110005f9744c1101cf7a544c1101cf78544c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110047da434c110007d9434c110005fb724c110006fb624c110006f9624c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c110015f0714c11000efb614c11000ff3614c11007f7b514c11007f79514c11007ff2414c110007f1414c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110015f8764811001ef87648110014f876481101c77a6548110007796548110005fb7448110005f974481101bf7a54481101bf785448110005fb7348110005f97348110006fb6348110006f9634811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003fea4248110007e9424811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff07148110015f0714811000efb614811000ff3614811005f7b514811005f79514811005ff24148110007f1414811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x8910217f010d8910004ff75d8910034fe75d89100067e75d89100347e75d8910004fd75d89100067d75d89100047d75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d89100067e54d89100067c54d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d8910006ef32d891003eec32d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102267f51d89102267d51d8910226f631d8910226ef21d8910226ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d89102167f50d89102167d50d8910216fa30d8910216ef20d8910216ed20d891001cff76589100067e65589100067d6558910005df7358910045dc735891003eec625891020df7715891021dfb70589100dff01058910004ff7558910034fe7558910004fd7558910034fc7558910004ff745891002cfe745891002cfc74589100067e54589100067c5458910004ff7358910006df7358910004df7358910024fe7358910024fc7358910006dc7358910024dc7358910214ff7258910006ef725891003eee425891003eee325891020cff7158910006f7715891005e7f515891005e7d515891005ef631589100dcff7058910006fb70589100de7f50589100de7d50589100defa3058910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100557c75509101967e65509100067d655091002ebe6450910006bd645091004f3c545091001eee6250910006ed6250910015f6715091000dfa705091017ff01050910004ff764c910004fe764c910004fd764c910004fc764c9101767e654c9100067d654c910026de634c910006dd634c91001eee624c910006ed624c91003fcc324c910015f6714c91000dfa704c91015ff0104c91000df4765051002ef4765051000cf47650510007777550510207747550510206f76550510207766550510206f56550510007756550510006756550510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb4645051004f76545051004f745450510005f7735051004fb74350510007b54350510005f7725051004fb74250510007b54250510007f3705051000df6705051000df4705051011ff0705051000df07050510016f76050510017f3605051011f77505051011f75505051011fb7405051011ff2405051011fb5405051011ff2305051011ff2205051000df4764c510026f4764c51000cf4764c5101ff76654c51000775654c510005f7744c510005f5744c5101f776544c5101f774544c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6434c510007d5434c510005f7724c510006f7624c510006f5624c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff
  | 2 => 0x34fc75d911011cfd74d9110006bf54d911004e7e54d911004e7c54d911004ebc54d911004e3c54d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102667f51d91102667d51d9110266bf41d9110266bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102567f50d91102567d50d9110256bf40d9110256bd40d911002cff76591100057f75591100557c75591100067e65591100067d655911004ebc645911024df7715911025dfb705911011ff01059110004ff75591100067f75591100047f7559110034fe7559110004fd7559110034fc75591100067c75591100347c7559110254ff7459110006bf745911004e7e545911004e7c5459110004ff7359110024fe7359110024fc735911004ebf4359110004ff725911001cfe725911001cfc725911004ebf425911024cff7159110006f771591100a67f51591100a67d515911011cff7059110006fb705911011e7f505911011e7d5059110024fe76d8d100557e75d8d100057d75d8d100067e65d8d100067d65d8d10046de63d8d10237f010d8d10004ff75d8d10034fe75d8d100067e75d8d100347e75d8d10004fd75d8d100067d75d8d100047d75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100067e54d8d100067c54d8d100fcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d10006de32d8d10046dc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d102467f51d8d102467d51d8d10246df31d8d10246dd31d8d10246f621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d102367f50d8d102367d50d8d10236df30d8d10236dd30d8d10236fa20d8d10024ff7658d100067e6558d100067d6558d10046dc6358d10005ef7258d1003dec7258d1022df77158d1023dfb7058d100fff01058d10004ff7558d10034fe7558d10004fd7558d10034fc7558d10004ff7458d1002cfe7458d1002cfc7458d100067e5458d100067c5458d10234ff7358d10006df7358d10046de4358d10004ff7258d10006ef7258d10004ef7258d1001cfe7258d1001cfc7258d10006ec7258d1001cec7258d10046df3258d1022cff7158d10006f77158d1007e7f5158d1007e7d5158d1007ef62158d100fcff7058d10006fb7058d100fe7f5058d100fe7d5058d100fefa2058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d101b67e6550d100067d6550d1002ebe6450d10006bd6450d1004f3c5450d10026de6350d10006dd6350d10015f67150d1000dfa7050d1019ff01050d1001cfe76d89100557e75d89100057d75d89100067e65d89100067d65d891003eee62d
  | 3 => 0xf6448520006ed644852028f6e544852028f6c5448520005ef7348520005ed7348520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe4614852005f6f514852005f6d514852005fe63148520007e53148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200df6f50485200df6d50485200dfea30485200dfe710485200dfea104852001df8764c120026f8764c12001cf8764c1202877a544c12028778544c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120067da434c120007d9434c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c120087ea424c120007e9424c120087db324c120087ea324c120087d9324c120067e9324c120007c9324c120005fb714c120006fb614c12027f7b514c12000779514c120067db314c120007d9314c120087eb214c120007e9214c12026d7f76595100567f76595100347f76595100073f745951004d7e745951004d7c74595100073c745951004d3c74595100067e64595100067c64595100067e63595100067c63595100067e62595100067c625951026d7f715951000777715951026d7771595100bf7641595100bf7631595100bf76215951013d7f70595100077b70595102757b705951013f7a405951013f7a305951013f7a20595100bf7b105951013f76105951013f74105951013f78105951013f7010595100067f74595100063f74595100067e745951002c7e74595100067d74595100067c745951002c7c74595100063c745951002c3c74595100067f73595100067e73595100067d73595100067c73595100067f43595100067e43595100067c43595100067f72595100067e72595100067d72595100067c72595100067f42595100067e42595100067c42595100067f32595100067e32595100067c32595100be7f715951026c7f71595100067771595100be7f41595100be7e41595100be7641595100be7d41595100be7c41595100be7f31595100be7e31595100be7d31595100be7c31595100be7f21595100be7e21595100be7d21595100be7c215951013e7f705951013c7f70595100067b705951013e7f405951013e7e405951013e7a405951013e7d405951013e7c405951013e7f305951013e7e305951013e7d305951013e7c305951013e7f205951013e7e205951013e7d205951013e7c205951013e7f105951013e7e105951013e7d105951013e7c105951002cfe76d91100557e75d91100057d75d91100067e65d91100067d65d911004ebe64d911004f3c54d9110257f010d9110004ff75d9110034fe75d91100067e75d91100347e75d9110004fd75d91100067d75d91100047d75d9110
  | 4 => 0xd20004fc7650d200057f7550d200757c7550d2002ebe6450d20006bd6450d2006f3c5450d20006df6350d20026dc6350d2001dee7250d201afce3250d2000dec765092002eec765092000cec76509200076f75509202b76c75509202b6ef65509202b6ed655092001def745092001faf7450920007af645092002eee645092002eec645092006fac64509202b7af545092006f6e545092006f6c545092006fac545092006f2c5450920005ef735092018eee635092018eec635092006faf4350920007ad4350920005ef71509202b76f515092006faf4150920007eb705092000dee705092000dec705092017fe8705092000de8705092001eef605092001feb605092017f6f505092017f6d505092017faf405092017fad405092017fea305092017fea105092000dec764c920026ec764c92000cec764c920005ef744c920005ed744c9202af6e544c9202af6c544c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920026cc634c920005ef714c9202a76f514c920067cf314c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015f6f504c92015f6d504c92015fcf304c92015fea304c92015fcd304c92015fea104c920014fe76d852005ef661d8520004ff75d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d85200067e54d85200067c54d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852029eee42d8520006ed42d852029eee32d8520006ed32d852005e7f51d852005ef621d852029ef521d852000cfe70d852001cfd70d852000cfc70d852020e7f50d852020e7d50d852020efa30d852020ef710d8520005df7358520065dc735852005ef46158520295fb70585200067f76545200067e76545200067d76545200067c765452006d7e745452006d7c74545200067f64545201567e64545200067d64545201567c64545200067f635452014e7e63545200067d635452014e7c635452013e7f62545201476e42545200076d42545201476e32545200076d325452026d7f715452007777715452005e7f61545200167e61545200167c615452005f76415452005f6f215452013d7f705452013e7f605452013f7a30545201477b205452013f6e205452013f6c205452013f78205452013f7a1054520004ff7650520004fe7650520004fc76505200057f75505200757c755052002ebe6450520006bd645052001dee7250520007ad4250520007755150520004ff764c520004fe764c520004fc764c520026de634c520006dd634c52001dee724c520007cd324c520016f6614c52000dfa704c52000dec7648520016ec764852000cec7648520005ef7448520005ed7448520006e
  | 5 => 0x6df644c530006dd644c5302ff5e544c5302ff5c544c530005df724c530006df624c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007f5f514c53007f5d514c53007fd6214c530007db704c53000dde704c53000ddc704c5300ffd8704c530026df604c530027db604c5300ff5f504c5300ff5d504c5300ffda204c5300ffd7104c5300ffda104c530004ff7648530004fe7648530004fc7648530025de7348530005dd734853001eee6248530007cd3248530016f66148530007d5314853000dfa704853002cfe76d91200757e75d91200057d75d912006ebe64d9120004ff75d9120034fe75d91200067e75d91200347e75d9120004fd75d91200067d75d91200047d75d9120034fc75d912017cfd74d912006e7e54d912006e7c54d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d91202f6bf42d91202f6bd42d9120014fe71d9120004fd71d9120014fc71d91200067f51d91202f6ef21d912001cff70d912001cfd70d91202e67f50d91202e67d50d91202e6bf40d91202e6bd40d91202e6fa10d912002cff76591200057f75591200757c755912006ebc64591202ddef72591202edfb7059120004ff75591200067f75591200047f7559120034fe7559120004fd7559120034fc75591200067c75591200347c75591202e4ff7459120006bf745912006e7e545912006e7c5459120004ff7359120024fe7359120024fc735912006ebf43591202dcff7259120006ef7259120004ff7159120014fe7159120014fc71591200067f515912006ebf41591200aeef215912017cff7059120006fb705912017e7f505912017e7d505912017efa1059120024fe76d8d20066de63d8d20004ff75d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d200067e54d8d200067c54d8d2015cfd73d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202d6df32d8d202d6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d200067f51d8d20006de31d8d20066dc31d8d202d6ef21d8d2001cff70d8d2001cfd70d8d202c67f50d8d202c67d50d8d202c6df30d8d202c6dd30d8d202c6fa10d8d20024ff7658d20066dc6358d202bdef7258d202cdfb7058d20004ff7558d20034fe7558d20004fd7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d200067e5458d200067c5458d202c4ff7358d20006df7358d202bcff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d200067f5158d20066df3158d20086ef2158d2015cff7058d20006fb7058d2015e7f5058d2015e7d5058d2015efa1058d20004ff7650d20004fe7650d20004fd765
  | 6 => 0xf7250d301aede6250d301aedc6250d3008f9f4250d30005df7150d303375f5150d3008f9f4150d30007db7050d3000dde7050d3000ddc7050d3019fd87050d3000dd87050d30026df6050d30027db6050d3019f5f5050d3019f5d5050d3019f9f4050d3019f9d4050d3019fda2050d3019fda1050d3001cfe76d8930086ee62d8930004ff75d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d89300067e54d89300067c54d893000cfd73d893001cfc73d8930086ee42d8930086ee32d893032eed32d8930014fe71d8930004fd71d8930014fc71d89300067f51d893032edf31d8930006ee21d8930086ec21d8930024fd70d89302be7f50d89302be7d50d89302beef20d89302befa10d8930086ec6258930325fb7058930004ff7650930004fe7650930004fc76509300057f75509300957c755093002ebe6450930006bd645093008f3c5450930025de73509300079d4350930006ef625093001eec625093018fcf325093000ddc764c93001edc764c93000cdc764c930005df744c930005dd744c93031f5e544c93031f5c544c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c93001ecc624c930005df714c9303175f514c930087cf214c930007db704c93000dde704c93000ddc704c93015fd8704c930026df604c930027db604c93015f5f504c93015f5d504c93015fcf204c93015fda204c93015fda104c930014fe76d853007ef661d8530004ff75d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d85300067e54d85300067c54d853000cfd73d8530014fc73d853030ede43d8530006dd43d853001cfe72d8530004fd72d853001cfc72d853030edf32d8530006dd32d853007e7f51d853007ef631d853030ef531d8530024fd70d853022e7f50d853022e7d50d853022efa20d853022ef710d8530005ef7258530085ec725853007ef46158530305fb70585300067f76545300067e76545300067d76545300067c765453008d7e745453008d7c74545300067f64545301567e64545300067d64545301567c645453013e7f635453014f5e43545300075d43545300067f62545301467e62545301467c625453014f5f32545300075d325453026d7f715453009777715453007e7f61545300167e61545300167c615453007f76415453007f5f315453013d7f705453013e7f605453014f7b305453013f5e305453013f5c305453013f78305453013f7a205453013f7a1054530004ff7650530004fe7650530004fc76505300057f75505300957c755053002ebe6450530006bd6450530025de73505300079d435053000775515053000ddc764c530016dc764c53000cdc764c530005df744c530005dd744c530
  | 7 => 0xc540004ff7648540004fe7648540004fc76485400067f65485400f67c654854002dbe7448540005bd744854001eee6248540007ad424854009f7b76541400367b76541400d778765414002d78765414003678765414002c7876541400d77b74541400073b74541400d77a745414002d7a74541400d77974541400d778745414002d7874541400d738745414000f7b645414000e7b645414000f3b64541400077b735414036f7a735414000779735414036f7873541400077b635414036f7a635414000779635414036f7863541400d77b43541400d73b43541400d77a43541400d77943541400073943541400d77843541400077b72541403677a72541400077972541403677872541400077b62541403677a62541400077962541403677862541400d77b42541400d73b42541400d77a42541400d77942541400073942541400d778425414036f7b32541403677a32541400077932541403677832541400077b71541400057b715414035f7a715414000779715414035f7871541400077b615414035f7a615414000779615414035f7861541400d77b41541400d73b41541400d77a41541400d77941541400073941541400d778415414036f7b315414035f7a315414000779315414035f7831541403677b215414035f7a215414000779215414035f78215414002cfe76d91300957e75d91300057d75d913008ebe64d9130004ff75d9130034fe75d91300067e75d91300347e75d9130004fd75d91300067d75d91300047d75d9130034fc75d913019cfd74d913008e7e54d913008e7c54d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130356bf43d9130356bd43d913001cfe72d9130004fd72d913001cfc72d9130014fe71d9130004fd71d9130014fc71d91300067f51d9130356df31d9130024ff70d9130024fd70d91303467f50d91303467d50d9130346bf40d9130346bd40d9130346fa10d913002cff76591300057f75591300957c755913008ebc645913033ddf735913034dfb7059130004ff75591300067f75591300047f7559130034fe7559130004fd7559130034fc75591300067c75591300347c7559130344ff7459130006bf745913008e7e545913008e7c545913033cff7359130006df7359130004ff725913001cfe725913001cfc725913008ebf4259130004ff7159130014fe7159130014fc71591300067f515913008ebf41591300b6df315913019cff7059130006fb705913019e7f505913019e7d505913019efa105913000ddc7650d3002edc7650d3000cdc7650d300075f7550d303375c7550d30336df6550d30336dd6550d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d303379f5450d3008f5e5450d3008f5c5450d3008f9c5450d3008f1c5450d30005d
  | 8 => 0x57f755894009d7c75589400067f65589400067c65589400aeec625894039dfb705894000dbc765094001ebc765094000cbc76509400073f755094038f3c75509400073f6550940196be6550940196bc655094038f3c65509401963c6550940005bf7350940006bf635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400afac62509400afae525094038fad5250940397af32509400afac3250940005bf715094038f3f51509400afaf2150940007bb705094000dbe705094000dbc705094017fb8705094002ebf605094002fbb605094017f3f505094017fba505094017f3d505094038fb9505094017faf205094017fba1050940004ff764c940004fe764c940004fc764c9400067f654c9401767c654c94002dbe744c940005bd744c9400afcc324c940014fe76d854009d7c75d85400067f65d85400067c65d85400a6f661d8540004ff75d85400067f75d8540034fe75d8540004fd75d8540034fc75d85400067c75d85400347c75d854000cfd74d8540014fc74d85403867e54d85403867c54d8540024fe73d8540004fd73d8540024fc73d8540386bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d8540386bf42d8540006bd42d85400a67f51d85400a6f641d8540386f541d854002cfd70d854024e7f50d854024e7d50d854024ef710d85400057f755854009d7c75585400067f65585400067c65585400a6f4615854037dfb70585400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c765454002d7e745454002d7c745454013e7f64545400067f635454014e7e635454014e7c63545401573f43545400073d43545400067f62545401467e62545401467c62545401573f42545400073d425454026d7f715454009f7771545400a67f61545400167e61545400167c61545400a73f41545400a776415454015775415454013d7f705454013f7a705454000779705454013e7f60545401577b405454013f3e405454013f3c405454013f78405454013f7a105454000dbc7650540016bc765054000cbc76505400073f75505403773c75505400073f65505403773c6550540005bf7350540006bf6350540005bf7250540006bf625054002dbf715054002fb77150540007b76150540016be6150540016bc61505400a7b461505400a73f51505400a7b651505400a73d5150540377b55150540007355150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011f3f505054011fba505054011f3d5050540377b9505054011fb7105054011fba1050540004ff764c540004fe764c540004fc764c5400067f654c5401167c654c54002dbe744c540005bd744c540026de634c5400079d434
  | 9 => 0xf41d954002d7f70d95403d77b70d954002d7d70d95403cf7870d95403d77b40d95403cf3e40d95403cf3c40d95403cf7840d95403cf7a10d95403ce7f74d95403d67e74d954002c7e74d95403ce7d74d95403ce7c74d954002c7c74d95400067f73d95400067e73d95400067d73d95400067c73d95403d67f43d95403d67e43d95403d67d43d95403d67c43d95400067f72d95400067e72d95400067d72d95400067c72d95403d67f42d95403d67e42d95403d67d42d95403d67c42d95400067f32d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d95403d67f41d95403d67e41d95403d67d41d95403d67c41d95400067f31d95400067e31d95400067c31d95400067f21d95400067e21d95400067c21d95403ce7f70d954002c7f70d95403ce7e70d95403ce7d70d954002c7d70d95403ce7c70d95403ce7f40d95403ce7e40d95403ce7d40d95403ce7c40d95403ce7f30d95403ce7e30d95403ce7d30d95403ce7c30d95403ce7f20d95403ce7e20d95403ce7d20d95403ce7c20d95403ce7f10d95403ce7e10d95403ce7d10d95403ce7c10d9540024fe76d8d400067f65d8d400067c65d8d400b6de63d8d40004ff75d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d403c67e54d8d403c67c54d8d400b6de43d8d403c6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d403c6bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d400067f51d8d403c6bf41d8d4002cfd70d8d4033e7f50d8d4033e7d50d8d4033edf30d8d4033efa10d8d400057f7558d4009d7c7558d400067f6558d400067c6558d400b6dc6358d403bdfb7058d4000dbc7650d40026bc7650d4000cbc7650d400073f7550d403af3c7550d400073f6550d401b6be6550d401b6bc6550d403af3c6550d401b63c6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400b79c6350d400b79e5350d403af9d5350d40005bf7250d403b79e3250d400b79c3250d40005bf7150d403af3f5150d400b79f3150d40007bb7050d4000dbe7050d4000dbc7050d4019fb87050d4002ebf6050d4002fbb6050d4019f3f5050d4019fba5050d4019f3d5050d403afb95050d4019f9f3050d4019fba1050d4001cfe76d89400067f65d89400067c65d89400aeee62d8940004ff75d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d89403a67e54d89403a67c54d8940024fe73d8940004fd73d8940024fc73d89403a6bf43d8940006bd43d89400aeee42d89403a6ed42d8940014fe71d8940004fd71d8940014fc71d89400067f51d89403a6bf41d894002cfd70d89402de7f50d89402de7d50d89402deef20d89402defa10d8940
  | 10 => 0x855026e7c40d855026e7f30d855026e7e30d855026e7d30d855026e7c30d855026e7f20d855026e7e20d855026e7d20d855026e7c20d855026e7f10d855026e7710d855026e7e10d855026e7c10d85503ed7f76585500057f74585500073f74585500053f74585500d57e74585500d57c74585500073c74585500d53c74585500067f64585500067e64585500067d64585500067c64585500057f73585500cd7e73585500cd7c73585500067f63585500067e63585500067d63585500067c63585500057f72585500c57e72585500c57c72585500067f62585500067e62585500067d62585500067c625855026d7f71585500077761585500be7e61585500be7c61585500bf7461585500bf76415855013d7f70585500077b70585503e57b705855013e7f60585500577b605855013f7a40585500057f76505500067f76505500047f76505500057e76505500057d76505500057c76505500067c76505500047c76505502557f745055002e7e645055002e7c64505500057f73505500cd7e73505500cd7c73505500d73f43505500073d43505500057f72505500c57e72505500c57c72505500d73f42505500073d425055024d7f71505500be7f61505500bf7661505500077561505500d77741505500bf3e41505500bf3c41505500bf74415055011d7f705055000d7e705055000d7c705055011e7f60505501377b605055011f3f405055011f7a405055011f7710505500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5500d57e744c5500057d744c5500d57c744c55010e7e644c55010e7c644c5502357f734c5500cf5e434c5500075d434c5500057f724c5500c57e724c5500c57c724c5500cf5f324c5500075d324c55022d7f714c5500be7f614c5500cf77314c5500bf5e314c5500bf5c314c5500bf74314c5500bf76214c5500fd7f704c55000d7e704c55000d7c704c5500fe7f604c5501177b604c5500ff7a404c5500ff5f304c5500ff77104c5500057f76485500057e76485500057d76485500057c76485500057f74485500d57e74485500057d74485500d57c74485500ee7e64485500ee7c64485500057f73485500cd7e73485500057d73485500cd7c73485502157f72485500c76e42485500076d42485500c76e32485500076d324855020d7f71485500be7f61485500bf7631485500077531485500c77721485500bf6e21485500bf6c21485500bf7421485500dd7f704855000d7e704855000d7c70485500de7f60485500f77b60485500df7a40485500df6f20485500df7710485503dd7e76d954009e7e76d95400347e76d954002d7e74d954002d7c74d95400067e63d95400067c63d95403d73f43d95400067e62d95400067c62d95403d73f42d95400057d71d95400067e61d95400067c61d95403d73
  | 11 => 0x67e64589500067c64589500057f73589500cd7e73589500cd7c73589500067f63589500067d635895041d7f72589500076f62589500c67e62589500c67c62589500c76c62589500c76e42589500057f71589500bd7e71589500bd7c715895040d7f70589500077b70589504157b705895040e7f60589500777b605895040f7a40589500057f76509500067f76509500047f76509500057e76509500057d76509500057c76509500067c76509500047c76509502e57f74509500073f645095002e7e645095002e7c64509500d73c645095002e3c64509500057f73509500cd7e73509500cd7c73509500d73f43509500073d43509502dd7f72509500c76e62509500076d62509500d76f42509500c73e42509500c73c42509500c76c42509504076f32509500c76c32509500057f71509500bd7e71509500bd7c71509500d73f41509500c76f215095017d7f705095000d7e705095000d7c705095017e7f60509501977b605095017f3f405095017f7a405095017f6f20509500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9500d57e744c9500057d744c9500d57c744c95016e7e644c95016e7c644c9502c57f734c9502bd7f724c9500cf6f324c9500c75e324c9500c75c324c9500c76c324c9500c74c324c9500057f714c9500bd7e714c9500bd7c714c9500cf5f314c9500c76f214c95015d7f704c95000d7e704c95000d7c704c95015e7f604c9501777b604c95015f7a404c95015f5f304c95015f6f204c9503fd7e76d85500d57e74d85500057d74d85500d57c74d85500067f64d85500067e64d85500067d64d85500067c64d85500cd7e73d85500057d73d85500cd7c73d85500067f63d85500067e63d85500067d63d85500067c63d85500c57e72d85500057d72d85500c57c72d85500067f62d85500067e62d85500067d62d85500067c62d855013d7d71d85500be7e61d85500bf7661d85500be7c61d85500357f70d855000d7e70d85500357d70d855000d7c70d855026e7f60d85503f77b60d855026f7a40d855026f7710d855026f7510d85500067f74d85500067e74d855002c7e74d85500067d74d85500067c74d855002c7c74d85500067f73d85500067e73d85500067d73d85500067c73d85500067f43d85500067e43d85500067d43d85500067c43d85500067f72d85500067e72d85500067d72d85500067c72d85500067f42d85500067e42d85500067d42d85500067c42d85500067f32d85500067e32d85500067d32d85500067c32d855013c7d71d85500be7f41d85500be7e41d85500be7c41d85500be7f31d85500be7e31d85500be7c31d85500be7f21d85500be7e21d85500be7c21d855026e7f70d855026e7d70d85500347d70d855026e7f40d855026e7e40d855026e7a40d855026e7d40d
  | 12 => 0x860581213dd7e76d915002c7e76d91504757d74d91500d67e64d91500d73e64d91500d67c64d91500cd7e73d91500057d73d91500cd7c73d91500d73f43d91500c57e72d91500057d72d91500c57c72d91500d73f42d91500bd7e71d91500057d71d91500bd7c71d91500073e41d91500d73c41d91500357f70d915048f7b70d915000d7e70d91500357d70d915000d7c70d91504867f60d915048f7b60d91504873f40d91504877a40d91504873d40d91503cd7f76591504857f74591500073f64591500d67e64591500d67c64591500d73c64591500057f73591500cd7e73591500cd7c73591500057f72591500c57e72591500c57c72591500057f71591500bd7e71591500bd7c71591504757f70591500077b705915047d7b70591504767f605915009f7b60591504777a405915046d7e76d8d500d57e74d8d500057d74d8d500d57c74d8d500067e64d8d500067c64d8d504457d73d8d500ce7e63d8d500cf5e63d8d500ce7c63d8d500c57e72d8d500057d72d8d500c57c72d8d500bd7e71d8d500057d71d8d500bd7c71d8d500357f70d8d5000d7e70d8d500357d70d8d5000d7c70d8d504567f60d8d504677b60d8d504577a40d8d504575f30d8d504575d30d8d5045d7f7658d500057f7458d500d57e7458d500d57c7458d500067e6458d500067c6458d504557f7358d500075f6358d500ce7e6358d500ce7c6358d500cf5c6358d500cf5e4358d500057f7258d500c57e7258d500c57c7258d500057f7158d500bd7e7158d500bd7c7158d504457f7058d500077b7058d5044d7b7058d504467f6058d500977b6058d504477a4058d500057f7650d500067f7650d500047f7650d500057e7650d500057d7650d500057c7650d500067c7650d500047c7650d503457f7450d500073f6450d5002e7e6450d5002e7c6450d500d73c6450d5002e3c6450d5033d7f7350d500cf5e6350d500075d6350d500d75f4350d500cf3e4350d500cf3c4350d500cf5c4350d500057f7250d500c57e7250d500c57c7250d500d73f4250d5043f5e3250d500cf5c3250d500057f7150d500bd7e7150d500bd7c7150d500d73f4150d500cf5f3150d5019d7f7050d5000d7e7050d5000d7c7050d5019e7f6050d501b77b6050d5019f3f4050d5019f7a4050d5019f5f3050d504357e76d89500d57e74d89500057d74d89500d57c74d89500067e64d89500067c64d89500cd7e73d89500057d73d89500cd7c73d89500067f63d89500067d63d895040d7d72d89500c67e62d89500c76e62d89500c67c62d89500bd7e71d89500057d71d89500bd7c71d89500357f70d895000d7e70d89500357d70d895000d7c70d895041e7f60d895042f7b60d895041f7a40d895041f6f20d895041f6d20d89504257f76589500057f74589500d57e74589500d57c7458950
  | 13 => 0x8d21024ff7658d210e6dc6358d214bdef7258d214cdf77158d21004ff7558d21034fe7558d21004fd7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d210067e5458d210067c5458d214c4ff7358d21006df7358d214bcff7258d21006ef7258d21164ff7158d21006f77158d211667f5158d211667d5158d21004ff7058d2100cfe7058d2100cfc7058d210067f5058d210e6df3058d21106ef2058d21166f71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210f57c7550d2102ebe6450d21006bd6450d210ef3c5450d21006df6350d21026dc6350d2101dee7250d211afce3250d21015ec765092102eec7650921014ec76509210076f75509214b76c75509214b6ef65509214b6ed655092101def745092101faf7450921007af645092102eee645092102eec64509210efac64509214b7af54509210ef6e54509210ef6c54509210efac54509210ef2c5450921005ef735092118eee635092118eec63509210efaf4350921007ad4350921007e77150921015ee7150921015ec7150921187e47150921015e4715092101eef615092101fe761509211876f51509211876d5150921187af4150921187ad4150921187e63150921005ef70509214b76f50509210efaf4050921187e71050921015ec764c921026ec764c921014ec764c921005ef744c921005ed744c9214af6e544c9214af6c544c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210e7cc634c921026cc634c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c9211676f514c9211676d514c921167cf314c921167e6314c921167cd314c921005ef704c9214a76f504c9210e7cf304c921167e7104c92101df4764c521026f4764c52101cf4764c52149f76544c52149f74544c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210e7d4634c5210e7d6434c521007d5434c521007e7724c52101df6724c52101df4724c521107e4724c521016f7624c521017e7624c521107e6424c521007e5424c521107d7324c521107e6324c521107d5324c5210e7e5324c521007c5324c521005f7704c52149777504c5210e7d7304c521107e7204c52100cfe76d81210defa60d8121004ff75d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d81210067e54d81210067c54d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d8121296ee42d8121006ed42d8121296ee32d8121006ed32d812101cfd71d812100cfc71d812121e7f51d812121e7d51d812121ef631d8121006f531d81210de7f50d81210defa20d81210defa10d8121005df73581210e5dc73581210def
  | 14 => 0x4ff7650931004fe7650931004fc76509310057f75509311157c755093102ebe6450931006bd645093110f3c5450931025de73509310079d4350931006ef625093101eec625093118fcf3250931015dc764c93101edc764c931014dc764c931005df744c931005dd744c9315075e544c9315075c544c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c93101ecc624c931007d7714c931015de714c931015dc714c931167d4714c931026df614c931027d7614c9311675f514c9311675d514c931167cf214c931167d6214c931005df704c9314ff5f504c931107cf204c931167d7104c93100cfe76d81310fefa60d8131004ff75d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d81310067e54d81310067c54d8131014fd73d813100cfc73d8131306de43d8131006dd43d813101cfe72d8131004fd72d813101cfc72d8131306df32d8131006dd32d8131024fd71d813123e7f51d813123e7d51d813123ef621d81310fe7f50d81310fefa30d81310fefa10d8131005ef7258131105ec72581310fef8605813102cfe76d91210f57e75d91210057d75d91210eebe64d9121004ff75d9121034fe75d91210067e75d91210347e75d9121004fd75d91210067d75d91210047d75d9121034fc75d9121184fd74d91210ee7e54d91210ee7c54d9121024fe73d9121004fd73d9121024fc73d9121014ff72d9121014fd72d91214f6bf42d91214f6bd42d912101cff71d912101cfd71d91214e67f51d91214e67d51d91214e6bf41d91214e6bd41d912100cfe70d9121004fd70d912100cfc70d91210067f50d91214f6ef20d91214e6f710d912102cff76591210057f75591210f57c75591210eebc64591214ddef72591214edf77159121004ff75591210067f75591210047f7559121034fe7559121004fd7559121034fc75591210067c75591210347c75591214e4ff7459121006bf74591210ee7e54591210ee7c5459121004ff7359121024fe7359121024fc73591210eebf43591214dcff7259121006ef7259121184ff7159121006f771591211867f51591211867d5159121004ff705912100cfe705912100cfc70591210067f50591210eebf4059121126ef2059121186f71059121024fe76d8d210e6de63d8d21004ff75d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d210067e54d8d210067c54d8d21164fd73d8d210e6de43d8d21014ff72d8d21014fd72d8d214d6df32d8d214d6dd32d8d2101cff71d8d2101cfd71d8d214c67f51d8d214c67d51d8d214c6df31d8d214c6dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210067f50d8d21006de30d8d210e6dc30d8d214d6ef20d8d214c6f710d
  | 15 => 0x551d814111efa60d8141004ff75d81410067f75d8141034fe75d8141004fd75d8141034fc75d81410067c75d81410347c75d8141014fd74d814100cfc74d814137e7e54d814137e7c54d8141024fe73d8141004fd73d8141024fc73d814137ebf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d814137ebf42d8141006bd42d814102cfd71d814125e7f51d814125e7d51d814111e7f50d814111efa40d814111efa10d81410057f75581411357c75581410067f65581410067c655814100775515814111ef8605814102cfe76d91311157e75d91310057d75d913110ebe64d9131004ff75d9131034fe75d91310067e75d91310347e75d9131004fd75d91310067d75d91310047d75d9131034fc75d91311a4fd74d913110e7e54d913110e7c54d9131014ff73d9131014fd73d913153ebf43d913153ebd43d913101cfe72d9131004fd72d913101cfc72d9131024ff71d9131024fd71d913152e7f51d913152e7d51d913152ebf41d913152ebd41d913100cfe70d9131004fd70d913100cfc70d91310067f50d913153edf30d913152ef710d913102cff76591310057f75591311157c755913110ebc6459131525df7359131535f77159131004ff75591310067f75591310047f7559131034fe7559131004fd7559131034fc75591310067c75591310347c755913152cff7459131006bf745913110e7e545913110e7c5459131524ff7359131006df7359131004ff725913101cfe725913101cfc725913110ebf42591311a4ff7159131006f771591311a67f51591311a67d5159131004ff705913100cfe705913100cfc70591310067f505913110ebf405913112edf30591311a6f71059131015dc7650d3102edc7650d31014dc7650d310075f7550d3151f5c7550d3151edf6550d3151edd6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3151f9f5450d3110f5e5450d3110f5c5450d3110f9c5450d3110f1c5450d31005df7250d311aede6250d311aedc6250d3110f9f4250d31007d77150d31015de7150d31015dc7150d311a7d47150d31015d47150d31026df6150d31027d76150d311a75f5150d311a75d5150d311a79f4150d311a79d4150d311a7d62150d31005df7050d3151f5f5050d3110f9f4050d311a7d71050d3101cfe76d8931106ee62d8931004ff75d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d89310067e54d89310067c54d8931014fd73d8931106ee42d8931106ee32d8931516ed32d8931024fd71d89314be7f51d89314be7d51d89314beef21d893100cfe70d8931004fd70d893100cfc70d89310067f50d8931516df30d8931006ee20d8931106ec20d89314bef710d8931106ec625893150df77158931
  | 16 => 0xd4112f9c6350d4112f9e5350d4157f9d5350d41005bf7250d415879e3250d4112f9c3250d41007b77150d41015be7150d41015bc7150d411a7b47150d4102ebf6150d4102fb76150d411a73f5150d411a7b65150d411a73d5150d4157fb55150d411a79f3150d41005bf7050d4157f3f5050d4112f9f3050d411a7b71050d4101cfe76d89410067f65d89410067c65d8941126ee62d8941004ff75d8941034fe75d8941004fd75d8941034fc75d8941014fd74d89415767e54d89415767c54d8941024fe73d8941004fd73d8941024fc73d8941576bf43d8941006bd43d8941126ee42d8941576ed42d894102cfd71d89414de7f51d89414de7d51d89414deef21d894100cfe70d8941004fd70d894100cfc70d89410067f50d8941576bf40d89414def710d89410057f75589411357c75589410067f65589410067c6558941126ec625894156df77158941015bc765094101ebc7650941014bc76509410073f755094155f3c75509410073f6550941196be6550941196bc655094155f3c65509411963c6550941005bf7350941006bf635094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac6250941127ae525094155fad5250941567af3250941127ac3250941007b77150941015be7150941015bc7150941187b4715094102ebf615094102fb761509411873f5150941187b651509411873d515094155fb55150941187af2150941005bf705094155f3f5050941127af2050941187b71050941004ff764c941004fe764c941004fc764c9410067f654c9411767c654c94102dbe744c941005bd744c941127cc324c94113777765454103677765454115774765454102d74765454103674765454102c74765454115777745454100737745454115776745454102d76745454115775745454115774745454102d74745454115734745454101777645454101677645454101737645454100777735454155776735454100775735454155774735454100777635454155776635454100775635454155774635454115777435454115737435454115776435454115775435454100735435454115774435454100777725454154f76725454100775725454154f74725454100777625454154f76625454100775625454154f74625454115777425454115737425454115776425454115775425454100735425454115774425454155777325454154f76325454100775325454154f74325454100777705454100577705454154776705454100775705454154774705454154776605454154774605454115777405454115737405454115776405454115774405454155777305454154776305454154774305454154f77205454154776205454154774205454100cfe76d81411357c75d81410067f65d81410067c65d81410077
  | 17 => 0x13e7c10d815113d7f76581510057f74581510073f74581510053f74581511557e74581511557c74581510073c74581511553c74581510067f64581510067e64581510067d64581510067c64581510057f735815114d7e735815114d7c73581510067f63581510067e63581510067d63581510067c63581510057f72581511457e72581511457c72581510067f62581510067e62581510067d62581510067c62581510bd7f71581510077771581513f57771581510be7f61581510577761581510bf76415815113d7f70581510077b605815113e7e605815113e7c605815113f78605815113f7a40581515ad7e76d95411367e76d95410347e76d954102d7e74d954102d7c74d95410067e63d95410067c63d95415a73f43d95410067e62d95410067c62d95415a73f42d954102d7f71d95415a77771d954102d7d71d954159f7471d95415a77741d954159f3e41d954159f3c41d954159f7441d95410057d70d95410067e60d95410067c60d95415a73f40d954159f7710d954159e7f74d95415a67e74d954159e7d74d954159e7c74d95410067f73d95410067e73d95410067d73d95410067c73d95415a67f43d95415a67e43d95415a67d43d95415a67c43d95410067f72d95410067e72d95410067d72d95410067c72d95415a67f42d95415a67e42d95415a67d42d95415a67c42d95410067f32d95410067e32d95410067c32d954159e7f71d954102c7f71d954159e7e71d954159e7d71d954102c7d71d954159e7c71d954159e7f41d954159e7e41d954159e7d41d954159e7c41d954159e7f31d954159e7e31d954159e7d31d954159e7c31d954159e7f21d954159e7e21d954159e7d21d954159e7c21d95410067f70d95410067e70d95410067d70d95410047d70d95410067c70d95415a67f40d95415a67e40d95415a67d40d95415a67c40d95410067f30d95410067e30d95410067c30d95410067f20d95410067e20d95410067c20d954159e7f10d954159e7e10d954159e7d10d954159e7c10d9541024fe76d8d410067f65d8d410067c65d8d4112ede63d8d41004ff75d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d415967e54d8d415967c54d8d4112ede43d8d41596dd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d41596bf42d8d4102cfd71d8d415267f51d8d415267d51d8d41526df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410067f50d8d41596bf40d8d41526f710d8d410057f7558d411357c7558d410067f6558d410067c6558d4112edc6358d4158df77158d41015bc7650d41026bc7650d41014bc7650d410073f7550d4157f3c7550d410073f6550d411b6be6550d411b6bc6550d4157f3c6550d411b63c6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc635
  | 18 => 0xc62589511476e42589515bd7f71589510077771589515c57771589515be7f61589510f77761589515bf7641589510057f705895113d7e705895113d7c70589510057f76509510067f76509510047f76509510057e76509510057d76509510057c76509510067c76509510047c76509514e57f74509510073f645095102e7e645095102e7c64509511573c645095102e3c64509510057f735095114d7e735095114d7c73509511573f43509510073d43509514dd7f72509511476e62509510076d62509511576f42509511473e42509511473c42509511476c42509515b76f32509511476c32509511857f71509510157e71509510157c71509511867f61509511977761509511873f41509511877641509511876f21509510057f705095113d7e705095113d7c70509511573f40509511476f20509510057f764c9510057e764c9510057d764c9510057c764c9510057f744c9511557e744c9510057d744c9511557c744c95116e7e644c95116e7c644c9514c57f734c9514bd7f724c95114f6f324c9511475e324c9511475c324c9511476c324c9511474c324c9511657f714c9510157e714c9510157c714c9511667f614c95117777614c95116776414c9511675f314c9511676f214c9510057f704c95113d7e704c95113d7c704c95114f5f304c9511476f204c95113d7e76d81511557e74d81510057d74d81511557c74d81510067f64d81510067e64d81510067d64d81510067c64d815114d7e73d81510057d73d815114d7c73d81510067f63d81510067e63d81510067d63d81510067c63d81511457e72d81510057d72d81511457c72d81510067f62d81510067e62d81510067d62d81510067c62d81510357f71d81510157e71d81510357d71d81510157c71d81512767f61d81513e77761d81512777641d815113d7d70d815113e7e60d815113f7a60d815113e7c60d815113f7a10d81512777910d81510067f74d81510067e74d815102c7e74d81510067d74d81510067c74d815102c7c74d81510067f73d81510067e73d81510067d73d81510067c73d81510067f43d81510067e43d81510067d43d81510067c43d81510067f72d81510067e72d81510067d72d81510067c72d81510067f42d81510067e42d81510067d42d81510067c42d81510067f32d81510067e32d81510067d32d81510067c32d81512767f71d815113e7d71d81510347d71d81512767f41d81512767e41d81512767641d81512767d41d81512767c41d81512767f31d81512767e31d81512767d31d81512767c31d81512767f21d81512767e21d81512767d21d81512767c21d815113e7f40d815113e7e40d815113e7c40d815113e7f30d815113e7e30d815113e7c30d815113e7f20d815113e7e20d815113e7c20d815113e7f10d815113e7e10d815113e7a10d8151
  | 19 => 0x91510057d72d91511457c72d91511573f42d91510357f71d915163f7771d91510157e71d91510357d71d91510157c71d91516367f61d915163f7761d91516373f41d91516377641d91516373d41d915113d7e70d91510057d70d915113d7c70d91510073e40d91511573c40d915159d7f76591516357f74591510073f64591511567e64591511567c64591511573c64591510057f735915114d7e735915114d7c73591510057f72591511457e72591511457c72591516257f715915100777715915162d7771591516267f61591511377761591516277641591510057f705915113d7e705915113d7c705915161d7e76d8d511557e74d8d510057d74d8d511557c74d8d510067e64d8d510067c64d8d515f57d73d8d5114e7e63d8d5114f5e63d8d5114e7c63d8d511457e72d8d510057d72d8d511457c72d8d510357f71d8d510157e71d8d510357d71d8d510157c71d8d516067f61d8d516177761d8d516077641d8d516075f31d8d516075d31d8d5113d7e70d8d510057d70d8d5113d7c70d8d5160d7f7658d510057f7458d511557e7458d511557c7458d510067e6458d510067c6458d516057f7358d510075f6358d5114e7e6358d5114e7c6358d5114f5c6358d5114f5e4358d510057f7258d511457e7258d511457c7258d515f57f7158d51007777158d515fd777158d515f67f6158d51117776158d515f7764158d510057f7058d5113d7e7058d5113d7c7058d510057f7650d510067f7650d510047f7650d510057e7650d510057d7650d510057c7650d510067c7650d510047c7650d5152d7f7450d510073f6450d5102e7e6450d5102e7c6450d511573c6450d5102e3c6450d515257f7350d5114f5e6350d510075d6350d511575f4350d5114f3e4350d5114f3c4350d5114f5c4350d510057f7250d511457e7250d511457c7250d511573f4250d515ef5e3250d5114f5c3250d511a57f7150d510157e7150d510157c7150d511a67f6150d511b7776150d511a73f4150d511a7764150d511a75f3150d510057f7050d5113d7e7050d5113d7c7050d511573f4050d5114f5f3050d515e57e76d89511557e74d89510057d74d89511557c74d89510067e64d89510067c64d895114d7e73d89510057d73d895114d7c73d89510067f63d89510067d63d89515bd7d72d89511467e62d89511476e62d89511467c62d89510357f71d89510157e71d89510357d71d89510157c71d89515ce7f61d89515df7761d89515cf7641d89515cf6f21d89515cf6d21d895113d7e70d89510057d70d895113d7c70d89515d57f76589510057f74589511557e74589511557c74589510067e64589510067c64589510057f735895114d7e735895114d7c73589510067f63589510067d63589515cd7f72589510076f62589511467e62589511467c62589511476
  | 20 => 0x39e7e54d814239e7c54d8142024fe73d8142004fd73d8142024fc73d814239ebf43d8142006bd43d814202cfd72d8142014fe71d8142004fd71d8142014fc71d81420067f51d814239ebf41d81422eeef21d814217e7f50d814217efa40d814217efa20d81420057f75581421957c75581420067f65581420067c655814206f3c545814217ef8605814202cfe76d91321757e75d91320057d75d913216ebe64d913264fcc32d9132004ff75d9132034fe75d91320067e75d91320347e75d9132004fd75d91320067d75d91320047d75d9132034fc75d91321acfd74d913216e7e54d913216e7c54d913201cff73d913201cfd73d913265ebf43d913265ebd43d9132024ff72d9132024fd72d913264ebf42d913264ebd42d913265eef32d913264ede32d913264edc32d913264eec32d913264ecc32d9132014fe71d9132004fd71d9132014fc71d91320067f51d913265edf31d913264eef21d913200cfe70d9132004fd70d913200cfc70d91320067f50d913265edf30d913264eef20d913202cff76591320057f75591321757c755913216ebc645913216f3c5459132645df7359132655ef72591321afcc3259132004ff75591320067f75591320047f7559132034fe7559132004fd7559132034fc75591320067c75591320347c755913264cff7459132006bf7459132006bf545913216e7e545913216e7c545913216ebc545913216e3c5459132644ff7359132006df73591321acff7259132006ef725913218eef32591321aede32591321aedc32591321aeec32591321aecc3259132004ff7159132014fe7159132014fc71591320067f515913216ebf415913218edf31591321aeef2159132004ff705913200cfe705913200cfc70591320067f505913216ebf405913218edf30591321aeef2059132014fe76d85324cfcc32d8532166f661d8532004ff75d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d85320067e54d85320067c54d853201cfd73d8532024fd72d85321667f51d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d85320067f50d853250edf30d85324ceef20d8532107cc3258532166f4615853200cfe76d81322cfcc32d813215efa60d8132004ff75d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d81320067e54d81320067c54d813201cfd73d8132024fd72d8132014fe71d8132004fd71d8132014fc71d81320067f51d8132326df31d81322ceef21d813215e7f50d813215efa30d813215efa20d8132087cc325813215ef860581325ad7e76d915102c7e76d91516257d74d91511567e64d91511573e64d91511567c64d915114d7e73d91510057d73d915114d7c73d91511573f43d91511457e72d
  | 21 => 0xd71d95420067c71d95426867f41d95426867e41d95426867d41d95426867c41d95420067f31d95420067e31d95420067c31d954267e7f21d954267e7e21d954267e7d21d954267e7c21d95420067f70d95420067e70d95420067d70d95420047d70d95420067c70d95426867f40d95426867e40d95426867d40d95426867c40d95420067f30d95420067e30d95420067c30d954267e7f20d954267e7e20d954267e7d20d954267e7c20d95420067f10d95420067e10d95420067c10d9542024fe76d8d420067f65d8d420067c65d8d426773c54d8d4218ede63d8d4201dee72d8d4202ded72d8d4218fcf32d8d42004ff75d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d42006bf54d8d426767e54d8d426767c54d8d42676bc54d8d426763c54d8d4218ede43d8d42676dd43d8d4202cfd72d8d4218eed72d8d4202ced72d8d42646df32d8d4218eef32d8d42646ec32d8d42014fe71d8d42004fd71d8d42014fc71d8d420067f51d8d42676bf41d8d42646ef21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420067f50d8d42676bf40d8d42646ef20d8d420057f7558d421957c7558d420067f6558d420067c6558d4216f3c5458d4218edc6358d4266def7258d421afcc3258d4201dbc7650d42026bc7650d4201cbc7650d420073f7550d42195be7550d42195bc7550d426673c7550d421953c7550d420073f6550d421b6be6550d421b6bc6550d426673c6550d421b63c6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4218f9c6350d4218f9e5350d426679d5350d42007af7250d4201dbe7250d4201dbc7250d421afac7250d4202ebf6250d4202faf6250d421afae5250d42667ad5250d4218faf3250d421af9e3250d421af9c3250d421afac3250d421af8c3250d42005bf7150d426673f5150d4218f9f3150d421afaf2150d42005bf7050d426673f5050d4218f9f3050d421afaf2050d42014fe76d85421957c75d85420067f65d85420067c65d854256f3c54d8542186f661d8542004ff75d85420067f75d8542034fe75d8542004fd75d8542034fc75d85420067c75d85420347c75d854201cfd74d854256e7e54d854256e7c54d8542024fe73d8542004fd73d8542024fc73d854256ebf43d8542006bd43d854202cfd72d85421867f51d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d85420067f50d854256ebf40d85424eeef20d85420057f75585421957c75585420067f65585420067c65585420ef3c5458542186f4615854200cfe76d81421957c75d81420067f65d81420067c65d814239f3c54d814217efa60d8142004ff75d81420067f75d8142034fe75d8142004fd75d8142034fc75d81420067c75d81420347c75d814201cfd74d8142
  | 22 => 0x8943025de73d894302ddd73d89431aeee62d89431afce32d8943004ff75d8943034fe75d8943004fd75d8943034fc75d8943024fd74d8943006bf54d894366e7e54d894366e7c54d894366ebc54d894366e3c54d894302cfd73d89431aedd73d894302cdd73d89431aeee42d89431aede32d89431aeee32d89431aedc32d8943014fe71d8943004fd71d8943014fc71d89430067f51d894366ebf41d8943656df31d894300cfe70d8943004fd70d894300cfc70d89430067f50d894366ebf40d8943656df30d89430057f75589431b57c75589430067f65589430067c655894316f3c54589431aeec62589431afcc3258943014fe76d85431b57c75d85430067f65d85430067c65d854358f3c54d85431a6f661d8543004ff75d85430067f75d8543034fe75d8543004fd75d8543034fc75d85430067c75d85430347c75d8543024fd74d854358e7e54d854358e7c54d854302cfd73d854301cfe72d8543004fd72d854301cfc72d854358ebf42d85431a67f51d85431a6f641d85431a6f631d854300cfe70d8543004fd70d854300cfc70d85430067f50d854358ebf40d8543536df30d85430057f75585431b57c75585430067f65585430067c655854310f3c54585431a6f4615854300cfe76d81431b57c75d81430067f65d81430067c65d81433bf3c54d814319efa60d8143004ff75d81430067f75d8143034fe75d8143004fd75d8143034fc75d81430067c75d81430347c75d8143024fd74d81433be7e54d81433be7c54d814302cfd73d814301cfe72d8143004fd72d814301cfc72d81433bebf42d8143014fe71d8143004fd71d8143014fc71d81430067f51d81433bebf41d814334edf31d814319e7f50d814319efa40d814319efa30d81430057f75581431b57c75581430067f65581430067c655814308f3c545814319ef8605814368d7e76d95421967e76d95420347e76d954202d7e74d95426873e74d954202d3e74d954267f3d74d954202d7c74d95420067e63d95420067c63d95426873f43d95426876f72d954267f6c72d95426876f42d954267f3e42d954267f3c42d954267f6c42d95420076f32d954267f6c32d95420057d71d95420067e61d95420067c61d95426873f41d954267f6f21d95420057d70d95420067e60d95420067c60d95426873f40d954267f6f20d954267e7f74d95426867e74d95426863e74d954267e7d74d954267e3d74d954267e7c74d95420067f73d95420067e73d95420067d73d95420067c73d95426867f43d95426867e43d95426867d43d95426867c43d954267e7f72d954267e7e72d954267e7d72d954267e7c72d954267e7f42d954267e7e42d954267e7d42d954267e7c42d954267e7f32d954267e7e32d954267e7d32d954267e7c32d95420067f71d95420067e71d95420067d71d95420047
  | 23 => 0x2000000c002000000001000c00d0048008006000000800c01e0030068004004003009801801000f0000000000029000001001c0060028010000000000801c01000f000001002001100180280020010000000006036000801402200900980040060030020004002000000002000000000380bc00a0050000000008010001800000000000080000000030000040000000000000c00001100000300000030000004008000000002400400000000140020090010000000009005000000200f002000800200101100040000000020000006004000000000c01400f0008004002000000c004001000000000800b00080080080140000030006000002006c000002000002c018000001801800000a00000000000040010048000005001800c00800100480000040000020000000004001003c00e000001001000400300800180000170000000000000000002c000003002000001e0040020000014000000800000a00000200000060010008000024002001000000c008001000400a0010010024022004001000c004002002800000200400000000000030060008002007000800800201d000000400000000000000020020000008002003000000000e0030000010000006001800400a00a00080000040016a57e76d95431b67e76d95430347e76d954302d7e74d954369f3e74d954302d3e74d95436973d74d954302d7c74d954369f5f73d95436975c73d954369f5f43d95436973e43d95436973c43d95436975c43d95430067e62d95430067c62d954369f3f42d95430075e32d95436975c32d95430057d71d95430067e61d95430067c61d954369f3f41d95436975f31d95430057d70d95430067e60d95430067c60d954369f3f40d95436975f30d95436967f74d954369e7e74d954369e3e74d95436967d74d95436963d74d95436967c74d95436967f73d95436967e73d95436967d73d95436967c73d95436967f43d95436967e43d95436967d43d95436967c43d95430067f72d95430067e72d95430067d72d95430067c72d954369e7f42d954369e7e42d954369e7d42d954369e7c42d95436967f32d95436967e32d95436967d32d95436967c32d95430067f71d95430067e71d95430067d71d95430047d71d95430067c71d954369e7f41d954369e7e41d954369e7d41d954369e7c41d95436967f31d95436967e31d95436967d31d95436967c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430047d70d95430067c70d954369e7f40d954369e7e40d954369e7d40d954369e7c40d95436967f30d95436967e30d95436967d30d95436967c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d954301cfe76d89430067f65d89430067c65d894366f3c54d
  | 24 => 0x401a0000018018000010000000000600000080100720010028000006000005000000c00300000080100170000028000003001800003c004004800400e00200280100020060090000000000000007803600f00100040000020000018004001001001c00400100000000060050058008004000003801800400000000dc00c000002803400000400080040020000010004000000001800000a00100080000040000000004008003000002401a000003800000a00400100000060040028000000001003800400000d000800400000b003800c00a0000000000004004002000c0000000008000010000000005801c000002800800200100000040280010010004000000000800000c00b00700000000000058038000000002002c026003001002001000a00300040020010030004000009000000400600000100000000050000000000002000800000600000a802c002000000000c00c0040080004012002003801400400b00380100020030010004000001000000400000700a806000000b003000000c0000008000010000000001c004001000006c00400600000140000080000000026005001000000000b00a0000008000000802000a0000050000002000008000000000e002801c0040000038008000000001800c00000600000040000010008010004008001800c00000300a000c00000800080080000020000000066003000800c00200300d801c000001000800c000001001000c002002000801000000300180040000010038004000012000000400c002000000000200600f80140000000010000000004001003000a000000001400000d0040010004006004000401200501500000000040018000000004000800400400400080040120010040004000006000000802001e007000401c023000000400800200380b800800000000040020010018000000001000000c08a000000800400e000006002401001900000100160060018004004001000003c004000002000000002c0020030006003003001c00200300000000000040000000020002001005c0120040028008000000000003400600200300040140000020044000003000802800c00400800240000060008030000001000000c0020000018030028002004800800000e0018000002000000800000c001004800400000100180000140020108020002001000801000600100480100200180008000000001003800400a00100200080140000000008000004001000000c001000005c00e0070010008008001004000002e007003000000a036001000c006000002803c000005000001800c02d002800001000300100080080000000004004004001001c01401100000000000060028068008000000800002c0110000000000017000000000402600080000040000000004000003002800000000
  | 25 => 0xda5f40002379d1a7b375e394c02a00637580000008920000000000dc459887fdba40001519574d28941710000000016300000008040000001c6000019a00c000000066d7630000f5400010cbe0417e15000001919e067721d85a800000000000000000004bd000000000031e80000002f3690b0b000010100000000001710000d4d430cdd00019f1c980005a7089c556000000000144ae064580cfd48e0217548661878a0300000005e80000003ad8b72000000296c3f49980000000c7c3c36483b0d8b071c01814317c8abb5dd174d4c08b262309c0f5c13a75aab29bc228c50a2f884b071368205c19c2000503aeb5710bb177a2f0576eb600000000c82f541ad820513c4a61a43df41e69da0373918ee2def13791c0262dcb0000001bf84a3000177ccec8560000a58ba882952a2a84000d475df98294128076f4bdf832a875000010c7a20007b800000003b3000000c0010078008002003000002c0040030000008006004004800c008017003000001000600a00200300030000000004000007803800000a002800002000e00100100020080010098042005000800402c0030000000000006002801000a000000800000a0010000010002001002800800400100080000020120010004000004000800400000000980180260000010000002001000000000400400000000020000078008002000000002400200400c8008004002001801801200500080000100030060000000001001800000000b001800800a000007000000e0010038000002000000801c00401100000100040010010000002017002801400001b0020004000005001000c00601a0050010014001003000000e007000800803a003007001400c003002804c00200000100000020000000000006004001000c00c00000000100040080070020000003000000c00a000000000000000500c000000000c001001400200f000800000000901d80080020000000000000000000000400e000006800c00e002000000400a0010110000000004000800000000000000040000060070000000000001800c0040010018000000002001000000400200780280000000000000000019000800400a003000800000000e001803400c00500b000000000c002000c000005003001c018000003802000200b0010020006000000801001a00b0008010002003000800000000500600080000000078008030000000001400400200f80580060000000008000000001000000400000180000020010000010000000003000400200000300000000060030008028001000000402000300c000400200600000000020010000014000002003001000000100080c001200000000000160000000038000000002800c006007000804400e0020000000008006007800c00200000f801c002003006004400600800000
  | 26 => 0x61a0000bde18f73401bddb000000032d9806000000000083c0000000000ea20004ef80010b6732000000192c0003290390a0ced700000018be7610000588000f9544293f4000230000326d1304320000000000bdb00000000000000000fc8b4e0000000e51c6a5191193894000e72495000072ecb200014dc2727e250f14040007f60003a5db3adb250683d400036c0000001416b136148001c44000000000000000000000000000004550000eb00001fda0fc17a3a80003764000c0709e07a80005d62778000000ce00000000c104c91f880000006f14c004f80001ca00039a47640000000a9982006901a00001942eb000135594aa3e517800000062600000000008a2000059c00000055338700000000679b2c000e5275f1d30560000000000052233a5f60001006429050126c000c9800000017da0792d8000078e00000011880008992ababe99108b56baa09dd023a95e83a08dca9b45703e90734cbc273a349c6e5d746f967038a23a53410e478c4fe780a501722ef92521dccc5c5112b18c08daaa7166897395568d4680afdd0fea244480f840a022320d82d4738e2e2b3b370cf22082101674d92e3922a25b83b2573532021d2da90b7c015d0f84f5b62a3458916d8a3a93e295da2cb58712f99c69a77b5b1f03f6d3e1f103f0d94bfc67f0001b48d0803c3a2905e3ea5793e3d52667b4241c995d6ef63af8001dfa6631133e5101e20f5d42d44000000655a9dc000d3f0000d1d42af865032178d7c2c1328b578d5cae400016c5d3e5c270526b9766a216f518097a25a15e680011c8b680002960bcca360000000000ca100000000000000132b9cf4a58308d00006c40000001918e3200062f3d351f82fa0d31b0db3e127077a3b088e074000130c8b627d000000000000000029bc0008ce7c199b0dbc3fe2d49d0901067e10c15b8b268eb000077800000007e8001102d804700001b0a00027200004549040003cb55aecee00000008b80000000000000d6a0003088a6ab0a3e83645dc2dee43c3969a94988038b9f840a000669899c0000001db1814838f5350531bc6c2b3230e83ad2786071f9800015252a7818759e0cb990060e6400000026b800000000010fada8ce443700000fd17c8f3654149c00042e47a8b8c00000022093614bcbe0000283194c0003e50000cbc00056012a143e4cb0002c8034675600026d40007af32b2f60b0000010580f9c941092188000f762400003eb5ce846b6228b14000bd60002d8c000f1033380000000000001ec0b780001f236dddcc2136b81aa40000005b0b810000a1c3dfaa740000000000000fa600000032f402000000f90b030a7105ef04600008680000001beaabf00000005eaf292741901d648cd3bf1811cf68d75be1db1a5699b431922850c5ee08d87247
  | 27 => 0x52a30550db3f49ba0000000000b0c5a60000001df4ef163d09a40003644fd26792561af6c33001dd00001cf0475c5800028fafc91901465c98b095685307d1898d65c00020aad70660ccf376b3403ea58478b37cda2800000029991982e7164aac534c3cc3b32b7921c0002afb1a0000cea0fe0001b760000918c6000000000000015a49e23be236ce8800015092d1a7800048d8088000f69348be40be27b50000000faa0000000d50c74731000000027e3660000001eea13700000000004ac42780000000000000000000c8131927b07ce9e70000001bda47461c1214000000518800000000072f9090000d3070bb5386fa8351290d0c0003d40000ed4a480000b58001ada8f141d8001c2a0005010bdc5de28800000140000000000001aa800900000000000004dc0001afc598000339048aa7e0bd00000000006cf17b40003d200000014a600063980018945f00002ab12b8000000129c0006bb00022b8000dd000005055640004f5800000000076e8638000dfb4430000000000000000000009025e20b0000ee900000000003f63ee0000a06e0314f000dce65fb74b24a150049e000000000000002b800000000075b87f8000aa568e80018960000bb800162212d26610a0886055000000000045f32e2a50d3a03b0001ca800047c70f1e14490b47554261099000007107c97807d13522cd12720000000000354cac0589b443c673800003218f00a30002a20ac4000383000128802d21a04edc2200000000000000004b8b958000000015b031d4c64f0002a80bea00037b9abc40c000000000040493d19d8000000acf5a1b3240002bd00038f1eca0005249a5943ab5d5f5320c47ed5214a8ab00001650000000fd6ab500000006cee7c0000000000963035bd3ce86de0607affc648b901a8000000000000000000000000f5bbe06b000009b254c000e0d3538f700000000000000000d5100000000001210000000a42360642078563206c0002bc12bad22000195c00000070d3b08000c26000000191a9023fd812cd10aef0000000c8e00004dac844660007538c745b8ddf294aa3d7b26a106ab28d12288d25d87e0eb25c900036353e89265d0824c0006850000000000416183800000046f02200000008255520001ef00000001d70000000000000182600045eb8e00000000000000ce8de5000000032ef43061319d3a0222259212400000076a0000000f9d5e294707e84b600000000000000000000000d0b29720614eac3500000000001ba13e068972875e24882e4e9000031c8000dd0000000001139ce2628e80018161332848419e26a7f52a80000000000b7aef40000004990001042c3d000000000000044202d81244720a2bb39b587042712df4a82e455d1002880200054380014dcbf17a5205800000070b15b000020d000000126856a0
  | 28 => 0xf9e4ff46e800090e00052930643a4b4268925a0d26000678800047a70d2508001eb400000032bc000e0b70f8000f4e92917f33c82e8f505a52928000000766371455400000000015b248824b0114000f0d5a49fc4dc083a715a550b9e0ae673b164dc65e757b90000008e24920000000c70000243c2086f578e097464a40f2290a8835687a343096d6d20004db8001240a39663b249cce77b0001ed09544042f639dd53cab9000297431846700018a88a2a620ed3201e74d9a5471084d6402427714f47442d14f9800138a00000012055fc01c00000000000000ea8cf00009c30000000e7ce4000019ad5e68c410b8fa08700004791509bb836872d99e1d0699158580010b800039f80000009e60001720a24eb1775000061200000003b00000004350000ac000039b2c405ca8c730e2d200000d6000000000000064734340006c1000356800056f0001964f36c6237f212c00000051a800134665800015fccfa0001148da93d47110000000a78c300000c05ab80007cc8465cd600000006b863c00000000000008420000001cb043e0a59b116c42ff6f41fcc0000007798000000e9b0ab183cc66a761dd8000a62be300002dd9145c317e2f99cdac9c2be9ad549030458a00001f27814a11135b6c7902b81f0123881d49d2918bfea7258a8001af4ed10000000000f3615388ed7583863379c542485ad2569f84afcf8e3d0be5da881b246c8174b3221b7bd8b1c51c4da0002a0cd32b76484365465c8f4000000092ed573e21ff594800021aa7e02b600028c326864649535020f1e1e00055800000002d600000017fa50500026140000007461dfc0000000000e31d0e0002548001c0e0a700023f97aa93f4b60001daa5944221dc0fb200000000000000001800c98bfa69e0da00000003af092800169804100032e09f4e4931f915499c00077d8000000d68000000000000000000012e60000000001dc0536000000000032268cb7c0f4c00025e8000000000000000000027b6159fb57fca4b7270000000abd0000000000e1d599ae59b323eb1bf8151dea6641ee838471c4f01080001df8c565771b7da0ce1215d217d2b48650d49db8db461100000001ee00019f2bb00000000000000000d5f0001ef567a00079e00009e40000002ba1c526006ce16a00000003048831d56b8743cab957686730003769a129673c48430000000709bd91838a5c1bb057d1cc00071ea934aee6d759f81a8f2ed4200012e56c894f6ea0908d6e2605e38000af45af00000000000000003e6c000000000000000000000000000000000001f200004ea0c11a480000000001eb5dd60000000001e7e98200000004b407d0a694fce7800027d86b45f20000001850fd80003ba800066ce60311800135e9d637101f000000000010b470ef740000001a9ea290000001
  | 29 => 0x2a4ac92fb33fd0ce3c21c2b48052082b3ed3050c42d8c02d2a5cc4e0006e380000000f007f2e4950ae2f00015e4664c8c4a834a9d769aa731be080000001afa9080002fd3410000000fb10003021c6822f1ebb0149be8fa57c3a4c6a20002a200012280000d01b8523adfe35a31305500004768dc80000005c48000f520002573b4c0002760000021d443aa0000b740a45b51c030a000000023ea034c9a5dc58d223c00008d41980f43ee115521a6c59b20006a9a671ca2deb0000000000000137088000000018a174800000000036f400000000000000009861b7a7dc7ca7f203a9f31e807784be800126ebd40003bb9b4400058f0000db23d34bf07b51fe3521a28c5c000bb62073a18ec41e91ea982cd360827240001f3ef680000000c78c420000000000d0f26780002040001bb82d14ceb8d000000000000013200000000000003334000c375aab11c2500000000001d0a00062d1d4c0000000000001a200001308fe8ab80001232e70116819000000180c0003a780005c8dc223c80000f68fb08b8000000b1800000000003cf102000107a6c81c9375cee4787359ab604d065a5af98480005a416335543e06d4000399956e000000386d3926bc1c100000000000003ca0000e6a4368001ba60000000000cd27166090854e5ecba000000049852b50282640001f437615306dc41928000003883c50001701aa02732cb2588d6008956301200000002da0ae431227e59e0eb44a20006c1000122e00024ca39c0000000000000182000000000021a113000072000008a0df0000c52d0c0000000000bf80003bb4a1c70e4201ba819cdc65ab8421700f510deb1100007213ceb9c4a9c00052b84c103e70376096880007091c08334ea0bdc5279e31d6890a2a4a651b90c090430000f3c3d80f32d18a68000530800000042a0002b055a64b7215a4ed1f28326f1a63080c0df5612659b0e2796d8a5a4c3005b70a1ff023c44832d8c0da8cef74f02d118fa79563622e167c87250231201226535228000598bf37bf80000005393b015980009950000000148edb0000000000739142bea40000000dd99399220002943610000000287a2d8000f9129f2fd436600079a800000087e325b58d1760004059f18a8e89b128365128a0000003ea00000dc0f11ca00320000000001cc84080000000000beb30b80009a800046b38cc0000f44f69c6cb54f0b53c318175eef0000000062246e66109d5adcd4012bb5c51b471a45baddd7a6b823aa1760482f564d21f14c4437126f19fc45604d000000126a0000000000cdc2770000000000f46798000000081b0f715d5a90b6f40abe8014adbe63b8f1065a21a074a649514ae926880041da6a543217e927078a06222acb66da10003c684860000000001caebee10b19a88142ee546006c000cd744191d906c9c6
  | 30 => 0xb86f2000000000000000000000016ead337c9a6b400000062e84bc2929ba1938a612f8f1858e00000008cb05621800007f82cb80000000000001e71b9c8f000016301ca1603f3249400000027180000000004913974e3cd660002115f5e3334b20645ec01874ed9310e0e0000001f48000000000175400000022b9d74f26000539877dee40004c18000000edc02482edbbc20a00000018c8d23367ad2c0000000001398000f9667a80012660004ea33e40003650000000000a2b3a0383c86c794000181872626a12f3061afa9876ac04d00008282bd8001f4a10a40608055ac6d03fd364800099d7839b300006c60beb6e0f9282d0003b7decc0000000000894cdf3780ef9a1c7910ac80000000cb19a2730000bcf57e06783803ff0002b7c0000002728000000745000147800000000010f18800000c98c6849200044a80392d49bc3ad38300000000000a0800019d44ea1f000046000017e1d5a7a27681b98000aa938e80000000000003d700000001b4800152c8a100000005a82b34ec800134a0007552160000f6a31d8400d1819b16c1eac00000000010ccc600000000851d886680000b640fea2336d9cb8e00d640000001d3c000649a15c0000000002385350000000041c0003211af000113e7644520000c6ad8300039e5a3400015b80016e8b0d41c31fdc300005d316680009b04028591f12e3a62d800000010f168107c0004d67c229680001c626db32c5a4ea1596acd5d168e50603d85af27b9490ad4c0005d1000200830800000000004e40f222c0c2000000000021640002d300000000000000000c4d7300960003b15808f6f0003c240009dc0000000d12b5800009b0c5823408595691049cb00008a18c2d744c5000000000000006190fadbc0003594f408c104033e87109f50f8a7096440001e697ac000c5512a01cd3bc0000cb2444b7a0004c4aeec0004751e480000009ca0002068e7a0b800000000003b80000000000d151b6ba9000098f75cb59c98a0000000001736c3a4a513644780005918001ad60003f4b7f51747275a78001e8ace600019e9680000112a63970aa192798ca40006bd00000006c6011000000000000023530c80005815dc87406b48142fe2594000a9f2ac2de489c0005073735194b833670d05d3000000000006840000001cd5c1cde64d08000150000000244cf1ca0f3a73145c64f4c56230fd6746980e3b3d15aa00000d2df80009a97a387909d87777239928000da9747375496ad1c69a80018a6cbe0000a9481665576505b1f1a1ac5458c30ede87301c34d854829f5cf860c6ae06600000d979c2f65cb91b5e40d344bfac485d49186bb001ccc486c0cfaf11c86000484a130000f0501d3d382f028d6a2827d6705fe000000053435d63904586966c02341250e1e00033a8f04332053396800
  | 31 => 0xc5e00069d97797d20006e0000000000000025d800032a0002cbc0000007c580000006c21f62258aca4b80000000c620006c58000000c230000d10000b8431280017780000003815bc81803fca0b94745ab00014bc00000000000013ae0002be00003fa00019cb9401a40003a59da964e9fe0e9a1993f69601549dd00009e9446000056c000227800122aa3218b222d6a4b360ee9d280005081eb00005c2000186847c9208bf0dc80005122090002fbcb8800073fbdf1f60cbb27e3621e3a77d3478955a0a0000003a20b408ad546868459e09c0003b9ca40000000234cbcad033280001b4a6f230abb580002994388001218fac395962547a1d700017c800000014db46c00000000024c4000000000108d45a00000028984fe5510000000aa87c31123b8c79c00066d04c800000030b00000002af209a5858360002df0000edaa8208e000000025c178aa40000c2421f800091800002fb13c000000573357400038423db288000ecd467ac252f6acb399869093e59e330800184e7cd4498000000000000225000000000029100008ef0638b6c00000000000000000706d400000000000001aa00008d10000f7dbac0ff06a00011dc000213b3cc00000079a16280000003061de59688763e72f202d0ce54e98ef5b260000c82f740000670000000000000000018000038a00032d40000000001308a28000000110800013d041bcdc00005e2ad9fa00003966108dd00000001650000e440000003984fae95242e800065ed310001ec50000003ad96540000001018000000caa00007d8bc01dc58fab89e5457646ab5350dcde276cab84000e6e00026c86560000000058000ebd0000bb11780000002a480000000910001cfae3b00000000000000001dd8192bf9787241cddc45a2e33c216f400000012700009d20000a482fc7e53ff3b1ccbac1d28a85280f45220000000d440511cd800000000000000013565716430000f3e3b900000017b40007d30c39822e3e68b987c46ca5660f15c94f692375736d5cde24f6ff9a2cccc9f6274b29d31a6f80e70e44d2a212463309447c0000bd9ce92eee4100000008f469f3b5b698ac20354f41c040508a60000001c9a0146eda3a82560005001d358fc4bf5dc0001c84c653c69b580000b0275a2a555c01e2298000f5800008700000000004ea80000005bf4100001c5037a00031c400000022eb99400092c74e8cb0000c50000000000000000031990b4c0e7b607cc7d200000000005e400014e168c00058700029b53ca000644aca400006800017a40ee0722881d9cb2090d6fc00f094a1541ce82142a200037795ac8806036c09a3802400004d2b30470d964501a40000e4f7b731a4dc808e7ac9fdcc1cf4b5d5050009ce9a0059da0b366a655b20a93bad2537487e593c0000098001b5a00
  | 32 => 0x52caf3000060d7d500000000002558001536ede0000001ae40007a200000003890003ae8000eff0001141c5a0370000efc0000ea00020dde760764f20dcc7f87b800000000007d84ec0000e4af426cd97e54be0005fda7b86920005183b3df0a34a230b964df26bf6d18f980004035618f00000c6b50933ed74038b2d91bd02b0bc66bba28c99a67000032fc0000005518000438d0a000119000000000010680007306d380007b20006b114680000006bc000001e7e40003c501561b10000ab82b8889396214971c16672232cd9d60e31358035d241e85b68000c501cc18e00010829995c5b80467a58f247b6d072062b0002b8d7e80006670000bee4f53abb63d9f089709aaed56f672000031340580000002129be2d3d34008b000033838f8e810c20fa78500c96ccebf5eb8000df80006e08001eee4e032200001c07652493068a902e9482976c00000000034c8b7674600033892900f108a3d55c3281340480bd3e2b7f7978001c0000075180001a21db0000a3c00000000000014f84450e780019527991000000000169000005c0000002183760054c0d2470649e5600000000013e47370001775038a5176480010aab16000257d2f061b7939a701eca3363b28b99eebbe5821e48000eac000321c528000000000166e9742a32544d02df25c630cd00222e28238c031a2650000001ac25561e41b140008b406613c445a8e84d015a400000000000004c4e9500035a52bc0002f9800048e0000000000000173234bc081ae0000000a1000048431c37d1f3cd2e00000007620af283ac3c0000000002bd80000000000000000bfa4892ab573cddd5830001da400063a00000000000000000000a5068c1f79220cc14528000000aa26d78000f16e5e000000000000000037b19a8000468247c000ace000000165000000000001a631f0000001ca80002bc30c4d8e00002b000000000005123e1dfc00030980080000002e8000000047300003400809c40002f2800051300038240000005d22a04c6ea2c00000000000003cd04b00000000233e1da48b3953e9a1df56f9a285800171ea400a21edc00010369d0b3532655937d3361e3e705291b6e50724b000002f00005170003e7000061e15c21340000001d715a09440007d08000f8e0000568001e82b0004ba6f40007be379a8fc5f63352608000000000497800076ea9914bb081c4edca39dac1c51695940733140940dd6010161cec81065680018540000a780000006710001ec906800010f335920c00000033191109fd263ac5c7f01d16760000f0495800004e139acfc4b780010084dc00028e000041704a000118a00024d2aa9298000358aa45dc800000036c00006ab0ad1b7168200021780cc000ec02c100000000843e583980ca4563ffae180da0007c6000000000000000010a23e30a980
  | 33 => 0x4e0f06410772a6b016400011aa4f800054f00000007b64ba562b9883ca000445093800000044700019a431000000007580003d2270000024d0000000632d130aeadcc0000003c428d09eee2a000013dde400000023f56e4cdb1dd072dd509b32e5a5194d800022f3d6123c0000001434000eef54c00000004ed63500006e0000000388400000000012bc0008473cc0000000d7c64c918d23269724980008f0a200001fd4c329bf4649b752e4870206bc945f06ff06f2ba888804c6a09074d5a3a10f60e603861e03ea1c51660b0c5b38ab5e6697916b8001db400000003683de52c0001fd1b8600004a98400000002c40000000155000188000084e0001769ade0005352f84b8202032f8d301b617c0c5883800000000034bc0000004e7963578682300032dc0000000002e5594035504600009c2110000029903ca1a0d82b356a8bc95d1acac0004b36fb99944220b300027e5d00000000173569a00000011c40000007b986d985a68403f3148e820002dc1b6003afa700000000008c204796d8000d4957d8001928f0400000016acc1554d3cf80002df4a58fd5402f384b81c498eaf6224c0001134ac758100000007e7110b25557c0005c08480aa07dd16f3d7864058e581809d86c9be17025d55b4e4b1740261f1062d64ba50dd205e1434850d3908f66df83a0aaa7b61252bc428ef1b2681050994f2128b1b482ea09e073a8dc0000002038001f5c0000000fdc0000003aa95480006604803478fb65c72f131b5c46be50001ca4b1678f5b733bc000cde29d000000025943a32c4dce8a7000000000000012fb41c07295500026887c0b456370651cb8c17129b23c4f00005a832e582cd5957e9cd15a03a32260001a725251a6a88800000074c9c8dd381e74ffb4459ecfa23009ae4d9a000531a2c4000025299167c000000000081d60270b00000000008b9000000000000000009e80000006dd0d700000001a008c5cd8f5f43ba459e2a1b55c50e98c6c00047b94ec0003b05933a10b9800002e1f0400018144380002ec0000002d9538239f000220069e39515f000000055300000002dc00000000000008500000000000000000000000000042a00009f2824000146c822df900000000007964cfa10d1804c60a73dc4f0c64805500001b028a1a32f2d302aa75d92598fe0a9c1de2d6d186f1e0000000526b59244a37174ac4e23f80006145ae3419bd8ec6af43519125a982f06642534706c2e7a917a8f4615700000000002c35ad31ede32c6369b80004e8d9700003e0f74f2c6bda0c593a49d75288e563a81716029e4fbed900bf80000000000ea2ca9044ecb3810000000000000073595cad158d80000000006c480018140003863d8d00c0003843a51cea48d43d8fbc000ba90000000000da000024696584656ab3a44000f7a2af0000a9a0
  | 34 => 0x255c000b6b23b8bb55f2c5c5fb14b4794f491f73638000b3b1ed1d1c00000000036ac29000000000000001294a380008b20314f80c48fdeeb82111c295b8c1f674b56da4e9e1496a9d0000d2d00000000000004f18ca000000056e8000000d28095352c00000000000006b200026024b8904bb0356000193ea11532b209a580000000001c48f6d1621e007565646949950000000171152c43a0000000e3dba2000000049800080a5150000b8a1a500006714825334a718d0fd42b124305b4000a280000e3400000032480015082da00033102bc2ce000018c53a000000000136c00035c1408000cc3185bc446ea89c0000000f5054352615140000ba198800142e8ac68000000000fb582a6ec5003156fd0b54d1a3a7457a189b66f98062b0e408e5ca0ec0a04f082c862088dde7290115a000025c2566931528bb208861f13d000077a0000000ed200015aa4d9bec1a81830a1ca14cca3263accb245380003cc94d2f7978639e95b61610002dc5d1e0003552c91b3000050b16e9c6cc01624800000000000010981b2a860002dc174e0000001ad9916e080773d5c57618a3228e913a241279880000006436b00000636d6c38b800000047e159000000086f0002f9d15000000000015124052f400000841c25e1000013a8300893dd84cc1720003abc00000000018900004094ab2f48000c3b0000000b58e7053d33544daf2651e28215903f90002ae9e5c56d0002af0b6e0003f7070542098b40918699da5e349816940000006743ac0d74000187800000046600027f11666fd00010304e283e55c0508000bae000379c9a4f1715f9200bc84d32c2bd9d022c431bc35fde24e89141a669998fb242306211b01b71a7264074ae02000000124e8e329300014e000048180012d64181fe800000074942985e400044b030bbb0fc0bf0474830c00000000031e40002a01f8000000000000000000000625098001c620004dcb15cf78ea05578f780000000000df0000b5e0000000000bdf4e3920c0000000002bd4000f4821e800000014c0000001c20e556d51b4c00000000037300000005b612816f03565841a68facd0205f00014760005d5afa0b22f3d0632e745ccf220003b2000036b77104440464f800000006f600012236b9c7e43a5270001cf00000000af00000006b9800020aad46580000768000258bc909ecd430003d7437e86b7918cdc0000004ad8000000cc00003c0156642500000000000004130df8000dcf014a89d32e00000027bc0b246c05086f07966fb1259f8ce480000d3a9ad90ac2f4a4800164a0005cd1a28370d1f7c90f415fe00032137240005402233
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa78845954044001c7108b2a808809f1edd1655011013f1dba2caa022000e3b435954044001c7684b2a80881369ee05655011000739c0acaa02206be3b4159540440d7ce482b2a80881af8e505655011000738a0acaa022000e3965d9140440053e103b9a80880038e5954350110014f840ee4a022000e396550940440053e50fb8a8088006ec21d4150110016d843a82a0220019b08750540440037650ca0a8088006ec219415011002f5843282a022005eb3765054044005b64eca0a808800b6c1d9415011002f583b282a022000f338550540441b3e610aa0a8088003ccdd541501106cf983aa82a0220d9eb36550540441b3e64caa0a8088367ac595415011000798b2a82a022000e3165505404400176706a0a80880036cdcd4150110005d9c1282a022000db37250540440013e10e98a8088002ec6113150110007c8a1a62a0220009f08748540440017630890a8088003e850921501100be3c3b2ca9822039b38845953044001cb0c6b2a6088136dce05654c1100beb838aca98220029f081dd130440051f10cba2608800a7c205744c1100056c432869822039f185450d30440053e103b92608800378887724c11000765996c498220048f8875893044001d92c4992608800a7ca1f714c110004f843a829822000db1745053044001f2286a0a6088006f421d314c110016e843a6298220019d0874c530440037a50c98a6088006f4219314c11002768432629822004ed3764c53044005ba4ec98a608800b741d9314c110027683b26298220d8f52654c53044001ea2ca98a6088002f4e11314c110005e8c22629822000dd3744c53044001ba2e898a608835fd4951314c1106bfa82a2629822000bd3824c53044001ba6e498a6088003b4d89314c11000768b126298220009f08748530440017a30690a6088003f04c9214c1100be3c3b2ca9022037b38845952044001cd0c4b2a4088136dce0565481100beb838aca90220029f081dd120440051f10cba2408800a7c2057448110014f840ee69022000dd231dcd20440051f10cb9a408800a7c205734811000765196c690220038f88758d20440015d10ca1240880dfca151424811000764b1a6490220029f287dc520440013e10ea0a40880036c5d14148110007d0a128290220009f0874c52044001ba2e698a4088003f04c9314811000df043a429022002de08748520440033c10e90a4088006f8a19214811000df0432429022003ee0864852044007dc6ec90a408800b789d92148110016f03b2429022003ee07648520441adec4ca90a4088003d85952148110005f1c22429022000be1844852044001bc6e890a4088003785d121481106afb12a24290220d5f605448520440017c70690a4088002f860d2148110006f1b9a429022000de1734852044001dc6c690a4088003b858d2148110
  | 1 => 0xf08baac4880162f21175589100046fc1aeab1220048dc835d5624400d0fd0bba2c4880021f61774589106962e39ca8b122000c3f74151624400b878e82a2c488353171cc54589100053ac08a8b122000a798015162440091bd0fb9ac4880031795373589100062e2a6e6b122000c5f51dcd62440018baa3b9ac48800317d4373589100062ea86e6b122000ccc73dc962440031f50fb82c48801a1f21776509100343f42ceca12200087d859d94244001878a93b284880021fe1576509100343e42aeca1220008df835d942440091b906bb2848801a1fa1476509100043ec28eca122000c3c541d942440091bd063b284880023760c76509100043ec36eaa12200097581dd542440012f301baa84880035c04375509100043f43acaa12200087c87595424400b47908b2a848800e2f21d64509101951e42ac8a1220058ec875894244001c58a8b1284880c6b320d62509100343f42cec992200087d859d93244001998653b2648800237e0d764c91000477c12ec992200687e851d932440010fb0a3b264880162fa10764c9100045ec20ec9922000ccc321d9324405b47908b2a6488003930c9654c91001c6e43ac69922003acc8258d32440091d90eb126488012b320d624c9105a63a3b6eaa0a2000d7070dd541440132e90eb2a828809f1d1d9655051004d9a422caa0a204eb7380595414404fae0e0b2a82880031de1d655051002d3a43acaa0a2000c7487595414400b0e90eb2a82880038de11655051002d3b422caa0a2005a74845954144001c6908b2a828805f1ddd165505100bf1bba2caa0a2000e37435954144001c6e84b2a828813a9de01655051000739c02caa0a20a8e37405954144151ce480b2a82882a38d50165505100071ab2ec8a0a20019f080dcd4144001c6acaa1a82880067c20372505100071ab2a84a0a20019f287dc1414404f8e8ecb2a62880facd211654c5100072a31aca98a204eb7380595314404fae0e0b2a62880067c203744c51000c7a432e898a20019f0805d131440015a90ca1a62880fbc5151434c51000cf8406e498a2000de220dc93144001d8e65b1262880123d21d624c51000762b126498a20019f287dc1314404f8e8ecb2a42880f2cd211654851000732312ca90a204eb7380595214404fae0e0b2a42880067c203744851000c7a432e890a20019f0805d121440033e101b9a4288003748c3734851000c7a432e690a20019f0805cd2144001d8c65b1a428800e3d21d6348510005724328490a203cf24545092144001d8ac699242880067ca1f70485103d63c3b6eaa022000d7071dd540440132f10eb2a808805f1e1d9655011004d9c422caa02204db7381595404402fae0e2b2a80880031ee1d655011002d3c43acaa022000c7887595404400b0f10eb2a80880038ee11655011002d3d422caa022005
  | 2 => 0xd72d91100246e41ae5b222000d7010dd564440130fd0f32ac8880161f21e655911004d1f424cab2220dba758199564441b54f30132ac8880161fa1d655911004c3e43acab222009a3c845956444151ce020b2ac88801a1fa1f755911002c3f426eab22200587c84dd564440010ff03baac8880021f60775591100043fc06eab22200087d80dd5644400117f08baac8880021fa1c75591100061e3aee8b22200993c845d7634409b2ef02baec68813a5ee0175d8d10006b8082ebb1a200087d8799763440010ff0eb2ec6880028f21165d8d100043ec3cebb1a20008bf845d7634400b17908baec68801a1fe1d75d8d100051e422ebb1a2000c3f845d7634400b0f908baec6880030f21175d8d1002c1e422ebb1a204d87f815d7634404f0fb02baec68813a1fe0175d8d100bc3ec02ebb1a200087f855d3634400d0f90aba6c6880161fe1e54d8d100043ec3ca9b1a200587f8715363440010fb0e2a6c6880170f1d054d8d100053ac08a9b1a2000a798015363440018d8e532ac6880028f2116558d1000636392cab1a2000c6e65dc963440018dacbb92c688003780437258d100045fc22eab1a20058bc845d563440011df04baac68800e3b2097558d100343f42ee8b1a200087d85dd1634419f8d8e52a2c6880030fdd05458d1002e1e3a0a8b1a20d1c6c7215163440014eb022a2c6880029e6005458d1001c7743ee4b1a2000c6e54dc963440018d8a9b92c6880031bd477258d1000636a8ee4b1a2000c6f50dc963440018daa1b92c68800333dcc7258d100343e42eeca1a200687e859d943440010fb0b3b286880030f1527650d100043fc2aeca1a200687c855d943440011df04bb2868800e3b2097650d100343f428eca1a200087d851d94344001878a83b2868800e3ba087650d1000476c10eca1a200087d86dd543440012eb03baa86880025e6037550d10006b8086eaa1a200087e8759543440010f90eb2a86880168f2116550d100245e43ac8a1a2036a3c85591434400b1b90eb1a8688003871516350d101ad66412c6a1a200687f865d7624404f0fb0cbaec4880264f21175d891026cbbc0aebb12204e97b805d76244001ae020baec4880021f61e65d89100043fc3acbb122000a3c8459762440010fb0f3aec4880022fe1175d891002c5e422ebb12200687f875d7624400147908baec4880030fe1175d891002c3e422ebb122000c3c845d7624400b07908baec4881361fe0575d891013c3ec0aebb12204e87f805d7624402f0fb00baec4880021fe1574d89100343e42ae9b12200587f8795362440010fb0f2a6c4880161fe1c54d89100043ec38a9b122005c3c7415362440014eb022a6c4880029e60054d89100062e39ccab122000a3c8459562440018b8e6b2ac4880031799773589100062eb2ee6b122000dd010dcd624400117
  | 3 => 0xb2a200587e87dd1654400b07d0fba2ca880038de0774595100071a40ee8b2a2000c3f71dd16544001c7701ba2ca880038e20374595100061fb86e8b2a2000a3e849d165440014eb033a2ca880029e60274595100053bc0ae8b2a2000a7b805d1654400b87ce83a2ca880030f5d074595100052f418e8b2a2000a5d831d165440014dd043a2ca880029b60874595100051f438e8b2a2000c3e871d16544001c3d063a2ca880038760c745951000717410e8b2a2000e2d821d16544001c6d023a2ca880038d60474595100061fb88e8b2a2000e3a801d16544001c73003a2ca880030fdc074595100061e3a6e6b2a2000a3e849cd654400147b0939aca880030f1d273595100053ac0ce6b2a2000a79809cd654400147f08b9aca880028f21173595100061e3a2e6b2a2000a6f825cd65440014d904b9aca880029de0573595100053dc02e6b2a2000c3c741cd654400b878e9a1aca880029ba0b435951000536c1686b2a2017a7681d0d65440014eb03a1aca8809e9ea0343595100053cc0686b2a200087e8790d65440010fb0f21aca880170f1d2435951002e1e3a086b2a2017a768110d65440014eb0221aca8809e9ea0043595100053cc0086b2a2000c3c74dc9654400147d09392ca880028f61272595100061e3a4e4b2a2000a75819c965440014f301392ca880028fe1172595100051e422e4b2a2000c3c745c965440014bf06b92ca880029720d72595100053bc0ae4b2a2000a7b805c96544001878e8392ca880170f1d342595100052f41e84b2a2000a5d83d09654402f4ed03a12ca880029d607425951013d3d40684b2a2000a7980d0965440010fd0f212ca880021f61e425951002e1e3a484b2a2005c3c74109654402f4ed02212ca880029d604425951013d3d40084b2a2000a7980109654419b878e9992ca8833b0f1d232595100043f43864b2a200087d870c9654400147d08192ca880028f610325951070e1e3a064b2a2017a76810c965440014eb02192ca8809e9ea0032595100053cc0064b2a204dc7687dc565440014eb09b8aca880038ddd371595100071a3a6e2b2a20e0c7770dc565441c1ce481b8aca8809f1ea1f70595100053cc26e0b2a2000e3b74dc16544001c70e9b82ca8837f1edc7705951000739b8ee0b2a20dfe7241dc1654409b2ef02baec88813a5ee0175d9110006b8082ebb22200087d8799764440134790932ec8883769d60665d91106e53cc04cbb22200087f87597644401347908b2ec88837b9c04165d91100043ec3cebb2220dda75819d764441b94f3013aec88801a1fe1d75d91100061fc22ebb222000c3c845d7644409b0ff02baec88809e1f60575d91102743fc02ebb22201787d805d7644401347d0baa6c8880030f15173d911000477c12e7b2220038ec825cf6444001878a8b96c88800237e0
  | 4 => 0x3480014f3002a6c69001a1fa177458d200043ec2ee8b1a4000a758115163480014f3002a2c69001a1fa167650d200043ec2ceca1a400087f855d9434800d0f90abb286900023de057650d200147a40aeca1a40048bc87591434806d4790ab22869001637a1f6350d200070e2a6c6a1a40d0c6c76dd542481a365d09baa84900035a1c375509202b59742ec8a1240e5d2c54dcd42480033d101b9a849015acb215435092018f4631a86a1240019e880dc542480033d50fb828490393ca153705092065e6631ee899240018ec865d132480aba58a8ba264900c73318d744c92000cf4402e89924004ace86d8d32480010ff0aba6c29001a1f21574d85200053ac08a9b0a4000a79801536148001c58a8a16c290013331cd32d85200053ac0ceca8a4000a3f845d9514805547908bb2a29000297e0d765452014d2e41aeca8a4000a77815d951480010fd0fb22a2900021f61f645452006e1e3a6c8a8a400087f8759151480010f90eb22a2900029de0563545200153a40ac6a8a4027a6c86509514801ba58e8a12a29009eda201425452013d3643264a8a4029e4c634c9514800d0fd0b3b282900021f61676505200145e43ac8a0a4056d2c75509414801b2e90ea8a82900ab8d99151505200071ab22a2a0a4000f2542545414800d0fd0a3b262900021f614764c52002c5f420ec98a40008bd841d931480051b90eb1a6290003331d9324c52000c76432e890a40019e8805d121480051d90eb22429000ab92056448520006e5186e690a40018ec865cd2148001d8c63b1a429000a3b21d634852000762b1a6290a4000ad88650d30480099b0eca1a6090143c6151434c120004f443a849824003ce87650930480a1e50a8a126090003e250d424c12000de443a649824003dc8874c930480037950c9926090006f2219324c12002764432649824004ecb764c93048007b94ec992609000f721d9324c120027643b2649824003cc8764c93048001797089926090002f2611324c12071fa52a26498240e3f48544c9304800179702992609038bd2d45324c120006e4996e29824000ec932d8530480518f0eca8a6090003d24c9514c120005e4c1a429824000fc131485304801327d0fba2ca880030fddb745951000798086e8b2a2000c3f761d16544001e60203a2ca880170f1d264595105453ac0cc8b2a206ba7980991654400b878e8322ca8800297a0c64595100052ec18c8b2a2000a6e8219165440014db04322ca880030f1d263595100051f420c6b2a2000a3d8418d6544001878e831aca880029ba08635951000536c10c6b2a2000c3c74989654400147d08312ca880028f61062595100061e3a0c4b2a2000a5e8318965440014bb06312ca880034ddd371595100069a3a6e2b2a2000d3b74dc16544001a70e9b82ca8809edca077059510006b9b8ee
  | 5 => 0x6ace21171541400069dba2e2a828000d38745c550500e12f10fb0aa0a01c31e1db6154140004bdc3ac2a8280139788758550500138f0ecb0aa0a012acee1161541406d73830ac2a828000d3b8750550500016750ea0aa0a0002ce21d41541400069c43a82a828001b3a8650550500036710ca0aa0a00174e9d9415414002e9c3b282a828000b3b83505505000167704a0aa0a0126cee0541541400d799c0a82a8280dad3b7150550500d7e64e2a0aa0a0003cc5c5415414000799b0a82a82806bf306150550500438f0ec98aa0a006acea1131541400059cc2262a828000f19434c5505003b8f0ec90aa0a006acea1121541400059cc2242a828000f294248550500010fb0f3aec8983ae9e60275d91300343fc3aebb22600087f815d7644c1d50ff00baec8980661f60175d91300246e41ae5b22600687f87d47644c0010fb0fa8ec89801a1fa1f75591300043ec0eeab22600087f80dd5644c0010fb01baac8980021fa1c75591300043f43ea2b22600687c87d45644c1a78b8edbaa8698352c7a137550d30006ac386eaa1a6066b1e85d91434c1d3a38a9b928698006762037250d3000cec406e2a1a60019da87dc1434c1d1e30a9b8286980021fe1574d89300343e42ae9b126000a7581153624c0014f3002a6c49801a1fa1676509300043ec2ceca1260038bc87591424c0654790ab22849819b471d543509301af4631286a1260058ee87d89424c001c58a9b1284983273318b744c93000c6e432e89926063d1c545d1324c06b998c4ba2649800676201744c93001d67436c4992600087f855d3614c00d0f90aba6c2980029d60454d85300053cc00a9b0a6000e1c5450f614c007998e4996c2980029d60676545300051fc22eca8a602aa3c845d9514c0014df04bb2a2980a29b20976545300053bc0aeca8a600087e87d91514c0010fb0fb22a2980470f1d364545300043fc3ac8a8a600087c87591514c04f4b90ca1aa298047471d1435453013dac40286a8a6027a5c864c9514c051c98c4992a29801a1fa1676505300043ec2ceca0a60028bc87591414c0cda38eaa1a82980465d21d51505301571b322a2a0a6000e3564545414c001e2a86a8a829800637219744c53000cec402e898a60028dc87591314c0055a902b22629800372883724c5300076310ec498a600687e851d9214c0010fb0a3b242980162fa1076485300045ec20ec90a60018dc865cd214c001998ec99242980021f61e75d912073d3cc04ebb22400687f875d764480010ff02baec89039a1fe0175d91200c43ec02ebb2240038ec825cf644800d0ff0fa8ec8900021f61f51d91200343f43eeab22400087d81dd564480010ff01baac8900021f60375591200043f438eab22400087e87d45644800d0f90fa8ac8900021fe1574d8d200343e42ae9b1a4000a75811536
  | 6 => 0x63d080eca8a8000c79101d9515004f4790ca1aa2a00030f1d9435454013d1e43284a8a8000c3c7650951500554f10cb82a2a03c6dce05705454059e1e3b6eaa0a8079c3c76d95415000b66d0ea8a82a0016cd21d51505400071bc32a2a0a8000b368654541500016690ca8a82a00038d21951505400171bbb2a2a0a8002e34765454150001c6ec6a8a82a00038dd8951505406dd9bc02a2a0a80a8f32805454150001e6300a8a82a02a3cc1c1515054025f1bb02a2a0a802af33605454150001e62a3b8282a001a1fa17764c5400043ec2eec98a80018bc865d13150147c38caa1a62a001a1fa1776485400043ec2eec90a80018bc865d1215012dc58caa1242a01eecea1f74541400d69d43ee8a828001b3a86dd150500036710dba2a0a006b4e9db74541400d69c3b6e8a828000b3983dd1505000167305ba2a0a0002ce60774541404663c3b6e6a82801ab3884dcd50500014f70cb9aa0a006a9e21973541400963c3b2e6a828000b3b845cd505003567108b9aa0a01e31e1db6354140004bdc3ac6a8280139788758d50500238f0ecb1aa0a01a2cee1163541407872c31ac6a828000d3b8750d50500016750ea1aa0a0002ce21d43541400069c43a86a828001b3a8650d50500036710ca1aa0a00db8edd9435414002e9d3b286a828005d387650d5050035c70eca1aa0a00170e1d9435414033d9dc1a86a82801af1b8350d50500dbe34e6a1aa0a0003c65cd43541400078db1a86a82806df186350d505000167704a1aa0a03bfc68c9435414036f8c19286a828000b3b8150d50500dbe3662a1aa0a02171e1db72541400d59c426e4a828000a7b865c950500354f10cb92a0a003b1e1d972541400059dc22e4a82801ab38845c950500e98f0edb12a0a00025ee1d625414009cbc43ac4a82800dc787658950500b967708b12a0a03bb9a18962541400069dc3a84a828000b3a8750950500016710ea12a0a00034e21d425414000d9d43284a828001b38865095050065c76eca12a0a00174e9d9425414002e9c3b284a82801ae3876509505000b870eca12a0a0002cee0d42541402dd9dc1284a82801af2b8250950500d9e54e4a12a0a0003ca5c9425414000795b1284a82806cf286250950501dbe5664a12a0a01b3ca0c942541400059dc0a84a82806cf2b21509505005b8f0ec992a0a006acea1132541400059cc2264a82806cf48324c950500fd8f0edb8aa0a006ace21371541400069dba6e2a828000d3874dc550501d92f50db8aa0a00034ee13715414002cbd426e2a82800597884dc55050001a7109b8aa0a01371ed93715414026e9db26e2a828000d3b43dc55050001a7287b8aa0a00034ed0b71541400069ca16e2a82802797981dc550500d7a7683b8aa0a00029ee1971541400d53c432e2a82800ac78765c5505000167708b8aa0a
  | 7 => 0x4c724c931540012f301bb242a80024fe1176485500d49e422ec90aa00095f835d921540332b906bb242a80025ee0176485500043f436e890aa00087d86dd1215403b878c9ba242a80021fe1974485500043e432e890aa00097b805cd21540032f100b9a42a805e5b21d42485500ef163228490aa017b6481509215402f2d90e99242a8067531cd32485500c4ba43a6290aa000f45324c521540df2f700b8ecaa004e1f61c61d95400052f418c3b2a8000a5d8318765500014dd0430ecaa00029b60861d95400063ab88c3b2a807aa3e841cf65500f347b0839ecaa01ea8fa1072d95403cd1ec20e5b2a800087e870cb65500010fb0e196caa01ea8fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa01e69ea0032d95400053cc0065b2a800587e845c7655000b0f908b8ecaa01be1fe0171d95403d51f420e3b2a8079a3d841c765500014bd0638ecaa00029760c71d954000537410e3b2a8000a6d821c765500f34f50038ecaa01ea9e60071d95400043f43c63b2a800087d878c765500010fd0e18ecaa00021f61c31d95403d51f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d95403cd3d40063b2a8000a79800c765500010fd0f10ecaa00021f61e21d95400043f43843b2a800087d8708765500f547d0810ecaa00028f61021d95400052f41843b2a8000a5d8308765500f34f50010ecaa00029e60021d954079e1e3a0cbb1a80048bc845d763500010fd0fb2ac6a00021fa1c6558d407ad1f436eaa1a80d2c3c76dd543501e747d0db2a86a01e70f1db6550d400070e32ec6a1a8000c3c65dc9435000b33b07b9286a03cf0f1d065d894001c5e422ebb128004c9e7350f62500010fd0fb2ac4a00021fa1c65589407a51f436eaa1280cfc3c76dd542501e747d0db2a84a01e70f1db65509400061e32ee6a1280059ad82dcd425000755d05b1a84a00038b19762509400343f42eec992800087d85dd93250001c9865b2a64a00062f219744c9400061e32ae89928076d8c325d132500014eb03baec2a00029d60475d85403853cc00ebb0a800087f855cf615000d0f90ab9ec2a00db0f1d543d85400043fc2ae5b0a800687c855cb6150065878eaa16c2a001a1fa1b75585403cc3e436eab0a800087e87d9561500010fd0e32ac2a03cb0fdd065585400043f434eca8a8000a75819d951500018eb033b2a2a00031d90676545400063aa0ceca8a800587d809d9515000147f08bb2a2a00029de05765454002c3f420eca8a800587c841d9515000187e863b2a2a00030fd0876545400343fc08eca8a800687d811d9515000187e823b2a2a00031d90476545400061ea08eca8a8000c75411d9515000b0ff003b2a2a00031ea00765454002c3ec00eca8a8000c79801d9515000187c803b2a2a00030f10076545400
  | 8 => 0x43a6c2a80029d60474d855026d3d400e9b0aa07ea79801d361540014eb03b9ec2a80028fa1273d85500051ec24e7b0aa04da7a809cf61541f94f30139ec2a80029d60473d855002e1e3a687b0aa000a6e82d0f61540014db05a1ec2a81369ea0343d85500053cc0687b0aa00087e8790f61540010fb0f21ec2a80021fe1d43d85500043e43a87b0aa005c3c7450f615409b4f50021ec2a80029e60043d85500053ac0ee5b0aa000a3e849cb615400147b09396c2a81369ea0272d85507dd3cc04e5b0aa000a75811cb615400b878e9a16c2a800297a0f42d85500052ec1e85b0aa04da7a80d0b61540014f301a16c2a80021fa1e42d85500043ec3c85b0aa00087f8750b61540010f90ea16c2a80170f1d142d855026d3d40085b0aa000a798010b61540010fd0e196c2a80021f61c32d85500051f42065b0aa000a3d840cb6154001c9a64196c2a805e9da0432d85500053ac0865b0aa04da7a800cb61540014f300196c2a80065e20374585500d49f43ee8b0aa000c3d86dd16154001a7701ba2c2a80034e20374585500061fb06e8b0aa000d3b60dd1615400187eec3a2c2a80021fa1f64585500d61e3a6c8b0aa000e3641d91615400b878e9322c2a805e9da0664585507d53cc04c8b0aa01787c875916154035878e8b22c2a80030fdd0645855002e1e3a0c8b0aa000a5e8319161540014bb06322c2a80029ba08645855000536c10c8b0aa017a76811916154001c6c82322c2a80030f1d363585500051f424c6b0aa000a3d8498d6154001878e931ac2a83e69e60263585500bc3e43ac6b0aa000c3c7458d6154001878e831ac2a80030f1d362585500051f424c4b0aa000a3d849896154001878e9312c2a83e29e60262585500bc3e43ac4b0aa000c3c745896154001878e8312c2a80065ea1f70585500069dba6e0b0aa000d3874dc161541efae6e3b82c2a80025e603765055002c3ec0eeca0aa000c7980dd941540018f481bb282a80021fa1a76505500049fc22eca0aa00097b805d9415400b0fd083b282a80161f21076505500061fa18eca0aa000c3f421d9415400b0ff023b282a80031da04765055002c3ec08eca0aa000c75811d9415400187c823b282a80030f10476505500343fc00eca0aa00687d801d9415400187e803b282a80031e90076505500061ea00eca0aa000c79401d941540018ee203b282a80031d44076505500bc9e43a86a0aa000c3c7650d415402f2790ea1282a80030f1d942505500d4ba43ac2a0aa0f6b738058541540012f301bb262a80024fe11764c5500d49e422ec98aa00096f825d931540312d904bb262a80025ee01764c5500043f436e898aa00087d86dd13154043878c9ba262a80021fe19744c5500043e432e898aa01795c8750d3154043c38c8a1a62a805ed5205434c5500bcae43a6498aa018d
  | 9 => 0x324c521006e2996e098a420087f855d3604840d0f90aba6c0908029d60454d81210053cc00a9b024200e2c5450b6048409998e6996c090803b14c931d812144cbdc02e7b22a001978805cf64541052f700b96c8a80065e20172d91503e4bdc02e3b22a001978805c7645400b87ced20ec8a840f4edd370591500cc3ec38c9b1aa005c3e7419363540334bd06326c6a80029b60864d8d500053ac08c9b1aa005c3c74991635400b87ce8322c6a806697a0c6458d5000536c10c8b1aa000a75811916354205ab6e7b82c6a80025e6037650d500061f426eca1aa000c3d84dd943540010fb03bb286a80031e6037650d500063d206eca1aa00087e869d943540012f700bb286a800317a0c7650d500062ec18eca1aa000c3f421d943540010fb023b286a801a1fe007650d500343ec00eca1aa000c3f401d943540018f4803b286a80030f5007650d500063ca00eca1aa000c5f301d943540018ba603b286a80664fa1f6450d5002d1f436c8a1aa01a95c8758d4354001c38c8b1a86a8406d6e016350d5066e1e326e4a1aa01a95d83dc943540310fb0e326c4a80170f9d064d89500052ec18c9b12a018a6e8219362540014eb02326c4a80621f61f63d895002e1e3a4c8b12a005c3e7419162540014bb06322c4a80629ba0864589500053ac08c8b12a01887c8758d6254201ad6e5b82c4a80025e60376509500061f426eca12a000c3d84dd942540010fb03bb284a80031e60376509500063d206eca12a00087e869d942540012f700bb284a80030fd0c765095000637410eca12a000c6d821d942540010fb023b284a801a1fe0076509500343ec00eca12a000c3f401d942540018f4803b284a80030f50076509500063ca00eca12a000c6f201d942540018da403b284a80624fa1f645095002d1f436c8a12a0cec3c64dcd42540352db05b9a84a80624f21d43509500051e43286a12a000c3c7650d425410fe1864a1a84a806a5b21d625095000716322c4a12a0ffb6b80589425403527d09bb264a80024f613764c950004bcc06ec992a00097b805d932540010fd0dba264a80021f61b744c9507f6a6196e8992a00087f865d132540010f90cba264a80b70f191744c95043ea6192e8992a01787d87d9361541fb4f301326c2a80021fe1d64d85500bc3ec38c9b0aa005c3e74193615400187ae8326c2a800297a0c64d85500052ec18c9b0aa000a6e8219361540014db04326c2a805e1f61f63d85500051f424c7b0aa000a3d8498f61541f94f30131ec2a805e1f61c63d85500bc3ec3ec5b0aa000a3e8498b615400147b09316c2a83ee9e60262d85500bc3ec38c5b0aa000a7581dd3615409b4f5013a6c2a83f69e60274d855002c3fc3ae9b0aa005c3e741d3615400187ae83a6c2a800297a0c74d85500052ec18e9b0aa000a6e821d361540014db
  | 10 => 0xb028200a7980dd760504df4eb023aec0a08029e60075d81410043fc2ae7b02820687c855cf605046d878eaa1ec0a08021fe1572d81410343e42ae5b028232c3c7550b605040d0fd0dbaac0a0ace1f21b75581410043f43ecab02820087e87195605061d87ee832ac0a089a5d21d515814104d3a432a2b02824cd37745456050551ce0c0a8ac0a08021f61e75d913186d3ac0cebb22620687f875d7644c6190ff02baec8988a61f60575d91310043fc02ebb22620687f87d43644c4010fb0fa86c89881a1fa1f75591310043fc0eeab22620087d81dd5644c4010fb01baac8988021fa1c75591310043f43ea0b22620687c87d41644c5a78b8edbaa8698b52c7a137550d31006aa38eeaa1a62a3b1e85d91434c617a38a9b92869880a752077250d31014eb43ee2a1a630af1454dc5434c4053a903b8286988021fe1574d89310343e42ae9b126200a7581153624c4014f3002a6c49881a1fa1676509310043ec2ceca1262038bc87591424c4654790ab228498a8f471d543509311af4631286a1262058ee87d89424c401c58a9b128498b273318b744c9310146e432e899262a0d1c545d1324c46b998c4ba2649880a75205744c93101d67436c4992620087f855d3604c40d0f90aba6c0988029d60454d81310053cc00a9b026200e1c5450f604c407998e4996c0988021f61e75d912184d3ac0cebb22420687f875d764486110ff02baec8908a21f60575d91210043fc02ebb22420687f87d4364484010fb0fa86c89081a1fa1f75591210043fc0eeab22420087d81dd564484010fb01baac8908021fa1c75591210043f43ea0b22420687c87d4164484010ff0aba6c69081a1f21574d8d210053ac08a9b1a4200a7980153634840d0fd0bba2c6908021f6177458d210053ac08a8b1a4200a7980151634840d0fd0b3b286908021f6167650d210043fc2aeca1a420687c855d943484011f700bb286908063e2017650d210245e43ac8a1a4236a3c85591434840b1bd0fb1a8690803871536350d21686363b6eaa1242d1b2e84dd54248401ac8e3baa8490a5acba17645092183e962a6e6a1242029e481dcd424852d6590aa1a84908c7a318d4350921014f343ee2a124306f2454dc542484053c903b828490b2f3318f744c92101476432e89924295d2c545d13248463998c6ba2649080a79205744c92102567436c69924200ad48650d31484099a8eca1a6290a4fc5151434c521004f243a8498a4203ce4765093148527e48a8a126290803e150d424c521015e243a6498a4203dc4874c9314840578d0c992629080af1219324c521027624326498a4204ec7764c93148407b8cec992629080f711d9324c521027623b26498a4203cc4764c9314840178f089926290802f1611324c52182fa32a26498a4305f44544c9314840178f009926290c13d1d41
  | 11 => 0x505674ed02106caa08029d60420d954189e1e3a0cbb1a820087e87d9563504010fd0e32ac6a0c568fa1b7550d416961e3b6eaa1a8313a3e86d954350567878edb2a86a0803871976350d410061e32ee4a1a820599d83dc94350627878e832ec4a0813279cd43d89410043f43ecab12820087e87195625062947d0dbaa84a0b3f0f1db755094189d1f436caa1282b3c3c76d954250401878cbb9a84a08166b60b735094101d57416c6a128200e2c65d89425040d0fd0bbb264a08021f617764c94100726196ca99282028bc865d13250401878caba264a0ac3630c9744c9415ad9b43ee8a8a822ad3687dd1515040566d0dba2a2a080acd21b74545411569b3b6e8a8a822ad3476dd1515040166b07ba2a2a0802cd60b74545410059ac06e8a8a82c2c7476dcd515045566909b9aa2a08029de1973545411553a432e6a8a8222c74765cd515040166f08b9aa2a08aacd21173545415963a3b6c6a8a82009778758d515044d2e90eb1aa2a08871d1d9635454152d9bc22c6a8a8312e546358d5150401a6f0ea1aa2a0802cda1d43545410059a43a86a8a8200d348750d515040566d0ca1aa2a080acd21943545411b71bbb286a8a8205d367650d515040ba68eca1aa2a08ab8d1d9435454102e1a3b286a8a82a4b378350d5150455e2f06a1aa2a0aabc59cd43545410078ab9a86a8a8200f176350d5150555e28c6a1aa2a0802cde09435454188f8b19286a8a82aaf143250d515040166f00a1aa2a0aabc5cc143545415de3a3b6e4a8a822ab3484dc951504014ef0cb92a2a08aa9d21972545410f63a3b2e4a8a8200b37845c9515045566908b92a2a0abb1d1db6254541004bbc3ac4a8a822697487589515043b8e8ecb12a2a0a72cde11625454188732312c4a8a8200d3787509515040166d0ea12a2a0802cd21d42545410069a43a84a8a8202b368650951504056690ca12a2a08cb8ddd9425454102e9b3b284a8a8205d34765095150455c68eca12a2a08170d1d942545410059bc1a84a8a829bb37825095150455e4f04a12a2a0aa7c99c9425454100792b9284a8a8200f27625095150553e48c4a12a2a0c3fc9cc9425454154f9219284a8a8200b37805095150553e4e40a12a2a08b71d1d932545411559b42264a8a8200b35844c95150553e8864992a2a09f31d1db70545411559a426e0a8a8200d3774dc15150401a68e9b82a2a0bb25da1b70545410069bc26e0a8a820597684dc1515040b2e909b82a2a08034d21370545412763bb26e0a8a824ed3764dc15150401a6e87b82a2a08034d50f70545410069ba16e0a8a8200d3542dc1515042f2eb01b82a2a0aa34dd0370545410053bc32e0a8a822aa74865c151504158e8ecb82a2a0802cde1170545411559a422e0a8a8200d37745c15150401a68e8b82a2a09be5d21d51d814137d3a432a3
  | 12 => 0x9f29d60474d81510053cc00e9b02a200a7980dcf605440147d0939ec0a88028f61273d815113d3b40ce7b02a31aa75819cf60544014f30039ec0a88170f1d343d81510053741687b02a200a6d82d0f605449d4ed03a1ec0a88029d60743d81510043f43c87b02a20087d8790f60544010ff0ea1ec0a88021f21d43d815102e1e3a287b02a24ea768110f60544014eb0221ec0a88029e60372d81510051f424e5b02a200a3d849cb605444f4ed03396c0a8c669d60672d81510053cc00e5b02a205c3c74d0b60544014bd07a16c0a88029760f42d81512753b40e85b02a200a7581d0b60544010fd0f216c0a88021f61e42d81510043fc3a85b02a20087c8750b605440b878e8a16c0a893a9da0442d81510053ac0885b02a20087e870cb60544010fb0e196c0a88028fa1032d81510051ec2065b02a200e4d320cb605449d4ed02196c0a88029d60432d815113d3d40065b02a200a79800cb60544052e903ba2c0a88aa4fa1f74581510061ec36e8b02a200d3781dd16054401a6903ba2c0a88030fd8774581510069bb0ee8b02a200c3f761d160544010fd0fb22c0a88ab0f1d364581510071d206c8b02a205c3c7499160546314eb03322c0a889e9ea02645815113c3e43ac8b02a22ac3c74591605440187ee8322c0a88170f1d064581510052f418c8b02a200a5d8319160544014dd04322c0a88029b608645815113d3d400c8b02a200e3a401916054401878e9b1ac0a88028fa1263581510051ec24c6b02a200c3c7498d605462f4eb0331ac0a889e1f21d63581510061e3a2c6b02a200c3c7418d6054401878e9b12c0a88028fa1262581510051ec24c4b02a200c3c74989605462d4eb03312c0a889e1f21d62581510061e3a2c4b02a200c3c741896054401a6ee9b8ac0a88034d1d37158151014bd43ec0b02a2f7d7371d8160544e12ef02b86caa089a1f61c60d95410052f418c1b2a8200a5d8318365504014dd04306caa08029b60860d95410063cb80c1b2a82b4a3e841cf655056747b0839ecaa0ad28fa1072d954159d1ec20e5b2a820087e870cb65504010fb0e196caa0ad28fa1032d95410051ec2065b2a82b3a76810cb65504014eb02196caa08029ea0032d95410053cc0065b2a820587e845c3655040b0f908b86caa09c21fe0570d95415a51f420e1b2a82b3a3d841c365504014bd06386caa08029760c70d954100537410e1b2a8200a6d821c365505674ed02386caa0ad29d60470d95410043f43c61b2a820087d878c365504010fd0e186caa08021f61c30d95415a51f42061b2a8200a3d840c365504014dd04186caa08029b60830d954159d3b40861b2a8200a75810c365504010fd0f106caa08021f61e20d95410043f43841b2a820087d87083655056947d08106caa08028f61020d95410052f41841b2a8200a5d8308365
  | 13 => 0x43fc2ae9b02640687c855d3604c80b87ce82a6c0990030f5d054d81320053ac08a9b026400a7980153604c8014f301a8ec0992fe5de0573d9151014ba40ae7b22a2b8977815cb64544052e902b96c8a89fa5de0570d9151014ba40ae1b22a205c3e769036454643a6ee9b8ac8a88a61f61c64d8d5102e1f3a0c9b1aa229a5e8319363544014db04326c6a88029e60064d8d5102e1e3a4c8b1aa205c3e7419163544534bd06322c6a88029b6086458d510053cc00c8b1aa320d5773dc563544012eb03bb286a88030fa137650d510061ec26eca1aa200c7581dd943544018ec83bb286a88021f6037650d510043f434eca1aa200977815d943544018bd063b286a88031760c7650d510061fa10eca1aa20687f811d9435440d0fb023b286a88030fd047650d510063b208eca1aa200c3d411d943544018ea823b286a880317cc47650d510062e988eca1aa20087d801d9435445327d0fb2286a88168fa1b6450d51154ae43ac6a1aa200e1c6458d435463f6af02b1a86a8b370f1937250d51154aec1ee4a1aa22887d87193625440b87ce8326c4a88029760c64d895114537410c9b12a200a798019362544510fb0fb1ec4a88170f1d2645895102e1f3a0c8b12a200a5d8319162544514dd04322c4a88029e60064589511443e43ac6b12a31ed6772dc562544012eb03bb284a88030fa1376509510061ec26eca12a200c7581dd942544018ec83bb284a88021f60376509510043f434eca12a200977815d9425440187e863b284a88031ba08765095100636c10eca12a20687f811d9425440d0fb023b284a88030fd0476509510063b208eca12a200c3d411d942544018ea823b284a88031bc84765095100636908eca12a20087d801d9425445127d0fb2284a88168fa1b64509516761e326e6a12a22a96d82dcd42544512790ea1a84a88028f21943509510061e3b286a12a2bdf0c3250d42544552d90eb1284a88038b19162509518edb3c0ac4a12a22a93e84dd9325440127b09bb264a88025d607764c951004bbc0aec992a20087e86dd132544010fb0dba264a8c73530cb744c9510043fc32e8992a20087c865d1325445b878c8ba264a8af7530c9744c95113c3ec3ec9b02a31ba758199360544010ff0eb26c0a889e1f61c64d815102e1f3a0c9b02a200c3d7419360544014bd06326c0a88029760c64d815100537410c9b02a200a6d82193605444f0fb0fb1ec0a88028fa1263d81510051ec24c7b02a31aa758198f605444f0fb0e31ec0a889e1f61f62d81510051f424c5b02a200a3d8498b60546334eb03316c0a889e1f61c62d81510053cc06e9b02a227a76819d360546374eb033a6c0a88161fe1d74d815102e1f3a0e9b02a200c3d741d360544014bd063a6c0a88029760c74d815100537410e9b02a200a6d821d3605449d4ed023a6c0a8
  | 14 => 0xd745c365508010ff02b86caa13428fa1070d954267d1ec20e1b2a8400a5e831c365508014bb06386caa133e9ba0870d954268536c10e1b2a8400a76811c365508014eb02386caa10021fa1e30d95420043ec3c61b2a840087e870c365508010fb0e186caa13428fa1030d95420051ec2061b2a84cfa6e820c365508014db04186caa10029da0430d95420053ac0861b2a840087e87c4365508010fb0f886caa10031d5c710d95420043f43c21b2a840087d8784365508018f2e1086caa10021fa1c10d95420043ec3821b2a84d0a3e84043655080147b08086caa100297a0c10d95420052ec1821b2a84cfa6e8204365508014db04086caa13431b5cb65d8d4295e1e3a0cbb1a852bc6d72197635080717b09baec6a10030f15375d8d4202c76c16ebb1a84cea3e85d53635080b95ae5aa6c6a133a8f21351d8d4299636b96a3b1a84cea3c84d436350a638dae5a86c6a10021fa1f6558d4295726196cab1a840087e871956350a61c986432ac6a14be4fa1f7550d429751f436eaa1a84d2c3c76dd54350a5be1865baa86a14b24fa1f6550d4295d1f436caa1a84cfc3c76d954350a55e1865b2a86a1003871976350d42006963aee4a1a8435b8e83dc943508652790bb8a86a10ca4f2177050d4201c5ec26ebb0a84ada3e84dd761508014eb03baec2a10029d60475d85420043fc2ae7b0a840687c855cf615086d878eaa1ec2a10021fe1570d85420343e42ae1b0a840087e87d4361508010fd0fb2ac2a10021fa1c655854201c5ec26ebb028473a3e84dd760508014f301baec0a10029e60075d81420043fc2ae7b02840687c855cf605086d878eaa1ec0a10021fe1571d81420343e42ae3b02840087e87d47605080d0fd0dbaac0a133e1f21b755814202c9f426eab02840087e87d9560508010fd0e32ac0a1003530c975d91320043ec3cebb226400e4c329d7644c80d0ff0ebaec899003930c975d91320043fc0aebb22640087f805d7644c80d0ff0fa8ec8990021f61f51d913294f26196a3b22640687f87d43644c8010fb0fa86c8994a3930cb50d9132006a6196eab22640687e87dd5644c801c9865baac8990030fa1375591320061ec26eab22640087d81dd5644c8010fb01baac8990021fa1c755913200726190eab226400a3e85dd1644ca4fd1865ba2c8990022fa1f545913216d1f42ea8b226526e8c32d51644ca4bc38a9b9ac8994938b15372591321ad6741ee4b22640087e87d45644c80d0f90fa8ac8990b68f213515913291f26196a2b22640087e87d41644c80d0f90fa82c8990b68f213505913291726196a0b2264058be84dd7614c80117b09baec2990021fe1574d85320343e42ae9b0a6405c3e74153614c80187ae82a6c2990029d60454d85320053cc00a9b0a6400a7581d43614c80b17d09baec0990022f61375d813200
  | 15 => 0x438ecaa18029ea0071d95430053cc00e3b2a860087e878876550c010fb0f10ecaa18021fa1c21d95430043ec3843b2a86d3a3e840876550c0147b0810ecaa1b4a97a0c21d95430052ec1843b2a8600a7a800876550c014f30010ecaa1b4e8fa1370d95436951ec26e1b2a8600c3d74dc36550c0187ae8b86caa18021fe0570d954369d1f420e1b2a86d2a3d841c36550da54bd06386caa1b4e9760c70d954300537410e1b2a8600a6d821c36550c014ed02386caa18029d60470d95430043f43c41b2a860087d878836550c010fd0e106caa18021f61c20d954369d1f42041b2a8600a3d840836550da54bd06106caa18029760c20d95430053b40841b2a8600a75810836550c010fd0f886caa18021f61f10d95430063ab8e21b2a860087e878436550c010fb0f086caa18031e5c210d95430043f43821b2a860087d870436550da747d08086caa18028f61010d95436952f41821b2a8600a5d830436550c014dd04086caa18029b60810d954369e2eb9ecbb12872fc3c741976250e5f8bae632ec4a18122f61375d89430061e2a6ebb1286058dd83dd76250d9b47d0baa6c4a1817275cf54d894366d1e426a3b128732c5d73d476250d9b47909a86c4a1cc7175cf50d89430043f43ecab12872de4c32d956250c010fd0e32ac4a1ccf930c865589430245ec26ebb0a86b1a3e84dd76150c014eb03baec2a18029d60475d85430043fc2ae5b0a860687c855cb6150c010ff0ab86c2a181a1f21570d85430043f43ea1b0a860087e87d956150c010fd0e32ac2a18122f61375d81433bd1f426ebb028600a7980dd76050c014f3003aec0a18021fe1572d81430343e42ae5b02860087f855c76050c0d0f90ab8ec0a18021fa1f51d81430343f436eab0286d287c86dd56050c0b27d09baac0a18021fa1f65581430043f438cab0286d1d2e74ccb655080b27d08b8ecaa10ca1f61c61d95420052f418c3b2a8400a5d8318765508018eae230ecaa10029ea0061d95420053cc00c3b2a840593e845c365508650fb0e306caa100297a0c60d95420052ec18c1b2a8400a768118365508014eb02306caa10031e5c060d95426851f426e7b2a84cfa3d84dcf655099f4dd05b9ecaa13429b60b73d95420061f3a2e7b2a84d0a3e841cf655099f47b0839ecaa13428fa1371d954267d1ec26e3b2a8400c3d74dc7655080187ae8b8ecaa10021fe0171d95426851f420e3b2a84cfa3d841c765508014bd0638ecaa10029760c71d954267d37410e3b2a84d0a6d821c765508014f50038ecaa10029e60071d95420043f43c63b2a840087d878c765508010fd0e18ecaa10021f61c31d95426851f42063b2a8400a3d840c7655099f4dd0418ecaa10029b60831d95420053d40063b2a8400a79800c765509a147d09b86caa133e8f61370d95420061eba6e1b2a8400c3
  | 16 => 0x3000000000803c00c01803801403402000c00001000c00800806c0040040040040f402c02000002c00800800400004804c07c00801404002411c06004403c00000400000801800006c00400000006400c0180f41800dc00400400426800800800000400401015c08c06400c00000012400400800403c08c00c01401401c00c0180c409002402001403400400400000800804c00404000803008c08800800c12006c00801c03402c01000000c00000000405800406800801800800000001402c0a801000001400000400400800c15c0140040000100240980a01e000804001000c01c00000000c0f408801800800405006003c06004c00000401802400000000000c00401c04400001409402802c02801802002001800406400824c0580040200080100a807c00800000408801401403409408800000c04406000000401000003801400c00400004c05000400002400000001804c01001c0100000000280040440280700500000040400b82b40100200100040902700140000700000400040180080340001b004c01000401003c02400002000003c03407c01c01001400000400407000003800000001400800403c00400c00c0f400c01400000004c00003400000000000c00803800000403400402c00400003404800000011400000401401c0080000500100000000d401002800018400c00c0c80140080600040040100040100680000040f804c00002c02400804000000801402400001001400000800000004400402000002401400400000c00801800c01401c0000140280180540f009400001c00800004002400401000805c00801000400800000c02000c01400000013c0140480c801801402807000000001001000c09806c01000800003c08413803000401c00800c03000003c01000802002800005402800800c04403005801412400000000004800000001000000c0240380bc1200000180080f004400400000c00403000c0dc00001400001002005c0780040040000080000c80400000000000000000100040080101a801c00400400800804c01401404402400003c03c01401400c03402000800403803c024000051a9a3ce9196caa18164fa1171d95431b43ec38c3b2a8600a6e821876550c014db0430ecaa18031d5c461d95430053d400c3b2a8600a79801876550c0b27d08b86caa18da1f61c60d954300537410c1b2a8600a6d821836550c014ed02306caa18029d60460d95430063cb80c1b2a86d3a3e84dcb6550da547b09b96caa1b4a97a0f72d954369d2ec1ee5b2a8600c3e745cb6550da747d08396caa1b4a8f61072d954369d1f426e3b2a86d2a3d84dc76550c0187ae9b8ecaa18030f5d171d95430043fc02e3b2a86d3a3e841c76550da547b0838ecaa1b4a97a0c71d954369d2ec18e3b2a8600a6e821c76550c014db0
  | 17 => 0x5a0e201f120d9e1475c83b3e9a19cd2e40344504c46306b00409ea81487144598b110168701ab00e00005221340ad000057c00000000004c32a592e45bc8612f11f040420e3304139898e5e03188bf05ac0970000f440000000740000000000000000000000000006ccd7e51b00000000223de2ca99609202fa0001224de66340d5a01878e43810f83f86f22ea3ab9270ed63f5000141c89a15d2e590749ce0ad37b0000ddc5304109c38fc484824c1ce49e006740d0fb4000000000000070477c2a2048000000012b80c86c87ef338091c2f2000000078c00000003a050c00000045380000000000e2199cc560001480000000105000058400021d2f5213cb9200034512c84500e61b49af059a23301b84100006a82e3a15874206f300885c71806102d89bc37e8a9383800000081e0001ac42ce48f0d002b8a042732b693e838e3f005d0b4cede23d0f49b000008c70449d942823541db92f043652d3688000e140002f195c00000aa0001208aec50a0809a004bc1810000b3c0005b000015604220003e500003bc67e00010b06f089b3010a4cfda0001d300008ec4800000b7cf523ba086813cee8579000000000018000018d86c41f61c914e114000008513381d867600014e85903a23f280005723ac3289644f5e4072f90614ec03a53718940e46000103159110c3020b500b400036e4298228fcc00000000000001cf146800000060425219800887153430f9cae215e0000014de258a1d20bf41e24621950ef040800000002f00001c802500c40006ac13c000095833d45893c40000db28999f48b023518f0ea0f4e00e01d9f9c8160d600004a8940000000035d13817341300000001b80001184276858420a2d4d90000452000000000042b942cf800001ad88ec58a1173a3a07cbca5ec000185cb9c64e15f0fdc0008131790f4c0004ef0000010794000000000800003c0040380140080580280000100080a40000380100000140cc0200000081a800401003401401c02c00400000005402c0a800400000c0000000000000340cc00400400002404400000801000000400c02400004800800800801405400000002002c00001c03c03c01404000000000800000006c00006c02400c01411c0000580000000140000000000000040e002004805800c0400c003c00800003401000000006c01404c0d80180780f002802800401400000403c00007c0f802402005800400801401c00800800000000007401000002400806000800001000402001800814401000006000001002c02800403803000c01000003803402400c00c02c10400c0280000140000041c800000802416403401405c00005800005c0200000180000000201040000640000080041cc01003c05800000009400803000008002c00401801001800803001c04003005800400c0040d
  | 18 => 0x22d1c59cc84266a017b191cd3a1280000e1470c3421a7140076c82d1011a78dfc5490cf05686fa3bd1120cccac030404b072c2280c135b9a2112c2420d4112c82e00b3728a1c28c4361978fd8ace84d0d305544ba6e100008dc2902aa16d1b2800000019f00009b602440e0378dcc0000210db026400011c8608000642460080496e45d000063094e0302e91c10f7089a019826891a3b8062976435a1a3000226053200024c97b80002f43cd82940004f51ac80000000001c095f80345df3578ae000024e0000aace4a000238016403878d36819648721180001ddc00040e44f00007e65d03800e5000044900004d8166000000015c48a2911470000a8479623d21380001622541660004230421a058a7c31c1772110be200029014f506a21c1b1893c3861aa29587f062265302422a852e8972d901a04442101149d041f611b21403f08982642d619502f44642aa0b603242842af9e649a64000ac8cb42dc5d11bf9a351741f3331024ccd23e13810be47dc0452711cacfae48829c8a7072a1d10000fa80003b221d119c0007f73b520b8f884ad1869c487c015f0511cd8a0c00814a95945de19f0f0a1a4e0c4eb003a03847079e3fd074c45480145f91400007794579e986bc60e0ec99951560ff0391540c4202b39b8a3c1ba8473398000fe27b60e69c7d0fc83f16e00004888074570c8800031543d126c02a0002d41c2ce18367355122c0000eb308800018c50d38b9c3c67600000b9840b204b3420216c0000003a2027800042d3479af800000045419f0e9e8c901ca0dcf5037100e991001e0000f90c585a0882000000000073421d858ca8251c2ce228ca8c43224f886084a0e70eba0a0dd48bd2790f5c71451d0310c64dc418b0c211006460f726804f902e47b02720ac3ba67813307a037458735c92e84c40630fb8fbc70e00035391203266bb0ea8dd10fa7e118f987c2263f4000179d07487800000004f46eb4448b64e7e45c2bf80011826900771410ec22533b60024b7084b441800000c0000000f708d86a20890cb0e3c23f000000000000000000000004aa013000089c00045b19280002fe0001608cc200000006647a86b518e80000000000000000a6605f45a16d43a844a30e2240ebe00020613705fe57d16d9e911246161cf853ca2c1330ac0a7482459214513fcb8a4f638087606f85f443598748fa4720160724a0624a0018c6c8fc6200a6938cbd00903fe89c4a5446d04798fc21c82a1e81440fa40101ed18681166da1ee8ca4e9255227712ac26a0d241e015035c4c941798350364ea3c5089892c792126937c60e1d21bd9d980823c943322e449602f386990cc4e16011d21311861a21c989a466a6681c79168b7826311721fc37a1c20301f3c55e05d0a116cc9628681921b1c19e2433ca9c843800003b19214a020001290
  | 19 => 0x8094fd024039e9798c5c7052da1558a4a7b900017905ca5181ea8f306e48503d103100001a92f996bcee245329a11e0ec45a942c82640ca629450888ce5e0b000c10fc20e0190be9c70de08153841dcd0c05211b692d8b287ac0ee04fcee40000f71b7879c60a1071b5cda65c426000004620000001ac8e5400024391990b871b26216984d87283748368b1278c12d968454432135d13b09fc43117a83c0c127d63de170c6280360000d4000000000012c00740000a60218db08842130fed0583051c19438d020003ff800000041400000000000003ac843000077a0000000f986b82c280000007b70bf8000efe7e43a991f000000037d80000006a53509e4c1805a200006f01042491881d5097a5a40ff099cb0c0a01ac04b48c01ea2d3828510a4a21991040bc20f238c1958ab21541a98ca05f08722970ee4fd20bb2c591781ca2a70c899c845e0200290000cdc7884100780d0a4cd09700008041370a99034bb60000000330a120001d99b7c0002561f5800000007d00016200004e90001cc4eac82504e08780002c023789600005140e6111cbac7222cf03a90ba0000001ff8a9a2ba0ef80008143e82c98000f9018d3320000d9200005e82fc000875336800000033400000006ea4681ad1f181e60003c3800091887b31a854456a3300000000f2e5bd46301b09f879137b8d0400012900019040008bc1da20306c056200002e1188000000063cc187ae28d20410b438d000187878834d10a21e4b1c4bf2b78d98d8c30042a1dc11181700dd8ce0ff063c3ec90dc24e10623522ec0aa3991f11a6899642a40c13dc7520fa2ae1c8088403d1b586d899088e20d03bcbda20a36700580ea6dd1fc8880fe006e2bb8cfc85e56345c0af0a8a742042147cd246392e016945c82e913e0a0c97012b15e9a4d0ec23e1c4906034e1f020414a0fe64a641820443385b91df064064018916194a4fd434b1b51e389ba76702018182cc8321aa9d90f28457176914822c2ce36287f4a621ce2ae925436427715194549d055131202c457e7b228795008a25d43bc01a4cd47b51f190b8d3e0b402d20143480c20a38ba000026e2889b480003bf0001898d1c00003207b118474d16e909cfa83521e683902d63f22d00000b945572938000c5e7c700001d87f83430a70000f1275e1069464fb45f51c81fd80007de08e0fe000063a14d00002420001241ad079e00018595b8d6c0000b905e00007553269d6800004b2181f74e3a74800011c40003250cc00004106dc31b9284dda3683421fb0eea4f434101e508c2d143280004e85f723a00002120830000000e120002a70d180000b71d380004d4000000042c64c00013e9bc860c65739a92ec04419b2f801ccb542e624e9328bd61ac00000000284d63930000000203200814c41e0c83cd0000f9a08702b1bfc146
  | 20 => 0x600007114151584d105394dc0fe05e1e294f0d9800000000002884431848d950324c60000d1071c79f0001ef85a46980530d843f088743513ec08654c17890f000083e08018a044e7034250dd88d230e02800000360000000830b7c78003f13680f82ad00000000923e526c20e0b8c00010016fce984f82a780a80000003bf1e0886a1b036d800043446e00018c82204860000cd8000834399a31489e38801f1eb43684210fca09095c7464320d74d961942a9974d02868320314b10f84110d09facc7a11f21f0e007e24413e485940007bb01f96b8ab42542f7935ceb0196000055c3ca4b509e0ec003e0000001b900000000000b1c2a46481c20364e7883619e00008447d53388790b9e0000ab07ecb1e2b7000125c5300003199fecd4c0002021f080002a11d597209260712e68c6824c00030285900004810001db48b20002610260a3c49145904750c64461719f70f2000000000000005f8179816000080917b811c0006952c0a0ccf9c66c4019b0c3722a00a505b4bf41743a19e3c19225500005707b60000000000ce859a000130517c62c02619dc4e410244e9a5052827b2c187d0abc77d377800415e66314d882c55c49e0001be811a47f04710a4e3252310a8b3000079d3741ff013a2c21759c68f1672e27e811824a53527085c40002091429ec49a40944441394bb45dc1eb0eb4a7e8311a40e7454c2161ce0f2cd565fd16a03b43ac7a11a003f40686752ff04e06ee6b32ff9b9cea222b4398df8ad00ca3fc9d40dea2792a383701560b92159dd90446fd1cc0f009c05c20a012680524f929b2298c4a8230ed1ed038c57b37c0b2ce4e6142b5861c9c88003de9b5856600010c848c6a260f23b8a482d20f61ec1658dc001e0d89ce883886d3a298887d218311916c43b675c33d85f02ea396135949825841f20782a473c6c13ce2328bba5bb0b60bb0b820001808a9000000000000000002c6421014501a18603506dc8c65d739d800055800015d99008327cb3e88dbd0043e6413800061e0000001a447f400012f9bd00000be14486bcc8a0000000cb8ef67291f61c4d0de0f900003600001f500015cc868275251a1543f40b60001ab87825f944a02a000032b0001be43da8c83a91d382106873cc045516e88f04298542064150d29f8d0e20e9026847819a1341d5222ccba20531185bcc266960920714af026517d80000000000708350458000323203c4985694148ec483c34a41c8000c920d10000b2448c13d34ca204cfe035000000056213933c8000ae40b50bd89f8bbc0d012e1a90b18345366833821e6c23e29c4475e74b40200005e052422a80a007837a3c088943c474044a95e872e2b02101c581243700061a70bf827f3e19cb114a2590a81e942443a0160944826059726c960046c0001ec88d0e607a33fa227ced086223c
  | 21 => 0x32d80005647e030d909091406b0000c307be53b0050000c2489143a034c4a234c2d58a94d7a17e11e16e800073816b8ffc0000002221948f7e86e00980010a472d000037c00056608d117cd363b50489664daa1eb08c9d2852c3fd4669a2412a64f00003d4fdc6fc4249ee80004af000152899859b3ef96342740000c41b10a5e0003d0000088a00000010140007ab300133d100000000000000048331c00007fc899000102402400041e800000000d3ed9730bb000036a1754100000193958462e35f1f20000f0c00032e104c67430a3ae80000b849431f01dc0000000f3809c00009b0000000c606cf00013b42220c71710000c326a919881b4cd6543011800000000016a852400059d0000b8501427634584bc0001be254830c5020003f91978a6455b0000d1c32e6d918412f85c075b286193038200040e8000c7619d000000000045612099bc96861821983807360003ec00011600000441ec0000000173916ce4839a07a000000000000006548ea4d41e10000ad842323582b0296212000168c00000032596d91260000000668b0887737621b060634928b9ab4ad400030380001640004289a308a83c62f4999800037324707bccf42821e922343cc3370bb937836a3a314f0d703fe3bb2398968d462211461940f082613e8232ca1014504f8c4908a76e144019840e2700c718a8b5a7830000aa098a55545683e078641614301c0bec28b1a78c4ccbe59f32d0f2072226039f09b40001d00000000f668cc154800000000023298b46ae5b742f00b82ec5753fa980c59429f40912946722b606a9210a9080821e86282b600003c032c000000000182c9e600032a80000008a23b480009aa000000217c5005fb03d000011800024900000000002ba07280f
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x15319404375509100055464c10dd5424400156192043755091002c0f25087595424400b82c87151625091099e8320c5458942440016259115162509100058a64054589424400b03c94616764c91000531644329d932440014c9900ca764c91000433660321d9324400188d840c8764c91000531644321d932440014c9900c8764c9109a683210325953244001645910c9654c91000592640325953244001551931c375505100055864870dd5414400b07698e1d65505100060d21f84595414400b8348721165505100058564c84595414400162592211655051002e0d21f43595414400162592d0d65505100058c64343595414400b83487d0965505100058564f42595414400163190d09655051004d0d25d65d91414400b43497595435051002d0d25d6550941440016159418d654c510006852106359531440016459218d654c510006851508650d31440012c592219434c5100253125d624c9314400162594189654851000689210625952144001645931896548510006891508650921440012c593219424851001d3125d634c92144001551931c775501100055864871dd5404400b07a98e1d65501100060e21f84595404400b8388721165501100058664c84595404400162992211655011002e0e21f43595404400162992d0d65501100058c64743595404400b83887d0965501100058664f42595404400163191d09655011002c9c26141595404400b87087505655011002e8c21141595404401343897597645011002d0e25d6550d404400b43897595425011059e4c21f8550540440f393087dd5415011004ccc26165505404401353097595415011013e4c21d655054044001a3398595415011002d8c261655054044001a309859541501100070ce5d65505404400b63297595415011002d8c25d655054044001c3097595415011000c6c25d844c540440031b097611215011000586650635953044001a188418d654c11000592648635953044001a1854219434c110004b26488650d30440094c897589324c1100146c26174505304404f95087595314c11013e94219654c5304402fc5076595314c1106bdc4251654c530440031d097611314c11000cb4259844c530440051d0985d1314c11001534259744c530440011b19421d214c11000c7425d8348530440019c0874c9214c1100058a650625952044001a288418965481100059264c625952044001a28542194248110004b264c8650920440074c89758d32481100146c2617450520440011b19421d314811001474261734c520440019c0874c9314811013e5821d65485204404fa608659521481100bf181d96548520441ab72094595214811000c7825d8448520440032e0966112148110014782617448520440054e0965d1214811000c7825d8348520440051e0985cd2148110
  | 1 => 0x147121d93254530480013329804374595100054ca5c10dd16544001711930437459510005c864810dd165440013319804074595100054ca5c101d16544001711930407459510005c8648101d1654400b81c74a0c645951002e071d183191654400b82c74a08645951002e0b1d1821916544001835811d063595100060e6007418d654400182c74a0863595100060b1d18218d6544001835811d062595100060e60074189654400181c74a0c6259510006071d183189654426d932811d3705951013c5c66371dc165440014369720774595100068ce0780dd1654400143a97203745951002e071d2831d1654400b81c7460c745951002e0b1d2821d1654400b82c74608745951002d0d246871d1654400b43890a1c74595100068360d821d16544001a1583604745951000689609811d16544001a198360074595100068a609801d16544001a318160074595100060b1d3825cd654400182c74209735951002e0b1d282d0d654400b82c7460b4359510006071d3835c9654400181c7420d725951002e071d283d09654400b81c7460f425951002c0f251870c9654400b03c97a1032595100040f25d840c965440018347460432595100060e1d1800c965440011729804175d91100054c650105d764440015519304175d911000558648105d764440014359115173d91100050e640545cf644400182c54e0973d91100050d644545cb64440014399015172d911000607153835cb64440015319404375591100055464c10dd564440015619204375591100045ca60105d763440015319404175d8d109ae4c210105d763440015519304175d8d1000558648105d7634400b03c9461e65d8d1002c0f25187153634400182c841c96558d100050b25165dc963440011e2980437258d100056865010dc963440015c1930437258d100060ddd1811516344001864726045458d100060edd1801516344001868726005458d100051964454dc96344001469901537258d100050d644549d94344001439901527650d100040f660541d9434400182c546087650d100045c66010dd54344001531940437550d100055464c10dd54344001561920437550d1002e0721c5458d4344261a0c821516350d10005856445458d4344001619901516350d100045ca60105d762440015319404175d89109ae4c210105d762440015519304175d891000558648105d7624400b03c9461e65d891002c0f25187153624400181c841cd65589100050725165dcd62440011d29804373589100056465010dcd62440015c19204373589100060ddd18115162440018547360454589100060edd18015162440018587360054589100051564454dcd62440014599015373589100050d644549d942440014399015276509100040f660541d9424400181c5460c76509100045c66010dd54244
  | 2 => 0x8401619901536350d210055164c71dd54248401561901c775509211af211d94350931485938c476e11324c5210147125d844c931484052c496611324c5211ae311d9844c9314860bb0454611324c521005896445450b60484016299015142d812100516642831d9435400143990d087650d5000706501301d9435400160d921916350d50005856446458d435400143990d0c76509500051a642821d94254001c294048076509500058364c6458942540016259119162509500060d5d1811d3615400b82c7460b43d855002e071d183d0b6154001a453260432d8550006924c9800cb615400183687907645855002e071d283191615400b81c7460c645855002e0b1d282191615400b82c7460864585500040f25d8498d615400b03f981d263585500040f25d84989615400b03f981d262585500050b64b431d9415400141d93d0876505500051c642811d9415400b8358190476505500050764c411d9415400142d9210476505500050e640411d9415400b83581d00765055002e1c606401d9415400b8358150076505500070c501101d94154031944874c9314855079e0760c65dc943501e782d8219773509400059164432d953250001649900cb654c940007030c8655d1325000b0779850676545400050b64b431d9515000141d93d08765454002e0e603411d9515000b87180904765454002e0e601411d9515000147191a00765454002e0e602401d9515000141d9310076545400050b648401d951500014359110076545400070c505101d9515005563096601515054002d0ea5b8750d5050035318985cd43541409c7061d97350d50500f1c1876d8d435414066e0e1db8250d505003531993e09435414002d0ea5b87509505019d83876e0d42541400d4ca64b835095050035328985c942541409bf0a1d97250950500e9c2876d8942541400044e25d844c9505005b83876611325414077ec20c9844c95050001519931d371541400054a64874dc5505000153191e1371541400054664c84dc550500015299221371541400054c64484dc5505000152992d0f71541400054664f42dc5505000183876e1171541400d60e21b745c5505000b838861d171541400054664c745c55050001529921d1715414002c1ea5b875855050035330985c5415414010f061d9434c5505003bc287650921541400055264870dd5434c001551911c37550d300058964454d89424c001629901536250930005856445450f614c0016199015143d853008e4521d43545414c001615911536350d200058664054d8d4348001549931c375509200055864470dd542480016259115142d85200058a6405450b614801b9248750951505201af221d94350930481938c876e11324c12000c7225d844c930480032c896611324c1201ae321d9844c930481c7b0854611324c12
  | 3 => 0x88c30ecbe9e60028200000b2000b49900998023000dc8004280003401000000040e0000202405000000000700c000041e0040301c00018010040500007064050380201c040080e02c0c0081d01c0000806010040040800000000250240303c00000000000b0042a00018020000000300418004000200a004040580f008080000a0480600803028010140a0000e00c0706000014030900000c1400001004070100d0280403c0103807038000241000c0f0040200001004000100f0240001c000040a030160000900801024020000a00800008040061c5c5801876550c01871815c060d954302e0760c54dd76250c018717160061d95420061c60570183655080b82d8215375d8d4200551644325d7644c801549900c975d913200493660329d7644c801645910ca75d913200592640329d7644c801645910c975d913200592640325d7644c801545910cb75591320055264032dd5644c801645910cb75591320059264032dd5644ca5da0c840c8755913200591644321d5644c801649900c87559132006830ca85dd1644c80b8367460454d85320060d5d181153614c80b83a7460054d85320060e5d180153614c80b8367460454d81320060d5d181153604c80b83a7460054d81320060e5d180153604c80145591a0c7650d510050d647421d94354401c15414c47650d51005836486458d4354401619901916350d510050d647431d9425440146591a08765095100709505211d9425440160d9319162509510058a6406458942544018397460074d815102e0b1d182d0f605440b81c7460f42d8151006914c9810cb6054401a493260032d81510060ea1e40d91605440b81c74a0c645815102e071d183191605440b82c74a08645815102e0b1d182191605440103c97612635815102c0fe607498d605440103c97612625815102c0fe6074989605462781d831977250d4189e0b60865dcd4250401645910cb654c9410059264032d953250401c0c32195744c94102d0da5b8750d5150455314985cd43545419d7051d97350d5150565c1476d8d435454166e0d1db8250d515045531593e09435454102d0da5b87509515059d83476e0d4254541154c964b835095150455324985c942545419cf091d972509515055dc2476d8942545410044d25d844c9515045b83476611325454188ec10c9844c95150401515931d370545410054964874dc1515040153190e1370545410054564c84dc151504015259221370545410054c64084dc1515040152592d0f70545410054564f42dc1515040183476e1170545411560d21b745c1515040b834861d170545410054564c745c15150401525921d170545410055164871dd5434c401551901c77550d310058964454d89424c401629901536250931005856445450f604c4016199015143d81310058564454d8d434
  | 4 => 0xd40f8228000000000290ce130d8818bd8f2631a8001b4788002e0ee091109129e3db100011e0c04e018ba80a625e9645d8b6002c22780050334b6ad01d9063a87e371d48d01cdd0b00009acf01ed4a6a970004080aab20c4994e1d1a2000480002a1e33ab629ad11f6002ba578009d000b985e00000cb8009e000da36438000059ea4035e002144309c1b8a40b354c3b46a888e02348361986c20e00038a0266c2800bf292a9328318e80496e60836daa6c162bc30b30a12220023e9a1f20012c9920a6ab327293ab1af8c080076250d8300471b6670d089a4a648e48780000296001fa5c03c848283f2f0280c8dc000422ee031320007c0000000160721e41328aaa16a730a68b1480025450800612a015000ac80000000398924f8008db24000641a070cf8006f00061a760f9c211000458007a1660005a00000002306c8e2002d4b79960036600000c728c0023c56034000006e060002100000096000d299e51800492ea5cb2c000fadb894712186f97e5a04aae1d07b12a001ac94aecbc80000320000801e8c4109dc001201997c810204f1544d152c500032a069cb4cc7abe9685644800001de002202b9fe5d000802ceb29d64a0100012e001ae000a8c1a46052b02084678188c8a0890326463181a9226eb4e0015600000b31da0c9f8aa80000022542b4922320000090a2a7ba600eb5a7f270868f0872f4ca81aa1ab6681a4aba2ebf80089000c200000000000cc6680030104b7342958f45280456b56589a6a980093800b0000000005e00073800c68882fa7a0000014000d700036a4c000aa0000034a167d0fe5b0861b28e28b40a71c0db0b42b0d4533169f0023395c263760000003800c10001c800003129780000358000000000000000450002cae00000025800b580000000b90007c040ba0de000008a0002f18e4e2380019414a7e00000748624688471a98510d624000a52e24385c62936cda6eb123a0b800002
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x42a0000664a385a00000a000000282e44026e42001e0c6c0000343e36186a000000001c00620014240080004e007a0826640000743200000040000030107872000050004612562c4c7e003a7000221a4868525c7c5e5820003c760e1606540060000000102000408080020c08400040000004001112ec81211910c8755913297641108c80643aac89900220da90ca85dd1644c801502d086542ee8b226400a8268032a17745913200481b52190caba264a0802c05a10c8655d13250669a02c886432ae89928200b0268032195744c94102e0290cc98e8b82a2a081702486648745c15150401206d486432ae89928000b0168432195744c94000581340190caba264a04d3409900c8655d1325000b80c433263a2e2a828005c0a219921d171541409b42654f4c021ba2ca880031128764c10dd1654400189143b24086e8b2a2000a0968454e0973d9110005053402a704b9ec888002815a1153835cb644400140cd00a9c1ae5b22200084c2a19404175d8d1000622108c9820baec68800312084648105d76344001016d4908392cab1a2000c81209911516350d1000641104c80a8b1a8688002130a8650105d7624400188842326082ebb122000c482119204175d891000403b52420e6b2ac4880032048364454589424400190441b202a2c4a122000c21611910c8764c91000611308c80643b264880032048464432595324400190442320192ca9922005c0521d93211655051002e0490ec9108b2a82880170248764b43595414400b80a43b27a12caa0a2000c846408418d654c51000640908c90c6b2a6288002215a91508650d31440019022a3244328698a2000c8864084189654851000640908c98c4b2a4288002225a91508650921440019022a3264328490a2005c0621d93211655011002e0510ec9108b2a80880170288764b43595404400b80c43b27a12caa022005c0c26097595415011000642322420c6b2a60880032088464863595304400110cd48a8432869822000c8215192219434c11000644322420c4b2a40880032088464c625952044001114d48a8432849022000c82151932194248110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x61100000004405b968432195744c9410064019168032195744c9410064019068432195744c940004409b968032195744c940
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x98a
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0xa0e
  | 20 => 0xa0a
  | 21 => 0xa0b
  | 22 => 0xa0c
  | 23 => 0xa4a
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0xb09
  | 28 => 0xb0c
  | 29 => 0xb0d
  | 30 => 0xb0e
  | 31 => 0xb49
  | 32 => 0xb4b
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0xb89
  | 36 => 0xb8b
  | 37 => 0xb8c
  | 38 => 0xb8e
  | 39 => 0xbc9
  | 40 => 0xbcb
  | 41 => 0xbcc
  | 42 => 0xbcd
  | 43 => 0xcc9
  | 44 => 0xcca
  | 45 => 0xccd
  | 46 => 0xcce
  | 47 => 0xd09
  | 48 => 0xd0a
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0xe89
  | 52 => 0xe8a
  | 53 => 0xe8b
  | 54 => 0xe8e
  | 55 => 0x98955
  | 56 => 0x98956
  | 57 => 0x9c955
  | 58 => 0x9c956
  | 59 => 0xa0956
  | 60 => 0xb0955
  | 61 => 0xb0956
  | 62 => 0xb4955
  | 63 => 0xb4956
  | 64 => 0xb8956
  | 65 => 0x1549
  | 66 => 0x1409
  | 67 => 0x150a
  | 68 => 0x128a
  | 69 => 0x16c9
  | 70 => 0x1449
  | 71 => 0x168a
  | 72 => 0x12ca
  | 73 => 0x1849
  | 74 => 0x1489
  | 75 => 0x180a
  | 76 => 0x130a
  | 77 => 0x19c9
  | 78 => 0x198a
  | 79 => 0x9c996
  | 80 => 0x9c995
  | 81 => 0xb0995
  | 82 => 0x138b
  | 83 => 0x124b
  | 84 => 0xcc996
  | 85 => 0xcc995
  | 86 => 0xd0996
  | 87 => 0x1709
  | 88 => 0x15c9
  | 89 => 0x168b
  | 90 => 0x12cb
  | 91 => 0x1889
  | 92 => 0x1609
  | 93 => 0x180b
  | 94 => 0x130b
  | 95 => 0xb49d5
  | 96 => 0x138c
  | 97 => 0x124c
  | 98 => 0xcc9d6
  | 99 => 0xcc9d5
  | 100 => 0x150c
  | 101 => 0x128c
  | 102 => 0xe89d6
  | 103 => 0x18c9
  | 104 => 0x1789
  | 105 => 0x180c
  | 106 => 0x130c
  | 107 => 0xa4a12
  | 108 => 0xa4a13
  | 109 => 0xa4a14
  | 110 => 0xb8a16
  | 111 => 0x138d
  | 112 => 0x124d
  | 113 => 0xd0a16
  | 114 => 0xd0a14
  | 115 => 0x150d
  | 116 => 0x128d
  | 117 => 0xe8a16
  | 118 => 0xe8a13
  | 119 => 0x168d
  | 120 => 0x12cd
  | 121 => 0x1949
  | 122 => 0x134d
  | 123 => 0x749
  | 124 => 0x138e
  | 125 => 0x14c9
  | 126 => 0x124e
  | 127 => 0x2c9
  | 128 => 0xd0a54
  | 129 => 0xd49
  | 130 => 0x150e
  | 131 => 0x1a09
  | 132 => 0x1649
  | 133 => 0x128e
  | 134 => 0x449
  | 135 => 0xe8a53
  | 136 => 0xec9
  | 137 => 0x168e
  | 138 => 0x1a49
  | 139 => 0x17c9
  | 140 => 0x12ce
  | 141 => 0x5c9
  | 142 => 0x1049
  | 143 => 0x180e
  | 144 => 0x1a89
  | 145 => 0x130e
  | 146 => 0xb4b16
  | 147 => 0xb4b15
  | 148 => 0xccb16
  | 149 => 0xccb15
  | 150 => 0xd0b16
  | 151 => 0x170a
  | 152 => 0x15ca
  | 153 => 0x16cb
  | 154 => 0x144b
  | 155 => 0x188a
  | 156 => 0x160a
  | 157 => 0x184b
  | 158 => 0x148b
  | 159 => 0xccb56
  | 160 => 0xccb55
  | 161 => 0x154c
  | 162 => 0x140c
  | 163 => 0xe8b56
  | 164 => 0x18ca
  | 165 => 0x178a
  | 166 => 0x184c
  | 167 => 0x148c
  | 168 => 0xbcb91
  | 169 => 0xbcb93
  | 170 => 0xbcb94
  | 171 => 0xd0b96
  | 172 => 0xd0b94
  | 173 => 0x154d
  | 174 => 0x140d
  | 175 => 0xe8b96
  | 176 => 0xe8b93
  | 177 => 0x16cd
  | 178 => 0x144d
  | 179 => 0x194a
  | 180 => 0x14cd
  | 181 => 0x74a
  | 182 => 0xd0bd4
  | 183 => 0xd4a
  | 184 => 0x154e
  | 185 => 0x1a0a
  | 186 => 0x164a
  | 187 => 0x140e
  | 188 => 0x44a
  | 189 => 0xe8bd3
  | 190 => 0xeca
  | 191 => 0x16ce
  | 192 => 0x1a4a
  | 193 => 0x17ca
  | 194 => 0x144e
  | 195 => 0x5ca
  | 196 => 0x104a
  | 197 => 0x184e
  | 198 => 0x1a8a
  | 199 => 0x148e
  | 200 => 0x18cb
  | 201 => 0x178b
  | 202 => 0x188c
  | 203 => 0x160c
  | 204 => 0xe8d16
  | 205 => 0x170d
  | 206 => 0x15cd
  | 207 => 0x194b
  | 208 => 0x164d
  | 209 => 0x74b
  | 210 => 0x194c
  | 211 => 0x17cd
  | 212 => 0x74c
  | 213 => 0xb09895d
  | 214 => 0xb09895e
  | 215 => 0xb49c95d
  | 216 => 0xb49c95e
  | 217 => 0xb8a095e
  | 218 => 0xa0a52
  | 219 => 0xb8bd1
  | 220 => 0x130a52
  | 221 => 0x148bd1
  | 222 => 0xbd491
  | 223 => 0x198a52
  | 224 => 0x19cbd1
  | 225 => 0x3cd
  | 226 => 0xcc9c99e
  | 227 => 0xcc9c99d
  | 228 => 0x150995
  | 229 => 0x15c995
  | 230 => 0x198b
  | 231 => 0x130a53
  | 232 => 0x1689d5
  | 233 => 0x1709d5
  | 234 => 0x198c
  | 235 => 0x130a54
  | 236 => 0x4d
  | 237 => 0xd0a4a1c
  | 238 => 0xa0a53
  | 239 => 0xe8a4a1b
  | 240 => 0xa0a54
  | 241 => 0xa1256
  | 242 => 0x75491
  | 243 => 0x14d
  | 244 => 0xd0751
  | 245 => 0xe8751
  | 246 => 0xb9396
  | 247 => 0x139256
  | 248 => 0x94996
  | 249 => 0x949d6
  | 250 => 0x94a16
  | 251 => 0x124996
  | 252 => 0x1249d6
  | 253 => 0x124a16
  | 254 => 0x178a53
  | 255 => 0xd1516
  | 256 => 0x151296
  | 257 => 0xe9696
  | 258 => 0x1692d6
  | 259 => 0x181316
  | 260 => 0xccb4b1e
  | 261 => 0xccb4b1d
  | 262 => 0x154b15
  | 263 => 0x15cb15
  | 264 => 0x19cb
  | 265 => 0x148bd3
  | 266 => 0x16cb55
  | 267 => 0x170b55
  | 268 => 0x19cc
  | 269 => 0x148bd4
  | 270 => 0x75312
  | 271 => 0xd0bcb9c
  | 272 => 0xb8bd3
  | 273 => 0xe8bcb9b
  | 274 => 0xb8bd4
  | 275 => 0x2cd
  | 276 => 0xd0752
  | 277 => 0xe8752
  | 278 => 0x94b16
  | 279 => 0x94b56
  | 280 => 0x94b96
  | 281 => 0x138b16
  | 282 => 0x138b56
  | 283 => 0x138b96
  | 284 => 0x178bd3
  | 285 => 0xd1556
  | 286 => 0x155416
  | 287 => 0xe96d6
  | 288 => 0x16d456
  | 289 => 0x185496
  | 290 => 0x198e93
  | 291 => 0x19ce93
  | 292 => 0x170cd5
  | 293 => 0x15ccd5
  | 294 => 0x1a8e93
  | 295 => 0x178e93
  | 296 => 0x199793
  | 297 => 0x19d793
  | 298 => 0x194e93
  | 299 => 0x44d
  | 300 => 0xd0754
  | 301 => 0x194d14
  | 302 => 0xe8753
  | 303 => 0x5cd
  | 304 => 0x74e93
  | 305 => 0x198d
  | 306 => 0x19cd
  | 307 => 0x74d14
  | 308 => 0x3ccd5
  | 309 => 0x4955
  | 310 => 0x94055
  | 311 => 0x98d16
  | 312 => 0x9ce96
  | 313 => 0xb0d16
  | 314 => 0xb4e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1185
  | 6 => 4019
  | 5 => 2254
  | 4 => 444
  | 3 => 65
  | 2 => 4
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (48190+((h/395+packedAt gbK7 (43845+(h % 395)*11) 11) % 1565)*12) 12
  | 6 => packedAt gbK6 (210319+((h/1339+packedAt gbK6 (192912+(h % 1339)*13) 13) % 5835)*13) 13
  | 5 => packedAt gbK5 (141998+((h/751+packedAt gbK5 (132986+(h % 751)*12) 12) % 2705)*13) 13
  | 4 => packedAt gbK4 (32560+((h/148+packedAt gbK4 (31080+(h % 148)*10) 10) % 586)*10) 10
  | 3 => packedAt gbK3 (5412+((h/21+packedAt gbK3 (5265+(h % 21)*7) 7) % 103)*8) 8
  | 2 => packedAt gbK2 (372+((h/1+packedAt gbK2 (368+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3801c71f8fcc478fc3c7070fe1fc1033c530cf
  | 1 => 0xc00e07e3f1f078f1fc3807f0fe1c20cccac333
  | 2 => 0xff803fe3f80fe003ff800ffe0c30f330c3c
  | 3 => 0xffffc003fff00003fffff000303f03c0fc0
  | 4 => 0xfff00000003fffffffc000000003fc003ff000
  | 5 => 0xffffffffffc00000000000000003ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8804104824001024201010420881011401045
  | 1 => 0x4102022110800810a008024048102044804112
  | 2 => 0x2248802241480a4089250009540c10a130428
  | 3 => 0x4491448002952001124a4aa000302a02c0a80
  | 4 => 0x90600000003e64c919803022044144003fa000
  | 5 => 0x278fe793c90000002200c0cc199abbffc00000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffee8feeefee8fffffee8feeefee8fffffee8feeefee8fffffee8feeefee8fffffee8feeefee8fffffee8feeefee8fffffee8feeefee8fffffee8feeefee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_33392
namespace PEqualNP.Outside.L_meta_33392
open PEqualNP.Outside.L_meta_33392.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_2_0 : Interval s1Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 5 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 91 := (concat bs1_4_0 (concat bs1_4_32 bs1_4_64))
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
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 9 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 50 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_128 : Interval s2Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 136 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
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
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 9 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 50 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_128 : Interval s3Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 136 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128)))
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
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 66 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
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
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_256 : Interval s4Atlas 3 256 23 := block_range (n:=23) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 279 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96)) (concat (concat bs4_3_128 bs4_3_160) (concat bs4_3_192 (concat bs4_3_224 bs4_3_256))))
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
theorem bs4_4_288 : Interval s4Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 302 := (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 24 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_32 : Interval s5Atlas 2 32 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 43 := (concat bs5_2_0 bs5_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_128 : Interval s5Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_160 : Interval s5Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_192 : Interval s5Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_224 : Interval s5Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_256 : Interval s5Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_288 : Interval s5Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_320 : Interval s5Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_352 : Interval s5Atlas 3 352 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 377 := (concat (concat (concat bs5_3_0 (concat bs5_3_32 bs5_3_64)) (concat bs5_3_96 (concat bs5_3_128 bs5_3_160))) (concat (concat bs5_3_192 (concat bs5_3_224 bs5_3_256)) (concat bs5_3_288 (concat bs5_3_320 bs5_3_352))))
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1376 := (concat (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat bs5_4_576 (concat bs5_4_608 bs5_4_640))))) (concat (concat (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 (concat bs5_4_768 bs5_4_800))) (concat (concat bs5_4_832 (concat bs5_4_864 bs5_4_896)) (concat bs5_4_928 (concat bs5_4_960 bs5_4_992)))) (concat (concat (concat bs5_4_1024 bs5_4_1056) (concat bs5_4_1088 (concat bs5_4_1120 bs5_4_1152))) (concat (concat bs5_4_1184 (concat bs5_4_1216 bs5_4_1248)) (concat bs5_4_1280 (concat bs5_4_1312 bs5_4_1344))))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 884 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat (concat bs5_5_96 bs5_5_128) (concat bs5_5_160 bs5_5_192))) (concat (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)) (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 bs5_5_416)))) (concat (concat (concat bs5_5_448 (concat bs5_5_480 bs5_5_512)) (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640))) (concat (concat bs5_5_672 (concat bs5_5_704 bs5_5_736)) (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 65 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_416 : Interval gbAtlas 4 416 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 444 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416))))
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
theorem bgb_5_2240 : Interval gbAtlas 5 2240 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2254 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))))) (concat (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)))) (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)))))))
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
theorem bgb_6_4000 : Interval gbAtlas 6 4000 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4019 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216))) (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)))))) (concat (concat (concat (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)))) (concat (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))) (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))))) (concat (concat (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 bgb_6_3360)) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 bgb_6_3616)) (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 bgb_6_3744))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)))))))
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
theorem bgb_7_1184 : Interval gbAtlas 7 1184 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1185 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 (concat bgb_7_384 bgb_7_416))) (concat (concat bgb_7_448 bgb_7_480) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))))) (concat (concat (concat (concat bgb_7_608 bgb_7_640) (concat bgb_7_672 bgb_7_704)) (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864)))) (concat (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024))) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184))))))
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
  · exact allgb_2 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 6 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffefefefefffffeeafeeefeeafffffffffefefefefffffee8feeefee8fffffffffefefefefffffeeafeeefeeafffffffffefefefefffffee8feeefee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 12 := by
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def sample7 (r : Row) (i : Fin 8) := bit r (fullRoots.getD i.val zero)
theorem table7 : ∀ r, posted (sample7 r) = bit r fullWord := by decide +kernel
theorem raw7 : List.ofFn (fun i : Fin 8 => fullRoots.getD i.val zero) = fullRoots := by decide +kernel
theorem eval7 (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = posted x) : (execute gs fullRoots).getD o zero=fullWord := by
  apply bit_ext
  intro r
  have e : List.ofFn (sample7 r) = fullRoots.map (bit r) := by rw [←raw7,List.map_ofFn]; rfl
  rw [←bRead,exeBits gs r fullRoots (fun g hg => (legal g hg).1),←e]
  exact (h (sample7 r)).trans (table7 r)
theorem binaryLower (low : Lower true fullRoots fullWord 12)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 12 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval7 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_33392.Model.Repr at out
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

def mono : List Gate := [⟨.or,[7,6]⟩,⟨.or,[4,8]⟩,⟨.or,[6,3]⟩,⟨.or,[4,2]⟩,⟨.or,[0,1]⟩,⟨.or,[0,2]⟩,⟨.and,[7,10]⟩,⟨.and,[9,12]⟩,⟨.and,[13,5]⟩,⟨.and,[11,8]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gs o legal _ correct
  by_cases clean : ∀ g ∈ gs, g.op ≠ GateOp.not
  · refine ⟨gs,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨op,len⟩ := legal g hg
    exact ⟨op.elim Or.inl (fun h => Or.inr (h.resolve_right (clean g hg))),len⟩
  · push Not at clean
    obtain ⟨a,ha,hop⟩ := clean
    have lo := binaryLower low gs o (by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using legal) correct
    have less : gs.countP (fun g => !isNot g) < gs.length := by
      by_contra! bad
      have e := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length bad) a ha
      simp [isNot,hop] at e
    exact ⟨mono,20,monoShape,by change 13 ≤ gs.length; omega,monoEval⟩
end PEqualNP.Outside.L_meta_33392

open PEqualNP.Outside.L_meta_33392 in
theorem PEqualNP.Outside.L_meta_33392 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
