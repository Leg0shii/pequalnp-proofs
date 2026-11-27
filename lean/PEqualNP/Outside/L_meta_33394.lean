import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_33394.Model
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


end PEqualNP.Outside.L_meta_33394.Model

namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_33394

namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2f1a1c8161e302250000c1c000530052b002d46a07003e008805c0c0000c5c4823c9ca8b3aac91a4000caa44909854228a083600110021800000008d0c5700ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1c934d2772894c0a003e000aa6628000983f31000000b001e80000210d4d60041800000000178ce004100090410787c8a2a2c2040000001a800002e0945c74000dcb6460c88c74003f1b10a7004800ae13069940000070008826060000000401382e030092c921d2b2102c7b0909c0000001e4561a030007a78321fc04041691c00612d084441c041009e6808000c6362182800201a180be2f180f0fa7619948584a37054ba383901c006d121c40000191cc003b0a16422001f000301e1421800290d8010e753795062000100000a02130002000b0000040c01000100040a0401060a010e020000020d060c0100050000000401031500b7294876d5290ebca7215754e42cf29c859d5390a7ca5214f546429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e940429ea8085b95010a72a0214f953329eaa6659e54ccb3aa9996790b32ce216655d538cb5885194fd51329e2a265ac424cb3ea8996715132e7a9265cf424cb3c84996710932e6212658c424cabca6194f94b41cf996839d32d067aa1a0cf552419e292839f325073a64a0edd45419fa82833e541067ca918cf552319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321af29e435d53c879a6590cf952219eaa443b5418867ea890cf15121e699243b5414867ca810cf55021af298435d53086f4a010de540219f296819f32d033a65a04f547409eaa4813c525033e64a0674c9409fa8a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184fd53209e2a6415e53c82baa790734cb209f2a4413d548837281104fd51209e2a241cd324837280904f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa88857d4d10ae29a213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3010e1106bc694000008c609801f5c00ca52e2960b5290d9634c568f4615022127802b008499d4e4810e20180070000a885400028001c425604809210c04000019ca358e5210b165354442c554d5110b315194042c694d5010b195354042cc9455010b315154042a558442cca996010b32a9584428caa96010a32a9584424caa96010932a3993524ca1e6590932a398a424ca1e6510932a5584424ca996010932b1584424cac96010932a3994424cb0e6510932e1984424ca8d6110932e1584424ca856110932e2980424ca8d6010932e2580424ca8960109328e580525070c524c9418e58054c870c544cb21c315132486346550521e14c941486356114940c314932502356115320c315132c830c544c9208e195404838932501208b189544424d6214d10d454d10043615244010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xa33002410107000045a05866010932d04c2b00849968161580424ca84b80a499283425c0544cb21c08ca9928290d05711493250282b88a899641821953250120
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (4032+((h/45+packedAt s0K4 (3672+(h % 45)*8) 8) % 180)*9) 9
  | 3 => packedAt s0K3 (1996+((h/16+packedAt s0K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s0K2 (453+((h/3+packedAt s0K2 (441+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 2 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 3 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 4 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4300a010422108400810504840904222051045
  | 2 => 0x84210220904030084022221084240504122112
  | 3 => 0x921101001244012480048429022890404c28
  | 4 => 0x890554a24900492b5448024324aa090e80e80
  | 5 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffcffc0fcfcfcc0fffcffc0fcfcfcc0fffcffc0fcfcfcc0fffcffc0fcfcfcc0fffcffc0fcfcfcc0fffcffc0fcfcfcc0fffcffc0fcfcfcc0fffcffc0fcfcfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x300078024000004a0098036000000000a9f141800000412263aa00004008400008958000000010011180005cd001c0000352000000001380002c60500a8000001c000005801c3c00000004400d0050021000000012640000000002000608000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1e912a0d80010000248022a680022c001b80000021130b800d15001c1da08007238f858e118025000000202d002b9b0a8994a925829e27998c07840a179601852c8e958ca9801226221a1803ab082416801c9280288000000000001a892d93a3000028000000a188991886971f141d060f048b2aa710901f80030080500470302006000008181066058002301850418201001c09dbb28e877551d0edca521db54a43af29c855d5390abca6215754c42bb28885755110af4a0215e540429f2a6653d54ccb3ca9996755332aea9c65cf524cb9e84997310932af298655e53d06baa7a0e794f41cea9e839f32d073a65a0cf55241cf992839d325076ea2a0cf95041daa0e633e548c67aa918cf950319eaa0636e520c6daa418ed50431bd2806379500c6bca790d754f21e6996433e548867aa910ed50621e699243b5414867ca810cf55021af298435d53086f4a010de54021af298815d53102dca4205b54840bb2888175511027ca8184f55030b7290616d520c2eca2185d54430af29e415d53c839a65904fd51209e2a241cd324827ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a838857d4d10ae29a21b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x90010369c0c23c0a1182e2ac4508048d58654cca956195332a3993524cac56110932b2580424ca4d6294f41a358a53d061d65ccb41a598f51507255250431cc505500c78532505218d584544830c544c9209358853443145350510
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x2000130090ae3326a4994857298f5150682b88a899241415c85350510
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
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
  | 5 => packedAt s1K5 (802+((h/14+packedAt s1K5 (704+(h % 14)*7) 7) % 99)*7) 7
  | 4 => packedAt s1K4 (2694+((h/30+packedAt s1K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s1K3 (633+((h/5+packedAt s1K3 (608+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s1K2 (200+((h/1+packedAt s1K2 (196+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 2 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 3 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 4 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 2 => 0x10888411049080c042024484484240a10a4112
  | 3 => 0x22024888090049200948012202902514208c28
  | 4 => 0x441241aa5225402495d4900a1324ac14740e80
  | 5 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffaffaafafafaa0fffaffaafafafaa0fffaffaafafafaa0fffaffaafafafaa0fffaffaafafafaa0fffaffaafafafaa0fffaffaafafafaa0fffaffaafafafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2018f2b0000aa23071401002cb02320000000006054a24b8f1a8c9130e00000000000014001803e000000000e8000010241044000089c0005400a000068da152987020206001800030203000c080ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x121e2105252800080daa95889c90230012869100018c82ac859e97221827108a0ba28026150929a1948f049ba4140d160000001da5ac27a680118a8419ab9f001900010200000e20800e80078003a90fad00939b09a000062da89a98802a0c0b2b178307001d131a169f9c23a48000870000002000c6920a0809500000191200c0212083000214004bb28e877551d0edca521db54a43af29c855d5390abca6215754c42bb28885755110af4a0215e540429f2a6653d54ccb3ca9996755332aea9c65cf524cb9e84997310932af298655e53d06baa7a0e794f41cea9e839f32d073a65a0cf55241cf992839d325076ea2a0cf95041daa0e633e548c67aa918cf950319eaa0636e520c6daa418ed50431bd2806379500c6bca790d754f21e6996433e548867aa910ed50621e699243b5414867ca810cf55021af298435d53086f4a010de54021af298815d53102dca4205b54840bb2888175511027ca8184f55030b7290616d520c2eca2185d54430af29e415d53c839a65904fd51209e2a241cd324827ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a838857d4d10ae29a21b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x20238000184a4b50f60c072ac2004a48d58654cca956195332a3993524cac56110932b2580424ca4d6294f41a358a53d061d65ccb41a598f51507255250431cc505500c78532505218d584544830c544c9209358853443145350510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x14c0090ae3326a4994857298f5150682b88a899241415c85350510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
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
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 75)*7) 7
  | 4 => packedAt s2K4 (2694+((h/30+packedAt s2K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s2K3 (633+((h/5+packedAt s2K3 (608+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s2K2 (199+((h/1+packedAt s2K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 3 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 4 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 3 => 0x22024888090049200948012202902514208c28
  | 4 => 0x441241aa5225402495d4900a1324ac14740e80
  | 5 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffeeffaaeeeeee88ffeeffaaeeeeee88ffeeffaaeeeeee88ffeeffaaeeeeee88ffeeffaaeeeeee88ffeeffaaeeeeee88ffeeffaaeeeeee88ffeeffaaeeeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x2f4e5c70020005800050080126559604614111080da318b051a06540004414380267879d383551242193293e1002d000122e4a1400016852c502e3c414e010ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xa61dd314c37c80986f10130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6186fd0c30dea18617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea10617e510c3eca2185d94430bea8861f5510c2eaa2186fd0430dea08617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c837e85907b90b20dea1641ed42c835a85907b8cb20f6996417e51c82faa3906fd0720dea0e41ef21c83da43906f90320de206417f548837ea9104fd5220bf2a4417d54882f8a9106f152209e2a4417f53882fca7105f54e20be29c41bf438837a87105f54a20dfa1441bd42882fca3105f54620dfa0c41bd41882fca1106f90220de20441fa30883f261107bc8220fd904417f544837ea8904fd5120bf2a2417d54482f8a8906f151209e2a2417f53482fca6905f54d20be29a41bf434837a86906fd0920f721241bd42483da84906b50920f719241ed32482fea2905f14520dfa0a41bd41483de42907b48520df20241bc40483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c530837e86106f50c20bf29041bf420837a84105f94420fb288417651082faa2107d54420baa8841bf410837a82105f94020df20041bc40083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10dfa1621bd42c437e83887d90710dea0e21f541c436a83887d8c710fa98e21f621c43ea43886f90310de206217f548437ea9084fd5210bf2a4217d54842f8a9086f152109e2a4217f53842fca7085f54e10be29c21bf438437a87085fd4a10bf294217d52842f8a5086fd0a10dea14217d518437e83086f50610bf28421be408437881087e8c210fc98421fa20843f241087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4886fd0910dea1221bf41443ec82886f50510faa0a21b541443ec62887d4c510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xe53886faa710df14e21dfa1c43bd43886faa510efd0a21dea14437e518877e8310ef50621fb18c43f531887de4310fdc8621bf284437d50886fea890df95121df2a2433e54486faa890ef551219eaa2437c54486fea690df94d21bea9a437c534877e8690ef50d21dfa1243bd42487dc6490fb4c921dfa0a43bd41487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843bd43086fca410efd0821dea10437e510877e8210ef50421f790843f621087da4210fd48421f2908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037e87206f90e40dea1c81bc43902fca5205f54a40dfa1481be429037a85206f10a40bf28c817d519037e83206f90640dea0c81bc41902fca1206fd0240fda0481bf539037ca7206f54e409ea9c81bc539037ea5206f94a40dea94813d5290378a5206fcca40df19481bd329037865206fd4640df28c81bd519027aa3206f14640df98c81be319037a63206f0c640df90c81be219037a43206f086409f284817f53502f8a6a06fd0d40dea1a817f52502f8a4a06fd0940dea12817f51502f8a2a06fd0540dea0a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d531037e86206f90c40dea1881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081be421037a84206f10840bf28881f651102eca2205f54440faa888175511037e82206f90440dea0881bc41102fca0206fd0040fd20081bd40103f280206fd4c40df298819e531037aa6204f54c40cea98811d5310378a6206fd4840df29081ae521037aa4204f54840d6a90812d5210378a4206fcc840df19081bd321037864206fd4440df28881b6511037aa2204f54440daa8881355110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc37e87987790f30dea1e61dd43cc33a87985f94b30bea9661bf42cc37a859877ccb30ee996617e51cc2faa3986fd0730dea0e61df31cc3ba63986f90330de206617f548c37ea9184fd5230bf2a4617d548c2f8a9186f152309e2a4617d538c37e87186f50e30bf294617d528c37e85186f50a30bf28c617d518c37e83186f50630bf28461be408c378811877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261bf434c3bc86986f50d30eea1a619d434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98
  | 2 => 0xcafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7196fd0e32dea1c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132df2a2653e544cafaa8996f551329eaa2657c544cb7e86996f50d32dfa1265bd424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865bf430cb7a86195f94832dfa1065bd420cbbe64197b8c832ee99065ed320cb9a64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0ef54f419ea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41dfa1c83bd43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d419fa9a83be535077aa6a0ef14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41dfa1883bd43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc77a8798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77e8718ef50e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131bf2a263be544c67ca898df55131deaa2633d544c6f8a898efd0d31dea1a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218f54c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8790ef50f21dfa1643bd42c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437
  | 3 => 0x406000001010004010000020000000300201c000000020100000500400401800004000000070080040580001000c0000201e000010030000000900500000c00001000008000030020100300200801800001008024020000020000080400003c02001004018028000040200000500000400000000004020020160000600100200c0080d00800000000000014000030020000000100a00400005008008000000000080080100401c008020000000080100000400002000000000000060080000301800c02000004020000040020000100000a0000000300400001800008008008010000000780d0140040180000001800002002000000040020040080100000c0180400400c018000080300280201000405002000000018010180080200001600c0000000200c00000000000000010000100500000400c01806000034000030020040a81d01800400004006004000040020000000000400800805000010000010000000580100c0040000200402800002000018008000080080300300000c0000000402000802000000000060000000000100001406000004004060010000500280d0020000100100803c01800016000010000000000100100400001007018000008000000100280000401c000000000040180100e016fca5a1df54b43bf28e877d51d0efca1a1df54343dfa9687be52d0f7aa5a1cf54b43de29687bf51d0f7ca3a1ef547439ea8e87bc51d0f7ea1a1ef943439f28687bd50d0f78a1a1df552439eaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa92873f5250f7ca4a1ef54943de29287bf5150e7ea2a1ef94543dea8a87bc5150f7ea0a1ef94143dea8287bc5050e78a0a1df950439f2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e853d53d0b78a7a16fd4742df28e85bd51d0a7aa3a16f14742dfa8685be50d0a7ca1a16f54342de286857d5490a7aa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a14fd4d42df29a85bd5350b78a6a16fd4942d7a9285bf5150a7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050a78a0a15f950429f2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccb7e87996f50f32dfa1665bd42c
  | 4 => 0xca10631c00052e0f27a80625a05b043e2f051a5fa5ac77a23e44a0002486862c240c45a13e11a6140000000000a86f04e61687cc1a80ee5703784e477e42400000005467a71217e5022fe00048a03616c0800000000000001aa00055c58c5ea42000000047436c12a55401c1980be3f87f20002702666160002aa71a58a72400044000030c79484c7c05967fe00015261812e0240000006f200000029e0007f44fe53c28c3ea1ba00000032000415406e1d83e20000001b014a0006a20500142560900006040000000003063d07a63c07f65dc5207e403c73e35e52c69e3a24640005ee0005e20000003e40000000000e24d200070a00069200051e46a0000000b20001501120000d002e0006800000003b000000040a2440000821f474a0704ce42e00000011c0161f80760002d20d80003fc78c56600020000032a62c00021c2380002200000002684f60c20000007420000002ae00048600076c4d05d454a4c239400000000079000000000000000075c00000000048852800062e0000005520000003a80000006ee13c6f80f84ec2d427a3e64562ea0000004047e60000005d200030a00000000031623a0743084f273400000000000078a00084600035600072619e71650a7d41fc27469c6441ae0000221e45220000640000000006905c67584660000000000de44433210800000026a54c6f40000000006fa0006201720e88420000840c81c650427c0004a60002925580004c042805a00000080200000066400000000054200000a0004e200000020221e3962dc0cc11000027209800063e5fc6881e00000000000003f044c03e8040c400000000078645c0006a60000c00000bc6ea0006d480c0000003700da0000000003be21600076e0000008561840000006e600007a2c015c0005c83dc6060000280000000001dc48280e0005146c600039860200000078429c79c4500004ae0ea0001ac5847460002ac43000000067e2860002b80002b68007d26d22823820600006d60004421ec0000000000003ec23c0000000000000005ca00000000053a25e4fa7f824c0003c61c800033406a6aa2de7ac6de7a471c38c25249c4ca1da0007d043a4f400c0006b40004b05ec4b22086e804c1f000075e5780521de0008400000008080001b80004980005e600012849076454056c0003d241c2f200025431074442605c24e4182d86980000b80266fe03856e0006504cc0006600000008227501145260005c443671e7920000001323a44101d025818651238a33c28a0c672c0920fc30456a45857a2045247b63242b47c800061e00000000030000006c5bc0e600000004a01070c85208667085440273a35060a6fc0000000000000003c400000003a81c8246be5e467260036285a1c4000030638014008000060000100180000c0100080300c000000
  | 5 => 0x5625e844e6585de0000000006344a20e400014213600038e0003d863a1740000000d40005445740000000000004c40004788485b24460000003fa5f02a80ae1fa66857c62400000000017c26e00009a0000000000002142e60005f655063200015636e3d600000065e4681a647c4be0724de57646c1cc30e7181247c42b20004ee77c77014c0886364c60002ce8346220007bc18a4a80120b000000053249682876800000051000074c7360060000006a400000000000000000000008c0007c20002e062600000000000018007c0000007b83520000001a47285f402a7e06d047e4ac79685c72a1d67d67386ac39c22203227664264600059c00000000074800006600000000000041e2da10c69a0000f400000057240e5f800000000000000000000041269421200000000000000034c30208e1ca0002d01167b475467c00032c0781021880000002cc0002e225a34042c32229a66c2242063b281a76a6ae6400000000d637400003400012270e61c3ae3bc83c0000000000000420ac0004140000000a63e86e001a48c81e0003f23d400044800222c6b86f627e12600000020e0000000000001ea0a47000461303ba7988442782fa7a065a6280006bc53601855659434e2b000016600049a3aa68c0002100003ee7a20006dc4e07560002bc4620000003f482a00000000000059a39263c0000000000006e40000002423300007da00083049400078242237235a3f60000000000000f00ba0000000000000006ca2508580002ee1e837c6e22c40000001901824c800081000000000022e00077800000048074e0004f82983b80583a000079a00000062a1a26b05be3c200820c00000058600014400000066a55e0000007b20003de0000007ce6c20003580003600000006da47000039a0003e00005e064c4e86ce29045450c0000000001e20000dc00083e6ba75a00046e2300001d468a00000017072e0560ca09c7303864bc4161c28323686b23842be4b61b40000004fc00080608a32e0000000003140005d826260c0007525487dc71033833643400000002019a10e00050e41a0004d61e60000000004080000000000000000003da0000000000005b66301b60000000e000028e00000001e0007227ae31e7f000000000067470251c8500000000aa0000000001ee82661a2f63127325828182ba07e15e00055a00000000000078e16e7c600066253e6c00000d200047659e7087fa00018c0003fe7ec00000000043c0000005386765cc00005e6ec00000033e00000000000000000049e00031832651883667813a1f266e00000000021a5a818e0962e80b458e0ce00000034222600016a7802460000ec0000b60000000005ce2600000000000003446b65460006cc0000000000000000000005342f464e37a6524924d417a15a60e0000485167
  | 6 => 0x4320000a20005a21340001b20000000007e20000003885687ee0004384ba00016468e39e00000014635c0004005007747ba2fc3ac2c85647de38004e00023200081200036437e0001000000000000000006d80007aa00000000000036642a84e5ba78882e6967600000007fc1be0000000000a014800082c0000000000002405a42a00003c88608620008161621d273c5a682034a4060000000f60004b40002340002a40006560005fe0006a06c431a3ca20a3b406800000000000e5da0002ca0000000000004f04ea0000000001940000005980000007400001ce0004a417836a00061260834800019248e2280000444522a272053025c4da0008382ec7725924a076284a12c66633a11e1bc24a0000000006480000fe0000000000005803ce59070476600002c0000000000002962c665c0000000000007d800000000000000000000034604058810a0000003903280000003cc0000005b422a0000000005b80000002f817600000045e00000080a13800068400000047a14e0006547be0000000007e81f63b62d60001a00000001c02e40000005f23a677600000000028800056000000010461019626450685e0008140000000000006822802a619c1205d057e0004aa0007b04605d66c800037600035400000000048470600023652a0002945aa4d84b847283a28471414064a5081fe09e6a80005c200079e0000fa7ea26c21854e0000001580940001600005ae4dc0000000000000001180005c000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x9208433754c42108f58f544423d62d51108f992544423e65151108f58c544423d6215110cd584544423e60151108f180544423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534423e65d0d108f19743442b561d0d108f995434423c6550d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d0910ad587424423e65509108f195424423e65d0510ae98341442b56490510cd152414423c6550510ae18141442746550510bc18141443376550510cd19541442346550510add8d41442b76250510ecd8141442b46050510ec18141442b06050510ad5923144274654c510ad5913144354534c510ad59221442746548510ad591214436452485108f996404423e6510110a758c40442ad6210110ad58440443b1418c1109e1953044399434c110ec50530443d1314c110ec50620442786548110ea50920443b14148110f848520443b141c4110add92104425e63d50109758f540426e62d50109b58b540423d65950108f58e540423d62950108fd8d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c108f992530423d6494c1097596530431e5494c10c7552530431e6494c10c7592530431e5454c10c7551530431e6454c10c7591530423e6414c108f590530425e6314c109b988530426d6214c109d984530427a6014c108fd97430423d65d0c10c794f430431d53d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48108f992520423d64948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432e6454810cb591520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d52508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d5250410cd945410423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010a758c400431e5310010c754c40042ad6210010cb948400432d5210010ad584400433554c4010d554f100436552c40109e59610043595384010da54a10042776544010cd55110043555344010d954910043b040440109ed9510043595344010da54910043b34144010
  | 1 => 0x823d61950208fd8d540823f62550208f589540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530831e6494c20c7592530831e5454c20c7551530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c208fd95430823d6550c20c794d430831d5350c208f992520823d64948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083374394420cd50e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083374354420cd50d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410823f65900208f596400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020a758c400831e5310020c754c40082ad6210020ad58440083365110020cd544400832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d20083655148020ea101200827b6548020d654d20083ab4248020dc545200823d63953108f58a54c433661953108fd8d54c423f62553108f99353c423d64d4f108f99253c423d6494f108f99053c423d6414f109b98853c426d6214f108fd9743c423d65d0f10ad58743c423f6550f108f59543c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c42b561d0b108fd9542c423d6550b10cd95141c42b76550710cdd9541c42b76350710add8941c42b46050710ad59231c42b5644c710d514d31c42b56488710ad59121c43645248710a758c40c42ad6210310ad58440c423d63d52108f58b548433561d5210ce983548425e63152109758c548426e62152109b588548429d6315210ab588548431e63152108f58c548431d63152108758c548432e62152108f588548432d62152108b58854843356115210ce980548423e6494e108f592538423f6454e108f191538423e6414e108f590538426e6214e109b588538423e65d0e108f197438423e6550e108f195438431e5350e10c754d438423e6494a108f592528423f6454a108f191528423e6414a108f590528425e6314a109758c528423e65d0a108f197428423e6550a108f195428432e5250a10cb54942842ba60d0610ae18141842b56190210a758c40842ad6210210ad5844084399434c210ea50
  | 2 => 0x4294430cd50a510c3365454430cd551510c3665254430d9549510c3366454430cd591510c3374354430cd50d510c3374254430cd509510c23f65d04308f597410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410c23f65900308f596400c29d6390030cb94a400c32d5290030cd946400c33551900308fd94400c23d6510030a758c400c2ad6210030cb948400c32d5210030ad584400c3365110030cd544400c31d54cc030d354b300c35551cc030da54a300c371518c03097d95300c31d544c030d3549300c355514c030e6101300c27b654c030e6d0d300c369524c030dc545300c23d6395320cb98a54c823d61953208fd8d54c823f61553208f99353c823d64d4f208f99253c823d6494f208f99053c823d6414f209d98453c82756114f208fd9743c823d65d0f20ab58b43c823f6550f208f59543c832e5450b20abd9542c832f6550b20abd8d42c82af6150b20ab18142c82ad648cb20ab59132c834c534cb208f99251c823d64947208fd9741c823d65d0720ab58b41c823f65507208f59541c82ad64c8720ab59121c829d6310320ab58840c82b561103208f58f548832d62d52208f587548833a60d52209798c548825d63152209d98454882756115220a758c54882b56115220c798c548823d6315220c758c548821d6315220cb588548833661152208f584548833561152208d584548833a60152208f992538823d6494e208fd91538823c6454e208f990538823d6414e209d98453882756114e208f997438823c65d0e208f995438823c6550e20c794d438831d5350e20ae98342882b86050a208f992518823d64946208fd91518823c64546208f997418823c6550620cd94541883355150620ab58a408829d6310220ab58840882b56110220e650d308832f54c82208f58f544823d61d51208f992544823e65151208f58c544832d62151208f584544823e6494d208f592534823f6454d208f19153482776154d209d185534823e6414d208f59053482766114d209d584534823e65d0d208f19743482ad62d0d208f995434823c6550d208f99742482ba60d0920ab592424832c54909208f19542482b860509209b19542482e86050920cbd95424832c65509208b19542482af6350920abd8542483ab6050920ab18142483a86050920aa18142482ad648c9209b19532482ad644c920d314d324823e64145208f590514825e63145209758c514823e65d05208f19741482ad62d05208f995414823c6550520ab59321482ad6448520d9145214823e65901208f994404829d6310120ab58840482b56110120ea50a3048278654c120e650d30483a9424c120f24c930483a942c8120abd92204825e63d50209758f540827661d50209d587540823d65950208f58e540
  | 3 => 0x4408f596211031d5388440cb54a211033551884408f595211031d5348440cb549211033551484408f994211023d6508440a798c211029d6308440c754c211032d5208440cd54421103a52108440ae98021102b96008440c794e501031d5394040cb94a501032d5294040cd94650103355194040ce982501039a5394040e654e50103aa5294040ea54a50103b25194040ec546501031e63953308f58a54cc23d61953308fd8954cc23f6155330c795143cc29f6550f30c7d9543cc29f6250f30a7d8543cc29c6050f308f99252cc23d6494b308fd9742cc23d65d0b30a758f42cc23f6550b308f59542cc29d64ccb30a759132cc23e64947308f59251cc23f65d07308f59741cc29d63d07308fd9541cc23d6550730a759331cc29d644c730a758c40cc2ad6210330ad58440cc31d63d52308f58b548c23d61d5230ce983548c26e62152309b588548c27661152309d584548c2ad6215230ad584548c31d6315230cb988548c23d6215230cb588548c22d6215230cd984548c23d6115230cd584548c2356115230ce980548c2ba60d0e30ae181438c23e6494a308f592528c23f6454a308f191528c23e65d0a308f195428c32e5250a30cb549428c23e64946308f592518c23f64546308f191518c23e65d06308f195418c3365150630cd545418c29d6390230a758c408c2ad6210230ad584408c31f54cc2308f58b544c23d61d51308f992544c23e6515130c758c544c23d62151308f584544c23e65d0d30ae983434c29d6490d30c7152434c23c6550d30ae181434c25c6550d30b6181434c31f6550d30c7195434c21c6550d30a7d89434c29f6150d30e6d81434c29c6050d30e6181434c2986050d308f990524c23d64149309d984524c27561149308f997424c23c65d0930a758f424c23e65509308f195424c29d64cc930a7591324c34c524c9308f990514c23d64145309b988514c26d62145308f997414c23c65d0530a758f414c23e65505308f195414c29d64cc530a7591314c354514c5308f996404c23e6510130a758c404c2ad6210130ad584404c39943cc130a7d92304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23d61950308fd8d540c23d63550308fd89540c23f61550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c23f6550c30c794d430c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32f4394830cb50e520c32e5454830cb551520c32e6454830cb591520c32f4354830cb50d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c23e64944308f592510c3365494430cd552510c3665294430d954a510c3366494430cd592510c3374394430cd50e510c337
  | 4 => 0xd50951103344254440c794f411031d53d0440cb94b411032d52d0440cd547411023d6590440c754e411032d5290440cd546411031e5350440c754d411032e5250440cb54941103365150440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401031d5350040cb549401033551500409ed9540102ae62d4c40ab58b53102b661d4c40ad58753102ba60d4c40a7596531023f6254c408fd85531031f6554c40c7d89531031e6254c40c7589531031c6254c40c7d85531031e6154c40c7585531031c6154c40c7981531031c6054c40a798c531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae980531029e63d4840a758f521031e53d4840c754f52102b661d4840ad58752102ba60d4840c754e52102ad6594840cbd4e521038e5394840cb54e521038d5394840c354e521031e5354840c754d521023f63548408fd85521032f6554840cbd4d521032e5354840e394d521030e5354840cb54d521038d5354840c354d521032c5354840cbd8d521032e6354840cb58d521032c6354840cbd85521032e6154840cb585521032c6154840cb981521032c6054840a798c521029d6314840c754c52102ae6214840cb54852102b66114840ad58452102ba60148408f997321023d65cc840c754f321032d52cc8408f996321023d658c840c754e321032d528c8408f595321031d534c840cb549321023e650c8408f594321031d530c840cb548321038d320c840ad98432102b5610c840ae98032102b9600c840a798f511029d63d4440c794f511031d53d4440ab98b51102ad62d4440cb94b511032d52d4440ae983511031d5394440cb54a51102b56594440cdd4e51103965394440cd54e51103955394440c554e51103375294440e994a51103355294440e954a51103255294440c794d511031d5354440cb949511032d52544408fd8d511023f6254440cdd9551103375354440cd94d51103965354440c594d51103355354440e554d51103155354440cd14d51103375254440cd94951103a65254440c994951103355254440e954951103255254440cd14951103376354440cd98d51103356354440cd18d51103376254440cd98951103356254440cd18951103373254440cd8c951103353254440cd0c951103366054440cd181511029e6314440a758c511031d5314440ab98851102ad6214440cb54851102b66114440cd54451102ba60144408f997311023d65cc440c754f311032d52cc440cd547311023e658c4408f596311031d538c440cb54a3110335518c4408f595311031d534c440cb5493110335514c4408f994311023d650c440c754c31102ae620c440ab588311032d520c440cd5443110395310c440ae98031102b9600c4408f997211023d65c8440c754f211032d52c8440cd547211023e6588
  | 5 => 0x430863f6550c218f595430871e5350c21c754d430863e64948218f592520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c8421d554e21086e562884219bd95210874d5348421e9d0521087a541484219dd9521087555348421e9d0921087a54248421b9d9521087676548421e999121087a56448421e995121087a55448421d9d4d21087c65348421d954d21087c55348421d154d21087a74348421e950d210873a5494021ce552500875a5394021d654e50087e12194021ced9250087386494021ced0e50087394394021ced0a50087394294021ced06500873941940218fd91500863c6454021d9485500873a5454021ce551500875a5354021d654d50087e12154021ced9150087386454021ced0d50087394354021ced0950087394254021ced0550087394154021dac8550087722154021da48550087712154021d8485500871d53d0f40cb54b42d033551d0740c794d439031d5350e40cb949429032d5250a40cd94541903355150640ae983539031f5394e408fd89539023f6154e40ab98853902ad6214e40ad98453902b56114e40ae98053902ba60d4a40cbd4a529023f6354a408fd85529029e6314a40a758c52902b66114a40ad58452902ba6014a408f997329023d65cca40c754f329023e658ca408f596329032d528ca408f595329031d534ca40cb549329023e650ca408f594329038d320ca40ad98432902b5610ca40ae98032902b9600ca40ae983519033751946408fd8d519023f6254640a798c519029d6314640ab98851902ad6214640ae980519023e65cc6408f597319031d53cc6408f996319023d658c640cd546319023d654c640c754d3190335514c6408f994319023d650c640ab98831902ad620c640e54c431902ba600c640ae580319023e65c86408f597219032d52c86408f996219023d6588640cd546219023d6548640cb549219033551486408f994219023d6508640a798c219029d6308640e948421902ba6008640ae580219023e65d0d40c7d4d435023e65d0940cbd49425023e65d0540cdd45415031e6454c40c754f431023d6590c40c754e431031e5350c40c754c431034e5394840d354e521032f4394840cb50e521034e5354840d354d521032e6454840cbd0d521032e4354840cb50d521032c4354840c794f421031d53d0840cb54b421023d6590840c754e421032d5290840c794d421031d5350840cb949421031d5310840cb54842103565394440d554e51103665294440d954a51103374394440cd50e51103374294440cd50a51103565354440d554d51103665254440d954951103366454440cdd0d51103364354440cd50d51103344354440cdd0951103364254440c
  | 6 => 0x72e6454831cb591520c72f4354831cb50d520c63f65d08318f597420c69d63d0831cb94b420c72d52d0831ad587420c63f65508318f595420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431b558e310c765528c43197d95310c74d524c431e5d05310c795414c4319dd95310c797434c431e550d310c765524c431b5d95310c757654c431e5991310c795644c431e5951310c795544c431f1949310c755524c431f1549310c745524c431e5d09310c795424c431ce952500c7395494031da94a500c7695294031f44c6500c73b6494031ce192500c73b4394031ce50e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c7553154031ce951500c7395454031da949500c7695254031f44c5500c73b6454031ce191500c73b4354031ce50d500c73b4254031ce509500c73b4154031ce505500c75b3154031dc8c5500c7593154031dc4c5500c75131540318f58e54c863e60953218fd8d54c863c60553218f99353c863d64d4f218f99253c863d6494f218f99053c863d6414f219e98053c86796014f218fd9743c863d65d0f21ad58743c863f6550f218f59543c874c534cb21ab58b41c86af62507218fd9150c863c64543218f58e548863e60952218fd8d548863c60552218f993538863d64d4e218f992538863d6494e218f990538863d6414e219e98053886796014e218fd97438863d65d0e21ab58b438863f6550e218f59543886b561d0a21add854288754534c6218fd91508863c64542219798e544865d6395121a758e544871e63951218f58e544871d63951218758e544863d6295121cb58a544863d6195121cd586544863e60951218fd8d544863f6255121cbd89544863f6155121cdd85544863c60551218f993534863d64d4d218f992534863d6494d218f990534863d6414d219e98053486796014d218fd97434863d65d0d218fd95434863d6550d21c7d4d434871c5350d21ad58742486b761509219b195324874c534c921b918532486ad62d05218fd95414863d6550521abd894148674654c521d514d31486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f58e540863e60950218fd8d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21c7952530871d5494c21c7992530871d6494c21c7951530871d5454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f43086ad62d0c21ad587
  | 7 => 0x294032dc946500cb715194032ced92500cb386494032ced0e500cb394394032ced0a500cb3942940328fd91500ca3c6454032d34c9500cb3a5454032ce551500cbc93254032dc945500cb715154032ced91500cb386454032ced0d500cb394354032ced09500cb394254032d6cc9500cb6a3254032d64c9500cb693254032d24c9500cb1d53d0f41cb54b42d06ae62d4f41ab58b53d06b561d4f418fd8953d063c6054f41ad58453d069e63d4b41a758f52d06b561d4b418fd8d52d063c6054b41ad58452d063e65ccb418f59732d072d52ccb418f99632d063d658cb41c754e32d063d654cb418f99432d063d650cb41c754c32d072d520cb41e34c832d06b6610cb41ad58432d06ba600cb41ae58032d063d63943418f58a50d069e6314341a758c50d06ae6214341ab58850d071d5350e41cb549429071f5350d418f994435072f52509418f994425065e63141419758c505066e62141419b588505063d62d4d418f98353506b56194d41add85535063d63d49418f98352506b56194941add85525063e65cc9418f597325063e658c9418f596325063e654c941add8532506b4614c9418f994325063d650c941e34c832506b6610c941ad58432506ba600c941ae58032506b560d4541a798c505069d6314141ab98850506ad6214141c798c505063d6314141c758c505061d6314141cb988505063d6214141cb588505062d6214141c754f431063f6550c41cb54b421063f65508418fd9541106776550441cd951411063d62953318f98254cc63f62553318f18154cc63e6494b318f59252cc63f65d0b318f59742cc6b561d0b318fd9542cc63d6550b31a758f41cc69f63507318fd9150cc63c64543318f58a548c63e60952318fd89548c63c6055231ad587438c6b76150e318f992528c63d6494a318fd97428c63d65d0a31a758f428c63f6550a318f595428c63f64542318f191508c66e62951319b58a544c6ad62951318f58e544c71d6395131cb98a544c63d6295131cb58a544c62d62951318f586544c73561951318f982544c63f6355131c7d8d544c63f62551318fd85544c73761551318f181544c6b561d0d31add85434c63e64d49318f593524c63e64149318f590524c67a60149319e580524c63d65d09318fd95424c72f5250931cb149424c74c524c931b5185324c69d63d05318fd95414c63d6550531a7d8d414c63e64d41318f593504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c318fd95430c63e64948318f592520c72e5494831cb552520c72e6494831cb592520c72f4394831cb50e520c72e5454831cb551520c
  | 8 => 0x401601700801000b03002a00600301601400c00001300600001d00300701400000506201800e014011000017006004001ad98752d0eb561d4b438fd8552d0e3c6054b43ab98b51d0ead62d47438fd8951d0e3c60547438f58a50d0e3d6194343ab98850d0ead6214343ad98450d0eb561143439b9885050e6d62141439d9845050e756114143a75835350e3d61d49438f9835250e3d62d45438f9835150eae6214143ab5885050eb66114143ad5845050f2e62141438f5885050f2d62141438b5885050f3661141438f5845050f3561141438d5845050e3f6550c4397d954310f1e5450c43c754f43d0aad62d4f42ad98753d0ab561d4f428fd8553d0a3c6054f42ab58853d0a9e63d4742a758f51d0a3f63547428f18151d0a3d63943428f58650d0a9e6314342a758c50d0ab66114342ad58450d0b1d5350e42c7d4d4350a3e6510d429798c5050a5d63141429d9845050a7561141428f5875350a3e60d4d42ab58a5350aaf6254d42ab5835250a3d63d45428f9835150a9e6314142a758c5050ab66114142ad5845050b1e63141428f58c5050b1d63141428758c5050b3661141428f5845050b3561141428d5845050b1d53d0c428fd954310a3f65508429bd954210b2e54508428f58654cca3e60953328fd8554cca3c6055332a758f42cca9f6350b328f99251cca3d64947328fd9150cca3c64543328f586548ca3e60952328fd85548ca3c6055232ab58b438caaf6250e328f992518ca3d64946328fd91508ca3c64542329d986544ca756195132ad586544ca3d6395132c758e544ca3d6295132cb58a544cb3661951328f586544cb3561951328d586544ca3e60951328fd8d544cb1f63551328fd89544cb2f62551328fd85544ca3c6055132ab58b434caaf6250d32a758f424ca3f65509328f595424ca9f63509328f993514ca3d64d45328f990514ca3d64145329e980514ca7960145328f993504ca3d64d41328f990504ca3d64141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540ca3d61950328f982540ca3f61550328f181540ca3e64150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430ca3f6550c328f992520ca3d64948328f597420ca3f6550832b358e320ca5f654c832e3d09320cb8d424c8329bd95320cb8f434c832e350d320cacf654c832d3d95320cb8e644c832e3591320cb8e544c832e3551320ca3e64944328f592510cb365494432cd552510cbc53294432cd992510cb356494432cdd0e510cb354394432cdd0a510cb354294432d34c9510cb365454432cd551510cbc53254432cd991510cb356454432cdd0d510cb354354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432d14c9510cb3a5494032ce552500cbc93
  | 9 => 0x39e24e000000ddc58e3f0090466e26000c080000002ea1b06aa37c6241dc2be0003f2420ca68ba5eae9ee420b08164180001c4bb20008eeb7011c9046121f63e838282263a0000669089e800012c16cde40009dc71a5a4b12c8c00064213ab260000582c8000502bacce486201200800304e00501d00500000000a00201001200200004600f00000100400600000200e00200000100000100d00101800002000400c00002302e03b00000100000000600302e01300300102c00700400600103d00400704700300c00000c01f01600000100600500600000300600300400900203c00c00801300c02600000600901700600004800200e00605400104700b00000b09000700200000204600002200400201400401d00000c02300100600300901800000000000100700d00201407e00000102a00104500601502d00500000000000a00000900000300000b00400000100100200000000000500100200100f07400200300900a00001000300000100300400200001000000f02300600201900100200400000300000400600204b00100301401301a00000400000c01101600300000000001e00000c00201400200000000000000600000701500001301300002b00100800100200000700000a00000000b00200400b00002203500500100700000000300a00400800b00201301500402004600000000d00200800a00000900202200000200100700000500800b00600400000800100200b00100100100000000100301000501300b00900800104600000201300a00000600400000001a00500100d00b01f00002400e00100000100500a00300302800100d00100900100000000000200501a00300900800400500100000000600000300200000100001401b01006200d00000000101702b00902000601c00106f00001e00200500200600c01900f00000001100f00100200800801400100000901500600001300200001500600102f00000700100203400a00003e00d01103b00001500202600000900300500000301800300000e06900000604000000300000000a00000000101300d02a00104009c01800000000002900800400003100400200100a00000000700202400000000700100200500100200b00000400000000100f03300b00e00901300a00200f00000301600000000500101700300b04f00300000900501e00000200b00000400000000400100800500400900000100000100000a00b00d00100200400700101100000201700100400201000500300500000e00400200c00100c02b00200001b00600a01301d01001104502f00700f07300601800500100005600000900300300b00100e00300b00500000b00100100000000000001400600200500000000000000000300f00000900004600d00000400005400700000300c00400500007700001
  | 10 => 0x287705cc562d9a3ea56e0009ba2126c081ec702bc220000dd23d2c4244c230116b565b6e36000544528c6e0009a200055c7b21a0832d94eaa01ebf69d2964aec4a20d0a6a0005a80000180f60feb96000bcceae5c0ad61c8ec0a9ed74e3c4aeefc00093ecc4ea4812cc21560006f080a000000bf0ab20004cc000cbc2020005085c428a35c000578b1eb4a0000000000d8c7c000000000ac80000002c44a8b9e3f89fc0009aa4480000000000005ec00013238ccc00000000000000000002dc0008fa0002640006e44ea5e009400097200023251e82c1885303264e2702550c140f8a5a6a22e022c66eaea1b6c0a1e64828da602d9800000020c32a03200003a632a04e9a270c5c7f68e4000000e2a000000000000c5a6b849a000b281ca0ce00000047033edee126438c622465da8ac000000000bfc474c6c9c055e9d80e40000000004569f839257e574e683809d0000000000000000dd45c2000b2c00019c000000000000d881aa9e074000000072a620000b0c460bd6ec8564df26600d686a1fc4085cea100423c2bdaee0a6cea60ec000000b18982944400d5ccb279e62a12a000cfe864a5ce402721540007ca442986ed294e2aa14ee040000008d8ac2000a642d6128afc3fe0000c20007e4810000000000d5a4444d0000a3acf01ae4349cee4440c0001f474a3b4854ae6b0e70e000eca7b00000003cc1f2e82d1c000000a2600011281400046c00008ce6a17e00000041024413c8b8b4e9be8b6000e9436ece0e762620000ca25a75828e516948000d0288087a734e50cc800042e8dcef2000b660e657293c1a240659e6dac40b782cee96608eea0003a2d60524c782a0b5e47c1c0da668845e74467c0f219684e2901f0e1a902316be6b368466cae0209630edc0a38e547bcbf4e125aecda73e72884c7f490c48ab98e0e54cd1469405c68220014c82438e732b601cc98cbe42ac4923dc6b2626b9c176ab0a721c6788cb8e8ef064403362ba34c7d2d4c658b5cd40098976dbe05e89c6e244eebe680b2078678276203ca96e6282841c4bce7430408a7928e85e450ad6c9f64b461045a750e3865c6767a06d278ed6edae820c684c2000be0bc2a6e00023e9626de000a30d80da0000d100006bc3884c4000000ee8110bc4000da2324000000404b76534dc6adca3c0004e65326c4000868000000162b020bc7e8100bc00001e8ada6beacc9d600083ad6abb8dca0000009966ac39c00026caee2f0c3cacee6e1f895a27823a49eb8e96c0002da19e0000d2258d9e000dfe000c663520000001d00a40003e0bd800000000000095821e00031c000260c0200000052a0002f600020879a000a82c96c36c82a8eb045dc978a2aa943d03c4cced2c3ce000a866ee61e022a54968000000000514158000000000ba04fe2f400008e6d692495e000ed4
  | 11 => 0xad50af2990d6637a992d3e1d462cc88028dc4c527aa35a8304c0c867be7eed845e2c8addace60ae8d00869fa826130d6850e0488ca2567c0d720b6118cfc9e240ac2c51069e068efa464a7a88c8feb1c640716322c06974a56baed9c0009d4806c00dded12d4e4887e236c1723f4088bd27a434e29c06aeba98e6b43fc5220c05d266493a55800012242ceda3c60daa6824c9f21fec4415eb2447643c19050cca0decaa83eedb8368a92614160e8800037436200064eae43ca000a8a000a90000af4000024000ea087e114c605bc678deaa84b000006ea000d825040c4afa4223489140002380be85224000063096eb2ed86000bdc5fe000d0a8f4e0a396104000d2e24a000000a0671e00085e6ec000000d90b48c8005ab8ca424aa0000000001bc414686e52000edc000d1eed0000284aba55a00085c0007380ba000000e647723ec4a6db033081815a000caa6d8dc22180006cc6e665600063cdf80000007000007422fa60a9c254ab8a79400048cbf269c00089e0000001d6000020000994dcc7a2d4855221681ac32c94c0403e45092010e9c4d0054860c83e8de07e6e0b6c000eccd3cbbc000e8000092c3b00000805f6224000000000b22e2810ad3acdc3842520008c8af699a1e0ceacd82b4d9646ade889ab72c380305802c2eeec7e00083c000a1656819a9807d627665e31ebe29deeb84f0a40de622edcee3ab9a04e56af0c0000643e61842985e6c2800068c354c34cf2f0041217c02cb8638a1ea4725deb3a76447a4a000e000ca8d4abcaccc88269ad463a80eab6a51cad27569ec9b05861463602e6e2447e9b2ba8c7a09e91ee32caed064ec98a31a91296a5fc2e84be000358aa013490a600000000000a60050918800000b804fa2fc13ea9c3e278a2f2000282000f124fc01a5ac0001948b4a489b8000078292d280004f2468000d7073059a7247fc016ec236a95400079608267479c6f82e40000009ae65a9c6bb4dbaa8c4364f87da280bfa4dc6a4e562266545f44baab8848aae66acd2dfa88a890c4c0a85a280cc5e59cc4e142a1e9a075c2a86060601bea0cceca34a12eac3660724d600051227cc100700007b8000b52328cd6236a52c4861c7dcd5e7d4b44672aac7661d2b0848e308300c6a13877c82ae3e288e189ea0000369c844a416ca4402e4c950e9c30a52e5c68be18e71239494a90e70445c8c649005615c8083fa8b0000aa40000008d65aaa08e089287540000009e69a4c0c3786486ce720000a5800000000039087c7180380002ca8c40004d263e844d22000000b744c800000070c000c1a6668508d2bb0a443d4d24598000e7a00035e000b92b6eafed30ac48a40000a000099e29a66c5c876c91a684d18cc600000053a72e04a61a8e0f02b4cd6221c8927fe85a00077a526a62662000f106ae7ea7c233c3d8a
  | 12 => 0x7c67a64eeb144ce11e0005ca0005460000000003ded320f0e20a0200082ea743344283be7ae3020000925f032ce482a45200e80000009fecbed542b0e30b5074e000be8000000652ef8a4eb549162f814aaa258206c6701a443edb2e003ae4620000000008e60000aa33a000e8a1e4b4228c8f80005b8bd0d92364b7c000250b1a6d41a826e898abcdaa67ed7a5387d00b8000a1c73c000000ee29300007ac2ec0000000080146dc000000774646ae2d2a04cc3e2ee760000bb6318a7086c2d8000e7c6500000004da71000092a00051a836000198c9a00434627454e0c8de20005d88f04f4bce71492e62eec61406a01b40a6e1e99c9328fc00078c3f625ecb00000006b6cca000b7a0003a6dfc000bf85a00007de6ba000124f0e5f22b64d4d1a00000a000000588000370a0e02eeb2010af81c24e47fa8ec838a7697c1a6590802604494dd6e2ecf4000e84000618bba286342496d58a004848b2d363e4b62628e70044000000000b0a00086688e500ef442634a00020e312a467c8c1684a6c6000000000000000e46372000b82000000000b64000000cbac20a2c170860e2c000988b38000000790b309227f2956310d045a6c500465b4000c744e0966000144bec266cac000db67ce000034776182abe000000eecea2c221360d410c43aed60845e864457c0e21fa0005d60003c0c56ea856cab675ebeaa0ab10a1a07a4caee4a242c6696ce21b84b8c12a66d567368ea6a6dbc242a4a8ce386d20778c72e92e906a89ca7689cc64ca32a14d7e9da64ad64b7e1927f81ba91c0e0960120584340a5ea2006e5be4b6dd8af07a82280fa3984e8c3a8943bc5fa5968e2ebc9425d43a462220a938152012e58aa61689ee69022a5701e26b0e7886e906e7e6f66c27b6204c5841e2c0432a4c002518ede4300fccde33878400658c210e8cda4a98e0cf046f2222d34a22cb47d82b2d8c1669469b6d8e97a748872b2aba2a9ae349528f647846e0a20b2a3ea2e09c6faac0d2687687018039a56670ac64d782aee607e068eb68e66bc85547526168f2e5add000041a74c052506ad4b90ee6bde446a3690067a8341d8cfa1640cc8ccab4da8000c18eb68409e4b885eed8a3baefe8785b2ae023c0407ec542498ed8c98beeba649c2cc74617494c248c9edf0bbed764240009bc77e00066860ea7cc2e896aaaad0000000000000320df6a18ef6000000856a8076e58a000f0a00057aeb4ef02963b2d421504c672675a000e4ad38cf627a4acf08000000e062060f4d7c2d2cf8cd097edb43aa636940a7e3500de2d4344998ca21b23a08c253e68a8041083c85924b2102d5273a2fe09a5404580265569361ee2b8cb6bc6e985d06342deece48652cdacb5a0acc84376c546f47b4148798c769a82d0d160b49268bc214780ac6e724de0626d0722baa69817a18
  | 13 => 0x40e294e5e42a9b4c927cc332970000dc800037e2a2000000c90c267e6e167f016ac2a8d46c80004b0b34d448a0b1680e4d8874eb0c9c706ad8a880009f0000b06074454480b32000000000268ce84527ba8c00000000543b83568ae186c8e0003d602a708c4aa50c1c0000000001ce0005bae86b588428aaaca93488600c3da1ac0006feb3e000ec43acde095c6fc254e22b4021a11a7c407c71cc300008a8000e1c4a4ae89ac5b0b4629e0002e2984df427ec0e5766388881da000c46e6cd0ee4e0009f40c68a6b84a78c1e00012e000594adeceed086924f653c01c000bfe30c0008a2076b3c17831453676acd46e800072c0dcbd4000000e149100005600eeba4d0c9a61062a625c234c2400018c1de88416eb945f8858e1081c26a0001ec0003063b632ee5c
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x904a57118142c82a2b88a699641075cf65d0720c52c5306a91060e635885488306b1ac42a4418558e6115220c4ac5308a91061663584548830ab1ac22a44189589611522086ae232e871043571195438824cb98c0a14412c5c46050a2083ae632a83105187550d30882163aac5a1a412a1c162d0d20932e630284904b1711814248264b98c0a1241385c4605092091ae630284904a57118142482c4b98c0a1241685c46050920954ea302849062a751814248345398c0a12412a5cc6050920d12e63028490489731814248351388c0a12412a5c46050920d42e230284904a1711814248254382c9192410b1d5644c920950e0b2264905457114d3248254382c5a0a412a1c164c8520950e0b2242905457314521482543b28518241461d5434c120950eca126090648654c930482c4ba264982410bdd56290020c1aa6b14801062562546400820eb9eca2004107dd5631002083aed298801041d7654c400830729ac4200418354d621002086eeab08801061653584400830aa9ac2200410d5da5110020c2ac7288801062562944400830ab1aa220041895895110020a52ea2024010589731012008384a988090041685c44048020e42a2202401052975d092008384a9e8490041c8d09514802085ae5b2e878841d73d9742c424ab98c0a0e21295c86050710a8ae429a63885457314921c4318b0cc1aa4218358e6215210c1cc6b10a90860d63588548430b31ac22a4218558d6115210c4cc4b08a908625625845484216b90cba1c210b5c86550e1083ae632e850841d73195428424cb98c0a0c212a5c86050610a30eaa1a610852875509208420eb98c02a2210b5c86015110868eab0e86884b070587434421a3aac3a12212c1c161d0910932e630282884a9721814144268b98c0a0a21385c8605051092ae630282884a57218141442c8b98c0a0a21685c86050510964ea3028288632751814144349398c0a0a212c5cc6050510d22e63028288491731814144351390c0a0a212c5c86050510d42e430282884a1721814144258382c918a210d1d5644c510960e0b2262885457214d3144258382c910a210d1d56448510960e0b2242885457314921442583b28318221461d5434c110960eca0a6088650654c530442c8ba262982212c1d94188110a50eaa1240884b076505204433032a4290221685d1214811086eeab0c8008615535864004312a92c320021075cf651001085ae5b28800843571594400420fbaac620021075da531001083aeca98800842f75588400430729ac4200218354d621001085aed290800860d639484004216bb2a4200218358d5210010c2ca6b088008615535844004313292c220021895496110010a62ea2022008591731011004388a988088021685c84044010e42a4202200853175d051004388a9e8288021c854b4144010
  | 1 => 0x511028ab9ea528881c154e5294440e0ca6a94a2207055354a5110293396a6a8881495cb5354440a2aeb29aa2204367614d511028b398a6a8881499c85354440a4ae429aa2205327014d511028b39ea4a8881455cf5254440a4aeb292a220706539495110382a9ca4a8881c194d5254440e0aa6a92a22043676149511028b398a4a8881455cc5254440a4ce4292a22053270149511030ab18c6a8881499c86354440a4ae431aa2205327018d511028b398c4a8881455cc6254440c4ac4312a22053270189511021b3b064a88810d5d83254440e0a64192a220532700c95110298b8064a8881459cc6054440a2ae6302a220526721815110292b90c0a888107dd95314440c1aa7310a22060d535885110217bb2a4288818398d5214440c1ac6a90a220615539845110312a94c2288818598d5114440c2ac6a88a220626625445110312b12a2288818654e6014440c52a5300a22042d729973110216b94cb188810b5ca650c44085aeb310622060d539883110306a9ac4188810bdd9520c44085aeca906220626625443110312b12a218881455d5310c440c2aca9886220685624c43110382a9262188818654e600c440c52a5300622063151980311030ca9ac0188818a549600c440c62a2b00622069131580311020eb9ccb90881075ce658844083ae7328422041d7598c211020fbb2a610881075d95308440c1cc6a90422060d63548211030b31aa2108818558d5108440a4aea9084220625654842110342b1a4210881c154d2108440c32a73004220629529802110318a8cc0108818654d6008440c52a4b00422063151580211035090ac010881c254d5294040e22a6a8ca020721525465010246b90c0a1e61255c46050f3086ae3b2e859842d72d9741cc30cb1cc1aa4618358e6215230c1ac6b10a91861563984548c312b14c22a4618558d6115230c4cc4b08a91862562584548c254b90c0a1c612c5c46050e3086ae232a851842d72195418c254b90c0a1a612c5c46050d30992e430286984d171181434c246b90c0a1a61255c46050d30b12e4302869859171181434c24d3a8c0a1a61869d46050d30d14e4302869849972181434c344b90c0a1a61225c86050d30d24e2302869849971181434c348b88c0a1a61245c46050d30930e0b1e849849870593324c24c382c899261515c4524c930930e0b1e829849870593314c24c382c898a61515c8514c53083eeab1c801860d6354a400c30ab1aa3200610bdd5621003085aed290801860d63948400c306b1aa4200610ddd56110030c4ca4b08801862552584400c21abb4a2200618558e5110030c4ac5288801861563544400c312b12a220061465d4404c030b12e4202601870952101300c2c8b888098061c4544404c030a32eba1a601870b43549300c389a1aa2980610d5c765d0f2091ae630285
  | 2 => 0xa498863255db424c431e0aa5a126218f0552509310c7a0a9263280634a5c8649403185ae4322a018f12544c5500c788aa262a8063d09493154031e82a498aa018d2972191500c68cb9e84a80634c5c74254031e268298aa018f11414c5500c789a1a62a8063c450d3154031e24e898aa018f11744c5500c789b2262a8063c41913154031e268498aa018f11424c5500c60eb98c0aa643525c0534cb2183ae6302a910d517014d318870731ac52a2438598d619512183ae6302a890c2d72d97434861ab8ecba1a430e1c16550d21a32e029a8690d497014d3248670b80c299243075cf6550521aa2e029a6290ce17018931486a23aa6498a4391195324c52183ae7326a090c1d731815408706a9ac5a18438554d61d0c21e0aa7a0a4210f05535052108782a9e8490843c154d4248421a4aeb3224210d85739912108693baac890843585c35348421a8aeb29a4210f065454d2108782aa2a690843c19d15348421e0ae8a9a4210f066454d2108782b22a690843295db4348421e0aa7a1a4210f055350d21087a0a9a4328043465cc649402183ae6322a010f22544855008790aa242a8043d094d2154021e82a690aa010d19731915008694b9686a80434c5c74354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e468690aa010f2143485500861bb8aca9948183595320ca40d0a64b086520689325803290217b92ca98c8185595310c640d0ac4988632069131580319020fb9aca90c81895952108640d0ac690843206a1215802190306b10c4a9881459c46254c40a2ae2312a62051a701895310287390c2a9881435c86154c40c2ac230aa62051a701855310287390c0a9881435c86054c40a2ce2302a620515711815310306a9cc4298818354d6214c40c2aa7308a62061553584531030aa9cc3a90818594d61d4840c2aa6b0ea42052571d4e521029338ea6a9081495c75354840a1aeb29aa42042e7614d5210287398a6a9081499c45354840a4ae229aa42052a7014d5210306b18c6a9081499c46354840a4ae231aa42052a7018d5210287398c2a9081435cc6154840c4ac230aa42052a701855210287398c0a9081435cc6054840a4ce2302a42052571181521020fbb2a6290818354e6214840c1cc6a90a42060d63548521030aa9cc2290818954a6114840c2aa6b08a42062552584521030ca9cc0290810d5c665cc84086ae332c6420435719943210286baa641908183595320c84086aeb3086420615539843210312a94c2190818554d610c840c4aa4b08642068532584321030ca9cc0190818a54a600c840c32a6b006420629525803210344992c0190818354e62d4440c1ca6b16a22060d5358b5110306b1ca5a88818398d52d4440c1ac6a96a22052572d4e
  | 3 => 0x2de128000000000000000033c50400196128000dd90546e000000ee458100661990464cc001ef000028bc0053b400000000000000e0000000180000f3000764400002ba001230000000000000000065000000000064000001840003f80000000120856000170000cb000760059a0378000000000520000000000000094800000000ad947000000a800008a9242a020000024df1eb31e5e90e90130e1c0de9650000000018a000000da0000006e8000000767f1120000966d48d000238000439a900064d0c8000004bc002060006cc00000106000000002183ac000d4000000000640008fc351e2000000000038020000100000100600c010000040000000200200005803004010010030100000100000401c0280400000000803000004000020020000500100002c0080000000c00000000004008000000000080200601000000000000000020000040180301a000008030000000700100800c0000c008004000010020080000000000000003000004000050000040000000003c008000000000300200200400801002000020010000040100100200c0300000000402001000000008030000040180000200c03801014004000000000040100b000000010000200080000500601c0180000400000800004004000030000040000600001000800004014010000080000000000400000000000000024357118152d0e16b90c0a8e878958a6114143c4cc4b08a0a1e25625845050e1ab88c0a9e85075cc6054742c2ac7308a0a1616635845050b0ab1ac2282850d5c4605533286ae2302a91961563986544cb12b14c32a2650d5c4605513286ae3326a09943571181540ca86bacc899065615c6644c832a1eeab226419706544c9510cb82aa264a8865c1d093254432e0a84992a219707434c9510cb82a1a64a8865c19d13254432e0ae8992a219706644c9510cb82b2264a8865d04c95194032a62e2324a01943571191500cb852a264a8065c25513254032e826528aa01974132545500ca98b88c8a8065c2d093254032e1284992a01970b434c9500cb84a1a64a8065c29d13254032e12e8992a01970b644c9500cb8432264a80650b5c86054f4183ae6302a5a0d0d754c832d070aa9ac21968389549610cb41d0a64b0865a0e195358032d0714a92c019683a24c9600cb41962e030a64a0e85325843250744992c0192838358e6214141c1cc6b10a0a0e0d635885050616b90c0aa6630b5c86055231c1ac7314a898e2662586544c616b90c0aa2634a5c05250931a92e02926498cd170185324c616b94c9a82630b5c86055031c1ac6a968418e2552587420c782a968298863c1549414c431e0e86a926218f0543549310c68abacc898863615ca644c431a2eeab226218f0654549310c782aa2a498863c19d1524c431e0ae8a926218f0664549310c782b22
  | 4 => 0x3867c00184000000000b5000394000003f0614001110000000000047800039800000000000003340000080007e000000000000000000000013d0f8001f42c000000000000691e02160007a11448e085140c9000454000001946c8848000746c4002090000000000000047d1c81f21e69c000000000003c1ee0001f0921e13420009e00000044c000000a22c4a10000000000017b09a5f40017900024469800072174000971542b86e0cd4680007b8900000011c00000082c0005f382068000de244000000e4000000131443be30c741c30ec544d80c71a0000670000ee074000da000000440000007d40000034c2a4290ac000000001550080d80008a1ba720b521831a0000a0003008883715e26855026000000418769a3062000a58280000002098e0005dc0006c0000000023100000000104452178000000003a400000274000000000003100000000057000204414790e3800402000000000003c84f0000b000000000000520f1800000000000000000000000027c00000063092654908000aa0bc038953700000000000072c000000000001593100000000000000000000083120009f80025000c3285a000001082332a60007d8002da848be000000110e880041e0010394007a118b100025a000000000007780000f000000f310814e60c389ec000000001720a075c000a314c86c1f14e000000750d6000608938a22c6061181d2000644000002307247e0000000d0000001de2d10701300004018000084000000003304d4000000000011d9ce0000006c1673f665c8e86733604871a3a1f02d9240000008bcbb000000670000d70007dc0014d000000000000000009d81146a218000e70707c4000990001ed210fd2ac2040017f2360000000c000208000000000000009800011cfd0e104e8f40024a26e50c000d900000000000000000c5800000000a280000087887000000858900002c8138730000000000000000022467930434900c08001d80000000002e814000000001b40000018a36c00000000730e28003587cc00000000000001750000000023e2940000015816e000000000f200000022000000579384565c430a0c0005685f0002e62e5190004280000007a28c0004d043200000d58002d01a4000250042a000000206000811d00907940000046c0004f80003c000001920fa0000013d45a89cb61e945c0000012600090cdb0bd1e226c59188000280ff186000000000000007280000000000000000000000478000007a889000000548fb03c0005851308e0000c800000000000000003da0000000000045800000000000001f00000000000000000068800000258640001f24940b13602a214e98000001d40017417400096006000000f900d0e42ecb582c3a8380d694c38822caf9e8000000001c6000001000000000001b800
  | 5 => 0xb4000f02205800000018c674c6000000834b812a3b67090a8000c40007f8ad1801f8df96e0004784e08439a290000000006b9151070003f87b0a53720005e12b04885d108d50000000000013a45c000000b624cd1000000000000f5124434ab9a43ce6dcff90a166000000000000000002e17e000001d52fc038b30002647f46f9af000198001cf0001ac2ba0306a0000000011a00015000000000fa0000001a09180000084c460000009140000000000000000000000970e200014c5c0000000000000000088c37800320164fc800000001089a8000000001aa00082000000000000198a1000895220002b21d0000000000000000000000000139036000000003b86940000000053c000003ba0000000023200000202000880a48c13ac870000ab0005a4000
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x109e25911d0015021400001397a21c800d1600079a8300000d989495838280208993120f26818024000a8019060000001e801711851f88870000000f800b800000058b0000238e800019a5000e00100000000000000009000122a4800a1b261a1280231f00001d8c009b801c0018200496a1040000068c8800218000000000041000e006810400007001000204002800c10584a05869d13254432b01819d13254032b01811913254032a05854c9610cb41a09854c9600cb4190587991524c431c057654b424c431b01829d13154031b0182191315403191187d093154031905879915348421c057654f4348421b01839d12154021b0183191215402192187d0d2154021c05625c46254c40c05725846154c40c05635c46354840c05735846154840a05854c9610c840a09854c9600c840c05635c86354440c05735886254440c05764c83254440d01325c03254440c0575589310c440a0586549310c440a11854c5600c440e01524c5600c440c057558d2108440a058654d2108440a21854856008440e01534856008440c81729c46050d30c82725c46050d30c81725c46050d30891811c163d0930891811c164cc930891811c1644c930889821c163d0530889821c164cc530889821c1644c530d01525c4404c030d0172544404c030911811d5434c2208a1811c162d0d20c81739c46050920c82735c46050920c81735c460509208a1811c1648c9208a1811c1644c920889831c162d0520889831c164c8520889831c164485208a1811d9428c120908855d1324c1209098754c4048020d01535c44048020d01735444048020909821d5434c210909831d542482108a1821c161d0d10891831c161d0910c81739c86050510c82735c86050510c81735c860505108a1821c1648c5108a1821c1644c510891831c16488510891831c164485108a1821d9418c110910855d1314c110891831d94188110920855d121481109118754c4044010d01535c84044010921875484044010d01735484044010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1074
  | 4 => 1930
  | 3 => 587
  | 2 => 78
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
  | 6 => packedAt s3K6 (864+((h/16+packedAt s3K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s3K5 (32936+((h/358+packedAt s3K5 (28998+(h % 358)*11) 11) % 1713)*12) 12
  | 4 => packedAt s3K4 (81056+((h/643+packedAt s3K4 (73340+(h % 643)*12) 12) % 2317)*12) 12
  | 3 => packedAt s3K3 (30908+((h/195+packedAt s3K3 (28763+(h % 195)*11) 11) % 1133)*11) 11
  | 2 => packedAt s3K2 (4862+((h/26+packedAt s3K2 (4680+(h % 26)*7) 7) % 124)*8) 8
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc3cf3f9fff0e38fc7e318f8ffc71c7c784f0cf
  | 1 => 0xfc0fc7e38ff03f1f8fc1f1f1c381f9f99b4333
  | 2 => 0xfff007fc0fffc01ff1fe01fe03fe01fe638c3c
  | 4 => 0xfffff8000fffffe001fffe0003fffe007c0fc0
  | 5 => 0xfffffffff000000001fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x410080010041008000020240104040001045
  | 1 => 0x44221108122090281040909088809091094112
  | 2 => 0x8880a201244402500292012411240124228428
  | 4 => 0x11040052488820012525240022492400540a80
  | 5 => 0xe228b45b00ed349a49f9c9c9380c34357fe000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xfefeeaeafefee8e8fefeeaeafefee8e8fefeeaeafefee8e8fefeeaeafefee8e8fefeeaeafefee8e8fefeeaeafefee8e8fefeeaeafefee8e8fefeeaeafefee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x904c1800024540000074000008d5994e2c01b0430028443800a3490000002000f26a40140a1150030941960e790a0007cb8938000111a240100004100004000003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe617e52cc2faa5986fd0b30dea1661df32cc3ba65985f94730bea8e61bf41cc37a839877cc730ee98e617f548c2fca9185f55230be2a4617d538c2fca5185f54a30dfa1461bd428c2fca3185f54630dfa0c61bd418c2fca1187e90230fca0461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8987790d30eea1a617f524c2f8a4986fd0930dea1261df324c3ba64985fd4530be28a61bf414c37a829877cc530ee98a61fa404c3f280987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4187b94830b7290617d520c3daa4185b54830dfa1061bd420c2fca2187d94430bb288617d510c3eaa2185d54430dfa0861bd410c2fca01877cc030fd18061dd300c3f26018764c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641ee42c837a85907b50b20d6a1641ee32c83da65905f94720bea8e41bf41c837a83907bc8720f690e417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d528837e85106f50a20bf28c417d518837e83106f50620bf28441fa30883f261107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41bf42483dc84906f50920f6a1241ad42483dc64907b4c920bfa8a417c514837e82906f50520f790a41ed21483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea10417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e50083de40107e88020f690041f920082fea9885f95310df2a6213e54c42faa9886f553109eaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c437e85886f50b10dfa0e21f641c437a83887d50710daa0e21f631c43ea63887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c217f52842fca5085f54a10be29421bf428437a85085f54610dfa0c21bd41842fca1087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a217f52442fca4885f54910be29221bf424437a84886fd0510fb20a21bd41443ea82886d50510fb18a21f531443ec42887d48510fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810bf28821bf410437a82085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5250778a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837e541067ca820df94c41bea98837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc77e8598ef50b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718df94a31bea9463bf428c77a8518df94631dfa0c63f6418c77a8318fd50631daa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c6f8a498efd0931dea1263df324c7ba6498efd0531fb20a63bd414c7ea8298ed50531fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf298637e520c7dca418db94831bea9063ed520c6daa418efd0831dea10637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21bea9e437c53c877e8590ef50b21f719643ed32c877e8390fd90721dea0e43f541c876a8390df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710df54e21be29c437d528877e8510fb90a21dea1443ed428875a8510df94621dfa0c43bd41887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e544877ca890cf95121beaa243bd544867aa890df15121bfa9a437e53486faa690df14d21dfa1243bd42487dc6490fb4c921dfa0a43bd41487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf42087dc8410ef50821f6a1043ad42086fca210efd0421fb20843bd41087ea8210ed50421f790843f621087da4210fd48421f2908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81bf41d037a83a05f55240bf29c817d539037c87206f10e40bf294817d529037e85206f50a40bf28c817d519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4207b94840b7290817d52103daa4205b54840dfa1081bd42102fca2207d94440bb288817d51103eaa2205d54440dfa0881bd41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9987790f30eea1
  | 2 => 0x101c018000020040000080000c034010040080100201000a0000400e00001c00001002000008040000340000300200000800012024008000080000000001000000000012008000040140080100101a0000000000000800801bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf28887f65110eeca221df54443faa8887755110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a17d94742bb28e857d51d0beaa3a15d54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f94742db28e85bd51d0a7aa3a16d547429aa8e85bc51d0b7ea1a16f94342dea8685bc50d0afaa9214f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42df21a85bd4350b7886a17bd0942df212857f5150af8a2a15fd4142be28285bf5350b7ca6a16f54d42de29a85bf5250b5ea4a16fd45429fa8a85be5150b7aa2a16f14542dfa8285be5050b7aa0a16f14142bf2a0853e5410afca6215f54c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465bf428cbdc85196f50a32f6a1465ad428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1265ee424cb7a84997b50932d6a1265ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d07dca5a0db94b41bea9683ed52d06daa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0ef54f41de29e83bf52d077ca5a0eb94b41dea96833d52d075aa5a0cb54b41de29683bf32d077c65a0ef4cb41de19683bf50d077ca1a0ef54341de286837d549067aa920df94e41bea9c837e52906faa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0cfd4941df29283b
  | 3 => 0x55e0000024600051ce096557056ce882f324bd0e300003ad3958000000b5c000000005dd13000000a40000000868b400249000a596606b212001570b71c25f490811110a3c002c469400174b3b4c68d90d9181cab58000812da19c502a71fc355602fc000168650fa3027c9450c11de7a195a1c298000003501ea848001f60001e9531262f2b98000000006758aa0200058c690c6274000000b45c80000002b00008400000000cbc000000000000000000006920800000d740034d282680658af6b80000036b1d89f4209cd43000026a340eeb489e00007a2f4000f86e00000006400044c0023e57a001339431985713c00060a5ece5182000001a30084ac108d50992cc8240c8f60007fcba9bc0003dd508000000013f000000aac368e922447413880442cd5459ad54600000000000c900007e00042c000000000000012245c000588005727c0001af4560011d194000000000be31a64d251c200436ce40e21283c56d1db000000000004d0ce034ab2000b8032a0b2e8c716719f20a968000002fcdb400000566c3c000003be000002f140c4b938b3c00015856a1600000003372526a892a8003927dc002f0000784d101500e28c281701b06c81d05d2c28a0001554f85c96799e068db9961f8000944e7800000000560840003ec0004867e000202222500010f2874404d49382e44a914002485d0c0cfd24d2466202a90f342b147695a0008bc00073000b283099a0445fdaaaf52d8048b99fc2f00010691564aa00a426b0d00006f000654000000000000000000012c000190005eed7800000000000cb9195b64680030d0003a85d308454940000000000014680014eb940029737000000000000d200009e000000002c9320dcd01aef686c28738001c6400a30000000011c0896b200000051530534001cb4dc2a10012d12ed9c0523f4207bd2e800266110000002c4000000000000000009c0001b800252000ce4000006340000000180000002c0300300e008028030000340080200401c010000260180601a0020000380206800400010006000000120040240080300e00400017026000038000020140000200400000806000000028030080040000000000001800010008030000000340000202200c000000020100200101601003000002000028020140100200500001c0082200600c00800000018058020000000f00400a0000380101a0240580001a00400804010000108030060000000400600c00001000000010010000000000700a0280080000001c0000100e0000000e0020181880200e0040000200803400006004004028010120000280a00a008028020080000380900002800005004024030020000140300000e004020030020040000000000c0600200a0000200000200000800000000020000040140000a00e000000000040000000
  | 4 => 0x145506240000022ea380023158c1ecb028349cc453a80020e4a56ab5a4cada5a39a4192298fe8002f4d94c6272488d8c97a9c0000000009b00085c432ec3c4000000f4000000f500020c00000000000a78000230004800008e000508da0b93ca000002eb644000000005ce7398f0b8374445198000a80f00009f0f8c657da54178d003610e000000020104d80002307f642000862b5000000458005f25f135000000d501c8e0000b74000005767646d0004220006825b000000001ae10a0009c8030e00006e0b3000cc4003202c83089d8000a40014a214484d595021f00091c0004a2ae874b527a000574001d5000be8001370000040000012a000000c3000b794f85b09c3f0000001768ece38003c00000000000000000169000af09a0fd23c000923026b6970759f10f00013d9d73982b87702c3d859c92acd3b0810b72736a6930e8223296a18eb0001209d16c1ab600c599b80d36a9fc1a80021a000c2b6864c00130323000001310000001a8001040004415b0145dc180000002b261074000000001a080011a000fdb640000009609a0006940000031c420001da3ce00184800000538000332380c498000000ca1b50134525bcf20cd1425105b0935109dce188a13061d71b6f3ba000780756d89e4f320809e2a5682b13720fc0000063a61800000000275380e62622acc595003e0002e0765480000000017e000580a5000000cc34900000099140144524488004ae000ab2c7000a31a605f000b64dba9167a07816872652000d42241887e463b623a40000003e3c6cf83c8aa0000005900006c0011e00032a978f48450602d52035840a00043b2d44e015560630e830156ad300003d80a0c0009bda90712a43517998f6609847c8c5534d15750666cc5c540b0e380d858a15846037d6fa13000409a78170000008f80e4b2cd80008f5ec0980030c2540240013e00000068800000b85b8ac1000c1c000000003c9052846081f40b317584000679bb56e5d8001d4000000001b30000016410a5fc164461ed1b20011ca5f0007d0002850386980000064eae90094a2d69a40000053a68d8d86f000000a99f33606b0000000000001000034e8d40002a148d10001c50007ac0da66190601899990181252799b04894cd8b3a6162494a8e4620001038005f00015a2cb3380001d80042aaa400000000000df800000130002dc0003395534200002cb40003dc000d48250ae7f8df00057c7790c8d654a188af1bd000a08001dc06ed8079996306afc00000000c480013805092c41af20a67d46eac3000459970d346e000001b6696b884100041e868000000000013b0385da0017fb51388ccd4915f0b040d3214541c90c00154322a6cc531f08ed7d3685e458000002990008c98c12b0003fc0004b5a835c003062a20000011b6aebf54480000000014800
  | 5 => 0x29e000000000000012c000000cd0001360300011e800000cc89ead120274c9f9
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xa54c426d6295310ab58a54c432e62953108f58a54c432d62953108b58a54c433661953108fd8954c423e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c42b561d0b108fd9542c423d6550b10cbd4942c432c5250b10ab58b41c43365450710add9541c43376550710cdd4d41c43355350710add8941c43365250710cd14941c42b5648c710cd55231c4335544c710ad59221c43a54288710ad59121c436452487109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f992528423d6494a108f990528423d6414a109798c528425d6314a10ad587428432e5250a10cb54942842ad62d0610d614d30843a942482109b98a544426d62951108fd91534423c6454d109bd89534426c6254d108f990534423d6414d109b988534426d6214d108f992524423d64949108f990524423d64149109798c524425d6314910ad587424432f5250910cb14942442ad62d0510ad59241442746550510bc18141443376550510cd19541443375350510cd54d41442b76250510cd94941443345250510ecd8141443b06050510ad5923144274654c510ad59221443a542885109d19521442b56448510d914921443b1418c1109e1953044358534c110ec50530443d1314c110ec50620442786548110ea50920443b14148110f848520443b141c41109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423f61550108f585540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810cb951520432d5454810d394d520434d5354810cb991520432d64548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b42042b561d08108fd95420423d6550810c794d420431d5350810cb949420432d52508108f992510423d64944108f597410431e53d0410c754f41042ad62d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb54941043365150410cd553100435553c4010d954b10042796584010d654e100436952840109dd9510043355444010d554d100436552440109ed9510043595344010da54910043b34144010
  | 1 => 0xc31d54cc030d354b300c35551cc030ce552300c2d9638c030da54a300c371518c03097d95300c31d544c030d3549300c355514c0309ed95300c339544c030da549300c371514c030b6d95300c35b654c030e6d91300c398644c030d6d51300c39a544c030d6551300c399544c030c6551300c3ca524c030d6549300c3c9524c030d2549300c39b424c030e6509300c3d2514c030d6545300c3d1514c030d4545300c39b414c030e6505300c27661953209d58654c82b56195320cb98a54c833661953208f58654c833561953208d58654c823f61553208f99353c823d64d4f208f99053c823d6414f209d98453c82756114f20ad58742c832e5450b20abd9542c832f6550b20cbd4d42c832d5350b20abd8542c82ad648cb20cb55232c832d544cb208f99251c823d6494720cb50a51c823f65d07208f59741c82ad62d07208fd9541c823d6550720ab59321c83a541c8720ab59121c825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d58453882b561d0a208f992518823d6494620ab58b41883365150620cd5454188358534c2209d986544827561951208fd91534823c6454d209dd8553482746154d208f990534823d6414d209d98453482756114d20ad58742482ad64909209b19542482e86050920cbd95424832c6550920cbd4d424832d5350920abd8542483ab6050920ea18142482ad648c9209b195324823e64145208f590514825e63145209758c514832d4214520ab58b41483375150520cd14541482ad64c8520e950721482ad6448520d914521483a9428c1209e1953048358534c120ea50930483c9324c120ea50b204825e63d50209758f540827661d50209d587540823d65950208f586540823f62550208f589540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208f992520823d64948208f597420831e53d0820c754f42082b561d08208fd95420831e5350820c754d420832e52508208f992510823d6494420cd95251083355494420d594e51083555394420cd99251083356494420cdd0a51083354294420cd95151083355454420d594d51083555354420cd99151083356454420cdd09510833542544208fd97410823d65d0420c794f410831d53d0420ab58b410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd545410832d54c8020d354f200836551c8020d654e200837151880209bd95200832d5448020d354d200836551480209ed9520083595348020ead09200837151480209b98
  | 2 => 0x5250a40cb54942902ad62d0640cd945419033551506409b988535026d6214d409d98453502756114d408f99743502b561d0940cbd4942502ad62d0540cdd45415023d6590c40c754e431031d5310c40ab58843102b56110c40ae580431034e5394840d354e521034e5354840d354d521032e6454840cb90d521032c4354840c794f421031d53d0840cb54b42102b561d0840c794d421031d5350840cb94942103565394440d554e51103665294440d954a51103374294440cd50a51103565354440d554d51103665254440d954951103366454440cd90d51103344354440cdd0951103354254440c794f411031d53d0440ab58b411032e52d0440cb54b411033551d0440c794d411031d5350440cb949411032d5250440cd945411031d53d0040cb54b401033551d0040d654e401023f6550040c754d401032d5250040cd545401027b6550040d654d401026e62153309b58854cc27661153309d58454cc23e6494b308f59252cc2b561d0b30cb94942cc32d5250b30e350932cc23e64947308f59251cc2ad62d0730cd94541cc3355150730e550531cc26e62152309b588548c27661152309d584548c23e6494a308f592528c2b561d0a30cb949428c32d5250a308f992518c23d6494630ab58b418c3365150630cd545418c23d62d51308f587544c23e64951309b988544c26d62151309d984544c27561151308f994544c2ad6215130ad584544c31d6315130cb988544c23d6215130cb588544c22d6215130cd984544c23d6115130cd584544c2356115130ce580544c31c5490d3097195434c2d86050d308f990524c23d64149309d984524c27561149308f997424c23c65d0930ad587424c23e65509308f195424c38d424c930b6181324c23e64145308f590514c26e62145309b588514c23e65d05308f197414c2ad62d05308f995414c23c6550530e5505314c2d8604c530ce152404c39a43901309e195404c2d86350130e650d404c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c23d61950308fd89540c23f61550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c23e64948308f592520c32e5494830cb552520c32e6494830cb592520c32e5454830cb551520c32e6454830cb591520c23f65d08308f597420c32e52d0830cb54b420c2b561d08308fd95420c23d6550830cb949420c32d52508308f992510c23d6494430cd952510c3355494430d994a510c3655294430cd992510c3356494430cdd0a510c3354294430cd951510c3355454430d9949510c3655254430cd991510c3356454430cdd09510c33542544308fd97410c23d65d0430ab58b410c32e52d0430cb54b410c33651d0430cd547410c23f65504308f595410c32e5250430cb549410c3365150430cd545410
  | 3 => 0xa21add85428872f6550a21cb195428872f5350a21cb54d42886af6150a21e9d8542887a46150a21ab58b4188735548c621e950a3188735544c621e950931886ad64c8621cd553218872d42542219b58a544867561951218f58a544872d62951218b58a544863d6195121cd586544863561951218fd89544872f62551218fd85544873761551218f993534863d64d4d218f990534863d6414d219e98053486796014d21ad58742486b76150921cb552324866c654c921cb55132486e4614c921ab58b414863f65505218f59541486af6250521cd5523148674654c521cd55131486e4624c521f14c9314873554c8521cb552214863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863e64948218f592520863d65d0821c794f420871d53d0821ad587420866d6590821ab592420874d5390821b9586420863f6550821c794d420871d5350821cb951420874d5350821abd95420872f6550821cbd4d420878e5350821cb54d420878d5350821c354d42086af6150821e998542087a561508218f992510863d6494421cb50a510863d65d0421c794f410871d53d0421ab58b41086756590421ad59241087555390421b958a41087a542904218fd95410871e5350421c754d41087365450421d554d41087a64250421e950941086b76550421cdd9541087375350421e594d41087355350421e554d41087155350421add8941087a66250421e958941087365250421ab593210874d53c8421e950721086b56488421d554e21086e56288421e950a210866f6548421ab591210874d5348421e9d0521087a541484219dd9521086b56448421d554d21087a74248421e950921086e76548421d9d9521086e76448421e999121086e56448421e959121086a56448421e995121087a55448421d9d4d21087c65348421d954d21087c55348421d154d210873a5494021ce552500875a5394021d654e50087a94294021ec50650087e12194021ced0a50087394294021ced0650087394194021cb50950087354154021d9485500873a5454021ce551500875a5354021d654d50087a94254021ec50550087e12154021ced09500876a4254021ce50950087694254021ca509500873b4154021dc90550087394154021dc50550087314154021dac8550087722154021da48550087712154021d8485500872d52d0b40ad58742d02ad62d0740cd54741d02ad6210e40ad58443902b96010e40ad587429032e
  | 4 => 0xf99442506e662d05419798c505065d63141419b988505066d6214141ad58653506b76154d41ab98853506ad6214d41ae98053506b96014d41cd58752506b56194941add85525072d5214941ad98732506b561cc9418f996325063d658c941add8532506b4614c9418f994325063d650c941ad98432506b5610c941ae98032506b9600c941ab98b51506ad62d4541ad58f51506b662d4541e998b51506a662d4541e958b51506b560d4541a798c505069d6314141ab98850506ad6214141cb98a541072d6295041cb54b42106b561d08418fd9542106ad62d04418fd9541106776550441cd951411066e62153319b58854cc67a60153319e58054cc63e6494b318f59252cc6b561d0b31cb94942cc72d5250b31e350932cc6ad62d07318fd9150cc63c64543319b98a548c66d6295231ab58a548c72e62952318f58a548c72d62952318b58a548c73661952318fd89548c63e6494a318f592528c63f65d0a318f597428c6b561d0a318fd95428c63d6550a31ab58b418c7365450631add95418c7376550631add89418c7365250631cd505508c66e62951319b58a544c63e64149318f590524c67a60149319e580524c6b561d0931cbd49424c72c5250931e3509324c6ad62d0531ad592414c6746550531b518d414c7376550531cd195414c7976350531e518d414c6b76250531cd149414c7973250531e54c9414c795418c531cd507504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63f62550318f990540c66e62150319b588540c67661150319e980540c67960150318f992520c63d6494831cb952520c72d5494831cb992520c72d6494831cb951520c72d5454831cb991520c72d64548318fd97420c63d65d0831cb94b420c72d52d0831ad587420c63f65508318f595420c72e5250831cb549420c63e64944318f592510c63d65d0431ab58b410c72e52d0431cb54b410c63f6550431cb949410c72d5250431cd945410c74d52cc431cd552310c765528c43197d95310c74d524c431e5d05310c677654c431cd551310c765524c431ce952500c7395494031da94a500c7695294031ced0a500c7394294031ced06500c7394194031ce951500c7395454031da949500c7695254031ced09500c7394254031ced05500c7394154031d6cc5500c7723154031d64c5500c7713154031cd58654c863e64d4f218f59353c863e6414f218f59053c867a6014f219e58053c872d548cb21cb55132c86ad62d0721cd95241c86af6250721add9541c87376550721cd19541c87375350721cd54d41c86b76250721e9d8941c87a46250721e98c941c87a53250721cd50550c872d62952218f993538863d64d4e218f990538863d6414e219e98053886796014e21ad587428872e5490
  | 5 => 0x4250a5e63141429758c5050a7661141429d5845050aad6294d42abd895350ab66114d42ad5845350aba6014d42ae5805350ab661d4942ad5875250aad63d4942ab9875250ba661d4942a99875250ba561d4942ab5835250b355114542a798c5050a9d6314142ad9845050ab56114142cd9865410b356195042ad5874210a3f65508429bd954210b2e54508429d98454cca7561153329e98054cca796015332ad58742cca3e64947328f59251cca3f64543328f19150cca7661952329d586548cab56195232cb98a548cb3661952328f586548cb3561952328d586548ca3f6155232ad587428cb2e5450a32abd95428cb2f6550a32abd85428ca3e64946328f592518cb2d4294632cb509508ca7661951329d586544cab561d0932ab592424ca6c6550932b318d424cb2f6550932cb195424cb8f6350932e318d424caaf6150932e350a324ca3e64145328f590514cb2d42145329e980514ca796014532cb50b504ca3e64141328f590504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f586540ca3f61550328f990540ca6e62150329d984540ca7561150329e980540ca7960150328f992520ca3d64948328f597420cab561d08328fd95420cb2e5250832cb552320ca5f654c832e3d09320ca6f654c832cb551320ca3e64944328f592510cb365494432cd552510cb366494432cd592510cb374294432cd50a510cb365454432cd551510cb366454432cd591510cb374254432cd509510cb573254432d98c9510cb553254432d94c9510cb3a5494032ce552500cb725194032dc546500cb3b4294032ce50a500cb3a5454032ce551500cb725154032dc545500cb3b4254032ce509500cb5b3254032da8c9500cb593254032da4c9500caae6210f41ab58843d06ba6010f41ae58043d072e6454b41cbd0d52d072e4354b41cb50d52d072c4354b41cb54b42d072d5290b41cb94942d072d5210b41ab98b53d06ad62d4f41ad58753d06ae6214f41ab58853d06b56114f41ae98053d06b96014f41ad58752d072f6554b41cbd4d52d072e5354b41cb54d52d072c5354b41cbd8d52d072e6354b41cb58d52d072c6354b41cbd8552d072d6154b41cbd8152d072e6054b41cb58152d072c6054b41cb54852d06b56114b41cb54b32d063e658cb418f59632d072d528cb41cb54932d063e650cb418f59432d072d520cb41ad98432d06b5610cb41ae98032d06b9600cb41ab98b50d06ad62d4341cb54b50d072d5294341cb54950d069e6314341a758c50d06ae6214341ab58850d072d5214341ad587429072d5250a41ab58b41906e662d06419b988535066d6214d419e98053506796014d41ad98643506ae6210d41ab58843506b66110d41ae98043506b96010d41ad987425072f5250941cb14942506b461509418
  | 6 => 0x2800002003018004068000040000b00100a0100000000401c010010020140280002a000020020020040000a00201001800002048000000000040000901000800001002008010010020600080b000004000050020280080001a00c018010120000080101600c01000006000008020020080600100403c0000900000003801014000058020000040080801c004028000120200280400000c0180701004c0280300c0000000c000004008060000240300000406000001024010018020020040100001c00c0100000a0000000000201000000002000008000040000580800401c000000020000000d0020000200000400002004008000008000040380101b0060000380200600c03004000018038050040040280b004004018040060000f8050000000d0000020040100000c0200100700005c0101300400001800004004018050060000080200000000003000010038020080180500c00a0180401300000005001006004000000200080100300604c000010000040000b0040040300100600c0080100600000801002014000000020100080400a0240b006000018008020000080200400000402805014000000000060040480100202c0880101400008808008004000000020440300b004004010020020600200100c000010020180100080600800000002004028030020000080000301a0040100000e00c0000800e004058080060080100200e0000c80000000c00012002020038000220080080e01e0040101600001c000000040100380500a0000980000a00004003000000048020000300000200e07c00001000028048000000000800000e0000f000004000008030040000100000c0180080c0000040180000000400010002000000019b9885050e6d62141439d9845050e7561141438fd954310e5f6550c43cb9915210f2f4354843cb50d5210f665294443d954a5110f665254443d95495110f366454443cdd0d5110f354354443da94a5010f695294043dc9465010f715194043da9495010f695254043dc9455010f715154043ced0d5010f5a4354043ce50d5010f594354043ad98443d0ab56110f42ae98043d0ab96010f42cd99151d0b374354742cd90d51d0b354354742cd10d51d0aad62d4f42ad98753d0ab561d4f42ab58853d0ab66114f42ad58453d0aba6014f42ae58053d0b376554742cdd4d51d0b365354742cd54d51d0b345354742cdd8d51d0b366354742cd58d51d0b346354742cd58951d0b376054742cd98151d0b356054742cd18151d0b355114742ad98750d0ab561d4342cd54750d0b355194342cd54550d0a9e6314342a758c50d0ab66114342ad58450d0b355114342ad5874290ae661d0a429d9845350a756114d429e9805350a796014d42ab98a4350aae6210d42ad9844350ab56110d42ae9804350ab96010d42b9987
  | 7 => 0xd427f1f596d80022d8230001ef80000000010900008d97c1551262468491da1d50000b90750001d380000010726328f91d0951e6800000000000127a76a0127b1230df182a4825e18421611a80014f1a580003f80017f98e02f00319603f094a2380000020011b9a52a227980029e9e00169d4a061620ea9080d295c9769b022f8f08b61e2800239aa780000008b0001360760cf08e800270a858001809cc0e58628d01f387c00000014f8000eb29b00018a0c790e11c04b80880000002680000000009b0250cc160000000110a3da72086a5100013f864a119069e126296e0af85906b80011523eaaa80000020287d8aea6fa9095b2190000549e39ab00c01f9b78000001438001df0001f40000c6a521140351cd9948aba4b8001b80281ed80006004c8c28dd9e329c13d298800212993991a1ba7296a9b60001f7000293000090090a8880000023291916c8f18841f22910c881301a80000000016300808d0000000371318000c327399281d0f61ec09c1bb0002590000000000001c40c193d9c59ff0a7800000000002000000000000028902a9d8aa80a139a6800000000021c26018aa608000000000000109248dba679d31fd9480c48ad8000b78cf8002138000000a800010113119e0000000830cb1af80028016f0000001c69b88771d41509149501ea2891a085203410501181c9d70d8000019181a8d2aa07a05391f85f8928fb00021100012ca8b8000ed8310878e980000000010b8000df8702179888990000002550f40bf818800162a949d803c042082084a93a1719f8000180b699885d84a00000000022900000000000000000019a80005a80002a9af05417b00d24a9a79b31380001812a398584815d93ba55831a7817402e2638e11ae92888b8889671b986900000012f80000000023600024500000000000012a80000015a9d615c0000001298978ac00010d0001b689416409a07b9ffa3d00003d9ba9468440000000040e90d49720002048320620001a1256825800134a7ca1d8000b08001730418000fc8000720378000fd8000f680016c0000161358000002038000002a51599c2170a14aae8000de15b84e00003b8ac8028148711f18001bc00b8000000eb98024c98d88584e80006e80029789da8492c04d00012700010300000000012219c8002081099b394da5300b209a3b9bb8f78399040201e49a016d0d08000e42a416b1a3a27287000237a3fa5a0388000bc812a8e8001bf28e01d80000027010c8e08b30ef1f096e8d72af02796f80029f8bda031da9269d681b9911bf8001bc86625b86a0980a200000000000000013b2790000000fa8bb25480a9638179f50c980000000015ea539d28e3a7a00018f8000860000000039728450000000001210002578001451de820a1e98f17ea9e1c80000002479f
  | 8 => 0x6d9520001c300d8001b9281a698000b81fe8bf00e9608001bd9f491b21b07e0e50d1154a9692580018b80022680018b00016183e800000000070857a470aa26d0000000001a20238439a9079859aafa7e00012e8c10ca07ea48a8297a0488d60000a500029000022e00000018300000026f1c780000000000015100015580000005b08c25f8000000cb80006800000000014892e0000470000000001c11898fba2c8002090d7990a508000000000000e21998c0210891a0880000020e00000000000014ba3a8cc82180000002a00000000000000000001e1902441f793a944000000046a4e8b394b147a5400028f0000ca8000001e78002a300000005f13c9650f294e06121d25609f82d80000000006f18c8651df8000000000c382297188c8d19fba230e491a2a715600627d0ce08980013880029600000000013a00005514a0f586e20f1f121f8c62228000580000000001ac29588a2380719ef2168001f323f00023c1ce0962759d0a1889397914aa2b92b21a8000b88c210f8001b2156aa61920000e69a2856971287a1510220d8988b72050588001178001701ee26c0000098880248002a1aac0c90139d027c0000000001c08000000a58170d20000a497e02c24983aa370778000000000001dc96780000000003004580018700001f0000001101c98001ca8002a88f313f0002640001331129a720700000000024206a9d599a02d0001420ed1a88e0221285000141a0c02fa5f00004b00029c8000000001308001518000851e21a41b29de0001699f98001208731491048ab00000000023320b00000024d876a688000cd89326e8959fa00000000001b00013280000002700020a8001d10b20b2a2494ca369cd1b51321dc1c70669fd0002308a40001852661e18a90000000fd23e1a303a03c8001dd8002648000512289169fa8091d199b1202a981401010ea6682600000000000017724594d000061a5a9570f52121a61f02659891aaa5c86c9e50b995785d0002ae0be1ba17d9a183d26d80025806088380000013000027d8c8174a8a80027700005c1b5a100da8000000000000ee8000ba8000001e9166015a2a1c1a8a2880000000002432320d69e40000001c5000252800278a8b25d8ba2ad8000000001682618f48e88560078e300014c2830d98f881a26a8d8a301078808000001690000000f10460de9408000001c28e817380000019900024086780000000013680000000029700000000000024d23c87380024f8a88b400006383380006880008fa8108f0e7a6e1b11fc06f8a394617890602206d14e8a9800050a6910a2ad00000026b0002079b08002a00dc87f1158001cfaa68da28da0206b23128400022990f04029280004a95f1970f82a28198002671c012d17794000000020d1758000570000001370fe8002998b5079
  | 9 => 0x1119b703280029a8b10dd2ac87485b80000001c00011e0000002140000001c90122941611e600018802927500022b1ca2400999b18fa17a9f618d02b15f9dd13e0ffaab1cba439aa0d5165800004a009449e801e8430db166a2091f1411e89cb124231a491eb0699160000001ae0000000000000000ec00000000000000000007a90b10aa3a0ef80080015904f98622400022c0e627329d0a282b97987d22217817b85e00000000019500000000000019ba3489b8e2905896a0ca6a00000000014980023b00008900024f00020e8640002281ea8c0aa912d80017d12521c8000a18d90500001ac8002358001170000d31a82388001c485ea8c0050bd25b0002518a015800fa05a2f00000010192f0001688000000ee1f880000000005280014292820a0a70001008000000000000000000000000000000380000c70728eca3509209a952a411fb0810cd00c8000000801088001f6a9a0bb91c99f21a0530001f815419da4c1379d7a0b86c09f17507808e2610630a10818000000ce92ba6c91110c0000000298001c60000002428c50b584991328389100e24a0001532a080000012a00005caa482100009e8ff1d8a262981c384c187a4e1340000000000000000000000000e70001941821181139be0000000001bea8ca860000000000000000000001218a60000000829978d393900009d1ada340390001350358f38000001b48001458001291cc99d00022e8011982198001a9996a7f8f90360369198070001e0a339d20000ae00680000000000000000000000010d8000002040001bd18483300017c8000001228001d9a418be8000f987ca449e9a6b89c8ad2598000448111fcaa584d98e8b18002749e580027e80025c03b00018380000014303095a1f90000000a300000000029f0c400000000007880027608a9338000002868c5a1e1eea159aba621e72250348b48fc291958a9b8fe23922199c0af1121db92384f24607b04280000000000020f800001a7baab8b016ba6500019580000000018686593e953947000087000000000000271220118a279ce9d9000000000164800289a2d1cf0e184780000011e8000000000000000240f72a110380007400000f0000000518000000002258670d5a06a95055aa822aa571a49db0000970a0a1819e89e0000a68dc2742588000002718f21b417629202c80027795d21f1ec80587fa9902e8001fe0bc13c1c8a5003e25e9a696a0001ed000000000000000000000100201a5d1930001ad0f028080000005a21301515e00000000027a80024b0ea11d98c00017f0000001eb800075a820410408000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1842d72992518c21bb8ac5aa2610bdc961d5130c1ac6b10a89862562984544c30ab1ac22a261899896115130c4ac4b08a89861963580544c314b12c02a2618c5856015130992e430286984d171181434c21ab88cba12610d5c46550930a18eaa12649849974181324c268b88c0992610b5c865d053085ae432a829851475505314c24cba0c098a61325c8604c530992e431a80984d17118d404c21ab8ec4aa0610b5cb615503086ae3324a41852571992520c292b8cc8a90610d5c765d083086eeab0e841862652587420c312a92c3a10610b5ca6494430a4ae5324a21843576d0a510c292b94c8a88610d5db425443085ae5b2e821842f7558b410c216bb4a5a08610b5d952d0430c4ac528e821862562547410c2c4b90c898061645c4644c030a92e5aa2601855171d51300c28cbaca898061469d9544c030a30ecaa2601851b72551300c28db8aa898061c2552524c030e14a8a92601870954549300c3853a2a498061c25d1524c030e16c8a92601870864549300c28cbae8498061c254b424c030b22e3a12601851975509300c384a928498061c4552514c030e82a528a601871254545300c388aa2a298061d0949514c030e82a4a8a601871274545300c388ba2a298061c4d91514c030e20c8a8a601871342545300c388a12a298061465d7414c030b12e5a0a601870952d05300c388a8e8298061465d5414c030e12a4a0a601871151505300c313312c32a6410d5c664d4f20a4ce32a285904a571d9542c829338ecaa16410d5c46454e20a32e829a61105517114d3088264b98c0a1241385c46050920a4ce3b2a849042c7654d424829238aa6a1241625cc6050920b42e2302849060d63508514828ab98a2a0a41895905148520a8ae628a42905197414d30482a8b88a6982412a1d9424c120a90ea992609061653587420830aa9ac3a10410d5db4254420c1ca6b16821060d5358b4108312b14a3a08418958951d0420a52eba12401070953d0920082d0b8e8490041c8d095148020c4ac530ca98842d7299353c4286b98a4a1621499ca545071094ae5b2a838852672d9541c421b3b4a4a0e21455cc5250710c4ac829243885457314921c4216b90c8a9c21465d0534c210a92e429a610850d731494244268b98c0a0a21385c86050510a4ce5b2a82884347654d4144292392a6a0a210d9da5250510a2ae629282885917318141442d0b90c0a0a21895905248510a8ae629242885197414d30442a4b90a6982212c1d9414c110aa0ea98a608862865509204431832a8290221981952148110b42e890a408842d72d85540421ab8acba10218594d61d0810c2aa6b0e8408626525874204312a92c3a10210b5ca6494410c1ca6b16820860d5358b4104216bb4a5a08210b5d952d0410a62eba0a200871153d0510042d0b968288021c854b4144010
  | 1 => 0x52d0692b88c6a96834a9c06354b41a52e031aa5a0d0e7318152d0686b98c0a9683495c46054b41c52c0302a5a0e255298432d0712a92c2196838a54a600cb41c52a4b0065a0e0e6354850d0706b1aa4286832c5c0614c94185ae4322a198e2562986548c693394a8a0c63295cb6550631a4ce5b2a8318c3676949418c694b80a4a1263315c863505319a2e031a8298d2672d95414c6c2b90c6a0a63645c06350531a62e02928298e2652587420c712a92c3a10630b5da52d043185aeca968218d1575d05310c6c2b968298863c154b414c431a62e3a14a018d2972d06500c698b8e84a80634a5cb4154031e268298aa018c2d72993534861ab8cc9a9a4389550614c9219c2e030a6490e25541893148670b80c498a43c1551324c521c2ca6b0e8410e15535874208722a9ac3210434a5c35350821a1aeb29a8410e0f6554d4208706a9ec2a1043c154e6150821a4eeab0a8410f0553585420870729ac5a08438354d62d0421c8aa6b148210e256550a4108782a9a8520843c154e4250421e0aa6a128210d3170d4d410868abaca6a084385d955350421c2aa7b128210d25759894108782a9cc4a084349dd56250421e0aa6b128210e0d6454f2108782a9a8390843855915388421e0aa6a144210c2f755912108706b22a690843c154f4148421e0aa6a0a4210c3775591210870ab22a690843c154f4248421e0aa6a124210ca574d952108692bacc89084349dd5644842194eeab224210e27755912108652bb2a890843895935348421ac2e1a9a4210d457594d2108742b24a690843895915348421d0ac8a9a4210f065454d2108782aa2a69084391d915348421e0cc8a9a4210e456454d2108782b22a690843815915348421e12a6a14a010f115350650086d0ba24328043d054d2194021a62e3a14a010d2972d065008692ba242a80434add54254021e14a6a12a010f09535095008699baa82a8043c494d4154021e22a6a0aa010da17448550087912a242a8043c85512154021e84a690aa010f41534855008698b8e84a8043585c64254021a56e2a12a010f22715095008790b8a84a80434a5cb4154021ac2e520aa010f2142905500879121282a8043c85094154021a66e4a0aa010f22725055008790b9282a80434a5d32154021e428390aa010d31748855008790a1442a80434a5d12154021e468290aa010f21414855008698ba242a8043c8d092154021e428490aa010d637448550087913a242a8043585d12154021e42e890aa010d21744855008706a9ac4218818554d6110c40a4ae3322a4205257110d5210294b8086a90818594d61d0840c2aa6b0e842062552587421021abb68528881495ca6454440a4ae421aa2205317010d511030729ac5a08818354d62d044085aed296822062562547411021ab8cc9296610b5ca649473086ae3324a5
  | 2 => 0x57729400000d0000a30013b24c4c1cc8a49cf9510b62f0b52993e5bca454cc21715f464990a4565844f02cdc0011017c635b0372851b5d8815cced3e1514acc02bc00579521e91c2d03e26c6e4306756835034d12c9450614845405058520e4000016e00129000a80680806c2009ce43688800000000005000053c00000aa4d0df4cd2613800075083f4515a400168000000056094054b85189e00000000d43c40000000000e22806c468003b14300000001062ec220007e000002008b001324b0000000a44469570000006a30c000003432cb3410bd384001bc0047939289385542833d4d190f24143c15154000f359ca70c0232e9240000011400154000008e39578000c90192f3ec115884a3d94c2c03127d4125c7d2692a5a05e0007f2c4003f9315b4ad260d70382d1851856d7112c760008515c49064d30008300000000ab0000000000334363e8000002a4a0174b90f224123601f1c044001034e8010ec004c00000047001720bc000c949001232e400030f5270dd000000009619400405094b5210000000041000003c0000000027460000ee000db0000053936001700002b304000b9470003d4500016cac000ff000002540000062000ea000504d55901120000e02f8b7458c85984200000160001b40000000240ce098de000fc00000000000015700150000000010a5d4d51ac0023c0031800000f431c003bc0000010000001dc3321c002b96b0503a5914a5d0000e1221d4022a400408911c88c14c822fc00000003996347d1d1214b03c240000000043000000000004c00001600000000000348003a407084400000000165494001a13c219001348d4dc59010018060000000800088020080005004010000480202804000020500a0180c0480e028040080a0200409800000020200c018000080002808008020d8000000001800000040480e0400400008018020301600000020080680a00802000020100c028061c0020000406818000040200c06800010020880000006080020280a07002000000000600000000160080001818008000681e0302a0200602001495c66454843a4ae5322a221c357598443d0a9938086a8e854c5c04354742a4ae429aa3a15327014d51d0a98b80a6a8e858558c6354742a4ae431aa3a15327018d51d0a98b80c6a8e85459cc6054742a2ae6302a3a15257218151d0b18b00c0a8e858598d5114342c2ac6a88a1a14357119150ccb13312c32a465499c65450a3294ae3b2a851952671d95428ca62b88c6a1265325c06350932a4ce3b2a84995857118d424cac4b80c6a12658a5096014532a1aeba12641958571d09320ca1abb684a8865c1d093254432a62e3a14a01953171d09500cb85a1264a80650b5d66210f41a54e021aa5a0d297010d52d0692b88a6a96834a9c05354b41a52e029aa5a0e0d6318d
  | 3 => 0x74078785750b1182c448920000033000198843ac0044ce745cc51e5560003f000000013d1c4253a00038cd65087c00000000004fc1c0000341cf75a8c43290d000000240043800364001ec0017
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x5c5800090a1f1834009088d00000880081ea4b000a000020038d2a4c0cd95249c8110c8452538749815078c190e18828000c28300529c881c05635c86354742c11635c06354742c11735806054742c21725806054742a0586d093254432b0181d093254032c05635c46354b41c09635c06354b41c09735806054b41c21715806054b419058754b414c431b0182d053154031c21545c0614c921c21545c0624c521c21645c35348421a05869915348421d017454d2194021d017494d2154021d017454d2154021905811d5424c930905821d5414c53091181dc9544c03090982dc5544c030b01819d1524c03090987191524c030b0181191524c030d01525c7424c030b01829d1514c03091187191514c030b0182191514c03091187d09514c0309098754b414c030d0172547414c030c05645cc51485208a1811d9424c120d01535c7424802092187d095148020c05645cc5248710c05645cc52485108a1821d9414c110c20655d12148110d01535cb41440109218754b4144010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 884
  | 4 => 1376
  | 3 => 377
  | 2 => 43
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
  | 6 => packedAt s4K6 (788+((h/14+packedAt s4K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s4K5 (27102+((h/294+packedAt s4K5 (23868+(h % 294)*11) 11) % 1283)*11) 11
  | 4 => packedAt s4K4 (57326+((h/458+packedAt s4K4 (52288+(h % 458)*11) 11) % 1998)*12) 12
  | 3 => packedAt s4K3 (19723+((h/125+packedAt s4K3 (18473+(h % 125)*10) 10) % 547)*10) 10
  | 2 => packedAt s4K2 (2664+((h/14+packedAt s4K2 (2580+(h % 14)*6) 6) % 52)*7) 7
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xbfc3cf38f7ff18c7e3f2238c7fc739e3c0f0cf
  | 1 => 0xcdfc0fc0f98fe0f8fc7c3c0f8e383efcd34333
  | 2 => 0xefff000fe0fff00ff8fc00ff03fc0ff238c3c
  | 3 => 0xf0ffffff000fffff000ffff0003fff003c0fc0
  | 5 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4101100101080400008012010820001045
  | 1 => 0x12442212241242814084242484881448914112
  | 2 => 0xe18880a441249012801a404921128092228428
  | 3 => 0x4110400004800000920890000242000040a80
  | 5 => 0x7be228b08500d4a4d24f326e4980841abbe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xffeaffeafee8fee8ffeaffeafee8fee8ffeaffeafee8fee8ffeaffeafee8fee8ffeaffeafee8fee8ffeaffeafee8fee8ffeaffeafee8fee8ffeaffeafee8fee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x1810c80008d59e2ca07004c0908000011002420000009100a16a8e033625487225cf93305469034147810c94a27007560f2123cd1022002d508c242ff43bf43fe43de43fd43bd43dd439d43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6617c54cc37e87987790f30dea1e61dd43cc33a87985f94b30bea9661df32cc3ba65985f94730bea8e61df31cc3ba63985fd5230bf2a4617d548c2f8a9185f54e30dfa1c61de438c37a87187750e30cea1c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130dfa1a61de434c37a86987750d30cea1a617f524c2f8a49877cc930ee992617f514c2f8a29877cc530ee98a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30dfa1861de430c37a86187750c30cea18617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c837e87907790f20dea1e41dd43c833a87907b90b20f6a1641ee32c83da65905f94720bea8e41ef21c83da43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7106fd0e20ef21c41bd43883ba87106750e20bea94417e51882faa3105f94220fd20441f940883f461107e4c220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e86907790d20dea1a41dd434833a86907b90920f6a1241ee32483da64905fd4520be28a41ef21483da42907e90120fca0241fa30483f260907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be29841bf43083bc86106f50c20eea18419d43082fca4105f94420fb288417651082faa2107d54420baa88417e50083de40107e88020f690041f920083d240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7886fd0f10ef21e21bd43c43ba87886750f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c538437e87087790e10dea1c21dd438433a87085fd4a10bf294217d52842f8a5085f54610bf28421fa40843f281087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a21bf43443bc86886f50d10eea1a219d43442fea4885f94910bea92217c52443ec82887d50510fb18a21f531443ec42887d48510fd20221f940443f460887e4c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10dfa1821de430437a86087750c10cea18217f52042fca4087b94810b7290217d52043daa4085b54810be290217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xe41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620efd0c41ef21883bd43107ba8620e750c41bf29083ee52106dca420df54841f6a90836d52106fca220efd0441fb20883bd41107ea8220df94041fd280837a50106faa020fe54041bca80837f54cc6fca998ef953319f2a6637d54cc77aa998cf55331be2a663bf43cc7bc8798ef50f31eea1e639d43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63bf438c7bc8718ef50e31eea1c639d438c6fca518df54a31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263bf434c7bc8698ef50d31eea1a639d434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618efd0c31ef21863bd430c7ba8618e750c31bf29063ee520c6dca418df54831f6a90636d520c6fca218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c87bc8790ef50f21eea1e439d43c87dc8590fb50b21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21dfa1c43de438877a8710f750e21cea1c437d52886fca310fd90621faa0c43f631887ea6310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690efd0d21ef21a43bd43487ba8690e750d21f721243ed42487dc6490fb4c921fb20a43f541487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21dfa1843de430877a8610f750c21cea18437e52086fca210fbc8421fb10843ed21087ea4210f948421bf28043fa50086f4a010df54021fca80437950086fca7a07794f40af29e817d53d03baa7a05754f40dfa1e81de43d037a87a07750f40cea1e817e52d02faa5a06fd0b40dea16817e51d02faa3a06fd0740dea0e817d54902fca7205f54e40dfa1c81de439037a87207750e40cea1c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9a817c535037e86a07790d40dea1a81dd435033a86a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40dfa1881de431037a86207750c40cea18817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa88817e501037e80207e90040dea0081f940102fea9985f95330df2a6613e54cc2faa9986f553309eaa
  | 2 => 0x600801df94b43bea96877e51d0efaa3a1df94343bea8687bf52d0f7ca5a1ef54b43de29687bf51d0f7ca3a1ef54743de28e87bf50d0f7ca1a1ef54343de286877d5490e7aa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243aeaa4871d5490fbea521f794a43eea9487dc5290fbea321f794643eea8c87dc5190fbea121f794243eea8487dc5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050f7ea6a1e7d4d43dfa9287be5250f7aa4a1ef14943dfa8a87be5150f7aa2a1ef14543dfa8287be5050f7aa0a1ef14143efaa2879f5450fbea4a1f794943eea9287dc5250fbea2a1f794543eea8a87dc5150fbea0a1f794143eea8287dc5050f3ea4a1e794943cea92879c5250f3ea2a1e794543cea8a879c5150f3ea0a1e794143cea82879c5050efca821cf95043bf298875e5310f7e8621f790c43dea1887dd4310f3a8621df94843bea90877e5110efaa221df94043bea80877e53d0bbca7a15794f42bea9e85dd53d0abaa7a16fd0f42ef21e85bd43d0bba87a16750f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216fd0e42ef21c85bd4390bba87216750e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350bbc86a16f50d42eea1a859d4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6216fd0c42ef21885bd4310bba86216750c42bf29085bf4210bdc84216f50842f6a10857e5110beca2215d94442bea8885f55110aeaa2215f94042fd280857a5010afaa0217e54042bca80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32ef21c65bd438cbba87196750e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a8996fd0d32ef21a65bd434cbba86996750d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6196fd0c32ef21865bd430cbba86196750c32bf29065df320cbdc6419774c832f6990657e510cbeca2195d94432bea8865f5510caeaa2195f94032fd280657a500cafaa0197e54032bca80657e53d07bca7a0d794f41bea9e83dd53d06baa7a0efd0f41ef21e83bd43d07ba87a0e750f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83bf43907bc8720ef50e41eea1c839d43906fca520df54a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0efd0d41ef21a83bd43507ba86a0e750d41bfa92837c525077e84a0ef50941fba0a83b
  | 3 => 0xbb8006e8998000762dc1088b1026c6000920000000000000000041800000614000003880000012925a60aa38000fd0000cc0022c00021c000000005bd3900b000001c6000000510aba0c3aad6d2e8f4350000000e207a278932ff000000000f80000000008f00a000002d9000000000004e8001253813ce8a01e000000000b98ee22a074e5b18000000000006b8000000e17063e400000000001172e806800000000570dd8000004064d400000000000000000000012e27e000ac58d28f3f2000d99cd2262584c8dd000a5800000140c7800000000dcc00000000c5c01a652cc0003880066a0000031427c868b8ab625245ccc0de2b28b528928000dd45780047e0000000000014414800000000001500000007d0000000000000066c0000024442e0000004369e0002092b0000006111958608c0000038a000bc000000000000004162e0000000a6001700004e6000000004b6774001e80f40000038400000000000000000000006a00010aac4554554000000007cce50000000005200027a51c002e20000011f000000000268000000018cb3b39807c000000008dc002f42608587d8005e2db56d8790000000000059200000206520524bd2050003a459a45308230001016aa000000d824481000221000ba979800392bd800000192000d39fa58e0d40008200000000000000001548cc314a00000000002f1a09ea23800095000004000c49182c609c0207c208c04c9158000000d494f3682110e852000d7800000000c4400000000000ad202158a089c8be092d0950a471642c4060ea1760006f80d3ec0000026b000000a330207ecf0db000000000002710000080000000200c01c01800000000000020000040280400a0180000100601c00004004000008010000000080000600000002000008008010060380200000e00000801002000000040000080200000c008028040060040300100000403002000034030000000080000000c00801000000000000050000040080000000003800000000018000080080100000e000000030040100000000003803804006004000020020140180001a0040080000000c000030000040000300000000000004014008010040040000201c000010010060040000000000401801000000000010000280080300a00000007006000000000000000080200200c01000000000000000000000000000801400000000004000080020000000100600c0180900000400800000020008000000080180000201000000000000010000000000180100200802803002000008020040300000400000c0000200400000800000000030000060000000100c000030020000000000200400002000000004008000000000080000c008028060000200000700c00800806000000020010000040000300800004000
  | 4 => 0xc80000000008cc000000004280000057a000f0a6105c288b500032e00000060000000000503784845c800660aa1761b265e0000024d5a28c59104e5940408593c454a3454000000000000003c4000002990400000021900000000000000000002ee0dc76000000000000002891262b8b4800438b48548371e4c1c00000000a7c348000000540015d00000000000000000609b00005d80002a3025f0000aa5f28789d1881a4a51b80c6000434001421e600000255540364002232beab0aa32a02ebec001dc0000000011400000000000000d89a50007140018a800000000001d7000000000000000000000000095d6323b00028d218003cac10001ec000248000004f8000e001b000b34b10006c0d9cdf800000a2000000000000001ff0000000000000000000000000768000002206349280052acc4b58c329ab95769333d20c187abc4c41882428a4b2d999989f4000015782b0000009d8a1000704000220007b400000000d74001aa42031c00000000000d5800000590000002b8c40b6b4d0000003eb5a12a0c800000000000000000000014b95e000000d0000000000000000009200000000e000620000e400018800282df000000038000000000c60011a800716000003240000000000053600004000000c9c00000000af80a35837c3fc0034b49600000000000000000002ca000e82f84dc32c092360007100002d44e1d4278da41e17d1eb39000000002d3000ae800000000000003590000000000025cb51990000000000000007200009a6a0002d55c8ce60c9f4001d20d693d6d35f430deda9800000000a600038c000230002d800000021000b980033f2fc9006a34c000000000000000016a83a000000362c044a0000000000000000111658000000241d8b840b00000053800044000000000006fc5fc000001aa000002770009e80021258400000000000000000006260000000065a00113000000a8c000000000000000047886d9400041400000000000000000001ca000000fe000d850a337264cf400000000000001534e040d7e1f246019c002ef0b20000000008e001660000000003f8ed000000000ad4220013d80058a000000cf68a0004d3576a25a000000000000000000f000000386000b59782796121159f0000000000000028a000000006c8001360e654800137afe2c0000000e0000000000f6000000ea000000a600018331c0016b8000000005819d000c980000000033400000000c0c0000058267000000000000001616000000002c0ee000000000000014985e484000c28003b2924002e75b025c0000000084ce88000fc001580000000015599e0760000027f000274918f719050c002a501239c003772f2990050005bc6b49f80000000000000000644bab895ee2d0862b24a0d0c9a3494b000000000704000001900
  | 5 => 0x54400000000000379c7000000000000000002b00022422c65000566000002bf0da56ce11930000000029a03c06120a4c6ac19417948000db93386134a9e000000000000001a42e88ada388d20eb8c55ab40004d8ef000000001299b90e00a0ca88e0f67ec6b33a0006f42c01a358001040fc6f29a0001c85be000002ce00048044b1d0b6295039090000011c000000780003234a820c130000cc74c0004a000d512700020a00168000502dc8002750002f4cd0000003bd0fa9c0000018f9ee00029c4c1ba000000000000006645b1b526e00000000000b740000000059d3b19f000001758000004bc00338000824000001e20018d9ce0000000000053c000000000000019080069066c5d0000007dc001380b8dac7425600000000000000e1d9a31c000d4807000000e00e78000000004400032862c001e4000000802e4000314c00002ac0000036f000340000000000000003e000469a7108596698fe0002588055a8003be3ad178000002280025f0008a5be800000d1800054100000c137a000000001bb000c30003850002dd678000000002592d14c7f91d1ae00046c000000ae00000000000ab97e8000000000011d0801544d9d61c6001873656fe00000000516000000001e000000000000a7400074000130000dc000000032e94c0a88d11ef5909a536a0e6240000014a6d07e087a636886840000026200087152102000002323e20000000035e001b60000000000000000061c0000050c001bc1f50000000014b00000000000000a9800186032d00078001ae391928000008d000abb3e00002eaf55e4630000913e8b71463160b40011c885000880001b11ea0000000000078d418000007f40000017eab548927138044000363cc000000680000000000000000012a460006dc000860000000000056ec340030b508da4000000005ec320c01a2000000000000000000054e0e10687350a36ca006a00063cb81b865200111000000000000000000000011f0005f40009400000069a5e000000002fa0007adb880000070c001964480000011e2e4000001db6d4a1c4832b610000001a3000cb9490000000000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd434431e5350d10c754d434431c5350d10c7d51434431e5450d10c7551434431c5450d10c7d95434431e6550d10c7595434431c6550d10e598543443956150d10e698143443996050d10c750f524431d43949108fd91524423c645491097d8d524425c6354910c750d524423e64149108f590524425e63149109758c524431d4314910e550e41442746550510e550d41442f06050510e550e3144274654c510e550d31442f0604c510e550e21442746548510e550d21443645248510bc181214439943901109e19540443994350110bc18540443b14150110e650e3044278654c110e650d30442f0614c110f44c5304439943881109e19520443994348110da14920442f06148110f8485204439943c4110e550e104425e63d50109758f540426e62d50109b58b540425e63950109758e540423d6595010a758e540431e63950108f58e540431d63950108758e540423f6355010c798d540431d63550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10a7592530431e5494c10c7552530431e6494c1097592530431d6494c1087592530431e5454c10c7551530425f6454c10c7991530431d6454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f430425f6590c1097596430429d6490c10c7952430431d5490c108fd95430423d6550c10c7d4d430431e5350c10c754d430431c5350c1097d95430425d6550c10c7d51430431e5450c10c7551430431c5450c10a7d95430431f6550c1087d95430431e6550c10a7595430431d6550c1087595430431c6550c108f993520423d64d48109798f520425d63d4810c750f520431d43948109b596520432e5494810cb552520434e5394810d354e520438d4394810cbd0e520434e4394810cb50e520434d4394810c350e520431d4354810cb951520432d5454810d394d520434d5354810e350d520432f4354810d390d520432d4354810d350d520430d43548108f990520423d64148109798c520425d6314810c750c520426e62148109d984520427a6014810c750e510431d4394010cd553100435553c4010e550f100436552c40109e59610043395484010d654e10043994384010da54a10042f161840109dd9510043355444010d554d10043954344010d9549100427b6544010ce55110043595344010e650d10043695244010bcd9510043736544010dcd5110043b25444010dc55110043b15444010cc55110043735344010f494d10043715344010f454d10043515344010ecd0d10043d24344010ec50d10043d14344010e450d10043735244010f894910043715244010f854910043615244010
  | 1 => 0x823d64d4c209d987530827561d4c208f992530823d6494c2097596530829d6494c20c7952530831d5494c20c7992530825d6494c20c7592530821d6494c20c7951530831d5454c2097d91530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c2097d96430825d6590c20a7592430831e5490c20c7552430823f6550c208f595430831f5350c20c794d430831d5350c20c714d430825f6550c2097595430831f5450c20c7951430831d5450c20c7151430829f6550c20c7d95430821f6550c20c7995430829d6550c20c7595430821d6550c20c7195430831d4394820c750e51083365494420cd55251083565394420d554e51083954394420cdd0e51083564394420cd50e51083554394420c550e510831d4354420cd95151083355454420d594d51083555354420e550d51083374354420d590d51083354354420d550d51083154354420c750e500832d54c8020d354f200838d43c8020d954720083395488020d654e20083994388020ba58a200837151880209bd95200832d5448020d354d200838d4348020d9545200827b6548020ce55120083595348020e650d20083715148020bad95200836b6548020dad5120083aa5448020da55120083a95448020ca551200836b5348020f294d20083695348020f254d20083495348020ead0d20083ca4348020ea50d20083c94348020e250d20083e25148020da54520083e15148020d8545200825e63953109758e54c425e63153109758c54c426e62153109b58854c423e6494f108f59253c423e6414f108f59053c426e6214f109b58853c431f5350f10c794d43c431d5350f10c714d43c431f5450f10c795143c431d5450f10c715143c431f6550f10c799543c431d6550f10c719543c43966150f10e558543c431d43d4b10c750e52c431d4354b108f99052c423d6414b109798c52c425d6314b10c750c52c43954390710e550d41c4395438c710e550d31c43954388710e550d21c436452487109798e548425d63952109798c548425d63152109b988548426d62152108f992538423d6494e108f990538423d6414e109b988538426d6214e10c7d4d438431e5350e10c754d438431c5350e10c7d51438431e5450e10c7551438431c5450e10c7d95438431e6550e10c7595438431c6550e10e698143843996050e10c750f528431d4394a10c750d528423e6414a108f590528425e6314a109758c528431d4314a10e650e40843994350210e650e3084399434c210e650e20843994348210da149208439543c4210e650f108425e63951109758e544425e63151109758c544426e62151109b588544423e6494d108f592534423e6414d108f590534426e6214d109b588534429d6490d10c7d4
  | 2 => 0x5490c30b6582430c23f6550c30c794d430c31f5450c30c7951430c31d5450c30c7151430c29f6550c30c7d95430c31d4394830cb952520c32d5494830e350e520c32f4394830d390e520c32d4394830d350e520c30d4394830c750d520c32e5454830cb551520c38d4354830cbd0d520c34e4354830cb50d520c34d4354830c350d520c31d4394430cd952510c3355494430e550e510c3665294430d954a510c3374394430d590e510c3354394430d550e510c3154394430c750d510c3365454430cd551510c3954354430d9949510c3655254430cdd0d510c3564354430cd50d510c3554354430c550d510c31d4394030a7593300c31d54cc030d354b300c35551cc030e650e300c369528c030dc546300c25f654c030c7551300c34d524c030d5545300c27b654c030e6d0d300c369524c030dc545300c25e63953209758e54c825e63153209758c54c827661153209d58454c823e6494f208f59253c823e6414f208f59053c82766114f209d58453c831f5350f20c794d43c831d5350f20c714d43c831f5450f20c795143c831d5450f20c715143c831f6550f20c799543c831d6550f20c719543c838e6250f20e358943c838d4390b20e350d42c838d438cb20e350d32c831d4394720c750d51c838d43c8720e350d21c825e63952209758e548825e63152209758c548827661152209d584548823e6494e208f592538823e6414e208f59053882766114e209d584538831f5350e20c794d438831d5350e20c714d438831f5450e20c7951438831d5450e20c7151438831f6550e20c7995438831d6550e20c7195438839a6050e20e6581438831d4394620c750d51883994390220e650d4088399438c220e650d308838d43c8220e650f208825e63951209758e544825e63151209758c544827661151209d584544823e6494d208f592534823e6414d208f59053482766114d209d584534829d6490d20c7d4d434831e5350d20c754d434831c5350d20c7d51434831e5450d20c7551434831c5450d20c7d95434831e6550d20c7595434831c6550d20e3989434838d6250d20e698143483996050d20e350e424826c6550920e350d42482e86050920e350e324826c654c920e350d32482e8604c920c750f514823e64145208f590514825e63145209758c514831d4314520e350f214838d4348520d914521482e86048520e650e40482786550120e650d40482e86250120ea5094048399438c1209e1953048399434c120ba18930483c9324c120e650f204838d43881209798f540825d63d50209d987540827561d50209798e540825d63950208f596540829d6395020c798e540823d6395020c758e540821d63950208fd8d540831e6355020c758d540823e64150209798c540825d63150209b988540827661150209d584540827a60150208f993530
  | 3 => 0x21d650e50087194394021c750d50087652154021ce95150087395454021d694d50087595354021e650d50087e12154021ced0d500875a4354021ce50d50087594354021c650d500876b2154021dc88550087692154021dc48550087612154021c799153d031d53d0f40c794d43d029f6550f40c7d9543d031d4394b40c750d52d029d63d0b40c754f42d031d5350b40c750e51d031d4354740a758f41d031d53d0740c754d41d031e5350e40c754d439039b6050e40e6181439031d4394a40c750d529031d4394640c750d519029d63d0240a7592435031f5350d40c714d43502b86050d40e6d8143503986050d40c750f525025e63149409758c525031d43149409d98452502756114940a758f425031d43d45409798c515025d6314540c750c515026e62145409b588515029d63d0540e650f405031e6454c40c754f43102b960d0c4097596431029d6490c40c794d431025f6550c40c7951431029f6550c40c7d95431031d4394840d394e521034d5394840e350e521032f4394840d390e521032d4394840d350e521030d4394840c750d521034e5354840d354d521038d4354840cbd0d521034e4354840cb50d521034d4354840c350d521031d4394440d594e51103555394440e550e51103665294440d954a51103374394440d590e51103354394440d550e51103154394440c750d51103565354440d554d51103954354440d994951103655254440cdd0d51103564354440cd50d51103554354440c550d511031d4394040a758f401031d53d0040cb54b401033551d0040e650e40103695290040dc546401023f6550040c754d401032d5250040cd545401027b6550040e690d40103695250040dc545401031e6395330c798d54cc31d5490f30c7d5143cc31e5450f30c755143cc31c5450f30a7d9543cc31f6550f30c750e52cc31d4354b30a759332cc31d54ccb30c755132cc31d4394730c750d51cc29d64cc730c755331cc31d544c7309b988548c26d62152309d984548c2756115230c7951438c31d5450e30c7d95438c31c6550e30e6d81438c3986050e30c750e528c31d4354a30c750e518c31d4354630a7593308c25d63951309798c544c29d6490d3097195434c31f5450d30c7151434c2d86050d30c7d95434c31e6550d30c7595434c31c6550d30e6d81434c3986050d30c750f524c23e64149308f590524c31d43149309d984524c2756114930a7593324c31d43d45308f990514c23d6414530c750c514c26e62145309b588514c29d64cc530e650f304c26e62d50309b58b540c27661d50309d587540c23d6595030c798e540c25d63550308fd8d540c31e63550308f58d540c21d63550308f990540c25e63150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c25d6590c30a7592430c31d
  | 4 => 0x350e42c878d4350b21e350e32c878d434cb21c750e50c871d43543219798e548865d63952219798c548865d63152219e980548867960152218f992538863d6494e218f990538863d6414e219e98053886796014e21c7d4d438871e5350e21c754d438871c5350e21c7d51438871e5450e21c7551438871c5450e21c7d95438871e6550e21c7595438871c6550e21e598543887956150e21e550e41887954350621e550e3188795434c621e350f218879543c8621c750e508871d43542219798e544865d63951219798c544865d63151219e980544867960151218f992534863d6494d218f990534863d6414d219e98053486796014d21a7592434871f5350d21c794d434871d5350d21c714d434871f5450d21c7951434871d5450d21c7151434871f6550d21c7995434871d6550d21c7195434878e6250d21e358943487966150d21e5585434878d43909219b195424878d4350921b9185424878d438c9219b195324878d434c921b9185324879543905219d19541487954350521b918941487a54250521e550e3148674654c521e550d31486e4624c521f14c9314879543c8521e350e214871d43d41218f990504863d64141219798c504865d6314121c750c504865e63d50219758f540867a60d50219e583540865e63950219758e540863d6595021a758e540871e63950218f58e540871d63950218758e540863f6355021c798d540871d63550218f990540865e63150219758c540866e62150219d984540867a60150219e580540863e64d4c218f593530867a60d4c219e583530863e6494c218f592530865d6594c21a7592530871e5494c21c7552530871e6494c2197592530871d6494c2187592530871e5454c21c7551530865f6454c21c7991530871d6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f65d0c218f597430871e53d0c21c754f430865f6590c2197596430869d6490c21c7952430871d5490c218fd95430863d6550c21c7d4d430871e5350c21c754d430871c5350c2197d95430865d6550c21c7d51430871e5450c21c7551430871c5450c21a7d95430871f6550c2187d95430871e6550c21a7595430871d6550c2187595430871c6550c21c750e520871d4394421cb553210874d53c8421e350f21087355488421d554e21087954388421b958a210866f6548421cb551210874d5348421e350d21086776548421cd55121087555348421e550d21086e76548421d9d9521087675448421e995121087655448421e955121087255448421d9d4d21087c65348421d954d21087c55348421d154d21087a74348421f190d21087a54348421f150d21087854348421c750e500873a5494021ce552500875a5394021d654e50087994394021f8486500873b4394021d690e50087394394
  | 5 => 0x521070d4394841c750d521074e5354841d354d521078d4354841cbd0d521074e4354841cb50d521074d4354841c350d521071d4394441a758f411071d53d0441cb54b41107954390441d954a411063f6550441c754d411072d52504419dd9541107964350441d9549411071d4394041d694e50107595394041e650e501076a5294041da54a501073b4394041d690e50107394394041d650e50107194394041c750d501075a5354041d654d50107994354041da94950107695254041ced0d501075a4354041ce50d50107594354041c650d501073b4154041dc90550107394154041dc505501071e6395331c798d54cc71d5490f31c7d5143cc71e5450f31c755143cc71c5450f31a7d9543cc71f6550f31c750e52cc71d4354b31a759332cc71d54ccb31c755132cc71d4394331c750d50cc66e62152319b588548c67a60152319e580548c71e5450e31c7551438c71f6550e31c7195438c7976150e31e5185438c71d4394a31c750d528c69d64cc631c750e508c71d43542319758e544c69d6490d3197195434c71f5450d31c7151434c6d46150d31c7d95434c71e6550d31c7595434c71c6550d31e5d85434c7946150d31c750f524c63e64149318f590524c71d43149319e980524c6796014931a7593324c79543cc531c750f504c63e64141318f590504c71d43141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c71e6395031c798d540c63e64150319798c540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c3197596430c69d6490c31c7552430c6d56190c318fd95430c71e5350c31c7d51430c71e5450c31c7551430c71c5450c31a7d95430c71f6550c31c750e520c72e5494831cb552520c78d4394831cbd0e520c74e4394831cb50e520c74d4394831c350e520c71d4354831cb951520c72d5454831e350d520c72f4354831d390d520c72d4354831d350d520c70d4354831c750e510c69d64cc431c7553310c74d52cc431e550e310c765528c43197d95310c71d544c431d3549310c677654c431e5d0d310c765524c431c750e500c73a5494031ce552500c7994394031da94a500c7695294031ced0e500c75a4394031ce50e500c7594394031c650e500c71d4354031ce951500c7395454031e650d500c76a5254031da549500c73b4354031d690d500c7394354031d650d500c7194354031d6cc5500c7723154031d64c5500c77131540319798e54c865d63953219798c54c865d63153219e98054c867960153218f99253c863d6494f218f99053c863d6414f219e98053c86796014f21c7d4d43c871e5350f21c754d43c871c5350f21c7d5143c871e5450f21c755143c871c5450f21c7d9543c871e6550f21c759543c871c6550f21e398943c878d6250f21e
  | 6 => 0xb3b4394042d690e5010b394394042d650e5010b194394042c750d5010b5a5354042d654d5010b994354042dc9455010b715154042ced0d5010b5a4354042ce50d5010b594354042c650d5010b3b4254042da9095010b394254042da5095010b1e6395332c798d54ccb1d5490f32c7d5143ccb1e5450f32c755143ccb1c5450f32a7d9543ccb1f6550f32c750e51ccb1d4354732c750e50ccb1d43543329d984548ca7561152329e980548ca796015232c7951438cb1d5450e32c7d95438cb1c6550e32e3d89438cb8c6250e32a7593328cb1d4394632c750d518cb1d4394232c750d508ca5d6395132a7592434ca5c6550d32c7d51434cb1c5450d32b3189434cb1f6550d32c7995434cb1d6550d32c7195434cb8f6250d32e3189434cb8d43cc932c750f514ca3e64145328f590514cb1d43145329e980514ca796014532c750f504ca3e64141328f590504cb1d43141329d984504ca7561141329d987540ca7561d50329e983540ca7960d50328f596540cb1e6395032c798d540ca3e64150329798c540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3d65d0c3297596430ca9d6490c32c7552430cacd6290c328fd95430cb1e5350c32c7d51430cb1e5450c32c7551430cb1c5450c32a7d95430cb1f6550c32c750e520ca9d64cc832c7553320cb8d438c83297d95320cb1d544c8329bd95320cb8f434c832c750e510cb365494432cd552510cb954394432cdd0e510cb564394432cd50e510cb554394432c550e510cb1d4354432cd951510cb355454432e550d510cb374354432d590d510cb354354432d550d510cb154354432d5cc9510cb663254432d54c9510cb653254432c750e500cb3a5494032ce552500cb994394032dc946500cb715194032ced0e500cb5a4394032ce50e500cb594394032c650e500cb1d4354032ce951500cb395454032e650d500cb725154032dc545500cb3b4354032d690d500cb394354032d650d500cb194354032d6cc9500cb6a3254032d64c9500cb693254032c799153d071d53d0f41c794d43d069f6550f41c7d9543d071d4394b41c750d52d069d63d0b41c754f42d071d5350b41c750e50d071d4354341c794d439071d5350e41e5d8543907946150e41c750e529071d4354a41a758f419071d4394241c750d509069d6490d41c7d4d435071c5350d41ad18543507976150d41e5185435071d43d49419798c525065d6314941c750c525067a60149419e580525069d63d0941e550f415071d43d41419798c505065d6314141c750c505066e62141419b588505071e6454c41c754f43106b561d0c4197596431069d6490c41c794d431065f6550c41c7951431069f6550c41c7d95431071d4394841d394e521074d5394841e350e521072f4394841d390e521072d4394841d350e
  | 7 => 0x114143b55845050f595014143a79875250e9d61d4943a79835250e9d60d4943a798a5250f1f5294943e3d4a5250e9e6194943a75865250e9e6094943a75825250f8f5254943c79495250e9f6154943a71855250e9f6054943a71815250e9e6514943c7d485250f8e5214943c75485250f8d5214943c35485250e9e6114943e59845250e966114943a75845250f956114943a55845250e9e6014943e69805250e9a6014943a75805250f996014943a65805250e9e62d4543a758b5150f1f52d4543c754b5150e9e60d4543a75835150e9e6294543a758a5150e9e6194543c7d465150f975194543a79825150e9d6094543a7d895150e9c6254543c7d495150f1d5254543e5d455150f1e5154543a7d815150e9c6054543a79945150e9e6214543e39885150e8e6214543a75885150f8d6214543a35885150f1f5114543e59445150f1d5114543e55445150f155114543a79805150f9a6014543a69805150e9d6014543e65805150e996014543a798b5050e9d62d4143c7d4b5050f1d52d4143a79875050e9d61d4143c7d475050f1d51d4143a798a5050e9d6294143a79865050e9d6194143a79825050f1f5094143e6d425050e9f6254143a71895050f1f5254143c75495050e9f6154143a71855050f1f5154143c75455050f9b5054143c79415050e9e6514143a79885050f8e6214143a39885050e9d6214143e35885050e8d6214143a79845050f966114143a59845050e9d6114143e55845050e956114143c7d405050f9a5014143c75405050f995014143c65405050e9d6490c438fd954310f1e5350c4397d954310f1e5450c43a7d954310f1f6550c43c750e5210f1d4354843c750e5110f1d4354443c750e5010f1d4354043c799153d0b1d53d0f42c794d43d0a9f6550f42c7d9543d0b1d4394742c750d51d0b1d4394342c750d50d0b1e5350e42c754d4390b8f6250e42e31894390a9d63d0a42c750e5190b1d4354642c750e5090b1d4354242a75924350b1f5350d42c714d4350aac6250d42e3d894350b8c6250d42e350f4250b1d43d45429798c5150a5d6314542c750c5150a7a60145429e5805150b1d43d41429798c5050a5d6314142c750c5050a7661141429d5845050b1e6454c42c754f4310aad62d0c42975964310a9d6490c42c794d4310a5f6550c42c79514310a9f6550c42c7d954310b1d4394842a758f4210b1d53d0842e350e4210a3f6550842c754d4210a6f6550842e390d4210b1d4394442d594e5110b555394442e550e5110b374394442d590e5110b354394442d550e5110b154394442c750d5110b565354442d554d5110b954354442cdd0d5110b564354442cd50d5110b554354442c550d5110b374254442d99095110b354254442d95095110b1d4394042d694e5010b595394042e650e5010b725194042dc5465010
  | 8 => 0x200100100000200d01300400000100700000c00900a00701100601400700001c00100000000100700100300a01600800200100400600000100100102200200402500000f00000001400501100800e00600000400500e02600000100100700401200301c01101100f00300100800000000100200400200101700000000000d00100300300200000100e00f00400000100000400301000000000002b00f00600000500000000600c00a00000100200000000600200100000000200c00000500b00200500600500300300200401e00000b00000102400b00b00200000100100300100001a00000100200401801400800200201800300400100002300000300300900300700900000400300300000000100900100301700200300e00400601200000000300800801f00300500800300000501900300100000500d00000000100000401600200500000100100000000200500500300000000700200800300900900500000700000300000000300b00200100300c03400000500100100f00100200900100000100000100000000400a02900600900100000000100000f00500000400200701000600a02700400101100000100000400100100500800400200000000501000100300000700000200100f00200200300500000500101000500100900800000e00a00b00000000d00100000000100000c00700400000000000001600000200000600000000600400500000505100100500700300100300000400002500100401000000400500700000600000000500d00700300200000000400500100900400200300100000400000000600800b00000700000601500200100201300100000b02a00000100300c00900400f00700200700300800200100801e003cb54852d0eb66114b43ad58452d0eba6014b43ae58052d0eae6214743ab58851d0f355114743ae98051d0eb96014743ab98850d0ead6214343ad98450d0eb56114343ce54050d0f4d5214a43b59845290ed56114a43b69805290ed96014a43b39885190ecd6214643d55445190eda6014643b65805190ece6214243b35885090ed66114243b55845090f5950142439d9845250e7561149439e9805250e7960149439b9885150e6d62145439e9805150e7960145439b9885050e6d62141439d9845050e756114143a798b5350e9d62d4d43a79875350e9d61d4d43a79835350e9d60d4d43cb5485250eb66114943ad5845250eba6014943ae5805250eae6214543ab5885150f355114543ae9805150eb96014543ab9885050ead6214143ad9845050eb56114143ce5405050e9e62d5143a758b5450e9e61d5143a75875450e9e60d5143a75835450f4d5214943b59845250ed56114943b69805250ed96014943b39885150ecd6214543d55445150eda6014543b65805150ece6214143b35885050ed66
  | 9 => 0x24000cae4f6000000000000000b120000001929be50a66e0000000000000000000002640c8000000d42af6c940c067a35cb48b849c2decb507f287ea0a178afa0a0d4a000866000b6ebcc07a0007b8000324a74b34d9cc7e52ca56d72408c5a82c0ba35ebd0ca6b746de9b4706d38202d304003784503509acafe00000000000068e3d45b805e4da0002b87d400498cbca000aba000a1e51403c122e167a42784748729a01842a6c5030e59646e4f23cec988e8ad0d0a6dc5d24eeb24c80708a608fc6e61e85ce08c7c24669a6876c66000b62a9e000642000000000000000142668000dc8dacb540000001040000c20004062ec5fc0001b6a2ca185620000648fa5b2000a960a6c44d52000a8000025ca5a4e8b2e2aa22060600000000015a000000002c36dce74ea9846c000b942ea00000012c4ac000000a00b46a889dc000a4a984ca023a0002f83b29421a200000000000000042e8d89ee41000000082098ac2a0000b4916560200b8cba2d3a0004d0000c8600000000000092a000d5ab9249e19a00042000049038e1a09cabf2d26cb000000000080edf25081de7b6776ad66f26c83be84607c280ce683081a35a9d67881d27a8d7e46a00000000000036426e9129b66bc000ae00000f23220003325e0678be00eeb202bc31cbbc9d4d2a726396adac90dcc4307346a477215275a14ac9643227a000376000000d3e3c00001ac00018265c43684ccf65f242800089031e84ed786c41baa20c0cb1c57a6b2ccc000a10ddc5b6a52b18618000072ca837a59acfe0004f0d90000bdc8cc574b6a69e812d8e31a00c494338444aa0d16c70aac1caa26b9e7148320005ec47ed36d880b8cbe7ccc4c1fccf267e9262145cc318000dd21380000d6cca958c06c6a00000088a91e00014e9a2aea00000064000057800000029cbd89464e4000d220820007b48ee4c252e0004b6470000c523a2de89d20000002b258e738000af45da000000dd43f869c000a700000000009b0000a7a000682b8a64a6eec6460e0000005e2136000a78cdc47c48454a8c20082d206260000600000000000900000300000000201c00401001900401200600000300000000300000100800101d00000a00200300000201300100900000100100c00000400700100100300400101800303a00300100a00000500100000000001100d01800200000200300300100400100200e00000900000601200300300400400000700800500700001100000e00100200000000700300000300000200200402300600000000100000200400400400000001004400000000100300300d00100000500500400201a00100000300002f02200400a00000400100000700200001200200900f00e01d00000100c00600500100200a00500800000800a00200000100900000100100200000600000d006
  | 10 => 0x695203a4aa00074200086296200089c0001bc0606480001e4266000bf662a0000000000000000005fa6ba8282900000000000008dc59800000000000029600043e7f84fe794abcce8b78000000000000000000ae454626c90a000d9452a000000000000ac0be400055a00000064e73c000bf00ac0009989740000004d25bc7fe00076400000084800087837c61619444aaa28b2628100426ade288816936a5cce06b40ec1b25c04be2b0000bfaa5e0000004720001e095acb8bde0e06ec64600000000000040c16c9f4798cf84a2000be800001030c00000015e000e1048811ad00bda00020e0d2000d603b0da021617c000496cc6cc085067221893e112c9a080424c003fed460009e4c02cba8ba78a000000a90dc000000070c2b65d84ce298786aeedfa96a00a9602561c84c6d4072c9c649c8f2da64b2486b6800043a8886641d60a2000bee478244d1a70ec3077484ad2eb640001540000000008c0000dd07522e8a36000000c9e0000005180009767ce12617083e40e7a047a0d859e8da82eb08464b5e4628ec4c088604ebf822486a7ac0007a2b4ade42527680000001060f00000001a809c00089432e258de0c6c02e51c90edcad4404c5a074639ac2271c4ecc562e6a1c0ceae6d92572000df608e48c254040c108004541d472ebe6bc6ce4a401a6a3adde0007ae97e02ca9c82a3a6548d18dd85923b4d6cb1011600009a3b600000090c50c780804570da406eab40eacb41b438aa48a023c8df04d40b060cc3eb3693a5be17ad5e000168712000448d482dc000db686c844c62b406d65f67ee5067d60dc0129ba806e0c15ccdadaa180144bc03f02ca64cd6a0003f451e4147602f0038aaea721667f08e00267dc0a492c068690b58456d14a8a65a6960160003a4bfc8aa50200034a934bce6ead32102000928300a42000880000dfe0364c80000006d0b7e8f4660a681b893842c348d54790384d86000c20bac2c4c4253495472482258a9f8c9c27e762bea130a46dae1c4000c3ca6a000b6c0000000000000002386aed56000000b5c870024b32b865300006fa0cca766660ae21c576710000aa60000003c6b046a200036000085232c000000000000ba8000000d34aaa9449b887c826e02b2a5f061e838092b4ed0c6440008f85f89d094c86e00000095edf82b468c5542d85c253c27273670200000001e0006aad200003aacd6964e18000d9a0000000003342322bacded4cd749960001641f2bc8d02458ba4b5a9e230a0005b0728ab6758c1a5d468a0b69f0000988b720703e8bd43da7f4d1e0008822623cc0006d8ac245c29a90059c15691453e05287a23c000590c7ae1aa22066c183263dca3e2845e42be79c5283d00742cc000000ac4000e0e0001280000009c82e43527be0321d801c0004ba000dda27642a000000000000000d
  | 11 => 0x9905260009943147843724980c64808104fa70a26a01a62e00000065436a3900003660005cacd2a1a000670e046c04123d6dc423462269a6ce000740c0ed6e8be4eaac681ea9a208afcdbe7480003980002740008ca50474a28a91a00017243c00000098e7fade6148d7ad7041a0007e8d0e5ea6a8e0a6e265879600000000096e0002a21f600061c48eb98836cce3a84ca05c17483434e1c2d8cc28dea2d6a64af05a2dc20bebd228c5ae5c4a16920b16c4e3c22e0ac8a320000007e2b90000286692634a500003f6d6665e0f45e89e8206240000d804aeb600009fc0002fe2d4c2c6f40004e60de00012471e36e3e09100440f634c92e9ce0da3945420000005ba51a684086cf49b2000342362b80650aa85de13cb142da6f6c3a8406c600078200000000000027c000d12d84000b44bf422cb2899200077e08a0007188ae000042000000700bb0330108160c38c6e6ca0007d80000007d2b7a8d23408c6d96732000b560766a0864a30000da800076e000ae2000536e1224a0004040000008a82123068a2be2612b525ee968a86d4e1908f6344baa11c1da6888b444eb66e081d04e202a9402ee2c21fe898c2e090cfc33c19639caf29bc8d4000b70b76000000ba67bcda254456a30430243405a000000ab8594000bb885c0007fc000c04db862cdee674000000000000cc234600000e0000000003860008ce00000000022e9fedb2dbaa3425a2ae81ccc40c400047673e000dfc000cd472000058200017696c5a400052220a0000005c800000000000018a0006360002422e2904000d5899c00041c000c8a00041e83c5647da1502f43a02500560008f04c40000000008e6000000000000638de2dd6292c4885666a000000b0026865289282400000065600088e1aeae8000a620068a40000000002288fe000000842aec00062400000011e000a080e80004922f2948000a0421a9503d885a8b00000007ea000bbe01450ebb23ead28d68df43ba204c5445a3808bca4421e44035880a586c0a38cc144d856e1be0001e2000966000000b380000000007300a8d080000001f835600055e0003fa4bc6e800000039e000382094580a54000ace000000000050af8a4e00000078ebc433a0300f8d82ab200037020c63e5246c2cb625e1b0048000c6083a1f00aa11806c7caa7e000754a6e4600008c86e08b80000000000000003d2694000000a820003ecc720000fa00016e6040006d4c1c9cc0001ee000468312532000000000000000000704c8c2c8bb6778c68b960002f6c8e3084028967b2000884000088bba9dab4c23e8e40000004b8a7c00009e3e6ba08d0906000246cb24b00e4000b301c09225c67a600057ec82418ad8000b22c5cc12310294c78bb43ee18895c5205ac438c24a840ca698c4687463c76a04a6f81e69aad062a48eac32db45a
  | 12 => 0x99e7507441460009a8cea10a0006301ec2a0ca2cac1cc7c00004a036c422020110918e0694e40a71a1dc9faa0cb0a28279a0000000000000004a85fe18e4426800000009e68580001204dc2a8a2428e000a929702c0aa41fa3ae91c4e054e37e098bc29f2000b820d000057c4a66a618c0e60002d0210a2ac5eaca50099aa3cb266b6a066325d05f41343e26d279e49a06aab0000c348b6ad20009a472a0001c60000006f0556caa6da77ac9200093073a00037417e8a05124d63de00014055232ac262262de5387e419e89acd01ced2ce1400000000000056c55ca4c000028b8ea946e40000002222c6000d1cacc000000b2cd6262000062613a000336000000000000608b9a540c76722b7ca6c9f600000009624ca58000932b0ecec74c00000048a000b9ca2e0e25840002faa284cc98654c9de0007de388b4275c0000006fc00045e80c66ccbc7d0000000000000bae4f8abe27000012a6020005683548ac5585101146acd8a3683bc0340006fe4fc956186db0000000792860adc0786b0ca42ac054676022bd697a9d84820d45e62363ca7f6000908b3ed3c000000dbc85ea0e04600016a7c489e0001582606be686cf01980008140000000007e0000bfed10c1e77c000dc67b00000001621ea00000033eb880000000003ac0000004dec880002307665500006cc97c5a8000c84a38a14a8c9c0000b3a0000000005aa4f46b856661abec10c1a40000008d6c580007703c4ad4d9e000cd878c8decee03e000000610b0c316000c167c8854b020bcb1ad9893c0000fc24e9248087e697832841629e10e588972cfa902d76248000868b3c3f2b1e0000004b4000446000802000000a6644c614ce2000d049824a413e00075e51622a0008e2c4076c3fc60a5b4b064529809c4084018c4aa8e0fe392000000d7c7c600063a0000000005dcd5c0000b20000008189e02ce8a62fc53a1aa0001f4d50000132e0005800000058c000000000a1200067c9ae0007569ec00088c12e07e3e4d64cc894ac74c7c14c8c40000000000000003200007aa19c9ea000c086627ba7167ec0005d63b8000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x85297414920842a4b98a490421c250c5248210a1ce429a868850d7214d4344287390a8a1a21435c85450d10a1ee4b2a868850c725954344287390caa1a21435c86550d10a28eab0a86886146558543442c8382c2a1a21461d56050d10c30cab028688590715814344348b0ac0a1a21075cc645491083ae831aa48841e7650d524420e3b286a9221075ce641491083ae9318a48841f7650c524420ebb286292218519543505109a2e63028288691431814144270b90c0a0a2185195434c510962e83026288691431813144270b90c098a21851954348510a4ae82924288545731492144382a18a490a212c5d060485109a2e6302428869143181214430c32a86a0221345cc6150110d228630a80884e172185404430c32a86982212c5d0614c110d228630a60884e172185304430c32a86902214a5d05248110a92e62924088709431492044258ba0c290221345cc6148110d228630a408856075485204433032a4290221e050d214811083ceda9a860850e72d4d4304286b96a6a1821079d85350c10a1ce429a860850d7214d430428b388a6a1821469c05350c1083cedaa2860850e72d514304286b96a8a1821079d85450c10a1ce42a2860850d72151430428b388a8a1821469c05450c1083aed32a860850e729954304286b94caa1821079d86550c10a1ce432a860850d72195430428b388caa1821469c06550c1083ae7326a40841d7498f520420fbb287a9021075d943d4810a1ae72a4a40850d7494e5204287baa8729021435d54394810a1ae72a2a40850d7494d5204287baa86a9021435d54354810a1ae921aa40841d73990520420eba4c62902107dd9431481083aeca18a40860d43988520430aa1cc2290218650e6014810a2aeaa1e20087054354b100428cbaa8708021865954384010e1286a9420085157550d100430bb2a8688021c150d5244010a32eaa1a200861b6550d1004384a1aa488021545cf5444010ac2e5aa220085317595110042c8b9ca8880214cdcd5444010e24e6aa22008711735511004298ba6a688021585cb5344010aa2eb29a20085917494d1004388aa4a688021c49515344010e22a8a9a20085537454d10043893a2a688021c45d15344010a62eba1a200871153d0d10042a8bac8688021645d24344010e22a921a20085317550d1004389a9a8688021c454d4344010aa2eaa1a20087135450d1004388aa2868802164dd54344010e24eaa1a20085917550d1004388baa8688021445d54344010d26caa1a20087136550d1004298ba6a488021545cf5244010e2287a922008561759491004390aa4a488021d054e5244010f028729220087114354910043912a2a488021c85515244010e84a6a9220087415354910043c0a1aa488021c8d0d5244010e8486a9220087214354910043a0a1aa488021c050d5244010
  | 1 => 0x43c828b388caa1e41455c46550f20c18cab1287905167114d438828ab88a6a1c41459c45450e20a2ae22a2871051671195438828ab88caa1c41861956050e20a2ce229a86905157114d434828b388a8a1a41455c45450d20a2ee2b2a869051471595434828b388caa1a41455c46550d20a18eab12869060c6558943482c4382c4a1a41461d56050d20c30cab028690588725814348344b12c0a1a41831954350920992e63028490689431814248270b88c0a124183195434c920952e83026490689431813248270b88c099241075ce641452083ae9318a29041f7650c514820ebb28628a41495d05148520a8ae628a4290705431452148254ba0c090a41325cc6048520d128630242906186550d4048264b98c4a0241a250c62501209c2e231280906186550d3048254ba0c498241a250c624c1209c2e2312609041e76d4d430828b38ea6a1841455c75350c2083cec29a861050e7214d430828b388a6a1841455c45350c20a34e029a861041e76d51430828b38ea8a1841455c75450c2083cec2a2861050e72151430828b388a8a1841455c45450c20a34e02a2861041d76995430828b38ccaa1841455c66550c2083cec32a861050e72195430828b388caa1841455c46550c20a34e032a861051573952510828aba4a72884145dd54394420a2aeaa1ca21051573951510828aba4a6a884145dd54354420a2aeaa1aa21050d7550f2008382a1aa390041465d54388020e2286a8c401050d7550d2008307b2a8690041c150d5148020a32eaa1a401061b6550d2008388a1aa290041525cf5448020ac2e3aa240105297595120082c4b9ca8900414adcd5448020e14e6aa24010709735512008294ba6a690041585c75348020a92eb29a40105897494d2008384aa4a690041c29515348020e12a8a9a401054b7454d20083853a2a690041c25d15348020a52eba1a401070953d0d20082a4bac8690041625d24348020e12a921a40105297550d2008385a9a8690041c254d4348020a92eaa1a401070b5450d2008384aa2869004162dd54348020e14eaa1a40105897550d2008384baa8690041425d54348020d16caa1a401070b6550d2008390aa4a290041d054e5148020f028728a40107094354520083912a2a290041c85515148020e84a6a8a40107415354520083c0a1aa290041c8d0d5148020e8486a8a40107214354520083a0a1aa290041c050d5148020a1ce429a878850d7214d43c4287390a8a1e21435c85450f10a1ce432a878850d7219543c430a32ac2a1e21075ce6414b1083ae9318a58841f7650c52c420ebb28629621495d05248710a8ae629243887054314921c4287390a6a1c21435c85350e10a1ce42a2870850d721514384287390caa1c21435c86550e10c30cab02870841d73990528420eba4c62942107dd94314a1083aeca18a5
  | 2 => 0xc828243075d2631412183eeca18a090c1d7650c504860f3b6a6a1843469c35350c21a32e1a9a8610c1e7614d4308687390a6a1843459c45350c21a34e029a8610d197014d430860f3b6a8a1843469c35450c21a32e1aa28610c1e761514308687390a8a1843459c45450c21a34e02a28610d1970151430860ebb4caa1843469c26550c21a32e132a8610c1e761954308687390caa1843459c46550c21a34e032a8610d19701954308686baa8790843455d54388421a1aeaa1a4210e0f6550d210868abaa869084385d954348421a8ae7aa24210d6170d512108692baca890843615ce5448421a4ee6aa24210f06735512108782b9aa890843495d35348421ac2e1a9a4210d457594d21086c2ba4a690843c15525348421e0ca8a9a4210f055454d21086a3ba2a690843c19d15348421e0ae8a9a4210d2575d0d2108782a9e8690843515d64348421b0ae921a4210f055490d2108692baa8690843c1d4d4348421e0aa6a1a4210d457550d2108783aa28690843c15514348421b0eeaa1a4210f067550d21086c2baa8690843c15d54348421a0aeaa1a4210e876550d2108783b2a8690843465ce5494021a32e929ca010d1b7550e500868cbaa8728043c85512194021e82a690ca010f81434865008782a1a42a8043465ce5454021a32e929aa010d1b7550d500868cbaa86a8043c89512154021e42a890aa010f425348550087a0a9a42a8043e050d2154021e128790aa010f11438855008784a1a42a8043c450d2154021e468690aa010f42434855008790a1a42a8043d050d2154021e028690aa010d0d7299153d028ab8cc8a9e81625c86050e40b22e230287204a9721814350258b88c0a1a81625c86050d40b22e230286a061543984525030aa1ac2292818350e6214540c1a86b10a2a0619535834310287baa86a90814a5c34354840e0a87294a2207054354a511028bbaa86a8881c150e5254440e0a86a92a22053170d0d5110306b1aa5a00818558d51d0040e1286a94802071143546401028cbac86a0081c290d5250040e2486a8a802050d7298d54cc28ab8cc6aa661439c86550e30a1ae432a871851671195438c28ab88caa1c61625c86050e30b22e230287184c972181434c268b88c0a1a61865946050d30b12e4302869859171181434c30aa1cc2292618550d6114930c1a87310a29860d43588514c30caa2c121861439cb5450c30a1ae5aa2861851671d51430c28ab8ea8a1861439c85450c30a1ae42a2861851671151430c28ab88a8a186143dd54354830a92e121aa4187054394a510c382a1aa52886145dd54354430e0a87292a21870543549510c2a8b8486a88618359152cc030c2ac8a8e60187094354a300c388a1aa318061465d7434c030e1686a92601871343545300c28b388a6a1e41455c45350f20a2ce22a2879051571151
  | 3 => 0xcf4254442e0a87212a221706435095110b88a1ca328085c450d5194042a36eaa1aa021711439455010b88a1aa2a80854a5cb4354042a32e7a12a021709439095010b8521a84a8085455c66355332a32e131aa99951671195438ca8ab88caa1c65469c06550e32a32e032a871958571189438cac4b80c4a1c65315c46250d32992e0312869960d65189434cac2b88c4a1a65625c06250d32c3287300a29961943580514cb0aa1cc2282658550d6114132c1aa8b14861951671d51430ca8ab8ea8a1865469c35450c32a32e1aa2861951671151430ca8ab88a8a1865469c05450c32a32e02a2861950d75d0d320ca8bbaa86a8865515ca4354432a2ae9992a219705438c9510cb83a1a64a8865c450e5194032e2286a8ca01951b7550d500cb88a1ca2a8065c450d5154032a92e521aa01951974cc9500cb84a1c64a8065c2d0d3254032a1ae5322a7a0d197099153d06c2b90c2a1c83645c06150e4194ae430a86a0cb17018543506c2b90c2a1a83645c06150d41c3287300a4a0e19435805250706a1cc4282838350d6214141c2aa6b0e8620d0f7550d5210692b8e86a90838358d52d0441e0a86a948220d157590d411078321aa4a0883c250e5294041e1286a94a020d1b7550d5010784a1ca4a8083c250d5254041a62e3a1aa020d1973d055010788a1c82a8083c490d4154041a1ae531aa998d197098d54cc687390caa1c63435c86550e31a34e032a8718d1970195438c6c2b90c2a1c63645c06150e3198ae430a8698cd170185434c70ab28c2a1a63615c86150d31b22e030a8698e1943980524c70ca1ac0292638350e6214131c1a86b10a098e1554586430c687396a8a1863435cb5450c31a34e1aa28618d1970d51430c687390a8a1863435c85450c31a34e02a28618d1970151430c687baa86a9063515c64354831c1ac8a966218f054354a310c68abae8698863c1d0d524c431e1287294a018f094354a500c68dbaa86a8063c250e5254031e1286a92a018d517190d500c68cba662a8063c450e3154031e268698aa018d1a7014d43c868cb80a6a1e43469c05450f21a32e02a28790d1a7019543c868cb80caa1e43831956250f21a34e029a8710d197014d438868d380a8a1c43465c05450e21a34e032a8710d1970195438870a32ac2a1c43469c05350d21a32e029a8690d1a70151434868cb80a8a1a4346dc16550d21a30e0b2a8690d1a70195434868cb80caa1a43431d56250d21c18cab128690d8471589434868a3aac2a1a43851956150d21b08e4b0a8690e8562585434870632a86a1243315cc6150921d0a8630a8490ce170185424870632a8699243295d0614c921d0a8630a6490ce170185324870a32a86a0a43315cc6250521d0a863128290ce170189414870a32a8698a43295d0624c521d0a863126290ce170189314860eb9c
  | 4 => 0x80a008680701a058100000203830010080a00227002058180200c0200034800028500281e04802000180180a0080e01000028161380400804048320000800000008261500423004030020d00623802070000002a030200102a1585601800000021101a01004018000001402800010000008e0004c0b02c1b800000000980a0980200008030600180c0204605004040020d8021c0120b80801026080100101a08020008180c0000001e01004050040201400006008000104a010741c00001000008040803203814160060287c00060058020f8060e01801014008020601405036006255258452d0f14a92c029687895895114743c62a2b00a3a1e296254050d0f18b0aa028687915496114a43c92a4b00a521e45625445190f28a8ac028c87925895014243ca2c2a80a121e25525845250f14a92c029287895895114543c62a2b00a2a1e29625405050f18b0aa028287915496114943c92a4b00a4a1e45625445150f28a8ac028a87925895014143ca2c2a80a0a1c9a701855250e4cb80c2a9287259c4605494392ae2302a4a1c1f765485250e47bb2a42928743dd95214943c1eeca90a4a1f05529845250f06a92c229287c15496114943c2ea4b08a4a1e86525845250f0aa92c229287a15496114943c0aa4b08a4a1f09529805250f4930cc029287a45866014943c1aa4b00a4a1f09525805250f4930ac029287a45856014943c36a4b00a4a1e8a525805250f0ca92c029287a25496014943c12a4b00a4a1c9a701895150e4cb80c4a8a87831895254543a28e2a92a2a1c8e721815150e46b90c0a8a878358b5114543d0ac5288a2a1c1f765445150f06b12a228a8725dd95114543d0ac4a88a2a1d17765445150f0bbb2a228a87c19895114543c2ac4a88a2a1f05625445150f02b12a228a87a298a6014543d12c5300a2a1f11519805150f0aa8ac028a87a29896014543d12c4b00a2a1f11515805150f0da8ac028a87a49456014543c32a2b00a2a1e91515805150f08a8ac028a87259c4625414392ae2312a0a1e0c625495050e8c382a4a8287239c8615414391ae430aa0a1e14615455050e8c382a2a8287a198a6114143d0ac5308a0a1e86625845050f42b12c2282878358b5014143c2ac3a80a0a1e89629405050f48b0ca02828707dd95014143c1ac4a80a0a1e15615405050e4dbb2a028287a25895014143d22c2a80a0a1d1b765405050f0dbb2a028287c29895014143c32c4a80a0a1f09625405050f04b12a028287c49855014143c32c2a80a0a1f11615405050f08b0aa028287455c66454f42a32e1322a7a1585711894390ac4b80c4a1c85295c46250d42952e031286a1585711894350ac4b80c4a1a858650e6014542c3286b00a2a1615439845050b0aa1ac2282858354d62d0c42a1aeb21a84215177550d5110a92b9686a8885455
  | 5 => 0x9893f1b8174001a338469163000410000649533c856cf621f28e7c0929880a675c5d12911e3d8ac84c000ba5568250000012615e06a2281d06033654106af351871c799ee2122912f30421412cfea4a4c27cc0005f32e9c00000011c00052ac519e24cbf9b55da80d6b89a42242d6786e17849cff0784562d47f2571b45b16da0e6063a8de0cb0ae5885696f42cc54d68002561f16d01d538078c728e622aec489393ce62cbd9e900028000145000000000002ee968dd2b33342ac9bad84840fd148d334aa74b4a6b1fa488718013bc0000031929e4f8413106120007f9d45b826c000000000a1721bf4f68d55007d61c530000000a8ae56f18639613437ac32a83297c90e4d8a04ec8400000000000046600000000086a01208000e20140025602474023809526b00000000ea0a93b2040c6000002bd044030002180001fd28000000001892c2000bc8d81652546ac000000008ece18000001207688d5286a0fb2894be000079604243153e25d4a2684038ec1180b553ae81122d019240144001480004045545da4600830400245000000a50773c000164a83366084e8a48158518ca0d1000270980e60000005b0003f0ae95a96e26c6251d3172965004c80005e8b8dd8150003ecb81db5d8000001a9000144839331dcbd943000000b8cb90d807a0d17e00053446c000000a464801acd000b9c0019c230158000310d6000002a25be08d450004c40015c000072c342e2194da894000702faaa00015200094cbc8004e20000031a38a73942239000664a695a4aa45c5782600093c002b40004e10d12359028c34181418560840c44204017827819a8a0aea4b1b258c4f09543c201702263c20005f9e840260d2a2f814c1b0e6a6431a0dce400029091d4d86725a9cd489dd1ee000600eb0e8880e00e957e124f93160000017fb1b0000011e2a53a4b8467193238970619b902e8240c95126a88d340d263840c102323d63d4638dd2ce2f8581824280f0e78e45320196e886486ad9273083f4538dc17e5cabd13a964278ba85498a3d47584bab0220188db0d750a274e62604e47c4792c15c48a80d8465308146a9712f8644caa7d6045708ea92394c2cea84e320bf49d03046c0e019aa62e8000391111cea90830e20383840012c1904805bab71f8104740002866798500a0001d97723105ca58869e50c8b54000880000a4e21873640440005b000001268162929a8de8002260340017a0009996922d2321b4588001f20090b8651060014697626484d030001500b02829501600800000001100000002018000280000012178000082a0101604860010180089a0000e03002150660a8420000400000010000c0041080204000000020781a008080080800804008000000000034018080080c1b02206876010240800c028040780013804000e400804
  | 6 => 0x133a770005ac8aa87504000000000000f8660000000005c800000000002a10008846fb0f618b4400279000ab1898bd0000009a0005646c575a524387bc120b810e1a945aef23ebe8ce9d31a013c7c09663a9e9579f43925858031e5963580f95f562450abb183f83d090afe02815482a074dc510d79f943a6dd112693ee3c4408443cc6f8a0a344b6aad249240000007827f3c663d6223d34e6b8728841a8001441f52347696c8360000011b8db00098c821aa0f4160610180006990a8ef0000000019614200154aa33f68fd1f1662e6681222f1414b1c002244b2b594f30125e688b400021e000ef88b2243198382b0fc83cda17551e248701d80bc43030800400114b6ad35a0000c2abc5ee250ff93d2d4661379420b212932afb00000013842204bd40580055c0000013b0000001d91615c03800000000498c222f4367187d2ce0004b9138b30008b0538003da0013f01a4602a8940105a8b30e091e0cc67c5930610a7712c1e241627c0027452e0214f901358378bc2aa2ac1a55f0730b4c14c62e662804c482385941e44c07b30
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x110700002a1511aca590281a040e99180c188f2505a3271b069f02891aa08b0f8e140016a1a4a2801ba91e9727a0298d12878a2680089dab1790a601a22104861fab8012001c8a948316289300a419880000001d0d89838000000b8200000115a3aa80001e1c0c80002c138005000002283000c50289060c50a00240810480107020c3010014f81e01525866014943e01529856014943e01525856014943a09801895254543911801c55254543e01625466014543e02625456014543e01625456014543a05811895254143911811c15254143a05821855154143909821c15154143e01629855014143e02625855014143e01625855014143a09801956250f21a11801956150e21a09801956250d21981801c56250d21a11801956150d21981801c96150d21a04855896150d21c04755896150d21c81435c06150921c81435c0614c921c81435c06250521c81435c0624c521b0180d4d4348421b0180d514348421905879d54348421b01809d54348421b018550d2194021b01839512154021b018494d2154021b038550d2154021b018550d2154021a05811956250f20a11811956050e20a05811956250d20981811c16250d20a11811956050d20981811c96050d20a08855896050d20c08755896050d20c81435c46050920c81435c4604c9209058750c51485208898750c6048520c81435c46250120c81435c4624c120b0181d4d4348020b0181d514348020909879d54348020b01819d54348020b018550e5148020b01839515148020b018494d5148020b038550d5148020b018550d5148020a05821956150f109058750c5248710a09821956050e109098750c5248210a05821956150d10981821c16150d10a09821956050d10981821c56050d10a10855856050d10c10755856050d10c81435c86050510c81435c8604c5109058750c52485108918750c6048510c81435c86150110c81435c8614c1109098750c52481108918750c6148110d007550d2148110e006550d2148110b0182d4d4344010b0182d514344010911879d54344010b01829d543440109118750f5244010b018550e5244010b01839515244010b018494d5244010b038550d5244010b018550d5244010b018490d5244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 45
  | 5 => 909
  | 4 => 1806
  | 3 => 799
  | 2 => 90
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
  | 6 => packedAt s5K6 (810+((h/15+packedAt s5K6 (720+(h % 15)*6) 6) % 55)*7) 7
  | 5 => packedAt s5K5 (27876+((h/303+packedAt s5K5 (24543+(h % 303)*11) 11) % 1756)*11) 11
  | 4 => packedAt s5K4 (75852+((h/602+packedAt s5K4 (68628+(h % 602)*12) 12) % 2384)*12) 12
  | 3 => packedAt s5K3 (41811+((h/266+packedAt s5K3 (39151+(h % 266)*10) 10) % 959)*11) 11
  | 2 => packedAt s5K2 (5610+((h/30+packedAt s5K2 (5400+(h % 30)*7) 7) % 109)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3f3f70f7be631fcc63c7e88e39cc739f6430cf
  | 1 => 0xcfcfbf07df83e3f07c78f0f1c1f383e7a8c333
  | 2 => 0xf3f3dff81ffc03ff807f1f01fe03fc07d30c3c
  | 3 => 0x3fc1fffe00003ffff801ffe0003fff81c0fc0
  | 4 => 0xfc001ffffffffc0000001ffffffc00001ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40400010820420408408000208401081001045
  | 1 => 0x10100101040804810081001040808102004112
  | 2 => 0x4040220080049000900210090012004010428
  | 3 => 0xaa01f4420152922840125aa4042a4a501c0a80
  | 4 => 0x2aaf8841142002a52249cc9252808501ea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8fefefee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x89e13001b0b86001c000004001f9a00071680890499970c1f0a069403160000110b19001180138d03800010801d098f81801592858015189c8c80001a85121b80001e878000180020828e8a800200000000000e101d8f200008178d800001000014800000000000000281020c0000008080041c4800008204042400002ffd500bfe5402ff5500bfc54027fd4c09fe53027f54c09fc53027fd0c09bf43027f90c09fd43026f50c09fc43037fd480d7f5201ff9480dfd52005f54807fc5202ffd0807fe4202ff50807fc42027fcc807fe32027f4c807fc32037fd440d7f51017f9440dfd51005f54405fc5102ffd0405fe4102ff50405fc41027fcc405fe31027f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50037f54003fc5002ffd0003fe4002ff50003fc40027fcc003fe30027f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x22400cff59120065fac890033fc644800b7e322400cffd5120067fca890033fd5448019fe2a2400bffd8d2005dfec69002ffe63480097f31a400bff58d2005dfac69002ffc63480097e31a400bffd4d2005ffca69002ffd5348017fe29a400bffd0d2005f7e869002ffe4348017fea1a400bef50d2005ff88690006ff6248007ffa924003dfd492001ffca49000fee5248007fea924003df54920077daa4900036d5248007fe2924003ffd092001ffc849000fee4248007fea12400cfb5092001ff8849000fff3248007ff1924003fb8c92001ffa649002fed3248007fe1924000ffd8520005fec290037fe61480057f30a4000ff5852006ff8c29000afc614801dffa8a400edfd452006ffca29003bfd5148001bea8a400dff14520067fe8290037fe4148019fea0a400dff1052005ffe6290037fe3148017fe98a400dff0c52001ffe429000fef2148007ff10a4003ff48520007da429000ffc21480037fb024001ffd412000ffca090007fd5048003fe2824001ffd012000ffc8090007fa4048003fea02400cfe5012000ff88090007ff3048003ff1824001fe8c12000ffa609002ff93048003fe1824001ffc812001ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff42090007fc1048013ffb2a2009bfd951004ffcca8801afe6544013feb2a2009bf5951004ff8ca8801afc6544011ffb222008bfd9110047fcc888016fe6444011feb222008bf59110047f8c888016fc6444011ffaa22008ff95110047faa888023fc544400fffb1a2007bfd8d1003ffcc688012fe634400ffeb1a2007bf58d1003ff8c688012fc634400fffa9a2007ff94d1003ffaa68801ffc534400fffa1a2007efd0d1003ffc868801ffd434400fdea1a2007ff10d10007fec488002ff6244015ff3122003bf98910007fac488002fd6244015fe3122003bf1891004ffea4880277f5244015ff2922009ff54910006faa48802bfc5244011ffa12200aff90910047fa848802bfc424400fff992200aff8c91003ffa648802bfc32440037fb0a2002ffd4510016fea28800bfe5144005fb28a2002ff54510016faa288027f55144001baa8a2002ff14510017fe828800bfe4144005fb20a2002ff50510047ea828800bfc4144005ff98a2002ff8c510017ec628800bfd314400ffa98a2002ff0c510017fe428800bfe2144005fb10a2002ff48510007ea428800bfc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fa4044003fea022008fe5011000ff88088007ff3044003ff1822001fe8c11000ffa608801ff93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x37e6154801beb0aa418df185520d6fe82a90637e4154835bea0aa418df105520cefe62a90637e3154833be98aa418df0c55201efe42a900f7e2154807be10aa400dfd81520befcc0a90037d605482fbe302a41adfd01520befc80a906b7d405482fbe202a419dfcc1520befc60a90677d305482fbe182a403dfc815201ede40a900f7e2054807be102a418dfc41520befc20a905f7c105482dbfb22a216df991510b6fac8a885b7c645442bbfb1aa215df98d510aefac6a88577c635442bbfa1aa215cfd0d510aefc86a88577d435442b9ea1aa215df10d51006fec4a88027f6254429bf312a200df589510a6f8c4a885b7f4254429bf212a216df509510a6f884a88577f3254429bf192a215df4c9510a6f864a880b7f61544053fb0aa206ddd8551016fe82a880b7e4154405bea0aa202df10551016fe62a880b7e3154405bb18aa202df4c5510aeea62a880b7c3154405bf90aa202df88551016f842a88037f6054427bf302a200df5815109ef8c0a885b7f4054427bf202a216df5015109ef880a88577f3054427bf182a215df4c15109ef860a88537f2054427bf102a213df08151016fe20a880b771054405bf082a202df04151097feca9084aff6548425ff32a4206bf99521096fcca9081a7e6548425feb2a4212bf59521006faca908027d6548425fe32a4206bf1952108ffec890846ff6448423ff3224205bf9912108ffac890846fd6448423fe3224205bf1912108ffea890847fe5448423feaa24211ff15121087fec690842ff6348421ff31a4204bf98d21087fac690842fd6348421fe31a4204bf18d21087fea690843fe5348421fea9a4210ff14d21087fe8690843bf4348421ff21a4210ff50d210877a8690843fc43484057fb124203ffd492101efea49080ffe5248407fea924203df5492101ff8a49080fff4248407ff2124203fb9092101ffa8490847ed4248407fe2124203ffcc92101ffc649080fee3248407fe9924210fb4c92101ff8649080aff6148405ffa8a4202dfd4521017fca29080bfd5148405bea8a4202ff14521017fe829080bfe4148405fb20a4202ff5052108fea829080bfc4148405ff98a4202ff8c521017ec629080bfd3148421fa98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4202f908521007fec090802ff604841fff3024201bf98121007fac09083ffc60484037e3024212ffd412107ffca09084bfd504841ffe2824211ffd012107ffc8090847fd404841ffe2024210ffcc12107ffc6090843fd304841ffe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe082420effd9520075feca9003bfe654800d7f32a400eff59520075faca9003bfc654800d7e32a400cffd9120065fec890033fe644800b7f3
  | 2 => 0x238e400000000c4206e585436a36a1800002d88cab414800cd024000004d39c0020e7e88a002802f2dabf020b88d23a0000031e168cac5800d699e891c4aa20c88b2eb700047800000007a0000000c1d016382e600000d625cd9b6800000000008f22a24000000000034828000000004c8006da8e3c0ba552e0cb23e00000ea80033800760002bb08002a0772780000000000ea19ca7000001a60fb1a9937ace00041a9acf320ae00035800000000013a0000000394190009880000000000de0aa725c3a22685eb7818a900000130609186a800002f00000000000458f87b1500000000000b5800000008baee39a146b204be8f6781ae5ca84b33141400040a9200000001b40000000042e80000034c0036e57b7877836d014c6f8b67390ee933e00354628d88080000000002feaf95c7322000000002c24280000800640625b9666f06a5e93c00000000d0c6364000007d91013000000000016c020fe000005d800470000e8c200000600000000000000dd00061000000000780000000048580000059000ac8000016248000829d4a621c000000c0b8be1a000082dc0cc31160b408eeb156b1336bd84865a08793624a000001a200000001982580e0bb448a00a000145e0c84b94adab24498c67c0d446884951446e38c068dc48aeca2218631ee769741d898cc92c758ee719fe9829000000001046a00000360ddb500980029000a2aaea339278b4e958e4ce800000000000008a002a8004a87c2027e17242221925a80050000d09eae3a68b4b30278289b91470aba0d37ee99882d240ba24ac38f45a1e652146230ec9498e8b32ad280096800b238adf398a59422fb461ea501e386bc8ea4904e0e39eac152ca000db1f453a5e003ae1c9c04e1fc74000c32b6668c0918922c2c0b9000100e2b5136922bc2c8004321e7e000000700000011800002445fa824200021800000001a384aa8000000102403008000080d010050080802400008000000e0100102c000000f01803038030040700002020000080c00c0000c000040f00400008000000b004000000400c050080000002004010080005c0900c08014000100b004040000001c01008000080101800008030281200c020040200017000010100002400014010480404008004110340900806018010300100001014590140400000004140040000001008000000100c1201405010010140201402000010100301c0300800004020080001417034000d6fec8a906b7e6454835beb22a41adf191520cefec6a90677e6354833beb1aa419df18d520cefe86a90673f4354833bf21aa419df50d520ce7a86a90677c4354807bfb12a4039fd8952036dec4a900f7f4254807bf212a403df5095201ef884a900f7f3254807bf192a403db8c95201efa64a90676d3254807be192a400dfd8552004fec2a906
  | 3 => 0xe080029832b18009d17c000006c00600000128f256b009da34d5b722531c960fce023a858000000000000b3800000000001c159867c8fa0435e9ab129eaca11322ab2f46caa2c2b068687e560609f000000000000065000e6800000aca79a40000028800c98000021200000000008c0a80102c0006e72a26a52a6003520006c938006ea661993ec11129c2ea841000f000c0b5c93000271c800000e20000026c7480000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x930549100bf6f20549100bf7a20549100bf6d20549100c77b10549100bf7610549100bf7410549100bf78105491004f77765451003677765451009f74765451003674765451015777745451013f76745451015775745451013f74745451013f77645451013f76645451013f75645451013f74645451014f77735451013776735451014f75735451013774735451013777635451013677635451013776635451013775635451013675635451013774635451013777435451013737435451013776435451013775435451013735435451013774435451000777725451000577725451014776725451000775725451014774725451000777625451014776625451000775625451014774625451013f77425451014776425451013f75425451014774425451013777325451014776325451013775325451014774325451009f77705451000773705451009f76705451009f75705451009f74705451009f70705451001777605451001677605451001773605451009f77405451009f76405451009f72405451009f75405451013f71405451009f74405451009f77305451009f76305451009f72305451009f75305451013771305451009f74305451009f77205451009f76205451009f72205451009f75205451009f74205451000df4764851001ef4764851000cf47648510125f7754851012f767548510125f5754851000775754851000575754851011df7744851011df5744851010ef7644851010ef56448510115f77348510115f57348510106f76348510106f56348510107b74348510107b54348510015f77248510017e77248510007e7624851001ef6624851001ef46248510057e4624851001ee46248510057775248510057755248510057e6424851010fe54248510057e63248510107e53248510007f3704851000df6704851000df4704851007ff07048510016f76048510017f3604851007ff2404851010ff1404851007ff23048510107f1304851007fe7204851007ff2204851007fe52048510015f8764811001ef87648110014f876481100fdfb74481100fdf974481100e6fb64481100e6f964481100f5fb73481100f5f973481100defb63481100def963481100dfbb43481100dfb9434811000dfb724811000feb7248110007eb624811001efa624811001ef86248110057e862481100577b5248110057ea52481100577952481100efe95248110007695248110057ea42481100e7e94248110057ea32481100dfe93248110007f37148110015fa7148110015f8714811006ff0714811000efb614811000ff3614811006f7b514811006ff2514811006f7951481100eff1514811000771514811006ff241481100e7f1414811006ff231481100dff1314811006feb214811006ff2214811006fe92148110057f12148110007e12148110
  | 1 => 0x45200a77b205452009f6e205452009f6c205452009f78205452009f77105452009f7a105452000dec7648520016ec764852000cec76485201b5ef75485201bf6e75485201b5ed75485200076d75485200056d75485201adef74485201aded744852019eef644852019eed64485201a5ef73485201a5ed7348520196ef6348520196ed6348520197af4348520197ad434852001def714852001fe77148520007e76148520016ee6148520016ec614852006fe46148520016e4614852006f6f514852006f6d514852006fe6414852019fe5414852006fe63148520197e53148520007eb704852000dee704852000dec704852007fe8704852001eef604852001feb604852007fea404852019fe9404852007fea3048520197e9304852007fe7104852007fea104852001cfe76d8910056ee62d8910004ff75d8910034fe75d8910004fd75d8910034fc75d8910004ff74d891002cfe74d8910004fd74d891002cfc74d8910004ff73d8910024fe73d8910004fd73d8910024fc73d8910006bf43d8910006bd43d891007cfd72d89100567f52d891000cff71d8910014fe71d891000cfd71d8910014fc71d891018e7f51d891018e7d51d891018ef641d8910006f541d891018ef631d8910006f531d891018eef21d891018eed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891017efa40d8910006f940d891017efa30d8910006f930d891017eef20d891017eed20d891001cff7658910005bf7458910045bc7458910056ec6258910175f77158910185fb7058910004ff7558910034fe7558910004fd7558910034fc7558910004ff7458910006bf7458910004bf745891002cfe7458910004fd745891002cfc7458910006bc745891002cbc7458910004ff7358910024fe7358910004fd7358910024fc7358910006bf4358910006bd435891017cff7258910006ef72589100567f5258910056ee4258910006ed4258910056ee3258910006ed3258910174ff7158910006f7715891006e7f515891006e7d515891006ef64158910006f5415891006ef63158910006f5315891007cff7058910006fb705891007efa4058910006f9405891007efa3058910006f930589100067f76549100067e76549100067d76549100067c76549101667f64549100d67e64549101667d64549100d67c645491015e7f63549100ce7e635491015e7d63549100ce7c635491015f3f435491015f3d435491016d7f725491004f6f72549100567f625491001e7e62549100567d625491001e7c62549100576e325491015f6d32549100c57f71549100c77671549100c57d71549100077571549100be7f61549100c77641549101677541549100c776315491015f7531549100c77621549100be7f60549100bf7a40549101677940549100bf7a305491015f7
  | 2 => 0x6bf43d8121006bd43d8121014fd72d812100cfc72d81211de7f52d81211de7d52d81211deee42d8121006ed42d81211deee32d8121006ed32d812101cfd71d812100cfc71d81211867f51d81211867d51d8121186f641d8121006f541d8121186f631d8121006f531d812107efa20d812107efa10d81210067e65581210067d6558121005bf745812108dbc745812106fe4215812107ef860581210776f76549200366f76549200bf6c76549200366c765492020f6f74549201f76e745492020f6d74549201f76c74549201f76f64549201f76e64549201f76d64549201f76c64549202076f73549201ef6e73549202076d73549201ef6c73549201ef6f63549201ee6f63549201ef6e63549201ef6d63549201ee6d63549201ef6c63549201ef6f43549201ef2f43549201ef6e43549201ef6d43549201ef2d43549201ef6c43549200076f71549200056f71549201ff6e71549200076d71549201ff6c71549201ff6e61549201ff6c61549201f76f41549201ff6e41549201f76d41549201ff6c41549201ef6f31549201ff6e31549201ef6d31549201ff6c31549200bf6f70549200076b70549200bf6e70549200bf6d70549200bf6c70549200bf68705492001f6f605492001e6f605492001f6b60549200bf6f40549200bf6e40549200bf6a40549200bf6d40549201f76940549200bf6c40549200bf6f30549200bf6e30549200bf6a30549200bf6d30549201ef6930549200bf6c30549200bf6f10549200bf6e10549200bf6a10549200bf6c1054920014fe76d85200076d52d852006ef661d8520004ff75d8520034fe75d8520004fd75d8520034fc75d8520004ff74d852002cfe74d8520004fd74d852002cfc74d8520004ff73d8520024fe73d8520004fd73d8520024fc73d8520006bf43d8520006bd43d852000cfd72d8520014fc72d85201e67f52d85201e67d52d85201e6ee42d8520006ed42d85201e6ee32d8520006ed32d852006e7f51d852006ef621d85201e6f521d852000cfe70d852001cfd70d852000cfc70d8520176fa40d8520006f940d8520176fa30d8520006f930d8520176f710d8520005bf7458520065bc74585200076d525852006ef461585201ddfb70585200067f76545200067e76545200067d76545200067c76545201ce7f64545200b67e64545201ce7d64545200b67c64545201c67f63545200ae7e63545201c67d63545200ae7c63545201c73f43545201c73d43545200a57f72545200a76e72545200a57d72545200076d725452009e7f62545200a76e42545201cf6d42545200a76e32545201c76d32545201d57f715452007777715452006e7f61545200167e61545200167c615452006f7631545201c775315452006f6f215452009e7f605452009f7a40545201cf79405452009f7a30545201c779305
  | 3 => 0xd71d81510157c71d81512367f61d815123f7761d81512377631d81510077531d815109d7d70d815109e7e60d815109f7a60d815109e7c60d815109f7710d815109f7a10d81512377910d815109d7f76581510057f74581510b57e74581510057d74581510b57c74581510067f64581510067d64581510057f73581510ad7e73581510057d73581510ad7c73581510067f63581510067d63581510073f43581510073d43581510057f72581510a57e72581510a57c72581510067f62581510067d62581512257f715815100777715815122d7771581512267f615815104f77615815122776315815100775315815109d7f70581510077b605815109e7e605815109e7c605815109f78605815109f7a305815100779305815109f7710581512157f76595210967f76595210347f76595210067f64595210067e64595210067d64595210067c64595210067f63595210067e63595210067d63595210067c63595210073f43595210073d43595212157f72595210076f72595212156f72595210a76e42595210076d42595210a76e32595210076d32595210c57f715952100777715952121d7771595210c77641595210077541595210c77631595210077531595210a77721595210c76e21595210c76c21595210c77421595210c76421595210067e60595210067c60595210a76f20595210c77710595210067f74595210067e74595210067d74595210067c74595210067f73595210067e73595210067d73595210067c73595210067f43595210063f43595210067e43595210067d43595210063d43595210067c43595210a67f72595212147f72595210066f72595210a67f42595210a67e42595210a67d42595210a67c42595210a67f32595210a67e32595210a66e32595210a67d32595210066d32595210a67c32595210c67f71595210c47f71595210067771595210c67f41595210c67e41595210c67d41595210c67c41595210c67f31595210c67e31595210c67631595210c67d31595210067531595210c67c31595210c67f21595210c67e21595210c67d21595210c67c21595210067f70595210067e70595210067d70595210067c70595210067f40595210067e40595210067d40595210067c40595210067f30595210067e30595210067d30595210067c30595210a67f20595210a66f20595210a67e20595210a67c20595210c67f10595210c67710595210c67e10595210c67c105952100cfe76d81210957e75d81210057d75d81210067e65d81210067d65d8121187e421d812107efa60d8121004ff75d8121034fe75d81210067e75d81210347e75d8121004fd75d81210067d75d81210047d75d8121034fc75d8121004ff74d812102cfe74d8121004fd74d812102cfc74d8121004ff73d8121024fe73d8121004fd73d8121024fc73d8121
  | 4 => 0x81520bd7f70581520077b60581520be7e60581520be7c60581520bf7860581520bf7a30581520077930581520bf6f205815225d7e76d89510057f74d89510b57e74d89510057d74d89510b57c74d89510067f64d89510067e64d89510067d64d89510067c64d89510057f73d89510ad7e73d89510057d73d89510ad7c73d89510067f63d89510067e63d89510067d63d89510067c63d89510073f43d89510073d43d89510c57d72d89510a67e62d89510a76e62d89510a67c62d89510357f71d89510157e71d89510357d71d89510157c71d89512167f61d89512577761d89512177631d89510077531d89512176f21d89512176d21d895109d7e70d89510057d70d895109d7c70d89510067e60d89510067c60d89512177710d89510067f74d89510067e74d89510067d74d89510067c74d89510067f73d89510067e73d89510067d73d89510067c73d89510067f43d89510063f43d89510067e43d89510067d43d89510063d43d89510067c43d89510c47d72d89510a67f42d89510a67e42d89510a67d42d89510a67c42d89510a67f32d89510a67e32d89510a67d32d89510a67c32d89512167f71d89512167d71d89510347d71d89512167f41d89512167e41d89512167d41d89512167c41d89512167f31d89512167e31d89512167631d89512167d31d89510067531d89512167c31d89512167f21d89512166f21d89512167e21d89512167c21d89510067f70d89510067e70d89510067d70d89510067c70d89510067f40d89510067e40d89510067d40d89510067c40d89510067f30d89510067e30d89510067d30d89510067c30d89510a67f20d89510a67e20d89510a67c20d89512167f10d89512167710d89512167e10d89512167d10d89512167c10d895124d7f76589510057f74589510b57e74589510057d74589510b57c74589510067f64589510067e64589510067d64589510067c64589510057f73589510ad7e73589510057d73589510ad7c73589510067f63589510067e63589510067d63589510067c63589510073f43589510073d43589512157f72589510076f62589510a67e62589510a67c62589510a76c62589510a76e32589510076d32589510c57f71589510077771589512457771589510c67f61589510977761589510c77631589510077531589510057f705895109d7e705895109d7c70589510067e60589510067c60589510a76f20589510c777105895109d7e76d81510057f74d81510b57e74d81510057d74d81510b57c74d81510067f64d81510067d64d81510057f73d81510ad7e73d81510057d73d81510ad7c73d81510067f63d81510067d63d81510073f43d81510073d43d81510a57e72d81510057d72d81510a57c72d81510067f62d81510067d62d81510357f71d815123f7771d81510157e71d81510357
  | 5 => 0xc67c61d85520c77621d855221f7521d85520bd7e70d85520057d70d85520bd7c70d85520067e60d85520067c60d855221f6f20d85520067f74d85520067e74d85520067d74d85520067c74d85520067f73d85520067e73d85520067d73d85520067c73d85520067f43d85520063f43d85520067e43d85520067d43d85520063d43d85520067c43d855221e7f72d85520c67d72d85520347d72d855221e7f42d855221e7e42d855221e7d42d855221e7c42d855221e7f32d855221e7e32d855221e6e32d855221e7d32d85520066d32d855221e7c32d85520c67f41d85520c67e41d85520c67d41d85520c67c41d85520c67f31d85520c67e31d85520c67d31d85520c67c31d85520c67f21d85520c67e21d85520c67621d85520c67c21d85520067f70d85520067e70d85520067d70d85520067c70d85520067f40d85520067e40d85520067d40d85520067c40d85520067f30d85520067e30d85520067d30d85520067c30d855221e7f20d855221e6f20d855221e7e20d855221e7d20d855221e7c20d85520c67f10d85520c67e10d85520c67c10d85520c57f76585520057f74585520d57e74585520057d74585520d57c74585520067f64585520067e64585520067d64585520067c64585520057f73585520cd7e73585520057d73585520cd7c73585520067f63585520067e63585520067d63585520067c63585520073f43585520073d43585520a57f72585520076f72585522556f72585520a67f62585520976f62585520a76e32585520076d32585520c57f71585520077761585520c67e61585520c67c61585520c77461585520c77631585520077531585520057f70585520bd7e70585520bd7c70585520067e60585520067c60585520a76f20585520c77710585520bd7e76d81520057f74d81520d57e74d81520057d74d81520d57c74d81520067f64d81520067d64d81520057f73d81520cd7e73d81520057d73d81520cd7c73d81520067f63d81520067d63d81520073f43d81520073d43d81520357f72d815227f6f72d815201d7e72d81520357d72d815201d7c72d81522767f62d815227f6f62d81522776e32d81520076d32d81520c57e71d81520057d71d81520c57c71d81520067f61d81520067d61d81520bd7d70d81520be7e60d81520bf7a60d81520be7c60d81520bf6f20d81520bf7a20d81522777920d81520bd7f76581520057f74581520d57e74581520057d74581520d57c74581520067f64581520067d64581520057f73581520cd7e73581520057d73581520cd7c73581520067f63581520067d63581520073f43581520073d43581522657f72581520076f725815226d6f72581522667f62581520776f62581522676e32581520076d32581520057f71581520c57e71581520c57c71581520067f61581520067d615
  | 6 => 0xb7c0000000007200008e4ce4e4cbbcc48cb8000d60000d80000000000000000000000c2c0ecf008045bc00002c000c3ca582c0000d84bec598178c842f82c8fb4d44854954030e1c0008740000000000000000000a83e8000000000000e30ff03b48780005b00000000004b0394b44d40d20000f1c0000000000009a49ec000000000000000000000274d9c04c2283c471098c6484f09840001b800000000000025c8440000380000009f8000dac12078c0008240000000000008d40002e0c08d5c00020c9481a00005d819c0000000000000000000000000000000008f409430c000000000ab80f03c04d4e80590990724bb8f8c17c0008f80f8bd000053cb1c000edc000000000000be502400000037cd7c000b0092c5700000000000000000010305b8000000358360e5504000062c000000000000000fcc000000de0000000a3c000cfc618000000500000bf4000000164000000000db438c0000007f89880000000000009805800080100101c0000100200000c03803000000008000300080000100000800000002008000000000000100000c0100000b0000000000a006000058020060000000100200001800004064000000100080100000400000004000008000010020000480300e00000000000000080000000040180000600400003000008000010020200080200a0000280800000800000008018000010000000400200000400003002000020000080340000002a000010000080080200500000000804006004020070000000180300c0000000900001000001000014000010000240080001e0040200100200001803006004008020020000080500a00000001000000030040020000100a0000000380300e01800006000014000000020000100300a004038000000040100100800c01002012018008030000040280a0020000000700000002800002000000010020040000100200000000004000020060000040000000001c0080300200003800000000000000000080000800000c0d00100201401800004010008040040280080300000c00801000004010010020040000000400c00006016000000010060080000000000000800006000000060060100000100600800001000010000000040040000100a0080000100000000003002004000020060140100000e030008000c57e76d85520057f74d85520d57e74d85520057d74d85520d57c74d85520067f64d85520067e64d85520067d64d85520067c64d85520057f73d85520cd7e73d85520057d73d85520cd7c73d85520067f63d85520067e63d85520067d63d85520067c63d85520073f43d85520073d43d85520357f72d855201d7e72d85520357d72d855201d7c72d855221e7f62d85522476f62d855221f6e32d85520076d32d85520c57d71d85520c67e61d85520c77661d8552
  | 7 => 0xe80000000006d40000009dc0004b8000000a4c0007d00000d811c1e0000368000d10000000000000000c14838000c50700000e6c6f0000000a7c00062048100c3e40000000000000000003240009d0000000ce8b98a9800000000000000077cd0c0000000000000009f45c0ec8698ca8000000fbcfc8fb0c7c0000000003b0000000000000a9c305054000058be8fa0ef0000000000000000ba10700000009cc7946d8e34004020fe401809c8ecf21048bf059c66901400000000000081089c000c006bcbb00002ec00000055c000a289f09e0f043203ac95c4bcc0491400000054c344404b60000000000000000d34574f3c000000000530c5c098c0c0006041e43a0170000dcc000000000000e140000000000000000000000000000007a41d850c000000398a945e80000000008b40007f0000000aa4000da00c00000100001b40000000000000007ec000000d740000000001900002385c4760000f245400004740008fc000f340002b412c11880cc5400001c6c00140000000000009000000000005e000079cffc998a5c5f8f58f68b284d0000000000f5c0009b8001044d68c80001050000ba400000000000018839ce0c150a6831cfa50280000000000000000000000000005d4000000ec405c000a60fb8dbd0089b000000000000000084848c0601bc84cb2c4e80000001b03d4a04b34000a440009c83f0d480680fcd54514fd4194770fa8ae0000000f88000000a18000738d7082000093c0005d04ec000000b9c0003385ac00000000000000000000000045425800049c000390000000e8c0006ac5649fc000000644000000000f64000000000ad800086c6e4f54000000210b2490485818c0000000001340000009502900000000008e0000285058dc0a2c0008f0c58c942d4d94cecfec29cf10d9852c00033000000000091cb8049876c000000a2400016c00000000068c0000000000007d80000000005040010740000003082f4000000a08e649580000000001d0fe0744bfc614000000000000ed502c00000042442c3a8000000000000000000000af800000000000081c764180c300000000000004e40008bc560eac0b80006e800000040864c000000000348d640e8c440000005ec000264388f3800000106c0004a80000007cc000cbc000000100608680000e18000000000e2000000000086800000000021497400069089800032c884e98444000d28000000000000104a002cc2c4000a7041c47c7b4ea00540001d400000000103c000528000000000cc01dc000000000314b70000f280000004280000bc4647840005200000001582241f83cc4200000008400ac000cb45f4000260b50880000318000f4000006c000000000000000790000cd47f40643ec9bc71c03cda4000000aacd7864000000075c000e10000000e38000000
  | 8 => 0xf80b404a502000058c34c2dc6c8000000000000000000000378ed00000000002a8af40000006a087cafc0000000000000008140000000000005c862824c00083ca107b07e0000000000000c88000000000e840008080000001745447c47bc000000000000000000000000000bb400022ce58e60084000ea4cdc0000000440000000000000f43dca509c0d580000000000000000e4bdc774d149d4a80000a141980000001106549ac000e9c0400000006d0d0497c000fc43640009b4000a34c183f4001010ca4c28000000000000000000000c1c000000000b14d1c00000000066000057cefc548f84000674cac000000000000c60000000000000000000e44f6c0000000007a0f70000414cf4c740000004846fc26ca0c000eb4cc4000ac446036c1ecde40080000007c00007b8894000000c6400000061000000000000000066c0000000000004d8c4c0002a4c9cb789c4b6c0c40005580004f894c000000acd05c000000000e3c0000007303408ac2440000000000007d40000000000001fc0000000000000007e4c2400000060000000103430014cc10f5051c2bc00000043c000028000cd8000b640e05385a00000b07e800000008c000dd8000000000b20ebc554000000d080000d4000ef833cbc8000934dc8000000434000000b08f2c0000002e400000104c000f18000c340000004905fc000078a880000000004380000000000008880a40004cc4c4000000000fd0e08000dfc4fc000000750000384ee0268000d6c83057800099427c13c000000000000000000000000000000e400000000000006380007342d8a48f142fc5a4000000000000550000000e4828c7781f0689000df0000000000960000000000000ee8000000b846e0ca07186b400045890c8c86b0b3c67c000000000a6cb1800000000000000000000000040000000074c000000b5c2a008023c000000a90000ea8000000000a54124eb8000d2c0000000000007acf08000000350c78dd4ddc0008504c8be00000004c0b54df8adc0000007a8000f0c000000000000000000000b48584ae440c000dd0cf82b800000099c0000000000000000000004b4000000cc8000bf8000f44000000860000ab4000000000dc40000006b80000002b01284108b87dc000000000834f61068000000000000000000000000000000a38cf01c810c0008c00006f4ed8418000f74e706f87045a8714e74fd894011461ca78468168f78488140d3cc701f4000000000588fc0000c98000000000000000000728000000000374748fac000524e7cc8ce24798ad065873c5f0bd4fdc000eb00000000003e0624000cb000000000000000000000000000091000008800000000000000000065cd3800068428872c0000000000008a87c8000ff8000000ee47400010186ccbac09007c450b74000e00d
  | 9 => 0x270000e94ce0bcc518000e2c1a4b040000000005b40000000001c0000000ef4000000000000000000000070000964000000aec0000006643c8f4c0000000000485684a0e04000200b58000828000af09a8278000e888183d0000670000650144d30000ff43a50600004e021c00000056cf30000000000000000000000000000250000230a2067800000093035cb8c0003544dc000a1c00000000085c508bc4ecc9e4ccd004ad4000000148000000000944221038000aa000000088ce5c1e84409d8000000000e900001c4000000000f904940dc0005940000000000008002e80000000b4ae80d06dc130870380a84000000000000c20000000001064000000000d50630218430ab0000dec000000000000000abc2f0d88000000d90000208478000240000000000000000968000000000634000c40000000000000a7400024800000c00082c1601840000000cc2d0864c68000000000000708000000f9d01c47075496c1385e4d4c000000000000890df4000b88000aa80008a00009700000009e8000a64000a30ec00000006a4d008b0e283bc8cc5100000501a88dc534108fe84f4000b94e783fc000db0f988d0074780b903288a4978b385dc0000004ac000204000db8000000c90000da8000924000000eec000cd00000003b8000000000758f94b6893800000070c69c6ec000b0c1cc000b300000008e83d80000000000000000000002809a0ac8294000000e683f8000000d8cac0a40a8c92803446c9085cc000000f48298000e50024b107fc694d18c6c44c6c431000015c0002ac0000000006a8000000c38ba89180001ac000370768d24000000154000000000000000000234f7c8d892060c448bd88c4000000254bc045c0000c8334b4c0000a078863c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc7760dc95144085ae6c1b92a2880035c9037254510006b8a06e4a8a2000d7230dc95144001ae261b92a2880a35c88372545100053bc32e4a8a2013a74865c951440258e8ecb92a288002dce01725451009db8402e4a8a2000d70705c9514400166f08b12a28809ecd21162545102d732312c4a8a2030b738058951440276e50fb82a28804f5ca1f7054510015b9436e0a8a2002b7086dc15144027ae4edb82a28804f5c1db7054510005b9c26e0a8a2000b7184dc15144001ae6e9b82a2880035c5d37054510005b9c1ee0a8a2000b7183dc15144001ae6e7b82a2880035c5cf705451000799a1ee0a8a2000f3143dc151440016e305b82a2880035cdcb7054510006b8b96e0a8a2014c74765d521440856cf04baa42880539918975485100063bc32ea90a2000c74865d521440018eec6baa42880031d58d75485100069ba1aea90a2000d35435d521440852ef04baa428800359e097548510146b3192ea90a2000d65325d52144001ae700baa42880035c20175485100c63bb02ea90a2018d73605d52144001ae480baa42880035c5017548510006b9182ea90a2000d71305d52144051ace40baa42880a35c8817548510006b2902ea90a2003ae686d892144001ae2ebb8242880039ae19524811000734432a49022003e6b765492044007cd0eca92408817b9ad9152481102f734b22a49022060d6b7354920440c1ad2e6a9240881779ad8d52481102ef34b1aa4902205df2b4354920440bbe5286a92408817edae0552481101ffb140aa4902205fb69815492044001ec302a9240880ffd81c552481100bf35b0aa49022017f6361549204407fec482a92408817bd850552481101ffb118aa4902205df61315492044001ec2a5b8a40880035ce1d5148110006b843aa29022002d72765452044005ae0eca8a40881735cdd151481102e6b8ba2a2902205bd737354520440b7ae2e6a8a40881639cd8d51481102c738b1aa29022058f334354520440b1e6286a8a408816adce095148110147b1412a2902205ab71825452044001ec304a8a408804f5cdc9514811009fb1b92a29022000f63625452044051ec0c4a8a40880a3d890951481102cfb0a12a29022028f623254520440b1ec264a8a4088006f821d2148110016f043a429022001be28648520440037c10c90a408800fb8219214811001f71bb2429022002de2764852044005bc0ec90a408800fb81d92148110016703b2429022056be38548520440afec50a90a408815af86152148110007b0c2a429022000b618548520440ab7c70890a4088156f861121481102a6f1ba2429022054de17448520440a7dc6c890a408814fb85912148110295f1c1a429022052be18348520440a3bc6e690a4088147785cd214811028771b1a429022050ee16348520440a1f468690a4088143e850d2148110
  | 1 => 0x461b8aa4900035a4c371549201feb5086e2a924000a6f865c5524802f4d90cb8aa49004b1b1d97154920005b5c02e2a924017b68805c55248001ad0e0b8aa49005edaa1f70549200beb543ee0a924003b6a86dc152480076d10db82a49005f5a9db70549200beb43b6e0a924000b6b84dc152480016d309b82a4900035add37054920006b4ba6e0a924000b6b83dc152480016d307b82a4900035adcf7054920006b4b9ee0a924000f2b43dc15248001e5287b82a490002da6077054920006b5b8ee0a924000d6971dc152480010ff0ab9ec29001a1f21573d85200264f39a87b0a4000c9d7350f6148001d1a86996c290003aa50940d85200074ca1a61b0a4000ec9324c36148001a5ee8a92c2900fb4b1d152585201ff3230aa4b0a403bd6b7054961480014eb033b2a2900028fe1176545200b51e422eca8a4000a5f835d9514802b4b906bb2a2900029de05765452009d36432e4a8a4062b67815c951480276d100b92a2900631b1d9754852021db3c0aea90a4018e64615d521480018df0cbaa42900031b219754852000637b1aea90a4000c6d635d52148001a5e86baa42900034b50d754852021cb7c0aea90a4000d67815d5214807facc62baa4290003594c57548520006b5c02ea90a4000d68805d521480298dec0baa42900535ad817548520006b5202ea90a4000d69405d52148001ad460baa42900035a4c175485201feb3882ea90a403fd6a105d521480055cd0db0a42900035a5d770485200043fc2ae7b12200687c855cf624400993ce6a1ec488003275cd43d89100074aa1a63b122000eb1415036244001d3286986c488003b44c530d89100045fc22eab1220058bc845d562440011bf06baac4880123720d755891002c5f43ee8b1220008bd83dd1624400187ea5ba2c4880030f54b74589100061fa8ee8b122000c3d51dd1624400117d0e3a2c488002a760c74589100043fc2ae6b12200687c855cd624400117f08b9ac4880162f21173589100045f43e86b1220058bc87d0d624400117d0ea1ac4880022f21d43589100264f39a86b122000c9d7350d624400b1d90ea12c4880123b21d325891000746a1a64b1220058f4875056244001d4a84a0ac4880123d21d31589100074aa1a62b122000ec5324c562440031f50fb82c4880163e21d405891000754a1280b122000eb14150162440091f10e982c488003a650d30589100076499260b122000ed1314c162440014db053b2a4880028fe1176549100d51e422eca922000a5f835d952440334b906bb2a4880029be0976549100bd3a432e2a922061b67825c5524402f6e100b8aa48812b1d1db725451009db8406e4a8a2000d7070dc951440018eec7b92a2880031d58f72545100069ba1ee4a8a2000d3543dc951440312eb05b92a2880035ce037254510006b8406e4a8a2042
  | 2 => 0xf71595210071ba1ee2b2a4200e3543dc565484d38eee5b8aca9080399dcb715952134f33196e2b2a4200e6532dc565484014eb01b8aca909a799c8371595210053b43a62b2a4200a74874c565484314ef0698aca9086395e0d31595210072bb9a62b2a4200e54734c56548401c6e8698aca908039590d31595210071aa1a62b2a4200e55434c56548401c2a8698aca9090b1ddc9315952100733b9262b2a4268e57324c565484d1ccc6498aca909a3954c931595210073299262b2a4200e45324c565484014ef0098aca909a399c81315952100536c14e0b2a4200a75819c1654840147f08b82ca908028f21170595210052fc1ae0b2a4200a5c835c165484014df04b82ca908029de0570595210051f420e0b2a4200a3d841c165484014bd06382ca908029760c70595210a53741480b2a4200a6d8290165484314ed03202ca908029d60640595210043f43880b2a420087d8710165484014bd06202ca908029760c40595210a53741080b2a4200a6d8210165484314ed02202ca908029d60440595210051f42660b2a4200a3d84cc16548401c3a87982ca908529ba0b305952100536c1660b2a4200e4d32cc165484314ed03982ca908029d60730595210072a98e60b2a4214a6e828c165484014db05182ca908629da0630595210053ac0c60b2a420087f874c165484010f90e982ca908038750d30595210a53741260b2a4200e4d324c165484314ed02982ca90803954c530595210043f43860b2a420087d870c1654840147d08182ca908028f61030595210a53741060b2a4200a6d820c165484314ed02182ca908029d60430595210343fc32ebb02421887d865d760484852df04baec09090e5de0575d8121006b210aebb02420087d8799760484cd4db0532ec0909969d60665d81210043fc3acbb024267e642159760484010fb0f3aec09099a9b60a75d812132d3ac0cebb02420687f875d760484850ff04baec0908621f60975d812100637192ebb02424387f815d760484290fb02baec0908031d8c575d81210343f42ee9b02420087d85dd3604840d0fd0bb9ec0908021f61773d81213261f3ae87b024200c3d75d0f60484c787ceaa1ec0908030f5d543d81210264f39a87b024200c9d7350f60484018daea996c090803a350d32d812100752a1283b024200c75754c76048401d2a8698ec090803b14c931d81210061e3a4cab02425fa6d8299560484b54eb0332ac0908030f1d165581211ff3210acab024200c3e65dd1604840187acbba2c090803690877458121246363b6e2a924017b6880dc55248001ad0e1b8aa4900031bd8f715492000636b1ee2a924000d2f43dc55248001a5a87b8aa4900525b6077154920006b5c06e2a924000d6880dc552480878dec1b8aa49010f5ad837154920006b5206e2a924000d6940dc55248001ad
  | 3 => 0xb02a27dd73714c16054401ea262982c0a88021fa1f64595213e73210cc8b2a427ba6f8259165484f54ef02b22ca908021fa1c64595210052f418c8b2a4200a5d8319165484f3cc842322ca908029ea0064595210053cc00c8b2a420087e87d8d65484f1cc843b1aca908028fa1263595210051ec24c6b2a4277a6d8298d65484ed4eb0331aca909ab9908563595210043f438c6b2a4200a3e8418d654840147b0831aca908029ea0063595210053cc00c6b2a4264c3f76d0d65484e7a5ee5a1aca909d74ddc7435952138f9210e86b2a4263c3f7650d6548401c3cc6a1aca908038758d435952137e97b9286b2a4274d377150d65484dbe4842a1aca908629b21942595210071632284b2a4218b64815096548487acee2a12ca908629b219325952100727b1a64b2a4200f0d434c965484316c902992ca9090f59dc532595210c5b3416e2b2a4200d6772dc565484294e90ca0aca908038d19141595210a5b241282b2a4242d67725056548401e4a84a0aca908529d21931595210072bb1a62b2a4200f15434c565484296c90498aca9090b59dc93159521007a299262b2a423fa6d8298165484514eb03302ca908028fa1060595210051ec20c0b2a4200a5e8318165484014bb06302ca9080297a0e74595210052ec1ce8b2a4200a6d829d165484014eb033a2ca908029be0974595210053bc0ae8b2a4200a3e849cd654840147b0939aca908029b60a73595210053ac0ce6b2a4200a6f825cd65484014ef02b9aca908028fa1073595210051ec20e6b2a4200c5d731cd65484014f50039aca908029e60073595210043f43e86b2a420087d87d0d654840187d0fa1aca908030f61f435952139e1fb9686b2a4272e2e32d0d65484e387ee3a1aca909c78d8c743595213971790686b2a4271e3710d0d65484e147b0921aca908529ba0a435952100536c1486b2a4218a768190d65484014eb0321aca9080387e0d43595210070fb9a86b2a4200e1c7350d65484df87ee4a1aca909bb87cc943595213771719286b2a426ee1d3250d65484db87ee2a1aca909b787cc5435952136f1b18a86b2a426de1d3150d65484ddc5e40a1aca909b78dc4143595213651f42086b2a4214a6e8210d65484014db0421aca908629da0443595210053ac0886b2a4242c6e87dc965484014db07b92ca908038bd0f725952100716a1ee4b2a426bc6f71dc965484d7ccc63b92ca908029b603725952135f33886e4b2a4200a6e874c965484014d90e992ca908529be0d32595210a727c1a64b2a4200e4f734c96548401c98e6992ca908038bd0d32595210072721a64b2a4200e2d434c96548401c9a86992ca908038350d325952121e37b8a64b2a426ae4f314c965484d5ccc62992ca909ab934c5325952100537c0264b2a426ae67104c965484318ed0fb8aca908029d60
  | 4 => 0x2544d1caa6498ec4a88029de0131d89512153b40ce1b12a28ba75819c3625440147d08386c4a88028f61070d89510052f418e1b12a200a5d831c362544014db04386c4a890a9da0470d89512553ac08e1b12a242a768190362544014eb03206c4a88021fa1c40d89510043ec3881b12a200a5e8310362544014bb06206c4a88529ba0840d895100536c1081b12a242a768110362544014eb02206c4a88028fa1330d89510051ec2661b12a200e1d43cc362544854ed03986c4a88029d60730d89510072a98e61b12a242a76818c362544014eb03186c4a88021fe1d30d89510043e43a61b12a200e1d434c362544854ed02986c4a8803954c530d89510043f43861b12a20087d870c3625440147d08186c4a88028f61030d89510a53741061b12a200a6d820c362544854ed02186c4a88029d60430d8951004bbc0ae8b12a21487e8799162544014bd07322c4a88029760e64589514553ac0cc8b12a21487c8759162544294d904b22c4a88025de0573589510a43f43cc6b12a200a3e8498d625440147b0931ac4a88529ba0a635895144d3ac0cc6b12a21487c8758d625442b8b8e6b1ac4a88028fa1063589510051ec20c6b12a214a6e8218d62544014f50031ac4a88029e60063589514469bb8e86b12a200d1f7350d625442ba38e6a1ac4a880387d8d43589510070e31a86b12a287d377150d625442b2d90e992c4a8803c350d3258951436b3b8a64b12a285d6772dc562544012ed0e98ac4a88565d21d31589510953a43262b12a200d57734c5625442baa8e698ac4a880395d8d31589510072a31a62b12a200f15434c56254401e8a6498ac4a880a5d20770589510a537414c0b12a225a7581981625440147d08302c4a88028f61060589510052f418c0b12a200a5d8318162544294dd04302c4a8a125de0574d8151014ba40ae9b02a21387d87d9360544010fd0db9ec0a880a5d20773d815141cbbc0ae7b02a202974815cf60544270fb0fb1ec0a88021fe1d63d81513269bb8e87b02a282d3471d0f6054401a3ee6a1ec0a8857471cd43d81510070fb1a87b02a263d377150f6054503a68e2a1ec0a89225de0572d8151014ba40ae5b02a21387d87d8b60544018dae5b16c0a881a5da1d31d815123cba43a63b02a200d57734c7605442baa8e698ec0a880395d8d31d81510078aa1a63b02a200977815d160544270f90eb22c0a880a5d20773581510043fc32e6b02a200977815cd60544010fd0fb1ac0a884e1f21d63581514069bb8e86b02a200d1f7350d605442ba38e6a1ac0a880387d8d43581513fe9bb8a86b02a21387c8758960544012ed0e98ac0a88565d21d3158151006abb9a62b02a215d54734c56054401caec698ac0a8803c550d3158151014bd43ec0b02a27ed7371d81605442b2f10e982c0a88039658d30581510078ca1a6
  | 5 => 0x900e5b20974d81520bc3ec3ec9b02a40087e86dcf60548072d905b9ec0a92525be0973d815201cb6412e7b02a41787d87d8f60548010ff0eb1ec0a91934bdcb43d815249e9639687b02a400d1f7350f6054833a38e6a1ec0a900387d8d43d815231e97b9287b02a492d2c7250f605480d2dd0e996c0a913e5b21d32d8152006a7b9a65b02a419d4c734cb6054801c9ec6996c0a9003c350d32d8152254b7c12e3b02a40396c825c7605482f0fb0fb0ec0a90031d5c761d8152004b7c12e8b02a41787c8759160548072d905b9ac0a90021fe197358152004b7c12e6b02a40087e87d8d605482f0f90eb1ac0a92474bdcb43581520068fb9a86b02a419d1c7350d6054801c3ec6a1ac0a92434bdc94358152004b743a64b02a41996c874c96054801a9ee6992c0a9067531cd325815200727b1a64b02a400f0d434c9605482f0f90eb0ac0a900e5ea1f605815247eb5b96c0b02a419978874c16054801cb2c6982c0a9003c650d3058152476b5b9260b02a400f49324c160548052ed03ba6c4a881a5d60774d89510a43ec3ec9b12a200a5e8399362544014bb07326c4a8a369d60664d89510a43ec38c9b12a21487d87d8f625440147d0931ec4a88028f61263d89514653ac0cc7b12a21487d8718f625440147d0831ec4a88028f61063d89510062eb98c7b12a200a7a8018f62544014f30031ec4a880347dcd43d89510ae8e39a87b12a200e1f6350f6254401c38c6a1ec4a892a9d21931d8951006abb9a63b12a215d54734c76254401caec698ec4a88039518d31d89510078aa1a63b12a28ba758198362544290fb0e306c4a88028fa1060d89510051ec20c1b12a200a5e8318362544014bb06306c4a88029b60b74d89512153b40ee9b12a24aa7581dd362544014bd073a6c4a88029760e74d89512153b40ce9b12a28da75819d362544014db043a6c4a88029b60b73d89510051f424e7b12a200a3d849cf62544854ed0339ec4a8a329d60673d89510051f420e7b12a200a3d841cf62544018bae639ec4a88029b60873d89512153b408e7b12a24aa75811cf62544014f50039ec4a88029e60073d89510043f43e87b12a20087d87d0f625440187d0fa1ec4a88030f61f43d89513261eb8e87b12a273e3631d0f62544e7c5e43a1ec4a89cf8dc4343d89512153b40c87b12a200a758190f6254401c3f06a1ec4a880387dcd43d89510070e39a87b12a26ee1f3250f62544ddc3a64a1ec4a898f0f5c543d895137f0f98a87b12a26fe363150f62544dfc3a62a1ec4a89bf8bc8543d895137f1b88287b12a242a768110f62544014eb0221ec4a890a9de0d31d89512172bc1a63b12a200e57734c76254401ca8e698ec4a88038dd0d31d89510072b21a63b12a200e35434c76254401caa8698ec4a88038550d31d89510c63ab9263b12a268e57324c76
  | 6 => 0xed36c14e9b0aa400a75811d361548014eb03b9ec2a90028fa1273d85520051ec24e7b0aa418a6e829cf61549394db0539ec2a90028fa1073d85520051ec20e7b0aa400c5d731cf61548874dd0439ec2a91229b60873d85520053ac08e7b0aa400a7a801cf61548014f30039ec2a90021fa1f43d85520043ec3e87b0aa400c3e87d0f615480187b0fa1ec2a91930f5cb43d85523af1719687b0aa471e3621d0f61548ebc5e41a1ec2a910e9ba0a43d855200536c1487b0aa400e1f8350f6154801c3ee6a1ec2a9003871cd43d855231e1eb9287b0aa474e1f3250f61548e9c5c64a1ec2a91d3874c943d855236f0f98a87b0aa46de1d3150f61548dbc6c42a1ec2a91d38bc8143d855221d3741087b0aa400a6d8210f61548874df06996c2a910f93e0d32d855200727b9a65b0aa400e4c734cb6154801c5e86996c2a90039390d32d855200716a1a65b0aa400e4d434cb6154801c1a86996c2a90531b5c532d85523572798a65b0aa46ae4d314cb61548014df00996c2a90629ba0a70d85524dd36c14e1b0aa400a3e841c3615480147b08386c2a900297a0c70d85520052ec18e1b0aa443a6e821c361548914db04386c2a90029d60470d855221d3741481b0aa400a6d8290361548010fd0e206c2a90021f61c40d85520052f41881b0aa400a5d8310361548874dd04206c2a90029b60840d85520c53b40881b0aa400a7581103615480147d09986c2a90028f61330d85520070ea1e61b0aa443a6e82cc361548014db05986c2a9003934cb30d855221d3741461b0aa400a6d828c361548010ff0e986c2a90021f21d30d85520070ea1a61b0aa443a6e824c36154801c9a64986c2a90021fa1c30d85520043ec3861b0aa400a3e840c3615480147b08186c2a910e9ba0830d855200536c1061b0aa418a76810c361548014eb02186c2a90025be0974585520c43f43cc8b0aa400a5e8399161548014bb07322c2a926a9b60a64585520c43e43ac8b0aa418a748159161548012df04b9ac2a90621fa1e63585520051f424c6b0aa400a3d8498d61549334db0531ac2a90629da0663585520c43e43ac6b0aa419c5c7358d615480147d0831ac2a90028f61063585520c53b408c6b0aa400a7a8018d61548014f30031ac2a92634bdcb43585520068fb9a86b0aa419d1c7350d6154801c3ec6a1ac2a90038718d43585524be97b9286b0aa40096e874c961548332d90e992c2a904a9b2193258552006a7b9a64b0aa419d4c734c96154801c9ec6992c2a90039318d325855200786a1a64b0aa485d6772d8561548332e90e98ac2a9003c550d31585524b6b3b9262b0aa400f45324c561548072d905b82c2a90de9b60a60585520c53b40cc0b0aa400a3e84181615480147b08302c2a900297a0c60585520052ec18c0b0aa418a7681181615492b2df04ba6c0a
  | 7 => 0x8163feba04e2e429e689c7800370858e28001e44583192b394ae0002f601c1edb7180000871379700007b4003020000018d0007d67e5979597c46a0010d676e37cf23331f200151ab15446e98b9383e80002682049669cc68d342652cadbab0001adc58000623dd12821088351b5bcd108f240991c6eaee5083ad42e5f8ce0c36104bd9116e35a6dd3616d51a5397716210a00000000324140942f924c3f9aca2e146e6c001fd5aaa285b02530cbcd62800000a1c1d299456d540020a5e8cc0819b06ca9ccbc26528ab383a1510d4454558521de320efbc6656f553227018a4ec9f2ef07c7658818b4b27781908b4cc97dc1b812bed4555a4268e7b832afa4cec051102a1fa29c80bb6652734cf9e645200a00c04005008008078110000080000200004800004000000058010000b411003056078000000060b0040150300040700100002c00000038000008030040e00000f03a0580e8070180080d0020060000f80300402006003006018020000100a00000c00a0040d0000000180800100000c0502f0040000000b0040b80680600200c008180120040000003a014000020040580681100200002803002004018010100000201001c0080880604c0040600600001401002006000068080080140d8000020080b01300004c00004022008070100000080000203a158030070000100a00c00a0340401d00000003000024084000070060000080200400003801002040030080041700c00d07400c008000000180080000c0640081001a0640e002008000220150260180200700005c170050000082180101400c0b02c00600c000080060280000200600401001002014040020040040001f00603c0000001c02c0000c00a074000080600e00a81f00200800801014000150020040241c00601a0000a0110040440084701a000020050000081300600401c170030060040000000000c000080020000580d00c00c00849000000000010000181500000200c00006006050058070080500000b0320640a00b0080396e82dd3615480d2db05ba6c2a90621f61f64d85520052f41cc9b0aa400a5d83993615493b4db05326c2a90621f61c64d85520c43ec3ec7b0aa400a3e8498f615480147b0931ec2a92729b60a63d85520c43ec38c7b0aa400a3e8418f615480147b0831ec2a9003175cc63d85520053d400c7b0aa400a798018f6154801a3ee6a1ec2a9067471cd43d85520070fb1a87b0aa400e1c6350f61548914d90c996c2a900353dcd32d85520cea639a65b0aa400e4f634cb6154801c98c6996c2a9003c350d32d85524dd36c14c1b0aa41887d87183615480147d08306c2a90028f61060d85520052f418c1b0aa400a5d8318361548874dd05ba6c2a91229b60b74d85520053ac0ee9b0aa400a5e839d361548014bb073a6c2a90629ba0a74d85524
  | 8 => 0x9d3c51ce0010300048cde9d78820008c800000058608002145f00004b0003200006dbd621e6ac00004240804ab0541123e931acf0009785c8000608a88c1af6e0000000007b6e21b105a2f86809491770ebf4d0b7f2d0e356ead1594158bf8000009ad5080077a0019e20562cf7c6384b39ca3000230526c2de00006c0020001fb4daba8003e81f8024abb420001b9900f66e40012b2c40802184e9f2390b354b16c64e770002e900a001a6ab64f0000001a32a0bb0000ac6483b9ed0007242ec363a315ca916a3f26fc834263a174a000e9a0f000001d88a43de14d2015c398a44e5a1207a0e58e203242ea80000069e07de599917a1c0489f70006294a1eb5ae1fdd99133c48b0719762b44c8b7a984428783882d46a184eba80642905a63bb20e554f1877330b096f2387346f5d822741c000e0a3c51690c0007c1925618f8cd0006b96c28e286251049391ba0007600033a64c5b81057200000000722000dfa491c2bc9569bc0008c4002d9168001a50000002884d000744000a41a900072400000000000408123b66118c9274685492825273e0b80c23b31c369311336e8000000007d23809b00054e188000dc66e0003200000032c3e872000000bbbde3a2349542b73180317e3bf6de8d800000000b1c25110182a999ab844b6cc57315d0f294d27a24268a414d1c4000488a02e348a7580023715af44f525d236d75adbd2364c152500049af64fe0731b0b680039c566001b48382e21240d80003c65df1800000bdd973931005509b800000001580000008696024e4e245098a4c20058028a4450466df5304436f1df8800664e580025800071c97000014411a99a66ee0011f8d900c0000006853c001d00335245a591b4661a655e18fb1a2448418b1000000003970ba001848eb26af0940a7542a001d22c1000419a080060000082a26000001c10670b059c44000000394001897ce000000000005f427897000c1c889b3278e51be29b5105189503f11a9ed37371000d00211fa7caeb8a39e70f43a55021d45e0000030a0aa6ec50386000000c0b6a4d22c8b302373210c8100072a000b18003c0d50db028000bc5d90245a0ed59a3e43b4db0003560000000001700000000312798ded6600000000164800774c54b589f2341382080000000111bd8124a24b902605e001552e10002792a27e0b6000000003a4001e0800152e38001c674c9dc13b793a00006337d02a001bb2836880011f2c37a024d0600057c5cc003a80fc00000014000e24002110442e95a8000004781b175000001e432d5b8e31b086f000a1400284000754002db6c8000002fb000de0e025500082c4a8af68abac79b3e4e4620000003fc5059fbce130a54000be73cd219b000362ce0543731bc1998e80054a0000003723ace891859292db50cbcf7200056b1be2161d46a
  | 9 => 0x15e692584e7b3d5be8a1c027d4c00d0daa04384a7415b5a06a495003be5962e0bdb0e3c2fb18306940e0455e1f04f8311ae03c1d43a04d93d5a6b88673dd000b945336827e1d8a13ca21ac7800000348fb5d490e0006b01480008afc0002e0000000cf0f457ee14000ca16a6453a0003e25950c2ba57ac31a72d22943d4fc2b40b842884aac1aeed04caaf51e7a07835208e921abb14034c619d99a48e00c0ea2d59053007bac184bd4da2a961ea7de9af03baac80c9080903b581a761c86a8c280b538650ea1e90da7d4a9b665ce63c0020243e7d9de17400023c5836308c60de225c3d8985633134d0d61ea0aa7ccd2c601440385e8660e200e5a84817964cab99505f260bf93fa3d14aa192bb283e62cdaf9875fe2fd1d25132c3c48fa6a770c95ebb393864b4920bc23223850b43658228f2a086a0f85f73a7372180b227a472f703c3ef1a0d78000004f2695ceb11000881cc36701a7607c0cf2580eca6a977144311985e10e3995daed118969f031b1fe15c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401e05434cb715952100585650734c56548401651901cd315952138585652434c565484016459290d31595214f7818c9434c56548401a168750d31595210068521d434c565484dfc177250d31595214f781c81434c56548401e0543dc9315952100781d0d324c56548401e05434c9315952100591a5d324c56548401644974c9315952100691a1d324c56548401a44874c9315952100591e41324c56548401a1543e013159521006914cb804c56548401a0d4360b30595210068361132cc16548401a15436073059521006914c981cc16548401a15844c730595210069160931cc1654840181c8750d305952100459a60215d760484015259408575d81210055164c215d760484015619008575d8121007035d5434cb6048401c157550d31d8121007115d5324c7604840103d981d265581210050764c74995604840182d821d265581210060d60474995604840141d931d16558121007090847459560484011a69808774581210056164c21dd160484015a19008774581210054a65070dc55248001549931c371549200070358d43dc552480015299420371549200055264c80dc552480015619120371549200045a26130dc55248001d09434c371549200054a650705c55248001549931c171549200045aa5f83dc1524800116b985cf7054920006c2e0d43dc15248001d0b7350f70549200065860771dc152480c741c955cd43d85200041b261635d52148001c0d6350d75485200071158d315d52148001d05434c575485200054a650805d5214800154993201754852000558646405d52148001561918c175485200045a261305d52148001d09434c17548520007504c5305d5214800116b985d7704852031d072557350f624400b09c985cd435891031d072557350d62440014989750d30589100054c65070dc95144001551931c372545100070558d43dc951440015319420372545100055464c80dc951440015619220372545100045c26130dc95144001d11434c372545100054c650705c95144001551931c172545100045ca5f83dc15144001173985cf7054510006c4e0d43dc15144001d137350f70545100065860b72dc151440010749858d75485100070558d435d52144001c45634c975485100074150d325d521440015319420175485100055464c805d521440015619290175485100055864a305d52144001170984c175485100074450d305d52144001d41324c175485100045ce6175dc1214402f5609760552481100bd9825981549204402756097609514811009d98259825452044031c6076615214811000658e5d85485204400196097615214811000698e59854852044001a6096615214811000658dcd85485204400196173615214811000698d8d854852044001a61636152148110006c8d0d854852044001b21436152148110
  | 1 => 0x2024000c030040801000000000000080002020040400028000604008280601008100200006165cd8018f61548016199018d43d855200583650634cb61548016499018d32d855243e83219434cb61548018557360473d8552006165cd801cf615480d06d92a1f43d85523250b64a87d0f615480141e97e0d43d8552005856477350f615490f60d921cd43d8552005856447350f6154801619901cd43d855200591647734cb615480160d941cd32d855200591644734cb6154801649901cd32d85520068350f804cb6154801a0d4360b30d85520068361132cc3615480d06d9221d30d85520060721d434c361548016199018d435855200583650634c961548016499018d325855200643a1d434c9615483390c8750d325855253683219434c961548339148750d315855255741dc9434c56154833944874c931585520341b64a86dcf605480141e96dcd43d815231e43a1d434cb605495390c8750d32d815200507a5f6350d605480190e8750d32581520ce4321d434c960548339188750d305815254742dc9434c16054833948874c93058152006165cd8018f62544016199018d43d895100585650634c762544016519018d31d89514be85219434c7625440184d7360873d8951006165cd801cf625440d07591a1f43d89513250d64687d0f625440141e97e0d43d89510058364b7350f625440160d921cd43d89514bd856447350f6254401619901cd43d89510059164b734c76254401615941cd31d895100591648734c76254401651901cd31d89510068550f804c76254401a154360730d89510068561131cc3625440d0759121d30d89510060721d434c362544016199018d43589510ae4321d434c9625454fd077150d325895100585650634c562544016519018d315895100645a1d434c5625442b9148750d315895153685219434c5625442b544974c931589510341d64686dcf605440141e96dcd43d815131e45a1d434c7605454b9148750d31d815100507a5f6350d60544019168750d31581510ae4521d434c5605442b9188750d305815152744dc5434c1605442b950874c5305815100691085831916548401a6021600645952151d8364a6350d65485456159198d435952150f810856350d654840160d9319142595210058a6406450965484e9d077150d32595210c45966372dc565484016159319141595210058c6406450565484313249850941595210c589259425056548429a2486509415952137f41dc9434c56548431344984c93159521006165cd801cd654840141e97e0d4359521005866407350d654840160d941cd325952100592640734c9654854160d9490d325952100591646434c9654853fe063150d325952100683a1d434c96548401a0c8750d32595213a703dc5434c9654853fe071050d32595210068350f804c96548
  | 2 => 0x176593d2b4289e00000d25403b85ca3b00001860000019c8b4692d800c0003412a5c630000000050d94ed33685db63e0000000006f800a4000000034d858b1c0000221c800000003982e04fa393210000640091178dc1ed91980000000000068a10015c4e003b00110816590400005c800006e661a000716e8a83a93419b0584d46b100853400000084180c516851c1400000000009200101fdc4c239acc00000b33400980007880431409914456ba248e6421314186f0000074aa0032800e36a128006700000aa000000090004100000000e35430be02988d4704797c10002c001b8920480144000017848652700136a90000120003580000a84e2f40079010005696688347aa06d0b8e8005c0003e87002b990000000000394d1f40094330000600000000015002aca2000d96c42a33e0b47e00119589e00232d400001480000a43180024a5432c06a135fa30f6ba5e0444a3c3c0c93a773f088b4d6262996eac64b38c0610092d5ede4b82c005d3a800000067ac8000d03c0a0100000060001014020905010080801800020001804060b0103000050301006010180c0000020140205000000a1b0
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2e48002223200001c02c00000001e02aa3618069880000a010c04e24500d0e5ba3260000800810050000c208c7206d152fc1a87b0aa463a036888750d30d855231c81b454b6e6a1ec0a918e415a1a5f8350f62544c740ad090ea1a61b12a26390568696dcd43d815100448b5210b06322ca90802a05a4085831916548401520d0042c18c8b2a42008986a42160064595210054434810b00322ca90802a41a3085801916548401806c9b043a4cab024200c0564d811d2655812100484b52108e8b2ac090802c05a3084745956048401a02c98423a2cab024200b08680211d1655812100621130a1a61b8aa49000290aa7e0d43dc15248001406542c6a1aea90a4000c42261434c1754852000622130a1a61b92a288002912a7e0d43dc1514400140a542c6a1aea90a2000c44261434c175485100042c152b9b0a90a4088002260a958d854852044001c80b9a86c2a429022000e8058d436152148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x806010004405ba64c211d1655812100640193680211d16558121005100b95cd436152148110005200b958d436152148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94c
  | 8 => 0x94d
  | 9 => 0x94e
  | 10 => 0x94b
  | 11 => 0x98c
  | 12 => 0x98d
  | 13 => 0x98a
  | 14 => 0x98e
  | 15 => 0xb09
  | 16 => 0xb0c
  | 17 => 0xb0d
  | 18 => 0xb0e
  | 19 => 0xbc9
  | 20 => 0xbcb
  | 21 => 0xbcc
  | 22 => 0xbcd
  | 23 => 0xd49
  | 24 => 0xd4a
  | 25 => 0xd4c
  | 26 => 0xd4d
  | 27 => 0x98954
  | 28 => 0x98955
  | 29 => 0x98956
  | 30 => 0x94994
  | 31 => 0x94995
  | 32 => 0xb0954
  | 33 => 0xb0955
  | 34 => 0x94b14
  | 35 => 0x94b15
  | 36 => 0x94b16
  | 37 => 0xb0956
  | 38 => 0xbc954
  | 39 => 0xbc955
  | 40 => 0xbc953
  | 41 => 0x94bd4
  | 42 => 0x94bd5
  | 43 => 0xd4954
  | 44 => 0xd4955
  | 45 => 0x1a09
  | 46 => 0x1549
  | 47 => 0x1409
  | 48 => 0x150a
  | 49 => 0x128a
  | 50 => 0xb0994
  | 51 => 0xb0995
  | 52 => 0x98b14
  | 53 => 0x98b15
  | 54 => 0x98b16
  | 55 => 0xb0996
  | 56 => 0xbc994
  | 57 => 0xbc995
  | 58 => 0x19c9
  | 59 => 0x138b
  | 60 => 0x124b
  | 61 => 0xd4994
  | 62 => 0xd4995
  | 63 => 0xd4992
  | 64 => 0x98d54
  | 65 => 0x98d55
  | 66 => 0x1a0a
  | 67 => 0x19cb
  | 68 => 0xa4a
  | 69 => 0x124e
  | 70 => 0x198a
  | 71 => 0x138e
  | 72 => 0x154e
  | 73 => 0x164a
  | 74 => 0x140e
  | 75 => 0x44a
  | 76 => 0xa4b
  | 77 => 0x128e
  | 78 => 0x198b
  | 79 => 0x150e
  | 80 => 0xb09895c
  | 81 => 0xb09499c
  | 82 => 0x9894b1c
  | 83 => 0xb09895d
  | 84 => 0xb09499d
  | 85 => 0x9894b1d
  | 86 => 0x9894b1e
  | 87 => 0xb09895e
  | 88 => 0xbc9895c
  | 89 => 0xbc9895d
  | 90 => 0x94bd3
  | 91 => 0xbc9499c
  | 92 => 0xbc9499d
  | 93 => 0xd49895c
  | 94 => 0xd49895d
  | 95 => 0x98d52
  | 96 => 0xd49499c
  | 97 => 0x95416
  | 98 => 0x99556
  | 99 => 0xe8e
  | 100 => 0x18ce
  | 101 => 0x138bd3
  | 102 => 0x150d52
  | 103 => 0xd5512
  | 104 => 0xb4bd3
  | 105 => 0x19cbd3
  | 106 => 0xccd52
  | 107 => 0x1a0d52
  | 108 => 0xd58d2
  | 109 => 0xe8d52
  | 110 => 0xe8bd3
  | 111 => 0xe9a12
  | 112 => 0xd4e92
  | 113 => 0x18cd52
  | 114 => 0x18cbd3
  | 115 => 0x18da12
  | 116 => 0xe99d3
  | 117 => 0x18d9d3
  | 118 => 0xbcb53
  | 119 => 0xd4cd2
  | 120 => 0x15cd52
  | 121 => 0x40d52
  | 122 => 0xbd853
  | 123 => 0xd5892
  | 124 => 0x188d52
  | 125 => 0x9d256
  | 126 => 0x139256
  | 127 => 0xe9256
  | 128 => 0x18d256
  | 129 => 0xe8a
  | 130 => 0x18ca
  | 131 => 0x16ce
  | 132 => 0x184e
  | 133 => 0x155416
  | 134 => 0xcd556
  | 135 => 0xe9556
  | 136 => 0x18d556
  | 137 => 0xb0b56
  | 138 => 0xb0b96
  | 139 => 0x140956
  | 140 => 0x140b56
  | 141 => 0x140b96
  | 142 => 0x9d296
  | 143 => 0x151296
  | 144 => 0xe9296
  | 145 => 0x18d296
  | 146 => 0xe8b
  | 147 => 0x18cb
  | 148 => 0x170e
  | 149 => 0x188e
  | 150 => 0xb5416
  | 151 => 0xe9416
  | 152 => 0x18d416
  | 153 => 0xb0cd6
  | 154 => 0xb0d16
  | 155 => 0x154996
  | 156 => 0x154cd6
  | 157 => 0x154d16
  | 158 => 0xe8b4bdb
  | 159 => 0xe8ccd5a
  | 160 => 0xbce93
  | 161 => 0xcce8d5a
  | 162 => 0xe8bcb5b
  | 163 => 0xe8d4cda
  | 164 => 0xe89d25e
  | 165 => 0xbd394
  | 166 => 0xe8b16
  | 167 => 0xe8cd55e
  | 168 => 0xe89d29e
  | 169 => 0xd5514
  | 170 => 0xe8b541e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 472
  | 6 => 1054
  | 5 => 1011
  | 4 => 230
  | 3 => 30
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 105)*8) 8
  | 7 => packedAt gbK7 (19034+((h/157+packedAt gbK7 (17464+(h % 157)*10) 10) % 685)*10) 10
  | 6 => packedAt gbK6 (54453+((h/351+packedAt gbK6 (50592+(h % 351)*11) 11) % 2036)*12) 12
  | 5 => packedAt gbK5 (63356+((h/337+packedAt gbK5 (59649+(h % 337)*11) 11) % 1214)*11) 11
  | 4 => packedAt gbK4 (16784+((h/76+packedAt gbK4 (16100+(h % 76)*9) 9) % 334)*9) 9
  | 3 => packedAt gbK3 (2490+((h/10+packedAt gbK3 (2430+(h % 10)*6) 6) % 48)*6) 6
  | 2 => packedAt gbK2 (371+((h/1+packedAt gbK2 (368+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x60631c88e0c7fe88e3870e38e3e3c081e430cf
  | 1 => 0x8383e30f00f8e10f1c07f1c0fcfcc32688c333
  | 2 => 0x3fc03f000ff01f01ff801ff00ff0c47130c3c
  | 3 => 0xfc0003ffff0001ffe00001ffff0030781c0fc0
  | 4 => 0xfffffc00000001fffffffe0000003f801ff000
  | 5 => 0xfffffffffffffe000000000000003fffe00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x400200120002081000820200000201045
  | 1 => 0x812109044844010402404050488122804112
  | 2 => 0x1240290089208100920009400920445010428
  | 3 => 0xa4000022420001aa401025228a0010081c0a80
  | 4 => 0xea4a4800120011cc9254ac020a003a801ea000
  | 5 => 0x53f393cc9ce49c000060c804101aaff7c00000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffeffeafefefee8fffeffeafefefee8fffeffeafefefee8fffeffeafefefee8fffeffeafefefee8fffeffeafefefee8fffeffeafefefee8fffeffeafefefee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_33394
namespace PEqualNP.Outside.L_meta_33394
open PEqualNP.Outside.L_meta_33394.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 9 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 50 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_128 : Interval s0Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 136 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
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
theorem bs1_3_0 : Interval s1Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 16 := bs1_3_0
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
  · exact alls1_2 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 16 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 92 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_32 : Interval s3Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_64 : Interval s3Atlas 2 64 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 78 := (concat bs3_2_0 (concat bs3_2_32 bs3_2_64))
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
theorem bs3_3_224 : Interval s3Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_256 : Interval s3Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_288 : Interval s3Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_320 : Interval s3Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_352 : Interval s3Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_384 : Interval s3Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_416 : Interval s3Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_448 : Interval s3Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_480 : Interval s3Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_512 : Interval s3Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_544 : Interval s3Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_576 : Interval s3Atlas 3 576 11 := block_range (n:=11) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 587 := (concat (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 (concat bs3_3_224 bs3_3_256)))) (concat (concat (concat bs3_3_288 bs3_3_320) (concat bs3_3_352 (concat bs3_3_384 bs3_3_416))) (concat (concat bs3_3_448 bs3_3_480) (concat bs3_3_512 (concat bs3_3_544 bs3_3_576)))))
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
theorem bs3_4_1312 : Interval s3Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1344 : Interval s3Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1376 : Interval s3Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1408 : Interval s3Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1440 : Interval s3Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1472 : Interval s3Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1504 : Interval s3Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1536 : Interval s3Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1568 : Interval s3Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1600 : Interval s3Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1632 : Interval s3Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1664 : Interval s3Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1696 : Interval s3Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1728 : Interval s3Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1760 : Interval s3Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1792 : Interval s3Atlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1824 : Interval s3Atlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1856 : Interval s3Atlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1888 : Interval s3Atlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1920 : Interval s3Atlas 4 1920 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1930 := (concat (concat (concat (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat (concat bs3_4_96 bs3_4_128) (concat bs3_4_160 bs3_4_192))) (concat (concat (concat bs3_4_224 bs3_4_256) (concat bs3_4_288 bs3_4_320)) (concat (concat bs3_4_352 bs3_4_384) (concat bs3_4_416 bs3_4_448)))) (concat (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat (concat bs3_4_576 bs3_4_608) (concat bs3_4_640 bs3_4_672))) (concat (concat (concat bs3_4_704 bs3_4_736) (concat bs3_4_768 bs3_4_800)) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 bs3_4_928))))) (concat (concat (concat (concat bs3_4_960 (concat bs3_4_992 bs3_4_1024)) (concat (concat bs3_4_1056 bs3_4_1088) (concat bs3_4_1120 bs3_4_1152))) (concat (concat (concat bs3_4_1184 bs3_4_1216) (concat bs3_4_1248 bs3_4_1280)) (concat (concat bs3_4_1312 bs3_4_1344) (concat bs3_4_1376 bs3_4_1408)))) (concat (concat (concat (concat bs3_4_1440 bs3_4_1472) (concat bs3_4_1504 bs3_4_1536)) (concat (concat bs3_4_1568 bs3_4_1600) (concat bs3_4_1632 bs3_4_1664))) (concat (concat (concat bs3_4_1696 bs3_4_1728) (concat bs3_4_1760 bs3_4_1792)) (concat (concat bs3_4_1824 bs3_4_1856) (concat bs3_4_1888 bs3_4_1920))))))
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
theorem bs3_5_864 : Interval s3Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_896 : Interval s3Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_928 : Interval s3Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_960 : Interval s3Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_992 : Interval s3Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_1024 : Interval s3Atlas 5 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_1056 : Interval s3Atlas 5 1056 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1074 := (concat (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 bs3_5_96)) (concat (concat bs3_5_128 bs3_5_160) (concat bs3_5_192 bs3_5_224))) (concat (concat (concat bs3_5_256 bs3_5_288) (concat bs3_5_320 bs3_5_352)) (concat (concat bs3_5_384 bs3_5_416) (concat bs3_5_448 (concat bs3_5_480 bs3_5_512))))) (concat (concat (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640)) (concat (concat bs3_5_672 bs3_5_704) (concat bs3_5_736 bs3_5_768))) (concat (concat (concat bs3_5_800 bs3_5_832) (concat bs3_5_864 bs3_5_896)) (concat (concat bs3_5_928 bs3_5_960) (concat bs3_5_992 (concat bs3_5_1024 bs3_5_1056))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 48 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 43 := (concat bs4_2_0 bs4_2_32)
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
theorem bs4_3_256 : Interval s4Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_288 : Interval s4Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_320 : Interval s4Atlas 3 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_352 : Interval s4Atlas 3 352 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 377 := (concat (concat (concat bs4_3_0 (concat bs4_3_32 bs4_3_64)) (concat bs4_3_96 (concat bs4_3_128 bs4_3_160))) (concat (concat bs4_3_192 (concat bs4_3_224 bs4_3_256)) (concat bs4_3_288 (concat bs4_3_320 bs4_3_352))))
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
theorem bs4_4_1344 : Interval s4Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1376 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992)))) (concat (concat (concat bs4_4_1024 bs4_4_1056) (concat bs4_4_1088 (concat bs4_4_1120 bs4_4_1152))) (concat (concat bs4_4_1184 (concat bs4_4_1216 bs4_4_1248)) (concat bs4_4_1280 (concat bs4_4_1312 bs4_4_1344))))))
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
theorem bs4_5_864 : Interval s4Atlas 5 864 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 884 := (concat (concat (concat (concat bs4_5_0 (concat bs4_5_32 bs4_5_64)) (concat (concat bs4_5_96 bs4_5_128) (concat bs4_5_160 bs4_5_192))) (concat (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)) (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 bs4_5_416)))) (concat (concat (concat bs4_5_448 (concat bs4_5_480 bs4_5_512)) (concat (concat bs4_5_544 bs4_5_576) (concat bs4_5_608 bs4_5_640))) (concat (concat bs4_5_672 (concat bs4_5_704 bs4_5_736)) (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_32 : Interval s5Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_64 : Interval s5Atlas 2 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 90 := (concat bs5_2_0 (concat bs5_2_32 bs5_2_64))
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
theorem bs5_3_352 : Interval s5Atlas 3 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_384 : Interval s5Atlas 3 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_416 : Interval s5Atlas 3 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_448 : Interval s5Atlas 3 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_480 : Interval s5Atlas 3 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_512 : Interval s5Atlas 3 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_544 : Interval s5Atlas 3 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_576 : Interval s5Atlas 3 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_608 : Interval s5Atlas 3 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_640 : Interval s5Atlas 3 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_672 : Interval s5Atlas 3 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_704 : Interval s5Atlas 3 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_736 : Interval s5Atlas 3 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_768 : Interval s5Atlas 3 768 31 := block_range (n:=31) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 799 := (concat (concat (concat (concat bs5_3_0 (concat bs5_3_32 bs5_3_64)) (concat bs5_3_96 (concat bs5_3_128 bs5_3_160))) (concat (concat bs5_3_192 (concat bs5_3_224 bs5_3_256)) (concat bs5_3_288 (concat bs5_3_320 bs5_3_352)))) (concat (concat (concat bs5_3_384 (concat bs5_3_416 bs5_3_448)) (concat bs5_3_480 (concat bs5_3_512 bs5_3_544))) (concat (concat bs5_3_576 (concat bs5_3_608 bs5_3_640)) (concat (concat bs5_3_672 bs5_3_704) (concat bs5_3_736 bs5_3_768)))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1376 : Interval s5Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1408 : Interval s5Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1440 : Interval s5Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1472 : Interval s5Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1504 : Interval s5Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1536 : Interval s5Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1568 : Interval s5Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1600 : Interval s5Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1632 : Interval s5Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1664 : Interval s5Atlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1696 : Interval s5Atlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1728 : Interval s5Atlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1760 : Interval s5Atlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1792 : Interval s5Atlas 4 1792 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1806 := (concat (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)) (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 bs5_4_416)))) (concat (concat (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)) (concat (concat bs5_4_544 bs5_4_576) (concat bs5_4_608 bs5_4_640))) (concat (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)) (concat (concat bs5_4_768 bs5_4_800) (concat bs5_4_832 bs5_4_864))))) (concat (concat (concat (concat bs5_4_896 (concat bs5_4_928 bs5_4_960)) (concat (concat bs5_4_992 bs5_4_1024) (concat bs5_4_1056 bs5_4_1088))) (concat (concat bs5_4_1120 (concat bs5_4_1152 bs5_4_1184)) (concat (concat bs5_4_1216 bs5_4_1248) (concat bs5_4_1280 bs5_4_1312)))) (concat (concat (concat bs5_4_1344 (concat bs5_4_1376 bs5_4_1408)) (concat (concat bs5_4_1440 bs5_4_1472) (concat bs5_4_1504 bs5_4_1536))) (concat (concat (concat bs5_4_1568 bs5_4_1600) (concat bs5_4_1632 bs5_4_1664)) (concat (concat bs5_4_1696 bs5_4_1728) (concat bs5_4_1760 bs5_4_1792))))))
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
theorem bs5_5_864 : Interval s5Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_896 : Interval s5Atlas 5 896 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 909 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat (concat bs5_5_96 bs5_5_128) (concat bs5_5_160 bs5_5_192))) (concat (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)) (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 bs5_5_416)))) (concat (concat (concat bs5_5_448 (concat bs5_5_480 bs5_5_512)) (concat (concat bs5_5_544 bs5_5_576) (concat bs5_5_608 bs5_5_640))) (concat (concat (concat bs5_5_672 bs5_5_704) (concat bs5_5_736 bs5_5_768)) (concat (concat bs5_5_800 bs5_5_832) (concat bs5_5_864 bs5_5_896)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 45 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 30 := bgb_3_0
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
theorem bgb_4_224 : Interval gbAtlas 4 224 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 230 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_992 : Interval gbAtlas 5 992 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1011 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992)))))
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
theorem bgb_6_1024 : Interval gbAtlas 6 1024 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1054 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))))))
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
theorem bgb_7_448 : Interval gbAtlas 7 448 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 472 := (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffefefeeefffeffeafefefeeafffffffffefefeecfffeffeafefefee8fffffffffefefeeefffeffeafefefeeafffffffffefefeecfffeffeafefefee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,2,66),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_33394.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[4,8]⟩,⟨.or,[3,9]⟩,⟨.or,[7,2]⟩,⟨.or,[6,5]⟩,⟨.or,[0,11]⟩,⟨.and,[8,4]⟩,⟨.and,[9,6]⟩,⟨.and,[12,13]⟩,⟨.and,[7,10]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_33394

open PEqualNP.Outside.L_meta_33394 in
theorem PEqualNP.Outside.L_meta_33394 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
