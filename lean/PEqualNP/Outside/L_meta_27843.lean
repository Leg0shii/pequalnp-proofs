import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27843.Model
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


end PEqualNP.Outside.L_meta_27843.Model

namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
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

end PEqualNP.Outside.L_meta_27843

namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2f1a000163c302005a00c003805580445c02c489c7003e0089a5c0c0280c644825498a8b3aa4907408d0900a3c0134a28a083600e5102d800000008c0c5080ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x807e003f96c0000000000022001e8867e00000c2563003c000b000c000013298c007d2714462003c0005c820000052640017c000000000003a251502c4400000bc6c028b4a63e11988ce6b2081c0004391d4f61300160da66278000012000ac007713000b41f418007a4d00094ae2a048643618211d8141a0f0d400153a0c80052398d0001d019a80000030a04e841c0d80000231a4181c38800dc00199704200001e4b211002006e002492000551c9002e50379c10c14000090a0e000001a0000000007c40800482c1d8010e0000000782f001a0984b2291c000004040ba000707010c000a0009000201010000030301000100020301020005010304060600040600000511000b0001000cb7294876d5290e7ca721eb94a43d6a94873d5190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010e7aa021ee540439ca80875e5390abaa7216710f329f2a4653d548cb5ca9196b55232b6a9c65ae438cb5887194fd51329e2a2659c434cb5ea8996b15132e7a9a65cf434cb5c86996b10d32e621a658c434cadca4194f94f41d719683ad32d067aa1a0cf552419e29a83ae325075a64a0edd45419fa82833e541067ea998cf15331b7296636d52cc79a6598cf952319eaa463b5418c67ea898cf15131e699263b5414c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d548867ca810cf55021af298435d53086f4a010de540219f29e81ae32d035a65a04f547409eaa4813c535035c64a06b4c9409fa8a81bb505027ca8204fd53309e2a6616e52cc2daa598734cb309f2a4613d548c37281184fd51309e2a261cd324c37280984f950309eaa0616e520c2daa4185d94430baa88613e548827aa9104f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa8885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x3200b8000800263a00083208802d4e01180000142e60009910cbc70018155b10e255245894d9f3408c1e1610a8f1070a124234b291402640204e086183385180040a358a5310f265254443c95495110f315194043ca9495010f295254043cc9455010f315154043a558443cca996010f32a9584438caa96010e32a5584434ca996010d32a3993534ca2e6590d32a398e434ca2e6510d32a9584434caa96010d32b1584434cac96010d32a3994434cb0e6510d32e1984434ca8d6110d32e1584434ca856110d32e2980434ca8d6010d32e2580434ca896010d328e580535070c534c9418e58054cc70c544cb31c3151324c6346550531e14c9414c6356114d40c314d32502356115330c315132cc30c544c9308e195404c38932501308718d544424d6314910d454d10043615244010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x20440398a040c065a05866010d32d04c2b00869968161580434ca84b80a699283425c0544cb31c08ca9928298d057114d3250282b88a899661821953250130
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
  | 4 => packedAt s0K4 (4032+((h/45+packedAt s0K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s0K3 (1996+((h/16+packedAt s0K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s0K2 (453+((h/3+packedAt s0K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1e1e3c7fc7f1fe3f1c63838fe3f1f87f10f4cf
  | 2 => 0x1fe03f8ff8fe3fc7e07c03f1fc7e3f87233b33
  | 3 => 0xe0003ff3ff003ff8ff8003fe3f803ff8c3cc3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x42804600424208400820908240910822105045
  | 2 => 0x84088840908050084044211084281204212112
  | 3 => 0x15511292424a401b4804a242904a550c28c28
  | 4 => 0x8440122002004922509080032448110440e80
  | 5 => 0xd198224836c93924da7273c900090666bbf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcc0fcfcfcc0fffffcc0fcfcfcc0fffffcc0fcfcfcc0fffffcc0fcfcfcc0fffffcc0fcfcfcc0fffffcc0fcfcfcc0fffffcc0fcfcfcc0fffffcc0fcfcfcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x30007802400000460098036000000000a8a521800000411243a9c0003e08400000158000000010011080005cd001c0018050000000001280160060500a8000001c0000058e003c00026004400d0050020000000012640008002002000608000000c000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x18300008ac00014c000028006c8878fc0048000000903444c858000d4464009964f931540070cc00840000113400003c55388c0159153c40000148015c0000c40000dc0100000000f4391c040000c000145168007401205d50bd4068d52908006000d8004d601cb4e0b87c24b0ecd0a8a02c20e89d24f0a4000095190d2c011000800104e4000a001c0220040a2e0c12001a02001e0e000804000210040e021c0006113e5390e7aa321db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010f72a021d794e42aea9c859c43ccaf4a1995e543329f2a4653d548ca7ea8994f15132ce21a653e53d067aa920d7d4d41ae29a839f5350678a6a0e714d418e29a83b7515067ca820cfd53319e2a6633e548c67aa918e710e31daa0c633f544c678a898ed505319f2a0633d540c7388618db94831b6a90637a500c6f2a018cf952219eaa4437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30b7296616d52cc27ca9184f552309faa2613c544c33886984f950209eaa0415e53082baa6105d94420baa8841e9200827ca9884f55310b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2e51a2241a6030020b0439240c000a0a62a71609e00088c30488c237265254443c95495110f315194043ca5495010f315154043a558443ccb184354332a5584434cb0e6214d41c358853507156114d41c698053507196014d41a5584438c69463506318d195414c61d6510c31c310d520c71843540318718d54886956110f30c310d52cc2956110d30d8545200821c6355310
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x40c0010801445c44354332c0ac4b08a6a0e09625805350708b0ac029a83415c44354b30
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
  | 4 => packedAt s1K4 (2697+((h/30+packedAt s1K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s1K3 (990+((h/8+packedAt s1K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x78f1ffc3f8fc7e3c71c0e3fc7e1c3fe30f70f
  | 2 => 0xf80fe1ffc7fff8fc07e00fc7f8fffc1e4339f3
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x50118484921288014304a2094124414c305305
  | 2 => 0x2221009040401080421044208509010412052
  | 3 => 0xa5444912212900368802489092092a81828c28
  | 4 => 0x31004ca081019244d1486000e48c08c4940f80
  | 5 => 0xc6089103364e249b26938f24001033196bf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0fffffaa0faf0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x2018f0056000153071381002cb02320000052006054624b8f1a849130e000000000026140018000000000000e800044fa210000000094004540001a0050da050907008206001800030202000c184ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x580e0056003a441d00010b36003e131c4700092c1145412e0c0d22571e1a494c2a0023543702081251433d354d17001b293128331021003f204b345052030f2f262b0607194e593b0053000a00165a0042152d463c4f040000001f0000273855304a052514183932402448000001060d1030a20580001030d0000200000003e003848508c488d073e5390e7aa321db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010f72a021d794e42aea9c859c43ccaf4a1995e543329f2a4653d548ca7ea8994f15132ce21a653e53d067aa920d7d4d41ae29a839f5350678a6a0e714d418e29a83b7515067ca820cfd53319e2a6633e548c67aa918e710e31daa0c633f544c678a898ed505319f2a0633d540c7388618db94831b6a90637a500c6f2a018cf952219eaa4437b50486f0a090cf950219eaa0435e53086baa610de94021bca80435e53902baa7206710f30b7296616d52cc27ca9184f552309faa2613c544c33886984f950209eaa0415e53082baa6105d94420baa8841e9200827ca9884f55310b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x61a380792b04aa6c0000082851c5822a400c89002e00818a3180e6a13265254443c95495110f315194043ca5495010f315154043a558443ccb184354332a5584434cb0e6214d41c358853507156114d41c698053507196014d41a5584438c69463506318d195414c61d6510c31c310d520c71843540318718d54886956110f30c310d52cc2956110d30d8545200821c6355310
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x1000048c01445c44354332c0ac4b08a6a0e09625805350708b0ac029a83415c44354b30
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 4 => packedAt s2K4 (2667+((h/30+packedAt s2K4 (2457+(h % 30)*7) 7) % 110)*8) 8
  | 3 => packedAt s2K3 (990+((h/8+packedAt s2K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s2K2 (249+((h/1+packedAt s2K2 (245+(h % 1)*4) 4) % 9)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x78f1ffc3f8fc7e3c71c0e3fc7e1c3fe30f70f
  | 1 => 0xf80fe1ffc7fff8fc07e00fc7f8fffc1e4339f3
  | 3 => 0xffe3ff80fff1ff8000ff8ff01ffe183ce3c
  | 4 => 0xfff0003ffff0001ffffff000fffe0001fc0fc0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x50118484921288014304a2094124414c305305
  | 1 => 0x2221009040401080421044208509010412052
  | 3 => 0xa5444912212900368802489092092a81828c28
  | 4 => 0x31004ca081019244d1486000e48c08c4940f80
  | 5 => 0xc6089103364e249b26938f24001033196bf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88ffffee88eeccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x485d49e207571600600a55e80d8f043489a105150a446460012a000b38b439258000033e10a800aad323424d3801c000000c00000137200d2162c5082005ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x291602ca80035820001f2f0785a5b2b1f0380d00000020643090443d3000088000000000402c9402284419dc00250184d005c0014cae363e800e24742924fc142a92cda7b2184860701f88000370798ca44d3119c4c38138f020733313c145a159fcf4092405cbe4235128c82e00060543501075023b3c21cde6e0b0e4502f071748c5130800f200000000000260d0e40700000341b000000a3a022080033348c4ea00000840000340648a323b08c9c652c1d02a41360f818100f0d09093504000320000015110004342300030201001200040c380019090400030b0002160006030b041300bd28487795090e7ca721cf54a439ea8c87ba5090f72a121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed944439ea8887b55110e6aa221ee94043dca80873e53d0a7aa3a14f552429e29a85af5250a7ea2a14f950429faa6653c54ccaf4a1995e543329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e540329f29e833d52d067aa920cf14d419fa9283b7515067ca820cfd53319e2a6637a50cc6f2a198cf952319eaa463b5418c67ea898cf15131daa0a633e540c67aa818db94831b6a90637a500c6f2a018cf953219eaa6433e548867aa910cf951219eaa2437b50486f0a090cf950219eaa0435e53086baa610f948421bd280437950086bca7205754e40ce21e613e548c27aa9186e95230dcaa46179538c37487186e10e30dda1461b9428c37683186e506309faa2613c544c33886986ed5130dc2a261db534c3b686986e90d30dc21a61d8434c33086986ed0930dca1261db324c3b264986ed0530dca0a61db314c3b262985e940309f2a6413d54c827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1030c050e00989003490a460180062000192a017ae480912922a8316585d5835a9ce203c7d29d346c09420005a81c3c20042000004c1000c034000c84000a3c604fa65825310f255294443c99495110f255254443ca54a5010f315194043ca5495010f3151540438d5845350a3561153328b195424ca2d6214d418b58854cc63465505318718d54486596314121d154d21087612154021a358843cc2956110f30aa588438c2b16110e30a3588434c2956110d30a6993534c23a6590d30a698e434c23a6510d30aa588434c2b16110d30b2588434c2d16110d30a6994434c31a6510d30e2988434c2996210d30e2588434c2896210d30e4984434c2996110d30e4584434c2916110d30a618d424c29864cc930a6191324c389424c930a618d414c29864cc530a6191314c391414c530
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x50206020440398065a058a6110d30d04c4b08869868162584434c248b88c6a1261245c464cc930910eca1264984897218d414c244b90c998a61241d9414c530
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
  | 3 => packedAt s3K3 (1996+((h/16+packedAt s3K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf0e3cffc38e3e3f38e3838fe38e38ff30f90f
  | 1 => 0xff03f1ffc0fffc7c0fc03f1fc0fff0f4331f3
  | 2 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6160464849144c401860988260a28866305905
  | 1 => 0x82048880902810084084211084051208412052
  | 2 => 0x8910112200a001a100422409402480828228
  | 4 => 0x2420004a080004920a29080032288022140d80
  | 5 => 0xc8cc2290334d3924f4d273c9004106ccebf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8ffffe8e8fcfce8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
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
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x367802a1e98c23004008e0058000267c58d34001064a009281210a29481ce15229d08a0a2158040011002e74c8c0604000608301f04d240480ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe61bf40cc3f481986f50330fca0661b940cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7186fd0e30ef21c61bd438c3ba87186750e30bf294617d528c2fca3185f54630bf28461bf408c37a811877cc230fd984617f544c2fca8986f951309f2a2617d544c37aa8984f55130be2a261bf434c37a86985fd4930be29261df324c3ba64985fd4530be28a61df314c3ba62986fd0130dea0261fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30dfa1861de430c37a86187750c30cea18617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c37e80187e90030dea0061f9400c372801877cc030fd18061dd300c3f26018764c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20dfa1e41bd43c83dc65907b4cb20bf28e417d51c83de43907b48720dfa0641bd40c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c538837e87106f50e20bea94417e51882faa3105f94220dfa0441fa408837a81107e50220dca0441fa30883f261107bc8220fd904417f54482fca8905f55120be2a2417f53482fca6905f54d20be29a41bf434837a86907b8c920f6992417f51482f8a2907bc8520f690a41bf40483f480906f50120fca0241b940483f460907e4c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c530837e86106f50c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020dfa0041bd40083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c437e87886f50f10bfa96217e52c42faa5885f14b10fb18e21f531c43ec43887d48710dfa0621bd40c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c538437e87086f50e10bfa94217e52842faa5085f14a10bea8c217e508437e81087e90210dea0421f9408437281087e8c210fc98421fa20843f241087dc4210fd884217f54442fca8885f55110be2a2217f53442fca6885f54d10be29a21bf434437a86885fd4910bf292217d52442f8a4887d8c510fa98a21f621443ea42886fd0110fd20221bd40443f280886e50110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437e86086f50c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xd43cc7ba8798e750f31bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718efd0e31dea1c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131dfa1a63de434c77a8698f750d31cea1a637f524c6f8a498f7cc931ee99263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77e8618ef50c31bf29063ee520c6dca418df54831f6a90636d520c6fca218f7cc431fb18863dd310c7ea6218df94031fd280637a500c6faa018fe54031bca80637f54c86fca990df55321be2a6437f53c86fca790df54f21be29e43bf43c877a8790fb90b21f6a1643ee32c87da6590df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c43bf438877a8710df54a21bf28c43f641887ea8310fd8c621fa98c43ef21887ee4310df94221bea84437f544877ea890cfd5121bf2a2437d54486f8a890ef151219e2a2437f53486fca690df54d21be29a43bf434877a8690fb90921f6a1243ee32487da6490fd90521faa0a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610efd0c21dea18437e52086fca210fbc8421fb10843ed21087ea4210f948421bf28043fa50086f4a010df54021fca80437950086fca7a07794f40af29e817d53d03baa7a05754f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d033ca7a06f54f409ea9e819d53d023aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d037aa3a06f14740df98e81be31d037a63a06f0c740df90e81be21d037a43a06f08740beaa4813d54902fca7205f54e40dfa1c81bd43902fca5205f54a40bf28c817d51902fca1206fd0240fda04817f53502f8a6a06fd0d40df21a81bd435037886a05fd4940be29281bf425037c84a06f50940de212817f51502f8a2a06fd0540df20a81bd415037882a07ed0140df20281bf535027ea6a06f94d40dea9a81bc535037ea4a06f94940dea9281bc525037e64a06f8c940de99281bc325037ea2a06f94540dea8a81bc515037e62a06f8c540de98a81bc315037e42a06f88540de90a81bc215037ea0a06ed4140bf2a0813e54102fca6205f54c40dfa1881bd43102fca4205f54840bf288817d51102fca0206fd0040fd20081bd40103f280205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a9986fd0f30dea1e617e52cc2faa59877ccb30ee996617e51cc2faa39877cc730ee98
  | 2 => 0x600000004000000008070000180100000200c0000404802c0500403e00002002022004000040020000380800200801801004000020000060380200301800c000020000100080000000c010040000000000200000800816bf296877d52d0efca3a1df54743bf28687fa50d0ef4a1a1df54343fca86877950d0f7ea5a1ef94b43dea9687bc52d0f7ea3a1ef94743dea8e87bc51d0f7ea1a1ef94343dd28687bd50d0e7aa1a1ee543439ca8687bc50d0efaa921cf55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be28287bf5350f3ea6a1efd4943df29287bd5250f78a4a1efd4543df28a87bd5150f78a2a1efd41439fa8287be5050f7aa0a1ef14143bf2a0873e5410efca621efd0c43ef21887bd4310fba8621df94843bea90877e5110efaa221df94043bea80877e53d0afaa7a16fd0f42dea1e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42dfa1c85bd4390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42dea1a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf29885de5310abca6215f54c42eea98855d5310b7e86216f50c42bf29085bf4210bdc84216f50842f6a10857e5110beca2215d94442bea8885f55110aeaa2215f94042fd280857a5010afaa0217e54042bca80857f54ccafca9996f953329f2a6657d54ccb7aa9994f55332be2a665bf43ccbbc87996f50f32eea1e659d43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7196fd0e32dea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132dfa1a65de434cb7a86997750d32cea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32dfa1865bd430cafca41977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41dfa1c83bd43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077e8620ef50c41bf29083ee52106dca420df54841f6a90836d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50107f4a020de94041bea8083f950106f2a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998efd0f31ef21e63b
  | 3 => 0x2fa00000000000001500002b83b40000011a2605a1ea00010597b6060e0010280009c00000000336400000003b63f80011e000198dc85d000cc4002332e04b9429ba00070c588d0400b7c000006cadbd14019084aa0e58004b4bfc000003ee0007e80027c0013faf323661c7528a4247999502740407c8a2ab000000d528d4941f98888f64e8d4002e648c0680031859e625778000000000021d1ca934a29462b66c80200003c7240109a4b0c7c6d9ca51e0004a355000658000000001b4002b341c59d592dd0ce0000006937e620e697b5cea211698a5e8bc52a83d42e5c52a0364485d1ad8ad26c6b18195e3565f0101a71ae000000ce43041c598d6296d2c1db5c31601d20853000c846c1ed0740000aa8b49800128000146001a923c0640018aa7b000210ee3516d4001258ac4eccf53184020212ced1311e64c924a7a44a4bcfaaed000c49b59733aa60440000000014000ee000b143997800000000000044000e9812000001653103800000000022e000000000001b11c000000000f20000006d80000029c7a44d8000005a400000000000db8004c0001359af3e6464c10a93307417032d5f82f4758000000000013d588000000000000008fa36224000002c9000001b322e4dc000bf0e60000008214f0000000020111230d0185b22a619609fe1149c8b905426ac5d088084525244e1ae4b6b096f13f088a490e0000000018cb4500027d668000e02300031c000d8c002e10000000e1520000017eb72056c9932818000c7961b3f000415a502150c278a18006ced047baf52c406c859330f6dc1a71760d000000000546000b71e75aa2996322c00000000267050381a617a426898eea7e000000610fa6680000012910cb940029006a0008800000000172000046615211d62101452794a0000000001d0008582c27d24c2f06e80028e459031b3226bb0148000f8b700017f1882ec3700e0003c4631576ae018a080002b0000240c81406e0000000400200000801002008000000040000280b00400001000002000008010040080280d0080080100000002003803000018008000000040080201200000000000010000070040040000100000402801014010028000020080300300a0000001900200c0080000200400000010004038030000140000200e0080000100c0100000401a0080100200400c03800000010000000000080780000a004000000000000000301a014008000000000000400a004000050000000000a004008000030180400000001800000800000014010110000200300d0080000000600200c03801000008000000200000300a006020018000000040180000a00c00800016000010000000000000000a0100080c00404002014030000008070080380480000a0000280a0020000980a000004008080040140000
  | 4 => 0xde0000015cab50000009436916cbb8428000006c4002740068c0000dc2a0c94868000006a4b305523800000076000979b62ea5327c56900036a6e0650005f600124000214bd8000000000040027953e0004a8000000009c0000000018584f4640012c9020005b1418000000008e953000001a1800000af0908002603b0000000000005721e416c04638004080007a000680670d01914182a11a000000000002d848a0000034f000b380000028081c058000000cc002f738c0014d80029a000000482d6001a233a000000e2abe000550d32b61f8720aa8141d2c209398400000051273000afc00000000274af8003ae000000773c6779a823f21e169b091a0000c5532a135acb8ad045026000389751a22e4c68b7580a58499a44e0cc9299640ea178280000a400138b20652a91588004f80001f03f000558e3a15508988002db51817050111480000000000f0000558c808c00052a82000000001d1054000000001e400000000022560001fd000b6563800284601ad00000067496872636a70c71e16ac990b28cb31ea74000b5218b4d0a079576ab06f9991800f1b400066c7381a2d017cb44252e819200091197254000000740aec689bb1400042406a5f46e194001b0246ced56b64198dcc871950d4cd5719594d4c342f887000000001fb0fa000000003204184cb2266e05c2cada018cb0002cb67c4aca893404cdc40016a000bac0026d45e000002610585749db4824ac00002b70debe182a873242c80b0d31b2000a20000002fc0000061e7b94d000000b20000004d00000000012c189108003be239afacc0003851531d000000000a100000000090440d50000005447c0f29e00000017c800000a95498c105e2906a9eb15edb40000055267c000003a87a00000a12e000e0800488249b70b83d839c000000480007b0000ac000003471de7495a23b3260019980009a348fd21b00000004800000aa8582750003149021a04a1807ca276a6389068643f07e4fa20a08e8f4000006c4710002fa2f220c1b9cf248001a116d1f0040001cc000840f10f005a001110005120012bb130002440029147c2092e160474001048383fea399434d1f67d99c8004a4000538616b0000a4000000001a30004f060d1c80057493800177530bc000000612ba5331030001316a281000c300002e4eea78000000009759e000000000002af0008c592000298ae0003590007f09d000000000b0b02560000002d70000007f8005fca9c6799e3284b021aae37c9bd219a562c125821b43e42e94000001e3d472163110c28d4000000b892b2d62784615e8e860c1acb4000000000cd208656a5c3f9390007080021f4d218c0025100035000000116001118000000018707a0000012380000000000338000d25158001026f0668003445bd91a6c060000001d95e4000de9a3
  | 5 => 0x2a800000432d75079bb52a7bd981d8318684000000000e4000da52838daf0
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc54c425d63153109b98854c426d62153108f99253c423d6494f108f99053c423d6414f109b98853c426d6214f10ae58343c431e5350f10c754d43c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c4395434c710d914921c429d63d03109798e548425d6395210a758e548431e63952108f58e548431d63952108758e548433a60952108fd8d548423e64d4e108f593538423e6494e108f592538423e6414e108f590538426e6214e109b588538423f65d0e108f59743842b960d0e108fd95438423d6550e10c7d4d438431c5350e108f993528423d64d4a108f990528423d6414a109798c528425d6314a10a758f408433a5450210aed95408433b6550210aed8d408433a5350210ce14d408433b5250210ce54940842b9648c210e650e30842b9644c210d614d30842b96488210ce552208433954482109798e544425d63951108f992534423d6494d108f990534423d6414d109b988534426d6214d10ae583434431f5350d10c714d434423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c5244274654c510e550d31442746548510d9149214429d63d0110ae59240442786550110bc185404433b6550110ce19540442bb6350110ce94d40443385350110ced4940443395250110ecd8540443b06150110ec8c540443b13150110ec88540443b12150110ae5923044399438c1109e19530442b9644c110d614d30443d1314c110ae59220442786548110f848520443b140841109798f540425d63d50109b98b540426d62d50108f596540423d63950108fd8d540423f60550108f581540423e64150109798c540425d63150109b988540426d62150109e980540423e64d4c108f593530426e62d4c109b58b530423e6494c108f592530425d6594c10c7952530431d5494c10c7992530431d6494c10c7951530431d5454c10c7991530431d6454c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423f65d0c108f597430431e53d0c10c754f43042b960d0c108fd95430423d6550c10c794d430431d5350c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432f4394810cb50e520432e5454810cb551520434e5354810d354d520432f4354810cb50d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108f992500423d64940108f597400429d63d0010c794f400431d53d0010cb94b400432d52d00108fd95400431e5350010c754d400432e5250010cb549400433a5050010d554f100436552c40109e59610043395484010d654e100436952840109dd9510043555344010d954910043b340440109ed9510043395444010d654d10043695244010
  | 1 => 0xc29d64cc030d354b300c35551cc030e6503300c2b9648c030b658e300c399438c030da54a300c371518c03097d95300c29d644c030d3549300c355514c030e6d01300c399404c0309ed95300c2b9644c030e6d0d300c399434c030da549300c371514c030b6d95300c35b654c030b6d91300c39a644c030b6591300c399644c030a6591300c39a544c030e6551300c3ca524c030d6549300c3c9524c030d2549300c3d2514c030d6545300c3d1514c030d4545300c25e63153209758c54c827661153209d58454c823e6494f208f59253c823e6414f208f59053c82766114f209d58453c82b960d0f20c794d43c831d5350f20e350d32c823f64547208f19151c829d63d03209798e548825d6395220a758e548831e63952208f58e548831d63952208758e548833a60952208fd8d548823e64d4e208f593538823e6494e208f592538823e6414e208f59053882766114e209d584538823f65d0e208f59743882b960d0e208fd95438823d6550e20c7d4d438831c5350e20a758f408833a5450220aed95408833b6550220aed8d408833a5350220ce14d40883395150220ae5923088399438c220ae5913088358534c2209798e544825d63951208f992534823d6494d208f990534823d6414d209d98453482756114d20ae583434831f5350d20c714d434826c654c920e350d324823e64145208f590514825e63145209758c51483645148520a758f40482b964901209e19540482e86250120ced9540483386550120aed8d404833a5350120ce14d40483ab6250120ea18940483aa3250120ea4c9404833b5150120eac8540483a92150120ae5923048399438c1209e19530482b9644c120d614d30483c9324c120ea502204825e63d50209758f540827661d50209d587540823d65950208f58e540823f63550208f990540825e63150209758c540827661150209d584540827a60150208f993530823d64d4c209d987530827561d4c208f992530823d6494c2097596530831e5494c20c7552530831e6494c20c7592530831e5454c20c7551530831e6454c20c7591530823e6414c208f590530825e6314c209b98853082766114c209d584530827a6014c208fd97430823d65d0c20c794f430831d53d0c20ae583430823f6550c208f595430831e5350c20c754d43083365494420cd55251083565394420d554e51083374394420cd50e51083365454420cd55151083565354420d554d51083374354420cd50d510823e64940208f592500823d65d0020a758f400831e53d0020c754f400833651d0020cd547400823f6550020c794d400831d5350020cd94540083355150020ce941400834d53c8020d954720083395488020d654e200837151880209bd95200834d5348020d954520083ab40480209ed9520083395448020d654d200837151480209798
  | 2 => 0x6314540ab98851502ad62145408f997315023d65cc540ae98231502b9608c540aed8131502b8604c5408f994315023d650c540ab98831502ad620c540ae98031502b9600c540ae98321502b960c8540ae98221502b960885408fd95215023c65485408f994215023d6508540a798c215029d6308540e948421502ba6008540ae580215029e63d4140a758f50502ba63d4140e698f505029a63d4140e658f50502b962d4140ae587505031e6395040c758e541031d53d0c40ae583431023f6550c40a758f401023f65500409ed95401033a5450040ce58254cc31d54ccb30c755132cc31d54cc730c755131cc29d63d0330ce95240cc29f6350330aed9540cc33b6550330ce19540cc2bb6350330e6d8d40cc3986350330ce54940cc39b3250330e64c940cc3395150330e6cc540cc3993150330c758e548c2b960d0e30c7952438c2bb6050e30c7d95438c31c6550e30a7d81438c39b6050e30e6181438c31d4354a30c750d518c29d63d0230a7593308c33954cc2309758e544c27960951308f58e544c31d63951308758e544c23d6095130ce582544c23960951308fd8d544c31f63551308fd81544c33b6055130ae583434c2bb6050d308f993524c23d64d49308f990524c23d64149309d984524c2756114930c7553324c31d544c930b6181324c23e64d45308f593514c23e64145308f590514c26e62145309b588514c31d54cc530c7551314c2d8604c530a758f404c23f65501308f595404c29f6350130ce553304c31d548c1309b98b540c26d62d50309d987540c27561d50308f596540c31e6395030ce982540c23f63550308f58d540c23e64150309b988540c26d62150309d984540c27561150308f992530c23d6494c308f597430c2b960d0c3097596430c29d6490c30b6582430c23f6550c30c7951430c29f6550c30c7d95430c29f6050c30e6981430c3996050c30cb952520c32d5494830e350e520c32f4394830cb50e520c31d4354830cb951520c32d5454830e350d520c32f4354830d390d520c32d4354830d350d520c30d4354830cd952510c3355494430e550e510c3665294430d954a510c3374394430cd50e510c31d4354430cd951510c3355454430e550d510c3665254430d9549510c3374354430d590d510c3354354430d550d510c31543544308f992500c23d6494030c750e500c23d65d0030a758f400c32e52d0030cb54b400c33651d0030cd547400c2796590030ae592400c2d96390030e650e400c3695290030dc546400c23f6550030cb949400c32d5250030cd945400c3355150030ce951400c39a4350030e650d400c3695250030dc545400c2bb6550030ced95400c2bb6350030e698d400c3996350030ce94d400c3aa5250030ce549400c3a95250030ca549400c3b25150030ce545400c3b15150030cc545400
  | 3 => 0xc219e98053086796014c218fd97430863d65d0c21c794f430871d53d0c21ae583430863f6550c218f595430871e5350c21c754d430872d54c8421d354f21087355488421d554e21086e562884219bd95210872d5448421d354d21086776548421cd55121087555348421b9d9521087676548421e9d9121087a46448421d9d5121087a65448421d955121087a55448421c955121087675348421f194d21087655348421f154d21087455348421e9d0d21087a543484218f992500863d6494021ce95250087395494021d694e50087595394021f8486500873a6494021ce592500873b4394021ce50e50087652154021ce95150087395454021d694d50087595354021f8485500873a6454021ce591500873b4354021ce50d500876b2154021dc88550087692154021dc48550087612154021c799153d031d53d0f40c754e43d031e5350f40c754c43d031d53d0b40c754e42d031d5350b40a798c42d029d6310b40c754c42d02b66110b40ad58442d031d53d0740c754e41d031d5350740a798c41d029d6310740c754c41d02ae6210740ab58841d02b960d4f40c7d9553d031f6254f40c798953d031d6254f40c718953d031f6154f40c798553d031d6154f40c718553d031f6054f40c758153d031d5314f40ae58053d029e63d4b40a758f52d031d53d4b40ae58352d031d5394b40c754d52d029e6314b40a758c52d031d5314b40ad98452d02b56114b40ae58052d023e65ccb408f59732d031d53ccb40c754e32d031d534cb408f99432d023d650cb40c754c32d02b6610cb40ad58432d02ba600cb40ae58032d029e63d4740a758f51d031d53d4740ae58351d031d5394740c754d51d029e6314740a758c51d031d5314740ab98851d02ad6214740ae58051d023e65cc7408f59731d031d53cc740c754e31d031d534c7408f99431d023d650c740c754c31d02ae620c740ab58831d02ba600c740ae58031d031d53c8740c754e21d023f65487408f19521d031d53487408f99421d023d6508740a798c21d029d6308740c754c21d03a52108740ae98021d02b96008740ae583439031d5350e40a758f40902da63d0240ae983435031f5350d40c714d43502b86050d408f994435025e63149409758c525027661149409d58452502ba6090940a798c425029d6310940ad98442502b56110940ae980425025e63145409758c515026e62145409b58851502ba6090540a798c415029d6310540ab98841502ad6210540ae98041502da63d0140ce58353502b96094d40aed81535031d5314d40ae58252502bb6054940a798c525029d6314940ad98452502b561149408f997325023d65cc940ae98232502b9608c940aed8132502b8604c9408f994325023d650c940ad98432502b5610c940ae98032502b9600c940ae58251502bb6054540a798c515029d
  | 4 => 0xf59250cc71d43943319b988548c66d62152319e980548c6796015231ae583438c63f6454a318f191528c63e64942318f592508c67a60951319e582544c6b960d0d31a7592434c65c6550d31b5185434c71f6550d31c7195434c7976150d31e5185434c69f6050d31c750f524c63e64149318f590524c67a60149319e580524c69d64cc931e550f314c63e64141318f590504c71d43141319b988504c66d62141319b98b540c66d62d50319e983540c67960d50318f596540c63d60950318fd81540c63e64150319798c540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63d65d0c31ae583430c63f6550c31c794d430c72e5494831cb552520c72f4394831cb50e520c72e5454831cb551520c72f4354831cb50d520c71d54cc431d354b310c765528c43197d95310c71d544c431d3549310c677654c431e5d0d310c765524c4318f992500c63d6494031ce952500c7395494031da94a500c7695294031ce992500c7396494031ced0e500c7394394031ce951500c7395454031da949500c7695254031ce991500c7396454031ced0d500c7394354031d6cc5500c7723154031d64c5500c77131540319798c54c865d63153219e98054c867960153218f99253c863d6494f218f99053c863d6414f219e98053c86796014f21ae58343c871e5350f21c754d43c878d434cb218f99250c863d64943219798c548865d63152219e980548867960152218f992538863d6494e218f990538863d6414e219e98053886796014e21ae583438871e5350e21c754d4388795434c6218f992508863d64942218f58f544863d60d51218f992544865e63151219758c544867a60151219e580544863e6515121a758c54486b96015121c798c544863d6315121c758c544861d6315121cb58854487356115121ce980544863d6015121ce580544863960151218f992534863d6494d218fd91534863c6454d219ed8153486786054d218f990534863d6414d219e98053486796014d218f997434863c65d0d21ae583434863e6550d218f195434871e5350d21c754d434872c54909219b19542486e461509219b195324878d434c921b918532487345490521e990a41486746550521b918941487a542505219d1953148795434c521b918931487c5324c5218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863d63950218f582540863f63550218fd81540863e64150219798c540865d63150219b988540867661150219e980540867960150218f993530863d64d4c219e983530867960d4c218f992530863d6494c2197596530871e5494c21c7552530871e6494c21c7592530871e5454c21c7551530871e6454c21c7591530863e6414c218f590530865e6314c219b98853086766114
  | 5 => 0x4210b1d53508429bd954210b565394442d554e5110b374394442cd50e5110b565354442d554d5110b374354442cd50d5110b374254442d99095110b354254442d95095110b5a5394042d654e5010b725194042dc5465010b3b4394042ce50e5010b5a5354042d654d5010b725154042dc5455010b3a6454042ced0d5010b394354042ced095010b3942540429e98254cca796095332ae58254ccb1e6395332ce98254cca3d6095332ce58254cca3960953328fd8154ccab960d0f32c795143cca9f6550f32c7d9543cca9f6050f32c750d51cca3e64943328f59250ccb1d43943329d984548ca7561152329e980548ca796015232ae583438ca3f64546328f191518ca3e64942328f592508ca7a60951329e582544cab960d0d32a7592434ca5c6550d32b3189434cb1f6550d32c7195434cb8f6250d32e3189434ca9f6050d32e350f324cb1d43d45328f990514ca3d64145329e980514ca7960145328f990504ca3d6414132c750c504ca7661141329d584504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f582540ca3f60550328f990540ca5e63150329d984540ca7561150329e980540ca7960150328f992530ca3d6494c328f597430cab960d0c328fd95430cb1e5350c32c7553320ca5f654c832c7551320ca6f654c832e3d0d320cb365494432cd552510cb374394432cd50e510cb365454432cd551510cb374354432cd50d510cb573254432d98c9510cb553254432d94c9510ca3e64940328f592500cb3a5494032ce552500cb725194032dc546500cb3a6494032ce592500cb3b4394032ce50e500cb3a5454032ce551500cb725154032dc545500cb3a6454032ce591500cb3b4354032ce50d500cb5b3254032da8c9500cb593254032da4c9500cb1d53d0f41ae58343d06b960d0e41c794d439071d5350e41a758c42906b56110a41ae58042906b960d0d41c7d4d435065e63149419758c525067a60149419e580525063e65d0941c7991531071d53d0c41ae583431071e5350c41d394e521074d5394841cbd0e521072d4394841d394d521074d5354841cbd0d521072d43548418f596421071d5390841cb54a421069d6310841c754c421072d5210841ad58442106b96010841c754f411072d52d0441d954a411063f6550441c754d411072d52504419dd9541107655250441d694e50107595394041da94a50107695294041ced0e50107394394041d694d50107595354041da94950107695254041ce991501073b4354041ce50d501073a4254041ce109501073b4154041ce505501067a60953319e58254cc6b96095331c798e54cc73a60953318f58254cc73960953318e58254cc63f6055331ae58343cc71e5450f31a7d9543cc71f6550f31a7d8143cc71d4354b31a759332cc71d54ccb31c755132cc63e64943318
  | 6 => 0x105280280200c0a001001000000000010000140280000002000002006000000030060140000500400804800002098008070040100080100a0000000300200c0000301401c1601200604c0000100005002008008004000000000000000d004000008030000000080301e00401800012044030010020380380602c0000000400002003000020018000000000080000100401c03001000000000030140000200a00002800000002008000000000080680c0040040080000001402801000014010010000000080000a000000000060080900300200001001000010000000020040200000200c0000000002c0b8000000100a801002000000010300000080100e004010090020000580b00e01800000004038030020b40000900000200805803010000088030020200180000a0000280200206806000000008010120020080480a00000c010030020000100401a000008010000000000800a00000000004024008020080180000800600400800008020008010260100c8080040100000302400801000016000008070020000c0080000300080f000004000030080180000000200404801002050000000000100000400e030008000000040000000602400002000000030150100000180001802800001012008000010080040080100001000003000004030030040000300d0020000000c00e004010020020500080900000000005000000000020020100000b004004008010020040000600a0080780003a02c0000000e0100600301e0000100600a04c06000016000050010000080080300001c000010020000000102c0280000000205804009000000000090180180180100e0040000100000801000002000010050000040100300001401000ce99150d0eba60d4b43ae58352d0eb66114b43ad58452d0eba6014b43ae58052d0eba60d4743ae58351d0eae6214743ab58851d0eba6014743ae58051d0f3b6554343ced4950d0f3a5254343ce54950d0f385254343ced4550d0f3a5154343ce54550d0f385154343ce58d50d0f3b6254343ce98950d0f396254343ce18950d0f3b6154343ce98550d0f396154343ce18550d0f395014343ae5834390eda60d0e43b69834350e7661149439d5845250e7a60149439e5805250e6e62145439b5885150e7a60145439e5805150eba60d4d43ae5835350e9d62d4d43a75875350e9e60d4d43e69835350e9a60d4d43e65835350eb66114943ad5845250eba6014943ae5805250eae6214543ab5885150eba6014543ae5805150f395014143ce9825410f396095043ae5834310e3f6550c4397d954310f1e5450c43c754f43d0ab960d0f42ae5834390b1e5350e42c754d4390ab960d0d42c7d4d4350a5e63145429758c5150a7a60145429e5805150b1e6454c42c754f4310ab960d0c42c794d4310b1d53d08428fd95
  | 7 => 0x124a3206525790c9db0b91af0000000318ec8000a384700000021e0001c0a210000858f727b82a29600023780026b8dc8000000000001e72021f080000000019e16312580000c8a51ba12f26d0b695707b0001a584d8000001408000000002580042088e08d71a28f78d38bc89ca6527818485c9260000000001ad0000001de80003f0621978000888698000000540d980005226198800f8e7000247a612ad2360000b51ef9792968ed19f19d00000323487180000e1a0000229a9c8269e894d9d504a00025009d21200006406f23b8a1a910000df8001e80002a81db80000022b0f689514c85e90793719211d800018a9ea1697711228a26e0c28f18cda158000000000e60af8e594fa9ba2f80018a2a900027d0000001cc8000000220000000000000ee25e8001ed03d80026782788a18d8001b31640000199ed9cb99b8001d284c80009680000c00000000005d80000024180000000000014b8000000002042071b19e48c68ba0ae9fd1fa00000014d08c89f0002112890f811e8038460290001ac9e293ea4900026f86ba5a8000001390000000000000000000000000002a1048a810000aaa518001610f8a2e8000000000fb8001119030270250158ca11faa427e2369b11f91a321389c0001238be80000020ea43a5d8b20941412219fa8d49d82ae8049f80001a7a839291480000000ac00006924b2409f98a116f0000e300010e80023d8000000000d829fa0481c00007f00015527980017385b1a487992418c0000000000000000002a683800022807800008780007d28e80000021d9af996a898000b600009a00000000009d9d19691f4813a948001b29910000000000860000000000000000000000000002ab10a80019b0001830ab8ff9c6058a2d0000001190000000e4146999a4d20127f81e14780580005e14e80000000029380001d0000000000000a921c11489b00000000000000029a0000f30000001708e2800265a6f110a7b14a8b000017e8000b18000001789d38000000000000f599600028e0c511b97e0d404e17a8001568002572052400b4a750000000f3a23a4f00010f86c00002c03520f9ad80000000021d23d0d592e0002972141ba8000732531cb1f38302aa06aa6b285242a3a02e0870000680481398000120000000001dc8000000ea2869f1a248002a395413610a00000000000010e00000008900000017308f8f620280022aa8f8f28eb8ce1df1d4000038a561038001d10e80820a61ff89280023f8002a70fc0d28000000001bda6d8000000920b58610400002a48348000fc8000000009bf09398921e9c30882af95c9c49bd03e88119a824000230a0980011b1380001768000000fe00021c800207a450000899ae0231fe80003200000000007582d8c000000005f80000027d80017000028188018280009a85011
  | 8 => 0x22a119c8166a1a98203d1fb8948518cb91a0000000738002388000ad1ae800294206161a2027380000017200027c2018000000778001950001201c78f528580000000022a17a134000000246a5d00003a8002ab957aaa87f99900006080008aa3400010692e9f7130122823aa196a21022306291c1f02221531cc0fd80900010b8a48c61b38ca8f40000000bf80010604e9b8a2896a8000b323f17786a1040901a703600f17d04c2448869a88830931801711330d6922208292a430fd1022a32a598e8761648538001dd9b4a871651d729d8b80002920000000000570bb9931189b996080011e0000219a62a62760000000000001c98000000000001b800000013ca278000001e995208194b15480780000018a8170ff00018784225200000000007523180000000023906c9f28000f900021f80006f80007d80b9d601f26a0e219f8b98190591c415091592ba50a0b92f9e094c2ac9dd2328741e92840000000000000002038002808000ef07c21a04b96b00004a8d884d01325e1c39ee0000000000001dfa150000e01e780010d81a282a2d87a20f0e8aa00000002758d3226a9f00021818582013a0ef9ab8000000002681018002129420b892508d80016619713180000018616d9452498000d780003e00000a2548de03a0980002411338000002800000002978001fe00000011319380023b11700004392d0000992260e7866217260aad80020d15da0c0510a71be17b29181006890f0768d18fb1e000027a20a05d25c0eea710000001528cc24b8cd26ea2c0002090149fb1621c280d0b099c01ba4818b0cf1d79b5a3c9a184f0c59328808579680000df29580980200018115a0000340000000000000001a38002398db800067171a629000000000bc00000029e1e128b1870000001089388001a819e8db11c8000180088b38459ec00000000003b8000442350c48c995d169837033a4e95911380024202809582ea4598080020a80000013f0c09798f0a0d9489b208e95e9f78000001c682b14900011692c8000001bb96d0001868000000ce80000000000000022580000008d00000000025c8000000001c10d51b92338ada568000000000000478028af0dc12b0a800006027e80023e86d05ba8c0001b709100000000000018f97f0359cd08b00807ea602190bf136a669ff2240c321080023e1cf2148cc80722c80b27219816880025a1ca84908296b89e9ea22f0000c82178000be1ce28f07880009180000000000017fa1f1f880019428224603300003ca2914a15b01280000000010501600010c1e695a9f68001430000701a100008495115c0002032310e50000000000000002648000002550002980000e380008380004085f1a528b8e180011611780000000028d0000001cd9a99f4271aa080000000000016c00000000024d98e00a960
  | 9 => 0x2f17611000008f08c19d97d95f89b98d2331d880000027702a98c8310000000000c19049b693b1d21eb00000027894981d92d8000000000581218561e62620000b41c000025f1c91c880013f8c10000550568108a080022e2470a31781d0072a8a866a2280007a9d48d000000000194e0410001401ec91f0000659b000000001680023a88424a1d98000000c429b0001208000001838000000001070000000000002a280512125914f00000000000023711aaa51438248da01c84299a0a6a861c70000002730c20001272270000368000a21ce89621b82b9bb16e13d9e302127a9ab1f22909eaa698001d089700000018b87e07480621b0000418a99758e48000001560a79d689f849a5392a8000000001929a900013500020c8548a5a76a6c1c18d080029011980022080e90080026402c8ec0001441ef1150002630a280000015824e0f00000001cfa8300000024fa998ba90900006da2517401504b2199de1f10daa5b18199c9c50001bc991800053134a5293a8000001a415e29d1b78a89419448c71fd9bc0001299e58000430e927c8209aa967063a639269e50eb2728000fa08e044a4a8708998d610826ca8d97ba58a9925b951800077268898a358000dd9f580004f99480005c064a5f90d1180001311888000000000bda4885999002d02f98993b8fa9140001e18ae0001428001e39fc8000000000f125980000018f00002597c80000000016e80d9b42af0178001aa21301ea18a440c786b15894729c1da0e12931500392778f495b8000509eb800216030927a5413c1322740000001029b60ab2ac1752671461a6a8c87b8630001308a416c8000010298f992806786e1d92a9a88a300cf9598000f208b93585a98505599883f806aa200001f8000001e400000000026aa380618000b120b06e8000288000000000140909e21be955a791a20000000721bf8000ac8cb28800000023c00012c0378000001d31da80007c80019592a0fe9a08000001538001059c5a9aa5100000000000027f09780000000022ba0e1841b08000790000851749c20002ae0e696593d0000001ac0c39ee8002878000d10e9aa79d5a66137a69000172967a068000d2000145a9880028483280005a04693e00001a8000002950000000b295f1fc0000000000b70bb039800255a0580000016283c0002748000de8001dc0000000bd10b1f60ed8c88000000d90dd1098002709638000000001010000000000000001ca0450112000001908001b511283b0000000aa24c8000002008002700710b796f928a4c0ea91d0000001f52a889e0c90a001b0119f302617c1230
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x187127050d510c388b8286a88618358e52d0030c1ac6a96801861563947400c30ab1aa3a0061865954390030c92c6a9480187094354a400c328b1aa320061c450d5190030e1486a92801870943549400c38921aa2a0061c450d5150030a32eb31a801851b7558d400c315b2aa4a00618ad8d5250030e14c6a92801870963549400c390a94a2a00618cd955150030e44a4a8a801872152545400c319b1aa2a0061c498d5150030e22c6a8a801860d6454b300c30ab22a398061c254940cc030e22a2a0660186296454a300c384a1aa5180618c591518c030e2286a8c601841f75591300c306b22a49806185591514c030e12a5a02601871151d01300c384a928098061c4545404c030876eab22601862964549300c385a1aa498061c250d524c030c62c8a8a601871343545300c388a1aa298061265d3654c030a32eb322601851b75591300c24dbaac89806186dd5644c030932ecaa2601868964949300c30cb22a498061a2591524c030e14a8a92601870954549300c325b22a498061c2991524c030c92c8a92601870964549300c304b22a498061a4592514c030e82a528a601861964545300c348b22a298061c4951514c030e22a8a8a601874252545300c3a0a92a29806194d91514c030e24c8a8a601865164545300c388b22a29806184591514c03083ae6322a39061963982548828ab88a6a1c41469ce5450220932e7b2a811051a73d95408821d3b4a6a04414c5c45350220c32c829a61105517114d308828ab88a6a1a4183195434c920a4ae828a4290545731452148264b98c4a0241385c46250120a34e7b2a809043a7694d4048298b88a6a0241625cc6250120b42e23128090528754c940482543b242a024186590534c120aa2e229a6090548754c93048344b2264982418694d60d0c20c32a6b06861053170d0e5108298b8686a8841075ce649402083aed29e801041d7654f400830ab1ca3a00418558d51d0020a52eba02401058973d012008384a9e8090041c8547404802083ae6322a5885257414921c42a2b98a490e218658e6095210a1ae429a870841d73993528428d39ca8a0421265cf6550210a34e7b2a810843a7694d4084294b90a6a042186590534c210a92e429a610850d7214d434430a32a8698a21495d05248510a8ae629242884d1731854044270b90c2a0221469cf6550110874ed29a80885297214d404421c3b2a4a0221461cd5250110b22e630a80885a17218540442983aa62a02212c1d92150110c32c829a60885497214d30442a83aa6298221a4591314c110cc0ca90a408841d73d81540421cb82cba18218694d60d0c10c32a6b06860852970d0e5204294b8686a9021075ce649401083aed29e800841d7654f4004306b1ca5a00218358d52d0010a62eba02200859173d011004388a9e8088021c854b4044010
  | 1 => 0x4210714a92c0210830e5db4394041a32e7322a020d19731095010698b8884a80838698d6095331a34e12a28798c9970d9543cc68d386caa1e630e5c06454a3198ae430a8698cd170185434c68d386caa1a63615c86150d31b22e030a8698e0d43588504c694b8687290634a5c34354831a2aeba1a6218d9170d0d310c783a1aa4988630e5db4354031e268698aa018c397099253c860eb9cc9286430e5c26494e2183ae7324a110c3b7058f544860fb9ac1aa2438358d6215121c2ac6b08a890e2562584544870cb1cc02a2438698d6015121c32c6b00a890e29625805448718b0ac02a2430e5c26494d21872e032e8690c3970195434860e3b2a6a1a43461c15350d2198ae630a8490ce17018542486863aa8699243295d0614c9219c2e030a6490cc5731894148670b80c4a0a43451d5434c52194ae83126290ce170189314861cb86c6aa043075cf6055021872e1324a610d1970992530868cb84c8a98430e5c365d0c21876eab068610e1a53583430870ca9ac1a1843615cc6448421b42e03224210d4573d5121086b0b86a890843495d65448421a4cecaa24210d24765512108693b9aa89084349dc15448421a4ae9a9a4210d6170d4d21086a2baca690843c15525348421e0ca8a9a4210f055454d21087833a2a690843c15d15348421e0ec8a9a4210f046454d2108692bae8690843c154f4348421b42e1a1a4210d257550d2108782a9a8690843075ce6494021e42a890ca010f4153486500868cb9cc9280430e5db4394021e44a890aa010f215448550087a129a42a8043d054d2154021a32e7322a010c3976d0d5008791ba242a8043c81d12154021e44c890aa010f21644855008791a1a42a8043c850d215402183aeb31885a06155398442d030aa9ac221681075d66310740c1aa731083a060d5358841d0306b10c4a9e81459c46254f40a2ae2312a7a05197018953d0287390c2a9e81435c86154f40c2ac230aa7a05197018553d030aa9cc2296818554d6114b40c32a6b00a5a06155398432d030aa9ac2196818654e600cb40c32a6b0065a060d5398851d0306a9ac428e818654d6014740c1aa731063a060d5358831d030ca9cc018e818654d600c74083ae632a43a041d7399421d020ebacc610e8107dd9530874083aeca9843a06256548421d0342b1a4210e81c154d2108740c32a730043a06195358021d035090ac010e812c5c4604c940952e430262a041d731952150312b2a4210a81a158d2108540d4242b0042a061954181324c268b88c09926186550604c530992e4302629851b75581430c294b86872906143dd54354830a52e1a1aa4185497090d520c287b8286a9061c29c14354830e12e0a1aa4187054354a510c298b86872886145dd54354430e0a87292a21870543549510c298b8686a8861545c24354430a2ee0a1aa2
  | 2 => 0xc6279ba688528f01a2a0b404000a9030059948b0006ba820f0d84910e391a660940002a68326ea807e4a0006804491a307aaeea29d82280e8a2cc729b01c2e4b4990b4090a62da8d21a630601b88800272932002ca1c00000000000615ca42ae550000010835000af0d000000000007e800000000000000000000f284176788000000000000000b84f19ab6000001d4b984c000007c94c00000189341f00000000001ec001880000021050448008e9f64f800001c8921468515e5ea088c96685a6816972258323aa923889a6f12c0003a589029fa9c77000121366b224ac808a00c87c19e4596804a7a99a4a960c2b1998b5a123688c49adc20acea7a509c25271000000f446a066da6c270009580078000002a2001805d2026716e282b69e17e7e02e202880025e0000000000381f400086bc1cc82ad4118ca3fac235ac8902ea5f2aa2f1a82d898909d000000000be8111e19138310001eae2aeaca0006c298ec009640e03e412641280c7fa96878287006a5c2744c0229aa224e8746928c8802a161440000056a8e3e90a4a9eeba094509b800040a1ade54a8400000000005b0006a8dc000002914e338f6ac000758004000079854ae22a00000332948b9329f1588e0aa0b000a6a762494a461e80820e950de00036af98600072001ce3b910002ec1a00055800749fc97000aa0660910c398e8628341726000000002e01381e001e4648264bab42385600000b0000001be00000348c000076000002c196540c62e8fc6118e109da9896048a3602800000145e11c709145200000000002185a800ab05e00006000000000000226001de9125a3c0a2000002b0008f9b2001b4b10ae480f8938041e000071060000402008040401028240003008302e030281c020204800181a000000400000280a0f0080c060602830040400064020206830000007804041506800040a020001c000781006001902820010080000070c814060c110e408060f80002030000024030100002010081402040204c0401028841400008045a00058100009000481202008300403078a8000500820054c9c45254343a62e2292a1a1d2a7214550d0e94b90a2a8687465cc6254343c52c4312a1a1d327118950d0e98b88c4a8687465cc6154343a54e430aa1a1d297218550d0f18b08c2a8687465c26454c42c32a6b06862153170d0e5110a98b8686a88850e5db4394042a32e7322a02161a6358254cca8d384a8a1e65265c36550f32a34e1b2a879943970191518ca62b88c4a1a65325c06250d32a34e1b2a869958571189434cac4b80c4a1a658550d6114132a1aeba1a641958970d0d320ca98b8687288654c5c34354432e0e86992a21943976d0d500cb85a1a64a8065465c26454c41c32a6b068620d2970d0e5210694b8686a90838358d5210841c2aa6b088420e1953580
  | 3 => 0x1
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x44000001800e2800e8000a4020022110d20a801f000039e0000b8c008d0800a0000016281804a080130000900009002800000001e242150068b0032980270000000000000038000000060d8001020c00004000010000080c09735886254343c21625c46254343c11735846154343c21725846154343b0180d0d3254432a0986d0d3254032b0180d0d524c431a1186d0d3154031909801d5434c921911801d5434c52192180dcd544842190583dc15448421b01809d15348421905871915348421b01801915348421d01535c34348421a21861d12154021b01831d12154021b01839912154021a2186d0d2154021c05625c46254f40c09625c06254f40c05725846154f40c11615c06154f40a058654d2108740e01534856008740c11545c4604c930c09545c8604c530e016454a514c030e0164949514c030e0164549514c030c11645c4534c220889831d92150120c11645c4534c120c0875591324c1209098754f4048020d01735474048020c09645c8534c210891831d92150110c09645c8534c110c1075591314c1109118754f4044010d017354b4044010
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (27102+((h/294+packedAt s5K5 (23868+(h % 294)*11) 11) % 1283)*11) 11
  | 4 => packedAt s5K4 (57326+((h/458+packedAt s5K4 (52288+(h % 458)*11) 11) % 1998)*12) 12
  | 3 => packedAt s5K3 (19598+((h/125+packedAt s5K3 (18473+(h % 125)*9) 9) % 498)*10) 10
  | 2 => packedAt s5K2 (2678+((h/14+packedAt s5K2 (2580+(h % 14)*7) 7) % 89)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xb3c3cf3e318f38e3e3f631e38e0739fbce40cf
  | 1 => 0xfdfc0fdfc1ffc0fc7c783e3c0ff83e3cd07333
  | 2 => 0x3efff01ffe0fff007f8fc03ff03fc03f238c3c
  | 3 => 0xc0ffffe0000fffff800fffc0003fffc03c0fc0
  | 4 => 0xfffffffff00000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x444061828211114444021060a281088a864045
  | 1 => 0x40204040202008080020404081010001112
  | 2 => 0x80088008002400090010400900120020008428
  | 3 => 0x1b9104012948a080092ca4804124a500380a80
  | 4 => 0x6fe22891a100b4d2524f393269808582bf6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8fefcfee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x158018048d000887818901169d80000a15128212109f099b9a9f9d13008d93829884001c161e00191e83059b050000000b00038f1c99a08814910c9a178c200e140a86118b8f80068700100e800000170e0116087020600081207448b00003041608000037fd500bfe5402df9500dfd5402ff1500b7c54037fd4c09fe53037f54c09fc5302ffd0c09fe43007f50c09fc43037fd480d7f5201ff9480dfd52005f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd440d7f51017f9440dfd51005f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50037f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a400eff99520035fcca9003bfd654801d7eb2a400eff19520035f8ca90003ff64480017fb22400dff9912002dfcc890003fd64480017eb22400dff1912002df8c89003bff544801bff2a2400ddf95120077faa890037fc544801bbe2a24000ffd8d20005fec690033fe63480097f31a4000ff58d20005fac690033fc63480097e31a400effd4d20067fca69003bfd5348019fe29a400dffd0d20067fc8690003fd4348019fe21a4001bfd892001ffea49000f7f5248007ff2924003ff5492001efaa49000ffc5248007ffa124003ff9092001ffa849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c920007fec290002ff6148017ff30a4002bf98520007fac29002ffc61480057e30a400effd4520076fea29002ffe514801dfea8a4000df5452005ff8a290037ff4148017ff20a4000ff5052005ff88290033ff3148017ff18a4000ff4c52005ff8629000fff2148007f790a4003ff8852001ffa4290003ed2148007fe10a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fd2024001ff50120007f28090007fc4048003ff9824001ff8c12000ff46090007fd3048001fc9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fa1048003fe082400affd9510055feca8802bfe654400d7f32a200aff59510055faca8802bfc654400d7e32a2000ffd9110005fec888027fe644400b7f3222000ff59110005fac888027fc644400b7e322200affd511004ffca8880277e5444015feaa22009ff1511004ef8a888003ff63440017fb1a2008ff98d10025fcc688003fd63440017eb1a2008ff18d10025f8c68802bff5344011ff29a200aff54d10047f8a688027ff4344011ff21a2000ff50d10047f88688003ff62440017fb122007ff9891001dfcc488003fd62440017eb122007ff1891001df8c48802bff5244015bfa922007ff94910057faa4880037d524400ffe2922009ffd091003ffc8488003fd424400ffe2122008ffcc91003ffc6488003fd324400ffe1922001bfd8510017fea28800b7f5144005ff28a2002ff54510016faa28800bfc5144005ffa0a2002ff90510017fa828800bfc4144005ff98a2002ff8c510017ec628800bfd3144001fa98a2002ff0c510017fe428800bfe2144005fb10a2002ff48510007ea428800bfc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x37f65500013fb2a8014ff99540035fccaa0053fd65500297eb2a8014ff19540035f8caa00537c655000d3e32a8001bfd914002ffea8a0053bf545000bff2a28005df9514002ffaa8a0017fc545000bbe2a28005ef1514002e78a8a0003ff63500017fb1a8013ff98d40025fcc6a0003fd6350027fe31a8004bf18d400a7fea6a004ffe5350029fea9a8013ff14d4002ffe86a0017bf435000bff21a8005ff50d400077a86a0017fc4350001ffb128000bfd89400b7fcc4a000efe6250001feb128016ff1894001df8c4a0053ff5250029bfa928016ff949400a7faa4a00037d525002dfe2928005ffd094002f7e84a0017fe425000bfea128000ef5094002ff884a004fff325002dff1928000ff4c9400b7f864a0003ff61500017fb0a8015ff98540015fcc2a0003fd615002bfe30a8002bf185400a7fea2a00537f515002bff28a8014ff54540006faa2a0057fc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff1054009ffe62a0057fe3150001fe98a8015ff0c5400b7fe42a0057fe2150001fe90a8015ff0854000dfec0a0007ff5050003ff2828001fe9414000ffaa0a0053f95050003fe2828001ffd014002ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828013fecc14000ffc60a0007fc3050003fc1828001ffc814000ffc40a0007fa2050003fe1028001ffc414000ffc20a0007fa1050003fe0828012ffd9530095feca9804bfe654c00d7f32a6012ff59530095faca9804bfc654c00d7e32a6000ffd9130005fec898047fe644c00b7f3226000ff59130005fac898047fc644c00b7e3226012ffd513008ffca8980477e544c025feaa26011ff1513008ef8a898006ff634c009ffa9a6004ff94d30027faa698013fc534c009ffa1a6004ff90d30027fa8698013fc434c001ffb126000bfd8930087fcc49800efe624c001feb126010ff1893001df8c49804bff524c025bfa926010ff94930097faa4980037d524c021fe2926011ffd0930087fc8498003fd424c021fe2126004ffcc930027be6498013fe324c009fe9926000f74c930027f86498003ff614c0017fb0a600fff98530015fcc298003fd614c01ffe30a6002bf18530097fea29804b7f514c01fff28a6012ff54530006faa29803ffc514c023ffa0a600fff90530007fa829803ffc414c009ff98a6004f7cc530027fc6298013fd314c001ee98a6004ff0c530087fe429803ffe214c001fe90a600fff0853000dfec098007ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c009fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000fb06098007ff204c003ff1026001fe8813000ff84098007ff104c003ff0826001fe8413000ff8209803bff654801d7fb
  | 2 => 0x41017fe20a080bfe1050405fe082821effd95310f5feca9887bfe654c40d7f32a621eff595310f5faca9887bfc654c40d7e32a6200ffd9131005fec898877fe644c40b7f3226200ff59131005fac898877fc644c40b7e322621effd51310effca8988777e544c43dfeaa2621dff151310eef8a89880aff634c409ffa9a6204ff94d31027faa698813fc534c409ffa1a6204ff90d31027bc8698813fd434c401eea1a6204ff10d31007fec498802ff624c439ff3126203bf98931007fac498873fc624c4077e312621effd49310f6fea498873fe524c43dfea926200df549310e7f8a498877ff424c439ff2126200ff509310e7f88498813ff324c409ef9926204ff8c931027fa6498803dd324c409fe1926202bfd8531017fea29880b7f514c405ff28a6202ff54531016faa29880bfc514c405ffa0a6202ff90531017fa829880bfc414c405ff98a6204fdcc531017fc629880bde314c405fe18a6202f70c531017e8629880bff214c405ff10a6202fd88531017f84298803ff604c4017fb02621bff9813100dfcc098803fd604c437fe3026201bf181310f7fea09886ffe504c43dfea82621bff141310effe809886ffe404c437fe2026204ffcc131027be6098813fe304c409fe182621cffc81310dffc409886ffc204c405ff8826202fdc4131017fc209880bfc104c435ffb2a421abfd95210d7fcca9081afe6548435bf32a42069f995210d7faca9086afd6548401beb2a42009f595210d7f8ca9081afc6548401ffb224200bfd91210cffcc890816fe6448401feb224200bf591210cff8c890816fc6448435ffaa24219ff951210cefca89086bfd5448433fe2a24219df15121007fec690802ff6348431ff31a4204bf98d21007fac690802fd6348431fe31a4204bf18d210d7fea690863fe5348435fea9a4218ff14d210cffe8690863fe4348401fea1a4218ff10d21015fec49080fff5248407bfa924203ff9492101ffaa49080f7d5248407fe2924203ffd092101ffc849080fee4248407fea124200fb5092101ff8849080fff3248407ff1924203fb8c92101ffa6490803ed3248407fe1924202bfd8521017fea29080b7f5148405ff28a4202ff54521016faa29080bfc5148405ffa0a4202ff90521017ec829080bfd4148401faa0a4202ff10521017fe629080bfe3148405fb18a4202ff4c521007ea629080bfc3148405ff90a4203fdc8521017fc429080bee2148405fe10a4202fb08521017e8429080be42148401ffb024200bfd81210bffcc090806fe6048401feb024217ff1812100df8c09086bff504842fff282421aff541210bff8a090867ff404842fff2024217ff101210c7fe609085ffe304842ffe1824203ffc812101fde409080ffe2048407fe1024202ffc4121017ee209080bfe1048405fe0824214ffd95400a5fecaa000
  | 3 => 0xea926403df5493201ff8a49900fff424c807ff2126403ff5093201ff8849900fff324c809f79926403ff8c93201fbc649900ffc324c807ee1926403fb0c932007fec299002ff614c851ff30a6402bf98532007fac2990a3fc614c8057e30a642affd4532156fea2990a3fe514c855fea8a6428ff1453214ffe82990a3fe414c851fe20a6404ffcc532027be6299013fe314c809fe18a6403ffc853201fde429900ffe214c807fe10a6400ffd8132005fec09909ffe604c8037f3026400ff5813213ff8c099006fc604c855ffa826427ff94132157faa09909ffc504c853ffa026427ff9013213ff88099013ff304c809ef9826404ff8c132027f8609900fff204c807f79026403ff8813201ff840990a3ff104c84fff0826427ff04132006fec8a889b7e645440b3f322a200df59151136f8c8a88167c6454401bfb1aa225df98d51006fac6a88977c635444dbfa1aa225df90d51006fa86a88977c4354401bfb12a2009fd8951126fcc4a88037d6254449be312a226dfd0951126fc84a88037d4254449be212a225dfcc951126fc64a88037d3254449be192a202dfd8551014fec2a881b776154405bfa0aa202df90551016ec82a880b7c4154405bf98aa202df8c551016f862a880b7f2154405bf10aa202df08551006fec0a888f7e6054401beb02a223df18151136fe80a888f7e4054447be202a225dfcc15111efc60a888f7c3054449bf902a223df8815111ef840a880b7f1054405bf082a202df04151117fecaa088aff6550401bfb2a82009fd9541117fccaa081afe6550445feb2a8222bf59541117f8caa081afc6550445be32a82069f19541015fec8a0817ff545040bff2a28205df9514102ffaa8a0817fc545040bbe2a28200ffd8d41005fec6a0887fe63504097f31a8200ff58d4110ff8c6a0812fc6350445ffa9a8221ff94d41117faa6a0887fc535040bffa1a8205efd0d4102ffc86a0817fd4350401dea1a8205ff10d41007fec4a0802ff6250441ff3128203bf98941007fac4a0883fc62504077e3128222ffd4941116fea4a0883fe5250445fea928200df54941107f8a4a0817ff425040bdfa128205ff9094102ffa84a0803bd425040bfe2128221ffcc941107fc64a0803fd3250441fe1928202bfd8541017fea2a080b7f5150405ff28a8202fd94541017faa2a080b7d5150445faa8a8200dd54541017f8a2a080bff415040bfba0a8202ff905410177c82a080bfc4150405de20a8202fd10541017fe62a080bfe3150405fe18a8202ffc8541017fc42a080bf62150405fe10a8200ffd8141005fec0a087ffe60504037f3028200ff581410fff8c0a0806fc6050445ffa82821fff94141117faa0a087ffc505040bffa028205efd014102ffc80a0817fc4050443ff982821fff8c1410fff860a0883ff205043fff102821fff081
  | 4 => 0x8d3fc2150c01ffb028600bfd814319ffcc0a1806fe6050c01feb028633ff1814300df8c0a18dbff5050c67ff2828636ff5414319ff8a0a1817ff4050c0bdfa028605ff9014302ff880a1813ff3050c09ff1828633f78c143027f860a1813dc3050c6bff9028633ff8814319ff840a18d3ff1050c67ff0828633ff04143006fec8a90cb7e645480b3f322a400df59152196f8c8a90167c6454801bfb1aa431df98d52006fac6a90c77c6354865bfa1aa431df90d52006fa86a90c77c4354807bfb12a4039fd8952036dec4a900f7f4254807bf212a403db9095201ef884a900f7f3254807bf192a403df0c952006fec2a90027f6154861bf30aa400df58552186f8c2a90cb7f4154861bf20aa430df1055218efe62a90c37e3154861be18aa403dfc855201efc42a900f7c2154801bfb02a42fdf98152006fac0a90bf7c6054865bfa02a42fdf9015217ef880a90c77f305485fbf182a42fdf0c15201efe40a900f7e2054807be102a430dfc415217efc20a90bf7c105485dffb2a842ebfd9542006fecaa10027f655085dff32a8406bf99542177facaa10bafd655085dfe32a8406bf19542176f8caa101a7c65508077fb228405ffd514202ffca8a10177e545080bfeaa28405ff1514202ef8a8a1003ff63508017fb1a842dff98d42025fcc6a1003fd635085bfe31a8404bf18d42177fea6a10b7fe535085dfea9a842dff14d4202ffe86a1017bf435080bff21a8405ff50d420077a86a1017fc43508077fb128403ffd494201efea4a100ffe5250807f72928403ff5494201efaa4a10bbed5250801b6a928403ff1494201ffe84a1017ef4250807ff2128403ef9094201ff884a100fbc4250807f62128403ffcc94201ffc64a100ffc3250801ffb0a8400bfd8542167fcc2a100afe6150801feb0a842cff18542015f8c2a10bbff515085dbfa8a842cff94542177faa2a10b3fc515080bffa0a8405efd054202ffc82a1017fc415085bff98a842cff8c542167f862a100fff2150807f790a8403ff8854201ff842a1003ff60508017fb02842bff9814200dfcc0a1003fd6050857fe3028401bf18142177fea0a10affe505085dfea82842bff1414202ffe80a1017bf405080bff2028405ff1014216ffe60a10affe3050857fe1828403ffc814201ffc40a100ffc2050859ff882842bff8414215ff820a10abff654c8557fb2a642aff99532035fcca990abfd654c8557eb2a642aff19532035f8ca99003ff644c8017fb226429ff9913202dfcc899003fd644c8017eb226429ff1913202df8c8990abff544c853ff2a26429df95132157faa8990a7fc544c853be2a26403bfd8d32027fea699013fe534c809fea9a6404ff14d32027fe8699013fe434c809ef21a6404ff50d32007ba8699013fc434c8077fb126403ffd493201efea49900ffe524c807f
  | 5 => 0x8cd0001ad02f18197185000a00f92821907801384298e9831268959109a687d1369a29e408e0641d48d4a200d10b70770eb80012d0001800ce15780000012210580016715422693c0000281ec14e8000002420be1291b603300a9e79b38000001af00000001113c9230b204300ea4f0309b99119af8261620000000020100000a002000008070060000400000a0b00600002201802800000004030000040180000000c00003804010008040080000100480e00a01001803000010000050480580000c0020140100700000001001046058018040000040400000a00401800006038008000040000180900601c078000140040c006002004090030080140500102408802012040018018000000000601300002006802004028000000220180100301e03c018040000080580101c0080200000203c0080000a00000000004010068020000040400600000000800002008000000040180580c00a08c0000300001c02805000000000030560240100400c0340000300401001004002000008010000280080000001c0200600a008030010140680081f0080040183400200001004018008010010040040580100800402801002000000010100000100000600405800000128018080400000380304200001000004000008040040040b00b03200802800016044000000300000380701c004038020080240000b024000000300000100000f00603c2080300001c0280300000c0080700006c018000560000201200000800009048000008020000080700000200003800016000000110040080000501600400804008024050090120140300000c0040b803000010000060220400200a00000c098040060040000e0020180000b0080000080000600001000012000010010020000080004e0080000101a0100000101e0042080002236ffd95431b5fecaa18037f6550c013fb2a8636ff99543035fccaa18dbfd6550c6d7eb2a8636ff19543035f8caa18db7c6550c0d3e32a8604bfd914302ffea8a18dbbf5450c0bff2a28605df9514302ffaa8a1817fc5450c0bbe2a28605ef1514302e78a8a1812ff6350c09ffa9a8604ff94d43027bca6a1813fd5350c6deea9a8604ff14d43027fe86a1817df4350c09ff21a8604ef90d43027f886a1813bc4350c09ee21a8600ffd8943005fec4a18d7fe6250c077f3128600ff589431aff8c4a180efc6250c6dffa928636dfd49431affca4a18dbfd5250c6bfe2928605ffd094302f7e84a1817fe4250c0bfe2128604ffcc943027be64a1813fe3250c09fe1928600ffd8543005fec2a18d3fe6150c057f30a8600ff585431a7f8c2a180afc6150c6dffa8a8636dfd45431a7fca2a18dbfd5150c69fe28a8605ffd054302f7e82a1817fe4150c0bfe20a8604ffcc543027be62a1813fe3150c09fe18a8635ffc85431a7fc42a1
  | 6 => 0x18983a80000000007499e1d21371fc0000f38390000930989960de0ad9d78fb11ba180002438001a00001c4a3e800000172944a289b218b14280000000011e20e8000002078000001968a802b0000000b79f80001a78f78da86e05424a83b918a2b9a721ea0612a839a2d19702903e0ae0000909db1068e49d91209349a08c80d0838924113092057a231bd8e780003c16995a80000000015517311e8e1a2f96d92b8c08251a31ad8071950ba84e85a97004d9b0927045075a3399d2350001d303fa0d80189e2188998c4820881897000238a4f8b410893183721795e800000176914a038a09710fa000a2a8bb09f24c0f813087c1f3a0c8cc90e9d8807909a06a2c9a39070b600018f06c23003c9d70002408ca8279fb82da3b18a8158000e20400f40cb8c395680006680021a1412108700000000cd9ba87420823797c0ef8890000000000e51b78002418000000002260000000000d180f0000000d900000013d8000001931100001760000fa8dd00000020a9ed8f686782c00002a8718000000b480008993316287096c875124a160fe86886f9f121714c0cb00011c1c418493b1fb08d14b0ef04414d8000cf20c11100024408311200023f9f214a83a1f78340f716597413880209018900384d0841030bf1d98c002481a87207aa168068001c08000f20000b590d0b116915d9b915f80023d99815201d00115c9039ec954a2c2142250001a92150918448000368001be0001409a100000004e0000200ab0170000000181fe80507294880d8db13405a00009b80014e00000805716d0d787600019a15e0001329278f914c94600009d80000024b2498f01e2000000000000000000000000178a139ba10209e9b69cf1468bd9cd24e8ac0c70059051751e51ce0ac8001c39d0a2192623a80893100020b8660000ee0418e98001cd83802f8509ed00000002b80012d80013b90f0001478000001b88000e72341fe0889ab0d50d28798000f19df9b59df1758f99c5a470000001d50000001e180005f0001c70028b387112595104800014a00004208296c14b80000020e1cba2a0338001b711d0000bc01a25005885d15d10c80004080ca3b80000000006d800000205a148000001439e38d21571be9cf87a1929d10001138839b00030000e80168000470311f98000000e422280015190100000017b88f80015f0000000000000108db80008c8000000001689c999e9398000658518001a20c880000011a16480d0cf80000021f20a18800005981788b80000000000012a00000024490a9e481f8c90001e300009480011d9539078eb01c8580a006b89b05c12f0ee84a8001d4197847a329a60000990000001eb0000000000001780000000378001e68000769748c68001ce9dea4013024d8001ab9cb12c8f2a3e23a19124699f05696f200897933980
  | 7 => 0xf89424c9640a20ba0b91f609f8dc0ab8a704f0b09bd0ec9ac000202800056052a39a2ea2f0002248858001451430000fc0001c10000000001a580006301c00018105900002a00018c96191614220714f8c98a30d400004996000b0611a4832878800201a102270a780020405d8001f88539ff84f91c8a9a4610183621e019a331ee9dc1eb8d68e0a0107b9360df04ba2083186b0f893807e8e29b29f58002488001e88000de80000000000000000024e0fc80b80000005e15a0000000000001908929f50002429c50000001150000241a800017e80016b8001001400f50df8000f61e60e687317f1a982288200000017a1cc8548001250ae93780015c1bc1ff1a195614d1b10af20304a0800790a608a0000000a41e10000000002238002048000b885c80015080005f86a0e10001fa80013f01621d22e00019b80600000000000008b0001d28000001c30e30848000878001b19c68000000001aa10c22416384580c0851608af81288e8b984b0220000001bc98892107e23185513e9de0a19860c5967945a3d1958c199200018401b80000015880023900001883500000000000009600006380018d00002988116123681e83597d9e280000000016f8671f70002020a28d38121668b6a0d15b14980000016b0000e5896906048a35a4581924816e9d00d621a8d81dd9359b48268e006c9709e724d04105b87f0f48000002298150000000239c19d380006e8ea8000aa0000000002280000000d98000001fd9e58869492279558271080ff8ce98a1918fb91409d0618dd8f58e61e0194a1193f86509512989817e10e1f693d2431091470491390b30cc02d0aa9ca9bba0f16e0c41ea00023817218798b8460ed0bd1db99000001317980000000000022100000000012380000000009387b1e08a38258288809c21dd0b19f088a9940000000001528218000c20000c79481fd1598000001c280000016318e1ef8001869c000010b8000521b30000000d00000001f18348f09c60000680000000d580e00009c000014869062a131b401b209a4b9850c50c32479a891917d12e97911691a86021b117800091060a159048b520507780019980018d9440b2a370000531d692191706a9320ed8ca22b24a2120fe17396a03019894f00010283e9ef0e396a9350c10000000000001f311f23c12b00012c0001180000001cc19d85b2452258fd1c892289a0a10212361e800980019c9d60000d89b518718299fa0f80018c11580017707d9d58000e89dc80403f19c02c8bb8001b821ba128000000001d8185a309580001c78dc82e06491987384c1ae08610b1fc91b20b05e8001419bb0000ad1ae8000ff0da15b9a4069800011a411ca18f8be89c9fa0001a517c83b0fda220049990000000f10000000000e90468b800022da1100015012e1da8001ee13a8510870
  | 8 => 0x23f22901e06d06f0000090001aa8ea03212016519b0000000000a51128000d30000a88001e903d10d80009a8001f488f0000001ac97797f9f9100a310001bf17a80017b1839820ec23c80000000016820000000005593a0000000a586208d82307f93e0000a69bf87c8bc8a90001c90b019a9660bf84c83da3202e9f01591f290a21da1c8f30d701f10fa3488824921f90412f8c28a49ea9f41532091da0439c808c19381021981421c01d9e99288c62089d191
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x7524c51000775524c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100dff0704c510016f7604c510017f3604c5100dff2404c5100dfd7304c5100dff2304c5100dfd5304c5100dff2204c51000df4764851001ef4764851000cf476485101e7767548510007757548510006f76448510006f564485101df7654485101df745448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851001ee4624851003f77524851003f75524851003fe64248510007e5424851003fe63248510007e53248510007f3704851000df6704851000df470485100bff07048510016f76048510017f360485100bff240485100bff230485100bfe720485100bff220485100bfe52048510015f8765011002ef87650110014f876501100077b75501101d77875501101d6fb65501101d6f9655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb864501101d7bb545011004f7a545011004f78545011004fb8545011004f385450110005fb735011009efa635011009ef8635011004fbb4350110007b94350110005fb7250110006fb6250110006f962501101d77b525011000779525011004fbb4250110007b94250110007f37150110015fa7150110015f871501100aff07150110015f0715011000efb615011000ff361501100af7b51501100af7951501100afbb41501100afb941501100aff23150110007f131501100aff22150110007f12150110015f8764c110026f8764c110014f8764c110005fb744c110005f9744c1101cf7a544c1101cf78544c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110026d8634c110005fb724c110006fb624c110006f9624c1101c77b524c11000779524c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c11000efb614c11000ff3614c11007f7b514c11007f79514c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110015f8764811001ef87648110014f87648110005fb7448110005f97448110006fb6448110006f964481101bf7a54481101bf785448110005fb7348110005f97348110006fb6348110006f9634811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003f7b524811003f79524811003fea3248110007e93248110007f37148110015fa7148110015f8714811005ff0714811000efb614811000ff3614811005f7b514811005f79514811005ff23148110007f1314811005feb214811005ff2214811005fe9214811003ff12148110007e12148110
  | 1 => 0x8d1002cfe7458d1002cfc7458d100067e5458d100067c5458d1022cff7358d10006df7358d10004ff7258d1001cfe7258d1001cfc7258d100067f5258d10046df3258d10224ff7158d10006f77158d1007e7f5158d1007e7d5158d1007ef62158d100dcff7058d10006fb7058d100defa2058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d1002ebe6450d10006bd6450d1004f3c5450d10006df6350d10026dc6350d1000dfa7050d1019fda3050d1001cfe76d891003eee62d8910004ff75d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d89100067e54d89100067c54d8910024fe73d8910004fd73d8910024fc73d89100bcfd72d891003e7f52d891000cff71d8910014fe71d891000cfd71d8910014fc71d891021e7f51d891021e7d51d891021ef631d891021eef21d891021eed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d891020efa40d891020efa30d891020eef20d891020eed20d891001cff7658910005df7358910045dc735891003eec6258910205f77158910215fb7058910004ff7558910034fe7558910004fd7558910034fc7558910004ff745891002cfe745891002cfc74589100067e54589100067c5458910004ff7358910006df7358910004df7358910024fe7358910024fc7358910006dc7358910024dc735891020cff7258910006ef725891003e7f525891003eee3258910204ff7158910006f7715891005e7f515891005e7d515891005ef631589100bcff7058910006fb70589100befa40589100befa30589100067f76549100067e76549100067d76549100067c765491004d7e745491004d7c74549100067f64549101967e64549100067d64549101967c64549100067f635491018e7e63549100067d635491018e7c63549101fd7f72549100576f725491003e7f625491001e7e625491003e7d625491001e7c625491003f6e42549101857f71549101857d715491017e7f615491018776315491018776215491017e7f605491017f7a405491017f7a305491017f7a20549101877b105491017f76105491017f74105491017f781054910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100557c755091002ebe6450910006bd64509100076d525091000dfa7050910004ff764c910004fe764c910004fd764c910004fc764c910026de634c910006dd634c91001eee624c910006ed624c910015f6714c91000dfa704c91000df4764c510026f4764c51000cf4764c5101f776544c5101f774544c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6434c510007d5434c510005f7724c510006f7624c510006f5624c5101ef7
  | 2 => 0x1df872501200b7e8725012001de8725012000efb625012000feb62501200b77b52501200b77952501200b7bb42501200b7b942501200b7ea3250120007e93250120005fb7150120006fb61501202777b515012000779515012006fbb4150120007b941501200b7eb2150120007e9215012001df8764c120026f8764c12001cf8764c120005fb744c120005f9744c12026f7a544c12026f78544c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120026d8634c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c1200877b524c12008779524c120087db324c120087ea324c120087d9324c120067e9324c120007c9324c120005fb714c120006fb614c1202677b514c12000779514c120067db314c120007d9314c120087eb214c120007e9214c12002cfe76d91100557e75d91100057d75d911004ebe64d9110004ff75d9110034fe75d91100067e75d91100347e75d9110004fd75d91100067d75d91100047d75d9110034fc75d91100fcfd74d911004e7e54d911004e7c54d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d91100067f52d911000cff71d9110014fe71d911000cfd71d9110014fc71d911025e7f51d911025e7d51d911025ebf41d911025ebd41d911025ef621d9110014ff70d911000cfe70d9110014fd70d911000cfc70d911024ebf40d911024ebd40d911024efa20d911002cff76591100057f75591100557c755911004ebc6459110245f77159110255fb7059110004ff75591100067f75591100047f7559110034fe7559110004fd7559110034fc75591100067c75591100347c755911024cff7459110006bf745911004e7e545911004e7c5459110004ff7359110024fe7359110024fc735911004ebf4359110004ff725911001cfe725911001cfc72591100067f525911004ebf4259110244ff7159110006f771591100ae7f51591100ae7d51591100aef621591100fcff7059110006fb70591100fefa2059110024fe76d8d10046de63d8d10004ff75d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100067e54d8d100067c54d8d100dcfd73d8d10046de43d8d1001cfe72d8d10004fd72d8d1001cfc72d8d100067f52d8d10006de32d8d10046dc32d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d1023e7f51d8d1023e7d51d8d1023edf31d8d1023edd31d8d1023ef621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d1022edf30d8d1022edd30d8d1022efa20d8d10024ff7658d10046dc6358d10225f77158d10235fb7058d10004ff7558d10034fe7558d10004fd7558d10034fc7558d10004ff745
  | 3 => 0xc764c9202af6e544c9202af6c544c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920067ce434c920007cd434c920005ef714c9202a76f514c920067cf314c920007eb704c92000dee704c92000dec704c92013fe8704c92001eef604c92001feb604c92013fea404c92013fcf304c92013fea304c92013fcd304c92013fea104c920014fe76d852005ef661d8520004ff75d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d85200067e54d85200067c54d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d852029e7f52d852029e7d52d852029eee32d8520006ed32d852005e7f51d852005ef621d852029ef521d852000cfe70d852001cfd70d852000cfc70d8520206fa40d8520206fa30d8520206f710d8520005df7358520065dc735852005ef46158520295fb70585200067f76545200067e76545200067d76545200067c765452006d7e745452006d7c74545200067f64545201367e64545200067d64545201367c64545200067f635452012e7e63545200067d635452012e7c63545201257f72545201257d725452011e7f62545201276e32545200076d325452028d7f715452007777715452005e7f61545200167e61545200167c615452005f76415452005f6f215452011e7f605452011f7a405452011f7a30545201277b205452011f6e205452011f6c205452011f78205452011f7a1054520004ff7650520004fe7650520004fc76505200057f75505200757c755052002ebe6450520006bd645052000775515052000dfa7050520004ff764c520004fe764c520004fc764c520026de634c520006dd634c52001dee724c520007cd324c520016f6614c52000dfa704c52000dec7648520016ec764852000cec76485202876e75485200076d7548520006ef6448520006ed644852027f6e544852027f6c5448520005ef7348520005ed7348520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec614852005fe46148520016e4614852005f6f514852005f6d514852005fe64148520007e5414852005fe63148520007e53148520007eb704852000dee704852000dec70485200bfe8704852001eef604852001feb60485200bfea40485200bfea30485200bfe710485200bfea104852001df8765012002ef8765012001cf876501200077b7550120277787550120276fb6550120276f9655012000dfb745012000fbb7450120007bb645012002efa645012002ef8645012006fb86450120277bb545012006f7a545012006f78545012006fb8545012006f385450120005fb735012009efa635012009ef8635012006fbb4350120007b94350120007eb725012001dfa7250120
  | 4 => 0xc53000dde704c53000ddc704c5300dfd8704c53000dd8704c530026df604c530027db604c5300dfda204c5300dfd7104c5300dfda104c530004ff7648530004fe7648530004fc76485300957e75485300057d7548530025de7348530005dd734853001eee6248530007cd3248530016f66148530007d5314853007fe4214853000dfa70485300bfd8304853002cfe76d91200757e75d91200057d75d912006ebe64d9120004ff75d9120034fe75d91200067e75d91200347e75d9120004fd75d91200067d75d91200047d75d9120034fc75d912015cfd74d912006e7e54d912006e7c54d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d91202ee7f52d91202ee7d52d91202eebf42d91202eebd42d9120014fe71d9120004fd71d9120014fc71d91200067f51d91202eeef21d912001cff70d912001cfd70d91202debf40d91202debd40d91202defa10d912002cff76591200057f75591200757c755912006ebc64591202d5ef72591202e5fb7059120004ff75591200067f75591200047f7559120034fe7559120004fd7559120034fc75591200067c75591200347c75591202dcff7459120006bf745912006e7e545912006e7c5459120004ff7359120024fe7359120024fc735912006ebf43591202d4ff7259120006ef72591200b67f52591200b67d5259120004ff7159120014fe7159120014fc71591200067f515912006ebf41591200b6ef215912015cff7059120006fb705912015efa1059120024fe76d8d20066de63d8d20004ff75d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d200067e54d8d200067c54d8d2013cfd73d8d20066de43d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202ce7f52d8d202ce7d52d8d202cedf32d8d202cedd32d8d20014fe71d8d20004fd71d8d20014fc71d8d200067f51d8d20006de31d8d20066dc31d8d202ceef21d8d2001cff70d8d2001cfd70d8d202bedf30d8d202bedd30d8d202befa10d8d20024ff7658d20066dc6358d202b5ef7258d202c5fb7058d20004ff7558d20034fe7558d20004fd7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d200067e5458d200067c5458d202bcff7358d20006df7358d202b4ff7258d20006ef7258d200867f5258d200867d5258d20004ff7158d20014fe7158d20014fc7158d200067f5158d20066df3158d20086ef2158d2013cff7058d20006fb7058d2013efa1058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200757c7550d2002ebe6450d20006bd6450d2006f3c5450d20006df6350d20026dc6350d2000dfa7050d2019fda3050d2000dec764c920026ec764c92000ce
  | 5 => 0x32eed32d8930014fe71d8930004fd71d8930014fc71d89300067f51d893032edf31d8930024fd70d89302b6ef20d89302b6fa10d8930086ec6258930325fb705893013fd830589300067f76549300067e76549300067d76549300067c765493008d7e745493008d7c74549300067f64549301967e64549300067d64549301967c645493017e7f63549301fd7f72549300976f72549300867f625493001e7e625493001e7c62549300876e42549300875f32549300057f71549301867e61549301867c615493018f5f315493017e7f605493018f7b305493017f5e305493017f5c305493017f78305493017f58305493017f7a205493017f7a1054930004ff7650930004fe7650930004fc76509300057f75509300957c755093002ebe6450930006bd64509300076d525093015fd8305093000ddc764c93001edc764c93000cdc764c930006df644c930006dd644c93031f5e544c93031f5c544c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c9300875f524c9300875d524c930005df714c9303175f514c930087cf214c930007db704c93000dde704c93000ddc704c93013fd8704c93000dd8704c930026df604c930027db604c93013fcf204c93013fda204c93013fda104c930014fe76d853007ef661d8530227d830d8530004ff75d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d85300067e54d85300067c54d853000cfd73d8530014fc73d853001cfe72d8530004fd72d853001cfc72d85300067f52d85300067d52d853030edf32d8530006dd32d853007e7f51d853007ef631d853030ef531d8530024fd70d8530226fa20d8530226f710d853007ef46158530305fb70585300dfd830585300067f76545300067e76545300067d76545300067c765453008d7e745453008d7c74545300067f64545301367e64545300067d64545301367c645453011e7f63545300057f72545300067f62545301267e62545301267c625453012f5f32545300075d325453028d7f715453009777715453007e7f61545300167e61545300167c615453007f76415453007f5f315453011e7f605453012f7b305453011f5e305453011f5c305453011f78305453011f58305453011f7a205453011f7a1054530004ff7650530004fe7650530004fc76505300057f75505300957c755053002ebe6450530006bd64505300077551505300ffd8305053000ddc764c530016dc764c53000cdc764c530006df644c530006dd644c5302ff5e544c5302ff5c544c530005df724c530006df624c5302f75f524c5300075d524c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007f5f514c53007f5d514c53007fd6214c530007db704
  | 6 => 0xf75505400a5be75505400a5bc755054035f3c75505400a53c75505400073f655054035f3c6550540005bf7350540006bf6350540005bf7250540006bf625054035f3f52505400073d525054002dbf715054002fb77150540007b76150540016be6150540016bc61505400afb461505400af3f51505400afb651505400af3d515054035fb551505400073551505400afb62150540007bb705054000dbe705054000dbc70505400ffb8705054002ebf605054002fbb60505400ffba505054035fb95050540357bb30505400ffb830505400ffba20505400ffba1050540004ff764c540004fe764c540004fc764c5400067f654c5400f67c654c54002dbe744c540005bd744c5400ef3c544c540026de634c5400079d434c540005fb704c54000df8704c54009fdb304c540004ff7648540004fe7648540004fc76485400a57e75485400057d75485400067f65485400d67c654854002dbe7448540005bd74485400cf3c544854001eee6248540007ad4248540016f66148540007b541485400afe4214854000dfa704854002cfe76d91300957e75d91300057d75d913008ebe64d913033fd830d9130004ff75d9130034fe75d91300067e75d91300347e75d9130004fd75d91300067d75d91300047d75d9130034fc75d913019cfd74d913008e7e54d913008e7c54d913000cff73d9130024fe73d913000cfd73d9130024fc73d913034ebf43d913034ebd43d913001cfe72d9130004fd72d913001cfc72d91300067f52d913034edf32d9130014fe71d9130004fd71d9130014fc71d91300067f51d913034edf31d9130024ff70d9130024fd70d913033ebf40d913033ebd40d913034efb30d913033ede30d913033edc30d913033ef830d913033ed830d913033efa20d913033efa10d913002cff76591300057f75591300957c755913008ebc645913008f3c5459130335df7359130345fb705913019fd83059130004ff75591300067f75591300047f7559130034fe7559130004fd7559130034fc75591300067c75591300347c755913033cff7459130006bf7459130006bf545913008e7e545913008e7c545913008ebc545913008e3c5459130334ff7359130006df7359130004ff725913001cfe725913001cfc72591300067f525913008ebf425913009edf3259130004ff7159130014fe7159130014fc71591300067f515913008ebf415913009edf315913019cff7059130006fb705913009efb305913019ede305913019edc305913019ef8305913019ed8305913019efa205913019efa105913001cfe76d8930086ee62d89302b7d830d8930004ff75d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d89300067e54d89300067c54d893000cfd73d893001cfc73d89300867f52d8930086ee32d8930
  | 7 => 0x494002d3c745494017e7f64549400067f635494018e7e635494018e7c63549401973f43549400073d43549401fd7f72549400a76f72549400b67f625494001e7e625494001e7c62549400b73f42549400b76e42549401976d42549400057f71549401867e61549401867c61549401973f415494017f7a705494000779705494017e7f60549401977b405494017f3e405494017f3c405494017f78405494038f7b305494017f78305494017f7a205494017f7a105494000dbc765094001ebc765094000cbc76509400073f75509400a5be75509400a5bc75509403873c75509400a53c75509400073f65509403873c6550940005bf7350940006bf635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400b7ac62509400b73f52509400b7ae52509400b73d5250940387ad52509400072d5250940005bf71509403873f51509400b7af2150940007bb705094000dbe705094000dbc705094015fb8705094002ebf605094002fbb605094015fba5050940387b9505094037fbb305094015fb8305094015fba205094015fba1050940004ff764c940004fe764c940004fc764c9400067f654c9401567c654c94002dbe744c940005bd744c94014f3c544c940026de634c9400079d434c940005fb704c94000df8704c94009fdb304c940014fe76d85400a57c75d85400067f65d85400067c65d85403773c54d85400aef661d8540004ff75d85400067f75d8540034fe75d8540004fd75d8540034fc75d85400067c75d85400347c75d854000cfd74d8540014fc74d85403767e54d85403767c54d8540024fe73d8540004fd73d8540024fc73d8540376bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d85400067f52d85400067d52d8540376bf42d8540006bd42d85400ae7f51d85400aef641d8540376f541d854002cfd70d8540246fa20d8540246f710d85400057f75585400a57c75585400067f65585400067c655854004f3c54585400aef4615854036dfb70585400067f76545400057e76545400067e76545400047e76545400067d76545400057c76545400067c76545400047c76545400073f745454002d7e745454002d7c74545401373c745454002d3c745454011e7f64545400067f635454012e7e635454012e7c63545401373f43545400073d43545400057f72545400067f62545401267e62545401267c62545401373f42545400073d425454028d7f71545400a77771545400ae7f61545400167e61545400167c61545400af3f41545400af76415454013775415454011f7a705454000779705454011e7f60545401377b405454011f3e405454011f3c405454011f7840545403677b305454011f78305454011f7a205454011f7a105454000dbc7650540016bc765054000cbc76505400073
  | 8 => 0x3c67f41d95403c67e41d95403c67d41d95403c67c41d95400067f31d95400067e31d95400067c31d95400067f21d95400067e21d95400067c21d95403be7f70d95403be7e70d95403be7d70d95403be7c70d95403be7f40d95403be7e40d95403be7d40d95403be7c40d95403be7f30d95403be7e30d95403be7d30d95403be7c30d95403be7f20d95403be7e20d95403be7d20d95403be7c20d95403be7f10d95403be7e10d95403be7d10d95403be7c10d9540024fe76d8d400067f65d8d400067c65d8d403b73c54d8d4009ede63d8d4000dfa70d8d4002df970d8d4009fdb30d8d40004ff75d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d40006bf54d8d403b67e54d8d403b67c54d8d403b6bc54d8d403b63c54d8d4009ede43d8d403b6dd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d400067f52d8d403b6bf42d8d40014fe71d8d40004fd71d8d40014fc71d8d400067f51d8d403b6bf41d8d4002cfd70d8d4009ef970d8d4002cf970d8d40336df30d8d4009efb30d8d40336f830d8d40336fa20d8d40336fa10d8d400057f7558d400a57c7558d400067f6558d400067c6558d4008f3c5458d4009edc6358d403adfb7058d4019fd83058d4000dbc7650d40026bc7650d4000cbc7650d400073f7550d400a5be7550d400a5bc7550d403a73c7550d400a53c7550d400073f6550d401b6be6550d401b6bc6550d403a73c6550d401b63c6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d4009f9c6350d4009f9e5350d403a79d5350d40005bf7250d403a73f5250d4009f9f3250d40005bf7150d403a73f5150d4009f9f3150d40007bb7050d4000dbe7050d4000dbc7050d4019fb87050d4002ebf6050d4002fbb6050d4019fba5050d403a7b95050d4009fbb3050d4019f9e3050d4019f9c3050d4019fb83050d4019f983050d4019fba2050d4019fba1050d4001cfe76d89400a57c75d89400067f65d89400067c65d894039f3c54d89400b6ee62d8940004ff75d89400067f75d8940034fe75d8940004fd75d8940034fc75d89400067c75d89400347c75d894000cfd74d894001cfc74d894039e7e54d894039e7c54d8940024fe73d8940004fd73d8940024fc73d894039ebf43d8940006bd43d89400b67f52d89400b6ee42d894039eed42d8940014fe71d8940004fd71d8940014fc71d89400067f51d894039ebf41d894002cfd70d89402d6ef20d89402d6fa10d89400057f75589400a57c75589400067f65589400067c655894006f3c54589400b6ec6258940395fb70589400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400073f745494002d7e745494002d7c74549401973c745
  | 9 => 0x7645052102ef6645052102ef464505210cfb464505210cf7654505210cf745450521005f773505210cfb74350521007b54350521007e7725052101df6725052101df47250521107e4725052101de47250521016f76250521017e76250521107775250521107755250521107b74250521107e64250521107b542505210cfe54250521007a54250521107e63250521007e53250521005f770505210cfb74050521107e7205052101df4764c521026f4764c52101cf4764c5213df76654c52100775654c521005f7744c521005f5744c5213d776544c5213d774544c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210c7d4634c5210c7d6434c521007d5434c521007e7724c52101df6724c52101df4724c5210e7e4724c52101de4724c521016f7624c521017e7624c5210e777524c5210e775524c5210e7e6424c521007e5424c5210e7d7324c5210e7e6324c5210e7d5324c5210c7e5324c521007c5324c521005f7704c5210c7d7304c5210e7e7204c52100cfe76d81210d57e75d81210057d75d81210067e65d81210067d65d8121217e421d81210befa60d8121004ff75d8121034fe75d81210067e75d81210347e75d8121004fd75d81210067d75d81210047d75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d81210067e54d81210067c54d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d81212967f52d81212967d52d8121296ee32d8121006ed32d812101cfd71d812100cfc71d81212167f51d81212167d51d8121216f631d8121006f531d8121006fb30d81210bef830d81210befa20d81210befa10d81210067e65581210067d6558121005df73581210c5dc735812105fe421581210bef860581213cd7e76d95400a67e76d95400347e76d954002d7e74d95403c73e74d954002d3e74d95403bf3d74d954002d7c74d95400067e63d95400067c63d95403c73f43d95400057d72d95400067e62d95400067c62d95403c73f42d95400057d71d95400067e61d95400067c61d95403c73f41d95403c77b70d95403bf7870d95403c77b40d95403bf3e40d95403bf3c40d95403bf7840d95400077b30d95403bf7830d95403bf7a20d95403bf7a10d95403be7f74d95403c67e74d954002c7e74d95403c63e74d95403be7d74d95403be3d74d95403be7c74d954002c7c74d95400067f73d95400067e73d95400067d73d95400067c73d95403c67f43d95403c67e43d95403c67d43d95403c67c43d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95403c67f42d95403c67e42d95403c67d42d95403c67c42d95400067f32d95400067e32d95400067c32d95400067f71d95400067e71d95400067d71d95400047d71d95400067c71d9540
  | 10 => 0x8d21004ff75d8d21034fe75d8d210067e75d8d210347e75d8d21004fd75d8d210067d75d8d210047d75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d210067e54d8d210067c54d8d21144fd73d8d21014ff72d8d21014fd72d8d2141e7f52d8d2141e7d52d8d2141edf32d8d2141edd32d8d2101cff71d8d2101cfd71d8d2140e7f51d8d2140e7d51d8d2140edf31d8d2140edd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210c6dc30d8d2141eef20d8d2140ef710d8d21024ff7658d210067e6558d210067d6558d210c6dc6358d21405ef7258d21415f77158d21147e42158d21005fb7058d210bdf87058d21004ff7558d21034fe7558d21004fd7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d210067e5458d210067c5458d2140cff7358d21006df7358d210c6de4358d21404ff7258d21006ef7258d210e67f5258d210e67d5258d21144ff7158d21006f77158d211467f5158d211467d5158d21004ff7058d21006fb7058d21004fb7058d2100cfe7058d2100cfc7058d21006f87058d2100cf87058d210c6df3058d210e6ef2058d21146f71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210d57c7550d211b67e6550d210067d6550d2102ebe6450d21006bd6450d210cf3c5450d21026de6350d21006dd6350d2101dee7250d21015f67150d211a7e42150d21015ec765092102eec7650921014ec76509210076f75509213ff6c75509213feef65509213ff6e65509213feed65509210076d65509210066d655092101def745092101faf7450921007af645092102eee645092102eec64509210cfac64509210cf6e54509210cf6c5450921005ef73509210cfaf4350921007ad4350921007e77150921015ee7150921015ec7150921167e47150921015e4715092101eef615092101fe761509211676f51509211676d5150921167af4150921167e64150921167ad4150921167e63150921005ef70509210cfaf4050921167e71050921015ec764c921026ec764c921014ec764c9213f76e654c9210076d654c921005ef744c921005ed744c9213ef6e544c9213ef6c544c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210c7cc634c9210c7ce434c921007cd434c921007e7714c921015ee714c921015ec714c921147e4714c921015e4714c92101eef614c92101fe7614c9211476f514c9211476d514c921147e6414c921147cf314c921147e6314c921147cd314c921005ef704c9210c7cf304c921147e7104c92101df4765052102ef4765052101cf476505210077775505213e77475505213e6f765505213e77665505213e6f56550521007756550521006756550521015f77450521017b77450521007b
  | 11 => 0xcd7e74595210cd7c74595210073c74595210cd3c74595210067e64595210067c64595210067e63595210067c63595214457f72595210076f72595214456f72595211276e42595211276e32595211857f715952100777715952144d7771595211877641595211877631595211277721595211876e21595211876c21595211877421595211876421595210067e60595210067c60595211276f20595211877710595210067f74595210063f74595210067e745952102c7e74595210067d74595210067c745952102c7c74595210063c745952102c3c74595210067f73595210067e73595210067d73595210067c73595210067f43595210067e43595210067c43595211267f72595214447f72595210066f72595211267f42595211267e42595211266e42595211267d42595211267c42595211267f32595211267e32595211267d32595211267c32595211867f71595211847f71595210067771595211867f41595211867e41595211867641595211867d41595211867c41595211867f31595211867e31595211867d31595211867c31595211867f21595211867e21595211867d21595211867c21595210067f70595210067e70595210067d70595210067c70595210067f40595210067e40595210067c40595210067f30595210067e30595210067c30595211267f20595211267e20595211267c20595211867f10595211867e10595211867c105952102cfe76d91210d57e75d91210057d75d91210067e65d91210067d65d91210cebe64d91210cf3c54d912142fe421d9121004ff75d9121034fe75d91210067e75d91210347e75d9121004fd75d91210067d75d91210047d75d9121034fc75d9121164fd74d9121006bf54d91210ce7e54d91210ce7c54d91210cebc54d91210ce3c54d9121024fe73d9121004fd73d9121024fc73d9121014ff72d9121014fd72d912143e7f52d912143e7d52d912143ebf42d912143ebd42d912101cff71d912101cfd71d912142e7f51d912142e7d51d912142ebf41d912142ebd41d912100cfe70d9121004fd70d912100cfc70d912102cff76591210057f75591210d57c75591210067e65591210067d65591210cebc6459121425ef7259121435f77159121167e42159121004ff75591210067f75591210047f7559121034fe7559121004fd7559121034fc75591210067c75591210347c755912142cff7459121006bf74591210ce7e54591210ce7c5459121004ff7359121024fe7359121024fc73591210cebf4359121424ff7259121006ef72591211067f52591211067d5259121164ff7159121006f771591211667f51591211667d5159121004ff705912100cfe705912100cfc70591210cebf4059121024fe76d8d210d57e75d8d210057d75d8d210067e65d8d210067d65d8d210c6de63d8d2140fe421d
  | 12 => 0xc7650d310075f7550d3146f5c7550d3146edf6550d3146edd6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d310ef9c6450d3146f9f5450d310ef5e5450d310ef5c5450d310ef9c5450d310ef1c5450d31005df7250d3146f5f5250d310ef9f4250d31007d77150d31015de7150d31015dc7150d311a7d47150d31015d47150d31026df6150d31027d76150d311a75f5150d311a75d5150d311a79f4150d311a79d4150d311a7d62150d31005df7050d3119ede6050d3119edc6050d310ef9f4050d311a7d71050d3101cfe76d89310e6ee62d8931004ff75d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d89310067e54d89310067c54d8931014fd73d8931466de43d8931006dd43d89310e67f52d89310e6ee32d8931466ed32d8931024fd71d89314067f51d89314067d51d8931406ef21d893100cfe70d8931004fd70d893100cfc70d8931466df30d8931406f710d89310e6ec625893145df77158931005fb70589310ddf870589310067f76549310067e76549310067d76549310067c76549310ed7e74549310ed7c74549310067f64549311967e64549310067d64549311967c64549311867f635493118f5e43549310075d43549314457f72549310f76f72549310e67f625493101e7e625493101e7c62549310e76e42549310e75f32549311857f71549311867f615493118f7731549311875e31549311875c315493118774315493118776215493117e7e605493117e7c605493118f5f3054931187771054931004ff7650931004fe7650931004fc76509310057f75509310f57c755093102ebe6450931006bd6450931025de73509310079d43509310076d5250931015dc764c93101edc764c931014dc764c931005df744c931005dd744c931006df644c931006dd644c9314575e544c9314575c544c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c9310e7cc624c9310e75f524c9310e75d524c931007d7714c931015de714c931015dc714c931147d4714c931026df614c931027d7614c9311475f514c9311475d514c931147cf214c931147d6214c931005df704c9310e7cf204c931147d7104c93100cfe76d81310defa60d8131004ff75d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d81310067e54d81310067c54d8131014fd73d813100cfc73d813101cfe72d8131004fd72d813101cfc72d81310067f52d81310067d52d8131306df32d8131006dd32d8131024fd71d81312367f51d81312367d51d8131236f621d81310defa40d81310defa30d8131006fb20d81310def820d81310defa10d81310def860581314457f76595210d67f76595210347f76595210073f7459521
  | 13 => 0x454103674765454102c74765454113777745454100737745454113776745454102d76745454113775745454113774745454102d7474545411373474545410177764545410167764545410173764545410077773545414a77673545410077573545414a77473545410077763545414a77663545410077563545414a774635454113777435454113737435454113776435454113775435454100735435454113774435454100777725454100577725454149f76725454100775725454149f74725454100777625454149f76625454100775625454149f7462545411377742545411373742545411377642545411377542545410073542545411377442545414a777325454149f76325454100775325454149f7432545410077770545414977670545410077570545414977470545414977660545414977460545411377740545411373740545411377640545411377440545414a777305454149776305454149774305454149f77205454149776205454149774205454100cfe76d81410067f65d81410067c65d81410077551d81410fefa60d8141004ff75d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d814136e7e54d814136e7c54d8141024fe73d8141004fd73d8141024fc73d814136ebf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d81410067f52d81410067d52d814136ebf42d8141006bd42d814102cfd71d81412567f51d81412567d51d8141256f621d81410fefa40d81410fefa10d81410057f75581411157c75581410067f65581410067c65581410077551581410fef8605814102cfe76d91310f57e75d91310057d75d91310eebe64d9131004ff75d9131034fe75d91310067e75d91310347e75d9131004fd75d91310067d75d91310047d75d9131034fc75d91311a4fd74d91310ee7e54d91310ee7c54d9131014ff73d9131014fd73d913148ebf43d913148ebd43d913101cfe72d9131004fd72d913101cfc72d91310067f52d913148edf32d9131024ff71d9131024fd71d913147e7f51d913147e7d51d913147ebf41d913147ebd41d913147ef621d913100cfe70d9131004fd70d913100cfc70d913102cff76591310057f75591310f57c75591310eebc6459131475df7359131485f77159131004ff75591310067f75591310047f7559131034fe7559131004fd7559131034fc75591310067c75591310347c755913147cff7459131006bf74591310ee7e54591310ee7c5459131474ff7359131006df7359131004ff725913101cfe725913101cfc72591310067f52591310eebf425913110edf32591311a4ff7159131006f771591311a67f51591311a67d51591311a6f62159131004ff705913100cfe705913100cfc70591310eebf4059131015dc7650d3102edc7650d31014d
  | 14 => 0x4debf42d8d4102cfd71d8d414767f51d8d414767d51d8d41476df31d8d41476f621d8d4100cfe70d8d41004fd70d8d4100cfc70d8d414debf40d8d410057f7558d411157c7558d410067f6558d410067c6558d4110edc6358d414d5f77158d41015bc7650d41026bc7650d41014bc7650d410073f7550d414cf3c7550d410073f6550d411b6be6550d411b6bc6550d414cf3c6550d411b63c6550d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4110f9c6350d4110f9e5350d414cf9d5350d41005bf7250d414cf3f5250d4110f9f3250d41007b77150d41015be7150d41015bc7150d411a7b47150d4102ebf6150d4102fb76150d411a73f5150d411a7b65150d411a73d5150d414cfb55150d411a79f3150d411a7b62150d41005bf7050d414c79e3050d4110f9c3050d4101cfe76d89411157c75d89410067f65d89410067c65d8941106ee62d8941004ff75d89410067f75d8941034fe75d8941004fd75d8941034fc75d89410067c75d89410347c75d8941014fd74d89414be7e54d89414be7c54d8941024fe73d8941004fd73d8941024fc73d89414bebf43d8941006bd43d89411067f52d8941106ee42d89414beed42d894102cfd71d89414267f51d89414267d51d8941426ef21d894100cfe70d8941004fd70d894100cfc70d89414bebf40d89410057f75589411157c75589410067f65589410067c6558941106ec62589414b5f771589410067f76549410057e76549410067e76549410047e76549410067d76549410057c76549410067c76549410047c765494102d7e745494102d7c74549411867f64549410067f635494118e7e635494118e7c63549411973f43549410073d43549414457f72549411176f72549411067f625494101e7e625494101e7c62549411073f42549411076e42549411976d42549411857f71549411877671549410077571549411867f61549411977741549411873e41549411873c415494118774415494118776215494117e7e605494117e7c60549411973f4054941015bc765094101ebc7650941014bc76509410073f75509414af3c75509410073f65509414af3c6550941005bf7350941006bf635094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941107ac62509411073f5250941107ae52509411073d52509414afad52509410072d5250941007b77150941015be7150941015bc7150941167b4715094102ebf615094102fb761509411673f5150941167b651509411673d51509414afb55150941167af2150941167b62150941005bf7050941004ff764c941004fe764c941004fc764c9410067f654c9411567c654c94102dbe744c941005bd744c941026de634c9410079d434c94111777765454103677765454113774765454102d74765
  | 15 => 0xf714c9510157e714c9510157c714c9511467f614c95115777614c95114776414c9511475f314c9511476f214c9510057f704c95111d7e704c95111d7c704c95112f5f304c9511276f204c95111d7e76d81511357e74d81510057d74d81511357c74d81510067e64d81510067c64d815112d7e73d81510057d73d815112d7c73d81510067f63d81510067d63d81511257e72d81510057d72d81511257c72d81510067f62d81510067d62d81510357f71d81510157e71d81510357d71d81510157c71d815150e7f61d81515177761d815150f7641d815111d7d70d815111e7e60d815111f7a60d815111e7c60d815111f7a10d815150f7910d815111d7f76581510057f74581511357e74581511357c74581510067e64581510067c64581510057f735815112d7e735815112d7c73581510067f63581510067d63581510057f72581511257e72581511257c72581510067f62581510067d62581514fd7f71581510077771581515057771581514fe7f61581510577761581514ff76415815111d7f70581510077b605815111e7e605815111e7c605815111f78605815111f7a40581514f57e76d95411167e76d95410347e76d954102d7e74d954102d7c74d95410067e63d95410067c63d95414ef3f43d95410057d72d95410067e62d95410067c62d95414ef3f42d954102d7f71d95414ef7771d954102d7d71d95414e77471d95414ef7741d95414e73e41d95414e73c41d95414e77441d95414e77621d95410067e60d95410067c60d95414ef3f40d95414e67f74d95414ee7e74d95414e67d74d95414e67c74d95410067f73d95410067e73d95410067d73d95410067c73d95414ee7f43d95414ee7e43d95414ee7d43d95414ee7c43d95410067f72d95410067e72d95410067d72d95410047d72d95410067c72d95414ee7f42d95414ee7e42d95414ee7d42d95414ee7c42d95410067f32d95410067e32d95410067c32d95414e67f71d954102c7f71d95414e67e71d95414e67d71d954102c7d71d95414e67c71d95414e67f41d95414e67e41d95414e67d41d95414e67c41d95414e67f31d95414e67e31d95414e67d31d95414e67c31d95414e67f21d95414e67e21d95414e67d21d95414e67c21d95410067f70d95410067e70d95410067d70d95410067c70d95414ee7f40d95414ee7e40d95414ee7d40d95414ee7c40d95410067f30d95410067e30d95410067c30d95410067f20d95410067e20d95410067c20d95414e67f10d95414e67e10d95414e67d10d95414e67c10d9541024fe76d8d410067f65d8d410067c65d8d4110ede63d8d41004ff75d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d414de7e54d8d414de7c54d8d4110ede43d8d414dedd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d410067f52d8d41
  | 16 => 0x895112d7e73d89510057d73d895112d7c73d89510067f63d89510067e63d89510067d63d89510067c63d89511857d72d89511267e62d89511276e62d89511267c62d89510357f71d89510157e71d89510357d71d89510157c71d89514467f61d895152f7761d89514477641d89514476f21d89514476d21d895111d7e70d89510057d70d895111d7c70d89510067e60d89510067c60d89510067f74d89510067e74d895102c7e74d89510067d74d89510067c74d895102c7c74d89510067f73d89510067e73d89510067d73d89510067c73d89510067f43d89510067e43d89510067d43d89510067c43d89511847d72d89511267f42d89511267e42d89511267c42d89511267f32d89511267e32d89511267c32d89514467f71d89514467d71d89510347d71d89514467f41d89514467e41d89514467641d89514467d41d89514467c41d89514467f31d89514467e31d89514467d31d89514467c31d89514467f21d89514466f21d89514467e21d89514467c21d89510067f70d89510067e70d89510067d70d89510067c70d89510067f40d89510067e40d89510067c40d89510067f30d89510067e30d89510067c30d89511267f20d89511267e20d89511267c20d89514467f10d89514467e10d89514467d10d89514467c10d89515257f76589510057f74589510073f74589510053f74589511357e74589511357c74589510073c74589511353c74589510067f64589510067e64589510067d64589510067c64589510057f735895112d7e735895112d7c73589510067f63589510067e63589510067d63589510067c63589514457f72589510076f62589511267e62589511267c62589511276c62589511276e42589511857f715895100777715895151d7771589511867f61589510d77761589511877641589510057f705895111d7e705895111d7c70589510067e60589510067c60589510057f76509510067f76509510047f76509510057e76509510057d76509510057c76509510067c76509510047c765095142d7f745095102e7e645095102e7c64509510057f735095112d7e735095112d7c73509511373f43509510073d43509514257f72509511267f62509511276e62509510076d62509511376f42509511273e42509511273c42509511276c42509511657f71509510157e71509510157c71509511667f61509511777761509511673f41509511677641509511676f21509510057f705095111d7e705095111d7c70509511373f40509510057f764c9510057e764c9510057d764c9510057c764c9510057f744c9511357e744c9510057d744c9511357c744c95114e7e644c95114e7c644c95140d7f734c95112f5e434c9510075d434c9514057f724c9511267f624c95112f6f324c9511275e324c9511275c324c9511276c324c9511457
  | 17 => 0x34fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d81320067e54d81320067c54d813201cfd73d8132024fd72d81322c67f52d81322c67d52d8132014fe71d8132004fd71d8132014fc71d81320067f51d8132326df31d81322c6ef21d813213efa40d813213efa30d813213efa20d8132006fb10d813213ef810d813213ef860581324f57e76d915102c7e76d91515757d74d91511367e64d91511373e64d91511367c64d915112d7e73d91510057d73d915112d7c73d91511373f43d91511257e72d91510057d72d91511257c72d91510073e42d91511373c42d91510357f71d915158f7771d91510157e71d91510357d71d91510157c71d91515867f61d915158f7761d91515873f41d91515877641d91515873d41d915111d7e70d91510057d70d915111d7c70d91511373f40d91514e57f76591515857f74591510073f64591511367e64591511367c64591511373c64591510057f735915112d7e735915112d7c73591510057f72591511257e72591511257c72591515757f715915100777715915157d7771591515767f61591511177761591515777641591510057f705915111d7e705915111d7c705915156d7e76d8d511357e74d8d510057d74d8d511357c74d8d510067e64d8d510067c64d8d515457d73d8d5112e7e63d8d5112f5e63d8d5112e7c63d8d511257e72d8d510057d72d8d511257c72d8d510357f71d8d510157e71d8d510357d71d8d510157c71d8d515567f61d8d515677761d8d515577641d8d515575f31d8d515575d31d8d5111d7e70d8d510057d70d8d5111d7c70d8d5155d7f7658d510057f7458d511357e7458d511357c7458d510067e6458d510067c6458d515557f7358d510075f6358d5112e7e6358d5112e7c6358d5112f5c6358d5112f5e4358d510057f7258d511257e7258d511257c7258d515457f7158d51007777158d5154d777158d515467f6158d510f7776158d51547764158d510057f7058d5111d7e7058d5111d7c7058d510057f7650d510067f7650d510047f7650d510057e7650d510057d7650d510057c7650d510067c7650d510047c7650d5147d7f7450d510073f6450d5102e7e6450d5102e7c6450d511373c6450d5102e3c6450d514757f7350d5112f5e6350d510075d6350d511375f4350d5112f3e4350d5112f3c4350d5112f5c4350d510057f7250d511257e7250d511257c7250d511373f4250d5112f5f3250d511a57f7150d510157e7150d510157c7150d511a67f6150d511b7776150d511a73f4150d511a7764150d511a75f3150d510057f7050d5111d7e7050d5111d7c7050d511373f4050d5153f5e3050d5112f5c3050d515357e76d89511357e74d89510057d74d89511357c74d89510067f64d89510067e64d89510067d64d89510067c64d
  | 18 => 0xf65d81420067c65d81420076d52d814215efa60d8142004ff75d8142034fe75d8142004fd75d8142034fc75d814201cfd74d81423967e54d81423967c54d8142024fe73d8142004fd73d8142024fc73d8142396bf43d8142006bd43d814202cfd72d81422e67f52d81422e67d52d8142014fe71d8142004fd71d8142014fc71d81420067f51d8142396bf41d81422e6ef21d814215efa40d814215efa20d81420057f75581421757c75581420067f65581420067c65581420076d525814215ef8605814202cfe76d91321557e75d91320057d75d913214ebe64d9132004ff75d9132034fe75d91320067e75d91320347e75d9132004fd75d91320067d75d91320047d75d9132034fc75d91321acfd74d913214e7e54d913214e7c54d913201cff73d913201cfd73d91325b6bf43d91325b6bd43d9132024ff72d9132024fd72d91325a67f52d91325a67d52d91325a6bf42d91325a6bd42d9132014fe71d9132004fd71d9132014fc71d91320067f51d91325b6df31d91325a6ef21d913200cfe70d9132004fd70d913200cfc70d913202cff76591320057f75591321557c755913214ebc645913259ddf73591325adef7259132004ff75591320067f75591320047f7559132034fe7559132004fd7559132034fc75591320067c75591320347c75591325a4ff7459132006bf745913214e7e545913214e7c545913259cff7359132006df73591321acff7259132006ef72591321ae7f52591321ae7d5259132004ff7159132014fe7159132014fc71591320067f515913214ebf415913216edf31591321aeef2159132004ff705913200cfe705913200cfc705913214ebf405913201ddc7650d3202edc7650d3201cdc7650d320075f7550d325975c7550d32596df6550d32596dd6550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d3214f9c6450d325979f5450d3214f5e5450d3214f5c5450d3214f9c5450d3214f1c5450d32007cf7250d3201dde7250d3201ddc7250d321afcc7250d3201dcc7250d32026df6250d32027cf6250d321af5f5250d321af5d5250d321af9f4250d321af9d4250d32005df7150d325975f5150d3214f9f4150d321afcf2150d32005df7050d3219ede6050d3219edc6050d3214f9f4050d321afcf2050d32014fe76d8532146f661d8532004ff75d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d85320067e54d85320067c54d853201cfd73d853245ede43d8532006dd43d8532024fd72d85324167f52d85324167d52d85321467f51d8532146f631d8532146f621d853200cfe70d8532004fd70d853200cfc70d853245edf30d8532416ef20d8532146f46158532005fb705853213df8705853200cfe76d813213efa60d8132004ff75d8132
  | 19 => 0x95420067e10d95420067c10d9542024fe76d8d420067f65d8d420067c65d8d4216ede63d8d42004ff75d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d425ee7e54d8d425ee7c54d8d4216ede43d8d425eedd43d8d4202cfd72d8d4259e7f52d8d4259e7d52d8d4259edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d420067f51d8d425eebf41d8d4259eef21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425eebf40d8d420057f7558d421757c7558d420067f6558d420067c6558d4216edc6358d425e5ef7258d4201dbc7650d42026bc7650d4201cbc7650d420073f7550d425df3c7550d420073f6550d421b6be6550d421b6bc6550d425df3c6550d421b63c6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4216f9c6350d4216f9e5350d425df9d5350d42007af7250d4201dbe7250d4201dbc7250d421afac7250d4202ebf6250d4202faf6250d421af3f5250d421afae5250d421af3d5250d425dfad5250d421af9f3250d42005bf7150d425df3f5150d4216f9f3150d421afaf2150d42005bf7050d425d79e3050d4216f9c3050d421776f76549420366f76549421976c765494202d6c76549420366c765494202c6c76549421976f74549420072f74549421976e745494202d6e74549421976d74549421976c745494202d6c74549421972c745494201f6f645494201e6f645494201f2f64549420076f73549425cf6e73549420076d73549425cf6c73549420076f63549425cf6e63549420076d63549425cf6c63549421976f43549421972f43549421976e43549421976d43549420072d43549421976c43549420076f71549420056f71549425c76e71549420076d71549425c76c71549425c76e61549425c76c61549421976f41549421972f41549421976e41549421976c41549425cf6f31549425c76e31549425c76c31549420076f70549425bf6e70549420076d70549425bf6c70549425bf6e60549425bf6c60549421976f40549421972f40549421976e40549421976c40549425cf6f30549425bf6e30549425bf6c30549425c76f10549425bf6e10549425bf6c1054942014fe76d85421757c75d85420067f65d85420067c65d85420076d52d8542166f661d8542004ff75d85420067f75d8542034fe75d8542004fd75d8542034fc75d85420067c75d85420347c75d854201cfd74d85424b67e54d85424b67c54d8542024fe73d8542004fd73d8542024fc73d85424b6bf43d8542006bd43d854202cfd72d85424367f52d85424367d52d85421667f51d8542166f641d8542166f621d854200cfe70d8542004fd70d854200cfc70d85424b6bf40d85420057f75585421757c75585420067f65585420067c65585420076d5258542166f4615854200cfe76d81420067
  | 20 => 0x1957e74585521957c74585520073c74585521953c74585520067f64585520067e64585520067d64585520067c64585520057f735855218d7e735855218d7c73585520067f63585520067e63585520067d63585520067c63585521257f72585520076f725855252d6f72585521267f62585520d76f62585521276e42585521857f71585520077761585521867e61585521867c61585521877461585521877641585520057f705855217d7e705855217d7c70585520067e60585520067c605855217d7e76d81521957e74d81520057d74d81521957c74d81520067e64d81520067c64d815218d7e73d81520057d73d815218d7c73d81520067f63d81520067d63d81520357f72d815201d7e72d81520357d72d815201d7c72d815261e7f62d81526276f62d815261f6e42d81521857e71d81520057d71d81521857c71d81520067f61d81520067d61d815217d7d70d815217e7e60d815217f7a60d815217e7c60d815217f7a20d815261f7920d815217d7f76581520057f74581521957e74581521957c74581520067e64581520067c64581520057f735815218d7e735815218d7c73581520067f63581520067d635815260d7f72581520076f72581526156f725815260e7f62581520776f625815260f6e42581520057f71581521857e71581521857c71581520067f61581520067d615815217d7f70581520077b605815217e7e605815217e7c605815217f78605815217f7a40581526057e76d95421767e76d95420347e76d954202d7e74d954202d7c74d95420067e63d95420067c63d95425ff3f43d954202d7f72d95425ff6f72d954202d7d72d95425f76c72d95425ff6f42d95425f73e42d95425f73c42d95425f76c42d95420057d71d95420067e61d95420067c61d95425ff3f41d95425f76f21d95420067e60d95420067c60d95425ff3f40d95425f67f74d95425fe7e74d95425f67d74d95425f67c74d95420067f73d95420067e73d95420067d73d95420067c73d95425fe7f43d95425fe7e43d95425fe7d43d95425fe7c43d95425f67f72d954202c7f72d95425f67e72d95425f67d72d954202c7d72d95425f67c72d95425f67f42d95425f67e42d95425f67d42d95425f67c42d95425f67f32d95425f67e32d95425f67d32d95425f67c32d95420067f71d95420067e71d95420067d71d95420047d71d95420067c71d95425fe7f41d95425fe7e41d95425fe7d41d95425fe7c41d95420067f31d95420067e31d95420067c31d95425f67f21d95425f67e21d95425f67d21d95425f67c21d95420067f70d95420067e70d95420067d70d95420067c70d95425fe7f40d95425fe7e40d95425fe7d40d95425fe7c40d95420067f30d95420067e30d95420067c30d95425f67f20d95425f67e20d95425f67d20d95425f67c20d95420067f10d
  | 21 => 0xe63d8d5218e7c63d8d520357f72d8d5201d7e72d8d520357d72d8d5201d7c72d8d526467f62d8d526576f62d8d526476e42d8d526475f32d8d526475d32d8d521857e71d8d520057d71d8d521857c71d8d5217d7e70d8d520057d70d8d5217d7c70d8d5264d7f7658d520057f7458d521957e7458d521957c7458d520067e6458d520067c6458d526457f7358d520075f6358d5218e7e6358d5218e7c6358d5218f5c6358d5218f5e4358d526357f7258d520076f7258d5263d6f7258d526367f6258d521576f6258d526376e4258d520057f7158d521857e7158d521857c7158d520057f7058d5217d7e7058d5217d7c7058d520057f7650d520067f7650d520047f7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d525a57f7450d520073f6450d5202e7e6450d5202e7c6450d521973c6450d5202e3c6450d5259d7f7350d5218f5e6350d520075d6350d521975f4350d5218f3e4350d5218f3c4350d5218f5c4350d521ad7f7250d5201d7e7250d5201d7c7250d521ae7f6250d521b76f6250d521af3f4250d521af6e4250d521af5f3250d520057f7150d521857e7150d521857c7150d521973f4150d5218f5f3150d520057f7050d5217d7e7050d5217d7c7050d521973f4050d5262f5e3050d5218f5c3050d521857e76d85521957e74d85520057d74d85521957c74d85520067f64d85520067e64d85520067d64d85520067c64d855218d7e73d85520057d73d855218d7c73d85520067f63d85520067e63d85520067d63d85520067c63d85520357f72d855201d7e72d85520357d72d855201d7c72d855244e7f62d855251f6f62d855244f6e42d85521857d71d85521867e61d85521877661d85521867c61d85521877621d855244f7521d855217d7e70d85520057d70d855217d7c70d85520067e60d85520067c60d85520067f74d85520067e74d855202c7e74d85520067d74d85520067c74d855202c7c74d85520067f73d85520067e73d85520067d73d85520067c73d85520067f43d85520067e43d85520067d43d85520067c43d855244e7f72d85521867d72d85520347d72d855244e7f42d855244e7e42d855244e6e42d855244e7d42d855244e7c42d855244e7f32d855244e7e32d855244e7d32d855244e7c32d85521867f41d85521867e41d85521867c41d85521867f31d85521867e31d85521867c31d85521867f21d85521867e21d85521867621d85521867c21d85520067f70d85520067e70d85520067d70d85520067c70d85520067f40d85520067e40d85520067c40d85520067f30d85520067e30d85520067c30d855244e7f20d855244e7e20d855244e7d20d855244e7c20d85521867f10d85521867e10d85521867c10d85521857f76585520057f74585520073f74585520053f7458552
  | 22 => 0x89435e73c54d89431aeee62d8943004ff75d89430067f75d8943034fe75d8943004fd75d8943034fc75d89430067c75d89430347c75d8943024fd74d89435e67e54d89435e67c54d894302cfd73d89431ae7f52d89431aeee42d89431aeee32d8943014fe71d8943004fd71d8943014fc71d89430067f51d89435e6bf41d89435aedf31d894300cfe70d8943004fd70d894300cfc70d89435e6bf40d89430057f75589431b57c75589430067f65589430067c655894314f3c54589431aeec6258943014fe76d85431b57c75d85430067f65d85430067c65d85434d73c54d85431a6f661d8543004ff75d85430067f75d8543034fe75d8543004fd75d8543034fc75d85430067c75d85430347c75d8543024fd74d85434d67e54d85434d67c54d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85430067f52d85434d6bf42d8543486df32d85431a67f51d85431a6f641d85431a6f631d854300cfe70d8543004fd70d854300cfc70d85434d6bf40d85430057f75585431b57c75585430067f65585430067c65585430ef3c54585431a6f4615854300cfe76d81430067f65d81430067c65d81433af3c54d8143025de73d814302ddd73d814319efa60d814319fda30d8143004ff75d8143034fe75d8143004fd75d8143034fc75d8143024fd74d8143006bf54d81433ae7e54d81433ae7c54d81433aebc54d81433ae3c54d814302cfd73d814319edd73d814302cdd73d814301cfe72d8143004fd72d814301cfc72d81430067f52d81433aebf42d8143346df32d8143014fe71d8143004fd71d8143014fc71d81430067f51d81433aebf41d8143346df31d814319efa40d814319ede30d814319efa30d814319edc30d81430057f75581431b57c75581430067f65581430067c655814308f3c545814319ef8605814319fd830581436057e76d915202c7e76d91526657d74d91521967e64d91521973e64d91521967c64d915218d7e73d91520057d73d915218d7c73d91521973f43d91520357f72d915267f6f72d915201d7e72d91520357d72d915201d7c72d91526767f62d915267f6f62d91526773f42d91526776e42d91526773d42d91521857e71d91520057d71d91521857c71d91520073e41d91521973c41d915217d7e70d91520057d70d915217d7c70d91521973f40d91525f57f76591526757f74591520073f64591521967e64591521967c64591521973c64591520057f735915218d7e735915218d7c73591526657f72591520076f725915266d6f72591526667f62591521776f62591526676e42591520057f71591521857e71591521857c71591520057f705915217d7e705915217d7c705915265d7e76d8d521957e74d8d520057d74d8d521957c74d8d520067e64d8d520067c64d8d526357d73d8d5218e7e63d8d5218f5
  | 23 => 0x400200a0000000010017004800c00c00c002000400a0030020000000000005801c0060070020004000010000000c008015007800c00a0000008000000000000000c000000000000c02c008001000000400c003000800200d003800400600000380280000000000014000000004001000a007000000000e00d001000000000000a000000800000200280000030000000000001001000000a00000b800000e0040028010004007000000000400300100100000010000000002006001001400a000008000400000400580d4002007000000402c002006000400200200000040000030018004004003001000000000000000000060040000024004000000000001600100e80480040000018004034016001002001c01a002802c000004000003800c002000005c00000300180180120000000004002000002800000003b0030000008000000002c00000d0000000004000003001800200b00e000000c00000300140040000018038002009010000000c000001009c002001000800000800000780000000060010000000012003000c00400300b803c000001002800400600b0000008000002000000c004004006803000e00000080000040010018000000002001801400400200400000020026957e76d95431b67e76d95430347e76d954302d7e74d954368f3e74d954302d3e74d95436873d74d954302d7c74d954368f5f73d95436875c73d954368f5f43d95436873e43d95436873c43d95436875c43d95430057d72d95430067e62d95430067c62d954368f3f42d95436875f32d95430057d71d95430067e61d95430067c61d954368f3f41d95436875f31d95430067e60d95430067c60d954368f3f40d95430075e30d95436875c30d95436867f74d954368e7e74d954368e3e74d95436867d74d95436863d74d95436867c74d95436867f73d95436867e73d95436867d73d95436867c73d95436867f43d95436867e43d95436867d43d95436867c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d954368e7f42d954368e7e42d954368e7d42d954368e7c42d95436867f32d95436867e32d95436867d32d95436867c32d95430067f71d95430067e71d95430067d71d95430047d71d95430067c71d954368e7f41d954368e7e41d954368e7d41d954368e7c41d95436867f31d95436867e31d95436867d31d95436867c31d95430067f21d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d954368e7f40d954368e7e40d954368e7d40d954368e7c40d95436867f30d95436867e30d95436867d30d95436867c30d95430067f20d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d954301cfe76d89431b57c75d89430067f65d89430067c65d
  | 24 => 0xc000001003801c0040000008018010000005003000a00700200000060090000000000003000000801a000003000c0060020008008016002002000c002001001803c0000070000000000000002001800000a001001000600e000000001c00100080000020000010000004000001001000600300180180140000000044000003001800400001f0008010004000000000c0000030010004000000000800000400000000180040040010000000000009800000a008001800401000200080000020000008004004002000801802a000001000000000100200000040080000000000003000000c00800900000040100000000014006001000001c018002000003c0000030008000000008003800400c000001000c01001800a0018002012002003c00200c0000000026002003000800000d0000008000000005001800600700080000020150000000006002001800000c00000100040040010000000036008000000000e0030000008000001006001800800c000800800c00100a8004002000000000000a00200100040160070020000006000001000001800d006000c006003006800002a00400180040020000020008000001003000400a02a00000000000000000008002002003806c00800100a800000202f007800400a00e0018004006007000001001601e00200040080000020008000015000803c0000210008000038003004802803200a001001401000100000000000010040000016000000800c000000001000003400100280000040000020130002004001000001800400080900040030008010000001003000800000000000000000010038000016003003800000000700500000060080028000000001001004c0000000000038062004000800400001d000800001200000000380040090018008008001000808000000300180040140000000000010001000000c00e0000010004006003000801800800e0080000004003000000c01c00300000100000070068000002039001000800c000007802c00200600000040000030010004002004002800000a000001803c000002000800c000006000000c00a0030018020008002000803c0020020020020010001000001c0060000020010000004000800800a0020038014000000000800000200100000000000020018004014000000000003800900a0000000000004000c0000000008000002005001000000604b0040000012000000004c006001001001c006002001000000000100200000000020028000004001001000000a007002002800a005002001802a006003800c004005003000c00200a006800002800700200000020000020000022001003803400800300100000000030000084010000000002400c016001000000200400000240000000008004012000000000800001200a800c00000
  | 25 => 0x62a084dc94b8d0261200319e9aaad855d9b1a4b644026122ce82061be11834aca26e7765f0001394c7240000000004850000000e3000000027000001640003634000367000000002a5ec75e0169e000000000504736b787303e00000c26593a13c7b6dd700000000000002d78ab80008820002ea4ebeb6613f00000001464480ad48e800037a17e53b40006f20000000d2411c1d91ae0d7d00009fd15c01e000058950ec39000231400000027780000000000000000000a4600019200005b0191a9c0c94000236000000092354e943d906e6a1f5bbdda0c8ca6be2a3c39c1eb43f24c400011e71121bd5aab8c51c2bed4287b85b505154869ec51e29b8ef800015d8838b680000e6bdf000082428db478f8400036980000006ad08b324193c00000022f80da5f400013fc440c705e72cb400000052580010e20007bea43400057039b3229ede5101998000fe63150008000002005000c0040090008000002007002000000e003001002c0000050040000006001000800401a0010040000004010000001c00000e000002800c00000000080060030000010000005007000401c0150010000000006000000004a007007003801200c001800000a0040000018012003001801000a00d0000000000003005803c008005002001801400000100280000040000004012009000000001e000000000c000007000807c000000004000000000500000300060000008000000000000000000c003000001001e0040018000010000001001c010006002000000000f004801002c019002000000200a0010010006015003001c002002000000000a00000100000080060008000008008000001800a0010000000000015002800000400b00980280060000028000002003000000c00200000480540020000000000006002008000000000500180000100070000008002000000801800000b000800c00001400000000180010008008010001000000c00000100000080160050040008002005000800801000c00000140040060018000000002000800000000000000000080010020000000001000003000000000080000000010010040000002000800401200200a0008000001000000001e010000001c0020130010000002000000802c0000000000000002000000801400000300180040000020008018004000000006002800c001800c002011000001400600000480080380000010004006005001001400600000680180040000020000002000000800000c000000000c0000000010004004005000801000a00700080180040060000000020000004801c00001e0000014000008003002c0020000000000010001001000c008000000001c000000000800400e00000300000000010010020002010003800400000400080040000010028054000001004000800200900080
  | 26 => 0x789f300000000000000cd0d39000366c00006e000263ca5800013b924d6000000000000000000414b830704e91000234c00013b0000000000aa40001729db27e36cd0001d480370003850000c2010e11840000003edab75f2a0000003b28000a670003864000b0726d8d5dcfc000283330c00064600012480002f600000000000004bd8000df611d62e11991100003798000184c4d6afa1d40000001672be10e60000000000000e396600001bd68b85b480000000000000000c7c0000000d8800030a6203049d9cc7b09006a8000d0f2299d9c00056e69d0001e8ece51ab00001b200000010898a29a40c7000062800072808ccbb4122017819ce8600057490c4000512454000131059500000000000004880001a5413e00032e000000000000000000006c3a19400023d0003538718dd8194800000000053b00000000756a691fd5b40004308270f540004a40000f40acc000310cd48b406001d5c00030b52d86209c84497d19370ce42fa71ab444dbc328326bb4187c000247918943a4cf0003c04e2ee3b52e2198b3a3c30000a3473219d46c84dd47a50a5c4aac40925d01a2bd6cc7237f28aa4505f85f65ac8e10d04f7f24e93401600956899d351faf8a3a60200ce849c5b283701b0c182019a6173c3463c800003f2bc60002b0919ce584bb36e8376205447a5544aefa073e8350fb2b9003a17e00000007b535481bef8f000254c000efa2f13e5170c95b00000011c20004ee80000000005778001f0c0005e3a1fc87262f2e400009ca879126b9794b094c5f335989f0a337440438000a3f3cd0000d0e52152e98759524d571327d11401f50000000000000572aa8c046102446253ca0a4b41dd8b099b08c21e42c551aeeb91d39b35bac1716181ae817c28562796e9e9cdda20d21683b600042903c9bde1740fb39280003657c10fbc00066e2f580000004c326f36d092eb370000000d720000000001814e5c2fd80000006d7000304c00000000024fcd06b760000f78000cec1de25c0000bf3647b68c000ea8000240000076f5e880000000000000711a944430000e00ad600018c145100453c55b0000000b5b4dd16250e40bb1ac1acde14a246978028ada19a160bc3ce002f9000000000000060f3adc8665f101da320cac6c357619d886839171c1b1400000033489bc00087400029b15d40000000000848bed2eca49c0000004d485b40005ce6798a84e024e200000000004ae01d2990000d220000001c9a0007d6800072af173d180004a2ea300027bc0003cc53100000000000003184bcc6962791c54694ee75fdb2900006b14f6800121200000000000000000000198000b4144300340000000ab00716627971c7b380000000080201d24cc95535217400052b0000000cda44a10a0000ad40000003521af21e300000005003520c69e09e
  | 27 => 0x1fe8851482e14876e7b0000001cae4da25b8000000ef30001e14cba2c60002b00df8c1417f3c08000ee900021113d0b550db841449c54450fbc70252afd7d105ec6f4a7a48e0dd59a49b563a3671bc44b5649b7fd738cca0000000cc891912b09ccf1e9941972519788b575b915555580000de00000000000858a8c0b8000370800000082c00019f927459b00008b8000c03619961ca5a60f7c8000000011b7b40000b52db215b0084fd40000000b200000000001ed5ee81230001f880000002d0800000044156380000003d141b87dd0d28321930001136a830000d347fa0000000000000bb86470cd8000000659af540004e90003b585ba7ed6998c5dce2cb20000a097f014258fb73c00027a36021b400099a002bbe13b6c4e0f28000000bdc7cb8f703e60003d41aa000ec086de23a09920002950000000b6c00022f400057c55d2c3c0000000000000a840000002454e7400000019143dadf548d0cd00000005861f416a08360da36880000002142f6593a0000ae00000000000000000000000046000165c000775385400035b00011a0456a936519589a846f947536a1abc000760000c000d7f00001380000004bc800037a57d114800121e000000000000038b212ae94fb03a30000001c305b300018711fc0354d3175c7803f8000000034a911106b7643669d370226f0c4e00038685d800076b0000000840af000032f0158000479000091609f5260000000ee055f1c7423e02a1cb000195e0000000001a5a0003aa155921800074cb5b40005c600000a0000530318000038a0000e09c480003d9000000139c9360002d34b389e97b2800110e2494581850000b0d00029d0592ec80002b24000741000000043ee80352b524f1891d74e000000000009e0f85ea00000002870000c980001048564e1b00000000d4efe0d60ae9904df308d1cc0000cab0000cfc000000000000000000000026743442c04bf39502120000002f60e7600003597452b0000771ac74000aff6c5a2d80000003d232d8c0a6d542681197549576f800000000000000001e189dc6b7384055026856916ec000e8c310a6a91f2a6537b94003746c8640b06c0000005162b9cc0408f0000000000000149000000000001f800121c00071fbddc0000002d580000000000fa0000caa00042db448fa88576432aac0001df000206c2c200000039e0cc06477a30d641720006a200000000006cb8000000f9d000237dc0e000757ac4000069f5c98000a8c68b00002d000016c00010243e000000000000005a8000000000000000201750321da4748000302cc40678335e3200000000000003e045f80014920000002a20e0800077080000000003ac800145a3cf70004a1b2614422302c5412e9a68e802011c00000000011aca797a537dc000e707160000390495000315ce10cad4
  | 28 => 0x2318f4deb4b60720b6a4d0055945e0658c2274f3a3abcc7feb9a0002de400000000000000000007558001954af47a90a2400000017232f42926fa72490000000006352de8f6c9414592755e2a2372078101060000714a7353ac733664942d53c6854b0029d9fe22f2918000d2eb1837900000003730001b8890ef245b7832da001771d980017ea000301baa93eaab77239bb8000e972948000f4e7b91d9000169680e563242918e3696a31531242f3f2ccbd340008cc000392cc683850001521808965458914860825d62523e10240004cda28c0005ea000006400085567a8000332e9b7431a98f78d16000000000034e4ae1ff07304fe63f34c05947a92faa1a8ef20004b90f68ff46c10000a5000083132e0001dd6d781f530dc00048a4ea000000000005e000000000000000004e2978331a6540000e80002b4d72a58842b000000056324c2f893225d44298000000aa744f8000000ce671f2c0cbf45d2000000059878a000000106a0007638000000000256800130af9a5f234f02e000008085e85182a900000000000001d03b6c68ec8909700013dc28a0000001ac4cfb4703bd40007c000039b4b4443f59182c8a7ea6f2bb2b395bc499143b6ecfe2d3e6e822bdd1a4f91f98eb418a0000001c658c00006fd00014e228f3871bacc740002b38ba11b897c0003659d4275a11a3798000f8e1009a685885ee51b84309580007cc307c0a60000be0001ef443733e13299502192559ed0db4000501185d1da25300000017bedd336200000000001cb8001a0200057438b8558ea231010380000002e49b09230260177000000000056e29fc00076c000000000000000035500000006ef02849880006532985b3000036783b441000038b18c963200034498789124291459594e967ac72d0001b9831129104340000002d880008d69d80000001a42b044ad1179e08bf1000000000075b1da00000000000000001c3e00059d8aadc26c911a8ae847d2925208000000000000002a4cf20000000000000d26000000000034f54000019760002f1b2c01d8a2116f8135df2c4907800011663414aa07e00004544ab00013761d95c72a6ce705780ba80005e07051eb83112e20000000000c1a0004a80000f600004e41159480f410003a558f8e341e6b13198eef658595a17ce0d7509871c00056f26ea535ae40686d8000000000000017c996200040823185b00f47b21bf8d1ab910001ef40000004e5800094a01f00027c0000bca42f9288e5263c52922d49c6c7600000000000000000000000d0b0003b11f36ddf0000000910e550001130c2015361c0001dda000000091800007900011100007697a200000000000000001f489c100005e504200022f8a100000002c9000000057b0002cf4d56000000000000079b1c83dcdbc074e0000ba5128bd603c0001
  | 29 => 0xc1a42e04c4c86000173800043659100014cd70e000028165817e903000031c000c6c666a878948000477a4c0000f813caab45b0872a5d934d80003391060c885108ac15fbec4ff2ba820f9fb8bfe850365b56d2c21ef0001fd087a2b300018d9654b090b51bb194030c373acc000000035dbb95bc600011a80000002d429e8750f3a47b000285400004b4bf80000002e06b48f3984e51873b1d880000892758000b880000dcb38c1fa03900000000007835ed8000000c8c5b10000000d290e60000a92269287000053c0007059edd084c656828000000000168bae069676d00039ccd5ebe90001c2d4c00710003bc0d5400019a800134e0003680000ec60000d48a886e41ae00016b0fb83376a78000c32d202b8a909f3e00000033680f80000000811d0adc121503240000af5962e5c000a8d15a00000002815a9a785c3400050c800021ea823ebaa4153e00000037a8000e3d0000001730e250003a4090854d0000d8400003c000021000000000018fd44eea700034387ea27000006ac0ee6cc4be8cc400000004314dc3d2c2e66d80000001c317a25000000ff31ab1e400057900017557bad3800027ac000e9f0d8bcc000091f7479f2000000000032dc4a42e226c0001dfa7c963ab6f9d3000069d8000bd07c63b294bc6fae0e000000000086e59f395812e0004cb18c4e802d027b00017ae4c70db11948da3250c387458180824969d440860000000000000cf112393a03b89c70001a3861e00000002e0842c32000000000000007a800000018c66a8000b300835ca2ccc0006b00001fd8000c6b40180000000000003b180000f14f1aa39418000000000000000000000005c24d645c80019c20006c5000022a00053411c1dae8c103fac58000eee6bd800000069436e06001c833a3bf274871a7f876d0fd19ba572636a32d250c8500024ec00078060a8000d52ac336500012520516fdb16cb041065e69d207505d61080a3932433e4e80000e1e38e77da724ee6ab306da0a811aec545680004b0da07bf19414f6b132e59239d9677f0000280000a910eb87880000007d48000f285c50ffb72d39ead00003041cc8ad600000014f80007c88989e7600000000000000000002fb0b84000000194c0004d138f3115d9efa80000001c98000000000002c000000068da6e0000002b894ea6661b6000086064e3c599e09be0c141c28e8b00ef2789a38954a1d34260000536b465fe2f2000000033e80005a655b395a97d012e53737280c0000000002fe43aa3e632797f0878709000303deaaa0e104aabc000442000000000000079b8000000000000000035e0fb000000179e0002f6ac7094042d6d88004b1cc662b08c900006a15941de93f29513861900c508f47910000000000273bd200000002f4800003000047b000000036e0770001026279
  | 30 => 0xf000000005600031480000000005ed00017767990000000ec29810003e4c2580a51112a89e3ee1e08a2804dea00033600001c00003480000990000000000000000035f92f02720000000001d08cf400000000000003dfa630de01585f7bb7d04a0007218574e840000003b240007cf20d9445f5e0000003d81b4200000032e4b1e8dd2d72695ee23b70001da800047a022000016c000000320000000074e91213ae0004d18001756b7d0002259552560383a07d702000163b3b80005c1000000000000008c0f2400000017a80000000005f00000edc000000000038093e25395b00000000003044a127840003e94000dfd258ac44f648170001298754f6600000018740000002da060031e000345c0000004b100000000000b406086ccb9623f251c000dbf2238000d4400000037940000000af8000000a8b0000a94000000000002c0000000001d240008050000e71eb80000b3800078200000039f0a6ad7452d00012240006ca8900000000612800000000016580000000000002408cc285800000e0f1cd7100016a9b3cf6900018244c816523a80008700000001570b3e0002f3b6b9b1858c37b09940f688e0003af5c12d070000000000e3611cb594d082be0000000f22000067000055400065a3e59ec20000000000b480003ce0001bdc24475325d558aba243130341b49ff7c483dc996eac00028c5a280e312e3e0c70600000010c8dded0d24f12c0000b514da3b74000d6812f0829540d5374f231180a50d4de8000efa0004ef9f483a01553a93b89bfc2933460ee0e8855e000000077c1890000000da8000788897d0c80927b70a74000cf74f237c8c0c801000000104c00007980000001ca34f12080009a20000000000bff0000000fbe9ab3b88d7cd3a00040b055d54c6591752e083647f75f738c58c8000406b7e465ea2354d20a00e032b3fd94a00000001e9000059e77000000010b24f36fb04e000036a0003b3148e7e00748c69ad6b9d3722fc109c77640a80008380b321ab6d8000bf67318000e48cd04d60000d10d82000327c000a8500010d96dc65251317dc000000508a20ceea0007240038000e75000000058a4800000000fb44b22350f2c328a4522b9d140005640fd36dc0000006b028152168764d0000190e3ee3358000000a0f00002899580000002a299d23af1f68001312a0a7439b99a127880002a612568770c5bab927aeb200ba7116f86163c93871c740000003d2c1a60005a13985a3eb6b63b9de1b20bbd2f088c854097a2e6aa648a01a63880180e361781b7ae900648f56ab08c5b9ce8170688b02a82b95df28a84ec1ec52cbca0e58766610be3473c034600b0a9be21697051599a36bbc78728887c86db6ea3d3c1362245e60000298a4f00000001fce2b55cb5f920240c15e97cd38473100001302c6cd1190800
  | 31 => 0x1e954e659e5e18000a340003f082a800000061e1d7136c0000000000000e920003c0caa20001a83e2c91a0000003af94905542d03b0cbbc8fa0002841832c8b0000000b2858d000329422ec344b985449c08a42550001b900000000001044000000000026a0004d734a00001977410000b7cb262e0000156462442420d046cc3b39f0ec048620f2a52270000f254ef1ba06701a0069204508a00032b91804dae0253b841c0009be0e300008104fa00007980007ad14bbdedf60bcb60b352d71adad768ba2cc1816b32235409a8ee8339896d67e8f700000018526752e78319bb6b8b4e6171c44657e000366400087a0003eb114e44036f80009720006e0066d8a4000113800174600038180000000000000000000898239a2443ba0000001f90000da50000cc03dc0000000000afe0005b180008f00006818de0478e5139f93d000000008236497cac5513e00007428ec2023aa59f40005718154000a964a70b98d1400071200015cc1f22f024c8ec07a100019bc0004d20b70001c100000d200007ee00000000000002670000000a406be2de81bcce2623000000000000000000000009b700018a80003430688f9c19000063c0e284aa00000012e96f66bc00000016280002b9a9a55f4a5340f2db427e00018e8001e980000000000000061000015800000026300000002ec0000000e3e00003e9064242e2057e000000069c0000001e78054577000000000000000000004834c3b7085ac000000000064e72f4b78001350bb971087092943dd57f2d590a84ea262af507b065e79906e0a382131f8bad894219f33bbd45a68c846dc1e79b3ad3f0000000a7c8fc009bc59292e406c3000000000032a00000000000852c80000dd100030fc00000053e9629bc27c17378000eb03ba788000000000050320740000000a793f00000000003638fa65d849c04b40ec000312b0a009479617dbbf0f6200000012684000005af317c00031b5650a6000084a67ca99973eaf54729eb9d62e17378926df4c44b0001821a80ca12d6b5d4bca192420abac95e00070b0bccc2600000000000007d50003460ee80000000194000662000000106600062980c000002563ea301a4a6a76e28448b2086b1fb3468000ac40001b1cc3e0ab7270001cd0000000245889a01b16d004555455052213d41ec820733b319644000729000077a5470002ae000000000026c00000005908001ac8a9700000000003f200000000000007b586d400000020a935c4fa00025c00010740003f5800000000056680000004cd03202580e603646a8000fd24c03703bfca4c2fd74b00004500003c6b02c000933000182da4ec9a007b11892860e03f1c507d808a0003111eb2f6d3d7a8d4aea0095568e8824804742f3265320cfe0002eb504e91e3aa93300000100002b805b27f
  | 32 => 0x7400016d9186a347d50000000000592241c0000001efaff4a9cf066c180000000000188d00ca2ccb0ec0bac762f404170c7c00082300027140003630000b540000000001c180e400020b0000000f20625800000000029b000000089a4648001f0a3200003651a5c3c20000d3000036841d800156092a43e2e0c5da0002ab94c8f9c5ef2c2294484ca2b2732d0c00000013080000000001e2800000037e0000000000b924cbb150bb842719dafad804b020000000018f1a000133800023b052372826caf950d000000013d0000000000b7300027dc000d1c0d4000183a2f2200864054ea172038001d4a4bf62f0000d580002cd00000005975aa1fc8000d5a00014d00000293f804648b2a413e527c80000004cf281d700f122feaa501aa0005e28000604000016b50c000e596c0b621a18a6321f1ef80003f07bb214400072220516e04ea0002e98001e6c05e3e5aee89e2c7a172945c04094b44532d5ea86d800000b01f81fe505800082683e06035a833cc350000501944ce4594864c4343a54733b059be1bf4c30000000000576800000000001380519b84066f38e50000f330000579b1e0000000001ae683f0001bf4eba8bb00014219ac51930d2af513a0c37978000b0cb7f00038bd49496b0000001596000000391400072e39e97f8d1e0004df800143064c6490ca843c0003dd9f948aacce00011f5d26b340003b90f0e4910001adc00000067780000000005f907f5aba73c50030b4000c9472e80000001480000f29e100007cf07840003fc000169c00000000025dd76c0a800000000003136d7a57c000ce80000000000a2943031fcdcaa7e4b68000000df410100018b2abb0000001740622371b7e0d40b4545d0fa00005bc0c536a8000d3200000000000000001bb400000076119c16b8935646800100c0004d7b9b07acd2c628000000000000000000000000000278d920000002629e0a000251800930800058400000001f12bd0f40a1880f711a95545ee060000f95c5a0004c5a3acb4c8970003b50000cd40000000000ed3020aeb13860003bda39c0000000003ead4361270002f098820ca7c389649028aa5b08001e4e00000000018c4000302000000000005bbbb1f3821800000000002450000000000310031000014c00031b80000007c54040000000f4514322a412649020c1a8d9c40006378c652cecc5110a41400000000000000000004b701155e21ea5a48001a8ae01617b42800000009800000005f000000000d200000003ac00000020f2d296be195000000108ee271ae9b642387373a800000008180002e119d6b741bd80001200000001fa000043a489976ce4c8a2319a3edb4c52400004d0c5839232f92cc000c5a00000b9b12ccc1da91bc00000030d83940be00000001b14240007c639a400000066b84c9d2834900000
  | 33 => 0xb99b4e3740000e996147987581c4c664d353570a68f7400049611c47c4000000105000033d0001a496b453973933c05480000000000000211187000173645b405a7f8000cc877a2100f3eb640242278d262263671b75ade31c390063d1a8502611b93d3fa5451f18001208f587788000000000228a58ccce0005570b48000000597b2fc000000335113c81620367c11a580eadb1ea8f11a08cea3753c2cffa88b4ba160c7260005e48dc4eac6150002c3850600000020287482f81c0a54800062e00006180001ad1818684ebc9b84f9bce9e5a00011d1c71b3e2633f78000000c6800026381220000d80000aee6bd58d8e7dbd813327bace4d3615b00030ad7f40006e900751a20002eea9b40000000318725d9a7c7735aedc000a5440d12f40005e459c053856e0005722c0544042b52700001f04450000000000a2e29d82152689e044ca6c9a0400064b8001108000421800015c0000000001a9800067e2764c02dc40683dc9baa65a03d36ac2fced827700000340d6000000000008b00013b1cf2bd01092b5c3f89e243614c5e8600048309ade1ad237329fd5d6af3d00038cdec400055e0000a0e0002069d4d5b0969103be9dc3a472506ad61ebc72579189a821071a4b5009150200013609d0ffc0941ad1f3497c7e6332a4b8a3aad92163560d8c1267c411f0f56e663eb00018ce12a00025088460007948de58e614a000228400034404d0001f5c000070b3d86b800023b13f4000c2c368977c000ba628f2ad00000000001e889769f802daddc00000000025655ee0006da8001982ce75b3800000041139a08180669d110a800075896455a8000f12db90b02b503ace893488abdac2be16de8c15a62f1e49baf0560a000719223571ecfd00000000000006b1acd5092e460d395a4000b995bf3849f42000000134d19a000000000000000000025a0000649000000000000000000018c67d115e3ae8000f5f35b00006906e90002859e36d3d2d2b97c10e17d1840c498840000000000a06b2b029054800000000000000009f117f8000000000000203056200000009285ee14300011dc00000000000000000000000000000376000000000000000000008ba0000751e18000c9b00000000000000003718cb00000003dc0e8c000000079c0005bf51f295800076800003740000a3000196c00041d4f2a4207f2f2600019fd460a957078a5400062600025753ce0001d480017a60005a618004f6c477a9949ce4e000077893c000bbf4f307495820000003c855503b60003018000ed50000b8de68adf6b60000000e424c1260c43a24c425854033000000026c4000d9100000011c600049c86455e499966f3acd82e9800000001d1c3540000001ec614b6ae000000000020280000000000000000c7000041c91b80009b31e32f78000f7924335654ae5
  | 34 => 0xf80002781ea37f00002962a5a7d954232c1a9bd258389c619e000000000000031580008de390a67053883d0000ee59da0001c30001a2ad80095800105a1100002dc5c8801237f80010560004a2039ca08bb53f38000000000088aebd28abb05f1af480000005da12a00007dd467aec47f4ae151d98b482e00043da19d590b3c7b61731f0847966109418e230d6791f10000e5b13712300001660000bc40008933f6334cf86db3455a25400016f13300003f654000013ecb4672811f00007fc00073d0001bd2538477000000000017789680008685a408a80b27a671e0001c0ab4731e919ce640000000b5c0000000000001b8600045a38c016a8812af8000c82000000000000000000032703bc00014fa5b18bac0e1208c248c8042092be6550850146d18281bcb8854606700002913693cf800011312a00001025165448001bb80000000791dbcb4e1211c2992cdc776935e9890ded0b9ad3c98445847832e928613a4683c513f8f782e1b55d75cdcd51918ada20f09278220000000079caa48b160000003844000bea1d70000c766421833d5959e0000ad02f53f65b979c329d0383774c9a224b6ebe80000a99844bf71c488fc0007de2ae8001eea217000000105e36b000154c000000292a3cc30a000526ac5c3d003d07d02640001472a78000b268e44fd2c95aec8a652f082ce6a0005fa2a189c2f2e71b872da8292f1af21c06da79324b3cd460298d701a4889da9245ba860ca867b328f8000ee400068c9364b0a7116bb8000e04b1a0001ac960c2991b82118c96000000000078e1cf61896056e0a39644061049600000012d885c920396bc7400044e2179ad1eceb520acb545f6430776e1a18eee6b51580859e306d60f00eacdf0e286049e04cf60e22549505ce8e2a1b237a06f814d3a50000d700ba02ba6611b09a100029e0110e831aa8001d7e22d777816133e000000000199e86316e21f553880448b8001aceabf29d3a8070eb1e61ea7a80000000000260000d08156b9892bc000535a050000e8a1ce80000003fb00033641cc00000032b80003420979568000b5d46d8000c30a040000ae0000b8a000377514af2a51b127d4e4ebb7a10001d68a2801109c859ada407c91705b60002608000000dac000316049039a6a3a4f116ee7f0000efc00000059b1a541983160000895624bfe0003cb08b400000000015ec00039cbd75e56b321619a64000b441c43d5c00091b0003c1c00000000015605bc3600130000000000449000000083c04e813c65a0006e4800000000075685c91a4c365129c8d35a0005e021e02feba72daa940000552303be4815a9666373
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d859d942440010ff0abb2848801a1f21576509100046fc1aeca1220048dc835d942440071790eb2284880265b21d525091019717322a4a122000e2d6454942440011bf06bb264880023ee01764c9100343f428ec992200087d851d9324400b17d083b264880022f610764c91001c6e43ac699220048ec8758932440015a90ca1a6288013351d9434c5101f78a2a28698a20048f487589314405f8e8eca926288003b1589324c5101263a3b2ea90a203bb34845d521441116cf04baa4288093991897548510006b8382ea90a2003ae482d9121440071e90eb22428800eb92096448510006e9186e690a20018f4865cd21440075c905b1a4288003b18cb634851001c7a43ac690a2003ae48258d21440075cd0db124288002b9219424851000752b228490a2000ae4864c92144001d8ac699242881e31e1db75501103cd9d426eaa022000d7071dd540440756750bb2280883634e1537350110014f840ee6a02203ab388550d4044027d30c6a1a808800a7c20772501100071c2a6c4a0220058f8875894044001c70a8b12808804eb620d62501101863c3b2a4a022009b38845494044061ae0e2a9280880eace215425011000794a9284a0220029f287dc540441afe60a9b8a80880027c21d315011000d7843262a02203ef30544c54044001f228698a80880027c21d21501101df982a242a022000fa14248540440d39b0c7ba2608800a3e219744c1101ce9c2a2e89822013cd8635d130440053e102ba26088012b6a1b634c1100256c41ec498220048f88758930440095b106b1260880c31e1d9524c11018f2c31aa49822000ad8864c93044001d92c49926088006f421d314c110016e843a629822001bd2864c530440037a10c98a6088013b4219314c11000d68432629822004ed3764c53044005ba4ec98a608800b741d9314c110027683b2629822000dd3744c53044001ba2e898a608835bd4951314c1106b7a82a2629822000bd3824c53044001ba6e498a6088003b4d89314c11000768b126298220d5f53524c53044001ea2a498a6088002f460d214c110007e09924298220028f8865d120440053e102ba2408800e3e21d644811001d74412c89022000dd231dcd20440051f10cb9a4088003b28cb634811001c7c43ac69022000ec9634c92044001ba2e698a4088003f04c9314811000df043a429022002de08748520440037c50c90a4088006f8219214811001f70432429022003ee3764852044005bc4ec90a408800b781d9214811001f703b2429022002ce07648520441a9ec50a90a4088003d86152148110006f1ba2429022000de1744852044001dc6c890a4088003b8591214811069fb12a24290220d3f605448520440017c70690a4088002f860d2148110006f1b9a429022000de1734852044001dc6c690a4088003b858d2148110
  | 1 => 0x903b1a4290003b18c763485200147643ac690a4002ae48158d21480055cd0db0a4290002b9219414852000752b228290a4000ae4864c52148001d8ac698a42901e31e1db75501203cd9d426eaa024000d6872dd5404809d6750bb2280903774e153735012001cf4416e6a02404eb388550d4048027d30c6a1a809000e7aa1f72501206e7942a6e4a0240009e8874c940480035d10c9928090157ca1513250120007c4a1a64a0240039e882dc54048001c70a9b0a80900931e1d9515012006d9c422a2a024024d6872545404809d6710aa0a8090003cc5454150120004f443a42a02404ff28544854048001f428290a80901a73618f744c12001c7c432e8982404dd38545d130480279b0c6ba2609000e7a209744c1200256d436c69824001bc8874c93048007b910e9926090006f2a19324c12000de4432649824004ec8864c930480035910c9926090013b2dd9324c12001ee53b2649824003dc8764c93048009d90ec992609000372dd1324c120006e4ba26498240dbf4a544c930481b7e90a89926090002f2e05324c1206d7a5a8a649824000dc932dc530480095b107b0a6090003b24cb614c1201263c3b2a29824025e58635453048001e9264a8a6090002b6219314c120005e4c1a429824000fc13148530480010fb0f3aec8883669d60675d91100343fc3aebb22200087f825d764440a30ff02baec88808e1f60575d911000c7c402e7b22200687f87d4b64440010fb0fa96c88801a1fa1f755911002c3f426eab22200587c84dd564440010fb05baac8880021fe0775591100043ec0eeab22200087e871d564440010fd0fa92c88801a1f21f52591100043fc2ae9b1a200687c855d363440014db042a6c6880029d60454d8d100343f42ee8b1a200087d85dd163440014db042a2c6880029d6045458d100343f42ceca1a200087d859d943440010ff0abb2868801a1f2157650d1000477c12eca1a20038ec825d943440091790eb2286880da8f2156450d1002c6f43ec6a1a2000e1c54d8d43440010ff0aba6c48801a1f21574d891000536c10a9b122000a7581153624400117f08baac4880162f21175589100046fc1aeab1220048dc835d5624400d0fd0bba2c4880021f61774589106862e39ca8b122000c3f74151624400b878e82a2c48834b171cc545891000536c10a8b122000a758115162440091bd0fb9ac4880031795373589100062e2a6e6b122000c5f52dcd62440018baa5b9ac48800317d4773589100062ea8ee6b1220018fa87dc162440019b0e7b82c4880029b60a76549100051fc22eca922032a3c845d952440014bf06bb2a4880c69720d765491000537c12eca92200087e87d9152440010fb0fb22a4880270f1d364549100043fc3ac8a92200087c8759152440014df04b1aa48800e9b20963549100343f42ceca122000
  | 2 => 0x1525093000716b22a4a1260b7f4830549424c0cf9b0e1b22649800e3721d644c93070f0e2a2c89926003acc82591324c0679b0e0b22649800676203714c93000ced43ee099260058be84dd7614c00117b09baec2980021fe1574d85300343e42ae9b0a6005c3e74153614c00187ae82a6c2980029b60854d85300053ac08a9b0a6000a7581d4b614c04d47d093b2a2980028f61276545300053ac0ceca8a6000a77815d9514c0010fd0fb22a2980021f61f64545307072c186c8a8a600087f87591514c0010f90eb22a2980470f1d1645453053f2c182c8a8a6000d5830dc9514c0474b90c992a29808ed620132545300343f42ceca0a600087d859d9414c001ab061baa829800a2f21d64505300061e3aac8a0a6098e9830591414c0232e90ea8a829809b8d99151505300071ab22a2a0a6092f5030545414c0cf9b0e1b22629800a3721d644c5306ff0e2a2c898a6002ad481591314c0679b0e0b22629800676203724c53017e2e3b2a498a602fd5870549314c0033b50fb82629801a1fa1776485300043ec2eec90a6000cd830dd9214c00d0fd0a3b242980021f614764853002c5f420ec90a60008bd841d9214c0019b0603b242980464f2117548530006ac182ea90a60018dc865cd214c0033b100b9a42980021f61e75d91206f536c14ebb22400687f875d7644807f0ff04baec8900be1f60975d91200043fc0aebb22400687f87d4764480010fb0fa8ec89001a1fa1f75591200043fc16eab22400087d82dd564480010fb03baac8900021fa1c75591200043f43ea2b22400687c87d4564480010ff0aba6c69001a1f21574d8d2000536c10a9b1a4000a7581153634800d0fd0bba2c6900021f6177458d2000536c10a8b1a4000a7581151634800d0fd0b3b286900021f6167650d200043fc2aeca1a400687c855d943480011ef02bb2869000a3d2057650d200245e43ac8a1a4036a3c85591434800b1bd0fb1a8690003871536350d2000566432869924004ccc7650d32480abe18a8a1a64900021fe1574d85200343e42ae9b0a4000a6d8215361480014eb022a6c2900029d60676545200051fc22eca8a4026a3c845d951480014bf06bb2a2900969720d76545200053bc0aeca8a400087e87d9151480010fb0fb22a2900370f1d364545200043fc3ac8a8a400087c8759151480014ef02b1aa29000a9d205635452011d3643264a8a400687e859d941480010fb0b3b2829000a2f21d645052006cba43aa2a0a4026e36645454148001c6ac8a8a829001a1fa14764c5200043ec28ec98a40058be841d9314800117b083b2629000a3721d634c520186363b2ea90a404fb2c845d521481136cf02baa42900c3991857548520006b4382ea90a4002ae481d9121480051d90eb22429000ab92056448520006e5186e690a40018ec865cd21480055c
  | 3 => 0x6a8a8000c3c7650d515014fe3060a1aa2a00021fa1b725454002c9e426e4a8a800087c87d8951500012790ea12a2a008e8f21942545401353c432e0a8a8000d38745c151501dd6e702b82a2a03b64fa1f75505404e61e3b6eaa0a80ec93e87d9541500ef878edb2a82a00066ea0373505400061e3aec6a0a8005ab980d8d41500292790bb9282a00024f21d525054017e1e3b2a4a0a8014d3787545415000b66d0ea8a82a0016cd21d51505401369a43aa2a0a8005934875454150001c6f0ca8a82a0002cda1951505400059a432a2a0a8000e34865454150005c6eeca8a82a000b8d1d951505400071bb1aa2a0a8000b37825454150001c6ec4a8a82a024bcca01515054000798c02a2a0a8092f30705454150095c6ec0a8a82a009bccd81515054075f99982a2a0a8092f30305454150125e6440a8a82a00034e1d7705054000798a8ee0a0a800687e85dd931500010fb0bbb262a00062f219744c5400a49e42ae898a808de1c6550d3150067b30e0a1a62a00163ea1b704c5400069c2a6e098a800687e85dd921500010fb0bbb242a00030f15376485400343e42cec90a800687e851d921500010fb0a3b242a00030f15076485400246f418ec90a80008dd831d921500010f90cbaa42a00164f21175485400043fc3eca90a800087d87d9521500014db05b2a42a00029d60765485400073210eca90a80018bc865d121500292790aba242a00034b5d542485400069abaa8290a8000d58305d7644c0010fb0f3aec898003960c275d91300343fc3aebb226000e58305d7644c0010ff04baec8980021fe0575d91300343fc3ea5b22600087d87d4b644c1d5cb061a96c89801a1fe1f51d91300043ec3ea3b2260e9e5830d47644c001ab061baac89801a1fa1f75591300072c186eab226000c3e84dd5644c00187b09baac8980021f60b75591300043ec0eeab22600087e871d5644c001cb0603aac8980028fa1774591307474c186e8b2260008be87d51644c02347d0baa2c89839fa60c354591307370e2a6e6b22600087e87d49644c00d0f90fa92c8980468f213525913072f2c186a4b22600087e87d45644c00d0f90fa8ac8980468f21351591307272c186a2b2260e3e3854dc1644c0675b507b82c8980162fa1375d89300045ec26ebb12600087f855d3624c00d0f90aba6c4980170f9d054d89300061eba0a9b126000a6d82153624c0014eb022a6c4980029b60b51d89301951f424eca926000a3d849d9524c0014db053b2a4980029be0976549300043f43ec8a92600087d87d91524c1c5cb061b22a4980021fe1d64549300043e43ac8a926011c3c74591524c18bcb060b22a498003560c371549300343f42ceca12600087d859d9424c001ab061baa849800e2f21d64509300061e3aac8a1260bae9830591424c0232d90ea9284980cb8b99
  | 4 => 0x3501e7e3061b2a86a0003871976350d400a49e42ee4a1a801493c85dc54350001a70ebb8286a00cee6a0f7050d4000c5ec26ebb128073a3e84dd762500014db05baec4a00029b60875d89400043fc2ae7b12800687c855cf625006d878eaa1ec4a00021fe1571d89400343e42ae3b12800087e87d4762500010fd0fb2ac4a00021fa1c65589400043f434eca928000a6d829d9525000187d093b2a4a00030f612765494000636c14eca928000c6e429d952500018da853b2a4a00021f606765494000537c12eca92800587e841d9525000b0f9083b2a4a00030fd0c76549400343fc10eca92800687d821d9525000187e843b2a4a00031b90876549400061ea10eca928000c6d421d952500010fb023b2a4a00031ea0076549400063cc00eca928000c7a201d952500018f2403b2a4a00164fa1f745494017d1f436e8a928076c3c74d8d52500654f301b1aa4a00024f21d435494017d1e43286a928000c3c7650d525018be3060a1aa4a00021fa1b715494002c9e426e2a928032a78865c15250001a70e8b82a4a03cadae09705494078c9f43eeaa1280bec3c76dd542501e127d0fb2a84a01df0f1db655094000cdd406e6a128000c3c75d8d425000b57301b1a84a00534be1d525094002d9743aa4a128005b2c875494250065a590ea9284a00164b21d525094000717c32a4a128000b2e8654942500016590ca9284a00038b219525094001f17bb2a4a128003e2c765494250001c5ec6a9284a0002cbe0552509405bf95402a4a128000f2980549425016fe50e0a9284a01738bd81525094019795b02a4a1280eff2b30549425016fe5060a9284a02dfca84152509400a49e42ee2a128000d3875dc14250001e52a5b8284a001a1fa17764c9400043ec2eec99280018bc865d132500292790aba264a02cb87195434c94019ecc3828699280058fa86dc13250001a70a9b8264a00062f61375d85403751f426ebb0a8000a7581dd761500014eb023aec2a00021fe1573d85400343e42ae7b0a8036c3c7550f61500010ff0ab96c2a001a1f21572d85400043f43ea5b0a800087c8754b6150001c5aa4a16c2a001a1fa1b75585403bc3e436eab0a800593e84dd561500010fd0fb2ac2a00021fa1c65585400043f434eca8a8000a75819d9515000187d093b2a2a00030f61276545400043ec14eca8a8000c75819d951500018ec833b2a2a00031d50676545400053bc0aeca8a800587e841d9515000b0f9083b2a2a00030fd0c76545400043ec10eca8a800687f811d9515000d0fb023b2a2a00030fd0476545400063b208eca8a8000c3d411d951500018ea823b2a2a00031ea0076545400063cc00eca8a8000c7a101d951500018f2203b2a2a00164fa1f745454011d1f436e8a8a8076c3c74d8d515004d4f301b1aa2a00024f21d435454011d1e4328
  | 5 => 0x8162f21175d81210343fc3aebb024200a3c845d7604840187f08baec0908161f21175d81210061e422ebb02420583c845d760485110ff04baec0908c21f60975d812144c3fc0aebb02422487d815d760484010ff0aba6c09081a1f21574d812102c3fc3ca9b02420087d87953604840b0ff0e2a6c0908021f61c54d812102e1e3a0a9b024200a6d8215360484014eb022a6c090803b14c931d81210076499661b024200ed131cc360484018b8e732ac0908028f21165581210062e39acab024200c5e65dcd60484018bacbb9ac09080371087735812102c9f422e5b2a801487d8718b65500014bd06316caa00029760c62d954000636b90c5b2a8000a768118b65500014eb02316caa00164fa1171d95400a43ec38c3b2a8000a5e8318765500014bb0630ecaa00029ba0861d954000536c10c3b2a8000c757118765500f3a74e9986caa01e28fa1373d95403bd1ec26e7b2a8077a7a80dcf65500f14f301b9ecaa00030f9d173d95403c51f420e7b2a8077a3d841cf65500f147d09b96caa01de8f61372d95400061eba6e5b2a8000c3d745cb655000b0fd08b96caa00161f21172d95400043fc0ae5b2a8078a3e841cb65500ef47b08396caa000297a0c72d95400052ec18e5b2a8000a76811cb65500014eb02396caa01de9ea0072d95403c53cc00e5b2a800087e878cb65500010fb0f196caa00021fa1c32d95400043ec3865b2a8078a3e840cb655000147b08196caa00029da0432d95400053ac0865b2a8077a7a800cb65500014f300196caa01e28fa1371d95403bd1ec26e3b2a8000c3d74dc7655000187ae8b8ecaa00161fa1171d954002c3e422e3b2a800087f825c765500f147d0838ecaa01de8f61071d95400052f418e3b2a8000a5d831c765500014dd0438ecaa00029b60871d95403bd3d400e3b2a8078a79801c765500010fd0f18ecaa00021f61e31d95400043f43863b2a800087d870c765500f147d0818ecaa00028f61031d95400053741063b2a8000a6d820c765500ef4f50018ecaa00029e60031d95400043f43e43b2a800087d87c8765500018dae590ecaa00021fa1e21d95400043ec3c43b2a8000c757188765500010fd0e10ecaa00021f61c21d95403c51f42043b2a8000a3d8408765500014bd0610ecaa00029760c21d95403bd3d40043b2a8000a798008765500f18f2e1b2ec6a03d30f1d065d8d407a63cb80cbb1a80018bd84dd76350001878a9baec6a00163e60375d8d400245e422ebb1a8076a3e85d53635000b972e1aa6c6a01da8f21352d8d407de3cb86a5b1a8076a3c84d4763501f58f2e1a8ec6a00021fa1f6558d4079f2c186cab1a800087e8719563501f3cb06032ac6a03e24fa1f7550d407bd1f436eaa1a80d0c3c76dd543501ede3061baa86a03d64fa1f6550d407a51f436caa1a8077c3c76d954
  | 6 => 0x86b238acaa124200c6f87595424840b4d90eb2a84908031b21d655092102c3643acaa124200e2f84595424840b4dd08b2a84908169b211655092100716422caa124224c6f745954248449c5ee8b2a84908038bd0d655092144d37c0acaa124200e67815954248571c5e82b2a8490ae39990565509215c716a0acaa124200e2f405954248401c5acbb22849080a79207735092100716b2a86a1242029e687dc542484053c903b8284908c31b1d9654c9213ed96422ca9924200e4c6359532485136cf02b2a64908c3591c5654c921014f240ee899242028ec865d132484053c902ba26490802b3219434c9213ef862a28699242029e687dc532484053c903b82649080378c43704c9214ee3a3b6eaa0a4200d6472dd541484332e90eb2a82908931d1d965505210cd9a422caa0a4288b67825954148449ac8e4b2a82908031de1d655052102d3a43acaa0a4200c7487595414840b0e90eb2a82908038de11655052102d3b422caa0a4205a74845954148401c6908b2a82908c31ddd165505211871bba2caa0a4200e374359541485114ef04b2a829080399e09655052149f1ba12caa0a4293e66425954148527c6a84b2a82908039950965505210071ba02caa0a4200e3565d9141484073c905b9a82908038d595435052101cf343ee4a0a4202ba4875094148407b490ea12829080a6921d4250521015d343284a0a4202ba486509414840bd490ca128290817a9dd9425052101ed33b284a0a4203da476509414840bd48eca128290803c9e1542505217f79242a84a0a4200f277550941485fde48eaa128290bfba9d9542505217f79332a84a0a42feea5655094148401e4acaa128290803895954250521005d3c1a84a0a4200da773509414840174f00a1282908027921d3250521005d2c2264a0a4200f85434c941484073c905b8282908036950b70505211263a3b2ca98a427ab34845953148401ca8c6b2a6290a22d9e09654c521126b2392ca98a42039e482dd131484071e90cba2629080e79209744c5210056a4328698a427af145450d31484073cd0fb9262908027921d424c521006d2ba28498a4200f854350931484057890e992629080f7121d324c521014e243a6498a4202bc6864c931484057890c9926290813b1219324c52102763bb26498a4203dc6764c93148407b88ec9926290813b11d9324c5217efa332a6498a4200f45654c9314840178f089926290802f1611324c521006e3ba26498a4200dc5744c931485f9e8ca89926290bf3d1151324c521005e3c026498a42039e482dc13148401b8a65b82629080378c83704c5210343fc32ebb02423087d865d7604843327908baec090a225be0975d812144cbbc0aebb024200d64215d760484010fb0f32ec0908021fe1d65d81210051e422cbb02420087d879d7604840117f08baec09
  | 7 => 0x7d870c1654840147d08182ca908028f61030595218261e3a060b2a4224a6e820c165484014db04182ca908c29da0430595210053ac0860b2a428896f825d764485132ef02baec8908035908575d91210043ec3ccbb224219a3c8499764486054db0532ec890c069d60665d91210043fc3acbb224219a3c845976448607cc842b2ec8908021f61e75d912181536c14ebb224301a75819d7644840d0ff0ebaec8908030fe1175d91210061e422ebb22428887f825d764484610fb04baec890a261fe0575d91211243ec0aebb224219a3e85d536448401878a8b9ec8908023ee0173d912100c7c402e7b224200c3c545c364484011bf06b86c8908123720d70d9121006b210eeab22421987e87995644840b0f90f32ac8908668fa12655912180536c14cab2242ffa7581995644840b0fd0eb2ac8908661f21d65591210cd1e422cab2242b8e6421595644840d0fd0fbaac8908021fe0b75591210043ec16eab22420087f81dd564484010fb03baac8908022fe1175591210043f438eab224200c3c75dd1644843327908baec690a225be0975d8d2144cbbc0aebb1a4200d64215d763484010fb0f32ec6908021fe1d65d8d210051e422cbb1a420087d879d7634840117f08baec6908162f21175d8d210343fc3aebb1a4200a3c845d7634840187f08baec6908161f21175d8d210061e422ebb1a420583c845d763485110ff04baec6908c21f60975d8d2144c3fc0aebb1a422487d815d763484010ff0aba6c69081a1f21574d8d2102c3fc3ca9b1a420087d87953634840b0ff0e2a6c6908021f61c54d8d2102e1e3a0a9b1a4200a6d8215363484014eb022a6c6908031e1c26558d210051e422cab1a4200c787059563484018f4cbb82c6908031e5977058d21006f010ee0b1a42008bf845d5634840b17908baac6908023ee017558d2100c7c402eab1a420687e85dd163484010fb0bba2c6909df1e1c25458d210061fba0a8b1a4205c3c7415163484014db042a2c6908029d6045458d213ce3c380a8b1a42018fa87dc163484018f4a9b82c6908031e1537058d210063da96e0b1a4200c7952dc163484018f6a3b82c6908031e5477058d210066db98e0b1a420687c85dd9434840d0fd0b3b286908021f6167650d210061e2a4eca1a420087f855d9434840d0f90abb286908023ee017650d2100c7c402eca1a420687e851d943484010fb0a3b286908030f1507650d2100c7d400eca1a42008f9801d943484010fb0dbaa86908025b60b7550d21004bac0eeaa1a4200d6421dd543484010fd0eb2a86908021f21d6550d2102d1e422caa1a42048bc87591434846d4790ab2286908163721d6350d210070e2a2c6a1a4233ad88058d434857f8d8edbaa8490803591c775509210ccb643acaa124230c6c76595424843365908b2a8490a26d9e0565509211
  | 8 => 0x42a6c0988029d60454d81310076499641b02621993e87dd1654840187eedba2ca90803c908774595210061fbb0e8b2a4200f24211d1654840b878e9322ca90ae29b60a645952149d3ac0cc8b2a4205c3c7419165484014bd06322ca908029760c64595210053d400c8b2a4200a79801916548401878e931aca908028fa1063595210051ec20c6b2a4200c3c7418d65484014f50031aca908029e600635952100697ba6e4b2a4200d2c74dc96548401a6ee9b8aca908034d1d37159521185b3416e2b2a4200d6772dc56548401878e9302ca908028fa1060595210051ec20c0b2a4200c3c7418165484014bd06302ca908029760c605952102c3f43ee8b2a420583e87dd16548401c5f05ba2ca908038b20b74595210061fb96e8b2a4200e3781dd16548401c6903ba2ca908030fdc774595210051f424e8b2a4200a6d829d165484014eb033a2ca908029be0974595210053bc0ae8b2a4205c3e741d1654840187ae83a2ca9080297a0c74595210052ec18e8b2a4200a7a801d165484014f3003a2ca908028fa1c74595210061f438e8b2a4200e1e831d16548401c3b063a2ca908038ba08745952100716c10e8b2a4200c3f721d16548401c6d023a2ca908038d60474595210061fb88e8b2a4200e3a801d16548401c73003a2ca908030f1d373595210051f424e6b2a4200a3d849cd6548401878e939aca908029b60a73595210053ac0ce6b2a4200a3f845cd654840147908b9aca908030f1d1735952100537c12e6b2a4200a77815cd65484014f700b9aca908029e20173595210061e3a0e6b2a4205c3c74d0d65484494dd05a1aca908029b60b43595211853b40e86b2a4200a7581d0d65484014f501a1aca908029e60343595210043f43c86b2a420087d8790d654840b878e921aca908170f1d043595211253741086b2a4200a6d8210d65484614ed0221aca908029d60443595214463743ee4b2a4200a6d84dc96548401c5ee9b92ca908038b1d3725952183637b8ee4b2a4306e6641dc965484618ed0fb8aca908029d61371595210071bba6e2b2a4200e3474dc5654860b8eee5b8aca9080399dcb715952182f33216e2b2a4200c3c74dc1654840147d09382ca908028f61270595210061e3a4e0b2a4200a6d829c165484014eb03382ca908028fe1170595210051e422e0b2a4200c3c745c165484014bf06b82ca908029720d705952100537c12e0b2a4200a77815c16548401878e8382ca908170f1d340595210052f41e80b2a4200a5d83d0165484494dd05a02ca908029b60b40595211853b40e80b2a4200a7581d0165484010fd0f202ca908021f61e405952102e1e3a480b2a4205c3c7410165484494dd04202ca908029b60840595211853b40880b2a4200a758110165484eb878e9982ca909db0f1d230595210043f43860b2a42008
  | 9 => 0x43545410078ab9a86a8a8200f176350d5150529e28c6a1aa2a0802cde0943545414a78b99286a8a8200b378050d5150619e2c60a1aa2a0a53c50c1435454152e3a3b6e4a8a8226b3484dc95150401a6ee9b92a2a08034d1d3725454185cbb436e4a8a8200d3784dc9515040b2ed09b92a2a08165d21372545410069a426e4a8a8288c7764dc95150511a6ec9b92a2a08034dd0f72545410069aa1ee4a8a823097582dc95150527a6e85b92a2a08034dd0372545410053bc32e4a8a8226a74865c951504358e8ecb92a2a0802cde1172545411359a422e4a8a8200d37745c95150401a68e8b92a2a0a5e5d21f62545414be3a3b6c4a8a82009778758951504452e90eb12a2a08671d1d9625454142d9bc22c4a8a82ffe64625895150401a6f0ea12a2a0802cda1d42545410059a43a84a8a8200d3487509515040566d0ca12a2a080acd219425454102e9b3b284a8a8205d3476509515040166f06a12a2a0a12cde09425454113793c1284a8a82ffd37725095150527e4ce4a12a2a0803c95c9425454100793b1284a8a8293f2462509515040166f00a12a2a08a71d1d932545411359b42264a8a8200b35844c95150401e2a86992a2a0a8b1d1db70545411359a426e0a8a8200a77865c1515044d4e90cb82a2a082b1d1d970545410059bc22e0a8a8226b34845c151505db878e832ec0a09b69d21951d814100c5e422ebb028204c9e7350f6050401c5aa4a16c0a081a1fa1b75581414e43e436eab02820087e87d9560504010fd0e32ac0a088a5d21d515814104d3a432a2b02824bd37745456050525ce0c0a8ac0a08021f61e75d91318553ac0cebb22620687f875d7644c4010ff04baec898c261fe0575d913112c3ec0aebb22620687f87d4b644c4010fb0fa96c8988123720d70d91310343f43eeab22620087d82dd5644c4010ff03baac8988021f60775591310043f438eab22620087e87d49644c40d0f90fa92c898b47171db7550d316958f426eaa1a6200d5471dd5434c51b63d0bb22869880a752077250d31014eb43ee2a1a6308f1454dc5434c60fa38a9b82869880a752077050d310043fc2ae9b12620687c855d3624c4014db042a6c4988029d60454d89310070e2a287b126200a6d829d9524c40147f08bb2a4988ca8f211765493100537c12eca926200a7b805d9524c45f4f100bb2a4988021fa1f64549310043ec3ec8a92621dc3c74d91524c4010ff0eb22a4988021f21d64549311852e43286a92621dd1c7450d524c4616a902a1aa49881a1fa1676509310043ec2ceca1262038bc87591424c51ba38eaa1a84988765b21d525093119717322a4a126200e2d64549424c401e1a86a92849880a37219744c931014ea40ae899262038dc87591324c40759904b22649880374c43704c9310043fc2ae9b02620687c855d3604c4014db
  | 10 => 0xb2a8200a7a801cb65504014f300396caa08021fa1e32d95410043ec3c65b2a820087e870cb65504010fb0e196caa0a768fa1032d95410051ec2065b2a829ca76810cb65504014eb02196caa08029ea0032d95410053cc0065b2a829da3e841c3655053947b08386caa08021fa1c30d95410043ec3861b2a829da3e840c3655040147b08186caa08029ba0830d954100536c1061b2a829ca76810c365504014eb02186caa08021fa1f20d95410043ec3e41b2a820087e8708365504010fb0e106caa0a768fa1020d95410051ec2041b2a8200a5e8308365504014bb06106caa0a729da0420d95410053ac0841b2a82edc3c7419763504010fd0fb2ac6a08021fa1c6558d418851f436eaa1a82d0c3c76dd543505db47d0db2a86a0a730f1db6550d410070e32ec6a1a8200c3c65dc1435040b33b07b8286a08029b60b75d894100536c10ebb128297a75811d762504010ff0ab9ec4a081a1f21573d89411b61e3aa87b12820087f855c3625040d0f90ab86c4a08021fa1f65589410043f438cab12830fc3f7419562504010fd0d3b2a4a08029b60a765494100636c14eca928200c6e429d952504018da853b2a4a08161f60676549410051fc22eca928200a6f825d9525040187e863b2a4a081a1fe0876549410343ec10eca928200c3f421d952504018dc843b2a4a08030f508765494100636a10eca92820587f811d952504018ed023b2a4a08161f60476549410063ac08eca928200c3e411d95250401878823b2a4a08031d88476549410063a908eca928200c3f401d952504614790ca1aa4a08030f1d943549411953a432e2a92830eb67825c5525057d878edbaa84a0a730f1db655094102d9743aa4a128205b2c875494250401c5f0ca9284a0802cba19525094100596432a4a128200e2c865494250407c5eeca9284a080f8b1d9525094100717b1aa4a128300b2f815494250571e4d02a9284a0803c960552509415c79238aa4a128286e2f615494250465e4ec2a9284a0803c954b71509410343f42eec992820087d85dd932504051790cba264a0acb87195434c9414f59b43ee8a8a8226d3687dd1515040566d0dba2a2a080acd21b74545411369b3b6e8a8a8226d3476dd1515040166b07ba2a2a0802cd60b74545410059ac06e8a8a82acc7476dcd515044d66909b9aa2a08029de1973545411353a432e6a8a821ec74765cd515040166f08b9aa2a089acd21173545414de3a3b6c6a8a82009778758d51504452e90eb1aa2a08771d1d9635454147d9bc22c6a8a830de546358d5150401a6f0ea1aa2a0802cda1d43545410059a43a86a8a8200d348750d515040566d0ca1aa2a080acd21943545411b71bbb286a8a8205d367650d515040ba68eca1aa2a089b8d1d9435454102e1a3b286a8a828eb378350d515044de2f06a1aa2a0a53c59cd
  | 11 => 0x545114ed0221ec4a88029d60443d89510051f424e1b12a200a3d849c362545114ed03386c4a8c5a9d60670d895100536c10e1b12a205c3c74d0362544014bd07a06c4a88029760f40d89514453b40e81b12a200a7581d0362544010fd0f206c4a88021f61e40d89514453b40881b12a200a758110362544010fd0e186c4a88021f61c30d89510051f42061b12a200a3d840c362544494dd04186c4a88029b60830d89514453b40861b12a200a75810c3625444d27d0fba2c4a88030f61b74589510069bc0ee8b12a200d3481dd1625440187ec3ba2c4a88034dd8774589510061fbb0e8b12a20087e87d91625444d878e9b22c4a88038b90b645895102e1e3a4c8b12a224a6e82991625462b4eb03322c4a88921f21d64589511361e3a2c8b12a200c3f74191625440b878e8322c4a880297a0c64589510052ec18c8b12a224a6e821916254401c5c84322c4a88029ea0064589510053cc00c8b12a200c3c74d8d625440147d0931ac4a88028f61263589510061e3a4c6b12a314a758198d62544490f90eb1ac4a88030f1d163589510061e3a0c6b12a200d3774dc56254401a68e9b8ac4a8c4f59dcb71589510051f424c0b12a200a3d849816254401878e9302c4a88f29d60660589510061e3a0c0b12a20097581dd9425440b0fb05bb284a88031d60776509510063b20eeca12a20087e869d9425440127f08bb284a88025de0576509510061fa18eca12a20587f821d942544018dd043b284a88161f608765095100636c10eca12a200c3e421d94254401878843b284a881a1fe0476509510343ec08eca12a200c3f411d942544018ec823b284a88030f50476509510063aa08eca12a200c6f211d942544018da423b284a88030fd0076509511249e43a86a12a200c3c7650d425444d2d90eb1284a8c4ad9e056250951004bac0eec992a20093f845d9325444d27908bb264a88025de05764c951004bdc02ec992a223978805d932544010fd0dba264a88021f61b744c95114e1e326e8992a20087f865d132544010f90cba264a88925721d434c95114f0e32286992a224b4c8250d32544470fb0e326c0a88170f9d064d81510052ec18c9b02a200a6d8219360544470fb0fb1ec0a888e1f61f62d815100636b96c5b02a200a3c8458b60544052e903ba2c0a88170f1d2645815102e1f3a0c8b02a200a5d8319160544014db04322c0a888e9ea00645815111c3e43ac6b02a22387c87589605440147908b12c0a880a5ea1f605815188eb9b8ec0b02a296977815cb65504450fb0e316caa080297a0c62d95410052ec18c5b2a8200c6d7218b65504014f500316caa08029e60062d95414ed1f420e7b2a829ca3d841cf655052d0ff02b96caa0a768fa1072d95414e51ec20e5b2a8200a5e831cb65504014bb06396caa0a729da0472d95414ed3ac08e5
  | 12 => 0x1ca9b21952d81420264f39a87b02840687e86dd5605097d0f90dbaac0a10021fa1f65581420043f438cab02842e96c87549605081b4d90ca92c0a11774bdd152581425bf34302a4b02840087d879d7644ca3f4db053aec89901a1fe1d75d91328f43fc12ebb22643187d825d7644c8010ff02baec89901a1fe1f51d91320043ec3ea3b22640687e87dd5644c8010ff05baac8990021f60b75591320043ec0eeab22640087e871d5644c8010fd0fa8ac89901a1f21f515913268e2e3b6eaa1a64d2b1e84dd5434c801a98e5baa86992cac7a176450d3201ce743ee4a1a651df0c54dc9434c80739905b8a8699473471537050d3201ce6416e0a1a640087f855d3614c80d0f90aba6c2990029b60854d85320053ac08a9b0a6400e1c5450f614c8010ff0aba6c09901a1f21574d813200536c10a9b026400a7581153604c9532ef02b9ec8a880a5d20573d915151cbbc0ae5b22a202974815cb645440147b0d216c8a88170f9da42d9151504bbc0ae1b22a202974815c36454637a6ee9b8ac8a88961f61c64d8d5102e1f3a0c9b1aa225a5e8319363544014db04326c6a88029e60064d8d5102e1e3a4c8b1aa205c3e74191635444b4bd06322c6a88029b6086458d510053cc00c8b1aa31ad5773dc563544012eb03bb286a88030fa137650d510061ec26eca1aa20087d82dd943544018eb03bb286a88031d9077650d510043f434eca1aa200977815d943544018bd063b286a88031760c7650d510043ec10eca1aa20687f811d9435440d0fb023b286a88030fd047650d510063b208eca1aa200c3d411d943544018ea823b286a880317cc47650d510062e988eca1aa200c3f401d9435444b27d0fb2286a88168fa1b6450d51134ae43ac6a1aa200e1c6458d43546336af02b1a86a89d70f1937050d51134aec1ee0a1aa22487d87d9362546314eb03326c4a88021fe1d64d89511243ec38c9b12a205c3e74193625440187ae8326c4a880297a0c64d89510052ec18c9b12a224a6e8219362544014f500326c4a88029e60064d89511243ec3ec7b12a200a3e8498f625440147b0931ec4a8c5e9d60663d89511243ec38c7b12a200a3e84983625440147b09306c4a8c5a9d60660d89511243ec38c1b12a200a6d82dd362545114ed033a6c4a8c629d60674d895102c3fc3ae9b12a205c3e741d3625440187ae83a6c4a880297a0c74d89510052ec18e9b12a200a6d821d362545114ed023a6c4a8a969d60474d89510053d400e9b12a200a79801d362544014db05b9ec4a88028fa1273d89510051ec24e7b12a288a76819cf625462f4eb0339ec4a88029b60873d895102e1e3a687b12a288a7681d0f62544014eb03a1ec4a88029ea0343d89510053cc0687b12a20087e8790f62544010fb0f21ec4a88021fe1d43d89510043e43a87b12a205c3c7450f62
  | 13 => 0x51ec20e3b2a8400a5e831c765508014bb0638ecaa12fa9ba0871d95425fd36c10e3b2a8400a7a801c765508014f30038ecaa10021fa1e31d95420043ec3c63b2a840087e870c765508010fb0e18ecaa12fe8fa1031d95420051ec2063b2a84bea6e820c765508014db0418ecaa10029ea0031d95420053cc0063b2a84bfa3e841c3655097d47b08386caa10021fa1c30d95420043ec3861b2a84bfa3e840c3655080147b08186caa12fa9ba0830d954200536c1061b2a8400a76810c365508014eb02186caa10021fa1f10d95420043ec3e21b2a840087e8704365508010fb0e086caa12fe8fa1010d95420051ec2021b2a8400a5e8304365508014bb06086caa12fa9ba0810d954200536c1021b2a84f1c3c7419763508010fd0fb2ac6a10021fa1c6558d4291d1f436eaa1a84d0c3c76dd543509e347d0db2a86a12fb0f1db6550d420070e32ec6a1a8400c3c65dc1435080b33b07b8286a1302cba1f74549421969743ee8a928403b2e86dd152508076590dba2a4a10cb4b9db7454942196963b6e8a928400b2d83dd1525080165b03ba2a4a1002cb6037454942656363b6e6a928432b2c84dcd52508014df0cb9aa4a10ca9b2197354942156363b2e6a928400b2f845cd525086565908b9aa4a12f71b1db6354942004b7c3ac6a92842e96c8758d52508538d8ecb1aa4a12d2cbe1163549429172631ac6a928400d2f8750d525080165d0ea1aa4a1002cb21d43549420069643a86a928403b2e8650d52508076590ca1aa4a10db8bdd9435494202e973b286a928405d2c7650d5250865c58eca1aa4a10170b1d9435494259d97c1a86a928432f0f8350d5250973e1ce6a1aa4a1003c35cd435494200787b1a86a9284b9f0c6350d525080165f02a1aa4a12e7c3cc5435494200597c0286a928521f0e3050d5250973e1860a1aa4a128f1b1db715494219596426e2a928400d2f74dc55250801a58e9b8aa4a142e5ba1b715494200697c26e2a92840596e84dc5525080b2d909b8aa4a10034b213715494244e37b26e2a928489d2f64dc55250801a5e87b8aa4a10034b50f7154942124b6c0ee2a9284b8d2f41dc55250801a5e81b8aa4a10029be19715494219536432e2a92841ac6c765c5525080165f08b8aa4a10cacb211715494200697ba2e2a928400d2c745c552509898d8edb82a4a10cacb213705494200537c32e0a928432a6c865c1525081d8d8ecb82a4a1002cbe11705494219596422e0a92849696c8754b615092d4d90ca96c2a10029d60775d85424b536c10ebb0a8400a75811d761508010ff0ab9ec2a101a1f21573d85421b61e3aa87b0a840087f855c3615080d0f90ab86c2a10021fa1f65585420043f438cab0a8520c3f74195615085d2d90ea92c2a10669b219525854243e97ba2a4b0a84b8e646154961509e3878e832ec0a1
  | 14 => 0xf8759361548610fb0e326c2a90170f9d064d85520061eba0c9b0aa400a5e8319361548014bb06326c2a90029ea0064d85520053cc00c9b0aa43087d87d8f615480147d0931ec2a90028f61263d855294536c14c7b0aa43087d8718f615480147d09306c2a90028f61260d855293d36c14c1b0aa43087d8718361548014eb03ba6c2a90c29ba0a74d855294d36c14e9b0aa40587f875d3615480b87ce83a6c2a90030f5d074d85520052f418e9b0aa400a5d831d361549134dd043a6c2a928e9b60874d85520053ac08e9b0aa400a7a801d361548014f3003a6c2a90029d60773d85520051f424e7b0aa400a3d849cf61548614dd0539ec2a94a29b60a73d85520053ac08e7b0aa405c3c74d0f61549134dd05a1ec2a90029b60b43d85520053d40687b0aa400a7980d0f61548010fd0f21ec2a90021f61e43d85520043fc3a87b0aa40087c8750f615480b878e8a1ec2a92269ba0843d855200536c1087b0aa400a3e849c3615480147b09386c2a90c29ba0a70d855293d36c14e1b0aa400a75811c3615480b878e9a06c2a900297a0f40d85520052ec1e81b0aa489a6e82d0361548014db05a06c2a90021fa1e40d85520043ec3c81b0aa489a6e8210361548014db04206c2a90021fa1c30d85520043ec3861b0aa400a3e840c3615480147b08186c2a92269ba0830d855200536c1061b0aa430a76810c361548014eb02186c2a90ca4fa1f74585520061ec36e8b0aa400d2f82dd16154801a5905ba2c2a90030fd8b745855200697b16e8b0aa400c3f761d161548010fd0fb22c2a90cb0f1d364585520071b20ec8b0aa405c3c749916154a4d4db05322c2a90c29da0664585521843e43ac8b0aa432c3c74591615480187ee8322c2a90170f1d064585520052f418c8b0aa400a5d8319161548614ed02322c2a90038d90464585520053d400c8b0aa400a79801916154801878e9b1ac2a90028fa1263585520051ec24c6b0aa400c3c7498d6154a4b4db0531ac2a90c21f21d63585520061e3a2c6b0aa400c3c7418d6154801a5ee9b92c2a90034b1d3725855289eb3b96c2b0aa400a3e84981615480147b09302c2a90030f1d2605855228536c14c0b0aa400c3c74181615485f0fb0e326c0a90170f9d064d81520052ec18c9b02a400a7581193605485f0fb0fb1ec0a90be1f61f61d81520063ab8ec3b02a400a3c8458760548072d905ba2c0a90170f1d2645815202e1f3a0c8b02a400a5d8319160548014eb02322c0a90be9ea00645815217c3e43ac6b02a42f87c87585605480147908b0ac0a900e5ea1f6058152926b5b96c0b02a49796f825c7655085d0fb0e30ecaa100297a0c61d95420052ec18c3b2a8400c757118765508014f50030ecaa10029e60061d95425fd1f420e7b2a84bea3d841cf655092f0ff04b8ecaa12fe8fa1071d95425f
  | 15 => 0x4b8ecaa1b468fa1071d95436851ec20e3b2a86d0a5e831c76550da34bb0638ecaa18029ba0871d954300536c10e3b2a8600a7a801c76550c014f30038ecaa18021fa1f21d95430043ec3e43b2a8600c6d72c876550c010fd0f10ecaa18021f61e21d95430063ab8c43b2a860087e870876550c010fb0e10ecaa1b468fa1021d95430051ec2043b2a86d0a5e830876550c014bb0610ecaa18029ea0021d95430053cc0043b2a86d1a3e84dc36550da147b09b86caa1b4297a0f70d954368d2ec1ee1b2a8600c3e745c36550da347d08386caa1b428f61070d95430043f43e41b2a860087d87c836550c010fd0e106caa18021f61c20d954368d1f42041b2a8600a3d840836550da14bd06106caa18029760c20d95430053b40841b2a8600a75810836550c010fd0f886caa18021f61f10d95430043f43821b2a860087d870436550da347d08086caa18028f61010d95436852f41821b2a8600a5d830436550c014dd04086caa18029b60810d95430245ec26ebb1286bca3e84dd76250c014db05baec4a18029b60875d89430043fc2ae3b12860687c855c76250c010fd0fa8ec4a18021fe1570d89430343e42ae1b12860087e87d956250c010fd0e32ac4a18122f61375d85434d51f426ebb0a8600a7581dd76150c014eb023aec2a18021fe1572d85430343e42ae5b0a860087e87d4b6150c010ff0ab86c2a181a1f21570d85430043f43ecab0a860087e871956150da38bae7b2ec0a1be30f1d065d81437c62eb98cbb0286048bd84dd76050c01878a9baec0a18163760f75d81433ad1f42ea9b028605c9d73d536050ceb47909a96c0a1bef175cf52d81433ad1e426a3b0286fac5d73d476050c0d0fd0dbaac0a1b421f21b755814302c9f426eab02860087e87d956050dedcb061b2ac0a18021fa1c655814396f2c180cab0286c796f825cf64548072d904b9ec8a92965be0971d915201cb6412e3b22a405c3e7690764549852df04b86c8a900e5b20970d915296697ba6e4b22a43187d87193635480b87ce8326c6a90c697a0c64d8d520053ac08c9b1aa400a7980193635480b878e9322c6a90170f9d06458d5218d2f418c8b1aa400a758119163548014f300322c6a94af53dcf7258d52004b6c16eca1aa400c3e84dd9435480187b09bb286a90031b60b7650d5200637216eca1aa40087d81dd943548010fd0d3b286a90025be097650d520062f418eca1aa400c5d831d9435480d0ff043b286a901a1f6087650d520061fa10eca1aa400c6e421d9435480187a843b286a90031b5087650d520062f990eca1aa400c5d321d943548010fb023b286a90030fd007650d5218c9f43ec8a1aa405a3e86d9143548652b90eb1a86a9003871916350d52955a7c12c6a1aa475c3c64dc143548652bb07b8286a90c21f61f64d855294d36c14c9b0aa40087
  | 16 => 0x800000c01800807800400801801803c01001401402004800000400800c01c00c00402404800802006401000800000800000001000000000801c06801005404000001801c02400401400004804806c05800800007001c00000003800c00800008800000800c0000000200300000080000000100000fc00800000c01400003400001400c00400401c00400001801c02401403800801000007000000400001802c00008004408401400000c04400000403802000802400400000400801000c0c805000c02c00c0000000740041380080000040000000001240080080000080040542100000000dc01000000c00800c01000005802002402406c0100000000080e800402c03c0140d003400c00000000c00800c06800807002400800000000003402001800402800000006000403000000c02800001002800800002c00801c01803000000000004c02004403401c06000800407c00002000000800401c00c0540000b800404c01800000000401c00800000400000400002804000000403400000004800001000001000003000400002404801000c00400c00001000800000000000c01009801404000400800402805c00000000c00000406401401400405004001404000000801401001c01809c00c0080000000180000140141b001801001400404003804800000009402403400000400803000000006400402801803c03c00800001400c0540000000380340ec00800000807001803c00401c0400800c801c04801000804001c04400002c01401000008802402400c0b800000000400008002402c00000c0840080b000000804802001006803400000405c01005c00c02c02000000000c04c00c05401c01800c0000000000100f404801000000800000004804401800c0000600600000240140080300080b800800001806000000000c01c00800400800000803806800c00000001804400001c03c01c00000005808000805016000c0680340680000080100980100640500640341400400000100080dc03400403401419404400401801c02400403c01c02c00000004801000005002001400800008c00001000801401400c0000000500b00b27d08b96caa18da1f61c62d954300636b90c5b2a8600a768118b6550c014eb02316caa18029ea0062d95430053cc00c5b2a860593e845c76550c6d0fb0e30ecaa18029ba0861d954300536c10c3b2a8600c75711876550c014f50030ecaa18029e60061d95436968f3a461b2a86d1a3e84dcb6550da147b09b96caa18030f5d372d95430061eba2e5b2a860087f815cb6550da347d08396caa1b428f61072d95436852f418e5b2a86d1a5d831cb6550c014ed02396caa18029d60472d95430053d400e5b2a8600a79801cb6550da347d09b8ecaa1b428f61371d95430061eba6e3b2a8600c3d745c76550c010ff0
  | 17 => 0x1d43a045b2891bd4d420000001fe40006d54431a0d02214b0002169020268010199c0005c90f880b02268763ff22ec988878000145c0c06151b11f8c29a5560000ff82d63f00c0a198df851a33309e42ee4c5046879ccb24fd39b953c0004790e616947fa448000039509c6dc0c2000002447421b13f09e865d12284284488c73dd1de07426ff4470e50ff44540450b2cc9a74627f9f5c00055416f8a9c60c6bb1a29548178000382800093a6a2432810813c13e1299f20e8000003700001080001b29b306826120b5140888c0f33f91dbc88a4ba1bc80007e473f19b0000aba4302a318a4bf22a00000d8c00000004d961000075b2fb8e649f00002908000b60858203800000089d4028478b666a00b41f0904a8523d018890747f72f09c98bf800000006e000055a277815c4d23c502622800000001cf0d3cd6a6002722058a368c112a8000d7e00043b92e40000000911d780561f80000000c163b32df93746ee00020820b40000003d20ac86b636d0e182687fe71b00013406a80ed2eba05c9ec70800010ec5625d51e31fe064a89109c9018fe20591e400005ac000000109cde829e1060294d8818340400002c00001af0a690ea89621a8000ac400024a06ac10a152000000000057d46606d07a054c0fb1cf88d26971a600007100df4121d9c000375196149c8f81b5355977c56882f42a0000bba2724180d5426c6131f5a18c99a4b42f0059406a24b2de96311684430028168cf25151ce8fb441c12625e8fd49125550858c9cba84a441700391564f733a1674d180240f622b4f8a5c203d9c4000041217f003c00079932880000002bb11b130501c7dc0001458f0e00033a8000656000000053c0004a7000000108800042c94188a460d1e39bed15e57a2749f482b689a3189ea093e52332286500007851cd05284522313de0b988e651d2379d5cf0215538d001802803400403c00400800400801c0040080040080040140500040340300000180140000440200000100000080200a401801c00001000c00000000400004401000001c01402400403400004800400000400c02000005c03400400415402400400000c00000000000401c00c0500040000000a000003000800806c00401801010c01001c01402c05c04000001c01c00002800401c0000040180080000000000040180000380c000800802400000802400c00c0300980140140000640100540040000080040000fc00c0000340080080d40880000600200000040200b800000000001400c0540080100380000680100200b002800801400000400000c01c04001400c02802000400000003c00000000806400803400002400000000000001800000400000009402805400802801400000402400000001002401400c00801c01801001005000000800403800402c08400400000809808
  | 18 => 0x70a0000000fb05ec17f8f3103a57331080007640001220000de40000dd000030e13000022dc8700004068728cb805e352138472400031e8b547820ac0681f6c4be0004520bf012c4912198f0cfaa0ec1989704f3c3481540cecf8e1430be183841e3b44320d487b000000000000000000190ea8c040fd15f97f485a2b900f8824adc50e0631a7800000000009d112049501380000463742849a1400061c18913f80000000a89a2800000000002ccec60000f90000fce5670001c3c58600005900002880002c29b1c32459815790047f05a333c07145603e70718c400008532b014c451645d142800034689f25600006f46772ce0b1cdbc79f40d84dc0006e419988b4e7a00005f0f8c3d278433f99c80040dc3f6800000061b044000010475f258837872c5974509420afe7961751068e4674824b8a7c9064812c017e0224008282822435c0383ab000000000019b800032e4b23d700002f203d0de10a060e0ca41c9d7048410044a0c30bc81b312a164c56a30e10100d84a012d33e16384820780871ce899205230d081061e21300003fc00078f147060821e7ad000000054800a1350e1ce4830334791c03de77c437130c89600708e1dcc6745c42462134ef26c800022a411648514ca2942785ff25311048524571e210dd09446b37b84e00ca44743f18a038e0f40bf875cdf223b24f1a351503a23d280001b45b7000108cbe60cf1f9800067c000000034817a00000011000008c305f9c7802e2ef44c8ab405a16f15622081f289e1d798b8ba67ab31f120865044902f9e600005703138e9109e3d218b03f077e4ce1739ef86d053010c91d8dd801013b800117a0002f31ab887e4cf0000cf0fd42f83c488e851e26f3f619acb9e3e80ae8e8c7b253d18d82d03b036f1268000a4c3ae42105b468878c0d51f9041416e3eb00f8f463be3e0832d0f630b1be1ec0bf671c00019844bc00021a01281565ae3e60254a3e5763f4a214bce0aa2108e94d7887915320ac0120e2003002c9c079c10d1cc8bdc1ea44194e80006360dd8d9c96022833608fc61230a3f7007822009409d0d903641fb00006911606543a590749383cf2e3a070000212439a1f49081e13fe8af8d263f133da2b8a7288c0248000aae7b320b14d449e00035511881724313a203582661a60bf00000002d00001354956000249800046e0000db1e2c1fc64a1ef1164abc803001a1c07b41d20e480004cc0000001480000000008878814c00013716500000b743594ecb1a00025521b024056b3d5000047a46e000077c1a876002080007b864320a9e406e4234082036d17259235b0450fcc0000e20f2c1ae79d4240e0cc6603102a12e00a606c149059012231e000139c7785422b788ac3f80000a409882ec60c39c11081c226d3e711ed0fe7b729b8b1400046a02e1ced06c2dd4368
  | 19 => 0x156431062b00e8a608887341a703aca92000000147112e62c1908000a3c0d10f1841d00283c181013490c0193ee8bd09902383968184f4254409f9344c3c0773e880609da72530a1abc58c3824311ae091609f3609e0c4b641f18d1000fa869c2da9b6c0006c205a86807221e83b89980c323c018f8cc0f7083425f18244d636a1d48cbcb4011801311440001713c6a17876a5011620bdcffe0ea000000000000010180a8c0e000000000016c36624400b8b982e81a192608c20002ec07505383bd3b58fe85a422f0000000f6200032b20641482613488b6c74e60a3848e310666cf38fa0989a475445d0a743e000039099c000059e1c5026097808e364a0dc7a62330c68000bda00000019bd0f45f1000043021a1ce3b912bc0d640c000146097e7690001fac59c2a20518000e0c2641170ed8db01a5000082c6ec5822d20500000000064170cb7200008d917cbb839f2451e180000001600000f4c511102992c0001d542f80008e400007b00000003240001918b7c6480001a684a205b4191814c400003da839819c7f400007e40ce47d2fb1858eb41590000000f94000347000000015300000009cc24c15d1b88000000000232c0001f730200000007613ae800079a03c1d61a201b065e00012a400000000000000002c846002e88fe0f20c721740006d72d31b94aa65253f400000005ca1e886a000056d00008180008561508e2d16c0001f0a0ecc9250d1c78000efc2013448000b56221182000050e8882fa2140f8c4f223c1d40ce28613858bb06644c014b8270d806472de0d44088641356195517e24600013d42120000000ee08082dc25180004201b13e98000000349445184410e70e1d01ebc4382bc18880000007450d79f785ea63a3a8a2e00000002b3090c60a00000012d402c75920684b0fec2b62920b5c34e40f0819ad02527142b41e44c8877f356831c0003893b41c8099674f0001c9c8f460336fa0d4bea5e926980c0f266b70d09db108e1692d380000008230001d0424a00025000008304e228581e44c63a614183c05d20001a5818c37e2472f5a28c0002ae1781ddc2b05e529e0fec00025d2e30d1c2be2a32b0950473043e3d38000e527c00229d48a0021635298ec2c2081395959442200041e800079270204e90444f80002a513709a87313081024e0600000000000006a81ae13e4fe67df38c0b282f680c207000000000014d8d408fc00d02e8000db20b83210000af26321bf1cbc00065738b9078bb200017b0000b3652802721540004653628fe4b7446739705c8ac6051434847c00000009199301427da2ca800000005034c1fbc72627b41f800022c0a200000000006230000000380583335176c25406f0c61fd484a0002190000a4401b06986f402a1a93e492943121d91528f289b63132389190f1c6e60238820000
  | 20 => 0x662236998cd728a600000000900003a109fcf862bd0d10edc3346ce25b0ded028359248000055467e11187d0dd2174272902819a46c37f00d000021818b80010de3dd10d8dcc85854313980008441c112d204832632035493b8f367ac33b1f802ae67a274232464468016c8becdda1463681b48c722591a314a4ec80a81d403d44905b407d14285c61e03180e34aa02963caa1d0ca66240ab13080d254e1b60a443e62563b6813c4fa2cf180830489a65a2ed0b08f040cc32806603dc39b0000c647a80332cd15a405e606383a1f00007bf06280000000002d400000001fe00008b020c326313006862811a43422c8b8010225695d02a00bb03d12b8ecc1903cb9a64c4a2e4411131ca0e4de1b48dfce3a7cb4260000e9c4f12e590e8be46f0000199115851400013c0106551180141000070d35e80007be2750fa8e7000000005720e0b7000024b1c580006730c321709942883a986f8dc00372278a40e7827619e8ee86524a13ca06783ac7e220da2f8d600400001f1072a03b3169cb00000002e722f0cca8021469b68b1e3e511f1b3506249a11c867c3226b33b10484d0c12817591dcdc244a3ba9008502001039851ce6665b1b719389325af21c87e87f81e5358944c2ce06813d0770cdc7653d104ec25c728428936851842e45987ac0867b225117145fa6dd30ea2111947493291e48e6c60821e94410b642a40d20284648932a394b480641729614b832a0283a5223c6d649206e8894b5481f21598fc9f48453fd8cb424e10117691580e848f00010906847a9136150058200004c885004444c22f21807ee6f644e1a8cdd62d82041f3cc306f34620c3444c4660a606b4b5a34d1a014bc0aa3f631a9168a9a03f1ea85990e209040483090541da31794f85bc5d2334104cb7665f0000d8452a46312500005c263808b862cd8c2cc0000d28dce32a3912060ee862a29a13580004873bd9cd470c6961c7000000015e0580f80f7a0002b6000028a00023a9cc0f1059f2b210f0fca00035d17a09f682019195c449215409919a427a7b44201da8b425a910a9d3410c1cb451177800035803121c80182fa0920354f6c25207720184b824e3719e282c67fc41400003846f81af8a50a7e8c2320000014000044382b400069b1ae80e4d162d3402025c22275542b94cc1c8458000000105828936587981808b116d1070efa841058866436e84b00012dcde21ff19a024c5702e006c8ce0b124d72ba81f8c785d61c217c0b9a6c31181a980523ef0001dd904e8cd44097200007f02b9000000028a38012cc00055b000212498c00005380000423701b0000103c18f07487f44e26ef00000009be12b31b8fb062a1492db14ac0000003368b344e00003689bf49003ce1eb226cb202e20000000fa05d0000222c478895228219c1ce35712b83bc18815a142
  | 21 => 0x2c380103ba0003808fa81ee0660bc07184805381300e5d02615c4469c441c05320001c1000049b3a1800000069200015f800000020a109800017d00a183c0003d700001f03003801f2138c0000001039d1c6a65ea10f18d00000710000ec0af619d3b70dc400006d07c05cc11e0001dc8eecd086fa38c80004448001f702000006943750000e2a00000013a8b64000064800110000007d9ee40002ab000118056e5ac00989f80008152c400009b20f12878474fc20003cd000059250c25da10ca32000168940c0002001f31138dac5960bd0cfc08c5fa30f95a83b60002a59a9c0c807218420f8b622800c293cc44e2f202b00005dc31d054885cab042020597f80002201f4807000053600000000000003771ca8bc40003b8193ce2409222a9a7c3607d92c5000000000000000007624190578acc0005780b81ac8000000435166421055c0001ce40008aa17c800000071340789e100e19b00013600003c20c522480fa00000000000004ec229899470231c3e6812cd2a2e513381d880a21d1c295dc8d068134380940001ac00000000001b934e8000d0469012c05d46f0000000174400059111a978cc0200008a81c105200015487345261052f793ac32c80b0001d6000000001d157d11220d0f68000d7c48d09a9b500000000000eacda68c8074231439000000005043c806a1d69514e9833533e887c262000000229c6fa61716a04bc3a61340e780000000002c58d5800042f0000fd10422862c308a82848c63c02118e1848e00015f065c16208c92a05e60001411520ef40c31ed8d680008b500006707207bb0e88c6029c0002660bc40006580001b2800008c2c0800000033900000011300002d100002d800000014a800000037411707c41de00001fc0b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1259980c275d913000592648309d7644c001651910c275d913000592648305d7644c001651910c175d91300055264830dd5644c001551910c375591300059264830dd5644c001651910c375591307be86210301d5644c001649920c0755913000594644301d5644c001a1830a17745913002e0b9d182153624c00182d7460854d893002e0d9d181153624c0018357460454d89300055264830dc5524c001551910c371549300055264830dd5424c001551910c37550930007060c075591424c00122c98591525093008e0b21d64549424c243e0830591525093002e0b9d182153614c00182d7460854d853002e0d9d181153614c0018357460454d85300055264830dc9514c001551910c372545300055264830dd5414c001551910c37550530007060c075591414c00123498591515053008e0d21d64545414c219e1030591515053002c0f25185dd9214c0014c9920c376485300053464430dd9214c0010d9980c0764853000626610301d9214c0014c9920c0764853000534644301d9214c261918840c1754853000552648305d5214c001551910c175485300058364854d8d4348001615911536350d200054a650705d52148001928841c175485200055264c705d521480052a4985914148520004a9650864c521480052c49858d31485200055264c72dd54048001561911cb755012019ea2219434c940480016299215361501200058c64454d85404801b3309854541501200064a1508748540480011c99321d215012033e3221b744c930480071c8985d1324c12001d32259744c930480678c8865d1324c12097f42151744c93048047648964c9514c12000cb22598348530480016c0964c5214c1200058364854d8d4344001615911536350d100060bdd182151624400184c7360854589100060ddd18115162440018547360454589100051364854dcd62440014559115373589100054c650705d52144001930841c175485100055464c705d521440072a4985914248510004a9650864c921440072c49858d32485100055464c71dd54044001561921c775501100058a64854d89404400163191153625011002e0e21c54589404425ba188315162501100058a64854589404400163191151625011004cca261525094044067a908650d31501100064c1508748540440011d19321d2150110024b2261624c930440cf8d086dd1314c11001474261744c530440054d0965d1314c11019e34219744c5304425dd10545d1314c110024b4261624c5304405fa5086549314c11000cb42598348530440016c0964c9214c1101865821d854852044049a60866152148110187181d98548520441a7720946152148110014782617448520440054e0965d1214811001cb82616448520440074e0975912148110015382597348520440074e09758d2148110
  | 1 => 0x10058a64084595424840b82c87d0d65509210058964743595424840162990d0d655092102e0b21f40595424840160d93d0165509210058964740595424843342c97597645092102d0b25d6550d424840160d9418d654c921006832106359532484016499018d654c921006831508650d32484012c990219434c9210055164c72dd54148401561901cb755052102c1da6387595414840183487e11655052102e0d21c8459541484016159321165505210058c64084595414840b83487d0d65505210058964b43595414840163190d0d655052102c9926142595414840b86487509655052102e8921142595414840b83487d0165505210058564f40595414840162592d0165505210cd0d25d65d91414840b4349759543505215f64921f85509414853992487dd542505210ccc92616550941484335249759542505211864921d655094148401a2798595425052102d89261655094148401a2498595425052100709e5d65509414840b62697595425052102d8925d655094148401c249759542505210146925d844c941484016159418d654c521006852106359531484016519018d654c521006851508650d31484012d190219434c52101c6926174509314846194487595324c52118691219654c93148449c4476595324c5217e5c1251654c931484051c497611324c521014b1259844c931484071c4985d1324c52101d31259744c931484011669808575d812100549650215d760486679248408575d81210055164c215d760484015619008575d812102c0f25187997604840b03c9461c54d81210060721073595604840141c94597735812100471a6021dcd60484015859408773581210057064021dcd60484018657260462d95400061960971187655000b8398015375d8d4002c1be61429d9525000142d92d0c76549400051a64a801d95250001c294248076549400054664c745c15250001531911d1705494078e0e60075d8d425000b12e97a1952509403b60b21f63549425006562990d8d52509409964a21d8054942500656289660152509403954a25d52dc1425000152992153704c9400054c64454dc1325000b0779850676545400050d647431d9515000147191a0076545400070c505101d95150001519931d170545400054a648745c151501db839801d7635054002c4da5e8654541500ed83487d8d51505401358c6436354541502639308760151505401358c2598054541500db5309754770505400054a64854dc1315000153191153704c5400050b64854dd921500014359115376485400040f660541d9215000181c5460c764854002c0fa5387d9521500012659808765485400058965021d9521500016459308765485400059864021d95215000b12c985d5424854002c4d261755052150001549920c175d913000554644305d7644c
  | 2 => 0x40152592e1372545410054564c84dc951504015259221372545410054c64084dc9515040153190d0f72545410054564f40dc9515040183476e1172545411360d21b745c9515040b834861d172545410054564c745c95150401531901d17254541134c9261725095150453c147650d32545410055164871dd5434c401551901c77550d31005836485450f624c4016159115143d89310ee4321d43549424c40132698087745952100549a5c21dd16548401705930877459521005c864021dd1654840132598084745952100549a5c211d16548401705930847459521005c8640211d1654840b81c74a0c645952102e071d183191654840b83874a00645952102e0e1d180191654840182d821d063595210060d6047418d654840183874a0063595210060e1d18018d6548669926821d371595211845966372dc5654840182d821d060595210060d60474181654840181c74a0c6059521006071d183181654840142e9720b745952100689e0b81dd1654840143697207745952102e071d2831d1654840b81c7460c745952102e0e1d2801d1654840b83874600745952102d0b24a871d1654840b43491a1c74595210068360d821d16548401a1583604745952100689609811d16548401a198360074595210068a609801d16548401a318160074595210060e1d3805cd654840183874201735952102e0e1d280d0d654840b838746034359521006071d3835c1654840181c7420d705952102e071d283d01654840b81c7460f405952102c0f251870c1654840b03c97a1030595210040f25d840c1654840182c7460830595210060d1d1810c165484011669808575d912100549650215d764484015459308575d912100558640215d7644840142d9215173d91210050d644545cf644840183854e0173d91210050b648545c364484014359115170d912100607153835c364484015259408775591210055164c21dd5644840156190087755912100459a60215d763484015259408575d8d2199e49210215d763484015459308575d8d2100558640215d7634840b03c9461e65d8d2102c0f251871536348401838841c16558d210050e25165dc163484011e2980877058d210056865021dc163484015c1930877058d210060bdd1821516348401868706085458d210060ddd1811516348401870706045458d210051a64854dc16348401471911537058d210050b648549d94348401435911527650d210040f660541d94348401838546007650d210045966021dd54348401525940877550d210055164c21dd54348401561900877550d2102e0721c5458d434840160d921516350d21005856445458d43485f3a18801516350d210055164c71dd54248401561901c7755092102c1ba6387595424840182c87e11655092102e0b21c84595424840160d93211655092
  | 3 => 0x8a001ee4b2a05b2361684e001d07d2b60f81ed7a660d0fc058000000001005018010000200403008060140401c000040001c0106c0601c0000c04004030100000800000010080301c040080300000024000200b068030101800000028000000a0080000400000000100201400008160040f000010040102809000000041101402004040240300003014000580102c020080200c0700021014070000201800080000040101807000000700900c0101001000010a40d060020080000026000040180200402018120000000001000000100a01849006195c98118b6550c01865825c461d954302e0760c54dd76050c0144d92a0c7650d5200703509321d9435480142d92d007650d52005856446458d4354801619901916350d520060d5d1811d3615480b8387460343d855202e071d183d03615480183687907645855202e071d283191615480b81c7460c645855202e0e1d280191615480b8387460064585520040f25d8498d615480b03f981d263585520040f25d84981615480b03f981d2605855278e0760c65dc1435080b42e96e1d4354942194c32617350d5250a6dc0c765cd43549425ef031db6350d52508eb82c76e014354942194c364f8050d525080150d931d371549420054a64074dc5525080152591e1371549420054364c84dc552508015259121371549420054a64084dc5525080152990d0f71549420054364f40dc5525080182c76e1171549421960b21b745c5525080b82c861d171549420054364c745c55250801529901d171549420055164472dd5434c801549901cb7550d32005836485450f614c8016159115143d853200515646831d94354401c15414c47650d510050d647401d9435440160d921916350d51005866406458d435440182d7460874d895102e0e1d180d0f625440b81c7460f40d89510060ba1e42d91625440b81c74a0c645895102e071d183191625440b83874a00645895102e0e1d180191625440103c97612635895102c0fe607498d625440103c97612605895102c0fe6074981625440143990d0c765095100519646821d9425440b82d8290876509510050764c421d942544014359110876509510050e640421d9425440b82d82d04765095102e1960a411d9425440b82d82504765095100709505211d9425440141d93d00765095176e0760c65dc1435040143990d0c765494102e0d607421d9525040b86581908765494102e0d605421d9525040146592a04765494102e0d606411d9525040141d9310476549410050b648411d9525040143990104765494100709509211d9525040141d93d0076549411958925981549425040b43696e1d4354541134c52617350d515066bc14765cd43545414df051db6350d51504eb83476e014354541134c564f8050d5150401515931d372545410054c64074dc9515
  | 4 => 0x200000f060c72285997408a04189d4cab6c3a2bea19c4d0a000033091000251be5a8dc2184c02aaa3631a160a800216002920029c3c9fcc592846172b91e62f800790000000024000001e200000179bc9eab48501062ab00c9942831e9b0440006cb487ad9ab283a76d685cb434a459e88189a262ea5e9ba358965f184779cabf0f05000000000a2000d320a1a00023030b6800bb000a0b641aa809480000000b1800bc80000000001a2d80bcd4ae8492fa150e0861b2000000011a000000011400268c2b62b303648800cd0e46821e1baca120003b2a80000014000000780010600000000cc000c60693eb9804da000758008c000a9b3a1fb70ccace6984600304000060380000074000007600006000001a400000002620010430a6e3233e0025a001208216400092a40006d00027a3e002200000000136002428e800000001cb466a88a000000019ac180000000000000000042a3271b3c00000c8a1a00000002349380084800abb745c07c0036e00178d00009f144770d4cb1c20b888958b80012e9a93200000559e000254001029232e2b99e2d948003204380000076c094c6a00019b4e093244d1fa9780012800002e28e26005000701b84436a190eabc240002ac6b100a32c265842b60b252962a61da8f0007e20c6212ad6210bdaa4a883a87338c22ee0024c648000a2c8bf93c31000d22dc608009c8f437a942a9f2368a44722ec0198a115a1c22cd100089b14420560000047b54002d47a8120e008dc8f830084bd000008001000000000d40eea3b5c9919c8a8d0001cc9d0ba0709c50946b116e20938893569f94e4e852941802982a80a220000c5729a5608e638ce5fb76b01d25a18c3da783f9300027028abc54a9672000b5ade580e2ae9f0c4800cd8000000034800540b47b2b8be186430007f800b83283280009976c39f64482c398ac6b8003e9b6c9800a7b1057a46550009724a641ce96126083182c1b0c32
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4cb80001002800000020009800400054d8d0a4007c0050000000000000000000e82c00c800000024000008fc58e00000dc10c07030008000f8000000b000000018006c780000005cd49000000000000c34e40000b4000000c4000000ac00940064cc00bc000000ec88000000141ca8389c00000000000000008c60740068000000f43ca0440000000000004800f000000000840400000602000202020800000002040000040006080405c03219931d1715494202e0510cc80e8b8aa4a10170148664c745c9515040b818433203a2e4a8a8334849a9e98087745952100620d0ec9843ba2ca908031228764021dd16548401414d10a9c02e7b224200a0c68454e0173d912100501b442a706b86c890802815a1153835c364484010925432810aebb1a4200c412119308575d8d2100624108c8042baec690802039a9210705956348401904403242a2c6a1a4200c84201911516350d2102e0190ec9908b2a84908170288764084595424840b81443b21a1acaa124205c0321d93d01655092100640b22420c6b2a649080320884640635953248401106d48a8432869924200c8215190219434c92102e0290ec9908b2a82908170308764084595414840b81843b21a1acaa0a4205c0521d93d01655052102e049304bacaa128290803205922106359531484019084232031aca98a42008856a454219434c521006420a8c810ca1a6290802124a8650215d760484018824232610aebb024200c482119008575d812100403b52420e6b2ac090bdf20884648301d5644c1ef90842322180eab2260008866a430a177459130005413441850bba2c898002a11a10c285dd1644c00120cd48603aac8a126000b02688301d5645093098681324180eab228498002c11a10c075591424c00120cd48603aac8a0a6000b02688301d5645053000582342180eab2282984c3411910c075591414c001844c2324180ec90a6000c24611910c0764853000621108c9060baa429800311084644305d5214c001890c8908382ea90a4000c42211931c17548520004253522a10e90a80900031085464c874854048001890c9108382ea90a2000c44211931c1754851000641106c90a8b12808800321083644545894044001098d48a843a42a022000c441519321d2150110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1a0010004409b9688301d5645093000640192684301d5645093000640191688301d56450530004411b9684301d56450530
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
  | 19 => 0xa0c
  | 20 => 0xa0e
  | 21 => 0xa0a
  | 22 => 0xa0b
  | 23 => 0xb09
  | 24 => 0xb0c
  | 25 => 0xb0d
  | 26 => 0xb0e
  | 27 => 0xb49
  | 28 => 0xb4b
  | 29 => 0xb4d
  | 30 => 0xb4e
  | 31 => 0xb89
  | 32 => 0xb8b
  | 33 => 0xb8c
  | 34 => 0xb8e
  | 35 => 0xbc9
  | 36 => 0xbcb
  | 37 => 0xbcc
  | 38 => 0xbcd
  | 39 => 0xcc9
  | 40 => 0xcca
  | 41 => 0xccd
  | 42 => 0xcce
  | 43 => 0xd09
  | 44 => 0xd0a
  | 45 => 0xd0c
  | 46 => 0xd0e
  | 47 => 0xd49
  | 48 => 0xd4a
  | 49 => 0xd4c
  | 50 => 0xd4d
  | 51 => 0xe89
  | 52 => 0xe8a
  | 53 => 0xe8b
  | 54 => 0xe8e
  | 55 => 0x98955
  | 56 => 0x9c956
  | 57 => 0x9c955
  | 58 => 0xa0956
  | 59 => 0xb0955
  | 60 => 0xb0956
  | 61 => 0xb4956
  | 62 => 0xb4955
  | 63 => 0x1a09
  | 64 => 0x1549
  | 65 => 0x1409
  | 66 => 0x150a
  | 67 => 0x128a
  | 68 => 0x16c9
  | 69 => 0x1449
  | 70 => 0x168a
  | 71 => 0x12ca
  | 72 => 0x1849
  | 73 => 0x1489
  | 74 => 0x180a
  | 75 => 0x130a
  | 76 => 0x9c996
  | 77 => 0x9c995
  | 78 => 0xa0996
  | 79 => 0xb0995
  | 80 => 0xb0996
  | 81 => 0x19c9
  | 82 => 0x138b
  | 83 => 0x124b
  | 84 => 0xcc996
  | 85 => 0xcc995
  | 86 => 0x1709
  | 87 => 0x15c9
  | 88 => 0x168b
  | 89 => 0x12cb
  | 90 => 0x1889
  | 91 => 0x1609
  | 92 => 0x180b
  | 93 => 0x130b
  | 94 => 0xb49d6
  | 95 => 0xb49d5
  | 96 => 0x138c
  | 97 => 0x124c
  | 98 => 0xcc9d6
  | 99 => 0xcc9d5
  | 100 => 0x150c
  | 101 => 0x128c
  | 102 => 0x18c9
  | 103 => 0x1789
  | 104 => 0x180c
  | 105 => 0x130c
  | 106 => 0xb8a14
  | 107 => 0xb8a16
  | 108 => 0xbca14
  | 109 => 0x138d
  | 110 => 0x124d
  | 111 => 0xd0a14
  | 112 => 0xd0a16
  | 113 => 0xd4a14
  | 114 => 0x150d
  | 115 => 0x128d
  | 116 => 0xe8a16
  | 117 => 0x168d
  | 118 => 0x12cd
  | 119 => 0x1949
  | 120 => 0x134d
  | 121 => 0x749
  | 122 => 0xb4b15
  | 123 => 0xb4b16
  | 124 => 0xb8b16
  | 125 => 0xccb15
  | 126 => 0xccb16
  | 127 => 0xd0b16
  | 128 => 0x170a
  | 129 => 0x15ca
  | 130 => 0x16cb
  | 131 => 0x144b
  | 132 => 0x188a
  | 133 => 0x160a
  | 134 => 0x184b
  | 135 => 0x148b
  | 136 => 0x1a0a
  | 137 => 0x19cb
  | 138 => 0xccb55
  | 139 => 0x154c
  | 140 => 0x140c
  | 141 => 0xe8b56
  | 142 => 0x18ca
  | 143 => 0x178a
  | 144 => 0x184c
  | 145 => 0x148c
  | 146 => 0xbcb91
  | 147 => 0xbcb93
  | 148 => 0xbcb94
  | 149 => 0xd0b96
  | 150 => 0x154d
  | 151 => 0x140d
  | 152 => 0xe8b91
  | 153 => 0xe8b96
  | 154 => 0x16cd
  | 155 => 0x144d
  | 156 => 0x194a
  | 157 => 0x14cd
  | 158 => 0x74a
  | 159 => 0xa4a
  | 160 => 0x124e
  | 161 => 0x198a
  | 162 => 0x138e
  | 163 => 0x154e
  | 164 => 0x164a
  | 165 => 0x140e
  | 166 => 0x44a
  | 167 => 0xe8bd1
  | 168 => 0xeca
  | 169 => 0x16ce
  | 170 => 0x1a4a
  | 171 => 0x17ca
  | 172 => 0x144e
  | 173 => 0x5ca
  | 174 => 0x104a
  | 175 => 0x184e
  | 176 => 0x1a8a
  | 177 => 0x148e
  | 178 => 0xe8cd6
  | 179 => 0x18cb
  | 180 => 0x178b
  | 181 => 0x188c
  | 182 => 0x160c
  | 183 => 0xd4d11
  | 184 => 0xd4d12
  | 185 => 0xd4d14
  | 186 => 0xe8d11
  | 187 => 0xe8d16
  | 188 => 0x170d
  | 189 => 0x15cd
  | 190 => 0x194b
  | 191 => 0x164d
  | 192 => 0x74b
  | 193 => 0xa4b
  | 194 => 0x128e
  | 195 => 0x198b
  | 196 => 0x150e
  | 197 => 0xe8d51
  | 198 => 0xecb
  | 199 => 0x170e
  | 200 => 0x1a4b
  | 201 => 0x17cb
  | 202 => 0x15ce
  | 203 => 0x5cb
  | 204 => 0x104b
  | 205 => 0x188e
  | 206 => 0x1a8b
  | 207 => 0x160e
  | 208 => 0x194c
  | 209 => 0x17cd
  | 210 => 0x74c
  | 211 => 0xb09895d
  | 212 => 0xb09895e
  | 213 => 0xb49c95e
  | 214 => 0xb49c95d
  | 215 => 0x124955
  | 216 => 0x12c955
  | 217 => 0x148bd1
  | 218 => 0xcc9c99e
  | 219 => 0xcc9c99d
  | 220 => 0x128995
  | 221 => 0x12c995
  | 222 => 0x160d51
  | 223 => 0x9cb55
  | 224 => 0x178bd1
  | 225 => 0x9ccd5
  | 226 => 0x178d51
  | 227 => 0x1689d5
  | 228 => 0x19ce91
  | 229 => 0x1a0e91
  | 230 => 0x12c9d5
  | 231 => 0x1a8e91
  | 232 => 0x178e91
  | 233 => 0x19d791
  | 234 => 0x1a1791
  | 235 => 0xbcb8a1c
  | 236 => 0xa0752
  | 237 => 0x2cd
  | 238 => 0xa1256
  | 239 => 0xd4d0a1c
  | 240 => 0xa0753
  | 241 => 0x44d
  | 242 => 0xa1296
  | 243 => 0x194e91
  | 244 => 0x14d
  | 245 => 0xa0754
  | 246 => 0x194a14
  | 247 => 0xe8751
  | 248 => 0x5cd
  | 249 => 0x74e91
  | 250 => 0x19cd
  | 251 => 0x1a0d
  | 252 => 0xccb4b1d
  | 253 => 0xccb4b1e
  | 254 => 0xd0b8b1e
  | 255 => 0xb8bd3
  | 256 => 0xd0d52
  | 257 => 0x148bd3
  | 258 => 0x160d52
  | 259 => 0xd5612
  | 260 => 0xcd
  | 261 => 0x19cbd3
  | 262 => 0x1a0d52
  | 263 => 0x168b55
  | 264 => 0x16cb55
  | 265 => 0x19cc
  | 266 => 0x148bd4
  | 267 => 0x20d
  | 268 => 0xe8bcb99
  | 269 => 0xb8bd4
  | 270 => 0xb9416
  | 271 => 0x75612
  | 272 => 0xe8752
  | 273 => 0x139256
  | 274 => 0xd1556
  | 275 => 0x155416
  | 276 => 0xb0b56
  | 277 => 0xb0b96
  | 278 => 0x140956
  | 279 => 0x140b56
  | 280 => 0x140b96
  | 281 => 0xe96d6
  | 282 => 0x16d456
  | 283 => 0x185496
  | 284 => 0x168cd5
  | 285 => 0x170cd5
  | 286 => 0x1a0c
  | 287 => 0x160d54
  | 288 => 0x75493
  | 289 => 0xe8d4d19
  | 290 => 0xd0d54
  | 291 => 0xe8753
  | 292 => 0x151296
  | 293 => 0xb0cd6
  | 294 => 0xb0d16
  | 295 => 0x154996
  | 296 => 0x154cd6
  | 297 => 0x154d16
  | 298 => 0xe9716
  | 299 => 0x1715d6
  | 300 => 0x189616
  | 301 => 0x74a14
  | 302 => 0x9cb495d
  | 303 => 0x9ccc99d
  | 304 => 0xc9d5
  | 305 => 0x94a16
  | 306 => 0x98a16
  | 307 => 0x20b15
  | 308 => 0xb0215
  | 309 => 0xb4e96
  | 310 => 0xcce96
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
  | 3 => packedAt gbK3 (5433+((h/21+packedAt gbK3 (5265+(h % 21)*8) 8) % 149)*8) 8
  | 2 => packedAt gbK2 (371+((h/1+packedAt gbK2 (368+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3801c71f8fd8c78e1c070e1fe3fc3033ce40cf
  | 1 => 0xc00e07e3f1e0f8f01ff80fe0fc3c40ccd07333
  | 2 => 0xff803fe3f00ffe03ff000ffc0830f238c3c
  | 3 => 0xffffc003fff00003fffff000303f03c0fc0
  | 4 => 0xfff00000003fffffffc000000003fc003ff000
  | 5 => 0xffffffffffc00000000000000003ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8a04104824841824481020a21983011464045
  | 1 => 0x41020221108008100a08048048204044801112
  | 2 => 0x204880224010025001240009200810a008428
  | 3 => 0x4491448003292008124a954000302a0380a80
  | 4 => 0x90600000003ce4c8d1802046008914003f6000
  | 5 => 0x278fe793c90000010200c1981b32ebffc00000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffee8fefcfee8fffffee8fefcfee8fffffee8fefcfee8fffffee8fefcfee8fffffee8fefcfee8fffffee8fefcfee8fffffee8fefcfee8fffffee8fefcfee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27843
namespace PEqualNP.Outside.L_meta_27843
open PEqualNP.Outside.L_meta_27843.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 5 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 91 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 6 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffeeafffffeeafffffeeafefefeeafffffeeafffffeeafffffee8fefcfee8fffffeeafffffeeafffffeeafefefeeafffffeeafffffeeafffffee8fefcfee8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27843.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[8,5]⟩,⟨.and,[9,7]⟩,⟨.or,[1,2]⟩,⟨.and,[11,6]⟩,⟨.or,[0,4]⟩,⟨.or,[5,6]⟩,⟨.or,[14,7]⟩,⟨.and,[13,15]⟩,⟨.and,[0,4]⟩,⟨.or,[10,12]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27843

open PEqualNP.Outside.L_meta_27843 in
theorem PEqualNP.Outside.L_meta_27843 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 4, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
