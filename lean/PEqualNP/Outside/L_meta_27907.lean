import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27907.Model
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


end PEqualNP.Outside.L_meta_27907.Model

namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_27907

namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc89834c2c03a00011910ed8a995401435144002470c0da724d02292cb869a6224bb34005caf0c000253eb0c0038ac11e00dcea20000a2d0aec00c1000700000002100000001e0800022020c105000828206040110004302b7290876d5210eeca221dd54443bd28087795010ef4a1a15e54342bb28c85755190abea6a15714d429f2a0653d540caeca2195d54432bd2806579500cabca620d754c41b7290836d52106f4a020de54041bd286637950cc6dca518db54a319faa2633c544c67ca990cf55321af29c435d53886f6a090de14121b7296816d52d02bca7205754e40bba8a817451502eca3985d547309f2a4613d548c2dea4985b149309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (731+((h/13+packedAt s0K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s0K4 (1760+((h/20+packedAt s0K4 (1620+(h % 20)*7) 7) % 80)*7) 7
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xe3c7f8f1f1fff8e38e0e3f071c1fffe61c27f
  | 2 => 0xf03f8fffe01fe3f03f00fc7ffe01f83e867c73
  | 3 => 0x3ff00fffe3fc7fc000ff807ffe3fc1078f9c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc046421148314006282a409420484b2860c225
  | 2 => 0x24892502064884301104242352149094821c52
  | 3 => 0x29102924920a00d84010a90914a42485070498
  | 4 => 0x440146484400c9229a46000269190118a80b60
  | 5 => 0x882208009893124d2498d24c0020062155e000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcf0ffc0ccc0fffffcf0ffc0ccc0fffffcf0ffc0ccc0fffffcf0ffc0ccc0fffffcf0ffc0ccc0fffffcf0ffc0ccc0fffffcf0ffc0ccc0fffffcf0ffc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x430800f631f531bf40bd40
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (67+((h/1+packedAt s1K4 (64+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3c38f1f8f3e3fffc631c38fc18e1ffff21c0ff
  | 2 => 0x3fc0fe7ffc038f1f83e03f1fff01c70f467c93
  | 3 => 0xc000ff80fffc0fe3fc003fe01ffe07f0878f1c
  | 4 => 0xffff0000fffff003ffffc0001ffff800f80fe0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x501180111060400220510250020614820c025
  | 2 => 0x8892253020c9122181208908d90c9226421c92
  | 3 => 0x82a441524a412806c4022a424a5404a2870518
  | 4 => 0x10100424808002490948800094891004480ac0
  | 5 => 0x232088400b124c9272933493001020c8b5e000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfffffaf0ffaaaaa0fffffaf0ffaaaaa0fffffaf0ffaaaaa0fffffaf0ffaaaaa0fffffaf0ffaaaaa0fffffaf0ffaaaaa0fffffaf0ffaaaaa0fffffaf0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x70cb4fab4401419008561d4c0c800280170018902800035398006879e52011a0024c89c0494a8b2c5c42a5e24d8e1448000081070061000c318008e58b2ccff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x54ec2f2c800420000850002d2500086000000000001f1a00000020f41c00409b8ca0043000444e11800f6870f920c400001442e00101701e000c01c00002d800c2440509c2c800010860793382c34002c0d89e1939000e6001c8005c8500000fe00001584a002e878d63200000a4003f19818311d8008a3500001086f2d12c92000006c7e70099a4a63a369e8a008000ac0064000400000000a498573511c58021e01812111997c4c4120000f0000e814c000000000600002080000388009a002f20c00543b9d468631215400463a0dc70003e9f0d8280680054120e0000002000101050802120303001000000c000000050000220400020400061d01000308090700050d06010001030211bb28c87755190e7ca721cf54a43db28c87b55190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010e7aa021ee540439ca80873e53d0a7aa1a14f552429e29a85af5250a7ea0a14f950429faa6653c54ccaeca3995d547329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53907388798cf952319eaa463b6548c76aa918dd54e31db21c63b4438c76e8518ed50a319faa2633c544c7388698edd5131da2a263d7534c7ae8698ed90d31da21a63d4434c7288698edd0931daa1263d7324c7aa6498dd944319f2a6433d54c867ca810cf55021af298435d53086f4a010de540219f29e813d52d036c63a06d4c7409eaa4813c535027ea4a06d8c540da98a81bb505027ca8204fd53309e2a6617651cc2eaa398754c7309f2a4613d548c37281184fd51309e2a261d5314c37280984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9904f952209eaa4413e544827aa8905dd4520ba28a413e540827aa8105794c20aea98417651082eaa2107a480209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x817020c7075208c9f5054006004d28a4e8c0223820e910ac0620540001e003c00042004805c00d945600580300000034b06af00009044cb589648147020000000022e10100121cb80a55865310f255294443c95495110f295294043ca9495010f295254043cc9455010f3151540438e5805350a3960153328b195424ca8d6210f31a658043cc6a56210e31ac580438c68d6210d31a6580434c69664d4d318d996434c6966390d318d994434c6a56210d31ac580434c6c56210d31b4580434c6966510d31c5994434c7866210d31a5588434c7856210d31a1588434c7926010d31a5580434c7916010d31a4580434c6946350931a5193324c694644c931e1509324c62d6214d40c514d315022d6215330c515131cc314544c5308e195404c39131501308718d54482556314520d254d20083615148020
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10c0000a7000400000302021081a058a6010d31d04c4b008698e8162580434c648b80c6a1263245c064cc931908eca126498d057214d3150282b90a898e61841953150130
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
  | 4 => packedAt s2K4 (4032+((h/45+packedAt s2K4 (3672+(h % 45)*8) 8) % 198)*9) 9
  | 3 => packedAt s2K3 (2012+((h/16+packedAt s2K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s2K2 (456+((h/3+packedAt s2K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 1 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 3 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 1 => 0xa20c89489128540860a42910a424930a612912
  | 3 => 0x9110112400a0019100422409402440828228
  | 4 => 0x2404010a010004922229080032288102240d80
  | 5 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffee88ffaaee88ffffee88ffaaee88ffffee88ffaaee88ffffee88ffaaee88ffffee88ffaaee88ffffee88ffaaee88ffffee88ffaaee88ffffee88ffaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x32100df32dd32bf40bd40
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (67+((h/1+packedAt s3K4 (64+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3c78f0e3f3fff8fc638e0c70f8fff87f1133cf
  | 1 => 0x3f80ff03fc78ff1f83f00f80ff1c3f8f623d33
  | 2 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x6011804122041004102841420260844111045
  | 1 => 0x8852228a29419022829128884908950a622512
  | 2 => 0x1244440401220052400412212412220804a28
  | 4 => 0x9130065281103249a8a460021c918322a40f80
  | 5 => 0x224088800a64c49253498e4c8002044c5bb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xfffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8fffff8f8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2d06493283e1002f56000212025280541878d400002702b87003c00e824600a1736440192c69105482c0180e2840c5855493380004003c300b080083540000ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x143a03456761b808000023a050e091f9a436850e190f877248c8961e3c90ca45714178404205894c66223044427d3796c5e6c289b4dc861c20c0048189ed080028000ac0029800485a13a087200228f0441f0000076104001098003280cd65926828000c001ccce682093c003e3d1d4005400198003d1497c1c3025174e423389386a183f000b8190e9fc0006000140026001605c00381a8542d1a0480e003c000805509910741619800002c0a984c00f0085c001a1b0001003080013020a09000a0108050600001e011f05011e000e0e2d0104000e020a002901041a01130004010f000228b7294876d5290ebca7215754e42cf29c859d5390a7ca5214f546429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e940429ea8085b95010a72a0214f953329eaa6659e54ccb3aa9996790b32ce216655d538cb5885194fd51329e2a265ac424cb3ea8996715132e7a9265cf424cb3c84996710932e6212658c424cabca6194f94b41cf996839d32d067aa1a0cf552419e292839f325073a64a0edd45419fa82833e541067ca918cf552319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321af29e435d53c879a6590cf952219eaa443b5418867ea890cf15121e699243b5414867ca810cf55021af298435d53086f4a010de540219f296819f32d033a65a04f547409eaa4813c525033e64a0674c9409fa8a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184fd53209e2a6415e53c82baa790734cb209f2a4413d548837281104fd51209e2a241cd324837280904f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa88857d4d10ae29a213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x12897801600000500002b0078c2520088843499088385c50000b408c006c000000002c00c4980323ca00248000000013b03e541873a382a452a83231a5802e000230481006838914041021a20183a358e5210b165354442c554d5110b315194042c694d5010b195354042cc9455010b315154042a558442cca996010b32a9584428caa96010a32a9584424caa96010932a3993524ca1e6590932a398a424ca1e6510932a5584424ca996010932b1584424cac96010932a3994424cb0e6510932e1984424ca8d6110932e1584424ca856110932e2980424ca8d6010932e2580424ca8960109328e580525070c524c9418e58054c870c544cb21c315132486346550521e14c941486356114940c314932502356115320c315132c830c544c9208e195404838932501208b189544424d6214d10d454d10043615244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x830080104071942a1a05866010932d04c2b00849968161580424ca84b80a499283425c0544cb21c08ca9928290d05711493250282b88a899641821953250120
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 1 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 2 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4300a010422108400810504840904222051045
  | 1 => 0x84210220904030084022221084240504122112
  | 2 => 0x921101001244012480048429022890404c28
  | 3 => 0x890554a24900492b5448024324aa090e80e80
  | 5 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8fef8fef8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x447928a0ea0b21067008d32500002280795302c1064e7c829001092a4c00d93000118e0a2158000252003474b8c0004000b08000705f000040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x11069d131ba200228400800014a987a48e2d80020000001c25000c12960baaa3902198981b28819a0108120000060d8f049699a6ad159519258021072c890b0e80000d2408801e8526291f9427a0839c91ab1d8f829723058cab9e281389aa109a8aac1f000003002717a00000000a000600041810c102052a1c0030e001820a201001e140000000988b7294876d5290edca421db54843bb28887755110ef4a021de54043bb28e857551d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290656e52d06daa5a0eb94b41d6a9683ae32d075a65a0cf55241d719283ad325076ea2a0cf95041b7296636d52cc79a6598cf952319eaa463b5418c79a6498ed505319f2a0633d540c6dca418db54831bd2806379500c76a8390cf952219eaa4433e540867aa810d794c21aea9843b541086f4a010de54021af298815d53102dca4205b54840bb288817551102dca5985b54b30e6996613f544c278a898734c9309f2a0613d540c2dca4185b54830bb2886175510c27ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a83885bd4910b629221b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x7354129d6c1880031008000090000f0000188258d586548caa56195232a3993534cac56110d32b2580434ca4d6394b41a358e52d062d658cb41a998b51507853250531c554d410873141540218d584544c30c544c9309358c52443245250510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1610090ae3326a6994857398b5150682b88a899261415cc5250510
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 26)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3c78f3ffc7c7f1f8c470c7fe3f1f0f80f4cf
  | 1 => 0xf03f80fc63f9f8fe3f0780f8e3c7e7f1934b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 3 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040110004008020000100120090100001045
  | 1 => 0x10882222049101404204844848428241114112
  | 2 => 0x22035449492492a00dc80a92129054ac628c28
  | 3 => 0x44111009120080249151220003245024240e80
  | 4 => 0x88a26082403524c926a64ce4980080c95be000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8ffeaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c180027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4805fe52007f54805fc5201ffd0805fe42007f50805fc42007fcc805fe32007f4c805fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc21027fd40017f5000ff94001fd50005f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24002fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0824001ff0412002ffecb88016ff65c400bff32e2004bf9971002ffacb88002fd65c400bfe32e2005bf1971002ffec988016ff64c400bff3262003bf9931002ffac988002fd64c400bfe3262005bf19310067fea98802ffe54c4001feaa6200bff1531002ffec788016ff63c400bff31e2009bf98f1002ffac788002fd63c400bfe31e2005bf18f10067fea788003fe53c4001fea9e200cff14f1005ffe8788003fe43c4001fea1e200bff10f1002ffec588016ff62c400bff3162002bf98b1002ffac588002fd62c400bfe3162005bf18b10067fea58802bfe52c4001fea96200aff14b1005ffe858802bfe42c4001fea16200aff10b10007fe658802bfe32c4001fe996200aff0cb1000dfcc388017ff51c400bff28e2005ff5471002ff8a388017ff41c400bff20e2005fd9071002ffa8388003f541c400bfe20e2005ffcc71002ffc6388017f631c400bfe98e2000fd4c71002ff86388017ff21c400bff10e2005fd8871002ffa4388003f521c400bfe10e2001bf5831000ffea1880077f50c4003ff2862001ff5431000efaa188007fc50c4003ffa062001ff9031000ffa8188007fc40c4003ff9862001ff8c31000ffa6188007fc30c4003ff9062001ff8831000ffa4188007fc20c4003ff0862001fd8431000ff42188007fc10c4003fa0862000ffd9510005feca88023fe65440097f32a2000ff59510005faca88023fc65440097e32a2000ffd9110005fec88801ffe64440077f3222000ff59110005fac88801ffc64440077e3222008ffd511003ffca888003fd544400ffe2a22000ffd8d10005fec688003fe63440137f31a2000ff58d10005fac688003fc63440137e31a2008ffd4d10007fca688003fd5344011fe29a2007ffd0d10007fc8688003fd434400ffe21a2000ffd8910005fec48801bfe62440057f3122000ff58910005fac48801bfc62440057e3122008ffd4910037fca488003fd524400dfe2922007ffd0910037fc8488003fd424400dfe2122000ffcc910037fc6488003fd324400dfe1922001bfd8510047fea288017fe5144001fea8a2005ff1451003ffe8288017fe4144001fb20a2000ff50510007ea8288017fc4144001ff98a2005ff8c510007ec6288003fd3144001fa98a2005ff0c510037fe4288017fe2144001fb10a2000ff48510007ea4288017fc21440037fb022001ffd411000efea088007fe5044003fea822001df5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff104400bfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fe21cc001fe90e6012ff0873000dfac198007ff50cc003bfa866001ff9433000ffaa1980077d50cc003fe2866001ffd033000ffc8198007fd40cc003fe2066001ff8c33000fbc6198007fa30cc003fe1866001f70c33000ffe4198007fe20cc003fe1066001ff8433000ff82198003ff654c0017fb2a6011ff99530025fcca98003fd654c0017eb2a6011ff19530025f8ca98003ff644c0017fb226010ff9913001dfcc898003fd644c0017eb226010ff1913001df8c898047ff544c021ff2a26000ff55130087f8a898006ff634c023ffa9a6009ff94d30007faa698027fc534c021ffa1a6009ff90d30007bc8698003fd434c001eea1a6009ff10d30007fec498002ff624c01fff3126002bf98930007fac49803ffc624c0057e3126011ffd493007ffca498003fd524c01ffe2926010ffd093007ffc8498003fd424c01ffe2126009ffcc930007be649803ffe324c001fe9926000f74c93004ff86498003ff614c0017fb0a6000ff98530007fac298003fc614c00b7e30a6011ffd4530007fca298003fd514c023fe28a6010ffd0530007fc8298003fd414c021fe20a6009ffcc530007be6298003fe314c001fe98a6000f74c53004ff8629803fff214c001ff10a6000ff4853007ff84298006ff604c003ffa826001dfd413000ffca098007fd504c003bea826001ff1413000ffe8098007fe404c003fd2026001ff50130007f28098007fc404c003ff9826009fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001ff0813000ffc2098007fa104c003fe0826000ffd9520005feca9003bfe65480097f32a4000ff59520005faca9003bfc65480097e32a4000ffd9120005fec890037fe64480077f3224000ff59120005fac890037fc64480077e322400effd512006ffca890003fd544801bfe2a24000ffd8d20005fec690003fe63480137f31a4000ff58d20005fac690003fc63480137e31a400effd4d20007fca690003fd534801dfe29a400dffd0d20007fc8690003fd434801bfe21a4001bfd8920017fea49000bfe5248005fea924002ff14920017fe849000bfe4248005f72124002ff50920007da849000bfc4248005ff9924002ff8c920017dc649000bfd3248001f69924002ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290016fc614801dffa8a4000ff94520007faa29003bfc514801bffa0a4000ff90520007fa8290037fc4148001ff98a4000ff8c520007fa6290003fc3148005ff90a4002fbc8520017fc429000bfd2148001f690a4002ff0852000dfec090007ff5048003bfa824001ff9412000ff4a090007fd5048003bea824000fe54120006f2a090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9
  | 2 => 0x50006fac6a80037c6354031bfa1aa000df90d50006fa86a80637c4354001bfb12a017df98950006fac4a805f7c6254031bfa12a017df90950006fa84a805f7c4254001bf992a017df8c950006fa64a805f7c3254001bfb0aa000df98550006fac2a80037c6154031bfa0aa000df90550006fa82a80637c4154001bf98aa000df8c550006fa62a80037c315402fbf90aa000df88550006fa42a805f7c2154003bfb02a0019fd8150026f6c0a80077f4054003bf202a001de9015000ef880a80077e3054003be182a001dfc815000efc40a80077a2054003be102a001df8415000ef820a8003ff65500017fb2a8016ff99540025fccaa0003fd65500017eb2a8016ff19540025f8caa0006ff6450007ffaa28003ff9514001ffaa8a000ffc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8009bf18d400b7fea6a0003fe5350001fea9a8016ff14d4001ffe86a000fbf4350007ff21a8003ff50d400077a86a000ffc4350001ffb128000bfd89400affcc4a000afe6250001feb128015ff18940015f8c4a005bff525002bff2928000ff549400aff8a4a000fff4250007dfa128003ff9094001ffa84a0003bd4250007fe2128000ffcc9400affc64a0003fd325002bfe1928000ffd8540005fec2a0003fe6150001feb0a8000ff1854002df8c2a005bff5150001ff28a8000ff545400b7f8a2a000fff4150007dfa0a8003ff9054001ffa82a0003bd4150007fe20a8000ffcc540007fc62a0003fd3150001fe18a8015ffc8540007fc42a0003fd215002bfe10a8001bfd814000ffea0a00077f5050003ff2828001fe9414000ffaa0a00077d5050001fca828000de5414000ff8a0a0007ff4050007fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fa3050003fe1828001ffc814000ffc40a0007fc2050003ff0828001ff0414004ffecb98026ff65cc013ff32e6004bf9973004ffacb98002fd65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266003bf9933004ffac998002fd64cc013fe3266009bf193300a7fea99804ffe54cc001feaa66013ff1533000dfcc798027ff53cc013ff29e6009ff54f3004ff8a798027ff43cc013ff21e6009f790f3004ffa8798003dd43cc013fe21e6009ffd8b3004ffcc59800afe62cc013feb166000bf58b3004ff8c59800afc62cc029ffa966012ff94b30007faa59804bfc52cc027ffa166012ff90b30007fa859804bfc42cc013ff9966009f7ccb3004ffc6598027fd32cc001ee9966009ff0cb3004ffec398027fe61cc00b7f30e6009ff58730005fac398027fc61cc029ffa8e6000ff94730007faa398053fc51cc027ffa0e6000ff90730007fa839804ffc41cc013ff98e6009f7cc73004ffc6398027fd31cc001ee98e6009ff0c730097fe439800
  | 3 => 0xfa1a4200ff90d21007fa8690873fc434840b7fb124202ffd4921017fca49080bfd5248405fe2924202ffd0921017fc849080bfd4248405fe2124202ffcc921017fc649080bee3248405fe9924200fb4c921017f8649080aff614843bffa8a4205ff94521007eca290803fd5148401faa8a4205ff145210e7fe8290817fe4148401fea0a4205ff10521007fe6290817fe3148401fe98a4205ff0c521017fe429080bf7214840bff10a4205fb8852102ff84290817ec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843bffa82421bff941210dff8a090873ff4048437ff202421bff101210dffc609086ffc3048405ff9024202fbc8121017fc409080bfc2048437ff0824205ff04121026fec9a80137e64d4009beb26a004df19350026fec7a80137e63d4009beb1ea004df18f500d6fe87a80037e43d4001bea1ea01adf10f50026fec5a80137e62d4009beb16a004df18b500d6fe85a80677e42d4001bea16a019df10b50006fe65a80677e32d4001be996a019df0cb50026fec3a80137e61d4009beb0ea004df187500d6fe83a80037e41d4001bea0ea01adf10750006fe63a80037e31d4001be98ea000df0c7500cefe43a80037e21d4001be90ea019df0875000cfac1a80077f40d4003bf206a001df1035000efc61a80077c30d4003bf906a001df8835000ef841a80077e10d4003be086a001bfd9550007fec8a8002ff6454031ff322a003bf99150007fac8a8063fc64540077e322a004ffd5150026fea8a8013fe5454031bf2a2a004ff55150006faa8a8013fc5454009be2a2a000ffd8d50005fec6a8003fe6354001feb1aa000ff18d5004df8c6a8013ff5354009bfa9aa004ff94d50006fca6a8013fd5354001bea9aa004ff14d50026f8a6a8063ff4354001ff21aa000ff50d500c7f886a8003ff62540017fb12a017ff98950015fcc4a8003fd625402ffe312a002bf18950027fea4a80137f5254009ff292a017df94950027faa4a80037d5254009fe292a004df149500c7fe84a805ffe4254001fea12a017ff10950007fe64a805ffe3254001fe992a017ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8016fc6154009ffa8aa004dfd4550027fca2a80037e5154009fea8aa000df54550027f8a2a80137c5154031ffa0aa000ff90550007fa82a8063fc4154001ff98aa000ff8c550007fa62a8003fc315402fff90aa000ff88550007fa42a805ffc21540037fb02a001ffd4150027f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff480a8007fc4054003ff182a001ff0c15000ffe40a8007fe2054003fd102a001ff0815000ffc20a8007fc1054001bfb22a018df99150006fac8a80637c6454001bfb1aa000df98d
  | 4 => 0x8177e650c4093f3286205ff59431005faca188177d650c4013eb286205ff1943102df8ca18817ff640c40b7fb206205ff9903101dfcc818817be640c4075f3206205ff59031005fac818817bd640c4015eb206205ff1903102df8c818893ff540c447ff2a06200ff5503111ff8a818826fe630c413ffa986209ff94c3104ffaa618827fc530c413ffa186209ff90c3104ffa8618827fc430c40bffb106205ff98831015fcc418817ee620c405773106205ff58831005fac418817ed620c40176b106205ff1883102df8c418893ff520c445ff2906200ff54831117f8a41888fff420c445ff2106200ff50831117f88418827ff320c413ff1906209ff4c83104ff86418816fe610c40bffa886205ff9443102ffaa218817fc510c40bffa086205ff9043102ffa8218817fc410c40bff9886205f7cc43102ffc6218817f6310c40bfe9886205f74c43104fea6218817ff210c40bfe1086205ffd803102ffcc018806fe600c40bfd3006201be9803102ffac018802fd600c40bfcb006200be5803102ff8c018806fc600c449ffa806221ff9403110ff8a01888fff400c443ff2006221ff1003104ffc6018827fc300c445ff9006221ff8803110ff84018817fe100c40bfe0806205ffd962102dfecb10817fe65884097f32c4205ff59621005facb10817fc658840b7e32c4205ffd922102dfec910817fe64884077f3244205ff59221005fac910817fc648840b7e3244220ffd52210fffca910803fd548843ffe2a44205ffd8e2102dfec710817fe63884137f31c4205ff58e21005fac710817fc638840b7e31c4220ffd4e21007fca710803fd5388441fe29c421fffd0e21007fc8710803fd438843ffe21c4202bf58a21017fea51080bfe5288405fea944202ff14a21017fe851080bfe4288405f72144202ff50a21007da851080bfc4288405ff9944202ff8ca21017fa651080bfc328840b7f30c4205ffd462102ffca310817f6518840bfea8c4200fd5462102ff8a310817ff418840bff20c4205ff5062102ff88310817ff318840bff18c4205ff4c62102ff86310817ff218840bf790c4202fdc862102ff84310817f4218840bffb044205ff9822100dfcc110817fd60884017eb044205ff1822100df8c110883ff508843dff284421eff142210fffe811087bfe408843dfe204421eff8c2210f7f8611080bff2088405ff1044202ff0822102ffc2110817fc1088401ffb2a4200bfd95210effcca90812fe6548401feb2a4200bf595210eff8ca90812fc6548401ffb224200bfd91210e7fcc89080efe6448401feb224200bf591210e7f8c89080efc644843bffaa2421cff95121007faa890873fc5448401ffb1a4200bfd8d21007fcc690826fe6348401feb1a4200bf58d21007f8c690826fc634843bffa9a4200ff94d21007faa690877fc5348439f
  | 5 => 0x8b3104ffac598802fd62cc413fe3166202bf18b31187fea5988bbfe52cc401fea96622eff14b3117ffe85988bbfe42cc401fea16622eff10b3104ffe6598827df32cc413ff1966209ff4cb31007ba6598827fc32cc461ffa8e6205ff94731007faa398817fc51cc45fffa0e6205ff90731007fa8398817fc41cc45dff90e6205ff0873104ffec198827fe60cc4037f3066209ff58331005fac198827fc60cc4037e3066230ffd433116ffca1988b7fc50cc45fffa06622dff9033116ff88198827fe30cc413fe186622effc833116ffc41988b7fc20cc45bff0866205ff0433102ffecb18816ff658c40bff32c6204bf9963102ffacb18802fd658c40bfe32c6205bf1963102ffec918816ff648c40bff3246203bf9923102ffac918802fd648c40bfe3246205bf19231167fea9188affe548c401feaa4622bff15231005fac7188b3ff538c413ff29c6200ff54e3104ff8a7188afff438c413ff21c6200ff50e3104ff88718817ff628c40bff3146202bf98a3102ffac518802fd628c40bfe3146205bf18a31167fea5188abfe528c401fea94622aff14a3115ffe85188abfe428c401fea14622aff10a3104ffe65188abfe328c401fe9946209ff0ca3102dfcc318817ff518c40bff28c6205ff5463102ff8a318817ff418c40bff20c6205fd9063102ffa8318803f5418c40bfe20c6205ffcc63102fbe6318827f7318c40bff90c6205ff0863102ffec118817fe608c4037f3046205ff58231005fac118817fc608c4037e304622cffd423114ffca1188a7fc508c457ffa046229ff9023114ff881188a7fe308c413fe184622affc823114ffc41188a7fc208c40bff0846205ff04231007feca98802ff654c451ff32a6204bf99531007faca98802fd654c451fe32a6204bf19531007fec898802ff644c44fff3226203bf99131007fac898802fd644c44ffe3226203bf19131147fea89889ffe544c401feaa26227ff15131147fea698827fe534c401fea9a6209ff14d3113ffe8698827fe434c401fea1a6209ff10d31007fec498802ff624c44dff3126202bf98931007fac49889bfc624c4057e3126228ffd4931137fca498803fd524c44dfe2926227ffd0931137fc8498803fd424c44dfe2126209ffcc931007be649889bfe324c401fe9926200f74c93104ff864988a3ff514c40bff28a6200ff5453102ff8a29889fff414c40bff20a6200fd90531007fa8298803f5414c40bfe20a6209ffcc53104fee6298817fe314c40bef18a6226ffc853102ff84298803ff604c4017fb026225ff9813100dfcc098803fd604c44bfe3026201bf18131147fea098897fe504c44bfe2826227ffd013112ffc8098897fc404c44bff1826209ff0c131137fe4098897fe204c44bfe1026225ff8413102ff82098817ff650c40b7fb286205ff99431025fcca18
  | 6 => 0x9ffa82a204dfd4151027fca0a8813fc5054473ffa02a237ff901511bff880a88dffe305446ffe182a238ffc81511bffc40a88dffc205446fff082a205ff0415102ffecb20816ff659040bff32c8204bf9964102efccb208127e659040bfeb2c8200bf5964102efacb208027d659040bfe32c8205bf1964101dfac92080fff5490407ff2a48203ff5524101ff8a920817ff639040bff31c8209bf98e4102ffac720802fd639040bfe31c8236ffd4e41007fca720803fd539046dfe29c8203ffd0e4101ffc872080ffd4390407fe21c8205ffd8a4102ffcc52080afe629040bfeb148200bf58a4102ff8c520816fc629046dffa948235ff94a41007faa5208d7fc5290407ffa148203ff90a4101ffa852080ffc4290401ff9948235ff8ca41007fa65208d7fc329040b7f30c8205ffd464102ffca320817f6519040bfea8c8200fd5464102ff8a320817ff419040bdfa0c8203fdd064102ff88320817f4419040bff90c8235fdc864102ff84320817f4219040bffb048205ff9824100dfcc120817fd60904017eb048205ff1824100df8c1208dbff5090469ff2848234ff1424101ffe812080ffe4090407fe2048234ff8c2411a7f861208d7ff2090469ff1048234ff0824102ffc2120817fc1090401ffb2a8200bfd954119ffccaa0812fe6550401feb2a8200bf5954119ff8caa0812fc655040b7fb228203ffd514119f7ea8a080ffe5450407feaa28203ff1514101f78a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc63504137e31a8233ffd4d41007fca6a0803fd5350467fe29a8203ffd0d4101f7e86a080ffe4350407fea1a8200ef50d4101ff886a0803ff62504017fb128232ff98941015fcc4a0803fd6250465fe3128202bf1894119ffea4a08cbfe5250401fea928232ff1494101ffe84a080fbf4250407ff2128203ff509410077a84a080ffc4250401ff9928232ff8c941007fa64a08cbfc32504077fb0a8233ffd454102ffca2a0803f65150401fea8a8200fd5454102ff8a2a080fff4150407fba0a8205ff9054102f7c82a0817fc415040bde20a8203fd10541197fe42a08cbf7215040bfe10a8232fd08541007fec0a0802ff6050463ff3028201bf98141007fac0a08c7fc60504037e3028233ffd414118ffca0a08c7fc5050407ffa028203efd014101ffc80a080ffc4050463ff1828231ff0c141197fe40a08c7fe2050463fe1028231ff8414102ff820a0827ff65cc4137fb2e6209ff99731025fccb98827fd65cc4017eb2e6209ff1973104df8cb98827ff64cc4137fb266209ff9933101dfcc998827fd64cc4017eb266209ff1933104df8c9988c3ff54cc45fff2a66200ff5533117ff8a998827ff53cc413ff29e6209ff54f3104ff8a798827ff43cc413ff21e6209ff50f3104ff88798827ff62cc413ff3166202bf9
  | 7 => 0x990ffff544c87dff2a26400ff551321f7f8a89900aff634c87fffa9a6409ff94d32007bca699003fd534c801eea9a6409ff14d321f7fe86990fbdf434c813ff21a6400ff50d3204ff886990fbdc434c8057fb126402ffd49321ffdea49900bfe524c805fea926402ff14932017d8a49900bff424c805ff2126402fb90932017fa8499003ed424c805fe2126402ffcc93204fde649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6405bf185321fffea2990fffc514c87dffa0a643eff10532017fe429900bef214c805fe10a6400ffd8132005fec0990f7fe604c8037f3026400ff581321eff8c099006fc604c87fffa82643dff941321eff8a0990fbff404c87bff202643dff101321effc6099027fc304c805ff9026402fbc8132017fc409900bfc204c87bff082643dff04132025facb28817ff649440bff324a203bf9925102f7cc92880ebe649440bfeb24a200bf5925102f7ac928802bd649440bfe324a205bf19251027fea928813fe5494409feaa4a204ff1525102ffec728817fe63944137f31ca205ff58e51005fac728817fc6394409ffa9ca204ff94e51027faa728813fc5394479ffa1ca200ff90e51007fa87288f3fc439440bffb14a205ff98a51015fcc528817fd62944017eb14a205ff18a5102df8c528813ff5294409ff294a204ff54a51027f8a5288f3ff4294477ff214a200ff50a511dff88528803ff3294477ff194a200ff4ca511dff86528816fe619440bffa8ca205dfd4651027eea328817fc519440bfa28ca205ffd065102ff88328817ff219440bfe10ca205ffd825102ffcc128806fe609440bfeb04a200bf5825102ff8c128806fc6094409ffa84a204dfd4251027fca128813fc5094479ffa04a23aff902511d7f881288ebfe3094475fe184a23bffc82511d7fc41288ebfc209440bff084a205ff0425102dfecaa8803ff64544017fb22a239ff9915101dfcc8a8803fd6454473fe322a203bf19151027fea8a8813fe5454473bf2a2a204ff55151027f8a8a88137c5454401ffb1aa200bfd8d51007fcc6a8803fd6354401fe31aa209bf18d51027fea6a88137f5354409ff29aa204ff54d51006faa6a8813fc5354473ffa1aa200ff90d51007fa86a88e7fc4354401ffb12a200bfd89511c7fcc4a880afe6254401feb12a238ff18951015f8c4a8813ff5254409bfa92a204ff94951027faa4a88037d5254409fe292a239ffd09511c7fc84a8803fd4254471fe212a200ffcc9511c7fc64a8803fd3254471fe192a204bfd8551027fea2a8813f7515440bff28aa205df9455102ff8a2a88177c5154409fa28aa239ffd055102ff882a88e3ff215440bfe10aa200ffd8151005fec0a88dffe60544037f302a200ff581511bff8c0a8806fc605440
  | 8 => 0xf0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9016fc6154809ffa8aa404dfd4552027f8a2a911bff415488dfe20aa402ffc8552017f842a9003ff60548017fb02a445ff9815200dfcc0a9003fd605488bfe302a401bf18152027fea0a90137f5054809ff282a404ff14152237fe80a9117fe405488bfe202a445ff8c15222ff860a900bff2054805ff102a402ff0815222ffc20a9117fc1054801ffb2a8400bfd9542006fecaa10027f6550889ff32a8404bf99542007facaa1002fd6550889fe32a8404bf19542006f8caa10127c65508057fb228403ffd514201ffca8a100fbe5450807feaa28400ef5514201ff8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508137e31a8444ffd4d42007fca6a1003fd5350889fe29a8403ffd0d4201ffc86a1003be4350807fea1a8403ff10d4201f7886a100aff6250805ffa928402ff94942017dca4a100bfd5250801f6a928402ff14942017fe84a100fef4250805ff2128402ef90942017f884a100bbc4250805f62128402ff8c942017dc64a100bfc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8405bf18542227fea2a1113fc5150807ffa0a8403efd054201ff882a100bff2150805fe10a8402fb08542007fec0a1002ff6050887ff3028401bf98142007fac0a110ffc60508037e3028444ffd414221ffca0a110ffc5050807ffa028403efd014201ffc80a100ffc4050887ff1828443ff0c142017fe40a100bef2050805ff1028402ff0814221ffc20a110ffc1050813ffb2e6409bfd973204ffccb99012fe65cc813bf32e64049f9973204ffacb99002fd65cc813beb2e64009f5973204ff8cb99026fc65cc813ffb266409bfd933204ffcc99900efe64cc813feb266400bf5933204ff8c999026fc64cc885ffaa66441ff95332007faa999107fc54cc8057f31e6409ffd4f3204ffca799027de53cc813fea9e6400f754f3204ff8a799027ff43cc883efa1e6409ff90f3204ffa8799027fc43cc813ee21e6402bf58b32017fea59900bfe52cc805fea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b86599027ff61cc813ff30e6405bf9873204ffac399002fd61cc813fe30e6442ffd4732217f8a399107ff41cc883fe20e6402ffc8732017f84399027ff60cc813ff3066401bf9833204ffac199002fd60cc813fe3066401bf18332217fea199103fe50cc881fe2866441ffd0332207fc8199103fc40cc813ff1866409ff0c332017fe419900bfe20cc805fe1066440ff84332207f82199003ff654c8017fb2a643fff99532025fcca99003fd654c8017eb2a643fff19532025f8ca99003ff644c8017fb22643eff9913201dfcc899003fd644c8017eb22643eff1913201df8c8
  | 9 => 0xc017fb0aa600ff98553007fac2a9803fc6154c0b7e30aa604ffd4553026fea2a9813fc5154c9fffa0aa64fff10553277fe42a993bfc2154c01ffb02a600bfd815326ffcc0a9806fe6054c01feb02a64dff1815300df8c0a9813ff5054c09bfa82a604ff94153027f8a0a993fff4054c9bff202a64dff1015326ffc60a9827fc3054c9dff902a64dff8815326ff840a9937fe1054c9bfe082a609ffd964304dfecb21827fe6590c097f32c8609ff59643005facb21827fc6590c137e32c8603bf5924301ffea92180ffe5490c07feaa48603ff1524304dfcc721827ff5390c13ff29c8609f794e4304ffaa721803dd5390c13fe29c8609ffd0e4304f7e872180fdf4390c13fe21c8609f710e4304ffec521827fe6290c057f3148609ff58a43005fac521827fc6290c057e314864cffd4a4325ffca52192ffc5290c07ffa148603efd0a4301ffc852180ffc4290c13ff1948609ff0ca4304ffec321827fe6190c0b7f30c8609ff58643005fac321827fc6190c99ffa8c864cff1464301ffe832180ffc4190c97ff90c864bff0864304ffec121827fe6090c037f3048609ff58243005fac121827fc6090c037e304864cffd4243257fca12192bfc5090c07ffa048603ff9024301ff88121827fe3090c13fe184864bffc8243257fc412192bfc2090c95ff084864aff04243007fecaa1802ff6550c93ff32a8604bf99543007facaa1802fd6550c93fe32a8604bf1954304dfec8a180fff5450c07ff2a28603ff5514301ff8a8a180eff6350c93ffa9a8609ff94d43007bca6a1803fd5350c01eea9a8609ff14d4301ffe86a180fdf4350c13ff21a8609ef90d4304ff886a1827bc4350c07ee21a8600ffd8943005fec4a1923fe6250c057f3128600ff58943247f8c4a180afc6250c93ffa928648ff94943247f8a4a180fff4250c07ff2128603ff10943247fc64a1827fc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8605bf1854324ffea2a1927fc5150c07ffa0a8603efd054301ff882a1923ff2150c91fe10a8600ffd8143005fec0a191ffe6050c037f3028600ff5814323ff8c0a1806fc6050c93ffa828647ff9414323ff8a0a180fff4050c07dfa028603ff9014301ff880a191ffe3050c13fe1828648ffc814323ffc40a191ffc2050c8fff0828647ff04143015fecaa9003ff64548017fb22a446ff9915201dfcc8a9003fd645488dfe322a403bf19152027fea8a9013fe5454809feaa2a404ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9026fc6354809ffa9aa404ff94d52027faa6a9013fc535488dffa1aa400ff90d52007fa86a911bfc43548057fb12a402ffd4952027dea4a900bfe5254805bf292a402ff14952016f8a4a900bec5254805ffa12a402ff90952017dc84a900bfc4254805ff192a402f
  | 10 => 0x600000800400801a04800200000000000400000004e00000800007a01a00000c01001802e00e00002600200600000000401004e00c00205c02402401600400801800800406400a00200c00400803000000200400600a00001207c00600000200004201800a00600c00802800400000004801001400a00a00800000404200603002407202400a00000400800000403200201802200000200802e00e00202202200e00003a05800201a03a00c04400200c01603bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa026fc6355009ffa9aa804dfd4d54027f8a6aa00fff4355007fe21aa800ffd8954005fec4aa153fe62550057f312a800ff589542a7f8c4aa00afc6255009ffa92a804ff94954027f8a4aa00fff4255007dfa12a803ff9095401ff884aa153fe32550a9fe192a800ffd8554005fec2aa003fe6155001feb0aa800ff1855402df8c2aa013ff5155009fe28aa803ffd055401ff882aa153ff21550a9fe10aa800ffd8154005fec0aa14ffe60550037f302a800ff5815429ff8c0aa006fc6055009ffa82a804dfd4154027fca0aa013fc5055007ffa02a803ff9015401ff880aa14ffe30550a7fe182a854ffc815429ffc40aa14ffc20550a7ff082a853ff04154025facb29827ff6494c13ff324a603bf9925304ffac929802fd6494c13fe324a609bf19253027fea929813fe5494c09feaa4a604ff1525304dfcc729827ff5394c13bfa9ca604f7d4e5304ff8a729827dc5394c13ffa1ca609ff10e5304ffec529827fe6294c057f314a609fb98a53015dcc529827fd6294c017eb14a609fb58a53005dac529827fc6294c057e314a604ffd4a53027fca529813fc5294ca5ffa14a651ff90a5328ff88529827fe3294c13fe194a609ffd865304ffcc329816fe6194c13feb0ca600bf5865304ff8c329813ff5194c09fe28ca652ffd0653297f88329947ff2194ca3fe10ca609ffd825304ffcc129806fe6094c13feb04a600bf5825304ff8c129806fc6094c09ffa84a604dfd4253027fca129813fc5094ca5ffa04a650ff90253287f88129827fe3094c13fe184a651ffc8253287fc4129943fc2094ca1ff084a650ff0425304dfecaa9803ff6454c017fb22a64fff9915301dfcc8a9803fd6454c9ffe322a603bf19153027fea8a98137f5454c09ff2a2a604ff55153006faa8a9813fc5454c097fb1aa604ffd4d53027bea6a9827fe5354c13bf29aa609ff14d5304ef8a6a9813dc5354c9fffa1aa609ff10d53007fec4a9802ff6254c9dff312a602bf98953007fac4a993bfc6254c057e312a604ffd4953027fca4a993b7e5254c09fe292a604df1495327ffe84a993bfe4254c9dfe212a64eff8c95304ff864a9803ff6154
  | 11 => 0x2c080000120180000f200600600002e00003000200000200207c00000203a0020a200001400005200000000000003001e07000200400e03400600800200a04a00600800201606800000809600000201004000400c01400a00200601e02c01200200600002600000800400200602409200203009600401400600a00000800c00402403001601000400000c02200000800e01000002800401a00a00600000000200200000201601a00000c00c01000000400602e00401c07c02e02a02000000800a02e01c00405e02400404200608400000000801002a01400000200000200200401c00800000600200200603c03c00000a00401a00000000c01401a03000000400005a00000000009000600a05800000000a00400e00000400800400200401208c03800800001002c00601a0aa01c00c06008807000001c00200804204600400a00600002e01603a08400402400003803200600000601200801e05200c01c00201402204200200800400807a02402407c0c200002e0160040140ac00000207600002c02000000003a00a00206600000800a00001200c00402200c00005a0020000c401401205e00001a03c01004a04a03202c00000a00e02600002e03000c04c03201800602200400000202e00a00000801203404e01202400406e00200000e01206200800400000004203000202800400600200607200200000800001800800800e00200000000000000600400201c00207400202c00c00000200e0060020000280a200001a0040020040280040020120180000000180000120040000040b000a03a01000200000000001601a00801200400c04800401205400403406600000002000000000001600e02e01a00e00200400001a00600200400601200a00000200200000000000000200801c00200800800004800000801e00e01400e00600002200603800000003e0040fe04201001800004c02000001c00a00001800001200e01400000c00200002400400200a0d000e02400000c00000200800400600400001000800400802600a00400201c00200001003800000600000800000002a09200600602a01e00c02a00003402200200405400800201600200600203600800600801601200400801001402000600a00401c00000200401a00201800c00a00804800000a00600a00604800004600000000600200402c0380020040020000420020c404802a00205600200200a0080000040ae00801600602600400800002003a00400001600201001800000001e01a00002600800000a00400600a04200a01200002a00000002600000200000003400001800200003000201600e01a00a00000000400800800000c0020060160020460000a002000406c00000600000e02200401800004400200400e00800800600000002c00000203200202a01e00a00002e0140
  | 12 => 0x456e5c2013838c3a860214a2450e22000000000000000040b800091095a33a8b1c0000370000000e5a00009c80000004a549b00004f28db2b280012341e725480009d289200012b511234445518ec6ac0600002050c9c8270001cfd15c7620001c340001bd000000029872500000008e2000000183800000000003180004b1000005045a8c34a7871526a0b02c5800005600038b95c86940c4042a4cc0003260000ad0000000000175459a30912e8000b4c68741c9058f180001791cd881611a0000014c364b22c981c47966d824309850640b638a03c440c2e53ea95406b263a2cb207810e29122b0804c601734798844df23b321b10dcb6a24b26484c430c4a8444155094850707ea24d0c87eb36f1af03a293115a81d89568e006606e07f21e52ef1e4522074c31e0a3515e7c200008a50a405d0a401282c81e82e680011ec60824c11e862836d0fe8c203da6a10ae0000ebe90549221b92403c946215540f04430001a40a7a6d500006e509284a0d2034c88a6ee4a58000a3c8110000da4cd860c3861be805e3b81ba8000fe42e23ab14940001a902122a0e7c1270000ca01e011937680000000002801f6045600013e11a0b6e00039a00007ba0002f5895455a5862871c581e40950000a3880c0082851084ad80003de123c7fa4970e79b9c35811f1de00009b832235f80001ac4aa00008404a28340998df400017000006109761573cba20ca122504040b4ce2a0003101e340000003b900000920de3430078cd287806ba1551087b8000000000000047d000030e00e0000000bac0000000000e9c0001fa95ec31800010d04fd2781580000710c4e27f30681fc55c04f34620286c00000020380d8a6550000080000604000000033e13b3ad2204bc8882411196428a730291919c0009252e91b101940004878e1505000015c0000e0400d48e12387a80001801d645ba587091000000082a000234800033a3e68b509b61e30d91b94ab00003fc10402dc1470001accf8e7380001994cd0000063800066e45e07e06000223f432d22740000c523823040ac28a14a8cb40008bd0231ac90ec00030188f10fa7760001e8c6f44c520ba46d0fc7b1000086c53271c4778000b4e6c603410944ac4bc3e70f0c5767b9367058ce420804300f5841083634119b46360a746723b4c5843c0171bec89453526e9ab128a5cb1c68e4c8f658334003a47aa40e2f9194493440032413651d213a38290741220cd3e79c112803b2370a268c468b822ba3fc9bc8d824104bc8c216b1479900a406b425c87746b846016a95a899c43a4218b98bfe8721cea054366054434a448b5880e05f1ad51666b60a682b03f41513f721a8698123427a2f83e893a2761194f4a886161081c6ec7fd11080610003771960ea86208eb052a41cdd20001980b40fe80001a0928d1be000
  | 13 => 0x41e007f921c34d0b38850c2c87903e1d3caae7461951cac8920c80009f0c01e7701f423c40005911b1a340e7880428982bc7ce6e63e000c858a1924970120f167bd3b68bb4d0a7612990da85ec00019c11fc00031f279017d2040002e200000001c618c887cb08712000017046c0000a00ffc00075404122b41104913cf090cd443430000000cac51846d001c0000002a180000000001a121343d800000022e400084e12692c0b4400027c80009704d634c96c51f61af00010b11b2755000152c0001eb2fa000000047600000009c200000008811520000310c04882405211000065e00007f15f442a5660001a7c0000002df073836a000387800000072a235899918c76e00018a00006dc16f9f045dc5f12e71bf0fc840208f033c2ca61e13e8f38b2e00000012404c6111041800064826f1179e68ba619449f1cccbdc4be082839023a0a23ff0d909863501b41570b5455343e15ad04a4af23e1af40003b63371ae404a03003a80007f85da20783451fa7962da000070e3483479c001da00017c80007500003502018316575123083cc16496036214d1484cc143010452e18a34513688b014e3458d54d3a7190270000d1c5b300006d8516381491997009a01545a93b474e70138480003ee0000ec0eac47c54d2fba31c4ce000385a49919a45c330055000000038d11305727dd00020e834e413000036879a552045a21c0360742690ee80cc02136da3905560003ac14ac54c820467984d0ee7ba3ce1134dec4f33b190b8ae209822e9aa8d4a4a74280e98b04351139080077a0a62e89df46ca6e414ea1b47a61c01cb87c42243071e6187117629a26303b8b3a6f510c83045983a50fe088c5f417e0d31458cc2423064837486a08e2330e6c5e276c1301d802160343c086f10ea37440b027907a5292ca98a450a57812407705a219a32c157c8ea5fa0970c782aa2272c2a3983de35314f05dc6524280e3907cbf2821144814908293f0cb0e70c7214231a9aac03854138c19e40766451daa278f5a0000001894f248571562160dd816d2369c20cc81ff00601ed2768423fe113c00018e1818aa52945a306d8154ece0922530000e140d207b011468e0002721bacad21d34158df84f68bc000000086000035c22340002fe28ea4b00ce0ff2e79f98a7638b08b048472a2820001df800038e000057cf907a600000000000000000e2000000011f9a04f1e000265000025400044880002822cb0ad978cb4264c00006b80007af35b8c3400000032b8000cfe00b0bd9060c2402436b88e4e4e0313d80b3c2cc24f08622dc1d603f19917052907e3058a3d4b1a53a30e80000000531b617f0cfa43e0001e187202781438640ed63f33c987891322983c708d02e4000000186800000002d16e80006952cd992c00000010622fc98030f04b0000adc1a22719d3
  | 14 => 0x9891426d00000001ea137011000045c5264a380001d050c31f8eec06c674000000000000000000007e03e00000000a0800000006dc1566110421578fae1e40c413f826c7131cc0764dd481c4a6994c61c69102380004dc04b3a59a200003ef3530ac8508810171800116815a14fa3240008240838000862743047a5192b64013bc8204e624c72ad808ccd464943d994800028311917f92a077f3df0acd27a72f38191dd06a2ec29fa0f892800000017f4e904953ae140c00082f32082e800095705480010a86984058a00ea600015210449128f81b800011c21851918fe114c4fd4a704989b02533f41ed0b4800028da2c91dc45f0309dccd36911295181c00052e473844c00090334f00000006c10da1eec37e4521ac1b4012674a0d421ac87a53c19a0a94d7c7401c60000d807d647605a89cc56000000006dc91f3f0130862a2c91db891472427026a1ab44ae780328158847a3c501e106cdc464a35414843264e227a19bcea217815e10812169091640950fb86723d3a458cf462149c98bcb000ec2a386ac7e20a41909c1c7a439e3d09bfcc4c5d91ae83e08a89584168ea4a883d13000e083866e01a581e51447ab0000890e441cd44b8fecc1469c2bd143c15c9170359e54b200b348c21cc8aa20e4a9a1c44bc8441891be0ede0a044d9530e843fa3b893352188ea46f01cc6c215324f800106e7ac38e857805077437b8000cbe6092ef970d24401a27f89d01f61da0000a9c9064632780194b300000000cb800029b00017b000045b0001d1400000000009702880000f500012424ef45b000046a6fe0000000a440000000c4c0002da17780000003ac331907844c23b41489cca584ae0eb1e7c000000036a2601325d7102000000000029a00000000000a3084cb7000003b8000fee5c80b104500d417d15898904fc0bb3589544e4c02c1d114643be8cc2b9801819c000000038478c37902c10340000003199b4521411c49c12788b479939b9aa44241993b21c6d15639a2d001450247d30871f101862ff42420c48f05ef2e601c832a4f81bd8b5889073d3ef05e50be0d801ea400a9c71f24383bcf3667b42009a800020a0000340e8e0004079e140004990a49d1049c00000013d50182af3449fc09c02db000163039000000904b431200035396f40001f62658c9c0005a50000ae8a3e17500025640988e23fd8000a2803929991f847076917a99dd0fe1f3162250c73288009c12f48383af06f93a0ff41a529ca4a90ba118456224107e9132ee1100c443362390ee463a80136b141920c4b427388890ac3ca3f0a06c99e3572808964cce10046b82308680091a01a10bd04f12b182d0b2442a31c1028d463de3f6025c5ae6e83639e80d2656f2829fbc62c8630d09e74d946970960e107c65bb15095081b229c05a9d94f087d42041584d243e
  | 15 => 0x501fb800034028c4a10aa000000025623f0c0c1200000d9c32e9293941efc6e224a10106b512877810e92803822752c49908bba70e3ba923079e2f00a592d8dba56429895d887e57c40487e040a3ae294227c3028960612478c2059e1360270b5a89c39187eca9e25204307d48520004199aecbb02493af0878ef841428906346c47e918e0284c9a7da038172421e06e09814d81700bd0281a350764fb0000000a4885100000011425bc104800000000039480006301d000001bc9080001f51f6cbd200000000000002652ad04d4f5c07e2f800003ae0004029cc80000004119f2c3e47b71359320000706092178041600000000001f24d31f480004f45d02ac81f4b720003188cc41c40003f88b48f645461a700000002c0083118856039419a800103e38a00020b07fc7943c4068d1842d81b9a280de817f151800000069a23723a068c7772c798b42942f717085b041a6f30b01fd51961b1425a3c025642b0b4849400084c1e39b4845009f0000fb0a380000148000cb60001ad95e421000004a0a2000078200980000001b047f19502203d82fa8000b527c615b0000c1e8613fb0faca7c0d420200006be1cc0000000f987b3000000011a50236d06a80000003398e841aa3d74940644aba2a22a0067876233343411cc1cc62a3e880d4d2c23a0b780e8da60aa02d9ac120842639208590d87df0bb13445b29343d51b8c27a2c1000219cbb6678472839403e8c000187540000001b90d3c0005e200021d0c5c0002978b7027c30420d05400042f84239cb8000378272800000079800016691940000000000e4041239d952528210332f111090a14324ea344b3e0173230a406724c13a8185cb8c0a81670224fa444604e853c0006620df0d2492625f2379fb43c20004aa843402c8d51da1974f5233e2bb97848d41093c80000000069497946884801d2f5112c5264810001520eba0001f7000000000000000004c40102c517cc0006cd203815c20862b10ba194b1c0b246b0cfc1e80000dd1f2485a86612114dc8327681bf9420a7051004522e81ee2811e40fb42e85674461b50fca5bf05c98f8b56000298172807002d0000000ff267624587e46181d200010ec71e00000000000007574ab13f07a049c1018bcc0008621700894dbe3170739bf471276a323987ce720442f38558ad03c21ad18d112a1e900000008f28c50ae9b0ca2278a43800009ae783417229c8d273a4a6090084e644499254404c8190799d240c82e40dd94b4b5e7890c18f7052485e13b000000000000024ac00010a0000728fd4233442a01c00049b333000033800000000010702681901a0cafe6c23a90f6c7225b022c87780000001be0af40002eb44789dc64a91500017ec23642f25b85c400000000023e44b41980001514e8288e21c879903a305051a16c00015900020
  | 16 => 0x22c17a14544823df44500000000002b80bec00044240680000005c51df0cf00006c822880011b81c2000096c6222691830f10d9e6cb00003a800095c1cb25100000000ce800000087a0001a90c9e3a039aa0f000088b42e00002645743e8000022e30a27b08dc1348a33c3a54800059c06002f04301db0000b781b85c7000026cd5e8021a91fcca1a47424009112027d9219800046277a1ed0548ecc000232100c73e4ea00018dc1f430b3f10000bcc6ae4840000f940000000b0d08c01920600002f800040c105494400000008706d61c933f179400000017e032cc300404180bf43e05b21ec8f886042aa422a06822a6f22fb1c780000002c4114d1e85270e58af91ba66b0000d145401280b080000006431d223509f43e140980000546700810c6867a6f1437817800000000024c00009541650f04bda6cc0001ed80007a22d4000016e4df1d1965049836613880000003b036c8ba497e00020485e889c4ba471a49c46061509a0b9d26e00000019f02526f039604048644c40000000c288c8000200c4c803e31b0000a164a13880e18dde5c023e9f14ef62470218028d743ad259800091a8f70001ea087000046998c87cc57e0001f9d0b22584528cec7e46c91aa0cad2920590c793acc7a1ee11524b40c6380163124852c85a2b695287ec13c0b4078116260115f8d7888e3e548e99c4ba80330c10dbcd285b64869e90bf000000013b88d84d00000000b5c0003ff955817e59948c866c7066054581ed4a2e0903ada3c85d400027b8000c324d5056800096a07a0000efc5d04
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x4708c51002ff0708c51002ef7608c51002ff3608c51014f77508c51014f75508c51014ff2308c51014ff2208c51004cff764c51000cfe764c51012cfd764c51000cfc764c510006df634c51004edc634c51002fd4314c510005fb704c51000df8704c51002ff0104c51000df4764c51004ef4764c51000cf4764c510005f7744c510005f5744c510006f7644c510006f5644c51002df7734c51002fd7734c510007d7634c51004ef6634c51004ef4634c510007d4634c510005f7724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c51012ff0704c51002ef7604c51002ff3604c51012f77504c51012f75504c51012fd7304c51012ff2304c51012fd5304c51012ff2204c5102adf6768851002ef67688510006f76588510006f5658851002df77488510005f5748851002df77388510005f573885100ddf57288510016f66288510016f46288510037e64288510007e5428851002ff3708851000df6708851000df4708851002ff0708851002ef7608851002ff360885100f77750885100f77550885100f7f230885100f7f22088510014ff764851000cfe76485100dcfd764851000cfc7648510006ef6248510016ec624851002fe42148510005fb704851000df8704851002ff0104851000df47648510016f4764851000cf47648510006f76548510006f56548510005f77448510005f57448510005f77348510005f5734851002df7724851002fe77248510007e76248510016f66248510016f46248510037e46248510037e63248510007e53248510007f3704851000df6704851000df470485100dff0704851002ef7604851002ff360485100df7750485100df7550485100dff230485100dfe720485100dff220485100dfe5204851002df8764c11004ef8764c11002cf8764c110006fb644c110006f9644c11000dfb734c11000fdb734c110007db634c11004efa634c11004ef8634c110007d8634c110007da434c110007d9434c110005fb724c110007db324c110007d9324c110007f3714c11002dfa714c11002df8714c110007f0714c11000efb614c11000ff3614c110007f2414c110007f1414c110007db314c110007f2314c110007d9314c110007f1314c110007d1314c110007f2214c110007f1214c11002df87648110016f8764811002cf87648110006fb6548110006f96548110005fb7348110005f9734811000dfb724811000feb7248110007eb6248110016fa6248110016f86248110037e86248110037ea4248110007e94248110037ea3248110007e93248110007f3714811002dfa714811002df87148110007f0714811000efb614811000ff36148110007f24148110007f14148110007f23148110007f13148110037eb2148110037f22148110007e92148110037f12148110007e12148110
  | 1 => 0x8910004fd74d891001cfc74d891004cfe73d8910004fd73d8910006ef52d8910036ec52d8910036ee42d891002cfe71d891000cfd71d891002cfc71d8910036ef21d891002cff70d891000cfe70d891002cfd70d891000cfc70d89100f67f50d89100f67d50d89100f6ef20d89100f6ed20d8910036ec62589102c5f77158910004ff7558910024fe7558910024fc7558910004ff745891001cfe745891001cfc7458910004ff735891004cfc73589100f4ff7258910006ef7258910036ee32589102c4ff7158910006f771589100dcff7058910006fb70589100de7f50589100de7d5058910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100457c755091001ebe6450910006bd6450910006ef6250910016ec625091004cff76cc910004fe76cc910004fd76cc91004cfc76cc9100457e75cc9100057d75cc91004ede63cc910006dd63cc91002df671cc910005f571cc91000dfa70cc910005f970cc910004ff764c910004fe764c910004fd764c910004fc764c91004ede634c910006dd634c910016ee624c910006ed624c91000dfa704c910024ff765451000cfe76545101bcfd765451000cfc76545100067f65545100267c6554510005fb705451000df8705451002ff010545102bdf6769051002ef6769051002f76759051002f757590510006f76590510006f5659051018df5749051001ef6649051001ef46490510005f57390510006f76390510006f56390510005f572905101aef662905101aef4629051000df6709051000df4709051002ef7609051002ff360905101a77750905101a77550905101a7f230905101a7f2209051001cff765051000cfe765051018cfd765051000cfc7650510006bf645051001ebc645051002fb44150510005fb705051000df8705051000df4765051001ef4765051000cf47650510006f76550510006f5655051002df7745051002fb77450510007b7645051001ef6645051001ef4645051003fb464505102b7b7545051003fb45450510005f77350510006f76350510006f5635051003fb74350510007b54350510005f77250510196f66250510196f4625051003fb74250510007b54250510007f3705051000df6705051000df4705051018ff0705051000df0705051002ef7605051002ff3605051018f77505051018f75505051018fb7405051018fb5405051018ff2305051018ff2205051000cfe76cc51000cfc76cc510006df63cc51004edc63cc51000dfa70cc510005f970cc51010df6768c51002ef6768c51002df7748c510005f5748c510006f7648c510006f5648c51012df5738c51004ef6638c51004ef4638c510005f5728c51002ff3708c51000df6708c51000df
  | 2 => 0x467c5459510004ff735951004cfc73595100467f5359510004ff7259510006ef7259510004ef7259510014fe7259510014fc7259510006ec7259510014ec72595100467f52595102dcff7159510006f771595102d67e51595102d67c51595101bcff7059510006fb70595101be7f50595101be7d50595101befa205951001cfe76d91100457e75d91100057d75d911003ebe64d9110024fe75d91100067e75d91100247e75d9110004fd75d91100067d75d91100047d75d9110024fc75d911004cfe73d9110004fd73d9110014fe72d9110004fd72d9110014fc72d911002cfe71d911000cfd71d911002cfc71d911003ebf41d911002cff70d911000cfe70d911002cfd70d911000cfc70d91101a67f50d91101a67d50d91101a6bf40d91101a6bd40d91101a6fa30d911003ebc6459110005df7359110005dc73591102cdf77159110004ff7559110024fe7559110024fc75591101a4ff7459110006bf7459110004ff7359110006df7359110004df735911004cfc7359110006dc735911004cdc735911003ebf4359110004ff7259110014fe7259110014fc725911003ebf42591102ccff7159110006f7715911018cff7059110006fb705911018e7f505911018e7d505911018efa3059110004ff7655110004fe7655110004fd7655110004fc765511004cfe76d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d1002cfe71d8d1002cfc71d8d1002cff70d8d1000cfe70d8d1002cfd70d8d1000cfc70d8d1014e7f50d8d1014e7d50d8d1014edf30d8d1014edd30d8d10006df6398d1012df57198d1016df77158d10004ff7558d10024fe7558d10024fc7558d10004ff7458d1001cfe7458d1001cfc7458d10006df7358d10004ff7258d10014fe7258d10014fc7258d1016cff7158d10006f77158d1012cff7058d10006fb7058d1012e7f5058d1012e7d5058d1014cfe7618d100457e7518d100057d7518d1003dbe7418d10005bd7418d1004ede6318d10006dd6318d10035ee7218d10005ed7218d1004cff7694d10004fe7694d10004fd7694d1004cfc7694d10006df6394d1004edc6394d10035ee7294d10005ed7294d1002df67194d10005f57194d1000dfa7094d10005f97094d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100267e6554d100067d6554d10006df6354d1004edc6354d1004cff7690d10004fe7690d10004fd7690d1004cfc7690d1002df67190d10005f57190d1000dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1001ebe6450d10006bd6450d10014fe76d8910036ee62d8910024fe75d8910004fd75d8910024fc75d891001cfe74d
  | 3 => 0xf7690f1002cfe7690f10004fd7690f1002cfc7690f1002df67190f10005f57190f10004ff7650f1002cfe7650f10004fd7650f1002cfc7650f1001ebe6450f10006bd6450f1002df67150f10004ff7558b10024fe7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b1004cfc7358b1002eef7258b10056ee3258b1002cff7158b1000cfe7158b1002cfd7158b1000cfc7158b1002eee2158b1002eec2158b100de7f5058b100de7d5058b100deef2058b100deed2058b1002efa1058b1002ef91058b10004ff7654b1002cfe7654b10004fd7654b1002cfc7654b100267e6554b100067d6554b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b100057f7550b100657c7550b1001ebe6450b10006bd6450b102feef6250b10016ec6250b1002df67150b102ffe62150b1004cff76ccb1002cfe76ccb10004fd76ccb1002cfc76ccb100657e75ccb100057d75ccb1004ede63ccb10006dd63ccb1002df671ccb10005f571ccb10004ff764cb1002cfe764cb10004fd764cb1002cfc764cb1004ede634cb10006dd634cb10016ee624cb10006ed624cb1002df6714cb1002df776507102f6f7765071002ef76550710006f5655071002fb7745071002fb7645071001ef6645071002ef4645071002fb464507102efb7545071005fb45450710005f7735071002ef76350710006f5635071005fb74350710007b54350710005f77250710196f6625071002ef4625071005fb74250710007b5425071000df6705071000df4705071018f77505071018f75505071018fb7405071018fb5405071002df7764c710006f7764c710005f7744c710005f5744c71002ef7644c710006f5644c71002fd7734c71002fd7634c71004ef6634c71002ef4634c71002fd4634c710005f7724c710007d7324c710007d5324c71000df6704c71000df4704c71012f77504c71012f75504c71012fd7304c71012fd5304c71002df776487102e6f7764871002ef76548710006f56548710005f77448710005f57448710005f77348710005f5734871002fe7724871002fe76248710016f6624871002ef4624871002fe46248710057e63248710007e5324871000df6704871000df470487100df7750487100df7550487100dfe720487100dfe52048710024fe76d95100467e65d951001cfe74d9510004fd74d951001cfc74d951004cfe73d9510004fd73d9510014fe72d9510004fd72d9510014fc72d951002cfe71d951000cfd71d951002cfc71d95100467f51d951002cff70d951000cfe70d951002cfd70d951000cfc70d95101d67f50d95101d67d50d95101d6fa20d95100467c6559510005ef7259510035ec72595102ddf771595101d4ff75595100067f7559510004ff745951001cfe745951001cfc74595100067e5459510
  | 4 => 0x41200bf7952541200bf7852541200bfea4254120007e942541200bfea3254120007e93254120005fb71541200777b51541200077a51541200077951541200777851541200bfeb2154120007e921541200777b76541200267b76541200bf7876541200267876541200077b74541203077a74541200077974541203077874541200077b64541200067b64541203077a64541200077964541200067964541203077864541200077b73541200077a73541200077973541200077873541200077b63541200077a63541200077963541200077863541203077b43541200077a43541200077943541203077843541200bf7b72541200076b72541200bf7a72541200bf7972541200bf7872541200bf68725412000f7b625412000e7b625412000f6b62541200bf7b42541200bf7a42541200bf6a42541200bf7942541200076942541200bf7842541200bf7b32541200bf7a32541200bf6a32541200bf7932541200076932541200bf7832541200077b71541200077a71541200077971541200077871541200077b61541200077a61541200077961541200077861541203077b41541200077a41541200077941541203077841541200077b31541200077a31541200077931541200077831541200bf7b21541200bf6b21541200bf7a21541200bf7921541200076921541200bf78215412002e7f7559710004ff745971001cfe745971001cfc74597100067e54597100667c5459710004ff735971004cfc73597100667f5359710004ff7259710014fe7259710014fc72597100667f525971002cff715971000cfe715971002cfd715971000cfc715971002e7e515971002e7c515971002ef6415971002ef621597101be7f50597101be7d5059710004ff7559310024fe7559310024fc755931002ebf7459310006bf545931005ebc5459310004ff735931004cfc735931005ebf4359310004ff7259310014fe7259310014fc725931005ebf425931002cff715931000cfe715931002cfd715931000cfc715931002ebe415931002ebc415931002ef6315931018e7f505931018e7d505931018ebf405931018ebd4059310004ff765531002cfe7655310004fd765531002cfc7655310004ff7558f10024fe7558f10024fc7558f10004ff7458f1001cfe7458f1001cfc7458f1002edf7358f10004ff7258f10014fe7258f10014fc7258f1002cff7158f1000cfe7158f1002cfd7158f1000cfc7158f1002ef64158f1002ede3158f1002edc3158f1012e7f5058f1012e7d5058f1012edf3058f1012edd3058f1002efa1058f1002ef91058f1004cff7694f1002cfe7694f10004fd7694f1002cfc7694f10055ee7294f10005ed7294f1002df67194f10005f57194f10004ff7654f1002cfe7654f10004fd7654f1002cfc7654f100267e6554f100067d6554f1004cf
  | 5 => 0x7eb704c92000dee704c92000dec704c9201efe8704c920016ef604c920017eb604c9201ef6f504c9201efea504c9201ef6d504c9201efcf304c9201efcd304c9201efea104c92002cfe76d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d852004cfe73d8520004fd73d852000cfd72d852030eee32d8520006ed32d852030ef621d852030ef521d852000cfe70d8520014fd70d852000cfc70d85202c67f50d85202c67d50d85202c6f710d8520006f76198520035f97098520055fb70585200757e75185200057d751852006dbe7418520005bd7418520005de7318520005dd731852002ef66118520006f56118520004fe7694520004fd769452002cfc769452006dbe7494520005bd7494520015ee7294520005ed729452000dfa7094520005f97094520004ff7654520004fe7654520004fc76545200267e65545200067d655452000dfa7054520004fe7690520004fd769052002cfc76905200757e75905200057d7590520015ee7290520005ed7290520006f7619052002ef461905201afe7219052000dfa7090520005f97090520004ff7650520004fe7650520004fc765052001ebe6450520006bd6450520015ee7250520007ad4250520006f7615052002ef46150520197e72150520004fe76cc520004fd76cc52004cfc76cc52004ede63cc520006dd63cc520015ee72cc520005ed72cc520007cd32cc520006f761cc52002ef461cc520004fe768c520004fd768c52002cfc768c520015ee728c520005ed728c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c52004ede634c520006dd634c520015ee724c520007cd324c520004fe760c520004fd760c52002cfc760c5200757e750c5200057d750c52006dbe740c520005bd740c520015ee720c520005ed720c520006f7610c52002ef4610c52000dfa700c520005f9700c52000dec764852002eec764852000cec7648520005ef7448520005ed7448520005ef7348520005ed7348520006ef6348520006ed6348520015ef7148520017e77148520007e7614852002eee614852002eec6148520007e46148520007e65148520007e55148520007eb704852000dee704852000dec70485200dfe87048520016ef6048520017eb60485200df6f50485200dfea50485200df6d50485200dfea1048520015f87654120026f87654120014f8765412000dfb755412000f7b75541200077b6554120026fa6554120026f86554120077786554120006fb6454120006f964541200777b54541203077a54541200077954541200777854541200777b53541200077a5354120007795354120077785354120007eb7254120015fa7254120015f872541200bfe8725412000efb625412000feb62541200bf7b52541200bf7a525
  | 6 => 0xd40d912001cff76591200057f75591200757c755912006ebc645912032def725912033dfb7059120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c7559120334ff7459120006bf7459120004ff735912004cfc735912032cff7259120006ef72591200aeee3259120004ff715912002cfc715912006ebf415912021cff7059120006fb705912021e7f505912021efa505912021e7d5059120004ff7655120004fe7655120004fd7655120004fc765512004cfe76d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d2000cff72d8d20014fe72d8d2000cfd72d8d20014fc72d8d20326ee42d8d20326df32d8d20326dd32d8d2002cfe71d8d20004fd71d8d20326ef21d8d20014ff70d8d20014fd70d8d2031e7f50d8d2031e7d50d8d2031edf30d8d2031edd30d8d2031efa10d8d201ecfd7698d200757e7598d200057d7598d20006df6398d201eded7298d2007df97098d2004cff7658d20205ef7258d20005f77158d20005f47158d20095fb7058d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d20204ff7258d20006ef7258d2007eee4258d20004ff7158d20006f77158d20004f77158d2002cfc7158d20006f47158d2002cf47158d2007eef2158d201ecff7058d20006fb7058d201ee7f5058d201ee7d5058d201eefa1058d2031cfe7618d2004ede6318d20006dd6318d2004cff7694d20004fe7694d20004fd7694d2004cfc7694d20015ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200267c6554d2004cff7690d20004fe7690d20004fd7690d2004cfc7690d20015ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20015ee7250d2000dec765092001eec765092000cec76509200076f75509200076c7550920006ef6550920006ed6550920015ef7450920017af7450920007af645092001eee645092001eec645092006fac645092006fae5450920007ad5450920005ef7350920006ef6350920006ed6350920007ae435092006fac4350920005ef71509202feec615092006faf4150920007eb705092000dee705092000dec705092021fe87050920016ef6050920017eb605092021f6f505092021fea505092021f6d505092021faf405092021fad405092021fea105092000dec764c92004eec764c92000cec764c9201feee654c9201feec654c920005ef744c920005ed744c920006ef644c920006ed644c920015ef734c920017cf734c920007cf634c92004eee634c92004eec634c920007cc634c920007ce534c920007cd534c920317cf434c920317cc434c920005ef714c920
  | 7 => 0xc53004ede76cc53004ddf74cc530005dd74cc530005dd72cc530006df62cc53002ede61cc53002edc61cc53004fdb70cc53000dde70cc53000ddc70cc53004fd870cc53004edf60cc53004fdb60cc53016f5f50cc53016f5d50cc53016fda40cc53016fda10cc53000cfe768c53012ddd738c530006f7618c53002ef4618c53000dfa708c530005f9708c53000cfc764c530006f7614c53002ef4614c53004fd4314c530005fb704c53000df8704c53004fd8304c53000ddc764c53002edc764c53000cdc764c530005df744c530005dd744c530005df724c530006df624c53004ddf714c53004fd7714c530007d7614c53002ede614c53002edc614c530007d4614c530007d6414c530007d5414c530007db704c53000dde704c53000ddc704c53012fd8704c53004edf604c53004fdb604c53012f5f504c53012f5d504c53012fda404c53012fda104c530004fe7688530004fd768853002cfc768853004dde7388530005dd738853000dfa7088530005f97088530004ff7648530004fe7648530004fc764853004dde7348530005dd7348530016ee6248530007cd324853004df8765013001ef8765013004cf87650130006fb6550130006f9655013000dfb745013000fbb7450130007bb645013001efa645013001ef86450130087b86450130007db735013004dfa735013004df87350130007d8735013000efb635013000fdb6350130087bb4350130087da4350130007b94350130087d94350130007994350130087bb4250130007b94250130007db3250130007d93250130005fb7150130087bb4150130007b94150130007db3150130007d93150130024fe76d95200767e65d952022cfd75d952001cfe74d9520004fd74d952001cfc74d95200067e54d95200767c54d952004cfe73d9520004fd73d95200767f53d952000cff72d9520014fe72d952000cfd72d9520014fc72d952035e7f52d952035e7d52d952035eee42d952002cfe71d9520004fd71d9520014ff70d9520014fd70d95203567f50d95203567d50d9520024ff76595200767c655952034def72595200cdfb7059520354ff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff735952004cfc735952034cff7259520006ef72595200be7e52595200be7c52595200beee4259520004ff715952002cfc71595200767f515952022cff7059520006fb705952022e7f505952022e7d505952001cfe76d912006ebe64d9120024fe75d9120004fd75d9120024fc75d912021cfd74d912004cfe73d9120004fd73d912000cff72d9120014fe72d912000cfd72d9120014fc72d9120346bf42d9120346bd42d9120346ee32d912002cfe71d9120004fd71d9120014ff70d9120014fd70d91203367f50d9120336fa50d91203367d50d9120336bf40d9120336b
  | 8 => 0x4edf6050d3004fdb6050d3023f5f5050d3023f5d5050d3023f9f4050d3023fda4050d3023f9d4050d3023fda1050d30014fe76d893008d7e75d89300057d75d893007eee62d8930024fe75d89300067e75d89300247e75d8930004fd75d89300067d75d89300047d75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893000cfd73d8930014fc73d893007eee32d893002cfe71d8930004fd71d893004cfd70d89302067f50d89302067d50d8930206ef20d8930206fa10d893007eec6258930005f77158930005f47158930004ff7654930004fe7654930004fc7654930004ff7650930004fe7650930004fc76509300057f755093008d7c7550930006bf645093001ebc64509300079e4350930016ee625093036dde76cc93004ede76cc93004f5e75cc93004f5d75cc930006df65cc930006dd65cc93004ddf74cc930005dd74cc93020ede64cc93020edc64cc9301eddd72cc930016de62cc930016dc62cc930005dd71cc93000dde70cc93000ddc70cc93004edf60cc93004fdb60cc9302075f50cc9302075d50cc930207da40cc930207da10cc93000cfc764c930006ef624c930016ec624c93004fcc324c930005fb704c93000df8704c93000ddc764c930016dc764c93000cdc764c930006df654c930006dd654c930005df744c930005dd744c9301f6de644c9301f6dc644c93004ddf724c93004fcf724c930007cf624c930016de624c930016dc624c93007fcc624c930367cf524c93007fcc524c93007fce424c930007cd424c930005df714c93007fcf214c930007db704c93000dde704c93000ddc704c9301efd8704c93000dd8704c93004edf604c93004fdb604c9301ef5f504c9301ef5d504c9301efda404c9301efcf204c9301efda104c93002cfe76d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d8530014fe72d8530004fd72d8530014fc72d8530006df32d8530006dd32d8530006f721d8530006f421d853004cfd70d853016e7f50d853016e7d50d853016ef710d8530006f7619853008d7e75185300057d7518530085be7418530005bd741853007dee7218530005ed721853002ef66118530006f56118530004fe7694530004fd769453002cfc7694530085be7494530005bd749453004dde7394530005dd7394530006f7619453002ef4619453000dfa7094530005f97094530004ff7654530004fe7654530004fc76545300267e65545300067d6554530006f7615453002ef46154530004fe7690530004fd769053002cfc769053008d7e75905300057d759053004dde7390530005dd739053002ef6619053000dfa7090530005f97090530004ff7650530004fe7650530004fc765053001ebe6450530006bd64505300079d435053000dfa705053010dde76c
  | 9 => 0xc704c73012f5f504c73012f5d504c73002cff768873004cfe7688730004fd768873004dde7388730005dd7388730004ff7648730004fd764873004cfc764873004dde7348730005dd7348730016ee6248730006ed6248730007cd3248730024fe76d953008e7e65d953001cfe74d9530004fd74d953001cfc74d953004cfe73d953000cfd73d953004cfc73d953008e7f53d9530014fe72d9530004fd72d9530014fc72d953002cfe71d9530004fd71d953004cff70d953004cfd70d95302867f50d95302867d50d9530286fa40d953008e7c6559530005bf7459530085bc745953038ddf7359530284ff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc745953008e7f545953038cff7359530006df73595303867e53595303867c5359530004ff7259530014fe7259530014fc72595300067e525953008e7c5259530004ff715953002cfc715953008e7f515953026cff7059530006fb705953026e7f505953026e7d505953026efa405953001cfe76d9130086be64d9130024fe75d9130004fd75d9130024fc75d9130006bf54d9130086bc54d913004cfe73d913000cfd73d913004cfc73d9130086bf43d9130014fe72d9130004fd72d9130014fc72d9130086bf42d913002cfe71d9130004fd71d913004cff70d913004cfd70d91302567f50d91302567d50d9130256bf40d9130256bd40d9130086bc645913037ddf7359130004ff7559130024fe7559130024fc7559130254ff7459130006bf745913037cff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff715913002cfc7159130086bf415913023cff7059130006fb705913023e7f505913023e7d5059130004ff7655130004fe7655130004fd7655130004fc76551300267e65551300067d6555130024ff7654d3000cfe7654d3026cfd7654d3000cfc7654d300067f6554d300267c6554d30005fb7054d3000df87054d3004fd83054d30375de7690d3004ede7690d30006df6590d30006dd6590d3023ddd7490d3001ede6490d3001edc6490d30005dd7290d300879f4290d30005dd7190d3004fdb7090d3000dde7090d3000ddc7090d3004fd87090d3004edf6090d3004fdb6090d302575f5090d302575d5090d30257da4090d30257da1090d3001cff7650d3000cfe7650d3023cfd7650d3000cfc7650d30006bf6450d3001ebc6450d3004f9c4350d30005fb7050d3000df87050d3004fd83050d3000ddc7650d3001edc7650d3000cdc7650d30006df6550d30006dd6550d3004ddf7450d3004f9f7450d300079f6450d3001ede6450d3001edc6450d300879c6450d30005df7250d30005df7150d300879f4150d30007db7050d3000dde7050d3000ddc7050d3023fd87050d30
  | 10 => 0x9730004ff7559330024fe7559330024fc755933004ebf745933004cff735933000cfe735933004cfd735933000cfc735933004ebe435933004ebc4359330004ff7259330014fe7259330014fc7259330004ff715933002cfc715933009ebf415933023e7f505933023e7d505933023ebf405933023ebd405933004efa305933004ef93059330004ff765533004cfe7655330004fd765533004cfc76553300267e65553300067d655533004ddf7650f303aedf7650f3004edf6550f30006dd6550f3004f9f7450f3004f9f6450f3001ede6450f3004edc6450f3004f9c6450f30005df7250f30005df7150f3009f9f4150f3000dde7050f3000ddc7050f3023f5f5050f3023f5d5050f3023f9f4050f3023f9d4050f30004ff7558b30024fe7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3000cfe7358b30014fd7358b3000cfc7358b3004eef7258b30006ef5258b30096ec5258b30096ee4258b3004eef3258b3004eec3258b30004ff7158b3002cfc7158b3004edf3158b30096ef2158b301ee7f5058b301ee7d5058b301eeef2058b30004ff7654b30004fd7654b3004cfc7654b30004ff7650b30004fd7650b3004cfc7650b300057f7550b300a57c7550b303a6bf6450b3001ebc6450b3004dde7350b303a79e4350b30016ee6250b30006ed6250b3004ddf764cb3039edf764cb3004edf654cb30006dd654cb30005df744cb30005dd744cb301f6de644cb3004edc644cb3004fcf724cb3004fcf624cb30016de624cb30016dc624cb3004fcc624cb30397cf524cb30097cc524cb30097ce424cb30007cd424cb30005df714cb30097cf214cb3000dde704cb3000ddc704cb301ef5f504cb301ef5d504cb301efcf204cb30004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc745873000cfc7358730004ff7258730014fe7258730014fc725873004edf3258730006dd325873004ef7715873004ef7315873004ef4315873012e7f505873012e7d505873004efa305873004ef9305873012ef7105873002cff769473004cfe7694730004fd769473009dbe7494730005bd749473004dde7394730005dd7394730004ff7654730004fd765473004cfc76547300267e65547300067d655473002cff769073004cfe7690730004fd76907300a57e75907300057d759073004dde7390730005dd739073002ef66190730006f56190730004ff7650730004fd765073004cfc765073001ebe6450730006bd645073004dde73507300079d435073002ef66150730006f5615073004ddf764c730006df764c730005df744c730005dd744c730005df724c730006dd624c73004fd7714c73004fd7614c73002ede614c73002edc614c73004fd4614c730007d6414c730007d5414c73000dde704c73000dd
  | 11 => 0xdfa70cc540005f970cc540004fe768c540004fd768c54002cfc768c54001dbe748c540005bd748c540006df638c54004edc638c54002ef6618c540007b5418c540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c540007b5414c540004fe760c540004fd760c54002cfc760c5400b57e750c5400057d750c54001dbe740c540005bd740c540006df630c54004edc630c5400adee720c540005ed720c54000dfa700c540005f9700c540004fe7688540004fd768854002cfc768854001dbe7488540005bd7488540007ad4288540004ff7648540004fe7648540004fc764854001dbe7448540005bd744854001df87654140026f8765414001cf8765414000dfb755414000f7b75541400077b6554140026fa6554140026f865541400b7786554140007bb745414001dfa745414001df874541400c7b8745414000efb645414000fbb64541400c77b54541400c77a54541400c77954541400c7785454140005fb73541400b77b53541400077a53541400077953541400b77853541400c7bb4354140007b94354140006fb62541400b77b52541403b77a52541400077952541400b77852541400c7bb4254140007b942541400b77b51541400077a51541400077951541400b77851541400c7bb4154140007b941541400b77b76541400267b76541400c77876541400267876541400c77b74541400073b74541400c77a74541400c77974541400c77874541400c738745414000f7b645414000e7b645414000f3b64541400077b73541400077a73541400077973541400077873541400077b63541400077a63541400077963541400077863541400c77b43541400c73b43541400c77a43541400c77943541400073943541400c77843541400077b72541403b77a72541400077972541403b77872541400077b62541400067b62541403b77a62541400077962541403b77862541400c77b42541400c73b42541400c77a42541400c77942541400073942541400c77842541400077b32541403b77a32541400077932541403b77832541400077b71541400077a71541400077971541400077871541400077b61541400077a61541400077961541400077861541400c77b41541400c73b41541400c77a41541400c77941541400073941541400c77841541400077b31541400077a31541400077931541400077831541403b77b21541400077a21541400077921541403b778215414004e7f7559730004ff745973001cfe745973001cfc74597300a67f545973004cff735973000cfe735973004cfd735973000cfc735973004e7e535973004e7c535973004ede4359730004ff7259730014fe7259730014fc72597300067e52597300a67c525973004edf3259730004ff715973002cfc71597300a67f515973026e7f505973026e7d505
  | 12 => 0xf6350d4004ebe6350d4004ebc6350d400079c6350d400079e5350d400079d5350d40005bf7250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d4023fb87050d4001ebf6050d4001fbb6050d4023f3f5050d4023fba5050d4023f3d5050d4023fba3050d40014fe76d89400aeee62d8940024fe75d8940004fd75d8940024fc75d894000cfd74d8940014fc74d894004cfe73d8940004fd73d89400aeee42d89403d6ed42d894002cfe71d8940004fd71d89403d6bf41d894001cfd70d894032e7f50d894032efa50d894032e7d50d894032eef20d89400057f75589400b57c75589400aeec62589403cdfb7058940004ff7654940004fe7654940004fc765494000dbc7650940016bc765094000cbc76509400073f75509400073c7550940006bf6550940006bd6550940005bf73509403a6bc635094001dbf725094001faf7250940007af6250940016be6250940016bc62509400afac62509400afae5250940007ad52509400afae3250940005bf71509400afac2150940007bb705094000dbe705094000dbc705094021fb8705094001ebf605094001fbb605094021f3f505094021fba505094021f3d505094021fba305094021faf2050940004fe76cc940004fd76cc94004cfc76cc9400b57e75cc9400057d75cc94001dbe74cc940005bd74cc940006df63cc94004edc63cc94020f9f43cc94000dfa70cc940005f970cc940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940006df634c94004edc634c9401f79f434c940016ee624c940007ad424c94002cfe76d8540024fe75d8540004fd75d8540024fc75d854000cfd74d854004cfe73d8540004fd73d85403c6bf43d8540006bd43d8540014fe72d8540004fd72d8540014fc72d85403c6bf42d8540006bd42d85403c6f641d85403c6f541d854001cfd70d85402ce7f50d85402ce7d50d85402cefa30d85402cef710d85400b57e75985400057d7598540006f7619854003df97098540005df7358540005dc735854005dfb705854002ef66118540006f56118540004fe7694540004fd769454002cfc769454001dbe7494540005bd7494540004ff7654540004fe7654540004fc76545400067f65545400267c655454000dbc765054002ebc765054000cbc765054019ebe655054019ebc6550540005bf7350540006bf6350540005bf7250540006bf625054001dbf715054001fb77150540007b7615054002ebe615054002ebc6150540007b46150540007b65150540007b551505403bfb721505403bfb42150540007bb705054000dbe705054000dbc705054018fb8705054001ebf605054001fbb605054018f3f505054018fba505054018f3d505054018fba3050540004fe76cc540004fd76cc54004cfc76cc54001dbe74cc540005bd74cc540
  | 13 => 0xc55038775310c55010d7f700c55000d7e700c55010f7a700c55000d7a700c55010d7d700c5502d779700c55000579700c55000d7c700c55010e7f600c5501277b600c55010f7a400c55010f7a200c5502d57f76885500057e76885500057d76885502d57c76885502d57f74885500c57e74885500057d74885502d57c74885502d57f73885503857e73885500057d73885502d57c73885500dd7d72885500076f62885500bf6c62885500bf6e42885500076d42885502ad7e71885502d77661885500077561885502d76f21885500bf7721885502d77421885500f57f708855000d7e70885500f57d708855000d7c70885500f67f60885501077b60885500f77a40885500f77a20885500f77710885500057f76485500057e76485500057d76485500057c76485500057f74485500c57e74485500057d74485500c57c74485500057f73485503857e73485500057d73485503857c73485500f57f72485500bf6e32485500076d32485502c57f71485500077661485500077561485500bf7721485502d76e21485502d76c21485500bf7421485500dd7f704855000d7e704855000d7c70485500de7f60485500ef7b60485500df7a40485500df6f20485500df7a2048550024fe76d95400b67e65d954029cfd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d95403f67f54d95403f67d54d954004cfe73d9540004fd73d9540014fe72d9540004fd72d9540014fc72d95400067e52d95400b67c52d95403f6bf42d954002cfe71d9540004fd71d95400b67f51d954001cff70d954001cfd70d95403ee7f50d95403ee7d50d9540024ff76595400b67c65595403e5bf74595400d5fb70595403ecff75595400067f75595403e4ff7459540006bf74595400c67e54595400c67c5459540004ff735954004cfc73595400b67f5359540004ff7259540014fe7259540014fc72595400c6bf4259540004ff715954002cfc715954029cff7059540006fb705954029e7f505954029e7d505954004cfe76d8d40024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d403dede43d8d403dedd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4002cfe71d8d40004fd71d8d403debf41d8d4001cfd70d8d4037e7f50d8d4037e7d50d8d4037edf30d8d40006df6398d40085f97098d4009dfb7058d400b57e7518d400057d7518d4004ede6318d40006dd6318d400adee7218d40005ed7218d40005f67118d40005f57118d40004fe7694d40004fd7694d4004cfc7694d4001dbe7494d40005bd7494d400adee7294d40005ed7294d4000dfa7094d40005f97094d40004ff7654d40004fe7654d40004fc7654d400267e6554d400067d6554d4000dfa7054d4000dbc7650d4004ebc7650d4000cbc7650d4001dbf7350d4001f9f7350d400079
  | 14 => 0x40f7a201855040f77101855040f7510185502d57f76905500057e76905502d67e76905500047e76905500057d76905502d67d76905500047d76905502d57c769055018d7d74905503857e73905500057d73905500bd7e72905500057d72905502d57c72905502bd7e71905502d77661905500077561905502d73f41905500c77741905502d77441905504077721905502d77421905501a57f709055000d7e70905501a57d709055000d7c70905501a67f60905501b77b60905501a77a40905501a77a20905501a77710905500057f76505500057e76505500057d76505500057c76505501a57f74505500073f64505500c73c64505500057f73505503857c73505500c73f43505500073d43505500057f72505500bd7e72505500bd7c72505500c73f42505500073d42505502cd7f71505500077661505500077561505500c77741505502d73e41505502d73c41505500c77441505503ff7721505503ff74215055018d7f705055000d7e705055000d7c705055018e7f605055019f7b605055018f3f405055018f7a405055018f7a20505503857f76cc5500057e76cc5500057d76cc5503857c76cc5503857f74cc5500c57e74cc5500057d74cc5503857c74cc5500bd7e72cc5500057d72cc5500bd7c72cc5503875f32cc5500075d32cc55016d7f70cc55000d7e70cc55016d7d70cc55000d7c70cc55016e7f60cc5501877b60cc55016f7a40cc55016f5f30cc55016f7a20cc5502d57f768c5500057e768c5500057d768c5502d57c768c5502d57f748c5500c57e748c5500057d748c5502d57c748c55012d7d738c5500bd7e728c5500057d728c5502d57c728c55010d7e718c5502d776418c55000775418c5502d75f318c55038777318c55014d7f708c55000d7e708c55014d7d708c55000d7c708c55014e7f608c5501677b608c55014f7a408c55014f7a208c55014f77108c5500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5500c57e744c5500057d744c5500c57c744c5500057f724c5500bd7e724c5500bd7c724c5500075f324c5500075d324c55000776414c55000775414c55038777314c5502d75e314c55012d7f704c5500077b704c5500057b704c55000d7e704c55000d7c704c55012f78704c55000d78704c55012e7f604c5501477b604c55012f7a404c55012f7a204c5502d57f760c5500057e760c5502d67e760c5500047e760c5500057d760c5502d67d760c5500047d760c5502d57c760c5502d57f740c5500c57e740c5502d73e740c5500c53e740c5500057d740c5502d73d740c5500053d740c5502d57c740c55016d7e730c5500bd7e720c5502d76e720c5500bd6e720c5500057d720c5502d76d720c5500056d720c5502d57c720c55014d7e710c5502d75f310c5502d776310c5502d75d310
  | 15 => 0xc71509500c73f41509500bf6c215095021d7f705095000d7e705095021f7a705095000d7a705095000779705095000d7c705095021e7f60509502277b605095021f3f405095021f7a405095021f6f205095021f7a20509503857f76cc9500057e76cc9503867e76cc9500047e76cc9500057d76cc9503867d76cc9500047d76cc9503857c76cc9503857f74cc9500c57e74cc9500057d74cc9503857c74cc95036d7e73cc9503875e63cc9500075d63cc95042f5f43cc9503875c43cc9501ed7d72cc9500bf5e32cc9500bf6e32cc9500bf5c32cc9502d57e71cc9500057d71cc9502057f70cc95000d7e70cc9502057d70cc95000d7c70cc9502067f60cc9502177b60cc9502077a40cc9502075f30cc9502077a20cc9500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9500c57e744c9500057d744c9500c57c744c95031d7f734c9500075e634c9500075d634c9504275f434c9504275c434c9502057f724c9500076f624c9500bf6c624c9500bf6e424c9500076d424c9503876f324c9500bf5e324c9500bf5c324c9500bf6c324c9500057f714c9502d57c714c9500bf6f214c9501ed7f704c95000d7e704c95000d7c704c9501ee7f604c9501ff7b604c9501ef7a404c9501ef6f204c9501ef7a204c9500c57e74d85500057d74d85500c57c74d85500067e64d85500067c64d85503857e73d85500057d73d85500067f63d85500067d63d85500bd7e72d85500057d72d85500bd7c72d85500067f62d85500067d62d85500257f70d85500257d70d85502de7f60d855041f7b60d85502df7a40d85502df7a20d85502df7710d85502df7510d85500c57e74985502d73e74985500c53e74985500057d74985502d73d74985500053d74985502d57c74985503857e73985500057d73985500bd7e72985500057d72985502d57c729855040d7e71985502d67f61985500077761985501d57d70985502d77970985500057970985501d67f60985500677b60985501d77a40985501d77a20985500057f74585500c57e74585500c57c74585500067e64585500067c64585500057f73585503857c73585500067f63585500067d63585500057f72585500076f72585500056f72585500bd7e72585500bd7c72585500076c72585500bd6c72585500067f62585500067d62585500077761585502d67e61585501bd7f70585500077b70585500057b70585500477b60585501bf7a40585501bf7a20585502dd7e76185500c57e74185500057d74185502d57c74185503857e73185500057d73185500bd7e72185500057d72185502d57c72185501d57e71185502d67f61185502d77661185502d67d61185500077561185500257f701855000d7e70185500257d701855000d7c701855040e7f60185504177b601855040f7a4018550
  | 16 => 0x8d500057f7458d500073f7458d500053f7458d500c57e7458d500c57c7458d500073c7458d500c53c7458d500067f6458d500067d6458d500075f6358d503867e6358d500057f7258d500bd7e7258d500bd7c7258d500067e6258d500067c6258d500057f7158d502d57c7158d5026d7f7058d500077b7058d500057b7058d5008f7b6058d5026f7a4058d5026f7a2058d5038d7e7618d500c57e7418d500057d7418d503857c7418d502857e7318d503867f6318d503875e6318d503867d6318d500075d6318d500bd7e7218d500057d7218d500bd7c7218d502d57e7118d500057d7118d500257f7018d5000d7e7018d500257d7018d5000d7c7018d504467f6018d5044f7b6018d504477a4018d504475f3018d504475d3018d504477a2018d503857f7690d500057e7690d500057d7690d503857c7690d5023d7d7490d500073f6490d500c73c6490d503757e7390d503875e6390d500075d6390d503873f4390d500c75f4390d503875c4390d500bd7e7290d500057d7290d500bd7c7290d500c73f4290d502d57e7190d500057d7190d502557f7090d5000d7e7090d502557d7090d5000d7c7090d502567f6090d502677b6090d502577a4090d502575f3090d502577a2090d500057f7650d500057e7650d500057d7650d500057c7650d502557f7450d5037d7f7350d500075e6350d500075d6350d500c75f4350d503873e4350d503873c4350d500c75c4350d500057f7250d500bd7e7250d500bd7c7250d500057f7150d502d57c7150d500c73f4150d5023d7f7050d5000d7e7050d5000d7c7050d5023e7f6050d5024f7b6050d5023f3f4050d5023f7a4050d5023f7a2050d5043d7e76d89500c57e74d89500057d74d89500c57c74d89503857e73d89500057d73d89500be7e62d89500bf6e62d89500be7c62d89500bf6e32d89502d57e71d89500057d71d89500bf6c21d89500257f70d89504377b70d895000d7e70d89500257d70d895000d7c70d895034e7f60d89504377b60d895034f7a40d895034f6f20d895034f7a20d895034f6d20d89503557f76589500057f74589500c57e74589500c57c74589500057f73589503857c735895034d7f72589500076f62589500be7e62589500be7c62589500bf6c62589500bf6e42589500057f71589502d57c715895022d7f70589500077b70589500057b70589500777b605895022f7a405895022f7a20589500057f76509500067f76509500047f76509500057e76509500057d76509500057c76509500067c76509500047c76509503357f74509500c73e64509500073d64509500057f73509503857c73509500073e43509500c73c435095032d7f72509500bf6e62509500076d62509500c76f42509500bf3e42509500bf3c42509500bf6c42509500bf6e32509500057f71509502d57
  | 17 => 0x1bf7870545500267f60545500277b60545501bf7a40545501bf7a2054550004fe7690550004fd769055002cfc76905502d57f75905500257e75905500057d75905500257c759055002ef661905502d7765190550007755190550004ff7650550004fe7650550004fc76505500057f75505500257e75505500057d75505500257c7550550006bf645055001ebc645055019f3f54505500c73c5450550007765150550007755150550004fe76cc550004fd76cc55004cfc76cc5503857f75cc5500257e75cc5500057d75cc5500257c75cc550004fe768c550004fd768c55002cfc768c5502d57f758c5500257e758c5500057d758c5500257c758c550004ff764c550004fe764c550004fc764c5500057f754c5500257e754c5500057d754c5500257c754c550005fb704c55000df8704c550004fe760c550004fd760c55002cfc760c5502d57f750c5500257e750c5500057d750c5500257c750c5500c5be740c550005bd740c5500bdee720c550005ed720c55000dfa700c550005f9700c550004fe7688550004fd768855002cfc76885502d57f75885500257e75885500057d75885500257c7588550006ef6288550016ec628855002ef661885502d7765188550007755188550004ff7648550004fe7648550004fc76485500057f75485500257e75485500057d75485500257c75485500077651485500077551485504657e76d91500c67e64d91500c73e64d91500c67c64d91503857e73d91500057d73d91500c73c43d91500bd7e72d91500057d72d91500bd7c72d91502d57e71d91500057d71d91500c73f41d91500257f70d915045f7b70d915000d7e70d91500257d70d915000d7c70d91503e67f60d915045f7b60d91503e73f40d91503e77a40d91503e73d40d91503e77a20d91503ed7f76591503e57f74591500073f64591500c67e64591500c67c64591500c73c64591500057f73591503857c73591500057f72591500bd7e72591500bd7c72591500c73f42591500057f71591502d57c715915029d7f70591500077b70591500057b70591500b77b605915029f7a405915029f7a20591500c57e74d8d500057d74d8d500c57c74d8d500067f64d8d500067d64d8d500bd7e72d8d500057d72d8d500bd7c72d8d500067e62d8d500067c62d8d502d57e71d8d500057d71d8d500257f70d8d500257d70d8d5038e7f60d8d504577b60d8d5038f7a40d8d5038f5f30d8d5038f5d30d8d5038f7a20d8d500c57e7498d500057d7498d503857c7498d504457e7398d503867f6398d500075f6398d500bd7e7298d503876e7298d500bd6e7298d500057d7298d503876d7298d500056d7298d500bd7c7298d502d57e7198d500057d7198d502857d7098d50387797098d50005797098d502867f6098d500a77b6098d502877a4098d502877a209
  | 18 => 0xd75d89500beee62d89500bf6e52d895000cfd75d895034e7d75d895000c7d75d8950014fc75d895001cfe74d8950004fd74d895001cfc74d895004cfe73d8950004fd73d89500be7e52d89500beee52d8950436ed52d89500be7c52d89500beee32d895002cfe71d8950004fd71d89504367f51d89500beec21d8950024fd70d895034eef20d89500beec625895046dfb705895000d7c76549500167c765495000c7c76549500057f74549500c57e74549500c57c74549500057f73549503857c73549500257f72549500276f72549500076f62549500167e62549500167c62549500bf6c62549500bf6e42549500057f71549502d57c71549500077b705495000d7e705495000d7c705495022f7870549500267f60549500277b605495022f7a405495022f7a2054950004ff7650950004fe7650950004fc76509500057f75509500257e75509500057d75509500257c755095001ebe64509500c73e54509500073d5450950016ee62509500bf6e52509500076d525095000dfa7050950004fe76cc950004fd76cc95004cfc76cc9503857f75cc9500257e75cc9500057d75cc9500257c75cc95004ede63cc9503875e53cc9500075d53cc950004ff764c950004fe764c950004fc764c9500057f754c9500257e754c9500057d754c9500257c754c9500075e534c9500075d534c950006ef624c950016ec624c9501ff6f524c9500bf6c524c95002cfe76d855000cfd75d85502de7d75d855001cfe74d8550004fd74d855001cfc74d85500067e54d855041e7c54d855004cfe73d8550004fd73d855041e7f53d85500067d53d8550014fe72d8550004fd72d8550014fc72d855041e7f52d85500067d52d855041ef651d855041ef551d85502d67c51d8550024fd70d85502defa20d85502def710d85500c5be7498550005bd7498550006f76198550045f97098550005ef72585500bdec7258550065fb705855002ef66118550006f5611855000d7e76945501d67e769455000c7e76945500c57e74945502d73e74945500c53e74945500057d74945502d73d74945500053d74945502d57c74945503857e73945500057d73945500bd7e72945500057d72945502d57c72945500257e71945500277671945502d67f61945500077761945502d774619455000d7e70945501d77a70945502d779709455000d7c70945500267f60945500277b60945501d77a40945501d77a209455000d7c765455002e7c765455000c7c76545500057f74545500c57e74545500c57c74545501ce7e64545501ce7c64545500057f73545503857c73545500067f63545500057f72545500bd7e72545500bd7c72545500067f62545500257f715455002777715455000777615455002e7e615455002e7c61545500077461545500077b705455000d7e705455000d7c7054550
  | 19 => 0x87500cf77214875047f6e214875047f6c21487500cf7421487500dd7f704875000d7e704875000d7c70487500df6f204875001cfe76d91500257e75d915000d7d75d91500c6be64d91500c73e54d915000cfd75d91503e67d75d915000c7d75d915001cfc75d91500c67e54d91500c6be54d915045ebd54d91500c67c54d915004cfe73d9150004fd73d915045e7f53d91500c6bc43d9150014fe72d9150004fd72d9150014fc72d915002cfe71d9150004fd71d91500c6bf41d9150024fd70d91503e6bf40d91500c6bc6459150475fb705915000d7c765515001e7c765515000c7c76551500257f74551500273f74551500073f645515001e7e645515001e7c64551500c73c64551500057f73551503857c73551500057f72551500bd7e72551500bd7c72551500c73f42551500057f71551502d57c71551500077b705515000d7e705515000d7c705515029f7870551500267f60551500277b605515029f7a405515029f7a205515004cfe76d8d5000cfd75d8d5038e7d75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d504567f54d8d500067d54d8d50456de53d8d50456dd53d8d503867c53d8d50014fe72d8d50004fd72d8d50014fc72d8d500067e52d8d504567c52d8d5002cfe71d8d50004fd71d8d504567f51d8d50024fd70d8d5038efa40d8d5038edf30d8d50006df6398d500bdee7298d50005ed7298d5008df97098d50005bf7458d500c5bc7458d500a5fb7058d5004ede6318d50006dd6318d5000d7e7694d502867e7694d5000c7e7694d500c57e7494d500057d7494d503857c7494d500257e7394d500275e7394d503867f6394d500075f6394d503875c6394d500bd7e7294d503876e7294d500bd6e7294d500057d7294d503876d7294d500056d7294d500bd7c7294d502d57e7194d500057d7194d5000d7e7094d502877a7094d50387797094d5000d7c7094d500267f6094d500277b6094d502877a4094d502877a2094d5000d7c7654d5004e7c7654d5000c7c7654d500057f7454d500c57e7454d500c57c7454d500067f6454d500257f7354d500275f7354d500075f6354d5004e7e6354d5004e7c6354d500075c6354d500057f7254d500bd7e7254d500bd7c7254d502767e6254d502767c6254d500057f7154d502d57c7154d500077b7054d5000d7e7054d5000d7c7054d5026f787054d500267f6054d500277b6054d5026f7a4054d5026f7a2054d50004fe7690d50004fd7690d5004cfc7690d503857f7590d500257e7590d500057d7590d500257c7590d50006bf6490d5001ebc6490d5004ede6390d503875e5390d500075d5390d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257e7550d500057d7550d500257c7550d500075e5350d500075d5350d50014fe76d89500257e75d895000d7
  | 20 => 0x19d7f76507500257e765075019d7d76507500257c765075019f3f64507500d73c64507500057f73507504857c73507500d73f43507500073d43507500057f72507500cd7e72507500cd7c72507500d73f42507500073d42507502cd7f715075019f76615075019f7561507500d777415075047f3e415075047f3c41507500d774415075048f77215075048f74215075018d7f705075000d7e705075000d7c705075018f3f40507504857f76cc7500257e76cc7501857d76cc7500257c76cc7504857f74cc7500d57e74cc7500057d74cc7504857c74cc7500cd7e72cc7500057d72cc7500cd7c72cc7504875f32cc7500075d32cc7501877661cc7501877561cc75016d7f70cc75000d7e70cc75016d7d70cc75000d7c70cc75016f5f30cc75047d7f768c7500257e768c7501657d768c7500257c768c75047d7f748c7500d57e748c7500057d748c75047d7c748c7501675e638c7501675d638c7500cd7e728c7500057d728c75047d7c728c75047f76418c75000775418c75047f5f318c75048777318c75014d7f708c75000d7e708c75014d7d708c75000d7c708c75014f77108c7501457f764c7500257e764c7501457d764c7500257c764c7500057f744c7500d57e744c7500057d744c7500d57c744c7500057f724c7500cd7e724c7500cd7c724c7500075f324c7500075d324c75000776414c75000775414c75048777314c75047f5e314c75012d7f704c75000d7e704c75000d7c704c75047d7f760c7500257e760c75047e7e760c7500247e760c7501257d760c75047e7d760c7500047d760c7500257c760c75047d7f740c7500d57e740c75047f3e740c7500d53e740c7500057d740c75047f3d740c7500053d740c75047d7c740c7504875e630c7501275d630c7500cd7e720c75047f6e720c7500cd6e720c7500057d720c75047f6d720c7500056d720c75047d7c720c75047f76610c75012775610c75047f5f310c75047f76310c75047f5d310c75048775310c75010d7f700c75000d7e700c75010f7a700c75000d7a700c75010d7d700c75047f79700c75000579700c75000d7c700c75047d7f76887500257e76887501057d76887500257c768875047d7f74887500d57e74887500057d748875047d7c748875047d7f73887504857e73887500057d738875047d7c73887500cf6e42887500076d42887502ad7e718875047f76618875010775618875047f6f21887500cf77218875047f7421887500f57f708875000d7e70887500f57d708875000d7c70887500f77710887500ed7f76487500257e76487500ed7d76487500257c76487500057f74487500d57e74487500057d74487500d57c74487500057f73487504857e73487500057d73487504857c73487500cf6e32487500076d32487502c57f71487500ef7661487500ef75614
  | 21 => 0xc75d812101cfe74d8121004fd74d812101cfc74d812104cfe73d8121004fd73d812102cfd72d812100cfc72d8121056ee32d8121006ed32d8121014fd71d812100cfc71d81210defa20d81210defa10d81210def860581214857f7690f500257e7690f502657d7690f500257c7690f503757e7390f504875e6390f502675d6390f504873f4390f500d75f4390f504875c4390f500cd7e7290f500057d7290f500cd7c7290f500d73f4290f5047d7e7190f500057d7190f502557f7090f5000d7e7090f502557d7090f5000d7c7090f502575f3090f5024d7f7650f500257e7650f5024d7d7650f500257c7650f5037d7f7350f5024f5e6350f5024f5d6350f500d75f4350f504873e4350f504873c4350f500d75c4350f500057f7250f500cd7e7250f500cd7c7250f500057f7150f5047d7c7150f500d73f4150f5023d7f7050f5000d7e7050f5000d7c7050f5023f3f4050f502257f7650b500067f7650b500047f7650b500257e7650b502257d7650b500257c7650b502267c7650b500247c7650b503357f7450b500d73e6450b502273d6450b500057f7350b504857c7350b500073e4350b500d73c4350b5032d7f7250b500cf6e6250b502276d6250b500d76f4250b500cf3e4250b500cf3c4250b500cf6c4250b500cf6e3250b500057f7150b5047d7c7150b500d73f4150b500cf6c2150b5021d7f7050b5000d7e7050b5000d7c7050b5021e7d6050b5021f3f4050b5021f6f2050b504857f76ccb500257e76ccb504867e76ccb500247e76ccb502157d76ccb504867d76ccb500047d76ccb500257c76ccb504857f74ccb500d57e74ccb500057d74ccb504857c74ccb5036d7e73ccb504875e63ccb502175d63ccb504a75f43ccb504875c43ccb500cf5e32ccb500cf6e32ccb500cf5c32ccb5047d7e71ccb500057d71ccb502057f70ccb5000d7e70ccb502057d70ccb5000d7c70ccb502075f30ccb501fd7f764cb500257e764cb501fd7d764cb500257c764cb500057f744cb500d57e744cb500057d744cb500d57c744cb5031d7f734cb501ff5e634cb501ff5d634cb5049f5f434cb5049f5c434cb501ff6f624cb500cf6c624cb500cf6e424cb500076d424cb504876f324cb500cf5e324cb500cf5c324cb500cf6c324cb500057f714cb5047d7c714cb500cf6f214cb501ed7f704cb5000d7e704cb5000d7c704cb501ef6f204cb5047d7f76907500257e769075047e7e76907500247e76907501b57d769075047e7d76907500047d76907500257c76907504857e73907500057d73907500cd7e72907500057d729075047d7c72907502bd7e719075047f7661907501b775619075047f3f41907500d777419075047f74419075049777219075047f7421907501a57f709075000d7e70907501a57d709075000d7c70907501a7771090750
  | 22 => 0x5121004fc765512104cfe76d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2102cff72d8d2102cfd72d8d21156df32d8d21156dd32d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21156ef20d8d210ed7e7598d210057d7598d21006df6398d21135f57198d21175f77158d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d21134ff7258d21006ef7258d21174ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21136ef2058d21154fe7618d2104ede6318d21006dd6318d2104cff7694d21004fe7694d21004fd7694d2104cfc7694d21015ee7294d21005ed7294d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d2104cff7690d21004fe7690d21004fd7690d2104cfc7690d21015ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d2102dec764c92104eec764c92102cec764c9211feee654c9211feec654c921006ef644c921006ed644c921015ef734c921017cf734c921007cf634c92104eee634c92104eec634c921007cc634c921007ce534c921007cd534c9214bfcf434c9214bfcc434c921007e7714c92102dee714c92102dec714c921007e4714c921016ef614c921017e7614c921005ef704c9214b5f6769452102ef676945211c5f57594521026f66594521026f4659452102fb6749452102fb57494521006f76494521006f56494521015f6729452102df4729452102ef7629452102fe762945211dfe63294521007e53294521005f570945210ef7750945211dfe72094521024ff7654521014fe76545211c4fd7654521014fc76545210067f65545210267c6554521005ef7254521015ec725452102f745154521015f47654521026f47654521014f4765452102df7755452102f777554521007776554521026f66554521026f465545210ef746554521006f76454521006f564545214af7654545210ef7454545210ef775354521007755354521007e77254521015f67254521015f472545211c7e4725452102ef7625452102fe762545211c77752545211c77552545211c7e63254521007e53254521005f770545210ef7750545211c7e7205452101cff7650521014fe7650521194fd7650521014fc7650521006bf645052101ebc6450521005ef7250521015ec7250521196f7615052102fe42150521014fe76cc521014fc76cc521006df63cc52104edc63cc521015ee72cc521005ed72cc521007cd32cc52104cff764c521014fe764c521134fd764c521014fc764c521006df634c52104edc634c521005ef724c521015ec724c521007cd324c52100cfe76d81210defa60d8121024fe75d8121004fd75d8121024f
  | 23 => 0x67d6554e2104cff7690e2102cfe7690e21004fd7690e2102cfc7690e21004ff7650e2102cfe7650e21004fd7650e2102cfc7650e2101ebe6450e21006bd6450e212fdef7650a2101eef7650a2101cef7650a210076f7550a210076c7550a212feef6550a21006ed6550a21015ef7450a21017af7450a2101eee6450a212ffae6450a212ffad6450a2101eec6450a210ffae5450a21007ad5450a212feef6350a21006ed6350a21007ae4350a210ffac4350a212fdef7150a21007e77150a212ffe47150a21016ee6150a21017e66150a212ffe65150a212ffaf4150a212ffad4150a210ffaf4050a2102df776546214e6f7765462102f77755462102f776554621026f6655462102ef4655462102f74655462102ef76454621006f564546214df765454621107745454621107775354621007755354621015f67254621015f472546211c77752546211c77552546211c7e64254621007e54254621005f77054621107775054621004ff7558221024fe7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff735822104cfc7358221036ee4258221006ed425822102cfe715822100cfd715822102cfc715822102eef215822102eed215822102efb70582210f6fa30582210f6fa205822102efb105822102ef81058221024fe76d95210ee7e65d952101cfe74d9521004fd74d952101cfc74d95210067e54d95210ee7c54d952104cfe73d9521004fd73d95210ee7f53d952102cff72d952102cfd72d95211de7f52d95211de7d52d9521014fd71d95210ee7f51d952100cfe70d9521004fd70d952100cfc70d95210ee7f50d95210ee7c65595214d5f771595211dcff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff735952104cfc73595211c4ff7259521006ef72595214d4ff7159521006f77159521004ff705952100cfe705952100cfc70595210ee7f505952101cfe76d91210e6be64d9121024fe75d9121004fd75d9121024fc75d912104cfe73d9121004fd73d912102cff72d912102cfd72d91211aebf42d91211aebd42d91211aeee32d9121014fd71d91210e6bf41d91211aef721d91214ceee21d91214ceec21d91211aef421d912100cfe70d9121004fd70d912100cfc70d91211aeef20d91210057f75591210ed7c75591210e6bc64591214c5f77159121004ff75591210067f75591210047f7559121024fe7559121024fc75591210067c75591210247c75591211acff7459121006bf7459121004ff735912104cfc7359121194ff7259121006ef7259121196ee32591214c4ff7159121006f77159121196f721591212feee21591212feec2159121196f42159121004ff705912100cfe705912100cfc70591210e6bf4059121196ef2059121004ff7655121004fe7655121004fd765
  | 24 => 0xe75580310067d7558031024fc7558031004ff745803101cfe745803101cfc745803100cfd7358031004ff7258031014fe7258031014fc725803102edf315803102ef6315803102edd315803104ef5315803102cff705803102efb7058031006fb505803110efa505803110ef85058031006fb405803110efa405803110ef8405803104efb305803104ef83058031006fb205803110efa205803110ef8205803102efb105803102ef81058031006fb7558031006fa75580310067a7558031006f97558031006797558031006f87558031006fb7458031006fa7458031006f97458031006f87458031006fb5458031006fa5458031006f95458031006f8545803104efb735803104efa735803104ef8735803104efb535803104efa535803104ef9535803104ef8535803104efb435803104efa435803104ef9435803104ef84358031006fb7258031006fa7258031006f97258031006f87258031006fb5258031006fa5258031006f95258031006f85258031006fb4258031006fa4258031006f94258031006f8425803104efb325803104efa325803104ef9325803104ef8325803102efb715803102efa715803102ef8715803102efb515803102efa515803102ef9515803102ef8515803102efb415803102efa415803102ef9415803102ef8415803102efb315803102edb315803102efa315803102ef2315803102ef9315803102ed9315803104ef1315803102ef8315803102efb215803102efa215803102ef9215803102ef8215803102e7f7559621004ff745962101cfe745962101cfc74596210067e54596211067c5459621004ff735962104cfc73596211067f53596211c67f52596211c67d52596211c6ee425962102cfe715962102cfc715962102e7e515962102e7c5159621004ff705962100cfe705962100cfc70596211067f5059621004ff7559221024fe7559221024fc755922102ebf7459221006bf54592210febc5459221004ff735922104cfc73592210febf4359221196bf4259221196bd425922102cfe715922102cfc715922102ef6515922102ebe415922102ebc4159221196f7215922102ef42159221004ff705922100cfe705922100cfc70592210febf405922102ef71059221004ff765522102cfe7655221004fd765522102cfc7655221004ff7558e21024fe7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e2102edf7358e21136ee4258e21136df3258e21136dd3258e2102cfe7158e2102cfc7158e2102ede3158e2102edc3158e2102eef2158e2102eed2158e21004ff7058e2100cfe7058e2100cfc7058e2102ef71058e2104cff7694e2102cfe7694e21004fd7694e2102cfc7694e21015ee7294e21005ed7294e21004ff7654e2102cfe7654e21004fd7654e2102cfc7654e210267e6554e21
  | 25 => 0x903104ebf535903104ebe535903104ebd535903104ebc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf5259031006be5259031006bc525903104ebf325903104ebe325903104ebd325903104ebc325903102ebf715903102ebe715903102ebd715903102ebc715903102ebf515903102ebe515903102ebd515903102ebc515903102ebf315903102ebe315903102eb6315903102ebd315903104eb5315903102ebc315903102ebf215903102ebe215903102ebd215903102ebc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bc505903104ebf305903104ebe305903104ebd305903104ebc3059031006bf2059031006be2059031006bc205903102ebf105903102ebe105903102ebd105903102ebc1059031004ff765503102cfe7655031004fd765503102cfc76550310267e65550310067d655503101ebe6455031006bd64550312a6ee625503129efa6055031004ff7558831024fe7558831024fc7558831004ff745883101cfe745883101cfc745883102cff725883102eef7258831006ef5258831116ee5258831116ec5258831006ef4258831116ee4258831116ec425883104eef325883104eec325883102cfc715883102edf315883102edd315883102eee215883102eec2158831004ff705883100cfe705883100cfc7058831116ef2058831006ee2058831116ec2058831006ef7558831006ee7558831006ed7558831006ec7558831006ef7458831006ee7458831006ed7458831006ec7458831006ef5458831006ee5458831006ed5458831006ec545883104eef735883104eee735883104eec735883104eef535883104eee535883104eed535883104eec535883104eef435883104eee435883104eed435883104eec435883102eef715883102eee715883102eec715883102eef515883102eee515883102eed515883102eec515883102eef415883102eee415883102eed415883102eec415883102eef315883102ecf315883102eee315883102eed315883102ecd315883102eec3158831006ef7058831006ee7058831006ed7058831006ec7058831006ef5058831006ee5058831006ec5058831006ef4058831006ee4058831006ec405883104eef305883104eee305883104eed305883104eec305883102eef105883102eee105883102eed105883102eec1058831004ff7654831004fd765483102cfc76548310267e65548310067d6554831236be6454831006bd6454831016ee6254831006ed625483122efa6054831004ff7650831004fd765083102cfc76508310057f75508311257c75508312267e65508310067d655083101ebe6450831006bd6450831016ee6250831006ed625083121efa6050831004ff7558031024fe75580310067
  | 26 => 0x6f5655053102df7745053102fb77450531007b7645053101ef6645053101ef4645053113fb464505314efb7545053113fb45450531007d7735053104df6735053104df47350531007d4735053102ef7635053102fd7635053113fb74350531007b54350531196f66250531196f4625053113fb74250531007b54250531007d73250531007d53250531005f7705053113fb7405053100cfe76d813112efa60d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813102cfd73d813100cfc73d8131014fe72d8131004fd72d8131014fc72d8131006df32d8131006dd32d813104cfd71d8131006f641d8131006f541d813112efa50d813112efa30d813112efa10d813112ef8605813102cff755943102e7f7559431004ff745943101cfe745943101cfc74594311267f54594310067e54594311267c545943104cfe735943104cfc735943104e7e535943104e7c5359431004ff7259431014fe7259431014fc72594311267f52594310067e52594311267c525943102cfe715943102cfc715943102e7e515943102e7c5159431004ff705943100cfe705943100cfc70594311267f50594310067e50594311267c50594310067f74594310067e74594310067d74594310067c745943104e7f735943104e7e735943104e7d735943104e7c735943104e7f435943104e7e435943104e7d435943104e7c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067c425943104e7f325943104e7e325943104e7d325943104e7c325943102e7f715943102e7e715943102e7d715943102e7c715943102e7f415943102e7e415943102e7d415943102e7c415943102e7f315943102e7e315943102e7d315943102e7c315943102e7f215943102e7e215943102e7d215943102e7c21594310067f70594310047f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067c405943104e7f305943104e7e305943104e7d305943104e7c30594310067f20594310067e20594310067c205943102e7f105943102e7e105943102e7d105943102e7c1059431004ff7559031024fe7559031024fc755903102cff745903102ebf7459031006bf545903111ebe545903111ebc545903104cfe735903104cfc735903104ebe435903104ebc4359031004ff7259031014fe7259031014fc725903111ebf4259031006be425903111ebc425903102cfe715903102cfc715903102ebe415903102ebc415903102ef6315903104ef53159031004ff705903100cfe705903100cfc705903111ebf4059031006be405903111ebc4059031006bf7559031006be7559031006bd7559031006bc755903104ebf735903104ebe735903104ebd735903104ebc735
  | 27 => 0xe7259531014fc7259531184ff7159531006f77159531004ff705953100cfe705953100cfc70595311467f505953101cfe76d913113ebe64d9131024fe75d9131004fd75d9131024fc75d913102cfd73d913113ebf43d9131014fe72d9131004fd72d9131014fc72d913113ebf42d913104cfd71d913113ebf41d913100cfe70d9131004fd70d913100cfc70d913113ebc6459131004ff7559131024fe7559131024fc755913113cff7459131006bf745913115cff7359131006df7359131004ff7259131014fe7259131014fc725913117cff7159131006f77159131004ff705913100cfe705913100cfc705913113ebf4059131004ff7655131004fe7655131004fd7655131004fc765513102cfc7654d310067f6554d310267c6554d31005f77154d3102df47154d3104fd43154d3102cfc7650d31006bf6450d3101ebc6450d31005f77150d3102df47150d31014fe76d8931136ee62d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893102cfd73d8931136ee42d8931136ee32d893104cfd71d8931136ef21d893100cfe70d8931004fd70d893100cfc70d8931136ec6258931004ff7654931004fe7654931004fc7654931004ff7650931004fe7650931004fc76509310057f75509311457c7550931006bf645093101ebc6450931006ef6250931016ec6250931005de76cc93104ede76cc93104f5e75cc93104f5d75cc931006df65cc931006dd65cc93120ede64cc93120edc64cc931135dd72cc931016de62cc931016dc62cc93102dde71cc93102ddc71cc93104edf61cc93104fd761cc931005dd70cc93102cfc764c931006ef624c931016ec624c93104fcc324c931005f7714c93102df4714c93102ddc764c931016dc764c93102cdc764c931006df654c931006dd654c9311f6de644c9311f6dc644c93104ddf724c93104fcf724c931007cf624c931016de624c931016dc624c931137cc624c9314f7cf524c931137cc524c931137ce424c931007cd424c931007d7714c93102dde714c93102ddc714c931007d4714c93104edf614c93104fd7614c931137cf214c931005df704c931137cf204c931024ff7654531144fd765453104cfc76545310067f65545310267c6554531005df735453104ddc735453102fd43154531005f6769053102ef6769053102f76759053102f757590531006f76590531006f5659053113df5749053101ef6649053101ef4649053104df6739053102df4739053102ef7639053102fd763905311aef662905311aef46290531007d73290531007d53290531005f5709053101cff765053113cfd765053104cfc7650531006bf645053101ebc6450531005df735053104ddc735053102fb4415053104df4765053101ef4765053104cf47650531006f76550531
  | 28 => 0x8331014fc725833104edf3258331006dd325833104ef6315833104ef5315833104efb705833116efa405833104efb305833104ef8305833116efa105833102e7f7559631004ff745963101cfe745963101cfc74596310067e54596311667c54596311667f5359631004ff7259631014fe7259631014fc72596311667f525963102cfc715963102e7e515963102e7c515963102ef64159631004ff705963100cfe705963100cfc70596311667f5059631004ff7559231024fe7559231024fc755923102ebf7459231006bf545923115ebc545923115ebf4359231004ff7259231014fe7259231014fc725923115ebf425923102cfc715923102ebe415923102ebc4159231004ff705923100cfe705923100cfc705923115ebf405923102ef71059231004ff765523102cfe7655231004fd765523102cfc765523104ef73158e3102ede3158e3102edc3158e3102ef43158e31024ff7654e3102cfc7654e310267e6554e310067d6554e31005f77154e3102df47154e3101cff7650e3102cfc7650e3101ebe6450e31006bd6450e3104f9c4350e31005f77150e3102df47150e31004ff7558a31024fe7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a3102eef7258a31156ee3258a3102cfc7158a3102edf3158a3102edd3158a3102eee2158a3102eec2158a31004ff7058a3100cfe7058a3100cfc7058a31156ef2058a3102ef71058a31004ff7654a31004fd7654a3102cfc7654a310267e6554a310067d6554a31004ff7650a31004fd7650a3102cfc7650a310057f7550a311657c7550a3101ebe6450a31006bd6450a31016ec6250a31014ff764ca31016ee624ca31006ed624ca31005f7714ca3102df4714ca3102df7765063111ef7765063102ef76550631006f5655063102fb7745063102fb7645063101ef6645063102ef4645063102fb464506314ffb7545063115fb4545063104df6735063104df4735063115fb74350631007b54350631196f6625063102ef4625063115fb74250631007b54250631005f7705063115fb74050631004ff7558231024fe7558231024fc7558231004ff745823101cfe745823101cfc7458231004ff7258231014fe7258231014fc725823102cfc715823102ef64158231006f5415823102edf315823102edd315823102efb705823114efa305823114efa205823102efb105823102ef81058231024fe76d95311467e65d953101cfe74d9531004fd74d953101cfc74d953102cfd73d95311467f53d9531014fe72d9531004fd72d9531014fc72d953104cfd71d95311467f51d953100cfe70d9531004fd70d953100cfc70d95311467f50d95311467c6559531144ff75595310067f7559531004ff745953101cfe745953101cfc7459531164ff7359531006df7359531004ff7259531014f
  | 29 => 0x26f4765454101cf4765454102df7755454102f777554541007776554541026f66554541026f4655454119f746554541007b7745454101df6745454101df474545411cfb4745454102ef7645454102fb7645454119fb754545411cf7654545411cf7454545411cfb454545411cf345454541005f7735454119f7753545410077553545411cfb74354541007b54354541195f67254541195f47254541006f7625454119f7752545410077552545411cfb74254541007b54254541005f7705454119f7750545411cfb7405454100cfe76d814118efa60d8141024fe75d8141004fd75d8141024fc75d814102cfd74d814100cfc74d814104cfe73d8141004fd73d814105ebf43d8141006bd43d8141014fe72d8141004fd72d8141014fc72d814105ebf42d8141006bd42d814101cfd71d814118efa40d814118efa10d8141005df7358141005dc735814118ef8605814104e7f7559731004ff745973101cfe745973101cfc74597311867f545973102cfc735973104e7e535973104e7c5359731004ff7259731014fe7259731014fc72597310067e52597311867c525973104edf32597311867f5159731004ff705973100cfe705973100cfc70597311867f5059731004ff7559331024fe7559331024fc755933104ebf745933102cfc735933104ebe435933104ebc4359331004ff7259331014fe7259331014fc725933117ebf415933104ef6315933104ef53159331004ff705933100cfe705933100cfc705933117ebf405933104edf3059331004ff765533104cfe7655331004fd765533104cfc76553310267e65553310067d6555331004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b3102cfc7358b3104eef7258b31006ef5258b31176ec5258b31176ee4258b3104eef3258b3104eec3258b31176ef2158b31004ff7058b3100cfe7058b3100cfc7058b3104edf3058b31176ef2058b31004ff7654b31004fd7654b3104cfc7654b31004ff7650b31004fd7650b3104cfc7650b310057f7550b311857c7550b313a6bf6450b3101ebc6450b31016ee6250b31006ed6250b3104ddf764cb31116df764cb3104edf654cb31006dd654cb311f6de644cb3104edc644cb3104fcf724cb3104fcf624cb31016de624cb31016dc624cb3104fcc624cb31507cf524cb31177cc524cb31177ce424cb31007cd424cb3102dde714cb3102ddc714cb31177cf214cb31005df704cb31177cf204cb31024ff765473104cfc76547310267e65547310067d6554731005df735473104ddc735473101cff765073104cfc765073101ebe6450731006bd6450731005df735073104ddc7350731004ff7558331024fe7558331024fc7558331004ff745833101cfe745833101cfc745833102cfc7358331004ff7258331014fe725
  | 30 => 0xe7218d41005ed7218d4118dfa7018d41005f97018d41004fe7694d41004fd7694d4104cfc7694d4101dbe7494d41005bd7494d41195ee7294d41005ed7294d4102df67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410267e6554d410067d6554d41005bf7454d4101dbc7454d4119f3f5454d4102cbc7650d4119dbe7550d4119dbc7550d4101dbf7350d4101f9f7350d410079f6350d4104ebe6350d4104ebc6350d410079c6350d4104e9c6350d410079e5350d410079d5350d41005bf7250d41007b77150d4102dbe7150d4102dbc7150d41007b47150d4101ebf6150d4101fb76150d4151fb72150d4151fb42150d41005bf7050d41014fe76d8941196ee62d894102df671d894101df571d8941197e721d8941024fe75d8941004fd75d8941024fc75d894102cfd74d894104cfe73d8941004fd73d8941196ee42d89410feed42d894101cfd71d8941196f571d894101cf571d8941196ef21d8941196f721d8941196f421d894100cfe70d8941004fd70d894100cfc70d89410febf40d89410057f755894119d7c7558941196ec6258941515f77158941197e42158941004ff7654941004fe7654941004fc7654941005bf745494101dbc7454941005f7715494102df4715494102dbc7650941016bc765094102cbc76509410073f755094119dbe755094119dbc75509410073c755094119d3c7550941006bf6550941006bd6550941005bf73509413a6bc635094101dbf725094101faf7250941007af6250941016be6250941016bc6250941197ac6250941197ae5250941007ad5250941197ae3250941007b7715094102dbe715094102dbc7150941007b4715094101ebf615094101fb76150941197b721509412ffac2150941197b42150941197a42150941005bf7050941197af2050941004fe76cc941004fd76cc94104cfc76cc94119d7e75cc9410057d75cc94101dbe74cc941005bd74cc941006df63cc94104edc63cc94120f9f43cc94102df671cc941005f571cc941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941006df634c94104edc634c9411f79f434c941016ee624c941007ad424c941005f7714c94102df4714c941197e7214c94150df6769454102ef676945411cdf57594541026f66594541026f4659454101df6749454102fb6749454101db6749454102fb5749454102df4749454102ef7649454102fb7649454119fb754945411e7b45494541005f573945411e7b74394541007b54394541195f6729454102df47294541006f762945411e7b74294541007b54294541005f5709454119f7750945411e7b74094541024ff765454101cfe76545411ccfd765454101cfc76545410067f65545410267c6554541005bf745454101dbc74545411cf3c545454101df47654541
  | 31 => 0x8a41024fe7558a41024fc7558a41004ff7358a4104cfc7358a4102eef7258a411aeee4258a410e6ed4258a411aeee3258a4102cfe7158a4102cfc7158a4102ef47158a4102cf47158a4102ef65158a4102ebf4158a4102ebd4158a411aef72158a4102eee2158a4102eec2158a4102ef42158a41004ff7058a4100cfe7058a4100cfc7058a411aeef2058a4102ef71058a41004ff7654a41004fd7654a4102cfc7654a410267e6554a410067d6554a41005f77154a4102df47154a4104cff76cca4102cfe76cca41004fd76cca411b57e75cca410057d75cca412167e65cca410067d65cca4104ede63cca41006dd63cca4102df671cca41005f571cca41004ff764ca41004fd764ca4102cfc764ca411fe7e654ca410067d654ca4104ede634ca41006dd634ca41016ee624ca41006ed624ca41005f7714ca4102df4714ca411afe7214ca4102df7765464152ef7765464102f777554641026f6655464102f76655464102676655464102f75655464102ef4655464101df6745464101df474546411cf7654546411cf745454641005f773546411b77753546410077553546411adf672546411adf47254641006f562546411b7775254641007755254641005f770546411b7775054641004ff7558241024fe75582410067e75582410067d7558241024fc7558241004ff735824104cfc7358241004ff7258241014fe7258241014fc725824102cfe715824102cfc715824102ebf415824102ebd415824102ef6315824102efb70582411a6fa40582411a6fa30582411a6fa205824102efb105824102ef81058241024fe76d954119e7e65d954101dbe74d954102dbd74d954119f3f54d954102cff74d954102cfd74d954119ebd74d954102cbd74d95411e67f54d954119ebf54d95411e67d54d95411e6bc54d954104cfe73d9541004fd73d9541014fe72d9541004fd72d9541014fc72d95410067e52d954119e7c52d95411e6bf42d954101cfd71d954119e7f51d954100cfe70d9541004fd70d954100cfc70d954119e7f50d954119e7c65595411cf3c5459541525f771595411e4ff75595410067f75595411ccff7459541006bf745954119ebf54595411ce7e54595411ce7c54595411cebc5459541004ff735954104cfc735954119e7f5359541004ff7259541014fe7259541014fc72595411cebf4259541524ff7159541006f77159541004ff705954100cfe705954100cfc705954119e7f5059541024fe75d8d41004fd75d8d41024fc75d8d4102cfd74d8d4115ede43d8d4115edd43d8d41014fe72d8d41004fd72d8d41014fc72d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4115ebf40d8d41006de30d8d41006dc30d8d41006df6398d4113df57198d4117df77158d4119d7e7518d410057d7518d4104ede6318d41006dd6318d41195e
  | 32 => 0x267f61549510277761549510057f7054951004ff7650951004fe7650951004fc76509510057f75509510257c755095101ebe64509511cf3e5450951006ef6250951016ec62509510076d5250951004fe76cc951004fd76cc95104cfc76cc9510257e75cc9510057d75cc95104ede63cc9510075d53cc951004ff764c951004fe764c951004fc764c9510257e754c9510057d754c9510075d534c951006ef624c951016ec624c9511ff6f524c95100cfe76d81511befa60d815147e7f75d815102cfd75d815100cfc75d815100c7c75d815101cfe74d8151004fd74d815101cfc74d81510067e54d81510667c54d815104cfe73d8151004fd73d81510667f53d81510067d53d8151014fe72d8151004fd72d8151014fc72d81510667f52d81510067d52d8151024fd71d815147e7e51d815147e7c51d81511be7f50d81511befa50d81511befa10d8151005ef72581511c5ec72581511bef8605815102e7f75596411ce7f54596411ce7d5459641004ff735964104cfc73596411b67f53596411b67c5359641004ff7259641014fe7259641014fc72596411b67f52596410067e52596411b67c525964102cfe715964102cfc715964102e7e515964102e7c5159641004ff705964100cfe705964100cfc70596411b67f50596410067e50596411b67c50596411ce7f74596411ce7e74596411ce7d74596411ce7c74596410067f73596410067e73596410067d73596410067c73596411ce7f43596411ce7e43596411ce7d43596411ce7c43596410067f72596410067e72596410067d72596410067c72596411ce7f42596411ce7e42596411ce7d42596411ce7c42596410067e32596410067c325964102e7f715964102e7e715964102e7d715964102e7c715964102e7f415964102e7e415964102e7d415964102e7c415964102e7f315964102e7e315964102e7d315964102e7c315964102e7f215964102e7e215964102e7d215964102e7c21596410067f70596410047f70596410067e70596410067d70596410067c70596411ce7f40596411ce7e40596411ce7d40596411ce7c40596410067e30596410067c30596410067f20596410067e20596410067c205964102e7f105964102e7e105964102e7d105964102e7c1059641004ff7558e41024fe7558e41024fc7558e4102edf7358e4113ede4358e4113edd4358e41004ff7258e41014fe7258e41014fc7258e4102cfc7158e4102ebf4158e4102ebd4158e4102ede3158e4102edc3158e41004ff7058e4100cfe7058e4100cfc7058e4102ef71058e4104cff7694e4102cfe7694e41004fd7694e410267e6594e410067d6594e411adee7294e41005ed7294e4102df67194e41005f57194e41004ff7654e41004fd7654e4102cfc7654e410267e6554e410067d6554e4102df67154e41004ff755
  | 33 => 0xc2158a51004ff7058a5100cfe7058a5100cfc7058a510ee7f5058a511deef2058a51004ff7650a51004fd7650a5102cfc7650a510057f7550a510257c7550a5101ebe6450a51006bd6450a51016ec6250a5102df67150a5104cff76cca5102cfe76cca51004fd76cca510257e75cca510057d75cca5120ebe64cca51006bd64cca5104ede63cca51006dd63cca51004ff764ca51004fd764ca5102cfc764ca511f6be644ca51006bd644ca5104ede634ca51006dd634ca51016ee624ca51006ed624ca510067d7558251004ff745825101cfe745825101cfc7458251004ff735825104cfc7358251004ff7258251014fe7258251014fc725825102cfe715825102cfc715825102e7f515825102e7d515825102ef6415825102ef6215825102efb70582511d67f50582511d6fa50582511d6fa30582511d6fa205825102efb105825102ef8105825101cfe76d91510257e75d91511cebe64d91511cf3e54d915102cfd75d915102c7d75d91511ce7e54d91511cebe54d91511b6bd54d91511ce7c54d915104cfe73d9151004fd73d91511b67f53d9151014fe72d9151004fd72d9151014fc72d9151024fd71d91511cebf41d915100cfe70d9151004fd70d915100cfc70d91511b67f50d91511cebc64591511cf3c545915153df7715915102cfd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51166de53d8d51166dd53d8d51014fe72d8d51004fd72d8d51014fc72d8d5100cfe70d8d51004fd70d8d5100cfc70d8d511667f50d8d51006df6398d511c5ee7298d51005ed7298d51145f57198d51185f77158d5104ede6318d51006dd6318d5102c7c7654d511cd7e7454d511cd7c7454d510067f6454d510257f7354d510275f7354d510075f6354d5104e7e6354d5104e7c6354d510075c6354d510057f7254d512767e6254d512767c6254d51007777154d5102d7e7154d5102d7c7154d51007747154d510267f6154d51027776154d510057f7054d51004fe7690d51004fd7690d5104cfc7690d510257e7590d510057d7590d510075d5390d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257c7550d510075d5350d51014fe76d89511c6ee62d895102cfd75d895101cfe74d8951004fd74d895101cfc74d895104cfe73d8951004fd73d89511c6ee52d8951106ed52d89511c6ee42d89511c6ee32d8951024fd71d89511c6ef21d895100cfe70d8951004fd70d895100cfc70d89511067f50d8951006ee20d89511c6ec20d89511c6ec6258951535f7715895102d7c76549510167c765495102c7c76549511cd7e74549511cd7c74549510057f73549510257f72549510276f72549510076f62549510167e62549510167c62549511c76c62549511c76e425495100777715495102d7e715495102d7c7154951007747154951
  | 34 => 0x9321f78c4350932005ef71509322feec61509321f7af4150932005ef70509321f7af4050932024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853204cfd72d8532176f621d853200cfe70d8532004fd70d853200cfc70d8532176ef20d8532006f610d8532006f410d8532006f761985321fd7e75185320057d75185321f5be7418532005bd741853202ef66118532006f561185321edfa7018532005f9701853200cfe76d81321eefa60d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d8132014fd73d813204cfd72d8132096ee42d8132006ed42d813202cfe71d8132004fd71d8132096ef21d81321eefa30d81321eefa20d8132005f77158132005f471581321eef8605813202ebf74592511e6be545925119ebd5459251004ff735925104cfc73592511e6bf43592511e6bc4359251004ff7259251014fe7259251014fc72592511e6bf4259251006be42592511e6bc425925102cfe715925102cfc715925102ebe415925102ebc4159251004ff705925100cfe705925100cfc705925119e7f50592511e6bf4059251006be40592511e6bc405925119ebe755925119ebd75592511e6bc7559251006bf7359251006be7359251006bd7359251006bc735925119ebf535925119ebe535925119ebd535925119ebc5359251006bf7259251006be7259251006bd7259251006bc725925119ebf525925119ebe525925119ebd525925119ebc5259251006be3259251006bc325925102ebf715925102ebe715925102ebc715925102ebf515925102ebe515925102ebd515925102ebc515925102ebf315925102ebe315925102ebd315925102ebc315925102ebf215925102ebe215925102ebd215925102ebc2159251006bf7059251006be7059251006bd7059251006bc705925119ebf505925119e3f505925119ebe505925119ebd505925119ebc5059251006be3059251006bc3059251006bf2059251006be2059251006bc205925102ebf105925102ebe105925102ebd105925102ebc1059251004ff7458e5101cfe7458e5101cfc7458e5102edf7358e51146de5358e51146dd5358e51004ff7258e51014fe7258e51014fc7258e5102cfc7158e5102e7f5158e5102e7d5158e5102ef64158e5102ede3158e5102edc3158e51004ff7058e5100cfe7058e5100cfc7058e511467f5058e5104cff7690e5102cfe7690e51004fd7690e5101ebe6490e51006bd6490e51004ff7650e51004fd7650e5102cfc7650e5101ebe6450e51006bd6450e51004ff7458a5101cfe7458a5101cfc7458a51004ff7358a5104cfc7358a5102eef7258a511deee5258a510eeed5258a511deee3258a5102cfe7158a5102cfc7158a5102e7f5158a5102e7d5158a5102eee2158a5102ee
  | 35 => 0xcfe705953200cfc70595321fe7f505953201cfe76d91321f6be64d913204dde73d9132015dd73d91321f79f43d9132024fe75d9132004fd75d9132024fc75d9132014fd73d913225edd73d9132014dd73d91321f6bf43d91321f6df43d91321f6dc43d913204cff72d913204cfd72d913225ebf42d913225ebd42d913202cfe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d913225eef20d91320057f75591321fd7c75591321f6bc6459132545df73591321f79c4359132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913225cff7459132006bf7459132544ff7359132006df73591321f6df43591323a6be43591323a6bc43591321f6dc4359132244ff7259132006ef7259132004ff715913202cfc71591321f6bf4159132004ff705913200cfe705913200cfc70591321f6bf4059132246ef2059132004ff7655132004fe7655132004fd7655132004fc7655132005df735513204ddc7355132005ef7255132015ec725513254dde7694d3204ede7694d32275dd7594d32026de6594d32026dc6594d321f5de7494d3204ddc7494d32006df6494d32006dd6494d32015de7294d3204fce7294d32015ce7294d3204fcd7294d32015dc7294d3204edf6294d3204fcf6294d321ffcf5294d3228fcc5294d3228fce4294d32005dd7194d3228fcf2194d32005dd7094d321ff5f5094d3228fcf2094d32024ff7654d32014fe7654d32274fd7654d32014fc7654d320067f6554d320267c6554d32005ef7254d32015ec7254d322776c5254d32015dc7654d32026dc7654d32014dc7654d3204ddf7554d3204f5f7554d320075f6554d32026de6554d32026dc6554d321ff5c6554d321f5de7454d321f5dc7454d32006df6454d32006dd6454d321ff5f5454d320075d5454d32007cf7254d32015de7254d32015dc7254d32277cc7254d3204edf6254d3204fcf6254d321ffcf5254d322775e5254d322775c5254d32277cc5254d322774c5254d32277ce4254d32005df7154d321ff5f5154d32277cf2154d32005df7054d321ff5f5054d32277cf2054d3201cff7650d32014fe7650d32244fd7650d32014fc7650d32006bf6450d3201ebc6450d32545df7350d3204f9c4350d32005ef7250d32015ec7250d3204dec765093201eec765093204cec76509320076f75509321fdee75509321fdec75509320076c75509321fd6c7550932006ef6550932006ed6550932015ef7450932017af7450932007af645093201eee645093201eec64509321f7ac64509321f7ae5450932007ad5450932007cf735093204dee735093204dec7350932007cc7350932016ef6350932017cf6350932007ce5350932007cd53509321f7cf43509323a7ae43509323a7ac43509321f7cc435
  | 36 => 0xd71597320067c71597320067f41597320067c415973204e7f315973204e7e315973204e7d315973204e7c31597322767f21597322767e21597322767d21597322767c21597320067f70597320047f70597320067e70597320067d70597320067c70597320067f40597320067e40597320067c405973204e7f305973204e7e305973204e7d305973204e7c30597322767f20597322767e20597322767d20597322767c20597320067e10597320067c1059732004ff7559332024fe7559332024fc755933204ebf7459332014fe7359332014fc735933204edc7359332014dc735933204ede535933220edf435933204ebe435933204ebc435933204edc4359332246bf4259332246bd425933204eee325933204eed3259332004ff715933202cfc715933220ebf4159332004ff705933200cfe705933200cfc705933220ebf405933204edf3059332004ff765533204cfe7655332004fd765533204cfc76553320267e65553320067d6555332005df735533204ddc735533204ddf7654f3255edf7654f3204f5f7554f32026de6554f3204f5e6554f320265e6554f3204f5d6554f3204edc6554f3220dde7454f3220ddc7454f3204edf6454f32006dd6454f322175f5454f320075d5454f32015de7254f32015dc7254f322775e5254f322775c5254f32005df7154f322175f5154f32005df7054f322175f5054f32004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc7458732014fc735873204eee325873204eed325873204ef7715873204ef7315873204ef43158732136f62158732004ff705873200cfe705873200cfc705873204edf3058732004ff7558332024fe75583320067e75583320067d7558332024fc7558332004ff745833201cfe745833201cfc7458332014fe7358332014fc735833204eee325833204eed3258332004ff715833202cfc715833204edf315833204efb7058332206fa405833204efb305833204ef83058332206fa2058332206fa1058332024fe76d95321fe7e65d9532015ee72d953204ded72d95321ff6f52d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321fe7c54d9532014fd73d95321fe7f53d953204cff72d953204cfd72d95321feed72d953204ced72d953228e7f52d95321feef52d953228e7d52d953228eec52d953228eee42d953202cfe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d95321fe7f50d95321fe7c6559532555df73595322776c525953228cff75595320067f7559532004ff745953201cfe745953201cfc7459532554ff7359532006df7359532274ff7259532006ef72595321feef52595322767e52595322767c5259532276ec5259532276ee4259532004ff715953202cfc71595321fe7f5159532004ff7059532
  | 37 => 0x4d42004ff7654d42004fe7654d42004fc7654d420067f6554d420267c6554d42005bf7454d4201dbc7454d420073d5454d42015ee7254d422776e5254d42015be7690d4225ebe7690d42014be7690d423a5bf7590d42005bd7590d420073f6590d420073c6590d4201dbe7390d4201f9e7390d423a6bf6390d420079f6390d423a79c6390d423a79e5390d420079d5390d42015be7290d4225fae7290d423a7ad7290d42015bc7290d4201ebf6290d4201faf6290d4225fae5290d4225fae3290d42005bd7190d4225fac2190d42005bd7090d4225faf2090d4201dec7654942026ec765494201cec7654942015ef75549420176f75549420076f6554942026ee6554942026ec65549422276c6554942007af745494201dee745494201dec7454942237ac7454942016ef6454942017af6454942237ae5454942227ad5454942005ef7354942007ae4354942237ac43549422fdec71549422276f5154942237af4154942005ef70549422276f5054942237af405494202cfe76d85420067f65d85420067c65d8542024fe75d8542004fd75d8542024fc75d8542014fd74d854204cfe73d8542004fd73d854201cfd72d8542516ed72d85424c6ee32d8542516f641d85424c6f621d85422feec21d854200cfe70d8542004fd70d854200cfc70d8542516bf40d85424c6ef20d85422257e75985420057d75985420067f65985420067c6598542006f761985422ffe421985420057f75585422257c75585420067f65585420067c6558542197e421585420067f65185420067c651854202ef66118542006f5611854200cfe76d81420067f65d81420067c65d814221efa60d81420067f75d8142024fe75d8142004fd75d8142024fc75d81420067c75d8142014fd74d814204cfe73d8142004fd73d814201cfd72d814233eee32d814202cfe71d8142004fd71d81423cebf41d814221efa40d814221efa20d81420057f75581422257c75581420067f65581420067c655814221ef8605814204e7f7559732004ff745973201cfe745973201cfc74597322167f54597320067e54597322167c5459732014fe7359732014fc735973204e7e535973204e7c53597322767f52597322767d5259732004ff715973202cfc71597322167f51597322167c5159732004ff705973200cfe705973200cfc70597322167f50597320067e50597322167c50597320067f74597320067e74597320067d74597320067c745973204e7f735973204e7e735973204e7d735973204e7c735973204e7f435973204e7e435973204e7d435973204e7c43597322767f72597322767e72597322767d72597322767c72597322767f42597322767e42597322767d42597322767c425973204e7f325973204e7e325973204e7d325973204e7c32597320067f71597320067e71597320067
  | 38 => 0x57f6f20d954257e7f74d95425967e74d954257e7d74d954257e7c74d95420067f73d95420067e73d95420067d73d95420067c73d95425967f43d95425967e43d95425967d43d95425967c43d954257e7f72d954257e7e72d954257e7d72d954257e7c72d954257e7f42d954257e7e42d954257e7c42d954257e7f32d954257e7e32d954257e7d32d954257e7c32d95420067f71d95420067e71d95420067d71d95420067c71d95425967f41d95425967e41d95425967d41d95425967c41d954257e7f21d954257e7e21d954257e7d21d954257e7c21d95420067f70d95420067e70d95420067d70d95420047d70d95420067c70d95425967f40d95425967e40d95425967d40d95425967c40d95420067e30d95420067c30d954257e7f20d954257e7e20d954257e7d20d954257e7c20d95420067e10d95420067c10d9542024ff76595422267c6559542585bf745954258def725954257cff75595420067f7559542584ff7459542006bf7459542004ff735954204cfc73595422a4ff7259542006ef7259542004ff715954202cfc7159542004ff705954200cfe705954200cfc70595422267f505954257d7e76195422267e761954257c7e76195425773e741954256f3d741954256e7f64195422275e73195422275d73195425773c431954256f6e72195425776d721954256e7f62195425776f421954256f3e421954256f3c421954256f6c421954256f6e32195422277671195422277571195425773f411954256f6c21195422277a70195420057d70195422277970195420057970195420067e60195420067c60195425773f401954256f6f2019542015bc7655142026bc7655142014bc765514201dbf755514201f3f75551420073f6555142026be6555142026bc65551422273c65551423a5bc73551422273f5355142007af7255142015be7255142015bc72551422a7ac725514201ebf625514201faf62551422a7ae52551422a7ae3255142005bf71551422a7ac2155142005bf70551422273f50551422a7af205514204cfe76d8d420067f65d8d420067c65d8d42024fe75d8d42004fd75d8d42024fc75d8d42014fd74d8d42546bd74d8d42566de43d8d42566dd43d8d423a6bc43d8d4201cfd72d8d42546df32d8d4202cfe71d8d42004fd71d8d42566bf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42566bf40d8d42546ef20d8d422257e7598d420057d7598d420067f6598d420067c6598d42006df6398d423a79c4398d421f5ed7298d420057f7558d422257c7558d420067f6558d420067c6558d421f79c4358d4220def7258d420067f6518d420067c6518d4204ede6318d42006dd6318d42004fe7694d42004fd7694d4204cfc7694d420067f6594d420267c6594d4201dbc7494d4204ede6394d42015ee7294d42005ed729
  | 39 => 0xd70d894300cfc70d894320ebf40d89430057f755894324d7c7558943246ec6258943024fe75d8543004fd75d8543024fc75d854304cfd74d8543014fe72d8543004fd72d8543014fc72d854317ef641d854300cfe70d8543004fd70d854300cfc70d854317ebf40d854324d7e75985430057d7598543006f7619854302ef66118543006f5611854300cfe76d814323efa60d8143024fe75d8143004fd75d8143024fc75d814304cfd74d814301cfd73d8143014fe72d8143004fd72d8143014fc72d814302cfe71d8143004fd71d814309ebf41d814323efa40d814323efa30d814323ef8605814301cfe76d9152236be64d9152014fd75d9152236be54d91525aebd54d915204cfe73d9152004fd73d9152024fd72d9152586bf42d915202cfe71d9152004fd71d9152236bf41d915200cfe70d9152004fd70d915200cfc70d91525ae7f50d9152236bc64591525a5ef725915204cfe76d8d52014fd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d5259ede53d8d5259edd53d8d52024fd72d8d5259eef52d8d525567e52d8d525567c52d8d52556ec52d8d52556ee42d8d52556df32d8d5202cfe71d8d52004fd71d8d5259e7f51d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5259e7f50d8d52006df6398d521fded7298d52215ef7258d5204ede6318d52006dd6318d52004fe7690d52004fd7690d5204cfc7690d52004ff7650d52004fe7650d52004fc7650d5202cfe76d8552014fd75d855201cfe74d8552004fd74d855201cfc74d855204cfe73d8552004fd73d8552024fd72d8552536f651d85524d6f621d855200cfe70d8552004fd70d855200cfc70d85525367f50d8552235be7498552005bd7498552006f7619855202ef66118552006f5611855200cfe76d815222efa60d81520ce7f75d8152014fd75d815201cfe74d8152004fd74d815201cfc74d815204cfe73d8152004fd73d8152024fd72d81520ce7e52d81520ce7c52d81520ceee42d815202cfe71d8152004fd71d815246e7f51d815222e7f50d815222efa50d815222efa20d815222ef86058152024fe76d95422267e65d95422a4fd75d9542014ff74d9542014fd74d95425967f54d95425967d54d954204cfe73d9542004fd73d95422267f53d95422267c53d954201cff72d954201cfd72d954257e7f52d954257e7d52d954202cfe71d9542004fd71d95422267f51d95422267c51d954200cfe70d9542004fd70d954200cfc70d95422267f50d95420067e50d95422267c50d954256d7e76d95420247e76d954257f3f74d954257f3c74d95425973c43d95425976f72d954257f6c72d95425976f42d954257f3e42d954257f3c42d954257f6c42d954257f6e32d95425973f41d954257f6c21d95420057d70d95420067e60d95420067c60d95425973f40d9542
  | 40 => 0x4e435d75e5254e432675c5254e4327f9f4254e432675f5154e43005df7054e432675f5054e43004ff7558a43024fe7558a43024fc7558a4304cfe7358a4304cfc7358a4304ede5358a43006dd5358a431f6df4358a4304edc4358a4304eef7258a43006ef5258a4325eec5258a4325eee4258a4304eef3258a4304eec3258a43004ff7158a4302cfc7158a4325eef2158a43004ff7058a4300cfe7058a4300cfc7058a4304edf3058a4325eef2058a43004ff7558643024fe7558643024fc755864304cfc735864304ebf435864304ebd4358643004ff7258643014fe7258643014fc725864313ebf425864304ef7715864313ef6415864304ef7315864304ef43158643004ff705864300cfe705864300cfc705864304edf3058643004ff7558243024fe7558243024fc755824304cfe735824304cfc735824304ebf435824304ebd4358243004ff7258243014fe7258243014fc7258243086bf4258243004ff715824302cfc715824304efb7058243256fa405824304efb305824304ef83058243256fa1058243024fe76d954324e7e65d954304cff74d954304cfd74d95432967f54d95432967d54d954301cfd73d954324e7f53d9543014fe72d9543004fd72d9543014fc72d95430067e52d954324e7c52d954302cfe71d9543004fd71d954324e7f51d954300cfe70d9543004fd70d954300cfc70d954324e7f50d954324e7c65595435cddf7359543294ff75595430067f755954327cff7459543006bf74595435ccff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff715954302cfc7159543004ff705954300cfe705954300cfc705954324e7f50595435c5de7694d4304ede7694d4327ddd7594d43026de6594d43026dc6594d4301dde7494d4304ddc7494d4304edf6494d4304f9f6494d4304fce7294d4304fcd7294d432979f4194d43005dd7094d4324f5f5094d432979f4094d43024ff7654d4301cfe7654d4327cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d4304f5c5354d4304f9c4354d4301ddc7654d43026dc7654d4301cdc7654d4304ddf7554d4304f5f7554d430075f6554d43026de6554d43026dc6554d4324f5c6554d430079f7454d4301dde7454d4301ddc7454d4327f9c7454d4304edf6454d4304f9f6454d4327f5f5454d4327f5d5454d435bf5e5254d4324f5c5254d4324f5f5154d4327f9f4154d43005df7054d4324f5f5054d4327f9f4054d43014fe76d8943246ee62d8943024fe75d8943004fd75d8943024fc75d894304cfd74d894301cfd73d8943006de53d8943006dd53d894320edf43d89435b6be43d89435b6bc43d894320edc43d8943246ee42d8943246ee32d894302cfe71d8943004fd71d894320ebf41d894300cfe70d8943004f
  | 41 => 0x14fc725865304edf325865304ef77158653146f6515865304ef7315865304ef43158653004ff705865300cfe705865300cfc70586531467f50586530067d7558253004ff745825301cfe745825301cfc745825304cfe735825304cfc735825304e7f535825304e7d535825304ede4358253004ff7258253014fe7258253014fc725825304edf3258253004ff715825302cfc715825304efb70582532867f5058253286fa5058253286fa405825304efb305825304ef83058253286fa105825301cfe76d915327ebe64d915304cfd75d915327ebe54d9153266bd54d9153024fd73d915327ebf43d9153014fe72d9153004fd72d9153014fc72d915327ebf42d915302cfe71d9153004fd71d915327ebf41d915300cfe70d9153004fd70d915300cfc70d91532667f50d9153006be40d915327ebc40d915327ebc64591535e5df735915304d7c765515301e7c765515304c7c76551530257f74551530273f74551530073f645515301e7e645515301e7c645515327f3c64551530075f735515304d7e735515304d7c73551530075c73551530267f63551530275f63551532757e72551532757c725515327f3f42551530057f71551530057f7055153014fe76d89530257e75d8953276ee62d89532776e52d895304cfd75d895304c7d75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d89532767e52d8953276ee52d89532767c52d8953276ee32d895302cfe71d8953004fd71d89532167f51d895300cfe70d8953004fd70d895300cfc70d89532167f50d8953276ec62589532776c525895304cfd75d855301cfe74d8553004fd74d855301cfc74d8553014fe72d8553004fd72d8553014fc72d8553186f651d855300cfe70d8553004fd70d855300cfc70d85531867f50d855327dbe7498553005bd7498553006f7619855302ef66118553006f5611855300cfe76d815326efa60d81534867f75d815304cfd75d815301cfe74d8153004fd74d815301cfc74d81530a67f54d81530067d54d8153024fd73d81534867e53d81534867c53d8153014fe72d8153004fd72d8153014fc72d81530067e52d81530a67c52d815302cfe71d8153004fd71d81530a67f51d815326e7f50d815326efa50d815326efa30d8153005bf745815327dbc745815326ef8605815304e7f755964327e7f545964327e7d545964304cfe735964304cfc735964304e7e535964304e7c5359643004ff7259643014fe7259643014fc72596430067e52596432667c525964327ebf4259643004ff715964302cfc71596432667f5159643004ff705964300cfe705964300cfc70596432667f505964304ddf7654e435dedf7654e4304f5f7554e4304f5f6554e43026de6554e4304edc6554e4304f5c6554e4301dde7454e4301ddc7454e4327f5f5454e4327f5d545
  | 42 => 0xc70d8d545e67f50d8d54006df6398d542a5ee7298d54005ed7298d5404ede6318d54006dd6318d54014fe76d89542a6ee62d895401cfd75d8954024fd74d895404cfe73d8954004fd73d89542a6ee52d89542a6ee42d89542a6ee32d895402cfe71d8954004fd71d895400cfe70d8954004fd70d895400cfc70d89545a67f50d89542a6ec625895402cfe76d855401cfd75d8554024fd74d855453ebf54d85545267e54d85545267c54d8554526bc54d855404cfe73d8554004fd73d855453e7f53d8554014fe72d8554004fd72d8554014fc72d8554526bf42d855453ef651d8554526f641d855400cfe70d8554004fd70d855400cfc70d855453e7f50d8554006f7619855402ef66118554006f5611855400cfe76d815429efa60d81540d67f75d815401cfd75d8154024fd74d81540d67e54d81540d67c54d815404cfe73d8154004fd73d81544767f53d8154014fe72d8154004fd72d8154014fc72d81540d6bf42d815402cfe71d8154004fd71d815429e7f50d815429efa50d815429efa40d815429ef8605815404ebf7459253296be545925324ebd545925304cfe735925304cfc735925304e7f535925304e7d535925304ebe435925304ebc4359253004ff7259253014fe7259253014fc7259253004ff715925302cfc7159253296bf4159253004ff705925300cfe705925300cfc705925324e7f5059253296bf4059253004ff7458a5301cfe7458a5301cfc7458a5304cfe7358a5304cfc7358a5304eef7258a5328eee5258a53006ef4258a5328eee4258a5328eec4258a5304eef3258a5304eec3258a53004ff7158a5302cfc7158a5328eef2158a5328eec2158a53004ff7058a5300cfe7058a5300cfc7058a531fe7f5058a5328eef2058a53006ee2058a5328eec2058a531feee7558a531feed7558a5328eec7558a53006ef7458a53006ee7458a53006ed7458a53006ec7458a531feef5458a531feee5458a531feed5458a531feec5458a5304eef7358a5304eee7358a5304eec7358a5304eef5358a5304eee5358a5304eed5358a5304eec5358a5304eef4358a5304eee4358a5304eed4358a5304eec4358a53006ef7158a53006ee7158a53006ed7158a53006ec7158a531feef5158a531feee5158a531feed5158a531feec5158a53006ef4158a53006ec4158a5304eef3158a5304eee3158a5304eed3158a5304eec3158a53006ef7058a53006ee7058a53006ed7058a53006ec7058a531feef5058a531fe6f5058a531feee5058a531feed5058a531feec5058a53006ef4058a53006ee4058a53006ec4058a5304eef3058a5304eee3058a5304eed3058a5304eec3058a53006ee1058a53006ec1058a53004ff745865301cfe745865301cfc745865304cfc735865304e7f535865304e7d5358653004ff7258653014fe7258653
  | 43 => 0x3000c008000000e0008002000c00f00080000000005001000700040000024001000c002000c001000800100040030028001000000200000040018004000000000180120004006008c004002800100080020000001000c000003400200080000000000000c008000800000300020010005000000800000000008003006000100080020004002000800000000050000000003000100340060008002000000000040070004000001000500040020004002001000100000000000005002000000000000030000001c00d00000060000000000800600080000004005000800300080040008000002800200000000088000000400700000000000005001c000001000a0004004000000000000010004000000000600000010000005000000000000030004007001800700280020054001000000000080030000000000c001001c0040018000002000a0000001000c00a0038003000000400040010010004000000100200010000008003c001001c0100000000000c006001c000000400200400030000004000800300100010008000001800a000000000080000000001004c000000000100080090004007000000000100000020000005c001000400000000020008002000c0040010000000400000300000010000001800000000030018001000000000140040000009001800500040000004000000000000000000000008000000700040040000000000000c00000020004000000400100040000060001000800000000090018003000c0040004002001400f0010002001401900000000000004000400200280070018000000000000080050000007000000000080170000000000800000000040008001000000500100080010004000000000340020008005000400100140020034000000000b0004004000000000000010008003001c00300100030000000001000100000010004003000c005002001e0020000001c005000c000000000700040020000008001c00100080010004001005c000001000b0008003000c0010000001000c00000180040018001002000000080020020000001800200040080004000002800b000000300180010000002001c000002000100280030014005000000900000000010004000000000380020048000000800f003800b0028000000000b00100090000006000c0040004005000000b00080010000008000400800080040028000003c0060008002001c000000000600040000004000000400200040030008001001000b0000000000000c001c00200000110008000001c000000c0000008000002400100000000004001001801704cfe76d8d5401cfd75d8d54024fd74d8d545e6de53d8d545cede43d8d54014fe72d8d54004fd72d8d54014fc72d8d5402cfe71d8d54004fd71d8d5400cfe70d8d54004fd70d8d5400cf
  | 44 => 0x400000040010000000001c000003000700000000008001000400200000020010006000c000000400000080060050001004c000000000000000000038000000c00f000c00000000000000000000400300240000000000000400000040020000003001400b00000000028001000c00200400050000002000400700100050044000000400000000010004004000000000000010004001003000b00000080004000000400000240070000002000c00000000030004000005800f0010002000000600140010064000000000900180010004000001c00000000020010000004000000000000028004000400000140010000000001c000000000000040000004004000000600040010020001000c0000004002000401000040030020001000000000300000000000004400600180000024000001c00300000030000008000400e00000000004002000000400400020004000001000a00000020004001000000200000000040001000800200080000000002000000000040010000006000c0030008001001401c000000100280000004003000c0020004000004400200140070018000000000200080070000005001c0000004003000c0030034008000400200380080004000000000000080050004004000400000000040020006000400500080120044007000000000200040014006004000100000020000001000c0020000004001400000040010014007001800500100020000001000400600040050018001000800e00080000000002001800100000050008004000000000000010000002003c00000000010004000001800300040020008000000000100080050008000001000000000020000001003800100000010010003000c00200000000018003001800000240040004000000000100000060004003000000000000000000003000000300140020000000000001300000000004009004400500080100000000002401100040000018000000000a000400100040000004000001c012001c0000028001000400200000030018010001800c0010003000000000280000000006002c0060038003000c005000c000000c00300080000000000000000100100140000008003000300080110008000000000100180000004003000c000000c0080018001001c002004c0000018003001000d00080020000003000c0000000003003000d006c009004000800040040008001000400900040000014000002c001000c00000100060004002000800700000000008000001400b000c008001800000000000000001000000000080000000000000000500240070000000001c000000c001002c00200000000014006000000a000800000080000028002000000c0010001000000000040020008004006000c00140000004001000401600040040004008000000000a0
  | 45 => 0x800500140040008008001800000000090000001001800d000400400000070044002000000400000010000002001c00600080000008000000000b000401000000000000006001c004001c0030000009000c00000040030008008000c00e0004010002400400000020004000000400b0028002000800000000000020000000c000004800000040010020008000000b001c00000040000024000000c00000000030010001000800d0000000001c0000004015000c0010034006000c0000024002000400c00040040000002001000400000000000002000c00000040050000001000000800000000008000000400700000000000000000000700040000024005000c0080000000000000900040050028000000000e000000600040030000000000000100040000014006001800500040000010003001000600340060004000000000f00000000020000000c000002800500080010008004000000400080010000000001800300080050000000000401400000040000000001000000300040000001002c000002400000180040008000000400900240090000000000400d000000000100000000000000c000000800000040050000002000000000040020000002002001100140190010002001800000000000000000000800300100060004008000c00000040060000000001c004000000100040010008000003000000000040008001002000000400000038002000c000000400a0000000000800100080030004000000000300040060000007006000300040000000000002c00300580230028000000000000200010028008000c000001c002003400b00100020010003000000300000060004000001400b0000004000000a000c001001000b0004000000c0040010004000400300280050000004000c002000400100100020000002000c0000000001000000200000000010006000c001000c000007400300000020038006000000000200040018009000000e000000200000130000000000c00000100010010000000001000140050048000003000100000040000000000000400680030000005001000a00000000008007000401700000050014001002400400080020000000000400100140050004000000800100080010018000000000600100000008002001000100180020000000001c00200000050004007003400b00000000028000005800000080030000002000000000180000000003001000200000000030005001c000000400000240000028001001000a0008004000000100100030010001000c0000004000002c0040004000000000200040000004002000800b000400a00000020000003000000000000000000000000c00600000030000000000000400140050008000000400600040040000000000400500100030000000001c0100034007
  | 46 => 0x50008000000000b000000000040000008004000c0000048000000800100280050008002000000600080030000005007800100040010014000000800200080000024000000400200200010010009000400b0010007001c000000000500080020018012005800200180020004008000000100080000000002002c00200200010044005001000100200010014000000001200280040018000000400000000030028000000400000080000010000000800000000030008000000000900140000000000000c0000044000000400200040000004003000400000480000034007000c00b000000600080010000005000800100180020014001000000000000010004002000000600040020008000003c001000400200000090004000001c008000000000580000000005000000a000000700040000000000000800c00300000000000000c0070000001001000100080020010003000400100180010008008000c00000100030000000001400000140010018000000800000180030010000000400d00040080000008000800500040000014000000800100b800000040000000000000800400080010004005001c0000000004000c000004000000200000000001000c0080000000001000400000020000015001c0030000000000c0050000007000c00100000010024006000000100440080004002000400300040090000002002000c0008001000800000000000060000000000000080010004000001800100000000004002000000e0004000000400200040000040001000000100140040008004000800000180020010002001400200000090010002000800000080000038001000000600140020010000000000f0024000001400000000050000000000400b0000009000000200080030000001000c00600000030004000000400200040010008000002c003000000f0000000000800400ac000000800200080060008000000000300040000000000000800d0010009003c000000000a000400000100010010007001400800100080000000004400100000020000003000000100040070014005000400300040000000008000000100080010024000000000100040160000001000400000000060014004000c0000004004002800500000000004004000c00000000040000000001000200040000000002000c0020000003000000100100010018000000000e00200030004001000400000500000008005000000300040000024002000c0020004001000400500000060000000000000000000000000000002c005000c000000000200080020000000000000000080030004024000c00100000000000000001000c001000300040000000000000000100000000024006000400200040000044005002c000000000e002c00000380050008001000800c0008004000
  | 47 => 0x2126205117c1ac0de607b800067302880000000986b28600000008382cee00031460002a66000266c0002be26b90ebed832b8ae352c3440534fe5741878ada164a905262e6d407e8c441194000372aae2156e63086168820000a502c18a2b35c089e80000000000a903754b7f80000002914000235e000000018f35c800029cc0000000000000008f9e5e8128000e230000716000004083b26929290cd81782a37143e0810000c3607c207f8000e1400005c9096a00000000000e5c66183e06931cd6d900000d6b3094387ac540000000000000000000000000000d7380005b300000000000000000000000000001b900000f4c1b6a49c34f0d386550000648061c0002c3c0001d0a4b9800000003fc237110e000000008819dc000292c00018e6c20287a46a8bec84c81d8c7022483948d90c7a80d60000bb21841ce405f86e2ce1af6e77c190c9e723344a88000384000019704ae00000000000000000000000000420002bc20002a920000000c06b8c4000281a0003238e12000013c00000000396ba100008ef11e420213c25390dec05a0000bfa8000024189860b91249fd2e7ae179ef64b3a3d850c9fe6582a024180a45472d14f4586879c7f02ec2a70ac4c8d719c874d80000001cb857b1fb400580001ad202c070000000000006cc800038b8c04a050000000294665424663b4a5de2d2016c3a288fcb4dab6c25c800086b80004250384884000080f29a20e29944a841b1200009ba22aa20a71899aa63eaf58cddb1d67f138ac52f0000000312e000000094bb35a0000000b7014a800000000000000000000000006c00000000ae72c08620831c00b29e80d60000000000000019fe66307f23158000ae102f800021986b292b0347a36e000000000020208210000db7aff6000251086ea5163cc00000000000000147aaacab3053700004fe0000ccf80007de80000002c620001496e358000425a59ea1f1fca14b37600000000da90000000000076080000000000c0da0a463a8fc20002c4e00003768b00108670842024a8000a748ba400000080010003000400000040000000001000c0020000002000000100100000010005002c016000400400000000000003000800400000000000004002800200000000000002002800100040070000002000800200400000000001000000000000000000000001c01100100000000004000400c000400000040000000005000400f0000000000000a0014000002c002001400000000000000000000c00000000000048000000000000300040010000003c0000000004000000000000000028000002c0000000000000000000040000020000002c002001c000000400200100010030001000c0020004002000001d000000a001c00000180050000001000000000000010014001000c00
  | 48 => 0x120000e880000efc03a800000003e600000009b0b3a4db32a62c4c17e2e3e80000000000000000040880004b8a2eeb213348506920cad90ac41669b94a5f9b0000001e610d8000a35b4909a888827be8000000365c566a89c99e80000e4000069d800064da4761e90000000295003d30627ab80000002fce85facc629700000001fa667eaa9425d12da5e2016e86835807ec038659c30b82d5358c055a0a09fe06c2adfa6607bc068c7838e1a08531e6b688c2c0000000000346c162928e0002c8a94993be00000000002c0a0000000c571f6a6d08af00002a56000000000000000001ab800000303a7800000000006b60000769aad200011cc00028b855f12684bc958e03137ae207b7fa0001c74a0f89f2000000000011ee6ec80004410b2c29ba93000000000000000000014e000370c0001ea256280000000000000331e97012c6251139e1729b1e000333c25716c4c498b1c2d032e06388cf2a79186e0001af49c114b60001dd8d748000e1a31a08d0332674a00000000000c350000000000000000007b932d44aa8b38b6196c65169c6a1f1966e1c2000000023000001ba20002d9e0002722d7f342eb43a7ec380b4e445c0fac3e528ce9f690f4110000062100008070000000114a00031120000000000264e061896000000000001af80000000a2f83044d18aea1d59c2200024aed9992785469ba80000000d9a000041208943cd8000373000000000001b100000002d040000000e45021600d1cd2448046298eb23000010f21308000de29e7a87990906e1000085880008e9000000016ba90800007292adc3942486913012a6d580000000ab8dd78000e1820aa00020ca000000059f0000000191a00001407598000c6324689c78000d3caa6ed5285f8672b50400000000000000000000000018049c6922a1a101f800035568208000c2c83605c02c8027f0000ae30000bbe2db8000062800033949d8a6127c7a3709f1ac4a9be8c427009a9677d212c0b63456af493a803b896e6f7800065037bc0000000c87800082e0000c289fccd6100000000f127150000000000003401c837cb26600000009af8000d1c0aeebe8b67042f003e0001e68868ad500c41c0c18d191437f2daed5035d4b698d720003636302241a3ee00004f60000000000000000008619ce0e2c35b47d3800045d8000c8985f056a800052c125623083f8000000000026564010000ae533a01f882e2d490000000369edd8adcc1fb000060a2fb801c0000409800006a20cc02e125a450b6f4000202600000007b4800043f1e9200000000000000db6800035d000027a383802809c492022ced85000000000005a7000000000000920000d2f90522bc89cc00009660d7a2ec0003894796b00084e124e0ef8cee2a19b1c0000516a8a800000021f0b5988ce00012c4cb307fc00
  | 49 => 0x480002658000000000001a00002a3000031a800000000800000a140748e6600009e0af6000038d9630bbeab9800000b40000afc72385a0569a0f485483ec374118a0000000cfd368ad0e00000002fe06f587f400000000002fbccd8958647eab12000242ca329cc40000000b46b2d815f167ee471ff69ed0df81f9b7a05a9875a25d982214b98c46eb8b6a3b000002010000826800000000000003170aba9da80000000007a91687700000000cf000016d8d8e05600000778aed36fe00000008d5b5a05c0800000000006a91d7c0001caae5625927728b7e7bfb11a70e80000003346dd58000d6ba02200019be000000084d02783ef8000a530d120001d18000381ccbb054c0000000a2400000000000b2d800032e0000d4600000000000000177c9d780002feb3420002f6228222502c694580318f16bc988d25b380009230000dfa00004c180000000000d8f00005b4800024686d2411800001d00006e6960c7e18000000000000000009390000dc1112c5e62226000000073684c4400a2623ea1b020001becdc01c96641304089193686390fbc519046ea9d179c110982cb5d313aa92138ec77205cba698dc10583fe4cd1f0200026222e980000000000d8a1fa000026b2318800000000008a217680001cfa77aa7ac00000000000000bbd8dcaa81055c94a8d3e1a71a020461f10c50a08eb20858c8e334f8741180240b199817d98880e52de23929a66039867c000000061838e6000000070009d2000000000012dc44a0cba8ff26348aa80000000000ded97d653300004c0040e000000000000000001e4c9538000533800000016000000000c1c9a4600035f00000000000295e90280000000000a22000040a867000027dc0a607f65ce80000000dae000210400000000000f0049480001288e2c3680e067560000d7a9e60ab180000003092930800000003327960eac000000000000000000000afc80000003294b5916be78f8000000000068a9578000082e0000d42bc38f3400023a0a408000000000000000008f319889a229ec36288980f596c030c80006090000000000000017da4631be00000db20001a1e0000000000000000000000000000000000000000000000000e3a962ca9c8000000000035f8000000000000014049fb80004e282e000021540000000a62025a685ae2e00017dc21131f00490000000281235600000000000b6f0000de1301e96da61443e0014000250257194c80001bcaac500009e326cc12d00000000000a9f211000028527ef000084700000000ab43c8800051580000003148000000057200000000000c56856600000005cd84a40000000000081c00018aa2f9384e3bc9d1c93c3340000069e1da8c4a000051874480006c50000544000000021d60002faa00000000000a3ed39a15ecf60000e19a58c00015
  | 50 => 0xa8a0000000000000088da8c80002a0635ab1a887600005b818b0a78a12245f8540c2c0000c7d109200000000002736b6237bee1ea828c398e2018d8000000270a030800054d8000d129aaa000377a3650f9a26a00000000fd2526b8ec3b98000000000062680002b70000be080000000000e4280004b8227e00000000000000a598000000316c45707267f5b70e102000049836f094e96680000000000000051400000000e4200000000001c92000000000005c0ca10000b3d800091c80000000000000000088f000025f80000000712e5680000fcb00e000137600006ac000280613a80006c380000000000d810f445e32732ace107c00000000000000000033c5570000000075cd2e1b206a111fec458000e4a16b80002058000332e9579e328d1989e801ab8e87b030e507ac069e180eca6b976a4cf31be66db826a3e268a0000000154151e794800000000000000000000000047b00005f783c8d9091c66530f1c34b02f6b7919760000bc86c61c600000578d9780005522b060001d0eb40aae8c5f00000000000b259d46db41fd0d50a02a5d900000002520a290000b9e2432753956014d197c5cca2d2d8380fc36e00aa445000000022560003596a0a93b2de638085d01442000318249000000000000000000000000003f69f7c6e79d3c4bd1f701b58000000000000014182e80096d062ee24170000116175c85cb2f24531eded9333840002de6a652d42cae94f28d4375866134d0cc4800000014c081c800000007da8b42d5e1549d5c0000000b068000c63aeaaa2d1690b8880000000000000324a0000000000000045534680000000d5990dae3d1ac20000574c6515147dd1d1400014fa00000006f881cccde800070b0000000376440c82b63fe22e206d0d760000136091800073b800081e2ce40003252a13a29ec1980009fa0000000000041c800000000006c32d3e11a8000000000000034320002b221dc8000cb286cc000000000028a600000000002baa000090a6952cf8b4883687b51138731b6ba93316569fc19da0003834000222a0002e986f219a264480008ea9fa431800000002bb61709b66929b04651f866c88b8000000038800000000001d1e2fc00000000000a4000000000190000000093000000000000b8d936a75d800000000000000000000110a13983bc99c8afe000198e000106821a00003dd0000abd8000912000020f800076b800000017e40c91a004f80000000000000000009dc9024d8191ba438ad828782606000061200000000002df400009faa2a25c800000003d500000000b5617b81665a29ef2823000037083262178b645858000bba000056ca1fc5288c86a1f91acb1d0000542b1acc64a5c4000082c000188c00035f88c2b41c8b216f099b9f6200000004d2a7b00000000ad21acc000000000000005
  | 51 => 0x2e020000000485a6840001fce8fa8000000199e9c4962e00000005a787666d786a000000000000c500000000000114edcdadaa93137883deb82817a0116bcfa8042eb2fa61abaa2c9c81166ad78c8c74b095ebd384c083d82c0e389df2a413748d369c1a26b81dcbc6353eada88468e8b7348a08666000067ab5280002a4997e9e91942475117a14e00003c38000d5ab8b833f24d45e9990ed101db4a7e32f800017a4671996200029360001a8e000200a113afaea5a30f600000004e30590c37a34e00000000001cf4000295823305e6e0b80003aa043cc7290ce0000000c339d98a649b58000303449f213c2d2800042e0000628800000000008d60000000000063400000002cc00000000043abb003a00004c928387378000681800000004f6cbd0000c57800000014000000000000000070d0c929f9000058e000024f040600025a800016f45fc26b8ab636d854c898422203d06aead987ba3122a4d000018327809bb347c0002bf00828000d402a167058000000000079cb52600000002ac800000000000000000000000000000000000000c2b96e600032809cc00000001b4c405b7a269ea6e676394e200000001dd0cde00015220709db033280003610000000223200db0be32000000000000c1e8000d4b80002d9961800000000fa00005dd8000bec89b6b35946a17d000085e21940000000000000095e23323e60000000000016fa7285690fca000036425c18900b08e481d40000df400003b10bb600018d634319a00f329fcc23833ad860d862b3a0acd3831c4d188000000000072b8000a2ab28e000000062b8000000275400009c2000000000000007ff083c501b836bc116c80000000b18000009a93d60000aca81b00000000000e2480000000000cbaaa02189800000000001688000dc82b722be2b2a00008a47350e320000f3800003b610e38fe69080009b8000000038a651200000e69818a6321d00001e48a4fb06ac129a725250000203280a1cf8000307b81ec36a3a6947329abb125cabe800008fe1b3aaaf253c47e31888b6ae744fd96f80000000347000093c920400010ee0002e5abb00a020000942185211a670197246380a2a839bfc000000000006320000000000149e00000000000000987aaa80001c94688000000000000000ac62360000000152c0000000000000025ea0660c6ae000000000000380a0001ca8a3b930e18e2784339000000005e000013560002ebe62802423cb061e38a36020001212b1d9236b91800000005c6cc293acc161ed80001fe435c00007938f02a1c2bc65d29d1059eb94acbf064a52a8000b85800000000000002c925be800012c80000001d4263698766e2a7000000000000000083380005ee8e4e000000043200000ea0000000020e0578e460000000e05000000016fe0001
  | 52 => 0xb3280000d92000000080fa37448008b255b0000a080000000000000021bc21f324c0000000d5788ea10900000001c7000000000001e3000034dea5e93d277880000db143a10018b2e1680000003274c308b76000254017e9ebe798a7fe00033b800000006ee8000dea00002c4984c93a34ac00031760d3231200029d4381047a96cae900000000988328a0002ada0000000000000040402c40000b320000e0eca400005dd140803800006cb15761f22a8c85b0cd41d609d4269b27800007ba9388c3a41427f2a0b84fe36d2d40000000000005eabbd0000b44b90c4fc0b741af31a6d921b96d4e8b8630491b6008115694c051cc6c96126a725aec558bea54a883ae0a98ba0001facac78000593800000000007280426000000000000000001e7e00000000003546b9509980000850cf39e88a9797607be0000c8911c400b9daa3db21660001ffa00000005c61bf0000000000000000000000000000095415823260e6c28a96b6266a8821d100009238000e34a68020a8422126108a2838000818000000000008e00000a5b32c80002528000354e0000ae091680000000000a17853a0000000000000034e80000002b2491b31a47fd000051e2e8050997c00e31afe0001d74000000009000000001e26db88000000000000000004f3800000000000000c1000009120000000000101e5d4ab180000d5ad8708ee877b330bb7aff875313a46198000bc580000002642ad19da00001ba615918b68ba80007da0000000254600000000000000221000066f00000000000151800037580d400016a8a3f00000000000d478000c3f21284ba9d5e6840d3028e2b2e00000009550b7c686b2a62830ff600000000000000000000079b0000c3b8000a380000ce38000000000094e0dc43a01e0cbf7013abbc80f67991994000386acda80000dc871e749afb60000000390209846f3044000307416bb05215c8000355214c6002d80000000000000003b18000b0532acc77800000029ba00030eab74835a00035860002d2c447238409900000000000000000000080000000000000000000028ae0000000958a6a0ae004e2c7b87b61d0311800034b4a3c800002b8ceadcba06212aa7cc0c50964677889c36c221600020ee5df9e2231b9ade7e432d619506c6a8e0b6e000000076e9e38de4183c00000d8247991659804ee4409f6c8c631d800017700001eec0002348e5b00008df34d475fb79a47201e2b2d0064a30ad5275436fa96e974cb0eb6f8e45951856433ba94b2e8a402146c86cb810a5d14602ba1e08c6735589511a980002960a4894a400000000001cc093b80000000a5600014d0d3aaca40000d288fc8000054903c45b80008a009464cc0000000000000016c270bb8dc0001e9c04180000002202000000026080001c3826000000000000000d7a3184
  | 53 => 0x257cb3162638000dd000000000000000000046980006f130aa00000000001ce6a0f00007510000e1f800000000009e6800000027027848ce61b410e867a350cc263120305123a00000000000000d9a8000000045e69482d25918000000000036200009d91be80002d3ce438f666f6800082ea44400000008a680009490000000000012700007dc8be69b5aa8615209f40000000166063a000239e0000000000000000000000000000c84800044fb20c41e8af4000000052434a2c86adfabf53482b8738ded5b2014ddb8000000000028432d01939744c59b6ae1bf132e00000000000000000099cd0480007d7800097800000000000124940e0000d5000029ca000337000004884d88000abd28944cd800000000000000cbc000000000000000002bd6c9600001e3aea400025aa00003c40002c680370000000112689a8cd8b58aae43ba91003e98000cafaba44c5800000000000000cc8ad5aba0000000063b000000009e477991320000000000000000000009d1b900ceb00004d4af648860000000000000000000000000b1ca3ac00022b254e80007a010f0000011e0001b6a000172c051af989f59cf63c3320265d2f889dd18d200000000002cfa412800090fb9127a60000cbc0000c8700003070000000000051880009221c3091e8d0a52205d60001d9e0000000000000000000000002c780b583f64440000000000019ab8700000000c180000895055e0002b401b900005b73206ad72e380001f0a0000000376000000000006bc0000b898000000267400000002a107ae00030420001d8c0000a180000000bdf80000000000421017a026165cc9780000000886000086e00029dc7a122a200000000eb8000daa31e46a20000000000096e00000000000bf2a32a8fc347a00000004d6866e0000000da632cec330000287a95c77da2c6bc8800000000000001c0400014c200000000f6adb400014e60000000000035c00000000002b860000000000000000000007fc33c07fa0682c7e00000000000c281f42c7c8a4e24ba7cec31ae0c1c280004fe95ba1c58000152a89ec8518bc00000000000c00a349c664619cf85e68000ac0a1d2a67391e9e61d861911fe254c0a582ce89b4a5caf943e700000001d00000000000013ae4c6a2faa47b63a00011080b7265c500848e5898000e1e05060f7b7b860980006e6378e83f0b8c0a7ad72708339ab941f0ea9e376a0000a4400000000000000000205012980000000000000312c00000003bf800000020d667880004a90000000203a000000000000009469262c21137029500000000ef4000000000038c80000000000000043f81fa00001d06de00000002dd046f985a2c98000af301a29858be248e1f6081b9d9082c000000004940001a80a690000000000051a33e80001c32a739dee0001dfabf1
  | 54 => 0x580000000000353800000030b41be02ba0000000cda0000000000084d95b800012b4000000032a8afa00037260001db20002b1a5b7995eb5620400002a605708000d9b9e3a10c8266a8c9b36e1b817048212480002c1e0003548000111a3518f6a00025707d93424037927042c800000006b2a5d8ad2e1738f8d0c000000032ae00003a416c000000000006c8a1b417b164839ba2ca8831ce24bd8b3e5cd09c60091106e51376c01b006056a0000c81000000031787f1987abb61e660002864e40ab580001c5c00000008ff800000017e85710000dad8a60d9422d80000000000000000011727fb9288000145eb9a32b079c20a66f01e160000f287748000c7a000000000001e985b63ed31d2d4c800000031bc5f1000095aa04c51d06be7418000263224c63e00000c22a9c5b900007100000c8b0000dcb337e000133e0001d9a000000047d0e562d300000b7948626f9c9066026b4e51ad9caae800041c388238c1674000218ae3600003599e349df377c00a1c6ebbf8000ba80000000001806c17ac918b38298c95e2bc8000000000003fe80000000e1c00000000000eb86a80000148b5120508000288800044a80000b6a5760001c72c542f66daf2cfc000374a000214e0002bacd02a2ac0000000c7b20d800033b6601800078a1f360003950af380008e3800000021442dc9a62b7c88f43d807620001a4028d0f728bc2ef0a031556a4a160896196a0000024adff0fe2e5a2e9c55692c80001bf473601305f38000000000000029800002268cc500007aa36543be8000000000000011d6000267000000000002b00461265aa9923cabdc800040e253ecbbac6e6cf368664d1bdc43790c2852348ca79b7801b794ee69b92acdee9b6401499ea0480d9874e13fe9c20000097214aaef9d966fd832c90a015a1bbaf8400033e2a8c0114d76b69c35b0e78000011c7a80e5e00000000001c9800002942e480001fb8000b64b8ee1c12c2034ab5fa856978e000000000000000001ec800023da0000000000000000019c4b370b9e11f9dcee2197c26cd000092f000000000000002fee000097c0000baa80380000003884d62970e29c8000df3b7f6a1a893a38e2c16000000000000000000000368a6fe2b20c760000e080000a2c68292ec9a080003d380000000000000034056f1dbc6e830d0b2e94d66ba0bae000000077083f00000000afe80000000000c40a0f09dd9e5600000000003300000000053d8000a6c0cb400011e07e30000a5082b4b7f1196bab8000c70944c5ff0dc6d3000002f7806ecaf221c0000000000115e000000000035ca59db70a0000650a8280009368000000000000000000000bd2000268c8f9874e02498d41a92ee00222f0255f80000000fe8000245e000266204d386430c2bee1ec1b7a000000066e0bbabb3076cb9ab15
  | 55 => 0xac264177800025dc0002b9298a2ccc2ca364eb56961eb82800058a2da491b832820592aebe31dbea38ab042c43906d9e36c2e01a7889fd82e6b99071072006466dfab266e30000e4613429c580000001c843a1870621297e0c9e80002160000dde22946bb2ddc67380004a6800000029567852bead40b4f4cdd0cdc5769a2e336800cbcbb0ec0001438de3092477900009bc80000002d2a0000000db380000bb8000a7d2de8000000050b09b82a980000000dfa40d0000000176c5e10000000000000025c2000000000000000002ea20003786a3620b241780009b52a4c0000c9645424507d000003989abe41f82f42fa29e00ed36820a01dda9022a362909d7851b88be000000000000000a88000000205248f00000001fd8e4f25ea49c8000c788c9e08d986423980005b4000e000119ab3a9840499000046ca452000316ecf580000001508000327600021ee6ac0000492acd200001b880c96360002dd64d900000001d68d4d2afc01faba880100000002e3a000305a000000000000000000ad080b80000a434ec1d20000add800030d12b6b9735f200000000000000d31895800000000002d784a185820000000c550000a871e74ad4244058d090cde984608322eb200033c200000003a30000d9e9bd84ec185000003922aa00004d62ee47f83002000035200000000000000000368c850a0868ee000000000001da33bee3da9861231b240001dacc428000cf997042c500003a71e863e38776aaab7b4ae58000d96068e76100002cc08bc2e417484f9800042b23de37880004d78000b82000000000000000000b2400005658000d0300007b4303a7aeb81ab0b0e0c000259613c95749d4800008998d893e80000000000bcd93320001bccb4814148810000c938000522800000018c63fa9f440a6953e0002b6094500000002d1e6b012fc0003190048a412ce21df80002f08000000039f80002f6800091f809c0001d9400001fc0000000a0d0000b09af4cbdb00003eca16065a251215a0796b1a800000000000002d5c470183657394927ee1b9269b17e6912a91a0002cd800013c688e80004299d0800000000003208bf5800000034420000b8e0000000c5a0000d30ad1612e800000014e00000000696816a8af91823f5b85402e880a116b7acca236e62f601f46ed25be0002bf85baa302000358e3a9196a00000000000000000345e276000045680004f400000000000cd12cde78f022c4083336a3fa0124168e60c39171c0001ec69e49d3a00038aa00000006478830d918f9e5b280b2a3435084d5000000028c611c1c5e8be00001140000000108864f996caecadbe3da093e6c1201a74d0132000000067b94986b1aeceb783560da581be0000000198247c7c4b3c8374ad4e281000078794d800000008378000000000000027de0000000dc
  | 56 => 0xa200000001074e2b80000000d4000000000000790514ac5093da91800003568118662e30000085f000000027c8494055a73380009caa6403100000a8890c06bf0a48c2f00004b5352266b800000000000000000b118b461bd000000000c803e9cfc0000000000121cbee9b4e0002db2000000054900000000000155a2301c6b83eaa60000d7db34a0002f3a0001eb84e4307c8d2ac56d6084d632800006d19a56969abf6a1daa460002ee6559b6beadb9dc60df800027222a8b84b264423857ad3db5b655193609a1886c2b89edc60539421d484b03f1873833f800000036640752b5240da5d019488b874c34060001b1698e0ad400026bc5cc25d2b38aaee7a6b8a2a5381bccf90c0a55323c078123f4489b23e13e800057632200001e78c920b16979862053100002450000c8caba6a7ba6089d980005e02ff43b6b1c6289081ab4000000001624c8600009c9327ed41862aab294820000000176a2243a136c00a3b3fa8ce21fe000180c065aeb67ad80009bd00000001202306aa1eb550bf84de355c0000000d80000000000005fe0000000000000009f800000000000000c0b8000cb8800000021880002a340000d22000000004e0000000000026b0000000000000032a8000088c4e98f56ca60000000000000000000000000956889e4a70000000000000000000000000000106411b000085c305e2859fb6000000050580000000ea60001d32ddd9b7c0001dde43b2b16000148ede48000000000000015fc896a4d0b90800033d0000000000004f000047f227ca101606c530dbc792896800035c40000000000258e0000d360f38000b5188520000000000000000000000238f7e0f509486a9800007a8000d8900000003960000104e00013bc00000000000a8a00006b60b40000000000012400008cd9a860000000000000000000000000000e220000bca00007ba8000000000087ca552617a9c025585a6bae943028f134ecb9916c699079a20009fec25b06ed1235ba788079200709cad55248aa42330414f28787911a5800005fc566311c3aaa1f8000044600008902e601a09829b4a0002ffe0000000577000000008600000000000100a685000000000000000000cea026206317b0aa900727c3139a2e886688f5800000000005ca24e66d12498d54b3fc560000000037940000000000324600000000000000000262cbc280005b5847cd3c0000000000034400005d42d700000000000073cc8bae34000000051c07b80000000000067e2db33567e50d441f90000a9484b6000042ce2600009ce89de9eb800000005020000c5c0002cce036a3ced5a261c338363eac700002cf00004e12548000207e0003422ce2ab329a48000dfc2344000000000035d80002e7c00000005ef80000001b9c00000000001122000000051ca3080000000d1aa9
  | 57 => 0x716e273272d69365a0b500002328000000323a149933a07c80002422e149838000000000090e0cc200000004310000000357200027c4780b7b239300003c9a396d16b36ee548000000018adc2050ac0e0e2659e216a55ca9b446a1ce80000206cb4b73c941005e29c09109ec8000bae00003e4000000000000000000c6da5d40000000adc3282c9f077a6058ee8000285090f140abf4895088d31002a000009da0000000000043606aa7b321c0730a0420000f5a1b70d68bdda64800000005200c7a00000005ea98420000bbc9f000005ed9efc000000000038cc000000000000583f41436000183200015e600000000002264000000000000005e5a9d8b2c959c00000000002f2ae238d2400033500000000e2f194ad7400000002be070511742e68ecc095122e4aa0000aebafbe67d800000000009ed8000000000000037a4ccd38f2000241ec4e08ac00012b800008668059ae0c028a367ee8000000249e39a036e0531cc8b0c9d4a355b4e877b0a1c0001f08b920cae00000000c31ee0000072e0002b4e0001f8400000000000000000000000027fa6128000b652926d6f2aae9d32124a1a12d64ed888eb0bb1e07a2800000014ecb862378acf98e8000213e3cb9b26c731614d86b4fcbd5a31abea03ac000084c000182ac9a35380000000e26a2149f4969a575000000000001e2000000000000002f120002eb484280000000000b3521827e6ad440000000cfc21920000184bf0807c00000000002abe00015b498c00003b60000000000000000000002be60002c9a00e9be600000000a81410b0c29d62f38000508a0020001fdca658e9a24d85840c2ab620210000000011200033a6dfbaf8035880000000cec0000000000000005907d0107800063286480000bf600000000ac87468ce96207a30428994b4cc96109f0b66870c4919c8adf9a95a4518876a8ea2a0033179400000008e6800004fa4debb529c4bc02618b3c3940c32000015115f0bda939c50b8c8e0002668df3227895b9c4a00000000000a5a17380000000000000000000012a6cdb00000002292a311c069d59e7c7040000000000000000540000c1898f80000000000000000044d1e9600018f4c982c94dcc831655a25da000247000002fa00000004df800025e09da00007bca1705960001f9600000003f70000000000000000004c3000000000000000000000377200014a658a800000025940000000dce186cb9cac5ae158b5e0002734d73274000037308a1800000000000000000b2a85d40000000e4b048a0c026b60000434000242600000000000000bcb00001fa9b6200028e6000000089b9e6e3d1b35ca51119ec1b1a3a0001b1a18b8000bb4b26a000284ac6ea2de080023abdf0ffc02f0554a21ab5a65b8228855b3083b438a8b1f1cb29250bd67ef800000018f01
  | 58 => 0x12fa458bd0a1c22690a6c8aea23e000189c0000000000000023db616dec230614902389421ad00001c560000000d3b8000cea8000a9d80005a3128a097b41400027d401695b6a698000b47000000000007e700003dc0be0255082200033c400000009dc190a00026101790000d7b9aa26b4aae64c112de24b246497d049a2bb0f58000000033d80000002fe48e28000000000000019d20002c9c0002c2200004aca4aa1c4713b5c6a37a99e00013de5d9b516000156400035e2000000095cb6dc09b80004350056dba141c000324000000000003728b6e80000000000000000000000000000000ac30000b7e00007eb8630000264ae0e8000cf4a59806627be82fa91000023b6bc52fac57d971a640375a000099431390dc00027a836a16bc7d72750df0b6a00002ce8000251e00012fedab282660eb67c63daf3800000003f7ab3400022c22868000416256c0000000d320000105344e4680e58cccae1005800000fab68800000005990000000000047a8de852e3380d0ea37213210e4a612af800033a21ecb3b239f36624690268d8c07d61860d7a6acb3ccb65911873b317e1c9123ed77b6f62f0392000000000000322cc0b67e0000000000000000000005bf194e6029cbc0000000000381200039320000000d1424d25e4b8a07ca9542509375206d92ee24c0bfe2d6909800004a005e142a0000e96b70a83688b00008fa0000000000004430ba66a000000000000000c7e000000000000000000000000000000000000c8307000028ba289a646ca4b23600000008040672e59217483491da380000000037c800000000000000775379e000000000000000c093b481a97d80f716ee83fad103828000659800000000000000000000000094198bedfe0000d5e24920002fc8000339232100009f82a260000000bb59550000357e5ffb7aa0000000d09b2540e6000000024a20000000cb1999a95fb024365800064ea5227548000978a9980000f100000000c170b5844e9b70955b8e889280002b9000000031fc0000a960001adc0000000b8f8000a7400000000000a230000d6a98940000000c490000000039c8b700940000000000000000014280000000386346ec84298a000310e8b99f7e08303420aa1f004b43478dbc8ea2d5b8ac20122f9c7cb83800000000000000068f9808000105672b106a7c71da400002320000bd090c04841690b8a5d1aad0ac2b66c0001b28000187e0002e2a78407ace59815c000000000036a20000000095b10cbd18000bd68000ce3243a8ad0000000353607a2dd82f72b424840a5000006f699126769b39c185feaf3cb4c9544a24ac04d5e800000000002f1a1a6975872c4b02f0c5ce25cec4f000097a285a0000000cd318de37905b88030000000106c3721ae20001ec0249961c2c0aa4e0000000a5a822a0001
  | 59 => 0xaf1e0b3240437d05aaa238000000000000020c46a40c06e36800000000002190bf26f3a90c020b076606a6dcd111c24883b71c813a7aa0001d1652c82f0000000083019300001e06d56abc0897231c7b68a6447c9afaa0599323319712b6b00004ee00006160ece338800063c8594000000011595040001f56c0c34600002cae0000ebc0ea8000273924c00000000001d48ad2a6a60001c08000000067e34b0aac2f680000c9000000000000000000000000000004db00001f300000000f840000de000000000000000be4a75a000000000027e695e8000000100c97e0000a6a000045600000000c3600034a80001ada000021883086ce9bc1dcc75c2cc4bac12c29a70000b71177245a339600000003ce8000a910000c5600000ce00000000000000000005ca91c28e86580000000d2713443462bf4000000000011800550faa000121e0000000e0900000000000000000016c9e0081c0b8800008d40000aba3698000464000000000002c00ef8188850c38e800000003180d18000b750000c26800077200000000000001845400013aa3a40000000000000000009d621c800000000c180000e0800000000f200034200001e4224580002620000d2baac00000000000000015db00ca1b32e830f9b529a40cd0000000000000000000000000000023680002c21b880000000cdf0000000000040c1b5cd1d0b202480000a2800000de8000000000071ea07a4a600001890000633a27000000000000000000000000008facef2c0c0002f5e000000000025363d904d0b5f8000cb700000002698cfba5a498f04042a72bdcdc90c4c6ef1d56000000000021e8000135c5e81af24860ebadd70000d05a59c000000038d10187ca00000000a7cc0184c6000250c0000bb42f2aa1a0000000000053e8370000d4500002d891165ed0e5a6d20eae22ba2221478592ad1000072c0b7a2e58000322b2fa00000005c182b800039080001d4092137683701dfc3c682ce23c80002ab8b1e00017f600002fe00014a0000210c58c80001ca8000af9245c6d52f540000000e2f846816b08485cab0283a080001170e94000246a71218340000000a1cb4ce000000035700000000cd26a7addad0f8b0c000000030a800074f844a1e2adee3fd379c0028000d438df0dd1800000026eabb680005139440000346600009e66bb95cce240000825a5901c824180002fc40000000a00231e000000000030f4000000000037d2000120a9ac279e6eb00000000000850292400031628fb80000000000b8680002ad8000000341000000005a58000cb68010a07235a089312ada000a4b8a000000000008062bdab2b274e9c3852a000000006984bc36e9c3c9c304f892d800043280001200000bdd33d0df18000851b4e20001680000000007d8000000218409e80000001c5200009d0
  | 60 => 0xdc6af8e03280f8000332a1348000174ae400001a0c27a808625001046bd80007c115285b6a83000000000000000000240c77f9328ba3800000e0840e4a80001f10000000145ca41800000026c80002bca953000000007e0000078200010a00002ca8000000063f00006218000000192809f33f2d29ae4a25393ea0f0921a6238f8ad6495e87e490121e3187084e817c68627fc9338786b368000cf800003b091125ee01da2979e36cdc986a39500004e516864e886f000006e61068c0ebde8000a25800082280000001b08000205418b00000000000000000093d000000019ba0cba164c76ae049370000aa089a0acead8c0000c46000000000000008e7325c7ea11e63d4800000000000000000000000000023989be11ca7f49b385cba78e04980000002474c120000000000034035100001eaaa5f23b4282965abd80000b5d8dac1b52fde000000073a80007d323a800014da93200002bd8000000000034228548c400003fc0a2815b000078b80000000b2493b0f2000010b00000000232000000000000002e8689d36900001c9c200800000000001fe0478a52b7deb4ba8f47f7b2a28a32cec52b1e9000000000000a9e00000003419144b718000000388069127480001006000000000006b8b83aa90c9b8fa25d0800000000009208000b039310ba5a964000040257e1a300001fea8af1322b309d6c0188fe02a42cbe94007a20000000000163c9e5b5a200022cc31e000000000005400334000000000021900ba800000028a2067207c6038a7460c29b600024a800019e00002a887c838d0d792f10707b1981dc1f76d1536b00000000b9fa74ac61808c614acb01028472d0a317a20900000d11282a90800000000000000000000000073c80000000000000000052d00000002a7e0100000bfc8000768a93841da1d41e79382216a44619d80008cb0a7eb112106c838210a7219f0dc1b9368a3800042f800000009f60000000a8635b01f4b5c23b90000787000071a000000020fa71e15e00001aae0000f0a9269d2ea038000cec13c864423c60f60c2600031b800000000000000a2c0c4415c285815bb31885a0b2200000000000000000000000000006fe31c85f3266664f10b4674276a72d800047880000000000960800000019b08bfa252e2780007c68000b910000000000057e82aa0af10ea000085c0002298000000097b0000000373e56c1b0626c800099e000082000000000000b9d8eec0002c58000000000007f044c00000000000dbb000000004f40000000000301c79d800097b8cc04f92aac0001192a352ce63120c383630e6a90a800035282443b7a9aa4349446c220370000000000011a23ca8000ba500000000000000319ebf680000000000000000073423547430000d9d1d88d248000a3ea54add38d64cfd88e04c9
  | 61 => 0xa800030bab5400000000199e9e00026e25ac0780000265e000000000000004a78000897989690580000002a5ccff80009de8000000006a08c2242c6893fc00003ba0a5a36a000159e5c980000000000cadb010d4b171069f302cbe2a376225a518db48ca8665a24058123e256800a61c080001a01a280002366dc78000cde00008190000c968000d8404de8f5000031caa6a00012cc75826d000000000000000b7c2eeea108000b9c00003208000000000000000000000fe457003a20001be40002a6c9360000bde25ac86d80002c38000ad306746cc00000002ac20000000aa388b00000000b6d8f424ae8eb0000089a53a000000000000000000cc395e4e1098e0a63b47ecd79b100002a0c000010087e8000346a7cac09a8ea3220000e038000e5700000002a280001f8a15a9f500f1908c000000000024b82ab240214c108243580000000000a26971e67d03faa2133d43c7964cc27abd45ba1f340002f9e7ac16f20a4800000006080001ae610400005328000421800000034dcaee0000bc70000000000000001b246200b0bfa17c6ce78000d34906e00028ec38f0000000152600000002b60f86b4180005c2000000022e8675869600032f68ae15029dbb8b210bb6eecd38000000209e0000528bc69a240000000aca0000a6f8df600037d400a800021cb7f2488b1040000586000210e0001de85418fe613b00008738902e338000000000009c800000000006aa03d20000000000000000005d000038ca48b35fe294928c0d21692000011a83980004761844c2980006640000000000000000000000000b21a4780000000e259bee0a0a4ea0e9b35400010d086a0cb20ec3622cc400002569a4e881acfe0348b2ae061a70a11a4b29b792745eb97148df83eeafa2ec68fe800000023b292d2948aa59f1401e80000000e741b6000000000001b8000000032c25d517b2d27835077580000002108ab3130a938000000000002a53710891052022280000003804b9ba0f2171000000038720000000b9600000002d0c17c800046c0000c82800000013f233a2ae018f8000d5409bccd60a4ad282cbc000000000000008179ace0000f883912cc87648a9a38f8000ba0b59a2e00000c4d80001cd2c424b280000cc00000000d9c01d8b5000027d800011e827588de0001838000345800006cadb1b472c243050a850a76be5800000000004e60accc3e0ab0ddd1f3c000149c000000000020c60b21b2e00000008120aaa1d080000001642dfb1350181028ade5800000000000000000073927a4c4833e9c5342c5a8800068e2c9e0000000a0895d66a51720652343600000007bd000000000000000000b29b31a0000000bd001ae00030acd219ccc000329c000000000000000002ab489b0000a20153c000000005226c4c6b80007c8b26c0001eb4000000
  | 62 => 0xa4c4d00000000000000313e017250a0001eeec6c000053f000000024be000268e0000000000000000026a420a2a84c3015de0000000a7d800000016829b290400931b6e69fb65661d0000262842a993025293f00003e92b903cc957a93f85dc7592bbcca8000037ab84498035764fd0000a07b49a000132c0000d14545b69a40a0000bd2937c1e60000000292e75533eac158728b61322a8f9221a6330fce03895700001f9800000000000ac0d0380000001ece0001ff800006ea54b963e59500006d809c00000000000127e000000000029f2000364400000000000cf800013ec0000000009800000000003ad2ad6512a9325a50000d2223286f500002dc2d6ab0f8000be40ba8000069800038468d09bb6ddc0b4e1110448d7b134c9cfa0b410602840001bc6cbf8000309129600000000002e06144a1ea45900000000000a548daad6f80002901242000218000000000001f883289938add352803925640000ef000000005fb8000000084eaa6800032980007e0a862786376600000000001a5c3cf80000002e8c7600c540001232515276c00029bc5bd97869cb29fea60a65416a232e71080001c51c44848373ada4aebc6d6829c1a683740000aa4000000000000001620d9e73f80000000a12000000035803a0ac4309ca640000cad08f8d69ad6e8c88000a0c80000000000c909970000000000000008d480003de00000000ee000026c000018621a42d14550000098089dc48180008bd139200020e268731ce0002d2496c089213914f0119023c23c1a0e0888000c7412bcab7894a9d7374c20c907819681aa34d1314cc30e76000101c00020ec00000000000b2e4113938071000081d800050d0b606672a5400009807770c52000357000029b2bd70dbea43b62e0000000000000000026aa0000fec0001d2000005dee319992d2da7827d98000000390400003c010700000000000d2f0d8e8c5075eb0480006f4209c000041244786643d7899e4e1b7185c280000002a2000026260002e660000000c0512447e780000000000a00ac8e8d82c1c70f8000000000000037e400022000002c88ab2215c5d580000001666cc93924000000000002ca0002090854314000007de00007cadba9c9abd4a5c6a68034e8a9165e027ab3c3c61eac3fb8abe2a61340c0f000000006a8db131fa92c08e20df051a4740952669b8fc71f2eca0428d2ed2639262a81c7eb4ea6509e40000da990ae7c903f4000219a9bdb04c00025a00000000740800000000004d980000002a12079000000000000000000113000000000007d492140002d9000000001be800000017f40001a26000000000001a4c4a1e820002d268d3290a1670000d8aabba00000001ea36b46040a82000000053a800088a188a5e28000ab10000000000000011ae0000000000203600034aa38
  | 63 => 0x396ec000359499628100000bee4aca1ccdd400002f082f20001374846004a000000000000006b500000002038000181241888780b90000000155400000000000000c800000a6680000000000000000096f00008b91f26b8c1644000308ad238000000165869200000001cbace7377eab8854ed8ca11200029dac380000000269a22a00007a9800000000000ba15fec3fb6ca1db8000452000006200001678000000316449d8a3238880004bc00004ba229cb3d2c36000055892a8000da11f78c151c8805d1f2ccc1804ec05abec00030d60000000136800000008a00000000c452d0a957051483690c6000181cabb2c2879a88808bf35201f733da0002f340000158c958f7c876b7d831d179eaa8800000006fe7d20fbac4ca5f60000000c209cbe9a500000000000d000000b6a0000c6d27e2000043054e0bbe4f10000b7388428e49abc5c8800004b109c00000000ac00008f1000000003620002c480000000cb00d040000c6c000000089d8a8800000007c597d41a2800000032b808d23ae9830ee2000000000000000e38c0200017f25cf9c36000197859a8f04d62104200005d80000000000000068d10a8572920e000000000000002af00f0c98b0220001a60132ab7ad358000ac227188d91964679800000014be778000000003ca71b21f400000007cc800000000003d2800098100004dc800000000000000000966a5344739bfe00000000002f70a3d8eee3d8a4069b480000f88ed4230000000000002311c2600007d400009aa65ea4aca4f0d1647c0000c23009aa94000017236fce2d96e2000132a00000000002b207568000d78219c00000000000c5a7ac97580da94440000000c53a1be608031eb97ac100000000b1c2390000000000000000000000000344600000000002e92000000016000003d700003adb43c1ba2fc0a58ad8a0000f0642936d600025609bb98a488e1bb81371eca3c5386c000000048a000000000000002dea0002f480001cdc000000014d9534000000000000000000000d2100001902d7a29980001d91c1c45e3702c478c0c0010fd43690000000000009d000000000000000d0256480000000000000229000000000000000d6780000002c403bd8b9cabca4100782d5613a30f2bf329126b220d400023161bb16d45a3a24e20e0f76c34b652000237a0002ffc50f1c76d4c000040021167d68000df107841b20000000000000000000000000af100009b6395e2b98000246301200024ba22d0000d5900000002bfc0000e8e0000a8e1800000d9c985c749094cc5d073a1c00ffe00002080002d08ae080000000000000000000000000000c680000e1484b8ec800004822c1190274a8000b94a5fc0000000cb925e40000d7c568847644d85cc0000bf440ea03000026245d6931ec063086b5f2b7827ba2ae00019
  | 64 => 0xd8d2ed000020b6b3400002f131960001a1200000000002e9e00018c0000000020d0000b8f2568000232400000000000000000283a64b80000000c669b1a7b88288c941339bd212a126e0002dca0000e7067b23d20002aa0d311d9cc4213960d51aac83a80000002bde6ba80000000000000000000000000002cca00018eed770022cac877e4399b76a0b0aa256f9b8eda384d400000000000000389000069415ea000000000024a472198a89438000cd92e568001fa20718000000000086b00000d280000002f307f0a1e4cfb0000261a9de000000000000000002fd000033ae0000b6800000000001dc49762b7c0000000000331c09c36e00338b5c75a80000000000a5e216e0000000a8fa7ea660800000000003f20862aa7800084500000000000000000000000be0000000dd116400002bfe00000000002dec723000085e800000028560000000000112e00000000003954000000000020f80000000000000000000000000000b3c82c6000000040f800000000000000510b720562c2a22581422fb469d38f0e55ae4c49b269e00018b83c9151ca122fa400009003e30deedd08000000267c000156a0529868000191c2919c6400039300000000000249000020280000f480000000e48a1f6011272e09f8000b19170ca89160ecf1ae600001e50000000000000002081a5e067acb87048c6400017a25cf13da5ea274497c27a000000004af96ac0af80000001320ba20e9207288a60000870000000000000001c60000000000000000009e2a9ea53fac2ac5ab0e2ca90836ca3167200013ee8c307c000000000000000000000069a000000023b00608732000161000022e007c0000000380c2b78000a9a0bb000000000002d488ad80004e800000000b42ca58fcc280060ae5380000000000cf2800029a000000021583770b940ee17eabf9b81603fb8c21d520bc0002130e2eb91a96d043e00000000000000b5b138057480002e0ac8c000000068200007cc0000360393a00000000000b346da22660001520b63b3f8cce25580000000000000000000000000000000000000038584960000000000086c0b849c70fb6df880000002b660000000000000000000005351bf21a18000e0c2212d79800000001d60001140e0b00000ab0000000000000000004f5258a4f280001cc0fa02c28e64822000000000000000000000206840b8000000090400008fe000000095999d400000003db800008b800000000000001a3c0002c0000000007e380000000000bbf000080d0000baa22a686936aaba9a5a21a8ac6c000028ce12a874c0f86ba000003c8f20000c3c0000c3ea1b852307a00002434000000000000008078000000350a68b000000000007d18edc7b5a46097c80000002a2e0000000000018e05400000002ace9ae930800021ca5f42ba29
  | 65 => 0x87191f6cc894c60000000c190452b4e2388190b910a9608d0632230e81d054200000000000cd6000000093296ae999274200000b60000db6df7233053788ba00000002c600001ed00005030000000000068124a0058b452646000086580000002c38000125c000000046e0000d6400000000000000353c00000000000e98b1fb02a5808212000000000004fc0000000000069200000007ce27946203078d6a0500b9b085662b02ae0000dfec52800000000000000000b7d800000037f4497887e00015ae7fc922400000000002574c582f2400000009f423d0910a33eb938000000000000000006079e2a0001a8c782b7d6df280003d000006f0800062d119c0bf09b0d8980006cf80000001762000000082a000010e800000000000000b788409c0ae0f2808201800000000007f689320000fc00000000000184e4c71f3a143b0a45f200000c490fa1218f50000286e0001fb269a9fc80000cc4000230439eb80026894f800033dea2c8fc43522c5c06688c6406ab9a6faa382000071cb148000000021e64b00002ee2e2cbfe8fb019580000000000c510000000000000023ec00031720000000403b934000000000020920a980000000000bc1977a000341a0002a8ae1f004c000000022d857e0000000d3ea3ba186937a9ab0d3231c082698a8736d2595ee63f8ff26581234b1780000000000d360d0e00000003268000a18000000011d23272580000155e0002636c139466a82000000000005588000000000000000001c89dc006b012e1f61ca6e5aa778c1f800044f0000e4b8000c3a1f5497f8000d92800000000000000000ce40794000000007b1906000000000000000002d60e148000b98800000029709dfa4968db02020000f9238490ba00000007b0a22000000000000000662aab6c8f02761d300000002f9a29e0000b8c8a20427b180000000000000007b1000012780000000cfa59416888b51c9e32f80000002368000000002b1e1ae228000a368000e58b4ba28b85b439c8000000000000035b86568bd417fa362c0101944770934935800000021762039c828bc8000000000000000000001594863065e9088000d170ca4317a6e845ab8e00002fb0a260000abe9baa00000001fe92928b1109a9071c46d8800007b9b52a28c00007db80000002d34cf735d6d9d800042a88180001ac400032288788180022b3526e0a0ae3e01f184eea9fa00019228f724f8abc0000000039e1818128000000000019f20001a9a5a111608340000b46000070a00005539e947d61d220000eca0002c020000000d0132c40000000a2f00000000000774000056b000075c99d8000126a0000000e292b9e0000000e1311c206ea73c68d8000bfc00000001e5400000000000000a92a532183b32060fa0e41bc975ec62821c3e58d26228b2224f7000064a8
  | 66 => 0x5bccb791520000000000000000000000000678a2da8186a49d620a9000035e0000000387466b0b4489c8000ca7800000018a6a09166c32d80004131f800002da07892e2000000000001a220002a3c0000032000000009380003f60000a11293a0001b8000007be8112d286491388a13000042880003549bb0000162200027bad25000000034b26e18000000000000019fc0000000000000086797ca1ff88e8e4f8000d1d800091584e07140000df8212a000000066cb1f60001f4aa48343400005e2d983562bab2ab82048000dac80000000000c9c0000594b59832b13cc000032aa9ea2f600003660002d680000000dc88000d328000c6a800049538762988000443344c8b5b51c0001ca2000348adae00000001bfa816800099f800000000000000000000086a000087ac3128f049999460003408000346401e00000f926fcbf600000bb05327f518560001294e1884d85a60000a7c00000000336000295400000000001e4000000000000000db200000000000002000000023c20002ad40000000239288a8fd80000002a5a1df0000d8206a67ea96b270a858e000184876d8dda00017ecaf40c1600000000000000913adde4b480002930000000000034825fa00000a80000000000000075ba6a800000005db800000037ea76296b4d5127c2b3807607b88000000000000000000000000418000030f12f800036940000b5200000008c82c240961ba4d8b08d6316000075e80000000000000010c00000002c1800000000000001c5a46d00004ce1c3800000007fb130220400002470000c66a7bc000000086aa0568980000d00950e438000000000000001f06d290938006ab2c9c180007af0000c372c7a0002bc800027a2000332c1330000000000000000006d012e4c32adb05f4a57c00009e20002a804dba6da000001205d800000022b000004b84a1000000000002b590b66dd00000300d4c000359c333b032bb2000028190f651f1d1a61ca436c083068c2db7c02649790df6afe22418dd4e0c890e141276076e341e554908069e00000511908c9100003c20dcec7f9a3200000001eaaf3256100000001b0a9b900000000000000096c00003786b59bbed6ca7380000000000000000018920002424ce60e163b593c09ab89284be840cbfb2c980942e1e0001ab44331846ced14d2a330496a5b8d9a000242e000211e000394c48800005081ffe8ef800000032aa000000000000000001e5ca199cca000000000037fe4198a6aa390ada00029b809b19b47a911628a2a0084a008ec70399526790cccde08bccacd9e8eaa9847456321008c9b60aabfaf5027b3250c7533660001956b4c05ba8cf2f44b2827100000000000382000014bad5d0000bba96a4791974ee2d0000cceb9480002d4c000085451da0e8d5f0d823eb8000308aeecb891b6c
  | 67 => 0x158871313e2e08987cdb5238657d0962d5300009000000011b6129c9b840248800000000000001e2c0000000000000000000004fa000000000000000ea00000000000000000028c0d0a80000000000000195c8f811980003480000000019338e40000000db9074a48c105499a950c0000dde8a5a2842cd8000077a588825021a000000000025cc000163a000361e00000000000000b1996aaac3954a1f38000dc480000001484c41aedc0142542a800d6e2ff351a31f00005ef1b720000694556218e73c14ae0000000000000035780000001854be1a21e3e080007cf8000b28887400000003ac8cb0dc519260000000a3a1a8200000004a80000e009ab6c02000029e8c2011980000001958d7d000000000006ca81924c632340a1800059893488e50000000000000029c63cf2a700000000000000000011de00027a69a580004b60000c85a4c630a
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bc845d953440011df04bb2a68800a3b2097654d1004c3e43acaa9a204ea6c8259553440091bd0fb1aa6880063d2197190d1002c7c432e121a200487e859d943440010fb0b3b2868800237e0d7650d1004c5e43ac8a1a2009a9c8359143440011bf06ba6c4880263720d74d891000477c12eca92200287c8759552440090fd0b3b284880021f61676509100043fc2aeca12200487c855d942440011bf06bb284880263720d76509100145e43ac8a122074a9c8359142440071dd0fb1284880031b1d762509100146f41ced99220018f4865c7324400b1f10cb8664880023de05764c9100243f428ec992200087d851d9324400717d083b264880022f610764c9100146e43ac699220098ec87589324406b5c904b2c82880d63d219729051019d1f42ec8a0a2003ab684d9541440071e90eb2a82882f78d151655051019572412caa0a2056b3685d9141440033e101b9a8288003748c373505100074ba1ec6a0a20038f48758d41440033e101b92828815acd21542505101975231284a0a20019f287dc141440033e100ba46288026b520d648c51000c7a432e898a20019f0805d131440131e90eb226288002f1608634c510005e8c066498a2002ae48259621440033e100ba442880063ea1b70485100147a43aca90a20018f4865d121440033e100ba242880063d219734851004c7c43ac89822000b998418d30440017930431a6088002f4606434c1100074cb22869822000bd181cc930440015b10c9926088002ec610714c110005f0c10e29822000bd18390530440013e10ea0a6088003e450d414c11002e6c3b6629822005cf0768c5304404b7a30718a60880067621d314c11002e6c3b2629822005dd0714c530440035e10c98a60880173c1d9314c11004f6831a629822001bd0874c5304400bba10e98a6088006f4a19314c11000de8432629822009ed0864c53044013da6ec98a6088017749d9314c11002ee83b2629822009ed0764c530440017a70898a6088002f4611314c11000769b22629822000ed1644c530440017a70498a608800374dc9314c110005e8c1c429822000bd1834853044001f826490a608800a3e21d654811002c7c432e69022002ce87650920440017630838a4088002f460c714811002e783b4829022000be18290520440013e10ea0a40880173c1d94148110007d0a12829022000be1828c52044001ba2e698a4088003f04c9314811000cf443a429022005ce876485204400bbc0e290a4088006f821d214811002ef043a429022001be28648520440037c10c90a408800bb8219214811001771bb2429022005de276485204400bbc0ec90a408800bb81d9214811000771b2a429022000ee16548520440017c70890a4088002f86112148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x706a12a090003ca90d42541203079421a84a824000b6b8150950480c1e5682a12a090002daa1d3254120005b443a64a824001b6a864c950480036d10c992a0900ff9add932541200bf343b264a824000b6b844c950480016d308992a0900039ad91325412000734b2264a824063b6b834c9504802fe9706992a090003d29cd3254120007a4b9a64a824000f4b634c95048001e90c6992a0902ffd2d0d32541205ffa421a64a824000b6b814c9504802f6d105b8aa0900035adcb71541200bd3d434e2a824000a79869c550480c16750938aa090002ce61271541200bdb5414e2a824000b69829c550480014f70cb8aa09005e9e2197154120005b5c12e2a824017b68825c55048001ad6e4b8aa09005edaa087154120005b4c10e2a82401bb6982985504803d6d704b0aa0900025ea1c61541200bcbcc38c2a824060b3a8418550480016730830aa090002d6a0c6154120005acc18c2a824000e716118550480012f50f20aa0900025e61e41541200bdb541482a824000b69829055048101ec64320aa0900038e59141541200bdb541282a824000f294250550480ffec642a0aa09005edaa0b3154120005b4c1662a824000f4932cc5504802f6d50518aa090002da60a31541200053dc3262a824000a78864c5504802f6d50498aa090003d24c93154120004bd43862a824000979870c550480014f50c18aa0900029e61831541203059d42062a824000b39840c5504802f6d50418aa090002da6083154120005b543a42a824000b688748550480036d50c90aa090006da2192154120005b5c2242a824000b698448550480016d70690aa090002da60d21541202c5b5c0a42a824017f63814855048001ec4e290aa090003d85c52154120007b1b0a42a824000f6061485504800b0fd0f2a2cb880162fa1f545931001c7ac0ee4b26200587c8759553c40031ed03bb287880162f21d6450f1004d4e41ac8a1e200587c8759552c40071db05bb285880063da077650b100043fc2aeca16200487c855d942c400b1790eb2285880030f1d56450b1000c7b40eec99620058dc8758d32c400b1d90eb1265882fb8d15165507101947ac36e4a0e205db348550941c40bfd48c4a1283880023de19734871057e36394a8b2a20028ee87dc965440018dea1b92ca880031b54372595100053cc04ebb22200487f875d7644411f0ff00baec88816a1f60175d911002c7a40ae5b2220098de87dcd64440018bea1b9ac8880031754373591100043ec2cecaa220008df835d954440131b906bb2a8880023be09765511001476412ecaa220008ef825d763440051d904baec6880029761443d8d100056ac0887b1a2000ad98010f63440011bf0eb18c6880273398d7218d1000666b1ae431a20098dc835da53440031e90cb8ca6880163e2197094d100045fc22eca9a2003
  | 2 => 0x3635092001c7643ac6a12405fae48158d424800535d0f21a849000a7360f744c92000c76432e89924009ace83d9132480131d90eb2264900fe9b215644c92000567434a6992403fe4c6554d3248001bc421b8a64900021fe1574d85200243e42ae9b0a40008f78758461480031d90cb94a2900163e219709452002c3e43acaa8a40058f4815da41480031d90cb9482900163e219709052002e7830ae120a40058bc8759141480674790ab22829017fa9185425052001c7b43ec2a0a40058de839db314800b5a902b1e62900063b21972cc52000762996c398a40018ec865ca314800b1f10cb8462900163721d634c52002c76414ec18a40018f8809d8314800b1e902bb062900172d185740c52000c76432e418a4000cb574d8431480019cae5b0862900163e219700c52000679b0ae018a4005cf0615c031480031d90cba242900063b219734852002c7643ac690a4000b658518521480017c30128a42900129ea1764541200247c43ac8a824017b6a8294d50480016d30529aa0900131e1d95354120307952a284a824000f295450950480059d0ec992a090003d294d3254120007a4a9a64a82400197a8794550480c16750928aa090002ce61251541200bdb5414a2a824000b69829455048001ec4a290aa090003d854521541200bdb4416e8a824000a7b865d1504802f4f10cba2a090002dae0974541200bdb4412e8a8240c0e3a64d9150481874f50fb22a09022e9e21f645412021d3cc26c8a824001a7b82d9150480034f305b22a09030b8ed0b64541206171ca16c8a8240c2e6a32d9150480012f70eb22a09003a5e21d645412032db5c12c8a824000c7b8759150480094f50eb22a0900129e21d64541200063c43ac8a8240048788759150480cd4f708b22a0900038ee11645412032d3dc12c8a824000e6b825915048183cd464b22a0903038ed0564541204563c3b6e6a824017b6882dcd504802f4f50d39aa0900029e61a73541200bdb5414e6a824000b69829cd50480014f70cb9aa09005e9e219735412008e3c3b2e6a824000b3b845cd50480c167108b9aa090002dae0973541200bdb4412e6a824017b6a821cd50480016d30439aa09003a5ea1e6354120004bcc3cc6a82403db698298d50480816d704b1aa090002dce056354120005b840ac6a824000e596318d504802f6d50521aa090002da60a43541200bdb541286a824087b6a87dc9504802fad50fb92a090006daa1b725412000db4436e4a824017d6a76dc9504802fad0edb92a090002da6137254120005b4c1ee4a824000b6981dc95048001ad70ea12a090002daa1d4254120005b443a84a824000d688750950480036d50ca12a090006da2194254120335b5c2284a824017f2b8450950480c1e54e8a12a090003ca5d1425412000795b2284a824060f286450950480016d
  | 3 => 0x4a166000c6c7558942cc18bc98a4b2a65980fa3761b744cb30395a642a849966074e8c6450932cc0031bd07bb28398027271d9435073004c7a43ac2a0e60008df865d131cc0031bd07bb2439800e2fa1f74595300061fa86e8b2a6000c3d50dd1654c165878e9292ca980030f5d754d91300047bc0ae5b2260058f4815cb644c00117f08bb2a89800e1f21d655513001d4e422cb21a60019d8805ca434c0071b90eb2a86980029e60275d89300243fc3aebb12609087f805d7624c0e10fb00baec49800a3720d74d89300043ec2ceca92600487e859d9424c0010fb0b3b2849800a2fa1f64509300061e3aec8a126041a9c84597324c0831b90cba664980fe9ba17624c93001567416ca99260028dc87595324c07d53908b2a649831393149654c93000cec406e899260018dc865d1324c0033b100ba264981b2d3a17624c930365a642a84992603ee8c64509324c0033b101b8a649800374843714c93000ced43ee099260008bf845d7614c00717908baec298003b14cb21d85300053ac2843b0a6000ad583087614c0015e30010ec2980172d98574185300047bc3ac230a6000cb574584614c00b1e902bb4a29800637219739453002c3e43acaa8a6039a3c84595514c0091ed0fb0aa2980163da06769053000c6e432e720a600487e851d9414c0010fb0a3b2829800a3ba08765053000476c10eca0a60058bc87591414c001938eca1a82980067620172cc53000c6e432e898a6000b9584185314c0017a30120a62980063721973885300243f42cec90a600087d859d9214c0031b90cb9a429800676201734853001c7c43acaa026000bc9821cd404c0017a30239a80980066e21d435013004e5c3b286a026009d987350d404c0037310ea1a80980276621d435013000dcd43286a026001b988650d404c007d310ca1a809800fa6dd9435013004ecd3b286a026009d987650d404c007d30eca1a8098003a6d9543501300074cb2a86a026000b9b8250d404c00173702a1a809800f2e1d9425013004e6c3b664a026000b9984cc9404c0013b10e9928098027361d93250130005ccc2264a026000f89424c9404c001b3287b8a8098002e66133150130005ccc2262a026000f91414c5404c00187ae92a6ca900029b60a54d952001476412e3b22400487e87dd564480010ff01baac8900021f60375591200043fc2aecaa24000c7750dc563480018eaa1b8ac69000237e1d6318d2001476414ed29a40018ec865ca534800117f08bb2a69000e2f2117654d200047bc0aeca9a40058f4815d953480130fd0fb2aa6900023de057690d2002c7a40aed21a40018ec865ca43480010ff0abb286900121f2157650d200047bc0aeca1a40058f4815d943481658d8edbaa84902bb1b1d87550920005b4c00eaa124000e2e54d9542480071d90eb2a849000eaba1
  | 4 => 0x500ed6d50539aa0a0002da60a73541400053dc32e6a828018a78865cd505000167708b9aa0a0062ce21173541400069dba2e6a828018b3a841cd50500016730839aa0a011ece61263541402559dc22c6a82800097a8718d50500312f30e31aa0a00039658c63541403b5b5410c6a828000b698218d50500016e50231aa0a0002dc60463541400059d43a86a828000b388750d50500036750ca1aa0a0006ce219435414037d9dc1a86a828018f1b8350d5050001e34e6a1aa0a0003c65cd43541400078db1a86a828000f186350d505000167704a1aa0a0002cee0543541400c59c426e4a828000a7b865c950500314f10cb92a0a0002cee1172541400c59c422e4a8280c8a7a87d89505010d4f10fb12a0a00069e613625414060f35216c4a8280c7e6942d89505018fc7683b12a0a00025ee1d62541400b4bc43ac4a828066b3b845895050001a770ea12a0a0002cea1d42541400059c43a84a828000d388750950500036750ca12a0a0006ce21942541400059dc1a84a828065b3b825095050031e5704a12a0a01dbca9c9425414000794b9284a828000f2b6250950500ede50c4a12a0a01dbca8c942541400059dc0a84a828076f282150950500012f50f992a0a00025e61f32541400c59d42664a828000b3984cc9505010be3687992a0a0062cea1132541400059cc2264a828084f1b434c95050001e5284992a0a020f1e1db71541400c59c426e2a828018a7a869c550500014f30d38aa0a0062cea1271541400059cc24e2a828000a7b865c550500314f10cb8aa0a00231e1d971541400059dc22e2a828018b38845c550500016d704b8aa0a01dada20971541400c59d420e2a828000b39841c5505002d2f50f30aa0a00025e61e615414018d9cc24c2a828034b3b8458550500016b706b0aa0a0002d620d615414000738b08c2a828000b3a8750550500016710ea0aa0a0006cea19415414000d9c43282a828033e3b765055050031c70eca0aa0a0002cee0d41541400059dc1282a828000e3b6250550500b367702a0aa0a0063cce0541541400079938a82a828000f31715055050001e66c2a0aa0a0003cc18541541406379990a82a8280c6f302150550500316750998aa0a0002ce61331541400c59d42462a828000b39848c55050001e628318aa0a00029ee1931541400053c43262a828018b3a844c550500016730898aa0a0003cc5053154140004bd43862a828000979870c550500014f50c18aa0a00029e61831541400c59d42062a828000b39840c550500ed6d50418aa0a0002da60831541400c59d42442a828000b39848855050001e528510aa0a0062cea1121541400059cc2242a82800987c8759554cc0051bb07ba2c5980263ba1f5258b300145ec26eca1660018de83dd942cc0010ff0abb285980121f2157650b3004c7643ac
  | 5 => 0x80031ee02760c5500243ec04ec18aa05ac78809d831540018f4813b062a80031e882760c550004bdc02ec18aa000c7b605d8315411f0ff00bb062a80031ee01760c5500063d202ec18aa000c7a205d831540032f500ba062a80034e901740c5502d69b18ae818aa070d35315d03154001a7500ba062a80034e601740c55047e1fb02e818aa000d3b605d03154001a7440ba062a80065ea01720c550006b5102e418aa05ad4f315c831540b5a9a62b9062a80035aa01720c550006b4c02e418aa08fc6f605c83154001ad6c0b9062a80035a901720c550024bd432e018aa08fc7a865c031540b58f30cb8062a80125e219700c550004bdc22e018aa00097b825c031540b5ab662b8062a816b5c8c5700c5502d6ac98ae018aa070d71315c031540b52ed033b442a80025ee017688550004bdc02e710aa001978805ce21540312df0ea1442a80029b21942885500bdb2412c310aa000e676258621540016e700b0c42a80025e6037648550004bdc02ec90aa00087f865d121540010f90cba242a80025ee01734855000cbc402e690aa05a96c874c921540016e30130a42a805e5d21d6148550005b9c02c290aa000a3d8494b65500010ff0ab96c6a00121f21572d8d400046fc3ac631a80018bc865d253500131f10cb84a6a00261f21d6554d400058ec28c6a1a8000b998094d435000517908b9ec4a02bf0f1db755094056e1e3b0eaa128000b39801d54250001c5ca5b2a84a000a2f21d65509400146e41aed99280018bc865d332500131f10cb8664a00273618d70cc94000c5e432e899280028de87d8d32500e9d18c6a1264a000b2b9c942d85400047bc3ac230a80058bc849da51500031790cba4a2a0003668c3735054001cdac0ee4a0a8005ab681d89415000156d0d28a82a00cf8d195515054000c5e432e998a80098f8865c3315000b1ed033b462a00062f219748c5400074bb1a8318a80018bc865d1315000b179093b062a00062f219740c5400064eba6c618a8000ccf635c83150013998c6b9062a00163e219700c5400066db1ae018a8009cd8635c031500011bf06bb442a00263720d768854000c5e432e910a80039af8750a21500031790cba242a00065ea1e53541400c59d424a6a828000b398494d50500ed6d50529aa0a0002da60a53541400078d29a86a828000f195350d50500094f50bb12a0a01dbca949425414000794a9284a828018b3a8494550500016730928aa0a00131e1d9515414001e5c3b282a828000f32515055050001e62a2a0aa0a0232cea1f74541400c69d43ee8a828001b3a86dd150500036710dba2a0a00634e9db74541400c69c3b6e8a828000b3983dd1505000167305ba2a0a0002ce60774541400c59c426e6a828000d3b74dcd50500314f50d39aa0a00029e61a73541400c59d424e6a828000b39849cd5
  | 6 => 0x2d8e422c7992a000b5b8058f32540012f700b8e64a80065e20171cc950004bcc06ec992a00093f845d9325403127908bb264a80025de05764c9502d4ba40aec992a00097b805d9325402f2bb07ba264a80021fe19744c9500043e432e8992a017b4e8298d32540016b30131a64a805e5721d634c9504258e422c6992a000e4c6258d32540016b700b1a64a81c25ba1f624c950384b643a84992a000a6c865093254109e1886a1264a816a1f61c64d85500052ec18c9b0aa000a6d8219361540b54ed02326c2a816a1f61f63d85500051e422c7b0aa05a87d87d8b6154001a7500ba4c2a80034e601749855047e1fb02e930aa000d3b605d26154001a7440ba4c2a80025ee117098550004bdc12e130aa000d73615c261540b5ae0c2b84c2a816b5c90570985502d6b910ae130aa00197880dd161540018d8e5322c2a80029760c645855000536c10c8b0aa000c6c7219161540b54ed02322c2a80031b1cb63585502d43e43ac6b0aa000a3c8458d61540018d8e4b1ac2a80065e20372585500bcb743ee4b0aa000d6b80dc96154001ad101b92c2a80035ad837258550006b5206e4b0aa017c6c72d8961540b50f90eb12c2a80035adcb7058550006b4396e0b0aa00197a86dc161540032f10db82c2a80025e6137058550004bcc16e0b0aa000d7361dc161540292f700b98c2a80025de1d6118550005b9c02c230aa05a976819da41540b58ed033b482a816b0fd0676905502d61ea0ced20aa00487f809da41540090fb013b482a80031e90276905500063ca04ed20aa000c7a209da41540b58ee213b482a80031d4427690550004bdc02ed20aa000c7b805da41540018f480bb482a80031e8817690550004bdc02e720aa001978805ce41540b52e902b9482a80031d9d96190550405b2412c320aa000b738058641540012f301bb282a800257e0d7650550384ae41aeca0aa00096f825d9415402f2d904bb282a80025ee0176505502d49f43ec8a0aa05a93c8750d41540e1a38e6a1a82a80625d60772505502d49e43a84a0aa000a3c8650941540ffe4842a1282a8062cda126150550005b8c04c2a0aa018974875854154001c68c8b0a82a81fed92096150550005b9c02c2a0aa00093f845db315403127908bb662a80025ee0176cc550004b7c12ed18aa01796c825da31540012f700bb462a80025e603764c5500049fc22ec98aa01893c845d931540012df04bb262a805e5b209764c550004bdc02ec98aa00197880dd131540012f700ba262a80065e201744c55000cbc406e498aa05a95c874c931540e12e90ea0a62a80065ea1f704c550024bd436e098aa00497886dc131540012f309b8262a80025e60b704c550006ad996e098aa000d5932dc13154001ae483b8262a80035c507704c55000cbc404ec18aa000c7b609d831540090ff013b062a
  | 7 => 0x78805cf645411b2f700b96c8a80065e20172d9150004b7c12e3b22a01796c825c764540192f700b8ec8a80065e20171d9150024bdc26e0b22a00497984dc16454001a76c9b82c8a832b4e1937059150004bcc16e0b22a0cad3b42dc164540e10fb0fb26c6a81c21f61c62d8d500051ec20c5b1aa000a758118b6354001ad500b94c6a80035a6017298d5048637b02e531aa000d6b605ca6354001ad480b94c6a80025ee117098d50006adb1ae131aa070d58635c263540e1ab486b84c6a80025ee097098d50386ad992e131aa01893e87dd16354001a7701ba2c6a80034e2037458d500069db06e8b1aa000d3a20dd16354031878e9b22c6a81c21f21d6458d500061e3a4c4b1aa000a3d841896354001878e8312c6a81c297a0c6258d500053ac08c4b1aa000d3b74dc16354001a70e9b82c6a80025e6137058d50006adb1ee0b1aa00097982dc163540012bf0eb18c6a8002d6e016318d50064bdc02e231aa07095e839da43540012f700bb486a80030f5db6490d500c58e422c721aa000e1f6458e43540016b700b1c86a80025ee017190d5000cbc402e321aa00097980dd943540012f700bb286a8002d66026350d500c4ae43ac6a1aa000b5b8058d435411d2f700ba6c4a80065e20174d89500049fc22e7b12a01893c845cf62540292f700b9ec4a80065e20173d8950064bdc02e3b12a001978805c762540012f309b82c4a80125ee0b7058950024bcc16e0b12a000d6b62dc16254193ad0c5b82c4a83275a90b7058950004bcc06eca12a000c7a70dd942540018f301bb284a80031e90376509500063d106eca12a00087e869d942540012f700bb284a81c257a0c7650950004aec18eca12a05a976811d942540012eb023b284a80030fa1076509500061ec20eca12a000c5e831d942540018bb063b284a80030f10c765095000637410eca12a000c6d821d942540018dc643b284a80031da0476509500063ac08eca12a000c3f411d942540018d8423b284a80121fe0076509500063d400eca12a00487d801d942540018f3003b284a80030fd0076509500063d200eca12a000c3d401d942540018f2803b284a80031bc8076509500063d100eca12a000c6d201d942540018f2403b284a805e4f21d64509500059dc02c8a12a00197a80dcd42540012f301b9a84a805e4fa1e43509500061e3b486a12a01896c8758942540016d700b1284a80065ea037150950004bcc06e2a12a044a78865c142540018f0ecb8284a805e57a0e76cc9503862f41ced992a070c6e329db32540e18da653b664a80121fe0276cc9500243ec04ed992a000c7a409db32540e18be613b664a8003174c276cc9500063d104ed992a000c79209db32540012f700bb664a80031ee0176cc9500063d202ed992a000c7a205db325402f2b906ba664a8003179d963cc9504
  | 8 => 0xaba6c0908030fd037650b500061ea06eca16a000c6f20dd942d40018da41bb285a80664fa1e4350b504862f982ed996a000c5d305db32d40332b906ba665a80665760f744cb500043fc32e8996a00487c865d132d41212d90ea1265a80fe9b219424cb5049f8621a84996a08fc77105da41d40018ea20bb483a823e5d20572907504868e39a86a0ea01a97581dc941d411f2790ea1283a80ce8f219425075048f9210a84a0ea08f95c874c931d41212e90ea0a63a823f1ea01760c7500063cc02ec18ea090d1e635d031d4001a3ac6ba063a823f4d985740c7500069ab0ae818ea08fd36315d031d4121a6a62ba063a82435398d720c750006a6b1ae418ea08fd66615c831d4001acac2b9063a823f53cc5720c75047ea698ae418ea08f97b865c031d4121ab4c6b8063a80035658d700c75047eb930ae018ea000d71615c031d411fab662b8063a823f5c8c5700c75047eac98ae018ea090d71315c031d40352df0ea1443a80021fe1974487500243e432e890ea0008ef825c764540051d904b8ec8a800237e1d6318d50006b5102e529aa000d6a805ca5354001ad300b94a6a82431bd817294d501feb5b02e529aa000d6a405ca5354001a7481ba2a6a80630f1d36454d5000c3ec2ced21aa0098de839da43540030f90cbac86a80030f5d76490d500070fb22a721aa00187e86dd543540030f90cbaa86a80125721d5350d500045fc22e7b12a0038bc845cf62540090f90a3b284a80030f950765095004c6f418eca12a0008dd831d942540018dca43b284a80163da0476509500047ac08eca12a00187e86dd542540032f501baa84a80061f21975509500249e43aa8a12a00496c8754942540030fb0b3b664a80261f21676cc9500146f41ced992a00187c865d732540018bceca9e64a80061fa1b754c950384b6c16ea992a00187c865d5325402f69d0529a64a80125721d534c95027726312a6992a0008f7875846154001a7480ba4a2a80034ea0174945500069cc02e928aa08fc3f605d25154067a76c0ba4a2a80034e8817494550006b5106e4a8aa017c6c72d8951540030fb0b3b482a80161f216769055002c7b40ced20aa00187c865d641540018ececa8c82a80061fa1b75505502d49ec26eaa0aa00187c865d5415403166d0928a82a80125d21d51505501cf1a322a2a0aa00187d859db315400117f08bb662a800e2f21176cc55000c3e432eb98aa00187d859da31540011df04bb462a800a3b209768c55000c3e432eb18aa00187e86dd531540030f90cbaa62a80065e201754c5500247d436e098aa00187d859d8315400b0f90b3b062a80061f219750c55002c7c432e018aa00187d859da215400b1ed033b442a80061f219758855000733b12a310aa00187e86dd521540030f90cbaa42a80125d21d51485500a4bdc02e7b22a0019
  | 9 => 0x76508310043ec36eaa1062b2c3e64dd5420c55f8dcc5baa84188031e98375508310043f43acaa10620087c87595420c40b1790eb2284188030fdd564508310061e3aac8a1062058ec87589420c4018deeab1284188031b1d562508312d53cc04eab00628fa7b805d5600c4090fd0bba2c0188021f61774580310243f42ee4b00620087d85dc9600c4135b507a82c018816bca07505803104d6d41ceab006200ad9839d5600c40b5e5033aac018802bc60675580314872d41ceab006200e59839d5600c51fce5033aac0188039c606755803147f2d98ceab00628fe72319d5600c51fcb2633aac018a439c4c675580310063dc3aeab00625ae5b315d5600c4b5ce462baac01896b964c575580313873898aeab006200a7a85dd1600c4014f30bba2c0188031e5d774580310063cbaae8b006209ad8835d1600c4014f50a3a2c0188029e614745803104d6d418e8b006221ad9831d1600c4015d5043a2c018802ba608745803102d79408e8b006221af1811d1600c4011f50e2a2c0188023e61c545803104d6d418a8b006200ad983151600c4015d5042a2c018802ba608545803102d79408a8b006200af181151600c4014f50bb92c0188029e61772580310063cbaee4b006200c79755c9600c40b5e102b92c0188029ea1472580310053cc28e4b006200aba841c9600c40157308392c018826b6a0c725803110d6cc18e4b006205af2811c9600c4435e302392c0188023ea1c52580310047cc38a4b006200aba84149600c40157308292c018826b6a0c52580310056cc18a4b006205af281149600c4015e302292c018816bca07425803100578c0e84b006209ada83909600c4015b307212c0188029ee1542580310053c42a84b00620587e8795165884014db052a2cb108162fa1f545922104c77c32e529c420587c87595538840b1790eb228710826a720d6450e2159637bb6eaa1442aec6f761d542884016d3003aa85108038b9516550a2101d56422c6a144200aad8690d42884655cb0db8a8510b2f8d15164546214df932a284a8c420487e85dd160884010fb0bba2c1108030f5d254d952100c3e42ee0b2a420487e87dd564484010fb01baac8908021fe1576551210046fc3ac631a42058ec865ca534840717d093b2a6908022f6127654d2104c3f43ecaa9a42058ec865ca43484010ff0abb286908121f2157650d210047dc02eca1a42018f8805d9434841359d07b2264908263b21d644c9211fd3642ac89924200ace8694d324847fc98caa9a6490802d9614714c921005f0c00e29924204a748559251484094ed0bb22a2908123d21d64545210263a3b2a6a8a42009e4874c951484059c8ec992a290803d154d32545214cf5210ec8a0a4205acc864cb314840b3990e9926290816b3219324c52102de240a6498a420087f855d360484090f9
  | 10 => 0xb286200a3d841c9650c4134bd06392ca188929760c725943102d3b408e4b286224a75811c9650c4014f500392ca188029e600725943102d3b40e84b286200a7581d09650c4134bd07212ca188029760e42594310043f43c80b28620087d87901650c4010fd0e202ca188021f61c405943104d2f41880b286200a5d83101650c4014dd04202ca188029b608405943102d3b40880b286200a7581101650c4010fd0f102ca188021f61e20594310043f43840b28620087d87081650c40147d08102ca188028f610205943104d2f41840b286200a5d83081650c40b4ed02102ca188029d604205943102c5f43ea8b206209a9e83909640c40147d0b202c8188028f616405903104d4f418eab206223a9d831d5640c40155d043aac818802ab608755903102d5b408eab206223ab5811d5640c401575003aac818802ae600755903102d5b40ee4b206223ab581dc9640c41353d07392c818802a760e72590310051fc2ae4b206200a3c855c9640c40117d0e292c8188022f61c525903104d4f418a4b206200a9d83149640c40b56d02292c818802ad60452590310055d400a4b206200ab980149640c40147d0b382c8188028f616705903104d4e41ae0b206200a3e851c1640c40147b0a382c818826a7a0c705903111d4ec18e0b206200aae821c1640c40155b04382c818816ada04705903111d5ac08e0b206209a9e83d41640c40153b07a82c818816ada0750590310055ac0ea0b206200a3e85881640c40147b0b102c8188022fa1c20590310045ec3840b206200a3e85081640c40147b0a102c818826a7a0c20590310054ec1840b206205ab681081640c40156b02102c8188161f21d655503102c5e43ac8aa06205ae681d09620c4014dd0b102c4188029b616205883100557420eab106200aad841d5620c41359d063aac41888ab360c755883102d73408eab106222ae5811d5620c4015d5003aac418802ba600755883104d6741ee8b106222acd83dd1620c40b5cd033a2c418802b9606745883100537c2ae8b106200a6c855d1620c4011dd0e2a2c4188023b61c545883104d67418a8b106200acd83151620c40b5cd022a2c418802b9604545883100575400a8b106200ae980151620c4014dd0b382c4188029b616705883102d7240ae0b106200a6e851c1620c4014db0a382c418802aba10705883100556c20e0b106209ace831c1620c44559b06382c418816b9a04705883111572c08e0b106209ace83d41620c40159b07a82c418816b9a07505883100572c0ea0b106200a6e85901620c4014db0b202c4188023ba1c405883100476c3880b106200a6e85101620c4014db0a202c418826b3a0c405883100566c1880b106205ae681101620c4015cb02202c4188161f21d655483102c7643ac4a90620487c85dd9420c4010ff0abb284188121f215
  | 11 => 0x904094ed0ab12a3208165d21d52546410053bc32a4a8c825aa79809d5609051f4f700baac1208121fa1773582410043ec2ee6b04820487e85dc960904010fb0bb92c1208028f61252d95410043fc2ae5b1a820487c855cb635040153b08186c6a0802b360830d8d410056ac0861b1a82008df8758c63504139b4c6b80c6a08033658d7018d4104c7a432e329a820987c87595535041353d0db1a86a0802c76146350d41005ccc00c6a1a820399c8754d43504015390ca9a86a0adb2718f7250d4102cdb40ee4a1a82038f686dc5525055d27d0fbaa84a0abf0f1db75509416879210eeaa1282adc3c761d5425059fe48423aa84a0802ce600755094119e1e3aecaa128200e2e52d9542504051790eb2a84a080e6b21d52509412fdd240aa4a128200d3475dc54250401a68ea38a84a097ee920871509410146e41aed9928209c9c635d332504131e90cb8e64a08273518d71cc94102c5e432e8992823393c855d132504e9938c6ba264a080a37a1f634c941006563b28499282ceb2c8550932504e9d18c6a1264a097f691c5424c94101c7b436e299282039b6845ce515040136f0ea1ca2a08ca3d61f6294541004dbc3a8528a8233b348550a51504bfb48e4a14a2a080e6da1170945411cd9b42ee8a8a8239b348454d51504676690aa1aa2a0803c554d435454102cba43aa4a8a8239b348454951504013690ea12a2a08cecd2154254541196d239284a8a8200f2552509515057da68a9b82a2a08021fe1572d81410243e42ae5b02820987c8759554cc40517b09bb285988021fe157650b310243e42aeca1662098ec8758942cc4018d8eab128598b3793149654cb31505a642a849966274e8c6450932cc413938e6b2283988121fa1772583310043ec2ee4b06620587e87951658c40b17d0faa2c9188161f21d6554a3101c76c16eca14620087f855d9428c4090f90abb285188162f21d6450a310061e3aac8a1462cce3454595418c40b3690ea1a8318827651cd43506314fd9a42a84a0c625fea462509418c4090fd0bba2c1188021f61774582310243f42ceca12620087d859d9424c40517d0fb22849880e3ba1f625093101567416ca99262028dc87595324c405998eca126498a7ad3215424c9311f746322849926200b95841c5324c4017a30038a6498816b5219329053101d5b426caa0a62038f487595414c40178b0439a8298802f4600735053102cda43a86a0a6209cb47650d414c413b28e6a1a829880f2d1d942505314ed9a42a84a0a6232ea462509414c4139a8ed99282988027521d325053102d6a43264a0a6209cd4764c9414c401f0a8499282988161fa1e545943104d2f418e8b286224a5d831d1650c4014dd043a2ca188029b608745943102d3b408e8b286224a75811d1650c4014f5003a2ca188029e60074594310051f420e4
  | 12 => 0x8f28fa1473592510051ec28e6b24a200c9d731cd649440155d0439ac928802ab608735925102d5b408e6b24a23cab5811cd64944015750039ac928802ae600735925102d5b40ee4b24a23cab581dc9649440153d07392c928802a760e725925102d5b40ce4b24a200ab5819c9649440147f0ab92c9288022fa1e32592510045ec3c64b24a205ab6810c9649440156b02192c9288ce8fa1670592510051ec2ce0b24a23ca3e851c1649440147b0a382c928802a7a0c70592510054ec18e0b24a200aae821c1649440155b04382c928816ada0470592511e55ac08e0b24a233a3e858c1649440147b0b182c9288022fa1c30592510045ec3860b24a233a3e850c1649440147b0a182c928802aba08305925100556c1060b24a205ab6810c1649440156b02182c9288ce8fa1620592510051ec2c40b24a2008be87081649440117b0e102c9288ce8fa1420592510051ec2840b24a200a9e83081649440153b06102c928816ada0420592510055ac0840b24a209a9c83591439440717d09b9ac5288022f6137358a5101c76c16eca14a2058f681dd9429456587cc9baa85288162f21d6450a510061fbaac8a14a233c3c75591429440187cc8bae65288cf0f9d564cca510061ebaac9994a200c5d7558f329440b1b90eb1a6528a3e9ee0175582510046fc3ac631aa2028ee82dd943544011db05bb286a88125721d5350d510061f2a0eca12a2afc6c62dd542544071dd0fb1284a88125b21d525095101536432a4a12a2028de839db32544018bceca9e64a88161f219754c95127726312a6992a20187c855d360544030f90ab9ec0a88061f21572d815147c3e43aa5b02a200a6e829cd65904014db0539acb208169da06735964102d3a40ae4b2c8239a3e841c9659040147b08392cb2080297a0c72596410052ec18e4b2c8205a76811c9659046d4eb02392cb208029ea0072596410053cc00e4b2c8239a3e848c9659040147b09192cb208169da0432596410053ac0864b2c8205a76819c165904014eb03382cb208021fa1e30596410043ec3c60b2c820087e870c165904010fb0e182cb208e68fa1030596410051ec2060b2c8200a6e820c165904014db04182cb208169da0430596410053ac0860b2c820087e8788165904010fb0f102cb208021fa1c20596410043ec3840b2c8239a3e84081659040147b08102cb2080297a0c20596410052ec1840b2c8205a768108165904014eb02102cb208121fa177258e410043ec2ee4b1c8200c6e72596539047f8dccab94a7208031b5957294e410063ab2ae329c82058f681dd9539040b1e902bb2a5208161f21d6554a410063ab2ee2a94820487e855db32904010ff0cbae65208021fe1d65cca410043ec3acb99482058f4815d9329040b1b90eb1a6520817351c5634ca410053bc32a6a8c82358f48758951
  | 13 => 0xe3632ae529a8400c6e521d95350965878e9b2aa6a100a2fa1b7454d4201c9e43aa8a9a8404a3c865515350801a5ca4bac86a12bf0f9db6590d4256e1f3b0cb21a8400b3980196435087d33b0fb1c86a100387d976390d425d787292a721a84029ac825c643509658d8edb2aa4a100e6ba1373549420053cc00cbb0a84cfc3d7419661508014f30032cc2a10021fa1f65585420043f438cab0a8400a7980195615095d87ce8328c2a10029e60065185420047bc3ac230a8400a7980dd760508014f3003aec0a10021fe1573d81420243e42ae7b02840087f855c760508090f90ab8ec0a12be1f21b75581420043f43ecab02840087e8719560508130fd0f2a2cb990269720d745973204d2f418e8b2e6442a5d831d165cc89d4dd043a2cb990029b60874597320053b408e8b2e6400a75811d165cc8014f5003a2cb990029e60074597320051f424e2b2e6400a3d849c565cc8134bd0738acb9913a9ba0b415973200536c1682b2e6409a5e8310565cc8014bb0620acb9902697a0e70597320052ec1ce0b2e640087e8790165cc8010fb0f202cb990021fa1c40597320043ec3880b2e6409a5e8310165cc8014bb06202cb9913a9ba08405973200536c1080b2e6400a768110165cc8014eb02202cb990021fa1e10597320043ec3c20b2e640087e8704165cc8010fb0e082cb990028fa1010597320051ec2020b2e6409a5e8304165cc8014bb06082cb9913a9ba08105973200536c1020b2e64028dc835d954cc8130f90eb2aa99900317597735533220c6e43ac8a9e6404a5e8559153cc8132b90eaa2a79900297e195454f320243f42ee8b0e640087d85dd161cc8e14f3013aac1992429ee0175583320243f42ee8b06640087d85dd160cc8090fd0bb8ac1990021f61771583320061eba4a9b2a6400a6d82953654c8090fd0fbaac8990021f60375591320043fc2aecaa264028de86dcd544c8131dd0db92a8990fa3761f6494d320252e42ac929a64029ce825c6534c80539d04b84a6990123721d6454d3204cae43aa8a9a644eb4c82551534c89d69d0bb92a6993175314b7054d325b6c621ee4a1a64ad96e87dd5424c9658d8edbaa849934fc310f7550932576363b0eaa1264d2f0c431d5424c8016d3003aa84990ff1b1d76550932007172a6caa1264038ec87595424c8053590eaa284991d2e320d5450932006a63aee6a126400d4c751cd424c9a37190839a849900273a1e53509321fea63aca6a126474b8c8494d424c8013990ea9a84990ff531d553509321f5c6422a6a126400f0d5454d424c8010ff0aba6c2990121f21574d85320055ac2021b0a6400ad583043614c8015cb04086c2990023de1d611853202e7930ae030a6400cf1615c0614c8010ff0aba6c0990121f21574d81320054f41c84b24a200a9d83909649440147b0b202c928
  | 14 => 0xd841c56294c1359d0638ac529946b360c7158a5300575400e2b14a600ae9801c56294c011dd0fa0ac5298023b61f4158a5304d6741882b14a600acd831056294c7f4dd0b382c5298029b6167058a5328d37428e0b14a600a6d851c16294c0155d08382c529802ab6107058a5304d67418e0b14a651acd831c16294c015cd02382c529802b96047058a531fd3742c80b14a600a6d859016294c011dd0e202c5298023b61c4058a531fd3742880b14a600a6d851016294c1359d06202c529802b360c4058a530057340880b14a600ae5811016294c7f4dd0b082c5298029b6161058a530047743820b14a6008ed870416294c7f4dd0a082c5298029b6141058a530055742020b14a600aad840416294c1359d06082c529802b360c1058a534853dc02eab04a600a3d859036454c011ef0eb08c2a9a421f21d54d81530051ec24a4b2c86bae4c5254d6290c090fd0bb92c1218021f61772582430262f3aaa7b1286008f7875846150c010ff0ab96c0a18121f21572d81436ae2ebaec731aa4d4ccd72d8e63548011bf0eb18c6a92be1fe1574d855202e5a30ae930aa400cb574d8661548011ef0eb08c2a92be1fe1574d815200c3e42ae3b02a400a3d8494365508890fb0e306caa100297a0c60d95420052ec18c1b2a8400a768118365508014eb02306caa10031e5c060d954257d1ec26e7b2a84b2a6d821cf65509654db05b8ecaa12be8f61071d95420063db84e1b2a84b2a3e841c3655095f47b08386caa100297a0c70d95420052ec18e1b2a84afa6e821c365509654db04386caa10029da0470d95420053ac08e1b2a840087e878c365508010fb0f186caa10021fa1c30d95420043ec3861b2a84b2a3e840c3655080147b08186caa12be9ba0830d954200536c1061b2a8400a76810c365508014eb02186caa10021fa1e10d95420043ec3c21b2a840087e8704365508010fb0e086caa12ca8fa1010d95420051ec2021b2a8400a5e8304365508014bb06086caa12be9ba0810d954200536c1021b2a8400d3b405c06550801ad640b80caa10031ea1970195420069d422e032a8400d39845c0655096b8f6c8b80caa10034e10d7019542006b5412e032a8400d69825c065509698f6c4b80caa10035ad0970195420069d212e032a8400d38425c06550801ad084b80caa10035a8c970195420069da0ae032a8400d68215c065508018f2e1300caa100297a0c60195420052ec18c032a8400a768118065508014eb02300caa10031e5c0601954257e1e3b6caaa284029ae82dc554508014f30032ec6a134b1b5c86598d420053cc00cb31a840087e87d9563509a7c3887b2ac6a10021fa1c6558d420053cc00cab1a84adc6e7219463508014f300328c6a100237e1d6318d420145ec24ed29a84098de839da535095f8dce5b2ca6a10263b2197294d421f
  | 15 => 0x800000001001000800400c07c01400c00803801c00006800000c00800401400001400000000406c00000000800002405001800000402c04400000001401800802805800002803400400400401800002801c00800800401007400c00000400000c00800801c00c00402802000800800002001000001c00002c00000000801c04000000400002000801800002401c00c01001401c00402004c01004400400000804806c00400000000406401800c00405000800c01400400002000000003800802000800406400400001c00c00403800401802c00000801800000400002800000c05402800c00000003000400000000000400c00001c01000008802400800800000002c00000c00000800000000400004c00005000000001c01000000400c00001405401400000400800003801000400003c00000000801402400c00401400400401802400400c00804400003005400001001000000c00000001400c00802c0e800c00c04800000000000400002005801400000002400004800002400801400005001402802400000001c00001805c01001002401401c00000c07800c00000401402c00000000004c00001800000003404800401400000800c00400000000000001c00c01800403800c00802000402800001000001801401000c00000005402802400000000800400401800400400800400000401800c00c00800404400400002400801000800000000000400000000c01003400800802c02c00400c02000c00000000c03c00c00800400400000000003000000003800002000406001000001400002800000000801000000000000800000800c00801401400003401000000400000402000400001000c00000c0000c407400001402000000800802402002801000000800401000000001001000000c01c00000c00000401c01000400001003003000400005400003800800c01400002400001400401c01000800800001401803c00401402800c00000002000401401001800400001000000400000000800000800000000400400400c00c00800400801001c03c00c00401c00c01000c00000800800000800400002400400c03001000002000c00400000000001002800402c00000400c01008006802c01401000000002000400001001c00400001c00c00401c00c02401c00800400000000000c030000000000009650ff0ab96c6aa00333d8d7298d5404e6631ae531aa8008df8758c63551af8eaebb0cc2aa35b2d5d361985540047bc3ac230aa8b287f855cb60550051dd05b8ac9298023b60b71592530057340e84b14a600ae581d096294c014db0b102c529826b3a0f7458a5328d66c1ee8b14a609ace839d16294c0159b073a2c529802b9a067458a5300572c0ce8b14a600a6f855d16294ca34dd0a38ac5298029b6147158a5300557420e2b14a600aa
  | 16 => 0x261cc000070854e357217800102262029200000002e400001bcf620122b9172c52a54f32a0a600000000d41c60b061c604b10d0da24a214183901a00001be170000000029f84b80940000001dd4d1a55b3950000000000000000077e2a42b28000794000000000000000039000009681a600015b0000000231000061a0000000cb46861410000108448000000000074405610e8000000000000008400000028a00004d209c077072861009701f96a505e82825606a8a980943d28000dc8073000194c8123ad2d81e1506a4071c420a892e36f3eb108840200000000003c200019d95409a82b429f18f42027830020d3480a4b108f9dccb560052ea000000000017003704586a211680005160000001f90a680c200000000003a6000000000000011a19ecb180003cc800000000000000003f227c0001f0c0001970000000cc44d932103c0ca000034b98a40001703531bc83961e23bb9134fa637b3030d0828409f1500a005fe80a10b95dc0002033df800000000002300000006a300000009260002c48be4000352000000096e00000005d00003cf37f800018a03922e8bf4f2000f18e12e83ea6c20778918c367e2012936c0000000000c1d00c0da38d9c78f607341ed8000a3613c000091cf2223d0000e0437000026300004d43763b41fd00002a6000094822818808b899000063c21c00000826fe0001eaca027b7000187000014922d99f0c1c00022f10ec00038c3ff1ac4eac0000000164d56000260969088a6e600000000000000ab00000001cd0000000000000000105462a000000044c9865170f8a04c00009e00000000000001810e6c00000036e0000c0a82b1000d5101e0000a28000dfa2ae20000005d26e72b0800000044f1170e448e003129489cc2d6277000171c8e23cd0821ca06504ef3489ef895c4ca1e30a340aa7a933f10743660d211293f86905e40001b1800000000013680000001640000e0432e0001e207de67129e1ea000000003d85d473c48c0bc80005cc00000004681520eb0019798c4a737000040cbae00002e00000000001e388c400039d3ed1a7c00005030b1cf00000002a01af83d279f0001fb00006440000bec0607c43858ab00004e415b09808f022b29c0c483e022732c9b48112726000003000404c01800803401c04400400400c00c00c00803400000400400800002400000403800002000000801401402000800c00000000c01c00400800402800000001c00002c00400000c03800400400c00000403800801003c00000400c00c03c00400800000400002402800000000400401800001801000401401002400000002400800000802001400000403c0fc02000000000800000800400400000000001003c00401c00000000000000003004000000000400000400802002c00001000001800400000000403
  | 17 => 0xae1ba863a81e2b38d4c75c10900003b000007e17d000000000000000000000000000de88320000000564000000367a050f1281d0001fd8000000276800063064e000006c3726552af0a3d0720ce0eb0c248240022ae8ef4f9c00016f0210f9400001e000100a000111163809801f00015f447008e131910c0000b635e00001362810e98578000369000150cf3c31a3960f4400005e0001c184b43950a88000f1467f3261f2c2aa0000000000a5e5810000000cde0000000fd8eda7db15802f056400024283ec7980000000000aec000000118c1fc60220109f8cd48080db0000a1000012a1ef09c247d1db0c4000076a34980002586ba010000000024d2980b5c7423490b7854ca6449020e1f5c94800000020843142231ef8000d602673da00006ac000000084c61e0000f90000000000000000000014b11c863837e7e7245000034e0001f61608df400028d01c80002162970604f846f031a07f000005800000000000000901668c8c4cb0088000c5a1c11b20b28d38204332125827607c0000f9c0001ae16c861085a000000185c7ea80400000000007f9000079843600000016188a449f399800066e74e0de85e07703d01751cc8d765ac195873ceb274d378923c4a249a38b9140b0a49c417021c27c3d911fa008cce80910c9c847e40bf32682cce4a45919181c40001a11c79d4c2e46a92f19c24e705002d68ce0f440a210315f0a1870515d05186627150800644cac74f0da90c019663100f0e643527fd36c19d030c62a0a81e5c7066ec0b48f08af270f3b20d7498e0d80000acc8660ac3f1817c0006cb0d00eec0000000000000324000000032447600005d80002cc00000004c0000000000167c0000003538dc429a000058875c75e2420001600fd61d00cd9460c8600000000006b46682780494c902283b81794e441541b280000001e40309904d1c0001ee06c0000000000000000000026a80000005491678e5ccdc07625e09f48b070802399dc9e46f324c8c80fe00000000000fc20000bb90907280000a79dd841e2ab28b0d3ca400001c2000057e00003b80009d24550329f6027a0440931300c1a00000000000000f2000092c0003f8228800000033c22516d088e2df3dd80dc0005fa00004789ba69b2d8903c0005d21519df447455100002546dc00007e000000081711917b4bf2000000000000000020c00000000000000bf0b7400000000007dc0000ad08f013a6d30000000c260000e016f842a545392169c5184bd07d177ca6e0df00b024063c00000000002301a417c00385a600031091a418c4d11011abcbbc439019031c0c02fe264987c00029f0e420c82ce593412854800000000015180001ac3b70a500005220001d5082200023f8000aae000000000045400020a133000004e1950edcef46d62810c940004b825302801
  | 18 => 0xe205cd2411274c4c483287988c1320a408c96f400000016280000007ee13c80000008073309f4000081b0000000dc67e631999c000029134480000000000000ff82483b22cf1ce88400000b71c740006283e08f0400069d2b69b004d80a800d0190b0e5a51f58f905b65bf38193e44900f31829484dda5a81949670aac5363238320b820000b880000007dd2ca80001fe38d0000b04cc04e71aaa0681ba75b000153400056e3c39358e8224c00000000000000000000e72000000149c00066c000021473466b3ae8000ad60000000ce40003aa000000000000000005ecb2e0000001adc5e403a27009c4bd21eb1af0000e8812214d00000001e532580000004411f50000b7671c1fb80007c646f3a602346060000000c0400000004900004ec30a2a51c9d06876129196ccff82ed0701800d0a6e81af80cc81c77440c0f80d0440a0d58a100000000c485f0a080001fe2088d5424e07080004aa3220001ebc0005533090f4c5b869900000005920a11bf9f54b7000000012a48740000ad94244f472b0f683c419851d09c0d10cb6000394956845e2aa076926091216214c9f5072c0883758000abe5472e411841cc4882371b74c306f4033039d0026f608aa0a462e358008093c3bc58d388962cbaa7cf0000d642722101d99ef49085d135906c4a0c8262b80e9cf245880001d7886e6c52f5051c00200030210782880d600000005143723c59c6400000002ba0e025e55840e000016400031b8c50ea408c39814482c00000000770f5c00008399f43645e017b066050a6ae1b080002800000001a54b6438206a1f9472434539883343ee20e34c05b0fa44f500007bc3f079b000019c00000000000003a200000000000000001449198bfc6bf37ca0800000004199cecd4a0003250ee400060b3d1983ca6a0000b2999800000016e8c10c0e0001d80000cba00000000000004e8000000053647c1bf00002e65da39b00002b000012c0b948b45af36f800065e7ad25a9948e7e00012e0000e8a00000a8c5800051000018f839c04328a80d800077b0698000ade3110cb00000000000000070a9608630480009720000000000c5e6b33bc03109d60003e28000e1a2573c6928c46c7071c585280d232c01c11dc0f00000580b447745a02ff9b24b840543491a68d3c00009380004140c020d1cd46f24cf00000000004b21e2000000000c37280004ca0ea1299fe800000000000003280cf2cd96d800000024d8e1c4da0002f900000005f129500005e66783dc800002819a25b032879201800000000000000000000d5a00021a8000cae10c3c2063c00050e0000000f406d9000000000014e0e393b05a41c504d0304f383ac0000d1c4cc6c80d68aa005068f0d28001032687275067800000000007ec8ca70c03e80007900002e21bec6d47041b307cc7c22932
  | 19 => 0x37c101803a1213ad0a1cc7646415c9d98f9a7ed1048e80000000000125014e79d0001e040000000001d600a400024000000005b7000000000000019382040003672191de400076b2de00000005e10001cb892a2d83f498fc7d27de2961b501146630288dcca3e0001680674bc44c808d8c6cb6a4e52968e24b242b70ce1a4000000030080006b80a30001d700002123a00c90eca0e300000000003a40000fc401a5dd08280000000000001f00000000409000057800000000000000000001698000000000000000080b0000000ece000000106c28643d01781e4dea0f630e92b41540003f8912070a71610688c00004c405c80007d053935b0d6c8fc5ec19996440003fd308800058402600000008f475100001208566800ea80000003c0000000000000000017280005cf000000000008200009b80003d2000000000025900000000006ee000082c34474a0f389ac0000000360c4c00003d000000000000033b0000b440000000000c7070023600000000002798a84d823b107c8c7c9c41611fd01b840a4d03db0e7034621a1d18408f9242a37b958c0101da21f1098afe6750341e3800000000004580004d719d057400000031716e400e0002341e607b072d255907ce8425b29987d80000bd0159ee0cb022117199c867c2c415111589164e32958914e2444b1131a508925980530d0456a59019e8710aea19924900006da000000000000045f05a8d185c442927e81e82be000000000046a5cc0e1800101c1e33ab8e94d982780559010482148389800067e00039f11cc3be3b40001e90000000000000066050b2e981acec60001cc1a80ebe5682068a74d8e40b2930b34ae22eb15889c0dc26a80c614445207013d994f421e46b0002040d485f409b0f5cd2c0230b20394cbc00000000000000003160ea440e000000000013064000013b85b400002796a8a1a6a10ff1d88c6029c22b99680004f70001b3400037509a0000000000004800000042321f9150c440000001b0c0000000ea141c1b2401289800000000013a80001aa0190000000cf20002bd000014a59612b0c64494000000000000000017a8000000000000000042800029d8ffcb46673071136000000000002bc5e200000000000002e726e134861c4e604580000005eb1f680000000002171718bfa4bb00000005a800024f0ba00001310000e4066812a000000000000000000000e8000000000088c0003be0ae000000000015f800059d0840f389e80001df00000006242789b280002f40001f209600000f700f80000003a1909408a4080000000be61830b418e4000000087000000000027b000086c37d000000030a0910bf20dc0007230000000dc4000000014c0000000002091060000000000064c0001a8812c10068b0001b3837c80d16195e00001dd229929c4f67481fa15ec
  | 20 => 0x4d062a93cb00008804a836a9d249bc58a0000428f1834c05d00000004ff0c814a08da00002000005ee00003f80a80003d61660000b1e0000000000fa27ea0000000eaa81600014c4f64000000000018650a000000000012d0000f540000003b90d380000002f7002800000031a91ec4ba00015d800095e5ce02d9da48e42882a091d82b85a11c31f7c4865d63ff820c97e00016398ad06c0002fd8000bce5031340c007963de00006000006100000af400000031380005de0000ff9e54ac46e030f00004402cb00017d8bd00000000000ed80ae0b51218fb200027e0eac4805f002e8000826000000004c88400038f95a80003f33cd02b482e7c7176083091a17d35ea0300006c400000000001353fc0de102a00000008dc00000000000000000001390dc00006d7000186400000000011d000008f01606082ae6860000f982fe137000000090e00000000004520000000f509f400000012040001ba0ec0748ea07ac1f2897c8ea28e06d9470fe40002b980005ac000000000000077f00000001bc6ac1770e00e346360000000bf80000b681882240000fa02f800065f000000000054800000004c22820000000f0c000000000000052500009d0f0067a38500000003f90000000a3c000000078094a0001c7000053c0002b200010000000000000c9e00041380000001fd0001548f282920249170e8e505305067c0003fb3c7800089c1e821e087d03e431000000094026f1b588608581b409400b49a665c0170d2c6d823e000191497c1bc0001244f5474b0bd098800028605b9ed4b864a12550b000007602a100000004df088800000000007a0000b280002a715545c20003d300a46420f803a94e829800000018546181953b79c50b926843b895d099c6810000e7c00c00035c00007b40630d785d830e0001ba09401a23f01569b6c0003772e80d28a882080001b78000444334a08cf747a13fa88cd06256007480000000002fc000080641000b80000000000948a58bb800000001c006a0273191cf42203c330600006a042737e009023800000000000000002471ad00000003ee1464422000000000037600009f93340003060000000e8c80318581b471400012200008422be00000000d46b50000d0049282d10f16108ce00030404c826600000004ac98a03b1f10abccca6b92d71e089660f51528cd876a7e00268000dde7c6000000000000007e80000005ef00008700000002060ef0fee3931ee816882c6141671ba40003a83460000ab213a08683dc0005c53fd9e9c58c1ec3e617dc8d410b1b01180d145d81780000c340000f517d400000000000006d011d3f400010585db33693083f44fb14b872400000036800001d002219a800006816300000005aa363214000000063a3289550db47ef0ed848ce1c0b83c99cbc36e1d906b8f146c44f8
  | 21 => 0x77e2b315a416800000000000000000000000b32106344062cc927f313f980c4bc3320058000326000000113031a479000176
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8018397460065985420061a1d9801d5424c801b084360075509320055264075dcd424c801549901d473509323a4c32615454d424c89d50c975515350932006265cd801cd6494401838766007550941006c8085801d54250401531901d771509410054c640751c542504733149854d43545411ccc92615250951504bf5249754942545410051a6407558942cc401439901d56450a310066121d424c9414c4bfa848650932505313a7211d9424c9414c5b17049550932505310048e640855c9640c4012699021574588310041e64087595420c401439901d564508310051a64075589420c4010799721542580310061add9801d5428849dc447654d32545210070558d615d031d4001c4563585720c7500071458d615c031d4001839801d06258d500060d1d181189635400181d8460c76509500040f660431d942540014359110c76509500050e640431d94254001469908c8765095059e1a602321d9425400185583604765095000619609811d9425400143990d04765095053e0e603411d9425400144d9308476509500051a640211d9425400183984600765095000616a0d801d942540018598360076509500061a609801d942540018728160076509500061c605801d94254001c294048076509500041ea60765c1425400160d94189634c950006832106258d325400164591189634c9500068310c86509325400106d981c864585500061360c721916154001869801c864585500060b2107258d6154001a242121942505500058564c645854154001625921916150550006892086458541540018387660075509401cf0c1d951505505000132b9260774541400c60e21b745cd5050031318985cd43541400c54665c6350d50500013199321d4254140004cc644875095050031328985c942541400c4cc647825055050031632969c541541400c4cc26171505505017bc30765c54154140635c82497150550500032389661131541400c4cae614288550500011389761121541400051a6407558942cc001439901d7645093000c6625d844c9404c0e9c887650932501300061a1d9801d5424809dc487654d32541200241ea6387591504800132b9460f7254120004d264c8750950480013619121d42541200bcca26174509504802f32a9890d42541200bcd264f844c950480011689761132541201fd1a25d644c9504802f64a969cd32541200bcd2261734c95048189c48765cd32541205fdc2251734c9504802f86886dc9715412019d0e25d6450550480032689660d21541200bcd826171485504802f5619718521541200050e6407559142c4001469901d7625091004d2625d6450d304400129994219324c110004786488750530440019908750d414c11000c7425d844c530440032d09660d214c1102ff281d94250520440031e0976112148110
  | 1 => 0xe4020000000000a1f800000000000760000000cc000d80000560000000001d000001e0600000123280cb80000000000000000267c00110001d001b4000015854fa000000000000000090591f000000008800000000000008100000000011214d2001e00034003589886470e21d04402f800d8001c14000250000000003d00000051b00000770000000140000000000001000001680000000000000290000000000013800212b908000000000000000000d00000000004a1205906173c800000000000000037000ba000c0409e003c080002c059d0000d03000000000180004500000000019218d4072988c0052000008c2f3b1d40000001909858000000000041041c2e2d9f8fe2a00000ce00248cc00302aa10a2000000000002d0a00037188000000048001e00000009602139840000001c4f60000134000038000001f37800bc00000f4c400398000000000000000000000034318006a8039150000000064000080008000200000000080000000000000000180000020000004070080800040300004030080000010001006000000402000044e660435c0655080152a9210d70195420054c644435c0655080156291d09701954200546a4e425c0655080143a9610970195420051aa58425c0655080152a948c970195420054aa4b415c065508011699808570195420054aa50215c0655080154993085701954200616a0d701806550801859835c060195420061ca05701806550801871815c060195420061a5c980196635080183a766006590d4269e0761f65d8e4350
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x310000000080aa4800669dc35904028021802309a910d801d5424c801580d0886c00eaa1264008c86a42160075509410056034610b003aa84a0803209902106258d325400190242322312c6992a0008836a443219424c95000540b422190ca1264a8002a09a010c865093254001016d4908392c6b0aa000a8168c212194250550005443401090ca1282a8002225a9208645854154001902c9904322c2a0aa000c88640821916150550
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x4
  | 10 => 0x138b
  | 11 => 0x138d
  | 12 => 0x138e
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9cb
  | 16 => 0x9cd
  | 17 => 0x9ce
  | 18 => 0x168b
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0b
  | 22 => 0xa0e
  | 23 => 0xa4b
  | 24 => 0xa4d
  | 25 => 0x198b
  | 26 => 0x198d
  | 27 => 0xb09
  | 28 => 0xb0d
  | 29 => 0xb0e
  | 30 => 0x1409
  | 31 => 0x140d
  | 32 => 0x140e
  | 33 => 0x249
  | 34 => 0x24b
  | 35 => 0x24d
  | 36 => 0x24e
  | 37 => 0xb49
  | 38 => 0xb4b
  | 39 => 0xb4d
  | 40 => 0xb4e
  | 41 => 0x1449
  | 42 => 0x144b
  | 43 => 0x144d
  | 44 => 0x144e
  | 45 => 0x16c9
  | 46 => 0x16cb
  | 47 => 0x16cd
  | 48 => 0x16ce
  | 49 => 0xb89
  | 50 => 0xb8b
  | 51 => 0xb8e
  | 52 => 0x1489
  | 53 => 0x148b
  | 54 => 0x148e
  | 55 => 0xbc9
  | 56 => 0xbcb
  | 57 => 0xbcd
  | 58 => 0x14c9
  | 59 => 0x14cb
  | 60 => 0x14cd
  | 61 => 0xcc9
  | 62 => 0xccd
  | 63 => 0xcce
  | 64 => 0x1709
  | 65 => 0x170d
  | 66 => 0x170e
  | 67 => 0xd09
  | 68 => 0xd0e
  | 69 => 0xd49
  | 70 => 0xd4d
  | 71 => 0xe89
  | 72 => 0xe8b
  | 73 => 0xe8e
  | 74 => 0x1789
  | 75 => 0x178b
  | 76 => 0x178e
  | 77 => 0xec9
  | 78 => 0xecb
  | 79 => 0xecd
  | 80 => 0x17c9
  | 81 => 0x17cb
  | 82 => 0x17cd
  | 83 => 0x1049
  | 84 => 0x104b
  | 85 => 0x209
  | 86 => 0xb8956
  | 87 => 0x289
  | 88 => 0x1549
  | 89 => 0x1849
  | 90 => 0xa4a
  | 91 => 0x19c9
  | 92 => 0x4b
  | 93 => 0xb9396
  | 94 => 0x4d
  | 95 => 0xd0a
  | 96 => 0xa4995
  | 97 => 0x124b
  | 98 => 0xcc995
  | 99 => 0x15c9
  | 100 => 0x12cb
  | 101 => 0x1889
  | 102 => 0x1609
  | 103 => 0x180b
  | 104 => 0x130b
  | 105 => 0x1a09
  | 106 => 0x1649
  | 107 => 0x134b
  | 108 => 0xcc9d6
  | 109 => 0x3c9
  | 110 => 0x589
  | 111 => 0x18c9
  | 112 => 0xa4c
  | 113 => 0x1a49
  | 114 => 0xcd696
  | 115 => 0xcb
  | 116 => 0xd0c
  | 117 => 0xcd
  | 118 => 0xa4a13
  | 119 => 0xb8a13
  | 120 => 0x124d
  | 121 => 0x150d
  | 122 => 0x128d
  | 123 => 0x12cd
  | 124 => 0x1a89
  | 125 => 0x1949
  | 126 => 0x134d
  | 127 => 0xb8a53
  | 128 => 0x148a53
  | 129 => 0x2c9
  | 130 => 0x4e
  | 131 => 0x124e
  | 132 => 0xcca55
  | 133 => 0x170a55
  | 134 => 0x128e
  | 135 => 0x449
  | 136 => 0x5c9
  | 137 => 0xce
  | 138 => 0x12ce
  | 139 => 0x130e
  | 140 => 0x749
  | 141 => 0x150e
  | 142 => 0x180e
  | 143 => 0x198a
  | 144 => 0x198c
  | 145 => 0xb9993
  | 146 => 0x149993
  | 147 => 0xcd995
  | 148 => 0x171995
  | 149 => 0xbcb15
  | 150 => 0x2cb
  | 151 => 0xccb15
  | 152 => 0x184b
  | 153 => 0x160a
  | 154 => 0x19cb
  | 155 => 0xbd415
  | 156 => 0x20e
  | 157 => 0xb8b56
  | 158 => 0xccb56
  | 159 => 0xb9456
  | 160 => 0xcd6d6
  | 161 => 0x2cd
  | 162 => 0x154d
  | 163 => 0xe8b93
  | 164 => 0x19cd
  | 165 => 0x28e
  | 166 => 0x154e
  | 167 => 0x184e
  | 168 => 0x18cb
  | 169 => 0x5cb
  | 170 => 0x1a4b
  | 171 => 0x3ce
  | 172 => 0x15cd
  | 173 => 0x74b
  | 174 => 0x44d
  | 175 => 0x194b
  | 176 => 0x1a8b
  | 177 => 0x1a0d
  | 178 => 0x164d
  | 179 => 0x15ce
  | 180 => 0x188e
  | 181 => 0x160e
  | 182 => 0x188c
  | 183 => 0xece93
  | 184 => 0x5cd
  | 185 => 0x1a4d
  | 186 => 0xed793
  | 187 => 0x58e
  | 188 => 0x18ce
  | 189 => 0x94b96
  | 190 => 0x138b96
  | 191 => 0xcca499d
  | 192 => 0x98a55
  | 193 => 0xa0a53
  | 194 => 0x130a53
  | 195 => 0x10e
  | 196 => 0x9ccd6
  | 197 => 0x168cd6
  | 198 => 0xb8a4a1b
  | 199 => 0x128a55
  | 200 => 0x8e
  | 201 => 0x198a53
  | 202 => 0x198a55
  | 203 => 0x140bd5
  | 204 => 0x144b96
  | 205 => 0x16ccd6
  | 206 => 0xccb96
  | 207 => 0x74b93
  | 208 => 0x194b93
  | 209 => 0x58b
  | 210 => 0x44cd5
  | 211 => 0x164cd5
  | 212 => 0x15ccd6
  | 213 => 0x1a4ed3
  | 214 => 0x184b96
  | 215 => 0x19cbd5
  | 216 => 0xccb8b5e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2397
  | 6 => 7351
  | 5 => 2106
  | 4 => 136
  | 3 => 15
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
  | 7 => packedAt gbK7 (98277+((h/799+packedAt gbK7 (88689+(h % 799)*12) 12) % 2877)*13) 13
  | 6 => packedAt gbK6 (387148+((h/2450+packedAt gbK6 (352848+(h % 2450)*14) 14) % 11741)*14) 14
  | 5 => packedAt gbK5 (132678+((h/702+packedAt gbK5 (124254+(h % 702)*12) 12) % 3058)*13) 13
  | 4 => packedAt gbK4 (9925+((h/45+packedAt gbK4 (9520+(h % 45)*9) 9) % 315)*9) 9
  | 3 => packedAt gbK3 (1240+((h/5+packedAt gbK3 (1215+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe38f8e07188e0c7ff1f83f83fc206980f4cf
  | 1 => 0x703f1f007e0f00f8e1e3fc3fc3cc191934b33
  | 2 => 0x7fc01fff8ff000ff01fc003ffc1061e638c3c
  | 3 => 0x7fffe0000fffff0001ffffc000207e07c0fc0
  | 4 => 0xf800000000ffffffffe000000003f8007ff000
  | 5 => 0xffffffffff000000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40408282410002001300481082102028801045
  | 1 => 0x9201111082409044844213015028c091114112
  | 2 => 0x2124002430b900a92094808a29810202628c28
  | 3 => 0x5aa2401102a2520001924a808820740240e80
  | 4 => 0x3000000020d4c8ce48c00100310948005be000
  | 5 => 0xc6d3c9c9c4000100010006304232b5fd800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffef8ffeaeee8fffffef8ffeaeee8fffffef8ffeaeee8fffffef8ffeaeee8fffffef8ffeaeee8fffffef8ffeaeee8fffffef8ffeaeee8fffffef8ffeaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27907
namespace PEqualNP.Outside.L_meta_27907
open PEqualNP.Outside.L_meta_27907.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 60 := (concat bs0_4_0 bs0_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 40 := (concat bs0_5_0 bs0_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 4 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 4 := bs3_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 9 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 50 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_128 : Interval s4Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 136 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 16 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 15 := bgb_3_0
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
theorem bgb_4_128 : Interval gbAtlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 136 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128)))
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
theorem bgb_5_2080 : Interval gbAtlas 5 2080 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2106 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))))) (concat (concat (concat (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280))) (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))) (concat (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792))) (concat (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)))))))
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
theorem bgb_6_7328 : Interval gbAtlas 6 7328 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7351 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)))))) (concat (concat (concat (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 bgb_6_2016))) (concat (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464))) (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720))))) (concat (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)) (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648))))))) (concat (concat (concat (concat (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096)))) (concat (concat (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544))))) (concat (concat (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 bgb_6_5216))) (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 bgb_6_5472)))))) (concat (concat (concat (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696))) (concat (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)) (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 bgb_6_5920)))) (concat (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat (concat bgb_6_6048 bgb_6_6080) (concat bgb_6_6112 bgb_6_6144))) (concat (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))) (concat (concat (concat (concat bgb_6_6432 (concat bgb_6_6464 bgb_6_6496)) (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 bgb_6_6624))) (concat (concat bgb_6_6656 (concat bgb_6_6688 bgb_6_6720)) (concat (concat bgb_6_6752 bgb_6_6784) (concat bgb_6_6816 bgb_6_6848)))) (concat (concat (concat bgb_6_6880 (concat bgb_6_6912 bgb_6_6944)) (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072))) (concat (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200)) (concat (concat bgb_6_7232 bgb_6_7264) (concat bgb_6_7296 bgb_6_7328))))))))
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
theorem bgb_7_2368 : Interval gbAtlas 7 2368 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2397 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)))))) (concat (concat (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440)))) (concat (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))) (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))))) (concat (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 (concat bgb_7_2016 bgb_7_2048)))) (concat (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208))) (concat (concat bgb_7_2240 bgb_7_2272) (concat bgb_7_2304 (concat bgb_7_2336 bgb_7_2368)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffefefffefefefffffefcffeeeeecfffffefafffafefafffffef8ffeaeee8fffffefefffefefefffffefcffeeeeecfffffefafffafefafffffef8ffeaeee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,2,130)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,2,130)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27907.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.or,[6,7]⟩,⟨.and,[8,9]⟩,⟨.or,[0,2]⟩,⟨.and,[11,5]⟩,⟨.or,[1,7]⟩,⟨.or,[4,6]⟩,⟨.and,[13,14]⟩,⟨.or,[4,7]⟩,⟨.and,[0,16]⟩,⟨.or,[10,12]⟩,⟨.or,[18,15]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27907

open PEqualNP.Outside.L_meta_27907 in
theorem PEqualNP.Outside.L_meta_27907 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 1, 6, 3, 6, 5, 6, 0, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
