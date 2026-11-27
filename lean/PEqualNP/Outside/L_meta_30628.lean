import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_30628.Model
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


end PEqualNP.Outside.L_meta_30628.Model

namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
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

end PEqualNP.Outside.L_meta_30628

namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x2474f8d1c6900656000004e6c22a26040004a213190014500420861044614910655400388c4a4005800f285c5873c043000484000081046241ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x100003d18a4000000013c00000000480000345c00400000f4008414fc00c8585410016000ac88e400007c68002894b53400ec010c8c092c0000d96524816820011c01280098bc255c0c3878915874f80000d00108b8b00148000114c4015104193154f05141109c0000d46044cc64a81c04e86c4c00014c014430c1380120dc00002c70a0e0000e0402020200101404000c280200020200061c040a0e00100a1e000009765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x281825a440002e10000000052002c01c00aa8048002600cc0061a7883a200210020908103493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x4820601885496010631c22a6b008310e05635885150308b1ac028a81885896014540
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
  | 4 => packedAt s0K4 (2697+((h/30+packedAt s0K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s0K3 (998+((h/8+packedAt s0K3 (950+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s0K2 (248+((h/1+packedAt s0K2 (245+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 2 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 3 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4028004410502000420502480101429008c025
  | 2 => 0x24448c080c88910601209086c832244c221c92
  | 3 => 0xa88094912409402a8802a41252500944870518
  | 4 => 0x41529224820125515480024a4a4a009700ac0
  | 5 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffcfcf0ffccccc0fffcfcf0ffccccc0fffcfcf0ffccccc0fffcfcf0ffccccc0fffcfcf0ffccccc0fffcfcf0ffccccc0fffcfcf0ffccccc0fffcfcf0ffccccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x360088028000004a00a803c000000000b80141800000492263ea000042084000001580000068100111800064e1a1e400035200000000139d002c60500a8000001c00000600004000000004c00e0058022000000012000000000002000608000000c000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xd001514c0000000070d4000010200000000000004000b800cc00480108008c00007400dc94b408f4540100000000a954c400001c0000006000355c00900120e830fcf024b07c0088000018010cbc04140000000000013569400000015928002ca400a0011130011c0c5c0000007828c0e5452c380000013c00011914680000ecd9612400000000008504000064e000980000000000005138004cac0000000000016400005800c800009c6cf8443d488000000a02000a0200040000000400040200000a000c180e04020600001403765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x498522000406b9a99cc24216a0400a38002c02078ca82015670650003493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc05000080001885496010631c22a6b008310e05635885150308b1ac028a81885896014540
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
  | 4 => packedAt s1K4 (2697+((h/30+packedAt s1K4 (2457+(h % 30)*8) 8) % 176)*8) 8
  | 3 => packedAt s1K3 (990+((h/8+packedAt s1K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s1K2 (249+((h/1+packedAt s1K2 (245+(h % 1)*4) 4) % 13)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 2 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 3 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 4 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 5 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 2 => 0x24448c080c88910601209086c832244c221c92
  | 3 => 0xa88094912409402a8802a41252500944870518
  | 4 => 0x41529224820125515480024a4a4a009700ac0
  | 5 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0fffafaf0ffaaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
def s2K6 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa714aa67ac10062218e5a402e00042020001a4a83021882006006fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa0105800040d0000c00000e82c18050080006000083002340000800000080c00071801c2003008183601be41ccaf50732be40ccaf50332bd438caf90a32df328cbbcca32be418caf50632be408caf50232ef324cb78c932bf414caf10532bf404caf10132be430caf90832df320cbb8c832dd320cbb4c832cd320caf90432f6410cad90432bd410cbd50432b5410caf90032fa400cae90032bd400cbe50032b9400caf90b31bd42cc77ccb31dd32cc6f90331bd40cc6f50e31be428c6f50a31be418c77cc631f7318c6f90231bd408c6fd0931bc424c77cc931dd324c7dcc531de314c6fd0131bc404c6f90c31be420c7b90831ae420c6f50831ed420c6b50831be410c77cc431f6310c774c431f5310c754c431be400c7e90031ba400c6f50031f9400c6e50031bf43c86f90f21bd43c86f10f21ee32c87b4cb21be40c86f50321bf43886f90e21bd43886f10e21bd42886f90621f631887d4c621ef21887dc8621be40886f50221bf43486f90d21bd43486f10d21ee32487b4c921f631487d4c521f721487b88521bf40486f10121bf43086f90c21de43086790c21bd43087750c219d43086f10c21be42086f90421ef21087d88421ed21087d48421e521086f90021fa40086e90021bd40087e50021b940086f90b30bd42cc37ccb30dd32cc2f90730bd41cc37cc730dd31cc2f50e30be428c2f50a30be418c2f50630be408c37cc230fb308c2fd0930bc424c37cc930dd324c2fd0530bc414c37cc530dd314c3ecc130de304c2f90c30be420c3b90830ae420c2f50830ed420c2b50830be410c3d90430b6410c2f50430f5410c2d50430be400c37cc030fa300c374c030f9300c364c030bf43c82f90f20bd43c82f10f20ee32c83b4cb20be41c82f50720ef21c83b48720bf43882f90e20bd43882f10e20bd42882f90620bd41882f90220fa30883e4c220ef20883ec8220bf43482f90d20bd43482f10d20ee32483b4c920bf41482f10520ef21483b48520fa30483e4c120fb20483b88120bf43082f90c20de43082790c20bd43083750c209d43082f10c20be42082f90420f641082d90420bd41083d50420b541082f90020ef20083e88020ed20083e48020e920082fd0f10be43c42f50f10bc43c42fd0b10be42c42f50b10bc42c43d8c710f531c43d88710f521c42fd0e10be43842f50e10bc43842fd0a10be42842f50a10bc42842f50610be40843e8c210f930843e88210f920843dc4210fb10842fd0d10be43442f50d10bc43442fd0910be42442f50910bc42443d8c510f531443d88510f521443e8c110f930443e88110f920443ec4110f610442fd0c10be43043790c109e43042f50c10dd43042750c10bc43042fd0810be42043b90810ae42042f50810ed42042b50810bc42042f90410be40043dc4010fa10043d44010f910043c44010
  | 1 => 0x302f9ea001908f9d665224841062b008378da6ca0a352082e212660005710c968942c066001802785c810042107e280560000c000026a910000001624252978151501e93800060468c400036859ca14800000007482e370d8938ae4c122730a65f120491b6518000005e2f0707980000244498007e94200000510aa73a3440956018c28a0cc4280000000349f800000580000000a32152169e07b0e400000388000022e128007200000000000005c8a80002c00220000001a8005d800001888e9f21a0006b8805a98e78a0c45892589fc86800058fc7f9d0078e63c86e229a27004462918041ac809bc1315a8193a7d230000fe790005b80000000000001b1a400154659a0219a86e874679be5f80057872760b68ca0e0e8b44b2543412a9183c948fa530f6121046d14006148470c025a1e5e826929ee1900e64846000004001200000188ce4396600128209c4002180011e0a9d45c000001b8238886696c0013200000698b23aa56538009300000000560008f200000a2070c63b800000002625000226000002904e000ba082149022c4b8ca8a934631080a168001b07da385d0d6001c21e07c2709a888243c00096000108006100038000000408713e921121d9f03b05077986068383d1da00000671c63a0000c9e85913c0003e001820d00008814001144d80077000230003e23624000010b4060702010020000004061f01010000200000040d050181603000180004158280200018280208000003002000000801048080005000f4081100818000100020060001000
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x63b13150031c898a8018ce94043c8672a021e438c434cb219d2808710ce54043887288698c433b5050d219c2828690ce9404348672a021a432c544c921c621a6490d91453248668a898a4394434c521b22926290f14c9314863ca6202431d53101219d2868610ce543430863aa9218431e5310c21972908610cd9444308674a021843395010c21c6a1e4210e550e21086caa5108432f5448421c6a1a4210cdd51210872a8690843675448421d3aa24210e9d0d210878c8690843a54348421e2a1a4210e150d21087348720043994390021f090c8010e9485400873486a0043994350021f090a8010eac85400876442a0043a92150021d890a8010e8485400866ca221261355110930c6212649856141324c25ca420a612d5210530ca20a629856141314c34c8520861a54290430d3212821869509410c31a85980619541cc030aca9c60186a50a300c36283180611f544c030c6a12601865505300c276a898061a9424c030d8a0a601856d51300c336a898061ca424c030cca12601872509300c3128498061d2414c030cca0a601874505300c3228298061365110f209aa8887906310d32c826ca221c41355110e20cc21a61104dd454348268a2a1a41365110d209aa8886904b1513248318869924168504c9208f29882904754c41483488290a416850485209c2a260906610d30482d0a498241c9324c1209b28e86104d547430823aa9218411e5310c209729086104d944430826aa2218413a5010c20cb21c82106550e410832c86a0841954350420c6a1e40106950720083328710041695288020d8a0c40104bd51200831a8690041a541480209daa240106650d200836282900416b5448020d5aa240106ad0d20083948690041a94348020e4a1a40106250d20083c48290041a94148020f0a0a401068505200825ca421e212d5210f108f29885884754c42c43288698e21a442487109729087084b548438423ca6214211d5310a10cc21a61086a109208425ea4a1a212c5250d109729086884b548434423ea6a12211c53509108f29884884754c4244268a898a2194434c510b828262884d15121443488490a217050485109c2a260886610d30442e0a298221d1314c1109c2a240886a10920442e0a290221e121481109729686084b54b430423aa9218211e5310c109729086084b548430426ca2218213a5010c108f29e84084754f420425aa9210218e4390810c6a1c84086390d420431a86a10211e53108108ea9884084b948420426ca2210213a5010810caa1e20086950b1004272a908021994384010d4a1420085c546100426ea888021954344010d2a1220084ed5110043328688021a94244010b9aa220086cd5110043668688021d24344010d8a1a20087450d10043228688021b34244010f121220086c50910043c28488021a14244010
  | 1 => 0xd0003797c0020e001d2198008692e309be768187a0ce841640f9e45714c50198210a6770703a984410b646844890ee0019000212729a8288fc4902a429622e092270083e0fa148004a8004e208071080020a16000340000000000000509827c960688000013e708004d00040800528003b1d87c000740043ca220f16e739e2881cc0698c1e1fe0e05c00046000008309e158be181886808a00000551b4000bc4e8403f9e63280000000001c40015e250006987c4d85e001fc380000018025a16000ac62800369d4000d400000001b25f8022385066800000e83d9a44503219068000000000040082619ea07800038762a80000000318b0222061a800000001500005806001d60013c3d0000002c460006ea1e638ae348e20015a4704c5e8000880000000000000999c0004e000007e0240000056000458000000c659507d800000001b12000000521107e8202d176511ac05000000002a00a0d8d6390dc000000010e8b000430a000000000cc0006e00000311320004a000000002e000005a9b88a1220a0000000000194001ae5e0c04180000072361567d000000007788c1894e852043c1667b9728a926261ec1e9127821c001c8001680012c0016c00218000ba048a42c8000c010218c81f91e80000169b6120428089089992518001d1aa269c0201703983a719bc4a17400000679520000000130001b00280400080001808000e0400205008000c000580400020500800010200810010000414020002c0003000000001000180c00018440c16018000003010001400008140000000000000018500400058244200010080000000000602000000603020000606010000c0300ce940414ca72a020a653651101329aa8880995354e320ca3ea8990652f544c832a7aa2641963d51320cb8a65208658d3250432e2992821965cc9410cb4c64a0865953250432d29928219614c9410cb926520065b24190032d8a0c8019634c9400cb9264a0065b24150032d8a0a801966cc9400cb5464a0065993250032d49928019624c9400ca74a021263395010931c62126498d5145324c65ca4202632d5210131c6a166218d554e310c74a85188631f544c431c6a126218cdd51310c74a849886357544c431cbaa26218f1909310c72a8498863c5424c431c2a126218ea90a400c7528520063d13190031ca98a8018ea909400c75284a0063d13150031cd98a8018ec8c5400c73262a
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x91c118c8b130f9e080a8e86948f1f06170d818389a0100d0e1f85910002800000188416800a1581031c9299809b9200001a109380181d889e879780209a8b8480151d000c190207051b001416000a8006080010e102110c081020a1c600002c480e04c94190032e04ca4150032e04c94150032a2580424c93194580514c931e05093190031e09093150031e05093150031a2580434cb21a4580434c621a2580434c92198580514c921a4580434c52198580524c521a1191324c521c1151324c521a85834348421a15924348421e050d2190021e090d2150021e050d2150021a1584424c93094584504c930a1588414c53092588504c530e050a414c030e0909414c030e0509414c030a1584434cb20a4584434c220a1584434c92098584504c920a158c41485209258c5048520a4584434c12098584524c120a2191324c120c2151324c120a85874348020a25924348020e050e4148020e090d4148020e050d4148020a1588434c710a158c4248710a2588434c210a258c4248210a1588434c51098588504c510a158c42485109458c5048510a2588434c11098588514c110a4191314c110c4151314c110a258c42481109458c5148110a81912148110c81512148110a858b4344010a45924344010a458f4244010a85924244010e050e4244010e090d4244010e050d4244010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 24
  | 4 => 302
  | 3 => 279
  | 2 => 66
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*4) 4
  | 5 => packedAt s2K5 (i*15) 15
  | 4 => packedAt s2K4 (i*26) 26
  | 3 => packedAt s2K3 (i*37) 37
  | 2 => packedAt s2K2 (i*48) 48
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (5+((h/1+packedAt s2K6 (4+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (400+((h/8+packedAt s2K5 (360+(h % 8)*5) 5) % 29)*6) 6
  | 4 => packedAt s2K4 (8752+((h/100+packedAt s2K4 (7852+(h % 100)*9) 9) % 399)*10) 10
  | 3 => packedAt s2K3 (11160+((h/93+packedAt s2K3 (10323+(h % 93)*9) 9) % 404)*10) 10
  | 2 => packedAt s2K2 (3322+((h/22+packedAt s2K2 (3168+(h % 22)*7) 7) % 80)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffdfd273c777b0cf
  | 1 => 0xffffffffffffffffffffffffefe39cf87bd333
  | 3 => 0x77fc1f3f83ec3c
  | 4 => 0x7bffe03ffc0fc0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffa0448401108045
  | 1 => 0x10882108210112
  | 3 => 0x9014052020428
  | 4 => 0x6000aa4400a80
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 27 s2Pos s2Neg, 0xffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88ffeeee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5ca2a1e00c80227809d580010b0060b221024d9040bc51a1c9c9a646003805a0108352ac29c50b89243e106001a940150c14000300b082010a0f8d5005ff43fe43fd43fc43ff42fe42be42fd42fc42bc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x21006763a948de00000001400000d0002241100b83a000700000000345e700014c000027998000000000008000000d26d001e83a3900000b64a32000ba7300000c64c000000010000cc0000001d00c57000001212258905800000009a002a0ec00003e000d4000000026491b8001c5f1900000611e000002a30104dc003b8000a3f218d4000000000a200389e4d6163c000fa653f800fc3833a14aa000000000830c00000000c800000000120b21e340009c0f4318800460002c00000b8006c1a2811cd8270d8000000148b4462e000000001000103e7200108000710850002b128f8b408228a0ac871e800b0003d8004c1106204001500000040000000000022000000018880605e000000000000000100000000100000a01070100030404010000000d02020002000c020100030600000905000003000200b7294876d5290ebca7215754e42cf29c859d5390a7ca5214f546429ea84855e5310abaa6215d94442baa88857a5010af2a0216794c42cea98853e5210b5ca4216d944429ea8885b55110a6aa2216e940429ea8085b95010a72a0214f953329eaa6659e54ccb3aa9996790b32ce216655d538cb5885194fd51329e2a265ac424cb3ea8996715132e7a9265cf424cb3c84996710932e6212658c424cabca6194f94b41cf996839d32d067aa1a0cf552419e292839f325073a64a0edd45419fa82833e541067ca918cf552319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321af29e435d53c879a6590cf952219eaa443b5418867ea890cf15121e699243b5414867ca810cf55021af298435d53086f4a010de540219f296819f32d033a65a04f547409eaa4813c525033e64a0674c9409fa8a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184fd53209e2a6415e53c82baa790734cb209f2a4413d548837281104fd51209e2a241cd324837280904f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa88857d4d10ae29a213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x280260000a000000016116a73c848071c54b010c00000120000d56600110050da35c013314a80e995e01103340010c000042c540000000c090f52900000000f97007002800000008308040100a043842608100a358e5210b165354442c554d5110b315194042c694d5010b195354042cc9455010b315154042a558442cca996010b32a9584428caa96010a32a9584424caa96010932a3993524ca1e6590932a398a424ca1e6510932a5584424ca996010932b1584424cac96010932a3994424cb0e6510932e1984424ca8d6110932e1584424ca856110932e2980424ca8d6010932e2580424ca8960109328e580525070c524c9418e58054c870c544cb21c315132486346550521e14c941486356114940c314932502356115320c315132c830c544c9208e195404838932501208b189544424d6214d10d454d10043615244010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2004101c654182a1a05866010932d04c2b00849968161580424ca84b80a499283425c0544cb21c08ca9928290d05711493250282b88a899641821953250120
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
  | 4 => packedAt s3K4 (4032+((h/45+packedAt s3K4 (3672+(h % 45)*8) 8) % 238)*9) 9
  | 3 => packedAt s3K3 (2012+((h/16+packedAt s3K3 (1900+(h % 16)*7) 7) % 80)*7) 7
  | 2 => packedAt s3K2 (453+((h/3+packedAt s3K2 (441+(h % 3)*4) 4) % 11)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1e3f878fc7f8fe3f1c71f1c1e3f0fe3f0d34cf
  | 1 => 0x1fc7f80ff8ff1fc7e07e3e01fc7f0fc7323b33
  | 2 => 0xe007fff3ff001ff8ff803ffe3f800ff8c3cc3c
  | 4 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4300a010422108400810504840904222051045
  | 1 => 0x84210220904030084022221084240504122112
  | 2 => 0x921101001244012480048429022890404c28
  | 4 => 0x890554a24900492b5448024324aa090e80e80
  | 5 => 0xd124660836e49924da793939000cc126bfb000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefef8f8eeeee8e8fefef8f8eeeee8e8fefef8f8eeeee8e8fefef8f8eeeee8e8fefef8f8eeeee8e8fefef8f8eeeee8e8fefef8f8eeeee8e8fefef8f8eeeee8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
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
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x4070c8a0ea0b1f069008d1c500002279195302c1064e74829001092a4c00d1300010a50a215801e25100006cb8c00040004080007045000040ff43fe43fd43fc43ff42fe42ee42fd42ed42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x81bf40103f480206f50040fca00817f54cc2fca9985f55330be2a661de43cc3ba87985f94b30f7296616e52cc2faa5987b54b30b6a9661ee42cc3da859877ccb30f719661dd32cc3da6598734cb30bf28e617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c617e528c2faa5187b90a30f6a1461ee328c3da65185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c3dc84987b50930ef99261ee324c3ba64987b4c930e6992617f514c2f8a29877cc530ee98a61fa404c3f280987ecc130ef182617f540c2fca8186f950309f2a0617d540c37aa8184f55030be2a0617e530c2fca4187b94830b7290617d520c3daa4185b54830f721061ed420c3dc64187b4c830bf28861f6510c2eca2185f54430faa886175510c2fca01877cc030fd18061dd300c3f260185fd5320bf2a6417d54c82f8a9905fd4f20bf29e417d53c82f8a7907b90b20f6a1641ee32c83da65905f94720bea8e41ef21c83da43905fd5220bf2a4417d54882f8a9105fd4e20bf29c417d53882f8a7105f54a20f721441ed42883dc65107b4ca20bf28c417d51883dc43107b08620bf28441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20bf29a417d53482f8a6907b90920f6a1241ee32483da64905fd4520be28a41ef21483da42907ec8120f7102417f54082fca8106f950209f2a0417d540837aa8104f55020be2a0417f53082fca6107794c20af298417d53083baa6105754c20be298417e52083dc84107b50820f719041ed32082fca2107d94420bb288417d51083eaa2105d54420f710841ec21082fca0107bc8020fd10041ed20083f240105fd5310bf2a6217d54c42f8a9885fd4f10bf29e217d53c42f8a7885fd4b10bf296217d52c42f8a5887b90b10f6a1621ee32c43da65887d90710faa0e21f631c43ea63887d88710fa90e217f54842fca9085f55210be2a4217f53842fca7085f54e10be29c217f52842fca5085f54a10be29421ee42843da85087b8ca10f6994217d51842fca1087e90210fca0421fa30843f261087e88210fc90421f710843f621085fd5110bf2a2217d54442f8a8885fd4d10bf29a217d53442f8a6885fd4910f7a92216f52442fca4885f54910be29221ec52442d8a4887b90910f6a1221ee32443da64887d90510faa0a21f631443ea62887d88510fa90a21fa40443f280887e8c110fc98221fa20443f240887ec4110fb082217f54042fca8086f950109f2a0217d540437aa8084f55010be2a0217f53042fca6087794c10af298217d53043baa6085754c10be298217f52042fca4087b94810b7290217d52043daa4085b54810be29021ee42043da84087b8c810f6990217e51042fca0087dc4010fd08021f510043f220087c44010
  | 1 => 0xe52906faa520fb90a41f6a1483ee32907da6520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077e84a0fb90941dea1283ed425075a84a0fb8c941f699283f7415077c82a0dfd4141be282837e54106fca620f794c41af298837d53107baa620d754c41bf29083ee52106dca420df54841f6a90836d52107dc8420fb50841f719083ed32106fca220efd0441fb20883bd41107ea8220df94041fd280837a50106faa020fe54041bca80837f54cc6fca998df55331be2a663de43cc7ba8798df94b31f7296636e52cc6faa598fb54b31b6a9663ee42cc7da8598f7ccb31f719663dd32cc7da6598f34cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718df94a31bea9463ee428c7da8518fb8ca31f6994637e518c7ec8318fd50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131ef21a63dd434c6fea498df14931f721263ed424c7be6498fb8c931ee99263ed324c79a6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c6fca418fb94831b7290637d520c7daa418db54831f721063ed420c7dc6418fb4c831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb90b21f6a1643ee32c87da6590df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887dc8510fb50a21f719443ed32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fb90921f6a1243ee32487da6490fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40f7296816e52d02faa5a07b54b40b6a9681bf42d03dc85a06f50b40f6a1681ad42d03dc65a07b4cb40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40bea9481ee42903da85207b8ca40f6994817e51902faa3205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940dfa1281ee425037a84a07b50940d6a1281ee32503da64a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40bf29081ee52102dca4205f54840f6a90816d52103dc84207b50840f719081ed32102fca2207d94440bb288817d51103eaa2205d54440bf28
  | 2 => 0x80040100000500200000801054000000060040100201100200c01003002000020030000000000a0120000180e00000000801006008058000000000d80f0020040280000e00001000000008018040000140080100c00400801bf29687ee52d0edca5a1df54b43f6a96876d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521fb94a43b7294877d5290fdaa521db54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fb94943f6a92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85be43d0b7887a15f94742bea8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84856d5490bdea7217b94e42e729c85ed5390adaa7217354e42a6a9c85ec5390bde87217b90e42f6a1c85ec4390bdea3217b94642f6a8c85ec5190bdea1217b94242f6a8485ec5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142f7aa285af5450bdea6a15bd4d42f729a85ed5350bd8a6a17bd0d42f721a85ae4350bda86a17b10d42d621a85ef5150bdca2a17b54542f628a85ef5050bdca0a17b54142f6282857e5410afca6215f54c42bf290856e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997710f32f721665ed42ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32f7a1465ee428cbda85197b10a32ef99465ef328cafca3195f54632bf284657d508cbdea9195bd5232f72a465ae548cbdaa9195b55232d6aa4652d548cbd8a9195b54e32f7a1c65ee438cbda87197b10e32f7a8c65ee518cbdaa3197b14632f7a8465ee508cbdaa1197b14232bfaa2657e544cafaa8995f15132efa1a65dc434cbde84997b90932f6a1265ec424cbde6499778c932bfa8a657c514cafea0995f14132f7aa2656f544cbdca8997b55132b6aa265ec544cbdea69973d4d32f7a1a65cf434cbdc86997b50d32f621a65cc434cbdea2997b94532f6a8a65ec514cbdea0997b94132f6a8265ec504cafea8195f95032beaa0657c540cafca6195f94832b729065ee420cbda841977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41f7296836e52d06faa5a0fb54b41b6a9683bf42d07dc85a0ef50b41f6a1683ad42d07dc65a0fb4cb41bf286837d50d06faa920df94e41bea9c837
  | 3 => 0xc697e15800000167a1a4fa5c400000000aed318001240000000065c38055847000d1cdc80061e15400000000001a30000003b0f38000bcd30a506b0005eccd80000090d89af3106c84629b65a2000002746d6000000483bc001733643046b40d0eb2080010e800000d8c6e800512ce01000057a934000282060011e9a221c9d4979fe0004f8408943d2000001664042b1283240360000000000082c001cf19e000001320005d4f8b6030e0000f8000008586a003318c2000000518d9800000000d840007048c580002cd0d8b800028f1f86ccc6af12fc13ce48aa2ca8c8f80433845450814b04245c922f542255c92aeb2d2000e50cc62ccf4b52950001487d25200c759ab0410b08d40010b080001979f534e0000b20643e925270cb142d7c44aca07059daf23b00067077800274a6501b57618138c50460cc8d8cd0004744590080032a00000000000764eb95c0000008a3090005383b0e1000a70001342aa001690230260000024a3260c9508f42fe0000030720c000000003d81bc002f94100009b9190000017a0000000004cabe5b6000918f92bac015310814e5e914970000640d58de5a8c046cb4123c2e00000000000000000000000002a03d40000000020200142800000000000004585dd929e2186d006a8f228c5655fa5911c000fb2204606dd792ac00023ca61df2420019189a0e602c9f85959c5b52a929094000e709100085d8d89d4b80015d000000ca00000003abfd6a800000000000ad0005001531f5082100cb45000d54000a05721919a0224c83d5220000003f8968e56b62c0a9ae263c1f9b62c14da000a481c234af0002c314868d4ea696b2a28ee0000000d8ab19d1662707423c436895b800006044ce288b5b2000000004a60000030a2c2d3cb2205048ab94d9961f6000fd9c800007800298000a5803ad816e000001ba26a0a400173240408000000005e0ad0bb0e22d99d07f1506d10a0056d0c08958008070000180480a0000080280100801c0180300401402800012000050010840000000100203c0100000802800001000000010000080040300700000801005000000000020000040000300400c00000000004058000060180100000001c03000002000010020020080000500200c0000400000000000000010018010020200000600601c0000100a00404001002008058020060100380a006028000000020200480600a004000000040000180701c02c010000000180180300000c00000000010010010040100700401401c04801000000000000000040801d00a00001006004000050050000280000b0120000f805022008000030020180100000000400004008034058000020600381400c000028000000040180200400800005008000048000180180080601000004801018000030020040a4090020000180000
  | 4 => 0x57568449400ce000b7d8c172008000451220a0ba8a78d0666cf057a332d07902d0000005113f3030000018c80000000195b6a4bc6a4000002f2001002e40ce0015528d000000000000008e4011da4c454000000000000000bf000798000565440010c0f05da5217e8000000000024122a0cc0000021ea0400000270740001bf50e37c712093deba03d0003700000000025400000000000d70531c0000000f41fd58c001458f61b4038000000006ed7b0000000e4000003081313d000000000a291b2dc51c0028e1d4000000004d80006e2a7000054002ec306000cb8002c6000000001368c58aa940000004f000000cfc00000000679ae8b46884248680006e0019aa6865a00139219028d343a16f27a47c3ca832d60004c25a18c8b90787830c8bd0f0006869dd2132c0ae9c02210c66e620fd045000000c285d38e93d60000200000000001520005e800000c396e00009691c0024014662c772a5000000001910003ccad800000b1c000000ea00132800258a7858a6b00046148000000638003270000011200000030126000556980e307c6dc2b821367616000000005520f18baa8172135b7800000bdc88000000000000be0001dd93000000000082223d60009d86a000000318004be8a060b505ae7c87f86d2ecdcc7b808118c1099800672000000005983b40c2f866003c00351188db5a402767c0bc2885c3ee0008e0004468d15b22b3c60016f0004089fc88b53100b9c000000f61c971a45190b240bab74f64b800000000000001a860c208002d0638a7c0000044c334000610000000000055e24ccf800000780e9b2900000000000000d94001d2000214000004d4000d0800000000d00000000005d00005a288001a5194b2138a56000000d21943f825c000d601a000c009534c000002da3823e00011d04a0002da6f000000003524f0390c9000000000f9b4e360150000005e031d5800001857ce61cd0be001ac1af3642f0001dd000d898814104c6b8349be0007e0738000000014916231e0f400000000000000001cc6d444000000710000d10567519b087000001098004b60001a83e4a8a90fcb5a3dc000001bd4cc000d8a0e496258d60a51d29443020c0ca5788513c6849b80023813e760008003dac74000004ba000003110a6534000f12a8b087ea3f0d0bb933a216408dd308313120b0001db24ccc8f294226281d6eb122a49f09b0b26d2000000001b0b15432e9000ab400034000b2c000004e6235168492869210e2e54149d89cad361a8f85a8122fa34cd529a56a0014b83a1c641c372fa5aca09092b200035d62000000000001281b6cec002fe10ca20939d1012001069bc0c489c64974000604000001200003e8003aa0000030500000158afb000415b89ff2d8c89b92153c2000611f4332cc5aa22a05cd2c002ef2f8b8595000
  | 5 => 0x3860294880002272d599304b00ed5c1986940015180007ec50003495263493ca
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x528425e6314a109758c52842cd6390a10cb951428432d5450a10ab592328434e534ca10d354d32843a94250210f24c9308426e62951109b58a544425f63551109718d544426f62551109b189544425e63151109758c544426e62151109b588544426e6294d109b58a534423f6454d108f191534426f6254d109b189534423e6414d108f590534426e6214d109b588534426d64d49109b58f524426e62949108f990524423d64149109798c524425d63149109b99452442ad6414910b358c524432e64149109b590524432d64149108b590524434e63149109b58c524434d63149109358c52443656114910da580524426e65909109b19642442cd63909109b995424426c6550910cb951424432d54509109b996324426c658c910ab592324426e654c9109b195324434e534c910d354d32442746550510e950941442f060505109d19531443c5324c510bc181314436452885109d19521442f060485109e19540443a94250110bc18540443b141501109e19530443c9324c110bc18530443d1314c110da14a20443e221881109e19520442f06148110f8485204425e63d50109758f540426e62d50109b58b540426e62950109b58a540423d6595010cb98a540432d6295010cb989540432d62550108f990540425e63150109758c540426e62150109b588540427661150109e980540423e64d4c108f593530426e62d4c109b58b530426e6294c109b58a530425d6594c10c7952530431d5494c10d398a530434d6294c10c7951530431d5454c10d3989530434d6254c108f990530423d6414c109798c530426e6214c109b58853042766114c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d53948109b592520426d6394810cb951520432d5454810d394d520434d53548109bd91520426f63548108f990520423d64148109798c520425d63148109b988520427661148109e980520426f65908109b596420432e5490810cb55242042cd6390810d394e420434d53908109bd95420426d6550810cb951420432d5450810d394d420434d53508109bd96320426d658c810ab592320432e548c810cb552320434e538c810d354e320426f654c8109b595320432e544c810cb551320434e534c810d354d320433554c4010d554f100436552c40109e59610043395484010d654e10043695284010bc58610042776544010cd55110043555344010d9549100427b6544010ce55110043595344010da54910042f36544010dcd9510043735444010ec95110043715444010ec55110043315444010dcd4d10043d25344010dc54d10043d15344010d454d10043e36244010f818910043735244010f894910043715244010f854910043615244010f890910043e14244010f88c910043e13244010
  | 1 => 0xc26d6494830cb951520c32d54548309bd91520c26f65908309b596420c32e5490830cb552420c2cd63908309bd95420c26d6550830cb951420c32d54508309b596320c2ad648c830cb952320c32d548c8309bd95320c32e544c830cb551320c34e534c830cd952510c3355494430d994a510c3655294430d990a510c3654294430d98ca510c3653294430cd951510c3355454430d9949510c3655254430d9909510c3654254430d98c9510c3653254430c7553300c34d52cc030d5547300c339548c030dc546300c25f654c030c7551300c34d524c030d5545300c27b654c030ce551300c3ca324c030dc545300c25e63d53209758f54c823e64d4f208f59353c832d5490b20b358e42c832f5450b20ab59232c834d538cb20d3d4d32c825e63152209758c548827661152209d584548823e6414e208f59053882766114e209d58453882cd6390a20cb951428832d5450a20ab592328834e534ca20d354d32882ad6408620b358c21882e960086209b58a544826e62151209b58a534826e6214d20b358e424826c6550920cbd5142482ad648c9209b195324834f534c9208f990514823d64145209798c514825d63145209b997214825e63d50209758f540827661d50209d587540823d6595020cb98a540826d6255020cb989540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20d398a530826d6254c20c7951530831d5454c20d3989530823e6414c208f590530825e6314c209b98853082766114c209d584530826d6590820cb55242082cd6390820d394e420834d5390820cb951420832d5450820d394d420834d53508209b59632082ad648c820cb952320832d548c820d354e320832e544c820cb551320834e534c820d354d32083365494420cd55251083565394420d554e51083664294420d950a51083663294420d94ca51083365454420cd55151083565354420d554d51083664254420d950951083663254420d94c9510826d6588420cb552210834d5388420d954621082ad6408420cb55021082cd6308420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200826e62953109b58a54c425e63153109758c54c426e62153109b58854c426e6294f109b58a53c423e6414f108f59053c426e6214f109b58853c423e6414b108f59052c425e6314b109758c52c42cd6390b10cb95142c432d5450b10ab59232c434e534cb10d354d32c43a54250710f14c931c426e62952109b58a548425e63152109758c548426e62152109b588548426e6294e109b58a538423e6414e108f590538426e6214e109b588538423e6414a108f59
  | 2 => 0x6394b409358e52d026f6354b40b358e42d032e5250b40abd9542d032f6550b40abd8d42d032e5350b409bd9632d026d658cb40ab59232d026f654cb409b59532d02ad644cb40e3d0d32d032d4254740ab58b41d032d52d0740cb54941d026e6294e409b58a53902cd6390a40ab592329034e534ca40d354d329026f62546409b189519026e6214d409b58853502766114d409d58453502ad62d0d40c714d43502ad6490940b358e42502b86050940abd8d425032c5350940ead8142503a86050940ab59232502ad644c940d3d4d325034c534c940e3d0d325032d42d45409798c515025d63145409b988515026d6214540ab58b41503a942d01409b98a531026d6294c40d398a531034d6294c40d3989531034d6254c40d394e521034d53948409b58e521034e5354840d354d521026f63548409b59642102cd6390840d394e421034d53908409bd95421032e5450840d394d421034d53508409bd96321026d658c840ab592321034e538c840d354e321026f654c8409b595321034e534c840d354d32103565394440d554e51103665294440d954a51103664294440d950a51103663294440d94ca51103565354440d554d51103665254440d954951103664254440d950951103663254440d94c9511031d53d0040cb54b401033551d0040d654e401037151900408fd95401031d5350040cb549401033551500409ed9540103595350040ea909401037151500409b98b54cc26d62d53309b98a54cc26d62953309b98854cc26d62153309d98454cc2756115330b358a43cc31c5450f308f99252cc23d6494b30ab59252cc32e6494b309b59252cc32d6494b308b59252cc26f6454b309bd9642cc26d6590b30b358e42cc26f6550b309b59542cc32f5450b30cb15142cc38e4350b30ab59232cc34e524cb30b3d9532cc34f654cb30b3d9132cc2cd644cb30d395132cc34c544cb30d34c951cc2cd62cc730d354b31cc34d524c7309b98a548c26d62952309b988548c26d62152309d984548c2756115230b358e428c32e5450a30cb551428c2ad648ca309bd89518c26c6254630ea509408c26e62951309b58a544c26e62151309b588544c27661151309d584544c2cd6290d3097195434c31c5450d30b358e424c32f5450930cb151424c38e4350930ab592324c2cd638c930b6181324c2cf644c930b3591324c34e544c930d3151324c3cb604c930f2181324c34d32d45308f990514c23d64145309b988514c26d6214530b358b314c3c932901309e195404c3994350130ea509404c3c93250130f24cb304c26e62d50309b58b540c27661d50309d587540c26e62950309b58a540c23d6595030cb98a540c32d6295030cb989540c32d62550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c32e5494830cb552520
  | 3 => 0x131b358a434c65c6550d31c7151434c6cd6390931cbd51424c72c5450931e390d424c6ad648c931b358e324c6d4614c931b3d91324c6cd644c931d3951324c74c544c931f1d85324c7c4614c931f14ca414c6746550531e550d414c7a54250531f14c9414c7c532cc531d34cb504c63e64141318f590504c66e62141319b588504c66e62d50319b58b540c67a60d50319e583540c66e62950319b58a540c63d6595031cb98a540c72d6295031cb989540c72d62550318f990540c65e63150319b988540c66d62150319d984540c67a60150319e580540c72e5494831cb552520c66d6494831cb951520c72d54548319bd91520c66f65908319b596420c72e5490831cb552420c6cd63908319bd95420c66d6550831cb951420c72d54508319b596320c6ad648c831cb952320c72d548c8319bd95320c72e544c831cb551320c74e534c831c7553310c74d52cc431cd552310c65f654c431c7551310c74d524c4319dd95310c735544c431f18c9310c73a5494031ce552500c76a5294031da54a500c76a4294031da50a500c76a3294031da4ca500c73a5454031ce551500c76a5254031da549500c76a4254031da509500c76a3254031da4c9500c75b3154031dc8c5500c7593154031dc4c5500c65e63d53219758f54c863e64d4f218f59353c872d5490b21b358e42c872f5450b21ab59232c874d538cb21d3d4d32c865e63152219758c548867a60152219e580548863e6414e218f590538867a6014e219e58053886cd6390a21cb951428872d5450a21ab592328874e534ca21d354d328866d62951219b58a53486cd63909219b195424872f5450921ab592324866c654c921d3d4d324863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540872e62550218f990540865e63150219758c540866e62150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530874e6294c21c7951530871d5454c21d3989530863e6414c218f590530865e6314c219b988530867a6014c219e580530866d6590821cb55242086cd6390821d394e420874d5390821cb951420872d5450821d394d420874d53508219b59632086ad648c821cb952320872d548c821d354e320872e544c821cb551320874e534c821d354d320872d54c8421d354f210866f6548421cb551210874d53484219dd95210873a5494021ce552500875a5394021d654e500876a4294021da50a500876a3294021da4ca500873a5454021ce551500875a5354021d654d500876a4254021da509500876a3254021da4c9500876b2154021dc88550087692154021dc485500866e6294f409b58a53d02ad62d0f409798e52d025d6394b40b358e52d034e6394b409b58e52d034d
  | 4 => 0x3994434cace6410d32e3990434cb4f5410d32e3950434cb4d5410d32e3550434cb0d5410d32f1984434cacd6110d32f1584434cac56110d32f2980434cacd6010d32f2580434cac96010d32ab990514caad6414532ba980514cae96014532ab990504caad6414132b9984504cae561141329798f540ca6e62d50329b988540ca7661150329d584540ca7a60150329e580540ca3e64948328f592520cb2e64948329b592520cb2d64948328b592520ca6f65908329b596420cb2d5490832b358e420ca6f6550832cbd51420caad648c83297d95320cb4e524c8329bd95320ca6e6294f419b58a53d06ad62d0f419798e52d065d6394b41b358e52d074e6394b419b58e52d074d6394b419358e52d066f6354b41b358e42d072e5250b41abd9542d072f6550b41abd8d42d072e5350b419bd9632d066d658cb41ab59232d066f654cb419b59532d06ad644cb41e3d0d32d072d42543419b98a539066d6294e41b358e42906ad648ca41d394d329074d534ca419bd89509066c62542419b988535066d6214d419e98053506796014d41ab58b435071c5350d41ab59242506cd6390941ad18542506af6350941cb14d42507a76150941e918542506ad648c941ab591325074f534c941d314d325078f434c941e950b415072d42d41419798c505065d63141419b988505066d62141419b98a531066d6294c41d398a531074d6294c41d3989531074d6254c41d394e521074d53948419b58e521074e5354841d354d521066f63548419b59642106cd6390841d394e421074d53908419bd95421072e5450841d394d421074d53508419bd96321066d658c841ab592321074e538c841d354e321066f654c8419b595321074e534c841d354d321071d53d0441cb54b411075553904418fd95411071d5350441cb54941106776550441d554d41107a64250441d694e50107595394041da94a50107695294041da90a50107694294041da8ca50107693294041d694d50107595354041da94950107695254041da90950107694254041da8c950107693254041ced0550107724154041ce505501077141540419b98b54cc66d62d53319b98a54cc66d62953319b98854cc66d62153319e98054cc6796015331b358a43cc71c5450f318f99252cc63d6494b31ab59252cc72e6494b319b59252cc72d6494b318b59252cc66f6454b319bd9642cc66d6590b31b358e42cc66f6550b319b59542cc72f5450b31cb15142cc78e4350b31ab59232cc74e524cb31b3d9532cc74f654cb31b3d9132cc6cd644cb31d395132cc74c544cb31d34c950cc66e62952319b58a548c66e62152319b588548c67a60152319e580548c6cd6390a31cb951428c72d5450a31ab592328c7a542506319bd89508c66c62542319b98a544c66d62951319b988544c66d62151319e980544c6796015
  | 5 => 0x5190acd63d4642d354f5190b4d5394642d354d5190ace6314642b358c5190b4d5314642ba9805190ae96014642b398f5090acd63d4242d354f5090b4d5394242d354d5090ace6314242b358c5090b4d5314242b99845090ae56114242ab9884350ab56110d42ae5804350a9e63909429798c5150a5d63145429e9805150a7960145429798c5050a5d63141429d9845050a756114142b398f5450acd63d5142ab98f5450b8e63d5142a398f5450b8d63d5142ab5875450aad60d5142d354c5350a6e65d0d42d3d4e4350aae6390d42cbd4e4350b8f5390d42e314e4350aad6190d42ab5824350b4f5350d429b9944350b8d4310d42b99844350ae56110d42ba9804350ae96010d42ab9944350b2e6510d42ab98c4350b8e6310d42cbd4c4350b8e5310d42e354c4350ba66110d42ab5844350ba56110d42a95844350baa6010d42ab5804350ba96010d42aa5804350ace6314542b358c5150aea6014542ba5805150ace6314142b358c5050ae66114142b95845050b4e6394842d358e5210acd63908428fd954210b2e52508429bd954210a7661153329d58454cca7a60153329e58054ccace62d0f32c755043ccad56110f32b658043ccacd6390b32cb55142ccb8c4350b32cb98a548cb2e6255232cb189548cb2d54d0a32cb552428cb2e5450a32cb551428cb2d5410a32c7953328cb2d54cca32b358f548cb4d63d5232cbd91548cb2f6555232cbd8d548cb2d6355232cbd85548cb2e6155232cb585548cb2c6155232cbd81548cb2e6055232cb581548cb2c6055232cb550548cacd6315232cb553438cb2d5490e32cb551438cb2d5410e32e350c438cae66110e32b9584438caea6010e32ba580438caae64d4632ab593518cb2d54d4632cb552518cb2d5454632ab990518caad6414632cb550518caea6014632ba580518caae64d4232ab593508cb2d54d4232cb552508cb2d5454232ab990508caad6414232cb550508cae66114232b9584508ca6d629513297997434cb1d5410d32b3988434cad56110d32b6580434ca6e65d0932e310f424cace63909329b195424cb2f5450932cb151424cacc6350932e310d424ca6e6510932a7992324ca3e64145328f590514ca7a60145329e580514ca3e64141328f590504ca7661141329d584504cb4d63d5132b358e544cacf6355132cbd91544ca6f6355132d3d8d544ca6e6515132cb550544caae64d4d32ab593534cace64d4d32e3993534ca8e64d4d32e3593534cacd61d4d32b3583534ca6e65d0d32cbd53434cace65d0d32d3997434ca4e65d0d32b3197434cb4f54d0d32e3d53434cb4d54d0d32e3153434cacd61d0d32b3583434ca6e6590d32cb552434cace6390d329b595434cb2f5450d329b994434cb2d5410d32e350c434cae66110d32b9584434caea6010d32ba580434cace6510d32d
  | 6 => 0xe9bc00181e0200000000101c0000300000600c00000000034000000000080780000e020000010060040280f0040140301a00a0000a00300200002001008028068000120100080200c0200080001409400000010034010040120000180200200c01002000000000010060000000504a0340100400c048030000000540200002a0000900e03a024000000080140100b030004018040080f80100200e0000000000a0100680c00e0001500100000801001000008018010000080400301e000000070000000800800200c050000020040280e0240140080001404000000000010050010020300300000c008010000140300200400a00c05001000008040060160140080000201c0000200001c0300100000800012004000040020000080001300000003001000010058100060640100f00a02001808020010008000340080180300000c000040020001a000002010008020000200200000a00001001002064000110080000200d002004010000040000c80b0000000280000a0040280000600004804010010058110020040080000e0040200e008000078030220a80100000a004010050000540880801600c010070000000680301200c0080900c0080002800000400803000008000010080080880300e020010000140200a0040320040a80400a048020000180040b00100200004805018020030000060080000200000c018000040600380200a00402002024000000030000000781102600400001002028020060040380380000e004050000020181180a00201c0780800005c040090060341580002803c01801012008030010180080b0020060140180800803401004002020020000000340c00002c028018030080040080000e00802800ab58b4390f4f4354a439b98b5150e6d62d45439b9885150e6d62145439e9805150e7960145439b98b5050e6d62d41439b9885050e6d62141439d9845050e756114143ab58b4310e9d6490c43b358a4310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43e39894310f8d6250c43e350e5210f8d4354843e550e5110f665294443d954a5110f1d4354443e550d5110f665254443d95495110f374354443d590d5110f354354443d550d5110f154354443e650e5010f6a5294043da54a5010f725194043dc5465010f1d4354043e650d5010f6a5254043da5495010f725154043dc5455010f3b4354043d690d5010f394354043d650d5010f194354043ab98a43d0b1d5310f42ad58443d0ab96010f42d398a5390b4e6254e42d31895390b1e53d0a42d354f4290b4f6554e42d35915390b4f6154e42d39855390b4d6154e42d31855390b4f6054e42d39815390b4d6054e42d31815390b4d5314e42d354e4390b4d5350e42d354c4390b8d4310e42b99844390ae56110e42ba9804390ae96010e42b398f
  | 7 => 0x25b00012080012691f9a722ca1b9929fd00001b17385f2148000db9f51ab0001bf97295e91e06e98d1a301b84f19180000012f0001580bb88f9b71f715600000014480000000017c80028580012c0000e710f9ae8000878001960fc0000d98000af8000800e30b20000000000000000001e00000000859e9a808cc80000000010505f800000000000076a410000001692012ac81206900000028c0900002030000000000ed05b1629e300008ea5c8000002000001488d79da102a0202f1c30558391d0a6e93180000027400008700011400028299317fa83200a848de9ca04e16105390f19786011ca460849ca84b95988986c82200e00007d0000c08b128d0002618520000330c686fa8018c1a48000000000000002110339d020b1009dd87616b15909988e11aa1c181a5696ea2387900011a0000000300bf9ed10b1d58000000f703a15d10c83683f00023e1ba1e804b14c1b200019580020c849a480fe0060e797b82113b06e04d9eaa770000571068e080014b9e90000001b282b13d23300003292fa0b9cf05500000016e0d11fc000253a710679c20efa6a07e0a104c04a1df0c3aa792e27e8f58719f783091b88f07003986b8b91ac1c19be194a891f686c06aa889468d482a8cf8fb19a977a6a8960f98059542789410000f51eb1f0866a119e18362a82498610001ae22f0001782910a89662629a08d09190a1a4481d01025e87b0f10d58ce23a18609686f1bf2841c682d881a7c2a3801137aa209a9789999f48eb80017a2af0001509ad9678b992595e2280e50daa720a680007d8000001088000ef0000000000fd89500f00023a83423787400005c2868f629f00023982c8000b88f79349fe9491a38b480015c80000000024f96c1d414e8000000000f1a688001460000000cba289fd90a8000dd9cd000000000255a380000e68000000000000629a880000b0001840000a297e0000f880000009800016a16980029316d0fe9ea00020a2099e08001990000001a200000000013680005600021f28617e85d8000002640d31712169c98fa80000005427822d8ae10e14b28803200011308822b0c59b326d8000070a60001f4099000107a6210218793c88d17f02800e83ba3c0b18f2800000177275a99a4b00017d88608215d9f2065a2f807a921749b7912a248c50ab0958000001fa1a600000026f1442a000021280004180015288ca7e0d60ca07722a0b829805d1f800013a2afa0717c11c00012d93b9b0a3280001fa3d1a18aa009a76800000008a8b0000000228000b399898b80001e23884400000000000b80000001da4780003b1da9ef0b696511584d0000000002368ac29080000020384e991000048800000265a942470001799531bc883a6fa1725d9f19ee80000802f918140a2d0ba8519d8948078a0c25190821da651d697202
  | 8 => 0x6a0a00e216c9cd8c78b600022409e80000000016681c0a9a7b02409c1338708000000000000000000000000000001ce01980024c9ab90d99700016306489f8208000002018000032670ea24a96d8798001801618002438000468000000000001740890000001750b41aa9ad1b61f5960a50162151a3480000000019c8b00411db00000021000695c1811040ce8000528001280e4947a2c2561568be8002a28889fba2e8279100189b185c9ec17625420495521980397093f0a4196a30164154a0daad1d90978471c283ea5500a91481190d06d9719252818fd00c180a0590327ba79a4403f8ca8420001138fc80023c8c606425aa528000608000000001efa5f0dc25faae1b404008d9fb2090cf00000020ea820a089b0002088001ff94012300000000014584f80000d8be00029700419807a93e9d38fa02d19e8500930bd2108f000019396aa2a97698a27d23b2938cd9002188111361b01a2863877a9296584280022213500013d8002ad8000000000002662612571e7a898d6a690a79a4221911800000021a6d10606709180090b9b6a6799e2838450029dd05a893a2792b91ea299e61200000001a926c8002342201dc22905107c95103e1828599c80000002a60928000002648001b801ca870001a81c3a749d280027600000001a16b9ee2a08920e10000000000bf13e00013594e00024e0000480000001859aa0000001ba8909091cc80224d0dc80012b2949888f90000000bc8000e028ba390e39f28b28001b39b8a9912887e80014d80029a17d00d14520290a22599200021a2521830ec24921a9a78001cc1689a111600000000000000000012a8000000002a325995a1bd8738002a18000000002488000eb13824f0ed8000d200025087289a28d9589c78af02a05302e13fa1e240a6980027000013aa8126080003d80000000000019a26399c0001e2a0faa91228002270000000c714c8001b4a2102719f23b82b80526689e0000000000bda2e0001c51a0130164a1820524a1d18ff2a71f38c9a6c14aa87a3590c12106307329e2400f206193921393300907f85b91500018ca9500ca370910431bb0c91759d200005a1c4a59000000101a7d8002428cd0662a68b705900010382329e84c9f90379328462900df045aa10b30e60d88ee8000d700000018f2318000ada9c00000000000029d9e700011d8000000311d72530e5a1e8001ec9dc8000001f30000f30318868ea8f6a708002230a80000000d50ec8409880000ab98d8000000000001e400000019f80008401a80000000005e16f0000a31faa9f9012600000c00000ad28e12a0688048e98001188388001578000588d42718c824ba4588092c8239cb9178c28000000000ee2aa94280023f8b7a150e2a6e2078509d7a081bd24520d0b527a8000b0a1fa732321c41240751c7134000
  | 9 => 0x126016a040250699d522521780027798500021d20e0c20000001c5a351218001270dd00008ba9d1db9908832159e381f1e581ea2603824c00000017b15f80001387814180025b800194189843aa99849c6071241a6b1d30000a59cb0bb0ba0000128e411229ca960001a686d0a21430000000db12ea141570000358000c31eb83d15a9c0a9b08c1e4a969471398c10000c899b83a88aa58953a979311b114218b08280010e80019022280000000000007a0001249321558000000000001acaaa0000002958000001fe2739af95000002887207480014d0aca1b0000000000001f10000001a99058001b50650000000002aea680f09a514f9cf99d0352469048001d99c88000e19ed80014a1f882c08a1af05823e97aa989b915b85ea131ff0001821438a3aa4857aa40c4149a0f25813c160186910a4d9dfa1ca308cb15b00013700028a8aa8290000001c10dfa91aab9d11e8a8a272a850f41d80478d802995f11f1239a5a421e200025117903ca1224e9890a4909a6b80027900028f89d00012d2a599b00000025c00027f1638002161bb9308448191e11cea5782488b06807f0000371298f39870000f4a548258ff84901729a8fb8000d38c18000001f61279f0138862075970206800010aa500018a89da430000a900000000028f07c00012923123f06b0001170001b980025d0988000141731c90000002ab20a9670b58de000236085000000000000000000000000000263116a3d8d90bc0201e69520e91070da11d22089ba062190178e807b9fc82629b8548018e89f980004a8180268a70d2a8c92218f91b0159b5a7c9be8d18c483c2269839e525e0001951680f825a0cc19d9de89727a2ac27501500001480028e89f22b89400a0349c00569de1d498e2a880009480f8810001d601300009c91100018e94f2338d016f81627f8ae9198a50
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x205297590940102c4b9c84a0081c254e4250040e4484a8a80205157115143cc292b88a8a1661439d2524cb3091ae9b2a659850e74d9532cc2273b4a89966183590544cb30a8ae22a2659842d74189518c28ab88a8a1a61495c45450930932e830264984d171181324c306b20a899261515c4544c930b12e830264985c171181324c30c32a86a02618a1954250130c90ca9928098589744c9404c3072a2c72106183551639083085aed2a4641842d76552320c2a2b9c8528861495d23294430a8ae7212a218525748c9510c2a4bac6498061625d2324c030e12a9192601874232545300c28739ea8a1641439d3534cb2089ae7310a89042d749885348286b9cc52a041435ce6255020a1ae9314a61050d749895308306aa2c721041135da539082089aeca9c841042d769523208216bb2a91904183591538c820a8ae7214a210525748ca51082a2b9c84a8841495d23254420c1aa8b18421060d6454c2108312b22a2108419158d5108420c52a8b004210649535802108226b9cc52a6210b5d26294f1089ae7314a90842d7498a5384226b9cc52a2210b5d26294d1089ee6b26a48842f7458f5244306b24c629221839916314910c1ac8b18a488625645845244322b1ac2292218a5916014910c92c6b00a488661615805244226b98cb21221135cc6550910858ecaa2848850c735514244216ba0cb192210b5d0654c910898eca9a648850c7454d32442923aa84a0a21345cc60505109c2e43028288544754c93144258ba0c098a21385c8604c510962e830242884d17318121442943aa84a0221345cc61501109c2e430a8088548754c93044258ba0c298221385c8614c110962e830a40884d1731852044226b9cc52a021435ce6295010a1ae7312a80842d7498a5304286ba4c529821435d26254c1089ae7b22a40842d74d8d5204226b9ecb2102113dd56390810c1ca8b1c840860d5458e4204226bb4a721021135d9539081085ae9b2c640842f755923204216bb4a9190210b5d9548c810c1ac929c640860d6454e32042a8b9ea888021585cb5444010a62eb2a22008722725511004390b92a8880214c5d35344010ac2e5a9a20085517594d1004388aa4a688021c49515344010e22a8a9a20087427254d10043a0b92a688021c85536244010e82a7b1220085a1741891004390aa0c488021705cc6244010e82a6312200853174d4910042a8b9ea488021585d65244010e42a929220087415394910043912a2a488021c85515244010e84a6a9220087415354910042b13b2a488021581d95244010ac6e8a9220085637354910042b0bac8488021c85524244010b82e721220087415390910042b0baa8488021c85514244010e82a6a122008561758c910042d0ba46488021c85523244010e82a71922008561754c91004390aa26488021d054d3244010
  | 1 => 0x4350b1332ac221a85a198d6110d42c4ea6b0886a1686535844350b42a9ac221a85a85866010d42c54cab0086a168a635804350b5130ac021a85a85856010d42c56a6b0086a168a535804350b44a9ac021a85855516110f32c32a8b0087995857110d42ccac4b8086a1665435cc6155232c4ac230aa91952a70185548ca94b80c2aa465435cc6055232a4ce2302a91952571181548cb14b00c0aa465895526110e32c4aa8b08871968543584438cb14aa4c021c658a5516010e32d1286b00871962954980518cb14aa2c028c65895526114232c4aa8b08a11961554584434cb0caa2c021a65615c443d0932b12e021e84995857110d424cac4b8086a12650bdd95410d32c4aa8b08869968543584434cb14aa2c021a65a250d6010d32a1aeb2a0869944f76550434ca47bb2a821a6543dd95410d32c1eecaa0869970554984434cb06aa2c221a65919956110d32d0cc8b08869970554584434cb23aa2c221a65a19516110d32c8aa8b08869968554584434cb02aa2c221a65c25526010d32d82c3300869960d54580434cb2532ac021a65a29916010d32e12a8b0086996c261580434cb60b0ac021a6592d516010d32d14a8b00869964954580434cb44aa2c021a65825516010d32a1ce7aa2841950e74949320ca8739ca4a1683235cf6550b41a1ce7b2a85a0c4d73189509068cb80a6a1a83255cc6150941962e030a84a0d297014d42506c2b98c2a1283685c06150941c1ac829a64a0d497014d3250626bb2a72108383592538c841c1ac8a9c6420d257590941106c2b9c84a0883c154e4250441a92e7214a020d29748ca50106a4b9c84a80834a5d23254041e4484a0aa020d197015143cc694b80a8a1663439d2524cb3191ae9b2a6598d0e74d9532cc6273b4a89966383590544cb31a92e02a26598c2d74189508c68cb80a8a1a634a5c0545093192ae830a6498cd170185324c706b20a899263525c0544c931b0ae830a6498dc170185324c70a32a86a0a63891954250531c88ca9928298d85744c9414c7072a2c72106383551639083185aed2a46418c2d76552320c6a2bac6498863615d2324c431e0aa91926218d497390a500c694ba46528063525ce4254031a52e9192a018f42324c5500c68739ea8a1643439d3534cb21a1ae7314a810d0d739895408686ba4c529843435d26254c21c1aa8b1c8410c4d7694e4208626bb2a7210430b5da548c82185aecaa46410e0d6454e32086a4b9c85280434a5d23294021a92e7212a010d29748c9500868739ca4a1681235cf6550b40a1ce7b2a85a044d73189519028ab88a6a1a81265cc6050940962e230284a05257114d42502c4b98c0a1281685c46050940c1ac829a64a05457114d3250226bb2a72108183592538c840c1ac8a9c64205457390a5110292ba46528881515ce4254440a4ae9192a2
  | 2 => 0x8880e0000007c484a24404059400518bc000610009900000404000008517cee51000280d81409c00000000004495000000559040007f3cc00000ba0000016400000c62280037d66000ed3816a000003640b4d800001713d8000000056000000002e073520004f40000175450000011b0015700060094e100018138a9000000000008c000000011c773d42d000540016e32c0000000000000080025800000004ec00000345dc002b40000000000e62ac005000d00004000090009a000000000000c000000040cb20016418c241d087000000c000211270017800000001080000000400534000000000000001495cc00000002d574000000000015ceb0003a000e7000000000000000000000bc0000116000000010a078c4000002c4414a8710002e0000044c00000001281d430000000000000000000000006c00000a72d0000004900000000000003e00000000003fc000000000123530003e8005bc001e400000cd00000000000000000000000000000000000000000000000000564000008d001113f4000000000000000005c00000125144d5044000013a000c20000000000254f956c00020be13400168800000000000000000fd3e01d342e4c740000224001a08f0009f19c00000004bcbd0acb7000003f0001e0000005e030ef580bf098621e8004349312c000006b028002ec0000120000c53a017064000c44c390ca0000e548c8000004ac00058650003c0000000000000535156800142000000000000000000000006d000000000000128000002a81c00115000000000000000000000016b001433300000000000002c130550c0344830691d148f2358d33415f00004800038000000000000000000000000800000040000c008000481001002010000000600014010000100a0100c00000018000180000802000000080000000000000380402000000040000002000000000000e0202c00802010000200002800000060080200004018000080400000000180180c02800000040000e018020000401004000020000400000020020181e0000200000000040000200001235cb6550c43a1aeb3128621d0f755894310f82a1ca4a8887c150d5254443a4ae5a1aa221d457290d5110e8bb9286a8887c19c94354443e0ae4a1aa221f11435465010f84a1ca4a8087c250d5254043e228728aa021f11435455010e94b9686a8087525ca4354043a36e4a1aa021f0a7250d5010f84b9286a80878554d6110f42c32a6b0087a150d741855390b22b08c2a9c85529c06154e42a92e030aa72150d741815390aa3388c0a9c85515c46054e42c92c0302a721645539844390b22a9ac221c85a150d6110e42c92a73008721649535804390b44a1ac021c859254e6014642c92a6b00a321645539845090b22a9ac228485a150d6110d42d1286b0086a148f7654c
  | 3 => 0xc10ece3000000007e0c8003d0c30000000000238002cc0000000000ec45c0000000000050a00000000324003680000000000000402c1c843000f0000003880003d31018005780000000000dd000f10000017000274000000000000000900000053ca4408004149b000360000000000000660009400000001511200025c810a8a50000000000001260000059c910002200069000a80012e4dd550005d00012278860516d0e41316107574b60dc6442400468ce35c761a8001d5351b0004c855584564e07d00000538cf00020000000011807cac370001ed0e0000023000298db000000851c0a50f000a300070488150013f000000011e000331bd624b4444f0e900163001720000009c000014a51cd43e000000004b15a00153378e513c8b00000000005a519000ea491412bd6c5d86e00000000fb3f94b4cc923dc00000004e400000000000000000000000000000000000ae42c0047d29000000010600000000000d442284451180000000000000005b260820003d0000000000570000000000000000000000034
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x14000009e005c6803600000080000048007a1441400e4a2812a0668f882401019005800038000003a600000098300009c0002a000002241423524c00718000000000589000000002000c0070c005000400007c05745846154e42c41615c06154e42c09745806054e42c41715806054e42c05735846155232c21615c06155232c09735806055232c21715806055232e01545866010d32e01549856010d32e01545856010d32c09645c0534c9419058754e4250441b01839094154041c09645c0544cb31c09645c0544c931c04655d1325053190587552324c431b01848c93154031c05645c4534c9409098754e4250040b01839095150040c05645c4544cb30c05645c4544c930c08655d1325013090987552324c030b01848c9514c030905831d54250510905841d5324c510909831d54250110909841d5324c110b01839c95444010b01849c95344010d01545cc6244010d017454c6244010921841d95244010941831d9524401094183dd1524401092184dcd5244010d01545ce42440109418754e4244010921875523244010d017454e3244010
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
  | 4 => packedAt s5K4 (57326+((h/458+packedAt s5K4 (52288+(h % 458)*11) 11) % 1817)*12) 12
  | 3 => packedAt s5K3 (19723+((h/125+packedAt s5K3 (18473+(h % 125)*10) 10) % 799)*10) 10
  | 2 => packedAt s5K2 (2678+((h/14+packedAt s5K2 (2580+(h % 14)*7) 7) % 81)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xdfc3de38f3c7f3c7e3f30388fce3f3e3c134cf
  | 1 => 0xeffc1fc0fcf8fcf8fc7c1c0f1f3c7cfc42cb33
  | 2 => 0xcffe000ff00ff00ff8fe00fe03f80ffb30c3c
  | 3 => 0xf0ffffff0000ffff000ffff0003fff003c0fc0
  | 4 => 0xffffffffff0000000fffffffc000003ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4201100810080400008024009020001045
  | 1 => 0x40402200120010080040108042040004112
  | 2 => 0x73c881b44a924a92c01f206a42a90a9b330c28
  | 3 => 0x55108900a2480804925492000324a09140e80
  | 4 => 0xbaa2112080800a24924a924c928000122ba000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8ffeeeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x71697818e07898f81049a0016180b199e8009000a9e021c9893941f8000949a9d04000e800280001c0005831f11850c1d800390120000208a201b080b970f0d1512861586908d9b91000c800893190001861a10100040110a105c40000580090e18181037fd500bfe54037f5500bfc54037fd4c09fe53037f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe5201df9480dfd5201ff148077c5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd440d7f51017f9440dfd51005f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd400d7f5000ff9400dfd50005f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x22400eff9912002dfcc890003fd64480017eb22400eff1912002df8c89002fff544801dff2a2400bff55120077f8a890003ff63480017fb1a400dff98d20025fcc690003fd63480017eb1a400dff18d20025f8c69002fff534801bff29a400bff54d2006ff8a69003bff434801bff21a4000ff50d2006ff88690006ff6248007ffa924003ff9492001efca49000ffd5248007fe2924003df1492001ffe849000ffe4248007f72124003ff50920007da849000ffc4248007ff9924003ff8c92001fdc649000ffd3248001f69924003ff0c920007fec290002ff6148019ff30a4002bf98520007fac290033fc61480057e30a400bffd452005efea290033fe5148017fea8a4000df54520067f8a29003bff4148019ff20a4000ff50520067f88290037ff3148019ff18a4000ff4c520067f8629000fff2148007f790a4003ff8852001ffa4290003ed2148007fe10a4001bfd812000ffea0900077f5048003ff2824001fe9412000ffaa0900077d5048017fca824000de5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048007fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffe2090007fe1048003fd0824001ff04120057feca8802aff6544015ff32a2006bf99510056fcca8801a7e6544015feb2a200abf59510006faca880027d6544015fe32a2006bf19510007fec888002ff6444013ff3222005bf99110007fac888002fd6444013fe3222005bf19110057fea888027fe5444015feaa22009ff15110007fec688002ff6344011ff31a2004bf98d10007fac688002fd6344011fe31a2004bf18d10057fea688023fe5344015fea9a2008ff14d1004ffe8688023fe4344001fea1a2008ff10d10007fec488002ff624400fff3122003bf98910007fac488002fd624400ffe3122003bf18910057fea48801ffe524400fbf292200aff5491003ff8a48801f7c5244013ffa122007ff90910007fa848801ffc4244011ff9922007ff8c910007fa648801ffc32440037fb0a2002ffd4510016fea28800bfe5144005fea8a2002df54510017f8a28800bff4144005ff20a2002fd90510017fa8288003f54144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff2144005ff10a2002fd88510017fa4288003f52144005fe10a2001bfd811000ffea0880077f5044003ff2822001ff5411000efaa088007fc5044003ffa022001ff9011000ff48088007fd4044001fca022001ff1011000ffe6088007fe3044003fd1822001ff4c110007f26088007fc3044003ff9022001ff8811000ff44088007fd2044001fc9022001ff0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0xafd655002dfe32a8006bf1954000dfec8a0017ff545000bff2a28005ff5514002ff8a8a0003ff63500017fb1a8015ff98d40025fcc6a0003fd635002bfe31a8004bf18d400b7fea6a0057fe535002dfea9a8015ff14d4002ffe86a0017bf435000bff21a8005ff50d400077a86a0017fc4350001ffb128000bfd89400a7fcc4a000efe6250001feb128014ff1894001df8c4a005bff5250029ff2928014df949400b7faa4a0053fc5250029be2928005ffd094002f7e84a0017fe425000bfea128000ef5094002ff884a0057ff3250029ff1928000ff4c9400a7f864a0003ff61500017fb0a8013ff98540015fcc2a0003fd6150027fe30a8002bf185400b7fea2a005b7f5150027ff28a8016ff54540006faa2a004ffc515000bffa0a8005efd054002ffc82a0017fd4150001dea0a8005ff105400affe62a004ffe3150001fe98a8013ff0c5400a7fe42a004ffe2150001fe90a8013ff0854000dfec0a0007ff5050003bfa828001ff9414000ffaa0a00077d5050003fe2828001ffd014002ff680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff460a0007fc3050003ff9028001ff8814000ff840a0007ff1050003ff0828001fe8414000ff820a004bff654c0257fb2a6012ff99530035fcca9804bfd654c0257eb2a6012ff19530035f8ca98003ff644c0017fb226011ff9913002dfcc898003fd644c0017eb226011ff1913002df8c89804bff544c023ff2a26012ff5513008ff8a898006ff634c009ffa9a6004ff94d30027faa698013fc534c009ffa1a6004ff90d30027bc8698013fd434c001eea1a6004ff10d30007fec498002ff624c021ff3126003bf98930007fac498043fc624c0077e3126012ffd4930087fca4980437e524c025fea926010ff14930086f8a498047ff424c021ff2126000ff50930087f88498013ff324c009ef9926004ff8c930027fa6498003dd324c009fe1926000ffd8530005fec29803ffe614c0057f30a6000ff5853007ff8c29800afc614c025ffa8a6012dfd453007ffca29804bfd514c001bea8a600fff1453008ffe829803ffe414c001fea0a600fff10530027fe6298013df314c009ff18a6004ff4c530007ba6298013fc314c021ff90a600fff88530007fa429803ffc214c0037fb026001ffd413000efea098007fe504c003fea826001df5413000ff8a098007ff404c003ff2026001fe9013000ffa8098003f9404c003fe2026001ffcc130027f66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff84098007ff104c003ff0826001fe8413000ff8209802fff65480177fb2a4000dfd9520004feca9002ffe654800d7f32a400bff5952005dfaca9002ffc654800d7e32a400bdf19520034f8ca90003ff64480017fb
  | 2 => 0x31016fea29880bfe514c405fea8a6202df54531017f8a29880bff414c405ff20a6202fd90531017fa8298803f5414c405fe20a6202ffcc531027ee629880bfe314c405ef18a6202ff0c531017b8629880bf4314c405ff90a6202ff88531017f84298803ff604c4017fb02621fff9813100dfcc098803fd604c43ffe3026201bf18131117fea09888b7f504c43fff2826222ff541310fff8a098887ff404c43fff202621fff10131027fe6098813df304c409ff1826204ff0c131107fe409887ffe204c43ffe1026202ffc4131017ee209880bfe104c405fe082621effd95210f5feca908037f65484013fb2a421eff99521035fcca9087bfd654843d7eb2a421eff19521035f8ca9087b7c654840d3e32a4200ffd9121005fec890877fe644840b7f3224200ff59121005fac890877fc644840b7e322421effd51210effca89087bfd544843bfe2a24200ffd8d21005fec690873fe63484097f31a4200ff58d21005fac690873fc63484097e31a421effd4d210e7fca69087bfd5348439fe29a421dffd0d210e7fc8690803fd4348439fe21a4202bfd892101ffea49080ffe5248407bf2924203ff5492101ff8a49080f7c5248407ffa124203ff9092101fdc849080ffd4248401f6a124203ff1092101ffe649080ffe3248407f71924203ff4c921007da649080ffc32484057fb0a4202ffd4521016fea29080bfe5148405fb28a4202ff54521016faa29087bf55148401baa8a4202ff14521017fe829080bfe4148405fea0a4202ff10521017fe629080bfe3148405fe98a4202ff0c521017fe429080ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843dffa82421edfd41210dffca09087bfd5048437fe282421dffd01210dffc809086ffc4048439ff982421bff8c1210dff8609080fff2048407f79024203ff8812101ff8409080bff1048405fb8824202ff84121017f820908037f6454035bf322a000df591500d6f8c8a80037f6354033bf31aa000df58d500cef8c6a806b7f4354033bf21aa000df50d500cef886a80037f6254031bf312a0039f98950006fac4a80637c62540073e312a01adfd09500c6fc84a80037d4254031be212a019dfcc9500c6fc64a80037d3254031be192a000dfd8550004fec2a805f7e6154001beb0aa017df185500d6fe82a805f7e4154001bea0aa017df105500cefe62a805f7e3154001be98aa017df0c5500c6fe42a805f7e2154001be90aa017df0855000efec0a80067f605400dbdb02a001dfd015000efc80a80077c4054003bf982a001df8c15000ef860a80077f2054003bf102a001de8815000ef840a80077f1054003bf082a001df041500b7fecaa005aff655002dff32a8006bf995400b7facaa005
  | 3 => 0xf9826404ff8c132027f8609900fff204c807f79026403ff8813201ff840990b3ff104c857ff082642bff04132006fec8a88ab7e6454401beb22a22adf19151006fec6a88a77e6354401beb1aa229df18d51156fe86a88a77e4354401bea1aa229df10d51006fec4a88a37e62544073f312a200df58951146f8c4a880e7c6254455bfa12a228df90951006fa84a88a37c4254453bf992a228df8c951006fa64a88a37c3254405bfb0aa2029fd8551036eec2a880b7f4154405bf20aa202df10551016fe62a880b7e3154405be18aa202dfc8551016fc42a880b762154405be10aa200dfd8151004fec0a889f7e6054401beb02a227df18151156fe80a889f7e405444fbe202a229dfcc15113efc60a889f7c3054451bf902a227df8815113ef840a880b7f1054405bf082a202df04151137fecaa089aff655044dff32a8206bf99541137facaa089afd655044dfe32a8206bf19541015fec8a0817ff545040bff2a28205ff5514102ff8a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe535044dfea9a8225ff14d4102ffe86a0817bf435040bff21a8205ff50d410077a86a0817fc4350401ffb128200bfd8941127fcc4a080efe6250401feb128224ff1894101df8c4a089bff5250449ff2928224df94941137faa4a0893fc5250449be2928205ffd094102f7e84a0817fe425040bfea128200ef5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202dfd4541017fca2a080bfd5150405bea8a8202ff14541017fe82a0817f74150405ff20a8202ef90541017f882a080bbc4150405fa20a8202ffcc541017fc62a080bf63150405fe18a8202ffc8541017fc42a080bfc2150401ffb028200bfd814111ffcc0a0806fe6050401feb028223ff1814100df8c0a089bff505044dbfa828223ff94141137faa0a088ffc505040bffa028205efd014102ffc80a0817fc405044bff9828223ff8c14111ff860a0893ff2050447ff1028223ff08141017fe20a080bf71050405ff0828202ff04141117feca9888aff654c445ff32a6206bf99531117faca9888afd654c445fe32a6206bf19531007fec898802ff644c443ff3226205bf99131007fac898802fd644c443fe3226205bf19131117fea898887fe544c445feaa26221ff15131015fec698813ff534c409ff29a6204ff54d31027f8a698813ff434c409ff21a6204f790d31027fa8698803dd434c409fe21a6200ffd8931005fec498883fe624c4077f3126200ff58931107f8c49880efc624c445ffa926220ff94931106fca49888bfd524c441fe2926220df1493110ffe8498883fe424c401fea126220ff10931027fe6498813df324c409ff1926204ff4c931007ba6498813fc324c4057fb0a6202ffd45
  | 4 => 0x8dbfd5050c67fe2828605ffd014302f7e80a1817fe4050c0bfe2028604ffcc143027be60a1813fe3050c09fe1828635ffc814319ffc40a18cffc2050c69ff8828633ff8414319ff820a18cbff65508657fb2a8400dfd9542004fecaa10cbfe655080d7f32a8432ff59542195facaa10cbfc655080d7e32a8432df19542034f8caa100eff645080bffaa28405ff9514202f7ca8a1017fd5450865deaa28405ff15142007fec6a1002ff6350863ff31a8404bf98d42007fac6a10c7fc63508097e31a8432ffd4d4218ffca6a10cbfd5350863fe29a8405ffd0d4202ffc86a10c7be435080bfea1a8405ff10d4202f7886a100eff6250807ffa928432fbd494201ffca4a100f7e5250807fea928403ff1494201ef8a4a100fec5250807b62928403ffd094202fde84a100ffe4250807df2128403ff1094201f7884a100fec4250807ff9928403ff8c94201fdc64a100ffc3250801ffb0a8400bfd8542187fcc2a100afe6150801feb0a8430ff18542015f8c2a10cbff5150865bfa8a8430ff94542197faa2a10c3fc515080bffa0a8405efd054202ffc82a1017fc4150863ff98a8430ff8c542187f862a100fff2150807f790a8403ff8854201ff842a1003ff60508017fb02842fff9814200dfcc0a1003fd605085ffe3028401bf18142197fea0a10cb7f505085fff2828432ff5414217ff8a0a1017ff405080bdfa028405ff9014202ff880a10c7ff305085fff182842fff0c14201ffe40a100fef2050807ff1028403ff08142187fe20a10bffe105085ffe082842effd9532175feca990037f654c8013fb2a642eff99532035fcca990bbfd654c85d7eb2a642eff19532035f8ca990bb7c654c80d3e32a6400ffd9132005fec8990b7fe644c80b7f3226400ff59132005fac8990b7fc644c80b7e322642effd513216ffca8990bbfd544c85bfe2a26403bfd8d32027fea699013fe534c809ef29a6404ff54d32177baa699013fc534c809ffa1a642df7d0d32027fc8699013fd434c809fe21a6404f710d3201dfec49900fff524c85df7a926403ff9493201efca49900ffd524c807fe2926403df1493201fd8a49900f6c524c807ffa126403ff9093201fdc849900ffd424c801f6a126403ff1093201ffe6499013ef324c807ff1926403f78c93201ff8649900fdc324c807f61926400ffd8532005fec2990b3fe614c8057f30a6400ff58532167f8c29900afc614c85dffa8a642edfd4532167fca2990bbfd514c859fe28a642dffd0532167fc82990b3fc414c809ff98a6404f7cc532027fc6299013fc314c807ff90a6403fbc853201ffc429900ffc214c801ffb026400bfd813215ffcc099006fe604c801feb02642bff1813200df8c0990bbff504c85dbfa82642bff94132177faa0990affc504c85bffa02642bff9013215ff88099013ff304c809e
  | 5 => 0x8d314588418e99a99b95280a90607d975a0d20414b9a919d0151441bc92e1c105415509d0110951f40bd0690d700007c10a80000000019a0d400022100000000000014698422c15a82a94020c96c8c42479240b81d0972800034a081ce1c980000b0000001d69ca00004481010980001294122e83202897f00080000801c028150080040100401c0080100000c09000000008014028050040080000000201c0101201201000804006000028010460000080701c000038000020040000201c01c00805002000028030000000b81300a028000020180040680200a010048000140300000000203006006000008060000020000780600200c0000d00e008030010020ac0b00b022080000000020100700800000006801014000028000100000180001405c0380200600400002002008008010040380000300400000001002018028020000040301b0000000a00500000403000010000088090000580480300200000800000000000030040280500200a03c000020080080180900400000000000008010020020040080100000c008010060400081002404c02838006000100030140740080200600804001000004078000000080180802002008801004008020030000500580800400000803010038010000000040200f0000001302400000000800018004000000080000380f0020180400200002c0380100e00c008060000540000b0280280e00201001c0300800600c0000300002c0200000005400007000008000000200000000200007c008000000000380000a0000401900400c1280001c0040000400c04401000002008050000020740080300000c06808024038010000020041b00100c018010080020480380702e038000000000300000300200403801002004000050000000100f0020080280801200c0500002036ffd95431b5fecaa18dbfe6550c0d7f32a8636ff595431b5facaa18dbfc6550c0d7e32a8604bfd914302ffea8a1817fe5450c0bfeaa28605ff15143025fec6a1813ff5350c09ff29a8604ff54d43027f8a6a1813ff4350c0befa1a8604ff90d430277c86a1813fc4350c09de21a8604f710d430273886a1803ff6250c017fb128635ff9894301dfcc4a1803fd6250c6bfe3128603bf189431b7fea4a18d7fe5250c6bbf2928636ff549431aff8a4a18d77c5250c0bffa128605ff9094302ff884a1813ff3250c09ff1928604ff0c943007fec2a1802ff6150c69ff30a8602bf98543007fac2a18d3fc6150c057e30a8636ffd45431b6fea2a18d3fe5150c6dfea8a8634ff1454302ffe82a1817bf4150c0bff20a8605ff10543027fe62a1813df3150c09ff18a8604ff0c5431affe42a18d3fe2150c69fe10a8600ffd8143005fec0a18cffe6050c037f3028600ff5814319ff8c0a1806fc6050c6dffa828636dfd414319ffca0a1
  | 6 => 0xf19a4a0e83e05b8798001708171558000ee95903c8a080000009a0df8b39391f78001199b121c8001e19ba00018f9a60000002182441cc96216022e00011480000f1f913b8dd0e58480ae80014902d8000bd8991360f58000731161dd80003f1331b1a32a240b40581c203d1b202b8419c19fb00000015300012500013e85c00003c2310000ce130907103a2800000003f9ba9790000000c09900001008f50d693c1cb0278c6973a3a80780014a2351538600519bd05298d14487a80004880009f0e30a51f2a390888020cb1b01c81b70000000ed0ba00015003a92712598aa4f8a780023d8a61f523000124d0000e61f88c118e14f11691892c0830001280bc0080000d2a1c1bda140c9a358710401f702a2460d0901042817a321a58f1a401d79110001a98d19750001e700006a8000760000790000001d70d39040001970000900000000000000001d20000d780024722b8ea17f81080000000000000015c2110e706b80000012d8001930000000000000000001ae11511902e89096a07780008a02d0000f88ba98987680007a0ec14206c8000d111d95199e800875939845959a1b8d510e16880009416b80024500009780024880004692f8358040f900003d96811598299121288b1570ee1690270511218000000c500281d1100810000071de0000c60000b700012a9f998697c0bb97d00012200197001f9b317b03a05fa42a0fa31a2a8989c39a40ea8478001bb1d49db0230000e695e85217300001a8b10198000f780021f05f00e8058ca87b0781660000dd85b1511d38088000398db18a1b4a3d0a28000c38a491796a80014500000000020224b90e80000016c0060002269ec0000001949ee0ef9208e78a58f10eb9642050cd0b219223f9d11ed1239480b294f9639f00701439e10001ec89c8090001c580010900000003112c83b90d05480000000000000000002e00015a20d9e28d98fc16521e9d423990688f9ff0d887f80010f8001ff9181d000014c1f480019296f00006424a0000001e40000030b987720180000016984400018908984c1430e522f96791d2438351d19e993a8c205d80006225000024097b81c84300000012a00013107280d0460d800000000016112ea038000001ee8000809f09ad85c80000389708a8001ca98601910783284b1969bc16fa1a0f990311fa278968b69dc17c8000000001488de0120f00938000e99e79b8a2a1581858000558ce8000390470fb80000000e1818d58fd00006a02280000000001a1378000929a28000001ad13b2491288002048000000220cf09b8001722030a700001f0a107085d10d92614d84e86107d1b284ba381f38001da00000000000000000000000000000020707b83b0001de9771c09eda459eb00000014ea4e9919fe9e914b1c78001b918c0ef24305a8001d589f9c61ab
  | 7 => 0xd89b0000a905307e146011a298a6a3f2168b18b610b93380005a11a8569da8fc8afa3401823488c92d1628f096080000019b1df0681d507e8e18001c001e9520f60340e080b85e8e397e95f8ae0e01a70000aa1ae8cf84d8000000000000388660f302c9bf16d80022c9c69a3238a190578538e2062a200b012001c03320f1d8800223a4b13a0da8ff882954a090fe04fa2506f1171018859cd2160000000001fc0000000000000000000fd956a4f02691b00c12f0631d61788000000000001ab0740000fe8999e22158001318000000001c280000017a96b11f15e112219914188a069058788e29c40251990589eb8890000001d90e4142a259560b48000001bb974a1f9cb8ab04e08700000000009107f0ad00000015d8002012288000000001128618000be80010006486e16ea1b2228000001470000189b58068000002338000000922291f20001021e088b8f68002371e393d1cc12980000c9ef0bf9c498088e81417d8b589604984f0cc00002493f1d988500024205908c1fe1a39769a01850a8a3e95d1b08cb9ac80019e01e16300003685e0c780001b0000e123e0001a789e0000688000000ed97e13282c23b88800000002183800020586b0bc98c998813a0284ca17a4e0001798000a99ef9be98820b12490489e96701b9fd80000018b9838000379cf0db80000000007198d8290ff2078608438001118000168000000f70000261df9f311e87490a00008621e0dc0000000000f280000011e00000000021716682988d9269ac0000000002060d49a52000df06690522d9ea9af86994789c113a4812b95b8d20a40a0127a2f0000b915796482f9e8a0c0ca18b22d00004d0001740b098f19591a04a1fb8c30148001a21aa8b7a3c800000226082000000141800000211a0080000000009a8878000280cd8240918aa80002b0001fd0000001710c810c000165a1d9780000000001801e01a8a120000001a09dd0560491cd8000000001ce8d60b500000009583600001d8e91a186c0da00f8000a30160f40000f800024c8e498499f06780024a8c91c313686d0fa99513413806513514d0bb0001230980659e323c07c9a81d29348b89980fb16d0571f68370211509618d0190a3080024c10c86e93fa188319b398711c921102a1000018795400020a80000013ca1380024114994a8c70001358001ea1b78a191ba499fca2b1e59409b400a0a8023a3b2088000001cf9b98739b699c9a11d31938c19a69320e89f58848000000000048001080f382f04220e0000eb1b61f800003000019f8001760000001e4a361371f600005020b88d12921d1c90638000001d81389c880000000000015f0b31be06d8a39bfa469e81aa0f201317a21a8f499783e91c22714c80500010f0dc9b80000fa10884a8be00000008180016e2331fa8000000550c488e1
  | 8 => 0x13015b02087200024480987508003393e1c51821b50000ac0000000000000000000408002098d912b0000000a22150000000000001941998ad8ec8002368001db9c719600019c10b24180000019d8002208000000599e68c29588670949e600008680000000d8258ac95c8838c58001830e80509dc8000410af030977a1300022222311314e23a122800110a3788f2248c88ab9e51fa09d8de97186f8bf0930450200cc9af214a21a10a4da0a0158c01811f113
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x3604c5100ff77504c5100ff75504c5100fff2404c5100ffd7304c5100fff2304c5100ffd5304c5100fff2204c51000df4764851001ef4764851000cf476485100077775485101e77475485101e6f765485101e77665485101e6f56548510007756548510006756548510005f77448510005f57448510005f77348510005f57348510015f77248510017e77248510007e7624851001ef6624851001ef4624851003fe4624851003f76524851003f74524851003fe64248510007e5424851003fe63248510007e53248510007f3704851000df6704851000df470485100dff0704851000df07048510016f76048510017f360485100df7750485100df7550485100dff240485100dff230485100dfe720485100dff220485100dfe52048510015f8765011002ef87650110014f876501101df7a655011000779655011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb86450110005fb7350110006fb6350110006f9635011004fbb4350110007b94350110005fb72501101d77a52501101d778525011004fbb4250110007b94250110007f37150110015fa7150110015f8715011009ff07150110015f0715011000efb615011000ff3615011009f7b515011009f79515011009fbb415011009ff2415011009fb9415011004ff14150110007b1415011009ff23150110007f1315011009ff22150110007f12150110015f8764c110026f8764c110014f8764c1101cf7a654c11000779654c110005fb744c110005f9744c110006fb644c110006f9644c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110047da434c110007d9434c110005fb724c1101c77a524c1101c778524c110047db324c110007d9324c110007f3714c110015fa714c110015f8714c11007ff0714c110015f0714c11000efb614c11000ff3614c11007f7b514c11007f79514c11007ff2414c110007f1414c11007fdb314c11007ff2314c11007fd9314c110047f1314c110007d1314c11007ff2214c110007f1214c110015f8764811001ef87648110014f876481100077b75481101bf7875481101befb65481101bf7a65481101bef96548110007796548110006796548110005fb7448110005f97448110005fb7348110005f9734811000dfb724811000feb7248110007eb624811001efa624811001ef8624811003fe8624811003f7a524811003f78524811003fea4248110007e9424811003fea3248110007e93248110007f37148110015fa7148110015f87148110067f07148110015f0714811000efb614811000ff361481100677b5148110067795148110067f24148110007f14148110067f23148110007f13148110067eb2148110067f22148110067e9214811003ff12148110007e12148110
  | 1 => 0x891003f6c52d8910217f010d8910004ff75d8910034fe75d89100067e75d89100347e75d8910004fd75d89100067d75d89100047d75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d8910006ef52d891003e7e52d891003e7c52d891003eec52d891003e6c52d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102267f51d89102267d51d8910226ef21d8910226ed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d89102167f50d89102167d50d8910216ef20d8910216ed20d891001cff76589100057f75589100557c75589100067e65589100067d655891003eec625891020df7715891021dfb70589100dff01058910004ff75589100067f75589100047f7558910034fe7558910004fd7558910034fc75589100067c75589100347c7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910214ff7258910006ef725891003e7e525891003e7c525891003eee425891003eee325891020cff7158910006f771589100667f51589100667d51589100dcff7058910006fb70589100de7f50589100de7d5058910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100557c75509101967e65509100067d655091002ebe6450910006bd645091001eee6250910006ed625091003f6c5250910015f6715091000dfa705091017ff01050910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100557c754c9101767e654c9100067d654c910026de634c910006dd634c91001eee624c910006ed624c91003f6c524c910015f6714c91000dfa704c91015ff0104c91000df4765051002ef4765051000cf47650510207766550510007756550510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb46450510005f77350510006f76350510006f5635051004fb74350510007b54350510005f772505101ff7652505101ff74525051004fb74250510007b54250510007f3705051000df6705051000df4705051011ff0705051000df07050510016f76050510017f3605051011f77505051011f75505051011fb7405051011ff2405051011fb5405051011ff2305051011ff2205051000df4764c510026f4764c51000cf4764c5101f776654c51000775654c510005f7744c510005f5744c510006f7644c510006f5644c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6434c510007d5434c510005f7724c5101ef76524c5101ef74524c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100fff0704c51000df0704c510016f7604c510017f
  | 2 => 0x11cfd74d9110024fe73d9110004fd73d9110024fc73d9110006be43d911004ebc43d911001cfe72d9110004fd72d911001cfc72d91100067e52d91100067c52d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102667f51d91102667d51d9110266bf41d9110266bd41d9110266f631d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102567f50d91102567d50d9110256bf40d9110256bd40d9110256fa30d911002cff76591100067e65591100067d655911004ebc6459110005df7359110045dc735911024df7715911025dfb705911011ff01059110004ff7559110034fe7559110004fd7559110034fc7559110254ff7459110006bf7459110004ff7359110006df7359110004df7359110024fe7359110024fc7359110006dc7359110024dc735911004ebf4359110004ff725911001cfe725911001cfc72591100067e52591100067c525911004ebf425911024cff7159110006f7715911009e7f515911009e7d515911009ef6315911011cff7059110006fb705911011e7f505911011e7d505911011efa3059110024fe76d8d100557e75d8d100057d75d8d100067e65d8d100067d65d8d10046de63d8d10237f010d8d10004ff75d8d10034fe75d8d100067e75d8d100347e75d8d10004fd75d8d100067d75d8d100047d75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d10006df43d8d10046dc43d8d1001cfe72d8d10004fd72d8d1001cfc72d8d100067e52d8d100067c52d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d102467f51d8d102467d51d8d10246f641d8d10246df31d8d10246dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d102367f50d8d102367d50d8d10236fa40d8d10236df30d8d10236dd30d8d10024ff7658d100067e6558d100067d6558d10005bf7458d1004dbc7458d10046dc6358d1022df77158d1023dfb7058d100fff01058d10004ff7558d10034fe7558d10004fd7558d10034fc7558d10004ff7458d10006bf7458d10004bf7458d1002cfe7458d1002cfc7458d10006bc7458d1002cbc7458d10234ff7358d10006df7358d10046de4358d10004ff7258d1001cfe7258d1001cfc7258d100067e5258d100067c5258d10046df3258d1022cff7158d10006f77158d1007e7f5158d1007e7d5158d1007ef64158d100fcff7058d10006fb7058d100fe7f5058d100fe7d5058d100fefa4058d10004ff7650d10004fe7650d10004fd7650d10004fc7650d101b67e6550d100067d6550d1002ebe6450d10006bd6450d10026de6350d10006dd6350d100479c4350d10015f67150d1000dfa7050d1019ff01050d1001cfe76d89100557e75d89100057d75d89100067e65d89100067d65d891003eee62d
  | 3 => 0x874541200077b645412028f7a645412000779645412028f7864541200077b73541202877a73541200077973541202877873541200077b63541202877a635412000779635412028778635412028f7b43541202877a43541200077943541202877843541200c77b72541200076b72541200c77a725412001d7a72541200c77972541200c778725412001d7872541200c768725412000f7b625412000e7b625412000f6b62541200c77b42541200c77a42541200c76a42541200c77942541200076942541200c77842541200c77b32541200c77a32541200c76a32541200c77932541200076932541200c77832541200077b71541200057b715412027f7a715412000779715412027f7871541200077b615412027f7a615412000779615412027f78615412028f7b415412027f7a415412000779415412027f7841541202877b315412027f7a315412000779315412027f7831541200c77b21541200c76b21541200c77a21541200c77921541200076921541200c778215412026d7f76595100567f76595100347f76595100067e64595100067c64595100067e63595100067c63595100076f725951003d7e725951003d7c72595100076c725951003d6c72595100067e62595100067c625951026d7f715951000777715951026d7771595100bf7641595100bf7631595100bf76215951013d7f70595100077b70595102757b705951013f7a405951013f7a305951013f7a20595100bf7b105951013f76105951013f74105951013f78105951013f7010595100067f74595100067e74595100067d74595100067c74595100067f73595100067e73595100067d73595100067c73595100067f43595100067e43595100067c43595100067f72595100066f72595100067e725951001c7e72595100067d72595100067c725951001c7c72595100066c725951001c6c72595100067f42595100067e42595100067c42595100067f32595100067e32595100067c32595100be7f715951026c7f71595100067771595100be7f41595100be7e41595100be7d41595100be7c41595100be7f31595100be7e31595100be7d31595100be7c31595100be7f21595100be7e21595100be7621595100be7d21595100be7c215951013e7f705951013c7f70595100067b705951013e7f405951013e7e405951013e7d405951013e7c405951013e7f305951013e7e305951013e7d305951013e7c305951013e7f205951013e7e205951013e7a205951013e7d205951013e7c205951013e7f105951013e7e105951013e7d105951013e7c105951002cfe76d91100557e75d91100057d75d91100067e65d91100067d65d911004ebe64d9110257f010d9110004ff75d9110034fe75d91100067e75d91100347e75d9110004fd75d91100067d75d91100047d75d9110034fc75d9110
  | 4 => 0xc920007cf634c920026ee634c920026ec634c92006fcc634c92006fce534c9202afcd534c9202b7cf434c92006fcc434c920005ef714c9202af6f514c92006fcf314c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015f6f504c92015fea504c92015f6d504c9202afe9504c92015fcf304c92015fcd304c92015fea104c920014fe76d852005d7c75d85200067f65d85200067c65d8520066f661d8520004ff75d85200067f75d8520034fe75d8520004fd75d8520034fc75d85200067c75d85200347c75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d8520014fc72d85202a67e52d85202a67c52d85202a6ee42d8520006ed42d85202a6ee32d8520006ed32d85200667f51d8520066f621d85202a6f521d852000cfe70d852001cfd70d852000cfc70d852020e7f50d852020e7d50d852020ef710d85200057f755852005d7c75585200067f65585200067c6558520066f4615852029dfb70585200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545200067f64545201567e64545200067d64545201567c64545200067f635452014e7e63545200067d635452014e7c635452001d7e725452001d7c725452013e7f62545201476e42545200076d42545201476e32545200076d325452026d7f715452005f7771545200667f61545200167e61545200167c61545200676f215452006776215452014775215452013d7f705452013f7a705452000779705452013e7f60545201477b205452013f6e205452013f6c205452013f78205452013f7a1054520004ff7650520004fe7650520004fc76505200067f65505201367c655052002ebe6450520006bd645052001dee7250520007ad4250520004ff764c520004fe764c520004fc764c5200067f654c5201167c654c520026de634c520006dd634c52001dee724c520007cd324c52000dec7648520016ec764852000cec76485200076f75485202976c75485200076f65485202976c6548520005ef7448520005ed7448520006ef6448520006ed6448520005ef7348520005ed7348520006ef6348520006ed634852001def714852001fe77148520007e76148520016ee6148520016ec6148520067e461485200676f5148520067e651485200676d5148520297e55148520007655148520007eb704852000dee704852000dec70485200dfe8704852001eef604852001feb60485200df6f50485200dfea50485200df6d5048520297e950485200dfe710485200dfea104852005f7b76541200367b76541200c778765412001d78765412003678765412001c7876541200077b745412028f7a745412000779745412028f7
  | 5 => 0x2f6fa10d912002cff76591200057f755912005d7c75591200067f65591200067c6559120076bc64591202edef72591202fdfb7059120004ff75591200067f75591200047f7559120034fe7559120004fd7559120034fc75591200067c75591200347c75591202f4ff7459120006bf7459120004ff7359120024fe7359120024fc73591202ecff7259120006ef72591200a67e52591200a67c52591200a6ee3259120004ff7159120014fe7159120014fc71591200067f5159120076bf41591200a6ef215912017cff7059120006fb705912017e7f505912017e7d505912017efa1059120024fe76d8d200067f65d8d200067c65d8d2006ede63d8d20004ff75d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d202e67e52d8d202e67c52d8d202e6ee42d8d202e6df32d8d202e6dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d200067f51d8d202e6ef21d8d2001cff70d8d2001cfd70d8d202d67f50d8d202d67d50d8d202d6df30d8d202d6dd30d8d202d6fa10d8d20024ff7658d200057f7558d2005d7c7558d200067f6558d200067c6558d2006edc6358d202cdef7258d202ddfb7058d20004ff7558d200067f7558d200047f7558d20034fe7558d20004fd7558d20034fc7558d200067c7558d200347c7558d20004ff7458d2002cfe7458d2002cfc7458d202d4ff7358d20006df7358d202ccff7258d20006ef7258d200867e5258d200867c5258d20086ee4258d20004ff7158d20014fe7158d20014fc7158d200067f5158d2006edf3158d20086ef2158d2015cff7058d20006fb7058d2015e7f5058d2015e7d5058d2015efa1058d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d201b67c6550d2006f9c4350d2001dee7250d2000dec765092002eec765092000cec76509200076f75509202bf6c75509200076f6550920196ee6550920196ec65509202bf6c65509201966c655092001def745092001faf7450920007af645092002eee645092002eec6450920077ac6450920077ae54509202bfad5450920005ef7350920006ef6350920006ed63509202c7ae4350920077ac4350920005ef71509202bf6f5150920077af4150920007eb705092000dee705092000dec705092017fe8705092001eef605092001feb605092017f6f505092017fea505092017f6d50509202bfe9505092017faf405092017fad405092017fea105092000dec764c920026ec764c92000cec764c9200076f754c9202af6c754c9200076f654c920176ee654c920176ec654c9202af6c654c9201766c654c920005ef744c920005ed744c920006ef644c920006ed644c92001def734c92001fcf734
  | 6 => 0xc704c5300ffd8704c530026df604c530027db604c5300ff5f504c5300ff5d504c5300ffda404c5300ffd7104c5300ffda104c530004ff7648530004fe7648530004fc76485300057f75485300957c7548530025de7348530005dd734853001eee6248530007cd3248530007755148530025f8765013002ef87650130024f8765013000dfb745013000fbb7450130007bb645013002efa645013002ef8645013008fb86450130007db7350130025fa7350130025f873501300afd8735013000efb635013000fdb63501300afbb43501300afda43501300afb9435013008fd9435013000799435013032f7a525013032f78525013008fbb4250130007b942501300afdb3250130007d93250130005fb7150130006fb61501303277b515013000779515013008fbb4150130007b941501300afdb3150130007d9315013031d7e76d952005e7e76d95200347e76d95200067e64d95200067c64d95200067e63d95200067c63d952001d7e72d952001d7c72d95203176e42d95203176e32d95200057d71d95200067e61d95200067c61d95203176f21d952001d7f70d95203177b70d952001d7d70d952030f7870d95203177b20d952030f6e20d952030f6c20d952030f7820d952030f7a10d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067c43d952030e7f72d95203167e72d952001c7e72d952030e7d72d952030e7c72d952001c7c72d95203167f42d95203167e42d95203167d42d95203167c42d95203167f32d95203167e32d95203167d32d95203167c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067c41d95200067f31d95200067e31d95200067c31d95203167f21d95203167e21d95203167d21d95203167c21d952030e7f70d952001c7f70d952030e7e70d952030e7d70d952001c7d70d952030e7c70d952030e7f40d952030e7e40d952030e7d40d952030e7c40d952030e7f30d952030e7e30d952030e7d30d952030e7c30d952030e7f20d952030e7e20d952030e7d20d952030e7c20d952030e7f10d952030e7e10d952030e7d10d952030e7c10d952002cfe76d91200067f65d91200067c65d9120076be64d9120004ff75d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d91203067e52d91203067c52d9120306bf42d9120306bd42d9120306ee32d9120014fe71d9120004fd71d9120014fc71d91200067f51d9120306ef21d912001cff70d912001cfd70d91202f67f50d91202f67d50d91202f6bf40d91202f6bd40d9120
  | 7 => 0x893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d89300867e52d89300867c52d8930086ee32d893035eed32d8930014fe71d8930004fd71d8930014fc71d89300067f51d893035edf31d8930024fd70d89302ce7f50d89302ce7d50d89302ceef20d89302cefa10d89300057f75589300957c7558930086ec6258930355fb7058930004ff7650930004fe7650930004fc76509300057f75509300957c7550930006bf645093002ebc6450930025de735093018f9e435093001eee62509300876c525093000ddc764c93001edc764c93000cdc764c9300075f754c93034f5c754c93034edf654c93034edd654c930005df744c930005dd744c93016ede644c93016edc644c930025df724c930027cf724c930007cf624c93001ede624c93001edc624c930087cc624c93034fcf524c9300875e524c9300875c524c930087cc524c9300874c524c930087ce424c930007cd424c930005df714c93034f5f514c930087cf214c930007db704c93000dde704c93000ddc704c93015fd8704c93000dd8704c930026df604c930027db604c93015f5f504c93015f5d504c93015fda404c93015fcf204c93015fda104c930014fe76d853007ef661d8530004ff75d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d8530346de43d8530006dd43d853001cfe72d8530004fd72d853001cfc72d85300067e52d85300067c52d8530346df32d8530006dd32d853007e7f51d853007ef631d8530346f531d8530024fd70d853022e7f50d853022e7d50d853022efa40d853022ef710d8530005bf745853008dbc745853007ef4615853033dfb70585300067f76545300067e76545300067d76545300067c76545300067f64545301567e64545300067d64545301567c645453013e7f635453014f5e43545300075d43545300857e72545300857c72545300067f62545301467e62545301467c625453014f5f32545300075d325453026d7f715453009777715453007e7f61545300167e61545300167c615453007f5f315453007f76215453013d7f705453013e7f605453013f7a405453014f7b305453013f5e305453013f5c305453013f78305453013f7a1054530004ff7650530004fe7650530004fc765053002ebe6450530006bd6450530025de73505300079d4350530016f6615053000dfa705053000ddc764c530016dc764c53000cdc764c530005df744c530005dd744c530006df644c530006dd644c530005df724c530006df624c5303375e524c5303375c524c530025df714c530027d7714c530007d7614c530016de614c530016dc614c53007fd4614c53007f5f514c53007f5d514c53007fd6414c530007d5414c530007db704c53000dde704c53000dd
  | 8 => 0xa57c72545400067f62545401467e62545401467c62545401573f42545400073d425454026d7f71545400b777715454009e7f61545400167e61545400167c615454009f3f415454009f76215454013d7f705454013e7f60545401577b405454013f3e405454013f3c405454013f78405454013f7a305454013f7a105454000dbc7650540016bc765054000cbc7650540005bf7350540006bf6350540005bf7250540006bf62505403973e52505403973c525054002dbf715054002fb77150540007b76150540016be6150540016bc615054009fb4615054009f3f515054009f3d515054009fb63150540007bb705054000dbe705054000dbc705054011fb8705054002ebf605054002fbb605054011f3f505054011f3d505054011fba305054011fb7105054011fba1050540004ff764c540004fe764c540004fc764c54002dbe744c540005bd744c540026de634c5400079d434c540016f6614c540007b5414c54000dfa704c540004ff7648540004fe7648540004fc76485400057f75485400b57c754854002dbe7448540005bd744854001eee6248540007ad424854000775514854002cfe76d913008ebe64d9130004ff75d9130034fe75d9130004fd75d9130034fc75d913019cfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d913038ebf43d913038ebd43d913001cfe72d9130004fd72d913001cfc72d91300067e52d91300067c52d913008ebf42d9130014fe71d9130004fd71d9130014fc71d91300067f51d9130006be41d913008ebc41d913038edf31d9130024ff70d9130024fd70d913037e7f50d913037e7d50d913037ebf40d913037ebd40d913037efa10d913002cff765913008ebc6459130375df7359130385fb7059130004ff7559130034fe7559130004fd7559130034fc755913037cff7459130006bf7459130374ff7359130006df7359130004ff725913001cfe725913001cfc72591300067e52591300067c5259130004ff7159130014fe7159130014fc71591300067f515913008ebf41591300aedf315913019cff7059130006fb705913019e7f505913019e7d505913019efa105913000ddc7650d3002edc7650d3000cdc7650d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d3002e9c6450d30005df7250d3036f5e5250d3036f5c5250d30005df7150d303675f5150d3008f9f4150d30007db7050d3000dde7050d3000ddc7050d3019fd87050d30026df6050d30027db6050d3019f5f5050d3019f5d5050d3019f9f4050d3019fda4050d3019f9d4050d3019fda1050d3001cfe76d89300957e75d89300057d75d8930086ee62d8930004ff75d8930034fe75d89300067e75d89300347e75d8930004fd75d89300067d75d89300047d75d8930034fc75d
  | 9 => 0xc52d8d400aedf32d8d40014fe71d8d40004fd71d8d40014fc71d8d400067f51d8d403debf41d8d40006de31d8d400aedc31d8d4002cfd70d8d403767f50d8d403767d50d8d40376df30d8d40376fa10d8d400aedc6358d403d5fb7058d4000dbc7650d40026bc7650d4000cbc7650d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400269c6350d40005bf7250d403cf3e5250d403cf3c5250d40005bf7150d403c73f5150d400af9f3150d40007bb7050d4000dbe7050d4000dbc7050d4019fb87050d4002ebf6050d4002fbb6050d4019f3f5050d4019f3d5050d4019f9f3050d4019fba3050d4019fba1050d4001cfe76d89400b57e75d89400057d75d89400a6ee62d8940004ff75d8940034fe75d89400067e75d89400347e75d8940004fd75d89400067d75d89400047d75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89400a67e52d89400a67c52d89400a6ee42d89403beed42d8940014fe71d8940004fd71d8940014fc71d89400067f51d89403bebf41d894002cfd70d89402ee7f50d89402ee7d50d89402eeef20d89402eefa10d89400057f75589400b57c75589400a6ec62589403b5fb705894000dbc765094001ebc765094000cbc76509400073f75509403af3c75509403aebf65509403aebd6550940005bf735094018ebe635094018ebc635094002dbf725094002faf7250940007af625094001ebe625094001ebc62509400a7ac62509403afaf52509400a73e52509400a73c52509400a7ac52509400a72c52509400a7ae3250940005bf71509403af3f51509400a7af2150940007bb705094000dbe705094000dbc705094017fb8705094000db8705094002ebf605094002fbb605094017f3f505094017f3d505094017fba305094017faf205094017fba1050940004ff764c940004fe764c940004fc764c9400057f754c9400b57c754c94002dbe744c940005bd744c940006df634c940026dc634c94016f9f434c94001eee624c9400a76c524c940007ad424c940014fe76d854009ef661d8540004ff75d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d8540024fe73d8540004fd73d8540024fc73d85403a6bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d85400067e52d85400067c52d85403a6bf42d8540006bd42d854009e7f51d854009ef641d85403a6f541d854002cfd70d854024e7f50d854024e7d50d854024efa30d854024ef710d8540005df73585400addc735854009ef4615854039dfb70585400067f76545400067e76545400067d76545400067c765454013e7f64545400067f635454014e7e635454014e7c63545401573f43545400073d43545400a57e7254540
  | 10 => 0x855026e7f30d855026e7e30d855026e7d30d855026e7c30d855026e7f20d855026e7e20d855026e7a20d855026e7d20d855026e7c20d855026e7f10d855026e7710d855026e7e10d855026e7c10d85503ed7f76585500057f74585500d57e74585500d57c74585500067f64585500067e64585500067d64585500067c64585500057f73585500cd7e73585500cd7c73585500067f63585500067e63585500067d63585500067c63585500057f72585500076f72585500056f72585500c57e72585500c57c72585500076c72585500c56c72585500067f62585500067e62585500067d62585500067c625855026d7f71585500077761585500be7e61585500be7c61585500bf7461585500bf76215855013d7f70585500077b70585503e57b705855013e7f60585500577b605855013f7a20585500057f76505500057e76505500057d76505500057c76505502557f74505500057f73505500cd7e73505500cd7c73505500d73f43505500073d43505500057f72505500c57e72505500c57c72505501267e62505501267c62505500d73f42505500073d425055024d7f71505500be7f61505500d77741505500bf3e41505500bf3c41505500bf7441505500bf76315055011d7f705055000d7e705055000d7c705055011e7f60505501377b605055011f3f405055011f7a205055011f7710505500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5500d57e744c5500057d744c5500d57c744c5502357f734c5500cf5e434c5500075d434c5500057f724c5500c57e724c5500c57c724c5501067e624c5501067c624c5500cf5f324c5500075d324c55022d7f714c5500be7f614c5500bf76414c55000775414c5500cf77314c5500bf5e314c5500bf5c314c5500bf74314c5500fd7f704c55000d7e704c55000d7c704c5500fe7f604c5501177b604c5500ff5f304c5500ff7a204c5500ff77104c5500057f76485500067f76485500047f76485500057e76485500057d76485500057c76485500067c76485500047c76485500057f74485500d57e74485500057d74485500d57c74485500057f73485500cd7e73485500057d73485500cd7c73485502157f724855001e7e624855001e7c62485500c76e42485500076d42485500c76e32485500076d324855020d7f71485500be7f61485500bf7661485500077561485500c77721485500bf6e21485500bf6c21485500bf7421485500dd7f704855000d7e704855000d7c70485500de7f60485500f77b60485500df6f20485500df7a20485500df771048550024fe76d8d400aede63d8d40004ff75d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d403dedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d400067e52d8d400067
  | 11 => 0xc67c62589500c76c62589500057f71589500bd7e71589500bd7c71589504157f70589500077b705895041d7b70589504167f605895005f7b60589504177a20589500057f76509500067f76509500047f76509500057e76509500057d76509500057c76509500067c76509500047c76509502f57f74509500d73e64509500073d64509500057f73509500cd7e73509500cd7c735095040f3e43509500d73c43509502ed7f72509500076f625095001e7e625095001e7c62509500c76c625095001e6c62509500d76f42509500c73e42509500c73c42509500c76c42509500c76e32509500057f71509500bd7e71509500bd7c71509500d73f41509500c76f215095017d7f705095000d7e705095000d7c705095017e7f60509501977b605095017f3f405095017f6f205095017f7a20509500057f764c9500067f764c9500047f764c9500057e764c9500057d764c9500057c764c9500067c764c9500047c764c9500057f744c9500d57e744c9500057d744c9500d57c744c9502d57f734c9500cf5e634c9500075d634c9504075f434c9500cf5c434c9502cd7f724c9500076f624c95001e7e624c95001e7c624c9500c76c624c95001e6c624c9500c76e424c9500076d424c9500cf6f324c9500c75e324c9500c75c324c9500c76c324c9500057f714c9500bd7e714c9500bd7c714c9500cf5f314c9500c76f214c95015d7f704c95000d7e704c95000d7c704c95015e7f604c9501777b604c95015f5f304c95015f6f204c95015f7a204c9503fd7e76d85500d57e74d85500057d74d85500d57c74d85500067f64d85500067e64d85500067d64d85500067c64d85500cd7e73d85500057d73d85500cd7c73d85500067f63d85500067e63d85500067d63d85500067c63d85500c57e72d85500057d72d85500c57c72d85500067f62d85500067e62d85500067d62d85500067c62d855013d7d71d85500be7e61d85500bf7661d85500be7c61d85500357f70d855000d7e70d85500357d70d855000d7c70d855026e7f60d85503f77b60d855026f7a20d855026f7710d855026f7510d85500067f74d85500067e74d85500067d74d85500067c74d85500067f73d85500067e73d85500067d73d85500067c73d85500067f43d85500067e43d85500067d43d85500067c43d85500067f72d85500067e72d855001c7e72d85500067d72d85500067c72d855001c7c72d85500067f42d85500067e42d85500067d42d85500067c42d85500067f32d85500067e32d85500067d32d85500067c32d855013c7d71d85500be7f41d85500be7e41d85500be7c41d85500be7f31d85500be7e31d85500be7c31d85500be7f21d85500be7e21d85500be7c21d855026e7f70d855026e7d70d85500347d70d855026e7f40d855026e7e40d855026e7d40d855026e7c40d
  | 12 => 0x8605812148d7e76d91504657d74d91500d67e64d91500d73e64d91500d67c64d91500cd7e73d91500057d73d91500cd7c73d91500c57e72d91500057d72d91500c57c72d91500067e62d91500067c62d91500bd7e71d91500057d71d91500bd7c71d91500357f70d915000d7e70d91500357d70d915000d7c70d91504767f60d91504877b60d91504773f40d91504773d40d91504777a20d915047d7f76591504757f74591500073f64591500d67e64591500d67c64591500d73c64591500057f73591500cd7e73591500cd7c73591500057f72591500c57e72591500c57c72591500067e62591500067c62591500d73f42591500057f71591500bd7e71591500bd7c71591504657f70591500077b705915046d7b70591504667f60591500b77b60591504677a205915045d7e76d8d500d57e74d8d500057d74d8d500d57c74d8d500067f64d8d500067d64d8d504357d73d8d500ce7e63d8d500cf5e63d8d500ce7c63d8d500c57e72d8d500057d72d8d500c57c72d8d500067e62d8d500067c62d8d500bd7e71d8d500057d71d8d500bd7c71d8d500357f70d8d5000d7e70d8d500357d70d8d5000d7c70d8d504467f60d8d504577b60d8d504475f30d8d504475d30d8d504477a20d8d5044d7f7658d500057f7458d500d57e7458d500d57c7458d500067f6458d500067d6458d504457f7358d500075f6358d500ce7e6358d500ce7c6358d500cf5c6358d500057f7258d500c57e7258d500c57c7258d500067e6258d500067c6258d500cf5f3258d500057f7158d500bd7e7158d500bd7c7158d504357f7058d500077b7058d5043d7b7058d504367f6058d500977b6058d504377a2058d500057f7650d500057e7650d500057d7650d500057c7650d5037d7f7450d503757f7350d500d75f4350d500cf3e4350d500cf3c4350d500cf5c4350d500cf1c4350d500057f7250d500c57e7250d500c57c7250d501ae7e6250d501ae7c6250d500057f7150d500bd7e7150d500bd7c7150d500d73f4150d500cf5f3150d5019d7f7050d5000d7e7050d5000d7c7050d5019e7f6050d501b77b6050d5019f3f4050d5019f5f3050d5019f7a2050d5031d7e76d895001c7e76d89500d57e74d89500057d74d89500d57c74d89500cd7e73d89500057d73d89500cd7c73d89504157d72d89500c67e62d89500c76e62d89500c67c62d89500c76e42d89500c76e32d89500bd7e71d89500057d71d89500bd7c71d89500076e21d89500c76c21d89500357f70d895042f7b70d895000d7e70d89500357d70d895000d7c70d89504267f60d895042f7b60d89504276f20d89504277a20d89504276d20d895030d7f76589500057f74589500d57e74589500d57c74589500057f73589500cd7e73589500cd7c73589504257f72589500076f62589500c67e6258950
  | 13 => 0x92102eec64509210efac64509210efae54509214bfad5450921005ef7350921006ef6350921006ed63509214c7ae43509210efac4350921007e77150921015ee7150921015ec7150921187e4715092101eef615092101fe761509211876f5150921187e651509211876d51509214bfe55150921187af4150921187ad4150921005ef70509214bf6f50509210efaf4050921187e71050921015ec764c921026ec764c921014ec764c9210076f754c9214af6c754c9210076f654c921176ee654c921176ec654c9214af6c654c9211766c654c921005ef744c921005ed744c921006ef644c921006ed644c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210e7cc634c9210e7ce534c9214afcd534c9214b7cf434c9210e7cc434c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c9211676f514c921167e6514c9211676d514c9214afe5514c921167cf314c921167cd314c921005ef704c9214af6f504c9210e7cf304c921167e7104c9210f777765452103677765452114774765452101d74765452103674765452101c7476545210077774545214a77674545210077574545214a77474545210077764545214a77664545210077564545214a774645452100777735452149f76735452100775735452149f74735452100777635452149f76635452100775635452149f7463545214a777435452149f76435452100775435452149f74435452114777725452100767725452114776725452101d76725452114775725452114774725452101d7472545211476472545210177762545210167762545210176762545211477742545211477642545211476642545211477542545210076542545211477442545211477732545211477632545211476632545211477532545210076532545211477432545210077770545210057770545214977670545210077570545214977470545214977660545214977460545214a777405452149776405452149774405452149f77305452149776305452149774305452114777205452114767205452114776205452114774205452100cfe76d81210f57c75d81210067f65d81210067c65d81210077551d81210defa60d8121004ff75d81210067f75d8121034fe75d8121004fd75d8121034fc75d81210067c75d81210347c75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d812100cfc72d812129e7e52d812129e7c52d812129eee42d8121006ed42d812129eee32d8121006ed32d812101cfd71d812100cfc71d812121e7f51d812121e7d51d81210de7f50d81210defa20d81210defa10d81210057f75581210f57c75581210067f65581210067c65581210077551581210def
  | 14 => 0x67e40d95210067c40d95210067f30d95210067e30d95210067c30d95215167f20d95215167e20d95215167d20d95215167c20d952150e7f10d952150e7e10d952150e7d10d952150e7c10d952102cfe76d91210067f65d91210067c65d91210eebe64d9121004ff75d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121024fe73d9121004fd73d9121024fc73d9121014ff72d9121014fd72d91215067e52d91215067c52d9121506bf42d9121506bd42d9121506ee32d912101cff71d912101cfd71d91214f67f51d91214f67d51d91214f6bf41d91214f6bd41d912100cfe70d9121004fd70d912100cfc70d91210067f50d9121506ef20d91214f6f710d912102cff76591210057f75591210f57c75591210067f65591210067c65591210eebc64591214edef72591214fdf77159121004ff75591210067f75591210047f7559121034fe7559121004fd7559121034fc75591210067c75591210347c75591214f4ff7459121006bf7459121004ff7359121024fe7359121024fc73591214ecff7259121006ef72591211267e52591211267c5259121126ee3259121184ff7159121006f771591211867f51591211867d5159121004ff705912100cfe705912100cfc70591210067f50591210eebf4059121126ef2059121186f71059121024fe76d8d210067f65d8d210067c65d8d210e6de63d8d21004ff75d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d214e67e52d8d214e67c52d8d214e6ee42d8d214e6df32d8d214e6dd32d8d2101cff71d8d2101cfd71d8d214d67f51d8d214d67d51d8d214d6df31d8d214d6dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210067f50d8d214e6ef20d8d214d6f710d8d21024ff7658d210057f7558d210f57c7558d210067f6558d210067c6558d210e6dc6358d214cdef7258d214ddf77158d21004ff7558d210067f7558d210047f7558d21034fe7558d21004fd7558d21034fc7558d210067c7558d210347c7558d21004ff7458d2102cfe7458d2102cfc7458d214d4ff7358d21006df7358d214ccff7258d21006ef7258d211067e5258d211067c5258d21106ee4258d21164ff7158d21006f77158d211667f5158d211667d5158d21004ff7058d2100cfe7058d2100cfc7058d210067f5058d210e6df3058d21106ef2058d21166f71058d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d211b67c6550d210e79c4350d2101dee7250d21015ec765092102eec7650921014ec76509210076f75509214bf6c75509210076f6550921196ee6550921196ec65509214bf6c65509211966c655092101def745092101faf7450921007af645092102eee645
  | 15 => 0xc764c93101edc764c931014dc764c9310075f754c9315375c754c931536df654c931536dd654c931005df744c931005dd744c93116ede644c93116edc644c931025df724c931027cf724c931007cf624c93101ede624c93101edc624c931107cc624c931537cf524c9311075e524c9311075c524c931107cc524c9311074c524c931107ce424c931007cd424c931007d7714c931015de714c931015dc714c931167d4714c931015d4714c931026df614c931027d7614c9311675f514c9311675d514c931167d6414c931167cf214c931005df704c9315375f504c931107cf204c931167d7104c931025f4765053102ef47650531024f47650531015f77450531017b77450531007b7645053102ef6645053102ef4645053110fb46450531007d77350531025f67350531025f4735053112fd47350531016f76350531017d7635053112fb7435053112fd6435053112fb5435053110fd5435053100795435053152f76525053152f74525053110fb74250531007b5425053112fd73250531007d53250531005f7705053152777505053110fb7405053112fd7305053100cfe76d81310fefa60d8131004ff75d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813133ede43d8131006dd43d813101cfe72d8131004fd72d813101cfc72d81310067e52d81310067c52d813133edf32d8131006dd32d8131024fd71d813123e7f51d813123e7d51d813123ef641d8131006f541d81310fe7f50d81310fefa30d81310fefa10d8131005bf745813110dbc74581310fef8605813151d7e76d95210f67e76d95210347e76d95210067e64d95210067c64d95210067e63d95210067c63d952101d7e72d952101d7c72d95215176e42d95215176e32d952101d7f71d95215177771d952101d7d71d952150f7471d95215177721d952150f6e21d952150f6c21d952150f7421d95210057d70d95210067e60d95210067c60d95215176f20d952150f7710d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067c43d952150e7f72d95215167e72d952150e7d72d952150e7c72d95215167f42d95215167e42d95215167d42d95215167c42d95215167f32d95215167e32d95215167d32d95215167c32d952150e7f71d952101c7f71d952150e7e71d952150e7d71d952101c7d71d952150e7c71d952150e7f41d952150e7e41d952150e7d41d952150e7c41d952150e7f31d952150e7e31d952150e7d31d952150e7c31d952150e7f21d952150e7e21d952150e7d21d952150e7c21d95210067f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f40d9521
  | 16 => 0xc94102dbe744c941005bd744c941006df634c941026dc634c94116f9f434c94101eee624c9411276c524c941007ad424c94100cfe76d814111efa60d8141004ff75d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d8141024fe73d8141004fd73d8141024fc73d814139ebf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d81410067e52d81410067c52d814139ebf42d8141006bd42d814102cfd71d814125e7f51d814125e7d51d814125ef631d814111e7f50d814111efa40d814111efa10d8141005df735814112ddc735814111ef8605814102cfe76d913110ebe64d9131004ff75d9131034fe75d9131004fd75d9131034fc75d91311a4fd74d9131014ff73d9131014fd73d9131576bf43d9131576bd43d913101cfe72d9131004fd72d913101cfc72d91310067e52d91310067c52d913110ebf42d9131024ff71d9131024fd71d91315667f51d91315667d51d9131566bf41d9131566bd41d913100cfe70d9131004fd70d913100cfc70d91310067f50d9131006be40d913110ebc40d9131576df30d9131566f710d913102cff765913110ebc645913155ddf735913156df77159131004ff7559131034fe7559131004fd7559131034fc7559131564ff7459131006bf745913155cff7359131006df7359131004ff725913101cfe725913101cfc72591310067e52591310067c52591311a4ff7159131006f771591311a67f51591311a67d5159131004ff705913100cfe705913100cfc70591310067f505913110ebf405913112edf30591311a6f71059131015dc7650d3102edc7650d31014dc7650d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3102e9c6450d31005df7250d315575e5250d315575c5250d31007d77150d31015de7150d31015dc7150d311a7d47150d31026df6150d31027d76150d311a75f5150d311a75d5150d311a79f4150d311a7d64150d311a79d4150d31005df7050d3154f5f5050d3110f9f4050d311a7d71050d3101cfe76d89311157e75d89310057d75d8931106ee62d8931004ff75d8931034fe75d89310067e75d89310347e75d8931004fd75d89310067d75d89310047d75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d89311067e52d89311067c52d8931106ee32d8931546ed32d8931024fd71d89314ce7f51d89314ce7d51d89314ceef21d893100cfe70d8931004fd70d893100cfc70d89310067f50d8931546df30d89314cef710d89310057f75589311157c7558931106ec625893153df77158931004ff7650931004fe7650931004fc76509310057f75509311157c7550931006bf645093102ebc6450931025de735093118f9e435093101eee62509311076c5250931015d
  | 17 => 0x13e7c10d815113d7f76581510057f74581511557e74581511557c74581510067f64581510067e64581510067d64581510067c64581510057f735815114d7e735815114d7c73581510067f63581510067e63581510067d63581510067c63581510057f72581510076f72581510056f72581511457e72581511457c72581510076c72581511456c72581510067f62581510067e62581510067d62581510067c62581510bd7f71581510077771581513f57771581510be7f61581510577761581510bf76215815113d7f70581510077b605815113e7e605815113e7c605815113f78605815113f7a2058151024fe76d8d4112ede63d8d41004ff75d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d415aedd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d410067e52d8d410067c52d8d4112edf32d8d4102cfd71d8d4155e7f51d8d4155e7d51d8d4155edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410067f50d8d415aebf40d8d41006de30d8d4112edc30d8d4155ef710d8d4112edc6358d415a5f77158d41015bc7650d41026bc7650d41014bc7650d4102dbf7350d4102f9f7350d410079f6350d41026be6350d41026bc6350d4112f9c6350d410269c6350d41005bf7250d4159f3e5250d4159f3c5250d41007b77150d41015be7150d41015bc7150d411a7b47150d4102ebf6150d4102fb76150d411a73f5150d411a73d5150d411a79f3150d411a7b63150d41005bf7050d415973f5050d4112f9f3050d411a7b71050d4101cfe76d89411357e75d89410057d75d8941126ee62d8941004ff75d8941034fe75d89410067e75d89410347e75d8941004fd75d89410067d75d89410047d75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d89411267e52d89411267c52d8941126ee42d894158eed42d894102cfd71d89414ee7f51d89414ee7d51d89414eeef21d894100cfe70d8941004fd70d894100cfc70d89410067f50d894158ebf40d89414eef710d89410057f75589411357c7558941126ec6258941585f77158941015bc765094101ebc7650941014bc76509410073f755094157f3c755094157ebf655094157ebd6550941005bf735094118ebe635094118ebc635094102dbf725094102faf7250941007af625094101ebe625094101ebc6250941127ac625094157faf52509411273e52509411273c5250941127ac52509411272c5250941127ae3250941007b77150941015be7150941015bc7150941187b47150941015b4715094102ebf615094102fb761509411873f51509411873d5150941187b63150941187af2150941005bf705094157f3f5050941127af2050941187b71050941004ff764c941004fe764c941004fc764c9410057f754c9411357c754
  | 18 => 0xf76509510067f76509510047f76509510057e76509510057d76509510057c76509510067c76509510047c76509514f57f74509511573e64509510073d64509510057f735095114d7e735095114d7c73509515bf3e43509511573c43509514ed7f72509510076f625095101e7e625095101e7c62509511476c625095101e6c62509511576f42509511473e42509511473c42509511476c42509511476e32509511857f71509510157e71509510157c71509511867f61509511977761509511873f41509511876f21509511877621509510057f705095113d7e705095113d7c70509511573f40509511476f20509510057f764c9510067f764c9510047f764c9510057e764c9510057d764c9510057c764c9510067c764c9510047c764c9510057f744c9511557e744c9510057d744c9511557c744c9514d57f734c95114f5e634c9510075d634c9515b75f434c95114f5c434c9514cd7f724c9510076f624c95101e7e624c95101e7c624c9511476c624c95101e6c624c9511476e424c9510076d424c95114f6f324c9511475e324c9511475c324c9511476c324c9511657f714c9510157e714c9510157c714c9511667f614c95117777614c9511675f314c9511676f214c95116776214c9510057f704c95113d7e704c95113d7c704c95114f5f304c9511476f204c95113d7e76d81511557e74d81510057d74d81511557c74d81510067f64d81510067e64d81510067d64d81510067c64d815114d7e73d81510057d73d815114d7c73d81510067f63d81510067e63d81510067d63d81510067c63d81511457e72d81510057d72d81511457c72d81510067f62d81510067e62d81510067d62d81510067c62d81510357f71d81510157e71d81510357d71d81510157c71d81512767f61d81513e77761d81512777621d815113d7d70d815113e7e60d815113f7a60d815113e7c60d815113f7a10d81512777910d81510067f74d81510067e74d81510067d74d81510067c74d81510067f73d81510067e73d81510067d73d81510067c73d81510067f43d81510067e43d81510067d43d81510067c43d81510067f72d81510067e72d815101c7e72d81510067d72d81510067c72d815101c7c72d81510067f42d81510067e42d81510067d42d81510067c42d81510067f32d81510067e32d81510067d32d81510067c32d81512767f71d815113e7d71d81510347d71d81512767f41d81512767e41d81512767d41d81512767c41d81512767f31d81512767e31d81512767d31d81512767c31d81512767f21d81512767e21d81512767621d81512767d21d81512767c21d815113e7f40d815113e7e40d815113e7c40d815113e7f30d815113e7e30d815113e7c30d815113e7f20d815113e7e20d815113e7c20d815113e7f10d815113e7e10d815113e7a10d8151
  | 19 => 0x91510067e62d91510067c62d91510357f71d91510157e71d91510357d71d91510157c71d91516267f61d91516377761d91516273f41d91516273d41d91516277621d915113d7e70d91510057d70d915113d7c70d915162d7f76591516257f74591510073f64591511567e64591511567c64591511573c64591510057f735915114d7e735915114d7c73591510057f72591511457e72591511457c72591510067e62591510067c62591511573f42591516157f715915100777715915161d7771591516167f61591511377761591516177621591510057f705915113d7e705915113d7c705915160d7e76d8d511557e74d8d510057d74d8d511557c74d8d510067f64d8d510067d64d8d515e57d73d8d5114e7e63d8d5114f5e63d8d5114e7c63d8d511457e72d8d510057d72d8d511457c72d8d510067e62d8d510067c62d8d510357f71d8d510157e71d8d510357d71d8d510157c71d8d515f67f61d8d516077761d8d515f75f31d8d515f75d31d8d515f77621d8d5113d7e70d8d510057d70d8d5113d7c70d8d515fd7f7658d510057f7458d511557e7458d511557c7458d510067f6458d510067d6458d515f57f7358d510075f6358d5114e7e6358d5114e7c6358d5114f5c6358d510057f7258d511457e7258d511457c7258d510067e6258d510067c6258d5114f5f3258d515e57f7158d51007777158d515ed777158d515e67f6158d51117776158d515e7762158d510057f7058d5113d7e7058d5113d7c7058d510057f7650d510057e7650d510057d7650d510057c7650d515657f7450d5155d7f7350d511575f4350d5114f3e4350d5114f3c4350d5114f5c4350d5114f1c4350d510057f7250d511457e7250d511457c7250d511ae7e6250d511ae7c6250d511a57f7150d510157e7150d510157c7150d511a67f6150d511b7776150d511a73f4150d511a75f3150d511a7762150d510057f7050d5113d7e7050d5113d7c7050d511573f4050d5114f5f3050d5151d7e76d895101c7e76d89511557e74d89510057d74d89511557c74d895114d7e73d89510057d73d895114d7c73d89515c57d72d89511467e62d89511476e62d89511467c62d89511476e42d89511476e32d89510357f71d89515df7771d89510157e71d89510357d71d89510157c71d89515d67f61d89515df7761d89515d76f21d89515d77621d89515d76d21d895113d7e70d89510057d70d895113d7c70d89510076e20d89511476c20d895150d7f76589510057f74589511557e74589511557c74589510057f735895114d7e735895114d7c73589515d57f72589510076f62589511467e62589511467c62589511476c62589515c57f71589510077771589515cd7771589515c67f61589510f77761589515c77621589510057f705895113d7e705895113d7c70589510057
  | 20 => 0x67c655913216ebc645913264ddf735913218f9c435913265def72591321af6c5259132004ff75591320067f75591320047f7559132034fe7559132004fd7559132034fc75591320067c75591320347c7559132654ff7459132006bf745913264cff7359132006df735913216edf435913218ebe435913218ebc435913218edc435913218e9c43591321acff7259132006ef7259132006ef52591321ae7e52591321ae7c52591321aeec52591321ae6c5259132004ff7159132014fe7159132014fc71591320067f515913216ebf415913218edf31591321aeef2159132004ff705913200cfe705913200cfc70591320067f505913216ebf405913218edf30591321aeef2059132025ec765093202eec7650932024ec76509320076f7550932175ee7550932175ec75509326476c75509321756c75509320076f6550932196ee6550932196ec65509326476c65509321966c655093201def745093201faf7450932007af645093202eee645093202eec645093216fac645093216fae5450932647ad5450932007cf7350932025ee7350932025ec735093218fcc735093201eef635093201fcf635093218fce5350932647cd535093216fcf435093218fae435093218fac435093218fcc435093218f8c4350932005ef71509326476f515093216faf415093218fcf3150932005ef70509326476f505093216faf405093218fcf3050932014fe76d85321757c75d85320067f65d85320067c65d85324df6c52d8532166f661d8532004ff75d85320067f75d8532034fe75d8532004fd75d8532034fc75d85320067c75d85320347c75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d8532024fd72d85324de7e52d85324de7c52d85324deee42d8532006ed42d85321667f51d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d85320067f50d853253edf30d85324deef20d85320057f75585321757c75585320067f65585320067c65585321076c5258532166f4615853200cfe76d81321757c75d81320067f65d81320067c65d81322df6c52d813215efa60d8132004ff75d81320067f75d8132034fe75d8132004fd75d8132034fc75d81320067c75d81320347c75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d8132024fd72d81322de7e52d81322de7c52d81322deee42d8132006ed42d8132014fe71d8132004fd71d8132014fc71d81320067f51d8132356df31d81322deef21d813215e7f50d813215efa30d813215efa20d81320057f75581321757c75581320067f65581320067c65581320876c525813215ef8605813263d7e76d91516157d74d91511567e64d91511573e64d91511567c64d915114d7e73d91510057d73d915114d7c73d91511457e72d91510057d72d91511457c72d
  | 21 => 0xc75d81420067f65d81420067c65d81422ff6c52d814217efa60d8142004ff75d81420067f75d8142034fe75d8142004fd75d8142034fc75d81420067c75d81420347c75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d814202cfd72d81422fe7e52d81422fe7c52d81422feee32d8142014fe71d8142004fd71d8142014fc71d81420067f51d81423b6bf41d81422feef21d814217e7f50d814217efa40d814217efa20d81420057f75581421957c75581420067f65581420067c65581420a76c525814217ef8605814267d7e76d95321767e76d95320347e76d95320067e64d95320067c64d953266f5f73d953266f5c73d95320075f43d95326775c43d953201d7e72d953266f6e72d953201d6e72d95326776d72d953201d7c72d953266f6e42d95326776f32d953266f5e32d953266f5c32d953266f6c32d95320057d71d95320067e61d95320067c61d95326775f31d953266f6f21d95320057d70d95320067e60d95320067c60d95326775f30d953266f6f20d95320067f74d95320067e74d95320067d74d95320067c74d953266e7f73d95326767e73d953266e7d73d953266e7c73d95326767f43d95326767e43d95326767d43d95326767c43d953266e7f72d953266e7e72d953266e6e72d953266e7d72d95326766d72d953266e7c72d953266e7f42d953266e7e42d953266e7d42d953266e7c42d953266e7f32d953266e7e32d953266e7d32d953266e7c32d95320067f71d95320067e71d95320067d71d95320047d71d95320067c71d95320067f41d95320067e41d95320067c41d95326767f31d95326767e31d95326767d31d95326767c31d953266e7f21d953266e7e21d953266e7d21d953266e7c21d95320067f70d95320067e70d95320067d70d95320047d70d95320067c70d95320067f40d95320067e40d95320067c40d95326767f30d95326767e30d95326767d30d95326767c30d953266e7f20d953266e7e20d953266e7d20d953266e7c20d95320067f10d95320067e10d95320067c10d953202cfe76d91320067f65d91320067c65d913216ebe64d9132025de73d913201ddd73d913216f9f43d91326576c52d9132004ff75d9132034fe75d9132004fd75d9132034fc75d91321acfd74d913201cff73d913201cfd73d9132656dd73d913201cdd73d9132666bf43d913216edf43d9132666bd43d9132666dc43d9132024ff72d9132024fd72d9132006ef52d91326567e52d91326567c52d9132656ec52d91326566c52d9132656bf42d9132656bd42d9132014fe71d9132004fd71d9132014fc71d91320067f51d9132666df31d9132656ef21d913200cfe70d9132004fd70d913200cfc70d91320067f50d9132666df30d9132656ef20d913202cff76591320057f75591321757c75591320067f6559132
  | 22 => 0x95426973f74d95426973c74d95420067e63d95420067c63d95420073e43d954269f3c43d954201d7e72d95426976e72d954201d6e72d954269f6d72d954201d7c72d954269f6f42d95426973e42d95426973c42d95426976c42d95426976e32d95420057d71d95420067e61d95420067c61d954269f3f41d95426976f21d95420057d70d95420067e60d95420067c60d954269f3f40d95426976f20d95426967f74d954269e7e74d95426967d74d95426967c74d95420067f73d95420067e73d95420067d73d95420067c73d954269e7f43d954269e7e43d954269e7d43d954269e7c43d95426967f72d95426967e72d95426966e72d95426967d72d954269e6d72d95426967c72d95426967f42d95426967e42d95426967d42d95426967c42d95426967f32d95426967e32d95426967d32d95426967c32d95420067f71d95420067e71d95420067d71d95420047d71d95420067c71d954269e7f41d954269e7e41d954269e7d41d954269e7c41d95420067f31d95420067e31d95420067c31d95426967f21d95426967e21d95426967d21d95426967c21d95420067f70d95420067e70d95420067d70d95420047d70d95420067c70d954269e7f40d954269e7e40d954269e7d40d954269e7c40d95420067f30d95420067e30d95420067c30d95426967f20d95426967e20d95426967d20d95426967c20d95420067f10d95420067e10d95420067c10d9542024fe76d8d420067f65d8d420067c65d8d4202dbe74d8d4201dbd74d8d4218ede63d8d4218f9e43d8d4264f6c52d8d42004ff75d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4264ebd74d8d4201cbd74d8d4218ebe43d8d4218ede43d8d4268edd43d8d4218ebc43d8d4202cfd72d8d42006ef52d8d4264e7e52d8d4264e7c52d8d4264eec52d8d4264e6c52d8d4264edf32d8d42014fe71d8d42004fd71d8d42014fc71d8d420067f51d8d4268ebf41d8d4264eef21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420067f50d8d4268ebf40d8d4264eef20d8d420057f7558d421957c7558d420067f6558d420067c6558d4218edc6358d4218f9c4358d42685ef7258d421af6c5258d42014fe76d85421957c75d85420067f65d85420067c65d85424ff6c52d8542186f661d8542004ff75d85420067f75d8542034fe75d8542004fd75d8542034fc75d85420067c75d85420347c75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854202cfd72d85424fe7e52d85424fe7c52d85424feee32d85421867f51d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d85420067f50d8542586bf40d85424feef20d85420057f75585421957c75585420067f65585420067c65585421276c5258542186f4615854200cfe76d81421957
  | 23 => 0x20018010000002000000001602f0010004000001001001c00e0020000004000002000801400c009000002800000a000000000000600080000180020008008000000000000c01400d000001800001200480000000000078004002008005000000000000080140020000000004004008002800800e01900380400180000058000000000002800000000600000380020000048000000004000002000c00f00000080060020000000000004002001000e0020000010000000001800401200600080280020000050008000000002800c00e002000801000c00d001000000a0050008000004002000000001200100180180020020000000002001000000800200f0050000000000000804c000000001000c00c0030010044006006000002401a00000c001000600200200000020090000030000000001000400000000c002c004000000000000000000000080300090008000018000000000802200400a00140200000020098000000001000400c00000080100020010008034000005001001c0280010000000000006001803c03400000100000060000010034000001001004000200400000080060150008000000002000000800400000000000060050000000000007001800401c007000000000000001cfe76d89431b57e75d89430057d75d894365f9c43d89431aeee62d8943004ff75d8943034fe75d89430067e75d89430347e75d8943004fd75d89430067d75d89430047d75d8943034fc75d8943024fd74d894302cfd73d8943686df43d894365ebe43d894365ebc43d894365edc43d894365e9c43d89431ae7e52d89431ae7c52d89431aeee42d89431aeee32d8943014fe71d8943004fd71d8943014fc71d89430067f51d8943686bf41d894365edf31d894300cfe70d8943004fd70d894300cfc70d89430067f50d8943686bf40d894365edf30d89430057f75589431b57c755894318f9c43589431aeec62589431af6c5258943014fe76d854356f9c43d85431a6f661d8543004ff75d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85430067e52d85430067c52d85431a67f51d85431a6f641d85431a6f631d854300cfe70d8543004fd70d854300cfc70d85430067f50d85435a6bf40d854356edf30d854312f9c43585431a6f4615854300cfe76d81433879c43d814319efa60d8143004ff75d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d81430067e52d81430067c52d8143014fe71d8143004fd71d8143014fc71d81430067f51d81433d6bf41d8143386df31d814319e7f50d814319efa40d814319efa30d81430af9c435814319ef860581436a57e76d95421967e76d95420347e76d
  | 24 => 0x10010000002001000400a000001c01000100080000100000018000002000000803400e004004000001e000003000801c00300100040040000020020010009001001400000000080080060090058000000009001801c00800000000000080000010008000002006800400a006001000400a0030010000008000000000001a0050060034002004000001000c002001800000000b00000000000000018008000006001001001400800d002003e00100100000000020020000006002000800800000000080040000000000010000003002001c00a0000010010002002002000c00e0050008000000001009800800000800380140020000000030002002000000c004001001000c006002003000000000200200080060030018000000001000001400e002007803000c000001002000000e000000000800300000000180100010004006006000000400c00000f0014002000005002c002007001802800000400080100040040008000004004002801800200300000140100010038024002000002802400000000000000140000008000004000002003801c0010050038002002001000000000000780000020020050000002001001001c000001000000400e00000100040000000000004008002004001c00a00000000100080070078084002013001000000a003000000000000100080100000030058010026001000006802c002001800001400b00100440000010008004000000000001c0060000010008000001001002400000400000040060050000010012001005800c000008000000c00200000080000020020050004004000002000000200100c8004008001002000c002007001800c000001004801c00c003003801000601f00300140160010048000000001001800800200000100040080190048000000003000800c0000070028000000000001000400200000680000040000020000004000002002c010005006801800e0030018004000000001801400000f005800000c00a004000c000004001000000000000000080000020058000000004000808002000100000040020000000000000001005000800000a005800800000200000040080090018020000000000003000000100000000020010068078004004005001000000e000001400a00000a00040080000028008008002000800c004002003000802c000000800401a001000000001e00600080140000000000010012002001800800800200000000080020000040002002000001800202300000200040000008000002004002000000c005001802c0060010028010004008000003800c0000008000008001000800800e00200000100120000070004006005000802000000b0000080004001000000c0240000000004002000001000800000e000800c0140000028008000008001000002800
  | 25 => 0x525cd2a83c9544c7b20030055e00f310b1afb9c2c6f0696080112c4bf5f4b820d1ca6f7a7384459690875fb1ed09efa700025cc00046e000130c18419800d00000000000001ea813a21a0003ce400014f77400000ce00027b85a0324000000000000000000000003f60006e6000000000061726d5a44103191925c0000000b7b39530aacf00000000002d15d708a1c72000000000000000075209895c0f1c57c06586fabaf1922860000f290000000c3e0005849121cfc9d57d8800013e6982053160e3c000019800000000045998d993c0006808000f5cf2858631180002585648000000be43171c64000abd000000000000067480000000005370000d360005f1020472e0001c480000000f37739dcd140a872b7a4b8a6c56c74701cdd3800042a8eb8c840006a48bc80008317078af4c6e66b18ea034326abf14e2d1847c8762a02aa0880e4f0c026e8512e880008032001002800800600200000140040030008004010008005802400000900080040000000000000000002002000000e001000005c0000020028000044007005801c00000300080580340030028000028001001000400c00100d000c00400000000000000000000000004000011000400800c001800001801400000c401a000001801c00c00f000000000a00000100480000010000000006003000000000000000d800c00e007004800c00200300d000800a0050030008004007004800802000800280480000000010000000008000000400c000003801000e0020018004010000002802c00800800000100080000000028002006006000403c01c001000000200200500080020070008044032003004000000c007001000002c002001001c002010000800000200000100000080010010004004009005001801200c0040004010003009000c0020000000020000000000800000801c012800000600b001800c000002000800c00000d0060014000000006800c0000000030020000000000800c0060090060004010008000800400400200980000000000008000000000000003c00c000000003c00c002002000000200f0108000000000000001001600b00100100000080018000004004000003c00000a003002c002006000000000c00c00580380000010000004000002003000c002003000800c008000000800400a0010008000000003000801001a0000018000002000006800000602c000800c0060050000000006000011000c0000000048000000000003000800200000080000000000100000002001008802c00200d00080080120030000000002000003802000400f0000000002005000800400200f00e00000020070010024000000006801000600200100140080000000018000003001001c00e00b00080040040060030000006006002801000c003001001c00000000080
  | 26 => 0x4c800000000000012f80006aa55281d0caa18d76db0d0000000000000180600065e00000004da0000000ea4000546000000073400010e80006ac00000004f00007a480002c4c6042d1d851b0889000158c7b2e330001ca194c60c00012bc0000005edaaac000000000235400011f4820001000ec23f6800046481a51400012c200062f04e0460df41ee05f51f4ad907b8001bbeef6561bc28000b771d5b0ad582a4e00032e80000000003b0400000000022a87da9f40000000eb00006c492e818000037c0000b5ac0709d07ac00000031c8000000ce8000000129e6690000dd8b1400000026f87ee4330e63d35db8000167000000003709e1b3419a31b608aae19600007270000b248a30001a200000000b2b699d74d835a480000000d22379b2cdb20003a63ccc56e0007cfa7b8000e155f815940004e753fa02594627b6f48000822bf1000028c0f200044d0fb96b651d0371725988c936bf20bc0d28b677a00000006e877a80007be8d62d0290c38adb530a000162823d00000008205b600025c89eacfe0000000d205d219a000000000058e9780c6200036ab3911001d944a126ceea4d7292814c7c24a666c13704465d67409b241709a72881fa954c0874a0b15134c9422a89785dfa2f7726b455b3856d3a9a79c000c89160ba015bedc45b895f9a8438324e00001fe6ca6c09078136e4903c342106c8ec59c1109ec8845000089decce143931d7c7680000002061da0bb1107b3ed96a0005a9ac9800044b6a18e20000aca0340000000abc0000ba800000030a9af9e2485d000000000000000011fc00000033187d80006080002badd508f500000a4000e3800032b000000000024b073c5ef00000012340ef38eb785230e342c1a3658bee76361a57024e00028180000000770d20cb06b848c00000000005187d32c6c97600072fb7400005fc0002038e888ae6fd08652b65db000078122e0000002214000ace6c81675b940004c6366445693b00000019e80007a28001ec600028c8000000d6e000000184400000000000009c33edba35de2000000353040c0000000000ccc0001fe9360000000520b1dc73a6805c883ad58096e05628f526a1d87b712c001800066d1f583ea3de0000000cd04f35df13b9b52000000010843e8c1659a4815844ea0000c44d1e4ff4910a017c0f4a49a0000000000000000196246d0001ad800058c6b100003420005680001c6a7af3580a7cbd620b000000021426e122ab69f105327ba3d3c9da7c3622a7bc5dc0003110000540bbb5cf8001a1ea380001c0d4087de6fc80004264a06bb0001b90bb97511f240000005a213a173200014800015ae45e662aec00000100c1807d13c00074a276064a11800000017bc867502a3e1c8e36000039e8b46000000000000071634d1994000000000072cefc76c5e921889
  | 27 => 0xaa2ad419c00019f41e3000000000060b000000190c0001348e8dcacf60000276c0001474b138c98000006120f8c00000000013457ec60e0000bac0006f4134000035adc05882e340001f90001f88be0e927bd19b46e2ec900000000003522330bc53ccd1346600018ce4163b333c8b9e94d000000000012100000000000004a3365c000a900000000efad4000015e0592d9d547045400000000000000007bb00000000400001c80000000000398800027a3a5000394826c00000000010980000002cc591a00000000000006930000001536539000000187067d251b94ca940000000744e26e8c426b4c5aa083d12909e9d6a7b97230e049c43fc0000001da6000000117c0006810002ae9d660004128ca40000000028c7d23c0000000000000d565df800001200000036393e40000001bcd5306030000000000b0532937800006d8000283800000000000018fa0000000ce532a8dd1ec11a574a436535a2c46b0d962f627e890ad7254fba6c8644b300004511140000c52211b8c000000102c00009216995f1c8600033a92253fa00032f00004945b9750b129dc82c6236257c000000784800c0001ff02d0000000f2b0000000872b480001405896420000000000012b2c693996e80580000000000a2435a2ce407cd1c2910000e547852a1b2d8ad0b4a000000000000000000003e873c065ae4d2d67dc33b3899382dbc0af1b4cfcc2e7013000152e0a60f22cbce1897964204e48e60302783abc0000000000000000c0c4d52d15e32000000367800065835380b8000000000081c0000006b89bf040696f0002e90000a3500033511a600000010a45cc00057d00015b01a30000000488bec6478000fec00016910f057800039b39a48f6e6b3a280018200000000001f5899c1b280000000005ff800000000003800000000000f6bda0000394755ba19c00135000262800000000027ec9a0b7a00031d00e20000000e7023ad5213e847932c6332178139ba2aad725800147caa1497bcdc742c280003ae0000939000000100600069180000008e00000000466f1a34e800112a30977b826966689214b8368af61fe00039680000006d09d65c46000000000000033d5061348000000416a78008edad000000168e000355a30000075c0d10001e8c28f09f8001828e2a00000000000002122428000c6600000016aa195000297dd2e0007ce24dc18a0002bb000091a8460000888962b780003429d0a2774860000000b2400020843402a661a80000001b80000000ebc5550000000dd674800002f000800050900014ba13251fb02dd86b2a08408e9eee3a00000000000000000000062c00000020a53fcc3d000293400000044400001281461c7bd042da59b15702e4e12bd300517140000005faa209634c88000207d65c5da106a9f1d682f60000a908540005
  | 28 => 0x66f94edf48b760000001b9600060cac10b880001bc1531346d1112128697467117728000ad4ea950580006c28ee19739b4f4e000000258000000000005c9f5ae0979f80000000002a6abedf02baa02415800002d03fe1b9c97aba9764000131e632058b16473ed785ac29a00006e44ac1c899dc9473ef932c4ba6a95388418a1ac8c37d000059400063c00000000000003cb12a800000015c84b60003289ecddb4cd22608bcc0000000000001dd852a5871a3145e1da7caa1ed410aee6ee008c00077c59916b09ba2fc0002fa94ac0000000000c1a00000000003ae00000029495aa000000000000000000000000000000002d509e87420000861c440000002730000000000000123eb3c3a19ed8c528c7550216c000a9a7a5bc9000000057500008ce86907600000000000000c501b6b73000232c89e5dc33f800175000000034315ba6c10001559ab66490000000f36c620001ac400000042406b166073a1d3a784454da577caa7800071700017a9aba45b0003954232e300000ccddbc1cd0003984000000000210470400000015040004fc0a538b465ebba4139b1192ec810003d89024f0e0001a50000de20ab13bd7c667059282e92e8b3b5f30c0994e000770123cc4aaf900000001f6b6b3e61425bf06602ee8cdcf028244b62bdde8800050890096420003f62cb0000e2c00000000003cc3d0915447e35b4909844bd200003004883606047c888705682f547597a1ab05957d8396527e71b6eb8ca06debce3c80000ac22f0000000000015b3e8201400000000032bc6c80000003601ee60002ae80000003010003960000bfd000000194a0000001dfcae23cf77fb1b8098ef014400000000aa0003a94ee40000002eb0000f472fea5c46604443628001ea07e74d280006cc1b200000000880001fa0494000a32000111400000000032f8d320004d72395ed2d6c6d90000a22460000000000057d000000137800000000006c600068c9e99d1e000000371c0000000000a4c0000006169fe11ce0006bc80014663c25ff3974b5cebe62b113494e32702bb45deca76f1450394420afc6ed83717245891e89b8da0c62b758217d3262e30d4a190db800000000001f22920002e786f800000015c00000003df9f1c0006617cb8001d8c000000000172cdde000191c0000006af8830cd45b043d3c7973400060e0000f12000243000000000075880016143bb0868001cd81605d000000008c636b862d1e2afe3cb99b97789846a3091c4ca5e600038613f261300000005089bb0002d340000000000000000e7f00023280007d43d6800131a5a50bf0001ac200040a0a19eb437b0123e680009bf22811e84b4b690a601f567474000006ac0005882da8cacfee16e00019cd8e67770f60000d0a6e6532800000000000000009d230e0000f355c607c23b8001
  | 29 => 0x9145370000e38cb28741e583c000083300030540ba6891b9b82d9f8b3e6d03cc16dc100766373928800064d261da5639b0001685dac00013fa199158000204abcc000b59000000000022f6f6b0208363b64953e8cb30f061af39bdc94c05372995c00019e68fa9d805094b16180018980000000ecc0000000000000f520000000000000e8a0000fbc010f1502a80016f683b0478f0d8549e42a22059460893352beac8501fd1c6986cc7ca1c000045d3ec9d96aaa8955e8db067080000000005570d2c6146351100001d320002318000000e012ac8ec1ac81ef2508001a400007262470fb077a4dc2dfcffa96905f8000000f5d00000008ba41900026e4db6dc21a8bbe000046a0000000cd81ea21db8480004ca00000000000003b1020920a0000000000000000000041188400000002dd6223bc00000019800000002ed144000066b3d4d86ec4755204a000049414d80018b40005159d5000053e6d3ac480000001330000b98c753e5822c972000000278d80c7507420c4d1e6e0603da87d4ce92b00000000000001029b2000041770f9220000a781eaba60f0ec720000000ee80000000000d64cef0001b51aae1f276cb2608582ef0000f154b46bc1818001d720000003b74000c1370b80010dc0000000eb442c71c139025c00072f00000000006f11263308f04abb73b80003881f8000000000060126a9890b7040d4cd96ecf6aaa70000225c7400000000000001875ce8944c301ca1f90000000d920001589b2a0000620001444000000116483a1130de8fec114d8234580000006ef00000000000006858001eb80006379c48000bd65db3cd8b7ae0a068b110f18b523909d442601bb0681c210500411e22abd7b80006dd82194e479d583a9196021e7793a8b44dac090002e9c83879e000250000000000029e9c18df34e8ac340005284b6800084283a50a99edc4a4c407224a40bc5737399410d669d34022a0cf2aeb214f352066aa940002e99172f670000000000c760dcaa341260004e39754ec0f722f9afdcf8ce7d053abd98909d2356800000000000012b5d5af510000001ae00003531cf40000002183660000faf64fa809b9e18143fafe436262c4d03e30000f4c7c8359cd428be4089f4913897a12837580009520000000000000070bb5c0361e202029eda6400000028757de00026316440000004fc00000000f60000000690f5f00019e91d28b759380000008fc665000000000012bb5dc000dbd1230aa44580003e8af3cc7675547822e025a9e23420ec9a88050000259c00000000000000000005a70001ac6e4213200004c000000016403e0c8373e1031a96d292573808bc8822146a5a93000e910d800415036e32e9e280009cd431831d78a6177bf80004906ce00000014320002db800110ecd000eafc842e99f18f00014ae000
  | 30 => 0xc477c00000000000000000000001a689eb000000000000062e85206ce0004db8afd6fa342097a59179a000000000038e8020578000c0479c14180010c095600017d523a0002ce0000000000000000000045c0001fc4e400006b500000000004ce863c0001850000000e1a0002c21f740000001ba18e144e0002320ac4f26b223ae8784a2800000027000000000003d4874800010522b5a06000368ab95756a742cf992d900d246d5b19000000000033e0000000531a679e540001eb27690604f2690b0604d45ff3ca199c4bc0006aca709b1a00040984cc4046d236636c4000dd4085800000000000000000001790000000faa00000002d0a0c0006739478deeea72dd3bbc2b2000202b434000a950000339a72b5d0000670f224bc0df80000000000000000b3c00051d800000000075dbd0c320c401aa27fccb675a5b680383a40000003aa94944f829180003348f644fab440000000003c810fa7a2374aab08c4b4b1eb9c7d2160000002a1874ccdb17f80000002db501acf53ca907325295484c85700000000000005118d5de3a1021829eace5c00000000000002140003995e7000003f8c1998cade0001c15e22d680001b7d144000000000000028214b0f953d08561b1042473469600002cc0000003b200000002e16c9b22d14a0004ad16fd6e02d541f20313d8000650a284c0a0000b20001d6c0000c6098c91610f17d936d8d45930000001718c5b78a1658000b6c17e830ddfc00046e2c21b0a7c1000146d2aa80b00000000001820002020a2a0f20000cf99200000000000920dae6d100000000000000bf838c0961a53011ee2bb7000273d51000052a0000000000000000000023408600000000006be000045200000024cd38ab900c2318510c8c243f1e814b81f30402911ad2dfe528994170200000000004a800062aaa2d66a59429d00000001940000001388a29000104c2d20000000000e8200000000012903ac78b8ffd72e8bd68a02ed40e9ca00035acb0a97d41a296c000c3a4e480004820005c100004f823b3fa35cdd3af2e64d9c9c000a48150b3b5742226136103c00061a1b58044000ad20000e88b6200031a0000000000298b0cc44a9a10000750d7a3962f680017a27372e50000da000056210f5e160000001cc80000001bf9148a1498639cbab0000f6f562a2ac15674f4a527798a2ecf1389e39e7ab8f1c02e6d87e1c95ea00019ea01c7d29a8000085e46a25393d25790001de4b54e1a2158c31a6c0005ab314c84e3933578b35b580000d505a8c98938000331c0d6f011660795a6e34316380ec00017f0000c98d709bd000000070ad35229b9900727146bf801cee086d0ce8001a366a22072124a5600001e9864000d477d485d814445a32f8e65b8a49263d2e542a26c038a89d481055c396815832e43446d1fa
  | 31 => 0x8e4fa14d88001426dc142899057d636c00034fc00045100037ac0000000002e394cc0004f80000d8489925403d0ba80007149ee9eb2d9f0001a48000c235efaf61c08687000000000000000000000000000000001d46aef0000000aae000000000150881900000000005a713083540000000002e18ed4ab44741d2d0ca776285823459ea9d4cc800112000017000003be000000223c0004413a50000f94000558800061a00020d046cc000000db9550c4c344104afcc2ea00043500000000006cd3bc8df20000003beda0400012ab25400009c4580be998662f308000148a19f0001aa08f8d003489c28a5c1a855819d1e90872000000128646139580000000000002055bce2aa316b4e9a342c245e00011d400000013840000000002b840000000000000580e5e1123d598367cf7be970c0001316718ced33467726700012202d9225000013276d08d28584b8321627acd165642561293f400000000000000c4a82000357995a0001e514a58d80004db0000000ce27a0000000073544b9508a587d9614800150291b733000062417444c000000030857a80001940006dc37bdce4075000000000035000021cdc3810147212641b200053a9395232000000153c000a7e00000000000007c7b6d91768773bdb3b02ccdd5531101088cbdd4730a6520218e0360d38f8a1ce031800000000072e1578b040004ac800000000009d820c000f7c7c901840005cb2239fcdf40c211ed8dc05be000280000077237a4c4b7a80002f442e201800000076a14e1b0e0000000000bfca801020001c481fc65a190d2ba3192e02e003b875b2f2a1bc0000006a78b58792ee100000006da50e00000608e8b3718e3cc800000045f80000001200000000f6056672a224419851700023bd7f6e283bc1bd51e893e00024c80000002a730754c2f700bd0ae5a947f02520acde74dbf35a85240f44382ef00000a8c911f000000000004e82f6800000059426b0f3e40000000000000000000001a2ca0f000000183c936609177d2ae0004222f3049e00077137dcb480000a032c868a2367908f50000c261091bf4486de84d91cf91920004e434a8ba2a3c453b884070d7d54e1c1805676b0000000afe01448b09f87900006451d3556c0000002c18a7e0000000000f1a6d62d30a9569801e287b19400000008700014c8000000188dd8a8a93d60721e203bf63c800146200076c1468000000516399c000c5000000000000000000001226c0f0fb92940ec32242c8000000000508182400036a00000000de0006073e299285f95c42c6546c00014eb86c2a09453271d9c2a603f1f13c3458806d37b364559abcb1d50048cc856e11c0261c5ee9a04293c40000006ec13f9ca00900002004cdec68000000027c7680000144000a3937720c9514ca9303002c000d2600990fc00000
  | 32 => 0xbc00000007cc00063e0d3c000db7157800150ad7a5a110c40000000002c80a18f6b71b3cbc79c03a0003b2880c0005e5213952448707521e4bc6e481dc00011a0f960000001442b0b00000000007256ee8000cb80000001b787140002920001e845201c59afcdfcae96c512880004c030b101c33696555100018e200006b800000015845239a0b1cd5300007e957285210e8edca4e00025c000004e00026b27c5b08d666f7309ce601af3a702b801ee3b1c31cb1a12c3c446bde05b07ef000057121a26b1daaf0c900dba65d9a8d9e60e621b803558e0000f491c03a035674f80013ac00000009d80005f81e9b7d8d1abf80e09969080b1f2a980019aef05345369092200000004d0eae5e20de33dc05e0006b2b505d20e310003cd045a379000211c06a0000000fa124ec4d00038141f838442c1c04b327650a1947c000c1a2ac000121ca4900000006340002afb4ccc4263d0788d7ce8c81e75b84583b680f01924f1552de35eaa494534f160000350b52e9e0003864000b2900012dc2ce2b5000000000079910091ad81a0007303be89d8000710006405a1de4a880000005520003cf0000aaa4cc000104673b42a2b18000b034bc19002f89b3470b2081f0a1b457ad959ecfaa7c39e49c6ef1f649000000035d000000106a0005ca32711da4fb4c426bc45c2bb0003a44000ecd20916bcbb08077229720a6af08067a2d5228fa800000013ba00000000004ce00000035b40002494cb8000000ae8000000000053006f05c4000f6d0000000a9200074980000000001fb194c164d2f0002dc80005a800000000000000002d5d6ce0004a48ab17da2ad000000000000024b2ff0000eeb63f0fe800063a68c3b4560400045333240008f70001e2c0000006f8800000000074580019fa0006e4a54dcf0cdc00038f92eeb8700003586b244900000000004232f39b1c8a836802cb0c80004fa7b509d014a92815180080000000000000086534339034d4a600014600000000000000000000b5f00000015cc000000000025479a0000000000000024ae61a4a00000034f80000003de800028aae717c000020a0004fa800092a9ce5789bfc00000067037edf0457458f1c2c570000000000135a00000000005c456b00011f40002154250fccfa67c8000000016032d7cda92c6806822271484b02ec44848ff984044c5b41fd4baeb4015f1cfddd499271eb2ddc1ccce40b83888fc04d02da06d804c2c0961ec49080000000539c80479000000107821e00033799a20002c394cd118aed4891f8c3aaab325aa4f54d2cf909b80000009a823b116101408e26a0000b2e0000000000ac80000000a9d474b364bfa321eae00000000011f2ba22758569e6a6e06f900d800051204200009a65ee1d49f5c0d4e3f72b800000000003900002a8000000387800049f0a900
  | 33 => 0xaada787837ac000016a2354f500012e000074196f8af43f100000000006560f30938000ed544700019b2347126907c000000000000149e42d1a9b4480007880aeaf257b2f6116a1005d8e33602916cc4de9f77d910d518a0003d2873de3692d00027b579097b6aa39440000007af3411630b3f36e8a058d23b12d5a3380000ed76025400000003631e6000000076914b5948d8c15119212045262ad9ffd5b653d3711324cf83dd26ca40d356871468a0e46547040001ef1a8a502027838c000e1317400003861ee4da1c68662b6f1f4be389042d72388c112cc0000000000000e073419ff81be1f104a99c400000000000002aa9fc00018f10960e058b37f1aea00000017c8b8c37535baf847180000c48838000f5469800014bc82b00000000003105b505e000059a2fb32ac00039100032f5414110000000000000074b37fc152bb34130231714ad305b2d4435c5771088000000ef30002de575abb20000000368000000005c00000003f30bc000c5230f0000db40000002d70c380910000000000000461b6d156e0005daa9dc87cb410002419f3200060b0000000f9313cb1fc000718000000000089b73a0884fe4bd766680000009a970e800000000008e0c2c000b635b125f8054a5953ca9313600a10a232882469752fb937cc88f0361b171c964923120162c4960e83e00d6992ce037c01ef8b1e23937600002e6000576133c000000000039cbe80003ab00009685c168e93149300004980000c8a7e931400003babe500021a0f1ebc43948000564000000339997200015b1ba84b28754540058000000000000000003c4c8305c9341910a12d791be270488b2754689df129b9b8000d5a39c14207d4a1469e800197e5a212fab714e0f0c6838c5ce46ab578787a14d4c6d0129ae4d9e98168819880000006c3181c0002080001c3c0008ba46dbaf40001a70002d840006ed0002c4c730e826fe8df80000001189239ef2a370000001c4e00000021e0d2e1b376fae140003f53150000000000000017cf9c0000002ef511600000029407c848101122040003da24eb96c00000000017082d8000000000145c8d200021400000000001f34000654429800052a00041600013b84cc148a87829a7964210505c8200021700007ce0006d50000d3ccea1c3a688f0cd0e46202b55127fb0001618806c4e2a32d0d7700000000000000cd30000f1867efae3091becec6cc1282b53809698275e38b86407a43e1193d860157289b9102482ec64383e869af7e56b03618c68fb6ec88f1f125676d9b2a1070d8b78c34ec2f62ba5bf0ba49840dd0001e8c0008d75c4a0a9e7c1d3383a85c8ac55a0eb32e1040b7c6e680000000006cd800113a0000000000e20f0738700000004ab43e000078eee639980000000003708000000e790000001716f0400017398145
  | 34 => 0x1187f0d0529e1051cea4786d42fe9782c5c5202e71b460000001f8400074700012a8000b500002d692f800007ab3c49bc8ff1b49458ff4f2d1a484a4068b0060fa530000a8f4b1800000000000034b9646a9100000000000000000000fc0e2b500b4a1a9a0006ae000000039553e951d9549002c00001f3c0005878000000c8e54b2b21a5a5d36f28bb47e04573c01ab90200000000c3c0000001e9189c0000000930001c200000002b900002980cc9ee15e44222a5a33cd2a98300000002d600000000005f2b2d34f8c1d9987b41470f402be0660000b1400000000039a80000000002d98000ccb0000ee80000001a094bcf5000037900015fa0bd1b936500007b70002b300000fe0000001ce234c1801f69164dc361ca62d5fedf5498832009463f0000000f08f9411b80016c84756208b71eea12e777095987c088000220c0000000000000ed286116ebe75d2a33c69398c12d01a67933790bf62a800023c80005b258aae0cd481610002f1de040002702b2c0000003103124000daf6ed3e34000000600a3f40002e400017640000006dc80018d600000006209c8ea60770fac99aa605e30001526d6005f35d06aa0002e8000000051c16d0000cfcd3800000017ce545326b6f90e0e3c3f2a9b40001c202284488ca83705035bc0000000b8000063000077480000006864c88000000ee355f3c8800000000011a0000f8625b183d9ba2de503131cc3a00061db7483800003fca38df16cf04e3000103a646000000169e0001a33c8cc1490f35d80000000000002ac91680002641c09b1000041f80000000000000000be2c430000000000f7b35d0ef492600077e0000000cd533c207030c9a4421a72c36a0005babdd93e695e504a4e93ae3ec000363c00074975000000000000000001d96a4200003182ee06447100016382c848aafd05165076e98001f440002560001eb60007670001cf60656f60000fd600062b9f1148e0006428a51e260000000000000000000000000000052c00011fccae00000009f29242a4000000000064c99e40007710003ab978414b6758ac000009e00016d0724bd024f03059feaf03f200014e69765f43a1d31c5697cc0ea1f06f3b0000c54192f550000444bf4021506ba240000000002f01be04f67768a14780e700000b94000000000000124c1071bbb5ec7f20007c295d4000000000398d32886c00006f8000f8420ab79800082e6640a1d0d64e37b630c47828cd46f09cd454c7001601713a80a45713989546b606501c003741a53f70000edcd1e221ac5d4d8a0007e8001708724000000036c00020c0000664e0d34e120d99e3af19d0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9f287dc540440037610ea0a808800b6c21d415011000cd843a82a022001bb28650540440037610ca0a8088017ac219415011002f59bb282a022002db2765054044005b60eca0a8088017ac1d941501106cf9932a82a022000f3165505404400176706a0a80880036cdcd415011000759b1a82a022000eb163505404400176704a0a80880036cdc941501106c79929282a0220d8f305250540440013e10e98a8088002ec6113150110007c8a1a62a0220009f08748540440017630890a8088003e850921501100be3c3b2ca9822000e586359530440716d104b2a6088136dce05654c1100beb838aca98220029f081dd13044001b6483ba2608800a3e219744c110014f840ae89822000e9a43d9130440091f10eb226088003a6591434c110014f840ee49822000ad8864c93044071e90a4992608800a7ca1f714c110004f843a829822000db1745053044001f2286a0a6088006f421d314c110016e843a6298220019d0874c530440037a50c98a6088006f4219314c11002768432629822004ed3764c53044005ba4ec98a608800b741d9314c110027683b26298220d7f52654c53044001ea2ca98a6088002f4e11314c110005e8c22629822000dd3744c53044001ba2e898a6088003b4d91314c11000768b22629822000bd3824c53044001ba6e498a608835bd4949314c1106b7a82926298220009f08748530440017a30690a6088003f04c9214c1103163c3b6ea9022000d7071dd5204400f2f10eb2a408805f1e1d9654811003db4412ca902204db7381595204402fae0e2b2a40880031ee1d654811001d3c43aca9022000c788759520440070f10eb2a40880039ae09654811001d3d412ca9022003a78825952044001cd104b2a408809f1edc9654811013f35b92ca9022000e6a425952044001cd464b2a40881369ee05654811000739c0aca902204fe6b21595204409fce442b2a408813f9a48565481100073890aca90220029f081dd120440051f10cba2408800a7c2057448110014f840ee690220028f8865cd20440053e102b9a40880039a597624811000734b2a849022000e69654c920440053e50fb8a40880027c21d4148110006d8ba2829022000fa14250520440013e10e98a4088003745cd3148110007e0992629022001be0874852044005bc10e90a40880067821d214811000df1432429022001be0864852044007dc10c90a408800fb8dd92148110016f13b2429022002de0764852044007dc0ec90a4088003d8e1521481106afb042a429022000f637548520441abec0ea90a4088357b8d9521481106afb132a4290220d5ee1654852044001ec2ca90a4088003985952148110005f1c22429022000be1844852044001bc6e890a4088003785d12148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0x20b2ac48801a1fa1f755891001c3f416eab12200387c82dd562440010ff03baac4880021f60775589100043fc06eab12200087d80dd562440011df04baac4880021fa1c7558910006363aee4b1220018fa87dc1624400d0f90bbb2848801a1fa1676509100043ec2ceca122000c6c529d942440010ff0abb2848801a1f21576509100046fc1aeca1220048dc835d9424400d0fd0a3b284880021f61476509100246f418eca1220008dd831d942440018d8a43b284880021f61b7550910004bac0eeaa12200097980dd54244001ae021baa84880021fa1d65509100043e43acaa122003a6c8259542440071790eb2284880c6a720d645091000716292c8a1220058ec8758942440654d90ab12848801a1f217764c9100343f42cec992200087d859d932440018d8a53b264880021fe15764c9100343e42aec99220008bf845d9324400b17908bb2648801a1fa14764c9100043ec28ec99220058be841d9324400117b083b264880031b148764c9100043ec36ea992200097581dd532440012f301baa64880035c043754c9100043f43aca992200087c8759532440074d904b2a648800e3721d634c91016d4e422c69922000e4c5258d32440091d90eb1264880ba9b215624c91013e3a3b2caa0a2000e3464595414407f6c904b2a828813adce01655051013eb8382caa0a20019f080dcd4144001ba461b9a8288003a5d0f635051002c7a43ac6a0a2000e956350d41440033e101b928288002ad21942505101ff9229284a0a20019f287dc1414404f8e8ecb2a62880039518d654c5101edb2412ca98a204eb7380595314404fae0e0b2a62880067c203744c510006d9206e898a20018f4865d131440033e100ba26288003a590f644c5100247a43ac898a2000e956450d31440033e101b926288002b5219324c5101efa22926498a20019f287dc131441458e8edbaa42880035c1c3754851003cba43aca90a2027c7476595214400f6c904b2a428813adce01654851013eb8382ca90a2000c778759521440074e90eb2a42880031d21d654851001c3a43aca90a2000e678259521440074ed04b2a428800e9d209654851000732412ca90a2017c7772595214402fccee4b2a428800399909654851000733192ca90a204ea77805952144001ce700b2a428824b99c81654851049739102ca90a2092e652059521440033e101ba242880063d219744851000cf8402e890a20019f080dcd21440031e90cb9a42880067c201734851000732b2ec490a2000e65655092144001ccaca99242880067ca1f70485100be3c3b2caa022000e386459540440756d104b2a8088136dce0565501100beb838acaa0220029f081dcd4044001ba463b9a8088003a6d0f635011002c7c43ac6a022000e996350d40440053e103b928088002ae21942501101d79429284a022002
  | 2 => 0xc52d911001e36390a5b222000a758114b64440014f300296c888003171ce65591100062e39acab222000a6c8259564440018bccbb9ac888003175977359110006e8086e6b2220008df835d564440091b906baac8880023be09755911001c76412eab2220048de87dcd64440018bea3b9ac8880031754773591100062fa86e6b222000c5d50dcd644400193ee839ac88801a1fa1772591100043ec2ee4b222000c5f73949644419d8b8e7292c88800317dcc52591107062e398a4b222000c6f7214964440078d8e4292c8880029d60452591100053cc00a4b22200796c825d7634409b2ef02baec68813a5ee0175d8d10006b8082ebb1a200087d8799763440010ff0eb2ec6880029b20965d8d100043ec3cebb1a20008ef825d763440071d904baec68801a1fe1d75d8d1000536412ebb1a2000c6f825d763440070f904baec6880031b20975d8d1001c36412ebb1a204d87f815d7634404f0fb02baec68813a1fe0175d8d100bc3ec02ebb1a200087f855cb634400d0f90ab96c68800e1fe1e52d8d100043ec3ca5b1a200387f8714b63440010fb0e296c68800f1b1c852d8d100053ac08a5b1a2000a798014b6344001878e932ac6880030f1d16558d1000536412cab1a2000c3e65dd1634400187acbba2c6880036c0437458d100045fc22eab1a20058bc845d563440011df04baac68800e3b2097558d1002c5f43ee8b1a2000c3f51dd1634400187aa3ba2c6880030fd437458d100061ea86e8b1a2000c9c74dcd634400d0fd0bb92c6880021f6177258d100061fba4a4b1a20d3c3c74949634400187ee8292c68837f0f1d05258d1000637b90a4b1a2003c6c7214963440014eb02292c6880029e6005258d100343f42ceca1a200087d859d94344001938873b286880022fe117650d100046fc1aeca1a200687e851d943440010fb0a3b286880032710c7650d1001c77410eca1a20008ed821d94344001c3886b2a86880d69b2096550d100245e43ac8a1a2004a9c83591434400b1b90eb1a8688016a72116350d100343fc32ebb12202787d865d7624409b2ef02baec48813a5ee0175d8910006b8082ebb12200087d87997624400f4d90532ec4883769d60665d89106e53cc04cbb12200087f87597624400f4d904b2ec48837b9c04165d89100043ec3cebb1220dda75819d762441b94f3013aec48801a1fe1d75d891000637c12ebb122000c6c825d7624409b0ff02baec48809e1f60575d89102743fc02ebb12201787d805d762440011bf06ba6c4880123720d74d891000636292e9b1220008bf845cf624400b17908b9ec4880031b14973d891003d3742ea5b122000d7010dd5624400f0fd0f32ac48800e1f21e655891003d37414cab1220dba758199562441b54f30132ac48800e1fa1d655891003c3e43acab122007a6c825956244125ce
  | 3 => 0x8b2a2000a6e829d165440014db053a2ca880029d60674595100053cc04e8b2a2000a5f835d165440014b906ba2ca880029be09745951000536412e8b2a2000a77815d165440014f700ba2ca880029ba0a735951000536c14e6b2a2000a75819cd65440014f30139aca880028fe1173595100051e422e6b2a2000a6f825cd65440014d904b9aca880029de0573595100053dc02e6b2a20c9c6c72d0d65441958d8e521aca880021fa1c43595100043ec3886b2a2000a6e8210d65440014db0421aca8838f1b1c843595100bd3b40886b2a2000a758110d654404f4f50021aca880029e600435951001c3f43ee4b2a200386e87dc96544001ccf03b92ca8800399207725951000637b8ee4b2a2000e6b80dc96544001cd101b92ca880031bdc3725951000537414e4b2a2000a75819c965440014f301392ca880029de0572595100053dc02e4b2a2000a3e841c9654400147b08392ca8800297a0c72595100052ec18e4b2a2003c6e721c965440018dae4392ca880029ba1c725951000637438e4b2a2000e2e841c96544001c5b08392ca880031bdd07259510006373a0e4b2a2000c6d741c965440018d8e8392ca8800393a0c725951000726c18e4b2a2000c6f731c965440018dce6392ca880031b5cc725951000636398e4b2a2000e66811c96544001ccb02392ca880031bdc4725951000735400e4b2a2000e69801c965440018dee0392ca880021fa1f42595100043ec3e84b2a2003c6c72d0965440014bd07212ca880029760e425951001e3639484b2a2017a768190965440014eb03212ca8809e9ea0242595100053cc0484b2a2003c6c72109654402f4ed02212ca880029d604425951013d3d40084b2a2000a798010965440010fd0f992ca880021f61f325951001e3639664b2a2000a3e848c9654400147b09192ca8800f1b1ca32595100bd3b40c64b2a2000a75818c9654404f4f501192ca880029e602325951001e3639064b2a2017a76810c965440014eb02192ca8809e9ea0032595100053cc0064b2a204dc7687dc565440014eb05b8aca8800399dcb715951000732396e2b2a20e2c7770dc565441c5ce441b8aca8809f1ea1f70595100053cc16e0b2a2000e6b72dc16544001cd0e5b82ca883871edc7705951000739b8ee0b2a20e1e7221dc1654400f2d904baec8881365de0575d9110274bdc02ebb222000d70105d764440010fb0f32ec8880021fe1d65d911000536412cbb22200087d879d764440011df04baec88800e3b20975d91100343fc3aebb222000a6c825d764440018df04baec88800e1f20975d911000636412ebb22200386c825d7644409b0ff02baec88809e1f60575d91102743fc02ebb22201787d805d764440010ff0ab96c88801a1f21572d911001c3fc3ca5b22200087d8794b64440070ff0e296c8880021f61
  | 4 => 0x480036d10db92a0900635a9db72541200c6b43b6e4a824000b6984dc950480016d307b92a090002da6077254120006b5c3a84a824000b6a8750950480016d10ea12a0900035a21d425412000db543284a824001b68865095048065cd6eca12a09000f5a9d9425412001eb43b284a824018e687650950480078d0eca12a09017adae1142541200c795c2284a824051f2a745095048001e52e8a12a090003cad91425412028f9432284a824000b6b8350950481cde5486a12a090147ca10d4254120005b5c0a84a824051f2b415095048001ad70e992a090002daa1d3254120005b443a64a824000d68874c950480036d50c992a090006da219325412017735bb264a824003d6a764c95048007ad0ec992a0900639a1d9325412001e343b264a824000b6b844c950480016d308992a09016adae0d32541200c7a5c1a64a824050f4a734c95048001e92e6992a090003d2d8d3254120287a431a64a8240e5f4b434c950480a1e9086992a090002dae053254120287a598a64a82407ec7876dc550480316d105b8aa0900035adcb7154120006b4396e2a8240e497a86dc55048001ad705b8aa09000e5ea0b715412001cbc416e2a824000d6882dc5504809b8f6c5b8aa0901375ad8b7154120006b5216e2a824000d6942dc55048001ad465b8aa0900035a4cb715412013cbcc0ee2a82404fd6b21dc550480014f70cb8aa0900629e21971541200563c3b2e2a824000b6b825c550480316d104b8aa0900035adc97154120006b4392e2a82405497887d8550480a98f0edb0aa0900025ee1d615412005cbc43ac2a824007c787658550480856d704b0aa09036b9c18561541201263c3b282a824018b6a825055048001e5284a0aa0900831e1d931541200c5b541262a824000f49324c55048001ad70e90aa090002daa1d2154120005b443a42a824000d688748550480036d50c90aa090006da219215412001eb53b242a824003d687648550480016d70890aa090002da6112154120005b5c1a42a824000b698348550480836d70290aa090063d8e0521541206d6b5b8a42a82404ff62714855048001ec2e290aa090003d8d85215412027fb030a42a824000c6c7299165440014bd06322ca880029760c645951000537410c8b2a2000a6d8219165440018d8e4322ca880031b1ca63595100051f420c6b2a2000a3d8418d65440014dd0431aca880029b608635951000636390c6b2a200796e87dc965440018deedb92ca88003d8043725951000637bb0e4b2a2000f60101c965440078d8e5312ca8824a9d606625951027d3cc04c4b2a2000a3e84189654400147b08312ca8800297a0c62595100052ec18c4b2a2003c6c721896544001acee5b8aca88003591cb7159510006b5b96e0b2a2000d6872dc1654404f6e503b82ca880035cdc770595100061fba4e
  | 5 => 0x34f1b1db755092075d37436caa124061c6c76d954248001c58cbb2284900031b197735092001cd6c26e6a124005aae84d8d424800b1d90eb1a84900ca9b215635092076537436ea99240cec6c76dd532481d74dd0db2a64901871b1db654c9200063632ee899240039cd83dd132480031d90cba264900031b195744c9202c6c621ae89924004ace83d9132480091d90eb2264900ba9b215644c9200072632ec69924000a7581dd761480014eb023aec2901529e60075d85200043fc2ae9b0a400687c855d361480010ff0ab9ec29001a1f21573d8520196363aa85b0a402ec6c754cb614800d0fd0dbaac2901861f21b75585200043f43ecab0a400087e8719561481d58dee432ac2900021fa1a76545200053ac0ceca8a4000c75819d951480018ec433b2a2900031d486765452001c3ec04eca8a4000a6f825d951480014ef02bb2a29000e1fa08765452001c3e410eca8a4000c6e421d951480018dc643b2a29001a1fe0476545200343ec08eca8a4000c6f211d951480018ec423b2a2900031b48476545200063a908eca8a400387f801d951480018f5003b2a29000e1f60076545200063cc00eca8a4000c6e201d951480018d8403b2a2900031e84076545200063c880eca8a400087f8759151480010f90eb22a2900021fe1d63545200043e43ac6a8a4027a6c8650951480018d8eca12a29009e9b2193254520006363b264a8a4028a78865c151481d36e702b82a29001a1fa1776505200043ec2eeca0a40028bc87591414800556902b2282902bf8b19542505200343f42eec98a400087d85dd931480051b90eb1a629000ab5205634c5205372632a6498a40a1c6c76dd521480c38d8edb2a42900063b21974485200147643ac890a40018ec865cd21480051d90eb1a429000ed9a1d514852001db243aa290a4000e678654521480016cd0ca8a4290002d9219514852000732432a290a4002e67765452148005cc8eca8a429000399d91514852000732b22a290a4000e67635452148001ccac6a8a429036ed9e015148520497b1402a290a4000f61805452148125ec0e0a8a429010f99d815148520147b1b02a290a4000f6151dc121481218f0edba2a090062da20b74541200053dc32e8a824018a78865d1504802d8f0ecba2a090002dae0974541200c5b4412e8a824060c7876d9150480012f70eb22a09002e5e21d64541200a63c3b2c8a8240e8e386459150480bb6d704b22a09022b1e1db73541200c5b4416e6a824000a7b865cd50480314f10cb9aa09004b1e1d97354120005b5c12e6a824018b68825cd50480b98f0edb1aa0900025ee1d635412005cbc43ac6a824010c787658d50481cfcb0c6b1aa090166dae0963541201ae3c3b286a824050f184350d50480316d504a1aa09018edaa1f72541200c6b543ee4a824001b6a86dc95
  | 6 => 0x53bc0aeca8a6000a7781591514c0054e902b22a29809e9721943545301570e32286a8a600087e87d89514c0010fb0fb12a2980431b1cb625453013d2e43264a8a6010d4c724c9514c04f6b100992a29801a1fa1476505300043ec28eca0a60038ee821d9414c0011db043b2829800a2f21d64505300064e3b286a0a6000d9a40dd1314c0031b90cba26298003a5907644c5300146e43ac898a6000e9564505314c00d0fd0b3b242980021f616764853000c6e432e690a60019d8805cd214c0d3a98ea99242980425d21d514853014733312a290a6000f4532545214c0037310ea1a80980136621d435013000dcd43286a026001b988650d404c00bd310ca1a8098017a6dd94350130026cd3b286a026004d987650d404c00bd30eca1a8098013261d94350130005cdc1286a0260eff1a5250d404c1dfe30a4a1a8098002e6e0543501307778da8a86a026000ab886509404c00b970eca128098197ca1494250130004ec43a64a026004cd8764c9404c001733089928098197d21493250130007c4a1264a026000d9943dc5404c001d3287b0a80980a71e1d951501300078ca1aa2a026000b99844c5404c001f228298a809814e5ee0171d952005c3ec38c3b2a4000a3e84187654800147b0830eca9000297a0c61d95200052ec18c3b2a4000c757118765480c54dd043a6ca901869b60874d952031537410e7b2a4061a6d821cf65480010fd0e21eca900021f61c43d95203153741087b2a4000a6d8210f65480014ed0221eca900029d60443d952030d3d40087b2a4000a798010f65480070fd04b8eca9000e1f20971d952029c3fc02e3b2a4000a3e841c7654800147b0838eca9000297a0c71d95200052ec18e3b2a4062a6e821c765480c34db0438eca901869ea0071d95203153cc00e3b2a400087e8790765480010fb0f20eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca9018a9ba0841d952000536c1083b2a4061a7a8010765480014f30020eca900021fa1e31d95200043ec3c63b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4062a6e820c765480014db0418eca901869ea0031d95200053cc0063b2a40ebc6c7219764480071d904baec8900021fa1f65591200043f438cab22400687e87dd564480010fb03baac8900021fe0375591200043ec06eab22400087e871d564480010fd0fa8ac89001a1f21f515912075e36390cbb1a40038ec825d763480010fd0fb2ac6900021fa1c6558d200343f43eeab1a400087d81dd563480010ff01baac6900021f6037558d200043f438eab1a400087e87d45634800d0f90fa8ac69001a1fa177650d200043ec2eeca1a400087f855d9434800d0f90abb286900023de057650d200147a40aeca1a4000e1c43d9543481db4dd0dbaa849
  | 7 => 0x6e211d921540018d8423b242a801a1fe0076485500343ec00ec90aa000c6f201d921540018f4403b242a80031b48076485500063c900ec90aa000c77101d921540018ea203b242a80021fe1974485500043e432e890aa00087f865cd21540010f90cb9a42a805e5b21d4248550006363b28490aa01796c874c921540018d8ec99242a80625d21d61485507c5b9c02c290aa00087f855cb635000d0f90ab96c6a00029d60452d8d400053cc00a5b1a8004a9e86d8d4350197938c7b9286a00021f61e75d89407bd3cc04ebb12800687f875d762500010ff02baec4a03da1fe0175d89400d43ec02ebb1280038bc845cf625000d0ff0fa8ec4a00021f61f51d89406961e3b6eaa128014b2e82dd54250001a70e1baa84a03d74b14b735094000cdc406e6a128075b2e85d89425000337101b8a84a00066ea1f70509407a794296e0a12800687e859d932500010fb0b3b264a00062f219744c94018e4e31ae89928079d2c525d1325000337100ba264a000e37a1f634c94000726296c69928075d2c755093250063d18c6a1264a0013271cd43d85400043fc2ae5b0a800687c855cb61500014eb02296c2a00029e60052d85400071629285b0a8000a75819d951500014bf06bb2a2a00a69720d765454000537c12eca8a8028a6c825d951500014ef02bb2a2a009e8f219435454014f0e31a86a8a800087e87d8951500010fb0fb12a2a00531b1cb625454013d1e43284a8a8014d2c72509515004f67100a12a2a0003668c373505400074b18ec6a0a800687e851d931500010fb0a3b262a000e3ba08764c54000476c10ec98a80018bc865d13150001938eca1a62a001a1fa1676485400043ec2cec90a80018bc865d1215000337100ba242a01d74b1d542485400a4ba43aa290a8028e66625452150001e4a84a8a42a00021fe1572d91300343e42ae5b226000a758114b644c0014f300296c89801a1fa1772591300043ec2ee4b226000a7581149644c0014f300292c898016a7a1b6450d306864e326e4a1a600087d879d7624c1e74f3013aec49801a1fe1d75d89300043fc0aebb1260f287f805d7624c0330fb00baec49800e3720d74d89300343fc3ea3b12600087d87d47624c00d0fd0b3b284980021f616765093001c5f43ec8a126000e2c52d91424c19b8b8edbaa6498042d3a0b754c930006ac386ea99260f1d4c52dd1324c0033b101ba2649800637219744c93016e4e322e8992606dd4c525d1324c0033b100ba264981a6d3a17624c93034da642a84992602de8c64509324c0033b101b8a649800676a1f704c930787a4296e09926005c9c7450f614c0010ff0ab96c29801a1f21572d85300053ac08a5b0a6000a798014b614c001c98a4996c2980029d60676545300051fc22eca8a602aa3c845d9514c0014df04bb2a2980a29b20976545300
  | 8 => 0x239ec2a80021fa1c43d85500043ec3887b0aa000e1d4310f61540014dd0421ec2a80029b60843d85500bd3b40887b0aa000a758110f615409b4f50021ec2a80029e60043d85500053ac0ee5b0aa04da7a809cb61541fb4f301396c2a800e1fe1d72d85500051f420e5b0aa000a3d841cb61540014bd06396c2a80029760c72d855001e37390e5b0aa000c6d721cb61540014eb02396c2a81369ea0072d85503f53cc00e5b0aa00087e87d0b61540010fb0fa16c2a800297a0e42d85500052ec1c85b0aa003c6c7290b615409b4f501216c2a80029e60242d85500043fc3a85b0aa00087c8750b61540078d8e4a16c2a81369ea0042d85500053cc0085b0aa00087e87ccb61540010fb0f996c2a80028fa1232d85500051ec2465b0aa003c6c728cb615409b4f501196c2a80029e60232d85500043fc3a65b0aa00087c874cb61540078d8e4996c2a81369ea0032d85500053cc0065b0aa000c6c72d91615400187ee9322c2a80029ba0a645855000536c14c8b0aa000c6c7299161541f94f301322c2a805e1f21d645855000636392c8b0aa000c6c7219161540018d8e5b1ac2a80029ba0a635855000536c14c6b0aa000c6c7298d61541f74f30131ac2a805e1f21d635855000636392c6b0aa000c6c7218d61540032f101b92c2a80625ba1f725855000636c36e4b0aa000d6b80dc96154001ad101b92c2a80031bd837258550006b5b06e4b0aa000c6f761c961540010fd0fb12c2a80631b1cb62585500073310ec4b0aa003c6c72989615402f4ed03312c2a83ea9e60262585500bc3e43ac4b0aa018c6c72589615400147d08312c2a80028f61062585500052f418c4b0aa000a5d8318961540018dee4312c2a800f1b1c862585500bd3b408c4b0aa000e662118961540032f50fb82c2a80035adcb7058550006b4396e0b0aa0f9d7371dc161540012f301bb282a800257e0d76505500ccae41aeca0aa00096f825d941540312d904bb282a80025ee0176505500bc9e43a86a0aa019d1c7350d41540010fd0db9282a80021f61b725055012636316e4a0aa01793c875094154049c58c4a1282a805ecd2054250550004bcc06ec98aa00093f845d9315403527908bb262a80025be09764c5500c4b6412ec98aa00097b805d931540012f700ba262a80065e201744c5500bcae43a8698aa01ad1c7450d31540010fd0db9262a80021f61b724c55010636316e498aa01795c874c93154041c98c499262a805ed5205324c5500ccba43a8298aa000f154350531540012f301bb242a800e1f60776485500063cc06ec90aa000c7a20dd921540010fd0d3b242a80025be097648550004bdc02ec90aa00387e821d921540070f9043b242a80031b908764855000637190ec90aa00387f811d921540018ed023b242a800e1f60476485500063ac08ec90aa000c
  | 9 => 0x655812183637b90cab02421e97487545604840f4e90ca8ac09091359dc9515812149738302a2b02421a87d8718b645403547d08316c8a80029760c62d915001e37390c5b22a000a758118b64540078d8e5312c8a806a8fa1062591500052ec18c4b22a003c6e7218964540014eb02312c8a84174edd370591500cc3ec3ec9b1aa01987d8718b635400147b08316c6a800f1b9c862d8d500053ac08c5b1aa01987c8759163540078d8e5312c6a80028f6106258d500cd2f418c4b1aa003c6e7218963540014eb02312c6a841356dcf7058d500c4b7416eca1aa00096d82dd943540012f301bb286a80025ee017650d500043f436e4a1aa00087d86dc94354207a3887b9286a82365ee0174d895000cbc402e9b12a08797b805cf62540032f100b9ec4a81f25ee0171d895000cbc402e3b12a003c6e768876254205ad6e5b82c4a80025e603765095000637416eca12a000c6d82dd942540010fb03bb284a80031e60376509500063d106eca12a00087e869d942540012f700bb284a80030fa1076509500061ec20eca12a000c6e321d942540010fb023b284a801a1fe0076509500343ec00eca12a000c3f401d9425400187a803b284a80031bc8076509500063d100eca12a000c6d201d942540018f2403b284a80624f21d645095000716312c8a12a101b3b80591425403127b09b9a84a83271b18b73509500d4b743ec4a12a003a6e86d8942540012f301bb264a80031ba0b764c95000636c16ec992a00087d81dd932540018f301bb264a80031e883764c9500043f434ec992a00097b805d932540018bd063b264a80031760c764c95000637210ec992a00087d811d9325400d0ff003b264a801a1f600764c9500062f980ec992a000c5d301d932540018de403b264a80031e880764c95000636900ec992a000c79201d932540312bb07ba264a832b1b18b744c9500043fc32e8992a00087c865d13254103a3886ba264a80d71b189744c9500c4ae43ac6992a000e4c6258d32542016b700b1a64a80665ba1f624c95001d37436c4992a01996c8750932540014d90ca1264a80031b1d9424c95040f8621a84992a01787d87d93615403587ce9b26c2a80029ba0a64d855000536c14c9b0aa0ffa7980993615402f0fb0e326c2a805e1f61f63d855000537414c7b0aa000a6d8298f61541fd4f30131ec2a805e1f61c63d85500bc3ec3ec5b0aa0fda798098b61540010ff0eb16c2a805e1f61c62d85500051f420c5b0aa000a3d8418b61540014bd06316c2a80029760c62d855001e37390c5b0aa000c6d7218b61540014eb03ba6c2a80030fdd274d855000537414e9b0aa000a6d829d3615409b4f5013a6c2a83fe9e60274d85500053ac08e9b0aa000a7581dcf61540014dd0539ec2a80029b60a73d855026d3d404e7b0aa0fea79809cf61540014eb
  | 10 => 0xa1242039ad84dcd424840b55d09b1a84908163b21d63509211953642ac6a12430ca6e86dd5324859d8d8edbaa6490c2e9ba1b654c92150e363b6ca9924200c6c65dd1324840739b07ba2649080a3b219744c9210063632ae89924298d8c435d1324840959d07b2264908123b21d644c9211753642ac89924200e4c65d8d324858d8e8edba2a2908a2d920b74545210053bc32e8a8a4228a74865d1514844d8e8ecba2a290802d9e097454521145b2412e8a8a42a0c7476d9151484012ef0eb22a29087a5d21d64545211263a3b2c8a8a430ae3464591514853b6cf04b22a290b031d1db7354521145b2416e6a8a4200a77865cd51484514e90cb9aa29088b1d1d97354521005b3c12e6a8a4228b64825cd51485398e8edb1aa2908025de1d63545210f4ba43ac6a8a4220c747658d5148613ca8c6b1aa290a66d9e0963545211ae3a3b286a8a4293f144350d51484516cd04a1aa290a8ed9a1f7254521146b343ee4a8a4202b6686dc951484056c90db92a2908a3599db7254521146b23b6e4a8a4200b6584dc951484016cb07b92a290802d96037254521006b3c3a84a8a4200b668750951484016c90ea12a2908035921d4254521015b343284a8a4202b64865095148465cceeca12a29080f599d9425452101eb23b284a8a4228e647650951484078c8eca12a290a7ad9e11425452114793c2284a8a4294f26745095148401e4ae8a12a290803c9d9142545214a79232284a8a4200b67835095148611e4c86a12a290a53c910d4254521005b3c0284a8a4294f27405095148401acf0e992a290802d9a1d3254521005b243a64a8a4200d64874c951484056cd0c992a29080ad9219325452117733bb264a8a4203d66764c95148407ac8ec992a2908a3991d9325452101e323b264a8a4200b67844c951484016cb08992a290a6ad9e0d3254521147a3c1a64a8a4293f46734c95148401e8ae6992a290803d1d8d325452149fa231a64a8a4307f47434c95148527e8886992a290802d9e01325452149fa398264a8a427cc7476dc151484516c905b82a29080359dcb7054521006b2396e0a8a42e497686dc15148401acf05b82a29080e5da0b705452101cba416e0a8a4200d6482dc1514849d8eec5b82a29093b59d8b7054521006b3216e0a8a4200d6542dc15148401acc65b82a290803594cb70545210bcbac06e0a8a4292d6720dc151484014ef0cb82a2908a29d21970545210563a3b2e0a8a4200b67825c151484516c904b82a29080359dc97054521006b2392e0a8a42539748754760484a74e90ca8ec0908029e60375d812129d3ac08ebb024200a79801d760484010ff0aba6c09081a1f21574d81210043fc2ae7b02420687c855cf60484658d8eaa16c0908bb1b1d532d81210343f436eab0242a187c86dd560484010fd0fb2ac0908021fa1c
  | 11 => 0x4c40d0ff0ebaec498c4a1fe0575d893114c3ec0aebb12620087f805d7624c40d0ff0fa86c4988021f61f50d89310343f42ceca12620087d859d9424c40717d0fb2284988038b14b645093166e2e3b6ea9926220b4e82dd5324c401aa8e3baa6498c475314b744c931014ea40ee899262028dc865d1324c45b938c8ba26498aab53149744c931014ea40ae899262a6b4e85d89324c54d6990aa1264988b7a3191424c931014eb43ee29926310f4452dc5324c4053a903b82649880ae521d4350531026ca43a86a0a6202b968650d414c4057290ca1a8298817a5219435053102f4bbb286a0a6204d967650d414c409b28eca1a8298817a51d943505310264a3b286a0a6200b978250d414c61fe2ca4a1a8298c3fc51494350531005cbc0286a0a630ef175050d414c4015690ca1282988172d1d9425053152f9229284a0a62009d4874c9414c4099a8ec9928298802e5611325053152fa229264a0a6200f85424c9414c401b2a87b828298817271d143d81310043fc2ae5b02620687c855cb604c4014eb02296c0988029e60052d81310072629265b026200e9543507604c4a92ef02b86ca9087a1f61c60d95210051f420c1b2a4200a3d8418365484014bd06306ca908029760c60d95210063cb80c1b2a42a2a6e821d365485434db043a6ca90a8a9ba0873d952150d36c10e7b2a420087e8710f65484010fb0e21eca90a8a9ba0843d952100536c1087b2a42a1a768110f65484014eb0221eca908029ea0043d95210053cc0087b2a420387e825c365484070f904b86ca909521fe0570d95210051f420e1b2a4200a3d841c365484014bd06386ca908029760c70d952151537410e1b2a42a1a6d821c365485434ed02386ca90a8a9d60470d95210043f43c81b2a420087d8790365484010fd0e206ca908021f61c40d95210052f41881b2a4200a5d8310365485454dd04206ca908029b60840d952150d3b40881b2a4200a758110365484010fd0f186ca908021f61e30d95210043f43861b2a420087d870c3654840147d08186ca908028f61030d95215153741061b2a4200a6d820c365485434ed02186ca908029d60430d952185e36390cbb22420087e87d9564484010fd0e32ac89081a1fa1f75591210043fc0eeab22420087d81dd564484010fb01baac8908021fa1c75591210043f43ea0b22420687c87d4164486178d8e432ec6908021fa1f6558d210043f438cab1a420687e87dd563484010ff03baac6908021f6077558d210043ec06eab1a420087e871d563484010fd0fa82c69081a1f21f5058d210343f42eeca1a420087d85dd943484010ff0abb2869081a1f2157650d210047dc02eca1a42018f8805d94348401c3887b2a8690c369ba1b755092169e363b6eaa12430ba6e86d9542485438d8edb2a84908038b19764509210063632ee6
  | 12 => 0x8029ba0843d815100536c1087b02a24ea768110f60544014eb0221ec0a889e9ea0043d81510053cc0087b02a200a7980dcb605444f4ed03396c0a8c6e9d60672d815101c3fc3ae5b02a200a3e841cb605440147b08396c0a880297a0c72d81510052ec18e5b02a203c6e721cb60544018dae4396c0a893a9da0472d81513e53ac08e5b02a200a79801cb60544010fd0fa16c0a88021f61f42d81510052f41c85b02a200a5d8390b60544078d8e5216c0a893a9da0642d81510053ac0c85b02a20087f8750b60544010f90ea16c0a880f1b1c942d81512753b40885b02a200a758110b60544010fd0f996c0a88021f61f32d81510051f42465b02a200a3d848cb60544078d8e5196c0a893a9da0632d81510053ac0c65b02a20087f874cb60544010f90e996c0a880f1b1c932d81512753b40865b02a200a75810cb60544018d8e5b22c0a88030fdd2645815100537414c8b02a200a6d8299160544018d8e5322c0a8c6a9d606645815113c3e43ac8b02a200c6c7259160544018d8e4322c0a88031b1cb635815100537414c6b02a200a6d8298d60544018d8e531ac0a8c669d606635815113c3e43ac6b02a200c6c7258d60544018d8e431ac0a880a5d2077258151144b743ee4b02a200c6d86dc96054401acf03b92c0a880359207725815100637b0ee4b02a200d6761dc960544018deec392c0a88021fa1f625815114636396c4b02a200e6a20d8960544078d8e5312c0a8c629d606625815113d3d404c4b02a22787c8758960544518d8e4b12c0a88028fa1062581510051ec20c4b02a200a5e8318960544014bb06312c0a88031bdc8625815101e36390c4b02a227a7a801896054401cd440312c0a880359dcb7158151006b2396e2b02a20297a87d8160545f3ae6e3b02c0a88021fe1572d8d410343e42ae5b1a8200a758114b63504014f300296c6a0812a7a1b6350d4165e4e31ee4a1a820087d879d7625062f4eb033aec4a081a1fe1d75d89418b43fc0aebb12822a87d815d762504010ff00baec4a081a1fe1f50d89410043ec3ea1b1282d2c3c76dd5425044965d05baa84a08034d1c775509418ae96296e6a1282029b481dcd425055f65d0bb1284a080a6da1f71509418a792296e2a1282029b481dc1425040d0fd0b3b264a08021f616764c9410145e432e89928231c9c635d13250567a58a4ba264a080a6d205744c94101c6f43ec69928200e4c52d8d325055fa58eaa1264a08c7a318d424c9410264e39a87b02820087f855cb605040d0f90ab96c0a08029d60452d81410053cc00a5b028200e2c5250b60504010ff0ab96c89881a1f21572d91310053ac08a5b226200a798014b644c40d0fd0bb92c8988021f61772591310053ac08a4b226200a7980149644c40b53d0db228698b43271937250d310043ec3cebb126313a75819d762
  | 13 => 0x43f43ecab02640087e87195604c8550fb0e316c8a88aa8fa1062d91510052ec18c5b22a203c6e7218b64544014f300316c8a880f1b1ca62591511551f420c4b22a200a5d8318964544078dce4312c8a88029e600625915191e9bba6e2b22a22987d87d9363544530fb0e316c6a88028f61062d8d5101e37390c5b1aa200a798018b63544530f90eb22c6a880f1b1ca6258d510051ec20c4b1aa229a5e8318963544078dce4312c6a88029e6006258d51916abb9ee2b1aa22896e82dd943544012db05bb286a88025d6077650d51004bbc0aeca1aa20087e86dc943544010fb0db9286a8c874710f7250d5161cbbc0ae9b12a202974815d3625457b2ef02b9ec4a880a5d20573d89513f4bbc0ae1b12a202974815c362544078dced106c4a8c8359dcb7158951004bac0eeca12a200c6e82dd942544018db05bb284a88031d60776509510063b10eeca12a20087d80dd942544010fd0d3b284a88025de0576509510061f420eca12a200c3d841d942544018dc643b284a881a1fe0476509510343ec08eca12a200c3f411d9425440187a823b284a88031bc8476509510063b108eca12a200c6d211d942544018ea423b284a88021f60076509511449e43ac8a12a200e2c62591425463f66f02b2284a88a24f613735095164e36316e6a12a22a96e87d8942544074dd0db1284a88025d607764c95100637416ec992a200c6d82dd932544018eb03bb264a88031d887764c9510043ec06ec992a20087e869d932544012ef02bb264a880317a0c764c9510062ec18ec992a200c6e421d9325440d0ff023b264a881a1f604764c9510062f988ec992a200c5d311d932544018de423b264a88031d884764c95100636908ec992a200c75211d932544010fb003b264a88a25760f744c95165636316e8992a20087f865d132544010f90cba264a8adf4710d744c9511ae36312e8992a22895c8758d3254401c98c4b1a64a8c7ad5e05634c95114cb743ec4992a203a6e86d8932544532d90ea1264a88029b219424c951006363b284992a2b7f0c43509325444f0fb0fb26c0a88ab0f9d364d815100537414c9b02a200a6d82993605463b4eb03326c0a889e1f61c64d815113c3ec3ec7b02a200a6e8298f60544014db0531ec0a8c729d60663d815113c3ec38c7b02a22787d87d8b60546374eb03316c0a88021fe1d62d815113c3ec38c5b02a200a3e8418b605440147b08316c0a880297a0c62d81510052ec18c5b02a203c6e7218b60544018dae4316c0a88029e60374d81510061fba4e9b02a200a6e829d360544014db053a6c0a889e9da0674d81518ed3ac0ce9b02a200a79801d360544014f301b9ec0a88029ba0a73d815100536c14e7b02a227a76819cf60546394eb0339ec0a88029e60073d81510043f43887b02a20087d8710f6054401c3a8621ec0a8
  | 14 => 0xe82dc7654c99d4db05b8eca990031b5cb71d953200636b92e3b2a640087f805c7654c80147d0838eca990028f61071d95326752f418e3b2a64cda5d831c7654c99b4dd0438eca9933a9b60871d95320053d400e3b2a6400a79801c7654c8010fd0f20eca990021f61e41d95320043f43883b2a640087d87107654c99d4bd0620eca990029760c41d953266d3741083b2a6400a6d82107654c8014f50020eca990029e60041d953266d37416e1b2a64cea6d82dc3654c8018dae5b86ca990031b5c970d95320043fc0ae1b2a6400a3e841c3654c80147b08386ca9933a97a0c70d953266d2ec18e1b2a64cda6e821c3654c99d4db04386ca990029da0470d95320053ac08e1b2a640087e87903654c8010fb0f206ca990021fa1c40d95320043ec3881b2a64cea5e83103654c8014bb06206ca993369ba0840d953200536c1081b2a6400a7681103654c8014eb02206ca990021fa1f10d95320043ec3e21b2a6400c7571c43654c8010fd0f086ca990021f61e10d95320063cb8421b2a640087e87043654c8010fb0e086ca990028fa1010d95320051ec2021b2a64cea5e83043654c8014bb06086ca993369ba0810d953200536c1021b2a64cdc5d73d97644c801c3e87b2ec89933f175cc65d913267e36390cbb2264038dd83dd7644c8091db05baec8990031b14b75d91326553742ea5b226403ccd73d4b644ca618bae7a8ec89932a9b20b51d913297e2eb9ea1b2264caa6c82d43644c8010fd0fb2ac8994938710f65591320043f438cab22652ee1c43195644c80d0fd0fbaac8990038710f755913200637416eab226400c6d82dd5644c8010fb03baac8990021f60375591320043f438eab226400e1c431d5644ca5bc58a5ba2c8990c6a7a13735913296726296e6b226400a6e85dc9644ca57d1887b92c8990023ba1f52591321ad3742ea4b22652ae8c43d49644c8010fd0fa8ac89901a1f21f515913294f0e21ea2b226435a6c82d45644c8010fd0fa82c89901a1f21f50591329470e21ea0b226435a6c82d41644c9a92dd0fbaa849949e9ba1b755093269e363b6eaa126526f0c43dd5424ca4b2dd0fb2a849933e9ba1b6550932676363b6caa126524f0c43d95424c801c58cbb228499003531d7735093271dc7426e6a12642e96c85dc5424c85d2d90bb8284990123b60b75d85324dd37416ebb0a6400a7581dd7614c8014eb023aec2990021fe1574d85320343e42ae9b0a6432c6c7550b614c8010ff0ab86c29901a1f21570d85320043f43ea1b0a640087e87d95614c8010fd0e32ac2990123b60b75d81322dd37416ebb026400a7980dd7604c8014f3003aec0990021fe1574d81320343e42ae9b026432c6c7550b604c8010ff0ab8ec09901a1f21571d81320043f43ea3b02640687e86dd5604c99b0f90dbaac09900e5ba0b755813200
  | 15 => 0x4b86caa10ca1f61c60d95420052f418c1b2a8400a5d8318365508014ed02306caa10029d60460d95420063cb80c1b2a84d3a3e84dcf65509a547b09b9ecaa134a9ba0b73d954269d36c16e7b2a8400c6e725cf65509a54dd0439ecaa134e9b60873d954269537416e3b2a84d3a6d82dc765508018dae5b8ecaa10031b5c971d95420043fc02e3b2a84d3a3e841c765509a547b0838ecaa100297a0c71d95420052ec18e3b2a84d2a6e821c765509a74db0438ecaa10029ea0071d95420053cc00e3b2a840087e878c765508010fb0f18ecaa10021fa1c31d95420043ec3863b2a84d3a3e840c7655080147b0818ecaa134a9ba0831d954200536c1063b2a8400a7a800c765508014f30018ecaa134a9ba0b70d954269d36c16e1b2a8400c6d72dc365508018dae4b86caa10021fe0570d954269d1f420e1b2a84d2a3d841c365508014bd06386caa10029760c70d954269537410e1b2a84d3a6d821c365508014ed02386caa10029d60470d95420043f43c61b2a840087d878c365508010fd0e186caa10021f61c30d954269d1f42061b2a8400a3d840c365509a54dd04186caa10029b60830d95420053b40861b2a8400a75810c365508010fd0f886caa10021f61f10d95420063ab8e21b2a840087e8784365508010fb0f086caa10031e5c210d95420043f43821b2a840087d8704365509a747d08086caa10028f61010d95420052f41821b2a8400a5d8304365509a54dd04086caa10029b60810d95426961eba6cbb1a8400e1e43d9763509a987ae832ec6a13531b1c865d8d4201c5ec26ebb1a84058ed82dd763508018d8a5baec6a13269ba1752d8d4201e56ba6a5b1a8530c3d74d4763509934d905a8ec6a14bf0f5d350d8d4264d36416a1b1a840087e87d956350a4dc3887b2ac6a10021fa1c6558d4298f0e218cab1a84058ed82dd7615093f4dd05baec2a10029d60775d85420053ac08ebb0a840087f855cf615080d0f90ab9ec2a10021fe1570d85420343e42ae1b0a840087e87d4361508010fd0fb2ac2a10021fa1c655854202c76c16ebb02845fa6e82dd760508014f301baec0a10029e60075d81420043fc2ae7b02840687c855cf60508010ff0ab8ec0a101a1f21571d81420043f43ea3b02840687e86dd560509a50f90dbaac0a100e5ba0b75581420043f43ecab02840087e871956050993a9ce5a1eca9900e5ba0971d95321743ec38c3b2a6400a3e84187654c80147b0830eca990031d5c461d95320053d400c3b2a6400a7980187654c8072dd04b86ca990ba1f61c60d95320051f420c1b2a6400a3d84183654c8014ed02306ca990029d60460d95320063cb80c1b2a64cea5e83dd3654c99b4bb07ba6ca993369ba0b74d953267536c16e9b2a6400c6e725d3654c80187ae83a6ca993369ba0874d953267536c10e9b2a64cda6
  | 16 => 0x1c00403800801001800400800800c09c01c00000000000800000400400003800000400000800000000403400001000004c0080000280040000a800000807002c00003400805408005c00006000001c0000040000d400000002400c0080600c801000401c17000400800006000c00c00800c0080b400001401806801000801400c0f004001000800c00400800000c00000400007800400000400000000400403402800000402400402403000000007c03000800c05400800805800400000002c02400000403800000000000000000800000400000402401009400000400400c00400003c00000800401409c02c02800001000800c00002802c01800401001800000400c0000000f000803c01400000c08803404804801000803000400402801000001007403800400400400001404400002400004800006802010407003c01001008801807801000806002c02801c00016c00001000400400407400001000002800400401c01c0b800400000400402800c01801c00802c00000801800000400400001006c00002005403400004801808800000801800401000403800006800401004800000c06802c06000006c02000802c03c0180040e000000400802c01c01001c08400000002c00002c01000000405c00400803800800c02400001400800001000003000001000400c03800000000400c00803c00400801805407002c03405c00400000000800401c02801000000400c00002c0c000001c01800400800805c02402801000800000800400000000000400000800000002400001000c0080940ec03802400000802801400800000c02800000403400c02800403801402800001800800000c0a001000402000402006400002800400400000001000000400000000c00400c0640c001c03001000800801c00802c00800003401806804800c00001400001800000000407400400801400801802001c07400000c00c00001000800800400000001c00800002000003000c00403805000001a3886baec4a18021f61e75d89430070e21cebb12860687f875d76250c01c3886baec4a18021fe0575d89430043fc02ebb12860687f87d476250c010fb0fa8ec4a1ccf8710f51d89430343fc3ea1b12860087d87d436250e65c3887a86c4a18034710f755894301c77416ebb0a86008ed82dd76150c010ff0ab96c2a181a1f21572d854301e37390a5b0a8600c6d7214b6150c014eb02296c2a18029e60052d85430053ac0ea1b0a86038ee82dd76050c011db05baec0a18021fe1572d81430343e42ae5b028603c6e7214b6050c018dae4296c0a18029d60452d81430053cc00a5b028600a7980d476050d95a5ce521ecaa100e5ba0971d95421943ec38c3b2a8400a5e8318765508014bb0630ecaa10031d5c461d95420053d400c3b2a8400a798018765508072dd0
  | 17 => 0xe5939035443914500000007470de800087084631480000000004181de8d04000014199000000011b00002b842f0000dfcd6858d1288000000000000207800000037f0f280005bf3031e28b7668c1e814d84b47cc2f2000118e85f3d39318126765000000000021a0000000b0289d0001cf48c200004d80004d87fc1a58000aba65100004f800000000000000006a54651c2000000038f81e4acc31802700010de11f0179c603c253f16e00000003a200012dc4781033170a980a45c72501e6c1fe66146a0cf49988680000000ffe0001ff8d980007b30000e700003890001a540000471fe0920cac8003380ed097c5961d7194c79e258364a2248b284822992045542261509facddc0330001dcc43c000000225059c00004c95d80a012c19b9e4434850b3b68050e944080000260b8600000017d88860001891f080000ca16e8000f1c0002848e751147980000000b4a1793dc971800075734700008fe35a3ac9e080000003fa000000041f0578000fa848d425954c0003150002298f9c02c2089814b7c15717498c80002d43c096d42f40000000000cb60002c784e84662982d51b54cfa21d1c78a3490e27600000000005f70000000a9e58b3918000228000429000119e7c4442000000000000003989220b13d90ef0b922341ac8384a8c0001a30000f566ea398066c0c05b70000000d9e1b2215000000047412e0ac4d724ed06f01b451087d28a229c0002f801c851c00061700003a40000001390000e36000000000082c14e0001c58a4c52400000000000000ed10f8cde53a08a8000ccc0000001da40005e9047800000060c00000000c46ba00006d45760000518fd90ac0000001df000000028a801003803401401802003800800001000001404400401001000401400000004003401c00000c02000805400401c00403400000001800001c0a800000001400401401015000000015400800401c00001401404000004000404400804005c06401000000800002c00002401400c09803400400400400000c00401400005000800800001802800802400801801000800000002c00001800000001000400000000000000000002400401000006402002c01c01c00c0040000680540040c002000800400000003c01400400802800000400400403402800000c00001000c06403003400006c0101c000000003c03800800403800800009c00400c00404807401800000001400c01002001c00402400400002401400000000401c00800400400000001000c0000000080080000241200100000040000d000001400801001800000c02406c00000000000003c00400403803c01801001402800400000c07408001003800001c00000801800402003802000001c00002c00800001802402400c02403c02000000003802c0240b803c00800001c02403c00409c
  | 18 => 0xd0e31c05680003246463f40f08ec264500c867cc3e59f3e980102685780c20cbc112599000095800000000011409d449518789d000045511d80007622d23868d0c3444a207207e86f600031d000075a78d2031f6cb307cd1fd12b8bf23134680a2497a4db0559ad43825a12341d88a382e5160216495400006d0e0c7f07f30dc000054612f43b80000000002208e003420001129f0ce1c2d900003f0fae0aa0019a9c00063f0000150000654283a13482870c0002234664000096800077012038c9a448402410fb000071a56f17307f053c828000000000000035980000000a70fe800000077d3b7800000031a0db9c242c44f73e78000c580002381524992547000176d15e0000b988180007293c00e184540cd40180005ee7d50000590b60000418989400073a410000077400030e19805487dd2190000000713000000000000035100002a241d3809d7c9a67923290fb8f0c32231886e84a052932080000ac5a70001878d7c20b000148c00036c176a06c1b233e25a8a48a3418f01c10c400050e17180000002320000a1484415e39622e07ee0000001a8c0000000a79bb437e5cc373805400033f01e885c00000014592986360000591678000890000188cf4a01f1c98e207185d90000d143502d611c98e03280000000de400016924c95940004d900003484a62441650000000879000000000000000020c80002b20000e0800069623209f8ab8000297000082000000000000005de000120cef00000000c5d13000019c05d02ec105371a1b81380002e4000000014c000008cd1400010e00000d200000404005f6544184194000008311f0ea032242430020e40e851f38581a90ce1420629bac95249c22d8f9000000000000010e800034f000000075835695ad07a63e3210c6450600014d8174b585f30e48014a3200024f0e045968852149030c7a1a60170f209f00431b8160c53279922622d8fd400019b080118200009d971000036b08c220c3980cf0001ca8dbe0b40000ce800050a3f910d4ffc2ac04f150c00061508982083e200039b1f6498a0113cb1060da08130e11c28be040123910d00ee36e13ba2304dc4262be9b2c338266428087cdf46fc0ff109c77204c35314a030e1770989bfc0182d111886941ee0db2f0080cf3429d25d8fbd15680d2b383b46484d40aa20ac45c6262c707649cc000000000000000000000009d600045a01c504a2ba05f9d90f926013ae888c11002a00016e0b380000001a689160000000f5c0006d90e380000001b30001c7466060432780008424d03318068d620bb392029516448e1dd80001f00001b480000f600000000008ec00000005c000037240380001dc3fd06e8bfc07c69402b8de80000003f01e300006c32a820ed12685707a8aa47568713d319386561c40b08db47e62f51f49fec0000003
  | 19 => 0x1d005e047e81609099d4d8a3a110a22183a402434598dd0f84d81ed1a5cfda4882960ef8a4e3353541c0904808d2541d4c74e82f03080000827fd38f0b18b843c60e516742042111f10ae403c73e16119747e24042f780000005203b197a01e646721b9c980002f0276177505289a0580c58cae6f92f5061453e0002fc057c00000000000000005d012d95a40006d700010a11380003879dd89ac2ea4360f98a707bd12102e82dc4e12741128040835347963057a86326b808904e0000bd94c4e843090f71900e7e4f44440f74abc5e53ca16e4d588042dd12e84023c1107a348a7840f2841514bda1392c9851082a1ad32c939408022c2d91954f120ef24d0b3c20839e426164048e85e2f700006920000001fe4e2e03a000000058e2f30000a9c7a206535b9c488d400042a22a86166b20000adccca7ee323881d01669f000000000000000000000000000a480010381450000000000000000000000000009380001f600000001f8d8c6f6354881483600037800000008141ab800059256a23e80000000002a5000000022d00000004c25fd2f18320e4a0c61d80000cc42b03a6a1740000001329378cec7c036980004505860001fc0000000000064d06e00000006003764c408c93bc6b822b39b92fccd05060181c440000002fa00000000003350000c305a211391b853456c41c22488e2775315928c9a2097000000036c19741b1ba09fe2e00001110c2c63c16d97f08761f33e30c44c5e00026e8000d762c51989f780000a11cd819ca260000000b5cc7262800713c83684ac0f505189b414822e859486059a23622381888ba1809e80bce15045f20542602ad27e1fc4e5c4cf18a14c8ebc56344d8bf8ae21f014986286fc20d2029af4d4234436080008f015d00000947461f5051048c00035b20482b04e00000f69120bea32a31398d51a200046282280aa00022700003e40001b093b90a664a1fa0cf00002ee000126c0007b51e9000050400007f127c81c4fa1ea9834e0e8912c419cc9725df0000000c8642c00021380007351f083007d81d8166950462005824e9168fbe636000000078800037c2128b52000355943c2d432e3120000000000000000080035e28094880000000001738a7c0d11820098c26580000084070e13d1481f1513e4b20000000b6c5d50001decea819603d0000cb42603049218eb8000224959065a0000ee1c0c7801cb159969824a8c31b2a0b880e4ce26195ecae86e528b01f416a8221f41ea81e80000c304383a03761d9847908638b33d000000000011b8000de263b09700c825416d0e9827d1460002a680609f600d03613f41824dc0318fece087bf25e0c9d00c46f00008105f41d12e59ddc57e61b23c87e4e62865379000021474e3b91e1d10400031000001b83420001cb499a6f42158ab89626880b38b30
  | 20 => 0x800000000002046f827c0e2a1ad1760000000000d2400008b08840007b81b894600005952d58000fde771147012861801300004401ae4c22331d1883c53341092ac4aa8600891610dc23342eb0000c0e0001e996f087427f08300009306783fd18d064000041f98cc00044245015850543262b1075c06259b00000000003e72399b7887a009000000104680a36698b470a18b000062400080109ba190c968c60391bf4a7a340286899069a6e6035957c7084a40001750f0620c0bf000038043c3a580001528a433ba03ce826af27187bc0000873f38660b4800026580006d405f0000000fee36238d11a4ba200000015c00000001720a700007882ec00001be34c0001d2075e79d00000000006790000858000000000017800027a1a883c0a54000000140cf7666b00011f00002a543f0efc00044f3d68000f425110d608280000a0416000400000000000000004031d9111d1aa0000000000f6e000000000104c86243a800000035d29a02400006e0000000000000000018a8000000000000000060f1369770b5e2961c900000007e240d000000070045c80000000002400af8afc3cc25a0f242b044b45488c0f8e2792bb9680dba7c82d6974c7221e311795003022671ed87e0d9477e1aa0b9ce786300c699f8a4269b1909a90db87e124280000001de00012bc0000eb2fd8fd400080901e1564b04017000108c5183032e90000f580003cb9068b945fe06a1bec3d28812058928f4400000000009ec5cd1510e286ce0f903c18291586110eb1a4d01c6480a0812044483e11006e43a8456048a2c50d476b3991e543b607f1a78f80aea350457031c34064c1cc07b07ac8110c718644e674001399a412a0962d8a06059024635505680e624c3a80a5c5e446b15e19fc88c5790e186a422e47b1ee0798a2049023f090c41c30205e0230ee80f106496500b24fe0df162800081700001d8d9016b1e29c84a9c3c340413e42780ea1090a1c9ea0e027106549a406839114ec6be1243010bb073407c3a216484d224d37aa1d800056000013800007d20ab00000000003ab00000000003fc0c345a03f00002308a5a000278a25400000024996a0dac04b3e81048000300393a0309140002ac131c6c073904582f4da25870000eb117e1fb07e80000007da11d20410da26f3940964a9600000000008ae46005c050068205c0000a180004a73b006ac26416f2e28c7c39a15b29b8b84a903940000bd0c0605a29a97843201ae13880002f88ce3bc8000d9c2df1ef8c746fa1ce1bb9bcc9946220001e3cbcc10800006690f07b10a6955c5b400005b95cc826000000175c0007f6000000087e7af0ce85c4e0a0e205f09d45822941d293008ee6db1318000000000232a2a00200003b7165cd080003408ad8ae45021c7123018484501097fc8c60001341851082356
  | 21 => 0x30ea15496010d00019b114a34a4168e54f6811c39c075412837500000000000003690bc478e25d1e693c0b821010001f6077a364244a1445f200000000000005680ff800048021b25988600000001d5043c0000002a1046cf1640d00007d10cc65809400000000000000000a563d91d30f60db00421b9800016c8610001ee82160641249a7400072000000000006bc088838c7482ef3f4843044873312701444700000000d20bb4107000000000057f196146cd302de3db1f580006bf0bf907000084720c9b001e42080958000000000000000000085c23d1f9855626b336910000000000000005fa7523c28554b7a27d00012585860e54580a006500e7175a25d02400042022dc99084f08d0e406aa0000541c711920003e88360a1806f3a280008a26d40490948a3a55b24906790843e500000000000000000dd008a7e33f21ec000030e34480004d400016994940001b017e199c0e000017b0048f786b60001f0405a01b3fa800000000044f1d98eaa0000ee80008a40002ab19250b00000000000eb439f13c00004be1a31f685f400030a36384d83ee8b346420cc318000000002c00000039a1550f480003221414bf445838800000000001cb1b880000003b500188be7be09a9838c100001828cec09200000011d41a016c1048808e5688b00002150921330530000c4200028f1d9d074000000093c33261a00000011980003d72288adc0000e30790c161883978200be2690199813c63c5ec00000000005cf2128000904000000000039003612599780000001620e6513256d15a0580000000383233481485a0ba81b800079f01a06bc00000007b23009e6143000000000009d0f29bb00008a134e000057000000000010f60003779c54ea2215357054c5b086927480000000441d48000d0a05b21b00006c64542171d311a601d26f99f023a36833708d400083432f8000d1a25e000000072e00044b000000000000000001ac45c00007ad0e00d529780000003de00000003622951f900000004b60000000af87ec40c884cd0623d40e84fc15c4332d98864000844094801c3785c01e5895000040200003300000001e7000018622901d800029400000000fcdb428424a00010f48b5289058ca084ad3ce0a04ce873b20b8de09ce3581f583b0d402570c1223cb225301f182105d054c1839dc00a601c16a9294b464d509c00008bc08e0001544b5c75b28b8000d846120000ed8d8800028011341f479e0741b3002c0cb402a21d1883b543922f00560000000000bd60003a4a07c000680247800006e00000021fc00000004d19c919604d0f00198522168093125c60c5e2000155400042d0001d3d0787142da1f70dee0000000000172000000154894255a014918900476c0001e4039e0863bf80d41a60001a980000000b300022000007433720ff
  | 22 => 0x45e8ce468e6993d1800097000000019c40003b70001e10fca00a0001ea09081663c99a182446103749f2856a76835801d45c43d42bd003c3062af2368a3c2b21e8131042419c3291a919ec3be6b82c480082a464d45685c869c14b1229ea414832313da16c88a3ea023079c5501e21500dbc7f25f232e00000005390d3a1ccb0a4c1000000064a00
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x156192043755091001e0b21c52591424425da0c8314964509100058964452591424400162990149645091000519644529d932440014699014a764c9100041b660521d9324400182d84148764c9100045c66010dd5324400153194043754c9100055464c10dd5324400156192043754c91001c1b24887595324400784c87149634c91098e832105258d324400164591149634c910005926405258d324400161593191655051000589648645954144001a2482191655051002d2525d6350d4144001295932194250510006891488650941440016159418d654c51000591648635953144001a448218d654c5100252525d6450d314400129594219324c51000691148864c93144001531941c375485100055464c70dd5214400707698e1d65485100061921f8259521440078648720965485100058965082595214400164593209654851001e1921e42595214400164593909654851000598642425952144007864878c9654851000589652325952144001661908c9654851003d1925d65d89214400746497595424851001d1925d654c921440016199319165501100058a648645954044001a2882191655011002d2625d6350d40440012999321942501100068a14886509404404f93087595415011013e8c21965505404402fc307659541501106c5c82496550540440011e19221d315011000c6c25d844c540440019908750d315011000c6c25d8448540440032b0966112150110005866506359530440016499218d654c1100069220863595304400949897591434c110004a6650864c93044001a4852219324c110004786488750530440051b0985d1414c1100066421d43505304404f95087595314c11013e94219654c5304402fc5076595314c1106b5d0249654c530440031d097611314c11001474261744c530440031d09760d214c11000cb4259834853044001531941c775481100055464c71dd5204400707a98e1d65481100061a21f8259520440078688720965481100058a65082595204400164993209654811001e1a21e42595204400164993909654811000598646425952044007868878c965481100058a652325952044001661918c9654811001c9c26121595204400787087485654811001e9820921595204400f46897597624811001d1a25d6550920440074689759532481100146c2617450520440054b0965d1414811001474261734c520440054d0965cd314811050e5821f8548520440c396087dd5214811003cd826165485204400f56097595214811013e5821d654852044001a6398595214811001d98261654852044001a6098595214811000718e5d65485204400766297595214811001d9825d654852044001c6097595214811000c7825d8448520440051e0985d1214811000c7825d8348520440051e0985cd2148110
  | 1 => 0xc4d826171485504800184e831c864595100061360c721916544001865811c864595100061a60072191654400182e841c863595100060b6107218d6544001865811c863595100061a6007218d654400136298043725951000558a5c10dc96544001721940437259510005d064c10dc9654400136198040725951000558a5c101c96544001721940407259510005d064c101c9654400782c72a10625951001e0b1c984189654400784c72a0c625951001e131c983189654426d962811cb705951013c5c66371dc1654400706c9261c435951001c1b25e8210d654400106c976084359510006191c98110d654400186872600435951000519a5c81dc96544001a6381e0372595100051aa5c80dc9654400782c72a10725951001e0b1c9841c9654400784c72a0c725951001e131c9831c9654400746491a1c725951001d1a242871c9654400144f935d072595100051324d741c96544001a0d8460c72595100050be51731c9654400142c945cc725951000689611811c96544001a458360472595100068a611801c96544001a4983600725951000698605801c9654400784c72a0e425951001e131c983909654400782c72a12325951001e0b1c9848c965440011729804175d91100054c650105d764440015519304175d911000558648105d7644426b9608204175d911001c1b24987997644400706c9261c52d9110006131cc82595644400144c92597735911000474a6010dcd64440015919404373591100057064810dcd6444001857736045259110006151cd81149644400186772604525911000616dcd8014964440018587360052591100061adc98014964440011729804175d8d100054c650105d763440015519304175d8d1000558648105d7634426b9608204175d8d1001c1b24987997634400706c9261c52d8d100060b1d082595634400142c925977458d100046ca6010dd16344001591930437458d100056864810dd16344001837746045258d100060d1d1811496344001867726045258d100060edd1801496344001838746005258d100061adc980149634400706c926167650d1000525644439d943440014999010e7650d1000427660431d943440014959110c7650d1000526640431d9434400188c436087650d109a6832084359543440016159110d6550d10005866404359543440011729804175d89100054c650105d762440015519304175d891000558648105d7624400184f8314974d891000519644525d362440014699014974d89100060be10525cf62440014659114973d89100051a640525cf62440015319404375589100055464c10dd5624400156192043755891000519644529d942440014699014a76509100041b660521d9424400184d8314876509100045c66010dd542440015319404375509100055464c10dd54244
  | 2 => 0x840156190e0b70545210054965082dc151484015459320b70545210055864082dc151484015459390b70545210054965232dc1514840186476e0970545211461921b725c15148407864861c9705452100549650725c15148401545931c970545210050e642841d94254001469908c876509500070a501201d9425400160d9318964509500058964462591425400145990a0c764c9500051a642421d93254001c4930480764c950005836506258d325400164591189634c9500068550d8110f6154001a194360043d8550006195c9811cb615400784c7260e42d855001e0b1c9848cb615400106c9760a645855001c1be6072991615400106c9760a635855001c1be607298d615400186687887625855001e0b1ca84189615400782c72610625855001e131ca83189615400784c7260c62585500ce4521d43505315400144d9390876485500050b652321d9215400147190a04764855001e19606211d9215400142d9408476485500051364c211d9215400146990084764855001e19607201d9215400787181880764855001e19605201d92154001c612044076485500054664c70dd54250001531911c375509400059164452d8d32500016499014b634c940005896445250b61500016299014942d85400a64921d4254521500016259114b64509300058a64052d91424c001519941c3754c9300055464470dd5324c0016459114932d853000592640524cb614c021944874c9514853065e261db8250d404c00319897611325013000ca6259844c9404c06389876611325013077ec2149844c9404c063c8876509325013014f061d943545404c0016159110f6550d200058664043d9543481d782d84197735092075e1360c65dd13248001c0c43195744c92001c1de61219d9514800144d9390876545200050b652321d9514800786980c84765452001e1c602211d951480078698048476545200051c646801d951480078698088076545200050b650201d9514800144d93080765452000519644201d95148001c612144076545201459825980545214800746a96e1d42541200c4ca261745095048271c28765d142541203070a1db64509504819386876e0d42541200c4ca65383509504800746a96e1d32541206561a1db844c9504803134993e1132541200045a25d844c9504806b868766113254120736c210d844c95048031348985cd32541209bf121d9734c950480b9c4876d8d32541200054a65072dc55048001549931cb71541200055864782dc550480015299420b71541200055264c82dc550480015619120b71541200055264e42dc55048001529948cb71541200061a1db825c5504803186886dc9715412001e1a218725c55048001529941c971541200055264c725c5504800707a96e1d61541201270a1d9425055048041c48764c9315412
  | 3 => 0x1b00408008000680100c0401000000210040400804000080000006c0001c07008090000905001014020000400c0001c0000000000000000000c020140005c020041a074040000405808004280000101400008050080c00c020680002c02030030000000013000010080100c0301409018010081d0080002406000000080105c06008050000200800000030080704c07018000280c00c08018000001f0300500403000000000001c0000c0c0000200408000000280204401014015159110d75d894300546640435d76250c0121d9810e75d894300585644439d76250c016199010e75d894300585644435d76250c016199010d75d89430054564443dd56250c015199010f755894301e199c98114b6150c018657260452d854301e1a9c98014b6150c018697260052d854301e199c98114b6050c018657260452d814301e1a9c98014b6050c018697260052d81430061c5c5801876550801871815c060d95429350765e43d97635080782d8414b75d8d420061c5c580187654c801871815c060d95329250765f43d97644c80784d8314b75d913200507a5c43dd5644c8016159110f75591320058664043dd5644ca69a0c8210c755913200585644431d5644c8016199010c75591320068310e85dc9644c80143591a10765095100519646321d94254401c254148476509510058364c62591425440162990189645095100515646831d9325440146591908764c951007114c5211d9325440160d94189634c951005926406258d3254401a154360443d81510068650d8010f60544018697260072d815101e131c98390b605440782c7261232d81510041b25d82991605440706f981ca64581510041b25d8298d605440706f981ca63581510061aa1e20d89605440782c72a10625815101e0b1c984189605440784c72a0c625815101e131c9831896054401515931c775509410054c64071dd542504016459114b634c9410059264052d8d32504016259114942d81410058a6405250b60504016259114b64509310058a64052d91424c401515941c7754c9310055464071dd5324c59789476e0943505310146525d844c9414c40529496611325053118e251d9844c9414c61fb0452611325053118f211d9424c9414c4016459114932d813100592640524cb604c4016159110f6550d210058664043d95434861782d84197735092185e1360c65dd13248401c0c43195744c92101d19a5b875095148451324985d142545219d7091d9745095148541c2476d91425452164e191db83509514845132594e0d425452101d19a5b874c9514859586476e113254521144d164f844c951484011649761132545211ae191d9844c95148611b04436113254521144d1261734c95148673c44765cd32545214e7111db634c95148401525941cb70545210055164c72dc1514
  | 4 => 0x22e5c31c9980000000df0a270000000005000000000002b0002f2d38002697a0017ec391e92000bb93c00000000000030640000aaa301f09435234c51ba4d11c5a14c7ba44b806acf000000000000000000640000020423aa40218e03000003588a800002700a0006c800000000000000154d79b0c0a4c9d8ac6a176cc25acd2fea71824514aa58ced5a7e000ec1708c0b0fabe1aa9e000de81800000a4800000c6000929f15c7f23c0007600000d492e001048e0005c922ab2de001a43b8d09e800a023214aae8e91a0b8000036000084000d8000007516ec6192b58000006cb88002c898000ba4eb42b214600032001300026ec69c83fae83a1fe001e2af838dc9face240b1b6a001181586644b44299589796491b126b8464e00090ae498860001f61e8aea40f68500000026582942a88a001a06506e000f20000000000000000000029180cb80048284392fc0000000000111d8003326190c2a05a5b048628005080000000001ac0014ea20000000066800d00d682a3e9637667800000005d15610086002e67296adc000cfb246f0000000000354150002fab4a8b50862ce4a35c1a1c23305edbaf0490dab12b28425c7e0884b14800256241da0a80083800da000002d4001dc822cc1300abe9b4000c4b400000200778007c000000800012a0003c3f0007c9ccbd800001a2002989293e819e6a3836b71c6d9ac0001d04caec1d34c598bc673740003a08830440780001c94000a6b1000000790de10b229a8f4348e200000002c2000003c000d20e600264ad8009d0b41c2a089a12db18c71320c58001cb2800000de000000f88a21e003080580000184980ca000000028c9a0640032c8727274804188ea000106e21a0d00e080c26215200000002a8c287e0028a002b800000001ea0000001ad25f22c001e8cd800c11785691628346579e0c7b0c06812b69267d10e95362161988084a05364ca80000224c01500000000000a18001380000144078006fb5a2d8000000000000208c8c9800422ca001960000041a0c002bc8d800000000929e7b0004d8c0baad8000002733a279d60026c38000939b64083ed2a8200000588b069aa6142babd0dc880968890a94a1600002001ce000002e00000c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x640062000076004c00005c46040056102600486c6a00005a4e000e00084a280c66782432687a403c6e3606720000007034027c007400001c007e800038422e0050584420300a52185e60142c2a541612223e003a1a1e2e0008a06100800604280020c00102000200727c812099110c755913293e41104c80863aac89900220da910e85dc9644c801502d088742ee4b226400a8268043a17725913200481b52218caba26490802c05a110c655d13248669a02c888632ae89924200b0268043195744c92101e0490cca0e4b82a29080f0448664c725c15148401206d488632ae89924000b0168443195744c92000581340218caba264904d34099010c655d1324800781443328392e2a824003c12219931c971541209b42c54f4c021b92ca880031228765010dc965440018a143b26086e4b2a2000c482099404175d911000628104c9820baec888002160a8648105d76444001026d48e6412cab222000c482099404175d8d1000628104c9820baec688002160a8648105d76344001016d48e8412cab1a2000a21684436087650d100051134021b043b28688003204826444359543440019044132021acaa1a2000c11e0d9114974d891000609706c80a4ba6c48800302784644525cf6244001815c2320292e7b122000c8120d91149645091000641106c80a4b228488003204846445258d324400190442320292c69922000c8164c82191655051000644320410c8b2a8288002225a9148865094144001902c98a443284a0a2000c816508218d654c51000648320410c6b2a6288002245a9148864c93144001902ca0a44326498a2003c0921d94209654851001e0890ec9904b2a428800f0448764e42595214400781243b29192ca90a2000c8264c82191655011000644322410c8b2a8088002229a9148865094044001904c98a443284a022000c826508218d654c11000648322410c6b2a6088002249a9148864c93044001904ca0a4432649822003c0a21d94209654811001e0910ec9904b2a408800f0488764e42595204400781443b29192ca9022003c18260975952148110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x68000020004405b968443195744c9210064019168043195744c9210064019068443195744c920004409b968043195744c920
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
  | 11 => 0x98e
  | 12 => 0x98a
  | 13 => 0x98c
  | 14 => 0x98d
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0xa0a
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0xa0e
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
  | 55 => 0x98956
  | 56 => 0x9c953
  | 57 => 0x9c956
  | 58 => 0xa0953
  | 59 => 0xa0956
  | 60 => 0xb0956
  | 61 => 0xb4953
  | 62 => 0xb4956
  | 63 => 0xb8953
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
  | 79 => 0xa4992
  | 80 => 0xa4994
  | 81 => 0xa4995
  | 82 => 0xb0996
  | 83 => 0x138b
  | 84 => 0x124b
  | 85 => 0xcc996
  | 86 => 0xcc995
  | 87 => 0xd0996
  | 88 => 0xd0994
  | 89 => 0x1709
  | 90 => 0x15c9
  | 91 => 0x168b
  | 92 => 0x12cb
  | 93 => 0x1889
  | 94 => 0x1609
  | 95 => 0x180b
  | 96 => 0x130b
  | 97 => 0x1649
  | 98 => 0x134b
  | 99 => 0x449
  | 100 => 0xa09d6
  | 101 => 0xa09d3
  | 102 => 0xb49d3
  | 103 => 0x138c
  | 104 => 0x124c
  | 105 => 0xcc9d6
  | 106 => 0x150c
  | 107 => 0x128c
  | 108 => 0xe89d6
  | 109 => 0xe89d3
  | 110 => 0x18c9
  | 111 => 0x1789
  | 112 => 0x180c
  | 113 => 0x130c
  | 114 => 0xb8a13
  | 115 => 0x138d
  | 116 => 0x124d
  | 117 => 0xd0a16
  | 118 => 0x150d
  | 119 => 0x128d
  | 120 => 0xe8a16
  | 121 => 0xe8a13
  | 122 => 0x168d
  | 123 => 0x12cd
  | 124 => 0x138e
  | 125 => 0x14c9
  | 126 => 0x124e
  | 127 => 0x2c9
  | 128 => 0xcca55
  | 129 => 0xd0a54
  | 130 => 0xd49
  | 131 => 0x150e
  | 132 => 0x1a09
  | 133 => 0x128e
  | 134 => 0xec9
  | 135 => 0x168e
  | 136 => 0x1a49
  | 137 => 0x17c9
  | 138 => 0x12ce
  | 139 => 0x5c9
  | 140 => 0x1049
  | 141 => 0x180e
  | 142 => 0x1a89
  | 143 => 0x1949
  | 144 => 0x130e
  | 145 => 0x749
  | 146 => 0xbcb11
  | 147 => 0xbcb14
  | 148 => 0xbcb15
  | 149 => 0xccb16
  | 150 => 0xccb15
  | 151 => 0xd0b16
  | 152 => 0xd0b14
  | 153 => 0x170a
  | 154 => 0x15ca
  | 155 => 0x16cb
  | 156 => 0x144b
  | 157 => 0x188a
  | 158 => 0x160a
  | 159 => 0x184b
  | 160 => 0x148b
  | 161 => 0x164a
  | 162 => 0x14cb
  | 163 => 0x44a
  | 164 => 0xb8b56
  | 165 => 0xb8b53
  | 166 => 0xccb56
  | 167 => 0x154c
  | 168 => 0x140c
  | 169 => 0xe8b56
  | 170 => 0xe8b53
  | 171 => 0x18ca
  | 172 => 0x178a
  | 173 => 0x184c
  | 174 => 0x148c
  | 175 => 0xd0b96
  | 176 => 0x154d
  | 177 => 0x140d
  | 178 => 0xe8b96
  | 179 => 0xe8b93
  | 180 => 0x16cd
  | 181 => 0x144d
  | 182 => 0xccbd5
  | 183 => 0xd0bd4
  | 184 => 0xd4a
  | 185 => 0x154e
  | 186 => 0x1a0a
  | 187 => 0x140e
  | 188 => 0xeca
  | 189 => 0x16ce
  | 190 => 0x1a4a
  | 191 => 0x17ca
  | 192 => 0x144e
  | 193 => 0x5ca
  | 194 => 0x104a
  | 195 => 0x184e
  | 196 => 0x1a8a
  | 197 => 0x194a
  | 198 => 0x148e
  | 199 => 0x74a
  | 200 => 0xd0cd6
  | 201 => 0x18cb
  | 202 => 0x178b
  | 203 => 0x188c
  | 204 => 0x160c
  | 205 => 0x17cb
  | 206 => 0x164c
  | 207 => 0x5cb
  | 208 => 0x170d
  | 209 => 0x15cd
  | 210 => 0x194b
  | 211 => 0x164d
  | 212 => 0x74b
  | 213 => 0xb09895e
  | 214 => 0xb49c95b
  | 215 => 0xb49c95e
  | 216 => 0xb8a095b
  | 217 => 0xb8a095e
  | 218 => 0x98a52
  | 219 => 0xb0bd1
  | 220 => 0x128a52
  | 221 => 0x140bd1
  | 222 => 0xbd411
  | 223 => 0x44d
  | 224 => 0x44c
  | 225 => 0x198a52
  | 226 => 0x19cbd1
  | 227 => 0x58b
  | 228 => 0x4b
  | 229 => 0xcca499d
  | 230 => 0xd0a499c
  | 231 => 0x98a54
  | 232 => 0x98a55
  | 233 => 0x99256
  | 234 => 0x45411
  | 235 => 0x14b
  | 236 => 0xcc451
  | 237 => 0xd0451
  | 238 => 0xe8a09de
  | 239 => 0xe8a09db
  | 240 => 0x1689d3
  | 241 => 0x1789d3
  | 242 => 0x198c
  | 243 => 0x128a54
  | 244 => 0x180a13
  | 245 => 0x18ca13
  | 246 => 0x198d
  | 247 => 0x128a55
  | 248 => 0xb1396
  | 249 => 0x139256
  | 250 => 0x94996
  | 251 => 0x949d6
  | 252 => 0x94a16
  | 253 => 0x124996
  | 254 => 0x1249d6
  | 255 => 0x124a16
  | 256 => 0xcd696
  | 257 => 0xd1816
  | 258 => 0x151296
  | 259 => 0x188a54
  | 260 => 0x1692d6
  | 261 => 0x181316
  | 262 => 0x45292
  | 263 => 0xccbcb1d
  | 264 => 0xd0bcb1c
  | 265 => 0xb0bd4
  | 266 => 0xb0bd5
  | 267 => 0x2cb
  | 268 => 0xcc452
  | 269 => 0xd0452
  | 270 => 0xe8b8b5e
  | 271 => 0xe8b8b5b
  | 272 => 0x16cb53
  | 273 => 0x178b53
  | 274 => 0x19cc
  | 275 => 0x140bd4
  | 276 => 0x184b93
  | 277 => 0x18cb93
  | 278 => 0x19cd
  | 279 => 0x140bd5
  | 280 => 0x94b16
  | 281 => 0x94b56
  | 282 => 0x94b96
  | 283 => 0x138b16
  | 284 => 0x138b56
  | 285 => 0x138b96
  | 286 => 0xcd6d6
  | 287 => 0xd1856
  | 288 => 0x155416
  | 289 => 0x188bd4
  | 290 => 0x16d456
  | 291 => 0x185496
  | 292 => 0x164d14
  | 293 => 0xcc455
  | 294 => 0x164cd5
  | 295 => 0xd0454
  | 296 => 0x198d14
  | 297 => 0x19cd14
  | 298 => 0x1a0d14
  | 299 => 0x188d14
  | 300 => 0x18ce93
  | 301 => 0x178e93
  | 302 => 0x44d14
  | 303 => 0x198b
  | 304 => 0x19cb
  | 305 => 0x44cd5
  | 306 => 0x199894
  | 307 => 0x19d894
  | 308 => 0x58e93
  | 309 => 0x4953
  | 310 => 0x94053
  | 311 => 0x9ccd6
  | 312 => 0xa0d16
  | 313 => 0xb4cd6
  | 314 => 0xb8d16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 1185
  | 6 => 4019
  | 5 => 2262
  | 4 => 447
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
  | 5 => packedAt gbK5 (142506+((h/754+packedAt gbK5 (133458+(h % 754)*12) 12) % 2986)*13) 13
  | 4 => packedAt gbK4 (32780+((h/149+packedAt gbK4 (31290+(h % 149)*10) 10) % 649)*10) 10
  | 3 => packedAt gbK3 (5412+((h/21+packedAt gbK3 (5265+(h % 21)*7) 7) % 86)*8) 8
  | 2 => packedAt gbK2 (372+((h/1+packedAt gbK2 (368+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1c71c7c701cc0e08fc3e3f0fe1fc0c34c134cf
  | 1 => 0xe381f8f801f0700f1fc3c7f0fe1c30c8c2cb33
  | 2 => 0x3fe00fffe3f800fe003f800ffe0c30f330c3c
  | 3 => 0x3ffff00003ffff00003ffff000303f03c0fc0
  | 4 => 0xfc000000003ffffffffc00000003fc003ff000
  | 5 => 0xffffffffffc00000000000000003ffffc00000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4204141104002002410090421080414401045
  | 1 => 0x21008888208010010900424050101048804112
  | 2 => 0x9200120c3c806a408a90228cc04101330c28
  | 3 => 0x2d51200441524a0000324aa044103a0140e80
  | 4 => 0x48000000882a494c92a800000882e8002ba000
  | 5 => 0x9369e4e4f1000180033000cc111bbefec00000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffefef8ffeeeee8fffefef8ffeeeee8fffefef8ffeeeee8fffefef8ffeeeee8fffefef8ffeeeee8fffefef8ffeeeee8fffefef8ffeeeee8fffefef8ffeeeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_30628
namespace PEqualNP.Outside.L_meta_30628
open PEqualNP.Outside.L_meta_30628.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_32 : Interval s2Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_64 : Interval s2Atlas 2 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 66 := (concat bs2_2_0 (concat bs2_2_32 bs2_2_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_96 : Interval s2Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_128 : Interval s2Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_160 : Interval s2Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_192 : Interval s2Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_224 : Interval s2Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_256 : Interval s2Atlas 3 256 23 := block_range (n:=23) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 279 := (concat (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96)) (concat (concat bs2_3_128 bs2_3_160) (concat bs2_3_192 (concat bs2_3_224 bs2_3_256))))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 302 := (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 bs2_4_192) (concat bs2_4_224 (concat bs2_4_256 bs2_4_288))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 24 := bs2_5_0
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
theorem bgb_4_416 : Interval gbAtlas 4 416 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 447 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416))))
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
theorem bgb_5_2240 : Interval gbAtlas 5 2240 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2262 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))))) (concat (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)))) (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 5 zero,inputs.getD 7 zero,inputs.getD 4 zero,inputs.getD 2 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffefefefffefefefffefefaffeeeeeafffefefefffefefefffefef8ffeeeee8fffefefefffefefefffefefaffeeeeeafffefefefffefefefffefef8ffeeeee8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 12 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_30628.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,6]⟩,⟨.and,[8,7]⟩,⟨.or,[0,1]⟩,⟨.or,[10,4]⟩,⟨.or,[11,5]⟩,⟨.or,[6,7]⟩,⟨.and,[12,13]⟩,⟨.or,[1,2]⟩,⟨.and,[15,5]⟩,⟨.and,[0,4]⟩,⟨.or,[9,14]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_30628

open PEqualNP.Outside.L_meta_30628 in
theorem PEqualNP.Outside.L_meta_30628 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 5, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
