import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27995.Model
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


end PEqualNP.Outside.L_meta_27995.Model

namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_27995

namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x430800f631f531bf40bd40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (67+((h/1+packedAt s0K4 (64+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3c38f1f8f3e3fffc631c38fc18e1ffff21c0ff
  | 2 => 0x3fc0fe7ffc038f1f83e03f1fff01c70f467c93
  | 3 => 0xc000ff80fffc0fe3fc003fe01ffe07f0878f1c
  | 4 => 0xffff0000fffff003ffffc0001ffff800f80fe0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x501180111060400220510250020614820c025
  | 2 => 0x8892253020c9122181208908d90c9226421c92
  | 3 => 0x82a441524a412806c4022a424a5404a2870518
  | 4 => 0x10100424808002490948800094891004480ac0
  | 5 => 0x232088400b124c9272933493001020c8b5e000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfffffcf0ffccccc0fffffcf0ffccccc0fffffcf0ffccccc0fffffcf0ffccccc0fffffcf0ffccccc0fffffcf0ffccccc0fffffcf0ffccccc0fffffcf0ffccccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x58a3760984a25c5c59874009202a101ab68015276c40d8514e03801ca46a8000968000e57a5669001f581801c000001d3c449800004000002001a623dd80186508000d5180640458080060c00602004800200d820e60001b7290876d5210eeca221dd54443bd28087795010ef4a1a15e54342bb28c85755190abea6a15714d429f2a0653d540caeca2195d54432bd2806579500cabca620d754c41b7290836d52106f4a020de54041bd286637950cc6dca518db54a319faa2633c544c67ca990cf55321af29c435d53886f6a090de14121b7296816d52d02bca7205754e40bba8a817451502eca3985d547309f2a4613d548c2dea4985b149309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 60
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (731+((h/13+packedAt s1K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s1K4 (1760+((h/20+packedAt s1K4 (1620+(h % 20)*7) 7) % 80)*7) 7
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe3c7f8f1f1fff8e38e0e3f071c1fffe61c27f
  | 2 => 0xf03f8fffe01fe3f03f00fc7ffe01f83e867c73
  | 3 => 0x3ff00fffe3fc7fc000ff807ffe3fc1078f9c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc046421148314006282a409420484b2860c225
  | 2 => 0x24892502064884301104242352149094821c52
  | 3 => 0x29102924920a00d84010a90914a42485070498
  | 4 => 0x440146484400c9229a46000269190118a80b60
  | 5 => 0x882208009893124d2498d24c0020062155e000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaf0ffa0aaa0fffffaf0ffa0aaa0fffffaf0ffa0aaa0fffffaf0ffa0aaa0fffffaf0ffa0aaa0fffffaf0ffa0aaa0fffffaf0ffa0aaa0fffffaf0ffa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1000000799004c027008000052a0d041c04e8d009449106002a6141c000000002300b4d8600b001c20017000000000005ca9e00ad7802458a1842905883e01522180600201000020b02043830e00518ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x4f159ccfa6d08158004d3d1085c00101887a002a920fc641521c0271408087e651c8747c510b1e4de462502c146e0d8005e000006800373901cce002600050001380008000280000312d800d80d0014c6c210c000324e00000007407104462d000a478614000080150007c8a2c001f03c1c2a208880606000ee583c218fe241980cb23408970d4661c000a025001a106132e8ecbe352ba14ea26238c886083d850e0493196844121812cbc000483d08521d1a4c076358002e00020b010000000300001e00040129000c020e0213020a051204000300010811000600020000030026070b0000bd28487795090e7ca721cf54a439ea8c87ba5090f72a121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed944439ea8887b55110e6aa221ee94043dca80873e53d0a7aa3a14f552429e29a85af5250a7ea2a14f950429faa6653c54ccaf4a1995e543329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e540329f29e833d52d067aa920cf14d419fa9283b7515067ca820cfd53319e2a6637a50cc6f2a198cf952319eaa463b5418c67ea898cf15131daa0a633e540c67aa818db94831b6a90637a500c6f2a018cf953219eaa6433e548867aa910cf951219eaa2437b50486f0a090cf950219eaa0435e53086baa610f948421bd280437950086bca7205754e40ce21e613e548c27aa9186e95230dcaa46179538c37487186e10e30dda1461b9428c37683186e506309faa2613c544c33886986ed5130dc2a261db534c3b686986e90d30dc21a61d8434c33086986ed0930dca1261db324c3b264986ed0530dca0a61db314c3b262985e940309f2a6413d54c827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x4a74a34528524c0310e88cb05e00e26007d7162e6d524580c8ab08b431e048119a1e046101c74a05002ca8000490801000c00002010000010063404a50c009ea65825310f255294443c99495110f255254443ca54a5010f315194043ca5495010f3151540438d5845350a3561153328b195424ca2d6214d418b58854cc63465505318718d54486596314121d154d21087612154021a358843cc2956110f30aa588438c2b16110e30a3588434c2956110d30a6993534c23a6590d30a698e434c23a6510d30aa588434c2b16110d30b2588434c2d16110d30a6994434c31a6510d30e2988434c2996210d30e2588434c2896210d30e4984434c2996110d30e4584434c2916110d30a618d424c29864cc930a6191324c389424c930a618d414c29864cc530a6191314c391414c530
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x500c0231c08204a0ba058a6110d30d04c4b08869868162584434c248b88c6a1261245c464cc930910eca1264984897218d414c244b90c998a61241d9414c530
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
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 75)*7) 7
  | 4 => packedAt s2K4 (4032+((h/45+packedAt s2K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s2K3 (1996+((h/16+packedAt s2K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s2K2 (453+((h/3+packedAt s2K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf0e3cffc38e3e3f38e3838fe38e38ff30f90f
  | 1 => 0xff03f1ffc0fffc7c0fc03f1fc0fff0f4331f3
  | 3 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x6160464849144c401860988260a28866305905
  | 1 => 0x82048880902810084084211084051208412052
  | 3 => 0x8910112200a001a100422409402480828228
  | 4 => 0x2420004a080004920a29080032288022140d80
  | 5 => 0xc8cc2290334d3924f4d273c9004106ccebf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffffee88ffccee88ffffee88ffccee88ffffee88ffccee88ffffee88ffccee88ffffee88ffccee88ffffee88ffccee88ffffee88ffccee88ffffee88ffccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x201820df32dd32bf41bd41
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
  | 4 => packedAt s3K4 (68+((h/1+packedAt s3K4 (64+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3c38f1e3f1f8f8fce38e0c70f8fc38ff31370f
  | 1 => 0x3fc0fe03fe7fff1f03f00f80ff1fff0f4239f3
  | 2 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8681184615215100a182a414282488a6311305
  | 1 => 0x82221082840802202110888410a1408422052
  | 2 => 0x1144480401220054400412212412240804c28
  | 4 => 0x919004d28410324968a460021c918262940f80
  | 5 => 0x222089000964c49293498e4c8002048c6bb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xfffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8fffff8f8ecece8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
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
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x447928a0ea0c21064008e1e586802680017342c1064e7c9290010a2a4c00e1500011800a2158022252003674c8c0004000b080007045000040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1f8c170524931e8096110f840819ad96940e94a12aa500002090020012238d98001ba8869c0aa30897818000108100001d04a2800d25802d079caca691801a0e0b090a290f0980002420002603802b001f000ba7aa2822191a92a982aba18c939b189515ac000600001e07271d85830100042c00c08015031208180121c00b08000821000302040c000b7294876d5290edca421db54843bb28887755110ef4a021de54043bd286857950d0abca7215754e429f2a4653d548cb5ca9196b55232b6a9c65cf534cb9e86997310d32b7290655e53106baa620db94841b6a90837a50106f2a020db94b31b6a9663cd32cc67ea898cf15131e6992633e540c67aa818db94831b6a90637a500c6f2a018cf950219eaa0435e53086baa610de94021bca80436e52d02daa5a06b94b40d6a9681ae32d035a65a04f55240d719281ad3250376a0a04f95040b7296616d52cc39a65984f952309eaa461b9408c39a64986e501309f2a0613d540c2dca4185b54830bb2886175510c37281904f952209eaa4413e540827aa8105794c20aea98417651082eaa2106e500209f2a4213d548437281085bd4910b629221b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x701ec001620a80000003001040180d480a70003000208e582548caa96095232a3993534cac56110d32b2580434ca396015131c3151324c64d6394b40a358e52d022d658cb40aa98b50503893250130c654d400833151500209358c52443285250110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100190912e1326a69950970151324c644b9cc5a8281425cc5250110
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
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 30)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3c38f1e3cfc7f1f9c470c7e23f3f1f91c4cf
  | 1 => 0xf03fc0fe7ff1f8fe3e0780f8ffc7c7e1827b33
  | 2 => 0xffc000ff83fe00ffc7f800ff03f807fe638c3c
  | 3 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x185011804450842008414412809210910c045
  | 1 => 0x10080220008001004000800840420200001112
  | 2 => 0x2202b445492892a00f480a92129094d4630c28
  | 3 => 0x44109005120080249251220003249044240e80
  | 4 => 0x88a32088402d24c925a64ce4980020995be000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8ffeceee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12454f12967a3178f428dc2c00d40000001c8012890006c0402b3c2c0283218fb06e21a2e36485334c1c83b06000322a0002d289cbba1ac42803a60e04263889a520698a011830000240cc0006081800c00a00027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4805fe52007f54805fc5201ffd0805fe42007f50805fc42007fcc805fe32007f4c805fc32027fd44017f5100ff94401fd51005f54403fc5101ffd0403fe41007f50403fc41007fcc403fe31007f4c403fc31017fc8403fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40007fcc001fe30007f4c001fc30017fc8001fe20007f48005fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824002ffc8120017f64090017fe204800bf71024005ff0812002fd8409000bf8204801bff8824005ff0412002ffecb08016ff658400bff32c2004bf9961002ffacb08002fd658400bfe32c2005bf1961002ffec908016ff648400bff3242003bf9921002ffac908002fd648400bfe3242005bf19210067fea90802ffe5484001feaa4200bff1521002ffec708016ff638400bff31c2009bf98e1002ffac708002fd638400bfe31c2005bf18e10067fea708003fe5384001fea9c200cff14e1005ffe8708003fe4384001fea1c200bff10e1002ffec508016ff628400bff3142002bf98a1002ffac508002fd628400bfe3142005bf18a10067fea50802bfe5284001fea94200aff14a1005ffe850802bfe4284001fea14200aff10a10007fe650802bfe3284001fe994200aff0ca1000dfac308007ff5184003bfa8c2001ff9461000ffaa3080077d5184003fe28c2001ffd061000ffc8308007fd4184003fe20c2001ffcc61000ffc6308007fd3184003fe18c2001ffc861000ffc4308007fd2184003fe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfd2042005ff50210007f28108017fc408400bff9842005ff8c21002ff46108017fd3084001fc9842005ff0c21002ffe4108017fe208400bfd1042005ff48210007f24108017fc208400bff8842005fdc421000ff62108017fc108400bfc0842000ffd9510005feca88023fe65440097f32a2000ff59510005faca88023fc65440097e32a2000ffd9110005fec88801ffe64440077f3222000ff59110005fac88801ffc64440077e3222008ffd511003ffca888003fd544400ffe2a22000ffd8d10005fec688003fe63440137f31a2000ff58d10005fac688003fc63440137e31a2008ffd4d10007fca688003fd5344011fe29a2007ffd0d10007fc8688003fd434400ffe21a2000ffd8910005fec48801bfe62440057f3122000ff58910005fac48801bfc62440057e3122008ffd4910037fca488003fd524400dfe2922007ffd0910037fc8488003fd424400dfe2122000ffcc910037fc6488003fd324400dfe1922005bfd851000ffea2880077f5144003ff28a2001ff5451000efaa288007fc5144003ffa0a2001ff9051000ffa8288007fc4144003ff98a2001ff8c51000fec6288007fd3144001fa98a2001ff0c51000ffe4288007fe2144003fb10a2001ff48510007ea4288007fc21440037fb022008ffd411002ffca088003fd504400bfe2822007ffd011002ffc8088003fa4044001fea022000fe5011002ff88088003ff304400bff1822000fe8c110007fa6088003f9304400bfe1822006ffc811002ffc4088003fa2044001fe9022000fe4811002ff84088007ff1044003fd8822005ff8411002fec2088017fc104400bfa0822001fe04110
  | 1 => 0xffe410c001fea086013ff1043004ffe6218027fe310c013fe9886009ff0c4300a7fe421804ffe210c001fe9086013ff0843002dfcc018017ff500c00bff2806005ff5403002ff8a018017ff400c00bff2006005ff5003002ff88018017ff300c00bef9806005ff8c03002ff46018017fd300c00bee9806009fe4c03002ffe4018017fc200c00bff8806005ff0403002ffecb10016ff658800bff32c4004bf9962002ffacb10002fd658800bfe32c4005bf1962002ffec910016ff648800bff3244003bf9922002ffac910002fd648800bfe3244005bf19220097fea910047fe5488001feaa44011ff1522002ffec710016ff638800bff31c4009bf98e2002ffac710002fd638800bfe31c4005bf18e20097fea710003fe5388001fea9c4012ff14e2008ffe8710003fe4388001fea1c4011ff10e20015fac51000bff5288005ff2944002ff54a20017f8a51000bff4288005ff2144002fb90a20017fa8510003ed4288005fe2144002ffcca20017fc651000bfd3288005fe1944005ffd862002ffcc310006fe618800bfeb0c4000bf5862002ff8c310016fc6188025ffa8c4000dfd4620087fca310003fd5188001bea8c4010ff1462008ffe8310043fe4188001fea0c4010ff10620007fe6310043fe3188001fe98c4010ff0c620017fe431000bfe2188005fe90c4002ff0862002dfcc110017ff508800bff2844005fe9422002ffaa110003f9508800bfe2844005ffd022002ffc8110017fd408800bfe2044005ffcc22002ffc6110017fd308800bfe1844005ffc822002fde411000bfb208800bfe1044005fe0822002ffe2110017fc1088001ffb2a4000bfd952007ffcca90012fe6548001feb2a4000bf5952007ff8ca90012fc6548001ffb224000bfd9120077fcc89000efe6448001feb224000bf59120077f8c89000efc644801fffaa2400eff95120007faa89003bfc5448001ffb1a4000bfd8d20007fcc690026fe6348001feb1a4000bf58d20007f8c690026fc634801fffa9a4000ff94d20007faa69003ffc534801dffa1a4000ff90d20007fa869003bfc434800b7fb124002ffd4920017fca49000bfd5248005fe2924002ffd0920017fc849000bfd4248005fe2124002ffcc920017fc649000bee3248005fe9924000fb4c920017f86490003ff61480017fb0a400dff9852000dfcc290003fd614801bfe30a4001bf1852007ffea2900037f514801bff28a4000ff54520006faa290037fc514801dffa0a400dff90520007fa8290037fc4148001ff98a400dff8c520007fa6290037fc3148005ff90a4002fbc8520017fc429000bfd2148001f690a4002ff08520015fec09003fff504800bff2824000fe94120007faa090003f9504800bfe282400effd012002ffc8090003fd404800bfe2024000ffcc12002ffc6090003fd304800bfe1
  | 2 => 0x30007fa8518073fc428c013ff994601cff8ca30007fa6518027fc328c00bffb0c6005ff9863000dfcc318017fd618c0017eb0c6005ff1863002df8c31807bff518c001bfa8c601bff94630007faa3180037d518c037fe28c601dffd06300dffc8318003fd418c037fe20c6009ffcc6300dffc6318003fd318c013fe18c601cffc86300dffc4318003fd218c037fe10c6005bf9823002ffea118017fe508c00bfea846005ff1423002ffe8118017fe408c00bfd2046005ff50230007f28118017fc408c00bff9846005f7cc23004ff66118017ff208c00bfe1046005ffc423002ff82118003ff654c0017fb2a601aff99530025fcca98003fd654c0017eb2a601aff19530025f8ca98003ff644c0017fb226019ff9913001dfcc898003fd644c0017eb226019ff1913001df8c89806bff544c033ff2a26000ff551300cff8a89806bff534c013ff29a6000ff54d3004ff8a698067ff434c013ff21a6000ff50d3004ff88698003ff624c0017fb126018ff98930015fcc498003fd624c031fe3126002bf189300d7fea498063fe524c001fea926018ff149300cffe8498063fe424c001fea126018ff1093004ffe6498003df324c031ff1926000ff4c930007ba6498027fc324c001ffb0a6000bfd85300bffcc298006fe614c001feb0a6017ff1853000df8c29806bff514c001bfa8a6017ff94530007faa2980037d514c02ffe28a6019ffd05300bffc8298003fd414c02ffe20a6009ffcc530007be629805ffe314c001fe98a6000f74c53004ff86298063ff214c02fff10a6000ff485300bff8429806bff504c00bff2826000ff5413002ff8a098067ff404c00bff2026000fe90130007fa8098003f9404c00bfe2026009ffcc13004ff66098017fe304c00bef1826018ffc813002ff8409805fff104c00bfe0826005ffd943002dfeca18017fe650c0097f3286005df99430024fcca18017fd650c0017eb286005df59430004faca18017fc650c00b7e3286005ffd903002dfec818017fe640c0077f3206005ef9903001d7cc818017fd640c0017eb206005ef590300057ac818017fc640c00b7e3206016ffd50300affca818003fd540c02bfe2a06009bf98c3004ffea618027fe530c013fea986009ff14c3004ffe8618027fe430c013fea186009ff10c3002ffec418017fe620c0057f3106005fb98830015dcc418017fd620c0017eb106005fb58830005dac418017fc620c00b7e3106016ffd48300a7fca418003fd520c029fe2906015ffd08300a7fc8418003fd420c029fe2106009ffcc83004ffc6418027fd320c013fe1906005ffd843002ffcc218006fe610c00bfb3086001bd9843002ffac218002fd610c00bfab086000bd5843002ff8c218016fc610c02dffa886000dfd443009ffca218003fd510c001bea886013ff144300affe821804
  | 3 => 0xe32a8005bfd914001ffea8a0097bf5450007ff2a28003ff5514001ff8a8a000fbc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8009bf18d4012ffea6a0003fe5350001fea9a8025ff14d4001ffe86a000fbf4350007ff21a8003ff50d400077a86a000ffc4350001ffb128000bfd8940127fcc4a000afe6250001feb128024ff18940015f8c4a0097ff5250049ff2928000ff54940127f8a4a000fff4250007dfa128003ff9094001ffa84a0003bd4250007fe2128000ffcc940127fc64a0003fd3250049fe1928000ffd8540005fec2a008ffe61500037f30a8000ff5854011ff8c2a0006fc615004bffa8a8000dfd454011ffca2a0003fd5150001bea8a8023ff1454001ffe82a000fbf4150007ff20a8003ff505400077a82a000ffc4150001ff98a8023ff8c540007fa62a008ffc3150049ff90a8023ff88540007fa42a008ffc21500077fb028025ffd414002ffca0a0003fa5050001fea828000fe5414002ff8a0a000fff4050007fda028005ff9014002f7c80a0017fc405000bde2028003fe10140127fe40a0093fb205000bfe1028024fe0814011ffe20a0017fc1050013ffb2e6009bfd973004ffccb98012fe65cc013feb2e6000bf5973004ff8cb98026fc65cc013ffb266009bfd933004ffcc99800efe64cc013feb266000bf5933004ff8c998026fc64cc045ffaa66021ff95330007faa998087fc54cc013ffa9e6009ff94f3004ffaa798027fc53cc013ffa1e6009ff90f3004ffa8798027fc43cc013ffb166009ff98b30015fcc598027fd62cc0017eb166009ff18b30015f8c59808bff52cc041ff2966000ff54b30107f8a598087ff42cc041ff2166000ff50b30107f88598027ff32cc013ef9966009ff8cb3004ffa6598003dd32cc013fe1966009ffd873004ffcc398006fe61cc013feb0e6000bf5873004ff8c398006fc61cc045ffa8e6000dfd47300fffca398003fd51cc001bea8e601fff1473010ffe839807ffe41cc001fea0e601fff1073004ffe6398027df31cc013ff18e6009ff4c730007ba6398027fc31cc041ff90e601fff88730007fa439807ffc21cc045ffa866005ff94330007faa198017fc50cc043ffa066005ff90330007fa8198017fc40cc041ff9066005ff083300fffe2198017fc10cc00bffb2c6005bfd963002ffccb18012fe658c00bfeb2c6000bf5963002ff8cb18016fc658c00bffb246005bfd923002ffcc91800efe648c00bfeb246000bf5923002ff8c918016fc648c03dffaa4601dff95230007faa918077fc548c0017eb1c601effd4e3004ffca718003fd538c013fe29c601dffd0e3004ffc8718003fd438c013fe21c6005ffd8a3002ffcc51800afe628c00bfeb146000bf58a3002ff8c518016fc628c03dffa94601cff94a30007faa518073fc528c03bffa14601cff90a
  | 4 => 0x16fc6194009ffa8ca004dfd4650027fca328013fd5194001bea8ca004ff14650177fe83280b3fe4194001fea0ca02cff10650007fe63280b3fe3194001fe98ca02cff0c65016ffe43280b3fe2194001fe90ca02cff0865002dfcc128017ff509400bbfa84a004fed425002ff8a128017f8509400bffa04a005ff1025002ffe4128017fc209400bff884a005ff0425002dfecaa8003ff64540017fb22a02bff9915001dfcc8a8003fd6454057fe322a003bf19150027fea8a8013fe5454057bf2a2a004ff55150027f8a8a80137c5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa009bf18d50027fea6a80137f5354009ff29aa004ff54d50006faa6a8013fc5354057ffa1aa000ff90d50007fa86a80affc4354001ffb12a000bfd8950157fcc4a800afe6254001feb12a02aff18950015f8c4a8013ff5254009bfa92a004ff94950027faa4a80037d5254009fe292a02bffd0950157fc84a8003fd4254055fe212a000ffcc950157fc64a8003fd3254055fe192a000ffd8550005fec2a80a7fe61540037f30aa000ff5855014ff8c2a8006fc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff1455015ffe82a80a7fe4154001fea0aa029ff10550007fe62a80a7fe3154001fe98aa029ff0c550157fe42a80a7fe2154001fe90aa029ff08550025fec0a8013ff5054009fda82a005ff9415002efca0a8017fc505400bbe282a004fe1415015ffe80a8017fc4054055ff902a005ff0815014ffe20a8017fc105400bffb2c8005bfd964002ffccb20012fe659000bbf32c80049f9964002ffacb20002fd659000bbeb2c80009f5964002ff8cb20016fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48005ffd8e4002ffcc720026fe639000bfeb1c8000bf58e4002ff8c7200a3ff5390001ff29c8000ff54e40147f8a72000fff4390007ff21c8003ff50e4001ff88720017ff629000bff3148002bf98a4002ffac520002fd629000bfe3148005bf18a40147fea52009bfe5290001fea948026ff14a4001ffe852000ffe4290007fea148003ff10a40007fe652009bfe3290001fe9948026ff0ca4002ffec320017fe61900037f30c8005ff58640005fac320017fc619000b7e30c8028ffd4640006fea32009ffe5190001fea8c8000df5464013ff8a32000fff4190007ff20c8003ff5064001ff88320003ff319004fff18c8000ff4c64013ff8632009bff219004fff10c8000ff4864013ff84320016fe609000bffa848005ff9424002ff4a120017fd5090001fca848005ff1424002ffe8120017bf4090007fda048005ff1024002ff08120017ff209004dfd9048005ff0824002ff04120017ff109000bfe0848000ffd9540005fecaa0097fe65500097f32a8000ff59540005facaa0097fc65500097
  | 5 => 0x5131007faa8988cbfc544c4037fb1a6233ffd4d3104ffca698803fd534c413fe29a6232ffd0d3104ffc8698803de434c401fea1a6200f750d3104ff88698803ff624c4017fb126231ff98931015fcc498803fd624c463fe3126202bf1893119ffea4988c7fe524c401fea926231ff14931197fe84988c7fe424c401fea126231ff1093104ffe6498803df324c463ff1926200ff4c931007ba6498827fc324c4037fb0a6201ffd453100efea298807fe514c403fea8a6201df5453100ff8a298807ff414c403ff20a6201fd9053100ffa8298803f5414c403fe20a6201ffcc53104fee6298807fe314c403ef18a6201ff0c53100fb86298807f4314c403ff90a6201ff8853100ff84298803ff604c4017fb026200ff98131007fac098803fc604c40b7e3026233ffd413119ff8a0988cbff404c465fe2026231ffc813118ff84098807ff104c403fb8826201ff04131007feca90802ff6548461ff32a4204bf99521007faca90802fd6548461fe32a4204bf19521007fec890802ff644845fff3224203bf99121007fac890802fd644845ffe3224203bf19121187fea8908bffe5448401feaa2422fff15121007fec690802ff6348401ff31a4209bf98d21007fac690802fd6348401fe31a4209bf18d21187fea690803fe5348401fea9a4230ff14d2117ffe8690803fe4348401fea1a422fff10d2100dfec49080bff5248405ff2924202ff54921017f8a49080bff4248405ff2124202fb90921017fa8490803ed4248405fe2124202ffcc921017fc649080bee3248405fe9924200fb4c921017f86490806ff6148403ffa8a4201dfd452100ffca290807f65148403fea8a4201df54521007eaa290803755148403fe28a4201ffd052100ffc8290807fd4148403fe20a4201ffcc52100ffc6290807fd3148403fe18a4201ffc8521017ee4290807fe2148403f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024205bf18121187fea0908c3fc504845fffa02422fff10121017fe409080bef2048405fe1024201ffc412100fee2090807fc10484097eb2ca005ffd925002ffcc92800efe649400bdf324a003af9925002ffac928002fd649400bdeb24a000af5925002ff8c928016fc6494009ffaa4a004ff95250027faa928013fc549400bffb1ca005ff98e5004dfcc728017fd63940017eb1ca005ff18e50027fea728013fe5394009fea9ca004ff14e50177fe8728003fe4394001fea1ca02eff10e5002ffec528017fe62940057f314a005ff58a50005fac528017fc629400b7e314a004ffd4a50027fca528013fd5294009fe294a02effd0a5016ffc8528003fd429405bfe214a000ffcca5016ffc6528003fd329405bfe194a005ffd865002ffcc328006fe619400bfeb0ca000bf5865002ff8c328
  | 6 => 0x5bfa12a239df90951006fa84a88e77c4254401bf992a239df8c951006fa64a88e77c3254403bfb0aa2019fd8551026eec2a88077f4154403bf20aa201dd9055100ef882a88077e3154403be18aa201dfc855100efc42a8807762154403be10aa200dfd8151006fcc0a88037d6054401be302a23adfd01511d6f880a88e77f2054473be102a201dfc415100ef820a8803ff65504017fb2a8238ff99541025fccaa0803fd65504017eb2a8238ff19541025f8caa0806ff6450407ffaa28203ff9514101ffaa8a080ffc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8209bf18d411c7fea6a0803fe5350401fea9a8238ff14d4101ffe86a080fbf4350407ff21a8203ff50d410077a86a080ffc4350401ffb128200bfd89411bffcc4a080afe6250401feb128237ff18941015f8c4a08e3ff525046fff2928200ff549411bff8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe2128200ffcc9411bffc64a0803fd325046ffe1928201bfd854100ffea2a08077f5150403ff28a8201fd9454100ffaa2a08077d5150401faa8a8200dd5454100ff8a2a0807ff4150407fba0a8201ff9054100f7c82a0807fc4150403de20a8201fd1054100ffc62a0807f63150403fe18a8201ffc854100ffc42a0807fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028205bf181411c7fea0a08e3fc5050407ffa028203efd014101ff880a08dfff205046ffe1028201ffc414100ff820a0827ff65cc4137fb2e6209ff99731025fccb98827fd65cc4017eb2e6209ff1973104df8cb98827ff64cc4137fb266209ff9933101dfcc998827fd64cc4017eb266209ff1933104df8c9988dbff54cc46bff2a66200ff553311aff8a998806fe63cc413ffa9e6209ff94f3104ffaa798827fc53cc413ffa1e6209ff90f3104fbc8798827fd43cc401eea1e6209ff10f3104ffec598827fe62cc4057f3166209ff58b31005fac598827fc62cc4057e3166236ffd4b311a7fca598803fd52cc469fe2966235ffd0b311a7fc8598803fd42cc469fe2166209ffccb3104fbe6598827fe32cc413fe9966200f74cb3104ff86598806fd61cc403ffa8e6201dfd473100ffca398807fd51cc403bea8e6201ff1473100ffe8398807fe41cc403fea0e6201ff1073100ffc6398807de31cc403fb18e6201ff0c73100fb86398807ff21cc403ff10e6201ff0873104ffec198827fe60cc40b7f3066209ff58331005fac198827fc60cc46dffa866236ff143311affe81988d7fc40cc469ff9066234ff0833100ffe2198807fc10cc401ffb2a6200bfd953119ffcca98812fe654c401feb2a6200bf5953119ff8ca98812fc654c401ffb226200bfd9131197fcc89880efe644c401feb226200bf59131197f8c89880efc644c467ffaa26232ff9
  | 7 => 0x990ffff544c87dff2a26400ff551321f7f8a89900aff634c87fffa9a6409ff94d32007bca699003fd534c801eea9a6409ff14d321f7fe86990fbdf434c813ff21a6400ff50d3204ff886990fbdc434c8057fb126402ffd49321ffdea49900bfe524c805fea926402ff14932017d8a49900bff424c805ff2126402fb90932017fa8499003ed424c805fe2126402ffcc93204fde649900bfe324c805ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd85321effcc299006fe614c801feb0a643dff1853200df8c2990ffff514c87bff28a643dff145321f7fe82990f7fe414c87bfe20a643dff8c53204ff8629900bff214c805f790a6402ff88532017f84299003ff604c8017fb026400ff98132007fac099003fc604c80b7e302643fffd41321fff8a0990fbff404c87dfe2026402ffc8132017de409900bfc204c87bff882643dff04132026fec9a88137e64d4409beb26a204df19351026fec7a88137e63d4409beb1ea204df18f511e6fe87a88037e43d4401bea1ea23cdf10f51026fec5a88137e62d4409beb16a204df18b511e6fe85a88ef7e42d4401bea16a23bdf10b51006fe65a88ef7e32d4401be996a23bdf0cb5100cfac3a88077f41d4403bf20ea201df1075100efc63a88077c31d4403bf90ea201df8875100ef843a88137f60d4409bf306a204df58351026f8c1a88f37f40d4479be206a23bdfc83511def841a88077f10d4403be086a201bfd9551007fec8a8802ff6454475ff322a203bf99151007fac8a88ebfc64544077e322a204ffd5151026fea8a8813fe5454475bf2a2a204ff55151006faa8a8813fc5454409be2a2a200ffd8d51005fec6a8803fe6354401feb1aa200ff18d5104df8c6a8813ff5354409bfa9aa204ff94d51006fca6a8813fd5354401bea9aa204ff14d51026f8a6a88ebff4354401ff21aa200ff50d511d7f886a8803ff62544017fb12a239ff98951015fcc4a8803fd6254473fe312a202bf18951027fea4a88137f5254409ff292a239df94951027faa4a88037d5254409fe292a204df149511d7fe84a88e7fe4254401fea12a239ff10951007fe64a88e7fe3254401fe992a239ff0c95100dfec2a8807ff5154409fba8aa201ff9455100efca2a8807fc5154403be28aa201fd1455100ffe82a8807fe4154403fb20aa201ff1055100ffc62a8807fc3154403ff90aa201ff8855100fec42a8807fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a205bf18151027fea0a88137f5054409fe282a204df141511d7fe80a88ebfc4054473ff902a239ff0815100ffe20a8807fc1054401bfb22a23adf99151006fac8a88eb7c6454401bfb1aa200df98d51006fac6a88037c6354475bfa1aa200df90d51006fa86a88eb7c4354401bfb12a239df98951006fac4a88e77c625447
  | 8 => 0xf0c952007fec2a9002ff615488bff30aa401bf98552007fac2a9117fc61548037e30aa404ffd4552026fea2a9013fe5154809fe28aa446ffd055222ffc82a9117fc415488bff18aa445ff0c552017fe42a900bfe2154805fe10aa400ffd8152005fec0a9003fe6054801feb02a400ff1815202df8c0a9013ff5054809bfa82a404ff14152237fe80a911bfc4054805ff902a402ff0815222ffe20a9117fc1054801ffb2a8400bfd9542006fecaa10027f6550889ff32a8404bf99542007facaa1002fd6550889fe32a8404bf19542006f8caa10127c65508057fb228403ffd514201ffca8a100fbe5450807feaa28400ef5514201ff8a8a1003ff63508017fb1a8400ff98d42007fac6a1003fc63508137e31a8444ffd4d42007fca6a1003fd5350889fe29a8403ffd0d4201ffc86a1003be4350807fea1a8403ff10d4201f7886a100aff6250805ffa928402ff94942017dca4a100bfd5250801f6a928402ff14942017fe84a100fef4250805ff2128402ef90942017f884a100bbc4250805f62128402ff8c942017dc64a100bfc3250801ffb0a8400bfd854221ffcc2a1006fe6150801feb0a8443ff1854200df8c2a1113ff5150887ff28a8443ff1454201ffe82a100fbf4150807ff20a8403ff1054221ffc62a110ffc3150805ff90a8402fbc8542017fc42a100bfc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028405bf18142227fea0a1113fc5050807ffa028403efd014201ff880a100bff2050805fe1028402fb0814221ffe20a110ffc1050813ffb2e6409bfd973204ffccb99012fe65cc813bf32e64049f9973204ffacb99002fd65cc813beb2e64009f5973204ff8cb99026fc65cc813ffb266409bfd933204ffcc99900efe64cc813feb266400bf5933204ff8c999026fc64cc885ffaa66441ff95332007faa999107fc54cc8057f31e6409ffd4f3204ffca799027de53cc813fea9e6400f754f3204ff8a799027ff43cc883efa1e6409ff90f3204ffa8799027fc43cc813ee21e6402bf58b32017fea59900bfe52cc805fea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b86599027ff61cc813ff30e6401bf9873204ffac399002fd61cc813fe30e6401bf18732217fea399103fe51cc881fe28e6441ffd0732207fc8399103fc41cc813ff18e6409ff0c732017fe439900bfe21cc805fe10e6409ffd833204ffcc199016fe60cc813feb066400bf5833204ff8c19910bff50cc885fe2866441ffd033220ff8819900bff20cc805fe1066440ffc4332207f82199003ff654c8017fb2a643fff99532025fcca99003fd654c8017eb2a643fff19532025f8ca99003ff644c8017fb22643eff9913201dfcc899003fd644c8017eb22643eff1913201df8c8
  | 9 => 0xc017fb0aa64dff9855300dfcc2a9803fd6154c9bfe30aa601bf18553027fea2a98137f5154c09ff28aa604ff1455327ffe82a9937fe4154c9bfe20aa64dff8c55304ff862a993bff2154c9bff10aa64dff08553007fec0a9802ff6054c01ff302a600ff58153007f8c0a9816fc6054c09ffa82a604dfd4153027f8a0a993fff4054c9ffe202a64effc8153277f840a9937ff1054c9bfe082a609ffd964304dfecb21827fe6590c097f32c8609ff59643005facb21827fc6590c137e32c8603bf5924301ffea92180ffe5490c07feaa48603ff1524304dfcc721827ff5390c13ff29c8609f794e4304ffaa721803dd5390c13fe29c8609ffd0e4304f7e872180fdf4390c13fe21c8609f710e4304ffec521827fe6290c057f3148609ff58a43005fac521827fc6290c057e314864cffd4a4325ffca52192ffc5290c07ffa148603efd0a4301ffc852180ffc4290c13ff1948609ff0ca4304ffec321827fe6190c037f30c8609ff58643005fac321827fc6190c037e30c864cffd4643257fca32192bfc5190c07ffa0c8603ff9064301ff88321827fe3190c13fe18c864bffc8643257fc432192bfc2190c13ffb048609ff9824302dfcc121827fd6090c017eb048609ff18243267fea121933fc5090c07ffa048603ff1024325ffe412192ffc2090c95ff884864aff04243007fecaa1802ff6550c93ff32a8604bf99543007facaa1802fd6550c93fe32a8604bf1954304dfec8a180fff5450c07ff2a28603ff5514301ff8a8a180eff6350c93ffa9a8609ff94d43007bca6a1803fd5350c01eea9a8609ff14d4301ffe86a180fdf4350c13ff21a8609ef90d4304ff886a1827bc4350c07ee21a8600ffd8943005fec4a1923fe6250c057f3128600ff58943247f8c4a180afc6250c93ffa928648ff94943247f8a4a180fff4250c07ff2128603ff10943247fc64a1827fc3250c01ffb0a8600bfd854323ffcc2a1806fe6150c01feb0a8647ff1854300df8c2a1927ff5150c8fff28a8647ff1454301ffe82a180fbf4150c07ff20a8603ff1054323ffc62a1827fc3150c91ff90a8647ff8854323ff842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c0b7e3028649ffd414324ff8a0a180fff4050c07dfa028603ff10143247fe40a1923fc2050c8fff8828647ff04143015fecaa9003ff64548017fb22a446ff9915201dfcc8a9003fd645488dfe322a403bf19152027fea8a9013fe5454809feaa2a404ff15152007fec6a9002ff6354801ff31aa400ff58d52007f8c6a9026fc6354809ffa9aa404ff94d52027faa6a9013fc535488dffa1aa400ff90d52007fa86a911bfc43548057fb12a402ffd4952027dea4a900bfe5254805bf292a402ff14952016f8a4a900bec5254805ffa12a402ff90952017dc84a900bfc4254805ff192a402f
  | 10 => 0x800002a01a00c03604202600000000000800200400000001000800601800002600404602a00000600201e00200603a00e00601e00e00600c00600e01801800600a00000600401a01a01400201400800000000200e00a00000e00c02000000a00206004400800a00000200000000001000200400a00000003001e00e00c05e00c00204400a00005a00001a00005003400201004602600801200800201200400000c00200600a00001001e02803a00407200a03bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa026fc6355009ffa9aa804dfd4d54027f8a6aa00fff4355007fe21aa800ffd8954005fec4aa153fe62550057f312a800ff589542a7f8c4aa00afc6255009ffa92a804ff94954027f8a4aa00fff4255007dfa12a803ff9095401ff884aa153fe32550a9fe192a800ffd8554005fec2aa14ffe61550037f30aa800ff5855429ff8c2aa006fc6155009ffa8aa804dfd4554027fca2aa013fc5155007ffa0aa803ff9055401ff882aa14ffe31550a7fe18aa854ffc855429ffc42aa14ffc2155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a805bf18154027fea0aa013fc5055007ffa02a803ff101542a7fe40aa153fc20550a7ff882a853ff04154025facb29827ff6494c13ff324a603bf9925304ffac929802fd6494c13fe324a609bf19253027fea929813fe5494c09feaa4a604ff1525304dfcc729827ff5394c13bfa9ca604f7d4e5304ff8a729827dc5394c13ffa1ca609ff10e5304ffec529827fe6294c057f314a609fb98a53015dcc529827fd6294c017eb14a609fb58a53005dac529827fc6294c057e314a604ffd4a53027fca529813fc5294ca5ffa14a651ff90a5328ff88529827fe3294c13fe194a609ffd865304ffcc329806fe6194c13feb0ca600bf5865304ff8c329806fc6194c09ffa8ca604dfd4653027fca329813fc5194ca5ffa0ca650ff90653287f88329827fe3194c13fe18ca651ffc8653287fc4329943fc2194c13ffb04a609ff9825302dfcc129827fd6094c017eb04a609ff18253027fea129813fc5094ca5ffa04a652ff1025328ffe4129947fc2094ca1ff884a650ff0425304dfecaa9803ff6454c017fb22a64fff9915301dfcc8a9803fd6454c9ffe322a603bf19153027fea8a98137f5454c09ff2a2a604ff55153006faa8a9813fc5454c097fb1aa604ffd4d53027bea6a9827fe5354c13bf29aa609ff14d5304ef8a6a9813dc5354c9fffa1aa609ff10d53007fec4a9802ff6254c9dff312a602bf98953007fac4a993bfc6254c057e312a604ffd4953027fca4a993b7e5254c09fe292a604df1495327ffe84a993bfe4254c9dfe212a64eff8c95304ff864a9803ff6154
  | 11 => 0x154832000600800000601c00a00000002a01200600000400e00600400201200007c00001800000200000400400200000206800800600805800c01200c02600000801000002801600400000400000400000400000601200e0040000140140ea02000600000a00000201800400005e02401000008200601000400c00001601200000e00801c00000600000400a00400000e02800000801402802000800201a00c00000200402401a03a00409000600e01c08e0ac00201800807202800a00000400604601601c00000a01002400802200e00000601200800400400402c00000800002600000200000603001e02407800200201607600000007001602000a00000600000000000400400405c00002400e07a06606c01800000200200200602200002802400000000000a00400804200800400207800c00000c00a00004603600000400000000400603803800200800000803c01c02200a00801602a00003201a00c00c00e00000600801400001201a00414004e00800001600c01407400000407c00002c01e00000a06800001a0aa03e00000203000601600600a00c00003e01e00200800604e00c00401000003004200a0dc00a00601c00002400600600000200e01205e00a02800000000204803600800800000c07c00000001603c0b000800000a00000600200000200002200802c02401401000001200a03401001002200203600201400000400600000401400004e0220b60000000000020020060f000200e01400000005e03201a01400a01c01400a00200000200200000c04a0240040ac00400000e00000407200400c06601a00801000800e00000c05605001200200000e00000000000408e01601602000a00000400a00000400202a00000800801800003c00400e0000020020460040000040220d000800600207400001400001400006801202600000003400001201a00600400003805000001c00a00a05400803e03200600000a01000800401400601c05001a01c00000800400400400600001800607c01600200000200000601200a01001a04000600000e00601200200000407000400e01600601a01600003600602c00201000c01000000c00600c00a02802001c00002600600800202c01802c00000a01c01a01800200005c00801800e00204400c0000000b607400800000000000000202400601c00201204c0aa00002604007205600800200c04600201600400000600005800a01e01402201600000c00001200000001600c01000200802201c00a00605800000001400000800600000801e01200000001a00600401a00e00401000000800000000800200000600a01000e01401200600a00600200c01000205a00209e00800200c00000200200000000601e00602e00202e00800402600200400204800001203000801a01a00200602a0000
  | 12 => 0xd02e26601398e517e70e310245000060e000160400018528d80000000374ad24d80003fb00014fc8e41363968664a7645647116988a829917fa46894646632d8eb80000864139104d2c8aa446823ccba06044424c8ce60000fd2050eb88ae3838e34e7e50b0000e704267251e30b4ca0262836c06d877033f0ee06b470401500000005b68c349a076929e60400017480005b838b800000049700002bc84600000000006e63ea20113e8bf400000020e4e260ed0000ddcf185da0ae000022e73613b17acd027d513f801400081e28c9fc912e31d31d14e91a2489038994494c80920c04b812448c0000930d1a2bd11d0c5c6be32529f11283725dd34205f441e79123c051ca8c88e07c9fad0c83c80be1ae417819d1f58ba925c5413e0a4407262fe46c8b382e08af32f1ed876460c42784fc3aa00036f0174e988f6025197062652e2860e7497e0000fa1a6814800019d08a0eb4000479888059e2820001a144d08c418217c8b0a4b941921b83f684403e9bb8daa3ca4a5958d0229051c5877822c62638318bc05a0002639d4c16656a37d03b09e81a600022a0e7c0000000108dda0a01d500002480003ec15080005b037c8cf07421e72960da4e6829a1f190540005cd2a51c585500000e8800057688300000200002e829100002385483db8d941dc0003739dc84da6be03a00000004572a0115417483411b933c00021b00000002607b23cb892d00c3242a380006c840800f0a58f1a0000ae98fc1ba884024835801c8780002150bfa171000000038a14e00023e800000000000001a61400000000d3a74e00000004a25c23109c5443807a16d191817c000473813cc4e3d006f8010c98000349a020d8a09801012bc3441380541d584c64d7398000121e06d00000007c888100024f123e0003358000ad08820000034d887550000d150441bf0618fb8a4291b2179bfc56a41008f923513682a2e7234846a4643570bf00e46e51de1820aa659c41410f000020e00007c0f9a0002401f1c000000343891c9da1f207c21f42a80111440f048902bf356a3040ac19e06614002bc8bd1ed9e8d0ec4500231ce06a07760000608b744cc31923bc73487e2f60da82ce2b10ba9c706586c6062880c63e06819e800044e3f14671f38e426ce10014544d28ed2da0acc3127b341b24a4c9a3d2380a514d526fb1c800b09ca5ca43019b0d044df28719d8e0046200014c04647f33dc8ed4c267f809b87208125650b5a5011cc57c00b0530dc289409619e8f9e7141188eed1fe28b321198d1704192a892a4d5e0953d29d80a1a5ae05522cc9d01f702a0e3cf4e8be406832c93247a48921a508086a16588506208723f70c28d601200de205428c84919913c927438e00002d49de45126480011d67fb1b823605ec90720292f07740b40fe94e49900820000618b901e9
  | 13 => 0x32599b289347ec13718c50f21fe067a438ee00c21fc9cad0aa0010079db8dcc74610323c4bb048a3e1183525054f018866ceb609c3dd10786e47bf3c58120ed81c742e8284aee2a400012ec84e60312b07bc0000002c58d292045cb38807340be06e16e082c1583300e901700000000000d5c0000000000000a4a79e424000039808400022b400e8d62ad02e40004920000c0c5248470ce0ec05603cd2f380011f60000d58ef86c2000133964c9225fe22f8000000000226a354000437164020c6048b914b80006625060000000000000000000000006220f90c02e44b4454991c00000007d00006500000001c2400000000006a87582e703d80000000001be1ca918c79a209000000000013a00000000003f2046cf807330001778c7a6dc4001fe4eda383000046834627300000000000001a10960eca00049f00004520e308212e0b6c5c40c8827c93a0002cf9558d765f043e0de4a1e5af27b948c00002e2cd209400014d01287408880000ab0000000000000000000000026c925889c35a0001e5800080145219fc90c1ca2148c8cb7825031994982d0851036118c0820001278b74a5671910a823800089d02712880008fd0000000c904d345a9c0c02e47b1cf013525400014a9acc5e28c700023346a48dd166965524000044380000001b53828000c3245b38d2080c227dd1e620e858a00000005647de6152d483640cc13b0001828db60211f096dcae00000c700007bc38000018b0cb479c30f80000000c73ae89f861a00037b1d5000038500021dcb927b418b14f4dc83d5387a12896a32b46fa1b4bc609d324927917677d045a46485410f2b003ec0006f507505b46243341da05ccb542d612295608ca6a238c03700008cf33e873884476b0c906c880287538200d09e614440b131860e2d214702c82145bf1ae1414bb825e20316882566b20bd98ec5ea21a3c089e06ec4a047009ec7b42de42c08f929425a11502300a41e62e624fcadc66832b00ecb1229310617dd04202f00e2270f5400c0000f88d185e81cd9e486366ec32224ec62a1b33379a450ae3df19c11b435e2342190600ec80f202281541b453c1538ff43186790ca96b4dd682b2b08e9c58280317613407ae00000009f0be23c023ba2f0b062a0216a49423c0fc3f3019c2266ba26e939cc3600027e93800003bf1119f2090e1421db887c0002c7000112d11877e1a99e3c9b400024a849c0001c30000658cfc4003388000bcc00042800000006b13d3000000015f000000116e00b0000090dae363000000000013d11580008082420859eb0c560e80181f8d2908f52ea0000fe263c0518d3469000025f062c07e0530000000000727000000000078e44989500007ab3b50becf261d42710000ce00000001e180000e249781680003202200fb40005b20000bb447246c3a69a3
  | 14 => 0xbca3a3874a383c42680000c197cc68256b4130088a920e633100005686bd00000d800000000000000000000001514d4c0001569d2d14609b33c16848a627112684ccfae711000034929a3e840e1ba80000000238af80007c4025a14c00000017e85b916841d00010592b600010f24f4e5e664000041886a00017900010203e93a1a4d4892731464808cb5666d43d99dd29c3463a907c4efe7bc30e141c75614f159181906a950000161d28c83e042861cef23c53ab9d20c168ee1ea055d2ae4aa34c209105e80a0a28610d060a72af1550bde8f828e18911d04c245307fc2464610d602f51b43672b99ebcbd219829501852068b20881dcca529111ca139079e2cc06215bcd286222c207605aa48436012c11c646f1d48f64b300993a012949306800dc0244aaa7d64761d284ea3fe11817d09bc86b3da8000f4291c00006288ba6bf0b49af0fd01c03b10694fc06e22d20d44acc35914e80f0da023f3b889b00ea2573ee0804e0416f33711a8c8a3fc052a1c43f85c7300130050228f09d1900ca058f4290da112a0e91b599d4c3c3913c0081d22c28930483d09569584168b647486fe2c61b805863f206505252721d600001ace446a719aa2447ac90b10c91d90e69172a59e546e85d7081a460b829532ca23a86446250601be01763bd1db0520e844b1484a43106e09a4749c7512c00029a935053691e0001dd00002223081bdcede2e6000113c0364580329a24c462f328b0e483da02828400009e00001c480000000001d313b03820f706a80000000000000dc4e8a47d0d0a284ace91d45b0c682c65df1a490800fe57118090e80000a92069e7c53c0001779c3000034f21b00002d800005fa0a40000003dd8ab912428a19b80000002a22bd17ec5f000000008340d40001050000c6a0003fa08982226ac0000910c860000b28000b72726070000000c8cc15b0c9c0569380001e64a683af02c00012143e708c9b441a0485303956c3be73726585549f825d19302dcd5071b42f814419a6542f29f0c5227d3217043506268b3ef1028e7a4cd30a166515625912014250241eb4219d1cb2c71f075835cf3651a00000f400026f405800000083f4079e1442000025200007ca0001b105a8a5e44c2fe04a881c0002e99fc11b62df009000049c4ba2b200006189272f50c24000204156000000023c02600010fe6a30001444af09003fb954069876721300e510015209a9adce883f84a18fc03ea1c93fb00005707fe0001600dac64116211c522647044c1764af68ac483256415663034f8e310360de491845472a8560bd1608fc279d04821348e836d21f23500120fd0fc01f8a044902d28c503c21a71998a00458659205a218dd06c734413a4f405b321e86dcfde1530a51cf02cc0c913284a50c60d82890a306fc69e2c51d78fa88d026b1e107305a
  | 15 => 0x340c690844c89421c51068000181000000023a53625b8a1c13c8b012d8000ef08fc2e18cb909688f3078d78a487282618ecc74643b14e1740eea0ad0ad15d8a3e21236e8000f7a1cf187201c00056d1c0a2786cc5bd15790e473e0142f2000113230b39198a87b05171888b5c9168331241ad865e1971cb8200eb22c00968948fd254e16301c0e9e35d31c18d852805000015f50761a80000001098672259000000059717115a4786000394800000000018e000074a0000001a800de37b3eda280bea00000000012587da0000ec40000002cf000000000009916389041213ff8ba4f968230000c200000003be117074419a1381cc81ea70d00013f8f2859d329000000000023f0bc01c264e000101cf5a00024d80000004e60001370f1010540f87087ea3e600020b11842c22229d4113e4c505897580000001ee8f24de8000000000092877712300008283a000008cc0003214228b2919633911200003ca22f0940000000211369000108c8e537980a40001222af825000000034912a020e00016484380006fc0099f18b800003c123f8bfe00006a17b800067c31480000001bb2c3072c7a22e5430a3c00002a636d00000000000001eb895c4671358954b105443699b8c0e62090c816805dc2622999784f9814b0729108fa240f1f604f869c05b11b0a1007464a11e85d8a064ea22d1f7ce481f946f00d526686c3b48fd8d707a948210cc8188c043385801c84c4058193c11200300f9270a5a8054911cb80f21db1e100010d057424400090e80000f211b88501d9000213842e00034305608f20003cc1c803401b039d93d800063428c040416c2bc000132928260500c8228cd2751221800119400020180003d44520000858b4e0ae16a006000037527f8f4cb227ed35284305f42792942554b7c2a50d881e0ab810849805d00007b849580000000000001640a280693e911fc0000000000ca40000003ac015c02001d2e8840800037832580008d60002ea8aacd1c83d432800090627a000219800007c00003ccecc0f02a615fcf2035611da2e87085a80f98e580706d43f295f91120002688000f925753309c48fea0000b08690a3c00018f06200002d0175a3143c64e14481ce863273915d0cd83ba6df43114c868030f1d4104c3d88700001da000066a1d698f89b68e40220000b580002538000d9a0000498884caa30000015348c00002850000dfa82e3c1a5589ea4174a60f2d14e667498a54404c749150892837478a40c8b450bc6950000190ae442400003bcd865c64920d500008853c48b8c2120003f500000005311a39a2800000013018740000002758df4d846c1000138d07008117b85dc50600000006507e6468445846122a8f900011a43880000001858000388000163499c74134c91182fe88a40208e103a25c42d800043a55d23a8d
  | 16 => 0x67c55221296d4dd20002770d5450a20200008145200000002030d9060224706a43d02e0073a5485b00000000dfcebe0000e31b3c4106cb06700012b89442bc9a6c00085c1308000f9487a1550000d2000039a9a9100400008a20f00005f833a1f40c3080e00009c91445bb1a584bc8225e21951e1ca700000001aac0000883fe036c5e86a11e224042f25043ec88600000002899de86884810001aa800076100003f89e20b83f103d885849f0000d608e643f00019607ee2434842108c2401a27d8000bf200040c000000089a00000012a8000116997cde415b42090ac97a32d0000b850340401cc90c414483014f84942240001f01c781a28d747a15b060c2251720f70c6e000469924cdb2096256021c546000000173c3c000000000c800002a409923c0ee6f1437817896c0001ffa4b40000000d71c282001d336606f4ccc7a23d88adcbb60000b1063c33e00046e13609f0000000106cbda7be0bc194c530241490995c68613109324dc8b237a2b10540de062e33d9cb050c62d3fe83fc6c08c800000f84ee4383f38f1c88e305377955cc2e7c53bd94400140430b209a8e166b50bf148011a53719d9284b243ce260a3846dc36c0c997142a235b45281d83ec7a803197d924c5b11dca2c44a69490a08e18a4e4d2330243400022e17c825c36813947b84f0d383fa1fa12b400061a42ca1684926c90530c60c0203302c91f000000027c9d8c00025f34b80009aa0c10001ec03c41ee0001c20a861be2ac9e90ff45e00eb8ae483845e000199428600000023c851a27d35a166c18c4
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb7450110007bb645011001efa645011001ef8645011003fb864501102b7bb545011003fb85450110005fb7350110006fb6350110006f9635011003fbb4350110007b94350110005fb7250110126fa6250110126f8625011003fbb4250110007b94250110007f3715011000dfa715011000df8715011011ff0715011000df0715011002efb615011002ff3615011011f7b515011011f79515011011fbb415011011fb9415011011ff23150110007f1315011011ff22150110007f1215011000cfe76cc11000cfc76cc110006df63cc11004edc63cc11000df671cc110005f571cc110007d531cc11009dfa768c11002efa768c11002dfb748c110005f9748c110006fb648c110006f9648c1100bdf9738c11004efa638c11004ef8638c110005f9728c11002ff3718c11000dfa718c11002df8718c11002ff0718c11002efb618c11002ff3618c1100df7b518c1100df79518c1100dff2318c110007f1318c1100dff2218c110007f1218c11004cff764c11000cfe764c1100bcfd764c11000cfc764c110006df634c11004edc634c110005f7714c11000df4714c110007d5314c11002fd8304c11002ff0104c11000df8764c11004ef8764c11000cf8764c110005fb744c110005f9744c110006fb644c110006f9644c11002dfb734c11002fdb734c110007db634c11004efa634c11004ef8634c110007d8634c110005fb724c110007db324c110007d9324c110007f3714c11000dfa714c11000df8714c1100bff0714c11002efb614c11002ff3614c1100bf7b514c1100bf79514c1100bfdb314c1100bff2314c1100bfd9314c110007f1314c110007d1314c1100bff2214c110007f1214c1102adfa768811002efa7688110006fb6588110006f9658811002dfb7488110005f9748811002dfb7388110005f9738811006df97288110016fa6288110016f86288110037ea4288110007e9428811002ff3718811000dfa718811002df8718811002ff0718811002efb618811002ff361881100877b5188110087795188110087f23188110007f13188110087f22188110037f12188110014ff764811000cfe764811006cfd764811000cfc7648110006ef6248110016ec6248110005f7714811000df47148110007e5214811002fe8204811002ff0104811000df87648110016f8764811000cf87648110006fb6548110006f96548110005fb7448110005f97448110005fb7348110005f9734811002dfb724811002feb7248110007eb6248110016fa6248110016f86248110037e86248110037ea3248110007e93248110007f3714811000dfa714811000df8714811006ff0714811002efb614811002ff3614811006f7b514811006f79514811006ff23148110007f1314811006feb214811006ff2214811006fe92148110037f12148110007e12148110
  | 1 => 0x8910004fd74d891001cfc74d891004cfe73d8910004fd73d8910006ef52d8910036ec52d8910036ee42d891002cff71d891000cfe71d891002cfd71d891000cfc71d89100867f51d89100867d51d8910086ef21d8910086ed21d891002cfe70d891000cfd70d891002cfc70d8910036ef20d8910036ec62589102c5fb7058910004ff7558910024fe7558910024fc7558910004ff745891001cfe745891001cfc7458910004ff735891004cfc7358910084ff7258910006ef7258910036ee325891006cff7158910006f7715891006e7f515891006e7d51589102c4ff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100457c755091001ebe6450910006bd6450910006ef6250910016ec625091004cff76cc910004fe76cc910004fd76cc91004cfc76cc9100457e75cc9100057d75cc91004ede63cc910006dd63cc91000df671cc910005f571cc91002dfa70cc910005f970cc910004ff764c910004fe764c910004fd764c910004fc764c91004ede634c910006dd634c910016ee624c910006ed624c91000df6714c91002df4764c51004ef4764c51002cf4764c510006f7644c510006f5644c51000df7734c51000fd7734c510007d7634c51004ef6634c51004ef4634c510007d4634c510007d6434c510007d5434c510005f7724c510007d7324c510007d5324c510007f3704c51002df6704c51002df4704c510007f0704c51000ef7604c51000ff3604c51002df47648510016f4764851002cf47648510006f76548510006f56548510005f77348510005f5734851000df7724851000fe77248510007e76248510016f66248510016f46248510037e46248510037e64248510007e54248510037e63248510007e53248510007f3704851002df6704851002df47048510007f0704851000ef7604851000ff36048510037e72048510024ff765411000cfe765411014cfd765411000cfc76541100067f65541100267c6554110005f7715411000df4715411002ff010541102bdfa769011002efa769011002f7a759011002f797590110006fb6590110006f9659011011df9749011001efa649011001ef86490110005f97390110006fb6390110006f96390110005f97290110136fa6290110136f8629011000dfa719011002df8719011002efb619011002ff3619011013f7b519011013f79519011013ff23190110007f1319011013ff22190110007f1219011001cff765011000cfe765011011cfd765011000cfc7650110006bf645011001ebc6450110005f7715011000df4715011002fb8405011000df8765011001ef8765011000cf87650110006fb6550110006f9655011002dfb745011002fb
  | 2 => 0x467c5459510004ff735951004cfc73595100467f5359510004ff7259510006ef7259510004ef7259510014fe7259510014fc7259510006ec7259510014ec72595100467f525951014cff7159510006f7715951014e7f515951014e7d515951014ef621595102dcff7059510006fb70595102d67e50595102d67c505951001cfe76d91100457e75d91100057d75d911003ebe64d9110024fe75d91100067e75d91100247e75d9110004fd75d91100067d75d91100047d75d9110024fc75d911004cfe73d9110004fd73d9110014fe72d9110004fd72d9110014fc72d911002cff71d911000cfe71d911002cfd71d911000cfc71d911013e7f51d911013e7d51d911013ebf41d911013ebd41d911013ef631d911002cfe70d911000cfd70d911002cfc70d911003ebf40d911003ebc6459110005df7359110005dc73591102cdfb7059110004ff7559110024fe7559110024fc755911013cff7459110006bf7459110004ff7359110006df7359110004df735911004cfc7359110006dc735911004cdc735911003ebf4359110004ff7259110014fe7259110014fc725911003ebf425911011cff7159110006f7715911011e7f515911011e7d515911011ef631591102ccff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc765511004cfe76d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df43d8d10006dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d1002cff71d8d1000cfe71d8d1002cfd71d8d1000cfc71d8d100de7f51d8d100de7d51d8d100dedf31d8d100dedd31d8d1002cfe70d8d1002cfc70d8d10006df6398d100bdf97098d100fdfb7058d10004ff7558d10024fe7558d10024fc7558d10004ff7458d1001cfe7458d1001cfc7458d10006df7358d10004ff7258d10014fe7258d10014fc7258d100bcff7158d10006f77158d100be7f5158d100be7d5158d100fcff7058d10006fb7058d100dcfe7618d100457e7518d100057d7518d1003dbe7418d10005bd7418d1004ede6318d10006dd6318d10035ee7218d10005ed7218d1004cff7694d10004fe7694d10004fd7694d1004cfc7694d10006df6394d1004edc6394d10035ee7294d10005ed7294d1000df67194d10005f57194d1002dfa7094d10005f97094d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100267e6554d100067d6554d10006df6354d1004edc6354d1004cff7690d10004fe7690d10004fd7690d1004cfc7690d1000df67190d10005f57190d1002dfa7090d10005f97090d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1001ebe6450d10006bd6450d10014fe76d8910036ee62d8910024fe75d8910004fd75d8910024fc75d891001cfe74d
  | 3 => 0xf7690e1002cfe7690e10004fd7690e1002cfc7690e1002dfa7090e10005f97090e10004ff7650e1002cfe7650e10004fd7650e1002cfc7650e1001ebe6450e10006bd6450e1002dfa7050e10004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a1004cfc7358a1002eef7258a10056ee3258a1006e7f5158a1006e7d5158a1006eef2158a1006eed2158a1002cff7058a1002cfe7058a1002cfd7058a1002cfc7058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a100267e6554a100067d6554a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a100057f7550a100657c7550a1001ebe6450a10006bd6450a102feef6250a10016ec6250a1002dfa7050a102ffea2050a1004cff76cca1002cfe76cca10004fd76cca1002cfc76cca100657e75cca100057d75cca1004ede63cca10006dd63cca1002dfa70cca10005f970cca10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca1004ede634ca10006dd634ca10016ee624ca10006ed624ca1002dfa704ca1002dfb76502102f6fb765021002efb6550210006f9655021002fbb745021002fbb645021001efa645021002ef8645021002fb864502102efbb545021005fb85450210005fb735021002efb6350210006f9635021005fbb4350210007b94350210005fb7250210126fa625021002ef8625021005fbb4250210007b9425021000dfa715021000df8715021011f7b515021011f79515021011fbb415021011fb9415021002dfb764c210006fb764c210005fb744c210005f9744c21002efb644c210006f9644c21002fdb734c21002fdb634c21004efa634c21002ef8634c21002fd8634c210005fb724c210007db324c210007d9324c21000dfa714c21000df8714c2100bf7b514c2100bf79514c2100bfdb314c2100bfd9314c21002dfb76482102e6fb764821002efb6548210006f96548210005fb7448210005f97448210005fb7348210005f9734821002feb724821002feb6248210016fa624821002ef8624821002fe86248210057ea3248210007e9324821000dfa714821000df8714821006f7b514821006f79514821006feb214821006fe92148210024fe76d95100467e65d951001cfe74d9510004fd74d951001cfc74d951004cfe73d9510004fd73d9510014fe72d9510004fd72d9510014fc72d951002cff71d951000cfe71d951002cfd71d951000cfc71d95101667f51d95101667d51d9510166f621d951002cfe70d951000cfd70d951002cfc70d95100467f50d95100467c6559510005ef7259510035ec72595102ddfb7059510164ff75595100067f7559510004ff745951001cfe745951001cfc74595100067e5459510
  | 4 => 0x4120026fa6594120026f8659412002fba749412002fb97494120006fb6494120006f96494120015fa729412002df8729412002efb629412002feb629412016fea3294120007e93294120005f9719412007f7b519412000779519412016feb2194120007e92194120024ff7654120014fe7654120154fd7654120014fc76541200067f65541200267c6554120005ef7254120015ec725412002f785054120015f87654120026f87654120014f8765412002dfb755412002f7b75541200077b6554120026fa6554120026f8655412007f786554120006fb6454120006f964541203077a545412007f78545412007f7b5354120007795354120007eb7254120015fa7254120015f87254120157e8725412002efb625412002feb62541201577b5254120157795254120157ea3254120007e93254120005fb715412007f7b5154120007795154120157eb2154120007e9215412001cff7650120014fe7650120124fd7650120014fc7650120006bf645012001ebc6450120005ef7250120015ec7250120126fb605012002fe82050120014fe76cc120014fc76cc120006df63cc12004edc63cc120015ee72cc120005ed72cc120007cd32cc12004cff764c120014fe764c1200c4fd764c120014fc764c120006df634c12004edc634c120005ef724c120015ec724c120007cd324c12002e7f7559610004ff745961001cfe745961001cfc74596100067e54596100667c5459610004ff735961004cfc73596100667f5359610004ff7259610014fe7259610014fc72596100667f525961014e7f515961014e7d515961002cff705961002cfe705961002cfd705961002cfc705961002e7e505961002e7c505961002efa405961002efa2059610004ff7559210024fe7559210024fc755921002ebf7459210006bf545921005ebc5459210004ff735921004cfc735921005ebf4359210004ff7259210014fe7259210014fc725921005ebf425921011e7f515921011e7d515921011ebf415921011ebd415921002cff705921002cfe705921002cfd705921002cfc705921002ebe405921002ebc405921002efa3059210004ff765521002cfe7655210004fd765521002cfc7655210004ff7558e10024fe7558e10024fc7558e10004ff7458e1001cfe7458e1001cfc7458e1002edf7358e10004ff7258e10014fe7258e10014fc7258e100be7f5158e100be7d5158e100bedf3158e100bedd3158e1002cff7058e1002cfe7058e1002cfd7058e1002cfc7058e1002efa4058e1002ede3058e1002edc3058e1002ef71058e1002ef51058e1004cff7694e1002cfe7694e10004fd7694e1002cfc7694e10055ee7294e10005ed7294e1002dfa7094e10005f97094e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e100267e6554e100067d6554e1004cf
  | 5 => 0x4fe7690d20004fd7690d2004cfc7690d20015ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2002dec764c92004eec764c92002cec764c9201feee654c9201feec654c920006ef644c920006ed644c920015ef734c920017cf734c920007cf634c92004eee634c92004eec634c920007cc634c920007ce534c920007cd534c920337cf434c920337cc434c920005ef714c920007eb704c92002dee704c92002dec704c920007e8704c920016ef604c920017eb604c92000cfe76d852006ef661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d852004cfe73d8520004fd73d852002cfd72d852000cfc72d8520056ee32d8520006ed32d852006ef621d8520056f521d852002cfe70d8520014fd70d852002cfc70d852006ef710d852006ef4615852032dfb70585200267f76d452007e7e76d452007e7d76d45200267c76d45200067f64d45201e67e64d45200067d64d45201e67c64d45200067f63d45203267e63d45200067d63d45203267c63d452031e7f62d45201df6e32d45200076d32d452006d7d71d452006e7f61d452000e7e61d452000e7c61d452006f6f21d452007f7a70d452007f7970d45202c67f60d45201df7b20d452031f6e20d452031f6c20d45201df7820d4520004ff7654520004fe7654520004fc76545200067f65545200267e65545200067d65545200267c65545200067f76545200067e76545200067d76545200067c76545200067f64545201d67e64545200067d64545201d67c64545200067f63545203167e63545200067d63545203167c63545202d67f62545201cf6e32545200076d325452006d7f715452007f77715452006e7f615452000e7e615452000e7c615452006f76415452006f6f215452006f7621545201cf7521545200077a70545200077970545202c67f60545201cf7b20545202d76e20545202d76c20545201cf782054520004ff7650520004fe7650520004fc765052001ebe6450520006bd6450520007755150520004fe76cc520004fd76cc52004cfc76cc52004ede63cc520006dd63cc520015ee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c52004ede634c520006dd634c520015ee724c520007cd324c52002dec764852000eec764852002cec7648520006ef6448520006ed6448520005ef7348520005ed7348520006ef6348520006ed6348520015ef7148520017e77148520007e7614852000eee614852000eec614852006fe4614852006f6f514852006fe6514852006f6d5148520007e55148520007655148520007eb704852002dee704852002dec7048520007e87048520016ef6048520017eb604852006fe7104852030dfa769412002efa7694120155f9759
  | 6 => 0xb765422035efb765422002f7b755422002f7b6554220026fa655422002ef8655422002f78655422002efb6454220006f964542203577a54542200977854542200977b5354220007795354220015fa7254220015f872542201577b5254220157795254220157ea4254220007e94254220005fb71542200977b5154220007795154220024fe76d952007e7e65d952001cfe74d9520004fd74d952001cfc74d95200067e54d952007e7c54d952004cfe73d9520004fd73d952007e7f53d952002cff72d9520014fe72d952002cfd72d9520014fc72d952016e7f52d952016e7d52d952000cfe71d9520004fd71d952000cfc71d952007e7f51d9520014fd70d952007e7f50d952007e7c655952034dfb705952016cff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff735952004cfc7359520154ff7259520006ef7259520004ff715952000cfe715952000cfc715952007e7f515952034cff7059520006fb705952001cfe76d9120076be64d9120024fe75d9120004fd75d9120024fc75d912004cfe73d9120004fd73d912002cff72d9120014fe72d912002cfd72d9120014fc72d9120136bf42d9120136bd42d9120136ee32d912000cfe71d9120004fd71d912000cfc71d9120136ef21d9120014fd70d9120076bf40d9120136fb20d9120346ee20d9120346ec20d9120136f820d91200057f755912007d7c7559120076bc645912033dfb7059120004ff75591200067f75591200047f7559120024fe7559120024fc75591200067c75591200247c7559120134ff7459120006bf7459120004ff735912004cfc7359120124ff7259120006ef7259120126ee3259120004ff715912000cfe715912000cfc7159120076bf4159120126ef215912033cff7059120006fb7059120126fb20591202feee20591202feec2059120126f82059120004ff7655120004fe7655120004fd7655120004fc765512004cfe76d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d2002cff72d8d20014fe72d8d2002cfd72d8d20014fc72d8d200e6df32d8d200e6dd32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d200e6ef21d8d2007d7e7598d200057d7598d20006df6398d200c5f97098d20105fb7058d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d200c4ff7258d20006ef7258d20004ff7158d2000cfe7158d2000cfc7158d200c6ef2158d20104ff7058d20006fb7058d200e4fe7618d2004ede6318d20006dd6318d2004cff7694d20004fe7694d20004fd7694d2004cfc7694d20015ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d200267c6554d2004cff7690d20
  | 7 => 0x8e200c6df3258e200c6dd3258e20004ff7158e2000cfe7158e2000cfc7158e2002cfe7058e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e2002efa1058e2004cff7694e2002cfe7694e20004fd7694e2002cfc7694e20015ee7294e20005ed7294e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e200267e6554e200067d6554e2004cff7690e2002cfe7690e20004fd7690e2002cfc7690e20004ff7650e2002cfe7650e20004fd7650e2002cfc7650e2001ebe6450e20006bd6450e202fdef7650a2001eef7650a2001cef7650a200076f7550a200076c7550a202feef6550a20006ed6550a20015ef7450a20017af7450a2001eee6450a202ffae6450a202ffad6450a2001eec6450a2008fae5450a20007ad5450a202feef6350a20006ed6350a20007ae4350a2008fac4350a2008faf4150a202fdef7050a20007eb7050a202ffe87050a20016ee6050a20017ea6050a202ffea5050a202ffaf4050a202ffad4050a20004ff7558620024fe7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff735862004cfc7358620036ee4258620006ed425862002ef77158620086f63158620086f62158620036f5215862002cff705862002cfe705862002cfd705862002cfc705862002eef205862002eed205862002ef6105862002ef410586200267f76d462031e7e76d46200967d76d46200267c76d462031e7f64d46201e67e64d46200067d64d462031e7c64d462031e7f63d46203267e63d46200067d63d462031e7c63d46201df6e42d46200076d42d462031e7f61d462000e7e61d46200867d61d462000e7c61d462031f7a70d46200977970d462031e7e60d462031f6f20d46201df7b20d462031f7820d462031f7a10d4620004ff7654620004fd765462002cfc76546202d67f65546200267e65546200067d65546200267c6554620005ef7254620015ec725462002dfa70546202d77a50546200067f76546202d67e76546200067d76546202d67c76546202d67f64546201d67e64546200067d64546202d67c64546202d67f63546203167e63546200067d63546202d67c63546200076f72546201cf6c72546201cf6e42546200076d42546200977771546202d67f615462000e7e61546200867d615462000e7c61546200877641546200877621546201cf7521546202d77a70546200077970546202d67e60546202d76f20546201cf7b20546202d77820546202d77a1054620004ff7650620004fd765062002cfc765062001ebe6450620006bd6450620007ad425062000775515062004cff76cc62002cfe76cc620004fd76cc62004ede63cc620006dd63cc620004ff764c620004fd764c62002cfc764c62004ede634c620006dd634c62000ef6614c620006f5614c62002df
  | 8 => 0x31e7f64d44301e67e64d443031f3e64d44301e63e64d44300067d64d443031f3d64d44300063d64d443031e7c64d44303275e73d44300b75d73d44300fe7e63d44301de7e62d443031f6e62d44301de6e62d44300067d62d443031f6d62d44300066d62d443031e7c62d44302d57d71d443031e7f61d443000e7e61d443031f7661d443000e7661d443009e7d61d443031f7561d44300067561d443000e7c61d443031f7a70d44300b77970d443031e7e60d443031f5f30d443031f7a30d443031f5d30d44303277930d4430004ff7654430004fd765443002cfc76544302d67f65544300267e65544300067d65544300267c65544301d6be6454430006bd64544301ceee6254430006ed625443000ef66154430006f561544302d57f76544300067f76544300047f76544302d67e76544302d57d76544300067d76544300047d76544302d67c76544302d67f64544301d67e64544302d73e64544301d63e64544300067d64544302d73d64544300063d64544302d67c64544300fe7e63544301ce7e62544302d76e62544301ce6e62544300067d62544302d76d62544300066d62544302d67c625443031d7f71544300b77771544302d67f615443000e7e61544302d776615443000e76615443009e7d61544302d775615443000675615443000e7c615443009f76415443009f7621544302d67e60544302d75f30544302d77a30544302d75d3054430317793054430004ff7650430004fd765043002cfc76504301c67e65504300067d655043001ebe6450430006bd6450430005df735043004ddc73504301beee6250430006ed625043000ef66150430006f56150430007755150430004ff7648430004fd764843002cfc76484301867e65484300067d654843017ebe6448430006bd6448430016ee6248430006ed624843000ef66148430006f56148430007755148430005fb704843002df8704843002e7f7559620004ff745962001cfe745962001cfc74596200067e54596200967c5459620004ff735962004cfc73596200967f53596201567f52596201567d5259620156ee4259620004ff715962000cfe715962000cfc71596200967f515962002cfe705962002cfc705962002e7e505962002e7c5059620004ff7559220024fe7559220024fc755922002ebf7459220006bf545922008ebc5459220004ff735922004cfc735922008ebf4359220126bf4259220126bd4259220004ff715922000cfe715922000cfc715922008ebf415922002cfe705922002cfc705922002efa505922002ebe405922002ebc4059220126fb205922002ef8205922002efa1059220004ff765522002cfe7655220004fd765522002cfc7655220004ff7558e20024fe7558e20024fc7558e20004ff7458e2001cfe7458e2001cfc7458e2002edf7358e200c6ee425
  | 9 => 0xe735883004eec735883004eef535883004eee535883004eed535883004eec535883004eef435883004eee435883004eed435883004eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef5158830006ee5158830006ec5158830006ef4158830006ee4158830006ec415883004eef315883004eee315883004eed315883004eec315883002eef705883002eee705883002eec705883002eef505883002eee505883002eed505883002eec505883002eef405883002eee405883002eed405883002eec405883002eef305883002ecf305883002eee305883002eed305883002ecd305883002eec305883002eef105883002eee105883002eed105883002eec1058830004ff7654830004fd765483002cfc76548300267e65548300067d6554830236be6454830006bd6454830016ee6254830006ed625483022ef66154830004ff7650830004fd765083002cfc76508300057f75508300b57c75508302267e65508300067d655083001ebe6450830006bd6450830016ee6250830006ed625083021ef66150830004ff7558430024fe75584300067e75584300067d7558430024fc7558430004ff745843001cfe745843001cfc745843000cfd7358430004ff7258430014fe7258430014fc725843002cff715843002ef77158430006f7515843009ef6515843009ef45158430006f7415843009ef6415843009ef4415843004ef7315843004ef43158430006f7215843009ef6215843009ef4215843002cfc705843002edf305843002efa305843002edd305843004ef9305843002ef6105843002ef41058430006f77558430006f67558430006767558430006f57558430006757558430006f47558430006f77458430006f67458430006f57458430006f47458430006f75458430006f65458430006f55458430006f4545843004ef7735843004ef6735843004ef4735843004ef7535843004ef6535843004ef5535843004ef4535843004ef7435843004ef6435843004ef5435843004ef44358430006f77258430006f67258430006f57258430006f47258430006f75258430006f65258430006f55258430006f45258430006f74258430006f64258430006f54258430006f4425843004ef7325843004ef6325843004ef5325843004ef4325843002ef7705843002ef6705843002ef4705843002ef7505843002ef6505843002ef5505843002ef4505843002ef7405843002ef6405843002ef5405843002ef4405843002ef7305843002ed7305843002ef6305843002ef2305843002ef5305843002ed5305843004ef1305843002ef4305843002ef7205843002ef6205843002ef5205843002ef4205843031d7f76d44300267f76d44300247f76d443031e7e76d443031d7d76d44300b67d76d44300047d76d44300267c76d4430
  | 10 => 0x94300067c415943004e7f315943004e7e315943004e7d315943004e7c31594300067f21594300067e21594300067c215943002e7f705943002e7e705943002e7d705943002e7c705943002e7f405943002e7e405943002e7d405943002e7c405943002e7f305943002e7e305943002e7d305943002e7c305943002e7f205943002e7e205943002e7d205943002e7c205943002e7f105943002e7e105943002e7d105943002e7c1059430004ff7559030024fe7559030024fc755903002cff745903002ebf7459030006bf54590300aebe54590300aebc545903004cff735903004cfe735903004cfd735903004cfc735903004ebe435903004ebc4359030004ff7259030014fe7259030014fc72590300aebf4259030006be42590300aebc4259030004ff715903000cfe715903000cfc71590300aebf4159030006be41590300aebc415903002cfe705903002cfc705903002ebe405903002ebc405903002efa305903004ef93059030006bf7559030006be7559030006bd7559030006bc755903004ebf735903004ebe735903004ebd735903004ebc735903004ebf535903004ebe535903004ebd535903004ebc5359030006bf7259030006be7259030006bd7259030006bc7259030006bf5259030006be5259030006bc525903004ebf325903004ebe325903004ebd325903004ebc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006be5159030006bc515903004ebf315903004ebe315903004ebd315903004ebc3159030006bf2159030006be2159030006bc215903002ebf705903002ebe705903002ebd705903002ebc705903002ebf505903002ebe505903002ebd505903002ebc505903002ebf305903002ebe305903002eba305903002ebd305903004eb9305903002ebc305903002ebf205903002ebe205903002ebd205903002ebc205903002ebf105903002ebe105903002ebd105903002ebc1059030004ff765503002cfe7655030004fd765503002cfc76550300267e65550300067d655503001ebe6455030006bd64550302a6ee625503029ef66155030004ff7558830024fe7558830024fc7558830004ff745883001cfe745883001cfc7458830014fd735883002cff725883002eef7258830006ef52588300a6ee52588300a6ec5258830006ef42588300a6ee42588300a6ec425883004eef325883004eec3258830004ff715883000cfe715883000cfc71588300a6ef2158830006ee21588300a6ec215883002cfc705883002edf305883002edd305883002eee205883002eec2058830006ef7558830006ee7558830006ed7558830006ec7558830006ef7458830006ee7458830006ed7458830006ec7458830006ef5458830006ee5458830006ed5458830006ec545883004eef735883004ee
  | 11 => 0xef4614c53004fd4314c530005fb704c53002df8704c53004fd8304c53002ddc764c53000edc764c53002cdc764c530006df644c530006dd644c530005df724c530006df624c53004ddf714c53004fd7714c530007d7614c53000ede614c53000edc614c5300bfd4614c5300bf5f514c5300bf5d514c5300bfd6414c530007d5414c530007db704c53002dde704c53002ddc704c530007d8704c53004edf604c53004fdb604c5300bfd7104c530004ff7648530004fe7648530004fc764853004dde7348530005dd7348530016ee6248530007cd3248530007755148530024ff76541300d4fd765413004cfc76541300067f65541300267c6554130005df735413004ddc735413002fd83054130005fa769013002efa769013002f7a759013002f797590130006fb6590130006f965901300cdf9749013001efa649013001ef8649013004dfa739013002df8739013002efb639013002fdb6390130136fa6290130136f86290130007db3290130007d93290130005f97190130006fb61901300077b5190130007795190130007db3190130007d9319013001cff76501300ccfd765013004cfc7650130006bf645013001ebc6450130005df735013004ddc735013002fb8405013004df8765013001ef8765013004cf87650130006fb6550130006f9655013002dfb745013002fbb7450130007bb645013001efa645013001ef864501300cfb86450130367bb54501300cfb85450130007db735013004dfa735013004df87350130007d8735013002efb635013002fdb63501300cfbb4350130007b94350130126fa6250130126f862501300cfbb4250130007b94250130007db3250130007d93250130005fb7150130006fb61501300077b51501300077951501300cfbb4150130007b94150130007db3150130007d9315013002cff755943002e7f7559430004ff745943001cfe745943001cfc74594300b67f54594300067e54594300b67c545943004cff735943004cfe735943004cfd735943004cfc735943004e7e535943004e7c5359430004ff7259430014fe7259430014fc72594300b67f52594300067e52594300b67c5259430004ff715943000cfe715943000cfc71594300b67f51594300067e51594300b67c515943002cfe705943002cfc705943002e7e505943002e7c50594300067f74594300067e74594300067d74594300067c745943004e7f735943004e7e735943004e7d735943004e7c735943004e7f435943004e7e435943004e7d435943004e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067c425943004e7f325943004e7e325943004e7d325943004e7c32594300067f71594300047f71594300067e71594300067d71594300067c71594300067f41594300067e415
  | 12 => 0xd74d893001cfc74d893002cfd73d8930014fc73d89300c6ee42d89300c6ee32d893000cfe71d8930004fd71d893000cfc71d893004cfd70d89300c6ef20d89300c6ec6258930004ff7654930004fe7654930004fc7654930004ff7650930004fe7650930004fc76509300057f75509300d57c7550930006bf645093001ebc6450930006ef6250930016ec6250930005de76cc93004ede76cc93004f5e75cc93004f5d75cc930006df65cc930006dd65cc93020ede64cc93020edc64cc9300c5dd72cc930016de62cc930016dc62cc930005dd71cc93002dde70cc93002ddc70cc93004edf60cc93004fdb60cc93002cfc764c930006ef624c930016ec624c93004fcc324c930005fb704c93002df8704c93002ddc764c930016dc764c93002cdc764c930006df654c930006dd654c9301f6de644c9301f6dc644c93004ddf724c93004fcf724c930007cf624c930016de624c930016dc624c9300c7cc624c93036fcf524c9300c7cc524c9300c7ce424c930007cd424c930005df714c9300c7cf214c930007db704c93002dde704c93002ddc704c930007d8704c93004edf604c93004fdb604c9300c7cf204c93000cfe76d85300bef661d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853002cfd73d853000cfc73d8530014fe72d8530004fd72d8530014fc72d8530006df32d8530006dd32d85300bef651d85300bef631d853004cfd70d85300bef710d85300bef461585300267f76d45300d67e76d45300d67d76d45300267c76d45300067f64d45301e67e64d45300067d64d45301e67c64d45300067f62d45301de7e62d45301de7c62d45300075f32d45300075d32d45300bd7d71d45300be7f61d453000e7e61d453000e7c61d45303277b30d453031f5e30d4530004ff7654530004fe7654530004fc76545300067f65545300267e65545300067d65545300267c6554530006f7615453000ef461545300067f76545300067e76545300067d76545300067c76545300067f64545301d67e64545300067d64545301d67c64545300067f62545301ce7e62545301ce7c62545300075f32545300075d32545300bd7f71545300d77771545300be7f615453000777615453000677615453000e7e615453000e7c61545300bf74615453000e7461545300bf7641545300bf7621545303177b30545302d75e3054530004ff7650530004fe7650530004fc765053001ebe6450530006bd6450530007755150530005de76cc53004ede76cc530006df64cc530006dd64cc530005dd72cc530006df62cc5300bddd71cc53000ede61cc53000edc61cc5300bf5f51cc5300bf5d51cc53004fdb70cc53002dde70cc53002ddc70cc53004fd870cc53004edf60cc53004fdb60cc53002cfc764c530006f7614c530
  | 13 => 0x463031f5f30d46303277b30d463031f7a10d4630004ff7654630004fd765463002cfc76546302d67f65546300267e65546300067d65546300267c65546300067f76546302d67e76546300067d76546302d67c76546302d67f64546301d67e64546300067d64546302d67c64546301ce7e62546300067d62546302d67c62546300f77771546302d67f615463000e7e61546300de7d615463000e7c61546300df7641546300df7621546302d77a40546302d75f30546303177b30546302d77a1054630004ff7650630004fd765063002cfc765063001ebe6450630006bd6450630005df735063004ddc735063000775515063002dfa705063000cff764c63000ef6614c630006f5614c630005fb704c63002df8704c630004ff7648630004fd764863002cfc7648630016ee6248630006ed624863000ef66148630006f5614863000775514863002dfb76502300aefb765023002efb6550230006f9655023002fbb745023002fbb645023001efa645023002ef8645023002fb86450230377bb54502300efb8545023004dfa735023004df873502300efbb4350230007b94350230126fa625023002ef862502300efbb4250230007b94250230005fb7150230006f961502300077b51502300077951502300efbb4150230007b94150230024fe76d95300d67e65d953001cfe74d9530004fd74d953001cfc74d953004cfe73d953002cfd73d953004cfc73d95300d67f53d9530014fe72d9530004fd72d9530014fc72d953000cfe71d9530004fd71d953000cfc71d95300d67f51d953004cfd70d95300d67f50d95300d67c65595300d4ff75595300067f7559530004ff745953001cfe745953001cfc74595300f4ff7359530006df7359530004ff7259530014fe7259530014fc7259530004ff715953000cfe715953000cfc71595300d67f5159530114ff7059530006fb705953001cfe76d91300cebe64d9130024fe75d9130004fd75d9130024fc75d913004cfe73d913002cfd73d913004cfc73d91300cebf43d9130014fe72d9130004fd72d9130014fc72d91300cebf42d913000cfe71d9130004fd71d913000cfc71d913004cfd70d91300cebf40d91300cebc6459130004ff7559130024fe7559130024fc75591300ccff7459130006bf74591300ecff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff715913000cfe715913000cfc71591300cebf415913010cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc765513002cfc7654d300067f6554d300267c6554d30005fb7054d3002df87054d3004fd83054d3002cfc7650d30006bf6450d3001ebc6450d30005fb7050d3002df87050d30014fe76d89300c6ee62d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004f
  | 14 => 0x9edf764c73004edf644c730006dd644c730005df724c730006dd624c73004fd7714c73004fd7614c73000ede614c73000edc614c73004fd4614c7300ff5f514c7300ff5d514c7300ffd6414c730007d5414c73002dde704c73002ddc704c7300ffd7104c730004ff7648730004fd764873004cfc764873004dde7348730005dd7348730016ee6248730006ed6248730007cd3248730007755148730005fb704873002df87048730024ff765433004cfc76543300267e65543300067d6554330005df735433004ddc735433001cff765033004cfc765033001ebe6450330006bd6450330005df735033004ddc735033002e7f7559630004ff745963001cfe745963001cfc74596300067e54596300f67c54596300f67f5359630004ff7259630014fe7259630014fc72596300f67f5259630004ff715963000cfe715963000cfc71596300f67f515963002cfc705963002e7e505963002e7c505963002efa4059630004ff7559230024fe7559230024fc755923002ebf7459230006bf54592300eebc54592300eebf4359230004ff7259230014fe7259230014fc72592300eebf4259230004ff715923000cfe715923000cfc71592300eebf415923002cfc705923002ebe405923002ebc405923002efa1059230004ff765523002cfe7655230004fd765523002cfc765523004efb3058e3002ede3058e3002edc3058e3002ef83058e30024ff7654e3002cfc7654e300267e6554e300067d6554e30005fb7054e3002df87054e3001cff7650e3002cfc7650e3001ebe6450e30006bd6450e3004f9c4350e30005fb7050e3002df87050e30004ff7558a30024fe7558a30024fc7558a30004ff7458a3001cfe7458a3001cfc7458a3002eef7258a300e6ee3258a30004ff7158a3000cfe7158a3000cfc7158a300e6ef2158a3002cfc7058a3002edf3058a3002edd3058a3002eee2058a3002eec2058a3002efa1058a30004ff7654a30004fd7654a3002cfc7654a300267e6554a300067d6554a30004ff7650a30004fd7650a3002cfc7650a300057f7550a300f57c7550a3001ebe6450a30006bd6450a30016ec6250a30014ff764ca30016ee624ca30006ed624ca30005fb704ca3002df8704ca30004ff7558630024fe7558630024fc7558630004ff745863001cfe745863001cfc7458630004ff7258630014fe7258630014fc725863002ef771586300def631586300def6215863002cfc705863002efa405863002edf305863002edd305863002ef6105863002ef410586300267f76d463031e7e76d46300f67d76d46300267c76d463031e7f64d46301e67e64d46300067d64d463031e7c64d46300f75e73d46300f75d73d46301de7e62d46300067d62d463031e7c62d463031e7f61d463000e7e61d46300de7d61d463000e7c61d463031f7a40d
  | 15 => 0x9415414004e7f7559730004ff745973001cfe745973001cfc74597301167f545973002cfc735973004e7e535973004e7c5359730004ff7259730014fe7259730014fc72597300067e52597301167c525973004edf3259730004ff715973000cfe715973000cfc71597301167f51597301167f5059730004ff7559330024fe7559330024fc755933004ebf745933002cfc735933004ebe435933004ebc4359330004ff7259330014fe7259330014fc7259330004ff715933000cfe715933000cfc715933010ebf415933004edf315933010ebf405933004efa305933004ef93059330004ff765533004cfe7655330004fd765533004cfc76553300267e65553300067d6555330004ff7558b30024fe7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3002cfc7358b3004eef7258b30006ef5258b30106ec5258b30106ee4258b3004eef3258b3004eec3258b30004ff7158b3000cfe7158b3000cfc7158b3004edf3158b30106ef2158b30106ef2058b30004ff7654b30004fd7654b3004cfc7654b30004ff7650b30004fd7650b3004cfc7650b300057f7550b301157c7550b30386bf6450b3001ebc6450b30016ee6250b30006ed6250b3004ddf764cb300a6df764cb3004edf654cb30006dd654cb301f6de644cb3004edc644cb3004fcf724cb3004fcf624cb30016de624cb30016dc624cb3004fcc624cb3037fcf524cb30107cc524cb30107ce424cb30007cd424cb30005df714cb30107cf214cb3002dde704cb3002ddc704cb30107cf204cb30004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc745873002cfc7358730004ff7258730014fe7258730014fc725873004edf3258730006dd325873004ef771587300fef6415873004ef7315873004ef4315873004efa305873004ef930587300fef710587300267f76d47303267e76d47301167d76d47300267c76d47303267f64d47301e67e64d47300067d64d47303267c64d47301de7e62d47300067d62d47301de7c62d47303275f32d47300075d32d47300fe7f61d473000e7e61d47300fe7d61d473000e7c61d47300ff5f31d47301177a70d47301177970d4730004ff7654730004fd765473004cfc76547303167f65547300267e65547300067d65547300267c65547300067f76547303167e76547300067d76547303167c76547303167f64547301d67e64547300067d64547303167c64547301ce7e62547300067d62547301ce7c62547303175f32547300075d32547301177771547300fe7f615473000e7e61547300fe7d615473000e7c61547300ff7641547300ff5f31547300ff762154730004ff7650730004fd765073004cfc765073001ebe6450730006bd645073000ef66150730006f5615073000775515073004ddf764c730
  | 16 => 0x45400267e65545400067d65545400267c6554540005bf745454001dbc745454012f3f54545401d73c54545400067f76545400067e76545400067d76545400067c76545400073f74545401d73c74545402d67f64545400067f63545403167c63545401d73f43545400073d43545400067f62545401ce7e62545401ce7c62545401d73f42545400073d425454011d7f715454012f77715454011e7f615454000e7e615454000e7c615454011f3f415454011f7641545401d775415454011f7621545400077a70545400077970545402ce7f60545401d77b40545402d73e40545402d73c40545401d778405454039f7b205454039f78205454002dbc765054000ebc765054002cbc765054012dbe755054012dbc7550540005bf7350540006bf6350540005bf7250540006bf625054001dbf715054001fb77150540007b7615054000ebe615054000ebc615054011fb4615054011f3f515054011fb6515054011f3d5150540007b5515054000735515054011fb63150540007bb705054002dbe705054002dbc7050540007b8705054001ebf605054001fbb6050540397bb2050540397b82050540004fe76cc540004fd76cc54004cfc76cc54001dbe74cc540005bd74cc54004ede63cc5400079d43cc54002dfa70cc540005f970cc540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c5400079d434c54000ef6614c540007b5414c540004ff7648540004fe7648540004fc764854001dbe7448540005bd7448540016ee6248540007ad4248540007755148540005fb704854002df87048540127eb204854038dfa769414002efa769414015df97594140026fa6594140026f8659414001dfa749414002fba749414001dba749414002fb9749414002df8749414002efb649414002fbb649414012fbb5494140177b85494140005f97394140177bb4394140007b94394140125fa729414002df87294140006fb6294140177bb4294140007b94294140005f9719414012f7b5194140007795194140177bb4194140007b94194140024ff765414001cfe765414015cfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc745414015f3c545414001df87654140026f8765414001cf8765414002dfb755414002f7b75541400077b6554140026fa6554140026f8655414012f786554140007bb745414001dfa745414001df8745414015fb8745414002efb645414002fbb645414012fbb545414015f7a545414015f78545414015fb8545414015f385454140005fb735414012f7b535414000779535414015fbb4354140007b94354140125fa7254140125f87254140006fb625414012f7b525414000779525414015fbb4254140007b94254140005fb715414012f7b515414000779515414015fbb4154140007b
  | 17 => 0x1dbf7350d4001f9f7350d400079f6350d4004ebe6350d4004ebc6350d400079c6350d4004e9c6350d400079e5350d400079d5350d40005bf7250d40005bf7150d40007bb7050d4002dbe7050d4002dbc7050d40007b87050d4001ebf6050d4001fbb6050d403bfbb2050d403bfb82050d40014fe76d8940126ee62d894002dfa70d894001df970d8940127eb20d8940024fe75d8940004fd75d8940024fc75d894002cfd74d8940014fc74d894004cfe73d8940004fd73d8940126ee42d894008eed42d894000cfe71d8940004fd71d894000cfc71d894008ebf41d894001cfd70d8940126f970d894001cf970d8940126ef20d8940126fb20d8940126f820d89400057f755894012d7c7558940126ec62589403b5fb7058940127e82058940004ff7654940004fe7654940004fc7654940005bf745494001dbc7454940005fb705494002df8705494002dbc7650940016bc765094002cbc76509400073f755094012dbe755094012dbc75509400073c755094012d3c7550940006bf6550940006bd6550940005bf7350940386bc635094001dbf725094001faf7250940007af6250940016be6250940016bc6250940127ac6250940127ae5250940007ad5250940127ae3250940005bf7150940127af2150940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb6050940127bb20509402ffac2050940127b82050940127a82050940004fe76cc940004fd76cc94004cfc76cc94012d7e75cc9400057d75cc94001dbe74cc940005bd74cc940006df63cc94004edc63cc94020f9f43cc94002dfa70cc940005f970cc940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940006df634c94004edc634c9401f79f434c940016ee624c940007ad424c940005fb704c94002df8704c940127eb204c94000cfe76d854011ef661d8540024fe75d8540004fd75d8540024fc75d854002cfd74d854000cfc74d854004cfe73d8540004fd73d854005ebf43d8540006bd43d8540014fe72d8540004fd72d8540014fc72d854005ebf42d8540006bd42d854011ef641d854005ef541d854001cfd70d854011ef710d8540005df7358540005dc735854011ef461585403adfb70585400267f76d454012e7e76d454012e7d76d45400267c76d454012f3f74d45401e73c74d454031e7f64d45400067f63d45403267c63d45401e73f43d45400073d43d45400067f62d45401de7e62d45401de7c62d45401e73f42d45400073d42d454011d7d71d454011e7f61d454000e7e61d454000e7c61d454011f3f41d454012f7a70d454012f7970d45402ce7f60d45401e77b40d454031f3e40d454031f3c40d45401e77840d45403a77b20d45403a77820d4540004ff7654540004fe7654540004fc76545400067f655
  | 18 => 0x771546402d67f615464000e7e615464013e7d615464000e7c615464013f7641546401d775415464013f7621546402d77a70546400077970546402d67e60546402d73f40546401d77b40546402d77840546403d77b20546402d77820546402d77a105464004cff76cc64002cfe76cc640004fd76cc6401b67e65cc6400067d65cc64004ede63cc640006dd63cc64002dfa70cc640005f970cc640004ff764c640004fd764c64002cfc764c64019e7e654c6400067d654c64004ede634c640006dd634c64000ef6614c640006f5614c64002dfa704c640004ff7648640004fd764864002cfc76486401867e65486400067d6548640016ee6248640006ed624864000ef66148640006f56148640007755148640005fb704864002df87048640137eb204864002dfb76542403cefb765424002f7b7554240026fa655424002f7a65542400267a655424002f79655424002ef8655424001dfa745424001df8745424015f7a545424015f785454240005fb73542401477b5354240007795354240135fa7254240135f87254240006f962542401477b5254240007795254240005fb71542401477b5154240007795154240024fe76d954012e7e65d954001dbe74d954002dbd74d954012f3f54d954002cff74d954001cfe74d954002cfd74d954012ebd74d954002cbd74d954001cfc74d95401767f54d954012ebf54d95401767d54d9540176bc54d954004cfe73d9540004fd73d9540014fe72d9540004fd72d9540014fc72d95400067e52d954012e7c52d9540176bf42d954000cfe71d9540004fd71d954000cfc71d954012e7f51d954001cfd70d954012e7f50d954012e7c655954015f3c54595403c5fb7059540174ff75595400067f755954015cff7459540006bf745954012ebf545954015e7e545954015e7c545954015ebc5459540004ff735954004cfc735954012e7f5359540004ff7259540014fe7259540014fc725954015ebf4259540004ff715954000cfe715954000cfc715954012e7f51595403c4ff7059540006fb7059540024fe75d8d40004fd75d8d40024fc75d8d4002cfd74d8d400eede43d8d400eedd43d8d40014fe72d8d40004fd72d8d40014fc72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d400eebf41d8d40006de31d8d40006dc31d8d40006df6398d400cdf97098d4010dfb7058d4012d7e7518d400057d7518d4004ede6318d40006dd6318d40125ee7218d40005ed7218d4011df67118d40005f57118d40004fe7694d40004fd7694d4004cfc7694d4001dbe7494d40005bd7494d40125ee7294d40005ed7294d4002dfa7094d40005f97094d40004ff7654d40004fe7654d40004fc7654d400267e6554d400067d6554d40005bf7454d4001dbc7454d4012f3f5454d4002cbc7650d4012dbe7550d4012dbc7550d40
  | 19 => 0x964002e7f305964002e7e305964002e7d305964002e7c305964002e7f205964002e7e205964002e7d205964002e7c205964002e7f105964002e7e105964002e7d105964002e7c1059640004ff7558e40024fe7558e40024fc7558e4002edf7358e400cede4358e400cedd4358e40004ff7258e40014fe7258e40014fc7258e40004ff7158e4000cfe7158e4000cfc7158e4002cfc7058e4002ebf4058e4002ebd4058e4002ede3058e4002edc3058e4002efa1058e4004cff7694e4002cfe7694e40004fd7694e400267e6594e400067d6594e40135ee7294e40005ed7294e4002dfa7094e40005f97094e40004ff7654e40004fd7654e4002cfc7654e400267e6554e400067d6554e4002dfa7054e40004ff7558a40024fe7558a40024fc7558a40004ff7358a4004cfc7358a4002eef7258a40136ee4258a40076ed4258a40136ee3258a40004ff7158a4000cfe7158a4000cfc7158a40136ef2158a4002cfe7058a4002cfc7058a4002ef87058a4002cf87058a4002efa5058a4002ebf4058a4002ebd4058a40136fb2058a4002eee2058a4002eec2058a4002ef82058a4002efa1058a40004ff7654a40004fd7654a4002cfc7654a400267e6554a400067d6554a40005fb7054a4002df87054a4004cff76cca4002cfe76cca40004fd76cca401457e75cca400057d75cca402167e65cca400067d65cca4004ede63cca40006dd63cca4002dfa70cca40005f970cca40004ff764ca40004fd764ca4002cfc764ca401fe7e654ca400067d654ca4004ede634ca40006dd634ca40016ee624ca40006ed624ca40005fb704ca4002df8704ca40137eb204ca40004ff7558640024fe75586400067e75586400067d7558640024fc7558640004ff735864004cfc7358640004ff7258640014fe7258640014fc725864002ef7715864013ef6415864003ef5415864013ef6315864013ef6215864002cfe705864002cfc705864002ebf405864002ebd405864002efa305864002ef6105864002ef4105864031d7f76d46400267f76d46400247f76d464031e7e76d464031d7d76d46401467d76d46400047d76d46400267c76d46403267e63d46400067d63d46401de7e62d46400067d62d464031e7c62d464031e7f61d464000e7e61d464013e7d61d464000e7c61d464031f7a70d46401477970d464031e7e60d464031f3f40d46401e77b40d464031f7840d46403df7b20d464031f7820d464031f7a10d4640004ff7654640004fd765464002cfc76546402d67f65546400267e65546400067d65546400267c655464002dfa70546402d77a50546402d57f76546400067f76546400047f76546402d67e76546402d57d76546400067d76546400047d76546402d67c76546403167e63546400067d63546401ce7e62546400067d62546402d67c62546401477
  | 20 => 0x4fe76cc950004fd76cc95004cfc76cc9500257e75cc9500057d75cc95004ede63cc9500075d53cc950004ff764c950004fe764c950004fc764c9500257e754c9500057d754c9500075d534c950006ef624c950016ec624c9501ff6f524c95000cfe76d855014ef661d855031e7f75d855002cfd75d855000cfc75d855000c7c75d855001cfe74d8550004fd74d855001cfc74d85500067e54d85500667c54d855004cfe73d8550004fd73d85500667f53d85500067d53d8550014fe72d8550004fd72d8550014fc72d85500667f52d85500067d52d855014e7f51d855014ef651d8550066f551d8550024fd70d855031e7e50d855031e7c50d855014ef710d8550005ef7258550155ec725855014ef461585503e5fb70585502d67e765455002d7c765455000e7c765455002c7c765455015d7e745455015d7c74545500067f64545501d67e64545501d67c64545500057f73545500067f63545503167c63545500057f72545500067f62545501ce7e62545501ce7c62545500257f715455002777715455014e7f615455000777615455000677615455000e7e615455000e7c615455014f74615455014f76415455014f7621545500077b705455002d7e705455002d7c70545500077870545500267f60545500277b6054550004ff7650550004fe7650550004fc76505500057f75505500257c7550550007755150550004fe76cc550004fd76cc55004cfc76cc5500257e75cc5500057d75cc550004ff764c550004fe764c550004fc764c5500257e754c5500057d754c550005fb704c55002df8704c550004ff7648550004fe7648550004fc76485500257e75485500057d754855000ef6614855000775514855002e7f755964015e7f545964015e7d5459640004ff735964004cfc73596401467f53596401467c5359640004ff7259640014fe7259640014fc72596401467f52596400067e52596401467c5259640004ff715964000cfe715964000cfc71596401467f51596400067e51596401467c515964002cfe705964002cfc705964002e7e505964002e7c505964015e7f745964015e7e745964015e7d745964015e7c74596400067f73596400067e73596400067d73596400067c735964015e7f435964015e7e435964015e7d435964015e7c43596400067f72596400067e72596400067d72596400067c725964015e7f425964015e7e425964015e7d425964015e7c42596400067e32596400067c32596400067f71596400047f71596400067e71596400067d71596400067c715964015e7f415964015e7e415964015e7d415964015e7c41596400067e31596400067c31596400067f21596400067e21596400067c215964002e7f705964002e7e705964002e7d705964002e7c705964002e7f405964002e7e405964002e7d405964002e7c405
  | 21 => 0x621546502d57f70546500077b70546502d77870546500267e60546500277a6054650004ff7650650004fd765065002cfc765065001ebe6450650006bd645065000775515065004cff76cc65002cfe76cc650004fd76cc6501aebe64cc650006bd64cc65004ede63cc650006dd63cc650004ff764c650004fd764c65002cfc764c650196be644c650006bd644c65004ede634c650006dd634c65000ef6614c650006f5614c650005fb704c65002df8704c650004ff7648650004fd764865002cfc764865017ebe6448650006bd6448650016ee6248650006ed624865000ef66148650006f5614865000775514865001cfe76d91500257e75d915015ebe64d915015f3e54d915002cfd75d915002c7d75d915001cfc75d915015e7e54d915015ebe54d9150146bd54d915015e7c54d915004cfe73d9150004fd73d91501467f53d9150014fe72d9150004fd72d9150014fc72d915000cfe71d9150004fd71d915000cfc71d91501467f51d9150024fd70d915015ebf40d915015ebc645915015f3c54591503f5fb705915002cfd75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d500f6de53d8d500f6dd53d8d50014fe72d8d50004fd72d8d50014fc72d8d5000cfe71d8d50004fd71d8d5000cfc71d8d500f67f51d8d50006df6398d50155ee7298d50005ed7298d500d5f97098d50115fb7058d5004ede6318d50006dd6318d5002c7c7654d5015d7e7454d5015d7c7454d500067f6454d500257f7354d500275f7354d500075f6354d5004e7e6354d5004e7c6354d500075c6354d500057f7254d502767e6254d502767c6254d500057f7154d500077b7054d5002d7e7054d5002d7c7054d50007787054d500267f6054d500277b6054d50004fe7690d50004fd7690d5004cfc7690d500257e7590d500057d7590d500075d5390d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257c7550d500075d5350d50014fe76d8950156ee62d895002cfd75d8950014fc75d895001cfe74d8950004fd74d895001cfc74d895004cfe73d8950004fd73d8950156ee52d8950096ed52d8950156ee42d8950156ee32d895000cfe71d8950004fd71d895000cfc71d89500967f51d8950006ee21d8950156ec21d8950024fd70d8950156ef20d8950156ec62589503edfb705895002d7c76549500167c765495002c7c765495015d7e745495015d7c74549500057f73549500257f72549500276f72549500076f62549500167e62549500167c62549501576c62549501576e42549500057f71549500077b705495002d7e705495002d7c70549500077870549500267f60549500277b6054950004ff7650950004fe7650950004fc76509500057f75509500257c755095001ebe645095015f3e5450950006ef6250950016ec62509500076d5250950
  | 22 => 0x925012ebf535925012ebe535925012ebd535925012ebc5359250006bf7259250006be7259250006bd7259250006bc725925012ebf525925012ebe525925012ebd525925012ebc5259250006be3259250006bc3259250006bf7159250006be7159250006bd7159250006bc715925012ebf515925012e3f515925012ebe515925012ebd515925012ebc5159250006be3159250006bc3159250006bf2159250006be2159250006bc215925002ebf705925002ebe705925002ebc705925002ebf505925002ebe505925002ebd505925002ebc505925002ebf305925002ebe305925002ebd305925002ebc305925002ebf205925002ebe205925002ebd205925002ebc205925002ebf105925002ebe105925002ebd105925002ebc1059250004ff7458e5001cfe7458e5001cfc7458e5002edf7358e500d6de5358e500d6dd5358e50004ff7258e50014fe7258e50014fc7258e50004ff7158e5000cfe7158e5000cfc7158e500d67f5158e5002cfc7058e5002e7f5058e5002e7d5058e5002efa4058e5002ede3058e5002edc3058e5004cff7690e5002cfe7690e50004fd7690e5001ebe6490e50006bd6490e50004ff7650e50004fd7650e5002cfc7650e5001ebe6450e50006bd6450e50004ff7458a5001cfe7458a5001cfc7458a50004ff7358a5004cfc7358a5002eef7258a5016eee5258a5007eed5258a5016eee3258a50004ff7158a5000cfe7158a5000cfc7158a5007e7f5158a5016eef2158a5002cfe7058a5002cfc7058a5002e7f5058a5002e7d5058a5002eee2058a5002eec2058a50004ff7650a50004fd7650a5002cfc7650a500057f7550a500257c7550a5001ebe6450a50006bd6450a50016ec6250a5002dfa7050a5004cff76cca5002cfe76cca50004fd76cca500257e75cca500057d75cca5020ebe64cca50006bd64cca5004ede63cca50006dd63cca50004ff764ca50004fd764ca5002cfc764ca501f6be644ca50006bd644ca5004ede634ca50006dd634ca50016ee624ca50006ed624ca500067d7558650004ff745865001cfe745865001cfc7458650004ff735865004cfc7358650004ff7258650014fe7258650014fc725865002ef771586501667f5158650166f65158650046f55158650166f63158650166f6215865002cfe705865002cfc705865002e7f505865002e7d505865002efa405865002efa205865002ef6105865002ef410586502d57f765465000e7f765465000c7f76546501d67e64546502d73e64546501d63e64546500067d64546502d73d64546500063d64546502d67c64546503167e63546500067d63546501ce7e62546500067d62546502d67c62546500257f715465002777715465000e7e61546502d77661546501667d61546502d775615465000675615465000e7c61546501677641546501677
  | 23 => 0x7ce534c921007cd534c921407cf434c921407cc434c921007e7714c92100dee714c92100dec714c9211efe4714c921016ef614c921017e7614c9211ef6f514c9211efe6514c9211ef6d514c9211efcf314c9211efcd314c921005ef704c9211efe7104c921015f47654521026f47654521014f4765452100df7755452100f777554521007776554521026f66554521026f46554521187746554521006f76454521006f564545211877754545213ff765454521007755454521187745454521187775354521007765354521007755354521187745354521007e77254521015f67254521015f472545211cfe4725452100ef7625452100fe762545211cf7752545211cf7652545211cf7552545211cf7452545211cfe64254521007e542545211cfe63254521007e53254521005f770545211877750545211877450545211cfe720545211877776545210267776545211cf7476545210267476545210077774545213ff7674545210077574545213ff7474545210077764545210067764545213ff7664545210077564545210067564545213ff7464545210077773545210077673545210077573545210077473545210077763545210077663545210077563545210077463545213ff7743545210077643545210077543545213ff7443545211cf7772545210076772545211cf7672545211cf7572545211cf7472545211cf64725452100f77625452100e77625452100f6762545211cf7742545211cf7642545211cf6642545211cf7542545210076542545211cf7442545211cf7732545211cf7632545211cf6632545211cf7532545210076532545211cf7432545210077770545210077670545210077570545210077470545213ff7740545213ff7440545211cf7720545211cf6720545211cf74205452102cfe76d81210077551d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d812104cfe73d8121004fd73d812100cfd72d812132eee32d8121006ed32d8121014fd71d81212c67f51d81212c67d51d812132efa20d81212c6fa10d8121007755198121006fb60981210077551581211857e75181210057d751812117dbe7418121005bd7418121005de7318121005dd731812100775511812102efa6018121006f9601812102ebf7459250176be545925012ebd5459250004ff735925004cfc7359250176bf4359250176bc4359250004ff7259250014fe7259250014fc7259250176bf4259250006be4259250176bc4259250004ff715925000cfe715925000cfc715925012e7f5159250176bf4159250006be4159250176bc415925002cfe705925002cfc705925002ebe405925002ebc405925012ebe755925012ebd7559250176bc7559250006bf7359250006be7359250006bd7359250006bc735
  | 24 => 0xd71d91214267f51d9121426f651d91214267d51d9121426bf41d9121426bd41d912102cfe70d9121004fd70d912101cff76591210057f75591211857c755912117ebc645912141def725912142df77159121004ff75591210067f75591210047f7559121024fe7559121024fc75591210067c75591210247c7559121424ff7459121006bf7459121004ff735912104cfc735912141cff7259121006ef72591211beee325912121cff7159121006f7715912121e7f515912121ef6515912121e7d5159121004ff705912102cfc705912117ebf4059121004ff7655121004fe7655121004fd7655121004fc765512104cfe76d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2100cff72d8d2100cfd72d8d21416ee42d8d21416df32d8d21416dd32d8d21014ff71d8d21014fd71d8d2140e7f51d8d2140e7d51d8d2140edf31d8d2140edd31d8d2102cfe70d8d21004fd70d8d21416ef20d8d2140ef710d8d211ecfd7698d211857e7598d210057d7598d21006df6398d211eded7298d2118df57198d2104cff7658d21205ef7258d211a5f77158d21005fb7058d21005f87058d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d21204ff7258d21006ef7258d2118eee4258d211ecff7158d21006f77158d211ee7f5158d211ee7d5158d21004ff7058d21006fb7058d21004fb7058d2102cfc7058d21006f87058d2102cf87058d2118eef2058d211eef71058d2140cfe7618d2104ede6318d21006dd6318d2104cff7694d21004fe7694d21004fd7694d2104cfc7694d21015ee7294d21005ed7294d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d2104cff7690d21004fe7690d21004fd7690d2104cfc7690d21015ee7290d21005ed7290d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21015ee7250d2100dec765092101eec765092100cec76509210076f75509210076c7550921006ef6550921006ed6550921015ef7450921017af7450921007af645092101eee645092101eec645092117fac645092117fae5450921007ad5450921005ef7350921006ef6350921006ed6350921007ae435092117fac4350921007e7715092100dee715092100dec715092121fe47150921016ef6150921017e7615092121f6f515092121fe6515092121f6d515092121faf415092121fad4150921005ef70509212feec605092117faf405092121fe7105092100dec764c92104eec764c92100cec764c9211feee654c9211feec654c921005ef744c921005ed744c921006ef644c921006ed644c921015ef734c921017cf734c921007cf634c92104eee634c92104eec634c921007cc634c921
  | 25 => 0xc931006df65cc931006dd65cc93104ddf74cc931005dd74cc93120ede64cc93120edc64cc9311eddd72cc931016de62cc931016dc62cc93100dde71cc93100ddc71cc93104edf61cc93104fd761cc9312075f51cc9312075d51cc931207d641cc931005dd70cc931207d710cc93100cfc764c931006ef624c931016ec624c93104fcc324c931005f7714c93100df4714c93100ddc764c931016dc764c93100cdc764c931006df654c931006dd654c931005df744c931005dd744c9311f6de644c9311f6dc644c93104ddf724c93104fcf724c931007cf624c931016de624c931016dc624c93118fcc624c931457cf524c93118fcc524c93118fce424c931007cd424c931007d7714c93100dde714c93100ddc714c9311efd4714c93100dd4714c93104edf614c93104fd7614c9311ef5f514c9311ef5d514c9311efd6414c9311efcf214c931005df704c93118fcf204c9311efd7104c93104df4765053101ef4765053104cf47650531006f76550531006f5655053100df7745053100fb77450531007b7645053101ef6645053101ef46450531197b46450531007d7735053104df6735053104df47350531007d4735053100ef7635053100fd76350531197b74350531197d64350531007b54350531197d54350531007954350531197b74250531007b54250531007d73250531007d53250531005f77050531197b74050531024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d8131014fe72d8131004fd72d8131014fc72d8131006df32d8131006dd32d813104cfd71d81310fe7f51d81310fe7d51d8131006fb20d8131006f820d81310fefa10d8131006fb609813119d7e75181310057d7518131195be7418131005bd741813118dee7218131005ed721813102efa6018131006f96018131024fe76d95211867e65d952122cfd75d952101cfe74d9521004fd74d952101cfc74d95210067e54d95211867c54d952104cfe73d9521004fd73d95211867f53d952100cff72d952100cfd72d952144e7f52d952144e7d52d952144eee42d9521014ff71d9521014fd71d95214467f51d95214467d51d952102cfe70d9521004fd70d9521024ff76595211867c655952143def72595211ddf77159521444ff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff735952104cfc735952143cff7259521006ef72595211ce7e52595211ce7c52595211ceee425952122cff7159521006f7715952122e7f515952122e7d5159521004ff705952102cfc70595211867f505952101cfe76d912117ebe64d9121024fe75d9121004fd75d9121024fc75d912121cfd74d912104cfe73d9121004fd73d912100cff72d912100cfd72d9121436bf42d9121436bd42d9121436ee32d9121014ff71d9121014f
  | 26 => 0x19e7f5459531474ff7359531006df73595313167e53595313167c5359531004ff7259531014fe7259531014fc72595310067e525953119e7c525953126cff7159531006f7715953126e7f515953126e7d515953126ef64159531004ff705953102cfc705953119e7f505953101cfe76d9131196be64d9131024fe75d9131004fd75d9131024fc75d9131006bf54d9131196bc54d913100cfd73d9131196bf43d9131014fe72d9131004fd72d9131014fc72d9131196bf42d913104cff71d913104cfd71d91312567f51d91312567d51d9131256bf41d9131256bd41d913102cfe70d9131004fd70d9131196bc645913146ddf7359131004ff7559131024fe7559131024fc7559131254ff7459131006bf745913146cff7359131006df7359131004ff7259131014fe7259131014fc725913123cff7159131006f7715913123e7f515913123e7d5159131004ff705913102cfc7059131196bf4059131004ff7655131004fe7655131004fd7655131004fc76551310267e65551310067d6555131024ff7654d3100cfe7654d3126cfd7654d3100cfc7654d310067f6554d310267c6554d31005f77154d3100df47154d3104fd43154d31465de7690d3104ede7690d31006df6590d31006dd6590d3123ddd7490d3101ede6490d3101edc6490d31005dd7290d311979f4290d3104fd77190d3100dde7190d3100ddc7190d3104fd47190d3104edf6190d3104fd76190d312575f5190d312575d5190d31257d64190d31005dd7090d31257d71090d3101cff7650d3100cfe7650d3123cfd7650d3100cfc7650d31006bf6450d3101ebc6450d3104f9c4350d31005f77150d3100df47150d3104fd43150d3100ddc7650d3101edc7650d3100cdc7650d31006df6550d31006dd6550d3104ddf7450d3104f9f7450d310079f6450d3101ede6450d3101edc6450d311979c6450d31005df7250d31007d77150d3100dde7150d3100ddc7150d3123fd47150d3104edf6150d3104fd76150d3123f5f5150d3123f5d5150d3123f9f4150d3123fd64150d3123f9d4150d31005df7050d311979f4050d3123fd71050d31014fe76d893119d7e75d89310057d75d893118eee62d8931024fe75d89310067e75d89310247e75d8931004fd75d89310067d75d89310047d75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893100cfd73d893118eee32d893104cfd71d89312067f51d89312067d51d8931206ef21d893102cfe70d8931004fd70d8931206f710d893118eec6258931005fb7058931005f87058931004ff7654931004fe7654931004fc7654931004ff7650931004fe7650931004fc76509310057f755093119d7c7550931006bf645093101ebc64509310079e4350931016ee625093145dde76cc93104ede76cc93104f5e75cc93104f5d75c
  | 27 => 0xc74597311b67f545973100cfe735973100cfc735973104e7e535973104e7c535973104ede4359731004ff7259731014fe7259731014fc72597310067e52597311b67c525973104edf325973126e7f515973126e7d5159731004ff705973102cfc70597311b67f5059731004ff7559331024fe7559331024fc755933104ebf745933100cfe735933100cfc735933104ebe435933104ebc4359331004ff7259331014fe7259331014fc725933123e7f515933123e7d515933123ebf415933123ebd415933104ef6315933104ef53159331004ff705933102cfc70593311aebf4059331004ff765533104cfe7655331004fd765533104cfc76553310267e65553310067d655533104ddf7650f3148edf7650f3104edf6550f31006dd6550f3104f9f7450f3104f9f6450f3101ede6450f3104edc6450f3104f9c6450f31005df7250f3100dde7150f3100ddc7150f3123f5f5150f3123f5d5150f3123f9f4150f3123f9d4150f31005df7050f311af9f4050f31004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b3100cfe7358b3100cfc7358b3104eef7258b31006ef5258b311a6ec5258b311a6ee4258b3104eef3258b3104eec3258b311ee7f5158b311ee7d5158b311eeef2158b31004ff7058b3102cfc7058b3104edf3058b311a6ef2058b31004ff7654b31004fd7654b3104cfc7654b31004ff7650b31004fd7650b3104cfc7650b310057f7550b311b57c7550b31386bf6450b3101ebc6450b3104dde7350b313879e4350b31016ee6250b31006ed6250b3104ddf764cb31486df764cb3104edf654cb31006dd654cb31005df744cb31005dd744cb311f6de644cb3104edc644cb3104fcf724cb3104fcf624cb31016de624cb31016dc624cb3104fcc624cb3147fcf524cb311a7cc524cb311a7ce424cb31007cd424cb3100dde714cb3100ddc714cb311ef5f514cb311ef5d514cb311efcf214cb31005df704cb311a7cf204cb31004ff7558331024fe7558331024fc7558331004ff745833101cfe745833101cfc745833100cfc7358331004ff7258331014fe7258331014fc725833104edf3258331006dd32583310be7f51583310be7d515833104ef6315833104ef5315833104efb705833104efb305833104ef830583310befa1058331024fe76d953119e7e65d953101cfe74d9531004fd74d953101cfc74d953100cfd73d953119e7f53d9531014fe72d9531004fd72d9531014fc72d953104cff71d953104cfd71d95312867f51d95312867d51d9531286f641d953102cfe70d9531004fd70d953119e7c6559531005bf7459531195bc7459531475df7359531284ff75595310067f7559531004ff7459531006bf7459531004bf745953101cfe745953101cfc7459531006bc745953101cbc7459531
  | 28 => 0x941386bc635094101dbf725094101faf7250941007af6250941016be6250941016bc62509411bfac62509411bfae5250941007ad52509411bfae3250941007b7715094100dbe715094100dbc715094121fb4715094101ebf615094101fb7615094121f3f515094121fb6515094121f3d515094121fb6315094121faf2150941005bf70509411bfac2050941004fe76cc941004fd76cc94104cfc76cc9411c57e75cc9410057d75cc94101dbe74cc941005bd74cc941006df63cc94104edc63cc94120f9f43cc94100df671cc941005f571cc941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941006df634c94104edc634c9411f79f434c941016ee624c941007ad424c94101df47654541026f4765454101cf4765454100df7755454100f777554541007776554541026f66554541026f465545411c7746554541007b7745454101df6745454101df474545411d7b4745454100ef7645454100fb764545411d77754545411d77654545411d77554545411d7745454541005f773545411c77753545410077653545410077553545411c77453545411d7b74354541007b54354541006f762545411c77752545414977652545410077552545411c77452545411d7b74254541007b542545411c77750545411c77450545411d7b740545411c77776545410267776545411d77476545410267476545411d77774545410073774545411d77674545411d77574545411d77474545411d734745454100f77645454100e77645454100f3764545410077773545410077673545410077573545410077473545410077763545410077663545410077563545410077463545411d77743545411d73743545411d77643545411d77543545410073543545411d77443545410077772545414977672545410077572545414977472545410077762545410067762545414977662545410077562545414977462545411d77742545411d73742545411d77642545411d77542545410073542545411d77442545410077732545414977632545410077532545414977432545410077770545410077670545410077570545410077470545411d77740545411d73740545411d774405454149777205454149774205454102cfe76d81410077551d8141024fe75d8141004fd75d8141024fc75d814100cfd74d814104cfe73d8141004fd73d81413aebf43d8141006bd43d8141014fe72d8141004fd72d8141014fc72d81413aebf42d8141006bd42d814101cfd71d81412ce7f51d81412ce7d51d81412cef631d81413aefa40d81412cefa10d81411c57e75981410057d7598141007755198141006fb6098141005df7358141005dc735814100775515814100775511814102efa6018141006f9601814104e7f7559731004ff745973101cfe745973101cf
  | 29 => 0x14f76415815114f7621581510077b60581512d67e60581512dd7e76181511d57e74181510057d74181512d57c74181513157e73181510057d73181511cd7e72181510057d72181512d57c72181510257f711815100d7e71181510257d711815100d7c711815131e7f61181514d77761181514cf7641181514cf7621181512d67f60181512d77a60181512d67d60181510077960181512d77a10181514cf791018151024fe76d95411c67e65d954129cfd75d954100cff74d954100cfd74d95414c67f54d95414c67d54d954104cfe73d9541004fd73d9541014fe72d9541004fd72d9541014fc72d95410067e52d95411c67c52d95414c6bf42d954101cff71d954101cfd71d95414be7f51d95414be7d51d954102cfe70d9541004fd70d95411c67f50d9541024ff76595411c67c65595414b5bf74595411e5f771595414bcff75595410067f75595414b4ff7459541006bf74595411d67e54595411d67c5459541004ff735954104cfc73595411c67f5359541004ff7259541014fe7259541014fc72595411d6bf425954129cff7159541006f7715954129e7f515954129e7d5159541004ff705954102cfc705954104cfe76d8d41024fe75d8d41004fd75d8d41024fc75d8d4100cfd74d8d414aede43d8d414aedd43d8d41014fe72d8d41004fd72d8d41014fc72d8d4101cfd71d8d4146e7f51d8d4146e7d51d8d4146edf31d8d4102cfe70d8d41004fd70d8d414aebf40d8d41006df6398d41195f57198d411adf77158d411c57e7518d410057d7518d4104ede6318d41006dd6318d411bdee7218d41005ed7218d41005fa7018d41005f97018d41004fe7694d41004fd7694d4104cfc7694d4101dbe7494d41005bd7494d411bdee7294d41005ed7294d4100df67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410267e6554d410067d6554d4100df67154d4100dbc7650d4104ebc7650d4100cbc7650d4101dbf7350d4101f9f7350d410079f6350d4104ebe6350d4104ebc6350d410079c6350d410079e5350d410079d5350d41005bf7250d41007b77150d4100dbe7150d4100dbc7150d4123fb47150d4101ebf6150d4101fb76150d4123f3f5150d4123fb65150d4123f3d5150d4123fb63150d41005bf7050d41014fe76d89411beee62d8941024fe75d8941004fd75d8941024fc75d894100cfd74d894104cfe73d8941004fd73d89411beee42d89414a6ed42d894101cfd71d894141e7f51d894141ef651d894141e7d51d894141eef21d894102cfe70d8941004fd70d89414a6bf40d89410057f75589411c57c75589411beec625894149df77158941004ff7654941004fe7654941004fc765494100dbc7650941016bc765094100cbc76509410073f75509410073c7550941006bf6550941006bd6550941005bf735
  | 30 => 0x7615895122f76415895122f7621589510057f70589512d57c70589510057f76509510067f76509510047f76509510057e76509510057d76509510057c76509510067c76509510047c76509514257f74509511d73e64509510073d64509510057f73509513157c73509510073e43509511d73c435095141d7f72509511cf6e62509510076d62509511d76f42509511cf3e42509511cf3c42509511cf6c42509511cf6e325095121d7f715095100d7e715095121f76715095100d76715095100775715095100d7c715095121e7f615095122777615095121f3f415095121f76415095121f6f215095121f7621509510057f70509512d57c70509511d73f40509511cf6c20509513157f76cc9510057e76cc9513167e76cc9510047e76cc9510057d76cc9513167d76cc9510047d76cc9513157c76cc9513157f74cc9511d57e74cc9510057d74cc9513157c74cc95145d7e73cc9513175e63cc9510075d63cc9514e75f43cc9513175c43cc9511ed7d72cc9511cf5e32cc9511cf6e32cc9511cf5c32cc9512057f71cc95100d7e71cc9512057d71cc95100d7c71cc9512067f61cc9512177761cc9512077641cc9512075f31cc9512077621cc9512d57e70cc9510057d70cc9510057f764c9510057e764c9510057d764c9510057c764c9510057f744c9511d57e744c9510057d744c9511d57c744c95140d7f734c9510075e634c9510075d634c9514df5f434c9514df5c434c9512057f724c9510076f624c9511cf6c624c9511cf6e424c9510076d424c9513176f324c9511cf5e324c9511cf5c324c9511cf6c324c9511ed7f714c95100d7e714c95100d7c714c9511ee7f614c9511ff77614c9511ef76414c9511ef6f214c9511ef76214c9510057f704c9512d57c704c9511cf6f204c9511d57e74d81510057d74d81511d57c74d81510067e64d81510067c64d81513157e73d81510057d73d81510067f63d81510067d63d81511cd7e72d81510057d72d81511cd7c72d81510067f62d81510067d62d81510257f71d81510257d71d81512de7f61d81513e77761d81512df7641d81512df7621d81512df7a10d81512df7910d81511d57e74981512d73e74981511d53e74981510057d74981512d73d74981510053d74981512d57c74981513157e73981510057d73981511cd7e72981510057d72981512d57c72981512d775719815131e7f61981510677761981511677641981511677621981512d57e70981512d67f60981510077b60981510057f74581511d57e74581511d57c74581510067e64581510067c64581510057f73581513157c73581510067f63581510067d63581510057f72581510076f72581510056f72581511cd7e72581511cd7c72581510076c72581511cd6c72581510067f62581510067d6258151007777158151047776158151
  | 31 => 0x8d5150f7761d8d514777641d8d514775f31d8d514775d31d8d514777621d8d512d57e70d8d510057d70d8d511d57e7498d510057d7498d513157c7498d514fd7e7398d513167f6398d510075f6398d511cd7e7298d513176e7298d511cd6e7298d510057d7298d513176d7298d510056d7298d511cd7c7298d512857d7198d51317757198d51005757198d512867f6198d511b7776198d51287764198d51287762198d512d57e7098d510057d7098d510057f7458d510073f7458d510053f7458d511d57e7458d511d57c7458d510073c7458d511d53c7458d510067f6458d510067d6458d510075f6358d513167e6358d510057f7258d511cd7e7258d511cd7c7258d510067e6258d510067c6258d5126d7f7158d51007777158d51005777158d5119f776158d5126f764158d5126f762158d510057f7058d512d57c7058d514757e7618d511d57e7418d510057d7418d513157c7418d512857e7318d513167f6318d513175e6318d513167d6318d510075d6318d511cd7e7218d510057d7218d511cd7c7218d510257f7118d5100d7e7118d510257d7118d5100d7c7118d514fe7f6118d51507776118d514ff764118d514ff5f3118d514ff5d3118d514ff762118d512d57e7018d510057d7018d513157f7690d510057e7690d510057d7690d513157c7690d5123d7d7490d510073f6490d511d73c6490d514657e7390d513175e6390d510075d6390d513173f4390d511d75f4390d513175c4390d511cd7e7290d510057d7290d511cd7c7290d511d73f4290d512557f7190d5100d7e7190d512557d7190d5100d7c7190d512567f6190d51267776190d51257764190d512575f3190d51257762190d512d57e7090d510057d7090d510057f7650d510057e7650d510057d7650d510057c7650d512557f7450d5146d7f7350d510075e6350d510075d6350d511d75f4350d513173e4350d513173c4350d511d75c4350d510057f7250d511cd7e7250d511cd7c7250d5123d7f7150d5100d7e7150d5100d7c7150d5123e7f6150d5124f776150d5123f3f4150d5123f764150d5123f762150d510057f7050d512d57c7050d511d73f4050d514f57e76d89511d57e74d89510057d74d89511d57c74d89513157e73d89510057d73d89511ce7e62d89511cf6e62d89511ce7c62d89511cf6e32d89510257f71d89514ef7771d895100d7e71d89510257d71d895100d7c71d895143e7f61d89514ef7761d895143f7641d895143f6f21d895143f7621d895143f6d21d89512d57e70d89510057d70d89511cf6c20d89514457f76589510057f74589511d57e74589511d57c74589510057f73589513157c735895143d7f72589510076f62589511ce7e62589511ce7c62589511cf6c62589511cf6e425895122d7f71589510077771589510057771589511877
  | 32 => 0x1ceee62d89511cf6e52d895100cfd75d895143e7d75d895100c7d75d895101cfe74d8951004fd74d895101cfc74d895104cfe73d8951004fd73d89511ce7e52d89511ceee52d89514eeed52d89511ce7c52d89511ceee32d8951024fd71d895143eef21d895102cfe70d8951004fd70d89514ee7f50d89511ceec20d89511ceec6258951525f7715895100d7c76549510167c765495100c7c76549510057f74549511d57e74549511d57c74549510057f73549513157c73549510257f72549510276f72549510076f62549510167e62549510167c62549511cf6c62549511cf6e425495100777715495100d7e715495100d7c715495122f7471549510267f615495102777615495122f76415495122f7621549510057f70549512d57c7054951004ff7650951004fe7650951004fc76509510057f75509510257e75509510057d75509510257c755095101ebe64509511d73e54509510073d5450951016ee62509511cf6e52509510076d525095100df67150951004fe76cc951004fd76cc95104cfc76cc9513157f75cc9510257e75cc9510057d75cc9510257c75cc95104ede63cc9513175e53cc9510075d53cc951004ff764c951004fe764c951004fc764c9510057f754c9510257e754c9510057d754c9510257c754c9510075e534c9510075d534c951006ef624c951016ec624c9511ff6f524c9511cf6c524c95102cfe76d815100cfd75d81512de7d75d815101cfe74d8151004fd74d815101cfc74d81510067e54d81513e67c54d815104cfe73d8151004fd73d81513e67f53d81510067d53d8151014fe72d8151004fd72d8151014fc72d81513e67f52d81510067d52d8151024fd71d81512def621d81513e6fa50d81512d67c50d81512defa10d81511d5be7498151005bd7498151006fb6098151005ef72581511cdec725815102efa6018151006f9601815151d7e76d91511d67e64d91511d73e64d91511d67c64d91513157e73d91510057d73d91511d73c43d91511cd7e72d91510057d72d91511cd7c72d91510257f71d91515177771d915100d7e71d91510257d71d915100d7c71d91514b67f61d91515177761d91514b73f41d91514b77641d91514b73d41d91514b77621d91512d57e70d91510057d70d91511d73f40d91514bd7f76591514b57f74591510073f64591511d67e64591511d67c64591511d73c64591510057f73591513157c73591510057f72591511cd7e72591511cd7c72591511d73f425915129d7f71591510077771591510057771591511c777615915129f76415915129f7621591510057f70591512d57c70591511d57e74d8d510057d74d8d511d57c74d8d510067f64d8d510067d64d8d511cd7e72d8d510057d72d8d511cd7c72d8d510067e62d8d510067c62d8d510257f71d8d510257d71d8d514767f61d
  | 33 => 0xc324cb511df6c324cb511ed7f714cb5100d7e714cb5100d7c714cb511ef6f214cb510057f704cb5131d7c704cb511df6f204cb5101cfe76d91510257e75d915100d7d75d91511d6be64d91511d73e54d915100cfd75d91514b67d75d915100c7d75d91511d67e54d91511d6be54d9151516bd54d91511d67c54d915104cfe73d9151004fd73d91515167f53d91511d6bc43d9151014fe72d9151004fd72d9151014fc72d9151024fd71d91514b6bf41d915102cfe70d9151004fd70d91511d6bf40d91511d6bc645915152df7715915100d7c765515101e7c765515100c7c76551510257f74551510273f74551510073f645515101e7e645515101e7c64551511d73c64551510057f73551513157c73551510057f72551511cd7e72551511cd7c72551511d73f425515100777715515100d7e715515100d7c715515129f7471551510267f615515102777615515129f76415515129f7621551510057f70551512d57c705515104cfe76d8d5100cfd75d8d514767d75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d5150e7f54d8d510067d54d8d5150ede53d8d5150edd53d8d513167c53d8d51014fe72d8d51004fd72d8d51014fc72d8d510067e52d8d5150e7c52d8d51024fd71d8d51476f641d8d51476df31d8d5102cfe70d8d51004fd70d8d5150e7f50d8d51006df6398d511cdee7298d51005ed7298d5119df57198d51005bf7458d511d5bc7458d511b5f77158d5104ede6318d51006dd6318d5100d7e7694d512867e7694d5100c7e7694d511d57e7494d510057d7494d513157c7494d510257e7394d510275e7394d513167f6394d510075f6394d513175c6394d511cd7e7294d513176e7294d511cd6e7294d510057d7294d513176d7294d510056d7294d511cd7c7294d5100d7e7194d51287767194d51317757194d5100d7c7194d510267f6194d51027776194d51287764194d51287762194d512d57e7094d510057d7094d5100d7c7654d5104e7c7654d5100c7c7654d510057f7454d511d57e7454d511d57c7454d510067f6454d510257f7354d510275f7354d510075f6354d5104e7e6354d5104e7c6354d510075c6354d510057f7254d511cd7e7254d511cd7c7254d512767e6254d512767c6254d51007777154d5100d7e7154d5100d7c7154d5126f747154d510267f6154d51027776154d5126f764154d5126f762154d510057f7054d512d57c7054d51004fe7690d51004fd7690d5104cfc7690d513157f7590d510257e7590d510057d7590d510257c7590d51006bf6490d5101ebc6490d5104ede6390d513175e5390d510075d5390d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257e7550d510057d7550d510257c7550d510075e5350d510075d5350d51014fe76d89510257e75d895100d7d75d8951
  | 34 => 0x9321f78c4350932005ef71509321f7af4150932005ef70509322feec60509321f7af405093200cfe76d85321eef661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d8532014fd73d853204cfd72d85321a6ee42d8532006ed42d85321eef631d85321eef621d853202cfe70d8532004fd70d85321a6ef20d85321eef46158532005fb7058532005f87058532024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813204cfd72d813200cfe71d8132004fd71d813200cfc71d8132106ef21d8132106fa20d8132006fb10d8132006f810d8132006fb60981321fd7e75181320057d75181321f5be7418132005bd74181321edf67118132005f5711813202efa6018132006f960181323257f7690f510257e7690f512657d7690f510257c7690f514657e7390f513275e6390f512675d6390f513273f4390f511e75f4390f513275c4390f511dd7e7290f510057d7290f511dd7c7290f511e73f4290f512557f7190f5100d7e7190f512557d7190f5100d7c7190f512575f3190f5131d7e7090f510057d7090f5124d7f7650f510257e7650f5124d7d7650f510257c7650f5146d7f7350f5124f5e6350f5124f5d6350f511e75f4350f513273e4350f513273c4350f511e75c4350f510057f7250f511dd7e7250f511dd7c7250f5123d7f7150f5100d7e7150f5100d7c7150f5123f3f4150f510057f7050f5131d7c7050f511e73f4050f512257f7650b510067f7650b510047f7650b510257e7650b512257d7650b510257c7650b512267c7650b510247c7650b514257f7450b511e73e6450b512273d6450b510057f7350b513257c7350b510073e4350b511e73c4350b5141d7f7250b511df6e6250b512276d6250b511e76f4250b511df3e4250b511df3c4250b511df6c4250b511df6e3250b5121d7f7150b5100d7e7150b5100d7c7150b5121e7d6150b5121f3f4150b5121f6f2150b510057f7050b5131d7c7050b511e73f4050b511df6c2050b513257f76ccb510257e76ccb513267e76ccb510247e76ccb512157d76ccb513267d76ccb510047d76ccb510257c76ccb513257f74ccb511e57e74ccb510057d74ccb513257c74ccb5145d7e73ccb513275e63ccb512175d63ccb5153f5f43ccb513275c43ccb511df5e32ccb511df6e32ccb511df5c32ccb512057f71ccb5100d7e71ccb512057d71ccb5100d7c71ccb512075f31ccb5131d7e70ccb510057d70ccb511fd7f764cb510257e764cb511fd7d764cb510257c764cb510057f744cb511e57e744cb510057d744cb511e57c744cb5140d7f734cb511ff5e634cb511ff5d634cb515375f434cb515375c434cb511ff6f624cb511df6c624cb511df6e424cb510076d424cb513276f324cb511df5e324cb511df5
  | 35 => 0x4ff705953202cfc70595321fe7f505953201cfe76d91321f6be64d913204dde73d9132015dd73d91321f79f43d9132024fe75d9132004fd75d9132024fc75d9132014fd73d913225edd73d9132014dd73d91321f6bf43d91321f6df43d91321f6dc43d913204cff72d913204cfd72d913225ebf42d913225ebd42d913200cfe71d9132004fd71d913200cfc71d913225eef21d913202cfe70d9132004fd70d91320057f75591321fd7c75591321f6bc6459132545df73591321f79c4359132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913225cff7459132006bf7459132544ff7359132006df73591321f6df4359132386be4359132386bc43591321f6dc4359132244ff7259132006ef7259132004ff715913200cfe715913200cfc71591321f6bf4159132246ef2159132004ff705913202cfc70591321f6bf4059132004ff7655132004fe7655132004fd7655132004fc7655132005df735513204ddc7355132005ef7255132015ec725513254dde7694d3204ede7694d32275dd7594d32026de6594d32026dc6594d321f5de7494d3204ddc7494d32006df6494d32006dd6494d32015de7294d3204fce7294d32015ce7294d3204fcd7294d32015dc7294d3204edf6294d3204fcf6294d321ffcf5294d3228fcc5294d3228fce4294d32005dd7194d321ff5f5194d3228fcf2194d32005dd7094d3228fcf2094d32024ff7654d32014fe7654d32274fd7654d32014fc7654d320067f6554d320267c6554d32005ef7254d32015ec7254d322776c5254d32015dc7654d32026dc7654d32014dc7654d3204ddf7554d3204f5f7554d320075f6554d32026de6554d32026dc6554d321ff5c6554d321f5de7454d321f5dc7454d32006df6454d32006dd6454d321ff5f5454d320075d5454d32007cf7254d32015de7254d32015dc7254d32277cc7254d3204edf6254d3204fcf6254d321ffcf5254d322775e5254d322775c5254d32277cc5254d322774c5254d32277ce4254d32005df7154d321ff5f5154d32277cf2154d32005df7054d321ff5f5054d32277cf2054d3201cff7650d32014fe7650d32244fd7650d32014fc7650d32006bf6450d3201ebc6450d32545df7350d3204f9c4350d32005ef7250d32015ec7250d3204dec765093201eec765093204cec76509320076f75509321fdee75509321fdec75509320076c75509321fd6c7550932006ef6550932006ed6550932015ef7450932017af7450932007af645093201eee645093201eec64509321f7ac64509321f7ae5450932007ad5450932007cf735093204dee735093204dec7350932007cc7350932016ef6350932017cf6350932007ce5350932007cd53509321f7cf4350932387ae4350932387ac43509321f7cc435
  | 36 => 0xe71597320067d71597320067c71597320067f41597320067e41597320067c415973204e7f315973204e7e315973204e7d315973204e7c31597322767f21597322767e21597322767d21597322767c21597320067f70597320067e70597320067d70597320067c70597320067f40597320067c405973204e7f305973204e7e305973204e7d305973204e7c30597322767f20597322767e20597322767d20597322767c20597320067f10597320067c1059732004ff7559332024fe7559332024fc755933204ebf7459332014fe7359332014fc735933204edc7359332014dc735933204ede535933220edf435933204ebe435933204ebc435933204edc4359332246bf4259332246bd425933204eee325933204eed3259332004ff715933200cfe715933200cfc715933220ebf415933204edf3159332004ff705933202cfc705933220ebf4059332004ff765533204cfe7655332004fd765533204cfc76553320267e65553320067d6555332005df735533204ddc735533204ddf7654f3255edf7654f3204f5f7554f32026de6554f3204f5e6554f320265e6554f3204f5d6554f3204edc6554f3220dde7454f3220ddc7454f3204edf6454f32006dd6454f322175f5454f320075d5454f32015de7254f32015dc7254f322775e5254f322775c5254f32005df7154f322175f5154f32005df7054f322175f5054f32004ff7558732024fe75587320067e75587320067d7558732024fc7558732004ff745873201cfe745873201cfc7458732014fe7358732014fc735873204eee325873204eed325873204ef77158732206f6415873204ef7315873204ef43158732206f62158732004ff705873202cfc705873204edf3058732206f71058732004ff7558332024fe7558332024fc7558332004ff745833201cfe745833201cfc7458332014fc735833204eee325833204eed3258332004ff715833200cfe715833200cfc715833204edf315833204efb705833204efb305833204ef830583320c6fa2058332024fe76d95321fe7e65d9532015ee72d953204ded72d95321ff6f52d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321fe7c54d9532014fd73d95321fe7f53d953204cff72d953204cfd72d95321feed72d953204ced72d953228e7f52d95321feef52d953228e7d52d953228eec52d953228eee42d953200cfe71d9532004fd71d953200cfc71d95321fe7f51d953202cfe70d9532004fd70d95321fe7c6559532555df73595322776c525953228cff75595320067f7559532004ff745953201cfe745953201cfc7459532554ff7359532006df7359532274ff7259532006ef72595321feef52595322767e52595322767c5259532276ec5259532276ee4259532004ff715953200cfe715953200cfc71595321fe7f5159532
  | 37 => 0x4d42004ff7654d42004fe7654d42004fc7654d420067f6554d420267c6554d42005bf7454d4201dbc7454d420073d5454d42015ee7254d422776e5254d42015be7690d4225ebe7690d42014be7690d42385bf7590d42005bd7590d420073f6590d420073c6590d4201dbe7390d4201f9e7390d42386bf6390d420079f6390d423879c6390d423879e5390d420079d5390d42015be7290d4225fae7290d42387ad7290d42015bc7290d4201ebf6290d4201faf6290d4225fae5290d4225fae3290d42005bd7190d4225faf2190d42005bd7090d4225fac2090d4201dec7654942026ec765494201cec7654942015ef75549420176f75549420076f6554942026ee6554942026ec65549422276c6554942007af745494201dee745494201dec7454942237ac7454942016ef6454942017af6454942237ae5454942227ad5454942005ef7354942007ae4354942237ac4354942005ef71549422276f5154942237af41549422fdec70549422276f5054942237af405494200cfe76d85420067f65d85420067c65d854221ef661d85420067f75d8542024fe75d8542004fd75d8542024fc75d85420067c75d8542014fd74d854204cfe73d8542004fd73d854201cfd72d854242eee32d854221ef641d854221ef621d854202cfe70d8542004fd70d854249ebf40d85420057f75585422257c75585420067f65585420067c655854221ef4615854202cfe76d81420067f65d81420067c65d8142024fe75d8142004fd75d8142024fc75d8142014fd74d814204cfe73d8142004fd73d814201cfd72d81423b6ed72d814233eee32d814200cfe71d8142004fd71d814200cfc71d81423b6bf41d814233eef21d81423b6fa40d814233efa20d81422feec20d81422257e75981420057d75981420067f65981420067c6598142006fb60981422ffe820981420057f75581422257c75581420067f65581420067c6558142127e820581420067f65181420067c651814202efa6018142006f9601814204e7f7559732004ff745973201cfe745973201cfc74597322167f54597320067e54597322167c5459732014fe7359732014fc735973204e7e535973204e7c53597322767f52597322767d5259732004ff715973200cfe715973200cfc71597322167f51597320067e51597322167c5159732004ff705973202cfc70597322167f50597322167c50597320067f74597320067e74597320067d74597320067c745973204e7f735973204e7e735973204e7d735973204e7c735973204e7f435973204e7e435973204e7d435973204e7c43597322767f72597322767e72597322767d72597322767c72597322767f42597322767e42597322767d42597322767c425973204e7f325973204e7e325973204e7d325973204e7c32597320067f71597320047f71597320067
  | 38 => 0x57f6c20d954257e7f74d95425967e74d954257e7d74d954257e7c74d95420067f73d95420067e73d95420067d73d95420067c73d95425967f43d95425967e43d95425967d43d95425967c43d954257e7f72d954257e7e72d954257e7d72d954257e7c72d954257e7f42d954257e7e42d954257e7c42d954257e7f32d954257e7e32d954257e7d32d954257e7c32d95420067f71d95420067e71d95420067d71d95420047d71d95420067c71d95425967f41d95425967e41d95425967d41d95425967c41d95420067e31d95420067c31d954257e7f21d954257e7e21d954257e7d21d954257e7c21d95420067f70d95420067e70d95420067d70d95420067c70d95425967f40d95425967e40d95425967d40d95425967c40d954257e7f20d954257e7e20d954257e7d20d954257e7c20d95420067f10d95420067c10d9542024ff76595422267c6559542585bf745954258def725954257cff75595420067f7559542584ff7459542006bf7459542004ff735954204cfc73595422a4ff7259542006ef7259542004ff715954200cfe715954200cfc71595422267f5159542004ff705954202cfc705954257d7e76195422267e761954257c7e76195425773e741954256f3d741954256e7f64195422275e73195422275d73195425773c431954256f6e72195425776d721954256e7f62195425776f421954256f3e421954256f3c421954256f6c421954256f6e32195422277671195420057d71195422277571195420057571195420067e61195420067c61195425773f411954256f6f21195422277a70195422277970195425773f401954256f6c2019542015bc7655142026bc7655142014bc765514201dbf755514201f3f75551420073f6555142026be6555142026bc65551422273c6555142385bc73551422273f5355142007af7255142015be7255142015bc72551422a7ac725514201ebf625514201faf62551422a7ae52551422a7ae3255142005bf71551422273f51551422a7af2155142005bf70551422a7ac205514204cfe76d8d420067f65d8d420067c65d8d42024fe75d8d42004fd75d8d42024fc75d8d42014fd74d8d42546bd74d8d42566de43d8d42566dd43d8d42386bc43d8d4201cfd72d8d42546df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d42566bf41d8d42546ef21d8d4202cfe70d8d42004fd70d8d42566bf40d8d422257e7598d420057d7598d420067f6598d420067c6598d42006df6398d423879c4398d421f5ed7298d420057f7558d422257c7558d420067f6558d420067c6558d421f79c4358d4220def7258d420067f6518d420067c6518d4204ede6318d42006dd6318d42004fe7694d42004fd7694d4204cfc7694d420067f6594d420267c6594d4201dbc7494d4204ede6394d42015ee7294d42005ed729
  | 39 => 0xe70d8943004fd70d894320ebf40d89430057f755894324d7c7558943246ec625894300cfe76d854323ef661d8543024fe75d8543004fd75d8543024fc75d854304cfd74d854301cfd73d8543014fe72d8543004fd72d8543014fc72d854323ef641d854323ef631d854302cfe70d8543004fd70d85431aebf40d854323ef46158543024fe75d8143004fd75d8143024fc75d814304cfd74d8143014fe72d8143004fd72d8143014fc72d814300cfe71d8143004fd71d814300cfc71d814310ebf41d814310efa40d814324d7e75981430057d7598143006fb609814302efa6018143006f9601814301cfe76d9152236be64d9152014fd75d9152236be54d91525aebd54d915204cfe73d9152004fd73d9152024fd72d9152586bf42d915200cfe71d9152004fd71d915200cfc71d91525ae7f51d915202cfe70d9152004fd70d9152236bf40d9152236bc64591525a5ef725915204cfe76d8d52014fd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d5259ede53d8d5259edd53d8d52024fd72d8d5259eef52d8d525567e52d8d525567c52d8d52556ec52d8d52556ee42d8d52556df32d8d5200cfe71d8d52004fd71d8d5200cfc71d8d5259e7f51d8d5202cfe70d8d52004fd70d8d5259e7f50d8d52006df6398d521fded7298d52215ef7258d5204ede6318d52006dd6318d52004fe7690d52004fd7690d5204cfc7690d52004ff7650d52004fe7650d52004fc7650d5200cfe76d855222ef661d85521de7f75d8552014fd75d855201cfe74d8552004fd74d855201cfc74d855204cfe73d8552004fd73d8552024fd72d85521de7e52d85521de7c52d85521deee42d855222e7f51d855222ef651d855222ef621d855202cfe70d8552004fd70d85525267f50d855222ef4615855202cfe76d8152014fd75d815201cfe74d8152004fd74d815201cfc74d815204cfe73d8152004fd73d8152024fd72d815200cfe71d8152004fd71d815200cfc71d81523ee7f51d81523eefa50d815234efa20d8152235be7498152005bd7498152006fb609815202efa6018152006f96018152024fe76d95422267e65d95422a4fd75d9542014ff74d9542014fd74d95425967f54d95425967d54d954204cfe73d9542004fd73d95422267f53d95422267c53d954201cff72d954201cfd72d954257e7f52d954257e7d52d954200cfe71d9542004fd71d954200cfc71d95422267f51d95420067e51d95422267c51d954202cfe70d9542004fd70d95422267f50d95422267c50d954256d7e76d95420247e76d954257f3f74d954257f3c74d95425973c43d95425976f72d954257f6c72d95425976f42d954257f3e42d954257f3c42d954257f6c42d954257f6e32d95420057d71d95420067e61d95420067c61d95425973f41d954257f6f21d95425973f40d9542
  | 40 => 0x4e435d75e5254e432675c5254e4327f9f4254e43005df7154e432675f5154e432675f5054e43004ff7558a43024fe7558a43024fc7558a4304cfe7358a4304cfc7358a4304ede5358a43006dd5358a431f6df4358a4304edc4358a4304eef7258a43006ef5258a4325eec5258a4325eee4258a4304eef3258a4304eec3258a43004ff7158a4300cfe7158a4300cfc7158a4304edf3158a4325eef2158a43004ff7058a4302cfc7058a4325eef2058a43004ff7558643024fe7558643024fc755864304cfe735864304cfc735864304ebf435864304ebd4358643004ff7258643014fe7258643014fc7258643196bf425864304ef77158643256f6415864304ef7315864304ef43158643004ff705864302cfc7058643256f71058643004ff7558243024fe7558243024fc755824304cfc735824304ebf435824304ebd4358243004ff7258243014fe7258243014fc72582430cebf4258243004ff715824300cfe715824300cfc715824304edf315824304efb70582430cefa405824304efb305824304ef83058243024fe76d954324e7e65d954304cff74d954304cfd74d95432967f54d95432967d54d954301cfd73d954324e7f53d9543014fe72d9543004fd72d9543014fc72d95430067e52d954324e7c52d954300cfe71d9543004fd71d954300cfc71d954324e7f51d954302cfe70d9543004fd70d954324e7f50d954324e7c65595435cddf7359543294ff75595430067f755954327cff7459543006bf74595435ccff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff715954300cfe715954300cfc715954324e7f5159543004ff705954302cfc70595435c5de7694d4304ede7694d4327ddd7594d43026de6594d43026dc6594d4301dde7494d4304ddc7494d4304edf6494d4304f9f6494d4304fce7294d4304fcd7294d43005dd7194d4324f5f5194d432979f4194d432979f4094d43024ff7654d4301cfe7654d4327cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d4304f5c5354d4304f9c4354d4301ddc7654d43026dc7654d4301cdc7654d4304ddf7554d4304f5f7554d430075f6554d43026de6554d43026dc6554d4324f5c6554d430079f7454d4301dde7454d4301ddc7454d4327f9c7454d4304edf6454d4304f9f6454d4327f5f5454d4327f5d5454d435bf5e5254d4324f5c5254d43005df7154d4324f5f5154d4327f9f4154d4324f5f5054d4327f9f4054d43014fe76d8943246ee62d8943024fe75d8943004fd75d8943024fc75d894304cfd74d894301cfd73d8943006de53d8943006dd53d894320edf43d89435b6be43d89435b6bc43d894320edc43d8943246ee42d8943246ee32d894300cfe71d8943004fd71d894300cfc71d894320ebf41d894302cf
  | 41 => 0x4ede4358653004ff7258653014fe7258653014fc725865304edf325865304ef771586532867f5158653286f65158653286f6415865304ef7315865304ef43158653004ff705865302cfc7058653286f71058653004ff745825301cfe745825301cfc745825304cfc735825304e7f535825304e7d5358253004ff7258253014fe7258253014fc725825304edf3258253004ff715825300cfe715825300cfc71582530d67f515825304efb70582530d6fa505825304efb305825304ef8305825301cfe76d915327ebe64d915304cfd75d915327ebe54d9153266bd54d9153024fd73d915327ebf43d9153014fe72d9153004fd72d9153014fc72d915327ebf42d915300cfe71d9153004fd71d915300cfc71d91532667f51d9153006be41d915327ebc41d915302cfe70d9153004fd70d915327ebf40d915327ebc64591535e5df735915304d7c765515301e7c765515304c7c76551530257f74551530273f74551530073f645515301e7e645515301e7c645515327f3c64551530075f735515304d7e735515304d7c73551530075c73551530267f63551530275f63551532757e72551532757c725515327f3f42551530057f71551530057f7055153014fe76d89530257e75d8953276ee62d89532776e52d895304cfd75d895304c7d75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d89532767e52d8953276ee52d89532767c52d8953276ee32d895300cfe71d8953004fd71d895300cfc71d89532167f51d895302cfe70d8953004fd70d89532167f50d8953276ec62589532776c525895300cfe76d855326ef661d85533267f75d855304cfd75d855301cfe74d8553004fd74d855301cfc74d85531b67f54d85530067d54d8553024fd73d85533267e53d85533267c53d8553014fe72d8553004fd72d8553014fc72d85530067e52d85531b67c52d855326e7f51d855326ef651d855326ef631d855302cfe70d8553004fd70d85531b67f50d8553005bf745855327dbc745855326ef4615855304cfd75d815301cfe74d8153004fd74d815301cfc74d8153014fe72d8153004fd72d8153014fc72d815300cfe71d8153004fd71d815300cfc71d81531167f51d8153116fa50d815327dbe7498153005bd7498153006fb609815302efa6018153006f9601815304e7f755964327e7f545964327e7d545964304cfe735964304cfc735964304e7e535964304e7c5359643004ff7259643014fe7259643014fc72596430067e52596432667c525964327ebf4259643004ff715964300cfe715964300cfc71596432667f5159643004ff705964302cfc70596432667f505964304ddf7654e435dedf7654e4304f5f7554e4304f5f6554e43026de6554e4304edc6554e4304f5c6554e4301dde7454e4301ddc7454e4327f5f5454e4327f5d545
  | 42 => 0xe70d8d54004fd70d8d54006df6398d542a5ee7298d54005ed7298d5404ede6318d54006dd6318d54014fe76d89542a6ee62d895401cfd75d8954024fd74d895404cfe73d8954004fd73d89542a6ee52d89542a6ee42d89542a6ee32d895400cfe71d8954004fd71d895400cfc71d89545a67f51d895402cfe70d8954004fd70d89542a6ec625895400cfe76d855429ef661d85541e67f75d855401cfd75d8554024fd74d85541e67e54d85541e67c54d855404cfe73d8554004fd73d855452e7f53d8554014fe72d8554004fd72d8554014fc72d85541e6bf42d855429e7f51d855429ef651d855429ef641d855402cfe70d8554004fd70d855429ef4615855402cfe76d815401cfd75d8154024fd74d81543f6bf54d81543c67e54d81543c67c54d81543c6bc54d815404cfe73d8154004fd73d81543f67f53d8154014fe72d8154004fd72d8154014fc72d81543c6bf42d815400cfe71d8154004fd71d815400cfc71d81543f67f51d81543f6fa50d81543c6fa40d8154006fb609815402efa6018154006f9601815404ebf7459253296be545925324ebd545925304cfe735925304cfc735925304e7f535925304e7d535925304ebe435925304ebc4359253004ff7259253014fe7259253014fc7259253004ff715925300cfe715925300cfc715925324e7f5159253296bf4159253004ff705925302cfc7059253296bf4059253004ff7458a5301cfe7458a5301cfc7458a5304cfe7358a5304cfc7358a5304eef7258a5328eee5258a53006ef4258a5328eee4258a5328eec4258a5304eef3258a5304eec3258a53004ff7158a5300cfe7158a5300cfc7158a531fe7f5158a5328eef2158a53006ee2158a5328eec2158a53004ff7058a5302cfc7058a5328eef2058a5328eec2058a531feee7558a531feed7558a5328eec7558a53006ef7458a53006ee7458a53006ed7458a53006ec7458a531feef5458a531feee5458a531feed5458a531feec5458a5304eef7358a5304eee7358a5304eec7358a5304eef5358a5304eee5358a5304eed5358a5304eec5358a5304eef4358a5304eee4358a5304eed4358a5304eec4358a53006ef7158a53006ee7158a53006ed7158a53006ec7158a531feef5158a531fe6f5158a531feee5158a531feed5158a531feec5158a53006ef4158a53006ee4158a53006ec4158a5304eef3158a5304eee3158a5304eed3158a5304eec3158a53006ef7058a53006ee7058a53006ed7058a53006ec7058a531feef5058a531feee5058a531feed5058a531feec5058a53006ef4058a53006ec4058a5304eef3058a5304eee3058a5304eed3058a5304eec3058a53006ef1058a53006ec1058a530067d7558653004ff745865301cfe745865301cfc745865304cfe735865304cfc735865304e7f535865304e7d5358653
  | 43 => 0x20004000000801a000c000000c001000000100000000000000003800400000070038011002c0020000007002c00b0058003000400700080000004000000400000100010008001005c001000c00600040030048000000c00e0004000001404400280050008000005801d000c012008c0010000000000c0020000001000c00000040010000000008800000100010004011000000000140020000010000001000000010050002000001500080070014007000400000040000000000000001400200060008000000401000000020020000000400700100110020015001000e000c00a00180010008007000000700400000014002004800000040060028012006c0000024006000000000740000000003000800b0018010001c000004400500a0003000801e000800200000030004001000401100000030004000000001900180030014000000c00e0008066000000200000050004002001000600300020008002004c00c000c00200080080028010000c00200080030008000000400500080010004004000000d001c003000c0080000006003400000080000034001000000300100010020004006400000100000000000002c000003c00900100000000001000800100000010020019002800000240030000000001400c001c0000000006001c003004400d002c012001000b00440080000001000c00000d4004000400e00000000000001000c007001801900080030000000002800000000020014004000000100040080004000000c00200080060008004000801a00000030000005000000200680050008000000400000140030000009002000100000030040026000400200200200018000001c001001c00c000800100040000068000000800a000002000000000000000002c00100040000010009000400200000160000001003c025000c0040000001003800a000000a001c0000008001001c0010000000008800900000070000000002c0020008000008401200000030000004001001a000400900000050000001001002100ec0000050001000800200040390064003000000000380080014000000000001080030004000002400100040000000001004c00100280000000007000000000440000000001000c00300240030004005001c00100380040008007003400a00100040008000003c0040048000003401d00c40030010001000c00000180040048012008c0060000000000801a000400300000000000001000000800000080008025002400a00000000014003001800f000002000400000000002002002c000801f002c01000100090018009000c00504cfe76d8d5401cfd75d8d54024fd74d8d545e6de53d8d545cede43d8d54014fe72d8d54004fd72d8d54014fc72d8d5400cfe71d8d54004fd71d8d5400cfc71d8d545e67f51d8d5402cf
  | 44 => 0x40060004001000800600bc001001000300000000004001000000000180010000001001001300040000004000003c00a001c0040008007002c00400ac01b0018001002c0080000000000000000100060000004001400300280000024002005c0010004001000400e00100000004000004c00700000010004001005801c000000000000010000006000000300100010004004001800201000020000000001800d000000200240050000001000000f0010002002000000040180020000000400900000100004008000000200000220048006006000a00000010004002000402e001000100000020018033000800a00180060000000001c0000004001000000000000080038008000400b001c00100300020004001000004b000001c0018011000400c000000900840070008036000000c00040000004002001400c006c0050000000000000700240240000018000000100000180034006000800100040000000002000c00200140000044001003c026000000000f000000280050004006002c000005c00200340020008000000400700200070024000001c00300000050010000001000300280010000027004c00000140000000000000000400040070008003001c001000000000140040024000001c003008000c000c013008c00900380030000008004000100600000000007006800000080070010000002400b0020000009800500080230004015000c0010014001003c008000003900200000004000000c010002c0020020007003c004001c0020004000000c000000800c003c000001000000080060044001006c00400400080098000001c000004c02b001800a000000100580080000001002000f002c006001c00500140000008010001400200040030010000000c0030000002001000400140000000004000000f000c0040000008000c000000000c0008003000000000000040010000002c0010000002001800100000010008001000001a001c00b000c0020010002000c0000000002001800000240090040007000000b0038006001000000100160004001001000700040120008000000000500000010010002001800a000000a000800f0000005000400a0004000003c00b0010004000001f0000003005000200880030028004001000200140010020000001800700100010024006001c000000400b0004002001800c0000000000400300000030004006000000200e4000001c00a003400000380060020008001800000280000010005005c00a000800200000000020001001000500580070004003000000000240000010005000c00f0034008000c003000003200040020008000000402a0038000000000a001c0040018000000401a0000001000000600100040030000006c00c0010000000400200180000018003000000100180010004
  | 45 => 0x13000c00f0054003000400400000100000000004800200000000000001000c0020008005000800100100000004002000c0060000001001c00000000000030000002c00c004c000000c004000000400000040000002000000d000c012000800c0000001000400500000170000001001000000000000000001009c00e00040070000005000400700000000000001000c00000700010008002000000200140020000002000400900000010000000000000d0000014000c002000400000080080048006000c0020000003000800300000060008000000000600000000000016000c013000c000000c017000400300040000030000002400b00100010000000000000000000020020000002000a002c00000040020000009001000000180010004000000800e000000000300060004003000c00800000000028001000001000180020000004007c00000000010074029001c00b001000300040090040004002c000006c00100040020040006002000f00400040000000001400000000050014001000800400240070004010001c0000004008000c0040020003001000b0000007000c00c0020020001400500000080000008001800200440180000001000800000040050000006001000b00040110004017006400c0000009003800000040000000000000000000000030000000000c000001400600280090000000000001b00000000008000000c005001800b00140060004006008800000040000068001002801b002c000000000a000c001000002a000000a00080070054000000400700c80020014001004c0040038002000c000000001f0078000000000500080020004000000c00600100000000001005c0020004009001800200000000000004000000a00940000004006000000000000030014002000c00a00040010040001002400900700040018000001000e000400200500000028021000000100240070010004000800f000400b0008003000c0180024015000000100000030004004001801100240090034013003000500140020010003000800400080010040000000c00e0028000001c00900000320044002000c008000000200000010004000000002b007c004000000b000c002002c008000000e000800a00000030004000006800200180000008001005400400c0010002c000003400d0010013001400500000000000000000c00000000130014000000800200080000004000001c00000100000028002003000a000c000000c012000c0070008006000802e0004009000400400000000000000000800b00000160014000000000f000c00f001000000000010028000000400100140020008013003c0020000003001c00300600030000008000000600000010008000000c00800000060010002003800d000400200000000008007000000e
  | 46 => 0x3006c00100000030008003000c00400000040004001001402b0010006000000100040090038006000400600040010000000000c010003000f001000d001c005000401400000030008002001c00500480010004005000000000000000004003000c000004000f000c00200040200004000003400100040030018000001800c0054000000c00100000070000000000000600140070000000000c002000400100100050044000000000e0008001006c001000000100040220018019000400c000000c0000002000c00a0028009002401300000030098000002c00000000000004000000400a000001d000801a000c02800240020000001001000000000080054002000400000000000014000000000c00040080004004000000100000020000014004c00200200000008000000000300240000028001000000000000020030000000c0050068007008c00000000070004000000800600080000000002001c00d0000000000000500400010004000001400000500010004000003400800000010024000001000c000400100300010000016005400200000000004001000000200040020014040001400600100000000009002000500f400000140080000000000000200080030008022002c002000c007000000100940000018009001400e00dc000000000b00100010014004000c00000140000040000000000e0000001003c0000010029000c01e000c003002400300380040040002000802d0000019003400d0004003000000100f4005002400300180020094001001000600300100018000002c0020004000002000000080030014021003c0010000000000000100040010028000006003a002c000004c00500400020018001001c001003c000004400a0008004000c0010000002004c00e0020001000400400000000014001001c001003002d0008001000800300380010000003002c0030000001000c00c0000003000000300000070004000000c000002c00300140000048007000400600000250008001000800100100000088001000c007000c017001400c00000000004008000c0040060013009400100140000000001000c0030034000000000000040000018001000c000005000000000000070003000000200780020040006000400300480010008009000001a0000026005c045000c004001800900080000004011001400000040010028007000c0000044006000000400000000008028001400000080010014002000c01200440000010000001000000300020060000002c0030020000001800c000c000000400000140150000000000400b000c001000000c000000800c80040004000000000000000040010000002000a0000004002800300100030000000001400000080040000000000000000040010048009000400500040160078007001
  | 47 => 0x917c453829dc000004200022d800022d4899170e7752b3000024c847a87b21fb00b80000000000394264f800014087f8792352aaf68000da926ea0000000000278a79b35340c5b68004d00009e200005132dd442680ba65431bac4e212c6d536c8a5b122e0f8849c87d92465cba0f05e91d6074690b4b998cbe5aa000000000008a7adf0000000000000009c500001bf8000b45af9200000002249fc8a5b80005f82aec000168e4c72372a8eb1b497e80004ec80002c100002fd800089c102e2ed1270c2634e6d0e226007c834c86000000000000b30348c2998000a1695f000017465ac294edaaa9a629681c8214393c8f719408f980008760000281800022231ca6fe22280000000084271a98394b858207800001530ac91ff439722202a1276a1af1ec685098d0000000000020240000000aba227254b8000a90800000011780000000000343eaf090ca000000000000000d28000e0000002faa1fe000303c454a4220002d44a3b87cec670e044ef9824d95a7123d030586d5a1ec4a980003343886e53a566000000068c2dbc6462d965912fa41adb728c532d2e8c1b42c4f7102822f8c6052fabd2d59af40483a8267158ec8cf00738928231a9781e8e53b344066800000001bca00020b4cd01f5cbff0ba461498a2b09211667a07ea791819c35f359a9f5b82c1b892d864410e692a0f700012b8cd6132f67d79d428b89df0bae9df8d518af0cf52190254a18ea2e02727820c0ed02b62ac5cb8fa10f8aca000084222c16a4000074600030feb67af223d515ae0001aec6eaa686259924a0001b1200012e0b949d6616f31601c28b542f691b00000310502366ecc69c0800013f21d89f1a57b30f800000000e7800065b2d1400005442b2000068580003e38f206e5800000032f800008f00001f54aa7000082c0000b343560000203838ea17600035f0a79263a45c0000000133a00000002d88000d8229003d285c00da955400003a29e49bf0922a4a4d97b4e4b6013927d5a1a818f9a0a613229830b05300003034d21a75000000007a299de9e403a44b532c800a0001000800f006c00d003000000000240000000003800000240070024001001401100240060000000008401500040050000000001400200040000008014001c0010008006007000000280090048003008000100080010000001000c0010000000000800b00200000004000000c001000000b0008000004c008002001700600080010004000000f00180080004000001400800b00050000001000000000300000018000001000000180120008014000400000180050020000002000600c8000000000000040090030000000000b00040040034002002400c00040010000009000400b002c0050000008002c00e0000003000000300000020000002000000000040050000002000000
  | 48 => 0x82cb011c64a527e63df890c818b7aac0a814235dafd66b3ab7088794dc000304cd9100005b708f2000133cb0e220809a26d00381c1a6adb10c148000017188d2000092223ea160733372e5ba800005a9484cfa8000b31000002a05560001e44000000051c00001b18000129b4e8c588000d560eba096207c0001fee11da7c200000001c9a5f00da3368dba885e5848f023a7168099ab1ce46217583850000000120270c0000000000077880009de800000038d27c50000c910532000138c139b1d239a28faab713f4051a73237b1fd6d6e192290105d43caa8b2b2480000001674000338800005a200004ae000000000009a400013200000000c20000000022f80000fec8ad9052000325c786842acfd80009872f1800015fa787b806c629faa23728ac79d8000000000000038dc708acd64ac80001d70000104aa1e0002e8647e8000271240aa9704fc000375600000005e9800000000000000000000164c77a800000015be81a00000001522de00000844a2ac86a907807e2f9c60883c89b213884c2b6ac4338eecac20000aa593fa3019b8655c8a7c8ee2fe867eb1a61e3b7b49e9aed49e7815447d320c9219c4a0001bfc1b60bbc00012a2765b790959283c00004bcc96100258a0328bc532ce62390e09ff2dfa2bd153eb60838a927280685215e20001d1c000000053012de8489f42c7e8e2e94aa274058aee05d5a3502021c6ce088000128800000016240002e3aa8d987600008ba0000000314000022089c2cec22ec41b326e00034f43311fea00026f2cfca488893181e66d000000007bc3d9800025ca2f0d2286d690f97d890e000083e899aa152100aa11c4cb1a069ea9128624f780005660000bed0d1a000367e00014502c52976000248c0002b8294e8000411a786a451d9e7e58f987640b68b630000bbe2a884800000000125e000253200001701621ca2dee00008ab9a1445419d0ab780c600000000000c82292107c18529a410980008352e36ba002b27e0141200025ac000000000026b6000085498f000014980008fe88e4b720000dba00000000000000000000000000002aeea2a1528000190271906a8be100002cdb0ba00036320000c660000000a5720280000f3a4d734f2a94169a211000028639560000000c0b00002acb1d60000000b479d0c0002d901f4b26868e800032ba828a24afde00008ea08c3062a8180005e01764d900000310800043780000000100d0225880002ee8000000065b9364000118a508a370af21ef8822b4c86b183de7488ec28d1b72c28c1488bd8961a19338c092980945950f12000220621e86b2000080ecdc9b2200000000000000000000011a800000000000001882b4100009098a4ed5c93325698000bef80000001b0a59c1df400036009ce0fb200036f600010206b619c8d819d54724800009
  | 49 => 0xa00004a62bb062da746e2fb778bbc31645aeaf325cf2bb28d21f1060584e206329988152358977370863f9ea87a09ae88843016687ab78cfe363a6620f2e73700d242bb6d64bdaf36338abd04a11b2e978a6b83cc1ae01f0241013389380001fcc0ef858200016b8e48141000004aa00000000000e1e0000b1cd608000e23b4660001750d2c86b8000000024f31d85810dca3f89c1c5f7b57e6188d6ecce32bc4b687540000b4c0002f060000000000105a00000005a0a1dc0000000b7780009a330c20000000c239cee7a9862e5d4b6b82cb80c000009787c728f06e0a33a3a50910a2397e64f9a304309aae4d1d1e5a2cc9d2e98487220c192321a503e8000077e1ab165c000340e1fea6ac0002406d429b28a410af693400000000000000000072200009aa38ac9460c7e80f35e810d30887d130aeb7a87ac44b0418659233026623b29249a725c4a84200000008612c0826b8000ad5800000005a8000000075c9c7c00012aea6d199ccb5b216ce1336e4ba00001059f46bbbaa2a7341aa8ab28d80acd8000000225a000000006bb12800038ca46d800000036ec326b528c6500002c40000265b54e000139e00013d4914b452ce4b8b6000011ea0b2c74994a2927c2818ad24a1b4000000072183c2ceb800021b8490011a32e1cd8a0e62c000e00012c0583b09271c8886760031892b00003e98000016912200004423d4000033a17dc30d0000afb176000000008032a380000000404b4dadd880003189274cab2ad88d28000d3e915c841366ae528000735b65c2fc0514000192e6d4141c00000000000000000000000002a06be03d600000001ca80007ab8000a820000a6a000023e00009428c780003686cf700003dd80007a6875e60336a218da134d7001e856d9b04a46a650c20b14a816ad5438a1c3c50c2074aad9c68000000083db71e0000000a85000000021c46bb86d2d500b388f22c365b3a88439f0748bd5879245629fa2651916d4fafa2000000021f2b2c7810000b3b963c95db16c000197eb789e8c76a18a6dfc9afebc217f4ab324e8dd92ad225a8dbebc59edc21b3446db68fb620eb56e666a1cecc70db881435a47f52a6637006489b900000001b08d52305ad7a939aaf28fceaaeaf0c0001e4e00028c0baa2a260001dd69631e509d52b547049d7c1b80632c4584e466bb552d98a642c87029a0c8987e0ed8132405b5e20c21a7890d8000bd900000003892ab09cde0002092558007053f25503830000a71b28ea9b000049f886800014ca359b4fe93013260001c3218725cc01d97d6204a3560000000b5d000000000000000000a5c98f2288000013a0014368b6762468000b0a929cc1a0d0cc6819087a48b8a00010d8d010d86c6115a89e02dd615c8ae069a013e3e10d96e1800ce0003024e240be600036a8cb90d605ca91
  | 50 => 0xa085db02883b78000617a73067e1b3a72798380d10524b373174000163879e34cea480f9ee44aeb60001782dda9172b3cae40046b4220000000000000028900007dd00006180000d1c2dc6000000000000000001b80bb4ab2000015c600035982ea0000c560000b3f000081bb7924d6107200031c600023d800000000000000000000000016ee91d2b921c7279400028dc4d538709391ca60002044000275200004f6000078609e973630ea49a6ed2394968b856856884eadb00008e405ce9be1e068a5ab960f2800088e178a0d709b693302f601b210a5f6aa0203daaf80000000c668000b400000a3200001da33285ceb2740000000b1f0000cf682eade91c8200015d800008d400024c6d1300000e3b09035205660002f5a02016ec48b270a0000000a622ae672d33fa4d3ac1045a00000ac02620001e0c00009b8ccaa8820001c6000000000003096c89a27aa4b2e6431bafec5d7a626000245824600008b280000000cfe000197a2c0889e6861a063b68b26000205e43e38760000d0026e84249351f6248e12e2dcd811245eb6f2bfd8000d8e03e0ada80004068000b869e4a0002eae0002d321bb800000010c4000112ecc602b4a1723acaaa9808744161cc4b8000000031ea03800028f00008951a2600007a8531ae9284400000002ec4649984427a364820b262436405ea00017fa00000004b28000291acb2d0686026390000d280b880000000588872e893a7c800017540000e30c88af1e9fd8000d7c8000000259c0d98000d26957800023e400000000000000659adca99321a61cf0dac94bb4541188000de38bee20f8000a9300d40001d78d46056c85a00000ee000050f8214000094e82309440002f52e4433cc0000eb80000000ccb80002269cba0003494dc2b35e0002f38b46850ca1f0000ce502400002c1e90816d8000002a2e000006d7351ad0a9ee2e1b8f94b24126cc6a14cc47380000000456e2200003338f6e3cf0000c27348e9d7abe080780008689086165021e3f508ce723061063e8000000000023835fa6fe80ee9e3a90c014000017c995a273866ce4e0adc44d164607080000000d62785b126000000075a972c0003722806ae30000023c0d42b0485635f46c811387ac2fc27ca9c9a68db34462e8d7e5b797c62189d689af0698379addc06c80003239480a9a0000000189aa4d80000001e6e00025907e2865e000000000000123070000c1c80005883670acc94529b00000698920800005ba000315040283f044a244e00025c400000001c5a500cac1e70a310908a3ab0c6c8900008e2153688f288a6e694b2000010c57bae0ac4ea0ec4ad2ea63e801cebbab7ae8ad08a0c0403dc313159238d353a263ac2273a35200120e20a73866a1c18e12cb80bf28fa367c8deb1bc3d79cb899b023447314bc69d25c2207b10e2
  | 51 => 0xd7485f8a740d829d2000000039662570000d159490a4e93aeaa00e765e6b5ca00020aa000339cbc71f000818bd01981d9466a048e0002e060000000d779952b501eacba3000006899c4000140e6c0000000014b45c7800000030c4710800000034102b403400001dd2d1e00000000000e1a2daa000000036c9300518aa5a0001dfec9d8000af380003be80007ed8000000319e0638684b203134a6522cc52eac0c6882d24ace067c150317a0000000cd2a630000184aaef00008269cec89b9c268a3800072da968242b0ca07181d6d06337a00018541458d5a0ee800000000001f833001b4259a000050e9968fe619a1c1ed84827000000bc00000004579dd8000154e1d80b9a0dea42813100000000674a4b895e57000c8665a772122369eb8236a0bc383c4000000000034d4963aa0a4492d9a2bca74ae0780001ed80007ec01ac2df1b447fe8b3e9dc1d88e49a4943df12ac45298a05a2ac1a00000cc000283844594a8cc10e0ecf4a25288395960000cc8a600db438a9dbaaedb65a32ea6721442feedbf00004c18000c68800000006c26260000d328000486385e6dbb0d8475a0e2d6f92e6c64913e2c38d161f9b8ba6f48ae448da280bed9e960008ec6bd52c128861ef2b662424c0730025fe09f2dd71b8823180003a7b15e51000007d6800076f84a04321254e11378867d33e00ed1fec27aa5f67e9ade462e121e63633b68cda66641e8c5a394966ea641258916b030dc32a943610552000092c62a91f8b3c17ca8c7aa620cdb88a0001b4a5878fbe6cf8bfadda0d50d5d0f28bd3958469b0baeb381a1cac885d2c730bde31284d49ca1434d6eabfe1e798b47688d9edd0917449f20f21278710b362c48af9b748e17131e3d58136000000070e94ce157218a8988c74d430df20000be26678000000136255a19fe0000000ba50000285000045f1f080002e323d61032e1f937a00018e8417b862730000000024405dd000015ab4fc55c0b305e896f6ca1a6fa0002606000000079e80009e933266b78000bc80b50b74800046f0000353ac2c00025a8289a8ba7c60a385f028cca6bb2307cf32363d71fb8396800000015d2891b1362399afa93b8354b670d2439985a64c912240001a0ea60a2a0337a61090cad6609088fc762b37c000116200000000000000d9c8c58000100e7cf8000cbeb6b613a9494261ae12c3793960001af61f11fe6d8f158aaa8000078d99cca359bb27adb436a3189e01c8000001c8dc444990a459e31441be00000000000d739ed600021d40000000000272c3e219f200012567ed318800000000000000af89b3c0000630cceaa6000017c2795137cc19263828f9d5e5112ee6a2d80005060dee1f419e033e2538402243aaeeb71290001cc00036cc9628d6caac232498b000040faf80b591dec0000cd45672a9aa7e0
  | 52 => 0x35e40000000413b61600003900b080002f5800000018864e387509c79be812b10480001f349f5226c000054a0f30e2c00012d000002da000168c62a00006e400002f71380000000000007cc00029f22718e900000dd400000005569f726bf2c8a00013a63e693425829ab43d081e600011a6740365000e0000773800033b00a400006aea4d3834c8837e62a6938469731768ea80000002b104d78f805068000a849696a5800002d0000028bb774c6b2dce00000007980000459000000000006f6a3fc000000000000004a0008edfa1c2e6c193cc5819bd8295b29ca6383a6d7415cc3b722f45b437a215e80002ffb0aa000349034ab554c810e1c16e051a57e28da0c6a986d69a54ab2b2e22887239ea1225344f80b84c95891ea70802810ea2d05c180000001b8c18900007f2b3f486588c0052386c000000095380000001ca4000183412c0000598189c00000000001ea4000000000004ba000286ebdf9d62dd6b1b09e104d66e51d74957800001f0b3c0002460980800000001de56e0c1264e965e000387c0b980903c20ac21b6b24c5bf0d5e5a4910e599a2b80000000b4b190a4c88e8043a94a2b5e0000000000011a26fe000000004e241a4880000c1d8252cb7800073c9e2ee0c0a4088d2c06000050676e0feebb3868200002041beb82a741b46c44a800068b9a2252b9e3235c1ab20002e4c3f71f640000000166064278e239a7412fda7e69460cbf2312410afe60000ff0bf91d586a73324465062c1ec251273fa946852aface022d5e44f1fc4a94b7c01ce80003498000a75255abf627e40d808d00b6000015e2b3487c80000000370444220a24eafd0b4a2d5851d992400021e88b80000d0300000000a22823a1720caa516703389ec77a17a03d35c2000000000005ec86780000000000000000029c00000000a7e470931693ca5420001f68655b1e249e1cd84c20000a190000dbe21501641b840000d9a000000000002ee000343c0001c80000000081e02940d491da60121b000333aa00000002a7800037480009858000b862b0e88900006f1138600000000000000000000084c128862b8000e1200449cb9ffecaf97e448d0000d5f2d8ead098b2000000000039545599312bca800069680002a3988000010102970a6a0adb4c2976a24090c0e0031012a8e3a90d6000391c1fb80000000158993800019c949a32839588fd8000000000000038f8ab1800046ba06c0000000000065c82196a2bc135d80000b822cb148a4b3000060c2cec90a948e00000006a28000551000067c2ac439d32cc000071200036c28ae80003b5000000000006d0084c6a035140a022b00a915b4c293710dc680f20808b221bd01f01a9a2367bf990095d28f217705e46af152ab03a8944991f2e81c245cd44167c34827609a01a0c185a1d0b05130c00021fc
  | 53 => 0x2b4ed6415a4434292adad03b000000000000000000000066e9a460000000255000000030321d30b5c857b6960002dae00000000000000ae18f16016000000010c227685500000000160310aa3a000000000000002a58000084038c80000000000000153248500000002afa368026c55200005ec375ec900e26dd9a86a8832f3489f2026aaf10da39e800094883c67dc0cc06b9956ad449de085882f8835b78a99a145a00000000000992b71017800013e48c5a1a000008584cd00007662b52ab59a340001a904a80dbc74d0000cd39cc8b1ca138c158ea01a4b0400e214ee36635b010093b668a8d9c94b28a64ad9a7c3c91a4aabaa37c4d699ee22d8df431f2d2271e9812248076499da57219389d0259163495e806030fa40ec1119a479323aeb1d88460feb73a9c5b53080b290ac120afcd298c249de0000e2800003f800001fa25f8c82a3de000000082420ea0002be497d25de00035965e6357800019fcc05000018980000000000a47b1b2dcd0000cbb06a2ab0322eb8b800023216a6000000014b2bf60002ad4c3a000000000000002e341c300002dbaf0a0002288000305c8cf03d8000000000005d60000000c98317eb7a0000713a76214b800093897fccdd2392ae2b31200020f4496b4ec6b5800045980001d08b0c7b297b2e31951e8849ff01211262df7800080131f8336075ade31a5000028360002e244fdb8c2ba235700440000d340400ca9b0ea042879aa45a3f40000dc8000000000000000000fa88d70fb000022ce000368e75480000003918c5a2fca00000000000cb80001b10000000000026dc04baae2000259400000009b60870000000000000001260296c0d8000e338000796329000026220001f063b9277eab393fc2eb01d80000b2a000000000000de7c7a90e5920000ad235dc0002ee2b9fae6000002de37085d825b11921a820349ea9038000000053a00000000ad824daf00b7b1c5a0002360e1d00003860c561918000717b5ee0000000230aeec96008648460866161aa3e1fc32ea0000000794aecaa11a0825ea000000000000002fea00032664e62e56b850000291266298d099c9368000483000010b9d382b1b484000238c000247c17a00000001730000000019580000003218e0a2e2a3e2acd4bae15aa0000772178b5a89a2277c08bb066d998db000011ac00000e64f4a2e8a488a58c4b00007be9090cd199d637f16fe3909acc8c421a4711389cc7d00000000000dbc12a400000000000bbe00010a000021b25cd000077935d618e256cd8280008d0000000000000001f3000027d07d31a32742354c5a18eae701000000037549719ec40001eeeb8f0000000003c152057496810f20000c32cf41a827680d92d19144e07a9d4abe981d0a540000d1fb614d2214640002bbe00011e892d800047b0000000
  | 54 => 0xf00b6900ecc4200008d4800027588a298300000001bc20000a861e980004f58924b56a84400022b227eb2e800026e0ccf03f41a72ce271519700b90000453000000000004c6000014db074b53240ca36179e3788000159002693b00006a1acc800034de5ccaa720000000ad68000000175c6fb37d235c926e4db0000ddcb0e0689280a9a6a0c032898be47818f0b80a1e255093a400037944193682bffa9d290625460af3812000392e97900000000000699920a00000005b19b9c00000000000000000395a000000000019e29991ef6c598000000000000008780c0300412f800000033524d49564c80a320a8c089c47f8a3a00031aa0002a4e0000000000210c91e8000958377e00003824c52876e378d0200015b20b10e408072c8ce3f80401f28ccabbcb3ec0002c9c91c00003b880009a429ac6afb01a24727f2c25351c1532c16a3880000000000000037470d0398000189260a0b649ac9ec2a9e03e4ceb20a8df700aee0f29beb941dda871824800000001ee0da639580000001c507428000aa4b544b4a8e6e13e88ee0000000000373c892a4e691d99cea5c27e00000000000000076c919ad93942c0002a86ca019d40000000382800000015de3f314d20000f3400000000000000ba61edabf500000932d4634ca094000061a5d10aa8e540326444a47eb5213ba5109e1000028f45742834cf88ac489e00008a31cdacd69f4856180005ed1dca000000000000000002978ce18a04ccd14ac1292dd84e281c47d2956eb1b287a04f1244801991e13c145cc41aefc1c52f4221fa3d60fb0000653af024ff82d04de11dca701076b0622fa3c6000000006b4dfaa22c00038187f0000000000009b131eeb8a28e68e192ee0002b183bf2e1e0000000ddd82ba589865087b853ad45994a49da4dc4900dde0000dfa0002718000000061f000099f29b0855293c000355006fb8f65d336bc8039574b3aa3eabbeb4143429c74b3a1c0edec89d469201e403c2468ad29d70b33032cd6d3786da69c02857121c7a1143879ab85aa391336e570f9600000c20bd2b6087789aa0001d820002b74000000070a35aeabd9290521a3b632618d2669911ac81b5ecbe82c7e7af2822268a0d80828032ca32f301c3a81ab208ad6156b0a640d000072ba384206020c53218d69bd37d0117092acee31da5771a70864b070d3c2dac6c7afc80000f52b100000ac300005c20b8c29493b80000d4c2dd10aa17b8a600c81614ab419be7a2347209f8796000391a0002a4000016be25b8ea4c28951a00028fc1370000cb697f020f2c4cae00000738800071e0a903c3b1ea13ca26600000002de19589fbb7a88bc81720000000000244400000000000000af729f40003342c8389f40000000b4d00000000fdac551f0e00019aada4a2de7e80000dd3a8161581954622800
  | 55 => 0xa400033ce83a158c845000000000002be95249e638a2d679c58c920000000047e0000aac019101458e8d880001e3031a9ece3fa9d12000100ca7309cacc41b24e488000c3c8000000364200001e295f0eb2baf8e9200034be284a2be00033fcc60a2c0b5b328adb12684a7b3110241b52e7f38eac7f7800000016d600038260000dd83058b94e11833c33da0dc039309e643a6c694c38d8153b46ece41058955800074f02c0d07321ed180000000000049ab6d89fc1b382d481b0799295a921111e6bca51ca8a17844670000369000000019f68bd98c814d1d7eb2997ae69910bad122c4e3e30960c79b366a67a5289cd21e6d4e3602be4003ee0bad680890d1e34e26be5ad1414b00a7da321b34c2adb502c022e0023d9aa0d5b107052821ea000142e282a4ae2ed86beae88000144951409d11020000ee0dca9dc000032620000b6a000048000000007dd8000843b6242dc991c4ac1e246e91748dcf98ec06d00005858570098071e3a1902c855800000021c26ec0396c351558d1680007b525d000007840000000000000014280000000000b951fd2889990672294e4c5709d24dcb69c4569118c10b3a8610a13285f1f9e0002ba62b78000b811ff2a280000008313ecd8037659b00be859894802b292674b0666000044c00020fedac1f22bfc32b87b3000060b9cf6cb9977004500000000e601229bf20279d8c0002e9acc5b25e06e37e0da62f9ec720ed820435f8650a06008fb59459fb362b1830e6062394400000008f01840aa7b09a0ff8546d0a246cd2000009d9219c1e900003cdaa0c9728a0c0000b90b8980b6a77b442b741cd41e60f74897988c4d595f6b83216ca04950e0000000dd3000003a98908ed000000016c0046000000007e40000c64ded8486df0aa6ed33230c000271c89580000002d0ce41800000022a4ad1a5f2e0380002993702593abf2000289e33c091237900003e9000009402128518000c8a8946baf0000076a46400034b0e0400000000000401a17e5e1950c94788ded48b8e051e11e4d2b9f38324b8360000000cad24d841a800000033a000025d27d39d4800000000001f92b61abac5030fc2c8500000001af000000000002ab2aea0a0045b24d65e230f66a1000033f1f3a75b82d2d601db696c8124756834602195e07d4942ab379a94313b568141101c6431fe00a70000000021807db79834b1874a0b89fc95891eebb0374060f8496e0281a6000000040ea36e2fd1a96df129d68ec238272a80003f48eb43fa203e86b9ffc22412dc9b588e266e300c28c8b4485e289800028023390f48b9d80000002b120002b5c0000000b5e80001c006060002fce6452c3e6d8819a67700005eb07020000106d7d977868e1ca8ccf89d8b2d91467c4921a6c580009a7aa7639a800070620480000000b0b929ae29000000
  | 56 => 0x46ea91a7767fe04ca380a656218209e6d08414e40a1fa5fb9e7e1709044961b6644c3acc6a1326481080000df88ff41dd80006b016f871713c000011b220e36dc00017ba425000056b0000e230000cd5355a000000015d80008048000c5c000000008a84701f900003186c7b00000000000000066248180009bc136050585c800036901ee800065d307e0001fdc00020b800001609e700000001f50000186e3f1065a000032e63aa61800032dc4cfa50478f9068ac700000000f1c2f1253cabc0000d41243c000044e5990d781550000a8612f25a72b9edb29a8896d12d6a002396a9589cc57212f410a0eb063508743740df8208b06cbde08c409aa3c6cef04f4d2f2b5826b014053680a2aa618327a739301149ff677b91f6a06008caa2a85e7cda8687a037e41f8862244006f2d13a1d25c00fd800030da25c11a4797ac3a9f01d4ee5aab3a5be95042c784a8d6b0bc29da1c8470d8472a381cc6b163302aa3a85839c32341e400008d88000ad1171a3de80000002a48479800000000000003330000344a00000000003932285800060b2ed60701d566eda86c089b90044d997cbdca9e0088a0ba28a1e8643d947ed57000000006e68f8b0f087584d8a4700000002f68ad9ac6400000000000e7251b9e02509000064125541f18000b68ad762d38be0ce68ef4987b93a50824c238fa60a000000000010a661e8000000000000000003a99d145f480000000000c3b000000000e80000000da2195e000177261692827b81694907b726abd1bf6600868a63f00006912ede7b01ebe1c60c76cee981a500005ea13962e3cfa4626d800007258000613ab7600015e6000162a000045400002cc25f0000bd11ef4000000026c8000bc6a018cb1804c172867eb46333200030544e704d227b98c0000000016d233eb730000b7980000000fa248a00008fc800000000001ac000000029f05f217aa0000000000157e0002d62344b8c42000000afe1266096a9f6e45821cc3d06dc06d9b2a00021ba0003378acf0000790a7b600036d0df500000002e6c4060000e3d1456542229ab5ca9e251d22047619d64b9e12f039f8c2e8193026db5238e8a9b2082aea9e67802e962148f10c2a383a9381f026ef1f8838434c042f85de6f534ba92d0e50be50000000000000000000002bea0c1000000021640003694d682f5e18295387a817180003738878000000000000000e78da28000cbc30846ac0dcec9b000043fa7d8bd31e9824d385034c1b2600022a86da11087f90b92b8805fc00018103d6b8728471b76b1896bcde132a4a9f00007c10c6c2f30000000087200013ec6cc0000e25000047f0000054000000000008f0af9a00020ee000000000000002f6226800000005ab0000392b12086f8d42000085664c2958ced0f683ad80000000000147948c00b18
  | 57 => 0x2e98d8000dcc80000002514e2a2d7ca89153400037da8e6147a4aeaa1ac1e9ba860f1610b9f0b00d780000e322706be3000058089749ab830e0000000afe80000e820b649426fc0000a420000a9c0000000000083600028d0c39387834b8000000145e00000000001ad2000000094db880000218c14a9c520370634d9e21da00030c052c01220002e2c95a0000c04af5c00010622f18a4a0088000bbfa42c3e0a964e2c8494bbd9552040b4129611b5a2e1ac7adbd24f842b090eae11a3cb4207d4000000039b058400037f614f2b7a38e335c000000063993c4000000051a2fe2b62a7405360abc7261630000098896e0aec46aacfe8c037fa00000000000de00d6a170695053e866349e2613468af7a214c94000000017d0000038400002c838d9eba99eb634892117eb440b201bd8000e1ea95e56383da8ef80000000982a8826ec97b8c529fa336c176a27ee3a289abf18686ad42a047882cc249a18843a3390457aa6922770000633ae5a7ae0fb48bf30b40002f768d9140adb3adba00010dc1678000d8ba0581a3b00e2942c54ab2088a00021f80002ec2365288c6449d50b4e9d8edc3aa1c2009672a9a80000001472d171b4c7aa939400015620003050a6e807e52737fc0000000e2588d64fa812a408833eb3e2a346c600007d600004b3afaa13b80000001dac57a371600000000000000183201400011f073c000000000000002b7c0000000000000045d80003628a2a000000000012ea3aa927236a0fc0de5ae62db894f68f119ac0b28000ac006706e980002b98f8699180000001b5806600005cfb0d600004c2cb42b1a00017e2c3310261bf335031c85ac41d271004a21865291c0a0000d2237339089869cf81de0000dacaab83b3b82063826605682608bdc23ce57692c80002e9eb5b8a983271b92b498000dab80000328832b6205aa000124e000064400031528aa89bcb979e5c8db000023b29480002e443af8a68b0d0000000177c8469f8e0a2b556af520be6b090d400000006d1ada68378d18ac197943d8282000000004c680000000000000000000013acb42800031ea34e71b808a00028806701d84000287ee5a27ceb78294a0000342000000026d0c38b0832520002cf6df288146e834c49a50de80001b2c93f000000012fc5ef2e5c6718000ba70a78000110c509970c1070c10c2e0608c0e18daacba6e2254275a0002ccaad79e72b4c27fe335a874732b2540c500003bca408a7ab07c000357ab1100002f4a144a4c3006dfb28667dab1c4c568e9862f3380c11b6decbc8ca4000213e3c9971c9b48942478a9d8cc8b8e6b6a2962d3194ea9971ddca1c2c9a20d15a202993822ea963e01880001f72b8e1baa85600016b2705239c676b3de92aa052000009811d2e7a6581a9ab4702fc26013bc000000014a24140002d420
  | 58 => 0x66286a40000a62511853881f89589700000bdf1e94d1a9154bd9aba0bb91f268e9141e00009f83029bc87e30c220001fbc8808efe065947c8e82276000000000028880a78f0ca2d30bc9a9946ca6115889c913f0d16248023a2f6a09f39487ca2bd80002bc4d8698c2e050f3800000008c08aa2000000000030ee00000004bfaa4a27f9204ca5a3d29b30000ce7b3ee0000000000000066f03e6872167aa76a4be3e40c8ad258000cb299687e88000e45121262b000029d8000c1baeb40000b60d961aa6441172031a003a3411662b4fa23eaafb1783b037f82d0b5645c8842c975b078ba404c038697a00b1b2d2caa0000aed0000da33782000308ae5180000002b622db2a10e50000000000003370904e21339856ea4b2db49b1c29301fa37d800064b350675025261f6800008ca0e6382094a000000000000000001ea20a9aa3c55433c6a1282546f91740e35ab9a0dfa490cbb888e1380104661b50072c093053c183a6949060caa9c4679f38409a0a804bd294820822200aa936047a40a823b9b56a0388618006a174d88b3c4943139000026e60a38d7a5650000bfd28ae615929611213d0000316a05291d2b9180000cea102d1e822cd6a96845c080008199a081e3213ab0284b20d90bb2b8f9f20c451a40000364a036800033480000002d84000007a7f6379c00000f800028ca3fc98c60002fb00001a2855f118415b812613191b43b300000f398782e71d0277c9f7c0ba00005350000a181084c06000000000000000ba600000000158000e580000000165aa6e15fe0db81ee7bb0000000000065210cc6ee9ae20001f6600000000000000c348000879000099c0000000060e31c00000eb05a4a1005b64348000b00000025e9762465936a5da980649e9512391b79a00010c600000000002d389679742d528000a5aacd20b80000e578ab40838c200000000a46324613780001d0178c28681ba32d977a08ea5fec1780000002e820af800025f868801a00009fd10b04c1081a91319903c8b2fe37c12fa555a3da61b29bc45236e4825b8162c1817655306f0e108000bca29caca500002568000000314091280000000348c63a6da50f0d08000000000000000002454be20ed6ddf1fa4b54043071996429d99cfa7499e18bac327c5dba46a3891652b7f82dcd64816432d0a8aa5f82ec6a38184943acb89feb576996323a9d620a4bfe2d060c2935015a0d36a71088c3c6972802ab2a2c0a057ca7a1b3248f0c00d43b62656417685b6b1f66de8478d4b05a06eb102a1d4aab45aab8da41f9bc6c750000dfb86800649a6e41b8c944f185facc299d2560a30a854800005f974e00010b88a09e12c408aaad9a00004f0ab140f5000040039342632010166800075e8b3499fafd26608000e0e000000012e4000062886f37140003
  | 59 => 0x76e96d863c910800057929287df8000b44869a800ac5a15781a41e738b49f8837c0000b128910e64cf59e684419776c7c000082cadb2c3ea7ae8d30e9a0000000787038642cb04a90b8000165b7a6cb501aa661000092e000027c00000000000c559a4ee5309c8602ae4a29539247e1011605702a88420cda965a0324dd80005c9866e0001dcc00000008fe13406f79ee48f52f74b9615208ef3348c0f9be20000c900000000000363ea5580002ec0f9200030dc88e800016380003f282fe0002c3000010ec551b93e3298000c800b664cb2ea22bb9b7e2a904508ca3832020909e0a4908eca6859cb570000b6800000058000000096800032ba4258758be0aaa6d0c2f8ec40119e0001658d099b8e09e06c4000207aa6807247cca73e0002d94025840e22c88d8743b0be0a192ec571231c94fb0ceb071a92ae737a064a846c2a30d28277a32a9dd26ee60a959a97399b629d380c9ac041ecdd8436cad94c2091a7baa99073278a8ab084a22909850284bbd02f05f385f041738523da84f8d751f9cb7bb130b0f20cc194903c1f5b6e02f290989fb24eae3f0ad45759156501a98c000001ed9b00007bc000083100007eb00004e8800046a219a112962c000000066525c8196297c815b7c682236744da207670b08a4000000099d2c78681108c3511190b9b99b036e8e844fe0c142840b58000000000023260001d9a67b00003950000c0280003bc301e28b00001231bcedb9824a0002ecc668b8e259a90661633180bf81fc224534aa000202e1e880000001366b6480000000ef800000005b900000002e7200000006a7800050d89169e5b60c7648000b4d9140013b724988092e0211c704302aa800034322c211d0573872c2b4a57e30f0b568260000d8d8000944000091408b83f4360edf3a26aa648ef618aa2eae4326400772c42391000033088f4000124c3baabf478a0ae2d5091a25c4134896c0000d3db3586cd97d48cd17f6b2eb1a46980000d2900005472b2600018f47fa288600012c403e80006df2fcc00037bc0002c86c49014c2a51cce3aa2c986a6351ec44809c7cb0238dc11d322d2a1f48ea27c43399de84ce381c8a1840a8942524c4620e01e08b76cf2276e1f7800032000004f6000059a000ab3d392c0341198767000034535cc32b0000017293ece59c1065a883071f8000739000000024a20001fbe90080000001004e439e4081000349ea08763ff2ec65428000af193da36d92c2cb10000c218fb889628c26dca31400023ec344045e19ea5920003758000294000017ec00015265b081a000034020d3adda97a80000cc984654e9c6a00000000000000269ac6a0000000000236aa491d360000000b129aca5fa00000000000bc480000a08000b0a0000a53094074e80000000a020000cee00017cca29000000000000880000
  | 60 => 0x1f0800076b80001ba31c0b01077461ab4b85d9a036e3b16e600000006d9088000000000000c2ac1aa05ce3c0a7a92c244871d94028b934e0a0797901e511be00001a8b4f07c8bb680008d5000000000001648380ca202e20421beeb17806ee138d5200000000eb82000001d160000000a6d80000000690158983635a02ae3b404ecbee035e0002c660000f6c000092600000009d5aedc1c691bad1f00001343060557273640c336a5278daaa4e000000027046ab1502b14b8b80091516a1c96565a224d2000000040790400003146a24144a000082678f136e000000077400008b7039c0000ff6000214e0858caa0002520000017c8318000000000068b114e00038a60001e3a0000000445000053d078a00027f85ab93a0747993400022d68c21fa8d579ba205bab688a50bfc00000003ff8faa03f1d3edc1800099e28bedf60000bc4104ad20a1b8c9e06cc5440c5e7f8800000033f0956228a7251f78000038c00010fa000361c000337e03f94282e5b1ae976222e42db652a3d811c00000006b2235a43f22c86959818311000073118f83d8a82a2baad60a7ba4f007f0e4e941afa8409283eafa1260c2c90e272f96e26709b5264c8ac0b0ca62ec3f179297f34a2cb08256c478e8e22f1bd66728000c50ac9604805e61e210887b9a74ec148f1e6ba93ee849af2e05b1bd088c1ed255e87aad2d80008cc8cf4648118c428a974d6f04928d080003f7943288898640001a0270035622f90000000000000028d40000e8a9aeb1e4000000000018cc9530000b2ab8cc808b4b4000028c000000000031d0258a3a2d79800053e20aeab8129200db8829a282aa9f795f22fa0c3633a8cb263d8186ae41d765b2a3804908000751a2c4ba924f69c82d56dbb80000000000000000000017fec3200000000dd683e00d884a922256c32280002f3a6ef8500bfe809a1a330006dd14fe5bd232c67aa942055b022a4221f0c6d8000dec1896bee800019e12d2ce9272a2b3a0840071b982092dc00608000000350876d1bf4cacb6187f18b485df80009311ab8e1625986c38000450800000038044fa29c837fa0ac6d9800000000001041e62d7f383ee2a827647500000000000000330c00018723d3800000005be7c90bb8e191da4c8e00004af874a0001a120fe0000d2b07be2c6aa2c96930b60002e682ce800004b00003e71bdc6039b7074c00003528000000000000032709d0800048e93b4dde8e82a5129fe0510000dd40000a2c00000000d3400037f00002db600036200001f7a47cb3c268f80003558c0252586ba37707347720000c4f0000bc9a8d23221c3e47213a84d2a70000ba2d2c082bd639786e44cc118676c2482ad037441b00000053819e489ac941160000000000000012f811937309ad3962000000039633e6a5eaf6e2c60000d36
  | 61 => 0x80a49480001fd265436380007839992000181433e8000000396cb2f81bc48f80000002fc000015d40001ad400015f41473416d688e4c2d686209d70000000170a30c34504a317166b6af3c1cf80003c100001bb000000026965b11c2a39880000002632cef8e16b2a2fae000000082f074e20aa2da991043251ab9520001180d8414980549ed0663000069da0a008aa4de873070800016a09db255c00020208308fe4d37063ab9c128a1b200007ac9fbab279dc2dfd007416c8ab807fb2e23eb1636000381a20b806a4a7a570dd2b5266388ffabab0000c341998870293200000006c080000e5216a00025520000e96d01b84c33c8000af30000a66a0d0550000078b00009e82aae02211b8917824e0000000ba81ce000004b40001d6c0003760287a10608a16e03438b0a4aa8000078290622b80005943720d76a478000273c679283a8b080009b0ae4e9b3993c0002df232f0000136a36600024960000000b7d985c26c197267980000000f0a73480005e70e220002c8400000003d1998e8fbaeb20002952000000000016e800000006cd212e00029660000000d0ea69c00019b2e47aafc8d1085cb9ab6bec6f953c0000bc893ea3687512c88df59210bf1000000000000000000e2f000000031e8000000022ab802746281ce39362ce0900005b3376e59005d0b8705cc34eb6fe0750b46317004ae15196298f8000a8c80003c1af3ede788da38f00009f18000c4c8000000225c00018ee2c5911c000000088580000000eee000077c24a3444000150009980000000000bb62fbcd879e9ee1a8d1c0000ebcb920fc66378000db00000a68b3d8db1b3fe351800000000009bd80000002e42c7c80000000820b36a604ac5932e9eb0000b9d330e006000000009008f2800064a0180000000000000000000000cc180000000000b118000abf9b9e13f800000004460868000afb8d5c1fc8bc0cd91938940af868df903610f274c95b8b700000000a85b5c600000005bc800072383120000000000000000000002ba0000000113a8c62a7001e00000000130d0900000000000a552a000151dc4000049ad4cb190000209c61208cc8ffa7bc0000a926ee25be7f4015a53128ceccd91a0cb631e01b794d0969b5c8d618ff85ed800000000000000bce000216e6098000dc01fae00028a272b1b6c592b1b83dcadb48a1272286206405298f785a6104c7dba6aabdb00000002194000036cd8a0244ce2800017800001a5954a0000000000000000032929c22a22451000000000005378000000000000003fc00005b000000000eaa4bc00000003d11a7e00025aa2c90000000316e000025c0000000541b27a8e2861e8de25e8a442caeb288000132200800000000002c560a8800000000009ed25d430300000002a0eaeb8ea2771abfc00008ac93f8b988b9800
  | 62 => 0x50129121ed0000ce08000aca000000035b6d07800000018001033272000258200000000000000779800065daff2000000000032840001df60000000a1e057e9c09d5c2fe2b2a56008b4705842200c13c8aea819400000004f8800000027b805a0000c48a8f8000045a4a180000003718cd580000e48000aa300000b5af24000143a02c909c1561dfac2b0000c2c2140b2c0f4cccb0c1ea2ab64c4d1b4d626824ca80580007b20bba5fa832478d36fa00020c800026d4e3c80000000000af000003f5800021aa90235aa2fe07288944580ee8000000032c0000c4705f45b4b3ca00010f4338299cd1d81740000a3400000001460000bde876c3b48302dd4af96acf810e00005420000000000000000003ea8f32b720000e06c96ac5c9a80f32000157698034ea86db42037a9b5e88c87285a7a3761198f140ec90e4b1c2f2cbe28aa63cb29aa267a2429048676b5c0abe0fb93ce6a9340029cb24e64da04c0dc96c8c0e80001ff1b0c27b1216a3f9dbc00000000003210000000000037ac79d108a44cb5243ef0c9622589a891c8af8b23881600033700002d6a00000000002f4800000000000000cec9a580000000c538000c84a5ba9279328ab684b6bd182ce52a8ca814233088eea0cac8b278c91bb53695a898a000262a000353c000000000014e65832f984af07ae1f602d473f1f6c2a5815ee4a839a58000004ca8000ad3359c9f280000000000000000075300006d21c4800038d00000092000289c4158000d628290538a7cc00013449ec0beca3b0000c77144800026ca000235ed34ab9854b1ddea95000067621ac0001a1a0c311de6b138d47b62cfa4dc09c00003462923a0fc2a0080c00014fa718a0a22a200000000000ca0899047600b000010f0c7f00000001946ae52a7aba3b8ee000000071004b8000000080c06ce0003320000245600011caafc312ac38a6e8bd413746532a7e6140c54df20b5e00000006c5134ce2b8afe21289e610e345ee129efcabcaf60def836242a270e9511f166bd0c085a41080e4a1858da100004b180527481bae557831c5c100085ce264a708254800004cc8490fae4a3a1209a6200026f9ae441504402ab858a8a7122adf32a829b788ca81c9cea9500a362f50600cbd2338000266e0001a6a933885a0001f863069a00a378000c5f110a65700000f480000001eea3012df456f202a44c1bcc0f0047c00024669c988049e09da6d0b80009a89b1a0ae000000006d400025080000000e269f0cca780009071632e5900000cc29fc19523a6d9e9cf400000003119944c70897600006643419b8a5c9000000020460003746a6c80000002498724358eb54a5e6000041a00002fa000026e00036309ef80002260000bb400004710000b6c1cbcb43951835d211ebf7338e8fc145829b8eca813997842f338c00
  | 63 => 0xb48f8243400036ba0000000d38870400027d26072fb2000298a35511209a912b80ef0000463800097b2c267398d3e7b79e26adf81ec1208000c63319692e80007491f60cc78806000000029798ca30a31fe497131000034986199cc20002dbe8dd10eea0c093e0ea06120599b6a8608902101800061a08fec2332640748000d6208846b41092aab00000001e0ad9807306aba44662516d40000522ddb2810b4080008bbb7ba0de000000018200002c501ff9be600000009a38fc800000008af0000b53a7a2839137e00000001da800000000007d020806311c9c5ad97b8001a814b6e076678883346aab24a00005c41d5b04e5d2800000000005e5a51a8728000b858066a659c063768ba0000000081a989e0d6282474a2e8427d94f2e4daba400034340358a6cd710000b392f58c281d2aa2f00009c32dfc2ca02360000000255817a9e69e66ca632ae7ad33e8660124800000000ce2cb402823220000000c9f800084f00000000000baa87a0a14a74469795ca000323211c09e4cf90cc617d86ca96f203a24cb23ca8ba2a29f73898c6622c65bc1e147ec9f98ac29230306175a836b1040978acc9ec87f61de86aa004214cdc71a1017f8000a141daae198000d2a02ac2e39c386de2b1ec8f8adac9098dc1110356a0c9082aee029800000000000000ba2a62800000006a300c400000009979a42000000096b93aa3b10d8c35606048349888000000000000007f69a4cd7f959e57f0000d63149251500006d39aa23ee800007d1f944c08dae00015c2aa40c84b7e34f800002f2333200a35037707ba077052d80000000000d952dc24141be0b2f013a327a3d00fcb49c000156c519a04a16b8b9e6ff8744e2c20ce359311a5c517f264680000001f820000000a020000000230e45b94d6b52b148b292ce661c2e38ce98c48b8409e210220420fd8e48dff9ca04ec00003718f6495e1a7a0001cb25e3ab882deb3142072cce0000c8c21232a0000094c000221ac9ab90a10100002298000ac09aba0000b7e88a8a1c9059618aa8a7ead6ca80c59db3a26faab6e34f1c242e89dfc00034ee00000003a20000795b646b5fb6a60f40000000289600000000000000bb224f4c86800000010e800013ca00017be000000084d8000a978aa00001adc6f0047a1182c6ead9273ab28116a00000008298000b83aa74b480000192800006400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bc845d953440011df04bb2a68800a3b2097654d1004c3e43acaa9a204ea6c8259553440091bd0fb1aa6880163d2197190d1000c7c432e121a200487e859d943440010fb0b3b2868800237e0d7650d1004c5e43ac8a1a2009a9c8359143440011bf06ba6c4880263720d74d891000477c12eca92200287c8759552440090fd0b3b284880021f61676509100043fc2aeca12200487c855d942440011bf06bb284880263720d76509100145e43ac8a122070a9c8359142440071dd0fb1284880031b1d762509100146f41ced99220058f4865c732440031f10cb8664880023ee01764c9100243f428ec992200087d851d9324400717d083b264880022f610764c9100146e43ac699220098ec8758932440131e90eb226288002e5610634c510005e2c10c698a2000bd18090d3144001d2ac8a1a6288002f4603324c5100056a4326498a2000bb1841c131440017c304382628800a3d21d654851002c7a432e690a2002ce4765092144001763083824288002f460c704851013574412cb20220268f8865ca4044001ba2e698c8088016bc2192190110006f0b92432022025a3e85d91404400757509b2a808800e3e21d65501105ef1c2a2caa022024ae88259540440ad6750bb2280880067c2077350110006e918ee6a022000e9b43d8d40440071f10eb1a80880067c20772501102b59c42a84a022024ea86250940440033e50fb8a80880027c21d3150110007c8a1a62a0220009f087485404400b5e10c90a8088003e8509215011002d6a4326398220019f0815d230440135b106b246088016bc219318c1100bee8b9a631822000de172486304400b3a90e98a6088016b5219314c11002de84026298220018f8865d130440033e102ba260880263e21d644c110005e4c10c69822000bd181cc9304400b5e10c98a60880073c1d9314c11004f6831a629822005bd0874c53044003ba10e98a6088016f4a19314c11002de8432629822009ed0864c53044013da6ec98a6088007749d9314c11000ee83b2629822009ed0764c53044001ba6e898a6088003745d1314c11000769b22629822000ed1644c530440017a70498a608800374dc9314c110005e8c1a429822000fc13248530440055d104b2c40880067c2057488110006e8b9a6310220058f686dc5204400b3c90e90a4088016b9219214811002df04024290220028f88759520440031f10cba240880067c205744811000c7c432e69022000dd1734c52044001f826498a4088016f821d214811000ef043a429022005be286485204400b7c10c90a408800bb8219214811001771bb2429022001de2764852044003bc0ec90a408800bb81d9214811000771b2a429022000ee1654852044001bc6e890a4088003785d12148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0xa84a8a83100163721d634c6205ff1c2a2c8a84406af2a5450950880016d704a8aa1100035cdc551542200061eba4a9b2a400187c85dc565480090fd0fbaac8900021f60775591200043fc2aecaa240008df8758c63480051d9053b4a6900163b2197294d2001c5f424eca9a40008bd849d953480130fd0fb2aa6900163b2197290d200043fc2aeca1a400487c855d943480011ef02bb286900063d2057650d2004d6741ec899240098ec87591324807f4d90ab226490002b3a1a534c9201ff2632aa69924000b69851c132480017c30238264900021fe1574d85200243e42ae9b0a400087f8759351480090f90eb26a29018e9b21932d452000c3f43ecaa8a400187c8759551480014eb033b2a2900029de0576545200043fc3ac8a8a400087c8759151480014ef02b1aa2900069d20563545202d53643264a8a4039a78865c151480031790eb2282900eb8d99151505200071ab22a2a0a40018de839db31480090fd0bbb262900021f617764c52000c6e43ac698a4001ad48158d31480031d90eb2242900163b219734852000c7643ac690a4000e67865452148001cc90ca8a429000799dd9514852000f323b2a290a4000e67645452148001ccac8a8a429000399d8d514852000732b1aa290a4000f62805452148001ec300a8a429016399d8151485201cfb1b02a290a4000f6151dc121480016d30a3824290003d854470485200253c42ac92824000d71715465048001bc2e290ca090003d854521941200253d42ec8a8240048f88759150480098f0eca9aa0900027a21d3254120016743b264a824000f49534c950480098f0eca8aa0900035cdc55154120007b0a8a42a824068ea820d91404800b5990c99660900167321d324c12002d66432649824005bc8804c9304800b0fd0f2a2cb080162fa1f545921001c7cc06e4b24200587c87595538400b1f501bb287080162f21d6450e1004d4e41ac8a1c200587c8759552840071db05bb285080163ea037650a100043fc2aeca14200487c855d9428400b1790eb2285080030f1d56450a1002c7d406ec99420058dc8758d328400b1d90eb1265082fb8e15165502101247cc36e4a04205db388550940840bfd50c4a1281080023ee19734821057e36394a8b2a20028ee87dc965440018dea3b92ca880031b54772595100053ac0cebb22200487f875d764440c70ff02baec88816a1f60575d911002c7c402e5b2220098de87dcd64440018bea3b9ac8880031754773591100043ec2cecaa220008df835d954440131b906bb2a8880023be09765511001476412ecaa220008ef825d763440051d904baec6880029761443d8d100056ac0887b1a2000ad98010f63440011bf0eb18c6880273398d7218d1000666b1ae431a20098dc835da534400b1e90cb8ca6880063e2197094d100045fc22eca9a2003
  | 2 => 0x5425843031e3b40aeda886000c75815db510c0c9c3ce6b26a218003875cd64d44302d61eb8ac9a886063e3a70593510c001c72e0b26a21818f8e8c164d44303271c982c9a886064e4e7358b510c001c9ae6b16a21818f9a9c162d443000734b82c5a886063e4f3058b510c0c7c9a60b16a21818e9de1d61d44303272b39ac3a886000e5573587510c0c7ce4e0b0ea2180039c5c161d443031f2b982c3a886063e7230587510c0c7caa60b0ea2181939c4c161d443000c3ec2eeca88600587c85dd9510c0b50fb0eb2aa2180161f21d655443002c7a43ac2a886001a7481dd9510c0018eee3bb2a2180121fe0776544300063bc0eeca88600487d81dd9510c0b58e903bb2a2180031d90776544300063b10eeca886000a77815d9510c0018eee2bb2a21818e1fe0576544300063bc0aeca886000c76415d9510c0018ec42bb2a2180069da0564544300071b20ac8a886000e3681591510c001c6b02b22a21818f0fdc564544300071bb8ac8a886000e3621591510c0b5c7460b22a21818b8e4c1645443000d3b40ac4a886000e6621589510c001ccd02b12a21800399605625443000733b8ac4a886000e6641589510c0b5c9e60b12a21816b934c162544300253b43ac2a886063c7687585510c0b58eb0eb0aa2180129d21d61544300053bc22c2a886000a7782585510c0b5cae60b0aa21816b9c8c161544302d72a982c2a886062e7130585510c00b17909bb282180162f21d64504300064eb26e6a086000ccf73589410c013998e6b1282180163d21d61504300066bb9ac2a086009cd473585410c0014ef0ca8a82180029d61951504300063bbb2a2a086000c7576545410c075c6cc8a8a82180038d591515043049733312a2a086000e6562545410c00b1d905bb242180163d207764843002c7c402ec9086005cb870591210c00b1d90eb1242180163d21d614843002e78382c29086000a7786545210c0014eb0ca8a42180031ddd951484300063abb2a2908607fe3664545210c001c6ac8a8a42180e799989514843000732b12a29086000cb964dc1210c0019d2c5b8242180033c587704843002c3f43ca8b2c4000a6d82951658800b17d0faa2c9100263be197294e2002c3e43acaa9c40058bc87591438801353906b2287102cb1bddb7550a2057637bb0eaa144000b65811d54288001c5ca8b2a851000eab2116350a2000556c3486a144024ae986dc142880090fd0bba2c3100021f61774586201e537c3285a8c400187d85dd9518800b1f501bb2a3100161f21d65546202d53d406eca8c4000a77815d951880014ef02b1aa3100069d2056354620004b643a84a8c403aa6f8650951880736d104b82a3100035adc970546200046fc1aeca0c40098dc835d9418800b1790eb22831000eabe1942506201d71b322a2a0c4000e35645454188001e4
  | 3 => 0x4b106000a6e85885620c0014db0b10ac418002aba10755883000556c20eab106009ace831d5620c02959b063aac418002b9a04755883000572c08eab106005aea801d5620c0295d3003aac418026b3a0f74588300a566c1ee8b106005aea809d1620c0015d3013a2c4180029be1574588300053642ae8b1060008ee87151620c0011db0e2a2c418026b3a0c545883000566c18a8b106000ae681151620c0015cb022a2c418016baa00545883000574c00a8b106000a6e859c5620c0014db0b38ac418016ba201715883000537428e2b106000a6d851c5620c00155d0838ac418002ab610715883004d67418e2b106014acd831c5620c00b5d50038ac418052ba600715883004d6741ea2b106000acd83d45620c00b5d501a8ac418002ba60351588300053742c82b106000a6d85905620c0011dd0e20ac4180023b61c41588300053742882b106000a6d85105620c01359d0620ac418002b360c415883002d7540082b106000ae980105620c00b0f90eb2aa4180163b21d62548300243e42eeca10600087f855d9420c0090f90abb284180021f61b75508305961f326eaa1060afc6e62dd5420c0018ecc3baa84180021fa1d65508300043e43acaa1060058bc87591420c00187eeab2284180030f1d5645083002c7643ac4a106000c6f75589420c0018d8eab12841816a9d606755843031d3bc0aeab08600487e85dd1610c0010fb0bba2c2180121fa1772584300043ec2ee4b086009ad683d45610c00b5e501a8ac218026b5a0e75584300056ac1ceab086005af2809d5610c0015e3013aac21819395a0e75584300072ac1ceab086063e72809d5610c001ce3013aac21818f95cc2755843031f39184eab086063e55309d5610c0c9ce2613aac2180031de1d75584302d72b982eab08605ae72305d5610c0b5caa60baac21818b9c4c175584300053b42ee8b086000a7585dd1610c0018eaebba2c2180031d5d5745843004d6a41ae8b086000a76851d1610c0014eb0a3a2c218026b5a0c745843009d6ac18e8b086000ae6821d1610c0015cb043a2c218016bca00745843009d78c00e8b0860008f687151610c0011eb0e2a2c218026b5a0c54584300056ac18a8b086000ae682151610c0015cb042a2c218016bca00545843000578c00a8b086000a7685dc9610c0014eb0bb92c2180031d5d772584300063abaae4b086005af0805c9610c0014ed0a392c2180029d61472584300055b420e4b086000ab5841c9610c0135ad06392c21804eb560c725843002d79400e4b086013af1801c9610c0011ed0e292c2180023d61c52584300055b420a4b086000ab584149610c0135ad06292c218002b560c525843002d79400a4b086000af180149610c00b5e501a12c218002bc603425843004d6b41c84b086000ad583909610c0014ef0aa12c2180029d21
  | 4 => 0x14c0094ed0fb0aa2980129d21f61545300053ac26c2a8a6000a7582d85514c001cae65b0aa298003954cb615453000c5e43ac8a0a6000c7676545414c0018e8eca8a82980eb8d99151505300071ab22a2a0a60008df87593314c0031b90eb226298003a5591414c530005ccc20e098a60058dc865cd214c0018ececa8a42980031d1d951485301cf33312a290a6000f4532545214c00b5b10c99480980039cd855190130006e8b8a632026003aba84d95404c0071f10eb2a8098002f26087350130005e8c08e6a0260059b88750d404c013970eca1a8098027661cd435013001e5c3b284a02606cb3885509404c049d50c4a128098027361db3250130004ec43a64a026005ad8864c9404c0139b0ec9928098003e250932501303263c3b6a2a026062c7876545404c001ce6c2a8a8098003cc5454150130007c8a0a62a02600587e87951650c0134bd063a2ca1805a9760c745943000537410e8b286000a6d821d1650c0014ed023a2ca180029d604745943002d3d400e8b286016a79801d1650c00147d08392ca180028f610725943004d2f418e4b286016a5d831c9650c0014ed02392ca180029d604725943002d3d400e4b286016a79801c9650c00b4f501a12ca180029e603425943004d2f41c84b286000a5d83909650c0010fd0f20aca180021f61e41594300043f43882b28600087d87105650c0134bd0620aca180029760c41594300053741082b286000a6d82105650c00b4f50020aca180029e60041594300043f43c42b28600087d87885650c0010fd0e10aca180021f61c21594300051f42042b286000a3d84085650c0134bd0610aca180029760c215943002d3d40042b286000a7980085650c00b17d0faa2c818026a7a0e42590300051f42c82b206000a3d85905640c01353d063aac818056a760c755903000557410eab206000aad821d5640c00156d023aac818002ad604755903002d5d400eab206015ab9801d5640c00b57501b92c818056ae603725903004d4f41ce4b206000a9d839c9640c00147f0ab92c8180028f21572590300045f438a4b2060008bd87149640c01353d06292c818002a760c52590300055b408a4b206000ab581149640c00b57500292c818002ae60052590300051f42ce2b206000a3d859c5640c01353906b8ac8180028fa1471590300051ec28e2b206009a9e831c5640c02b53b0638ac818002aba08715903000556c10e2b206005aba801c5640c02b5730038ac818026a7a0f51590300054ec1ea2b206005aba80d45640c00157301a8ac8180028fa1621590300051ec2c42b2060008be87085640c00117b0e10ac8180028fa1421590300051ec2842b206009a9e83085640c00153b0610ac818016aea0021590300055cc0042b20600587c87595540c00b1790eb22a81800a3760f745883002d754068
  | 5 => 0x3cc547705054000798a88e0a0a80018de839db3150013938eca1e62a00263e21970cc5400243f428ec98a800087d851d931500051dd043b262a00023b608764c54002c5e432e898a8000c9c7650d315000b1790cba242a00964f21574485402fed43828490a8000d35745452150073cccc4a8a42a0003c9509514854039fb1902a290a80038fa86dc1215000737508b9ca0a00026ee1d43941401247cc3ec528280009bb8750a505004b6710aa14a0a017f6a1c9429414001cdd422e3282803ad3a745465050001ae2e2a8ca0a00026ee1d419414000798a8a83282802bb3a85dd1505005767108a9aa0a0096ce21543541400078ca9a86a82800597887549505005767108a92a0a00026e21d425414012d9c42a84a828024da8725095050001e52a4a12a0a02fb4e15371541400263c3b2a2a82802bb38845455050001ae6e2a8aa0a0096ce215415414000798a8a82a82800987c8759554cc00517b09bb285980021fe157650b300243e42aeca1660098ec8758942cc0018d8eab12859830793149654cb3037da642a849966070e8c6450932cc0090fd0bb92c3980021f617725873000c3ec2eeca8e60008bf845d951cc00717908bb2a3980061f21d65547300051fc22eca8e603aa3c845d951cc0014ef02bb2a3980062f21d645073004c7a43ac2a0e603ae366454541cc001c6ac8a8a8398006b5205624c7300074ab228298e60058de83dd921cc00b3b100b9a43980063b21d62487301cf33312a290e6000e656254521cc001e8a64a8a4398003724cb704873004e4e39ac8a06600587e87951658c00b17d0faa2c9180161f21d6554a3001c76c16eca14600087f855d9428c0090f90abb285180162f21d6450a300061e3aac8a14600487e85dd1618c0010fb0bba2c3180061f617765463000477c12eca8c60028ec825d9518c00b0f90eb2aa3180029be0976546301cd36412eca8c6000a77815d9518c00b1f501bb283180162f21d64506301d71b322a2a0c6000e3564545418c00b1d90eb1243180163d21d61486301cf33312a290c6000e6562545218c181c70a8b2a81180166e21d435023004ecc39a86a04606eb3885509408c0bfd50c4a128118002e6e0d415023000798a8a82a0460028dc835d3624c0090fd0b3b284980021f61676509300145f43ec8a1260038ee87d89424c00559d05b2a649800a3721d654c930016663b284992606db4c85509324c07dd18c8a126498002e6610704c930005e8c08e09926063a5c864cb514c0030fd0fb2aa2980061f21d655453000d3a40acaa8a60048f687d85514c0014eb033b2a2980028fe1176545301d51e422eca8a6000a6f825d9514c0734d904bb2a2980029de05765453000d3a40ec8a8a6000a7781591514c0034e902b22a2980069d20762545302d52e43264a8a6001a7686d855
  | 6 => 0x43ec2ee4b0c8063c7a105db51900018f220bb6a32018e9e20162d464000c3ec2eeca8c800587c85dd9519000b1f501bb2a3200161f21d65546402d53d406eca8c800487f81dd951900090fb03bb2a3200031d90776546400063aa0eeca8c8000c7621dd951900b58f501bb2a32016b0fd0376546402d61ea06eca8c805ac7a10dd951900018f221bb2a3200029de0576546400063bc0aeca8c8000c76415d951900018ea82bb2a3200031d88576546400053bc0ac6a8c8001a748158d51900b54f100b12a3200031edd970546403d5b4412e0a8c80058fa80dd9319000b1b90eb1a63200163e201764864002c7643ac490c80058f487585219000b9e0e0b0a43200029de1951486400053ac32a290c8039e66625452190001ccac4a8a43201ebd8c8151486400053dc32a6a8480268f88758950900094f50ab12a1200165e21d52542400053dc32a4a848000a7b865455090001ae6e2a8aa1200028f61252d95400043fc2ae5b1a800487c855cb635000153b0818ec6a0002b360831d8d400056cc0063b1a80008df8758c63500139acc6b88c6a00033558d7118d4004c7c432e129a800987c87595535001353d0db1a86a0002c76146350d40005cac08c6a1a800399c8754d43500015390ca9a86a02db2718f7250d4002cdd406e4a1a80028bc845cf62500071f50db82a4a02ba4fa1f755094057e1e3b6eaa1280c5f2820dd5425015b878ec3aa84a0002cd604755094062794100eaa128025c3c75d954250001c5ca5b2a84a000a2f21d655094001cd643aa4a12805fba8805494250001a70ebb8284a00034e1d470509402fdd4410e0a1280028dc835db3250013938c6ba664a00263e21970cc94004e6c31ae199280058bc865d1325004b2790aba264a01c32718d744c9400146f43ec69928000cac7650932501876590aa1264a01c3a318d424c9402fed43828499280038fa86dc132500010ff0ab96c2a00121f21572d85403270e31a87a8a803ca7980d8b515004b2790ea16a2a018e8f21942d45403a79410285a8a800187e87d9551500b547b09b2aa2a00061f21d65545400053ac0ceca8a8000a5f835d951500c54b906bb2a2a00029be0976545401cd36412eca8a8000a77815d951500b547d0dba2a2a018b8718d43545401d53cc06c4a8a800093c8750951500b54790ca12a2a01cfca08142545401d59d424e0a8a803aa78865c15150001a70e8b82a2a01ceda20970545400074b18ec6a0a80059ba80dc9415000757301b1282a000e6d21d515054012e9bc3aa2a0a803ad34875454150001c6f0ca8a82a00038d219515054000f1bbb2a2a0a8001e34765454150001c6ec6a8a82a00034ddc951505400071bb12a2a0a8000f32805454150001e6300a8a82a01678dd8151505401d799b02a2a0a80c2f33205454150185e6040a8a82a
  | 7 => 0x9d83085649400b5750010ac928002ae600215925004d4e41ac8a1ca0038be84dcd629400117b09b9ac52800e3b60b7650a5002c7d406eca14a0b2c3e64dd5429400b1790eb2285280030fdd56450a5012e1e3aac8a14a000c3e645d7329404b87ceab2665280030f5d564cca500062ebaac7994a0058dc8758d32940c74ef02baac3280038d90564546500071b40ac8a8ca000e358159151940c787ee2b22a3280978ddc564546500071b10ac8a8ca000a778458551940014ef04b0aa32816b9c1c161546502d739202c2a8ca05ae72205855194001ce2c3b82a3280162f213765065002c5e43ac8a0ca000c75765454194075c6cc8a8a83280038d591515065002c7c402ec98ca0058dc8758d319400b1d90eb1243280163d21d614865000d3bc32a290ca000c757654521940ffc6cc8a8a43280038d59151486501cf33312a290ca000e656254521940011bf0eb18c6a800a3ba0b7650d5000476c16eca1aa00495c8754d43540090f90a3b284a80030f950765095057e36316eaa12a0038ee87d8942540092d90ea9284a800a9b219525095004c3e42ced992a0028de839db32540018bceca9e64a80161f219754c95027726312a6992a00187c855d361540030f90ab9ec2a80061f21572d855031c3e43aa5b0aa039c6c62dc95154001ccc43b12a2a80069d21f61545500053ac26c2a8aa000a7582d8551540034f50db82a2a80039cd87705455000739b08e0a8aa0049748754541540018ececa8a82a80161f219754c55015c9e422ea98aa0048fa86dc1315400b0f90cbaa42a80031d9d9514855000537414e6b2c8000a6d829cd659000b4f50139acb200169e201725964015d1f420e4b2c8000a3d841c965900014bd06392cb200029760c72596400053b408e4b2c8000a75811c9659000b4f500392cb200a29e600725964015d1f42464b2c8000a3d848c9659000b4f500192cb200029e600325964002d3d404e2b2c8000a79809c565900010fd0f18acb200021f61e31596400043f43862b2c800087d870c5659005747d0818acb200028f61031596400053741062b2c8000a6d820c5659000b4f50018acb200029e60031596400043f43c42b2c800087d8788565900010fd0e10acb200021f61c215964015d1f42042b2c8000a3d8408565900014bd0610acb200029760c215964002d3d40042b2c8000a798008565900090fd0bb92c7200021f6177258e4000637392cb29c803fc6e655ca53900018dacab94a7200031e5957094e4002c7d406eca9c80058f8805d9529000b0f90eb2aa5200031e5977054a400243f42aed994800087f865d732900010ff0eb2e65200021f61d65cca4002c7c402ec99480058dc8758d329000b9b0e0b1a652016a9d606755864031d3bc0aeab0c800487e85dcd61900010fb0bb9ac3200121fa1772586400
  | 8 => 0xcb9aa2908e69d219735452119e3a3b2e6a8a4200b37845cd51484ff66908b9aa290802d9e0973545211cdb2412e6a8a4239b66821cd51484016cb0439aa2908c25da1e6354521004bac3cc6a8a423db658298d51484816cf04b1aa290802dce016354521005b8402c6a8a4200e556318d51484736cd0521aa290802d960a43545211cdb341286a8a429eb6687dc95148473acd0fb92a290806d9a1b725452100db2436e4a8a4239d6676dc95148473ac8edb92a290802d96137254521005b2c1ee4a8a4200b6580dc95148401acf0ea12a290802d9a1d4254521005b243a84a8a4200d648750951484036cd0ca12a290806d92194254521425b3c2284a8a4239f278450951484ffe4ce8a12a290803c95d1425452100793b2284a8a427ff246450951484016cf06a12a290803c990d42545213ff9221a84a8a4200b678050951484ffe4e80a12a290802d9a1d3254521005b243a64a8a4201b66864c951484036c90c992a2908ff99dd932545211cf323b264a8a4200b67844c951484016cb08992a29080399d91325452100732b2264a8a4281b67834c95148473e8f06992a290803d19cd3254521007a2b9a64a8a4200f47634c95148401e88c6992a290b1bd1d0d3254521637a221a64a8a4200b67804c951484736c905b82a29080359dcb70545211cd3b434e0a8a427fb36849c1514840166b09382a2908e6d9a0a7054521005b2c14e0a8a4239a74865c151484016cf04b82a2908e6d92097054521006b3b92e0a8a4239b66821c151484016cb04382a2908021fe1574d81210243e42ae9b02420dd65725466048421acee4a8ac0908025de1d51181211ccbac3aa2302427fd36745446048401a6ae8a88c090803559cd5118121006aab9aa230242008fb875806048401ce2a2b00c090802a7a0e42592500054ec1c84b24a000a3d85905649405d47d0a39ac9280028f61473592500064eb98e6b24a000aae821cd649400155b0439ac928002ada0473592500055ac08e6b24a005aba801cd649405d5730039ac928016aea0372592501755cc06e4b24a000a9e839c9649400153b07392c928016aea0272592500055cc04e4b24a000a3f855c9649400117d0f192c9280022f61e325925002d5d40064b24a000ab9800c9649404b47d0b38ac9280028f61671592501751f428e2b24a000a3d851c5649400153d0638ac928002a760c715925000557410e2b24a000aad821c5649400b5750038ac9280baae600715925012d1f42c62b24a000a3d858c5649400117d0e18ac9280022f61c315925012d1f42862b24a000a3d850c5649400155d0418ac928002ab608315925002d5d40062b24a000ab9800c5649404b47d0b10ac9280028f61621592500045f43842b24a0008bd87085649404b47d0a10ac9280028f61421592500054f41842b24a000a
  | 9 => 0x76509310145f43ec8a126200c3c75d91424c48353908b2e64989063721974cc9311fd3742ec49926202ace82d95324c4051b90eb2a64988faa7211654c93165f26292ca99262019d481dd1324c4031b90cba2649880675205744c931455a742ec4992628ab4c85509324c47dd18c8a12649880675a1f714c93100cea40ee09926200dd310dc1324c4071e90eb2a8298802f16087350531005e8c00e6a0a62019b48750d414c413968eca1a8298827651cd435053100dca43a86a0a6209d948750d414c40372d0ca1a8298806e5219435053101f4a43286a0a6203e977650d414c413b2ceca1a8298827651d9435053101f4a3b286a0a6200e976550d414c401d2acaa1a8298802e5e094350531005cbc0286a0a6203cb476509414c4139a8ed9928298802e56133250531004ea43a64a0a6209cd4764c9414c40172b089928298803e15093250531006caa1ee0a0a62008bf845d7604c40717908baec098803b24cb20d81310053cc2841b026200ad983083604c4015e302106c0988172e98174181310047dc3ac03026200cb974580604c40187ae92a6ca908029b60a54d952101476412e1b22420487e87dd564484010ff03baac8908021f60775591210043fc2aecaa24200c7b51dc163484018f2a3b82c69080237e1d6318d2100c76432e529a42008bf845d9534840717908bb2a6908023ee017654d2102c7c402eca9a420987e87d9553484011f700bb486908163e2017690d2100c76432e521a420087f855d943484090f90abb286908023ee017650d2102c7c402eca1a42b2c6c76dd5424855d8d8ec3aa8490802d96047550921007172a6caa1242038ec87595424840755d09b1a849080e3b21d63509212fd74402c6a1242029ae8790d424840539b07ba264908063b219744c92104d6741ec899242098ec87591324847f4d90ab226490802b3a1a534c9211ff2632aa69924200de310dc132484094ed0bb22a2908123d21d64545211cdb3414a6a8a4200b658294d51484098e8eca9aa2909ffc9951425452100792aa284a8a4202ce4764c95148401e8ca6992a290803d154d32545211cdb2416e8a8a4200a77865d151484734e90cba2a290802d9e0974545211cdb2412e8a8a42c7e3664d9151485954ed0fb22a290a8a9d21f645452121d3ac26c8a8a4201a7782d9151484034eb05b22a290b278dd0b645452164f1aa16c8a8a42c9e6632d9151484012ef0eb22a2908c25d21d645452141db3c12c8a8a4200c778759151484094ed0eb22a2908129d21d64545210063a43ac8a8a42048748759151485094ef08b22a2908038de11645452141d3bc12c8a8a4200e67825915148591ccc64b22a290b1f8dd01645452150e3a3b6e6a8a4239b6482dcd51484734ed0d39aa2908029d61a73545211cdb3414e6a8a4200b65829cd51484014ef
  | 10 => 0xa8a8204a7685d895150525e4ca4a12a2a0803c9549425454151d9b43ee8a8a823ad3687dd1515040366d0dba2a2a0806cd21b74545411d69b3b6e8a8a823ad3476dd1515040166b07ba2a2a0802cd60b74545410059ac06e8a8a823ab3484dcd5150401a6ee9b9aa2a08ea9da1a73545410053ac34e6a8a823ab36849cd515040166b0939aa2a0a4ad9a0a7354541005b2c14e6a8a8200a77865cd51504754e90cb9aa2a0802cde1173545411d59a422e6a8a8200d37745cd515047566d0839aa2a0802cd610735454123d9ac24c6a8a824ab378458d51504012ed0e31aa2a08ea5d61c63545410072ab18c6a8a8292b668218d51504016cb0431aa2a0802dca006354541005b8c00c6a8a8200b368750d51504016690ea1aa2a0806cda19435454100d9a43286a8a828db378350d5150475e2f06a1aa2a0803c59cd43545410078ab9a86a8a8200f176350d5150401e28c6a1aa2a0802cde0943545410059bc0286a8a823ab3484dc951504014ef0cb92a2a08ea9d21972545410059bc22e4a8a823ab34845c9515059d4ed0fb12a2a0a769d21f625454100d3ac26c4a8a82c8e6642d89515059bcca85b12a2a0b378dd036254541004bbc3ac4a8a823897487589515050966f08b12a2a08034de1d42545410059b43a84a8a8200b34875095150401a690ea12a2a0806cda19425454100d9a43284a8a8200b3783509515050766f04a12a2a08ebc9e0942545414979339284a8a8200f25725095150401e4ec4a12a2a0a4bc918942545414979319284a8a8200b37805095150525e4840a12a2a08025da1f3254541004bac3e64a8a823ab3684cc9515040166b09992a2a0a73c5d0f32545411d59b42264a8a8200b35844c95150537e2e86992a2a0803c950932545413e63a3b6e0a8a823ab3484dc151504754ed0d382a2a08eacda1270545410059ac24e0a8a823aa74865c151504118e8ecb82a2a0802cde1170545411d59a422e0a8a8200b67825c151505256c904b82a2a08eacda1070545410059ac20e0a8a8202cae7250b60504712ef0ea8cc0a088f4d5d1519814113e9bba2a2b028200d57735456050401aa8e6a8ac0a08023ee1d601814100738a8ac0302820987c8759554cc4131dd0fa92c59880a2f6137650b3100c6f41eeca16620087f855d942cc4090f90abb285988263b21d6250b31006363aac4a1662cce4c5259532cc47d1bb0dba26598a3ed3215424cb31387463228499662038be87dd1654c40187ea3ba2ca988030f54774595315961e3a4a4b2a6200c3d75d53644c4011f700b96c8988163e20172d91310045fc22ecaa2620387c87595544c40753908b2c8698806752057290d3101c6e43acaa1a6200a75819d7624c4090ff0ebaec4989921fe0575d89313143ec0aebb12620087d859d9524c4090fd0b3b284988021f616
  | 11 => 0x544b52f5003b284a88025e60076509510061f420eca12a200c3d841d942544018bd063b284a88031760c76509510061e218eca12a200c6e821d942544018db043b284a88031b8c876509510243fc08eca12a200c76811d942544090fb023b284a88031d60476509510061fa08eca12a200c76411d9425440187a823b284a88031d504765095100637908eca12a200c76211d942544018da423b284a88031d48476509510063d400eca12a200c79801d9425440187e803b284a88031b08076509511cc9e43ac8a12a200b378159142544032ed03b9a84a88025d60773509511cc9f43c86a12a200c3c7690d42544752d90eb1284a8802d9e0562509512253a432e2a12a200c74765c542544032ed03b8284a88025d60770509511ccaf41ced992a262c5e839db32544c58dc653b664a898b1b4ca76cc9510243fc0ced992a20487d819db32544018ec833b664a898b17cc676cc9510062e98ced992a200c76219db32544018ea433b664a88025de0576cc9510063bc0aed992a200c76415db32544018ec42bb664a88e65720d74cc9510062f3b2c7992a29cb1c8458f32544016af02b1e64a88025de0570cc95100cba40ae1992a20097581dd9325440127f08bb264a88ea4f211764c951004bbc0aec992a20097b805d932544b52f100bb264a88e65760f744c9510043fc32e8992a20087c865d1325447369d0531a64a8802d5606634c9511ccae43ac6992a29bb1c8458d3254401c98c4b1a64a8802d5e05634c951314b743ec4992a26296c8750932544014d90ca1264a8a6fc310d424c9512d43ec38c9b02a200a5d8319360544014db04326c0a896a9ea0064d81512d43ec3ec7b02a200a3c8458f60544b50fb0fb16c0a88034da0574981510069ac0ae9302a263c3f615d26054401a6ec2ba4c0a88034d885749815100cba40ee8b02a200c6c7299160544014bb06322c0a88029b608645815100636390c8b02a25aa7a8019160544018d8e5b1ac0a88028f211635815100636392c6b02a20197481dc960544732dd0fb92c0a880359e077258151006b240ee4b02a200d6761dc96054401acc83b92c0a88e71b1cb62581512d43e43ac4b02a200d6772dc56054401ac8e5b8ac0a88da5de057318151004bdc3ac0302a200a3d8494b65504010ff0ab96c6a08121f21572d8d410046fc3ac631a82018bc865d253504131e90cb8ca6a08261f21d6554d410058ec28c6a1a8200b958194d435055f878edbaa84a0ab70f1d875509410059ac08eaa128200e2e52d9542504051790eb2a84a080a3720d76cc94100c5e432e999282098f4865c732504139a8c6b8e64a08062f219744c9410146f43ec69928270e8c6350932504032ed0f29aa2a08eacda1253545410059ac24a6a8a8292b668294d51504016cb0529aa2a0803c594d43545410078aa9a86
  | 12 => 0x8031b4877650b511dc9f43c86a16a264c5f315db32d44018ba62bb665a88ee5720d74ccb511dcaec1ee8996a20087f865d132d44090f90cba265a89925b21d424cb511fd3643284996a2a6f0c4350932d44011df04b86c8a880a3b20970d91510046fc3ac631aa200d66215ca5354401acd02b94a6a8803596057294d5132637b0ae529aa23fd67615ca5354401acc82b94a6a88034d9077454d511d61e3a6c8a9aa20187d859da43544131bd073b486a88061f2197590d510061ebaec921aa200e1f6454e43544030fd0dbaa86a88061f2197550d51024ae43aa6a1aa2008bf845cf625440717908b9ec4a88030f950765095104c6f418eca12a2008dd831d942544018dca43b284a88163ea0076509510047cc00eca12a20187e86dd542544032ed03baa84a88061f21975509510249e43aa8a12a20496c8754942544030fb0b3b664a880a37a0e76cc95100c3e432eb992a200c5e7654f32544030fd0dbaa64a898a5b60b754c95100c3e432ea992a239b4e8294d32544092b90ea9a64a893b93189534c9510047dc3ac0302a236977815cf64544032e902b9ec8a8a925de0572d915100cba40ae5b22a20096f825c364544732d904b86c8a88325de0570d915100cba40ae1b22a20497784dc564544092eb09b8ac8a88034dd9371591516869a326e2b22a20097582dc564545a1a6e85b8ac8a898a1f61f64d8d513143ec38c5b1aa200a3d8418b63544014f300316c6a880359a057298d51006b2c0ae531aa264c6f615ca6354401acec2b94c6a8803599057298d51004bbc22e331aa200d57635c663544c5aa8c6b8cc6a898b5590d7198d51004bbc12e331aa262d57325c6635447527d0fba2c6a88034de077458d510069a40ee8b1aa200d3761dd16354401a6c43ba2c6a88eb0f1d36458d513143e43ac8b1aa200c3c74989635440147b08312c6a88030f1d06258d513152f418c4b1aa200a79801896354401a6ee9b8ac6a88034d1d37158d51004bac26e2b1aa200d5763dc563544012eb05b8ac6a880257e1d6318d51005abc0ac631aa20c977815c063544c52bd073b486a88025de057690d510061ebb6c921aa23ab1c8458e4354401c3ec8b1c86a8802d5e056390d51004bbc0ae121aa201974815c243544012eb03bb286a88025de057650d51005aac0cc6a1aa23a95c8758d43544016af02b1a86a8a965de0574d895100cba40ae9b12a20093f845cf625447527908b9ec4a88da5de0573d895100cba40ae7b12a20c977815c362544032e902b86c4a88025d6137158951024bbc16e2b12a20497582dc56254401acec5b8ac4a8b3f5918b715895167eb3216e2b12a20097581dd942544018ece3bb284a88031d60776509510063b20eeca12a200c7621dd942544010fd0d3b284a88025de057650951314af418eca12a20095d831d942
  | 13 => 0xe3632ae529a8400c6e521d95350965878e9b2aa6a100a2fa1b7454d4201c9e43aa8a9a8404a3c865515350801a5ca4bac86a12bf0f9db6590d4256e1f3b0cb21a8400b3581196435087d33b0fb1c86a100387d976390d425d787292a721a84029ac825c243509658d8edb2aa4a100e6ba1373549420053ac0eebb0a8400a75811d761508010ff0ab9ec2a10121f21573d85420043fc2ae1b0a840487c855c361508010fd0fb2ac2a10021fa1c65585420053ac08cbb0284c4c3d7419660508014eb0232cc0a12be1f21b75581420043f43ecab02840087e8719560508014eb0232ac0a12bb0f9d065181420053ac08ca30284008fb8758060508130fd0f2a2cb990269720d745973204d2f418e8b2e6442a5d831d165cc89d4dd043a2cb990029b60874597320053b408e8b2e6400a75811d165cc8014f5003a2cb990029e600745973204d2f41ce2b2e6400a5d839c565cc8010fd0f20acb990021f61e41597320043f43882b2e640087d8710565cc8134bd0620acb990029760c41597322753741082b2e6400a6d8210565cc8014f50020acb990029e60041597320051f424e0b2e6400a3d849c165cc8134bd07382cb9913a9ba0b405973200536c1680b2e6409a5e8310165cc8014bb06202cb990021fa1f10597320043ec3e20b2e640087e8704165cc8010fb0e082cb990028fa1010597320051ec2020b2e6409a5e8304165cc8014bb06082cb9913a9ba08105973200536c1020b2e64028dc835d954cc8130f90eb2aa99900317597735533220c6e43ac8a9e6404a5e8559153cc8132b90eaa2a79900297e195454f323153ac0ceab0e6464a77815d561cc8090fd0bba2c3990021f61774587320243f42ee0b0e640087d85dc161cc8090fd0bba2c1990021f61774583320061eba4a9b2a6400a6d82953654c8090fd0fbaac8990021f60775591320043fc2aecaa264028de86dcd544c8131dd0db92a8990fa3761f6494d320252e42ac929a64029ce825c6534c80539d04b84a6990123721d6454d3204cae43aa8a9a644eb4c82551534c89d69d0bb92a6993335314b7154d325b6c621ee4a1a64ad96e87dd5424c9658d8edbaa849934fc310f7550932576363b0eaa1264d2f0c431d5424c8016cb023aa84990ff1b1d76550932007172a6caa1264038ec87595424c8053590eaa284991c2e320d5450932006a63aee6a126400d4c751cd424c9a37190839a849900273a1e53509321fea63aca6a126470b8c8494d424c8013990ea9a84990ff531d553509321f5c6422a6a126400f0d5454d424c8010ff0aba6c2990121f21574d85320043fc2ae9b02640487c855d3604c80157308086c099002b660c10d813200574c1021b026405cf2605c4604c8011f70eb00c0990033c5c560181320061fa0eeca16a200c3d41dd942d44018de43bb285a8
  | 14 => 0xd851c56294c0155d0838ac529802ab6107158a5304d67418e2b14a651acd831c56294c015d50038ac529802ba6007158a531fd3742c82b14a600a6d859056294c011dd0e20ac5298023b61c4158a531fd3742882b14a600a6d851056294c1359d0620ac529802b360c4158a530057540082b14a600ae9801056294ca34dd0a382c5298029b6147058a5300557420e0b14a600aad841c16294c1359d06382c529946b360c7058a5300573408e0b14a600ae5811c16294c011dd0fa02c5298023b61f4058a5304d6741880b14a600acd831016294c7f4dd0b882c5298029b6171058a530047743820b14a6008ed870416294c7f4dd0a082c5298029b6141058a530055742020b14a600aad840416294c1359d06082c529802b360c1058a533253bc0aeab0ca600a3d859076454cc90f90eaa6c2a98023ee1d60181530051ec24a4b2c86bae4c5254d6290c090fd0bb92c3218021f61772586430262f3aaa7b12860087f855cb6150c090f90ab96c2a18023ee1d60181436ae2ebaec731aa4d4ccd72d8e63548011bf0eb18c6a92be1fe1574d855200c3e42ae1b0aa4af87f855d3605480b970c0ba4c0a90032e5d360981520047dc3ac0302a400a3d8494765508890fb0e30ecaa100297a0c61d95420052ec18c3b2a8400c757118765508014f50030ecaa10029e60061d954257d1ec26e7b2a84b2a6d821cf65508018eee338ecaa12ca8fa1071d954257d1ec20e3b2a8400a5e831c765508014bb0638ecaa12be9ba0871d954259536c10e3b2a8400a7a801c765508014f30038ecaa10021fa1e31d95420043ec3c63b2a840087e870c765508010fb0e18ecaa12ca8fa1031d95420051ec2063b2a84afa6e820c765508014db0418ecaa10029ea0031d95420053cc0063b2a84b2a6d82dc3655095f47b08386caa10021fa1f10d95420043ec3e21b2a840087e8704365508010fb0e086caa12ca8fa1010d95420051ec2021b2a8400a5e8304365508014bb06086caa12be9ba0810d954200536c1021b2a8400d37415c46550801ace42b88caa10031da1971195420069b422e232a8400d35845c4655096b8eec8b88caa10034d10d7119542006b3412e232a8400d65825c465509698eec4b88caa100359d0971195420069b212e232a8400d34425c46550801ac884b88caa1003598c971195420069ba02e232a8400d64205c465508018eae3308caa100297a0c61195420052ec18c232a8400c757118465508014f500308caa10029e600611954257e1e3b6caaa284029ae82dc154508014eb0232ec6a134b1b5c86598d420053ac08cb31a840087e87d9563509a7c3887b2ac6a10021fa1c6558d420053ac08cab1a84adc6e7219463508014eb02328c6a100237e1d6318d420145ec24ed29a84098de839da535095f8dce5b2ca6a10263b2197294d421f
  | 15 => 0x401000c00002000801000403400000400c04800c00000000400400000000400800001400000c00c00400001800001400400001001800403400801c00000000802801001800000800c01c00000c00000400800002400002c00400000000002400000400000400400400000000000000403c01000400400800400000803000000004000400c00001000006c03800c00000400400000800000c00c01c00401c00001800400400000001000000000c00005c00000402c00000001401c02c00400400001c01800800000000000000000400000000c00400003802000c00000000c00402800000004402400000000c00400000000001400001001c00000001000c02401400001000001000800400400800400000001000001001800000001000800000400401c00400000400807c00001000000401802801801c00400800401c00000000000000000000400000000800000800000400000c00000c00406c02c00000c00400400800c01800801000000401c01c00401001400001402c00000400000400400800000c00804c01800002001c01000400000003001800c00001400804000004400000000800c02400400c00005402c00001000000000400000402c01400402801800400000c00400c00c01800003802c00001400400001800000001c01c00400801006400000400400001c00c01400000c01c01800003800801002c00800000c00800000000000c03800001405000000400000000000400800c00800c00401800000c01400000401800403800800000001402801c01001800801001c00000003c01c00401401400c00001002400000401000800400800400000800000800400400c00c01c00001400802000001800400000000000000401400000c00000800800000800001c00800000000400400000400c04c00000000400000002800000001400001800400800c00800404400800800c00000800000000001800400800800001000001002800000800000000801400c00001400000001002800c00000001800801800400000802802800000800000001000001400000c02800000001400400000400000000401401400800400000c01402801800000000001c02401801000000000002400002800000000000400800000000400c00000002401801000000800400800000802c02400802c03400c000000009650ff0ab96c6aa00333d8d7298d5404e6631ae531aa8008df8758c63551650ff0ab96c2aa35f1e5d760981546b65cba6c1302a8008fb8758060550051dd05b82c9298023b60b70592530057540684b14a600ae980d096294c014db0b10ac529826b3a0f7458a5328d66c1ee8b14a609ace839d16294c0159b073a2c529802baa027458a5300574c04e8b14a600a6f855d16294c7f4dd0b38ac5298029b6167158a5328d37428e2b14a600a6
  | 16 => 0x5ca37d2d8800000000000000000000df1d08980f380001eb8000c9c00024c9e3000000000001d40002370001270c684a80270f5400003c19d80006ea7691909c6400061837a80000000001a08000498000000100084c17821c0000818143000000023a56c08689904ba44800000000000000000000636742000000000000024d0c20ffc0001829f2400032700015bc8f469330106585720002d51cec42e000000080c000150000157479e00012389a803470d3cc20b48be24f2f101943382ca1100008b485361af014c8127e4311952016e59e2d400001c06ad0731194ec07f91ff14dc49a4762430bd423e0003e30000000000000118800000019e1bc8000000109207c0000000000b705c62a61b40f74b646d040710040000003ca0fa4000000000073077e7260000a54af055a17406980007ac000195062e0000000000ece2660db8040fc221427d80000002a904c99bc0000003cd03cc4a00002d71e84af429d3f41698000000000000000042a000036c00062d0bc9d84ccc39200001e400000031107680000002999ea4cf66822bf000000000000011f846600000000000000cc1e18270000754353871c3903730dc00000000ca0000000c14811000196000000000006449780ee000000000005f2fa00009000cf2548e2c6640302ef152805a7ea0cc90f072c0000a2800100200007e099c00001537b004c41e0002f80bd0e5204f00014ec75224e000000000017e000000000026f19293080960000e507500000000000d407020000000d0c7f253c000000037c00001880003ee00000000004b6837079010c00048c1c100000000002c78000792000000035000000000000000000000d1800029000000006bc000367000179c4940000e692dc0000000f19ddc10a7892928c4400000004f0d08cdc01700000000001230139de8eb046b10286a0e9e64a0000000a3400025a032c0007ec40400000002d30001acc2aa3790000e742926a13ce8824e165fa2b9900cfe80002a0000000000000002e400055500000007ac11600000000000de19c8de102c000219000000060d01580000000002260b44426340097207104c0001408d48f0c0b33408638ba40001788000e4e0002ea921c0006d42419e6cb6e0000d4800000001001001800400000000000c00c00000400c01005000c00000400802400c00c00c01002800800801800000000000000400000000000800000400400000800000000800000401802001c01400000400000000000400000800000000000000400c00800800000c00400801800000400000c00001001800801c00000400400002401000c01c05000000000000c00800000000000000800401000000000401400000000001400400000401401000000000000c01400002c00400c00000801000c00000000000400
  | 17 => 0x5400000000000000000a9c7d500000000000003231c243e40be2b697cc6e025214f0050b920000000000f445b80608cf8ff85562e3886c7a4131013168cd2200035e8000a560bd0f61fc842039419496ac00000000000000006040000d8400019a37a000102a000000143000061a09683702480002bd96640fa0000001d680000000000000c4000021594e40008283a904240000000b48000b2e724303983000000035c959cb003ee0000a8855c6392f91d2c50e82b00008d06a20002fd80003260003650fa106c1291900000000000238139906837e20308d8ba00003cb8000a2469e2bf91e40000000001db505e0001aa80000000000000000a9a4ea0000f6800052e2a5800000032d0000000000000000000055e000000000000000000000000000000001d7c000000223937c0000000001648d6843d0408000e9234e0ff13390060001f90a905160004118cdc2b42b800000000000000000000d8c0000b98000000000000000091c000000000000000037680000006430000000d640000c10000000000000000000000007c85ec2f40000058f1c8e400532d00006f40002df9e1000080631298900000002901cb40000000000000cd003d3308000a4262b2e79ec8a744ed10582acb16001020080466c0000cd9f6800000028f991c8a876a3910000d346f916c0fdc9a805a00000008d000026c0000b664f10a0145c68e81839597d4d9c6d60a31b540c24d90000be41902d2000000073239117f17043fe000205800000040e21f8000624000000167461400012107880005353fa800059241e04c19d890200004d0988a0e21800010148d444137389640000001759b7026c1a110a90204d80000000f4c08e7871dd02100001a20000000e5800000000000000000000000284000000064000034f18b0000b600000001e9000065316a11740001c40d000005b677833f12c034a4ec00009ec31a62c0001c28e5434d0ae9b140002890001e2c00057737780009480000000000e8a2b5000001000000024c000049036427c800000071f0908dd00000000001c0c1f046108999c0a92069136800000059a0000000d7000002c184c0000002d79c5400000023d8000c8a2cb010115c648000000186cf8435d00000001de08e01b1800fa0415052800085800000006a8000000000000000000017d80007c600000007d47582c13b613c89d22410e79a710721f30000000a5814701c09a412a4a016a96249284193659c608ea0004050b34bc200000018d8000278000000000000000000004ca446000133c00000039e9a7cab800000016084a600000001cc00000010712cc5d80000b580001ce05500014bc9de0000001a0c0000970000558e9c7ae000143cc907d9000000038c0000000000534000000000000000040a0240c6a36a2b100008ac00039420340
  | 18 => 0xfa000204c0002390019cc897000000020004a87cd00000004644ab00014f48e67370448a940a40570b3209400037700019a423c4ff0249d7027a18b3ff96f8bee00000000005d401c09e00001600001d286f4aea00000013f420e0000e980008ee0000001dfcf3c4fe3f5974c00014f0000000a9e3f53f982450546d30001a54000000072000000037b00018a0b8c000300816c33c00000000005e669241700001d637600017605220001660000c541022499c0000050a12b8000d4c000325800000000038787704a2000000089000000024a9d1800000025d1e14e0a7a500000005581d82a19b941840001188000a4c00001d00002da5bc000000039200000000005da704000000000000000013340003280000000fe264c29c00006b84b503a0b410085ca000000000000019786b800006332f00003be51e0e180205ae78e1778d80db20512570228dc80ac08794d0bba36209d0db001c82400003b400059133984a0d0045234382c812c6cf13580000006b7167207800000000000a4a3a0000000aec0003b900000000000003500000754000271800000044e24e800000076e33e01400000a70001c04000000000088400000000001c80000002b20000e0463000004d45561610719cc40000002d680009881b40000ab40004bf2988000e1c00000015f000000012f10a00000000000000a4472f3b319340b200021d9f7800077c15907042a25cb1c795780d458a1d81b0071842300000000000001160000000579000000000068c00000000000000fe01e80005ac00010947786751ef9380f5e5d60000c74f4c2aa1d7058851a5950000a08000436000027c45c1dd000000000000040d114cc1c1a40001dc8fbe69400001902b6000000000012400000019c49a000000018dc7d62161d59aa48680002aa0ad0094000000000000045a1fe15c800011000000001427142990c7c00056500000001fe00000010a4fce5ce0000e40000000083101000040d00000000005052ca060476c7ef1afa0c47100000001b600000001f61e0498c0ec0000c4000000031c05b00006aa08900009ae000000000000022940288940000002081b341707b90f31840c244310001c410580d3335800066609d3eb00000840003109b8400000000000005ce00000000006a82980d8087865c7e001b828066815c35280004180003138000000000000164c00039330b94600007d400009cca120000000f2c0000000681a64f500000000af0f7c0000bf97fc8800003fb856000028e000165832a5d72b1800060413e00000000000000000ac088a5a515b8c7874c39e2ac04e03e204d000000025656a000000000000023689d0506000208800000040a1de80000000003e8800000000011e00000000001138f7000000038d13d87640000f68000c1656b000000066a3630
  | 19 => 0xec800005300000000180001e9c9b61c50e886ac4dc7b000000002e4780000132027210a08282b42e23d01588000d7800023e9510bcc0000dd00009ea5f910c80000000002949378000000000000095473900012c40000003af000000008f3570afc0007dc1ad000000034c000000000046c0cb940c0002f80000000ff40e11bf85bcee26ab00012b000073500012580006d213a93ac1ae65d388875800000f3a993d099208d2720f9000032b3e28d58a8c59f3170ed0db6202111913ccf418a057151ceaa63a2e60e003c21b339e19906f800034800000007c0000000000055227b91f00005270aa00009c41d22d005489a607f40580002ec46f000000000059b00003a400000004d948c51e0002f21be80000da00000000000000889954bb63481fa15a05202c628c97640d06400dd9210c3c1a71f803948aa6ff0000000000738000042021c07b08d83607620c0000103c6600000820e680002b600000000000002a89afcac24c018e000030a7961cd80003ae3ed00014380183c00001b1c1d07bc18a800000030d00020407cc5c3298000083063c35f000047e0000000000f545d400000004c60002bb00000000000000ba474e28a000000072a00031d95085bc48f0109710cf22800001e4820263121697708260113cc80a80000002770000dc6629000000000011532f95b891218001118c8c660003a406d400000016b0000000000000000017634400000000004640000000244000000000007200034d80000005b50001d1c000510000010499877e1781458c7c6052110bf00003e70000000000000172154c00000002280000000d938b1ed068c3ff000000068a1b100000000000000980464f9600000000f8a482c32d39dd000010c000000000054c1c203ece6c5c22458000ec43bb3a19744cae0b10000000000000000000000008b000144c40e2e00fe800025e6141fd09f49640000000000dba00027c019c3ec1883f4800074406e0000ce06de21f00003480d600016f9edc45e76b0f508ec47a3f33a61b7805e29c1ce0844d161d00689a5cbd27dd1c4877830c000225051000000026e8000dd883000d8a4c0000003a0000029a00000007d03646f033119940001e90000000d4822b3b983f42ee1650ca1e345c432a25b1bf06587c30b70b6400000011694182e00000000000cb813700018f40000000002088a500000000edca2a0002da146c23447127809183aa000149000102400000000005f429f14b82200007790621ed8b1c00003b9f5c14400019888e001a000000000000000000b0000972093000000045028500010580007412db1bb800000000000000000003899bf8000132064968800067d0261ed4ee03c437d82a417e6df08591249c23b80220c4c51000006280005ba1871f08738fb05080000a58df00000000000
  | 20 => 0x40000000000000c220002349944000000000000000067f37320080b821a1b7129c0001ac00016e873000028a0000d5e200000000000012600000007ec4d50000000abe0000300000ea205e0001aa094c00000013a000038d14c96600000a42b88ea06ae54120e8000bc60000be82d433a25c1c38b683800fe3b297b0e183d912f90840000000000000d6c0000000985042000000143415e00006180010648274101df400075600000005cc000000000000000000000007f60000c90e14f9e0000000e8c0005e800000002b20001ec187c0000002b81e5430845e2fe800094a00011a93e8d1000000000000000cd29f1ee80005573e61e8085e27a00000001ea4dc25f12f44e481b00018240000003f11cb8c1e606000000003e66d0f40d6c0003a40001ba800002800002081282941da9c1800000000000000006c11e28ff40000800001bc40000000190000cce43502b000000000000015d0c103c62e0000004600017e91401ba00041a80006da66a3f70bd800078a0000000f2248d13814000005111e6a06400000000000003720001d690dc00000000000000660000e5905cd1c0001b88000e4a63f2490c380005f11040b0040c0000001d6400012709513f00001fa00012200006601c300000000003a68000000000000156ced00002799170b0243a3f313940000001e51fec00030114d9134fec000000054cf4649733c01bc00000030a8000d46000000142c2d45830000c980004510000e0c2e800026900d000014e07a09dc9760003c80000eec7bb3d9800024a47f09f95a46b258715000009ce7501340fe0f1010025790e47b67821420aa0fb600041487ec00073438e000033000000011e00000000f70000c8427e11509fc47478f20a177c0004cb34781f80003180000af4000708122096080446000011b8fa43e21b59cfc8660001519e0c0000003741f4cf900b4162000085c5a90af03a884e62638e8000574000000063d0666960df800000067712b1a2898a00000000000005c81021f046282493278000b4221d00001c08b656026507bc7144c730e0c18d621641f00bfc00046700016f4d3a41c2fb02d808c13b4039ce8000000000000024006c0001208a385662ed1ff4fca6f70b181e003277526d0af89443af1a5800059e0001628da4d0c000159985879c4630171ad460e45808b800000000007881d8ce45cd03100b00006c335115f40246e0000154000044300000010121bc0000000e3c0e232489682381e50af96341180000000000d900003bd9dbc000000389000074035810e0000b0c000000031c0006f30000fbc41475b19181982986e90a5996400049b1b3092c06a12c21f1b44f8e00002e9a140002862f282e8b0a3e5000060cbfc8381ea0708e46000000001883600009a00000900003620000d8449e2f5198c7bc189
  | 21 => 0x58e80c0000cf49142c8120000082400000017144e2000000112cca049f0550954d924423f6935844403b29f908033e0000518c0cb100070000a9c0007bd35d083486005400000000003c100014b4cac4c100003184604a30f000fcb086cc33612404ec71b1d99ac00000f01878c887e26ac3c9930ca0807c2a285f0f7071700000008b27301cb9d7400000000014083b62c2000000102e4ad20d00006001b613c8460cb65ef0438f4429448511300000005ee099800000039f000000000007136b9c1c000000004800079800019d0000fc6466000000000000000014a800031a2f6907c19c000317800000000005e00003d60000ba840c0000000001a1061258c24890907841f91790f2069474a0c60580f880d60d69a24f5600018c91101aa08637100000000000000e380004a10001948c3a5b90000000ab20003fc03d8228000346800000000039005a0dfa0000001f38fe0000000009000000000000000000003b180001ee245000000000000000000000002f73221eb45c27330b38ef85426eb0f380000000001460000bf000000000000000002ce00000006740000764618365182000101e0003e50d24bf80000000000000698000009447c00a1f50000f3e000185855c5dc000000020c9a281d30180006e45902f58000b761f80001cf8a0227c000000067e00036d17800000000a0890ce424740001ec403c00000007900000003208d4c0000000001d10c326bb0001efc0007570f8000000001d20381b
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x801835746046598142006191d9811d5424c801b044360475509320055164475dcd424c801545911d47350932384c32615454d424c89d50c9755153509320060d604741896354401838746006258d5100607611831d9425440103d9810c76509510050d644431d942544014399010c765095100519646321d94254567865818c876509510060d611811d942544018568360476509510061560d811d9425440186582604765095100709505211d9425440187181a0076509510061660d801d942544018698260076509510061c605801d9425440143591d0076509513f60d607401d9425440144d93080765095100519644201d94254401076981d97150951005836506258d3254401a0c84189634c951005926406258d3254401a0c43219424c9510041b66072191605440184d831c864581510061960472191605440182c841c963581510060d1d9811d542504013279260374545411d60d21b745cd5150475314985cd43545411d54565c6350d51504013159321d4254541004cc640875095150475324985c94254541005196447558942cc401435911d7645093100c6525d844c9414c4e1c84765093250531006191d9811d5424849dc447654d32545210241da638759151484013279460f7254521004d164c8750951484013619021d42545211ccc92617450951484733269890d42545211ccd164f844c951484011649761132545211fd1925d644c95148473646969cd32545211ccd1261734c95148597c44765cd3254521635c1251734c9514847386486dc97054521006255cd811cd6494001834766047550940006c8081811d54250001531911d770509400054c644751c142500019282021d42545400054664c745c15150001529921d170545400064a208745c1515007563190d8951505401d54ca5e80545415017b9308760151505401d58c25980545415018572092601515054012c4d2617454521500573189854d435414015cca2615250950500bf52897549425414015ccc261515055050001465911d56250b300050d64475591428c0034349759151505300066221d424c9404c0bfa88865093250130387221d9424c9404c1b17089550932501300048d644855c9640c0012659121574588300041d64487595420c001435911d564508300051964475589420c001075972154258430007065cd70593510c001c49735c162d4430007145cd70587510c001867766047550a201d589e5942545418800123498591515052000d1925d6354521480736609660151485201ccd8661511c1214809dc487654d32541200050d644755914284001465911d7625091004d2525d6450d314400129594219324c51000478648874c540440019908750d31501102fea82194248540440031d0985d1314c11000d34259734c520440031e0985d12148110
  | 1 => 0xac00000009800001000000000019400003b870003f198000000230008417288000000000dce46d00124648400000002400000002f42800d8000000000000000c00360000062002b8000080080000055438000012000000000040003c861c8000076108000000001143038001040000169f44a003c828e60000000c600009b8b8003d8000000000009613001c40a0b001e00000110f8980031000a4000a0641e003d07c1c530008c220000000000000168cc3b031f84e0000000527f2c000004400054802c23800b63d00000740706000e0000492800004086800002b164006900000000027000000000000be482193c9a7c351803a611a1783616280c0045d1a810006f2a000000000000ea003580000000020cce00411a0002e00000780d1500050003a190050100400000002c06000000806000200408000000000010000c0000010401400028000001000040003010000000000102a000044d660435c465508015269210d71195420054c640435c4655080156290d09711954200545a4e425c4655080143696109711954200519a58425c46550801526948c9711954200549a4b405c4655080116598081711954200549a50205c4655080154593081711954200615a0d711846550801855835c461195420061c5c6801846550801871716006119542006195c9811966350801836766046590d4269e0761f65d8e4350
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x140281c0680c00258009c680088b0000004080002305a910d811d5424c801580d0086c08eaa126400c8164484189634c95100641108c80c4b1a64a880220da910c865093254401502d088643284992a200a8268043219424c95100405b52420e4b1ac0a8802321a9081811d54250001580d1840c08eaa128000a4268c2021d4254540005243421010ea12a2a0002129a9208745c15150001884c99043a2e0a8a8000c48644821d17054540
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x4
  | 10 => 0x124b
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x98a
  | 14 => 0x98d
  | 15 => 0x98e
  | 16 => 0x128a
  | 17 => 0x128d
  | 18 => 0x128e
  | 19 => 0xca
  | 20 => 0xcb
  | 21 => 0xcd
  | 22 => 0xce
  | 23 => 0x9ca
  | 24 => 0x9cb
  | 25 => 0x9cd
  | 26 => 0x9ce
  | 27 => 0x12ca
  | 28 => 0x12cb
  | 29 => 0x12cd
  | 30 => 0x12ce
  | 31 => 0x168a
  | 32 => 0x168b
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa0a
  | 36 => 0xa0b
  | 37 => 0xa0e
  | 38 => 0x130b
  | 39 => 0x130a
  | 40 => 0x130e
  | 41 => 0xa4a
  | 42 => 0xa4b
  | 43 => 0xa4d
  | 44 => 0x134a
  | 45 => 0x134b
  | 46 => 0x134d
  | 47 => 0xb0d
  | 48 => 0xb0e
  | 49 => 0xb4b
  | 50 => 0xb4d
  | 51 => 0xb4e
  | 52 => 0x16cb
  | 53 => 0x16cd
  | 54 => 0x16ce
  | 55 => 0xb8b
  | 56 => 0xb8e
  | 57 => 0xbcb
  | 58 => 0xbcd
  | 59 => 0x19cb
  | 60 => 0x19cd
  | 61 => 0xcca
  | 62 => 0xccd
  | 63 => 0xcce
  | 64 => 0x170a
  | 65 => 0x170d
  | 66 => 0x170e
  | 67 => 0xd0a
  | 68 => 0xd0e
  | 69 => 0xd4a
  | 70 => 0xd4d
  | 71 => 0xe8a
  | 72 => 0xe8b
  | 73 => 0xe8e
  | 74 => 0x178a
  | 75 => 0x178b
  | 76 => 0x178e
  | 77 => 0xeca
  | 78 => 0xecb
  | 79 => 0xecd
  | 80 => 0x17ca
  | 81 => 0x17cb
  | 82 => 0x17cd
  | 83 => 0x104a
  | 84 => 0x104b
  | 85 => 0x8a
  | 86 => 0xa0956
  | 87 => 0x10a
  | 88 => 0x150a
  | 89 => 0x180a
  | 90 => 0xbc9
  | 91 => 0x198a
  | 92 => 0x4b
  | 93 => 0xa1256
  | 94 => 0x4d
  | 95 => 0xd09
  | 96 => 0xa4995
  | 97 => 0x14b
  | 98 => 0xbcc
  | 99 => 0x19c9
  | 100 => 0x19cc
  | 101 => 0x138b
  | 102 => 0xcc995
  | 103 => 0x180b
  | 104 => 0x1609
  | 105 => 0x198b
  | 106 => 0xa5295
  | 107 => 0x8e
  | 108 => 0xa09d6
  | 109 => 0xcc9d6
  | 110 => 0xa12d6
  | 111 => 0xcd696
  | 112 => 0xd0c
  | 113 => 0x14d
  | 114 => 0xb8a13
  | 115 => 0xbca13
  | 116 => 0x19ca13
  | 117 => 0x138d
  | 118 => 0x150d
  | 119 => 0xe8a13
  | 120 => 0x198d
  | 121 => 0x10e
  | 122 => 0xbd313
  | 123 => 0x19d313
  | 124 => 0x138e
  | 125 => 0x150e
  | 126 => 0x180e
  | 127 => 0xbcb15
  | 128 => 0xccb15
  | 129 => 0x15ca
  | 130 => 0x144b
  | 131 => 0x188a
  | 132 => 0x160a
  | 133 => 0x184b
  | 134 => 0x148b
  | 135 => 0x1a0a
  | 136 => 0x164a
  | 137 => 0x14cb
  | 138 => 0xccb56
  | 139 => 0x3ca
  | 140 => 0x58a
  | 141 => 0x18ca
  | 142 => 0x1a4a
  | 143 => 0xcd6d6
  | 144 => 0x24b
  | 145 => 0x24d
  | 146 => 0xbcb93
  | 147 => 0x154d
  | 148 => 0x140d
  | 149 => 0x144d
  | 150 => 0x1a8a
  | 151 => 0x194a
  | 152 => 0x14cd
  | 153 => 0x14a
  | 154 => 0x4e
  | 155 => 0xccbd5
  | 156 => 0x170bd5
  | 157 => 0x140e
  | 158 => 0x44a
  | 159 => 0x5ca
  | 160 => 0x24e
  | 161 => 0x144e
  | 162 => 0x148e
  | 163 => 0x74a
  | 164 => 0x154e
  | 165 => 0x184e
  | 166 => 0xcd9d5
  | 167 => 0x1719d5
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
  | 189 => 0x94a16
  | 190 => 0x124a16
  | 191 => 0x128a55
  | 192 => 0x12ca16
  | 193 => 0x168cd6
  | 194 => 0xbcb8a1b
  | 195 => 0xcca16
  | 196 => 0x74a13
  | 197 => 0x194a13
  | 198 => 0xccbcb1d
  | 199 => 0xb0bd5
  | 200 => 0xb8bd3
  | 201 => 0x148bd3
  | 202 => 0x28e
  | 203 => 0xb4cd6
  | 204 => 0x16ccd6
  | 205 => 0x140bd5
  | 206 => 0x20e
  | 207 => 0x19cbd3
  | 208 => 0x19cbd5
  | 209 => 0x58b
  | 210 => 0x44cd5
  | 211 => 0x164cd5
  | 212 => 0x15ccd6
  | 213 => 0x1a4ed3
  | 214 => 0x180a16
  | 215 => 0x198a55
  | 216 => 0xcca09de
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
  | 6 => packedAt gbK6 (387148+((h/2450+packedAt gbK6 (352848+(h % 2450)*14) 14) % 9704)*14) 14
  | 5 => packedAt gbK5 (132678+((h/702+packedAt gbK5 (124254+(h % 702)*12) 12) % 3363)*13) 13
  | 4 => packedAt gbK4 (9925+((h/45+packedAt gbK4 (9520+(h % 45)*9) 9) % 261)*9) 9
  | 3 => packedAt gbK3 (1240+((h/5+packedAt gbK3 (1215+(h % 5)*5) 5) % 26)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe38f8e07388e0c7e11f87f87fc606991c4cf
  | 1 => 0x703f1f007c0f00f8ffe3f83f83c8191827b33
  | 2 => 0x7fc01fff8ff000ff01fc003ffc1061e638c3c
  | 3 => 0x7fffe0000fffff0001ffffc000207e07c0fc0
  | 4 => 0xf800000000ffffffffe000000003f8007ff000
  | 5 => 0xffffffffff000000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x5040828241108244124048308518602890c045
  | 1 => 0x82011110820010008502120140208091001112
  | 2 => 0x2124002430e900a92094810a32810202630c28
  | 3 => 0x5aa2401104a25200019254810820740240e80
  | 4 => 0x3000000020b4c8ce48c00010230928005be000
  | 5 => 0xc6d3c9c9c4000100010006604432d5fd800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffef8ffeceee8fffffef8ffeceee8fffffef8ffeceee8fffffef8ffeceee8fffffef8ffeceee8fffffef8ffeceee8fffffef8ffeceee8fffffef8ffeceee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27995
namespace PEqualNP.Outside.L_meta_27995
open PEqualNP.Outside.L_meta_27995.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 4 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 60 := (concat bs1_4_0 bs1_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 40 := (concat bs1_5_0 bs1_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 4, 36)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 3 zero,inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 4 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffffffffefaffffffffffeceee8fffffefafffffefafffffef8ffeceee8fffffffffffffefaffffffffffeceee8fffffefafffffefafffffef8ffeceee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,32,160)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27995.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[7,0]⟩,⟨.or,[1,8]⟩,⟨.or,[5,8]⟩,⟨.or,[6,9]⟩,⟨.or,[5,6]⟩,⟨.and,[4,1]⟩,⟨.and,[7,11]⟩,⟨.and,[10,13]⟩,⟨.and,[3,12]⟩,⟨.or,[14,15]⟩,⟨.or,[18,16]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27995

open PEqualNP.Outside.L_meta_27995 in
theorem PEqualNP.Outside.L_meta_27995 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
