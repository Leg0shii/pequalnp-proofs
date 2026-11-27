import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27929.Model
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


end PEqualNP.Outside.L_meta_27929.Model

namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
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

def SBf (j : Nat) : Nat := [5, 6, 8, 7, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_27929

namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffc3fe1fffc3c38703fff87e0fffe19f39f
  | 2 => 0xf07ffc3fff87fc03f803c3ff8fff03f213cf3
  | 3 => 0xff87ffc01ff87ffc0003fc3ff00ffc1c1cf1c
  | 4 => 0xf0007ffffe0007ffffffc003ffff0001fe0fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x11220491025000141812884501241518185185
  | 2 => 0xa291490a5084c54224841628c852a0a5212432
  | 3 => 0xc4555228d5244eea440926a2d20aca85c18e18
  | 4 => 0x6220808031108c89218003248c03084a0bc0
  | 5 => 0x8884433319c66733364e3b3040108c31b5f000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0ffffccc0fcf0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3000270192052ca040044600000020ee42ed42ee32ed32bf41f641bd41f541b541ef21ed21ee20ec20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x5012020400030050000d0200058007001e3001c230100000196aa46565518ca6aa920e990941d2a1283a6525074aa4a0e98c941d299283a541c874a8290e95062096aa0414d53082caa2106950420
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x10c20a158e5250625658c9418959541083055350420
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (228+((h/4+packedAt s1K4 (208+(h % 4)*5) 5) % 20)*5) 5
  | 3 => packedAt s1K3 (462+((h/5+packedAt s1K3 (432+(h % 5)*6) 6) % 33)*5) 5
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xc3c3ffffc7f0ffff0c21c3fffc3f0fff81f27f
  | 2 => 0xfc03c387f8ff1e1ff03e03878fc7f3c3c94d93
  | 3 => 0x3fc07ff001fe1ffc003f80ff803fc718e1c
  | 4 => 0xfffc0007ffffe001fffffc000ffffc007e0fe0
  | 5 => 0xfffffff800000001fffffffff00000007ff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x40044000400100000000400880090040001025
  | 2 => 0x8928a94c92a82931523211c52642a28b494492
  | 3 => 0x3ab11b55266a5513be502ad44e906b39718e18
  | 4 => 0x10801022004004442484880009244810120b40
  | 5 => 0x23222244348c9999cb393366620082226de000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xffffaaaafafaaaa0ffffaaaafafaaaa0ffffaaaafafaaaa0ffffaaaafafaaaa0ffffaaaafafaaaa0ffffaaaafafaaaa0ffffaaaafafaaaa0ffffaaaafafaaaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa5185f94630bea8c617e508c3f481187e50230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3be6298774c530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a90617e510c3eca2185d94430bea8861f5510c2eaa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec82887d50510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a16f90d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ee21e657e51ccbeca3995d94732bea8e65f551ccaeaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83be43d077887a0df94b41f7296836e52d06faa5a0fb54b41b6a9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41bf294837d52906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f7d0f31ee21e637e52cc7dca598db94b31bea9663ed52cc6daa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31bf294637d528c6fca318fd90631faa0c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a263df434c7b88698dfd4931be29263df324c7ba6498fd90531faa0a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fd90721faa0e43f631c87ea6390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887dc8510fb50a21f719443ed32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f721043ed42087dc6410fb4c821bf28843f641087ea8210fd8c421fa98843ef21087ec4210fb48421fa90843e521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9
  | 2 => 0x7a4905983606510a474389d4158600000460de8c151a1c0000000000014c1101e17c0008cc840954ce5345083507e75cf993e53c8242da0b44c1553c8945323d93f1e32a6a18a4175224718cb82414422c91a63414808002a015c498a3a204884f46d81d2a842c319210002207d2a94d4a693a00052619c0029b11a60942a83190000001872d63900000053e33d3623c138a451b15928c8b0149680dc37d2c1f22184644925f52c000002770000b05f00026c7551d17a22e1ec2c9220fc38c6b0e9118869410ee3303a02724d2dc7ad228e70206a8efa56208184ae0050c00000000031e11cc21c300007cca8f23b200054a921bc418170003146e40020103053000000442000002083820009f8000007a8109ee3667b40013c000930000000001ccfb85a0006709017b05e000fa0533c8000db911000000000c9000864070004501fca81e80003e0b92a52001146621b202a74000000002f5301ca1d8680d69a902a848a91a51ca0700022d096630568000009747b800452814449d854c000ad1740006e0702380007f4bc8cb1ea794f313a0ec1acdf9994823006909314821c208001a6001342473f6129078ff47c47c7e2401f61f5380004cc9ad4a9e9050508d600b000860201f1000000000001726687f1342602bc5526938a634001cf1ae6f13ea3d1820140204c0104000008060580e034010041a0001003c0300001000000ec010500003c05000010d821010030080a01c01000050540b0380400476024230000102c2704c020081c058120000e0000f020080240008c050000306414004020640700000000010000001421004080001200c010141d0081e0040802000018010000001c080741407c1201400004000140e0140d08419000180ac05008140000000004004040281903800014030500300c0a0080c04c000101008c3901800000120080103491004000700c004170200001003004040040000400000020080d048010000201007000000c018018040001701c0301c03008180000402000000080380a0000e00009000000a80303c00000230100505405018000241700000006fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443fb28887765110efaa221fd54443baa88877e5010ff4a021de94043bea8087f95010ef2a021df94f42bea9e85be43d0b7887a15f94742fb28e857651d0afaa3a17d54742baa8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857
  | 3 => 0xf38250000006387a348338000000007f8000004f04400000046e3682b92e4de94079a2f29640c0f09931c294ee85f01a30c939572141e034a7c4c83144807216a0dc9ca8a30a2384f8740002001a0072e23888722b3f8000c194f13c0e9152a80001712d0003a400011a840a406800232000618cf032114310000000000594380032620cb10140006207519452e93800000000000ab18136a13ce116d2fc71c412550541f0dd196500204101910143ace58061a87fc709bd1f28e41821f04c5907311526a4588d9ef42895cf61145286c483a1e3e028d4e10535c9ed0b84d2ca3605900418c03ca50333ac648352594fe2609680000009d24a3125e4cce024a4ca88d310000007810815f39010d399be06c0003315d000000d581700078400000000158bb1f82e6944cf9fa16c9b5031af21e948fa8000a8000001093880ec0024643a328040004dc6ec001db2ce000681a100093d088000000313916a000000d189d0a01dcd90ef0240b506000000088e71b600006501a6141c1453a8014841c00000000058cb0864176001110001a277929a2407a2e13b0cd51a8fd4c13712c5045e1134b64c8bf98b24a524be8a04e28001f0023121242e92c256835129553c4510049b40004e1458003f24a000000000478489310000c4cd8002b6a90001d11fa8d45f8d51da734001da476724ac1510d04702f16c0f24687809a51289cb812a2c00e4869d316800c00000166000158003988b83695e0365e0539a740e460cea434b85dcd424b4bc515470001baa85478b73440007a2882de0e06c9f62861d50a94e2522e8420dc2804082113b468640ee08f1621889228136025c430a8426309460ab54e3c4099690b08100004c544120089d034c26c580005208592a2
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x514823d64145209798c514825d6314520cd99051483356414520d598c51483556314520d990851483654214520d98c851483653214520dc580514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020b9185200836551480209ed95200837151480209798f54c425d63d53109b98a54c426d62953108f99353c423d64d4f109b98a53c426d6294f108f99052c423d6414b109798c52c425d6314b10b558e41c42b5648c710d914921c425f63552109718d548425e63152109758c548426e62152109b588548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e6414a108f590528425e6314a109758c52843675208610bc58021843e02188210bc18520843e321482109b98a544426d629511097d8d544425c63551109bd89544426c62551109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109b98a524427761549108f990524423d64149109798c524425d63149109b994524432e6414910cb590524434e6314910d358c52443656114910da58052442d56390510d914a41442746550510d914941442b5648c510d914a3144274654c510d914931442766588510d914a21442746548510d914921443685288110f888620442786548110f8485204436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109e980520427565c8410cd553210435553c8410d954b21042756508410cd55021043555308410d954821042f16008410cd553100435553c4010d954b10042796584010da54a10042776544010cd55110043555344010b9189100436552440109ed9510043695244010
  | 1 => 0x873a5454021ce551500875a5354021d654d50087e12154021da90950087694254021da8c950087693254021dc90550087714154021dc8c550087713154021dac8550087722154021da48550087712154021d8485500865e6394b409758e52d02b561d0b409798e51d025d6394740ab58b41d02b96010e409dd8552902746154a409bd89519026c62546409b988535026d6214d409d98453502756114d40d3988535034d6214d40d598453503556114d40d6580535023e65d0d40c714f435031c5350d40c714f42502b561d0940c714d425031c53d0540ab58b415031c5350540c714e405023d6590c40c754e431031d5310c40ae580431034e5394840d354e521034e5354840d354d521032e4354840cb10d52103565394440d554e51103665294440d954a51103565354440d554d51103665254440d954951103364354440cd10d511031d53d0040cb54b401033551d0040d654e401023f6550040a718d401031d5350040cb549401033551500409ed95401035953500409b98854cc26d62153309d98454cc2756115330c715143cc23e6494b308f59252cc2d561ccb308f99251cc23d6494730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b6580438c2776154a309d185528c26f62546309b189518c3984390230b618d408c39b43502308f992544c25f63551309b988544c26d62151309d984544c27561151308f994544c31d6315130cb988544c32d6215130cd984544c3356115130ce580544c25e6590d30c7152434c25c6550d30c7151434c31c54cc930b5587324c31c544c930c7153314c2cd62cc530c7151314c3385490130e690e404c2786550130e650d404c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c63550308f990540c25e63150309b988540c26d62150309d984540c27561150309e980540c25d65d0c30c7553430c25d6510c30c7550430c2d96010c30cb952520c32d5494830cb951520c32d5454830d3d0d520c34c4354830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430c7553300c34d52cc030d5547300c339548c03097d95300c29c644c030c7551300c34d524c030d5545300c27b654c030ce551300c25e63d53209758f54c827661953209d58654c823e64d4f208f59353c82766194f209d58653c82cd6390b20ab59232c825f63552209718d548825e63152209758c548827661152209d584548823f6454e208f191538823e6414e208f59053882766114e209d58453882e960086209d9865448275619512097d8d544825c63551209dd85544827461551209d98653482756194d208fd91534823c6454d209dd8553482746154d20b358e424826c6550920ab592324826c654c9208f99
  | 2 => 0x6494732cd59251ccb574354732d510d51cca7661952329d586548cb2e6295232cd986548cb356195232cb951428cb1e54cca32b9987328ca7661951329d586544ca5e65d0d32c7550434cace6210d32b5584434cad96010d32b398e424ca6c6550932e310d424cae661cc932a7992324ca3e64141328f590504ca7661141329d584504ca5e63d50329b988540ca7661150329d584540ca7a60150329e580540ca3e64948328f592520ca5f654c8329bd95320cb1d5310f41ab58843d06b96010f419798e52d065d6394b41d398e52d074d6394b41cb90d52d072c4354b41cb94942d066e6294e419b58a539074e6294e41d358a53907566194e41c794f41906e662d0641ab58843506b66110d41ae58043506b661d0941b998b415069e63905419798c505065d63141419b988505066d62141418fd95411067765504419b98b54cc66d62d53319b98854cc66d62153319e98054cc6796015331c755043cc6cd6210f31b658043cc63e6494b318f59252cc72e6494b31cb59252cc74f4354b31d310d52cc74e524cb319b98a548c66d6295231cb98a548c72d6295231cd986548c7365450631c7953318c6e662cc6319b98a544c66d629513197997434c71d5410d31b3588434c6d66110d31b6580434c6d661cc931b598e414c6746550531e510d414c6e662cc531a7992314c63e64141318f590504c66e62141319b588504c65e63d50319b988540c66d62150319d984540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c65e63d53219758f54c863e64d4f218f59353c86d56390721ad59231c865e63d52219758f548863e64d4e218f59353886cd6390a21ab592328865e63d51219758f544866d62951219d586544863e64d4d218f593534866d6294d219d586534863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d6595021cb98a540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a53087566194c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866d6590821b358e420874d5390821b9586420872e5450821d354d420866d658c821ab592320872d548c821b9586320872d544c821d394d32086756590421b558e41087555390421b958a41087365450421d554d41087a542504219d59631086b5648c421cd55231086e5628c421cd5513108756534c421f14c931086e562884219bd9521086776548421b9d9521087676548421b9d9121086e56448421e995121087a55448421b9d8d21086e56348421f194d21087c55348421b9181210873a5494021ce552500875a5394021d654e50087e12194021d9485500
  | 3 => 0x68b080a0947c001491d92be7095d80036290ca1a08000000020000008787328a59c0013e8c9000000e525c000000509a9000460001bf0d4000001d52c4000000e1000a6d3a8000008ec0016f0784100005239a17c00071000000b380035e000a226a0300000025923636c0000007e6b55b042000834002a5000a04248002d2328499e70005195c1143ba0000027b45e0015a1ed3f6000001e900000054800106974002701dc0a4001bd53c500b09861e0000a380000028d1a81055c44485800000710001f70d26584e840516a242ca655922500000058000168ac214e3ac9e9fa45a9d0f41f50567e0330770000005827c4bea691401b10e0011ea97000a4c0000029e170981ae0c294cdb00004aa5946211182778001a54de001650fb1bc9c4000dc4e60009f19b07c00000000000838000d7000000001bc3dc0b0ee000002688008008000060200180600e000018020000000380000200c018000000000080a00000000004000000008000000080000500001406803000000030020040680180000200800803002000040030040000400000001404801000004018040000780380700000c0000f0020480180000400400002002000008070020080000900e00c020020000400000700000c028000020000000100600c008000000000100800003c000000000180380800c0080000100200003000002000000000000040480000000000005000030048000000040000b00200c05802006000000030080040180101c000008030000000000300800400000004004000020200040000400c02c0200000e00c008090000000500301201401803000034010070000200080700000c0080000a004028040040200600000601002004000000008020020040000001e01802806004000000020040027661d49439d5875250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9f6150c43a71814310f8d4394843e350d5210f954394443d994a5110f655294443e550d5110f665254443d95495110f994394043da94a5010f695294043dc9465010f715194043c750d5010f994354043da9495010f695254043dc9455010f715154043ced0d5010f5a4354043ce50d5010f594354043c650d5010f1d5310f42ad58443d0ab96010f429798e51d0a5d6394742d598e51d0b556394742cd90d51d0b3443547429d9865390a756194e42d398a5390b566194e42d55865390b1e53d0a42b99874290aae6210d42ad5844350ab96010d42b99874250a9e63909429798c5050a5d63141429d9845050a7561141428fd954210a6f65508429d98754cca7561d53329d98454cca7561153329e98054cca796015332c755043ccad56110f32b658043cca3e64947328f59251ccb36
  | 4 => 0x4da000002ba00045c3a9cb210638dd19f112530b29e50f89dc5c82043e000001060f2000000001804d4be8000005808d0b8046000b989b5560000012d1de554289280dc65c1c8000009b05588e1eeb20b6a053a64580019c0146084300058a000000003340012588c50a0011a000000001438d633227ca0a8f00000067800498000f88272f203c35a7f25c13d6a2272269e0b624a17c3fd1c11e0000010c00000075000000376000ed0003a440d14800000000001a043601400102522001320000000000000000037c891eb0004889200000065168000000000001105086c81229547200109121318aa9679e21d02d07e000316000001510001289916e000000000441c6260000f342e0bc802a30f081c240950000006c9b90003d800000000034000000000000001a0000000017f000674481050ba2290a1494605c1668f40d0348000e521a00000000290a98e41be0009f859183004534000003b6aa4001260009152693b1c06d4000000c00013c91d4ce000000fe5980d8f1a0f3faa894305011a2688aa8854042946942000374c80c239c2215f20c4b00d0cf18f4e4000d09c70823112a26e0000f51b1e43bea74001501f4354ae000000000002a40005140005313c00000000000000000000009380a1f30006dc928004040000018115c000e604d0009415792319c704000000000000015d000000000001f20000015600049d4fa44408298790001fa0b44e09231031400184402918eb8000008cc001660fc64c001330603600018d0002f15b8560002a0230d43248e8000002d490400000000000a52c6000000eb00000047c000a01d84f0000003fc6a95a800000000000000000642c176000a50002cb49e00017298000744000000005c540043000000000001a27c80900027e8ac00290064320378000002d49ba2e48000015000174000000160000009b000000000369681e200058881000000000000000010015304cb040007003a890000634f4001638000000009a191000288000005640c5118002584e8d380c000000038004c40012a8ad0000013580034c73c001c5000000001781a04a400000196294000bb0000000a8000000014c8004d00dc0000000000128800000841290003601500000b0005c80f0990d8000d5800000470000005880000000000000000107066000262d30ce0180010f0009252b9540001550aaac2e87fc3e800000388000000000d4ad0c70003a4001c00007f000000240a9d0e263000614000960e6001589310004382597c0424e4d21e01660e800000000000860004cc5ec2f0000f4000000000007180017a5382a85e9520e4000000001d40015fa82000001030e40009d80000900053800000000000001c92c8654560c601c4e15e9a3000a0d109d80101d045a323cc000000004bcaccc01191081fc110f52d
  | 5 => 0x122001569f94260000022008a000d9a3c000000520c3000000000000000004b80009c0000026002600000000000334a5a4746e0000025a000b0c0015b1980a0000000b40015412f00098423800256628000000004a8d40380006e118a2a03e20842a69572560000ed0000000023f0005f912800000000000000000000015e000000002561f000001a8e5602fc00000000000ba8000000705b9e13861880b9984141ed212d236823c00248000741018003d896c7380015e000000000000ec000003d40006981143400032800000564fa17742ca850e963578200ab8da4447c03b06444c86400187000424c48000b60005b1ef3ec15d059ac
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x90007808c8000302c80151d801a28970312b2a1a406049a8e0b8fa9b1201c11001b8003a599b18c0017ab2ba11f9e86a524801880002a2d2a82a914909b139d000d80130a16278b1c802c1f2280000f20992305821826001001968022320d26afaf2800000008800e850a8107099e00002e11800000158000040023aea700001430ad880012000000c24140010103c00140008000c00000c000410000408181808000000283c10541e4ab8ec4a1887235cb6150c4391ae43028621c95711814310f82a1aa4a8887c250e5254043e1286a92a021f11439455010f88a1aa2a8087461d94354043a36e4a1aa021d1b7150d5010f0ca9ac021e854c5c04354742c32a8b0087995517010d51ccb0caa2c021a65615c44350932b12e021a84996195358043d0694b8086a9683865516010f31a92e021aa598e1954580434c6c2b9086a0a63645c04350531e0aa6a128210f05544c93108662b9ec890843295d36348421e0aa8a9a4210ca5741812108662b98c090843c89512154021e42a890aa010f425348550087a0a9a42a8043525ce4254021ac2e3212a010d29748c950086b0b8c64a8043545ce4154021ac2e520aa010f21425055008698ba462a8043585ca3154021e826498aa010d607648550086b1ba242a8043585d12154021ac6e690aa010d61734855008722b12c229a81925896014d40ca2c2b00a6a061453587425030629ac5a0a814a5c04354840a62e021aa22060c63549401030a31aa2a008186d516010e30934eda1a811862562584544c30cb1ac02a2618a5896015130c62c2b00a89861454587324c3062a2c598a61469d64390130c30caa1a809861954580430c2a4b8086a9061545c04354430838ecaa2601860c64549300c30a322a298061855916314520a8ae7210a290525748c85148318b22c028a419458d6014520c52a8b004210649535802108312aa0c2900419154c6148020cc6a4b0043084e276c852084306b22c6292218a5916014910c92c6b00a488661615805244322b18a520a2189590528c510ac4eb10c4088660654852044318aa2c0108219454d6008410cc2a4b004208625541891004322a98c488021191d95244010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xe40c06a0080201909821d94354043911811d9435404391181dc9435404390982dc54354043921841d92154021941831d9215402194183dd1215402192184dcd2154021
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 682
  | 4 => 725
  | 3 => 102
  | 2 => 8
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20684+((h/227+packedAt s2K5 (18414+(h % 227)*10) 10) % 819)*11) 11
  | 4 => packedAt s2K4 (30201+((h/241+packedAt s2K4 (27550+(h % 241)*11) 11) % 1158)*11) 11
  | 3 => packedAt s2K3 (5270+((h/34+packedAt s2K3 (4998+(h % 34)*8) 8) % 135)*8) 8
  | 2 => packedAt s2K2 (488+((h/2+packedAt s2K2 (480+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1e3e3c7ffc7ffe3f0c63831ffc7ff83f00f3cf
  | 1 => 0x1fc03f8e3f8e3fc7f07c03e38f8e3fc7334d33
  | 3 => 0xe0003ff03ff03ff8ff8003fc0ff03ff8c38e3c
  | 4 => 0xffffc0003fffc000fffffc000fffc000fc0fc0
  | 5 => 0xffffffffc0000000fffffffff0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2004400040000400000800480120800001045
  | 1 => 0xc4148944492854085064292124849286314512
  | 3 => 0x1a912289244a801ac80524849212530c28a28
  | 4 => 0x488c032520240c92352918000e498192540f80
  | 5 => 0x9130204803493124ca52639260000624abe000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88ffffeeaaeeaaee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5a4003c000001c98a50ac2193c14000069441a4c24b80200108052446810060f9d00180002400020009ca15008d500386c6024458700000010401410c7401183003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x151d2799802482a815a9ac239d9b2c8011089c8c89960624000f19001781a285000e9f800c2300252680078380a61aa113a1a21b800da8ab169012119492a00b080f85820d2d0020870b8a010400290e180000001c00000300002d802b8a89270006a598931e142a2a849f1a1e90970189020010118c02813000228000000514202011e0019a0a5c106bb28c87755190edca421db54843bb28887755110ef4a021de54043bb28e857551d0b6ca3a16d547429eaa485af5250a7ca8215d94732baa8e653e548ca7aa9196b50a32d6a12653e540ca7aa8195d94432baa88657a500caf2a0195b94b41b6a96835e53906baa720cf952319eaa463b6548c76aa918dd54e31dba1463b5428c7aea698f5d0d31ea21a63b7424c76a8498f5cc931ea9926376510c67ca990cf55321d6a14433e540867aa810d794c21aea9843ad42086f4a010de54021af298815d53102dca4205b54840bb288817551102eca3985d54730ea98e613f544c278a898754c5309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6a1641ad42482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x6a881100603000f395096000072c0004259558e51d0a956394742a99875250a2d6295231a958a548c63565d0a31a5993534c6c56210d31b4580434c785424c931c354d420872942540218b588544c314544c5309558c51483254214520
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x42018090ae730ea4a148572993534c682b90a898a618158d4214520
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 16
  | 2 => 4
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
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2694+((h/30+packedAt s3K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s3K3 (633+((h/5+packedAt s3K3 (608+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf1e78f3ffc71ff1f88c70c7fe38ff0f80f1cf
  | 1 => 0xf01f80fce3f818fe3f0f80f8e3c0e7f3b34933
  | 2 => 0xffe000ff03ffe0ffc7f000ff03ff07fc438e3c
  | 4 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 5 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1020110004020020000100120082100001045
  | 1 => 0x10c4322a44925160430c86484a425263314912
  | 2 => 0x22014440892402800c90089210940488428228
  | 4 => 0x44481008520200249125220003229021140d80
  | 5 => 0x88916082803494c926ca4ce4980400ca6be000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8ffffeaeafafae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x40014e3584046180a424018043bf43bd43bf42bd42df32ee32dd32ed32cd32bf41bd41be40bc40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x354311805001c8005877812b00000010700000a6a9c658f424cb1a849963d0d32c6a1a658e544cb1aa8994754f4196a96838d32d071a64a0e34ca408ea98812d521031a64204d54440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x400d00a1586544ca0d654cb418359532103053254440
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (228+((h/4+packedAt s4K4 (208+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s4K3 (457+((h/5+packedAt s4K3 (432+(h % 5)*5) 5) % 26)*5) 5
  | 2 => packedAt s4K2 (155+((h/1+packedAt s4K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7fc7fff87f0ff0ff0f87e1ffe1fc3f0fa4f4cf
  | 1 => 0x87f870ff8ff0ff0ff1f87e1c3e1fc7f1db4b33
  | 2 => 0x7ff80fff000fff1fe007fe03fe007fe638c3c
  | 3 => 0xf80000ffffff0001ffff80003ffff8007c0fc0
  | 5 => 0xffffff0000000001ffffffffc00000007ff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x400008001001000000802400240100001045
  | 1 => 0x20820111040140102088220882090241094112
  | 2 => 0x55112aa222aaa88356445541354094ac628c28
  | 3 => 0x14354cc44a882aa59b5511023992b024740e80
  | 5 => 0x662668876cccccc9ede67993910320c97fe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8eeeaeeeaeee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x427928a0ea0b1f067008d32500002280795302c1064e00829441092a4c00d93000118e0a2158000252003474b8c0004000b08000705f000040ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1406a4000d079da900a9aaa88017a489252c8b0eaa28101723839a929a1892020027812b9d001c1b080180040026060f04a321228c2c001ba59580072d94800e0b801f80089e800a1680050019271e2191a2209600001310952d0fab058c938d82899f198a83001ca6912000180000008702000010c10600040c10c20001081e0c705062c0001800301bb28e877551d0edca521db54a43af29c855d5390abca6215754c42bb28885755110af4a0215e540429f2a6653d54ccb3ca9996755332aea9c65cf524cb9e84997310932af298655e53d06baa7a0e794f41cea9e839f32d073a65a0cf55241cf992839d325076ea2a0cf95041daa0e633e548c67aa918cf950319eaa0636e520c6daa418ed50431bd2806379500c6bca790d754f21e6996433e548867aa910ed50621e699243b5414867ca810cf55021af298435d53086f4a010de54021af298815d53102dca4205b54840bb2888175511027ca8184f55030b7290616d520c2eca2185d54430af29e415d53c839a65904fd51209e2a241cd324827ca8104f55020af298415d53082eca2105d544209f2a6213d54c436a838857d4d10ae29a21b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x434003386012de93808c0800a2804a80428d58654cca956195332a3993524cac56110932b2580424ca4d6294f41a358a53d061d65ccb41a598f51507255250431cc505500c78532505218d584544830c544c9209358853443145350510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1418090ae3326a4994857298f5150682b88a899241415c85350510
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
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 22)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3cfe3c7fc7e3f1f8c63c70fe3f0fc78474cf
  | 1 => 0xf03f1fc063f9fc7e3f07c780e3c7f1f99a4b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1040200804004020000081020090040001045
  | 1 => 0x10888411049080c042024484484240a10a4112
  | 2 => 0x22024888090049200948012202902514208c28
  | 3 => 0x441241aa5225402495d4900a1324ac14740e80
  | 4 => 0x88a091304035924926a7264c9800c8215f6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8fefaeee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x5c38c89189188352816a20078a320c00b2536b001d34a802f0441f3724fc508003de174e10fb9741518768340004c84a9102f40286ccd5b50071d800000000700000b6000000004cc0012001000104801000000b8304046030e0098201ffd5001fe54007f55007fc5401ffd4c05fe53007f54c05fc53007fd0c05fe43007f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803fe4200ff50803fc4200ffcc803df3200ff8c803fd3200f74c803fc3201ffd4401fe51007f54407fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc2101ffd4001fe50007f54007fc50007fd0001fe40007f50001fc40017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000ffd9110005fec888003fe64440157f3222000ff59110005fac888003fc64440157e322200dffd5110007fca888003fd544401bfe2a22000ffd8d10005fec688003df63440016fb1a200cff98d10015fcc688003fd63440017eb1a200cff18d10015f8c688003dc63440056e31a200dffd4d10067fca688003fd5344019fe29a2000ffd0d10067fc8688003fd4344019fe21a200bffd891005dfec48802ffe62440037f312200bff5891005dfac48802ffc62440037e312200bffd491005efea48802ffe5244017fea92200bdf5491005ff8a48802fff4244017ff212200bff5091005ff8848802fff3244017ef992200bff8c91005ffa648802fdd3244017fe192200dffd4510027fca288003f65144001fea8a2000fd54510027f8a288003ff4144009ff20a2000fd90510007fa8288003f54144009fe20a200cffcc510027fc6288003f63144001fe98a2000fd4c510027f8628802fff2144009ff10a200bfd8851005ffa428802ff52144009fe10a200dffd4110007fca088003fd504401bfe2822000ffd0110007fc8088003fd4044001fe202200cffcc110007fc6088003fa3044001fe9822000fe4c110067f8608802fff2044017ff102200bfe8811005ffa408802ff92044017fe1022004ffc4110027f62088003fe1044001fb0822005ffd9410025feca08013fe65040077f3282004df9941001cfcca08013fd65040017eb282004df59410004faca08017fc65040097e3282005ffd9010025fec808013fe64040157f3202004ef990100057cc808013fd64040017eb202004ef590100057ac808017fc64040097e3202008ffd5010007fca808003fd5404011fe2a02005ffd8c10025fec608013fe63040057f3182004f798c10015bcc608013fd63040017eb182004f758c10005bac608017fc63040097e3182008ffd4c1003ffca608003fd530400ffe2982000ffd0c1003ffc8608003fd430400ffe2182005ffd8810025fec408013fe62040037f3102004fb9881000ddcc408013fd620400d7eb102004fb58810005dac408017fc62040097e3102006ffd4810036fea40801bfe520400dfea902006df54810037f8a40801bff420400dff2102006ff50810037f8840801bff320400def9902006ff8c810037fa640801bdd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841004dfcc008023ff500400bff2802000ff5401002ff8a008003ff400400bff2002000ff5001002ff8800801fff300400bff1802000ff4c01002ff8600801bff200400bff1002006ff4801002ff84008013ff1004009fb8802005ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x3fd404c001fe2026002ffcc130017f6609800bfe304c001ef1826002ff0c130017b8609800bf8304c027ff9026013ff8813009ffa409804ffc204c009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2000bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98802afe64c4009feb262000bf59310027f8c988012fc64c4025ffaa62000ff95310007faa98804bfc54c4009ffb1e2004bfd8f10027fcc78800afe63c4009feb1e2000bf58f10027f8c788012fc63c4025ffa9e2011ff94f10007faa788047fc53c4001ffa1e2011ff90f10007fa8788047fc43c4009ffb162004bfd8b10027fcc588006fe62c4009feb162010bf58b10027f8c588012fc62c4021ffa962010dfd4b10087fca588043fd52c4021bea962010ff14b10087fe8588043fe42c4021fea162010ff10b10087fe6588043df32c4021ff1962010ff4cb10087ba6588043fc32c4009ffa8e2004ff94710027eca388013fd51c4001faa8e2004ff14710027fe8388013fe41c4009fb20e2004ff50710007ea8388013fc41c4009ff98e2004ff8c710027ec6388013fd31c4001fa98e2004ff0c710027fe4388013fe21c4009fb10e2004ff48710087ea4388013fc21c4025ffa862000ff94310007faa18804bfc50c4001ffa062000ff90310007fa8188003fc40c4023ff9862000ff8c310007fa6188047fc30c4021ff9062010ff88310087fa4188043fc20c400bffb2c2000bfd961007ffccb0800efe6584001feb2c2000bf5961002ff8cb0800efc658400bffb242000bfd9210007fcc90802afe6484001feb242000bf5921002ff8c90802afc648401fffaa42000ff95210007faa90803ffc548400bffb1c2000bfd8e10077fcc70800afe6384001feb1c2000bf58e1002ff8c70800afc638401fffa9c200eff94e10007faa70803bfc5384001ffa1c200eff90e10007fa870803bfc438400bffb142009bfd8a1004ffcc508006fe6284013feb142009bf58a1002ff8c508006fc6284013ffa942009dfd4a1004ffca508027fd5284013bea942009ff14a1004ffe8508027fe4284013fea142009ff10a1004ffe6508027df3284013ff1942009ff4ca1004fba6508027fc32840177eb0c200fffd4610027fca308003fd5184009fe28c2000ffd0610027fc8308003fd4184009fe20c200effcc610027fc6308003fd3184009fe18c2009ffc8610027fc4308027fd2184009fe10c2004bf9821007ffea108017fe5084001fea842005ff14210007fe8108017fe4084001fea042005ff10210077fe6108017fe3084001fd1842000ff4c210007f26108017fc3084013ff9042005ff8821004ff44108027fd2084013fc9042005ff08210027fe2108003f71084009fd8842000ffd9510005feca88037fe65440077f32a2000ff59510005faca88037fc65440077e3
  | 2 => 0x40005fac22002bf561100017ab088005ff184400cffea220003fe5110001fea888019ff14440057fe822002bfe4110015fea08800aff104400c7fe6220003fe3110001fe9888018ff0c4400bffe422005ffe211002ffe9088017ff084400d5fcc020067ff501000bff2808000ff5404002ff8a02002bff4010015dfa008005ff90040057f4802002bfd4010001dea00800afe500400c7fe6020017fc301002fff9008005ff880400bffa4020017fc201000bffb2c6000bfd96300b7fccb1800efe658c001feb2c6000bf5963002ff8cb1800efc658c00bffb246000bfd9230007fcc91802afe648c001feb246000bf5923002ff8c91802afc648c02dffaa46000ff95230007faa91805bfc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bfd438c005fe21c6005ffd8a300adfec518057fe628c0037f3146015ff58a300adfac518017fc628c0037e3146015ffd4a300aefea518057fe528c02bfea946015df54a300aff8a518057ff428c02bff2146015ff50a300aff8851800bff328c005ef9946002ff8ca30017fa6518057dd328c005fe1946005ffd8630007fcc318012fe618c001feb0c6000bf5863002ff8c31805bff518c001ff28c6000ff546300b7f8a318003ff418c001ff20c6000ff50630007f8831800bff318c005ff18c6000f78c630017fa631800bfc318c005ee18c6015ffc86300affc4318057fd218c02bfe10c6002bf982300b7fea118017fe508c001fea846005ff14230007fe8118017fe408c001fea046005ff10230017fe611800bdf308c005fd9846005ff0c230017f06118057ff208c00bff1046015ff4823002ff84118003ff654c0017fb2a6014ff9953001dfcca98003fd654c0017eb2a6014ff1953001df8ca98003ff644c0017fb226000ff99130055fcc898003fd644c0017eb226000ff19130055f8c898053ff544c001ff2a26000ff551300a7f8a89800aff634c005ffa9a6002ff94d30017bca69800bfd534c001eea9a6002ff14d30017fe869800bfe434c005ef21a6002ff50d30007ba869800bfc434c027ffb126013bfd893009ffcc498006fe624c027feb126013bf5893009ff8c498006fc624c027ffa926013dfd493009ffca49804ffd524c027bea926013ff1493009ffe849804ffe424c027fea126013ff10930017fe649800bdf324c005ff1926002ff4c93009fba649800bfc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6004bf185300a7fea298003fe514c001fea8a6014ff14530007fe8298003fe414c001fea0a6000ff10530017fe629800bdf314c005ff18a6002ff4c530007ba629800bfc314c027ff90a6013ff8853009ffa429804ffc214c0057fb026014ffd4130007fca098003fd504c029fe2826000ffd0130007fc809800
  | 3 => 0xf214801aff50a40057f8852006bff3290035ef994801aff8ca400d7fa652006bdd3290035fe1948005ffd8640007fcc320012fe6190001feb0c8000bf5864002ff8c32007fff5190001ff28c8000ff546400fff8a32002bff4190001ff20c8000ff50640057f8832007bff3190001ff18c8000ff4c6400f7f8632006bff2190035ff10c801aff486400d7f8432002afe609003fffa848005ff94240007f4a120003fd5090001fca848005ff14240057fe8120003bf4090015fda04801effcc24002ff8612006bff209000bff104801afe882400d7fa412006bf9209000bfe1048000ffd9540005fecaa00037f65500013fb2a801dff9954001dfccaa0003fd65500017eb2a801dff1954001df8caa00037c65500073e32a801dffd5140057fca8a0003be5450001feaa28000ef55140057f8a8a0003ff63500017fb1a801cff98d40015fcc6a0003fd6350039fe31a8002bf18d400effea6a0073fe5350001fea9a801cff14d40057fe86a0003bf4350039ff21a8000ff50d400077a86a002bfc4350037ffb12801bbfd89400dffcc4a0006fe6250037feb12801bbf589400dff8c4a0006fc6250037ffa92801bdfd49400dffca4a006ffd5250037bea92801bff14940057fe84a006fbf4250037ff212801bff509400df7a84a002bfc4250037ff992801bf7cc9400dffc64a006ffd3250037ee992801bff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0012fc615003bffa8a8000ff94540007faa2a0077fc5150015ffa0a8000efd0540007fc82a0003fd4150001dea0a800aff105400e7fe62a0003fe3150001fe98a801cff0c5400dffe42a006ffe2150037fe90a801bff085400effea0a0003fe5050001fd2828000ff54140007f2a0a0077fc5050015ffa02800afed0140007fc80a0003be4050039ff982801cff0c1400dffe40a006ffe2050037fd102801bff481400dff240a006ffc205000bffb28800abfd9440057fcca2000efe6510015bf32880039f99440057faca20002fd6510015beb2880009f5944002ff8ca2002afc65100157f320800affd5040057fca82002bfd5410015fe2a08005ffd8c40057fcc62000afe6310015ef3188002b798c40057fac620002fd6310015eeb188000b758c4002ff8c62000afc6310033ffa988018ff94c40007faa620063fc5310015ffa18800aff90c40057fa862002bfc431000bffb10800abfd8840057fcc420006fe6210015f73108001bb98840057fac42005efd6210015f6b108000bb5884002ff8c420006fc621002fffa908017dfd48400bffca42005ffd521002fbea908017ff14840057fe842002bfe4210015fea10800aff108400bffe642005fdf321002fff1908017ff4c8400bfba642005ffc321000bffb08800aff98440025fcc22002bf661100017b308800aff584
  | 4 => 0x3fc64540157e322a003ffd515001efea8a800ffe5454007feaa2a000df5515001ff8a8a8003ff63540017fb1aa024ff98d50015fcc6a8003fd6354049fe31aa002bf18d5001ffea6a800f7f5354007ff29aa003ff54d50006faa6a800ffc5354001ffa1aa024ff90d50007fa86a8093fc4354047ffb12a023bfd895011ffcc4a8006fe6254047feb12a023bf5895011ff8c4a8006fc6254007ffa92a003dfd495001ffca4a800ffd5254047bea92a003ff1495011ffe84a808ffe4254047fea12a023ff1095011ffe64a808fdf3254047ff192a023ff4c95011fba64a808ffc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa004bf1855001ffea2a800f7f5154007ff28aa003ff54550006faa2a800ffc5154001ffa0aa000ff90550007fa82a8003fc4154049ff98aa000ff8c550007fa62a8093fc3154047ff90aa023ff8855011ffa42a808ffc21540077fb02a003ffd415001ff6a0a800ffe5054001bf282a003ff1415001ef8a0a800ff85054049ff982a024ff0c15011ffe40a808ffe2054047fe902a023ff08150057fecba002aff65d0015ff32e8003bf99740057facba0002fd65d0015fe32e800abf19740057fea9a002bfe54d0015df2a6800aff553400077aa9a002bfc54d0015ffb1e800aff98f40015fcc7a002bfd63d00017eb1e800aff18f40015f8c7a008bff53d0043ff29e8000ff54f4010ff8a7a002bff43d0015dfa1e800aff90f40057fa87a0003bd43d0015fe21e800affd8b40055fec5a002bfe62d00037f316800aff58b40105fac5a002bfc62d00037e3168020ffd4b40106fea5a0083fe52d0041fea968020df54b40107f8a5a002bff42d0015dfa16800aff90b40057fa85a0083bd42d0015fe2168020ffccb40107be65a0083fe32d0041fe9968020f74cb40107f865a002bff61d0015ff30e8004bf98740057fac3a0002fd61d0015fe30e8022ffd4740007fca3a0003fd51d0045fe28e800affd07400577e83a002bfe41d0015fea0e8000ef50740057f883a0087ff31d0001ff18e8000ff4c74010ff863a0083ff21d0041ff10e8020ff48740107f843a008bff50d0001ff2868000ff54340117f8a1a0087ff30d0043fe1868020ffc8340107fc41a0083fd20d0041fe1068005ffd9640005fecb2007ffe65900077f32c8000ff59640005facb20017fc65900077e32c801bbf592400fffea92002bfe5490001feaa4800aff1524002ffec72007bfe63900057f31c8000ff58e40005fac720017fc63900057e31c801fffd4e400f7fca720003fd539003dfe29c800affd0e400f7fc8720003fd4390015fe21c8005ffd8a400d5fec52006bfe62900037f314801aff58a400d5fac520017fc62900037e314801affd4a400d6fea52006bfe5290035fea94801adf54a400d7f8a52002bff4290035f
  | 5 => 0xa3114ffc85188a7fd428c453fe2146202ffcca31017be651880bfe328c405fe9946229f74ca31017f86518812fe618c409ffa8c6204ff94631027faa318813fc518c409ffa0c6204ff90631027fa8318813fc418c409ff98c6204f7cc631017ee6318813fc318c409fa18c6204ffc8631027fc4318813fd218c409fe10c6204ffd8231027fcc118802fe608c409feb046200bf58231027f8c1188abff508c455fe2846202ffcc231017f8611880bdc308c453ff9046229ff8823114ffa41188a7fc208c401ffb2a6200bfd9531147fcca9880efe654c401feb2a6200bf59531147f8ca9880efc654c401ffb226200bfd9131007fcc89882afe644c401feb226200bf59131007f8c89882afc644c451ffaa26200ff95131007faa8988a3fc544c4097fb1a6202ffd4d31017fca69880bfd534c405fe29a6202ffd0d31017fc869880bfd434c405fe21a6227ffd893113dfec49889ffe624c4037f3126227ff5893113dfac49889ffc624c4037e3126227ffd493113efea49889ffe524c44ffea926227df5493113ff8a49889fff424c44fff2126227ff5093113ff8849880bff324c405ef9926202ff8c931017fa649889fdd324c405fe1926202bfd8531147fea298813fe514c401fea8a6204ff14531007fe8298813fe414c401fea0a6204ff10531017fe629880bf7314c409ff18a6204f78c531027f86298813dc314c405fa18a6227ffc8531027fc429889ffd214c409fe10a6200ffd8131005fec098803fe604c401feb026200ff18131005f8c0988a3ff504c451fe2826202ffcc131017be609880bfc304c44fff9026227ff8813113ffa409889ffc204c4077eb2ca005ffd9250007fcc92802afe6494001feb24a000bf5925002ff8c92800fff5494007ff2a4a000df9525001ffaa92800ffc5494007be2a4a005ffd8e50137fcc72800afe6394001feb1ca000bf58e5002ff8c72800afc6394007ffa9ca003ff94e5001ffaa72800ffc5394001ffa1ca026ff90e50007fa872809bfc439400bffb14a025bfd8a5012ffcc528006fe629404bfeb14a025bf58a5002ff8c528006fc6294007ffa94a003dfd4a5001ffca52800ffd529404bbea94a003ff14a5012ffe8528097fe429404bfea14a025ff10a5012ffe6528097df329404bff194a025ff4ca5012fba6528097fc329400bffb0ca000ff98650025fcc328003fd61940017eb0ca005ff1865001ffea32800ffe5194007fea8ca003ff14650007fe8328003fe4194001fea0ca000ff10650137fe6328003fe3194001fe98ca026ff0c65012ffe4328097fe219404bfe90ca025ff0865001dfcc12800fff5094007bfa84a003fed425002ff8a12800ff8509404dff984a005ff0c25012ffe4128017fe209404bfe904a005ff0825001dfecaa8003ff64540017fb22a000ff99150007fac8a8
  | 6 => 0x17fb2a8230ff9954101dfccaa0803fd65504017eb2a8230ff1954101df8caa08c3ff5450461dfaa2820aff95141007faa8a082bfc5450461de2a28200ffd8d41005fec6a08bffe63504057f31a8200ff58d4117ff8c6a080afc6350461ffa9a822fff94d41007faa6a08bffc5350415ffa1a8200efd0d4117ffc86a0803fd4350401dea1a820aff10d41177fec4a08baff625045dff3128201bf98941177fac4a08bafd625045dfe3128201bf18941177fea4a08bb7f525045dff292822eff54941176faa4a08bbfc5250415ffa12822eefd0941177fc84a08bbfd425045ddea12820aff10941177fe64a08bbdf325045dff192822eff4c941177ba64a08bbfc3250461ffa8a8204ff94541007eca2a0803fd5150401faa8a8204ff14541057fe82a082bf74150409ff20a8204ef9054117ffe62a08bff73150409fe18a822ffd0c541177fe42a0813fe215045dfb10a822eff48541177ea42a0813fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028200bf18141187fea0a08c3fc505045fff982822fff0c141177fe40a08bbfe205045dfe902822eff08141027feca20812ff6510409ff3288203bf99441027faca20802fd6510409fe3288204bf19441055fcc82082bff5410415ff2a0820aff55041057f8a820813ff6310409ff3188202bf98c41027fac620802fd6310409fe3188204bf18c4116ffea6208b3fe5310401fea98822cff14c41057fe862082bfe4310415fea18820aff10c41027fec420812ff6210409ff3108201bf98841027fac4208aefd6210409fe3108204bf1884115ffea4208af7f5210457ff290822bff5484115efaa4208affc5210415ffa10820aff90841057fa842082bfc4210457ff990822bf7cc84115ffc64208affd3210457ee990822bff0c841025fcc220813ff5110409ff2888204ff54441027f8a220813ff4110409dfa088204ff90441027ec8220813fd4110409dea08820afd50441027fe6220813fc3110409ff9088204ff88441027fa4220813fc2110409ffb008204ff98041005fcc020813fd60104017eb008204ff1804116ffea0208b7fc5010459ff980822cff0c04115ffe40208affe2010457fe900822bff08041027fecb18812ff658c409ff32c6203bf99631027facb18802fd658c409fe32c6204bf19631027fec918812ff648c409ff324620abf99231027fac918802fd648c409fe3246204bf19231157fea918803fe548c401feaa4622aff15231015fac71880bff538c405ff29c6202f794e31017faa718803dd538c405fe29c6202ffd0e31017fc871880bde438c405fea1c6200f750e31017f88718813ff628c4097fb146204ff98a3100dfcc518813fd628c4537eb146204ff18a31025f8c5188a7ff528c453bfa946229ff94a3114ffaa5188a77d528c453fe2946229ffd
  | 7 => 0xa880fff5254407bfa92a203ff9495101ffaa4a88df7d5254407fe292a237ffd09511bffc84a88dffd425446ffe212a237ffcc9511bfbe64a88dffe325446ffe992a237f74c9511bff864a880eff6154407ffa8aa203fdd4551027fca2a88137e5154409fe28aa204df1455101fe8a2a88e3ff3154409fe18aa237ffc8551027fc42a88dffd2154409fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a880fff5054407bfa82a203ff141511c7fe60a88e3fc305446fff902a237ff881511bffa40a88dffc2054415ffb2e820abfd9741057fccba080efe65d0415feb2e8200bf59741057f8cba082afc65d0415ffaa68236efd5341057fca9a082bfd54d0415fe2a6820aef15341057fec7a082bfe63d04057f31e820af798f41015bcc7a082bfd63d04017eb1e820af758f41005bac7a082bfc63d04057e31e8236ffd4f411affca7a0803fd53d046bfe29e820affd0f410577e87a082bfe43d0415fea1e8200ef50f41057f887a082bff62d04157fb16820aff98b4100dfcc5a082bfd62d04697eb16820aff18b4100df8c5a08d3ff52d0469bfa968234ff94b411a7faa5a08d37d52d0469fe296820affd0b410577e85a082bfe42d0415fea168234ef50b41057f885a08d3ff32d0469ef9968234ff8cb411a7fa65a08d3dd32d0469fe1968236ffd4741027fca3a0803fd51d0409fe28e8235ffcc741027f863a08d3ff21d0409ff10e8234ff48741027f843a082bff60d0415ff3068200bf98341057fac1a0802fd60d0415fe3068236ffd43411b7f8a1a08d7ff30d046bfe1868234ffc83411a7fc41a08d3fd20d0469fe1068204ffd9641025fecb20813fe65904077f32c8204df9964101cfccb20813fd65904017eb2c8204df59641004facb20813fc65904097e32c822ebf5924119ffea92082bfe5490401feaa4820aff15241027fec720813fe63904057f31c8204ff58e41005fac720813fc63904097e31c8233ffd4e41197fca720803fd5390465fe29c820affd0e41197fc8720803fd4390415fe21c8204ffd8a41025fec520813fe62904037f3148204ff58a4118dfac520813fc62904097e3148231ffd4a4118efea5208c7fe5290463fea948231df54a4118ff8a52082bff4290463ff2148231ff50a41057f885208c7ff3290463ef9948231ff8ca4118ffa65208c7dd3290463fe1948204bf98641027fea320813fe5190409fb28c8204ff54641007eaa320813fc5190409ffa0c8204efd0641057ee8320813ff3190465fb98c8204ff0c641027e86320813ff2190409ff10c8204fd88641027fa43208c7f52190409fe10c8204ffd8241027fcc120802fe6090409feb048200bf58241027f8c1208cfff5090467fe2848232ffcc241197f861208c7ff2090463ff1048231ff4824118ff84120803ff655040
  | 8 => 0xf187431f7fea3a18fbfc51d0c05ff98e8602ff0c7431effe43a18f7fe21d0c7bfe90e863dff08743057fec1a182bfe60d0c017f306860aff58343005fac1a182bfc60d0c7dffa86863eff14343017fe61a180bfc30d0c7bff906863dff883431effa41a18f7fc20d0c01ffb2a8600bfd95431e7fccaa180efe6550c01feb2a8600bf595431e7f8caa180efc6550c057fb22863cffd5143057fca8a1803fd5450c15fe2a28602bfd8d43017fea6a180bfe5350c05ef29a8602ff54d43007baa6a180bfc5350c05ffa1a860af7d0d43017fc86a180bbe4350c05fe21a8602ef10d43017b886a18efff6250c777fb12863bff9894300dfcc4a18effd6250c777eb12863bff1894300df8c4a18efff5250c77bfa92863bff949431dffaa4a18ef7d5250c77fe292860affd09431dffc84a18effd4250c15fe2128602ffcc943017be64a180bfe3250c05fe992863bf74c943017f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c097e30a863cffd45431e7f8a2a180bff3150c05fe18a8602f70c5431dffe42a18effe2150c77fe90a863bff08543007fec0a1802ff6050c01ff3028600ff58143007f8c0a1802fc6050c79ffa82863cff14143017fe60a180bdf3050c05fe182863bffc81431dffc40a18effd2050c77fe1028603bf59651027fec928813fe64944157f324a204ef992510057cc928813fd64944017eb24a204ef592510057ac928813fc6494407ffaa4a203ff9525101ffaa92880ffc5494409ffb1ca204ff98e51015fcc728813fd63944017eb1ca204ff18e51025f8c72880fff5394407ff29ca203ff54e5101ff8a728803ff4394475ff21ca200ff50e511d7f88728813ff62944097fb14a204ff98a5100dfcc528813fd62944737eb14a204ff18a51025f8c52880fff5294407bfa94a203ff94a5101ffaa5288e77d5294407fe294a239ffd0a511cffc85288e7fd4294473fe214a239ffcca511cfbe65288e7fe3294473fe994a239f74ca511cff86528812fe6194409ffa8ca204dfd465101feea328813fc5194409fa28ca204ffcc651027f86328813ff2194409ff10ca204ff48651027f84328813ff6094409ff304a200bf98251027fac128802fd6094409fe304a203ffd425101ff8a1288ebff3094475fe184a239ffc82511cffc41288e7fd2094473fe104a204bfd9551007fec8a8802ff6454401ff322a200ff59151007f8c8a882afc6454407ffaa2a203ff95151006fca8a880ffd5454407fe2a2a203df15151007fec6a8802ff6354471ff31aa202bf98d51007fac6a88e3fc63544057e31aa203ffd4d5101efea6a880ffe5354407fea9aa200df54d5101ff8a6a8803ff4354471ff21aa200ff50d511c7f886a88dfff625446f7fb12a237ff9895100dfcc4a88dffd625446f7eb12a237ff1895100df8c4
  | 9 => 0x17eb04a80aff1825401ffea12a00ffc5095007be284a843ffcc25421ff8612a10bff2095085ff104a842ff48254217f8412a02aff65550077fb22a803ffd515401f7ea8aa02bfe5455015bf2a2a80aff15154056f8a8aa00fbc5455001ffb1aa800bfd8d5420ffcc6aa00afe6355001feb1aa841ff18d54015f8c6aa00fff5355007ff29aa803ff14d5420ffc86aa02bfc4355081ffb12a840bfd8954207fcc4aa006fe6255081feb12a840bf58954207f8c4aa006fc6255007ffa92a803dfd495401ffca4aa00ffd5255081bea92a803ff14954057fe84aa103fe4255081fea12a80aff10954207fe64aa103df3255081ff192a840ff4c954207ba64aa103fc3255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa804bf1855401ffea2aa00ffc5155083ff98aa841ff0c554207fe42aa103fe2155081fe90aa840ff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa002fc6055007ffa82a803dfd415401ff8a0aa107ff3055083fe182a840ffc8154207fc40aa103fd2055081fe102a802bfd9553007fec8a9802ff6454c01ff322a600ff59153007f8c8a982afc6454c07ffaa2a603ff95153006fca8a980ffd5454c07fe2a2a603df15153015fec6a980bff5354c07efa9aa602ff94d53016fca6a980bfc5354c05be29aa602f714d53017fc86a980bde4354c05fe21aa63fffd89531fdfec4a98fffe6254c037f312a63fff589531fdfac4a98fffc6254c037e312a603ffd495301efea4a980ffe5254c07fea92a63fdf5495301ff8a4a98ffff4254c7fff212a63fff509531fff884a980bff3254c05ef992a602ff8c953017fa64a98ffdd3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553025f8c2a980fff5154c07bfa8aa603ff14553017fe62a980bfc3154c05ee18aa63fffc85531fffc42a98fffd2154c7ffe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff18153005f8c0a980fff5054c07bfa82a603ff14153017fe60a980bdf3054c05fe182a63fffc81531fffc40a98fffd2054c7ffe102a60affd9743055fecba182bfe65d0c077f32e860aff59743005facba182bfc65d0c157e32e8602bf99343057fea9a182bfe54d0c15feaa6860aff15343015fac7a180bff53d0c05ff29e8602ff54f43017f8a7a180bfe43d0c05df21e8602f790f43017f887a180bbc43d0c15ffb16860abfd8b43057fcc5a1806fe62d0c15feb16863dbf58b43057f8c5a1806fc62d0c7bffa96863ddfd4b431effca5a18f7fd52d0c7bbea96863dff14b43057fe85a182bfe42d0c15fea16860aff10b43017fe65a180bdf32d0c05ff1968602ff4cb431efba65a180bfc32d0c15ffb0e860aff98743025fcc3a182bf661d0c017b30e860aff58743005fac3a182bf561d0c017ab0e860af
  | 10 => 0xa02001600000003a00200600000400a00e02800400603202600002800e00008200000400a01c00201201400000a00000201201200e00000600200c01001a01e00401a00202e00400400402a00000200e00000002600000a00000800401200202001001200000003a00002200600c03600000001c0060aa01400600a03400200000000e00c00002801c02000003c00600e01200e00000800007800000403c01c01e00c03803000000202800400000000c02000603001a00000200e00601002001800400600400002e00a00602200c00001600201401200000000002801e00400402803a00200400200001e05201a00e01e00800800801200e01600200201002802000203a00600600000a00200200c00600000c01603c00c05401400400c01c00c00000000204000406400000400201400000400000001c00a00000000401600e01604003800000801800606c09800e00003c04800c04200000600000a00000200002200200401a01e00200600000000a00000e01800202402802600200200003a01a00200000000e00203400002000a00001600205800600a02200c04200200605c00400200000000800000000a00c00002000c02603001400001000201e0820380140100240a200000000000a00402800a02000e00600000000800a05000200200400800c00200800e00002800602c01200601a02600001600400401000800000800a00200404e00001c01c00601a00002400400005402000600000200a01400006800200601201000000003e00200601c00000a06801c00000000406e00000c01200001e00c00001200c00201a01a00a00801000000000401001000e01200a00200a00c00c07e00200404800a03c00801e00601200404600000004800000001601800000400200000001204e01601800201802400200c00000400200601000800601200000200000200400401000000000600600000002200600a01400000a00004601000200202000000200000c02a00e00000200001a00202405603bf59654055fcc92a02bff5495015bfaa4a803efd5254057f8a92a02bbc5495015ffb1ca80aff98e54015fcc72a02bfd63950017eb1ca80aff18e54015f8c72a00fff5395007bfa9ca803ff94e5401ff8a72a02bfe4395015fe21ca80affd8a54055fec52a02bfe62950037f314a80aff58a54215fac52a02bfc62950037e314a803ffd4a5401efea52a00ffe5295007fea94a842df54a5401ff8a52a02bff4295015ff214a80aff50a54057f8852a10bff3295085ef994a842ff8ca54217fa652a10bdd3295085fe194a80affd8654057fcc32a012fe6195015feb0ca800bf58654057f8c32a00fff5195007bfa8ca803ff1465421ffe632a10ffc3195085ff90ca842ff88654217fa432a10bfc2195015ffb04a80aff98254005fcc12a02bfd6095
  | 11 => 0x28f440003a5058009819c44381f020065f2918fd8c800f3000118c2d075b1a391e00006f035c1864000000000147855a0000000a0c60e2ee1c4897c9ac2b23f99650f3c7ec00000000627e93998000000759000000013a0002eea140cae50d00003ec5ba7f200000000000853f30d7400012000000000008841369504cd63330001f68000000027000000074200018bc3148b92f01b98c180003159c943d070b2a4975800000009793c47a68312fe0a4cb1649e09d8148b8a503085141c7200ac38ea2ecd9400c04881f87c410523f865cdb815f0e91898a8a0c71b49ba08605933779ef06f03d814585440248bd2c6a3147765d80938ce03480f83c502b80005e4429892c02864e2c09ac8bb40f62bb90640001c342f07dc95070a3f7056446a03a44f965c93a2bf2740100b700af1b707b025878c0c209886f48411b40a5075838f37f803408e1e026521300c23443a2a334f00000144906879240b21e893d0d21212990e4802e0ea000a07cb2433f1fa17fc60600041405b84f600000004a81444280a400010da7af446000000080440e00005bc0000000598ca222612190fc00025819ba24400000000000005e81f045b10d85f482a000040c9b01562d0899c96272704717b4b2c1ca0700550a501d020b0e44a680001e300f0cc24da0c59b6cf5c1dd00020acc3a0c432287e4d2276b41d00007723310000000000000000052c3205000000000b0004243f008ccbc46e00482b4cfe20d0d51c4c84a28419714289b600019100007e20004098a043dc00008c994c0504fe35806388941c71198cb43d276a0c40ed117c6dd1201deccb05a01b6a1f0b046e737f1ec40a86df3bf9e2ce7e1641ec8bcc0160b601e02001000606400000000e01a02400000400200c06c01400602200400805200a00201800000602000000c00000000400200200204402202400800601c08e01000205800200601600800405802800e02a00000600601200200600402e07a01200204c00000200600000a00000200000e00000200000200a00600800000a00c01200600002000400602c00200600000200800800800000000602a00200800202e00600000601601600600201600a02400200001201201a00200200002e00200000403400e04402e0dc00200405203800401600c00e03e00004800600000200001800800800000a00c00000200000e00000002200000601800400001600000600003000000000208c00800200001a01600000200004e00000400a02800000000005400000002000600000600800400000200001403400000201200e03401600201201200200401c00200000c01c00400c00a00000c00000000001802a00001201c00202203a03400201e05a00200a00002e02a00000202800002c02a00200000800007c00007600800600000c0180080000460
  | 12 => 0xef00002c05004af41914742d805d0398c709ca076101802c8388a50f0951c2ea1672a59bb4e2a7d10d888c4c967de3758bb47963a4366a26cfa821c1ee13b47de12315e16d000047130202c8fac4291a095b90e60a600009903c600004e1d7800010c00011b02688ae00010e0000000000172458e3182628000f6c0000000f3892600000000003d404432b00403c845f1220d5c60042b0000000e0a0003b800006a80000c0800000000010b1d5c0001040000f3c9307cc00020b095406c0000000b4e4f646890b0a2a0cd00009180007740e200010405f038604ac0008ad000115cc4a0781239ff48b20002e38eb40007092dd8bc505c32736298a4c220b51ca0c189b87a53220000b7249624f997504440c34b09484e830e14780011401020da87d4e361710001e5cfae1d400000007825aa000000000046a40e9a9c0002d309a93789c26890fe800091c77a000228d1c6227269029405c69332ca1ac7cc41e2b68ad40ae3973980f8485416533608e00000903b79ea000066300005b459c76622183a431e1e246c800116668c407a0340be54c44697acedc4a9304943cf286be17f1404ef24211e616f00de207384029c53625c18580009c65fb2b01700b525d224280000000b10001b450ea32144c8828aec0fa054986d0a80fd3468cd80fe16243b80000000003ff924068a5f823c95c8f266ab243a28848a47b1059d8504a4ff0d616e8fda0001640e58a9e6721820d805f20e23d38d0cbe47fa44d1bccbdc82133c913063219e06786f06b60002fe93e40000003ba9c051a800043c06f826c59831f8e149642b739d8f5504629234c0000d4a53944e1114b6a3bf2d881b80002971d40ab09a26d018120b4ebe8d3425008801e62e0b18218cb88802fb06d83ec8621c214e8d486c32b88000a4c79905b99202b476c000141800021f0001aa42b08052b28f80f422c32a70000d8c21009c8d680002212698c04a3e43c2d313740000000400000c6e64c28d187cd144d52b39a7c40a88a0180c6c69877342e96c05340003b38a14e6438327d8af4ff026e3ed895c0145402c89c005ee0640cd1c501b82a429f14fc00032c23d1ab4ed23e722902a8a7a3550cb199406431d2b309c07f60e639a15201ca8c41580ee065208246716ccaf87d9286178ce7c87607404e0e6a1c10d800ccf6a45424d8140c001cf0629460d888b711d95405ea62a35e9c845941061d1a20c8f84bb038867518c1011b21f8c8125e51ff03651746f414b0d0800048631a11f80344152eb9be86be290150800070c00031186b4b325512ca96c80004fc0000854e9a0003e49f708b869e2c817a8a1c3500970800d7e5fa1731d80b3c76811902f02744761918b7cc2e00000004987e06f719e800033e5611358e2cf9c00000000000005cc3e118c104c00022696705e076200005
  | 13 => 0x2500f213508f8a364ba3ce1284e448470000df4fd66050070000a1053c2908928000716000000111227d18981d46740530390838c342b40f791acc6c0160a7a1a11608520000374ba088524ba2f0e3006900000006288114721f0c5468883db80000ca8c90aa976511613c223050919839e27b83500002d500000002ae5c823a1ba40000cb4480bc8e9c0002a68000f907bd40a8b6c07a4bd1e5117828a4692c709b06d60250001ee400068e3ab0db0dae86c0a820d46565be1bd863079a35331387687b400001021140000002bea17c73a0ec2f384200000d02612320ff678d0001550f943c3009a0cc9c459b1b51a410203c53ae1c5c08c36537b1b38d0442203b8044ade4f215b050101207927221e41a64a4452077109274406a9754ee21e61f51b847a21430ef026c58475a2e5812cab47cf4030f1ce201b43a4824c47a0b809b9618c5042e0041f9ccd07b838910909563264268c446b00fc1c422c90f63a5232038c27a0491b98a390de79d0001098e8e00029a9be00004f5259991caaa7f10a6000091488e0001e1447e16b00010007ae055000092400000005e807915e4a2000156c0007b336a9490c1c24114c9b7827c0002e8800091e80131c2120af67a43f79a211c20001f606e8b062e910c1e08ae885a0490dc0c242662fb8a9514c19b031058426087f40b0fe467855e3211a044ea084425945828208c33a9510c74000345a0fc6c64ae35d157c4d20001761ddc18c4f41538000aa452d31d9448068510230847099283d0001cd81b44c3375000000000000015d45ae4a60020aa0a2679f00000000008cf000000000021d192842d0720002a99244b1e3673dd0000d0672a01b00010dc68f00018840000001981ce00544493eea01ce5862d342944452a0a12f89abd02851c336a0381321df465948850c46841e13a40000fe1be10cc27e320094909cf1c5190000000e9e000295084800084e0c00f209800002e122a8db20673ef84508b087004484c4fa661e25295180000d743d1c1101457e043800000087200000008da0be3281ad800061825a1e6058277c4058000000000000001858a0c30001b4800017042a87604844551b3000071c2fd00013105c44bc03d8000e964b600015ccc720003bc00000008df15c8b70b5a6f90000000a6c10d1531558c040c1091075c0001092ce83249240000000634ddc15c46d00004a8740088982800035e0001dd800038d2ab94100004cd2b413f40006ec0bc1a6412e0c836d202005224d0000cd400072b00000009408e20000e280008dd2de919c0004c83d0170439c000223a00800000022e9340c0c2af25a91080005250dc9cbc76e43539b8000b588403430000c1a02b18d0ed80007e43968d70bfc0003e9105006a707275118907c11d00022844fc0002f7800068c0000168ffc1724
  | 14 => 0x74c32780004f84f3000000047243415d9b048a000215988309ce0e4089828d06c0f12b180000004031991450fc241f0001b90c2027316000010681c62b5199c6947953d695fc00064d1ba0c3ccee46f036905c4c25580139624d2a45a000000000072910d0d5857c3bd0d71b9411e8953c41d90180000000080434c3d62c51fa86240ab000051c39a3762901aa0ab23a118404911683db417807d1707ac1450fc83506cf1fe1c90c385700000b9076a6943589f8889c7c702f21800000741d7904cf12377118206c94600038c812881c6cc0f985dcd927480d115a44c064118b0c280c621331e23489be19428494b8c640eb19c864cbe62060001f143e47e51ac923000030c0fd8b58e7a2cc4091bf003a5e9000000045418304f9dc85524ce0000f74d6a89402780010327f000002a087453004d041c0000001c0167c0001c500018f80006ac435194904e3e812883d00001a10dc235c00081e1d714c4dc67cd0000aacd9667300006c897c4ec331162053e1250000e984aa3a0206a16075438c0001a5c4de1c006c0664f464d73ac100400000044c0000d4c6d32e51e1c22a64645496d8d663c211412201da517138837c23c0b43348dfc42e31f1cfa27481037500c0f00e3e8a810d9fa070481800aa36c8e40002e7800022e152000210cd540000e8a09058867b00005a83980ca0001eecca848b21008b0a84418209088c00070d0000ae00003ba4289194b464cc17584605d01bd3ff0ecca944530d38160f801a9427a0307024d426092540b23a744105e512c0a43a90fdd1024803c906ecf565a53019a6c0001f441808d11940001f281350c80ff2979bd4c627411868f7c0001a31a790100000033fa08243f814d31019e86a429e3aa82600e006011796681846bc02890ec0b81af157028055411f0fc05ec0007aa3cd99b8f225a2222097444039a0ca938025a4411d10000d5c38705d2218f5225619d8878e1e6331fe80000003e316890f82f86d833818f40005a425699d800003f38f11c05401c940d18d476200016c92e412a25b36b11f508871c1510e710c62141cc84c8f7e7f730996fc22c8561df00e400041000299c42bc2760b7a31ca0a1fe12c97a0000000170a000d805e60038cbc99e85933f000058c8171a4816ce2257a00007b4ac48de0001df800075400000000f40212ea000000000000022fc45a5430f28070e1c73c35c80002b653739180011567061cd922419c7b211d19bc98e0f01e8195441e2fb0c88bf012c4b70f391446c47f62d41d8c7ea5f54589a74efa42d13d129ce8608d30097109dc03b29c022c3b60f705b098cd4685c0a2011506e1f13e203e42f43d223006cc0005dc3350b480006d42730cd0a762482118fe87884731281a8403642f020a15cc865ab18804cd14e4374680e541a22e33d30df80008e00000
  | 15 => 0x5249026783da176c97e6a02c6043c0d411b1729b080b44840000000b082cd33200007a87533438000ac845b000076434a8422b600008624f835da23c0cc0811b78de400065b35a0bbc6e2781305875800000001f120c000000000000036e6742469fd40000883c193c000029c24d0614114861414a24880a45612600006960000e980000000000001d942fa5272e70b40778000000216d0e80000000e4cf7c7b017f98201062d820d872ccfa6fd26c8000d080e73b695ac0002f805f800000033e16493e80004111f480008cc17f2038000a520000000ec91aa2190b988902d22ea44b8000000533000000089073900014ac8ea1fa1738a3400018611b00dc49c7fc000183ccb4000192038400000000008107c83eb139219893250b02189a0b9a00000022790e275d11700986542cf20e9a4888062400004389581c800000005c044f1fc000053047714406ac0ac0000001adc0000000001f2cfc04022f61b807303b02c28ca00007200359f4116a34d12d1209076189394103c0326c84600c7813c0480f58d440fa1103a317785ec000381992423400000000009d60000891cc405e4391b916dc00078415d230869c5af115800000000043e9d44bc269a1ef099400030500003b8000838340000000000038d036cc446143e088f0de455c04a1270ccc1720e109dc50e00006f00000008c300010c8fb00000690000bc40000df98580000000160574f2040a33e00007560000bf1e691b031501200005626a20000330aba3a916580005045c620312e000086739307546808ac397200c5a86c70c905d04225ae07a80011266fb0ff974ce043173e31e3c2ec0002960000ea00000c100000002da0000894ff22531f7131800000018480010ca22231612509600680a70a44faa000000132c28c29d2ef83bc690578225970c45218700015e40006f100014084bc27846b000000000042300011b828c0d017e4c0e0d633000e000020205d82ccc2a2080001e18c9473a0cc0000d385f413f961c6c20003cb08dc00015300009e4dc48c11f680007e6
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7654c1001e7e6554c100067d6554c10006be6454c10006bd6454c10016de6354c10006dd6354c101feee6254c10054ff76d0c1002cfe76d0c10004fd76d0c1002cfc76d0c101f67e65d0c100067d65d0c10056be64d0c10006bd64d0c10016de63d0c10006dd63d0c101eeee62d0c10025f671d0c10005f571d0c10004ff7650c1002cfe7650c10004fd7650c1002cfc7650c101e67e6550c100067d6550c10056be6450c10006bd6450c10016de6350c10006dd6350c101deee6250c10006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ce7358810006ed7358810006cd7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec3158810036ef705881002eee7058810036ed705881002eec7058810006ef505881002eee505881002eec505881002eee405881002eec4058810006ef305881002eee305881002eec3058810026ef1058810026e7105881002eee1058810026ea1058810026ed1058810026e9105881002eec105881007cff765401001e7e65540100067d6554010006be6454010006bd6454010126de6354010006dd635401011eee6254010006ed6254010004fd76d00101167e65d00100067d65d0010056be64d0010006bd64d001010ede63d0010006dd63d0010106ee62d0010006ed62d0010004ff76500100057f75500100457c75500100ee7e65500100067d6550010056be6450010006bd64500100e6de6350010006dd63500100deee6250010006ed6250010074ff764c0100a67e654c0100067d654c010006be644c010006bd644c010016de634c010006dd634c01009eee624c010006ed624c010076fa604c01002df77644010006f77644010004f7764401002ef7654401002f766544010006f5654401002f75654401000675654401002ef7644401002fb66444010006f5644401002fb56444010006b56444010007d77344010007d4734401002ef7634401002fd66344010006f5634401002fd56344010006d5634401002ef7624401002fe66244010226f5624401002fe56244010006e56244010227775244010227755244010227d73244010227d5324401002df77044010027f3704401002ef6604401002ff2604401002ff23044010007f1304401002ff22044010227f12044010
  | 1 => 0x9010006bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf32590100069f3259010006be3259010006bd32590100069d3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901002ebe705901002ebc7059010006bf505901002ebe505901002ebc5059010006bf305901002ebe305901002ebc3059010006bf205901002ebe2059010006bd205901002ebc2059010026bf1059010026b7105901002ebe1059010026bd105901002ebc1059010054ff769501002cfe7695010004fd769501002cfc769501001e7e65950100067d6595010056be6495010006bd649501021ede6395010216ee6295010004ff765501002cfe7655010004fd765501002cfc765501001e7e65550100067d6555010056be6455010006bd645501020ede6355010206ee6255010004ff7558c1001cfe7558c1001cfc7558c10004ff7458c10054fc7458c1002cff7358c1002edf7358c10006df5358c1003ede5358c1003edc5358c1003ede4358c1003edc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c1003edf3258c10006de3258c10006dd3258c1003edc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c10026de3158c10026dc3158c10014ff7058c1002cfe7058c10014fd7058c1002cfc7058c1002ede3058c1002edc3058c10026f71058c10026fa1058c10026f91058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10004df7258c10006de7258c10006dd7258c10004dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c100065d5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c1003edf7058c1002ede7058c1002edc7058c10006df5058c1002ede5058c1002edc5058c1002ede4058c1002edc4058c10006df2058c1002ede2058c10006dd2058c1002edc2058c10026df1058c10026d71058c1002ede1058c10026da1058c10026dd1058c10026d91058c1002edc1058c10004ff7654c1002cfe7654c10004fd7654c1002cf
  | 2 => 0x2e7e505941002e7c5059410026f710594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100047f72594100067e72594100067d72594100047d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100065f32594100067e32594100067d32594100065d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c21594100467f705941002e7e705941002e7c705941002e7e405941002e7c40594100067f305941002e7e305941002e7c30594100067f205941002e7e20594100067d205941002e7c20594100267f105941002677105941002e7e10594100267d105941002e7c1059410056bf7599010056be7599010056bd7599010056bc7599010056bf7399010056be7399010056bd7399010056bc7399010006bf5399010006be5399010006bc5399010056bf7299010056be7299010056bd7299010056bc7299010006bf52990100063f5299010006be5299010006bd52990100063d5299010006bc5299010006bf32990100069f3299010006be3299010006bd32990100069d3299010006bc3299010026bf7199010026be7199010026bd7199010026bc7199010026bf5199010026be5199010026bd5199010026bc5199010026bf3199010026be3199010026bd3199010026bc3199010026bf2199010026be2199010026bd2199010026bc219901002ebe709901002ebc7099010006bf509901002ebe509901002ebc5099010006bf309901002ebe309901002ebc3099010006bf209901002ebe2099010006bd209901002ebc2099010026bf109901002ebe1099010026bd109901002ebc1099010004ff755901001cfe755901001cfc755901002cff745901002ebf7459010006bf5459010006bc5459010004ff7359010014fe7359010014fc7359010006be4359010006bc4359010004ff725901000cfe7259010004fd725901000cfc72590100067f52590100067d5259010006bf4259010006be4259010006bd4259010006bc4259010006df3259010006dd3259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc4159010054ff705901002cfe7059010054fd705901002cfc705901002ebe405901002ebc4059010026f71059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bc5359010006bf7259010006be725
  | 3 => 0xc76d0110006bf64d0110056bc64d0110006df63d011010edc63d0110025f671d0110005f571d0110007b541d0110004fe7690110006df63901100f6dc6390110054ff7650110004fd7650110024fc76501100057f755011006d7c7550110006bf6450110056bc6450110006df63501100e6dc6350110005f77150110025f47150110007b54150110004fe761011006d7e75101100057d7510110065de7310110005dd7310110006df63101100c6dc631011005dee7210110005ed7210110025f67110110005f5711011008cfe768c110006df638c110016dc638c110007d6318c110005fa768c11008efa768c110065f9738c110007db638c110016fa638c110016f8638c110067d8638c110016d8638c11025dfb728c11025df9728c11024f7b528c11024f79528c110067db328c11024fd9328c11002ff3718c110025fa718c110025f8718c11002ff0718c11002efb618c110007f2518c110007f1518c110007f2418c110007f1418c110257da318c110067f2318c110007d2318c110067f1318c110257d8318c11024ff2218c11024ff1218c110014ff764c110064fd764c110024fc764c110006df634c110016dc634c110005f7714c110025f4714c110007d5314c110067d8304c110025f8764c110016f8764c110024f8764c110065fb734c110007db734c110007db634c110016fa634c110016f8634c110067d8634c110067da534c110007d9534c110067da434c110007d9434c110245fb724c110245f9724c11023f7b524c11023f79524c110067db324c11023fd9324c110007f3714c110025fa714c110025f8714c110007f0714c110007f2514c110007f1514c110007f2414c110007f1414c110067db314c110067f2314c110007d9314c110067f1314c110007d1314c11023ff2214c11023ff1214c110006df6384110076dc6384110025fa7084110026fb6084110025f6768411002ef67684110024f6768411002df77584110005f5758411002df77484110005f5748411002df77384110005f57384110007d76384110007d4638411002df77284110235f5728411022f77528411022f75528411022fd7328411022fd5328411002df6708411002ef76084110027f3608411002ff23084110007f1308411002ff2208411022ff1208411002cff755941002e7f7559410004ff7459410054fc74594100467f54594100467c5459410004ff7359410014fe7359410014fc73594100467f53594100067e53594100467c5359410004ff725941000cfe7259410004fd725941000cfc72594100467f52594100067e52594100067d52594100467c5259410006df3259410006dd3259410024ff7159410024fe7159410024fd7159410024fc71594100267e51594100267c515941001cff705941002cfe705941001cfd705941002cfc7059410
  | 4 => 0x4510027f3605451006f7750545102aff220545102aff12054510004fe76d051002cfc76d0510006bf64d0510056bc64d0510065de73d0510005dd73d0510006df63d05101aedc63d0510005fa70d0510005f970d0510005f67690510026f67690510025f77590510027767590510005f57590510027757590510005757590510006f76590510006f5659051028df57490510056f66490510056f46490510005f57390510007d76390510196f66390510196f46390510007d46390510196d46390510025f772905102a5f5729051029ef7629051029ef5629051029f77529051029f75529051029fd7329051029fd5329051002df67090510026f76090510027f3609051029ff2209051029ff12090510054fc7650510006bf6450510056bc6450510006df635051017edc6350510027b44150510005fb7050510005f87050510056f47650510054f47650510005f77550510005f57550510006f76550510006f56550510025f77450510027b77450510007b76450510056f66450510056f46450510007b46450510297b75450510297b45450510005f77350510007d7635051017ef6635051017ef46350510007d4635051017ed46350510007b74350510007b5435051028df7725051028df57250510286f76250510286f56250510287775250510287755250510287b74250510287b54250510287d73250510287d53250510007f3705051002df47050510007f07050510026f76050510027f36050510287f22050510287f12050510005f6768c510026f6768c510025f7758c510005f5758c510025f7748c510005f5748c510065f5738c510007d7638c510016f6638c510016f4638c510067d4638c510016d4638c510067d6538c510007d5538c510067d6438c510007d5438c510025f7728c51027df5728c51027777528c51027775528c510067d7328c510277d5328c510027f3708c51002df6708c510027f0708c510026f7608c510027f3608c510067d4308c510277f2208c510277f1208c510014fc764c510006df634c510016dc634c510027d4314c510005fb704c510005f8704c510027f0104c510065f4764c510016f4764c510014f4764c510005f7754c510005f5754c510005f7744c510005f5744c510025f7734c510027d7734c510007d7634c510016f6634c510016f4634c510067d4634c51026df7724c51026df5724c51026777524c51026775524c510067d7324c510267d5324c510007f3704c51002df4704c510007f0704c510026f7604c510027f3604c510067d7304c510267f2204c510267f1204c510094fe7694110006df6394110136dc639411001cff765411006cfd7654110024fc76541100067f655411001e7c6554110006df6354110126dc6354110005f77154110025f47154110007755154110024fe76d0110024f
  | 5 => 0x6df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d10256de71d8d10006dd71d8d10256dc71d8d10006df51d8d10256de51d8d10256dc51d8d10256de41d8d10256dc41d8d10006df21d8d10256de21d8d10006dd21d8d10256dc21d8d10256df70d8d10066de70d8d10006dd70d8d10006df50d8d10006dc50d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d10256df10d8d10256dc10d8d10066dc6358d10004ff7558d1001cfe7558d1001cfc7558d10004ff7458d10054fc7458d10064ff7358d10006df7358d10004ff7258d1000cfe7258d10004fd7258d1000cfc7258d100067f5258d100067d5258d10066df3258d10006dd3258d10074ff7158d10006f77158d1008cff7058d10006fb7058d10005de7618d10066de7618d10004de7618d100675e7518d100675d7518d10006df6518d10006de6518d10006dd6518d10006dc6518d100679e7418d100679d7418d10006df6418d10006de6418d10006dd6418d10006dc6418d10065df7218d10067ce7218d10005dd7218d10067cd7218d10005cd7218d10006df6218d10006de6218d10006dd6218d10006dc6218d100075f5218d100075d5218d10067d57118d10007d62118d10007d52118d10067d97018d102cedf6018d10007da2018d10007d92018d102cfdb1018d102cfd81018d10004ff7654d10004fe7654d10004fd7654d10004fc7654d1001e7e6554d100067d6554d10006df6354d10016dc6354d10054ff76d0d10004fe76d0d10004fd76d0d10054fc76d0d10056be64d0d10006bd64d0d10006df63d0d10016dc63d0d10025f671d0d10005f571d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10056be6450d10006bd6450d10006df6350d10016dc6350d10005f67694510026f6769451006df5759451001ef6659451001ef46594510027b67494510005f57494510027b57494510005b57494510006f76494510006f56494510005f57394510007d76394510007d46394510025f772945102c5f5729451006f7752945102bf7552945102bfd732945102bfd5329451002df67094510026f76094510027f360945102bff220945102bff1209451001cfc76545100067f655451001e7c6554510006df63545101c6dc6354510027745154510005fb7054510005f8705451006df4765451001ef4765451001cf47654510025f7755451002777755451000777655451001ef6655451001ef4655451006f746554510005f77454510006f76454510006f5645451000776545451006f745454510005f77354510007d76354510007d4635451006f7753545100077553545102b5f772545102b5f5725451006f7752545102af7552545102afd732545102afd53254510007f3705451002df47054510007f07054510026f7605
  | 6 => 0xd325951007cff7159510006f77159510094ff7059510006fb7059510054fe76d911001cfe75d9110004fd75d911001cfc75d9110014fe73d9110004fd73d9110014fc73d9110004ff72d911000cfe72d9110004fd72d911000cfc72d91100067f52d91100067d52d9110006df32d9110006dd32d9110024fe71d9110024fc71d9110006f621d9110006f521d911002cfe70d911002cfc70d9110006fa20d9110006f920d9110006bf6499110065de7399110005dd73991100057f755911006d7c7559110005df7359110065dc7359110005ef725911005dec7259110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec72591100067f52591100067d5259110006bf4259110006bd4259110006df3259110006dd3259110004ff7159110006f77159110006f62159110006f52159110004ff7059110006fb7059110006fa2059110006f92059110004fe7619110056be6419110006bd6419110054ff7695110004fe7695110004fd7695110054fc76951100067f659511001e7c659511021edc6395110025f67195110005f57195110004ff7655110004fe7655110004fd7655110004fc765511020edc6355110014fe76d8d10066de63d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10054fe74d8d10004fd74d8d10006df53d8d10066de53d8d10066dc53d8d10066de43d8d10066dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10066df32d8d10006de32d8d10006dd32d8d10066dc32d8d10024fe71d8d10064fd71d8d10024fc71d8d10066df31d8d1002cfe70d8d10024fd70d8d1002cfc70d8d10066df30d8d10065de76d8d10014de76d8d10006df65d8d10006de65d8d10006dd65d8d10006dc65d8d10006df64d8d10006de64d8d10006dd64d8d10006dc64d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d100075f52d8d100075d52d8d10007d771d8d10007d621d8d10007d521d8d10257db70d8d10007da20d8d10007d920d8d10257db10d8d10257d810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df52d8d100065f52d8d10006de52d8d10006dd52d8d100065d52d8d10006dc52d8d10
  | 7 => 0x8e1000cfc7258e100067f5258e100067d5258e10076df3258e10006dd3258e10076df3158e1002cfc7058e1002ede3058e1002edc3058e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e1001e7e6554e100067d6554e10016de6354e10006dd6354e10054ff76d0e1002cfe76d0e10004fd76d0e1002cfc76d0e10056be64d0e10006bd64d0e10025f671d0e10005f571d0e10004ff7650e1002cfe7650e10004fd7650e1002cfc7650e10056be6450e10006bd6450e10016de6350e10006dd6350e1001cff765461002cfc765461001e7e65546100067d6554610005fb705461002df87054610056be64d0610006bd64d0610075de73d0610005dd73d061002dfa70d0610005f970d0610054ff7650610056be6450610006bd6450610005fb705061002df87050610014ff764c61002cfc764c610016de634c610006dd634c610005fb704c61002df8704c610044ff765421002e7f655421002e7c655421002ebf64d021002ebc64d02100057f755021007d7c755021002ebf645021002ebc645021002df9768c21002ef9768c210024f9768c210016fa638c21002fda638c21002fd9638c21002ef8638c21002dfb728c2102f5f9728c2102ef7b528c2102ef79528c210077db328c2102efd9328c210025fa718c21002ff2718c21002ff1718c21002df8718c210257da318c210257d8318c21003cff764c21002edf634c21002edc634c21002fd8304c210005fb764c21003efb764c21002fdb734c21002fdb634c210016fa634c210016f8634c21002fd8634c210077da534c210007d9534c210077da434c210007d9434c2102e5fb724c2102e5f9724c2102df7b524c2102df79524c210077db324c2102dfd9324c210025fa714c210025f8714c210077db314c210007d9314c21002df576c4210026f576c421002ef765c4210006f565c421002ef764c4210006f564c421002ef763c4210006f563c421002ef762c42102d6f562c42102d77752c42102d77552c42102d7d732c42102d7d532c421002ff260c421001cfe76d951006e7e65d9510054fe74d9510004fd74d951006e7c54d9510014fe73d9510004fd73d9510014fc73d9510004ff72d951000cfe72d9510004fd72d951000cfc72d951006e7f52d95100067d52d9510006df32d9510006dd32d9510024fe71d951006cfd71d9510024fc71d951006e7f51d951002cfe70d9510024fd70d951002cfc70d951006e7f50d951006e7c6559510005df7359510065dc735951006cff75595100067f7559510004ff7459510054fc7459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc735951006e7f5359510004ff725951000cfe7259510004fd725951000cfc725951006e7f52595100067d5259510006df3259510006d
  | 8 => 0x25f671d0310005f571d0310007b541d031002df47190310054ff76503100057f75503100957c7550310056be6450310006bd6450310005f77150310025f47150310007b541503100957e75103100057d751031008dde7310310005dd7310310085ee7210310005ed7210310025f67110310005f57110310064fd768c310256df638c310016dc638c31002df4718c310257d6318c310014ff764c310024fc764c310016de634c310006dd634c310005f7714c310025f4714c310007d5314c31007cfd75d9610054fe74d9610004fd74d961007e7c54d9610014fe73d9610004fd73d961002cfc73d961002cff72d961000cfe72d9610004fd72d961002cfc72d961007e7f52d96100067d52d9610006df32d9610006dd32d961002ef571d961002efa70d961002e7f50d961001cff765961002e7c655961002e7f7559610004ff7459610054fc745961007e7f5459610004ff7359610014fe7359610014fc735961007e7f5359610004ff725961000cfe7259610004fd725961000cfc725961007e7f52596100067d5259610006df3259610006dd325961007e7f515961002cfc705961002e7e505961002e7c505961001cfe75d9210004fd75d921002cfc75d9210014fe73d9210004fd73d921002cfc73d921002cff72d921000cfe72d9210004fd72d921002cfc72d92100067f52d92100067d52d9210006df32d9210006dd32d921002ef571d921002efa70d921002efa20d9210006f920d9210004fd769921002ebf649921002ebc6499210054ff76592100057f755921007d7c755921002ebc6459210004ff75592100067f75592100047f755921001cfe755921001cfc75592100067c755921001c7c755921002ebf7459210004ff7359210014fe7359210014fc7359210004ff725921000cfe7259210004fd725921000cfc72592100067f52592100067d5259210006bf4259210006bd4259210006df3259210006dd325921002cfc705921002ebe405921002ebc4059210006fa2059210006f92059210054ff769521002cfe7695210004fd769521002cfc76952100067f659521001e7c6595210056be6495210006bd6495210004ff765521002cfe7655210004fd765521002cfc765521001e7e65552100067d6555210056be6455210006bd645521001cfe75d8e10004fd75d8e1002cfc75d8e10054fe74d8e10004fd74d8e10074fd73d8e1002cff72d8e1000cfe72d8e10004fd72d8e1002cfc72d8e100067f52d8e100067d52d8e10076df32d8e10006dd32d8e1002ef571d8e10256de31d8e10256dc31d8e1002efa70d8e1002edf30d8e10014ff7658e1002edc6358e10004ff7558e1001cfe7558e1001cfc7558e10004ff7458e10054fc7458e1002edf7358e10076de5358e10076de4358e10004ff7258e1000cfe7258e10004fd725
  | 9 => 0xc5159710026f641597100967f5059710004ff755931001cfe755931001cfc7559310026bf7459310006bf5459310006bc5459310004ff7359310014fe7359310014fc7359310004ff725931000cfe7259310004fd725931000cfc72593100067f52593100067d5259310006bf4259310006bd4259310006df3259310006dd3259310024fc7159310026f65159310026be4159310026bc4159310026f62159310006f52159310054ff7695310024fe7695310004fd7695310024fc769531001e7e65953100067d6595310025f67195310005f57195310004ff7655310024fe7655310004fd7655310024fc7655310025f67155310004ff7558f1001cfe7558f1001cfc7558f10004ff7458f10054fc7458f10026df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f1008edf3258f10006dd3258f10024fc7158f10026de3158f10026dc3158f1008edf3058f10026fa1058f10026f91058f10004ff7654f10024fe7654f10004fd7654f10024fc7654f1001e7e6554f100067d6554f1033edf6354f10016dc6354f10025f67154f1033fd63154f10054ff76d0f10024fe76d0f10004fd76d0f10024fc76d0f10056be64d0f10006bd64d0f10025f671d0f10005f571d0f10004ff7650f10024fe7650f10004fd7650f10024fc7650f10056be6450f10006bd6450f10336df6350f10016dc6350f10025f67150f10337d63150f10025f77654710046f7765471002777755471002777655471001ef66554710026f46554710027746554710005f77454710026f76454710006f56454710007765454710097745454710005f7735471009777535471000775535471032df7725471032df57254710097775254710327755254710327d73254710327d5325471002df47054710097775054710025f77650710006f77650710005f77550710005f57550710026f76550710006f56550710027b77450710027b76450710056f66450710026f46450710027b4645071031fb7545071031fb45450710005f7735071017ef66350710026f46350710007b74350710007b54350710315f77250710315f57250710026f7625071030ef5625071030f77525071030f75525071030fb7425071030fb5425071030fd7325071030fd5325071002df47050710025f7764c71003ef7764c710005f7754c710005f5754c710005f7744c710005f5744c710027d7734c710027d7634c710016f6634c710026f4634c710027d4634c710305f7724c710305f5724c7102ff77524c7102ff75524c71008fd7324c7102ffd5324c71002df4704c71008fd7304c71006cfd769431002df4719431001cff7654310024fc765431001e7e65543100067d6554310005f77154310025f47154310007755154310056be64d0310006bd64d0310
  | 10 => 0x853000cfc72d85300067f52d85300067d52d8530076df32d8530006dd32d8530076f631d8530076f531d8530006f721d8530006f421d853002cfe70d8530006f76198530065f9709853008dfb70585300a57e75185300057d7518530005be7418530005bd741853009dee7218530005ed7218530026f66118530006f56118530004fe7694530004fd7694530024fc7694530005be7494530005bd7494530015de7394530005dd7394530005fa7094530005f97094530004ff7654530004fe7654530004fc765453001e7e65545300067d6554530015de73545300075d5354530004fe76d0530004fd76d0530054fc76d0530056be64d0530006bd64d0530015de73d0530005dd73d05300079d43d0530004fe7690530004fd7690530024fc76905300a57e75905300057d7590530015de7390530005dd7390530006f76190530026f46190530197d73190530005fa7090530005f97090530004ff7650530004fe7650530004fc7650530056be6450530006bd6450530015de73505300079d4350530006f76150530026f4615053017fd73150530004fe7610530004fd7610530024fc7610530015de7310530005dd7310530005fa7010530005f97010530024dc764c530005df754c530005dd754c530005df744c530005dd744c530365df724c530365dd724c53035edf624c53035edd624c53035f5f524c53035f5d524c530015df714c530017d7714c530007d7614c530026de614c530026dc614c530007d4614c530007db704c53002ddc704c530007d8704c530016df604c530017db604c530354fe769413002ddc739413001cff7654130014fe7654130124fd7654130014fc76541300067f655413001e7c6554130005df7354130015dc73541300075d5354130014fe76d0130014fc76d0130006bf64d0130056bc64d0130015de73d0130005dd73d01300079d43d01300c4fe769013002ddc7390130054ff7650130014fe76501300e4fd7650130014fc76501300057f75501300a57c7550130006bf6450130056bc6450130005df7350130015dc73501300079d43501300f4fe76101300a57e75101300057d7510130015de7310130005dd731013009dee7210130005ed7210130005f67110130005f5711013002ddf758c130005dd758c13002ddf748c130005dd748c13002ddf728c13034ddd728c130346df628c130346dd628c1303475f528c1303475d528c130005dd718c130256dc618c13002dde708c13002fda708c13002edf608c130017db608c1300267f7559710004ff7459710054fc74597100967c5459710004ff7359710014fe7359710014fc73597100967f5359710004ff725971000cfe7259710004fd725971000cfc72597100967f52597100067d5259710006df3259710006dd3259710024fc71597100267e51597100267
  | 11 => 0xa67c54d953002cff73d9530014fe73d9530134fd73d9530014fc73d95301367f53d95301367d53d9530136de43d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300a67f52d95300067d52d9530136df32d9530006dd32d9530024fe71d9530004fd71d9530014fd70d95300a67f50d95300a67c655953038dfb7059530134ff75595300067f7559530004ff7459530054fc7459530124ff7359530006df7359530126de4359530004ff725953000cfe7259530004fd725953000cfc72595300a67f52595300067d5259530126df3259530006dd3259530004ff7159530024fc71595300a67f515953038cff7059530006fb7059530054fe76d913001cfe75d9130004fd75d913001cfc75d913002cff73d9130014fe73d91300f4fd73d9130014fc73d91300f6de53d91300f6bf43d91300f6bd43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300067f52d91300067d52d91300f6df32d9130006dd32d9130024fe71d9130004fd71d9130006bf6499130005f67199130005f571991300e5f970991300057f75591300a57c755913010dfb7059130004ff75591300067f75591300047f755913001cfe755913001cfc75591300067c755913001c7c7559130006bf74591300e4ff7359130006df73591300e6de5359130004ff725913000cfe7259130004fd725913000cfc72591300067f52591300067d52591300e6df3259130006dd3259130004ff7159130024fc715913010cff7059130006fb70591300f4fe7619130056be6419130006bd6419130054ff7695130004fe7695130004fd7695130054fc76951300067f659513001e7c6595130015de7395130005dd7395130004ff7655130004fe7655130004fd7655130004fc7655130015de73551300a5dc7654d3001edc7654d3001cdc7654d30015df7554d300175f7554d300075f6554d3001ede6554d3001edc6554d300a75c6554d30005df7454d30006df6454d30006dd6454d300075e5454d300a75c5454d30385df7254d30385dd7254d3037edf6254d3037edd6254d300a75f5254d3037f5d5254d30005df7154d3033edc6154d300a75f5154d30007db7054d3002ddc7054d30007d87054d30016df6054d30017db6054d300a75f5054d30056dc7650d30054dc7650d30005df7550d30005dd7550d30006df6550d30006dd6550d30015df7450d300179f7450d300079f6450d30056de6450d30056dc6450d300079c6450d30375df7250d30375dd7250d3036edf6250d3036edd6250d3036f5f5250d3036f5d5250d30005df7150d30336dc6150d30007db7050d3002ddc7050d30007d87050d30016df6050d30017db6050d3001cfe75d8530004fd75d853001cfc75d8530054fe74d8530004fd74d8530004ff72d853000cfe72d8530004fd72d
  | 12 => 0xd52d92300f6df32d9230006dd32d9230024fe71d9230004fd71d92300f6dc31d923002cfe70d923002efa70d923002edf30d92300e4fd769923002ebf649923002ebc6499230054ff76592300057f75592300b57c755923002ebc6459230004ff75592300067f75592300047f755923001cfe755923001cfc75592300067c755923001c7c755923002ebf74592300e6bf43592300e6bd4359230004ff725923000cfe7259230004fd725923000cfc72592300067f52592300067d5259230006bf4259230006bd42592300e6df3259230006dd3259230004ff7159230024fc71592300e6dc315923002cfe705923002cfc705923002ebe405923002ebc40592300e6df3059230054ff769523002cfe7695230004fd769523002cfc76952300067f659523001e7c6595230056be6495230006bd6495230004ff765523002cfe7655230004fd765523002cfc765523001e7e65552300067d6555230056be6455230006bd645523002ef7619863002ef4619863002ef46158630004ff755863001cfe755863001cfc7558630004ff7458630054fc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630066df3258630006dd3258630066f63158630066f53158630256dc3158630006f62158630006f52158630024ff705863002cfc7058630066df305863002ef6105863002ef41058630024ff769463002cfe7694630004fd7694630005be7494630005bd7494630026f66194630006f5619463002dfa7094630005f97094630004ff7654630004fd765463002cfc765463001e7e65546300067d6554630005df7354630015dc7354630026f66154630006f56154630054ff76d063002cfe76d0630004fd76d0630056be64d0630006bd64d0630015de73d0630005dd73d0630024ff769063002cfe7690630004fd76906300b57e75906300057d7590630026f66190630006f56190630257d4319063002dfa7090630005f97090630004ff7650630004fd765063002cfc7650630056be6450630006bd6450630005df7350630015dc7350630026f66150630006f5615063017fd43150630024ff761063002cfe7610630004fd761063002dfa7010630005f97010630006df658c630006dd658c630006df648c630006dd648c630255df728c63039ddd728c630396df628c630396dd628c6303975f528c6303975d528c630015de718c630017d6718c630257d6618c630256dd618c630007d5618c630257da708c630005dd708c630257d9708c630016de608c630017da608c63038cff765423002e7f655423002e7c65542300e4fd76d023002ebf64d023002ebc64d023010cff76502300057f75502300b57c755023002ebf645023002ebc645023001cfe76d95300a67e65d9530054fe74d9530004fd74d9530
  | 13 => 0x8440056f54258440056f44258440006f73258440006d73258440006f63258440006f53258440006d53258440006f4325844002ef6705844002ef47058440006f7505844002ef6505844002ef45058440056f74058440056b7405844002ef64058440056f5405844002ef44058440006f7305844002ef6305844002ef43058440006f7205844002ef62058440006f5205844002ef42058440024ff769444002cfe7694440004fd769444001e7e65944400067d6594440055be7494440005bd74944401d6de6394440006dd63944401ceee6294440006ed6294440026f66194440006f56194440004ff7654440004fd765444002cfc765444001e7e65544400067d65544401c6de6354440006dd63544401beee6254440006ed6254440026f66154440006f56154440024ff768c44002cfe768c440004fd768c4401567e658c4400067d658c440016de638c440006dd638c44014eee628c440006ed628c440026f6618c440006f5618c440004ff764c440004fd764c44002cfc764c4401467e654c4400067d654c440016de634c440006dd634c44013eee624c440006ed624c440026f6614c440006f5614c4400fcff765404001e7e65540400067d6554040126de6354040006dd635404011eee6254040006ed6254040006f66154040006f561540400fefa605404002dbf7650040006bf7650040004bf76500400073f75500400073c755004002ebf655004002f3e6550040006bd655004002f3d65500400063d655004002f9e6350040006bd635004002f9d63500400069d635004002ebf625004002fae62500403a6bd625004002fad6250040006ad62500403a73f52500403a73d52500403a79f32500403a79d325004002fb66150040006bd615004002fb56150040006b5615004002dbf7050040057bb705004002ebe605004002fba605004002fba5050040007b9505004002fba20500403a7b92050040124fd75d9630054fe74d9630004fd74d96300b67c54d963002edd73d963002cff72d963000cfe72d9630004fd72d963002cfc72d96300b67f52d96300067d52d9630136df32d9630006dd32d9630024fe71d9630004fd71d9630136dc31d963002cfe70d963002efa70d963002e7f50d963002edf30d963001cff765963002e7c655963002e7f7559630004ff7459630054fc74596300b67f54596301267f53596301267d5359630004ff725963000cfe7259630004fd725963000cfc72596300b67f52596300067d5259630126df3259630006dd3259630004ff7159630024fc71596300b67f5159630126dc315963002cfe705963002cfc705963002e7e505963002e7c5059630126df305963001cfe75d9230004fd75d923002cfc75d923002edd73d923002cff72d923000cfe72d9230004fd72d923002cfc72d92300067f52d92300067
  | 14 => 0x56ee5458840056ed5458840056ec5458840006ef7358840006ee7358840006ce7358840006ed7358840006cd7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec5358840056ef4358840056ee4358840056ed4358840056ec4358840006ef7158840006ee7158840006ed7158840006ec7158840006ef5158840006ec5158840056ef4158840056ee4158840056ed4158840056ec4158840006ef3158840006ec31588400beef705884002eee70588400beed705884002eec7058840006ef505884002eee505884002eec5058840056ef4058840056af405884002eee4058840056ea4058840056ed4058840056e9405884002eec4058840006ef305884002eee305884002eec305884002eee105884002eec1058840026f77598440026f67598440026f57598440026f47598440026f77498440026f67498440026f57498440026f47498440056f75498440056f65498440056f55498440056f45498440026f77398440026f67398440026f57398440026f47398440006f75398440006f65398440006f55398440006f45398440056f74398440056f64398440056f54398440056f44398440026f77298440026f67298440026f57298440026f47298440006f75298440006775298440006f65298440006f55298440006755298440006f45298440056f74298440056f64298440056f54298440056f44298440006f73298440006d73298440006f63298440006f53298440006d53298440006f4329844002ef6709844002ef47098440006f7509844002ef6509844002ef45098440056f7409844002ef64098440056f5409844002ef44098440006f7309844002ef6309844002ef43098440006f7209844002ef62098440006f5209844002ef42098440004ff755844001cfe755844001cfc7558440004ff7358440014fe7358440014fc7358440004ff725844000cfe7258440004fd725844000cfc72584400067f52584400067d5258440006df3258440006dd325844002ef77158440006f75158440006f45158440056f74158440056f44158440006f73158440006f43158440006f72158440006f62158440006f52158440006f42158440056bf405844002ef6105844002ef41058440006f77558440006f67558440006f57558440006f47558440056f77458440056f67458440056f47458440056f75458440056f65458440056f55458440056f45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f45358440056f74358440056f64358440056f54358440056f44358440006f77258440006f67258440006f57258440006f47258440006f75258440006775258440006f65258440006f55258440006755258440006f45258440056f74258440056f6425
  | 15 => 0xe505944002e7c5059440056bf4059440056fa4059440056f940594400567f74594400567e74594400567d74594400567c74594400067f73594400067e73594400067d73594400067c73594400567f43594400567e43594400567d43594400567c43594400067f72594400047f72594400067e72594400067d72594400047d72594400067c72594400567f42594400567e42594400567d42594400567c42594400067f32594400065f32594400067e32594400067d32594400065d32594400067c32594400067f71594400067e71594400067d71594400067c71594400567f41594400567e41594400567d41594400567c41594400067f31594400067c31594400067f21594400067e21594400067d21594400067c21594400ce7f705944002e7e705944002e7c70594400567f40594400563f405944002e7e40594400567a40594400567d405944005679405944002e7c40594400067f305944002e7e305944002e7c30594400067f205944002e7e20594400067d205944002e7c205944002e7e105944002e7c1059440004ff7558c4001cfe7558c4001cfc7558c40014fd7458c4002cff7358c4002edf7358c40006df5358c400c6de5358c400c6dc5358c40056df4358c40056dc4358c40004ff7258c4000cfe7258c40004fd7258c4000cfc7258c400067f5258c400067d5258c400c6df3258c40006de3258c40006dd3258c400c6dc3258c40004ff7158c40024fc7158c400c6df3158c400c6dc3158c40056bf4058c4002ede3058c4002edc3058c40006df7558c40006de7558c40006dd7558c40006dc7558c40056df7458c40056de7458c40056dc7458c40056df5458c40056de5458c40056dd5458c40056dc5458c40006df7258c40004df7258c40006de7258c40006dd7258c40004dd7258c40006dc7258c40006df5258c400065f5258c40006de5258c40006dd5258c400065d5258c40006dc5258c40056df4258c40056de4258c40056dd4258c40056dc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006dc5158c40056df4158c40056de4158c40056dd4158c40056dc4158c40006df2158c40006de2158c40006dd2158c40006dc2158c400c6df7058c4002ede7058c4002edc7058c40006df5058c4002ede5058c4002edc5058c40056df4058c400569f4058c4002ede4058c40056dd4058c4002edc4058c40006df2058c4002ede2058c40006dd2058c4002edc2058c4002ede1058c4002edc1058c40004ff7654c40004fd7654c4002cfc7654c4001e7e6554c400067d6554c40016de6354c40006dd6354c401feee6254c40006ef7558840006ee75588400066e7558840006ed75588400066d7558840006ec7558840056ef7458840056ee7458840056ed7458840056ec7458840056ef5458840
  | 16 => 0x5403e73d52505403e79f32505403e79d3250540055bf7150540057b77150540007b76150540026be6150540026bc6150540007b46150540007b65150540007b551505403efb731505403efb431505403e7b621505403e7b52150540007bb705054002dbc7050540007b87050540056bf6050540057bb60505403e7ba20505403e7b92050540004fe768c540004fd768c540024fc768c5400067f658c5401567c658c540055be748c540005bd748c540006df638c540016dc638c5400079d438c540004ff764c540004fe764c540004fc764c5400067f654c5401467c654c540055be744c540005bd744c540114fe76941400067f659414001e7c65941400073e54941400ef7b5094140005fa7694140116fa76941400edf975941400077b659414001efa659414001ef865941400ef78659414001e78659414002fbb7494140055fa7494140055f8749414002fb8749414002efb64941403df7a54941400efba54941400073a54941400efb954941403df785494140007bb4394140007b943941403d5fb72941403d5f972941400ef7b52941403cf7952941403cfbb42941403cfb942941403cfdb32941403cfd93294140007bb4194140007b9419414001cff76541400ecfd7654140054fc76541400067f655414001e7c6554140005bf7454140055bc74541400073d54541400ef785054140055f8765414001ef87654140054f876541400edfb75541400077b75541400077b655414001efa655414001ef865541400ef786554140007bb7454140055fa7454140055f87454140007b874541400ef7b54541400efba54541400077954541400efb954541400073954541400ef7b5354140007795354140007bb4354140007b943541403c5fb72541403c5f972541400ef7b52541403bf7952541403bfbb42541403bfb942541403bfdb32541403bfd932541400ef7b5154140007795154140007bb4154140007b941541400067f65901400fe7c6590140055fa7090140056fb609014002dbf7590140005bd75901400073f65901400073c6590140005bd739014002dbf72901403b5bd72901403af3f52901403af3d52901403af9f32901403af9d3290140005bd719014002dbe709014002ebf6090140057bb609014002fba5090140007b9509014002fba20901403afb9209014002cff755944002e7f7559440054ff7459440054fe7459440054fd7459440054fc74594400567e54594400567c5459440004ff7359440014fe7359440014fc73594400ce7f53594400067e53594400ce7c5359440004ff725944000cfe7259440004fd725944000cfc72594400ce7f52594400067e52594400067d52594400ce7c5259440006df3259440006dd3259440004ff7159440024fc71594400ce7f51594400ce7c515944002cfe705944002cfc705944002e7
  | 17 => 0xe5bd73d0d40016be63d0d40016bc63d0d40055bf72d0d40425bd72d0d4041f3f52d0d4041f3d52d0d400e79f32d0d4041f9d32d0d40057b671d0d40005bd71d0d40057b571d0d40005b571d0d4002dbe70d0d40056bf60d0d40057bb60d0d4041fba20d0d4041fb920d0d40014fc7650d400067f6550d401e67c6550d40006df6350d40016dc6350d400579c4350d40005fb7050d40005f87050d400e5bc7650d40016bc7650d40014bc7650d40005bf7550d40005bd7550d400073f6550d400073c6550d40055bf7350d400579f7350d400079f6350d40016be6350d40016bc6350d400e79c6350d400e79e5350d400079d5350d40415bf7250d40415bd7250d4040f3f5250d4040f3d5250d400e79f3250d4040f9d3250d40005bf7150d400e79c3150d40007bb7050d4002dbc7050d40007b87050d40056bf6050d40057bb6050d400e79f3050d4040fba2050d4040fb92050d400067f65d85400067c65d854001cfe75d8540004fd75d854001cfc75d8540014fe73d8540004fd73d8540014fc73d8540006bf43d8540006bd43d8540004ff72d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d8540006bf42d8540006bd42d8540006df32d8540006dd32d8540006fa20d8540006f920d85400ed7e75985400057d75985400067f65985400067c6598540006f761985400057f75585400ed7c75585400067f65585400067c6558540005df73585400e5dc7358540005ef72585400ddec72585400067f65185400067c6518540026f66118540006f56118540004fe7694540004fd7694540024fc76945400067f659454001e7c6594540055be7494540005bd7494540026f66194540004ff7654540004fe7654540004fc76545400067f655454001e7c65545400073e5454540005be76d0540056be76d0540055bf75d0540005bd75d05400073f65d05401b6be65d05401b6bc65d05400073c65d05401b63c65d05400579e73d0540005bd73d05400579d73d05400059d73d0540006bf63d0540055bf72d0540405bd72d05403febf62d05403febd62d05403ff3f52d05403ff3d52d05403ff9f32d05403ff9d32d0540026be61d0540026bc61d054002dbe70d0540056bf60d0540057bb60d05403ffba20d05403ffb920d05400ed7e75905400057d75905400067f659054019e7c65905403f5bd7490540006f76190540026f46190540005fa7090540005f97090540024fc76505400067f65505401867c6550540006f76150540026f46150540057b44150540005fb7050540005f87050540024bc7650540005bf7550540005bd75505400073f6550540186be6550540186bc65505400073c65505401863c6550540005bf7350540006bf63505403f5bf72505403f5bd72505403e6bf62505403e6bd62505403e73f525
  | 18 => 0xc32d95400067f71d95400067e71d95400067d71d95400067c71d95403de7f41d95403de7c41d95400067f31d95400067c31d95400067f21d95400067e21d95400067d21d95400067c21d95403de7f70d95400ee7e70d95400067d70d95403de7f40d95403de7c40d95400067f30d95400067c30d95400067f20d95400067e20d95400067d20d95400067c20d95400ee7c65595400ecff75595400067f75595400fcff7459540006bf7459540004ff7359540014fe7359540014fc7359540004ff725954000cfe7259540004fd725954000cfc72595400ee7f52595400067d5259540006df3259540006dd3259540004ff7159540024fc7159540114ff7059540006fb70595400057e76195400ee7e76195400047e76195400ef3d74195400ef5e73195400ef5d73195400067e63195400067c63195400ed7f72195400ef6e72195400057d72195400ef6d72195400056d72195400067f62195400067e62195400067d62195400067c62195400073f42195400073d42195400075f32195400075d32195400ef7671195400ef7571195400ef79701954044e7f601954044f7b401954044f7840195400077a2019540007792019540005be7695140056be76951400edbd75951400073f659514001ebe659514001ebc65951400ef3c659514001e3c6595140005bd73951400ef3f5395140055bf7295140445bd72951400ef3f529514043f3d529514043f9f329514043f9d3295140005bd71951400ef3f5195140057bb709514002dbe7095140057b87095140056bf6095140057bb60951400ef3c509514043fba209514043fb9209514001cfc76551400067f655514001e7c65551400573c5455140005fb7055140005f87055140057b840551400edbc765514001ebc765514001cbc7655140055bf75551400573f75551400073f655514001ebe655514001ebc65551400ef3c6555140005bf7355140435bf7255140435bd72551400ef3f525514042f3d525514042f9f325514042f9d3255140005bf7155140007bb705514002dbc7055140007b87055140056bf6055140057bb60551400ef3f505514042fba205514042fb92055140014fe76d8d400067f65d8d400067c65d8d400e6de63d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40014fc74d8d400e6de43d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400067f52d8d400067d52d8d400e6df32d8d40006dd32d8d40024fe71d8d40004fd71d8d400e6dc31d8d40054fd70d8d400e6df30d8d400057f7558d400ed7c7558d400067f6558d400067c6558d400e6dc6358d40004ff7654d40004fe7654d40004fc7654d400067f6554d4001e7c6554d400073e5454d40016de6354d40005be76d0d40056be76d0d40055bf75d0d40005bd75d0d400073f65d0d400073c65d0d40
  | 19 => 0x464002cfe7694640004fd7694640055be7494640005bd7494640026f66194640006f56194640004ff7654640004fd765464002cfc765464001e7e65546400067d6554640026f66154640006f561546400fd7e75906400057d7590640026f66190640006f5619064002dfa7090640005f97090640024ff7650640026f66150640006f56150640005fb705064002df87050640024ff768c64002cfe768c640004fd768c640016dc638c640026f6618c640006f5618c640004ff764c640004fd764c64002cfc764c640016de634c640006dd634c640026f6614c640006f5614c64002df9769424002ef97694240054f9769424001efa659424002f7a659424002f79659424002ef86594240055fa749424002fba749424002fb9749424002df874942403df7a54942403df78549424002dfb7294240475f972942400ff7b529424046f79529424046fdb329424046fd932942400ccff765424002e7f655424002e7c655424002f785054240005fb76542400cefb765424002f7b755424002f7b655424001efa655424001ef8655424002f786554240055fa7454240055f874542400ff7b54542400077954542400ff7b5354240007795354240465fb7254240465f972542400ff7b525424045f79525424045fdb325424045fd932542400ff7b515424000779515424002dbd76d0240056bd76d024002ebf65d0240006bd65d0240006bd63d024002ebf62d0240456bd62d02404573f52d02404573d52d02404579f32d02404579d32d0240006bd61d024002fba60d024002fba50d0240007b950d024001cfe76d95400ee7e65d9540054fe74d95400ecfd74d9540054fc74d95400ee7f54d9540014fe73d9540004fd73d9540014fc73d95400ee7f53d95400067e53d95400ee7c53d9540004ff72d954000cfe72d9540004fd72d954000cfc72d95400ee7f52d95400067e52d95400067d52d95400ee7c52d9540006df32d9540006dd32d9540024fe71d9540004fd71d95400ee7f51d95400ee7c51d9540054fd70d95400ee7f50d95400ed7e76d954001c7e76d95400073f74d95400067e63d95400067c63d95400057f72d95400057d72d95400067f62d95400067e62d95400067d62d95400067c62d95400073f42d95400073d42d95400075f32d95400075d32d95403df7b70d95403df7b40d95403df7840d95400077a20d95400077920d95400067f74d95403de7e74d95400067d74d95403de7c74d95400067f73d95400067e73d95400067d73d95400067c73d95403de7f43d95400067e43d95403de7c43d95400067f72d95400047f72d95400067e72d95400067d72d95400047d72d95400067c72d95403de7f42d95400067e42d95400067d42d95403de7c42d95400067f32d95400065f32d95400067e32d95400067d32d95400065d32d95400067
  | 20 => 0x4967f655474001e7c6554740055be74547404973e5454740026f66154740006f56154740055bf7650740006bf7650740005bf7550740005bd7550740186be6550740056bc6550740005bf7350740006bd635074048dbf725074048dbd7250740056bf625074047ebd625074047f3f525074047f3d525074047f9f325074047f9d3250740057b77150740057b76150740026be6150740026bc6150740057b46150740007b65150740007b55150740487b73150740487b4315074047fb6215074047fb5215074002dbc7050740024ff768c740054fe768c740004fd768c740055be748c740005bd748c740016de638c740006dd638c7400079d438c740004ff764c740004fd764c740054fc764c740055be744c740005bd744c7400ecfd76943403de7f659434001e7c659434002dbc74943403df3e549434001cff7654340054fc765434001e7e65543400067d6554340005bf7454340055bc74543400073d54543400fcfd75d964002ebd74d96403de7e54d96403de7c54d9640014fe73d9640004fd73d964002cfc73d964002cff72d964000cfe72d9640004fd72d964002cfc72d96400fe7f52d96400067d52d9640006df32d9640006dd32d9640024fe71d9640004fd71d964002efa70d964002e7f50d964001cff765964002e7c655964002e7f75596400fe7f5459640004ff7359640014fe7359640014fc73596400fe7f5359640004ff725964000cfe7259640004fd725964000cfc72596400fe7f52596400067d5259640006df3259640006dd3259640004ff7159640024fc71596400fe7f515964002cfc705964002e7e505964002e7c505964001cff765524002cfc765524001e7e65552400067d6555240005fb705524002df87055240057bb4055240014ff7658e4002edc6358e40004ff7558e4001cfe7558e4001cfc7558e400f6de5358e400f6de4358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e400067f5258e400067d5258e400f6df3258e40006dd3258e40004ff7158e40024fc7158e400f6df3158e4002cfc7058e4002ede3058e4002edc3058e40004ff7654e40004fd7654e4002cfc7654e4001e7e6554e400067d6554e40016de6354e40006dd6354e40014ff7650e40016de6350e40006dd6350e40005fb7050e4002df87050e4002ef7619864002ef46198640005df73586400f5dc735864002ef46158640004ff755864001cfe755864001cfc7558640004ff7358640006df7358640004df7358640014fe7358640014fc7358640006dc7358640014dc7358640004ff725864000cfe7258640004fd725864000cfc72586400067f52586400067d5258640006df3258640006dd3258640006f62158640006f5215864002cfc7058640006fa2058640006f9205864002ef6105864002ef41058640024ff769
  | 21 => 0xd7690550024fc769055001d7e75905500057d7590550026f66190550007755190550004ff7650550004fe7650550004fc765055001d7e75505500057d7550550006bf6450550056bc64505501873f5450550007755150550004fe7610550004fd7610550024fc761055001d7e75105500057d7510550005fa7010550005f97010550004fe768c550004fd768c550024fc768c55001d7e758c5500057d758c550006df638c550016dc638c5500075d538c550004ff764c550004fe764c550004fc764c55001d7e754c5500057d754c5500057d74941503de7c64941500057d739415002d7f72941504cd7d72941504c67f62941504c67d62941504c75f32941504c75d32941500057d719415002d7e709415002f7a709415002e7f609415001f7b60941500567f7559740054fc74597400567e54597400567c5459740004ff7359740014fe7359740014fc7359740004ff725974000cfe7259740004fd725974000cfc72597401167f52597400067d5259740006df3259740006dd3259740004ff7159740024fc71597401167f5059740056fa4059740056f94059740055bf76553400cebf76553400573f75553400573f655534001ebe6555340056bc65553400573c6555340005bf73553404bdbf72553404bdbd72553401173f52553404b73d52553404b79f32553404b79d3255340005bf715534002dbc70553401173f5055340004ff7558f4001cfe7558f4001cfc7558f40056df7358f4010ede5358f40056df4358f40056dc4358f40004ff7258f4000cfe7258f40004fd7258f4000cfc7258f400067f5258f400067d5258f4010edf3258f40006dd3258f40004ff7158f40024fc7158f40056bf4158f4010edc3158f4010edf3058f40004ff7654f40004fd7654f40054fc7654f404ae7f6554f4001e7c6554f40055be7454f404af3e5454f40016de6354f40006dd6354f40055bf7650f400c6bf7650f40005bf7550f40005bd7550f400579f7350f400579f6350f40016be6350f40016bc6350f400579c6350f4010f9e5350f400079d5350f404a5bf7250f404a5bd7250f4049f3f5250f4049f3d5250f4010f9f3250f4049f9d3250f40005bf7150f4010f9c3150f4002dbc7050f4010f9f3050f40004ff755874001cfe755874001cfc7558740004ff7358740014fe7358740014fc7358740056bf4358740006bd4358740004ff725874000cfe7258740004fd725874000cfc72587400067f52587400067d5258740056bf4258740006bd4258740006df3258740006dd3258740056f77158740056f74158740056f44158740006f73158740006f43158740006f62158740006f52158740024ff7694740054fe7694740004fd7694740055be7494740005bd7494740026f66194740006f56194740004ff7654740004fd7654740054fc7654740
  | 22 => 0x9150014fc73d9150004ff72d915000cfe72d9150004fd72d915000cfc72d91500fe7f52d91500067d52d9150006be42d9150006bc42d9150006df32d9150006dd32d9150024fe71d9150004fd71d9150006bf64991500edf97099150115fb7059150056be6419150006bd6419150125de7319150005dd731915011dee7219150005ed7219150005f67119150005f571191500547c765515001d7f745515001f3f74551500073f64551500567e64551500567c64551500073c64551500057f73551505057f72551505057d72551504fe7f62551504fe7d62551504ff5f32551504ff5d32551500057f71551500077b705515002d7c705515000778705515001e7f605515001f7b6055150014fe76d8d50126de63d8d50014fc75d8d50054fe74d8d50004fd74d8d50126de53d8d500b6dd53d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500b67f52d8d500067d52d8d50126df32d8d50006dd32d8d50024fe71d8d50004fd71d8d500b67f51d8d50126dc31d8d5001cfd70d8d50126df30d8d50126dc6358d504f5fb7058d501257c7654d500167c7654d500147c7654d500057f7454d504ae7c6454d5001d7f7354d5001f5f7354d500075f6354d500167e6354d500167c6354d501275c6354d501275e4354d504ed7f7254d504ed7d7254d504e67f6254d504e67d6254d501275f3254d504e75d3254d500057f7154d501275c3154d500077b7054d5002d7c7054d50007787054d5001e7f6054d5001f7b6054d501275f3054d50004fe76d0d50004fd76d0d50054fc76d0d5001d7e75d0d500057d75d0d50005f671d0d50005f571d0d50005fa70d0d50005f970d0d50004ff7650d50004fe7650d50004fc7650d5001d7e7550d500057d7550d50016de6350d500075d5350d50054fe74d8550004fd74d8550014fe73d8550004fd73d8550014fc73d855007e7f53d85500067d53d8550004ff72d855000cfe72d8550004fd72d855000cfc72d855007e7f52d85500067d52d8550006df32d8550006dd32d855007ef651d855007ef551d8550005be7498550005bd7498550006f7619855006df97098550005df7358550125dc7358550095fb7058550026f66118550006f561185500247c76545500057f74545504967c64545500057f73545500067f63545504dd7f72545504dd7d72545504d67f62545504d67d62545504d75f32545504d75d325455001d7f715455001f7771545500077761545500267e61545500267c61545500077461545500077b705455002d7c705455000778705455001e7f605455001f7b6054550004fe76d0550004fd76d0550054fc76d055001d7e75d05500057d75d0550006bf64d0550056bc64d05501b73f54d0550125de73d0550005dd73d0550005fa70d0550005f970d0550004fe7690550004f
  | 23 => 0x2cedc311813102edf301813102efa301813103ef9301813102ebf649925002ebc649925002ebc64592500eebe54592500eebd54592503de7c5459250004ff7359250014fe7359250014fc7359250004ff725925000cfe7259250004fd725925000cfc72592500ee7f52592500067d5259250006bf4259250006bd4259250006df3259250006dd3259250004ff7159250024fc715925002cfc70592500ee7f505925002ebe405925002ebc405925001d7e749525001f3e74952503df3e64952503de7d64952500073d64952500063d64952503dd7f72952505157d729525050e7f629525050e7d629525050f5f329525050f5d32952503df7a70952500057d70952503df79709525000579709525001e7e609525001f7a6095250014ff7658e5002edc6358e50004ff7458e50054fc7458e500067e5458e500a67c5458e50136de5358e500a6dd5358e50136de4358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e500a67f5258e500067d5258e50136df3258e50006dd3258e50004ff7158e50024fc7158e50136df3158e5002cfe7058e5002cfc7058e500a67f5058e5002ede3058e5002edc3058e50054ff76d0e5002cfe76d0e50004fd76d0e50056be64d0e50006bd64d0e50005f671d0e50005f571d0e5002dfa70d0e50005f970d0e50004ff7650e50004fd7650e5002cfc7650e500057f7550e5001d7c7550e50056be6450e50006bd6450e50016de6350e50006dd6350e5002ef7619865002ef46198650005df7358650135dc735865002ef46158650004ff7458650054fc74586500067e545865006e7c5458650004ff7358650006df7358650004df7358650014fe7358650014fc7358650006dc7358650014dc7358650004ff725865000cfe7258650004fd725865000cfc725865006e7f52586500067d5258650006df3258650006dd325865006ef6515865006ef55158650006f62158650006f5215865002cfc705865006e7f505865002ef6105865002ef41058650054ff76d065002cfe76d0650004fd76d0650056be64d0650006bd64d06503df3c54d0650135de73d0650005dd73d065002dfa70d0650005f970d0650024ff769065002cfe7690650004fd769065001d7e75906500057d7590650026f66190650006f56190650004ff7650650004fd765065002cfc76506500057f755065001d7c7550650056be6450650006bd64506501873c5450650026f66150650006f56150650024ff761065002cfe7610650004fd761065002dfa7010650005f97010650024ff768c65002cfe768c650004fd768c650016dc638c650026f6618c650006f5618c650004ff764c650004fd764c65002cfc764c650016de634c650006dd634c650026f6614c650006f5614c6500febe54d91500febd54d9150014fe73d9150004fd73d
  | 24 => 0xe70d9531004fd70d95311d6df30d95311467c6559531525f771595311d4ff75595310067f7559531004ff7459531054fc74595311467c54595311c4ff7359531006df7359531004ff725953100cfe7259531004fd725953100cfc72595311467f52595310067d52595311c6df3259531006dd3259531524ff7159531006f7715953133ede315953133edc3159531004ff705953102cfc70595311467f50595311c6df3059531054fe76d91311457e75d91310057d75d913101cfe75d91310067e75d913101c7e75d9131004fd75d91310067d75d91310047d75d913101cfc75d9131024ff73d9131024fd73d9131196bf43d9131196bd43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d91310067f52d91310067d52d9131196df32d9131006dd32d9131196f731d913151ede31d913151edc31d9131196f431d913102cfe70d9131004fd70d9131196df30d9131006bf649913117df571991311adf77159131004ff755913101cfe755913101cfc7559131006bf745913117cff7359131006df7359131004ff725913100cfe7259131004fd725913100cfc72591310067f52591310067d525913117edf3259131006dd32591311acff7159131006f7715913117ef73159131336de3159131336dc315913117ef43159131004ff705913102cfc705913117edf3059131194fe7619131056be6419131006bd6419131054ff7695131004fe7695131004fd7695131054fc769513101e7e65951310067d6595131004ff7655131004fe7655131004fd7655131004fc765513101cff7654531014fe76545311c4fd7654531014fc76545310067f655453101e7c6554531005df7354531015dc7354531014fe76d0531014fc76d0531006bf64d0531056bc64d0531015de73d0531005dd73d0531054ff7650531014fe765053117cfd7650531014fc7650531006bf6450531056bc6450531005df7350531015dc735053117ef76150531027d4315053101cfe75d8131004fd75d813101cfc75d8131054fe74d8131004fd74d8131024fd73d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d813108edf32d8131006dd32d813108efa30d8131006fb60981311457e75181310057d7518131005be7418131005bd741813113dee7218131005ed7218131006f9601813101cfe751813102e7e751813101c7e7518131004fd751813102e7d75181310047d751813102cfc7518131054fe741813102ebe7418131054be7418131004fd741813102ebd7418131004bd7418131024fd731813102cff721813100cfe721813102eee721813100cee7218131004fd721813102eed7218131004ed721813102cfc72181310067f52181310067d521813103edf3218131006dd321813102ef571181312cede3118131
  | 25 => 0x9631026f71059631004ff755923101cfe755923101cfc7559231026bf7459231006bf5459231006bc545923117ede535923117ebf435923117ebd4359231004ff725923100cfe7259231004fd725923100cfc72592310067f52592310067d5259231006bf4259231006bd425923117edf3259231006dd3259231024fe7159231024fc7159231026be4159231026bc415923117ef73159231026f43159231004ff705923102cfc7059231026f71059231054ff7695231024fe7695231004fd7695231024fc769523101e7e65952310067d6595231015de7395231005dd7395231004ff7655231024fe7655231004fd7655231024fc7655231015de735523133ddf7654e3101edf7654e3101cdf7654e31015df7554e310175f7554e3101ede6554e3133f5e6554e3133f5d6554e3101edc6554e31005df7454e3133edf6454e31006dd6454e310075e5454e311575c5454e3154ddf7254e3154ddd7254e3133edf6254e31546dd6254e311575f5254e315475d5254e3133ddf7154e31007d77154e3133fd47154e31016de6154e31017d66154e3133f5f5154e3133f5d5154e31005dc7054e311575f5054e31335df7650e31056df7650e31054df7650e31005df7550e31005dd7550e31336df6550e31006dd6550e31015df7450e310179f7450e31056de6450e313379e6450e313379d6450e31056dc6450e3153ddf7250e3153ddd7250e31336df6250e31536dd6250e315375f5250e315375d5250e31335df7150e31007d77150e31337d47150e31016de6150e31017d66150e313379f4150e313379d4150e31005dc7050e3101cfe7598231004fd759823102cfc7598231054fe7498231004fd749823102cff729823100cfe7298231004fd729823102cfc72982310067f52982310067d5298231076df3298231006dd3298231024fe719823102ef67198231024f6719823102cfc719823102efa709823102efa3098231076f9309823102efa2098231006f9209823102ef71098231026fb109823102ef81098231004ff755823101cfe755823101cfc7558231004ff7458231054fc7458231066de5358231006dd5358231066de4358231006dd4358231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231066df3258231006dd3258231024fc7158231026df3158231026dd3158231026fb7058231066fa3058231066dc3058231006fa2058231006f92058231026fb1058231026f8105823101cfe76d95311467e65d9531054fe74d9531004fd74d9531024ff73d9531024fd73d95311d67f53d95311d67d53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d95311467f52d95310067d52d95311d6df32d9531006dd32d9531014fd71d95311467f51d953152ede31d953152edc31d953102cf
  | 26 => 0x6f651d8141006f551d8141006f621d8141006f521d8141006fb60981410057f75581411857c7558141005df735814117ddc7358141005ef7258141175ec72581411857e75181410057d751814117dde7318141005dd7318141175ee7218141005ed7218141006f9601814101cfe751814102e7e751814101c7e7518141004fd751814102e7d75181410047d751814102cfc7518141014fe731814102ede7318141014de7318141004fd731814102edd7318141004dd731814102cfc731814102cff721814100cfe721814102eee721814100cee7218141004fd721814102eed7218141004ed721814102cfc72181410067f52181410067d5218141006df3218141006dd3218141024ff75594410267f7559441054fe7459441054fc74594410567e54594410567c5459441004ff7359441014fe7359441014fc735944116e7f5359441004ff725944100cfe7259441004fd725944100cfc725944116e7f52594410067d5259441006df3259441006dd3259441024fe7159441024fc71594410267e51594410267c5159441026f64159441056f54159441004ff705944102cfc705944116e7f5059441004ff7558c4101cfe7558c4101cfc7558c41024ff7358c41026df7358c41166de5358c41056df4358c41056dc4358c41004ff7258c4100cfe7258c41004fd7258c4100cfc7258c410067f5258c410067d5258c41166df3258c41006dd3258c41024fc7158c41026bf4158c41026bd4158c41026de3158c41026dc3158c41004ff7058c4102cfc7058c41166df3058c41004ff7654c41004fd7654c41024fc7654c4101e7e6554c410067d6554c41016de6354c41006dd6354c4101cfe7598041004fd759804102cfc7598041014fe7398041004fd739804102cfc739804102cff729804100cfe7298041004fd729804102cfc72980410067f52980410067d5298041006df3298041006dd329804102cfe709804102efa7098041056fb409804102ef8409804102efa2098041006f92098041026fb109804102ef81098041004ff755804101cfe755804101cfc7558041004ff7358041014fe7358041014fc7358041004ff725804100cfe7258041004fd725804100cfc72580410067f52580410067d5258041006df3258041006dd3258041026bf4158041026f64158041026bd4158041056f54158041026fb7058041056fb4058041056f84058041006fa2058041006f92058041026fb1058041026f810580410267f7559631004ff7459631054fc74596311567c54596311c67f53596311c67d53596311c6de4359631004ff725963100cfe7259631004fd725963100cfc72596311567f52596310067d52596311c6df3259631006dd3259631024fe7159631024fc71596310267e51596310267c5159631004ff705963102cfc70596311567f505
  | 27 => 0xe70d8d41004fd70d8d4117edc30d8d4117edc6358d4117fd43158d41004ff7654d41004fe7654d41004fc7654d410067f6554d4101e7c6554d41005bf7454d41055bc7454d411873c5454d41006df6354d41016dc6354d41005f77154d41025f47154d4117fd43154d41005be76d0d41056be76d0d41185be75d0d41055bc75d0d4117dbd73d0d41016be63d0d41016bc63d0d41055bf72d0d4158dbd72d0d415873f52d0d415873d52d0d4117f9f32d0d415879d32d0d41025be71d0d41057b671d0d41025b671d0d41057b571d0d41025bc71d0d41056bf61d0d41057b761d0d4117fb731d0d4117fb431d0d41587b621d0d41587b521d0d41005bd70d0d41024fc7650d41006df6350d41016dc6350d41005f77150d41025f47150d4117fd43150d41025bc7650d41016bc7650d41024bc7650d41185be7550d41185bc7550d41055bf7350d410579f7350d410079f6350d41016be6350d41016bc6350d4117f9c6350d4117f9e5350d410079d5350d4157dbf7250d4157dbd7250d415773f5250d415773d5250d4117f9f3250d415779d3250d41007b77150d41025be7150d41025bc7150d41007b47150d41056bf6150d41057b76150d4117fb73150d413379c3150d4117fb43150d4117f943150d41577b62150d41577b52150d41005bf7050d4117f9f3050d41005f67694541026f67694541185f5759454101ef6659454101ef46594541055f67494541027b67494541055b67494541027b57494541025f47494541026f76494541027b76494541187b75494541187b4549454117df67394541025f47394541007b74394541007b54394541025f7729454156df57294541187775294541567755294541567b74294541567b54294541567d73294541567d53294541005f5709454101cff7654541184fd7654541054fc76545410067f655454101e7c6554541005bf7454541055bc74545411873c5454541055f4765454101ef47654541054f47654541025f7755454102777755454100777655454101ef6655454101ef46554541187746554541007b77454541055f67454541055f47454541007b47454541026f76454541027b76454541187b75454541497765454541497745454541187b4545454118734545454117df6735454117df47354541187775354541007755354541007b74354541007b5435454155df7725454155df57254541187775254541557755254541557b74254541557b54254541557d73254541557d53254541005f7705454118777505454101cfe75d8141004fd75d814101cfc75d8141014fe73d8141004fd73d8141014fc73d8141006bf43d8141006bd43d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d8141006bf42d8141006bd42d8141006df32d8141006dd32d8141
  | 28 => 0x4e41016dc6354e41005f77154e41025f47154e4133fd43154e41014ff7650e411e67e6550e410067d6550e41016de6350e41006dd6350e41005f77150e41025f47150e41337d43150e41025f7765464116ef7765464102777755464101ef6655464102776655464101e766554641027756554641026f46554641055f67454641055f47454641497765454641497745454641195f67354641195f4735464119f77535464100775535464159df7725464159df5725464119f775254641597755254641597d73254641597d53254641005f7705464119f77505464101cfe7598241004fd759824102cfc7598241014fe7398241004fd739824102cfc739824102cff729824100cfe7298241004fd729824102cfc72982410067f52982410067d5298241006df3298241006dd3298241024fe7198241024f6719824102efa709824102efa2098241006f9209824102ef71098241026fb109824102ef81098241004ff755824101cfe755824101cfc7558241004ff7358241014fe7358241014fc7358241004ff725824100cfe7258241004fd725824100cfc72582410067f52582410067d5258241006df3258241006dd3258241024fc7158241026f65158241006f55158241026bf4158241026bd4158241026f62158241006f52158241026fb7058241006fa2058241006f92058241026fb1058241026f8105824101cfe76d95411867e65d9541055be74d9541025bd74d95411873f54d9541024fd74d9541186bd74d9541024bd74d95411867f54d9541186bf54d9541186bc54d9541014fe73d9541004fd73d9541014fc73d95411867f53d9541004ff72d954100cfe72d9541004fd72d954100cfc72d95411867f52d95410067d52d9541006df32d9541006dd32d9541054fd71d95411867f51d954102cfe70d9541004fd70d95411867c50d95411867c65595411873c5459541184ff75595410067f755954119cff7459541006bf7459541186bf54595414967e54595414967c5459541186bc5459541004ff7359541014fe7359541014fc7359541004ff725954100cfe7259541004fd725954100cfc72595411867f52595410067d5259541006df3259541006dd32595411b4ff7159541006f77159541004ff705954102cfc70595411867f5059541024fc76551410067f655514101e7c6555141185bf74551410573c5455141005f77155141025f47155141014fe76d8d4117ede63d8d41025f671d8d41055f571d8d4117fd731d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41024fd74d8d4117ede53d8d4117ede43d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d410067f52d8d410067d52d8d4117edf32d8d41006dd32d8d41054fd71d8d4117ef571d8d41054f571d8d4117edf31d8d4117ef731d8d4117ef431d8d4102cf
  | 29 => 0x4fd759834102cfc7598341024fe7498341024be7498341014fe7398341004fd739834102cfc739834102cff729834100cfe7298341004fd729834102cfc72983410067f52983410067d5298341006df3298341006dd329834102efa709834102ebf4098341056fb409834102ef8409834102efa2098341006f92098341004ff755834101cfe755834101cfc7558341024fc7458341004ff7358341014fe7358341014fc7358341056bf4358341006bd4358341004ff725834100cfe7258341004fd725834100cfc72583410067f52583410067d5258341056bf4258341006bd4258341006df3258341006dd3258341056f64158341056f54158341056fb7058341056fb4058341056f84058341006fa2058341006f920583410267f755964119e7f5459641004ff7359641014fe7359641014fc735964119e7f53596410067e535964119e7c5359641004ff725964100cfe7259641004fd725964100cfc725964119e7f52596410067e52596410067d525964119e7c5259641006df3259641006dd3259641024fc71596410267e51596410267c5159641004ff705964102cfc705964119e7f505964119e7c5059641026f710596410067f74596414967e74596410067d74596414967c74596410067f73596410067e73596410067d73596410067c73596414967f43596410067e43596414967c43596410067f72596410047f72596410067e72596410067d72596410047d72596410067c72596414967f42596410067e42596410067d42596414967c42596410067f32596410065f32596410067e32596410067d32596410065d32596410067c32596410267f71596410267e71596410267d71596410267c71596410267f41596410267e41596410267d41596410267c41596410267f31596410267e31596410267d31596410267c31596410267f21596410267e21596410267d21596410267c21596410067f70596410067e70596410067d70596410067c70596414967f40596414967c40596410067f30596410067c30596410067f20596410067e20596410067d20596410067c20596410267f10596410267710596410267e10596410267d10596410267c105964101cff7655241024fc765524101e7e65552410067d6555241005f77155241025f47155241057b74155241004ff7558e4101cfe7558e4101cfc7558e41026df7358e41196de4358e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e410067f5258e410067d5258e41196df3258e41006dd3258e41024fc7158e41026f47158e41024f47158e41026bf4158e41026bd4158e41196f73158e41026de3158e41026dc3158e41026f43158e41004ff7058e4102cfc7058e41196df3058e41026f71058e41004ff7654e41004fd7654e41024fc7654e4101e7e6554e410067d655
  | 30 => 0xc731815102cff721815100cfe721815102eee721815100cee7218151004fd721815102eed7218151004ed721815102cfc72181510467f52181510067d5218151006df3218151006dd321815102ef5711815102e7f501815102efa5018151046f950181510567f7559741024fc7459741056bc7459741024bc74597411b6bf54597410567e54597410567c5459741056bc5459741004ff7359741014fe7359741014fc7359741004ff725974100cfe7259741004fd725974100cfc72597411b67f52597410067d5259741006df3259741006dd32597411b67f5159741056f64159741056f54159741004ff705974102cfc70597411b67f5059741056bf4059741004ff7558f4101cfe7558f4101cfc7558f41024fc7458f41056df7358f41006df5358f411aede5358f411aedc5358f41056df4358f41056dc4358f41004ff7258f4100cfe7258f41004fd7258f4100cfc7258f410067f5258f410067d5258f411aedf3258f41006de3258f41006dd3258f411aedc3258f411aedf3158f41004ff7058f4102cfc7058f41056bf4058f411aedf3058f411aedc3058f41006df7558f41006de7558f41006dd7558f41006dc7558f41056df7458f41056de7458f41056dc7458f41056df5458f41056de5458f41056dd5458f41056dc5458f41006df7258f41004df7258f41006de7258f41006dd7258f41004dd7258f41006dc7258f41006df5258f410065f5258f41006de5258f41006dd5258f410065d5258f41006dc5258f41056df4258f41056de4258f41056dd4258f41056dc4258f41006df7158f41006dd7158f41336dc7158f41006df5158f41336de5158f41336dc5158f41056df4158f41056de4158f41056dd4158f41056dc4158f41006df2158f41336de2158f41006dd2158f41336dc2158f41006df7058f41006de7058f41006dd7058f41006dc7058f41006df5058f41006dc5058f41056df4058f410569f4058f41056de4058f41056dd4058f41056dc4058f41006df2058f41006de2058f41006dd2058f41006dc2058f41336df1058f41336dc1058f41004ff7654f41004fd7654f41054fc7654f414ae7f6554f4101e7c6554f41005bf7454f41055bc7454f414af3c5454f41016de6354f41006dd6354f41055bf7650f41166bf7650f411b5be7550f411b5bc7550f410579f7350f41016be6350f410579e6350f410169e6350f410579d6350f41016bc6350f411af9e5350f410079d5350f415adbf7250f415adbd7250f415a73f5250f415a73d5250f411af9f3250f415a79d3250f41025be7150f41025bc7150f413379c3150f41005bf7050f411af9f3050f4101cff7654741054fc765474101e7e65547410067d6554741005bf7454741055bc74547414973c54547411c6de6354741006dd6354741027b6415474101cfe7598341
  | 31 => 0x82510067d5258251006df3258251006dd3258251024fc71582510267f51582510267d5158251026f64158251026fb705825106efa5058251006fa2058251006f92058251026fb1058251026f81058251024fd75d915119ebe54d915119ebd54d91514967c54d9151014fe73d9151004fd73d9151014fc73d9151004ff72d915100cfe72d9151004fd72d915100cfc72d915119e7f52d91510067d52d9151006df32d9151006dd32d915102cfe70d9151004fd70d915119e7f50d9151006bf64991514973c54991511c5de7399151005dd7399151185f571991511873c54591511b5f77159151056be6419151006bd64191510247e769515101d7e749515101f3e74951514967f64951510073f64951514973c64951510057d73951514957f72951515d57d72951515ce7f62951515ce7d62951515cf5f32951515cf5d32951510257e71951514977671951514977571951510257c719515101e7f619515101f7761951510057d7095151014fe76d8d511c6de63d8d51024fd75d8d51054fe74d8d51004fd74d8d510067e54d8d511567c54d8d511c6de53d8d51156dd53d8d511c6de43d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d511567f52d8d510067d52d8d511c6df32d8d51006dd32d8d5101cfd71d8d511c6df31d8d5102cfe70d8d51004fd70d8d511567f50d8d511c6dc30d8d511c6dc6358d515c5f77158d510257c7654d510167c7654d510247c7654d514957c7454d514ae7c6454d5101d7f7354d5101f5f7354d510075f6354d510167e6354d510167c6354d511c75c6354d511c75e4354d515bd7f7254d515bd7d7254d515b67f6254d515b67d6254d511c75f3254d515b75d3254d51007777154d510257e7154d510257c7154d51007747154d5101e7f6154d5101f776154d5133f5c3154d510057f7054d511c75f3054d51004fe76d0d51004fd76d0d51054fc76d0d514957f75d0d5101d7c75d0d51025f671d0d51005f571d0d51004ff7650d51004fe7650d51004fc7650d510057f7550d5101d7c7550d51006df6350d51016dc6350d510075d5350d51024fd75d8151054fe74d8151004fd74d8151014fe73d8151004fd73d8151014fc73d81510967f53d81510067d53d8151004ff72d815100cfe72d8151004fd72d815100cfc72d81510967f52d81510067d52d8151006df32d8151006dd32d8151096fa50d8151006fb6098151005df73581511c5dc7358151005be7418151005bd74181511c5de7318151005dd73181511bdee7218151005ed7218151006f96018151024fd7518151054fe741815102ebe7418151054be7418151004fd741815102ebd7418151004bd74181510067e54181510467c5418151014fe731815102ede7318151014de7318151004fd731815102edd7318151004dd731815102cf
  | 32 => 0x1b6be50992511b6bd50992511b6bc5099251006bf3099251006bc3099251006bf2099251006be2099251006bd2099251006bc2099251026bf1099251026be1099251026bd1099251026bc1099251026bf7459251186be5459251186bd5459251004ff7359251014fe7359251014fc7359251006be4359251006bc4359251004ff725925100cfe7259251004fd725925100cfc72592511867f52592510067d5259251006bf4259251006be4259251006bd4259251006bc4259251006df3259251006dd3259251024fc7159251026be4159251026bc4159251004ff705925102cfc7059251026f71059251186be7559251186bd7559251186bc7559251006bf7359251006be7359251006bd7359251006bc7359251186bf5359251186be5359251186bd5359251186bc5359251006bf7259251006be7259251006bd7259251006bc7259251186bf52592511863f5259251186be5259251186bd52592510063d5259251186bc5259251006bf32592510069f3259251006be3259251006bd32592510069d3259251006bc3259251026bf7159251026be7159251026bc7159251026bf5159251026be5159251026bd5159251026bc5159251026bf3159251026be3159251026bd3159251026bc3159251026bf2159251026be2159251026bd2159251026bc2159251006bf7059251006be7059251006bd7059251006bc7059251186bf5059251186be5059251186bd5059251186bc5059251006bf3059251006bc3059251006bf2059251006be2059251006bd2059251006bc2059251026bf1059251026b71059251026be1059251026bd1059251026bc1059251004ff7458e51054fc7458e51026df7358e511d6de5358e51146dd5358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e511467f5258e510067d5258e511d6df3258e51006dd3258e51024fe7158e51024fc7158e510267f5158e510267d5158e51026de3158e51026dc3158e51004ff7058e5102cfc7058e511d6df3058e51026f71058e51054ff76d0e51024fe76d0e51004fd76d0e51056be64d0e51006bd64d0e51025f671d0e51005f571d0e51004ff7650e51004fd7650e51024fc7650e51056be6450e51006bd6450e51016dc6350e51054fe7498251004fd7498251014fe7398251004fd739825102cfc739825102cff729825100cfe7298251004fd729825102cfc729825107e7f52982510067d5298251006df3298251006dd3298251024fe719825102ef67198251024f6719825102cfc719825102efa709825102efa509825107ef9509825102efa2098251006f9209825102ef71098251026fb109825102ef81098251004ff7458251054fc7458251004ff7358251014fe7358251014fc7358251004ff725825100cfe7258251004fd725825100cfc725825106e7f525
  | 33 => 0xe765514320cfd7655143014fc76551430067f655514301e7c6555143005df7355143015dc73551430579c4355143055dc7654d4301edc7654d43054dc7654d43015df7554d430175f7554d430075f6554d4301ede6554d4301edc6554d431e75c6554d430079f7454d43055de7454d43055dc7454d430079c7454d43016df6454d430179f6454d434af5e5454d434af5c5454d435e5df7254d435e5dd7254d435dedf6254d435dedd6254d431e75f5254d435df5d5254d43335dc7154d4333edc6154d431e75f5154d43005df7054d431e75f5054d4301cfe75d8543004fd75d854301cfc75d8543054fd73d8543004ff72d854300cfe72d8543004fd72d854300cfc72d85430067f52d85430067d52d85431aedf32d8543006dd32d85431aef631d8543336dc31d854302cfe70d8543004fd70d85431aedf30d85431e57e75985430057d7598543006f76198543337d4319854317fd43158543026f66118543006f5611854301cfe75d8143004fd75d814301cfc75d8143054fd73d814310ede53d8143006dd53d8143004ff72d814300cfe72d8143004fd72d814300cfc72d81430067f52d81430067d52d814310edf32d8143006dd32d8143024fe71d8143004fd71d814310efa30d8143006fb60981430057f75581431e57c75581431e57e75181430057d75181431ddee7218143005ed7218143005f67118143005f57118143006f9601814301cfe751814302e7e751814301c7e7518143004fd751814302e7d75181430047d751814302cfc751814302ebd7418143054fd731814302cff721814300cfe721814302eee721814300cee7218143004fd721814302eed7218143004ed721814302cfc72181430067f52181430067d52181430c6df3218143006dd3218143024fe711814302ef67118143024f67118143004fd711814302ef57118143004f571181430c6dc311814302edf301814302efa30181430c6f93018143056bf7599251056be7599251056bc7599251056bf7399251056be73992510569e7399251056bd73992510569d7399251056bc73992511b6bf53992511b6be53992511b6bd53992511b6bc5399251056bf7299251056be7299251056bd7299251056bc72992511b6bf52992511b63f52992511b6be52992511b6bd52992510063d52992511b6bc5299251006bf32992510069f3299251006be3299251006bd32992510069d3299251006bc3299251026bf7199251026be7199251026b67199251026bd7199251026bc7199251026bf51992510263f5199251026be5199251026bd51992510263d5199251026bc5199251026bf3199251026be3199251026bd3199251026bc3199251026bf2199251026be2199251026bd2199251026bc2199251056bf7099251056be7099251056bd7099251056bc70992511b6bf5099251
  | 34 => 0x8743006f45158743056f74158743056f4415874317ef63158743006f72158743006f62158743006f52158743006f42158743004ff705874302cfc7058743056bf4058743006f77558743006f67558743006f57558743006f47558743056f77458743056f67458743056f47458743056f75458743056f65458743056f55458743056f4545874317ef6735874317ef5735874317ef4735874317ef7535874317ef6535874317ef5535874317ef45358743056f74358743056f64358743056f54358743056f44358743006f77258743006f67258743006f57258743006f47258743006f75258743006775258743006f65258743006f55258743006755258743006f45258743056f74258743056f64258743056f54258743056f4425874317ef7325874317ed7325874317ef6325874317ef53258743006d5325874317ef43258743006f77058743006f67058743006f57058743006f47058743006f75058743006f45058743056f74058743056b74058743056f64058743056f54058743056f4405874317ef7305874317ef6305874317ef5305874317ef43058743006f72058743006f62058743006f52058743006f4205874301cfe7598343004fd759834302cfc7598343014fe749834302ebe7498343014be749834302cfc749834302cff729834300cfe7298343004fd729834302cfc72983430067f52983430067d52983430f6df3298343006dd3298343024fe7198343004fd719834302efa709834302ebf4098343056fb409834302ef8409834302efa30983430f6f9309834302efa2098343006f92098343004ff755834301cfe755834301cfc7558343014fc7458343056de4358343056dd4358343004ff725834300cfe7258343004fd725834300cfc72583430067f52583430067d52583430e6df3258343006dd3258343004ff7158343024fc7158343056bf4158343056fb7058343056fb4058343056f840583430e6fa3058343006fa2058343006f9205834301cfe76d95431e67e65d9543014fd74d95431e67f54d9543054ff73d9543054fd73d954321e7f53d954321e7d53d9543004ff72d954300cfe72d9543004fd72d954300cfc72d95431e67f52d95430067d52d954321edf32d9543006dd32d9543024fe71d9543004fd71d95431e67f51d954321edc31d954302cfe70d9543004fd70d95431e67c50d954321edf30d95431e67c65595435edbf745954321cff75595430067f75595435ecff7459543006bf74595434ae7e54595434ae7c545954320cff7359543006df7359543004ff725954300cfe7259543004fd725954300cfc72595431e67f52595430067d525954320edf3259543006dd3259543004ff7159543024fc715954320edc3159543004ff705954302cfc70595431e67f505954320edf305954301cff7655143014f
  | 35 => 0x5be7498553005bd7498553006f76198553026f66118553006f56118553014fd75d8153054fe74d8153004fd74d815301cfd73d815338ede43d8153004ff72d815300cfe72d8153004fd72d815300cfc72d81534f67f52d81530067d52d815338edf32d8153006dd32d8153024fe71d8153004fd71d81534f67f51d81534f6fa50d815338efa30d8153006fb6098153005be7418153005bd74181531fdee7218153005ed7218153005f67118153005f57118153006f96018153014fd751815302e7d7518153054fe741815302ebe7418153054be7418153004fd741815302ebd7418153004bd74181530067e54181535f67c541815301cfd731815302edd731815302cff721815300cfe721815302eee721815300cee7218153004fd721815302eed7218153004ed721815302cfc72181535f67f52181530067d5218153356df3218153006dd3218153024fe711815302ef67118153024f67118153004fd711815302ef57118153004f57118153356dc311815302e7f501815302efa50181535f6f9501815302edf301815302efa3018153356f930181530567f7559743014fe7459743014fc74597430567e54597430567c545974320e7f535974320e7d5359743056de4359743056dd4359743004ff725974300cfe7259743004fd725974300cfc72597431f67f52597430067d525974320edf3259743006dd3259743004ff7159743024fc7159743004ff705974302cfc70597431f67f5059743056bf4059743026f77598743026f67598743026767598743026f57598743026757598743026f47598743026f77498743026f67498743026b67498743026f57498743026f47498743056f75498743056f65498743056f55498743056f45498743026f77398743026f67398743026f47398743196f75398743196f65398743196f55398743196f45398743056f74398743056f64398743056d64398743056f54398743056d54398743056f44398743026f77298743026f67298743026f57298743026f47298743006f75298743006775298743006f65298743006f55298743006755298743006f45298743056f74298743056f64298743056f54298743056f44298743196f73298743196d73298743196f63298743196f53298743006d53298743196f43298743026f77098743026f67098743026f57098743026f47098743006f75098743006f45098743056f74098743056f64098743056f54098743056f44098743196f73098743196f63098743196f53098743196f43098743006f72098743006f62098743006f52098743006f42098743004ff755874301cfe755874301cfc7558743014fc7458743004ff725874300cfe7258743004fd725874300cfc72587430067f52587430067d525874317edf3258743006dd3258743056f77158743006f7515
  | 36 => 0xd52d8d5420edf32d8d54006dd32d8d54024fe71d8d54004fd71d8d5402cfe70d8d54004fd70d8d541f67f50d8d5420edc6358d5420dde73d8554005dd73d8554054fd75d85541b6bf54d85546167e54d85546167c54d85541b6bc54d8554014fe73d8554006de73d8554014de73d8554004fd73d8554006dd73d8554004dd73d8554014fc73d8554004ff72d855400cfe72d8554004fd72d855400cfc72d85541b67f52d85540067d52d8554006df32d8554006dd32d85541b6f651d855402cfe70d8554004fd70d85541b67f50d8554006f76198554026f66118554006f56118554054fd75d8154014fe73d8154004fd73d8154014fc73d8154004ff72d815400cfe72d8154004fd72d815400cfc72d81541167f52d81540067d52d8154006df32d8154006dd32d8154024fe71d8154004fd71d8154116fa50d8154006fb609815420dde7318154005dd7318154205ee7218154005ed7218154005f67118154005f57118154006f96018154054fd751815402ebd741815444e7e541815444e7c5418154014fe731815402ede7318154014de7318154004fd731815402edd7318154004dd731815402cfc731815402cff721815400cfe721815402eee721815400cee7218154004fd721815402eed7218154004ed721815402cfc72181540ce7f52181540067d5218154006df3218154006dd3218154024fe711815402ef67118154024f67118154004fd711815402ef57118154004f5711815402e7f501815402efa50181540cef95018154054fe76d9153014fd75d91535ee7d75d915360ebe54d915360ebd54d91534ae7c54d915301cfd73d91535eebf43d9153004ff72d915300cfe72d9153004fd72d915300cfc72d915360e7f52d91530067d52d91535eedf32d9153006dd32d9153024fe71d9153004fd71d91535eedc31d915302cfe70d9153004fd70d915360e7f50d91535eedf30d9153006bf64991531e5dd7399153005f67199153005f571991531f5df7359153056be6419153006bd64191530157e769515321e7e76951530147e769515301d7e749515301f3e74951534ae7f64951530073f64951534af3c64951530157e739515321f5e73951534af5d73951530157c739515301e7f639515301f5f639515321f5e43951534ad7f72951536057d72951535fe7f62951535fe7d629515321f5f32951535ff5d32951530057d719515321f5c31951530057d709515321f5f3095153024fe76d8553014fd75d8553054fe74d8553004fd74d85530067e54d85535c67c54d855301cfd73d85535c6dd73d8553004ff72d855300cfe72d8553004fd72d855300cfc72d85535c67f52d85530067d52d8553526df32d8553006dd32d85535c6f651d8553526f631d855333edc31d855302cfe70d8553004fd70d85535c67f50d8553526df30d8553
  | 37 => 0x2400000380000000006000c000000000200080000004006000c0050008002000000800140080000000000c000000c00100180000004001001c003004c00100080040038001002000000240160014011000800000380190000001000c000000400400b800b00000050000000000800100000010004000000000200000070000003000000f0000004000c0220000003002c00100140060030000000c0010000000000c010000000000080000000000000400000040010008000000000b002800b0028002000000600040030004004000c004000c0040038004000000000000090000000001000100300030000001002400d0000000002801000000010000002000800700000000000000001400000180060010001000800f000001600040020058001000c00100000010000010001000000e800000000020000002000c0040088001002000400000060044007001000000040070000000000c000003000300000000004017054fe7458e54054fc7458e54056df7358e5421ede5358e54056df4358e54056dc4358e54004ff7258e5400cfe7258e54004fd7258e5400cfc7258e541e67f5258e540067d5258e5421edf3258e54006dd3258e54004ff7158e54024fc7158e541e67f5158e5421edc3158e54004ff7058e5402cfc7058e54056bf4058e5421edf3058e54054fc7458654186bf5458654056bc5458654004ff7358654014fe7358654014fc73586541867f5358654004ff725865400cfe7258654004fd725865400cfc72586541867f52586540067d5258654006df3258654006dd3258654056f77158654186f65158654056f74158654056f44158654006f73158654006f43158654006f62158654006f52158654004ff705865402cfc7058654056bf4058654054fe749825402ebe7498254054be749825402cfc7498254014fe7398254004fd739825402cfc739825402cff729825400cfe7298254004fd729825402cfc72982540fe7f52982540067d5298254006df3298254006dd3298254024fe7198254004fd719825402efa709825402efa50982540fef9509825402ebf4098254056fb409825402ef8409825402efa2098254006f92098254054fc74582540567f54582540567d5458254004ff7358254014fe7358254014fc73582540ee7f5358254004ff725825400cfe7258254004fd725825400cfc72582540ee7f52582540067d5258254006df3258254006dd3258254004ff7158254024fc71582540ee7f5158254056fb70582540eefa50582540ee7c5058254056fb4058254056f84058254006fa2058254006f92058254014fe76d8d5420ede63d8d54054fd75d8d5401cfd74d8d5461e7e54d8d5461e7c54d8d5420ede53d8d5420ede43d8d54004ff72d8d5400cfe72d8d54004fd72d8d5400cfc72d8d541f67f52d8d540067
  | 38 => 0x30014000000c000000401c00240000000000000c01700000020000004000c00000000010008001000801a00000000010019002c002000400d000c000000000000080010000004000c00000440020008009000c000000800300180120008000000000c000400d0074001000c003000000b0004002000000a0010007000800400280020000008000800000340050010008001400000080050004000000400b005000e000c0000004001001c01300000010000004001800300140010008002001800a0008004000c000000c0000004012000c0070004004002c0060000005000000000040030000000003003800040250028000000000b003000000000000000000000800300280000004005001c000002000300000020020003001c0010004002000c005004000e00140000000004000000200240000014004000801000480030010003000000700000000004003000800000000010018000002c00300000140014002000c006003001600280040024001000c00000000030000010000c001000000000080010000011000400c0004002001000000040010000000000c00800280080020002001c0000010000000c00000000030000000000c000000400000000060004008000800000000040004007000000e0084000000001500140030000006000400300000010000000001c0010000001000400200040000040005000c00300300000000001005c00c000c000001400b000800a000c004000000900000040090004000c00200000010000009001c00200100010000001000c000000c0000004017001c001000000500040040028004000000000140000004001000001e0000014000c0070000000000000500040030010001005800b00040180000000000000e0008002001c00200040000000001008000b0004016002401600080110010018001c00000100070014007002800b0000007000400000000130004008000000b00280010008004000800000000000054000000c000000001500140000000001000000b001c0010020000001c003000c00100000020034001000c001001000b00080030014000000c0000008015000c000000001e000400100000000000005004c002001c00100000030020000004c0020020001000000000500000008015000000700000000000000000c002000400e00340000050007000c001004c005000800000080030000000000c006001400000300030000003000000200040010044003000800000000000000000001c005000401400000080014000003c00200300030004000000000000300000010002001c008000c026000000400100000028000000800c001400c000800e005400200040010000000000c001001400100100000018003002001300080020000004001800c001000100240000000020000c00100
  | 39 => 0x4000801100000010000008000000400180000058003000c0000000000005c001001c00000340000000000000c0040000000000c000004000000200080000004000000000000010000000000400c0008006001400200100040004001002800100100020000008002400000040030000006000000800040030028000000000000040080000001000000b00200020004005003000400080130000018000800200b40030000006000000100000080000000001800300040000038018000801200080000000000000000200000000010004000c004000000b0000004000000000000090068010001000b00440070020009000000c00300080000002000800b0010030005c00700180030018003002c0000000001001c00000080010008001000c0090000000005400000280020000001002000400080030000004000000b00040010000004005800f00200030058003001000f001c002000c00800000010014003001c00f0008000000000300000000008003007400000340040024001000c00000080070064000001400300000000044005000000300200040004001000c010002800000080020024000000000100040070038003000000700000090014003001c0010004005001800e001800000200000014004003400200580000004000002800000000120000000000c01100040000010000002c002000000100180000004001000c00200000080000000000002b000800000100020004000000c004000c0020050009005800000000010020001000000000140020000005003400b0004005000000100100010000005000400100040100000002000400200200050010000000c0020008000000400200040000000008000000000540000008003000400f000c0000000000000000600040040004009001000000080010010001000000200000000000002000800100280010000000000400000000050014007000000000000000000001002c00500080000010000001000500200010004000002400200000050088000002c0070010001004c001000c0040004000000800200000010014005000400700440020000000000000000000040008005000400c000c00b00000000000036003000d0000000000c0060000004000c0050000004000c006000c006000800d000002900140000030000001c0030004007000400900000010004000002400000080020000026001000000080000010009002002f000401d0004001000000100bc00000000010000000001800300340000000011001000100040000000000000400500040010000000000400200100000048001000000400000000000000000c0030004000000000100100000008000000400300080130008001000c00300140030004000000800300180020004006003c000000400a000400300000
  | 40 => 0x400000070004000000400000000010000000000000100000040010004000000400080020000000000000500080000008003003000100280000010009003c0000060009000c000000c001002400100040010000001002000a00000010008003004c0050010004000400400040010010000000c00200540000000002000c0030010000000400d000800100000150004006002c00100240000000000000800500000010014004000c008001400400300000000001000c0010004003002c0060040000001c0220004000000002a00040000014000004000b0010000001c000000c00c000001a00000030000002002c004002c0000014003000000100080100000008000c0010000006000801b0000001000c00700040000000000002c0000018002001c000000000d0004002004000000040000000004003c0020000002000c000000000000300010008000001c00600040010000011000401800000010004000000800200100000008004000400500240000010001001c001000800400040010018008000c007004000f0050000001400000080010008047000800c0008000000400400400000004000000800000040020074000000400300000010008000002c00c00080070004005000800100040040004001000001000000040000003001c000000400d00040030060001000400600000030010000001400000040000008001000400000040010008016000c0150010000000c0000000006001c0000000000000000d00140060034002000800000040000024001000000200200000008001002000c000800c002800f000800b004c00800340000018001000c000001000400040020064000001c000000400500200000000001000c000003c004000000e00040000000000000c00e000c014000000900a80020004002003800200000030008000003400000040000000000000400000280020048001000c0050004000000c002000000000080000044001000400000000020028001000400000180100014001000c0010004001006c00000340010014007001c002000000900500010020000000001c00000090090000000c0020000000001c001000c00100000040008000001000b0010005000000000080070000000002c002000c00500480190000000001c00100040020004000000000400040020018001004c0070008001001000300080000000000000000200c400000000000008002004001000040030000000001800100000000010000000400100080000018003000400000040010020000002800300040000000002008000f00180020028008000400500200000044015002400000440030008007000400200080030014002000000c000000100080000010009000c00300100050008001000c002003400500040000000000000000300000120
  | 41 => 0x518abca49c9f86000000000027066c4a96e0002cfeb79204895498ea66fa822b54800000000002049960a8018823ad800069b1accae888ae2798000000144600000000002a32000000072d2eb4000000015d00000000000af10000b7498ac462000088d09d61b590fac7480782ef9e980ab13e014023147d788a600000000000640c0813c46262152c13800015baf98000000088792a0000000098e800054b0000925000073b000000000000000000be02fc20000000000000009d0aa842b038273b800000025fa8d7800063b02840000000000124400014be61690501c9904e86500000000000462a8485008000000000031d800000018a442d27fc0000000c3600005738000000000034c8000adf000080b00002709ace0000000b298000772800023d80000a800000162a3e5ce22f66e8904600008ca73614e400026aa9ce8410000027ea969c02383a0025e59f480000418aad1f2600023a43210d2ec5a800ca3a299e55489e40000396326000000002f8b2fadfe99e84e45aca17499f28a20000f3200013825f904880000cd4315a1ee82e0a4eb4b2db203d17a200014f800000000000000bf1844c00013e8c510b5655031b0602171a2628a2aa1180000001e2e9c8b03ea832a30affaab62788000ab9830054b8000365879aac8905691ea25852e0df27ba000008f0000c1a8c949e4800053cb04c02d2a222b80d38269222819c1f7ea81824c99a2c6ea7e8000166800056480000000ad80002af60001868440b106924a6e2a0630ca1d2a63e23aa758bd22ef630517780001390000000073e8000c0d92d0a5780008ae0bd458c24344881ccc211afac34712a80002f68530a07c85a0bb87a980008cf8b000001a403f99d0e32c93e60000000000000039400006fc1454000000092c011c4af80000f63136000000000000004e78000c520a0649d09e88d1800000009a84f7830847300008ba025c0001b8e16c285e00300060010000000000100580010014000000400b000000f000c000001c002001c000001400b00040020008002000000500040030008000000400600140000030003000400200000050000002001c00e000000700080010028000001000e000000800200020024007000c011001c0030008005000800500080050000000002400300040000000002000000100b400b000c000001c001000000e0014005000000200380130000000000400100040020008001000c008000c003000800b001400100180020034000002400100340060000005002c004000000a000400100080000000002002400200000010004009000c00200080030000001001c00200140040010000000c006001000100000000000000002800100080000000003000c0000004000001800000040040004000000c0060008001004c0020000000001400e0000
  | 42 => 0x202068a800000000000000000a340cca4e59812655a8902f90668062af2c724b1120ceaa0e86d2f3043100008e6b1b6a2685362ff00000001f920002700169188a78e92986eba7ea0002546ac00998916812e5a4116440a822495708dc186b0a25e905aca821dde979191a2a20e240000000c37295c6ca800000003f615819d80000000aa4000062380008b3ac1e02b14aa7478000000261689911e20001af2bdf80b03fc231e00023cc0b78000ba20b46390871a05500009fa21d40003188608800000005467b38f7c000211600018b6a6d9d6ca661efa0002cd87bdaf16c43967c598a91a1908f3497a2ecc1ac9dba7a8a7508b12fd26f98a3e14f8d760001eb6000134e00000007baa4e2000000000000000000974674800000022ba79a800000009a03b5305e0000000c0e110a5e31f2a2cc8000699128a35c180e00000006a580000002fce32f010a07daca20000ab80002902000000009c8000000034265d0000000311800015860001b560001aee00000005ef80000808000000000000000000250000000000000024660001fac00000004452a386da9d909e80000000000000001ee000000000013ac00000007f6981aa2823b236dabfc0139e1c3b8990c0000000000117400005544a12432ae800000001996aee9fb495c1b3ac2200005f2855c0009ac63d48622a6d0e901b6a12600010a40000afa3a89a769c7aa2a0000bd60001068c0201a21f000007f58000bc82eec8e323887de127618330b29cda6c600012548161bf400024840001d984c828b00000ef60000000b1f8000000000067c2d5a1398722578956e4b22cc4266937e6d4adc04e52c7a7ff04ae684800065c800014730b64d594d0aaf9edc89380383be245e299148e000194852522ca1f504c81678000b8dad849e180004e182063d72daea7900009de000051e1d5245c03d0871029638b8a6c4f50000000000002c9af400000009d69e72a5380005fe87de4e49034667889e36b03049042f1e36e9de806580000002fa6901a4d809580000002b82000000001f959482b00002b720f40000d24c07b13e455204415113d200000000000e1600000000000000997000000031fa2e6808c000295a87f052a075ac060002f129d9800000000008f10000775a33a8fa80000001a6630d932400000004d2276a0128d6674eaffe48593e2ab81c4c89c0e1c0a299aca658d809bd8000342800045f17ce0002cee0a1a5b65e18454b5fa6ce23f03763eea20a3c2800000000000000f4461208721032860c3e0f0c0e1abfa58a139abd306d4906817c1db126c5778d3e9e030ec000266e71facf24fe9b9a50d80002d880000000f427828c9a6e49a4c08b27aa4ff8d6cb5300002a992ce9fd09f87b5a95440313a09a706886601aaa79980000001d128bf20a271097deb029e2659d92e6
  | 43 => 0x45d181c21050a3a000000000000000000000c030440000000000001c6992a0ee000277676ab1b25ba06ac00011780000000000311a057000014790d089880008c11f466180000a9a0104779971e9eb000000008940f480005cc24187430000c4f0448000260a000118000031540000000b7c0000521ad708d20000000000039398ba0001c7000022e01912cf47ab2504c7514da05383504108ad21a09a940002276c75a9cc59e272e7e29a9e4ab000a60ca7982c506ee74b294c3bc278883601186400e340001d5a05600001349e445e01d420002c1c9d59bdc000000005c1fc80000000000140600000000000da8bbcadba1029f76bb0822200000001f380000000000b100da02b78f00c200250000000000000008c819420000338337095800011e400000001af80d6bb1ae2aa0980003fa0f9e4f40ff89d8b0a678c2c804ce979a844836e00005ca66e18382dc02703c1ae341f28dec87a9f5668100000000d6273c00000000000958128200000005ad00d0000317ca9d800022a800000030780000000b4f9f3419b02ee1fd98269182e9aa8098ae380869238f1854abb209800030a464600003010d1800008987272ae42ed0a92a14000036899c67a00a6a468090e66d8000950129e000000077f00000000f724cd219820308307930fd862e30282ad8000000000015889729f3946c7d999762e19720aca0d5800016922ac00005bc0c2a6c8af9c526800005200000000000a5b22400000000000085a491800062813183031cdc290a8d69681f906c72bf0301a47082300009b40000178a3f200020fa88a80005be00000000a866cb2fbe5c1800091d99860000a9000017cc0000494000137600000000b62e027ac19821c0943823816a88ee00000000236b779bbc34e95e07d800703ed310006700a2afb19e62e8156800020040200de88c42d0487c80862d6ac90b7e800042130ce9f68000715a71c94b1a1e718800000002100000000000000000023789320e2661400003f500004378000a7a13260002618000191667000006c80000000000000000008c09d9c70ba55a0000000000266c473b0404f089c80832d9800000009808a8a5f61a2429a174cb2da0aa9b700006a8909ea2b0000749800011621ac51a992c17f18ce3e51ef493b0a4c0001198c170000000000085e86627d306ec6bb00007d8828c00000000000b7200018be0a91b288e400000418000611000000000001c300000001b98000108c00006e4bc10cb03a3800000000000000000000000005000009ee1e8a9461ed22900fc2c71addc8e380000001a6a0000fd23b00000000089658e00005deab4c0002f1a6298cfeb8280001a1800009a800080619fcb4a0c487cd81bc53622d09ed1bea4df1b3800022b0000069ea4c00469d00b5e5270ba80000cda63e80000001b803f1
  | 44 => 0x500008692d62000207e8a80000200800046500009b9000026a9e16000000032e00000000000b5095100001c0e0000000639a450000000000012e8a6c955eb6da3c27f6152805403c8a932b2aae900006a1848400028f2000219e38b1a600002502189000023b800000000005ce800000007800000d8e0001674a21975896e00000000000000000092f8dcc0000f26a6280000000000000000000025ba25200000108b488dd0a1698692f44639c3000018aaacd27ec00030624d68000298849e00b80004a907b0663a1460ec0000248a27c3c1280e892163400015a600016e60000000397800000000001108000000000031f9e2a000279e0000000406000010a000000021e0000000017e25a205a9f3023080005b09b48000257410121a21852222a9996faa980c9639db1687a50000b35a4248c314a6c232c3e381ae664ebaca096f08700f99d7c5ea200628d1d9e54927d6a37021a44721de56286baae20b824af01ea0000334668a95858a8bfe0002b4abaeb0486a013320d120de25ea7ae0002cec5000000240166a8c28000540000000024360000fca0001c183508ed880400000002f0814f1736000000000000001448000000000094800000000f468730000a0b052e00002aab6f063400000005d990606fb84aa01007d0000297c650000000000000d800000001ab400018404b7033e0001dbe701000000000005fcaf72759af88bfd9108741a9ba67e8f6e8f4a2be5c000004d31020aa900004688a60000000062d000000021385c8800021600005c5000070d058688e9bc84ae8000000000000000000002064000223c000000000024420002a246fe303a510ad340000abc9be83b6000000089e000000021a600016661ab8000a8980000003214b5ca50a00000000001de000000003a295801eb00001ba31e89e38fd00002bc8000023e000271a0da201ca0f2cba9468000a3d1c8a000154e00026d60c3800029fa25e18ea4f6927a1629162108c648714a84228675f80005928000062300a84f09a2a26228ab65a84ac4993a27f9085c295a4689981612066203e0000000775218c92b1c12829995c0002c0200000004012b7806fb20cafc807686b9a9a6fdb1b85f1989cc8b878264529d61b200b86c2a5e229620b03af1de267698cc1650ea63fd86ca366acc8047847406c288447c12ae1490e0ac1d29c464994ae4281db05091e5e0589f7474d031c8400b60064877a9071a6eb6302e0146002802900004a0000000023d8019a39626018d4000092a4380d301ee020400031380c092080838000614800000000000a8800075180006808eca2b0b13aa3624ba00006b4497043a0000000000080400023f471d85500000df09550a385d7237a00027c600003b200000000001c44000128c00020f8c34139c13f2f82ae023008f28e3eab598f
  | 45 => 0xfc178034c608212e88d9d0a00025927bc31bc0d90b4ec7082b8c03a2c8251a772c808c6c21519de20f2c6000007c235e80000000c1a00031ae0000000a13a0e6c78b0426e78acc1a3ad123a0a2d625f23da74f14b201c800096ca0ce0002afa432a1ce0faa36654182ec21b0f4845b8eec95307a66fca9d2910123a8051afc3a61df86ea106693d2da268c8ea85b617b61232e1e171184280e8a0c73a128e5da1d5457993bc98a08f4b0a9b7a6f31abab2a06b8b678aac9bc800078600000000000c870e0c73912d40003196695a99a4d49d245451270604225005196c611580beac4aaa600000000002ace73a80004991090000000051900002198000740a3280000000ac41cc4000000000000000000000a7d0000c390000000000082b800058c80000eb00000000000c47800000003c40000000000000000000002a029120000000a35000098381de31d30bc0002d2400000008ffa91e000000088380002cdaacc32980000002d260001660ac115d80002c9c1c3a54e27719886b28a2e06400007fb80006bf8d36b8401b493eadf6b811cd000011c032700001070000000000000000005e284d810201142d72868b0612663e2ac8a000000000000001e210861452cf682697e871e268a356993ebb6114600025320002d002311d040fa17aeb7e1e4a5c62f32ad5af061e70aaaaa380006f83194297a4a210c938a32aa94aa6e1ddcb5b99aa6ab0dca000230e0cc8520000000059780000000000000090c00000008db80009f629781548000b5a9e609ed86cc0000434195a7c2b210000ac200000bfa8ce00002185818976000000063580000000422090000079d03842bd24c4819893a4efa662bec9a5c879b142000084886080008cd87fc00007b6000000000022d268b00000000ddc0000000b96000000000002df000000000000000bce00000000001a8a000000000001d2000084a3c8218034080001fd2b86392a8ee09a1b42ab6049099c00009ac2590acc8416a5c2d4413895f0355a538c798000184000000015f80001c20a3a8f1617017d0a7c00006b102fa92a001a0481cde0df996875e867cb7a0908342086853aa25aba580000000f7000003940001d9600000007f0a80000022980000000b38122c0000df48e517169b5000050e9d6a0000d9c2d318de33395029849c1a000035678f0a7aa6015e42e70000517a3600000000000310881a935c3619544459a6c07ae8bc80001c52338a80abe88ece33c0da482f8dc00618316a4b93302c5aa16ace800099e2f5a000000000020c2b2b0a1252d172c4fc9b042701b2400029525088dde260920000000001081c2a38d9a5a000232e3d8211e7592e1c00018360000014652b14a00002ce8532694c002cd2af80df8672163a00000008e01cba0000c1670980000002c12000000000000002a
  | 46 => 0x5c2266bce0d720000000000141e4741b78000083a0000000bc60d120000000c450000a1ab1ac505b12c81a1ce200000003ad2d82001806824d80001968000a8d998c00000000001ede0002bc28419ad458083629ef9b1a5d1175a0b00f90159000000011da43d8000bd38b98b12a50011f9d6ec5da4dc0000000a8825c84c0aec045b1ca82c793dc1c48d5c9dbacf87c00000b3a00008f580000001d8c550922a24f17a000018e80000c6200000000001c5e00012220f81702000000000000000002948000113a716082a72b133c8fc000043f021c50294180001e867bbab720258000954309200000002f40000b3923a8c382c36a4e8000164800000011fc00013162e308900002ee0b1200008f2208877689148819922000289c3da801c68200001fea324000196c00000000000e109a0acc0bc50000c66a60c00000006b5889ab94291822b26deaa29f6e624046e7531ab80000efc000000043b93ba0b1800000017f80001fb697b235a192000055e0bc069082644892288b0b1efe8aaae789651014997958800000000002b9a0000000619a40c5421a4eaeb94c09a4aaa200032001870000848800096321d800004c0018a676925985e00013140c48000000026e6f381c855f03aa7cc856c3531bb43f901b274e0cf241e000061e8874af68fec68f94bcc26000000000005e3aa5400000007eb80000000f984489232a420330452800058f000075131a600025a6334262e000000000026865bf80000000000a1e0000a9c0000a96000000000000001bd458629d00000000314000000000002ce8000b158142000000084aa342000000000000000000aec000200a2590e3a0000000644000000020c4a72248e96092a6000000087e165c9a609c630b060e54690eaa36945c8000f2800017fe12a1e5200000000002f8c03100000000b4013503dc00000000000000aba30520000000c579c0a0000000000318c0002cce6118000000236401225e641600003ce1adeb0a000020a2e568f5000000001e6000000092b9ae608e000037100000001cc206e000000029f8000006e00000003b194509a88f84000000000000000000000000000000026b80f3800021a800038880003df96f680d8860977800049781642b5ac30c4c86000b0a4140e399dcc16114ea0c9742aa82ec45bd2184a8b000000031400000000a632956662ae98280148200005fac3180009589db2000000000000009870000000161a96181840000482099acd000017123caa41e4018000a7c97d6045800000000001c6077278f80000001240947800077c0000000000000000000002230300000000000000000000a93923800009ca00011b80000000b2c1f8c0001e143b78000a2d000055e80f200000000001e96b7aaa1400001f443e000058288442aeb1901629c385f69522c0698
  | 47 => 0xd1600017765962530000000023e000000027e6c1d86a6443800012c80000000000000000049308d6a92000047fa8aa11800008439fe01ef11a89751be4a0190000001c880000000ae7ab7e09500008970000a64201200012da0b410a6960136832fad360da800048b9ea09880000a7f06bc4b7a988acb3086000000000016467aa886400007f235292f0c5606ea00031108baaae2000000000000000001ed8000136e7ec31a2168885e000247e67c8000000070a03a817aa900496812ae400000b926ec069abdb2b309aba87293a1d4e21482009bf0c645b22a345951dc0c239bd2ada0000a5ea2f80329c9400000007a780000000edac7d1ab6a761af03cf2bd64b11a9819e101cae71aae7e386d0000216c1cf1bd60aa1dc8642a7748500dd400015ac1d098c849f8cfc6a9000090c18f800011a48a9a34e91a96680000000000000063fa8543381b3c55428de1a884fe877120e1e9000000009405c3a4008cf00003d98000000000075780008f78b0e00003889e70000b2580005ed21d2bc4242c0002c922678000000000044a8cf600000000000d645dc06a85b580000000000000153e461800000000009a3800030a2ab05138b8e0ea0000ae624ca1578000000145a000162eafe1f6497080000001a100001e900001cb88bb2a98aaa96361c80d7e8aa18e2795800084d800095f800000000000000000a87800025e0000180aa6a34998926db1234001084c543052843c077eb6a305a2bca096b6d013c82a0b34092968240c96b61898c881a595c276d256470a0bcc8508000a64afb851c9b9025bb0220a014588099bb83b40baaac0a59e8e89b54827923c291a4b2c09161c81812cc4a728b800000003f580005242bb8000000030e80004d500000000000000000045aa35200022440000000815b004752140e000000000000002238000000000000000008ddb1a01e5a7f69c3091600029da0000ae800031cc2db94ec1fa19022c9a4a6000179013b8452a73a13066e948419ba7706c60000b46b01000012ca000196e6df8000939b0f65220000000121c6f019a8c7ab0269cc0ae4307000008c10367b000006ff99bc509800075291842f100009c6000035a23d0b4826c80000000a4280ec0002fb6a6ba6e82a906f049809b2a392e7c4ea8a0800000007a2225676499b2000315c00027e055227a8318000000014e20000d547e10b286af12c24ee1b101d02032be41148591008e0000d2209495c800000000000cc4289000049a0000aed108056800002090f80baca4f03ba800060f1d8a2d9862839481d4000051a795143077086643fab07221e0f4ab74125803203bc688013430c841e2a12aeaab72828a278000be585feb15045c754164043f800018b2aca7801322000000054e9f1a0000000ada8a366950000a34a8cc466902e6b691908
  | 48 => 0x4fc21f08ab137481c0000000222c9e1092cb6f9f441cfa0760001ff00000c2e00000000000000143a40289aa0a4000170c0c99dee1e4819a7c7075641491ee00002c485d8efeb551d140000000b76207868500006e0800018d9b8451592d61639388ab11da051d977200029bc00015f46b0000093794ba0002b5a000138c018282470419b09512adea1d00000000dfc00010225668e3224b80003f200000000000000000000000002512ac0014a2eeaf915c6000302c286884e26d0000b429f50bce800059088760af074677e825a7b98f5e1f18d4800005103698000769220400000000001b6e0002db800000000000000000000056d80003800b74a5c9566000000017380009892f9e0001372771980614cad74ad90bbc537800031a0b0a2ec000015f1c7200020eaa1b309aa69ab744a89936865901200016ca16ba040474a9c64cbaaae685ae8e2f4a59611ea7029fb8d927cb04ba0afa35400010a2a69043c49e0f6c2970000b9d05b400029dc90e8d6036631a40000ce8ba29bb23e904f80000ef2b3f20389fe14ee31c9cda7f798160001f0c21b800013c1ac8c790000ae3a6fe57fb19c87d1de405e00005f82fdc3e98000adb8b4a27380000dd00006a700000000000c7b1ad8b8000000000000000215600018a200013c00fb1932000000000000000002bd818b80000001da60002dac7483204ac3800000030b88fe9eecb0d0b5864e0a2c000000000000000001e7a044800002b80000001b16a3186a42f723e06612b060002f74000000028f07d800004bcc7f800064f000000015268c9a2720002bac000000099a8f5a3da15ca9f0000000000001680000607abe2000000051300003768e304de934a2cc0000c0aa268ace107c00005e6933ae4663c0000000000000024cc000220cb1880001d880003f78000000000048100007daadc400000007ee1b5000016ea780800002aab0c524829e29213f8000141abc2a946000276c263000074c08ec3f300000000000000000026b940c12e1894c0d009ab459bbeba4000048780003ac19a63852af27322caea97ab1c755aad21b794e088716a244b25beb5780005921ba09ad1cbc818930cad202206cba44e605091a9739378b83075a4c2065c4770c4612b012a489abd491e08420e80ba603912fcb4b82b66c225424238d4427caa0422e0000a022dd49cd23ce000079008d000057c80008321c9000025c6000076a4dc03280000eac0000000546000084f84d0baf90c21771d08b758c422b1910c00020ba0791c965e20e6c3970570b728ac89ccaed6c770248bb789967cb916019610d65c11e38bc31a5060a23aa4ad11ec4c187545771f685a20e1ab9d800023680000000000bae0b880002ac8a0c05423f3942a72021b09b3214eb5d8e6001a97aa10dae4ea4f0cac8c712c67ac82584008
  | 49 => 0x2d86ae9800000000006780776a5d8ce6585000058018a845409f039cb16e20c86608fb8e9602400f047800000131df4000000016f85d8c0580005fb237ebb98000000093847219700000000000206cb328cea7ee80002710000000312e0650dce41206e0000082c97300a60000000000079e0001e109af2c5e2e11928bf7a05c000000000000005ec943400022b44078000b232074add8fb60000000206800069c00002b68d8a0000000522800051d14ca00023ae00023c000017a600018c60001380000000036b855871f0bf40f900000001664b0e8afc00000005b30000000000000010948a500007c58000000036c0de800071a2882a048eee0002f02111000098180000002e3800000002248000000000087f800061b00002ad2fd0aef80000002d40613000000000000002604a3daa4424a2b58ab19e5c97a9350930ad6076680002cb000000000000002d6489e847800025d0156800000013444ca180a0001cb01be800000024d0a92906a0b98dd68af0000328800029b80000000000000000000019e825380000001dd819f8000022800081798e4000096a15580000000000059a2fe405800000002760000dea000022eafa11d4ad8a16a73380003090f3abfc25848e800000001cca0061aa040a00004c10db200000000002c78000000031b92b80001deaa8e80000000b0c3de8000000000000023f83e0930e00004c60fb84d625300006f6800086e91d6892802c50a2f4aa7baeb694f0cd634a9912647974abde0466a3897629c10800c740c18a5880000c9211c0000e74c88ad0e28807da4a5aec81d48ca4a592d48000309602a144a00000006be8110000000000011ba86d89180cb81ce788151eaa51b9400011b688699040001c4a000000025c1998000187e00001f243d0000420800027b8cba00014203a900009f12e160001b32b318000c3c0a0200000003fe800000000002a700000000000b8b8bc65ca293ea41aa9200008d09620000b1d000000025d69aa00000001c32000241283c1110000000046ab226a2596c07182d2a337ab1e18291623e82398c8380000a721aa3e3898617b095e01695f69fc1df295b80003fd07dcbef0ec80000b965b1000095a2b842bda4807fc8e4ca779db80e925ee0000446c2e8000827069ca2c800083d8cc239e037c089854892e052258915aa0002b42b8a000044a0000afd91fab0f201e92d2bd2b9910cc1ffad32133b134328078e67d0c5446d107e95e296852915465a5a52e47a049805caa425bb26507d28000c76a04c0000cc800017240000f2e000288c2e2a498043b0e6688a98405daba80000000000000000c8c8a0001ba6680117e84d13627aa020833e06f21d22f7a00000004be914438a98c4000301454f2e6e00003f29e281823500000308073400019d0583ada46d021280000000
  | 50 => 0x97680005480000000234040f8000b7b06b6aec0a1c43614cc0002b900b9000068e2b1800020224fb867a41100004718daa72ca8a400000007a08000000288a832800000000000000b6420821e40000000000000083500000000000000095200000000000000a3080009bd2640000248867e0ed2bcd00820001206bd195fc1271656390218ac470288346a050000000067b1d186d99f0ea4828b6000054a27500001d100000000bb60000318000000020da7b0703000028c000000006909c98000422126e0001c0600000007b2189eb890000941847c00028ba7c50000000030600001ae00027d23542cde6ac0d2c0002e541b1028e2fb8000803a0900c522240000000a1631fc0002e224ec212c0001a5200000002498000000229c351800090280004ba800092a8770000057a00000000000000ba480000002f003362ff24658b802c918564f2214456c992ab8f80001e1a1b895c8d94af7248c00000002fb161000000001da2fb47c09b9cb2081cc0b68000b470ac4a2480009522b3cb8c01da000000060922f28860000a59a17c6b48380698a57c01121880b5800000008a200000001a825aa39580009e300000002862bea80000001e84000000016a2b20ad80000000039c7b3318431100008a691d8c30a60866b9b72c18282a1ccaa9a8a58000c1ba524000000000003fc4d98000000000000000000002e5200000006cc12881862cda0000000000251200000000000000000042e4ad92e000011f20001d4005b1cbe01e83a60002dee9b08000b238000386000098500002748000000071c6e32fc4000235800000006aa1d608b500009fe94f08ca9aa6056800000020d28e0980200025ae236000090f800079380007cea4fc05a000000000005258a96000234a0bd0d820001f3c4f580000000000be9009c43526d2a1000000000000000000013d08a4000222000009e08340e08b1f017ea7880000002748c7c20c0a6a0e200001b263481e7e51f05d0b1a1aea7f480fc136a844bf58412391148c00025dc69100000001992000000000021bc000115eb8983401c780001ef9a2e3d388e207017645641fbc7c7a72000000007ea1a1a989aeca00018c0000000071b800000000008e1000000000000000000000000000030ae00024b65ac000067100007380a6600015d25022280aa5800038a00009b10000c5880002641c6a000308424c13c6c82827cc25053442a207a3e731f263b8000ab080008bea7d44b8a8760d9969ebfb800021e8000b9121044bca8f000000f86b7263626d80000fe8b4200018d2000000000000000002a8c00000002448000000000094e8774b649ca63aea42eade800000032100000834c7612f8ae480000000e1e746a8ec0001fa200003fe0000000b13000078223e27d5010c67926ea000290000012020001d94000
  | 51 => 0x880007c8a73e0000e620001d1c04dacaa5a28000034800000000000001b587de9fe8000275e6ff31023d01b0694f80000000bea2c600008fa00005a3aaba000000000004a097c1b7c711800000000007af000000000000000934a1f906200000000e4000017d09ea67a8000009960c5c20088000003659300000001e6e46c80000001f4221f800050f922826989ba5e7000000005e80000000672b186a798a4a55d8f9a2670000341800000020dc00000000e300008f90f968e487f0aa7a84c47086504400000666800000000000000000177a37c0000000000000071980008640f7400000007e92c08000000000023be00020b476b812854d0000689918c0000d0400000005d8045a00010e80001fec19504a6bd131280000000000269013a0000c701fbe00001ac000202a962878c1fe0000bfa0758991a80c9e580005678b20b4c00004a52456a3e8cee00000000000f080de0766000000000006320000000199800096900008e700005bf02dc1cc1f9ec352746bf88ce4c3a000063d80000c6a39ec542d4e000000000030d68552fd43eb2de60ac2790bca21dac0621187f5048000000008020074be3a9feabe04fab432a642b3ae3c0b5170aa3f1d2a142a9aa3d41ae880b982e4129e0c4fda81c697a1f66aca4ee3ec285c4fb272a0b28ee8000274e000196449087ec00000007a6800000900008c1a386b0590765010000617226cc2c000000030305eb0c925411338b291d7800019fe2940b3e9e69c1c000307ca0f8000000257a65113644e38af025500000002738aef0a5ab409e6c0002fd86a427fe449a1c800000007faa4d40002e942c18a720001698b9280001719c5c4f315ba5d219ee10900000002e8c0000000000000000020b21b4a9d4000000000000000000000b25000087a2a72942000008780000000000a0400007d600000000cf470d80000a527140f02290a6c0000594956034780006e5aff8000000e00000000000a1e11791523008000ad70000191a51617c0f2c60700007f100005cf29f6acd8d748cd0000402af547740000be10ec20001312849016e000251c60318840002cbc00010dc0000576330000000016727f309ec000222e000066a0001b8682100000003002b08024684830de00000000000c302cf1f285a107360000000a84800000000000000000000000023a0000000083e0000882000172a23c00000d7b1ba22d8e922bb800074a2dc28ce0f1a3ee2e80b4195741538000000256a000219c00015e860605f21bf96a400025f448f8000000215099d0102a2522de558b01ca2002a6000211452c175e87b2efa8d88000731800000029425a180000001440000288e00002ea75a000000024a05cfa9364460000000009217dad90000038a0002bc000000000001732bc9931e425ae0800002b200011ae000000
  | 52 => 0xe6bcf1ec22951290042002a00010400000000000000066700000cf000076f000029f0000000216e734a87c5a3064eac9803c208800009080001ed102600000de6a312f626f9e9c00014146f8aa46c54800061b8000c242c64c1500000000244aed8dc20ae876e3ef0a7642299d69842a7e00004e060c0abe48496bcb638ad0b7d245c0000c3caf98000a9884be7138000000000000003460000000000000082d99620000eb2bd5a46e4ec925ac6618c228caafc4e60a0e0002a1c39f2d100002a8898c1c22c33182c53f80000000ac000014808740e949c281228a3a0422c22a52af3155c0000000bbc0010000307e100176ec3f8e685e10956000000074f800032a00002730e125b505c845080001d300008cc2af483f158e00000000ad16da0001f0a000291c72d8bf200005403ff29c255aabf4aaa25c40e480000002c88000206e6d922025da8000000134297c955abee861262c0000a9d00000002e1803193a8c729be89d700000002422a5d00000000000abc1954a958000726975422d2d8a748ae86a941e24b7c95380b301a0aaf065256711c4119227e302b208612a4648759d3616c915c00007985630504c8caa3c6690000000000000003f481187a26b0888cbcf9d8400005900000000000000034d093e08e9f5c9d51876560a2da2fe879440eae623af910400013e47c19ed456880000000000b1b026c0000a0a31eae323b59292561275233308860001c081e1048e9f300005348888c1a00004179b346d1322a1cb015200016a01332d1800000007cfa8c47af8f780000000a781cf2bc910e40002888a5a873a00008c800000001c02b9650ca8a85a9b06cbbe0336b14ac320002c260001e409bb074e0000000c0f26807191564000011a42e00004b01c8400000008b60bba50f000047e28c8000000000000000000e6ac6d153600017742c8800082804a4b3895b88b32ab279697b8ac92510a15a7de11a00001249e125121e2c5f894dc00029168f99b4ebcd90ec0000470a68053a06e800000000c2ac500000b2279427fa0720000000b052688a5f98d89368c5a0000db03020000c5f80005fb8c9e000272c0001558a4c91400002c506be000065ea9ecb562ada106986a11b00000002db09acb15a2529726ad50a44bba941200007e63c7000042c000000000005ab0000000000000005825aea842000063c0000f1200000000000000000082e000000000008e600013ea9eca7162ce1c6c2db000073f82620000000866a9242fe1a8e30d166c6b8000077380004f3a838069954c36f8000000000000000000000dfa000322c1ea0000000035c00029348c48000000000054c095000009f6128a36c052a7dc44b800000004b4000144416e9bc607b215e2c724ea00000002a7a6006518000000000000000009749ae48a0941c545800087
  | 53 => 0xcf8000000000037d89faaf428c0b98090a2e5000088e0c4c3a2271203524381f31ee20372d3a2ec80002c09c740000000a61a6441c2307a00000008d100000000c8c0000ecc5d4a6f00000c8e95280000000000000000037480005a7000000000008382426bf9a55679c1cd441b97940000be600027ba000000000019ce00030325a699784270bde000000061380003a308b00001ef83b900000000000b9c15120002454000000099580ce9a683720000000bdf2baa0278000b42312a56916b80002e68000001e000124844cacfa00000000000c7c07f0d14038a6a41c40000101891e0001b463579eb45fd9ff40002f6a856800023e942cbd493a60152ad000015b42098000000000017a907a00000000a69e6200000009cf26222eb000000000000002a1a72600000001e50263ac380000000bb680fa5df025e0d201d8c60000000026ba00029ea9148000c8906c02f80000000231603f800000024e40000000afb96040000000000050c00000980000000000153203d94fc0000c261ec9c163c608c000000000001920c62a48a647000039f800000000003c0843839216d00000000289834e00000000000000000034a80900000000000c5e8dc60001b3600007ba112aed4b66800044f15b0000000049a83d60002f64000197cc8600005fc0000c22800044d800066409f4424a47c259ab4e482a18e1f9000000000e00001e64ba90b2e8b183beaa113401fb8ab200023b01611da867503ae3161ffa02f25ac00016e40000214130a08ead78e04740103046f1e489d8290e0ba2a2ebab20bc59420ecbd7848a76181a43219f94bc720da0021b1e4da9d82c3107aaaa1afdac63914c94899a08169f5249580000000806a0d9af6402000000025261fa8000a19b0be000124e036890293f800034389d8b620030c531fdc45c8840a6528bca2980003eb97d2000259a858032a4e11a1c257018c8ff088a83199cc69a228413b0f5432d9e7c547000047d0fa83e18000000249c59c0f2497f0000739877c600059c7b80cd23402c5cc2d0bca0000000000238a8a78000535800000009104130b10bfe96be5d5800000000008b70818c8c29380000cae10f8000c2781f8000026017b800000000008daa2006568000207000000031f60002c10bca8000b091fce86cafc003a2b2e1f2208a49425e0000226e1d4000000000004db119c1602d6683fa642b012a7a0000000c7215fa0001410000000000000003a1800000000000002ea28ad80005e60156533a528b219218a06800000000002de1dec0002fecb10a684000298e00025340000000000068400012101e8316441c31667c482920000000b0688de98794e600003c2030264e52dac6a45587281499d1037bb130bc8928698a82f2ad48000b2600004608faab931dfe00007d2000264800000007e680
  | 54 => 0xbdec3caa6e000146e0000afe8da101a00015720000000000000041b1c4886a000077d906407c20e8c5b2a800001d1618c032255580000000000000195800000000000aa00001c820000000a580000000000042b800024180006ee90ba10b000003b800000000000000000a4a00000002b440001f8000003d45b39fd069f9b0c5f10672756000079db22078a1da28069caa1a5102c57b2d9ca49a17eb1c080a00008be3efacccc86aefc4389bd0b780000bff00007ec98b204e032cbabab4048680000002ea09be0000000124a6d32dcc0002e0e7f00000baa80002dda9c023380007278eaa00008a8994947e68d1e1a0ee06d800000009bb94f49931bc49358000be493d80001b5a4b48fa2000000076200001d7b05005d211a0000000000125200014d400000000000000a3e2910000000000000004acb15687008845c70bae00018dab96a92abaa030c145afc80000000000000000003c6bb489da7b400000000e701a614fa1d71c146f60e7a692800096a00000000c5c2b50000b9b1d746f2ad7a9af93fc9992ceaa3818349f2898435e0f8836d24f84262f420728c1231a8de035b8b688d70aca91c9e8c0602654b5f0862000000059b8000331a8700000dfe24800007b68000b0baad499f80007c91f180578000c20942ec67ae7e0002c46000000000000000001a3683896ae2282658483131a8930000ba0895a0001fa60000000bbbaf9a2a080000002daa7e72558890812c97d8de497280002588c52b5a05cc000195257106ce000067400022e20001baa5f080000bf01323b1000000000000000370b2780003919ca04852a78182162600000003208000000185816a800057a8000000029800000009e98b7ac2a278200000002c6a56649e881010991340001db6b9ea1c200000000000fc61f8a7080000a8e00000009fc9862b9a8604643913e00000000001e4673d0000adc16226960000000068a00000000000000b880000000000040400000000bd81ca88fe0002f7036796de00007163ae0000ae52ddabdb800058780000000fe0353846a39520827d024203799a3a3d62ff43cc196a4150ee6000309c65300006a080004e90000000000000000000002a9c000000036421328520000000000000000006f0b0124481c505aa9ca43be84c4188220898b1f107102b1a3c511f66cf8c1eb2d07042861d623c3b10a0d52cf0093a308bd61c1e54290bc14195be9118b04b08956c5858c78b721ad07878a100001fc6531b04a426980400013b46c52d1e0001c24c5d00007f88000bf9000008a0c7000000000000000000103c0001b7698d001210c0ee000000009d28212c3000005e7872e51c000000000008cc98960ed19306af80004648a8c7602b507a381b6b03818e4cda4c6b9cae421a02172acf9dac7fe1a84000193a000000000000004
  | 55 => 0x5d38bf035f2a0a00012ecb2e1cfcbe280000001bec8e9a48200020e46230000000321647982e27ab80000000000000000090392fe8a4800006786f869ead4a0000d880001cc00000c3e17506e60001c544eda23e8bd0000a1929ca000040e9a32d56c3e98bc2e8977ebd703521b714a204e80a091b0b44467a86e28524086eb16e006a10be34f163e9381c8caf38cfa6372aac9c4200c94a9c2cb2691680001f5a0000000963a8ca00030da281287a00580d8aec80000002ef478d281e7ff8992153053016326ca008a3b46eda404b3708d29b997d425fa9a212c1072207aa280a080006220000202299c9d900001f11ff60000000000000000000003b7187800006388bc000046c0fda0000c229e8ad3c8f7000000000008c626a65f000006dc00005f20ffe2ca85da00027e269180005bb9e92205800000030eead180003cd80002be23b6692096c4d800000788000805857e22720940000000ba7800000030eaa05a5b0174a6d873e18643dd800075c00007ce0a22000167a36e12b0774b0065b4ae0652623561008a7000000000002cd40000000b7880002fd800000019c2000000000016dc45d9a880000000c780a98000073856a0fe2000192e000211068f00008b98c800002d5c000006c0000000566197e00021a06d28000c19042a42a8eae26f2f4020e2ce6bcb81fa1d8283a7dc17340491fca3740a286c004f238e24a400000000000000000000000031eea2fafa8b19864a4478000788b1700eeb1aa593ac4425a1a7479a13f4434a8528359d323bd190600000000002102000000000000000fe24280000476957a3721b080002140000051149e0000000af780000000000c28234c3a78000000007c68c07e07bf030a51a00000001ca298c800080a30d261c0fb2ac2932a5438000085ae3a574000000000b618598800002da627f000068a1346bb8af603d300000000000175800083314a0b9200cc76380000f8800000000009a597e666d00003548bda5fd304444c157000026a08b006c60000904659800091d2e1a6dd1a0c3040000bc3800002e8000573162cb650c66140ac4ea39800016204f6c84800086fad460f30c4a000000069c8000c1980000000000ae32a180000be23fcb1a8b48800097e00000001caebe1b0ac00000006fe9f04165aed000000000000e6e2ab8000a6fa46249f000000000000001e0e250a98200000345702efeb7180649ef22c2000176c1eb8feea0b8924b452ecea4327d047780001979608afa9ec600000000000000842800053a232c3430988c410000552900ec2aa1642a680002b890f2000277c1420aea324080e000244473d90c88a300000002158b0319e2a3f9d760001f720000000a48a2169d080008dc000000000006c0ad380000000000044e000253655f8c4e36f182a81531de00023ac0001
  | 56 => 0x13ca15e07d6bd8a25200000005ef0d8c924014c0a429ac0001a0a0c41f8800013da96d03ca000000000000000000000000000051e8000a5410740000000000203417900000000000814a03cabb800008a88f2000000000000000000000000000083c90ce0001c001c180000002274000064c1a305c20000000000130a57b80009120000000000000003f014b244a12180000000000532131c3d58000c3896804398ceca9704ca69f314609e25fe4172edcb54085607fa6ac04fb12445e8e5a23906f690597509969c7a0ab8000c712fe09b8000000003de000214a3cf80007168000181800000000008a88000000000095d9e7830386b000000009c91ba464214c480c0ae60001eca3a0242a04c061e29e31200001f4e0bd80000000724c81969407430c8519800000000009df95d40002c00000000042d9620a011b8a91325140002a8270e8000c1c1a7851824c00001b680000b6a22f22a4ba701260002904000000000031f800000000002fa07f999503e48e5848d994e233321e1b8a4f29d12da04d7aab82319452c6fa49a78121fa5e4b1164b9016098f2b16b84a820000183a00023ba015afccbd42a6c40922e47a91faa40e2178683913888524d28981596071000000000001d9224637200007b10b520d680007b91f6c36118f2af1a7a40c7a63878c8000000130000000000212e143c8a0865ff14a8000210c0000000b1623bc9671a061e2992418a80004468dd884e8000575a50e77317baa00a56cbddab6600029140000d6a000187400000002c49b5c0b4a77a00000000f6800000000007c2000086480000001310000000000009deb1cb02e0000d10000000000010b263280000001d5c47a8000000081400000000001e060002d7800000000002fea000243c62680000001c3e32d0f8c2949d7200000000001b6015981e8c3f0000000000073580003a121c600004501bf1f9613716e216da768498803e3d88bc2c4300007e600000002fca34a30f44b627c800010da0000c3888cb17253d9e420002814638005e576adfc22000000000000000020a7ae04729b684ea000115a00011be24705bc65784b60400000000152a2a880008fb2940b6011162d500000002d6c686000001400000002fae15a02f03f71b0e0001f8200005a60001c8600001aa0770000000039e2d42944999a21246b2fb063405984cb15ae0170462ba9a5d80782e5e5c40de28abab8ac580000c118b7e3a700000000000000000000025c0444aee4baf1b5ebac00000001740000000061c80005faadce1de24bc00000005ec000000003a2000183e000000000011ca000027a8d422540081b6248c0000824b056be52322921800067d80000c8270e12680000e686f4c73a50c0000000416aee859f9782a2b853881398860000f1e4aa800000000000000000a0d0000
  | 57 => 0x64d1f7c74b80001aa972e00e80000001fa0820063e22e88b27960000310000000000006e20000c8a11580002c763c40be819daafe88980002e9000085989b00d60000399292c9ad965a317ac5aa1699947c8215c4698000c6080000000000723a74c2581a9229d1c3c00000004a6800000010c09a7a1ca5f7023299c80000002cc244909d000003980001554c53acb23a689949ca00000002e2c16e22b224c8b9e0001e360000fc04bbb122b9714ac6b889acbd9a3f6ba105723a80b90235000000031780000000861a21000000007710000431800039980000002b6c0000000000000000000008c696f221f04de56f1ef200027e426e0000000056a3d9110661f25988f19358a9f
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe69105d562041914dd0a3aac408002b3a0c755881000566c18eab102000a6e85dd162040014db0bba2c4080031b5d774588100056741ee8b102000acd83dd162040018daeaba2c4080029ba14745881000536c28e8b102000ace831d1620400159b063a2c408012b9a04745881003572c08e8b102005aea801d1620400d5d3003a2c4080023ba1c545881000476c38a8b102000ace83151620400159b062a2c408012b9a04545881000572c08a8b102005aea8015162040015d3002a2c4080029ba17735881000536c2ee6b102000c6d75dcd620418d59b0f39ac408003939d6735881000726bace6b1020c5ec7109cd620418bd942139ac408317b2442735881000636baae6b1020c7ae7815cd62040095c902b9ac40800333e1d735881000667baae6b102000e4e755cd620400199aeab9ac408003935d5735881000626baae6b102000cce745cd6204001998e8b9ac408003b1e0573588106376240ae6b1020c6ccf715cd620418d99ae2b9ac40800333dc1735881000666b82e6b1020c6ec7105cd620418dd9420b9ac40831bb2441735881000537428e6b102000a6d851cd620418b59d0639ac4080023ba1c535881000476c38a6b102004ae681d0d62040015cb03a1ac4080023ba1e435881000476c3c86b102000a6e8590d62040014db0b21ac4080162f61176d001001c3e42eeca0020058bc84dd9400403b0fb0dbaa80081ef0f99375500100062f31eeaa002000c6e62dd540040010fd0eb2a80080221f21d65500100061fbaac8a002000c3c7559140040018beeab1a8008003171d5635001000637baac4a002000c6c7558940040019af07bb220080033520f76440100063ba96ec8802000c7552dd910040019ae65bb22008003354cb76440100053bc12ca8802000a75825951004001cae64b2a2008003954c9654401002e3bb82ca8802004e7370595100400bce460b2a20080179c881654401000738902ca8802000e37525911004001c6aa4b222008003a5cc964440100074a992c88802005cb7705911004009d66e0b222008017ac8c1644401002f59102c88802000eb12059110040019aeedb9a20080039559773440100074ab26e68802000cd7761cd1004001caaca39a2008003a55907344010005e2c10e68802005ed23058d10040015ad0eb1a2008002b521d63440100056bc12c68802000ad58258d1004001caea4b1a200800395549634401002f69402c68802005cd77058d1004009da6e0b1a2008017b4881634401000768902c68802000e66855891004001ccb0ab122008003b1a0d624401000762c1ac48802000ec7735891004001d88e6b122008017b8a01624401062770c02c48802005ce7705891004009dc6e0b122008017b88c1624401000738b2a608802000eb1644c11004001da2c69822008003b85893044010
  | 1 => 0xd06192c8080028fa1720590100051ec2e40b202000a9e83c81640400153b07902c8080038b54b20590100074699640b202000e2d524816404001d1a64902c8080161fe1d659501002c3e43acaaa020058bc8759154040070fd0bba2c6080021f6177458c1000c77416e8b1820008ed82dd1630400b1bd0fa9ac6080063720f7258c1000667992e4b1820048f4815c963040038dce4a92c6080031b5c95258c1002c6f43c64b182000a5e858c963040014bb0b192c6080039354a3258c1002c6e43a64b182000ccf724c96304001c9aa4992c608012b52053258c1000567410eab182000acd821d563040014bd0bba2c608002976177458c1000567416e8b182000acd82dd163040095ad033a2c60800237a1c5458c100046ec38a8b182000ace82151630400159b042a2c608012b5a045458c100056ac08a8b182005ada8015163040015b3002a2c60831735c437258c1062e6d086e4b1820c5cd910dc9630418d1bb0f392c60800297a167258c100052ec2ce4b182000ad7815c963040095a902b92c60800333e097258c100066bc0ae4b1820c6cd4815c9630418d9ae20b92c60831b368417258c106366c882e4b1820c58de871c963040014bd0a392c608002976147258c100062fb96a4b182000c5d72d496304191cae21a92c608323968435258c106472c886a4b1820008de8794963040011bb0f292c608326976165258c1000666b94a4b182000ccd725496304001c9f04a92c60800317dc95258c1000727392a4b182000c5d725496304001c9ae4a92c608003135c95258c1064f2710aa4b1820c9e4c215496304193cae20a92c608327968415258c1064f2c882a4b1820008de8714963040011bb0e292c60832297a145258c1000666b9684b1820008de8790963040011bb0f212c60800297a164258c100052ec2c84b182000e4d529096304001c9aa4a12c60800237a1c4258c100046ec3884b182000a5e8510963040014bb0a212c608003335c84258c100256b40884b182000ad581109630400b5b500212c608002b66004258c1003c6f43e40b1820008dd87c8163040014bd0b902c608002976172058c1000726a9640b182000e4d52481630400b0f90bbb2a6080161f21d6554c1002c6e43ac6a98200a8f5815db43040098ece2b2e86080132d9c564d0c1002c6fc3ac7a182004cd67158f43040018eccab8e86080031d59571d0c100565b322e3a182000cb5645c7430405f9acc6b8e86080033558d71d0c1000673312e3a1820058dc83dd9430400b1790eb2286080163721d6350c100056741eeab102000acd83dd562041934db0f3aac40832399c42755881064735084eab1020c8e69109d562040018df0ebaac4083271b9c5755881064e3638aeab102000c6f705d562040018dae0baac40832799c41755881064f35082eab1020c9
  | 2 => 0x8539901000556c10a732020c9a3d8594a640400153d07294c808002a760e529901000717c12a532020cbe2e7254a6404197c5ae4a94c8083278b885529901064f1610aa532020c8a3e8514a640400153d06294c808002a760c52990100070fa96653202000e1d52cca640400147d0b194c8080028f61632990106354ec1c653202000e2d528ca6404001c5aa4994c808003a3e09329901065747b926532020cae8c724ca6404001c3ea4994c808003a394932990100070ea92653202000e8d524ca6404001c1aa4994c80831ba3c8532990106374690a653202000a3e850ca640400147b0a194c808316a7a0c32990100051f42e413202000a3d85c82640400153d07904c808002a760f209901000716a96413202000e8d32c826404001c5aa4904c808003a34c9209901002c5f43ea8b202000a9e83151640400153b062a2c808002aba08545901000556c10a8b202004ab681151640400b575002a2c8080162fa1e43590100051f42c86b202000a3d8590d640400155d0521ac808002ab60a435901000e37392a4b202000c6d72549640400b17d0f212c8080028fa1642590100051ec2c84b202000a9e83909640400153b07212c8080038b54a425901002c5e43a84b202000e2d52509640400147d0a212c8080028f61442590100054f41884b202000a9d83109640400956d02212c808016aea00425901000667b9264b202001ccc724c96404001c9aa4992c808003a3d0932590100074621264b202000a9e831d5640400153b063aac808002aba08755901000556c10eab202004ab6811d5640400156b023aac808016aea0075590100055cc00eab202004ab681dcd640400147d0b39ac8080028f616735901000557414e6b202000aad829cd640400155d0429ac808002ab60853590100051f42ce4b202000a3d859c9640400153d07392c808002a760e72590100051f428e4b202000a3d851c9640400153d06392c808002a760c72590100255b408e4b202000ab5811c9640400b57500392c808002ae60072590106471b886a4b2020c9a3d85949640400153d07292c808002a760e525901000717c12a4b202000e2e725496404001c5ae4a92c8083278b885525901064f1610aa4b2020c9e3710549640419147d0a292c808002a7a0c52590100054ec18a4b202000e1f52cc96404001c3aa5992c808317a5c4332590100051f42c64b202000a3d858c9640418d53b07192c8080038b54a325901000716a9264b202000ab7814c9640400956902992c808003a3e09325901000747b9264b202000e8c724c96404001c3ea4992c808003a394932590100070ea9264b202000e8d524c96404001c1aa4992c808003a5e0532590106374a40a64b2020c6e8f214c9640418dd1a42992c80831ba5c4132590100051f42864b202000a3d850c9640418b53
  | 3 => 0x31822059dd2768c63044023da4ed18c608812af4e0a318c11068de8c146318220d0dd3728c630441a1ba2e518c608833fd4d4a318c11067fa8a9463182204acd471d8d304400b1ed0db8a60880167521d314c11002d6a432629822005bd0804c530440059b0edb9a608812b361db634c1100166c3b2a69822002cd87650d30440016e30a38a6088002ec610714c110256e9b98e29822000be1821c530440017630928a6088002f460e514c110007a8a9aa29822004cf07690530440016e30b20a6088002f460e414c110026783b2829822000f914350530440093b10e98a6088013361d9314c110026e838a629822004dd0874c530440197a10c98a608800bb4219314c11001769bb2629822004dd2764c53044009ba0ec98a608800bb41d9314c110005e9c2a629822000bd1854c530440017a70898a6088002f4611314c110675e9c126298220cebd1824c5304419bba6e498a6088337745c9314c110667a9a926298220ccf51524c530440012ef0aba42088017748c173841102566b3b6c70822002cd67618e104400178b0431c208801774dcd308411002c3f43ca6b28200187c85dc965040018dea4b92ca080161fa1e52594100052f41ca4b282000a5d83949650400b0f90ea92ca080031bdc9525941000e6739264b282000ccd724c96504001c9ca4992ca080039354932594100052f418e8b282000a5d831d165040014dd043a2ca080029b60874594100253b408e8b282008a75811d1650400b4f5003a2ca080229e600745941000537410e6b282000a6d821cd65040010fd0f21aca080021f61e43594100053741486b282000a6d8290d65041918ee21b92ca083261f61e72594100052f41ce4b282000a5d839c965040018df04b92ca083271b885725941064e3610ae4b2820c9c77105c965041910fd0e392ca0800297a0c72594100052ec18e4b28200087e8790965040010fb0f212ca0800297a0e42594100052ec1c84b282000c6d7290965040018dae4a12ca080021fa1c42594100043ec3884b282000a5e8310965040014bb06212ca080129da0442594100053ac0884b282005a7a8010965040014f300212ca0800317dcb32594100062eb9664b2820c5e5710cc965040010fd0f192ca080021f61e32594106352ec1c64b282000c6d728c965040018dae4992ca080029de0532594100253a40a64b282000e4f824c965040018bee4992ca08003939c932594100062eb9264b282000e4d724c9650400189ae4992ca0800393d0932594100072621264b282000e57814c9650418dca902992ca0831b93c8532594106372690a64b2820c6e57104c965040010fd0e192ca080021f61c325941062d2f41864b28200887e87c8165040010fb0f902ca0800297a0f20594100052ec1e40b282000e4d32c816504001c9a64902ca08002aba0
  | 4 => 0x344001b92e5100c688166b62192018d10006e4b924031a2000f49524806344001f8242900c68800237e0d7654d100143e43acaa9a20038de87d8d534400517d093b686880123d20676d0d100154e41ac9a1a204acd671d8f434400b1e90cb8e86880bf3518d71d0d100043fc2aeca1a200387c855d943440011df04bb286880063b2097650d100145e43ac8a1a200a8de87d8d43440a5a6ea4ba4a2880034d5497494510006cb992e928a2000d95325d2514400996ec0ba4a2880136cd817494510006d9102e928a2000db1205d251440074e90ab24a288003655d36394510006caba0c728a2000bc58218e51440013b306382a2880027a608705451001d3b42ec8a8a20038f48759151440092ed0f2a2a28800f1d1da54545100066a3b6c6a8a2000cd47618d514400178b0431aa288002f460c7054510005f0c10e0a8a20028dc839db41440011b90cb9e828800237e1f63d05100046ec3ec7a0a2000977825d641440012eb04bac828800355cc97590510006aa992eb20a2004c77605d64144009ae6c0bac82880035c8817590510006b8902eb20a2032ad48359641440651e90cb9c8288166b5a1b6390510006aabaec720a2000d557518e414400178b0431c82880027660c7050510004f4c10e0a0a20049b584dd5414400b1e90cbaa82880167c20175505100555b426caa0a20d2e3454d9541440151e90eb2a82880beb520d655051017e6a31ee6a0a202fad686d8d4144001d2ec831a8288002f160863505100055b43686a0a202fe9463d0d414405fd28c6a1a8288002f460c7050510005f0c10e0a0a202fcd4635d231440055ad0db1c6288003359db638c5100056a432a718a2000ad48650e31440019b6c638262880027a608704c51002c7a432ea98a200097585dd1314400b1e90cba26288033351db634c5102cee9b98e098a2000be1821c1314400b2e90ea8aa0880169d219515411002db8402a2a822000cd4635c7404400b5690ca0e8088243a518d41d011002c7ac0ced202200087f855d940440070f90abb2808800237e0d76501100146e41aeca0220008ef825d940440031d904bb280880031718f75501100062fbaec6a022000c5c75d8d404400b3690ea0a8088016ad21941501102969a3aa82a02207de9463505404400b76100a0a808800a3720e761011002c7a40cec2022000c5c635d440440311b90cb98808800237e1f63101100646ec3ec62022000c5e75d8c40440018baebb188088003339cb63101102566b38ec62022000ccf635c84044001998c6b90808800335d8d71101100066a31ae22022059cd6768c630440055b50db1c6088003369db638c110255e840ec71822000bb18494630440017a706a8c6088002dc616418c1101976831c831822000bd383506304405fda0c6a0c6088002f4a1a318c110257694346
  | 5 => 0x800333e0972d8d100052f428e5b1a2000a5d851cb634400153d08396c688002a761072d8d102556b408e5b1a2000ad5811cb63440015b500396c68812ab660072d8d100062fb96a5b1a2000c5d72d4b63440011bd0f296c6880023761e52d8d1000667b94a5b1a2000ccf7254b6344001c9f04a96c68800317dc952d8d1000727b92a5b1a2000c4f7254b63440018bae4a96c688003931c952d8d1069f2710aa5b1a20d3e4c2154b63440011bd0e296c6880023761c52d8d1000667b9685b1a20008de8790b63440011bb0f216c68800297a1642d8d100052ec2c85b1a2000e4d5290b6344001c9aa4a16c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c68800333dc842d8d102556b40885b1a2000ad58110b63440015b500216c688002b660042d8d100046f43ea3b1a20008dd87d47634400159d05a8ec688002b360b51d8d100046f43e43b1a20008dd87c8763440014bd0b90ec6880029761721d8d1000667b9643b1a2000ccf7248763440011bd0e286c6880323761c50d8d100054f420a1b1a2000a9d84143634400159d04286c688002b360850d8d102556b408a1b1a204a8de87c8363440011bb0f906c68800297a1720d8d100052ec2e41b1a2000ccf72c836344001c9aa5906c68800333dc920d8d1000726a9241b1a20008de8708363440191bb0e106c68800297a1420d8d100052ec2841b1a2000a9e84083634400153b08106c68812ab5a0420d8d100056ac0841b1a20008df835c963440011ef02b92c6880031bdc95258d1000e36392a4b1a20018dc874c9634400199ee4992c688003935493258d100046ec14ec31a20008dd87994634400159d05328c688002b360a6518d100046fc3aca31a20008dd8799063440011bf0eb20c68800297e156418d100052e42ac831a2000acf82590634400159904b20c68800333a197218d1000666432e431a2000d4e855c86344001a9b0ab90c68800333d957218d100066732ae431a2000ccd655c86344001998cab90c68800333d917218d1000667322e431a2000ccd645c86344001998c8b90c68800371a057218d10006e2c0ae431a200eccf615c86344001b9500b90c688003726017218d1008e67b02e431a2000dcb105c86344001b9020b90c68800237e1f6218d1000666b96c431a20008dd8798863440014bd0b310c688002976166218d1000666b94c431a20008df87588634400199ae4b10c688002b5e056218d100146f438c431a20008dd8718863440014bd0a310c688002976146218d100054f420c431a2000a9d84188634400199ae4310c688003179db5218d10006a6b96a431a2000c5e765486344001a9ae4a90c68800393d895218d1000726312a431a2000ad6868846344001b8ae5108c688003d154a2118d100056a4324231a2000dc5724846
  | 6 => 0x43ec16eab222000c5f75dcd64440018b8ebb9ac8880023760b73591100062fba8e6b222000c5c751cd64440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440018df0bb92c8880031b217725911000667c1ee4b222000ccc83dc964440010ff0ab92c88800e1f21572591100046fc1ae4b2220028dc835c964440018deea392c8880031b1d4725911000667b98e4b222000ccc731c964440010fd0fa92c88800e1f21f52591100062fb9ea4b2220d5c5c73d4964440018dee5a92c8880071b1cb52591100043f43aa4b22200087c8754964440018bee6a92c888353171cd525911000637b92a4b222001c6c725496444003958e5a12c8880062f21d425911000e5639284b222000e2d5250964440011bd0f992c88800a3721f32591100062fbae64b2220d7c5c75cc9644400199ee5992c888007331cb32591100046f43a64b2220008dc874c964440018beea992c88835b171d5325911000667b9264b222001ccc724c96444001c9aa4992c888003a3d09325911000e7239442b222000e655288564440031e90e90ac888003b14c9215911000e7439440b2220018f8874816444001cd2a4902c888003aa50920591100076499240b222000ee121481644400117f0eb20c88800237e0d76951100146e41aed2a220008ef825da54440031d904bb4a8880028f613659511002c7a432e32a22000c77655c654440019a8c6b8ca88800a37a0f76551100046ec1eecaa220008df835d954440051b906bb2a8880023be09765511000c76412ecaa2200087f855d363440070f90aba6c6880023be0974d8d1000c76412e9b1a2000c6f7254b63440038d8e4a96c68800297a1632d8d100052ec2c65b1a2000e4d528cb63440031bf0e996c688007339c932d8d1000666b9265b1a2000e4d524cb634400159d0532ec688002b360a65d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d1000666b96c5b1a2000a5e8598b63440014bb0b316c68800333dca62d8d1000667b92c5b1a200c8dd8718b63440014bd0a316c6880029761462d8d100054f420c5b1a2000a9d8418b634400199ae4316c688357179db52d8d106a62f3b2a5b1a2000d4f7254b6344001c9ec4a96c6880039318952d8d10256e9b86e3b1a2000f45528876344001b8ee490ec68812ab621920d8d10006e5b9241b1a2000f49524836344001f8242906c688002b3a0a75d8d1000566c14ebb1a204aad6811d763440015ab023aec68800297e1574d8d100052e42ae9b1a2000acf825d3634400159904ba6c688002b560474d8d100046f438a9b1a20008dd87153634400159d042a6c688002b360854d8d102556b408a9b1a2000ad58115363440015b5002a6c688002b660054d8d100052f42ce5b1a2000a5d859cb634400199ee5396c68
  | 7 => 0xdd83dd954c400b1ed03bb2a98800e1fa177458f100043ec2ee8b1e2000c6f7254963c40038d8e4a92c7880123721d3258f1000667b9264b1e2000e4d524c963c40071bb07bb2a7880163da077654f100243e43acaa9e2004cb67159343c40151bb07bb287880163da077650f100245e43ac8a1e2000e345459151c405f5ad07bb283883638d151655071017c7ac36e6a0e2004ab686d0d41c40cdd28c6a1a83880025d617744c7100061e3aac8a062063d347550540c40030ff0ea96cb080071b9c952d961000636b92a5b2c2001cce724cb658400199ae4996cb080039354932d96100045fc22e4b2c200a8bc845c9658400b0f90ea92cb080031bdc9525961000e6739264b2c2000ccd724c96584001c9aa4992cb080071b9c952d921000636b92a5b242001cce724cb648400199ae4996c9080039354932d921000734a9241b242000ec93248364840070fd0fbaac9080021f60b755921000536c10eab24200087f855c964840070f90ab92c9080021fa1f525921001c3e43ea4b24200087e8754964840010f90ea92c9080071b9c9525921000636b92a4b2420058bc875096484001c5aa4a12c90800317dd732592106be2e3ae64b242000c5f754c964841ad8b8ea992c90800333dc9325921000e6639264b242000e4d524c96484001d1e84992c9080039a549205921000754a1240b242000ec932481648400147b09b2ca90800e8f21564952100043fc2aecaa4200587c87595548400b1790eb22a9080021fe1574d8e1001c3e42ae9b1c2001c6e7254b63840018dae4a96c70800637e1d32d8e1000e6739265b1c2000ccd724cb6384001c9aa4996c70812ab520532d8e1000e37392a4b1c2000c6d72549638400b1b90e992c70800333dc93258e1000726a9264b1c200587c87595538400b1b90eb1aa70802a3de1971d0e100565b322e3a1c2000cb5645c743840010ff0abb2870800e1f2157650e1002c5e43ac8a1c20058dc8758d438406d4790ab26830802b2799173d06100064eb22e7a0c2030a3c85591418400b3b10e98a6108033b4585314c2100053bc2ac9884200187f8754b65440018dae4a96ca88007339c932d951000666b9265b2a2000e4d524cb65440051bd0fb9aca880023760b73595100062fa96e6b2a2000acd821cd654400117f08b92ca8802a2f21172595100046fc1ae4b2a20028dc835c965440030f90ea92ca8800317dcd52595106a62e39aa4b2a2000c6f7254965440038d8e4a92ca8800237a1f32595100146e43e64b2a20008de874c965440011b90e992ca88007339c9325951000666b9264b2a2000e4d524c965440018dee4a96c8880071b1c952d911000e6739265b222000ccd724cb6444001c9aa4996c8880039954a21d91100076299243b222000e69524836444001d9264906c888003b848520d91100
  | 8 => 0xa510ac3180163d21d21586300076299242b0c6004cb6615d2518c00196ae8b0ca3180163d21d61546301b51e42ac9a0c600ac9e645cf418c00193ac8b9e83180131d98575906300063abaac320c600087f855d9418c0070f90abb283180023be09765063000c76412eca0c6030a3c85591418c1b3d2862b22831800297e15648c6302cc6fc32e118c600187f8754b654c0038dce4a96ca980031b5c952d953000667b9265b2a6000e4d524cb654c0051b906b8eca980022fe1172595300545e422e4b2a60008f7815c9654c0091e902b92ca980061f21d525953000637b92a4b2a60018dc874c9654c00199ee4992ca9800393549325953000e37392a5b226000c6d7254b644c00399ce4996c898003335c932d913000726a9265b22600387e87dd5644c0010fb05baac89800317ccb755913000536c10eab22600087f855c9644c0070f90ab92c8980023de0572591300247a40ae4b22600087e87d49644c0070f90fa92c8980021fa1d52591300043e43aa4b226001c6e72549644c0018dae4a92c8980063721d32591300062fbaa64b2260d6c5c754c9644c00199ee4992c898007331c9325913000726a9264b2260008bf87590644c00147b09b2ca8980163721973951300062fb2ae72a2600087f855d9544c0074bd0bb22a69800e3721d6454d30014af43ca8a9a6003c5c76951534c0011bd0db8aa698002f46047054d3002c6e432eaa1a600a8dc87595434c0011bd0db8a8698002f46047050d300043fc2ae9b0a600387c855d3614c0038dce4a96c2980031b5c952d853000667b9265b0a6000e4d524cb614c001d8a6590ec298002ad61021d85300056ac1843b0a6000e6552087614c0015e30010ec29812b33d8d72185300047bc3ac230a60048f8865c2514c0031dd043b2a2980023b60876545300243e43acaa8a60048be849db414c0051b9073b682980da8f21564d05300064f3b287a0a60048f4815da414c0091f10cb8482980122f21d64505301851e42ac8a0a6066e946150d414c0091f10cb80829801637219754c530004aec2ee898a60058dc865d1314c00b2b90ea9aa09801697219535413002dac402a6a826005a9c8650f404c00b3390ea1a8098016a7219435013002dcc40286a02600095f855d2304c0051b90cb8c609812b35185718c13002ee9082e3182600487c8754965c40018dee4a92cb880071b1c9525971000e6739264b2e2000ccd724c965c4001c9aa4992cb880122fa1f54593100054ec18a8b262000aad8215164c400956d022a2c988002ae600545931000637b92a4b262001c6c7254964c4193ccc42a92c9880122f21d425931000e5639284b262000e2d5250964c400199ee4992c988007331c9325931000726a9264b262000e8f424c964c4001d8a6490ac9880121fe1d65953100146f41eecaa620008
  | 9 => 0x32584400053b42864b088000a75850c961101b75ad06192c2200029da1720584400053ac2e40b088000ad683c8161100015ab07902c2200039954b20584400076299640b088000e65524816110001d8a64902c2200122f61176944400561f3a2cb2888030c3e655d2511000187acaba4a2200032798d749444000657312e92888004cb6615d2511001593ce8b1ca220003275d16394440056573a2c52888000cad7458a511001596ce8b0ca2200032d5d1619444002c3e42eeca8880058f487585511000b1b907bb262200163d21d614c4400061fc2eeca008000c3c85dd9401000187ea5bb280200030f54b76500400064f996eca008000c9d32dd9401000b974a1bb280200030fddb75500400061fbb0eaa008000b2d821d5401000bc74a0b2a80200028fa1d65500400051e43acaa008000a3f82595401000147b04b2a802000387cc965500400070e992caa008005e3a80595401000b87ee0b2a802002b8edc1655004002f1d102caa008000e39205954010001c3eeab1a8020003871d563500400054fc12c6a008000a9d8258d4010001c3ea4b1a80200038754963500400574db82c6a008005e9a5058d401000bd3440b1a8020003a648163500400071742ac4a008000e2d855894010001c5eeab1280200038b1d562500400074741ac4a008000e8d83589401000bd5500b12802036baa601625004002e57b82c4a00800aeab70589401000bd54a0b1280200038ddd561500400071a3aac2a008000e37525854010001c6aa4b0a8020003a5cc961500400074a992c2a00800aeb370585401000bd64a0b0a8020017ac881615004000758902c2a008000cbb765414010001c72caa828020003a658d505004000754b12a0a008000eb16154140100030ff0ea96cb180071b9c952d963000636b92a5b2c60018df874cb658c00399ce4996cb18003335c932d963000726a9265b2c60008bf845c9658c01517908b92cb180161f21d525963000637b92a4b2c6001cce724c9658c00199ae4992cb1800393549325963000e37392a5b246000c6d7254b648c0031bf0e996c918007339c932d923000666b9265b246000e4d524cb648c0070fd0fbaac9180021f60b75592300062f996eab246000c5c31dd5648c0018be61baac9180029b60875592300043fc2ae4b24600387c855c9648c0010fd0fa92c91800e1f21f52592300043f43aa4b24600087c87549648c0038dce4a92c9180031b5c9525923002c5e43a84b246000e2d52509648c0018beea992c91835b171d5325923000667b9264b246001ccc724c9648c001c9aa4992c918003a3d0932592300051ec26cb2a46003a3c85592548c0010ff0abb2a9180161f21d655523002c5e43ac8aa46000c6f72549618c0038d8e4a92c318007339c9325863000666b9264b0c6000e4d524c9618c001cca
  | 10 => 0xb10800aaae840c5621000155b0818ac420016baa00315884000574c0062b108000ae68214e61100015cb0429cc2203269d61652984400056b41ca53088000ad58394a6110001ccf04a94c22032799dc9529844064f32392a530880cbe664254a6110197cca84a94c2203229da1452984400056b418a53088000ad58314a6110001caea5994c2200039554b32984400053b42c653088000a75858ca611018d5ab07194c2200039954a329844000732a92653088000ec7824ca611018dd8ce4994c22031bb15c932984400072ba92653088000ec6524ca6110001caaa4994c220003b1549329844000722a926530880caec7424ca6110195d8884994c2200029da1432984400053ac286530880c5ad6830ca61100014ed0b904c2200029d61720984400056b41e413088000ad583c826110001ccaa5904c220003b14cb209844000732a92413088000ec53248261100018dee4a92c2200071b1c9525844000e6739264b088000ccd724c96110001c9aa4992c220002b5a0f51584400056ac1ea2b088000ae682d4561100015cb05a8ac2200029da1431584400053ac2862b08800aab6840c561100015cd0418ac220002b9608315844002d7940062b0880058f687c8561100014ed0b90ac2200029d61721584400056b41e42b088000ad583c856110001d8a6590ac2200039954a215844002c7a43a42b088000ec53248561100014ed0a10ac2200029d61421584400555b42042b088000ad68308561100015ab0610ac22000399548215844002d7940042b08800aab684dd561100015ad073aac220002b560e755844000573414eab088000ae5829d561100014ed0a39ac2200029d61473584400555b420e6b088000ab5841cd61100015cd0439ac220002b9608735844002d79400e6b088000af1801cd61100015cd0429ac220002b960853584400053b42ce4b088000a75859c961100015ad07392c220002b560e72584400053b428e4b088000a75851c9611001556d08392c220002ad61072584400056b418e4b088000ad5831c9611000b5e500392c220002bc60072584406e71ba06a4b0880cba758594961100015ad07292c220002b560e52584400055bc22a4b08800aab4845496110001c6f08a92c22032f8d211525844000733c12a4b088000e67725496110001cc8e4a92c22032f99909525844065f32a12a4b0880cbe374054961101b94ed0a292c220002b5a0c52584400056ac18a4b088000e5752cc96110001caaa5992c22036fa5d0332584400053b42c64b088000a75858c961101955ab07192c2200039954a325844000732a9264b088000ec7824c96110001d8ce4992c220003b15c932584400072ba9264b088000ec6524c96110001caaa4992c220003b1549325844000722a9264b0880caec7424c96110195d8884992c22032ba5d01
  | 11 => 0x1019599e84b92c62032b331097258c406564fa02e4b1880db8de871c963100014bd0a392c620002976147258c400062fb96a4b188000c5d72d4963101b9c3e81a92c62000237a1e5258c400046ec3ca4b1880cba5d85949631000199ae5292c620002a7e115258c400554e422a4b188000ccd725496310001c3f08a92c62032f872115258c4000727c12a4b188000c5f725496310001c9ce4a92c620003175c95258c4000726b92a4b188000c4d725496310197c9c84a92c62032f935095258c4065f0fa02a4b1880008de8714963100011bb0e292c62037297a145258c400052f428e2b188000a5d851c5631001553d0838ac620062a76107158c4000567410e2b188000acd821c5631000b5b50038ac620062b66007158c400046f43ea2b1880008dd87d45631000159d05a8ac620002b360b5158c400046f43e42b1880008dd87c8563100014bd0b90ac620002976172158c4000666b9642b188000e4d52885631000199ae490ac62000237a1c2158c400046ec3842b188000a5e8508563100014bb0a10ac62002aa7a102158c400054ec2042b188000e4d52085631000b5b50010ac620002b66002158c400c46f43e40b1880008dd87c8163100014bd0b902c620002976172058c4000726a9640b188000e4d52481631000b0f90eb2aa6200163721d6354c400056741eeab108000acd83dd562101974db0f3aac4203738bd0275588406e735204eab1080dce69409d562101bb55f08baac42002aab211755884000637c3aeab108000e2f845d56210197c5908baac42032f1bdd1755884065e36ba2eab108000c6f705d562100018dae0baac42032f8bd01755884065f35202eab1080cbe69405d562101b94dd0a3aac420002b3a0c755884000566c18eab108000a6e85dcd62100014db0bb9ac4200031b5d7735884065566c3ce6b108000e4e759cd6210001c9aeb39ac42036fa3d0273588406df65204e6b1080dbec9409cd62100018daeab9ac42000333e1d735884000667baae6b108000e4e755cd621000199aeab9ac420003935d5735884000626baae6b1080cacce745cd6210195998e8b9ac42000333dc1735884000666b82e6b1080cae8f405cd6210195d9480b9ac42032bb2501735884000537428e6b108000a6d851cd62101b759d0639ac4200023ba1c535884000476c38a6b108000a6e85dc562100014db0bb8ac420002b3a0f715884000566c1ee2b108000ccd73dc562100018daeb38ac420003335cd715884000537428e2b108000a6d851c562100018daea38ac42002aaba1071588400bd56c20e2b108000ace831c5621000159b0638ac420016baa0071588400bd74c00e2b1080008ee87d4562100011db0fa8ac420002b3a0f515884000566c1ea2b1080008ee870c562100011db0e18ac4200029ba14315884000536c2862
  | 12 => 0xf8e1d954541400059dc1aa8a8280e0b3b8255150501c167304aa2a0a037f4edc954541406fe9cb92a8a8280def1b3255150501bde3264aa2a0a0002cee05545414001e3c3b2a6a828000b3985d0d505000176303a1aa0a0002ce61543541400078ca9a86a828003c78765455050015970eda0aa0a0002ce6174154140005ccc1e82a82800acb87650550500016730aa0aa0a0003cc545415414002e9d282eb202807bc3e76d9640500f7c76c1b2c80a000f0f9d8659014000596c10cb202800099f835c6405000ba76eaa8480a002a2f211725944000637a92e4b28800587e8794965100014bd07292ca200029760e525944002c3e43aa4b28800aa3c8454965100018dee4a92ca20007339c9325944000666b9264b288000e4e524c96510001c9aa4992ca2000a37a0f71594400046ec1ee2b2880018ee82dc565100011db05b8aca200029ba08735944000536c10e6b2880dcc3f40dc965101b98f481b92ca203731e503725944065c3ec3ce4b288000a5e839c965100014bb07392ca200028fe1172594400551e422e4b288000c3f845c9651019787908b92ca200031be09725944065e1fa02e4b2880cbc7a405c965101978f280b92ca203721fa1c72594400052f418e4b288000a5d831c965100018bee5992ca20003175cb32594406df0fa0664b2880dbe5a40cc965101b7cb281992ca200021fa1e32594400043ec3c64b2880caa5d838c965100018dae5192ca200031b5c9325944000727c1264b288000c5f724c96510001c9ce4992ca20003175c9325944000726b9264b288000c4d724c96510195c9e84992ca2032b9310932594406570fa0264b2880cae5a404c96510195cb280992ca200021fa1c32594400043ec3864b2880dba5e830c965100014bd07b8aca200029760f715944000537416e2b288000a6d82dc5651001547d0938aca200021fa1c31594400043ec3862b28800aa3e840c5651000147b0818aca200029ba08315944000536c1062b288005a7a800c565100014f30018aca200021fa1f21594400043ec3e42b288000a5e83c8565100014bb0790aca20003934cb215944000636b9442b288000e4d3248565100010fd0e10aca200021f61c21594400551f42042b288000a3d8408565100014bd0610aca200029760c215944000636b9042b288005a7a8008565100014f30010aca200661fa1f20594400043ec3e40b288000a5e83c8165100014bb07902ca20003934cb20594400072699240b288000ccf325c963100038dce4a92c6200031b5c95258c4002c6f43c64b188000a5e858c963100014bb0b192c6200039354a3258c4002c6e43a64b188000ccf724c96310001c9aa4992c620002b3a087558c4000566c10eab1880dbc9f40dc963101951bb0f392c62000297a167258c400052ec2ce4b188000ccf825c963
  | 13 => 0x43f43ecab1a800087e8719563500014db0432ac6a000a1fa1f6554d400061e3b4a8a9a8000b2d821974350001a6ecab8e86a00034d19571d0d400069ba92e3a1a8000d35525c743500fbb2e64b8e86a0003654c971d0d400565bb02e3a1a800adb3605c74350001b6440b8e86a00036c48171d0d403df0e21ecaa1a8000979851c143500013d30438286a00162f2197550d400061e3b6caa1a8000e1c63d954350001878ec32a86a0002cb6086550d400059cc28e0a1a8000ba9821c143500014db0432ec2a000b279cd43d854000e37392a5b0a8000c6d7254b6150001c5aa4a16c2a000333dc932d854000e6639265b0a8000e4d524cb6150001d1e84996c2a00039a54920d854000754a1241b0a8000ec93248361500014db0432cc2a00021fa1f65585400062e39ecab0a8000c6c72d9561500010fd0e32ac2a0003171cc655854000536c10cab0a8000c6c7219561500018becbb9ac2a000317197735854000637b2ee4b0a8000c6c65dc961500014db04328c2a00023de1d61185400245e424ed28a80048f6819da51500f787ce9b2ca2a00030fd9574945401861e32ae928a8000c3c76951515006d1790cbae82a02268fa1b65d054000596c10cba0a8000d1f655cf4150001a38cab9e82a000267e0973d0540004cec12e7a0a8000d1f525cf4150001a3aa4b9e82a002b27d8173d0540056cdb02e7a0a8000d9a205cf4150001b3240b9e82a00021f21975905400043ec3ecb20a8000979851c141500013d30438282a00c30f197755054002c5e432eaa0a8030a3e86d95415000165b0432a82a002a6d60773505400255b40ec6a0a80d9e9431d8d4150001c68cbb0a82a0002ada1a51505401871a32ca2a0a8030e346554541500016730a38282a0002ea60870505400043fc2aed18a800387c855da31500011df04bb462a00063b209768c5400061e32ae918a800a99f8750e31500055390ca1c62a000e1fa17764c5400043ec2eec98a80058bc865d1315000b37100ba262a01ee9e603659414044e1f3b4a92828003a7a86d9650500018f4edb2ca0a01eece21365941400059d434a9282807be3a869525050113a74ed2a4a0a008b8e9da54941403dd9dc14a928280e3b398295250501c5a76e52a4a0a038b4e5ca549414070f8d994a928280e1f1932952505000176303a1ca0a0002cee1543941401b71c32e832828000b9983d0650500016770aa0ca0a00c38e19541941403de1e3a6caa82800593c87551505000b4790caa2a0a0016ce201545414001e3c3b6eaa82807bc7876d9550500f7a76ea3a2a0a0002e660c7454140005d4c10e8a828000bb1811d150500152f10eaa2a0a002b1e1d954541400569c3a2a8a82800ad3887551505003b6710caa2a0a000f8e219545414001f1dbb2a8a82800ad3a765515050015a70ecaa2a0a0
  | 14 => 0xf72ccb65500018bae5996caa00021fa1e32d95400043ec3c65b2a8000c6f728cb65500018dee4996caa000393e0932d95400062fb9265b2a8000e4f724cb655000189ee4996caa0003175c932d95400072639265b2a80e4e4f424cb65501c9c9884996caa00021fa1c32d95400043ec3865b2a8000a5f835c765500014b906b8ecaa00029be0971d954000536412e3b2a8000a3d841c765500010fd0e18ecaa00021f61c31d95403dd1f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d95400053d40063b2a8000a79800c765500010fd0f90ecaa00021f61f21d95400052f41e43b2a8000a5d83c876550001c9a6590ecaa00031bdca21d95400072699243b2a800087e8708765500010fb0e10ecaa01ee8fa1021d95400051ec2043b2a8000a5e8308765500014bb0610ecaa00031bdc821d95400053d40043b2a8000a798008765500010fd0e186caa00761f61c30d95403dd1f42061b2a8000a6e820c365500014db04186caa00029da0430d95400053ac0861b2a807b87e87c8365500010fb0f906caa000297a0f20d95400052ec1e41b2a8000c6f72c836550001c9a65906caa00031bdc920d95400072699241b2a800087e87083655003b0fb0e106caa01ee8fa1020d95400051ec2041b2a8000a5e8308365500014bb06106caa00029da0420d95400053ac0841b2a800087f855c9655000117f08b92caa00061f21d525954000637b92a4b2a8000ccf724c96550003998e4992caa00039354932595400043ec14ec32a8000a6e8298c65500014db05318caa00031ba19721954000636432e432a8000d2e845c86550001a5b08b90caa007f1bd917219540006a741ae432a8000d4d835c865500018dcc6b90caa00031b18d7219540006b5402e432a8000d69805c865500458dec0b90caa00035ad017219540006b4202e432a800087f87d8865500018dae5b10caa00021f61e62195400052f41cc432a8000a5d8398865500018dae5310caa00021fe1d62195400051fc22c432a8000c6d7258865500070fd0e310caa00021f61c62195400052f418c432a8000a5d8318865500018dae4310caa00029da0462195400053ac08c432a8000a3e86d086550001a5ae5a10caa00028f219421954000696b928432a8000c5e76cc86550001a9ae5990caa0003179d93219540006a6b926432a8000e4f624c86550001c98c4990caa0003c3d093219540006b4b944032a8089a78864806550001ad2e4900caa0003ca5092019540007a49924032a8003a3e86d96545000187cedb2ca8a00c30f19571951400063db28e0aa280009e9821c1545003b878edb2aa8a00026760f715514044e9dba8e0aa28000ba9821c154500014db0432ec6a00071b9c952d8d4000636b92a5b1a80018df874cb635000199ae4996c6a00039354932d8d4000
  | 15 => 0x9bb2a3a002a3d21d61547401851f42eeca0e80308bd86dd541d01cbd2862b1a83a002aada1a51507404971a32aa2a0e800387e85dd931d00010fb0bbb263a00162fa13764c74000c3fc3aa5b2c807ba3c8454b65900038dce4a96cb200031b5c952d964000e6739265b2c8000ccd724cb6590001c9aa4996cb2000237e0d71d96400146e41ae3b2c800587c87549659000147f08a92cb200031bdc9525964000e6739264b2c8000ccd724c96590001c9aa4992cb200023de057258e400247a40ae4b1c8001c6e7254963900018dae4a92c7200163721d3258e4000667b9264b1c8000e4d524c9639000b0f90eb2aa7200163721d6354e400046ec16e6b0c8000acd821cd61900011bf06b92c32000a3720d72586400062fb9ea4b0c80d5c5c73d4961900018bee6a92c320353171cd525864000637b92a4b0c8001c6c7254961900011bd0f992c32000a3721f32586400046f43a64b0c80008dc874c9619000399ce4992c320003335c9325864000726a9264b0c8000e6552885619000b1e90e90ac320003b14c9215864000734a9240b0c8000ec9324816190001dc242902c3200132d98574946400065aba2c328c80008df835d951900051b906bb2a3200163d21d61546400263b30aeb20c8000c757558641900655a906b0c83200beb520d61506400156a41ac318c80058f487585319000b2f10eaa2a1200778e59154542400054fc1ac3a048000a3d8494f655000147b09296caa000297a0e52d95400052ec1ca5b2a800187f8754b65500038dce4a96caa00031b5c952d954000667b9265b2a8001ccc724cb6550001c9ca4996caa00039354932d95400046fc1ae3b2a80028dc835c765500011df04b8ecaa00063b20971d95403de9db86e9b2a8000a6e8298f65500014db0531ecaa00031b5cb62d95400052f41cc5b2a8000a5d8398b65500018dee5316caa00031bdc962d95400ec3ec38c5b2a8000a5e8318b65500014bb06316caa00031b5c862d95400053b408c5b2a8000a758118b6550001a5ee4a16caa00038b18942d95406be2f3b665b2a80d6c5e764cb6550001a9ee4996caa000393d8932d95400072631265b2a8000f0f424cb65500f74f10c906caa00035adc920d954000794a1241b2a8000f493248365500f7878e8ba6caa00029ba0a73d954000536c14e7b2a807ba3e841cf655000147b0839ecaa00021f61e43d95400053741487b2a8000a6d8290f65500014bd07396caa00029760e72d954000637b94e5b2a8000c6f825cb65500f747d08396caa00028f61072d95400052f418e5b2a8000a5d831cb65500014ed02396caa00029d60472d95400053d400e5b2a807ba79801cb65500010fd0f216caa00021f61e42d95400052f41c85b2a8000a5d8390b65500018dee5216caa00031bdc942d95403df1621285b2a8000c5
  | 16 => 0x952500063db12e12a4a000c79625c25494001ab664b84a928003564c970952500047bc0ae4b1ca0048f4815c963940038dce4a92c7280031b5c95258e5002c6e43a64b1ca000ccf724c96394001c9aa4992c72802b2d99171d0e500065ab22e3a1ca0058bc87591439400187eeab22872800a37a1f73586500062f2a6e6b0ca000c5c54dcd61940011bb05b9ac32800317d4b73586500062fa86e6b0ca000acd821cd61940011bf06b92c32800a3720d72586500062fb9aa4b0ca0d4c5c7354961940018dee4a92c3280071b1c952586500046f43e64b0ca0028dc87cc961940011bd0e992c3280023721d325865000e6739264b0ca000ccd724c96194001c9aa4992c3280039954a215865002c7a43a42b0ca000ec532485619401593cc8b9e83280032759173d06500263b30aeb20ca000c757558641940655a906b0c832800237e0d76506500146e41aeca0ca0008ef825d941940031d904bb283280030fdd564506506971a2a2c2a0ca02fad48358541940055a906b0c63280163d21d614c65000637b92a5b22a000a3d8590b6454001c5aa5216c8a80028f61442d91500055ac0885b22a000ab98010b645400399ce4996c8a8003335c932d915000726a9265b22a000e8c424cb64540011bf06b8ec8a800a3720d71d91500045fc3ac8322a07bc6f655c864540012bb07b8aa8a800a1f21574d8d5000637b92a5b1aa0018df874cb635400399ce4996c6a8003335c932d8d5000726a9265b1aa00087e86dd1535400167308382a6a802a3e21970d0d5000c77410eca1aa0008ed821d9435400b0f90cbaa86a800b179cd53d855000e37392a5b0aa000c6d7254b615400399ce4996c2a8003335c932d855000726a9265b0aa0008f78758461540010fd0dba2a2a8002ce61070545500245e422eda0aa00a8f8865c341540090f90b3b482a80123da0676905500063b3b2a320aa00587c865d54154125c68c8a8a82a80123e219701055001cafc3aa718aa002a5c8654e315400b0f90cbaa62a800e1f21974941503de1e322e9282a005d3a405d250540012bf06b8ca0a80061f21d525974000637b92a4b2e8000ccf724c965d0003998e4992cba00039354932597400146f41ee2b2e80008dd83dc565d000133b07b8aa9a00071b9c95258f4000636b92a4b1e80018dc874c963d000199ee4992c7a0007331c93258f4000726a9264b1e800287d85dd953d000b17d09bb2a7a002a3721d6354f4000637b92a4b0e8001c6c7254961d0003958e4a12c3a00038b549425874000667b9264b0e8001ccc724c961d0001c9aa4992c3a032ba3d0932587400053ac2862b0e800aab6840c561d0001d2a8618ac3a0002b9608315874000578c0062b0e8000e655288561d00031e90e90ac3a0003b14c921587400565b3a2c328e800487d85dd951d000b17d0
  | 17 => 0x46200c6d7254a608c5938ece2a94c118807339c9329823100666b92653046200e4d524ca608c4059ace2994c1188039a549209823100764992413046200c6f72549608c4038d8e4a92c118807339c9325823100666b9264b046200e4d524c9608c4091f10e902c1188039a54920582310076499240b04620a8be84dcb654c40117b09b96ca988061fe1d52d953100636b92a5b2a6200ccf724cb654c401c9aa4996ca98a96b520532d953100c3e43aa4b2a6200c6f72549654c4038d8e4a92ca988063721d325953100667b9264b2a6200e4d524c9654c4cf5a902992ca988029b60a75d913101c3fc3aebb22620087f825d7644c4018be64baec898803178c575d91310062e18aebb226200c5f305d7644c4070fd0bb96c8988021f61772d913101c3fc3ea5b22620087d87d4b644c4010ff0ea96c8988021f61d52d913100637b92a5b226201c6c7254b644c5ad8bcea996c898803175d532d913100e6739265b226200ccd724cb644c401c9aa4996c898a8eb520532d91317365ab8ec93226200c6f72549644c4038d8e4a92c8988063721d325913100667b9264b226201ccc724c9644c401c9aa4992c89899ab520532591310045fc3ac832262008dd83dd9544c4010fb0b3b2a8988da8fa1764d05310064fb22e7a0a6230a3e85d91414c547d2863b2282988031bdc952d813100e36392a5b026200ccf724cb604c401c9aa4996c0988023ee1d60181310043fc12ea3026200c5f325d4604c4018bc62ba8c098803170c5751813102e2f982ea3026205c5d305d4604c40b8ee20ba8c0988171d44175181310064f992e83026200c9e315d0604c40193862ba0c09881727cc1741813102e4e982e83026205cb7105d0604c40b96a20ba0c09880333cc972181310063742ae43026200c6d855c8604c40199d06b90c0988033360d72181310066718ae43026200ccc315c8604c40b99e60b90c098817334c1721813102e73882e43026205cea105c8604c40b9ca20b90c09880e1fe1f52181310043ec3ea430262dcc3e74d48604c40187ae9a90c0988071b9cb521813100636b96a430262d5c7571d48604c4010ff0ea90c0988021f61d521813165e1f3a2a43026200c3d74548604c4038dce4a90c0988031b5c952181316a63ab8aa430262d6c5e754c8604c4018baea990c098b2b279d132181310064eba2643026201cce724c8604c40199ae4990c0988039354932181312cd6a40a643026202cd5714c8604c4038dce4a92c9280031b5c9525925002c5e43a84b24a000a3f855096494001c5aa4a12c92800333dc9325925000e6639264b24a000e4d524c96494001d1e84992c9281ee8fe1d64952500061fc3ac92a4a07bc3f72592549400187ae4b24a92800387cc964952500070e992c92a4a08987f865c254940452f70cb84a9282271ee197
  | 18 => 0x5256690a3a2a2a08125d21d535454101e3a3b2a6a8a8292b348454d515040136d0fa1aa2a0a4acd2174354541004da43a86a8a8230b348550d515045fb28e6a1aa2a0803c554d435454100637b92a5b028201c6c7254b6050403958e4a16c0a08038b54942d814100667b9265b028201ccc724cb6050401c9aa4996c0a0803a3d0932d814100732a9443b028200ec532487605040b9d4c0b90c0a08023ee1d601814100674b92c0302820087f825d4605040b87e80ba8c0a08171e901751814102e1ea02ea3028205c77105d4605040b8ea20ba8c0a080237e09731814102e4fa02e63028205c9d405cc605040b9ae20b98c0a081736841731814102e6a882e63028200c6e855c860504018db0ab90c0a080333a0d721814100666c1ae43028205caf405c8605040b9d480b90c0a08172b501721814102e73882e43028205cea105c8605040b9ca20b90c0a080e1fe1f52181410043ec3ea430282d5c5e73d4860504018bae7a90c0a08071b9cb521814100636b96a4302820087f8754860504010fb0ea90c0a0b53179cd52181410062eb9aa43028201c6e7254860504018dae4a90c0a080a37e1f32181410046ec3e6430282d7c5e75cc860504018baeb990c0a0807339cb321814100666b966430282008df874c860504011bb0e990c0a0b5b179d532181410062ebaa643028201cce724c8605040199ae4990c0a08039354932181410243e43aa4b288200c6f72549651040399ce4992ca20803335c9325944100726a9264b288201c6e7254963104018dae4a92c6208123721d3258c4100667b9264b188200e4d524c963104090f90eb2aa6208123721d6354c4100e37392a53008200c6d7254a601040399ce4994c020803335c9329804100726a92653008200e69524826010401d9264904c0208071b9c9525804100636b92a4b008201cce724c9601040199ae4992c0208039354932580410247c43a40b008200e69524816010401d9264902c0208121f21d525963100637b92a4b2c6201c6c72549658c40399ce4992cb18803335c9325963100726a9264b2c62048be87d51648c40153b07aa2c918802a760c545923100556c10a8b246204ab681151648c401573002a2c9188031bdc9525923100e36392a4b2462048bc87509648c403958e4a12c9188038b549425923100667b9264b246201ccc724c9648c401c9aa4992c918803a3d0932592310243fc3acb2a4620a8df865ce548c4018bacab9ca91880e972156454e310070e2a2c8a9c620295e87951538c4014bb0d2a2a71880f17dda5454e310046ec30e0a9c620099d841c1538c40139b04382a718802756047054e3117d6ac36e2a1c62008dd861c1438c4012bb0a3828718802736087050e31004eac08e0a1c620087f855d2608c4070f90aba4c118b231d9c7529823100e37392a53
  | 19 => 0x21fa1e32596410043ec3c64b2c82c6a5d838c965904018dae5192cb208031b5c932596410053bc0a64b2c8204a74814c96590401c9f04992cb2080317dc932596410072739264b2c8200c5d724c96590401c9ae4992cb20803135c9325964174f27a1264b2c82e9e4c424c96590401caf02992cb20b1b9520532596416372790a64b2c82c6e4d214c9659058dcae20992cb208021fa1c32596410043ec3864b2c82c5a5e830c965904094ed03382cb20a4a8fa1070596410051ec20e0b2c8200a5e831c165904014bb06382cb208029ba08705964100536c10e0b2c8204a76811c165904674eb02382cb208021fa1c30596410043ec3860b2c8292a3e840c1659040147b08182cb208029ba08305964100536c1060b2c8204a76810c165904014eb02182cb208021fa1f20596410043ec3e40b2c8200a5e83c8165904014bb07902cb208031b5cb20596410072699640b2c8204a768188165904014eb03102cb208031b5c920596410072699240b2c820087e8708165904010fb0e102cb20a4a8fa1020596410051ec2040b2c8200a5e8308165904014bb06102cb208129da0420596410053ac0840b2c8200c7565dc554904653ad07b8aa9208123d2057258e416463a38ea4b1c8200c6f7254963904038d8e4a92c720b271d1c55258e410246e43a64b1c8200ccf724c96390401c9aa4992c720812b52053258e416366a38a64b1c82038dd83dd953904091e902bb2a7208121f21d6554e410063ab2ee2a9c820aad48158d43904092e90ea9aa3208029de19535464100e37392a53048200c6d7254a609040399ce4994c120803335c9329824100726a92653048200e69524826090401d9264904c1208031bdc9525824100e36392a4b0482c9e6621549609040399ce4992c120803335c9325824100726a9264b048203c76755456090401d8a6490ac1208123e21d205824100734a9240b048200ec9324816090401dc242902c1208122f61372d954100c3fc3aa5b2a82c9c3d7454b65504018dae4a96caa0b17275d332d95416364eba265b2a8200ccf724cb6550403998e4996caa08039354932d954100c3e43aa4b2a8292a3c8454965504018dee4a92caa08071b1c9525954100667b9264b2a8201ccc724c96550401c9aa4992caa0b0b4d153715514117ceb41ee2aa2820a8f581dcb63505b98eae3a96c6a08031bdc952d8d4100e36392a5b1a82cbc757154b63504031bf0e996c6a0803335c932d8d4100726a9265b1a822fcd5714cb63504031dd05bb2a6a08023b60b7654d410143f43ecaa9a82e8d9431dd153504071bd0fb1aa6a082a3da1b7154d4173e9a2a6e2a9a82049b4819db43504153390ea9a86a080b271d95350d41335ca40aa6a1a8266b94831c54350409369093b4a2a08026d61f4394541004dbc3a8728a8266d947350e515
  | 20 => 0x2f428e4b1e8200a5d851c963d040199ae4392c7a080317dcb5258f410062eb96a4b1e82dce1f40d4963d04011bd0f292c7a08023761e5258f4165d2ec2ca4b1e8200ccd7294963d040153f08a92c7a082aa72115258f4100666b92a4b1e8200e1f8454963d0597c3908a92c7a080393e095258f410062fb92a4b1e8200e4e7254963d04018bae4a92c7a0803935c95258f4100626b92a4b1e82cbe4e4254963d0597c9a84a92c7a0bab938855258f417572610aa4b1e82cbe1f4054963d04011bd0e292c7a08023761c5258f416e52f428a4b1e82008de87d4563d040159d05a8ac7a0802b360b5158f410046f43e42b1e82008dd87c8563d04014bd0b90ac7a0802976172158f4100666b9642b1e8200ccd7248563d041553d09382c7a080297a147058f410052ec28e0b1e820aa9e841c163d046b53b08382c7a0802b3a087058f4100566c10e0b1e8266ad6811c163d04015ab02382c7a080237a1c5058f410046ec38a0b1e820aa9e8414163d040153b08282c7a0802b3a085058f4100566c10a0b1e8266ad68114163d04015ab02282c7a080237a1f2058f410046ec3e40b1e8200a5e85c8163d04014bb0b902c7a0803335cb2058f4100726a9640b1e820aa9e8488163d040153b09102c7a0803335c92058f4100726a9240b1e82008de8708163d04011bb0e102c7a080297a142058f410052ec2840b1e820aa9e8408163d040153b08102c7a099ab5a042058f410056ac0840b1e820287d85dd953d040917908bb2a7a082a3721d6354f410064fba2c6a9e820a99c8754d43d040153f0ca9a87a08128f211655474100e37392a53068200c6d7254a60d040399ce4994c1a0803335c9329834100726a92653068200e695248260d0401d9264904c1a080b279cd435834100e37392a4b068200c6d7254960d0401c5aa4a12c1a080333dc9325834100e6639264b068200e4d524c960d0595d1e84992c1a08063e21d205834100734a9240b068200ea94248160d0401d9264902c1a08121fa1e52596410052f41ca4b2c8200a5d8394965904090f90ea92cb208031bdc9525964100e36392a4b2c8201cce724c9659040199ae4992cb2080393949325964100726a9264b2c8204a74815cd65904014dd0439acb208029b60873596410043f43c86b2c8200a6e8290d65904014db0521acb20b231dc43725964164c3ec3ce4b2c8200a5e839c965904014bb07392cb208129da0672596410053ac0ce4b2c8200c6f825c965905938dc42b92cb20b271b085725964164e3b882e4b2c82c887e871c965904014bd06392cb208029760c725964100636b90e4b2c820087e8790965904010fb0f212cb2080297a0e42596410052ec1c84b2c8200c6d7290965904018dae4a12cb20a4b8b10942596410062fb9664b2c8200c5d72cc9659058bcae21992cb208
  | 21 => 0x724c96394401c9aa4992c728812b52053258e510265b38ac9a1ca20acb6645c7439440196ac8b8e872882a3760f7650e510245e43ac8a1ca201c6e7254a60944018dae4a94c12880f1d9c5529825162e6b38e65304a201cce724ca609440199ae4994c1288039354932982516366b38a65304a200e69524826094401d9264904c1288031b5c9525825100e6739264b04a200ccd724c96094401c9aa4992c1288123e21d205825100734a9240b04a200ec93248160944018dee4a96c8a88071b1c952d915100e6739265b22a200ccd724cb6454401c9aa4996c8a88022fe1d64191511849ec3ec92a2a2038f581dcb63544018dee4a96c6a88071b1c952d8d5100c6fc3a65b1aa201cce724cb635440199ae4996c6a88039354932d8d510243ec2ceda1aa20a8f4865c743544072b90ea9a86a880a972195350d510062e3b2a6a1aa200c6f7254b60544038d8e4a96c0a8807339c932d815100666b9265b02a200e4d524cb60544011f70eb00c0a88030f15174181510061fc2ae8302a200c3c855d0605440187ea4ba0c0a88170fd41741815102e5d282e8302a205c3d505d06054401972a0ba0c0a88172dc41741815102e5a882e8302a20087d87950605440187ae92a0c0a88031795173181510062e2a2e6302a2008df825cc60544018bea4b98c0a881717d41731815102e2ea82e6302a205cd7105cc605440b9b420b98c0a881735441731815100637a92e4302a200c6e855c860544018db0ab90c0a88031b9517218151006362a2e4302a200cce835c8605440199b06b90c0a88171bd41721815102e36a82e4302a205ce7105c8605440b9d420b90c0a881739441721815165e1f3a2a4302a200c3d7454860545a98bce6a90c0a8803175cd521815100e37392a4302a200c6d7254860544078eae2a90c0a880a37e1f32181510046ec3e64302a2dbc9e74cc8605440193ae9990c0a8807339cb321815100666b9664302a2d7cd571cc860544011bf0e990c0a88023761d32181516564f3a264302a200c9d744c8605440399ce4990c0a8803335c9321815100726a9264302a2d6cd5714c8605440917908b92cba08061f21d52597410551e422a4b2e82c9c3c7454965d04018dee4a92cba0b17271d332597416364e3a264b2e8200ccf724c965d0403998e4992cba080393549325974100e37392a4b1e8200c6d7254963d04151bd0f192c7a080297a163258f410052ec2c64b1e8200e4d528c963d04031b90e992c7a080333dc93258f4100e6639264b1e8200e4d524c963d041553908baac7a0802b3a087558f4100566c10eab1e82dbc9f40dc963d05951bb0f392c7a080297a167258f410052ec2ce4b1e820aa9e849c963d040153b09392c7a080333e097258f4165667a12e4b1e82caccc425c963d059593e80b92c7a0b6e37a1c7258f41005
  | 22 => 0x994c928b1b87d4532992516370ea8a65324a2c6e8f214ca649458dd1a42994c9288da8fa1432992510051ec2865324a20a8be870c2649440117b0e184c9288da8fa1430992510051ec2861324a200aae820c2649440155b04184c928812ada0430992510055ac0861324a236a3e85c82649440147b0b904c928802a7a0f20992510054ec1e41324a200e2d52c826494401d1a65904c9288038b54920992510074699241324a20a8be87082649440117b0e104c9288da8fa1420992510051ec2841324a200a9e83082649440153b06104c928812ada0420992510055ac0841324a200a3d8590d649440155d0521ac928802ab60a435925100636b92a4b24a200a3d85909649440153d07212c928802a760e425925100716a9484b24a2048bc875096494403958e4a12c9288038b54942592510051ec2884b24a200a9e83109649440153b06212c928812ada0442592510055d40084b24a200ab980109649440199ee4992c928807331c9325925100726a9264b24a200e8f424c96494401d1884992c928812ada0773592511851f42ce6b24a200a3d859cd649440155d0539ac928802ab60a73592511851f42ce4b24a200a3d859c9649440153d07392c928802a760e72592511851f428e4b24a200a3d851c9649440153d06392c928802a760c725925100656b90e4b24a204ab6811c9649440156b02392c928802aea0072592510055cc00e4b24a2c8a3f825496494461c5f04a92c9288038b9c9525925100716b92a4b24a2c9e2e215496494593c5842a92c928b278dc4152592517670fa9664b24a200e1d52cc9649458bd2e21992c9288c28fa1632592510051ec2c64b24a200e2d528c96494401c5aa4992c928802ade0532592510255a40a64b24a200e8f824c96494401d1ee4992c928803a31c9325925175f0fa9264b24a2ebe8e524c96494401c3aa4992c928bafa3549325925100706a9264b24a200e97814c9649458dd2902992c928b1ba3c8532592516374690a64b24a2c6e97104c9649446147d0a192c9288028f61432592510255b40ce0b24a200a3f855c1649440147b0a382c928802a7a0c70592510054ec18e0b24a200aae821c1649440155b04382c928812ada0470592510045f43860b24a2008bd870c1649446147d0a182c9288028f61430592510055741060b24a200aad820c1649440956d02182c928802ad60430592511851f42e40b24a200a3d85c81649440153d07902c928802a760f205925100716a9640b24a200e8d32c81649440956d03102c928802ad606205925100716a9240b24a200e8d32481649440117d0e102c9288022f61c20592511851f42840b24a200a3d85081649440153d06102c928802a760c20592510255b40840b24a200ab58108164944091e902b92c7288031b5c95258e510246e43a64b1ca200ccf
  | 23 => 0x587430076299240b0e86008f68708161d0c011eb0e102c3a18029da1420587430053ac2840b0e860aab68408161d0c0156b08102c3a18beb5a0c20587430056ac1840b0e86d5c3e74d4a60d0da987ce8a94c1a18071b9c9529834300636b92a53068602c9e744ca60d0c0399ce4994c1a1803335c9329834300726a92653068600e695248260d0c01d9264904c1a18071b9c9525834300636b92a4b068600ccd724c960d0c01c9aa4992c1a18063e21d205834300734a9240b068600ec93248160d0c0517b09b96caa18061fe1d52d954300e37392a5b2a8600c6d7254b6550c0199ee4996caa1807331c932d954300726a9265b2a860187c875496550d2b47908a92caa18031bdc9525954300c6e43a64b2a8600ccf724c96550c03998e4992caa180393549325954300e37392a5b0a8600c6d7254b6150c0199ee4996c2a1807331c932d854300726a9265b0a86008f7875846150c038dce4a96c0a18031b5c952d814300667b9265b028601ccc724cb6050c01c9aa4996c0a18023ee1d60181430043fc12ea3028600c5f325d46050c018b862ba8c0a18170fd01751814302e3d202ea3028605c3d405d46050c0b8be60ba8c0a1817174c1751814300667992e43028600c6e855c86050c018db0ab90c0a180333a0d721814300666c1ae43028600ccc315c86050c0b95e80b90c0a18173a901721814302e56a02e43028605ccf305c86050c0b99a60b90c0a180e1fe1f52181430043ec3ea430286d5c3d74d486050c038dce5a90c0a18031b5cb52181436463b38ea4302860087f875486050c010fb0ea90c0a1b530f5d1521814300e37392a43028600c6d725486050d938ece2a90c0a1b5b179d532181430062ebaa643028602c9d744c86050c0399ce4990c0a1803335c9321814300726a926430286c6cd6714c86050c019a862b88c0a180335e0d71181430066a41ae23028600c77525c46050c018eaa4b88c0a180335cc971181430066a992e23028605cb7405c46050c0b96a80b88c0a181735cc1711814302e79182e23028605cd5305c46050c019e260b88c0a1b2f879cd529925165f0eb9aa5324a2c8a3f8254a649446dc5f04a94c928b2f8b9c9529925165f16b92a5324a2c9a3f8154a649459347b02a94c928b278d9c5529925165f1ab8aa5324a2c9e2e2154a6494593c5842a94c928b6ea7e1f32992516dd4ec3e65324a2eee1f52cca6494401c3aa5994c928b17a59c732992516df4ab8e65324a2c5e1f51cca649458bc3aa3994c9288da8fa1632992510051ec2c65324a200e2d528ca6494401c5aa4994c928b2aa7e1d32992516554ec3a65324a200e8f824ca6494595d1ee4994c928b2ba31c9329925176f0fa9265324a2ede8e524ca6494401c3aa4994c928bb7a3549329925100706a9265324a2c6e96714ca6494595d2ae2
  | 24 => 0xe86f1e663254a61d0de3cca64a94c3a18cab5a0c52987430056ac18a530e86c6e56754ca61d0d8dcaaea994c3a1b2ab5e1132987436556ac226530e86c6e96744ca61d0d8dd2ae8994c3a1b16b5e09329874319763c126530e86c6ec6724ca61d0d8dd8ae4994c3a180395d493298743007632926530e8600e55524ca61d0c01d8aa4994c3a180391549329874365763a126530e86caec4424ca61d0c091ed0e284c3a18023d61c50987430555b420a130e8600ab58414261d0c655ad06284c3a1802b560c509874300573410a130e8600ae58214261d0c014ed0b904c3a18029d61720987431956b41e4130e8600ad583c8261d0c01ccaa5904c3a1803b14cb209874300732a924130e8600ec53248261d0c091ed0e104c3a18023d61c20987430053b4284130e8600a758508261d0c1556d08104c3a1802ad61020987431956b4184130e8600ad58308261d0c018dee4a92c3a18071b1c9525874300666b9264b0e8600e4d524c961d0c015ab07a8ac3a1802b9a0b515874300572c16a2b0e8600a7685c8561d0c014eb0b90ac3a1802b560f21587430076299642b0e8600e655288561d0c031e90e90ac3a1803b14c921587430053b42842b0e8600a758508561d0c1556d0810ac3a1802b560c215874300732a9042b0e8600af28008561d0c015e30010ac3a182aada13755874317d6b41ceab0e8600ad5839d561d0c015cd053aac3a1802b960a75587430053b42ce4b0e8600a75859c961d0c5f5ad07392c3a1802b560e72587430053b428e4b0e8600a75851c961d0c1556d08392c3a1802ad610725874317d6b418e4b0e8600ad5831c961d0c015e500392c3a1802bc60072587437872b996a4b0e86dce3740d4961d0c5f5ad07292c3a1802b560e52587430055bc22a4b0e860aab48454961d0c01c6f08a92c3a1b2f8d211525874300733c12a4b0e8600e677254961d0c01cc8e4a92c3a1b2f99909525874365f32a12a4b0e86efe573254961d0ddfccc64a92c3a1bbf994c9525874365f1ba02a4b0e862fad68314961d0c015ab06292c3a18beb5e09325874317f63c1264b0e8600ec6724c961d0c01d8ae4992c3a180395d4932587430076329264b0e8600e55524c961d0c01d8aa4992c3a180391549325874365763a1264b0e86caec4424c961d0d95d2e80992c3a182aada1270587430056bc1ae0b0e8600a76851c161d0c014eb0a382c3a182aada1070587430056ac18e0b0e8600ae6821c161d0c015cb04382c3a18023da1c50587430047ac38a0b0e860aab68414161d0c0156b08282c3a18beb5a0c50587430056ac18a0b0e8600ae68214161d0c015cb04282c3a18029da1720587430053ac2e40b0e862fad683c8161d0c015ab07902c3a18039954b20587430076299640b0e860aab68488161d0c0156b09102c3a18039954920
  | 25 => 0x18bae6a90c0aa0071b9c9521815400636b92a4302a8c9c767154860550051bf0f990c0aa0023761f32181546be4eba664302a801cce72cc8605500199ae5990c0aa317359c732181540046fc3a64302a8008dd874c860551ad93ae8990c0aa007339c9321815400666b9264302a800e4d524c8605518d9ace2990c0aa0031d95171181540063a2a2e2302a800c77525c460550018eaa4b88c0aa00335cc971181540066a992e2302a805c77505c4605500b8eaa0b88c0aa0172dd01711815402e5aa02e2302a80287d85dcb6454c018dea4b96c8a9b521f61d52d915300637b92a5b22a602c5d754cb6454c0399ce4996c8a9803335c932d915300726a9265b22a600cb7645c66454c15968c8b8cc8a98022fe1d6419153014ae41ae32a2a600d54315c65454c071bb07b96c2a980333cc972d855301e2eb9aa5b0aa601c6e7254b6154c018dae4a96c2a9b5a3761d32d855300667b9265b0aa600e4d524cb6154c09968c2ba4c2a98032d5d361985530047bc3ac230aa600c6f7254b6054c0199ee4996c0a98039354932d81530047dc3ac0302a600c3c545d06054c0187f0aba0c0a98030f21574181530061fa92e8302a600c9f325d06054c0193862ba0c0a98170fd41741815302e5d282e8302a605c3d505d06054c01972a0ba0c0a981727cc1741815302e4e982e8302a60087d879506054c0187ae92a0c0a98031bd49721815300667992e4302a600c6e855c86054c018db0ab90c0a98031b9517218153006362a2e4302a600cce835c86054c0199b06b90c0a9803330c5721815302e37a82e4302a605c6d505c86054c0b99e60b90c0a9817334c172181536a43ec3aa4302a6cbc3e745486054c0187ae8a90c0a980f175cd521815300e37392a4302a600c6d725486054d938ece2a90c0a9b5a3761d32181530162ebaa64302a6cac9e744c86054c0193ae8990c0a9807339c9321815300666b9264302a600e4d524c86054d8d9ace2990c0a9803350c571181530063b2a2e2302a600c74545c46054c019af06b88c0a98033520d71181530063ba92e2302a600c75525c46054c019ae64b88c0a9803354c9711815302e3ba82e2302a605c75505c46054c0b9ae60b88c0a98173c8c1711815302e6a982e2302a600cf1305c46054c0517908b92cba18061f21d52597430551e422a4b2e8600c6f7254965d0c0199ae4992cba18039354932597436453bc3ea530e86c8a7587d4a61d0d91c6ce9a94c3a1b238d5d352987436e72b21ea530e86dce5543d4a61d0de5cae65a94c3a18cab5a0e52987430056ac1ca530e86c9a778754a61d0d934eb0ea94c3a1b278d9d1529874364f1aba2a530e86cbe564354a61d0d97caa86a94c3a180399e09529874364f33b92a530e86c9e647254a61d0d97ccc84a94c3a1b2f99509529874378f2b992a530
  | 26 => 0x3c007001801000000400100000040000028000000001002800000000b003800400000c001000000800e000001c01c00f0028014006009000000000e00700180080000000008020000002002003c0000000000018006000000800802400800a801800c0000000000012007000000000c000002800c00000000100180040000078024004001002000000e0000000014032007003800c02600700000000040030008034008001001800401400000000240000020020004000007000801c00200400200000000010000000002003005000400a002001000000000000000100000010028000002000000000c0040010030018000000001000405e000000003c004002002002c0020040000010024000000800000000300080080080020000004004002001800000a009007000001400200e37392a4b1ca800c6d7254963950031b90e992c72a00333dc93258e5400e6639264b1ca800e4d524c963950018dee4a92c32a0071b1c9525865400667b9264b0ca801ccc724c96195001c9aa4992c32a0029d61731586540053ac2862b0ca80aab6840c561950015cb0418ac32a002bc600315865400732a9442b0ca8018f4874856195001d8a6490ac32a00f0f9d1529825400e37392a5304a800c6d7254a60951b793ce9994c12a32b279d1329825400e6739265304a800ccd724ca6095001c9aa4994c12a00237e0d71982540146e41ae3304a800e69524826095001d9264904c12a0071b9c9525825400636b92a4b04a800ccf724c96095003998e4992c12a00393549325825400c7c43a40b04a800a7b854816095001cd2a4902c12a003b24c920582540247b40ee5b1aa8008f581dcb635518747908a96c6aa0031bdc952d8d5400c6fc3a65b1aa800ccd724cb6355001c9aa4996c6aa002b360a73d85540146fc3ae7b0aa800c5e545cf61550018b8a8b9ec2aa00237e0973d85540062fa92e7b0aa800c5f505cf61550051bd07b96c2aa0023760f72d85546151e422a5b0aa8d4c5e7354b61550018bae6a96c2aa0071b9c952d855400636b92a5b0aa8028df87ccb61550011bb0f996c2aa00237e1d32d85540046ec3a65b0aa800ccf724cb6155003998e4996c2aa0039354932d855479e5aba6c330aa8008f78758461550018dee4a96c0aa00333dc932d815400e6639265b02a800e4d524cb60550011f70eb00c0aa0031795173181540062e2a2e6302a8008df825cc60550018bea4b98c0aa01717d41731815402e2ea82e6302a805c9f405cc605500b93a80b98c0aa0031bd4972181540063742ae4302a800c6d855c860550018dca8b90c0aa0031b15172181540066741ae4302a800ccd835c8605500b8dea0b90c0aa0171b541721815402e57a02e4302a805cea405c8605500b95a80b90c0aa2268f211521815401e1eba2a4302a8d4c5e735486055
  | 27 => 0x4800c00001a000000400a000000801401e001001800001200000a000400001e00c8004024003003800800400700080000020090018028000002001801800200900c0000002005001800400c000000000000200400000000100030010000002000000000000000a001800000600000600240000060000000002000000001800a00500480000060010010008012002004001000c0000008004000000002000c002002003800000001a001800002c0000000000000004001002c0020000028008008001000000400000100480000120000000040004000002800c00200a00000040000010000004020008002800c002008003000000a00100000000000070000000004003000000800c0000000028002003003000c002003001800802000400000040000010060000000003000800400200000000040000000000000000005000008000c006003001000000a0058020002003002800c00c00700000040020010018008002001007004400600000180040040080058000000000000802c0000000008004004001000800000600000080040000010008044000000006000400400500000140000000020008000000001800c0260020000008014013000004000200100c0030006000000001c03600100080180140030098004000002002800400400f00000000020010008044006002002000000c001002002c01200b004000401a014000000c0160150028000000000002000c004004000000800e001001000801a000000000c0000000050004002004002000c008001001803000200200380100020000038020002001000801c000002004801800000000080040080080068000000003002001c00000000180000000020020008006011003801c01400000400040020010028000000004004800400c009000000000000f0010010008000007001c008001000002c0160390010000002000007000c00e00000000040000000010008006006000000000a00f00000000000050008000002005004803000e0030000000000000001001000200200100200080050020004000004001800c01600000000040000020018008002003001001c0000010018004006001000800c00400000080000000000018020000009000800801c0030000000004002002000001800a001001800c0000068000000000005804c0000070010018002003003002c00200a003801800a001017800c006002005003000e01f0000004002015001000c05c000000000400a006001801800200a0000000002001000000000200100000140040010060000002004001000000c000000000800400100200a003c0000010014000001000001800200c00480140000000028060000006000000c030007000801400600b000000001c01400080180020100050004002005001000000400200280040
  | 28 => 0x134a0005c2224c2600000000000194000000000198859e6920000000000556000081e5865e92d980000004d08db800000000000000000000000000b9c000234b549ccc00022400000008870001ae4000428000000000000004900010ba00c2f28001318000711ae693ca0003100c080003f6000121c00066000027dd1245fd2b21038f0600045a80012581e754813ad9760006d880009a40003bf800000000044b000000074a3c501d867cd1f0000238000717457b9ac00000000026080000004f184257b48d968302c4000c28000000000000003d000087a00051ca4881820004c880000003a90a08000000133698174400049a37405800000000001c9972a8683e880000000000000e0c0000000000000000aec2618b806669b24818000c8c9b956c80000000000000001c147b45e6a2347861766beacf168400064922c46fe0003d8a9e535e6a41ae9c6129ec3c7031480868000000002000d000801c008009000800800000200000080080000020000000000000800000000100180000000000048004002000000000c0000000000078006003002000000000d00880080000000038044004007008002800c007000001001400500c0004002002001803c00200200a800c00400c00d000000e00100000000000030008004004000000000000400300100000120050060000004000000001400401a000800800000c001000001c00100300000040010000018030000001002c01a01400100000000000000000016003003801400000400080280040040040004000005000000000000400200000080000000000000003000000801a0000000000002009000002800a009001801c004005001001c002000000000000200700400200060000000004040006000000c00c0070010020002000002800801600f00080000200060020004000003000000c00200b0018014000000000001000400f004800001200100e001800a002002000400000000000140000070028018000001002000400a000006800800000300000000000000000004006000005800000000c00100000100010080010000001006001401000a001800000c000001800c000000000800c00000500480000060000008000016008000801400e0020040000000000002801000200100080000000060000004000003000002800600100a801c00000f00100140020000028008004011002000c00801a000002802c0080020004000010000800800000c000002800e010002804400200000080000280000010004000004004800c00a0020028000004008000000c006002000000c0000000020028002003000000800c00200680000000000000010008000000001800800200180040040070010000004007004800c00600000280080020010030004002000000002001200100000100000050
  | 29 => 0x1b81b8994c42e0002180001ca80000e2871822c00000031e400004e6d980000000da4d6938400039268905d0000da200018e0dd25e16b3b4f5738000202b3982ba98a3cdaa0511050c39f094060e48d00023689467bc68ba728f289703af03900008a166900008fe73900000000004cf06220e98b0dd371a96651ee91d007851db1a8891a1af38f0c750068a1f40003750000b912222496ec1bc00002286b5092d5c06960938c50000757000029115873b5db8000ea60001fdb598346a354810434652dd90002ec0c7e00024fb19927626c000391400007f00000000000000c826641548322eb8000a44000000000159a4e31023780c980001ed00005d8000000000159cb4e58696ac3feb2621018e40001e331ba0bdc2c0191818dedaaa6094d8adb52c6000000358ca5c1047352154d120000480868196ab354b8000dfe00000000000009cf00003540000002a915c40001070000001c326c13f820496e200072d00012fe00000000000000002c0a4040000003b40b0d79800000033783664af4ee3834ddec6f24c1fb56ca91b1a1248cdf0c571d88f5cc96d082a08000c7a8be26c8910000672000000000000000032fd0328f455503a4ab4bf300038900000000000000000000359a9506620be0002d3c00000000026a800058f4bd01151f6000000000000024f34f93b80004290762b449160003db18c00002945e4911c100e69147ac75698cf8439b219bb4bc336d8a645d66a114e84206182314472080c80c275c0346d1be0004d73505118e3200026000ac9bc55a0c18d26505423b975a4c3e10001a090da2675ec0e3057cab82bdb72d73000000000011342110003454726526475a1880000000000000000be157929300006d300010283a0000660800030ec70000000000078d0cb0a000000004ed88f98eade16252b4000069e1a2881c00000e00037dc00033500000000008bd00000010520000002b593f40005a4822000000065f00014fad451b6308da86d2d64080019b2c3d000000090c0005d88dbc0000ed4fcaaec00029f000ac689d201d043b93529c95b4dfa309c28d2800009eced800036427040b67033e72bcd06a00027e00000ee4b100000417c860f652aeb90cc7c31f42c95ac45290000000000000030000000000051517543800000000000eda00026985a90900004692a74be2d5463fb82cb302cd353ac65a6e473500ae4045a00070c32cc0006e30e6ac80000d5c3d60a4142ad383b1000032200000000011ba14a47e07e00000001df0000c104fd4f081900000000003944c5000000008b80007e960ea9bc8160000000000000000000233c0000005b900002349e2454b5cd3cc0000001b68264d853eb00009980005400001864e7a490800000000073230edbd470b5180b4963e76e6c631894109f36f10afc0004ef5ea0
  | 30 => 0x8aa0000115000158c00000000037500001dc000000000097c4c73014000de900000007a611b0000001a9a32426a9608f6e0002a4b250c7800000013b52d03995990669b043cb6ac90015ecdf2000274d104d9b00180019ac11968825c41cc32e485800192e4593b019f83361db6a43344d18b8644a9975bec5e9000000064a6cd09c000000016f0160000000d5f0000f7c8927aa0002bdceeecdd260824c00047b00006080000001e2a2c80000000ddb77418c5720f92f2940c89000015fc16a0001fa0991b9a00000000000000000000b880720004249a180004240000000000c382d49a4033c67400000012509b051d800044e00030bb009a926ce01019643b26d75733600000e5600036ac00088b0000000a80a5d256800000000000000002f400004d8485298000000351c73436b00000000002f36a30000a0600050ca6244e291c70e80000e6824000028d38e0004aa39dc506a5543d859db80a58353343400039d1b5280877e24500000000009054da00000004b270d2e819f449e0001ae98c28d835b0000efc5fe00035ed5fe00071ca3d5b22db46100fe09d410555205619347161d29e985b87cd593b1f586208353a94ad99e5cb4af9b71a22cae0000001060000396a9b545064d6e9294ca2491530c937c78834b0c4054400000060a8650000ab636c1100d4492040aa44cd96a5700001042c800064a910443a71d0001f957ce6ec0001cac0007313a7a9119a8a2e3c78000f8a6ac0000000a90d4e00029d9c1053370f98443841350000000b22aa533091114ac00030e0000000b6800000000000000002a507128114e1b0cc57a7a700038f02a40003e3a77d9d029c59bb494542bfe0000000c821590001578cd247a67a01a5b0ea656910000d628072a7ae2d3ea0003e628400000003f40000c4839c000000000030400032711c460660d09680c66140002214748c882f21d198680584a31d606380000fca98148ed640a1000072271515800000000000000000000cc32048fdc07800069d2380d7000006f88dc0005f360928bc95ccbc000330943e00009a25ec5564613f5add934832c6b7b710b2015513838888fca9e1733108000bd0000000037c00028ab0781de11257e9084d7a5b85b214f121400000000000008fd03a9c480000000001f497d8bf807d891cdd6cce5e898340009dd2ef096c0000182370794000000000033c6947930001c4c0000002e4ad64e600000002c840009ab0000000000000411194800027d4af392568a29204e2bd56e047700012fc000b6e0000000000c9d0000001a840b94df00000008311ff20209fc00039b15e80000007028e400008e32d286bdc60cf05959ad02ea9fc0000324000e2000021dc968e6c05928cc4fe78413100017449642a6000000086a0d306a400000000000018a20000000000000
  | 31 => 0x84f6059a838a3810661f8830436c294ecae08cc86cc2b40000e6e0000000000000e530000001b32494000000000000000000004480000000d10cd6cc700000018ca81f18b2ebd61000066ab8c4000d333ce1e38000b4015980013a49ba07c88807b2b3800000000000005db21d00003475511b58144000000187825667972e05f000039f63c2c700000780000c48000000000000000000038d994518886c0c9ab95c5c1690021da8e460000001a68bcee09028115000000017800000000000e70adc6a42bb622800000033f000209c54000047900010040006201c7c1405a45312835b6e4363172ddd6eadc85d3094515a85263f000047068e23193fda6800012c000070e0b46120001b4c0006bb800189a000000109c6dac4e448a8ac00099d6cf00000b8d07000202c85800000035e000000000034acefa0240e1a56800000045d2e5c00039e1c11e040004f5000000101c71a36885fd67e29633d06d00003c826b80006907710000ca134e9e43a61e140007f1000000102e0004dc0000000e5b00033b000004f2069148000b2f67a80001ee0002800000a14ccb000228ca4881300001a80001f318f80000009bb0002bd0b3aa670002ac50fe8fe00025f856443311cb0005440001fd2f5d9e4d23000107519ab3100000ada5284351c15d4a1c93e4abb0acbfe34c3bc1a044806df00000019a0b12468187c54620b5b7800080e939000100400000050e00000004962ec083428600016388f06229b72e0a2c0eacdc300037a0cbc00020e2070000dfc06907d85de00016aa0607e47675de30e5474b9d2d9a23cd7c5fa0002da54c89764fc00012da1d600000000007b50002948ff0aa16d925000007f26c09f04000c0a0001eec0007240000000000d6d000000000016513685107dc567384a945be21cc264090c0009bd0fdb00d68e11000001ac6ceca323580008b03850000994cb84fb5ef87f01e283700b8a9932000033e8000e7a4f3000000000050b000000000085f0002d840001a049789e07d400019e944c000a311e027fd58e82a4db1ec1c18d7932db2b4000b573d000000004ab5b10000e0ca091b817bd6bc2b50000000d220000f00e5400000032192a0000000000000000037402600010a272100020f400000044baba85fa04451b0000000da12c39b80a428ce315a4919c40002658c64000000000000000052f486184800011800000009d81b25779d1084c00000015ad6161f11cc368c0009864f881006c6be862e00003dab46000000000000002f90893ceb7844a000000000017703152ea000567b21c2fc42b54f9358548b8f1680001930d8e0000409cea6a959a2fc02b43382c7150cc5a6574433988000000445000028c00019780009f0588427a325b089d61c314dc2501b61d59cfd714b99000076052e04a5c680000000003d9
  | 32 => 0x200000000001fe8000c8eb5000019e01eccb66da8000864000000000124e00007005b00006a800000016f21b100000000000004d00000000c0661507dc00000023e2c28000000635354c27a00039e0000e52e65373000000093400010f85bebde5f8a56542c2de41580000000005aa35a5a122c20c794b52287320002000eaa4b5000141c000c3700027300000003d234ed94247d0adaf0075c0000001f5cdfc1df03f000000000071300017fa54e47683d00005d3392a1400c20e70370be925c0004a68001b828ab00009c8000b2d42e1550d92acb00000000005086e80000000def00006b0000140000308905c9b35ad96543f47285120a350b690d00000002c67a240280000005c700000004bab553f709d0c4a4ce42b800105a0bb25c9e2483c7a9037951030a00000000002060060000000bbe00060380000000000000001a62cd35358855aeaa4f6861c45c5628c6d20000b2c00052d146c0006f61252d28b94000000271800000068118880000005cf31659448f03939e790f200000000009442ae0002c3066429b584b8840000000001360000000000352800091f6cc03ac0009730001311bfae070000b15c7e64865001e54e6dfa41d82e9bc686432a132996e4b60130f7067612a4e0366844c633543000144cbbe3ec9f914e20001f9a7693dca8b3ceb319080da73061fe8000dde1e70a60faa0e563600008da55b0000a156729ac0328d3d10865a1c50ed103a2f20002a8c0007f33418000000aaf0001334642abc2022de9a780000001c40000095000000125221f3810001648000000345800059c22984f1422d721c7aab8e9656d3468c680004065d59d84bb8e406e1066421866d60d9ef40000000a7228174aa0c042000000024200038f578cb8c101000088c77962404940001e800000c800012200000013fa00000035d80002ca014000101a0000641e5400000000000000006995252800f2200000000000000002df8000000a20000000000023463480000000000639b755f85bb000000000000000000016d80005820000000425000292c0009080000001b5400000000019ce0000000000000bf9501800000067700012258964a9201aed497a63500000000007c400000013d40005d3b90800076462d0000000d5b2d898c4000000000380c000e2f63baf659e65652a9a7614fcdc60180b04000d7e00003d400000000021d823e00000000d5536bba0001528a2800010915f80000000000bfd2ce7fe4c080003de6d53a710b8ff2131000067c000c990000934ef651d0000a18a6a2730b0b02da1664900009bc000000000000000029100000014e4000483b321818ddc441b1d04a46153cca0cc00000000000001280000001eac0005a800033e4000869000212d54e72e44fa2cd5d641b00003b8000a5b0000f94c6c93371a0000b7
  | 33 => 0x42a2140600017480000001fa8910ce32810000000a1d0001580000a320001bc8fce5c5000000000000000032c400033a01f94a0000ceb3838e500da0003330001508c7b29c83f901eac0000069108800014f00007ce0006f3000000023000017808860005deb6d94bc000000105800077300000000006654e69fed36aa634958e0521e0004382aa1ae0c8b658251403c8de22e8a54fbc23d14400580001b52e9000022609f71d35689ee000000314997a0003f12e25468a42000399d6c000032c0de8420a7012e1c887b0000000000000000d41fb4759b80001b30c000000000002c009ca00050393689265620000001766000000000000000000000680008675d0820800000000000019b0d4b713823530e6fd227a5a5bfed202723404f0048f04797b88187523afaf58b6c64445719f10f8000000000000075b49e257488ad1a30db65128e2c466da078086492305181d9e28782010001654c0f50a00003883d409b800000000000011c8878b334a80000000ada0000e10000ddf4cc1e58000000002b3853500005cb16f9ad0a43588265022e2f400009d40000720002c50db20002fb80001aedbc56f80000001502fa2c8948270000011904b25db170aa600002770000000afa4fa0528ecd95200055f24484282cb120acf8274be04bc868400000033794d17d2db042d07f80007ef0df919518ae13302000010a000628380000062f00035b1686de471b80000002360bc80017cc96b01280000000001a880a9cf2309112843c00058954185c400000000038d986a663000000000000000000004f80000000000000000000036c56c5d608e00000002e9000165c4563f156299580000ab58c0000cec5100000000000aa92929b48f10e74000000000055c28d15d84c6d4c68a0228ce0000111b9bc412df02f500019800000001ebd57a0006bfa9e1a382051ee9f850e4d8b00020414d8b5f6d480008100000000e384ac00047c18b02402356878d705eee293ed9d68fa8df528f999c53406209780000004660002cd8000396000000000000020a27bd66a1922a39a6c000000000115565c8ea0002050000000534a3715b603723c252c00063a24bad9c0004605098001458ac24c40d780000000002e1d00231d21505313a20001951ff5920e73000000000041000000009363b200015e4846ac85a21bb950e9d07232fed01443100022fc00084541280000e09f00000f45ac06e744cb478b7239b00000000000000003981098a8f0000000e70000000131d58c0002c92b0c00056c57f29198aac674c5b65591cacc41ca54c318e4834a02601f800071529b8b9e66c000296538acb85948de5c02e1104ba920474c7a5e58d590eae6d363aa6838e3970000d407de30f00000011e25853efa0d109a413079b2ace8e2875e200006806f93df32d50f456f2e
  | 34 => 0x9800015c65e800014101980ae00000000000001a331c5758e593b7ac180005d953e00000ccdcf31da4957224f406c00000003ad000000000032222100000008536dc80000000003e58ce4000ae826eb5e83903db05e873c4be7754638790fea3ed00000000005f6000000000000000006a8aba1450ab840429022c1870ae40000290002dac0002f5550015000093f3cd29400009103002108f7099e00000011e66843a689a4b58a7f5898610ee0caf24534bc24cc040af00000000fa5a091880003b7248857c02600057c8000000ce9578074caa07cf73d9efce400a96180000bf286e1e5206c5041a542b00002ee0000cab54171c0000000e35676c3e29d15c000030d6d6ab70000b5116da058ef4216351b91c8220002e000010bc0000d3b578bc60003bb0fe5b0c3570002d7122e0002c98be4000000632092000000019b86b4402e380000cf0000d6e0000000000e6e00007a86568bc01b1e9550a1ab4871c3c00000002980017e89ed00000000001111f13675b743cd5448001cec00000000000000005df80480002063ee03f55b06e109700012faa401d01814d1e0e30f733699da3b50000000000ad2000327c4a67c20000000000000000117c5620001d60c9c41e1976cf8a1151423f47b162874624e3f32e140000000001939180000000000091c42f15c3061b767c935e2298d9467b6390000966cef00005ad85889e00000000008cc682390d2120000581458444c6d57709559643c96469635ce0e1e48d1c100000005dc35c49b6a2d02d000000096f00014c8b5c00000022a80009300000000eb80f86ac045030c87e25f1f8db240001db148cf3e4e700000001c261800008a8dc80006eb80000003492d38001b5c86000026107d20003550c6cc20362252b69478e4953119d44fd826b58ab95c000b030001e8cf5a8a525036285522132629b117e40a10000000a622fc0001cb0aaa0005ed8000000734000000149c00064110e000043700000017dc1b0322800008cc846df3620d2ab6a5d410fc0004564618dc8bf8d2e4ae13445545111a70000ecc9f45c900005121e20000024744000000000000000033a800189e00020b80019bec2d2ba31b88a02fb000000070086500038a04ae47953dab740000000000000b900002e6951400095168c0674c4c83c69a800016c00073c000018035b496a724992719000275c000000000320d9ec00000000002460002f58000000e5f000265d2dc0000000000d405dd0002adc00070c000307000000000000ec0000002782dfcb06b023ba349c8a24155f7a4e8038e1522f1d9478c55629d92700006ab0e4a1193d80000000001b400000001cd5bdc0000670000d7e7413fe24600009650a4800037800059600007768fa4ca96b4f18ac1074054c876b8147337b00ce0000000d9400000000025218
  | 35 => 0x28a0002b914b8c5305f85f40008ef00020a100898367d9838000a91712b76c0002462d7b658000000000000000046a0000001ca0000000107c12c0001e90001c9ea3e7318001390b73000000157e00033700004f2d440002d68aee0006f6b0e800000010e37e4894c9b382b79c1580002b088386a80001018ef1cbcd831ef0f050d6c472848b598b64180dc80006fc4de1370000000a666ab80002481dd3193439bac0000fa304cf740a84cfb574d00000000000000048110c00017ca000338a7508ae3ff2742d34b2800055c882026c6a554931254be91e2d0a781752d2a1809a60a2ec914cb37242e62d421d0604a4e8d764508840f800000100009840002682e204a8db84761a2991e00015e13987602f151fb92d5c40000668029396e1036a30b80bc9190b6af0400000035714b0000000463008c0008c1140aaac4d00004fd968d2aa0b8549a70980200000000000000000002204000b52000000025200047faa980002b4193287959200000031f00000004540000000e02000000000000000006340000002ab800000000016620180005a00000000000be20bc38ed1a27d3000385c1a08d50001c28d2e000000007c0000000a6b2e800000000000003aab3a49c0001344d4f00000013240000000000640798000258402a01135903080008263613041a3263e00d9b1416e3cc48b03a95f000042a35f00007630000001ce40000002888a024841f61bd092049d32faa347a0d9708e8b5d49a79255aac8c7ac6c316e8f8c6ec34d3ed3738e9061a32ab0512eea6a328268da420000002669cd0e0e00006280d870800000016f8dd500000001225c600000b4000e526260124000a176e50000000bd300037cc00050d2f10000a7e4120002ae8c3a00000011bc0000005e29da4000bf7010800116e2ba00003719c84a70000000000000079000000082100000005b00001f000007cc00072208a4c2600013b0d8462a0000001ad400094921aa27184a0a6045afac0000000000df401600000008bc2b8d365fd00000004a1000000000000036322ec2dc50f5c18000200bf6438882800059a0000000000cc50e8af700000005a98000000df465238b1c7c89d3ec0000000be34cd815dba20000001c052948d30000000000ae74019e2da726fc0f58000c02000241b3f8000000578a4180000003d91aed92cb56057aa586c8551582b84800000069f800000000050780000ba0000002fd4ab00003c82decb6a00056200009540001dd25a8f0ed7413012e05c60523a1a498b861cb168875ceba95619180008d0dfb069b83cb3e5a200000002d00004522fa91445801578f54000ce50e900000003605ba2580ffeae12d518a466c12c719b7151ce00000000000008634d3371dce200045a2f740006f131a1c3941498540480000000000000a4d2cc98f2
  | 36 => 0x3058000000000013b4f9968baa2c58001058ad7639b6706eed65343b6fcb640002be1d1547a5c20fe8a9c772c0d2c604e47d600004336bd918000399b64c59cb1149b1b40b7a0144ba2a700002da22e00003bc0000000000d1003a00000000008a700000018c024c0ab0ab4f2e3a711999cc2e00002f92f08000d6100003880008d40000000a8c0000040c605160005569fd800000028c14a8784935000318c000000085b151950c853be1b944cc4f92269b780003bd0000000ae63085ffac3d9ee4760001bdc31c93138f0001660b9b02aa7d8fc0c5f7168000d2400004d344c3d80000c00000000d0501f00009c000001a00000000000001b3c0005382d827f9b5830a6e600000000000269d010340000001eb8000a454d491b000000000000000000000002320f901e100002654465360002128c4eade28f3401aa2823620a5103061da4b63044ba07dd3dcb1795101a820c9be833807b2ac95b90c28b64ac00005b2e4e1dc1d245a6ab00000000dd4b1b0000001a58cee6c81168bd8c1636009840846f3216880151c4bc6818878000bfc3d42e7cc2ccac1fe30207c894304f1a140664a62c22a65082cff0001884a3207d0b109a975a6ed46da9dd5da53d26000001ba4824b928dd44a2c0607000167a9ce6f5872811214b7252d2d78ed4018f0364974b170002c1cd3a13e003800000028e4a9030ce1a0000460001cc264f0c497b5602bb4358309800000033f82b4f044991af820490a34167e29d0ed67a10001f4065ad8937a87c16ba00007f800152a00035b975000066822db95400000060c94f920000000034c90b213f27899a928255f2fa80000000000002ba4d168ee0aa1ce8bf67144bc305d926000085000008ea612463024be09f24e203c0b36ca63fb92913d02a501126344fcc2f12f0cd18d60de25db329c985a60000b948eac4300000006d0000000000169044c53d00006f02c6000000013a5cc1c5a3591c200050d16d04f405964026709602e83e00bf8d5e0001b980008e04dc00028487e0566017b2e4000d6b0000751bfc3530002ac80001bd58b0000000a1b0002d60000000000000000010e4749f296fab9325b80000000006d425086b288000028100000005dd80000003050000000ee42c803880000007425e41d5000092a1751bed83ebed3e311c414ea0562e85980000005340f3c276bb25bf24c8bcc0d6720ac7907c1e658707040e88e81859d64bb48e42dd3158872c366662be8432ba320d28a4958df834e00000000000000c5cc8400000032a88ce3300000144316afb4f48d549c4e0416786dc5eccea59427ac00089800000c58eccc96448c4cad414f5b1800000000000023e5b1e0000003119c3654b00033800000005dca925bca000000000000012d0cc00000000002fc1ca95a835a01e80005ce0000b90000
  | 37 => 0x1f50002b558d0a274ef000005c8b85ca264c75000030100e0dc411e32506880008ca00000015046ad26a3111b7aa3c26308c90de00041c153579e8e50000000000cd764f000000044e1ac06b81783aa3150c4000084e0bda0d89e45062db8e989000004820000000388331000000060311d8ab15949371be0da4af00000000ebc592e1c0002a3000000000000005f000050595a489693d50c33f409089b0000e840008cb17686e999ae582a1275400096200000015a685823a35580000003978350fe871c0f48fd594ebd545cb428000000000012c000068
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1949856017218d1000670605805c863440011c9980417218d1000532a58105c8634400184e855ca6218d10006136157298863440018c572e056218d1000613a1572188634400184d855c86218d1000623a1172188634400188d845c86218d1000513e5f62548634400144d971895218d1000583650625486344001a468654a2118d10006312197248463440018c8865c92018d107b692219524806344001494964c9749451000741549325d25144001d21524817494510007604c9205d25144001985746086394510006311d98218d51440010cd9221973d051000433e4987d8f4144001454964c9759051000651609325d64144001961824817590510007504c9205d64144001945756086390510006a1d918218d41440019c373608704c51000531648635c7404400144d9218f75501100051364875d8d404400144d9218d751011000433660635c840440014c59218d711011025670dcd821c530440cdc907650d414c110004d4657844c530440058c67660863841100061360d729096504193864815c932594107ad1365e724c965041e9c44815c932594107a711c41724c9650400144d97109325941000591644424c96504001649901093259410007115cb814c9650400184d874cb20594107ad83656524ca6404001a0d8354b20990100068361532c826404001a0d8354a425901000583654424c9640400160d939c9525901064e89205524c9640400160d951c93259010005a1644724c96404001689901c932590107ad83656524c964041e9e048154932590107a781c41524c96404001e0552e0532590100068360d52c816404001a0d854cb205901064d19245725496304193a44815493258c107a51365e725496304193644915c95258c1000711e457254963041ebc44915c95258c107af11c417254963041ebc4a105c95258c107af1244172549630400184d8754a4258c100061361572109630400184d8754b2058c100051364f705d5620400184d7560f745881064e19205755cd62041eb44d979d573588107a711205755cd62041e9c47105d573588107a712841755cd62041e9c49105d5735881000513654745cd62040014c5911d1735881000532640745cd6204001c4575e05735881000513657705cd620400142d921d56450010005136487558d400400106d981d562500100053164883dd91004001c45524cb76440100051525d325951004001a45824c96544010007904c9205951004001494974c9644401000781549325911004001e21524816444010007a04c92059110040018c776608734401000691595821cd1004001a856460873440100043525d8258d1004001a45825496344010007905492058d1004001a618061562440100053125d835891004001a458560d6244010006b06018358910040012c5981cd6244010
  | 1 => 0x69160d52c826110001a45854cb20984400069161532c856110001a4583548215844000589650725496110001645931c9525844000598640725496110001645959c932584407c591656524c9611019568494549325844000781e51524c961101efe049454932584407bf81d01524c96110001a458354b20584400069161532c81611000142d9221776500400070354932dd9401000182f7660875500400040f25d825954010001a0d824c96550040007824c920595401000160d921d563500400050725d5258d4010001a0d825496350040007825492058d401000142c9761562500400068a60185589401000122d981d5625004000683615835894010001a898060d62500400058964875585401000143497549615004000781549325854010001e21524816150040007a04c920585401000344f9754932d963000e13e1d524cb658c19548c945c9325963000e13e1d524cb648c00144d920c775592300051664031dd5648c00706c985c9525923000513a5d524c9648c00144c97549325923001c1b26172549644c193464915c9525913000513a5d524c9644c00144c9754932591300068961152087614c001a458354821d85300069854980087614c00382c87549425931000e1321d524c963c4001615931516454710005896485459151c40016319015164547100050b6487559140c400344f9754932d961065523251724c9658400706c985c9525921000513a5d524c9648400144c97549325921000e13e1d524cb63841a7a448154932d8e1000d13e5d524cb65440050cc985c9325951065523251724c9654400184e8754932595100061321d524c9654400184f85e0f72591100050b25d52509644400382c87549425911000513a5d524c9644400144c97549325911000613a1d524c9644400184c8754932591100062321f424c964440014649754a21591100053125d3248564440038c4874c9215911000e1a21d5248164440038a887509205911000e3221d3248164440014c59218d7195110006136177298b63440010cf985c862d8d10005836506254b63441a7a488654920d8d1000613617729cb634400160d941c952d8d1069d91a447254b63441a7649901c952d8d1000613a1d5290b634400184d85dc842d8d1000631dc98110b63440018cb7260042d8d100061361772c87634400184d85dcb20d8d1069e13a1d52c83634400384c875493258d1000513a54865c8634400144d952197218d1000523a50865c8634400148d942197218d1000613a19855c8634400184c866157218d1000433a62655c863440010cd989957218d1000433e61645c863440010cc985917218d1000513e55645c8634400144c955917218d1019531a44645c863440014c696a057218d1000651616815c863440014c4966057218d1000532259805c86344
  | 2 => 0x38c4874c9215874000d13e5d524cb65901c960c9454932d964064d192457254963900050cc985c9325864000613a1d524c9619000184c8754932586400061360f7298b655000106f985c862d954000591644624cb65500f7a288650920d95407269221932483655000184d83dca72d95400061360f7290b65501c960e941c932d954000591644724cb65501c9649901c932d954000613a1d32c87655000182d84dc821d95400061360f72087655000186b7260021d95400061360f72c8365501c984e874cb20d954000d1325d524c9655000144e9321972195400051364c865c8655000146691219721954000519644865c8655000142e96a1172195400050b259845c8655000184e8660d721954000613219835c8655000190e8460d72195400041ba62635c865500014689660172195400064a611805c865500019498360172195400045a660405c8655000146a96101721954000613a0d72988655000184d835ca62195400060be1172588655000184e835c862195400061360d72188655000186572a046219540006195c981188655000182e865cb42195400060b21972508655000144f97d8932195400051365c624c8655000164591189321954000583a5b424c86550001868865c920195407ce9221932480655000192b75608705514000e13e1d524cb635000106d92a1f6558d4000549648655c743500014349654971d0d4000741549325c74350001d215248171d0d40007604c9205c7435000182c766086550d40006131cd82195615000106d981c865585400051364865dcd615000106e9819772585401b60b9d182194615000150d9219573d054000507259525cf415000190d8254973d054000662609205cf4150001d095248173d05400041b648865d6415000106f9261f65905400058964865d85415000142d92195748c5403de4add5821d1505000131993e0554541404970c1d951505505000782e76608659014065523251724c9651019560c9454932594407c51365e724c9651019560c945c9325944000703e51724c965101efc0c945c932594407bf03d01724c965101efc4a405c932594407bf12501724c9651000184d874cb21594400061360d72085651000184d874cb2059440656232117254963101ef44d979c95258c4000703e117254963101f1c0c845c95258c407c703d0172549631000184d855cb2158c400061361d520856310001a0d845482158c400069254980085631000184d8754b2058c400051364f705d562101f144d979d5735884065523251755cd6210001c0f945d573588407bf03251755cd62101efc0f405d573588407bf12901755cd62101efc49405d5735884000513657705cd621000184d855cf71588400060b611751c56210001869805d47158840006135d5831c562101eb64595949329844
  | 3 => 0x510058364e725496494593a2481549325925100583654724c96494401685911c93259251005a2640724c964945e9e048154932592517a781c41524c96494401e0552e0532592510068360d52c816494401a0d854cb205925101d19245725496394593a44815493258e516b7119c5524ca609440142d9215174181510050b648855d0605440143990215741815100513648545cc60544014599015173181510051a640545c8605440184d8560d721815100613e1d524c8605440184d8754932181517bf039d1524c86054401c0d7454932181516b7115c5524c8605440344c97549325974165583251524c965d05e9c0c74549325974100613615721c963d059588c845c95258f417bd1365e7254963d040160d949c95258f4100703e117254963d05f1c0c845c95258f417c703d017254963d040184d855cb2158f410061361572c8163d040184d8754b2058f4100e3221d3248160d040184d835c872596410061360d729096590593864815c932596417ad1365e724c96590401645919c932596417a711205724c965905e9c47105c93259641007115cb814c9659040184d835cb20596410061361d32c81659040384c875493258e4164e91205524c963905e9c44715493258e4100e1a21d5248160905e9c0d7454932d954100d1325d524c965505d360c94549325954177f115c5524cb63505253149854d43545413354525d5350d51504019148754d435454100613615835c8605040144f9754932181410051365d524c8605040184f8754932181410061361d524c8605040382c8754942592310058364854591538c401619901516454e316a7119c5524ca608c40386887549205823165523a53724cb654c5f9a448154932d953100e1321d524c9654c5f7a4481549325953100513648315d7644c401459900c575d913101c1ba637254b644c401854815d532d913100631205724cb644c40144f9754932d91310051365d524cb644c5f5a448154932d913100e1321d524c9644c5d5a4481549325913100513648315d4604c401459900c5751813100523648315d0604c401499900c5741813100613615835c8604c4014c49160d721813100532642315c8604c4010cd980c5721813100532640315c8604c401854815d5321813100625205744c8604c4018c4815c9321813100513e5d524c8604c40144d9754932181317bf039d1524c8604c401c0d7454932181317b691205524c8604c5a9c4571549321813172703dc9325925494001c49624c9709525064d1924572549639400144d9215373586500051664054dcd61940050cc985c9325865000613a1d524c9619400184c87549325865000583654424cb64540016859110932d9150005a2640424cb645400344c97549325974000685615430c561d0001a85436083158740006a450d800c561d
  | 4 => 0x400024000000100000008110000d00016000090080a02c0600c0000c0c008040340000001008070001c00c0000012008030200a0480b00000000000080f0000200c00020110041400c000040200002008010080300809000038c4874c921586546b7039d1524ca60950038c8874c9205825400692e1532481609519346691dc952d8d547fd83251524cb635500144d9215173d855400516640545cf615500181c845cd52d85540060b2117254b61550050ce98dc932d855400613e1d524cb615500184d8754932d85547f583251524cb615500144d92151731815400516640545cc605500142c9461572181540051a642545c8605500106d9815172181540051a640545c8605500184d8560d72181540060721173548605500182c845c9521815400613e1d524c8605500184d8754932181547cd83251524c860551adc0d7454932181547a7119c5524c860550014659215171181540051c640545c4605500143494549711815400711549325c460551a944d9754932d915300551648315c65454c01551900c571951536b61361d524cb6154c0142d9215174181530050b648855d06054c0143990215741815300523648315d06054c01499900c574181530041b660545c86054c0146990151721815300613615835c86054c010cd980c5721815300532640315c86054da944d9754932181536b61361d524c86054defc0e745493218153007035d1524c86054de9c4671549321815300531648315c46054c014659215171181530051c640545c46054c014c59220d711815300534640835c46054c01c45524c9711815301523251724c965d0d9560c9454932597437ad91e5d524ca61d0deb6459754932987437be91e11524ca61d0defa458454932987437a7819d1524ca61d0de9e057454932987430069160d52c8261d0c01a45854cb20987430069161532c8561d0c01a45835482158743006985498008561d0c01625941c952587430059164c7254961d0c01661901c9525874300591656724c961d0d9568494549325874300781e51524c961d0defe049454932587437bf81d01524c961d0c01a458354b20587430069161532c8161d0da9c0e74549329834300d1325d524c96550dfb60c94549325954300513648315d46050c01459900c5751814300613615835c86050c014c9900c5721814300513e5d524c86050c0144d9754932181436a7035d1524c86050de9c4671549321814300531648315c46050c014c59220d711814300534640835c46050c01c45524c971181437be83e1d524ca64945efa0d8754932992517ad83e45524ca64945eb60d9154932992517a7819c5524ca64945efe057154932992510068360d52c826494401a0d854cb20992510068360d52909649440160d951093259251005a2640424c964944018a97260072592
  | 5 => 0x430000003800006c258000000f22805891a1d324e01ce90003c26203e03114a6488180000000083113000000a58003780000019a1dc000001fd44a208ce8002f4000000b90000005f97c0002dc0019020e000000022543cc001d40007a07a0000527091089a08c8dc001543ee2900c896136074198000001d8f58000004f91780029e0d86504330e000da0b8000000350af18265488000210000458b30001f4d3800212000000000000006d8003c800000000000000000001c28646496f1540f0000000000000000000000000000024000001de00045c6a1212a6000af0003920011c93d0001f8ed864016020d61a235a8d8008472764991011a0ac1046415f2b200000000316000000000008a51f0003ca7d8368000ae000c08ab14e09c0016a39e334978f639c0011e05d000000bf0fb0806a44a01e164694bd9f001c5747d0000003180021c44e168150001980007c800000000000002907680b00021623113000000000820f00005e4df800000000fa9573422c4250d62e8300000000ee0e80016c0a04b8000650000000000037459c0000023627c000931aa6781c8000a2150e515800000000105000800d192b2d20000000019e73000070300478000000005a00000040c000e30000b6001070003b0000000003a25400011100000000095084000e09b80006080001c0a60004500009e000000000007a8a6800124000a20000004a40011d0960000000018e0000004e0006dcff8004166f80501f2da8489902f0ea1ec742130006b8f600037a0003c00047a1d000000000090000ea0000000001045a1b80480000030c4e0000002a4000003882e80000000a000000000000000000f2c800000000000000000000cc2d83405c3f6494000b441e200020000b24cca380046a6611981119c370f3a2c474000b58723a000c9a9ed00067d069b93604fcae08e10a2b8fc0000684643f8000005b9150001a60002c2110460009c80010e7e4000260003600006700000041800408000000000002241603d00000000000000000000000008140021738000022a2b07e23ca31384180840000000088cd20613f435c7e000284000000173be001040003dc000511164280010a8001a20b48e0552e47c41802b08887cb996521c6c45e00038a000001e000018cc7835000180191a81ee618fe0912ee1cca49830004c400000000804001a6000758d009909250d05000000004010000f0000300407018030000301c0000801000020000501c000000000c0400001000020000600801000010000100801000010000003c0101c00014000000600800004000040a02800000030101400005000060340008c000000d02c0000003014030000000001004000080400c00000020240202c070100200c0401800008060300400801008030000105400004090000000c00
  | 6 => 0x1b22e0000000003660000015b0005c4000001c81bcf922e312000e59f32ea8a0001e30000010180030a4a0d580000081c001c71604f0db1f40000007e838000000e40790364d1189d90004e800000000368b18cb448000388000000009b8a1000000be800332000891cd0000000015500043c000f802a2f862800436754110fe18400000084000824cb1452a23fc000e704000051818000000000e5000068000e90007a47a89e31838c4c1010266508112d2400dceb8000001e8c982e0006380008d0000009b0000006bc9219c4347f8ee800000000000000900008685e3de398710c422a2ec001b53360000009d23048cf310a40400000000000000860004645d80000042c17c000a02c001800152000374a08ad0000000a000354788068000003409121e12e2205a8280008ec8a1660002400004d1b2538bc0623221a45315610265cc694a0005fcdd8000000f877a1d1da6108018a2c2840e1a22470860060d223e0947594c1e23b0ad0de00037c5e8ac460000358003b82a02903b000000980000980
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1e000010e6800e00000003c009820a2c220220031c2e7401012006144601080002001914006802400000300cfa23654b000000000010004000218300503340422e6a96c2aa002829a02117254b61550018064a30ea9265b0aa800a032918560d721815400503340422e6a90c0aa002829a02117254860550018064a30ea9264302a80090c68094549711815400580948a9264b88c0aa002851a0205754cb644c401460d0102b9265b226200c112059754932d913100608b0a48b06b90c098802851a0205754c8604c401448d0102ba2643026200a30680815c9321813100608902cbaa4990c098803804815d1524c8604c401422d090cc1ae432a8000a03a9a8460d72195400060912cc1b00b90caa0002c04a6549325c743500018064b304a92e7a0a8000a0329d824c965500400060192ec12a4b1a802000280ca761583589401000160253aa4992c2a008000a03690866157218d1000608d2cc2d02b90c68800304896615805c86344001a024b2a4992e928a2000c11259824c975905100060892ec1264b2a20080034049754932591100400142253b04a92c68802000c1125d8560d6244010
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x480060200a000005009b02518754932d8554005009b0251875493218154004c01b0291524c97118154005041b02059754932d9131005041b0205975493218131005801b0205745493218131
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4e
  | 9 => 0x124b
  | 10 => 0x5
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94e
  | 14 => 0x124c
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138c
  | 18 => 0x138e
  | 19 => 0x9cb
  | 20 => 0x9ce
  | 21 => 0x12cb
  | 22 => 0x12ce
  | 23 => 0x10b
  | 24 => 0x10c
  | 25 => 0x10e
  | 26 => 0x130b
  | 27 => 0xa0b
  | 28 => 0xa0c
  | 29 => 0xa0e
  | 30 => 0x130c
  | 31 => 0x130e
  | 32 => 0x180b
  | 33 => 0x180c
  | 34 => 0x180e
  | 35 => 0xa4b
  | 36 => 0xa4c
  | 37 => 0x134b
  | 38 => 0x134c
  | 39 => 0xb4b
  | 40 => 0xb4e
  | 41 => 0x144b
  | 42 => 0x144e
  | 43 => 0x28b
  | 44 => 0x28c
  | 45 => 0x28e
  | 46 => 0xb8b
  | 47 => 0xb8c
  | 48 => 0xb8e
  | 49 => 0x148b
  | 50 => 0x148c
  | 51 => 0x148e
  | 52 => 0x184b
  | 53 => 0x184c
  | 54 => 0x184e
  | 55 => 0xbcb
  | 56 => 0xbcc
  | 57 => 0x14cb
  | 58 => 0x14cc
  | 59 => 0xe8b
  | 60 => 0xe8e
  | 61 => 0x18cb
  | 62 => 0x18ce
  | 63 => 0xecb
  | 64 => 0x104b
  | 65 => 0x104c
  | 66 => 0x194b
  | 67 => 0x194c
  | 68 => 0x94053
  | 69 => 0x124953
  | 70 => 0x95253
  | 71 => 0x9c953
  | 72 => 0x949d3
  | 73 => 0x12c953
  | 74 => 0x12ca
  | 75 => 0x952d3
  | 76 => 0xb4953
  | 77 => 0x94b53
  | 78 => 0x144953
  | 79 => 0x95453
  | 80 => 0xb8953
  | 81 => 0x94b93
  | 82 => 0xb8956
  | 83 => 0x148953
  | 84 => 0x95493
  | 85 => 0xbc953
  | 86 => 0x94bd3
  | 87 => 0x14c953
  | 88 => 0x954d3
  | 89 => 0xca
  | 90 => 0x139253
  | 91 => 0x9d253
  | 92 => 0x1249d3
  | 93 => 0x12d253
  | 94 => 0x1252d3
  | 95 => 0xb5393
  | 96 => 0x138b53
  | 97 => 0xb9393
  | 98 => 0x138b93
  | 99 => 0xb9396
  | 100 => 0xbd393
  | 101 => 0x138bd3
  | 102 => 0xe8a
  | 103 => 0xeca
  | 104 => 0x12c9d3
  | 105 => 0x9d2d3
  | 106 => 0x14c
  | 107 => 0xb49d3
  | 108 => 0x9cb53
  | 109 => 0xe89d3
  | 110 => 0x9ce93
  | 111 => 0xec9d3
  | 112 => 0x9ced3
  | 113 => 0x198c
  | 114 => 0x1452d3
  | 115 => 0x12d453
  | 116 => 0xa0113
  | 117 => 0x130a13
  | 118 => 0xa1313
  | 119 => 0xa4a13
  | 120 => 0xa0a53
  | 121 => 0x134a13
  | 122 => 0xa1353
  | 123 => 0x134d
  | 124 => 0xb8a13
  | 125 => 0xb8a14
  | 126 => 0xa0b93
  | 127 => 0x184a13
  | 128 => 0xa1853
  | 129 => 0xe8a13
  | 130 => 0xa0e93
  | 131 => 0x18ca13
  | 132 => 0xa18d3
  | 133 => 0x104a13
  | 134 => 0xa1053
  | 135 => 0x194a13
  | 136 => 0xa1953
  | 137 => 0x14d
  | 138 => 0x181313
  | 139 => 0xa5313
  | 140 => 0x130a53
  | 141 => 0x135313
  | 142 => 0x131353
  | 143 => 0xb9813
  | 144 => 0xb9814
  | 145 => 0x180b93
  | 146 => 0xbcd
  | 147 => 0xe9813
  | 148 => 0x180e93
  | 149 => 0xecd
  | 150 => 0x105813
  | 151 => 0x181053
  | 152 => 0x134a53
  | 153 => 0xa5353
  | 154 => 0xbca53
  | 155 => 0xa4bd3
  | 156 => 0xeca53
  | 157 => 0xa4ed3
  | 158 => 0x168e
  | 159 => 0x104a53
  | 160 => 0xa5053
  | 161 => 0x195353
  | 162 => 0x135953
  | 163 => 0x178a
  | 164 => 0x19cc
  | 165 => 0x17ca
  | 166 => 0xe9453
  | 167 => 0x144e93
  | 168 => 0xed453
  | 169 => 0x144ed3
  | 170 => 0xbcb93
  | 171 => 0xb8bd3
  | 172 => 0x14cb93
  | 173 => 0xb94d3
  | 174 => 0xe8b93
  | 175 => 0xb8e93
  | 176 => 0x18cb93
  | 177 => 0xb98d3
  | 178 => 0xbd493
  | 179 => 0x148bd3
  | 180 => 0xe9853
  | 181 => 0x184e93
  | 182 => 0xecbd3
  | 183 => 0xbced3
  | 184 => 0x16ce
  | 185 => 0x194bd3
  | 186 => 0xbd953
  | 187 => 0xece93
  | 188 => 0xe8ed3
  | 189 => 0x1a8c
  | 190 => 0xce
  | 191 => 0x194ed3
  | 192 => 0xed953
  | 193 => 0x178e
  | 194 => 0x19cd
  | 195 => 0x1a4d
  | 196 => 0x4953
  | 197 => 0x170a
  | 198 => 0xcca
  | 199 => 0x56d3
  | 200 => 0x1a0a
  | 201 => 0xd4a
  | 202 => 0xccd
  | 203 => 0xd4d
  | 204 => 0xb49c95b
  | 205 => 0xb4949db
  | 206 => 0x9c94b5b
  | 207 => 0x1452c95b
  | 208 => 0x144952db
  | 209 => 0x12c9545b
  | 210 => 0x94b96
  | 211 => 0xd52d2
  | 212 => 0xd4c
  | 213 => 0x1a0c
  | 214 => 0xcce
  | 215 => 0x170e
  | 216 => 0x138b96
  | 217 => 0xa0b94
  | 218 => 0x10a13
  | 219 => 0x170d
  | 220 => 0x1a0d
  | 221 => 0x11a93
  | 222 => 0x104a4a1b
  | 223 => 0x104a0a5b
  | 224 => 0xa4a105b
  | 225 => 0x19534a1b
  | 226 => 0x194a135b
  | 227 => 0x134a195b
  | 228 => 0xcd355
  | 229 => 0x180b94
  | 230 => 0x148b94
  | 231 => 0x16cb96
  | 232 => 0x1a8b94
  | 233 => 0xccbd5
  | 234 => 0xd4e92
  | 235 => 0xccb96
  | 236 => 0x170b96
  | 237 => 0xcd856
  | 238 => 0x171856
  | 239 => 0xd4b94
  | 240 => 0x1a0b94
  | 241 => 0xd5494
  | 242 => 0x1a1494
  | 243 => 0x184b96
  | 244 => 0xd4cd2
  | 245 => 0xccd52
  | 246 => 0xd40d2
  | 247 => 0xd4cd5
  | 248 => 0xccd55
  | 249 => 0xcc155
  | 250 => 0xd5792
  | 251 => 0xd4ed2
  | 252 => 0xd57d2
  | 253 => 0xcced5
  | 254 => 0xcd9d5
  | 255 => 0xcda55
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2277
  | 6 => 6426
  | 5 => 3708
  | 4 => 575
  | 3 => 36
  | 2 => 6
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (93357+((h/759+packedAt gbK7 (84249+(h % 759)*12) 12) % 2733)*13) 13
  | 6 => packedAt gbK6 (338436+((h/2142+packedAt gbK6 (308448+(h % 2142)*14) 14) % 9331)*14) 14
  | 5 => packedAt gbK5 (234840+((h/1236+packedAt gbK5 (218772+(h % 1236)*13) 13) % 5384)*13) 13
  | 4 => packedAt gbK4 (42160+((h/191+packedAt gbK4 (40250+(h % 191)*10) 10) % 919)*11) 11
  | 3 => packedAt gbK3 (2988+((h/12+packedAt gbK3 (2916+(h % 12)*6) 6) % 57)*7) 7
  | 2 => packedAt gbK2 (560+((h/2+packedAt gbK2 (552+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x87c3f0ffe30c78e0fe1fc0fe0fc01278474cf
  | 1 => 0xf8fc3f0e1c0f8f00e3e1ff0ff1c32da1a4b33
  | 2 => 0xff003ff01ff00fff03fe000ffe2431c638c3c
  | 3 => 0xffffc0001ffff00003fffff000383e07c0fc0
  | 4 => 0xf000000001ffffffffc000000003fc007ff000
  | 5 => 0xfffffffffe000000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x401200001020200240020000000801045
  | 1 => 0xa104411044804890448209404c18304a0a4112
  | 2 => 0xab222aa085900252035402292c24314208c28
  | 3 => 0x4cdaa888117a9200a13992ae024383a0740e80
  | 4 => 0x6000000001a4e4c8c98000c4040894005f6000
  | 5 => 0x8f6f33cc9c0800010011030818936bff000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffeeeafefaeee8ffffeeeafefaeee8ffffeeeafefaeee8ffffeeeafefaeee8ffffeeeafefaeee8ffffeeeafefaeee8ffffeeeafefaeee8ffffeeeafefaeee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27929
namespace PEqualNP.Outside.L_meta_27929
open PEqualNP.Outside.L_meta_27929.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
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
theorem bs1_4_0 : Interval s1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 13 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 8 := bs2_2_0
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
theorem bs2_3_96 : Interval s2Atlas 3 96 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 102 := (concat (concat bs2_3_0 bs2_3_32) (concat bs2_3_64 bs2_3_96))
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
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 725 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128))) (concat (concat bs2_4_160 (concat bs2_4_192 bs2_4_224)) (concat bs2_4_256 (concat bs2_4_288 bs2_4_320)))) (concat (concat (concat bs2_4_352 (concat bs2_4_384 bs2_4_416)) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512))) (concat (concat bs2_4_544 (concat bs2_4_576 bs2_4_608)) (concat bs2_4_640 (concat bs2_4_672 bs2_4_704)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 682 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 (concat bs2_5_192 bs2_5_224)) (concat bs2_5_256 (concat bs2_5_288 bs2_5_320)))) (concat (concat (concat bs2_5_352 bs2_5_384) (concat bs2_5_416 (concat bs2_5_448 bs2_5_480))) (concat (concat bs2_5_512 (concat bs2_5_544 bs2_5_576)) (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 16 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 16 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bgb_2_0 : Interval gbAtlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 6 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 36 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_544 : Interval gbAtlas 4 544 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 575 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)))) (concat (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)) (concat (concat bgb_4_416 bgb_4_448) (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)))))
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
theorem bgb_5_3680 : Interval gbAtlas 5 3680 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3708 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)))) (concat (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)))))) (concat (concat (concat (concat (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)) (concat (concat bgb_5_1952 bgb_5_1984) (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 bgb_5_2496))) (concat (concat (concat bgb_5_2528 bgb_5_2560) (concat bgb_5_2592 bgb_5_2624)) (concat (concat bgb_5_2656 bgb_5_2688) (concat bgb_5_2720 bgb_5_2752))))) (concat (concat (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976))) (concat (concat bgb_5_3008 (concat bgb_5_3040 bgb_5_3072)) (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)))) (concat (concat (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296)) (concat (concat bgb_5_3328 bgb_5_3360) (concat bgb_5_3392 bgb_5_3424))) (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680)))))))
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
theorem bgb_6_6400 : Interval gbAtlas 6 6400 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6426 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))) (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944))) (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))))))) (concat (concat (concat (concat (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744))) (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 bgb_6_3968))))) (concat (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))) (concat (concat (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448)) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)))))) (concat (concat (concat (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))) (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)))) (concat (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))) (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))))) (concat (concat (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760))) (concat (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856)) (concat (concat bgb_6_5888 bgb_6_5920) (concat bgb_6_5952 bgb_6_5984)))) (concat (concat (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080)) (concat bgb_6_6112 (concat bgb_6_6144 bgb_6_6176))) (concat (concat bgb_6_6208 (concat bgb_6_6240 bgb_6_6272)) (concat (concat bgb_6_6304 bgb_6_6336) (concat bgb_6_6368 bgb_6_6400))))))))
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
theorem bgb_7_2272 : Interval gbAtlas 7 2272 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2277 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))))) (concat (concat (concat (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248)) (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))))) (concat (concat (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824)) (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)))) (concat (concat (concat bgb_7_2016 bgb_7_2048) (concat bgb_7_2080 bgb_7_2112)) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 7 zero,inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 3 zero,inputs.getD 6 zero,inputs.getD 4 zero,inputs.getD 1 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xffffffffffffffffffffeeeefefeeeecffffeeeafefaeeeaffffeeeafefaeee8ffffffffffffffffffffeeeefefeeeecffffeeeafefaeeeaffffeeeafefaeee8
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
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27929.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[8,7]⟩,⟨.or,[1,3]⟩,⟨.or,[6,7]⟩,⟨.and,[10,11]⟩,⟨.or,[1,2]⟩,⟨.and,[13,5]⟩,⟨.or,[0,7]⟩,⟨.or,[4,6]⟩,⟨.and,[15,16]⟩,⟨.or,[9,12]⟩,⟨.or,[18,14]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27929

open PEqualNP.Outside.L_meta_27929 in
theorem PEqualNP.Outside.L_meta_27929 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 5, 2, 5, 0, 6, 1, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
