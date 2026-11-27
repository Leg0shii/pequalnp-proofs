import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27845.Model
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


end PEqualNP.Outside.L_meta_27845.Model

namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
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

def SBf (j : Nat) : Nat := [6, 7, 6, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_27845

namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x6500ee32ed32bf40bd40
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
  | 4 => packedAt s0K4 (67+((h/1+packedAt s0K4 (64+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3c38f1e3f3fc7ffc631c38e0f8fc3fff21327f
  | 2 => 0x3fc0fe03fc7f8f1f83e03f00ff1fc70f463d93
  | 3 => 0xc000fffcff800fe3fc003fff1fe007f087ce1c
  | 4 => 0xffff0000fffff003ffffc0001ffff800f80fe0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x6011804122084004105102820242184211025
  | 2 => 0x88a2214a2948182282222912490a822a462492
  | 3 => 0x819444c241192205a4008a461a419462824e18
  | 4 => 0x11100490801002492848800414911040880b40
  | 5 => 0x222089000a624c92539334988002208c75b000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xffffffc0fcfcccc0ffffffc0fcfcccc0ffffffc0fcfcccc0ffffffc0fcfcccc0ffffffc0fcfcccc0ffffffc0fcfcccc0ffffffc0fcfcccc0ffffffc0fcfcccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x383c0324c00b280c01b9400b1d804e7c2a348a8ab42e018a116d510334940990ebdc9100b4000086c00000800385ca460e202093012ac9b33cd810014e86983a0c3848716180000400000061c0000438009b7290876d5210eeca221dd54443bd28087795010ebca6215754c42bb28885755110af4a0215e54042bd286657950ccaeca3195d546329faa2653c544caf4a1a0de54341b7294836d52906bea6a0d714d419f2a0633d540c6dca418db54831bd2806379500c6bca790d754f219f2a4433d54886f6a090de14121bb28e817551d02bca7205754e40b7a92816c52502dca5985b54b309f2a4613d548c2eea2985d145309f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
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
  | 4 => packedAt s1K4 (1760+((h/20+packedAt s1K4 (1620+(h % 20)*7) 7) % 73)*7) 7
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe3c7c7f1fe3ff8e38e0e383f1f83ffe61339f
  | 2 => 0xf03f807fe3ffe3f03f00fc03fe3ff83e863cf3
  | 3 => 0x3fff8ffc03fc7fc000fffc7fc03fc107cf1c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x404610c15105400a182a40a0a0490d18611185
  | 2 => 0x288849228a4204502110a449121490a4862432
  | 3 => 0xa511282408c880b4400429185482a285024e18
  | 4 => 0xc40132484080c9268a46001069230309280bc0
  | 5 => 0x8224000931312493498d26200040430d5b000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0ffffffa0faf0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x182020df32dd32bf41bd41
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (67+((h/1+packedAt s2K4 (64+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3c38f1e3f1f8f8fce38e0c70f8fc38ff31370f
  | 1 => 0x3fc0fe03fe7fff1f03f00f80ff1fff0f4239f3
  | 3 => 0xc000fffcff80ffe3fc000fff1fe03ff083ce3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8681184615215100a182a414282488a6311305
  | 1 => 0x82221082840802202110888410a1408422052
  | 3 => 0x1144480401220054400412212412240804c28
  | 4 => 0x919004d28410324968a460021c918262940f80
  | 5 => 0x222089000964c49293498e4c8002048c6bb000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xffffff88eeccee88ffffff88eeccee88ffffff88eeccee88ffffff88eeccee88ffffff88eeccee88ffffff88eeccee88ffffff88eeccee88ffffff88eeccee88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
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
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c06480273e108151a9800046252a150187af400170002640003c5ce82480088536507082c6910c262cc000e2952b5a000293800010b5c300b403200580000ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x7d3b1490c733d008003d259b4166a121d064091d1e47e372790494672d86c42640f9c82c3c2e05cb081130f8107c270bc70801c9b8566314174b411021150e500e90cb2530f134bc220000040000019400471184058830d01ccc613400c666b420b84a0c3c0280000300c0d87f2a000900000000ee001a8000000310b43229200382a000009c0c46001c0001202800ae0024870a27b42800ac551d8008400000d0543126000260d001c42882221bc1e01001d4d27e2f8606c1101163600230f010201001701080300081506021149041801020009000712000000030a00002d020300080f02b7294876d5290e7ca721eb94a43d6a94873d5190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb94843d6a9087b65110e7aa221ed544439aa8887ba5010e7aa021ee540439ca80875e5390abaa7216710f329f2a4653d548cb5ca9196b55232b6a9c65ae438cb5887194fd51329e2a2659c434cb5ea8996b15132e7a9a65cf434cb5c86996b10d32e621a658c434cadca4194f94f41d719683ad32d067aa1a0cf552419e29a83ae325075a64a0edd45419fa82833e541067ea998cf15331b7296636d52cc79a6598cf952319eaa463b5418c67ea898cf15131e699263b5414c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d548867ca810cf55021af298435d53086f4a010de540219f29e81ae32d035a65a04f547409eaa4813c535035c64a06b4c9409fa8a81bb505027ca8204fd53309e2a6616e52cc2daa598734cb309f2a4613d548c37281184fd51309e2a261cd324c37280984f950309eaa0616e520c2daa4185d94430baa88613e548827aa9104f950209eaa0415e53082baa6105d94420baa88413e54c427aa9884f952109eaa4213e544427aa8885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30000000000000000001e1800050614800048a80567802d0044c8d3e0801b00708005c10b1d0090720601c431002509300b002746991170a2c500060178028052800069500001000280024000000188840000280a358a5310f265254443c95495110f315194043ca9495010f295254043cc9455010f315154043a558443cca996010f32a9584438caa96010e32a5584434ca996010d32a3993534ca2e6590d32a398e434ca2e6510d32a9584434caa96010d32b1584434cac96010d32a3994434cb0e6510d32e1984434ca8d6110d32e1584434ca856110d32e2980434ca8d6010d32e2580434ca896010d328e580535070c534c9418e58054cc70c544cb31c3151324c6346550531e14c9414c6356114d40c314d32502356115330c315132cc30c544c9308e195404c38932501308718d544424d6314910d454d10043615244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x200000404a720cc2805a05866010d32d04c2b00869968161580434ca84b80a699283425c0544cb31c08ca9928298d057114d3250282b88a899661821953250130
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
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (456+((h/3+packedAt s4K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e1e3c7fc7f1fe3f1c63838fe3f1f87f10f4cf
  | 1 => 0x1fe03f8ff8fe3fc7e07c03f1fc7e3f87233b33
  | 2 => 0xe0003ff3ff003ff8ff8003fe3f803ff8c3cc3c
  | 3 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x42804600424208400820908240910822105045
  | 1 => 0x84088840908050084044211084281204212112
  | 2 => 0x15511292424a401b4804a242904a550c28c28
  | 3 => 0x8440122002004922509080032448110440e80
  | 5 => 0xd198224836c93924da7273c900090666bbf000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8ffe8ffe8eee8eee8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x427928a0ea0c1f064008e1e586802680017342c1064e009294410a2a4c00e1500011800a2158022252003674c8c0004000b080007045000040ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe869b95981305292c80aa99a8929c248794902b820c012083a392112d9a01a817a7841f001e8022a008232d16a6060a0d00070000002c0489259a88801f8d8f8c8000108b170580000a98800000000f1180270013829d8029a1a42b22190e25151c8016142a1e211d268b801b030980020c00580006c38406e09020a1008520841a91c5c00014243a1bd286877950d0edca521db54a43af29c855d5390abca6215754c42bb28885755110af4a0215e540429f2a6653d54ccb3ca9996755332aea9c65cf524cb9e84997310932af298655e53106baa620db94841b6a90837a50106f2a020cf950319eaa0636e520c6daa418de94031bca80635e53c86baa790f34cb219faa2433c544879a6490cf950219eaa0435e53086baa610de94021bca80435e53d02baa7a06794f40cea9e819f32d033a65a04f55240cf992819d3250376a0a04f95040dca06613e548c27aa9184f950309eaa0616e520c2daa4185d94430baa8861b9400c2bca7905754f20e6996413e548827aa9106e50220e699241b9404827ca8104f55020af298415d53082eca2105d544209f2a4213d5484372810857d4d10ae29a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6480af629cb0b400188874000088078e58254cca996095332a3993524cac56110932b2580424ca396015121c3151324864d6294f40a358a53d021d65ccb40a698f50503295250030cc545400c38932501209358853443185350110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2d00912e1326a499509701513248644b94c7a8281425c85350110
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
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf3c7e1c63cfe3f1f9c63c70e23f1fcf8e44cf
  | 1 => 0xf03f9fe07ff1fc7e3e07c780ffc7e1f1907b33
  | 2 => 0xffc01fff83fe007fc7f807ff03f801fe638c3c
  | 3 => 0xffffe00003ffff8007fff80003fffe007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x18602808444844200820c1428090849064045
  | 1 => 0x10080401008000804000408040420080001112
  | 2 => 0x22014848090049200a48012202904524208c28
  | 3 => 0x4411415a522940249754900a1324d424780e80
  | 4 => 0x88a21190402d924925a7264c980098095f6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8fefceee8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12454f12967a3178f428dc2c00d40000001c8012890006c0402b3c2c0283218fb06e21a2e36485334c1c83b06000322a0002d289cbba1ac42803a60e04263889a520698a011830000240cc0006081800c00a00027fd5007fe54007f55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42017fcc801fe32007f4c805fc32027fd44017f5100ff94401fd51005f54403fc5101ffd0403fe41007f50403fc41017fcc403fe31007f4c403fc31007fc8403fe21007f48403fc21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40017fcc001fe30007f4c005fc30007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x804005ffc802002fde4010017fe200800bfd1004005ff4802002fda4010027f9200800bff8804005ff0402002ffecb08016ff658400bff32c2004bf9961002ffacb08002fd658400bfe32c2005bf1961002ffec908016ff648400bff3242003bf9921002ffac908002fd648400bfe3242005bf19210067fea90802ffe5484001feaa4200bff1521002ffec708016ff638400bff31c2002bf98e1002ffac708002fd638400bfe31c2005bf18e10067fea70802bfe5384001fea9c200aff14e1005ffe870802bfe4384001fea1c200aff10e1002ffec508016ff628400bff3142009bf98a1002ffac508002fd628400bfe3142005bf18a10067fea508003fe5284001fea94200cff14a1005ffe8508003fe4284001fea14200bff10a10057fe6508003fe3284001fe994200aff0ca1000dfac308007ff5184003bfa8c2001ff9461000ffaa3080077d5184003fe28c2001ffd061000ffc8308007fd4184003fe20c2001ffcc61000ffc6308007fd3184003fe18c2001ffc861000ffc4308007fd2184003fe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfd2042005ff50210007f28108017fc408400bff9842005ff8c21002ff46108017fd3084001fc9842005ff0c21002ffe4108017fe208400bfd1042005ff48210007f24108017fc208400bff8842005fdc421000ff62108017fc108400bfc0842000ffd9510005feca88023fe65440097f32a2000ff59510005faca88023fc65440097e32a2000ffd9110005fec88801ffe64440077f3222000ff59110005fac88801ffc64440077e3222008ffd511003ffca888003fd544400ffe2a22000ffd8d10005fec68801bfe63440057f31a2000ff58d10005fac68801bfc63440057e31a2008ffd4d10037fca688003fd534400dfe29a2007ffd0d10037fc8688003fd434400dfe21a2000ffd8910005fec488003fe62440137f3122000ff58910005fac488003fc62440137e3122008ffd4910007fca488003fd5244011fe2922007ffd0910007fc8488003fd424400ffe2122006ffcc910007fc6488003fd324400dfe1922005bfd851000ffea2880077f5144003ff28a2001ff5451000efaa288007fc5144003ffa0a2001ff9051000ffa8288007fc4144003ff98a2001ff8c51000fec6288007fd3144001fa98a2001ff0c51000ffe4288007fe2144003fb10a2001ff48510007ea4288007fc21440037fb022008ffd411002ffca088003fd504400bfe2822007ffd011002ffc8088003fa4044001fea022000fe5011002ff8808801bff304400bff1822000fe8c110007fa6088003f9304400bfe1822000ffc811002ffc4088003fa2044001fe9022000fe4811002ff84088007ff1044003fd8822005ff8411002fec2088017fc104400bfa0822001fe04110
  | 1 => 0x3fd2188013fe10c4005bf9822002ffea110017fe508800bfea844005ff1422002ffe8110017fe408800bfd2044005ff50220007f28110017fc408800bff9844005ff8c22002ffa6110017fc308800bff9044005fbc822004ff64110017ff108800bfe0844000ffd9520005feca90053fe65480097f32a4000ff59520005faca90053fc65480097e32a4000ffd9120005fec89004ffe64480077f3224000ff59120005fac89004ffc64480077e3224014ffd512009ffca890003fd5448027fe2a24000ffd8d20005fec69004bfe63480057f31a4000ff58d20005fac69004bfc63480057e31a4014ffd4d20097fca690003fd5348025fe29a4013ffd0d20097fc8690003fd4348025fe21a4014ffd492004ffca490003fd5248013fe2924013ffd092004ffc8490003fd4248013fe2124012ffcc92004ffc6490003ee3248001fe9924000fb4c92004ff86490003ff61480017fb0a4011ff9852000dfcc290003fd6148023fe30a4001bf185200a7fea2900037f5148023ff28a4000ff54520006faa290047fc5148027ffa0a4011ff90520007fa8290047fc4148025ff98a4011ff8c520007fa6290047fc3148013ff90a4000fbc852008ffc4290003fd2148001f690a4009ff085200a7fea090017fe5048001fea824005ff1412009ffe8090017fe4048001fd2024000ff50120007f28090017fc4048025ff9824005ff8c120007fa6090017fc3048013ff9024009fec812002ffc4090017ee2048023ff8824005ff0412002ffeca10016ff650800bff3284004bf9942002efcca100127e650800bfeb284000bf5942002efaca100027d650800bfe3284005bf1942002ffec810016ff640800bff3204003bf9902002f7cc81000ebe640800bfeb204000bf5902002f7ac810002bd640800bfe3204005bf19020087fea81003ffe5408001feaa0400fff1502002ffec610016ff630800bff3184002bf98c2002fbcc61000ade630800bfeb184000bf58c2002fbac610002dd630800bfe3184005bf18c20087fea61003bfe5308001fea98400eff14c2007ffe861003bfe4308001fea18400eff10c2004dfcc410027ff5208013ff2904009ff5482004ff8a410027ff4208013ff2104009ff5082004ff88410027ff3208013ff1904009ff4c82004ff86410017ff610800bff3084001bf9842002fecc210006f6610800bfeb084000bf5842002feac210002f5610800bfe3084005bf18420087fea2100037f510801bff2884000ff54420006faa210037fc510801fffa08400dff90420007fa8210037fc410801dff988400dff8c420007fa6210037fc3108013ff9084009ff8842004ffa4210027fc210800b7f3004005ffd402002ffca010017fd500800bfe2804005ffd002002ffc8010017fd400800bfe2004005ffcc02002ffc6010017fd300800bfe1
  | 2 => 0x300fff8a49807bff424c001ff2126000ff509300f7f8849800bff324c005ef9926002ff8c930017fa6498003dd324c005fe1926000ffd8530005fec298077fe614c0037f30a6000ff585300eff8c298006fc614c03fffa8a6000dfd45300effca298003fd514c001bea8a601dff145300f7fe8298077fe414c001fea0a601dff10530017fe629800bdf314c005ff18a6002ff4c530007ba629800bfc314c001ff90a601dff88530007fa4298077fc214c0057fb02601fffd413002ffca098003fa504c001fea826000fe5413002ff8a09807bff404c00bff2026000ff5013002ff8809800bff304c005fd9826005ff8c13002fbc6098017fc304c00bee1826002fe0c1300effe2098017fc104c013ffb2e4009bfd972004ffccb90012fe65c8013feb2e4000bf5972004ff8cb90026fc65c8013ffb264009bfd932004ffcc99000efe64c8013feb264000bf5932004ff8c990026fc64c8039ffaa6401bff95320007faa99006ffc54c8013ffb1e4009bfd8f2004ffcc79000afe63c8013feb1e4000bf58f2004ff8c790026fc63c8039ffa9e401aff94f20007faa79006bfc53c8037ffa1e401aff90f20007fa879006bfc43c8013ffa964009ff94b2004ffaa590027fc52c8013ffa164009ff90b2004ffa8590027fc42c8013ff9964009ff8cb2004fdc6590027fd32c8001f69964009ff0cb2004ffec390027fe61c80037f30e4009ff58720005fac390027fc61c80037e30e401cffd4720006fea390067fe51c8001fea8e4000df547200cff8a39006fff41c8033ff20e4000ff507200cff8839006bff31c8033ff18e4000ff4c7200cff86390027ff21c8013f790e4009ff8872004ffa4390003ed21c8013fe10e401cffd432002ffca190003fd50c800bfe286401bffd032002ffc8190003fd40c800bfe206401affcc32002ffc6190003fd30c800bfe1864019ffc432002ff82190017ff658800b7fb2c4005ff99620025fccb10017fd65880017eb2c4005ff1962002df8cb10017ff648800b7fb244005ff9922001dfcc910017fd64880017eb244005ff1922002df8c910063ff548802fff2a44000ff552200bff8a910017ff638800b7fb1c4005ff98e20015fcc710017fd63880017eb1c4005ff18e2002df8c710063ff538802dff29c4000ff54e200b7f8a71005fff438802dff21c4000ff50e200b7f88710002fd6288031ffa944009ff94a20007faa510027fc528802fffa144009ff90a20007fa8510027fc428802dff9944009ff8ca20007fa6510027fc328800bffb0c4005ff9862000dfcc310017fd61880017eb0c4005ff1862002df8c310063ff5188001bfa8c4015ff94620007faa3100037d518802bfe28c4017ffd06200affc8310003fd418802bfe20c4016ffcc6200affc6310003fd318802bfe18c4009ffc86200affc431000
  | 3 => 0xe32a8005bfd914001ffea8a0097bf5450007ff2a28003ff5514001ff8a8a000fbc5450001ffb1a8000bfd8d40127fcc6a000afe6350001feb1a8024ff18d40015f8c6a0097ff5350049ff29a8000ff54d40127f8a6a000fff4350007dfa1a8003ff90d4001ffa86a0003bd4350007fe21a8000ffd8940005fec4a0003fe6250001feb128000ff1894004df8c4a0097ff5250001ff2928000ff5494012ff8a4a000fff4250007dfa128003ff9094001ffa84a0003bd4250007fe2128024ffcc940007fc64a0003fd3250049fe1928000ffd8540005fec2a008ffe61500037f30a8000ff5854011ff8c2a0006fc615004bffa8a8000dfd454011ffca2a0003fd5150001bea8a8023ff1454001ffe82a000fbf4150007ff20a8003ff505400077a82a000ffc4150049ff98a8023ff8c540007fa62a008ffc3150001ff90a8023ff88540007fa42a008ffc21500077fb028025ffd414002ffca0a0003fa5050001fea828000fe5414002ff8a0a000fff4050007fda028005ff9014002f7c80a0017fc405000bde2028003fe10140127fe60a0093fb305000bfe1828024fe0c14011ffe20a0017fc105000bffb2c6005bfd963002ffccb18012fe658c00bfeb2c6000bf5963002ff8cb18016fc658c00bffb246005bfd923002ffcc91800efe648c00bfeb246000bf5923002ff8c918016fc648c045ffaa46021ff95230007faa918087fc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bde438c005fea1c6000f750e30017f88718017ff628c00bff3146009bf98a3002ffac518002fd628c00bfe3146022ffd4a30007fca518003fd528c045fe2946021ffd0a30007fc8518003fd428c043fe2146002ffcca30017fc651800bfd328c005fe1946005ffd863002ffcc318006fe618c00bfeb0c6000bf5863002ff8c318016fc618c045ffa8c6000dfd4630107fca318003fd518c001bea8c6020ff1463010ffe8318083fe418c001fea0c6020ff10630017fe631800bfe318c005fe98c6002ff0c630007fe4318083fe218c001fe90c6020ff0863002dfcc118017ff508c00bff2846005fe9423002ffaa118003f9508c00bfe2846005ffd023002ffc8118017fd408c00bfe2046005ffcc23002fbe611800bfb308c00bfe1846005fe0c23002ffe2118017fc108c001ffb2a6000bfd95300fffcca98012fe654c001feb2a6000bf595300fff8ca98012fc654c001ffb226000bfd91300f7fcc89800efe644c001feb226000bf591300f7f8c89800efc644c03fffaa2601eff95130007faa89807bfc544c00b7fb1a6002ffd4d30017fca69800bfd534c005fe29a6002ffd0d30017fc869800bfd434c005fe21a6000ffd8930005fec498003fe624c001feb126000ff1893004df8c49807fff524c001ff2926000ff549
  | 4 => 0x16fc6194009ffa8ca004dfd4650027fca328013fd5194001bea8ca004ff14650177fe83280b3fe4194001fea0ca02cff1065016ffe63280b3fe3194001fe98ca02cff0c650007fe43280b3fe2194001fe90ca02cff0865002dfcc128017ff509400bbfa84a004fed425002ff8a128017f8509400bffa04a005ff1025002ffe6128017fc309400bff884a005ff0425002dfecaa8003ff64540017fb22a02bff9915001dfcc8a8003fd6454057fe322a003bf19150027fea8a8013fe5454057bf2a2a004ff55150027f8a8a80137c5454001ffb1aa000bfd8d50157fcc6a800afe6354001feb1aa02aff18d50015f8c6a8013ff5354009bfa9aa004ff94d50027faa6a80037d5354009fe29aa02bffd0d50157fc86a8003fd4354055fe21aa000ffd8950005fec4a8003fe6254001feb12a000ff1895004df8c4a8013ff5254009bfa92a004ff94950027faa4a80037d5254009fe292a02bffd0950007fc84a8003fd4254057fe212a02affcc950007fc64a8003fd3254055fe192a000ffd8550005fec2a80a7fe61540037f30aa000ff5855014ff8c2a8006fc6154009ffa8aa004dfd4550027fca2a8013fd5154001bea8aa004ff1455015ffe82a80a7fe4154001fea0aa029ff10550157fe62a80a7fe3154001fe98aa029ff0c550007fe42a80a7fe2154001fe90aa029ff08550025fec0a8013ff5054009fda82a005ff9415002efca0a8017fc505400bbe282a004fe1415015ffe80a8017fc4054055ff982a005ff0c15014ffe20a8017fc105400bffb2c8005bfd964002ffccb20012fe659000bbf32c80049f9964002ffacb20002fd659000bbeb2c80009f5964002ff8cb20016fc65900077eb248003ffd524001ffca92000ffd5490007fe2a48005ffd8e4002ffcc72000afe639000bfeb1c8000bf58e4002ff8c720016fc6390051ffa9c8026ff94e40007faa72009bfc5390007ffa1c8003ff90e4001ffa872000ffc439000bffb148005ff98a4004dfcc520017fd62900017eb148005ff18a40147fea520003fe5290001fea948028ff14a4001ffe852000ffe4290007fea148003ff10a40137fe6520003fe3290001fe9948026ff0ca4002ffec320017fe61900037f30c8005ff58640005fac320017fc619000b7e30c8028ffd4640006fea32009ffe5190001fea8c8000df5464013ff8a32000fff4190007ff20c8003ff5064001ff8832009bff319004fff18c8000ff4c64013ff86320003ff219004fff10c8000ff4864013ff84320016fe609000bffa848005ff9424002ff4a120017fd5090001fca848005ff1424002ffe8120017bf4090007fda048005ff1024002ff08120017ff309004dfd9848005ff0c24002ff06120017ff109000bfe0848000ffd9540005fecaa0097fe65500097f32a8000ff59540005facaa0097fc65500097
  | 5 => 0x9321005fac990827fc64c84137e3264234ffd532119ffca990803fd54c8467fe2a64209ffd8f2104dfec790827fe63c84057f31e4209ff58f21005fac790827fc63c84137e31e4234ffd4f21197fca790803fd53c8465fe29e4233ffd0f21197fc8790803fd43c8465fe21e4201bf98b2104ffea590827fe52c8413fea964209ff14b2104ffe8590827fe42c8413f72164209ff50b21007da8590827fc42c8413ff9964209ff8cb2104fdc6590827fd32c8401f69964209ff0cb2100dfac390807ff51c8403bfa8e4201ff9472100ffaa3908077d51c8403fe28e4201ffd072100ffc8390807fd41c8403fe20e4201ffcc72100ffc6390807fd31c8403fe18e4201ff8872100fdc4390807f621c8403fe10e4201fb0872104ffec190827fe60c840b7f3064209ff58321005fac190827fc60c8469ffa864234ff1432119ffe81908cffc40c8465ff9864232ff0c32100ffe2190807fc10c8401ffb2a4200bfd952118ffcca90812fe6548401feb2a4200bf5952118ff8ca90812fc6548401ffb224200bfd9121187fcc89080efe6448401feb224200bf59121187f8c89080efc6448463ffaa24230ff95121007faa8908c3fc5448401ffb1a4200bfd8d2117ffcc69080afe6348401feb1a4200bf58d2117ff8c69080afc6348463ffa9a422fff94d21007faa6908bffc5348461ffa1a422fff90d21007fa86908bffc43484037fb124231ffd492104ffca490803fd5248413fe2924230ffd092104ffc8490803ee4248401fea124200fb5092104ff884908bfff3248413ff1924200fb8c921007fa6490803ed3248413fe1924201bfd852100ffea2908077f5148403ff28a4201ff5452100efaa290807fc5148403ffa0a4201ff9052100fec8290807fd4148401faa0a4201ff1052100ffe6290807fe3148403fe98a4201ff0c52100ffe4290827f72148403ff10a4201fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff1812102df8c0908c7ff5048463fe2824230ffd0121187f880908bfff304845ffe1824201ffc412100fee2090807fc10484097eb2ca005ffd925002ffcc92800efe649400bdf324a003af9925002ffac928002fd649400bdeb24a000af5925002ff8c928016fc6494009ffaa4a004ff95250027faa928013fc549400bffb1ca005ff98e50015fcc728017fd63940017eb1ca005ff18e5002df8c728013ff5394009ff29ca004ff54e50027f8a7280bbff439405bff21ca000ff50e5016ff88728017ff629400bff314a009bf98a5002ffac528002fd629400bfe314a004ffd4a50027fca528013fd5294009fe294a02effd0a50007fc8528003fd429405dfe214a02dffcca50007fc6528003fd329405bfe194a005ffd865002ffcc328006fe619400bfeb0ca000bf5865002ff8c328
  | 6 => 0x5bfa12a200df90951006fa84a88eb7c4254473bf992a200df8c951006fa64a88e77c3254403bfb0aa2019fd8551026eec2a88077f4154403bf20aa201dd9055100ef882a88077f3154403bf18aa201dd8c55100ef862a88077e2154403be10aa200dfd8151006fcc0a88037d6054401be302a23adfd01511d6f880a88e77f3054473be182a201dfc415100ef820a8803ff65504017fb2a8238ff99541025fccaa0803fd65504017eb2a8238ff19541025f8caa0806ff6450407ffaa28203ff9514101ffaa8a080ffc5450401ffb1a8200bfd8d411bffcc6a080afe6350401feb1a8237ff18d41015f8c6a08e3ff535046fff29a8200ff54d411bff8a6a080fff4350407dfa1a8203ff90d4101ffa86a0803bd4350407fe21a8200ffd8941005fec4a0803fe6250401feb128200ff1894104df8c4a08e3ff5250401ff2928200ff549411c7f8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe2128237ffcc941007fc64a0803fd325046ffe1928201bfd854100ffea2a08077f5150403ff28a8201fd9454100ffaa2a08077d5150401faa8a8200dd5454100ff8a2a0807ff4150407fba0a8201ff9054100f7c82a0807fc4150403de20a8201fd1054100ffe62a0807fe3150403fe18a8201ff8854100fec42a0807fc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028205bf181411c7fea0a08e3fc5050407ffa028203efd014101ff880a08dfff305046ffe1828201ffc414100ff820a0803ff654c4017fb2a6236ff99531025fcca98803fd654c4017eb2a6236ff19531025f8ca98803ff644c4017fb226235ff9913101dfcc898803fd644c4017eb226235ff1913101df8c8988dbff544c46bff2a26200ff551311aff8a898806ff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6202ff90d31017bc869880bfd434c401eea1a6202ff10d31007fec498802ff624c401ff3126200ff58931007f8c498826fc624c46dffa926200ff94931007faa4988dbfc524c46bffa126200ff90931007fa84988d7fc424c405ff9926202f7cc931017fc649880bfd324c401ee9926202ff0c93100dfec298807ff514c403bfa8a6201ff9453100feca298807fd514c403bea8a6200fd54531006eaa298807fc514c403ffa0a6201ff9053100ffa8298807fc414c403ff98a6202fdcc53100ffc6298807de314c403fe18a6201f70c53100fe86298807fe214c403fe10a6200ffd8131005fec098803fe604c401feb026200ff1813102df8c0988dbff504c46dfe2826235ffd01311aff8809880bff304c405ef9826202ff0c13100ffe2098807f7104c403fe0826209ffd972104dfecb90827fe65c84097f32e4209ff59721005facb90827fc65c84137e32e4209ffd932104dfec990827fe64c84077f3264209ff5
  | 7 => 0x990ffff544c87dff2a26400ff551321f7f8a899026ff634c805ffa9a643ff7d4d32017fca69900bfd534c805fe29a6402f714d32017fe869900bfe434c805ef21a6402ff50d32007ba869900bfc434c8057fb12643fffd493204ffca499003ee524c801fea926400fb5493204ff8a4990fbff424c87df7a126409ff90932007fa8499027fc424c87df62126402ffcc932017de6499027fe324c813ef1926409ff0c93204fb8649900bec324c801ffb0a6400bfd85321effcc299006fe614c801feb0a643dff1853200df8c2990ffff514c87bff28a643dff145321f7fe82990f7fe414c87bfe20a6402ffcc532017be629900bfe314c805fe18a643dff8853204ff84299003ff604c8017fb026400ff98132007fac099003fc604c80b7e302643fffd41321fff8a0990fbff404c87dfe2026402ffcc132017be609900bfc304c87bff882643dff04132026fec9a88137e64d4409beb26a204df19351026fec7a88137e63d4409beb1ea204df18f511e6fe87a88ef7e43d4401bea1ea23bdf10f51026fec5a88137e62d4409beb16a204df18b511e6fe85a88037e42d4401bea16a23cdf10b511defe65a88037e32d4401be996a23bdf0cb5100cfac3a88077f41d4403bf20ea201df1075100efe63a88077e31d4403be18ea201df8875100ef843a88137f60d4409bf306a204df58351026f8c1a88f37f40d4479be206a23bdfcc3511def861a88077f10d4403be086a201bfd9551007fec8a8802ff6454475ff322a203bf99151007fac8a88ebfc64544077e322a204ffd5151026fea8a8813fe5454475bf2a2a204ff55151006faa8a8813fc5454409be2a2a200ffd8d51005fec6a88e7fe63544057f31aa200ff58d511cff8c6a880afc6354409ffa9aa204dfd4d51027fca6a88e77e5354409fea9aa200df54d51027f8a6a88137c5354475ffa1aa239ff90d51007fa86a88e7fc4354401ffb12a200bfd8951007fcc4a8803fd6254401fe312a209bf18951027fea4a88137f5254409ff292a200df94951027faa4a88037d5254409fe292a204df149511d7fe84a8803fe4254401fea12a23aff109511cffe64a8803fe3254401fe992a239ff0c95100dfec2a8807ff5154409fba8aa201ff9455100efca2a8807fc5154403be28aa201fd1455100ffe82a8807fe4154403fb20aa201ff1055100ffe62a8807fe3154403fb18aa201ff0c55100ffc42a8807fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a205bf18151027fea0a88137f5054409fe282a204df141511d7fe80a88ebfc4054473ff982a239ff0c15100ffe20a8807fc1054401bfb22a23adf99151006fac8a88eb7c6454401bfb1aa239df98d51006fac6a88e77c6354475bfa1aa239df90d51006fa86a88e77c4354401bfb12a200df98951006fac4a88037c625447
  | 8 => 0xfd4a4204ffca521027ee5290813fea948400fb54a4204ff8a521027ff4290813dfa148403fbd0a4204ff88521027ec4290813ff9948409ff0ca4204ffec321027fe61908037f30c8409ff58642005fac321027fc61908037e30c8448ffd4642237fca32111bfc5190807ffa0c8403ff9064201ff8832111fff319088dff18c8446ff0c64204ffc4321027fc2190813ffb048409ff9824202dfcc121027fd60908017eb048409ff18242247fea121123fc5090807ffa048403ff1024223ffe612111ffc309088dff8848446ff04242007fecaa1002ff655088bff32a8404bf99542007facaa1002fd655088bfe32a8404bf1954204dfec8a100fff5450807ff2a28403ff5514201ff8a8a1003ff63508017fb1a8444ff98d42015fcc6a1003fd6350889fe31a8402bf18d4222ffea6a1113fe5350801fea9a8444ff14d4201ffe86a100ffe4350807fea1a8403ff10d4201dfec4a1117ff5250813ff2928400fb94942007faa4a1003ed5250813fe2928403ffd094201fde84a1027fe4250813df2128409ff1094204f7884a100fec4250889ff9928409ff0c942007fec2a1002ff6150887ff30a8401bf98542007fac2a110ffc61508037e30a8445ffd454221ffca2a110ffc5150807ffa0a8403efd054201ffc82a100ffc4150889ff98a8443ff8c54221ff862a110ffe2150813fe10a8400ffd8142005fec0a1003fe6050801feb028400ff1814202df8c0a1117ff505088bfe2828403ffd014201f7e80a100ffc4050889ff9828444ff0c14221ffe20a110ffc1050813ffb2c6409bfd963204ffccb19012fe658c813bf32c64049f9963204ffacb19002fd658c813beb2c64009f5963204ff8cb19026fc658c813ffb246409bfd923204ffcc91900efe648c813feb246400bf5923204ff8c919026fc648c885ffaa46441ff95232007faa919107fc548c8057eb1c6402ffd4e32017fca71900bfd538c805fe29c6402ffd0e32017fc871900bfd438c805fe21c6409bf98a3204ffea519027fe528c813f72946409ff54a32007daa519027fc528c813ffa146441fbd0a3204ffc8519027fd428c813fe2146409fb10a3204ffe6519027df328c805f79946409ff0ca3204fd86519027ff618c813ff30c6401bf9863204ffac319002fd618c813fe30c6401bf18632217fea319103fe518c881fe28c6441ffd0632207fc8319103fc418c805ff98c6402ff8c632017f86319027fe218c813fe10c6409ffd823204ffcc119016fe608c813feb046400bf5823204ff8c11910bff508c885fe2846441ffd023220ff8811900bff308c805fe1846440ffc4232207f82119003ff654c8017fb2a643fff99532025fcca99003fd654c8017eb2a643fff19532025f8ca99003ff644c8017fb22643eff9913201dfcc899003fd644c8017eb22643eff1913201df8c8
  | 9 => 0xc05ff9928602f7cc943017f864a1803ff6150c017fb0a864fff9854300dfcc2a1803fd6150c9ffe30a8601bf18543287fea2a193ffe5150c9ffe28a8603ffd054301f7e82a180ffe4150c07fe20a8602ffcc543017be62a180bfe3150c05fe18a864fff8854327ff842a1803ff6050c017fb028600ff98143007fac0a1803fc6050c0b7e3028650ffd4143287f8a0a180fff4050c07dfa028603ff10143017fe60a180bfc3050c05ee182864fffc414327ff820a1812fd6594813ffb24a409ff9925201dfcc929027fd64948017eb24a409ff1925204df8c929013ff5494809ff2a4a404ff55252027f8a929027ff6394813ff31ca402bf98e5204fbcc72900ade6394813feb1ca400bf58e5204fbac729002dd6394813fe31ca409bf18e52027fea729013fe5394809fea9ca404ff14e52277fe8729137fe4394801fea1ca44dff10e5204dfcc529027ff5294813bfa94a404fbd4a5204ff8a529027ec5294813ffa14a409ff10a5204ffe6529027fc3294813ffb0ca409ff9865200dfcc329027fd61948017eb0ca409ff1865200df8c329013ff5194809bfa8ca404ff94652027f8a32913bff4194899ff20ca44cff1065226ffe6329133fe3194899fe18ca409ff8865204ff84329027ff6094813ff304a405bf9825204ffac129002fd6094813fe304a404ffd4252027f8a12913bff409489dfe204a44dffcc25226ff86129133ff1094899fe084a409bfd9552007fec8a9002ff6454897ff322a403bf99152007fac8a912ffc64548077e322a404ffd5152026fea8a9013fe5454809feaa2a400df55152027f8a8a9003ff63548017fb1aa44aff98d52015fcc6a9003fd6354895fe31aa402bf18d52027fea6a9013fe5354895bf29aa404ff54d52027f8a6a90137c5354897ffa1aa44aff90d52007fa86a912bfc43548097fb12a404ffd4952027dea4a9027fe5254813bf292a409ff1495204ef8a4a9013ec5254897ffa12a409ff10952257fe64a9027fc3254801ffb0aa400bfd855224ffcc2a9006fe6154801feb0aa449ff1855200df8c2a9013ff5154809bfa8aa404ff94552027f8a2a912fff4154893ff20aa449ff10552257fe62a9127fe3154893fe18aa449ff8855204ff842a9003ff60548017fb02a400ff98152007fac0a9003fc605480b7e302a404ffd4152026fea0a9013fc5054897ffa02a44bff10152257fe60a912bfc3054893ff882a449ff0415204ffecb21026ff6590813ff32c8404bf9964204ffacb21002fd6590813fe32c8409bf1964201dfac92100fff5490807ff2a48403ff5524201ff8a921027ff6390813ff31c8402bf98e4204ffac721002fd6390813fe31c8409bf18e42247fea72111ffe5390801fea9c8447ff14e4201ffe872100fbf4390807ff21c8403ff50e420077a872100ffc43908137f3148409f
  | 10 => 0xc00000a00e04602200400800000000001000800400800200000800e00000600000205204a00000202c00604400004401801a01c00003c00002000004602400600e00801800a01600400000400200200006800e00401000001001400600000c00200000400800e00000a00001000000005601000200e00203400002603c05a00001c00000200605c00001a02c01202000e00000c00200000400000200000200001603400200a01202603200400600201c01003bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec6aa002ff63550a9ff31aa802bf98d54007fac6aa153fc63550057e31aa804ffd4d54027fca6aa013fc5355007ffa1aa803efd0d5401ffc86aa00ffc4355001ffb12a800bfd8954007fcc4aa003fd6255001fe312a809bf18954027fea4aa0137f5255009fe292a803ffd095401ff884aa153ff32550a9fe192a800ffd8554005fec2aa14ffe61550037f30aa800ff5855429ff8c2aa006fc6155009ffa8aa804dfd4554027fca2aa013fc5155007ffa0aa803ff9055401ff882aa153ff31550a7ff18aa853ff0c55429ffc42aa14ffc2155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a805bf18154027fea0aa013fc5055007ffa02a803ff101542a7fe60aa153fc30550a7ff882a853ff04154015fecaa9803ff6454c017fb22a652ff9915301dfcc8a9803fd6454ca5fe322a603bf19153027fea8a9813fe5454c09feaa2a604ff15153015fec6a980bff5354c09efa9aa602ff94d53016fca6a980bfc5354c05be29aa602f714d53017fe86a980bfe4354c05ef21aa602ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a9826fc6254c09ffa92a604ff14953297fe84a994bfc4254c05ff992a602ff0c953007fec2a9802ff6154ca3ff30aa601bf98553007fac2a9947fc6154c037e30aa604ffd4553026fea2a9813fe5154c09fe28aa652ffd055328ffc82a9947fc4154c05ff98aa602ff8c553017f862a9947fe2154ca3fe10aa600ffd8153005fec0a9803fe6054c01feb02a600ff1815302df8c0a9813ff5054c09bfa82a604ff14153297fe80a994bfc4054c05ff982a602ff0c15328ffe20a9947fc1054c01ffb2a8600bfd9543006fecaa18027f6550ca1ff32a8604bf99543007facaa1802fd6550ca1fe32a8604bf19543006f8caa18127c6550c057fb228603ffd514301ffca8a180fbe5450c07feaa28600ef5514301ff8a8a180aff6350c05ffa9a8602ff94d43017bca6a180bfd5350c01eea9a8602ff14d43017fe86a180fdf4350c05ff21a8602ef90d43017f886a180bbc4350c05ee21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894304df8c4a1943ff5250ca1fe2928603ffd094301ff884a180fbc4250
  | 11 => 0x2e40cf801c00600002202001a00000001809e00400002200803e00e00001800804201205e06601001000000000000000405600200200002a00200000c00a00800a00400000207202e00802e00000000200400400e00200600400000201604001a00800001000001c03603200005800801003001801801a00006400802000000001800601801200400600000000e01a00201611801200405600e06600a00400400000600400602000a0680dc01000200009805400c04405e00c02800a02600800401a00e01201402601401000a00002400200000201603c00400401000400800200001600602603000e0c200a07600200201600c00a00003e00401001200000000400001000000200800800000000601400800600c0040a401c00e00001e00003203200200001000e0000040ea02000e01000001001800c01400800600c00003200200000001601201400e00803200201804c00200600e01007800001a00000403a02000a00000400600000e03601600401c00801a06e03001000800403801800006200800000a00600002600001200001800401c03e01a00400400008c05c00603800200601000002600c05c0040020d602200000400402400000003c00000200602400800200000006200000603601003200400403a00001002200c01004c00e01200400000000000801a02203400200a05000e06605e00601800a01e00401200000005c00201800002004800002001a06800000200a00800001000a01400001c00601002c00000400000600000000800400000200200202e02a00600404400007000800200c00000000c02000000001400200602800805c00200c00000000c00401201403200a01201600a00403200800201000200000000600402800a00005a00c00e00a00600a04600202c00800c00a00c03400e00a00000600000a00a02200c00200000000202a00202a0ce01800602200601602e01800800a00000002000000000003606a06406c00201002000e00600400a00001600000801800200406802000400802401200004800800401a05000201200200000600000200000408e01003202200a02801200000000400c00400e00a01a00400000001403e01600800e00400002400a00002000000200601400a00205204606202c0120a001000400200400603604802e00400000000800802200600001200c00607002204601205c01402e00200800400600a00800000403005822c00c01408e00600001200409400001002000600a00400000400600e01406600800400002400001600001400001000800000a00601a00001001a00002000001c00400400600001000400204e03c10200009000000000800e02809a00000001000a00400003e01a00200000605601a04000200201200e01a00e0a000600c01a00000401801a01e00a0060080000
  | 12 => 0x42a07120f6009cab600013718381f020000000011527a64ad21e875c93645b887c7f6037000000092c7390d09d18b204562510bc00004542329d348e28832ca091cd2c7d004782180c04413e895851b465c32d1558ce693211f1d6c41600011f9b5118038d1e30e704d080b4538000a821090000000c503b721b000067e00000000547d45a64a700012685b80001744c080000000000db000000002bc00000000004e0f0e0002010dccb2c2282f584b4a9e1c5466908c00a0000c10ddcb1e1992b78b3509663a4719a045ac000000164c82e0711220388bb24892ae0c543648ae2531230124159382894c0006511489f608945231af0c94cb64bd2ee079079081523c1d0cd085240b29ae50606a734696647d692e0f19e341788c61c98ec91b600032e8a8900600039ea19504600002e983091c26502522680005170d415880005834620e7414869a19d21900000003888000eb200000009dc57e7c60000b6521a27f0001414ff01244a51bb89fa00003e8f08daa3ca0001e8d1440000000000420626016800098a22008a82cc46818137d1d846787320ac12dc0848183a902810fc6ed0c780010dc7311d50e2c25c0002a513340000001b40e8400000037c90507c65cd17880000000002d8085c626537117802000053828a95dc8ae0f5000000030e5950001af85886e70ad0c0009207438a11546c88c84a802e84e428e2fd8a8512e19b3c880000003633b810206482ed00f0000f107032c098fc3b00003d6052801c0d6000071826474e00000000001b7000000000000000000000001a93fa1918d3a5060000f4054e5c229481e8c4e87800009cc22804f2771930cd67c741e22641a60a80a60884d8a09801012b40080ea3499d5457406d05f068c4700003aa09880003e426a9f7123e6c400000001860001f70d144ae42f00695d8dca7e439497f061a24b45900008201370c51c08c108ba075850c23472329991911700721dd90f0b38264000000000080d1461ab870200012406f490080942988c0fc48e80b203303e02df2aa804473431706ea42c0ac00000014d0d0c907082a100d5a4500e393286a04483b9950c3d20000231728c600681ed9dc508a3090ee17b06586c6062874000033d2901fd46d20003098f4800020a1f8a458b6800006f89f861600041fa4a119464d000000000000000000000007e627185449ba80e23119e80584182c299d91106823361fe80001d40001c2c9547e040795910e82e22b5a384e546420cb98c40006b81c799885102892dd24003446af3dc9024a1e09535494f4dc05ae00002a898c0001dd09747ba0542b18ed01e889e47e032d20200048412e86d44984199e6cf9818b358000098e7371c70058a905450d811e911645105a8cc8f6c0001811fa47723c037488ec3da39020296381680820640b70f524fc
  | 13 => 0xa3fe0a0ca064994471b281b07174a3a294edc00f38d0df81847c2000833d1a62d71cc14a81426e63068270e5e8040188808eb45d73c31da86e480111a8120000568156909ca620001fc92e49140000000be8c060000001db01fa05f3d402b00007502e58d280dc33039201700000de286124425800000023e00005a700015e86ae53207c800000e000000000017200000000001088d50000f346103b024812c80003600000ba4f2c0002fe979c8be0003d6800087c382226a16520655909580005dc000041800041e000000000000033110c800000000000010c03b22be47b0ef40c40000b300006500000000000000000000096c75863d3ce81ec0002c91be1078f7c64712e129c00080209f88980000002eea09d19c0000000000ed62c03b1a240db80000c300007066bb49e157c0005b61a106fc00028015785c05905c40fc06142a409f24e0de51124b62f8167c36c0002a696bcaca57800013d0faa8b5091921843802e0128810000000392911000000048300009ae00024aa1a8f6a00000021684a844e15299fc00051a2148a986465bc42315ecc6458011b1e7c08246304723c45d82694751284f8606c0270000e320f60e88e78c904d10fa9efc00024e00b813400047b47e98b12523522800000be4665000243c28c9151f7a480f9e540033116cc223cc0a096a503e6151041acd1a07d60e10f781fe1a630c89442323e138618280426da08c038c00023d45800010c62d53a9a160dc676806398ecf282323ae16dd2325c930f9bd8ab02d210312cc70a6a606d9460b246dd41b1fd8ef429c1959924a6a9170bd927413a720045859cd0e5e31eaa1ed20a6f50ab87683ac42a19a0b3c9ea49f33e890c2846a228c8524b447da2e61da484213637e07e4a0e8a801a10050b62e526206b41645362ed96fc5021271ad85d880c2b50f1246c6ec65949e8658d646ec28f9df8c882ea1ed188477e08c1ef8a544e02b14a481483e647741c0410ff603b32a99a0bee02f3d990c90a28e94588070fd854937f17a0f1c28b3460f889d03381cd8c6c0182223a20e9ce4c7de2c891b05522f617f9a443ce0f70a38154ec493b3378c647fa6790fe057889624d45d9bad0e28922d69338d7404526f043485a7cb0740f5c0ce2d3398249431216841505fc2423be2a903700004e539f136c0002ca13d202890e3b60001c840005e63bda2046a600026c13ccf140001b1125032400046c86accfc400338986c39027600007f4fd031f27f9ac4016000000000109e5d347fa1a4fdc000012028c00000014110100002fc0bb9ced10062b01800005328264a2a13000000031e0d340a678925e07c81b474101f800000078f0000aac69090943923800000000001fb41dc92f02d15c4d1e4e000000000005b233821d825246b1900fb4c7229008880008807b20000af
  | 14 => 0xd00000000001eb82ba0224508e1c6827a007e17f90a810133084c4be630c35e80d800000010480010ce21a00023c0000000182a104d1400015196848a600000006780000d2000205c1366784a622b40006ea0238c5800080609a83b00960000001c20e9841c20a8fa0f7810833190d44ea95b000207529e26c0dc07b90fa55a3ee9cd0b5444928205c80468f533699dce363461e29ff92229351851df04985721d5981919222c3bb00000000001f4845928661c3ab182c10a94d45a14b117e9570e021e427c69844d88ccc6679c2f79a0c4547a20f5829c1da0bd1ee06b89808f31ea06384063662bf9fc4bd21ff230a3ec7280c400001849c46941e79890afc43742380002f8622382000000048425720e52546c004c883412246e1659660e1a1223401290be87a13c59afce844dc143a05800045d3fb800000091c0f8a08800066e4710ff8efa20c3cc9af0cf67381a88748e783a917a2408f9c81e37f969052c2ae0ab0b986b21d743a9824ebe82d1fe20d45b01a501e12f80ea3a4320194014a5c7371215892e0ca1c89dbc6ce6753228b8048c71c2cd058058695845e91a4f4a3f20a018006d66e130f1ef52727ea28086d04624731eb1e4066a95313791d803610e03585bcb825d607f08b4e3a3221ec98946e883b3081be01768de1de24601801b31da8bc8a3c000227a32c9a44af2c5096507409a10c1c88a5e2790001c04df676d48f1bdca8c4583449474c460651c923b8ad80281290000aba00000014447121cc0a2a4751fc16300000004c20000000dc474c53023e9c0042a6e420f8c6869200021d177c81a00000014840000a911393d824c0001a7a250f2e0e700000011720bf000237c3aa0f008e8c18ffa2e119b8be00000000000001290000131800000027d31a80002fa88403f9b584be06a32194885360002dc8000da08570a6873837c32700324500567ab2fd1ab099230e02c0000c0e0002c4a08000068b18e08501a03260c224e92702b424282dcaa265311701445d08132f2a01419a79321710290aa1792b8132cf9a8c31580f9ce3e0f32af23dc52e61443684811460d51b0835ce921130000ebc07a0003c08000a0423c0002280f80000133103800051243b91311386a32c200005484ed2e921fc000000009065400056710b0f949700002f5142c0000001820000d6e293000013007288700000000000001a600007e076508780011581a021300003763f8493874c0006b50000000000310000038000039507491c029669f47211bcc5e88636b9ee00007071c60000c82959055a110946941000045c6da00004800003c200900011d02d26e841a042c91e07e2d2a0c4a2c0001998b149f20002ec248c8166580de16cca7c43d3cc1a20d8e1943ca895907c0c934f073d0c44d44531074f002e32588af0b468143ae9d2d04870
  | 15 => 0xd406310887144344a010643e81e80c4246800012807d9d2813c0003078b780002b236f162c76632e3ba80006ba735260800074657917990ed1b810644c1dc8a4e0ad00000000006fd2de80011d671636893e091629e1ec005060e7ff2f218a8b9e8e631c0d9473e439294020072e8c50e194282681fe1758aa065e4b03a79d6063082e2e199c8c6c0701ae12948402cc000000000031d0000140000597468800033000028d80007860004248000ada00035000000000002fa81bd0380000001b6c74a85000000006f63b100024b11668ed2cf206ce8a19d39f80009e0000000223cf8800008d86c4ef245c37a0b187442010c613bc2c20002548000b3a00024105c416214e23f1c3cca40000000000fde75124d00009c84da20380007ea44500000007cc8af00022f00000002619e0d0b85d548600011d800010709147920003e4124cfb277414e8e80c9c0002098a28aa6267190a17522688213d8a1800018d11c800000019334900006726d237980000000000148250a5a7b70b99dfd27c5ff40400000000000099ebcb80000000000000017a2f700000000001118000c5200000005107a221b0000bf40000000000000000000000000000052e16103c4d0a2db0da8000f8a0732f099282a62ac15c8fb10225133d38550b407180708d38aae05b1469d1d26653f0001fc088429401a87748b482112f0fd80002373939620d6c0000fb80e881890a3b3a1788cc4c22c1126c1603c1044807c0064330d3a0a1244896112193c91042803c800825416d20787248da11c000070400026b00013ed2247923ed91e44c00002a61b3527e1070861550adc31426402d80322250451ed088660533498d000052520196f90908c21e989a909a24a2a102b906437512d11481a86a539595f4b5017816825540302fb17f12340f01744980000a4c1db495992c0000e53fc9d5c0d21032b5000000038400e80000000001948040ba013b1bc1c3800086f23505b90240573ea1a38ba847f18180005a248303e23580000000720cd8ec88e53c60d5920815f08f9f94da62922738e58f7600027f20a499e00000005700000380000728ae80000000b0400000044287bc00072800000000006a8000217c9be0003e98000d9c5873e4936468031236f9f8c00066031f1d9882466a13892a10e624921209e00885ac4872138000241000024d17c4601282374ca800028a1e1079695608521c0a963a82b00d511e8667498a54404c00020b1c5400000015013a4f0a6952c31b0c27a36f03224911982f72ef056c75a7c146905d4fce8684179cd868e51c00022a8e261af15b9874e740002870df41de6c11c41384d842420fd9330d328c716d07781023f346c00000004673f0860d2887ba23418583cc00000022545661ea46b8dfce804460000a3c33e5c600015cc8ea8b600009
  | 16 => 0xf620002128d54a8800046a0000b6a89d27509540002e74a10e00c040001090000d9067c000224c00095200005546e000010f1d7819c6cb3679a6c00095c000203000000015c0000fbe8100000d2cd202293961a903000002fc19d0c3000040ca27c49e0004778c0458e5bb0cd21088227822f114ac6543440a41a84d560000441420fae88c0001fac00082b2b48780c2426d0002244eee48105c11c800000028805a90d654741285887ee49e4739aa820443f1ac17e4cae7aa3e504e80344e625580010c229a2a8163400023a1088cb40004f200004e40001c4218a2ac1a200027610b00000401cc93c423c8c117a90acde47d21f01c782fc284043997812c4bb31b92490947a40c8028800024007309f05f26cc000173805492d39701dc9d66f1019255042600000001780001120000814ccc79e00005b0fe65f11ffa484bda0001879068bb41f60e594e496854e0dc935926e4a021c1bbca7465607d1d205306d918f06706866170efa0002d67103780de832288d1778b381e422b1afa440c5a82c0f28b7478803e2238734a1a1253bc096027808d317201d0c00432b3081caea00a27b9630bec50934e00cd0864bf29d844079c36c43617140ec1fa47906e86b40a62be20f46dc53c155251867694b493197c70c4d01e39868b62097142818c7701a4097a3e90cc3fa1fa12b119e1aa06c91f0f6021d02c8a7cc026c927d0ad8e5a70638480000008a444511642001302d5a3e4bc087c0a79a5c9a66200609e68cc87f222f0c442668373b012d45c885220d9ccd0346b40d6166c5762
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb7450110007bb645011001efa645011001ef8645011003fb864501102b7bb545011003fb85450110005fb7350110126fa6350110126f8635011003fbb4350110007b94350110005fb7250110006fb6250110006f9625011003fbb4250110007b94250110007f3715011000dfa715011000df8715011011ff0715011000df0715011002efb615011002ff3615011011f7b515011011f79515011011fbb415011011fb9415011011ff23150110007f1315011011ff22150110007f121501102adfa768c11002efa768c110006fb658c110006f9658c11002dfb748c110005f9748c1100edf9738c110016fa638c110016f8638c110037da438c110007d9438c110005f9728c11002ff3718c11000dfa718c11002df8718c11002ff0718c11002efb618c11002ff3618c1101077b518c11010779518c110107f2318c110037f1318c110107f2218c110007f1218c110014ff764c11000cfe764c1100ecfd764c11000cfc764c110006df634c110016dc634c110005f7714c11000df4714c110007d5314c11002fd8304c11002ff0104c11000df8764c110016f8764c11000cf8764c110006fb654c110006f9654c110005fb744c110005f9744c11002dfb734c11002fdb734c110007db634c110016fa634c110016f8634c110037d8634c110005fb724c110037db324c110007d9324c110007f3714c11000dfa714c11000df8714c1100eff0714c11002efb614c11002ff3614c1100ef7b514c1100ef79514c1100efdb314c1100eff2314c1100efd9314c110037f1314c110007d1314c1100eff2214c110007f1214c11000cfe76c811000cfc76c8110006ef62c811004eec62c811000df671c8110005f571c8110007e521c811006dfa768811002efa768811002dfb7488110005f97488110006fb6488110006f9648811002dfb7388110005f9738811008df9728811004efa628811004ef8628811002ff3718811000dfa718811002df8718811002ff0718811002efb618811002ff361881100af7b51881100af7951881100aff23188110007f131881100aff22188110007f1218811004cff764811000cfe764811008cfd764811000cfc7648110006ef624811004eec6248110005f7714811000df47148110007e5214811002fe8204811002ff0104811000df8764811004ef8764811000cf87648110005fb7448110005f97448110006fb6448110006f96448110005fb7348110005f9734811002dfb724811002feb7248110007eb624811004efa624811004ef86248110007e86248110007ea3248110007e93248110007f3714811000dfa714811000df8714811008ff0714811002efb614811002ff3614811008f7b514811008f79514811008ff23148110007f1314811008feb214811008ff2214811008fe92148110007f12148110007e12148110
  | 1 => 0x891001cfc7458910004ff7358910014fe7358910014fc7358910006ef725891008cff7158910006f7715891008e7f515891008e7d51589100ccff7058910006fb70589100acfe76189100457e75189100057d751891003dbe7418910005bd7418910035de7318910005dd731891004eee6218910006ed621891004cff7694910004fe7694910004fd769491004cfc7694910035de7394910005dd7394910006ef629491004eec629491000df67194910005f5719491002dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d6554910006ef625491004eec625491004cff7690910004fe7690910004fd769091004cfc769091000df67190910005f5719091002dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091001ebe6450910006bd645091004cff768c910004fe768c910004fd768c91004cfc768c9100457e758c9100057d758c91004eee628c910006ed628c91000df6718c910005f5718c91002dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910016de634c910006dd634c91004eee624c910006ed624c91000df6714c91002df4764c510016f4764c51002cf4764c510006f7654c510006f5654c51000df7734c51000fd7734c510007d7634c510016f6634c510016f4634c510037d4634c510037d6434c510007d5434c510005f7724c510037d7324c510007d5324c510007f3704c51002df6704c51002df4704c510007f0704c51000ef7604c51000ff3604c510037d7304c51002df4764851004ef4764851002cf47648510006f76448510006f56448510005f77348510005f5734851000df7724851000fe77248510007e7624851004ef6624851004ef46248510007e46248510007e64248510007e54248510007e63248510007e53248510007f3704851002df6704851002df47048510007f0704851000ef7604851000ff36048510024ff765411000cfe765411014cfd765411000cfc76541100067f65541100267c6554110005f7715411000df4715411002ff010541102bdfa769011002efa769011002f7a759011002f797590110006fb6590110006f9659011011df9749011001efa649011001ef86490110005f97390110136fa6390110136f86390110005f97290110006fb6290110006f9629011000dfa719011002df8719011002efb619011002ff3619011013f7b519011013f79519011013ff23190110007f1319011013ff22190110007f1219011001cff765011000cfe765011011cfd765011000cfc7650110006bf645011001ebc6450110005f7715011000df4715011002fb8405011000df8765011001ef8765011000cf87650110006fb6550110006f9655011002dfb745011002fb
  | 2 => 0x467c5459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc73595100467f5359510004ff725951004cfc72595100467f525951014cff7159510006f7715951014e7f515951014e7d515951014ef631595102dcff7059510006fb70595102d67e50595102d67c505951001cfe76d91100457e75d91100057d75d911003ebe64d9110024fe75d91100067e75d91100247e75d9110004fd75d91100067d75d91100047d75d9110024fc75d9110014fe73d9110004fd73d9110014fc73d911004cfe72d9110004fd72d911002cff71d911000cfe71d911002cfd71d911000cfc71d911013e7f51d911013e7d51d911013ebf41d911013ebd41d911013ef621d911002cfe70d911000cfd70d911002cfc70d911003ebf40d911003ebc6459110005ef7259110005ec72591102cdfb7059110004ff7559110024fe7559110024fc755911013cff7459110006bf7459110004ff7359110014fe7359110014fc735911003ebf4359110004ff7259110006ef7259110004ef725911004cfc7259110006ec725911004cec725911003ebf425911011cff7159110006f7715911011e7f515911011e7d515911011ef621591102ccff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc7655110014fe76d8d10036de63d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10006df53d8d10036dc53d8d10036de43d8d1004cfe72d8d10004fd72d8d1002cff71d8d1000cfe71d8d1002cfd71d8d1000cfc71d8d101067f51d8d101067d51d8d10106df31d8d10106dd31d8d1002cfe70d8d1000cfd70d8d1002cfc70d8d10036df30d8d10036dc6358d102c5fb7058d10004ff7558d10024fe7558d10024fc7558d10004ff7458d1001cfe7458d1001cfc7458d10104ff7358d10006df7358d10004ff7258d1004cfc7258d10036df3258d100ecff7158d10006f77158d100ee7f5158d100ee7d5158d102c4ff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100267e6554d100067d6554d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100457c7550d1001ebe6450d10006bd6450d10006df6350d10016dc6350d1004cfe76d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910014fe73d8910004fd73d8910014fc73d8910006ef42d8910006ec42d891002cff71d891000cfe71d891002cfd71d891000cfc71d89100ae7f51d89100ae7d51d89100aeef21d89100aeed21d891002cfe70d891002cfc70d8910006ef629891008df970989100cdfb7058910004ff7558910024fe7558910024fc7558910004ff745891001cfe745
  | 3 => 0xc6350e1002dfa7050e102ffda3050e10004ff7558a10024fe7558a10024fc7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10014fc7358a1002eef7258a1008e7f5158a1008e7d5158a1008eef2158a1008eed2158a1002cff7058a1002cfe7058a1002cfd7058a1002cfc7058a1002efa4058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a1004cff7694a1002cfe7694a10004fd7694a1002cfc7694a10055de7394a10005dd7394a1002dfa7094a10005f97094a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a100267e6554a100067d6554a1004cff7690a1002cfe7690a10004fd7690a1002cfc7690a1002dfa7090a10005f97090a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a1001ebe6450a10006bd6450a1002dfa7050a1004cff768ca1002cfe768ca10004fd768ca1002cfc768ca100657e758ca100057d758ca1004eee628ca10006ed628ca1002dfa708ca10005f9708ca10004ff764ca1002cfe764ca10004fd764ca1002cfc764ca10016de634ca10006dd634ca1004eee624ca10006ed624ca1002dfa704ca1002dfb76502102f6fb765021002efb6550210006f9655021002fbb745021002fbb645021001efa645021002ef8645021002fb864502102efbb545021005fb85450210005fb7350210126fa635021002ef8635021005fbb4350210007b94350210005fb725021002efb6250210006f9625021005fbb4250210007b9425021000dfa715021000df8715021011f7b515021011f79515021011fbb415021011fb9415021002dfb764c2102e6fb764c21002efb654c210006f9654c210005fb744c210005f9744c21002fdb734c21002fdb634c210016fa634c21002ef8634c21002fd8634c210005fb724c210057db324c210007d9324c21000dfa714c21000df8714c2100ef7b514c2100ef79514c2100efdb314c2100efd9314c21002dfb7648210006fb7648210005fb7448210005f9744821002efb6448210006f96448210005fb7348210005f9734821002feb724821002feb624821004efa624821002ef8624821002fe86248210007ea3248210007e9324821000dfa714821000df8714821008f7b514821008f79514821008feb214821008fe92148210024fe76d95100467e65d951001cfe74d9510004fd74d951001cfc74d9510014fe73d9510004fd73d9510014fc73d951004cfe72d9510004fd72d951002cff71d951000cfe71d951002cfd71d951000cfc71d95101667f51d95101667d51d9510166f631d951002cfe70d951000cfd70d951002cfc70d95100467f50d95100467c6559510005df7359510035dc73595102ddfb7059510164ff75595100067f7559510004ff745951001cfe745951001cfc74595100067e5459510
  | 4 => 0x4420004fd765442002cfc76544202d67f65544200267e65544200067d65544200267c65544201d6be6454420006bd64544201cede6354420006dd635442000ef66154420006f561544202d57f76544200067f76544200047f76544202d67e76544202d57d76544200067d76544200047d76544202d67c76544202d67f64544201d67e64544202d73e64544201d63e64544200067d64544202d73d64544200063d64544202d67c64544202d67f63544201ce7e63544202d75e63544201ce5e63544200067d63544202d75d63544200065d63544202d67c63544200ce7e625442030d7f71544200877771544202d67f615442000e7e61544202d776615442000e76615442006e7d61544202d775615442000675615442000e7c615442006f76415442006f7631544202d67e60544202d76f20544202d77a20544202d76d2054420307792054420004ff7650420004fd765042002cfc76504201c67e65504200067d655042001ebe6450420006bd64504201bede6350420006dd6350420005ef725042004dec725042000ef66150420006f56150420007755150420004ff764c420004fd764c42002cfc764c4201b67e654c4200067d654c4201aebe644c420006bd644c420016de634c420006dd634c42000ef6614c420006f5614c42000775514c420005fb704c42002df8704c42002e7f7559610004ff745961001cfe745961001cfc74596100067e54596100667c5459610004ff7359610014fe7359610014fc73596100667f5359610004ff725961004cfc72596100667f525961014e7f515961014e7d515961002cff705961002cfe705961002cfd705961002cfc705961002e7e505961002e7c505961002efa405961002efa3059610004ff7559210024fe7559210024fc755921002ebf7459210006bf545921005ebc5459210004ff7359210014fe7359210014fc735921005ebf4359210004ff725921004cfc725921005ebf425921011e7f515921011e7d515921011ebf415921011ebd415921002cff705921002cfe705921002cfd705921002cfc705921002ebe405921002ebc405921002efa2059210004ff765521002cfe7655210004fd765521002cfc7655210004ff7558e10024fe7558e10024fc7558e10004ff7458e1001cfe7458e1001cfc7458e1002edf7358e10004ff7258e1004cfc7258e10056df3258e100ee7f5158e100ee7d5158e100eedf3158e100eedd3158e1002cff7058e1002cfe7058e1002cfd7058e1002cfc7058e1002ede3058e1002edc3058e1002ef71058e1002ef51058e10004ff7654e1002cfe7654e10004fd7654e1002cfc7654e100267e6554e100067d6554e10004ff7650e1002cfe7650e10004fd7650e1002cfc7650e100057f7550e100657c7550e1001ebe6450e10006bd6450e102fedf6350e10016d
  | 5 => 0x2edc2058c2002edf1058c2002ede1058c2002edd1058c2002edc1058c20004ff7654c2002cfe7654c20004fd7654c2002cfc7654c200267e6554c200067d6554c20296be6454c20006bd6454c20016de6354c20006dd6354c2028ef66154c20004ff7650c2002cfe7650c20004fd7650c2002cfc7650c200057f7550c200857c7550c202867e6550c200067d6550c2001ebe6450c20006bd6450c20016de6350c20006dd6350c2027ef66150c20004ff7558420024fe75584200067e75584200067d7558420024fc7558420004ff745842001cfe745842001cfc7458420004ff7358420014fe7358420014fc735842000cfd725842002cff715842002ef77158420006f7515842006ef6515842006ef45158420006f7415842006ef6415842006ef44158420006f7315842006ef6315842006ef4315842004ef7215842004ef4215842002cff705842002cfd705842002cfc705842002eef205842002efa205842002eed205842004ef9205842002ef6105842002ef41058420006f77558420006f67558420006767558420006f57558420006757558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f4435842004ef7725842004ef6725842004ef4725842004ef7525842004ef6525842004ef5525842004ef4525842004ef7425842004ef6425842004ef5425842004ef4425842004ef7325842004ef6325842004ef5325842004ef4325842002ef7705842002ef6705842002ef4705842002ef7505842002ef6505842002ef5505842002ef4505842002ef7405842002ef6405842002ef5405842002ef4405842002ef7305842002ef6305842002ef5305842002ef4305842002ef7205842002ee7205842002ef6205842002ef2205842002ef5205842002ee5205842004ef1205842002ef4205842030d7f76d44200267f76d44200247f76d442030e7e76d442030d7d76d44200867d76d44200047d76d44200267c76d442030e7f64d44201e67e64d442030f3e64d44201e63e64d44200067d64d442030f3d64d44200063d64d442030e7c64d442030e7f63d44201de7e63d442030f5e63d44201de5e63d44200067d63d442030f5d63d44200065d63d442030e7c63d44203176e72d44200876d72d44200ce7e62d44202d57d71d442030e7f61d442000e7e61d442030f7661d442000e7661d442006e7d61d442030f7561d44200067561d442000e7c61d442030f7a70d44200877970d442030e7e60d442030f6f20d442030f7a20d442030f6d20d44203177920d4420004ff765
  | 6 => 0xc725902004ebe425902004ebc4259020004ff715902000cfe715902000cfc715902007ebf4159020006be415902007ebc415902002cfe705902002cfc705902002ebe405902002ebc405902002efa205902004ef92059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bc535902004ebf725902004ebe725902004ebd725902004ebc725902004ebf525902004ebe525902004ebd525902004ebc525902004ebf325902004ebe325902004ebd325902004ebc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006be5159020006bc5159020006bf3159020006be3159020006bc315902004ebf215902004ebe215902004ebd215902004ebc215902002ebf705902002ebe705902002ebd705902002ebc705902002ebf505902002ebe505902002ebd505902002ebc505902002ebf305902002ebe305902002ebd305902002ebc305902002ebf205902002ebe205902002eba205902002ebd205902004eb9205902002ebc205902002ebf105902002ebe105902002ebd105902002ebc1059020004ff765502002cfe7655020004fd765502002cfc76550200267e65550200067d655502001ebe6455020006bd64550202a6de635502029ef66155020004ff7558c20024fe7558c20024fc7558c20004ff7458c2001cfe7458c2001cfc7458c2002cff7358c2002edf7358c20006df5358c20076de5358c20076dc5358c20006df4358c20076de4358c20076dc4358c2004cff7258c2004cfe7258c2004cfd7258c2004cfc7258c2004ede3258c2004edc3258c20004ff7158c2000cfe7158c2000cfc7158c20076df3158c20006de3158c20076dc3158c2002cfe7058c2002cfc7058c2002ede3058c2002edc3058c2002eef2058c2002eed2058c20006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c2004edf7258c2004ede7258c2004edd7258c2004edc7258c2004edf5258c2004ede5258c2004edd5258c2004edc5258c2004edf4258c2004ede4258c2004edd4258c2004edc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006de5158c20006dc5158c20006df4158c20006de4158c20006dc4158c2004edf2158c2004ede2158c2004edd2158c2004edc2158c2002edf7058c2002ede7058c2002edd7058c2002edc7058c2002edf5058c2002ede5058c2002edd5058c2002edc5058c2002edf4058c2002ede4058c2002edd4058c2002edc4058c2002edf2058c2002ecf2058c2002ede2058c2002edd2058c2002ecd2058c20
  | 7 => 0x120136fa6390120136f8639012004dfa729012002df8729012002efb629012002feb6290120007ea3290120007e93290120005f97190120006fb61901200077b5190120007795190120007eb2190120007e9219012001cff765012009cfd765012004cfc7650120006bf645012001ebc6450120005ef725012004dec725012002fb8405012004df8765012001ef8765012004cf87650120006fb6550120006f9655012002dfb745012002fbb7450120007bb645012001efa645012001ef8645012009fb8645012031fbb545012009fb85450120126fa6350120126f8635012009fbb4350120007b94350120007eb725012004dfa725012004df87250120007e8725012002efb625012002feb625012009fbb4250120007b94250120007ea3250120007e93250120005fb7150120006fb61501200077b515012000779515012009fbb4150120007b94150120007eb2150120007e92150120014ff764c120094fd764c12004cfc764c120006df634c120016dc634c120005ef724c12004dec724c120007cd324c12002cff755942002e7f7559420004ff745942001cfe745942001cfc74594200867f54594200067e54594200867c5459420004ff7359420014fe7359420014fc73594200867f53594200067e53594200867c535942004cff725942004cfe725942004cfd725942004cfc725942004e7e525942004e7c5259420004ff715942000cfe715942000cfc71594200867f51594200067e51594200867c515942002cfe705942002cfc705942002e7e505942002e7c50594200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067c435942004e7f725942004e7e725942004e7d725942004e7c725942004e7f425942004e7e425942004e7d425942004e7c425942004e7f325942004e7e325942004e7d325942004e7c32594200067f71594200047f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067c41594200067f31594200067e31594200067c315942004e7f215942004e7e215942004e7d215942004e7c215942002e7f705942002e7e705942002e7d705942002e7c705942002e7f405942002e7e405942002e7d405942002e7c405942002e7f305942002e7e305942002e7d305942002e7c305942002e7f205942002e7e205942002e7d205942002e7c205942002e7f105942002e7e105942002e7d105942002e7c1059420004ff7559020024fe7559020024fc755902002cff745902002ebf7459020006bf545902007ebe545902007ebc5459020004ff7359020014fe7359020014fc735902007ebf4359020006be435902007ebc435902004cff725902004cfe725902004cfd725902004cf
  | 8 => 0x97ce434c920007cd434c920005ef714c920097cf314c920007eb704c92002dee704c92002dec704c920007e8704c92004eef604c92004feb604c920097cf304c92000cfe76d852008ef661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520014fe73d8520004fd73d8520014fc73d852002cfd72d852000cfc72d8520006ee32d8520006ed32d852008ef651d852008ef621d852002cfe70d852004cfd70d852002cfc70d852008ef710d852008ef461585200267f76d45200a67e76d45200a67d76d45200267c76d45200067f64d45201e67e64d45200067d64d45201e67c64d45200067f63d45201de7e63d45200067d63d45201de7c63d45200076e32d45200076d32d452008d7d71d452008e7f61d452000e7e61d452000e7c61d45203177b20d452030f6e20d4520004ff7654520004fe7654520004fc76545200067f65545200267e65545200067d65545200267c6554520006f7615452000ef461545200067f76545200067e76545200067d76545200067c76545200067f64545201d67e64545200067d64545201d67c64545200067f63545201ce7e63545200067d63545201ce7c63545200076e32545200076d325452008d7f71545200a777715452008e7f615452000777615452000677615452000e7e615452000e7c615452008f74615452000e74615452008f76415452008f7631545203077b20545202d76e2054520004ff7650520004fe7650520004fc765052001ebe6450520006bd6450520007755150520004ff764c520004fe764c520004fc764c520016de634c520006dd634c520007cd324c52000775514c520005ee76c852004eee76c8520006ef64c8520006ed64c852004def73c8520005ed73c8520006ef63c8520006ed63c852008ded71c852000eee61c852000eec61c852008f6f51c852008f6d51c852004feb70c852002dee70c852002dec70c852004fe870c852004eef60c852004feb60c852002cfc7648520006f7614852000ef4614852004fe42148520005fb704852002df8704852004fe8204852002dec764852000eec764852002cec7648520006ef6448520006ed6448520005ef7348520005ed7348520006ef6348520006ed634852004def714852004fe77148520007e7614852000eee614852000eec614852008fe4614852008f6f514852008f6d514852008fe64148520007e54148520007eb704852002dee704852002dec7048520007e8704852004eef604852004feb604852008fe71048520024ff76541200a4fd765412004cfc76541200067f65541200267c6554120005ef725412004dec725412002fe82054120005fa769012002efa769012002f7a759012002f797590120006fb6590120006f9659012009df9749012001efa649012001ef8649
  | 9 => 0xe76d95200a67e65d952001cfe74d9520004fd74d952001cfc74d9520014fe73d9520004fd73d9520014fc73d952004cfe72d952002cfd72d952004cfc72d95200a67f52d952000cfe71d9520004fd71d952000cfc71d95200a67f51d952004cfd70d95200a67f50d95200a67c65595200a4ff75595200067f7559520004ff745952001cfe745952001cfc7459520004ff7359520014fe7359520014fc73595200c4ff7259520006ef7259520004ff715952000cfe715952000cfc71595200a67f51595200e4ff7059520006fb705952001cfe76d912009ebe64d9120024fe75d9120004fd75d9120024fc75d9120014fe73d9120004fd73d9120014fc73d912009ebf43d912004cfe72d912002cfd72d912004cfc72d912009ebf42d912000cfe71d9120004fd71d912000cfc71d912004cfd70d912009ebf40d912009ebc6459120004ff7559120024fe7559120024fc755912009cff7459120006bf7459120004ff7359120014fe7359120014fc73591200bcff7259120006ef7259120004ff715912000cfe715912000cfc715912009ebf41591200dcff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc7655120014fe76d8d20096de63d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20096de43d8d2004cfe72d8d2002cfd72d8d2004cfc72d8d20096df32d8d2000cfe71d8d20004fd71d8d2000cfc71d8d2004cfd70d8d20096df30d8d20096dc6358d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20094ff7358d20006df7358d200b4ff7258d20006ef7258d20004ff7158d2000cfe7158d2000cfc7158d20096df3158d200d4ff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200a57c7550d20006bf6450d2001ebc6450d20006df6350d20016dc6350d2002cfc76549200067f65549200267c6554920005fb705492002df8705492004fe8205492002cfc7650920006bf645092001ebc6450920005fb705092002df87050920005ee768c92004eee768c92004f6e758c92004f6d758c920006ef658c920006ed658c92020eee648c92020eec648c920095ed738c920016ee638c920016ec638c920005ed718c92002dee708c92002dec708c92004eef608c92004feb608c92002cfc764c920006df634c920016dc634c92004fcc324c920005fb704c92002df8704c92002dec764c920016ec764c92002cec764c920006ef654c920006ed654c9201f6ee644c9201f6ec644c92004def734c92004fcf734c920007cf634c920016ee634c920016ec634c920097cc634c920327cf534c920097cc534c920
  | 10 => 0x8e2001cfe7458e2001cfc7458e2002edf7358e200b6df3258e20004ff7158e2000cfe7158e2000cfc7158e200b6df3158e2002cfc7058e2002ede3058e2002edc3058e2002eef2058e2002eed2058e2002efa1058e20004ff7654e2002cfe7654e20004fd7654e2002cfc7654e200267e6554e200067d6554e20004ff7650e2002cfe7650e20004fd7650e2002cfc7650e200057f7550e200c57c7550e2001ebe6450e20006bd6450e202fedf6350e20016dc6350e2004efb2058a2002eee2058a2002eec2058a2002ef82058a20024ff7654a2002cfc7654a200267e6554a200067d6554a20005fb7054a2002df87054a2001cff7650a2002cfc7650a2001ebe6450a20006bd6450a2004fac4250a20005fb7050a2002df87050a20014ff764ca2002cfc764ca20016de634ca20006dd634ca20005fb704ca2002df8704ca20004ff7558620024fe7558620024fc7558620004ff745862001cfe745862001cfc7458620004ff7358620014fe7358620014fc735862002ef771586200aef631586200aef6215862002cfc705862002efa405862002eef205862002eed205862002ef6105862002ef410586200267f76d462030e7e76d46200c67d76d46200267c76d462030e7f64d46201e67e64d46200067d64d462030e7c64d462030e7f63d46201de7e63d46200067d63d462030e7c63d46200c76e72d46200c76d72d462030e7f61d462000e7e61d46200ae7d61d462000e7c61d462030f7a40d462030f6f20d46203177b20d462030f7a10d4620004ff7654620004fd765462002cfc76546202d67f65546200267e65546200067d65546200267c65546200067f76546202d67e76546200067d76546202d67c76546202d67f64546201d67e64546200067d64546202d67c64546202d67f63546201ce7e63546200067d63546202d67c63546200c77771546202d67f615462000e7e61546200ae7d615462000e7c61546200af7641546200af7631546202d77a40546202d76f20546203077b20546202d77a1054620004ff7650620004fd765062002cfc765062001ebe6450620006bd6450620005ef725062004dec725062000775515062002dfa7050620004ff764c620004fd764c62002cfc764c620016de634c620006dd634c62000ef6614c620006f5614c62000775514c62000cff764862000ef66148620006f56148620005fb704862002df8704862002dfb765022007efb765022002efb6550220006f9655022002fbb745022002fbb645022001efa645022002ef8645022002fb8645022032fbb54502200bfb85450220126fa635022002ef863502200bfbb4350220007b9435022004dfa725022004df872502200bfbb4250220007b94250220005fb7150220006f961502200077b51502200077951502200bfbb4150220007b94150220024f
  | 11 => 0x24fe7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720014fe7358720014fc735872002cfc725872004eee3258720006ed325872004ef771587200cef6415872004ef7215872004ef4215872004efa205872004ef920587200cef710587200267f76d47203167e76d47200e67d76d47200267c76d47203167f64d47201e67e64d47200067d64d47203167c64d47203167f63d47201de7e63d47200067d63d47203167c63d47203176e32d47200076d32d47200ce7f61d472000e7e61d47200ce7d61d472000e7c61d47200cf6f21d47200e77a70d47200e77970d4720004ff7654720004fd765472004cfc76547203067f65547200267e65547200067d65547200267c65547200067f76547203067e76547200067d76547203067c76547203067f64547201d67e64547200067d64547203067c64547203067f63547201ce7e63547200067d63547203067c63547203076e32547200076d32547200e77771547200ce7f615472000e7e61547200ce7d615472000e7c61547200cf7641547200cf7631547200cf6f2154720004ff7650720004fd765072004cfc765072001ebe6450720006bd645072000ef66150720006f56150720007755150720004ff764c720004fd764c72004cfc764c720016de634c720006dd634c72004dee724c720007cd324c72000775514c720005fb704c72002df8704c72004def764872006eef764872004eef6448720006ed6448720005ef7348720005ed734872004eef6348720006ed634872004fe7714872004fe7614872000eee614872000eec614872004fe461487200cf6f51487200cf6d51487200cfe64148720007e5414872002dee704872002dec70487200cfe71048720024ff765432004cfc76543200267e65543200067d6554320005ef725432004dec725432001cff765032004cfc765032001ebe6450320006bd6450320005ef725032004dec7250320014ff764c32004cfc764c320016de634c320006dd634c320005ef724c32004dec724c320007cd324c32002e7f7559620004ff745962001cfe745962001cfc74596200067e54596200c67c5459620004ff7359620014fe7359620014fc73596200c67f53596200c67f5259620004ff715962000cfe715962000cfc71596200c67f515962002cfc705962002e7e505962002e7c505962002efa4059620004ff7559220024fe7559220024fc755922002ebf7459220006bf54592200bebc5459220004ff7359220014fe7359220014fc73592200bebf43592200bebf4259220004ff715922000cfe715922000cfc71592200bebf415922002cfc705922002ebe405922002ebc405922002efa1059220004ff765522002cfe7655220004fd765522002cfc7655220004ff7558e20024fe7558e20024fc7558e20004ff745
  | 12 => 0xe7648530004fc7648530015de7348530005dd7348530007cd324853034dfa769413002efa7694130155f97594130026fa6594130026f8659413002fba749413002fb97494130006fb6494130006f96494130015fa739413002df8739413002efb639413002fdb639413016fdb3294130007d93294130005f971941300ff7b519413000779519413016fdb3194130007d93194130024ff7654130014fe7654130154fd7654130014fc76541300067f65541300267c6554130005df7354130015dc735413002f785054130015f87654130026f87654130014f8765413002dfb755413002f7b75541300077b6554130026fa6554130026f865541300ff786554130006fb6454130006f964541303477a54541300ff785454130007db7354130015fa7354130015f87354130157d8735413002efb635413002fdb63541301577b53541301577953541300ff7b5254130007795254130157db3254130007d93254130005fb71541300ff7b5154130007795154130157db3154130007d9315413001cff7650130014fe7650130124fd7650130014fc7650130006bf645013001ebc6450130005df7350130015dc7350130126fb605013002fd8305013004e7f7559720004ff745972001cfe745972001cfc74597200e67f5459720004ff7359720014fe7359720014fc73597200067e53597200e67c535972002cfc725972004e7e525972004e7c525972004eee3259720004ff715972000cfe715972000cfc71597200e67f51597200e67f5059720004ff7559320024fe7559320024fc755932004ebf7459320004ff7359320014fe7359320014fc735932002cfc725932004ebe425932004ebc4259320004ff715932000cfe715932000cfc71593200debf415932004eef21593200debf405932004efa205932004ef92059320004ff765532004cfe7655320004fd765532004cfc76553200267e65553200067d6555320004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f2004edf7358f20006df5358f200d6dc5358f200d6de4358f2002cfc7258f2004ede3258f2004edc3258f20004ff7158f2000cfe7158f2000cfc7158f200d6df3158f2004eef2158f200d6df3058f20004ff7654f2004cfe7654f20004fd7654f2004cfc7654f20004ff7650f2004cfe7650f20004fd7650f2004cfc7650f200057f7550f200e57c7550f2033ebf6450f2001ebc6450f20016de6350f20006dd6350f2004def764cb20076ef764cb2004eef654cb20006ed654cb201f6ee644cb2004eec644cb2004fcf734cb2004fcf634cb20016ee634cb2004eec634cb2004fcc634cb20337cf534cb200d7cc534cb200d7ce434cb20007cd434cb20005ef714cb200d7cf314cb2002dee704cb2002dec704cb200d7cf304cb20004ff7558720
  | 13 => 0x8930004fd71d893000cfc71d89300b6df31d89300fd7e75989300057d7598930006ef6298930095f970989300d5fb705893004eee6218930006ed6218930004fe7694930004fd769493004cfc7694930015de7394930005dd7394930004ff7654930004fe7654930004fc76549300067f65549300267c6554930004fe7690930004fd769093004cfc7690930015de7390930005dd7390930004ff7650930004fe7650930004fc765093002cdc764c9301fede654c9301fedc654c930006df644c930006dd644c930015df724c930017cf724c930007cf624c93004ede624c93004edc624c930007cc624c930007ce524c930007cd524c93035fcf424c93035fcc424c930005df714c930007db704c93002dde704c93002ddc704c930007d8704c930016df604c930017db604c93000cfe76d85300eef661d8530024fe75d8530004fd75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853002cfd73d853000cfc73d853004cfe72d8530004fd72d8530056df32d8530006dd32d85300eef631d8530056f531d8530014fd70d85300eef710d85300eef46158530355fb70585300267f76d45300fe7e76d45300fe7d76d45300267c76d45300067f64d45301e67e64d45300067d64d45301e67c64d453030e7f63d45300067f62d45303167c62d45301df5f32d45300075d32d45300ed7d71d45300ee7f61d453000e7e61d453000e7c61d45300ef5f31d45300ff7a70d45300ff7970d45302c67f60d45301df7b30d453030f5e30d453030f5c30d45301df7830d4530004ff7654530004fe7654530004fc76545300067f65545300267e65545300067d65545300267c65545300067f76545300067e76545300067d76545300067c76545300067f64545301d67e64545300067d64545301d67c64545302d67f63545300067f62545303067c62545301cf5f32545300075d32545300ed7f71545300ff7771545300ee7f615453000e7e615453000e7c61545300ef7641545300ef5f31545300ef7631545301cf7531545300077a70545300077970545302c67f60545301cf7b30545302d75e30545302d75c30545301cf783054530004ff7650530004fe7650530004fc765053001ebe6450530006bd645053000775515053002ddc764c53000edc764c53002cdc764c530006df644c530006dd644c530005df724c530006df624c530015df714c530017d7714c530007d7614c53000ede614c53000edc614c5300efd4614c5300ef5f514c5300efd6514c5300ef5d514c530007d5514c53000755514c530007db704c53002dde704c53002ddc704c530007d8704c530016df604c530017db604c5300efd7104c530004fe76c8530004fd76c853004cfc76c8530015de73c8530005dd73c853004eee62c8530007cd32c8530004ff7648530004f
  | 14 => 0x1d67e64546300067d64546302d67c64546300075f73546301cf5c73546301cf5e43546300075d43546303067e62546300067d62546301177771546302d67f615463000e7e61546301067d615463000e7c61546301077641546301077631546301cf7531546302d77a70546300077970546302d67e60546302d75f30546301cf7b30546302d77830546302d77a1054630004ff7650630004fd765063002cfc765063001ebe6450630006bd64506300079d435063000775515063004cff76c863002cfe76c8630004fd76c863004eee62c8630006ed62c8630004ff7648630004fd764863002cfc764863004eee6248630006ed624863000ef66148630006f5614863002dfb7654230386fb765423002f7b755423002f7b6554230026fa655423002ef8655423002f78655423002efb6454230006f9645423037f7a5454230117785454230015fa7354230015f873542301577b5354230157795354230157da4354230007d943542301177b5254230007795254230005fb71542301177b5154230007795154230024fe76d95300fe7e65d953001cfe74d9530004fd74d953001cfc74d95300067e54d95300fe7c54d953002cff73d9530014fe73d953002cfd73d9530014fc73d953016e7f53d953016e7d53d953004cfe72d9530004fd72d95300fe7f52d953000cfe71d9530004fd71d953000cfc71d95300fe7f51d9530014fd70d95300fe7f50d95300fe7c6559530375fb705953016cff75595300067f7559530004ff745953001cfe745953001cfc7459530154ff7359530006df7359530004ff725953004cfc7259530004ff715953000cfe715953000cfc71595300fe7f5159530374ff7059530006fb705953001cfe76d91300f6be64d9130024fe75d9130004fd75d9130024fc75d913002cff73d9130014fe73d913002cfd73d9130014fc73d9130136bf43d9130136bd43d913004cfe72d9130004fd72d9130136df32d913000cfe71d9130004fd71d913000cfc71d9130136df31d9130014fd70d91300f6bf40d9130136fb30d913036ede30d913036edc30d9130136f830d91300057f75591300fd7c75591300f6bc6459130365fb7059130004ff75591300067f75591300047f7559130024fe7559130024fc75591300067c75591300247c7559130134ff7459130006bf7459130124ff7359130006df7359130004ff725913004cfc7259130126df3259130004ff715913000cfe715913000cfc71591300f6bf4159130126df3159130364ff7059130006fb7059130126fb30591302fede30591302fedc3059130126f83059130004ff7655130004fe7655130004fd7655130004fc7655130024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d893002cfd73d89300b6ee32d89300b6ed32d893000cfe71d
  | 15 => 0x9415414002e7f7559630004ff745963001cfe745963001cfc74596300067e54596301167c54596301567f53596301567d5359630156de4359630004ff725963004cfc72596301167f5259630004ff715963000cfe715963000cfc71596301167f515963002cfe705963002cfc705963002e7e505963002e7c5059630004ff7559230024fe7559230024fc755923002ebf7459230006bf545923010ebc5459230126bf4359230126bd4359230004ff725923004cfc725923010ebf4259230004ff715923000cfe715923000cfc715923010ebf415923002cfe705923002cfc705923002efa505923002ebe405923002ebc4059230126fb305923002ef8305923002efa1059230004ff765523002cfe7655230004fd765523002cfc76552302fddf7650e3001edf7650e3001cdf7650e300075f7550e300075c7550e302fedf6550e30006dd6550e30015df7450e300179f7450e3001ede6450e302ff9e6450e302ff9d6450e3001edc6450e3010f9e5450e300079d5450e3010f9c4250e3010f9f4150e302fddf7050e30007db7050e302ffd87050e30016de6050e30017da6050e302ffda5050e302ff9f4050e302ff9d4050e30004ff7558a30024fe7558a30024fc7558a30004ff7458a3001cfe7458a3001cfc7458a30096de4358a30006dd4358a3002eef7258a30096ee3258a30096ed3258a30004ff7158a3000cfe7158a3000cfc7158a3002cfc7058a3002edf3058a3002edd3058a3002eee2058a3002eec2058a3002efa1058a3004cff7694a3002cfe7694a30004fd7694a30015de7394a30005dd7394a30004ff7654a30004fd7654a3002cfc7654a300267e6554a300067d6554a3004cff7690a3002cfe7690a30004fd7690a300079d4390a30004ff7650a30004fd7650a3002cfc7650a3001ebe6450a30006bd6450a30004ff7558630024fe7558630024fc7558630004ff745863001cfe745863001cfc7458630036de4358630006dd4358630004ff725863004cfc725863002ef77158630106f63158630036f53158630106f6215863002cfe705863002cfc705863002edf305863002edd305863002ef6105863002ef410586300267f76d463030e7e76d46301167d76d46300267c76d463030e7f64d46301e67e64d46300067d64d463030e7c64d46301df5e43d46300075d43d46303167e62d46300067d62d463030e7f61d463000e7e61d46301067d61d463000e7c61d463030f7a70d46301177970d463030e7e60d463030f5f30d46301df7b30d463030f7830d463030f7a10d4630004ff7654630004fd765463002cfc76546302d67f65546300267e65546300067d65546300267c6554630005df7354630015dc735463002dfa70546302d77a50546300067f76546302d67e76546300067d76546302d67c76546302d67f6454630
  | 16 => 0x45400267e65545400067d65545400267c6554540005bf745454001dbc745454012f3f54545401d73c54545400067f76545400067e76545400067d76545400067c76545400073f74545401d73c74545402d67f64545400067f63545401ce7e63545401ce7c63545401d73f43545400073d43545400067f62545403067c62545401d73f42545400073d425454011d7f715454012f77715454011e7f615454000e7e615454000e7c615454011f3f415454011f7641545401d775415454011f7631545400077a70545400077970545402ce7f60545401d77b40545402d73e40545402d73c40545401d778405454039f7b305454039f78305454002dbc765054000ebc765054002cbc765054012dbe755054012dbc7550540005bf7350540006bf6350540005bf7250540006bf625054001dbf715054001fb77150540007b7615054000ebe615054000ebc615054011fb4615054011f3f515054011fb6515054011f3d5150540007b5515054000735515054011fb62150540007bb705054002dbe705054002dbc7050540007b8705054001ebf605054001fbb6050540397bb3050540397b83050540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c540016de634c5400079d434c54000775514c540005fb704c54002df8704c540127db304c540004fe76c8540004fd76c854004cfc76c854001dbe74c8540005bd74c854004eee62c8540007ad42c854002dfa70c8540005f970c8540004ff7648540004fe7648540004fc764854001dbe7448540005bd7448540007ad424854000ef66148540007b5414854038dfa769414002efa769414015df97594140026fa6594140026f8659414001dfa749414002fba749414001dba749414002fb9749414002df8749414002efb649414002fbb649414012fbb5494140177b85494140125fa739414002df87394140006fb6394140177bb4394140007b94394140005f97294140177bb4294140007b94294140005f9719414012f7b5194140007795194140177bb4194140007b94194140024ff765414001cfe765414015cfd765414001cfc76541400067f65541400267c6554140005bf745414001dbc745414015f3c545414001df87654140026f8765414001cf8765414002dfb755414002f7b75541400077b6554140026fa6554140026f8655414012f786554140007bb745414001dfa745414001df8745414015fb8745414002efb645414002fbb645414012fbb545414015f7a545414015f78545414015fb8545414015f385454140125fa7354140125f87354140006fb635414012f7b535414000779535414015fbb4354140007b94354140005fb725414012f7b525414000779525414015fbb4254140007b94254140005fb715414012f7b515414000779515414015fbb4154140007b
  | 17 => 0x1dbf7350d4001f9f7350d400079f6350d40016be6350d40016bc6350d401279c6350d401279e5350d400079d5350d40005bf7250d4033ebc6250d401279f3250d40005bf7150d401279f3150d40007bb7050d4002dbe7050d4002dbc7050d40007b87050d4001ebf6050d4001fbb6050d40127bb3050d402ff9c3050d40127b83050d40127983050d40024fe75d8940004fd75d8940024fc75d894002cfd74d8940014fe73d8940004fd73d8940014fc73d89400beee42d89400beed42d894000cfe71d8940004fd71d894000cfc71d89400bebf41d8940006ee21d8940006ec21d8940006ef629894009df970989400ddfb705894012d7e75189400057d7518940125de7318940005dd731894004eee6218940006ed621894011df67118940005f57118940004fe7694940004fd769494004cfc769494001dbe7494940005bd7494940125de7394940005dd739494002dfa7094940005f97094940004ff7654940004fe7654940004fc76549400267e65549400067d6554940005bf745494001dbc745494012f3f545494002cbc765094012dbe755094012dbc7550940005bf735094001dbf725094001faf7250940007af625094004ebe625094004ebc6250940007ac625094004eac6250940007ae5250940007ad5250940005bf7150940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb60509403b7bb30509403b7b83050940004fe768c940004fd768c94004cfc768c94012d7e758c9400057d758c94001dbe748c940005bd748c940006ef628c94004eec628c94020faf428c94002dfa708c940005f9708c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940016de634c9400079d434c940006ef624c94004eec624c9401f7af424c940005fb704c94002df8704c940127db304c94000cfe76d854011ef661d8540024fe75d8540004fd75d8540024fc75d854002cfd74d854000cfc74d8540014fe73d8540004fd73d8540014fc73d854005ebf43d8540006bd43d854004cfe72d8540004fd72d854005ebf42d8540006bd42d854011ef641d854005ef541d854001cfd70d854011ef710d8540005ef7258540005ec725854011ef461585403adfb70585400267f76d454012e7e76d454012e7d76d45400267c76d454012f3f74d45401e73c74d454030e7f64d45400067f63d45401de7e63d45401de7c63d45401e73f43d45400073d43d45400067f62d45403167c62d45401e73f42d45400073d42d454011d7d71d454011e7f61d454000e7e61d454000e7c61d454011f3f41d454012f7a70d454012f7970d45402ce7f60d45401e77b40d454030f3e40d454030f3c40d45401e77840d45403a77b30d45403a77830d4540004ff7654540004fe7654540004fc76545400067f655
  | 18 => 0x771546402d67f615464000e7e615464013e7d615464000e7c615464013f7641546401d775415464013f7631546402d77a70546400077970546402d67e60546402d73f40546401d77b40546402d77840546403d77b30546402d77830546402d77a1054640004ff764c640004fd764c64002cfc764c6401b67e654c6400067d654c640016de634c640006dd634c64000ef6614c640006f5614c64000775514c640005fb704c64002df8704c640137db304c64004cff76c864002cfe76c8640004fd76c86401a67e65c86400067d65c864004eee62c8640006ed62c864002dfa70c8640005f970c8640004ff7648640004fd764864002cfc764864018e7e65486400067d654864004eee6248640006ed624864000ef66148640006f5614864002dfa704864002dfb76542403cefb765424002f7b7554240026fa655424002f7a65542400267a655424002f79655424002ef8655424001dfa745424001df8745424015f7a545424015f785454240135fa7354240135f87354240006f963542401477b5354240007795354240005fb72542401477b5254240007795254240005fb71542401477b5154240007795154240024fe76d954012e7e65d954001dbe74d954002dbd74d954012f3f54d954002cff74d954001cfe74d954002cfd74d954012ebd74d954002cbd74d954001cfc74d95401767f54d954012ebf54d95401767d54d9540176bc54d9540014fe73d9540004fd73d9540014fc73d95400067e53d954012e7c53d9540176bf43d954004cfe72d9540004fd72d954000cfe71d9540004fd71d954000cfc71d954012e7f51d954001cfd70d954012e7f50d954012e7c655954015f3c54595403c5fb7059540174ff75595400067f755954015cff7459540006bf745954012ebf545954015e7e545954015e7c545954015ebc5459540004ff7359540014fe7359540014fc735954015ebf4359540004ff725954004cfc725954012e7f5259540004ff715954000cfe715954000cfc715954012e7f51595403c4ff7059540006fb7059540014fe76d8d40126de63d8d4002dfa70d8d4001df970d8d40127db30d8d40024fe75d8d40004fd75d8d40024fc75d8d4002cfd74d8d40014fc74d8d40126de43d8d4010edd43d8d4004cfe72d8d40004fd72d8d4000cfe71d8d40004fd71d8d4000cfc71d8d4010ebf41d8d4001cfd70d8d40126f970d8d4001cf970d8d40126df30d8d40126fb30d8d40126f830d8d400057f7558d4012d7c7558d40126dc6358d403bdfb7058d40127d83058d40004ff7654d40004fe7654d40004fc7654d40005bf7454d4001dbc7454d40005fb7054d4002df87054d4002dbc7650d40016bc7650d4002cbc7650d400073f7550d4012dbe7550d4012dbc7550d400073c7550d4012d3c7550d40006bf6550d40006bd6550d40
  | 19 => 0x964002e7f305964002e7e305964002e7d305964002e7c305964002e7f205964002e7e205964002e7d205964002e7c205964002e7f105964002e7e105964002e7d105964002e7c1059640004ff7558e40024fe7558e40024fc7558e4002edf7358e40136de4358e400f6dd4358e40004ff7258e4004cfc7258e40136df3258e40004ff7158e4000cfe7158e4000cfc7158e40136df3158e4002cfe7058e4002cfc7058e4002ef87058e4002cf87058e4002efa5058e4002ebf4058e4002ebd4058e40136fb3058e4002ede3058e4002edc3058e4002ef83058e4002efa1058e40004ff7654e40004fd7654e4002cfc7654e400267e6554e400067d6554e40005fb7054e4002df87054e40004ff7558a40024fe7558a40024fc7558a40004ff7358a40014fe7358a40014fc7358a4002eef7258a4009eee4258a4009eed4258a40004ff7158a4000cfe7158a4000cfc7158a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a4002efa1058a4004cff7694a4002cfe7694a40004fd7694a400267e6594a400067d6594a40135de7394a40005dd7394a4002dfa7094a40005f97094a40004ff7654a40004fd7654a4002cfc7654a400267e6554a400067d6554a4002dfa7054a4004cff768ca4002cfe768ca40004fd768ca401457e758ca400057d758ca402167e658ca400067d658ca4004eee628ca40006ed628ca4002dfa708ca40005f9708ca40004ff764ca40004fd764ca4002cfc764ca401fe7e654ca400067d654ca40016de634ca40006dd634ca4004eee624ca40006ed624ca40005fb704ca4002df8704ca40137db304ca40004ff7558640024fe75586400067e75586400067d7558640024fc7558640004ff7358640014fe7358640014fc7358640004ff725864004cfc725864002ef7715864013ef6415864003ef5415864013ef6315864013ef6215864002cfe705864002cfc705864002ebf405864002ebd405864002efa205864002ef6105864002ef4105864030d7f76d46400267f76d46400247f76d464030e7e76d464030d7d76d46401467d76d46400047d76d46400267c76d46401de7e63d46400067d63d464030e7c63d46403167e62d46400067d62d464030e7f61d464000e7e61d464013e7d61d464000e7c61d464030f7a70d46401477970d464030e7e60d464030f3f40d46401e77b40d464030f7840d46403df7b30d464030f7830d464030f7a10d4640004ff7654640004fd765464002cfc76546402d67f65546400267e65546400067d65546400267c655464002dfa70546402d77a50546402d57f76546400067f76546400047f76546402d67e76546402d57d76546400067d76546400047d76546402d67c76546401ce7e63546400067d63546402d67c63546403067e62546400067d62546401477
  | 20 => 0x4fe768c950004fd768c95004cfc768c9500257e758c9500057d758c95004eee628c9500076d528c950004ff764c950004fe764c950004fc764c9500257e754c9500057d754c950006df634c950016dc634c9501ff5f534c9500076d524c95000cfe76d855014ef661d855030e7f75d855002cfd75d855000cfc75d855000c7c75d855001cfe74d8550004fd74d855001cfc74d85500067e54d85500667c54d8550014fe73d8550004fd73d8550014fc73d85500667f53d85500067d53d855004cfe72d8550004fd72d85500667f52d85500067d52d855014e7f51d855014ef651d8550066f551d8550024fd70d855030e7e50d855030e7c50d855014ef710d8550005df7358550155dc735855014ef461585503e5fb70585502d67e765455002d7c765455000e7c765455002c7c765455015d7e745455015d7c74545500067f64545501d67e64545501d67c64545500057f73545500067f63545501ce7e63545501ce7c63545500057f72545500067f62545503067c62545500257f715455002777715455014e7f615455000777615455000677615455000e7e615455000e7c615455014f74615455014f76415455014f7631545500077b705455002d7e705455002d7c70545500077870545500267f60545500277b6054550004ff7650550004fe7650550004fc76505500057f75505500257c7550550007755150550004ff764c550004fe764c550004fc764c5500257e754c5500057d754c55000ef6614c55000775514c550004fe76c8550004fd76c855004cfc76c85500257e75c85500057d75c8550004ff7648550004fe7648550004fc76485500257e75485500057d7548550005fb704855002df8704855002e7f755964015e7f545964015e7d5459640004ff7359640014fe7359640014fc73596401467f53596400067e53596401467c5359640004ff725964004cfc72596401467f52596401467c5259640004ff715964000cfe715964000cfc71596401467f51596400067e51596401467c515964002cfe705964002cfc705964002e7e505964002e7c505964015e7f745964015e7e745964015e7d745964015e7c74596400067f73596400067e73596400067d73596400067c735964015e7f435964015e7e435964015e7d435964015e7c43596400067f72596400067e72596400067d72596400067c725964015e7f425964015e7e425964015e7d425964015e7c42596400067f32596400067c32596400067f71596400047f71596400067e71596400067d71596400067c715964015e7f415964015e7e415964015e7d415964015e7c41596400067f31596400067e31596400067c31596400067e21596400067c215964002e7f705964002e7e705964002e7d705964002e7c705964002e7f405964002e7e405964002e7d405964002e7c405
  | 21 => 0x631546502d57f70546500077b70546502d77870546500267e60546500277a6054650004ff7650650004fd765065002cfc765065001ebe6450650006bd6450650007755150650004ff764c650004fd764c65002cfc764c6501aebe644c650006bd644c650016de634c650006dd634c65000ef6614c650006f5614c65000775514c65004cff76c865002cfe76c8650004fd76c865019ebe64c8650006bd64c865004eee62c8650006ed62c8650004ff7648650004fd764865002cfc7648650186be6448650006bd644865004eee6248650006ed624865000ef66148650006f56148650005fb704865002df8704865001cfe76d91500257e75d915015ebe64d915015f3e54d915002cfd75d915002c7d75d915001cfc75d915015e7e54d915015ebe54d9150146bd54d915015e7c54d9150014fe73d9150004fd73d9150014fc73d915004cfe72d9150004fd72d91501467f52d915000cfe71d9150004fd71d915000cfc71d91501467f51d9150024fd70d915015ebf40d915015ebc645915015f3c54591503f5fb7059150014fe76d8d50156de63d8d5002cfd75d8d50014fc75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d50156de53d8d50116dd53d8d50156de43d8d5004cfe72d8d50004fd72d8d50156df32d8d5000cfe71d8d50004fd71d8d5000cfc71d8d501167f51d8d50006de31d8d50156dc31d8d50024fd70d8d50156df30d8d50156dc6358d503edfb7058d5002d7c7654d500167c7654d5002c7c7654d5015d7e7454d5015d7c7454d500257f7354d500275f7354d500075f6354d500167e6354d500167c6354d501575c6354d501575e4354d500057f7254d500057f7154d500077b7054d5002d7e7054d5002d7c7054d50007787054d500267f6054d500277b6054d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257c7550d5001ebe6450d5015f3e5450d50006df6350d50016dc6350d500075d5350d5002cfd75d895001cfe74d8950004fd74d895001cfc74d8950014fe73d8950004fd73d8950014fc73d89500c6ee52d89500c6ed52d895000cfe71d8950004fd71d895000cfc71d89500c67f51d8950155de7398950005dd7398950006ef62989500a5f970989500e5fb705895004eee6218950006ed621895002c7c765495015d7e745495015d7c74549500067f64549500057f73549502567e63549502567c63549500257f72549500276f72549500076f625495004e7e625495004e7c62549500076c62549500057f71549500077b705495002d7e705495002d7c70549500077870549500267f60549500277b6054950004fe7690950004fd769095004cfc76909500257e75909500057d75909500076d5290950004ff7650950004fe7650950004fc76509500057f75509500257c75509500076d5250950
  | 22 => 0x925012ebf535925012ebe535925012ebd535925012ebc5359250006bf7259250006be7259250006bd7259250006bc725925012ebf525925012ebe525925012ebd525925012ebc5259250006bf3259250006bc3259250006bf7159250006be7159250006bd7159250006bc715925012ebf515925012e3f515925012ebe515925012ebd515925012ebc5159250006bf3159250006be3159250006bc3159250006be2159250006bc215925002ebf705925002ebe705925002ebc705925002ebf505925002ebe505925002ebd505925002ebc505925002ebf305925002ebe305925002ebd305925002ebc305925002ebf205925002ebe205925002ebd205925002ebc205925002ebf105925002ebe105925002ebd105925002ebc1059250004ff7458e5001cfe7458e5001cfc7458e5002edf7358e5016ede5358e500fedd5358e50004ff7258e5004cfc7258e5016edf3258e50004ff7158e5000cfe7158e5000cfc7158e500fe7f5158e5016edf3158e5002cfe7058e5002cfc7058e5002e7f5058e5002e7d5058e5002ede3058e5002edc3058e50004ff7650e50004fd7650e5002cfc7650e500057f7550e500257c7550e5001ebe6450e50006bd6450e50016dc6350e5002dfa7050e50004ff7458a5001cfe7458a5001cfc7458a50004ff7358a50014fe7358a50014fc7358a5002eef7258a500a6ee5258a500a6ed5258a50004ff7158a5000cfe7158a5000cfc7158a500a67f5158a5002cfc7058a5002e7f5058a5002e7d5058a5002efa4058a5002eee2058a5002eec2058a5004cff7690a5002cfe7690a50004fd7690a5001ebe6490a50006bd6490a50004ff7650a50004fd7650a5002cfc7650a5001ebe6450a50006bd6450a5004cff768ca5002cfe768ca50004fd768ca500257e758ca500057d758ca5020ebe648ca50006bd648ca5004eee628ca50006ed628ca50004ff764ca50004fd764ca5002cfc764ca501f6be644ca50006bd644ca50016de634ca50006dd634ca5004eee624ca50006ed624ca500067d7558650004ff745865001cfe745865001cfc7458650004ff7358650014fe7358650014fc7358650004ff725865004cfc725865002ef771586501667f5158650166f65158650046f55158650166f63158650166f6215865002cfe705865002cfc705865002e7f505865002e7d505865002efa405865002efa305865002ef6105865002ef410586502d57f765465000e7f765465000c7f76546501d67e64546502d73e64546501d63e64546500067d64546502d73d64546500063d64546502d67c64546501ce7e63546500067d63546502d67c63546503067e62546500067d62546500257f715465002777715465000e7e61546502d77661546501667d61546502d775615465000675615465000e7c61546501677641546501677
  | 23 => 0x4def745092104faf7450921007af645092101eee645092101eec6450921187ac6450921005ef7350921007e7715092100dee715092100dec715092121fe4715092104eef615092104fe7615092121f6f515092121f6d515092121faf415092121fe6415092121fad4150921005ef7050921187af405092121fe71050921405ee768c92104eee768c92104f6e758c92104f6d758c921006ef658c921006ed658c92104def748c921005ed748c92120eee648c92120eec648c9211eded738c921016ee638c921016ec638c92100dee718c92100dec718c92104eef618c92104fe7618c9212076f518c9212076d518c921207e6418c921005ed708c921207e7108c921014ff764c92100cfe764c9211ecfd764c92100cfc764c921006df634c921016dc634c92104fcc324c921005f7714c92100df4714c92100dec764c921016ec764c92100cec764c921006ef654c921006ed654c921005ef744c921005ed744c9211f6ee644c9211f6ec644c92104def734c92104fcf734c921007cf634c921016ee634c921016ec634c92117fcc634c9213ffcf534c92117fcc534c92117fce434c921007cd434c921007e7714c92100dee714c92100dec714c9211efe4714c92100de4714c92104eef614c92104fe7614c9211ef6f514c9211ef6d514c9211efe6414c9211efcf314c9211efcd314c921005ef704c92117fcf304c9211efe7104c92104df4765052101ef4765052104cf47650521006f76550521006f5655052100df7745052100fb77450521007b7645052101ef6645052101ef46450521187b46450521187b74350521007b54350521007e7725052104df6725052104df47250521007e4725052100ef7625052100fe76250521187b74250521187e64250521007b54250521187e54250521007a54250521007e63250521007e53250521005f77050521187b74050521024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121014fe73d8121004fd73d8121014fc73d8121006ee32d8121006ed32d812104cfd71d81210ce7f51d81210ce7d51d8121006fb30d8121006f830d81210cefa10d8121006fb609812118d7e75181210057d7518121185be7418121005bd741812117dde7318121005dd731812102efa6018121006f9601812102ebf7459250176be545925012ebd5459250004ff7359250014fe7359250014fc7359250176bf4359250006be4359250176bc4359250004ff725925004cfc7259250176bf4259250176bc4259250004ff715925000cfe715925000cfc715925012e7f5159250176bf4159250006be4159250176bc415925002cfe705925002cfc705925002ebe405925002ebc405925012ebe755925012ebd7559250176bc7559250006bf7359250006be7359250006bd7359250006bc735
  | 24 => 0xe535952118e7c5359521424ff7259521006ef72595213067e52595213067c525952124cff7159521006f7715952124e7f515952124e7d515952124ef64159521004ff705952102cfc705952118e7f505952101cfe76d9121186be64d9121024fe75d9121004fd75d9121024fc75d9121006bf54d9121186bc54d9121014fe73d9121004fd73d9121014fc73d9121186bf43d912100cfd72d9121186bf42d912104cff71d912104cfd71d91212367f51d91212367d51d9121236bf41d9121236bd41d912102cfe70d9121004fd70d9121186bc645912141def7259121004ff7559121024fe7559121024fc7559121234ff7459121006bf7459121004ff7359121014fe7359121014fc735912141cff7259121006ef725912121cff7159121006f7715912121e7f515912121e7d5159121004ff705912102cfc7059121186bf4059121004ff7655121004fe7655121004fd7655121004fc76551210267e65551210067d6555121014fe76d8d2118d7e75d8d210057d75d8d2117ede63d8d21024fe75d8d210067e75d8d210247e75d8d21004fd75d8d210067d75d8d210047d75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2100cfd72d8d2117edf32d8d2104cff71d8d2104cfd71d8d212067f51d8d212067d51d8d21206df31d8d21206dd31d8d2102cfe70d8d21004fd70d8d21206f710d8d2117edc6358d21415ef7258d21005fb7058d21005f87058d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21204ff7358d21006df7358d2117ede4358d21414ff7258d21006ef7258d211ecff7158d21006f77158d211ee7f5158d211ee7d5158d21004ff7058d21006fb7058d21004fb7058d2102cfc7058d21006f87058d2102cf87058d2117edf3058d211eef71058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d2118d7c7550d21006bf6450d2101ebc6450d21016de6350d21006dd6350d21024ff765492100cfe765492124cfd765492100cfc76549210067f65549210267c6554921005f7715492100df4715492104fe4215492140dee769092104eee7690921006ef6590921006ed659092121ded749092101eee649092101eec6490921005ed7390921187af4390921007ad439092104fe7719092100dee719092100dec719092104fe4719092104eef619092104fe761909212376f51909212376d5190921237e64190921005ed7090921237e7109092101cff765092100cfe765092121cfd765092100cfc7650921006bf645092101ebc645092104fac4250921005f7715092100df4715092104fe4215092100dec765092101eec765092100cec7650921006ef6550921006ed6550921
  | 25 => 0x972104e7e525972104e7c525972104eee425972104eee325972124e7f515972124e7d5159721004ff705972102cfc70597211a67f5059721004ff7559321024fe7559321024fc755932104ebf7459321004ff7359321014fe7359321014fc735932100cfe725932100cfc725932104ebe425932104ebc425932121e7f515932121e7d515932121ebf415932121ebd415932104ef6215932104ef52159321004ff705932102cfc705932119ebf4059321004ff765532104cfe7655321004fd765532104cfc76553210267e65553210067d6555321004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f2104edf7358f21006df5358f21196dc5358f21196de4358f2100cfe7258f2100cfc7258f2104ede3258f2104edc3258f211ee7f5158f211ee7d5158f211eedf3158f211eedd3158f21004ff7058f2102cfc7058f21196df3058f2104eef2058f21004ff7654f2104cfe7654f21004fd7654f2104cfc7654f21004ff7650f2104cfe7650f21004fd7650f2104cfc7650f210057f7550f211a57c7550f2133ebf6450f2101ebc6450f21016de6350f21006dd6350f2104dee7250f2133fae4250f2104def7650b2143eef7650b2104eef6550b21006ed6550b2104faf7450b2104faf6450b2101eee6450b2104eec6450b2104fac6450b21005ef7350b2100dee7150b2100dec7150b2121f6f5150b2121f6d5150b2121faf4150b2121fad4150b21005ef7050b2119faf4050b2104def764cb21436ef764cb2104eef654cb21006ed654cb21005ef744cb21005ed744cb211f6ee644cb2104eec644cb2104fcf734cb2104fcf634cb21016ee634cb2104eec634cb2104fcc634cb2142fcf534cb21197cc534cb21197ce434cb21007cd434cb2100dee714cb2100dec714cb211ef6f514cb211ef6d514cb211efcf314cb211efcd314cb21005ef704cb21197cf304cb21004ff7558321024fe7558321024fc7558321004ff745832101cfe745832101cfc7458321004ff7358321014fe7358321014fc735832100cfc725832104eee3258321006ed325832108e7f515832108e7d515832104ef6215832104ef5215832104efb705832104efb205832104ef8205832108efa1058321024fe76d952118e7e65d952101cfe74d9521004fd74d952101cfc74d9521014fe73d9521004fd73d9521014fc73d952100cfd72d952118e7f52d952104cff71d952104cfd71d95212667f51d95212667d51d9521266f641d952102cfe70d9521004fd70d952118e7c6559521005bf7459521185bc7459521425ef7259521264ff75595210067f7559521004ff7459521006bf7459521004bf745952101cfe745952101cfc7459521006bc745952101cbc745952118e7f5459521004ff7359521014fe7359521014fc73595210067
  | 26 => 0x5dd73909310079d4390931004ff7650931004fe7650931004fc7650931015de735093100ddc764c93104edc764c93100cdc764c9311fede654c9311fedc654c931005df744c931005dd744c931006df644c931006dd644c931015df724c931017cf724c931007cf624c93104ede624c93104edc624c931007cc624c931007ce524c931007cd524c93144fcf424c93144fcc424c931007d7714c93100dde714c93100ddc714c9311efd4714c931016df614c931017d7614c9311ef5f514c9311efd6514c9311ef5d514c931005df704c9311efd7104c931015f47654531026f47654531014f4765453100df7755453100f777554531007776554531026f66554531026f465545311b7746554531006f76454531006f564545311b77754545314477654545310077554545311b7745454531007d77354531015f67354531015f473545311cfd4735453100ef7635453100fd763545311cf7753545311cf7653545311cf7553545311cf7453545311cfd64354531007d543545311b77752545310077652545310077552545311b77452545311cfd73254531007d53254531005f770545311b77750545311b77450545311cfd730545311b77776545310267776545311cf7476545310267476545310077774545314477674545310077574545314477474545310077764545310067764545314477664545310077564545310067564545314477464545311cf7773545310075773545311cf7673545311cf7573545311cf7473545311cf54735453100f77635453100e77635453100f5763545311cf7743545311cf7643545311cf5643545311cf7543545310075543545311cf7443545310077772545310077672545310077572545310077472545310077762545310077662545310077562545310077462545314477742545310077642545310077542545314477442545311cf7732545311cf5732545311cf7632545311cf7532545310075532545311cf7432545310077770545310077670545310077570545310077470545314477740545314477440545311cf7730545311cf5730545311cf74305453102cfe76d81310077551d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d813100cfd73d813104cfe72d8131004fd72d8131356df32d8131006dd32d8131014fd71d81312c67f51d81312c67d51d8131356fa30d81312c6fa10d8131007755198131006fb60981310077551581311b57e75181310057d75181311adbe7418131005bd7418131005ee7218131005ed721813100775511813102efa6018131006f9601813104e7f7559721004ff745972101cfe745972101cfc74597211a67f5459721004ff7359721014fe7359721014fc73597210067e53597211a67c535972100cfe725972100cfc725
  | 27 => 0xe74d9531004fd74d953101cfc74d95310067e54d95311b67c54d953100cff73d953100cfd73d953148e7f53d953148e7d53d953148ede43d953104cfe72d9531004fd72d95311b67f52d9531014ff71d9531014fd71d95314867f51d95314867d51d953102cfe70d9531004fd70d9531024ff76595311b67c655953147ddf73595311ddf77159531484ff75595310067f7559531004ff745953101cfe745953101cfc745953147cff7359531006df73595311ce7e53595311ce7c53595311cede4359531004ff725953104cfc725953128cff7159531006f7715953128e7f515953128e7d5159531004ff705953102cfc70595311b67f505953101cfe76d91311aebe64d9131024fe75d9131004fd75d9131024fc75d913127cfd74d913100cff73d913100cfd73d9131476bf43d9131476bd43d913104cfe72d9131004fd72d9131476df32d9131014ff71d9131014fd71d91314667f51d9131466f651d91314667d51d9131466bf41d9131466bd41d913102cfe70d9131004fd70d913101cff76591310057f75591311b57c75591311aebc645913145ddf735913146df77159131004ff75591310067f75591310047f7559131024fe7559131024fc75591310067c75591310247c7559131464ff7459131006bf745913145cff7359131006df7359131004ff725913104cfc72591311bedf325913127cff7159131006f7715913127e7f515913127ef6515913127e7d5159131004ff705913102cfc70591311aebf4059131004ff7655131004fe7655131004fd7655131004fc765513100ddc7650d3101edc7650d3100cdc7650d310075f7550d310075c7550d31006df6550d31006dd6550d31015df7450d310179f7450d310079f6450d3101ede6450d3101edc6450d311af9c6450d311af9e5450d310079d5450d31005df7250d311af9c4250d31007d77150d3100dde7150d3100ddc7150d3127fd47150d31016df6150d31017d76150d3127f5f5150d3127fd65150d3127f5d5150d3127f9f4150d3127f9d4150d31005df7050d312fedc6050d311af9f4050d3127fd71050d3104cfe76d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d893100cfd73d8931456de43d8931006dd43d8931456ee32d8931456ed32d8931014fd71d89314167f51d89314167d51d8931416ef21d893102cfe70d8931004fd70d8931456df30d8931416f710d89311b57e75989310057d7598931006ef629893117df57198931195f77158931005fb7058931005f8705893104eee6218931006ed6218931004fe7694931004fd769493104cfc7694931015de7394931005dd7394931004ff7654931004fe7654931004fc76549310067f65549310267c6554931004fe7690931004fd769093104cfc7690931015de7390931
  | 28 => 0x494100dbc765094104ebc765094100cbc7650941005bf735094101dbf725094101faf7250941007af625094104ebe625094104ebc6250941007ac6250941007ae5250941007ad5250941007b7715094100dbe715094100dbc715094121fb4715094101ebf615094101fb7615094121f3f515094121fb6515094121f3d515094121fb62150941005bf7050941004fe768c941004fd768c94104cfc768c9411c57e758c9410057d758c94101dbe748c941005bd748c941006ef628c94104eec628c94120faf428c94100df6718c941005f5718c941004ff764c941004fe764c941004fc764c94101dbe744c941005bd744c941016de634c9410079d434c941006ef624c94104eec624c9411f7af424c94101df47654541026f4765454101cf4765454100df7755454100f777554541007776554541026f66554541026f465545411c7746554541007b7745454101df6745454101df474545411d7b4745454100ef7645454100fb764545411d77754545411d77654545411d77554545411d7745454541006f763545411c77753545414977653545410077553545411c77453545411d7b74354541007b54354541005f772545411c77752545410077652545410077552545411c77452545411d7b74254541007b542545411c77750545411c77450545411d7b740545411c77776545410267776545411d77476545410267476545411d77774545410073774545411d77674545411d77574545411d77474545411d734745454100f77645454100e77645454100f3764545410077773545414977673545410077573545414977473545410077763545410067763545414977663545410077563545414977463545411d77743545411d73743545411d77643545411d77543545410073543545411d77443545410077772545410077672545410077572545410077472545410077762545410077662545410077562545410077462545411d77742545411d73742545411d77642545411d77542545410073542545411d77442545414977732545410077632545410077532545414977432545410077770545410077670545410077570545410077470545411d77740545411d73740545411d774405454149777305454149774305454102cfe76d81410077551d8141024fe75d8141004fd75d8141024fc75d814100cfd74d8141014fe73d8141004fd73d8141014fc73d81413aebf43d8141006bd43d814104cfe72d8141004fd72d81413aebf42d8141006bd42d814101cfd71d81412ce7f51d81412ce7d51d81412cef621d81413aefa40d81412cefa10d81411c57e75981410057d7598141007755198141006fb6098141005ef7258141005ec725814100775515814100775511814102efa6018141006f96018141024fe76d95311b67e65d953128cfd75d953101cf
  | 29 => 0x14f76415815114f7631581510077b60581512d67e60581512dd7e76181511d57e74181510057d74181512d57c74181511cd7e73181510057d73181512d57c73181513057e72181510057d72181510257f711815100d7e71181510257d711815100d7c711815130e7f61181514d77761181514cf7641181514cf7631181512d67f60181512d77a60181512d67d60181510077960181512d77a10181514cf791018151024fe76d95411c67e65d954129cfd75d954100cff74d954100cfd74d95414c67f54d95414c67d54d9541014fe73d9541004fd73d9541014fc73d95410067e53d95411c67c53d95414c6bf43d954104cfe72d9541004fd72d954101cff71d954101cfd71d95414be7f51d95414be7d51d954102cfe70d9541004fd70d95411c67f50d9541024ff76595411c67c65595414b5bf74595411e5f771595414bcff75595410067f75595414b4ff7459541006bf74595411d67e54595411d67c5459541004ff7359541014fe7359541014fc73595411d6bf4359541004ff725954104cfc72595411c67f525954129cff7159541006f7715954129e7f515954129e7d5159541004ff705954102cfc7059541014fe76d8d411bede63d8d41024fe75d8d41004fd75d8d41024fc75d8d4100cfd74d8d411bede43d8d414aedd43d8d4104cfe72d8d41004fd72d8d4101cfd71d8d4145e7f51d8d4145ef651d8d4145e7d51d8d4145edf31d8d4102cfe70d8d41004fd70d8d414aebf40d8d410057f7558d411c57c7558d411bedc6358d414a5f77158d41004ff7654d41004fe7654d41004fc7654d4100dbc7650d41016bc7650d4100cbc7650d410073f7550d410073c7550d41006bf6550d41006bd6550d4101dbf7350d4101f9f7350d410079f6350d41016be6350d41016bc6350d411bf9c6350d411bf9e5350d410079d5350d41005bf7250d4133ebc6250d411bf9f3250d41007b77150d4100dbe7150d4100dbc7150d4127fb47150d4101ebf6150d4101fb76150d4127f3f5150d4127fb65150d4127f3d5150d4127f9f3150d4127fb62150d41005bf7050d411bf9c3050d4104cfe76d8941024fe75d8941004fd75d8941024fc75d894100cfd74d8941014fe73d8941004fd73d8941014fc73d894149eee42d894149eed42d894101cfd71d894141e7f51d894141e7d51d894141eef21d894102cfe70d8941004fd70d894149ebf40d8941006ef6298941185f5719894119df771589411c57e75189410057d75189411bdde7318941005dd731894104eee6218941006ed6218941005fa7018941005f97018941004fe7694941004fd769494104cfc769494101dbe7494941005bd74949411bdde7394941005dd739494100df67194941005f57194941004ff7654941004fe7654941004fc76549410267e65549410067d655494100df6715
  | 30 => 0xd439095140d7e72909513076e62909510076d62909513073f42909511d76f42909513076c42909512357f719095100d7e71909512357d719095100d7c71909512367f61909512477761909512377641909512377631909512376f21909512d57e70909510057d70909510057f76509510057e76509510057d76509510057c76509512357f74509510057f73509511cd7e73509511cd7c735095141d7f72509510076e62509510076d62509511d76f42509513073e42509513073c42509511d76c425095121d7f715095100d7e715095100d7c715095121e7f615095122f77615095121f3f415095121f76415095121f7631509510057f70509512d57c70509511d73f40509513057f768c9510057e768c9513067e768c9510047e768c9510057d768c9513067d768c9510047d768c9513057c768c9513057f748c9511d57e748c9510057d748c9513057c748c9511ed7d738c9514057e728c9513076e628c9510076d628c9514e76f428c9513076c428c9513075f328c9511cf6f328c9513076c328c9512057f718c95100d7e718c9512057d718c95100d7c718c9512067f618c95121777618c95120776418c95120776318c9512076f218c9512d57e708c9510057d708c9510057f764c9510057e764c9510057d764c9510057c764c9510057f744c9511d57e744c9510057d744c9511d57c744c9512057f734c9510075f634c9511cf5c634c9511cf5e434c9510075d434c9514157f724c9510076e624c9510076d624c9514df6f424c9514df6c424c9511cf6f324c9513075e324c9513075c324c9511cf6c324c9511ed7f714c95100d7e714c95100d7c714c9511ee7f614c9511ff77614c9511ef76414c9511ef5f314c9511ef76314c9510057f704c9512d57c704c9511cf5f304c9511d57e74d81510057d74d81511d57c74d81510067e64d81510067c64d81511cd7e73d81510057d73d81511cd7c73d81510067f63d81510067d63d81513057e72d81510057d72d81510067f62d81510067d62d81510257f71d81510257d71d81512de7f61d81513e77761d81512df7641d81512df7631d81512df7a10d81512df7910d81511d57e74981512d73e74981511d53e74981510057d74981512d73d74981510053d74981512d57c74981511cd7e73981510057d73981512d57c73981513057e72981510057d72981512d775719815130e7f61981510677761981511677641981511677631981512d57e70981512d67f60981510077b60981510057f74581511d57e74581511d57c74581510067e64581510067c64581510057f73581510075f73581510055f73581511cd7e73581511cd7c73581510075c73581511cd5c73581510067f63581510067d63581510057f72581513057c72581510067f62581510067d6258151007777158151047776158151
  | 31 => 0x8d510257d71d8d5100d7c71d8d5147e7f61d8d515077761d8d5147f7641d8d5147f5f31d8d5147f7631d8d5147f5d31d8d512d57e70d8d510057d70d8d511cf5c30d8d514857f7658d510057f7458d511d57e7458d511d57c7458d5147d7f7358d510075f6358d511ce7e6358d511ce7c6358d511cf5c6358d511cf5e4358d510057f7258d513057c7258d5128d7f7158d51007777158d51005777158d511b7776158d5128f764158d5128f763158d510057f7058d512d57c7058d510057f7650d510067f7650d510047f7650d510057e7650d510057d7650d510057c7650d510067c7650d510047c7650d514657f7450d511d73e6450d510073d6450d5145d7f7350d511cf5e6350d510075d6350d511d75f4350d511cf3e4350d511cf3c4350d511cf5c4350d510057f7250d513057c7250d511d73c4250d511cf5f3250d5127d7f7150d5100d7e7150d5127f767150d5100d767150d51007757150d5100d7c7150d5127e7f6150d51287776150d5127f3f4150d5127f764150d5127f5f3150d5127f763150d510057f7050d512d57c7050d511d73f4050d511cf5c3050d511d57e74d89510057d74d89511d57c74d89510067f64d89510067d64d89511cd7e73d89510057d73d89511cd7c73d89510067e63d89510067c63d89510257f71d89510257d71d89514267f61d89514ff7761d89514277641d89514277631d89514276f21d89514276d21d89512d57e70d89510057d70d89511d57e74989510057d74989513057c74989511cd7e73989513075e73989511cd5e73989510057d73989513075d73989510055d73989513057c73989514ed7e72989513067f62989510076f62989512657d71989513077571989510057571989512667f61989511a77761989512677641989512677631989512d57e70989510057d70989510057f74589510073f74589510053f74589511d57e74589511d57c74589510073c74589511d53c74589510067f64589510067d64589510057f73589511cd7e73589511cd7c73589510067e63589510067c63589510076f62589513067e625895124d7f715895100777715895100577715895118f77615895124f76415895124f7631589510057f70589512d57c70589514257e76189511d57e74189510057d74189513057c74189511cd7e73189510057d73189513057c73189512657e72189513067f62189513076e62189513067d62189510076d62189510257f711895100d7e71189510257d711895100d7c71189514ee7f61189514f77761189514ef7641189514ef7631189514ef6f21189514ef6d21189512d57e70189510057d70189513057f76909510057e76909510057d76909513057c769095121d7d74909510073f64909511d73c64909511cd7e73909510057d73909513057c73909511d73f43909510073
  | 32 => 0x3067f62949510076f62949513076c629495100d7e719495126776719495130775719495100d7c71949510267f61949510277761949512677641949512677631949512d57e70949510057d709495100d7c765495104e7c765495100c7c76549510057f74549511d57e74549511d57c74549510067f64549510057f73549511cd7e73549511cd7c73549512567e63549512567c63549510257f72549510276f72549510076f625495104e7e625495104e7c62549510076c625495100777715495100d7e715495100d7c715495124f7471549510267f615495102777615495124f76415495124f7631549510057f70549512d57c7054951004fe7690951004fd769095104cfc76909513057f75909510257e75909510057d75909510257c7590951006bf649095101ebc649095104eee62909513076e52909510076d5290951004ff7650951004fe7650951004fc76509510057f75509510257e75509510057d75509510257c75509510076e52509510076d5250951004fe768c951004fd768c95104cfc768c9513057f758c9510257e758c9510057d758c9510257c758c95104eee628c9513076e528c9510076d528c951004ff764c951004fe764c951004fc764c9510057f754c9510257e754c9510057d754c9510257c754c951006df634c951016dc634c9511ff5f534c9511cf5c534c9510076e524c9510076d524c95102cfe76d815100cfd75d81512de7d75d815101cfe74d8151004fd74d815101cfc74d81510067e54d81513e67c54d8151014fe73d8151004fd73d8151014fc73d81513e67f53d81510067d53d815104cfe72d8151004fd72d81513e67f52d81510067d52d8151024fd71d81512def631d81513e6fa50d81512d67c50d81512defa10d81511d5be7498151005bd7498151006fb6098151005df73581511cddc735815102efa6018151006f9601815151d7e76d91511d67e64d91511d73e64d91511d67c64d91511cd7e73d91510057d73d91511cd7c73d91513057e72d91510057d72d91511d73c42d91510257f71d91515177771d915100d7e71d91510257d71d915100d7c71d91514b67f61d91515177761d91514b73f41d91514b77641d91514b73d41d91514b77631d91512d57e70d91510057d70d91511d73f40d91514bd7f76591514b57f74591510073f64591511d67e64591511d67c64591511d73c64591510057f73591511cd7e73591511cd7c73591511d73f43591510057f72591513057c725915129d7f71591510077771591510057771591511c777615915129f76415915129f7631591510057f70591512d57c705915150d7e76d8d511d57e74d8d510057d74d8d511d57c74d8d511ce7e63d8d511cf5e63d8d511ce7c63d8d513057e72d8d510057d72d8d511cf5f32d8d510257f71d8d515077771d8d5100d7e71d
  | 33 => 0xc324cb511df6c324cb511ed7f714cb5100d7e714cb5100d7c714cb511ef5f314cb510057f704cb5130d7c704cb511df5f304cb5101cfe76d91510257e75d915100d7d75d91511d6be64d91511d73e54d915100cfd75d91514b67d75d915100c7d75d91511d67e54d91511d6be54d9151516bd54d91511d67c54d9151014fe73d9151004fd73d9151014fc73d915104cfe72d9151004fd72d91515167f52d91511d6bc42d9151024fd71d91514b6bf41d915102cfe70d9151004fd70d91511d6bf40d91511d6bc645915152df7715915100d7c765515101e7c765515100c7c76551510257f74551510273f74551510073f645515101e7e645515101e7c64551511d73c64551510057f73551511cd7e73551511cd7c73551511d73f43551510057f72551513057c725515100777715515100d7e715515100d7c715515129f7471551510267f615515102777615515129f76415515129f7631551510057f70551512d57c7055151014fe76d8d510257e75d8d5100d7d75d8d511cede63d8d511cf5e53d8d5100cfd75d8d5147e7d75d8d5100c7d75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d511ce7e53d8d511cede53d8d51506dd53d8d511ce7c53d8d5104cfe72d8d51004fd72d8d511cedf32d8d51024fd71d8d5147edf31d8d5102cfe70d8d51004fd70d8d515067f50d8d511cedc30d8d511cedc6358d51525f77158d5100d7c7654d510167c7654d5100c7c7654d510057f7454d511d57e7454d511d57c7454d510257f7354d510275f7354d510075f6354d510167e6354d510167c6354d511cf5c6354d511cf5e4354d510057f7254d513057c7254d51007777154d5100d7e7154d5100d7c7154d5128f747154d510267f6154d51027776154d5128f764154d5128f763154d510057f7054d512d57c7054d51004ff7650d51004fe7650d51004fc7650d510057f7550d510257e7550d510057d7550d510257c7550d5101ebe6450d511d73e5450d510073d5450d51016de6350d511cf5e5350d510075d5350d5100df67150d5104cfe76d895100cfd75d89514267d75d895101cfe74d8951004fd74d895101cfc74d89514fe7f54d89510067d54d8951014fe73d8951004fd73d8951014fc73d89510067e53d89514fe7c53d89514feee52d89514feed52d89513067c52d8951024fd71d8951426f641d8951426ef21d895102cfe70d8951004fd70d89514fe7f50d89511cdde7398951005dd7398951006ef629895118df57198951005bf74589511d5bc74589511a5f7715895104eee6218951006ed621895100d7e76949512667e769495100c7e76949511d57e74949510057d74949513057c74949511cd7e73949513075e73949511cd5e73949510057d73949513075d73949510055d73949513057c73949510257e72949510276e7294951
  | 34 => 0x932006bf645093201ebc6450932005df7350932015dc7350932545ef725093204fac425093200cfe76d85321eef661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853204cfd73d8532196de43d8532006dd43d8532014fd72d85321eef631d85321eef621d853202cfe70d8532004fd70d8532196df30d85321eef46158532005fb7058532005f87058532024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813204cfd73d813200cfe71d8132004fd71d813200cfc71d81320d6df31d81320d6fa30d8132006fb10d8132006f810d8132006fb60981321fd7e75181320057d75181321f5be7418132005bd74181321edf67118132005f5711813202efa6018132006f960181322857f7650f510067f7650f510047f7650f510257e7650f512857d7650f510257c7650f512867c7650f510247c7650f514657f7450f511e73e6450f512873d6450f5145d7f7350f511df5e6350f512875d6350f511e75f4350f511df3e4350f511df3c4350f511df5c4350f510057f7250f513157c7250f511e73c4250f511df5f3250f5127d7f7150f5100d7e7150f5100d7c7150f5127e7d6150f5127f3f4150f5127f5f3150f510057f7050f5130d7c7050f511e73f4050f511df5c3050f513157f7690b510257e7690b512457d7690b510257c7690b511dd7e7390b510057d7390b513157c7390b511e73f4390b510073d4390b5140d7e7290b513176e6290b512476d6290b513173f4290b511e76f4290b513176c4290b512357f7190b5100d7e7190b512357d7190b5100d7c7190b512376f2190b5130d7e7090b510057d7090b5122d7f7650b510257e7650b5122d7d7650b510257c7650b510057f7350b511dd7e7350b511dd7c7350b5141d7f7250b5122f6e6250b5122f6d6250b511e76f4250b513173e4250b513173c4250b511e76c4250b5121d7f7150b5100d7e7150b5100d7c7150b5121f3f4150b510057f7050b5130d7c7050b511e73f4050b513157f768cb510257e768cb513167e768cb510247e768cb512157d768cb513167d768cb510047d768cb510257c768cb513157f748cb511e57e748cb510057d748cb513157c748cb514057e728cb513176e628cb512176d628cb5153f6f428cb513176c428cb513175f328cb511df6f328cb513176c328cb512057f718cb5100d7e718cb512057d718cb5100d7c718cb512076f218cb5130d7e708cb510057d708cb511fd7f764cb510257e764cb511fd7d764cb510257c764cb510057f744cb511e57e744cb510057d744cb511e57c744cb511ff5f634cb511df5c634cb511df5e434cb510075d434cb514157f724cb511ff6e624cb511ff6d624cb515376f424cb515376c424cb511df6f324cb513175e324cb513175
  | 35 => 0x4ff705953202cfc70595321fe7f505953201cfe76d91321f6be64d913204dee72d9132015ed72d91321f7af42d9132024fe75d9132004fd75d9132024fc75d913204cff73d913204cfd73d913223ebf43d913223ebd43d9132014fd72d913223eed72d9132014ed72d91321f6bf42d91321f6ef42d91321f6ec42d913200cfe71d9132004fd71d913200cfc71d913223edf31d913202cfe70d9132004fd70d91320057f75591321fd7c75591321f6bc6459132545ef72591321f7ac4259132004ff75591320067f75591320047f7559132024fe7559132024fc75591320067c75591320247c755913223cff7459132006bf7459132224ff7359132006df7359132544ff7259132006ef72591321f6ef425913233ebe425913233ebc42591321f6ec4259132004ff715913200cfe715913200cfc71591321f6bf4159132226df3159132004ff705913202cfc70591321f6bf4059132004ff7655132004fe7655132004fd7655132004fc7655132005df7355132015dc7355132005ef725513204dec725513204ddc7650d3201edc7650d3204cdc7650d320075f7550d321fdde7550d321fddc7550d320075c7550d321fd5c7550d32006df6550d32006dd6550d32015df7450d320179f7450d320079f6450d3201ede6450d3201edc6450d321f79c6450d321f79e5450d320079d5450d32007cf7250d3204dde7250d3204ddc7250d32007cc7250d32016df6250d32017cf6250d321f7cf4250d3233f9e4250d3233f9c4250d321f7cc4250d321f78c4250d32005df7150d321f79f4150d32005df7050d322fedc6050d321f79f4050d3254dee769493204eee7694932255ed7594932026ee6594932026ec65949321f5ee749493204dec7494932006ef6494932006ed6494932015ee739493204fce7394932015ce739493204fcd739493204dec739493204eef639493204fcf63949321ffcf539493226fcc539493226fce4394932007cd4394932005ed71949321ff6f519493226fcf3194932005ed709493226fcf3094932024ff7654932014fe7654932254fd7654932014fc76549320067f65549320267c6554932005df7354932015dc73549322575c5354932015ec7654932026ec7654932014ec765493204def755493204f6f75549320076f6554932026ee6554932026ec65549321ff6c65549321f5ee74549321f5ec7454932006ef6454932006ed64549321ff6f54549320076d5454932007cf7354932015ee7354932015ec7354932257cc735493204eef635493204fcf63549321ffcf53549322576e53549322576c5354932257cc53549322574c5354932257ce4354932007cd4354932005ef71549321ff6f5154932257cf3154932005ef70549321ff6f5054932257cf305493201cff7650932014fe7650932224fd7650932014fc765
  | 36 => 0xe71596320067d71596320067c71596320067f41596320067e41596320067c41596322567f31596322567e31596322567d31596322567c315963204e7f215963204e7e215963204e7d215963204e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067c40596322567f30596322567e30596322567d30596322567c305963204e7f205963204e7e205963204e7d205963204e7c20596320067f10596320067c1059632004ff7559232024fe7559232024fc755923204ebf7459232226bf4359232226bd435923204cfe725923204cfc725923204eec725923204cec725923204eee525923220eef425923204ebe425923204ebc425923204eec425923204edf325923204edd3259232004ff715923200cfe715923200cfc715923220ebf415923204eef2159232004ff705923202cfc705923220ebf4059232004ff765523204cfe7655232004fd765523204cfc76552320267e65552320067d6555232005ef725523204dec725523204def7654a3255eef7654a3204f6f7554a32026ee6554a3204f6e6554a320266e6554a3204f6d6554a3204eec6554a3220dee7454a3220dec7454a3204eef6454a32006ed6454a322176f5454a320076d5454a32015ee7354a32015ec7354a322576e5354a322576c5354a32005ef7154a322176f5154a32005ef7054a322176f5054a32004ff7558632024fe75586320067e75586320067d7558632024fc7558632004ff745863201cfe745863201cfc745863204cfe725863204cfc725863204edf325863204edd325863204ef77158632206f64158632206f6315863204ef7215863204ef42158632004ff705863202cfc705863204eef2058632206f71058632004ff7558232024fe7558232024fc7558232004ff745823201cfe745823201cfc745823204cfc725823204edf325823204edd3258232004ff715823200cfe715823200cfc715823204eef215823204efb7058232096fa305823204efb205823204ef82058232024fe76d95321fe7e65d9532015de73d953204ddd73d95321ff5f53d953201cfe74d9532004fd74d953201cfc74d95320067e54d95321fe7c54d953204cff73d953204cfd73d95321fedd73d953204cdd73d953226e7f53d95321fedf53d953226e7d53d953226edc53d953226ede43d9532014fd72d95321fe7f52d953200cfe71d9532004fd71d953200cfc71d95321fe7f51d953202cfe70d9532004fd70d95321fe7c65595322575c5359532555ef725953226cff75595320067f7559532004ff745953201cfe745953201cfc7459532254ff7359532006df73595321fedf53595322567e53595322567c5359532256dc5359532256de4359532554ff7259532006ef7259532004ff715953200cfe715953200cfc71595321fe7f5159532
  | 37 => 0x9542014fc7359542584ff7259542006ef7259542004ff715954200cfe715954200cfc715954222e7f5159542004ff705954202cfc7059542014fe76d8d42226de63d8d42024fe75d8d42004fd75d8d42024fc75d8d4204cfd74d8d42226de43d8d4220edd43d8d4201cfd72d8d4220eef42d8d4257ebe42d8d4257ebc42d8d4220eec42d8d42226df32d8d4200cfe71d8d42004fd71d8d4200cfc71d8d4220ebf41d8d4202cfe70d8d42004fd70d8d4220ebf40d8d420057f7558d4222d7c7558d42226dc6358d42575ef7258d42004ff7654d42004fe7654d42004fc7654d4256dee769494204eee769494225ded7594942026ee6594942026ec659494201dee749494204dec749494204eef649494204faf649494204fce739494204fcd7394942006ef6394942005ed719494222f6f5194942277af4194942277af4094942024ff765494201cfe765494225cfd765494201cfc76549420067f65549420267c6554942005bf745494201dbc745494204f6c525494204fac425494201dec7654942026ec765494201cec765494204def755494204f6f75549420076f6554942026ee6554942026ec655494222f6c6554942007af745494201dee745494201dec745494225fac745494204eef645494204faf645494225f6f545494225f6d5454942006ef63549425676e535494222f6c5354942005ef715494222f6f515494225faf415494222f6f505494225faf405494200cfe76d854221ef661d8542024fe75d8542004fd75d8542024fc75d854204cfd74d8542014fe73d8542004fd73d8542014fc73d854201cfd72d854221ef641d854221ef621d854202cfe70d8542004fd70d854219ebf40d854221ef46158542024fe75d8142004fd75d8142024fc75d814204cfd74d8142014fe73d8142004fd73d8142014fc73d814200cfe71d8142004fd71d814200cfc71d81420debf41d81420defa40d814222d7e75981420057d7598142006fb609814202efa6018142006f9601814204e7f7559632004ff745963201cfe745963201cfc74596322167f54596320067e54596322167c54596322567f53596322567d535963204cfe725963204cfc725963204e7e525963204e7c5259632004ff715963200cfe715963200cfc71596322167f51596320067e51596322167c5159632004ff705963202cfc70596322167f50596322167c50596320067f74596320067e74596320067d74596320067c74596322567f73596322567e73596322567d73596322567c73596322567f43596322567e43596322567d43596322567c435963204e7f725963204e7e725963204e7d725963204e7c725963204e7f425963204e7e425963204e7d425963204e7c425963204e7f325963204e7e325963204e7d325963204e7c32596320067f71596320047f71596320067
  | 38 => 0x1cfe74d8152004fd74d815201cfc74d8152014fe73d8152004fd73d8152014fc73d815200cfe71d8152004fd71d815200cfc71d81520e67f51d81520e6fa50d815225dbe7498152005bd7498152006fb609815202efa6018152006f9601815204e7f755964225e7f545964225e7d5459642004ff7359642014fe7359642014fc73596420067e53596422467c535964225ebf435964204cfe725964204cfc725964204e7e525964204e7c5259642004ff715964200cfe715964200cfc71596422467f5159642004ff705964202cfc70596422467f5059642004ff7558e42024fe7558e42024fc7558e4204edf7358e42006df5358e4223edc5358e4223ede4358e421f6dd4358e4204cfe7258e4204cfc7258e4204eee5258e421f6ef4258e4204eec4258e4204ede3258e4204edc3258e42004ff7158e4200cfe7158e4200cfc7158e4223edf3158e4204eef2158e42004ff7058e4202cfc7058e4223edf3058e42004ff7654e42004fd7654e4204cfc7654e4233dbf7650e42016bf7650e42014bf7650e420073f7550e420073c7550e4233ebf6550e42006bd6550e4201dbf7350e4201f9f7350e42016be6350e4233f9e6350e4233f9d6350e42016bc6350e4223f9e5350e420079d5350e4233dbf7250e42007af7250e4233fac7250e4201ebe6250e4201fae6250e4233fae5250e4233f9f3250e4223f9f3150e4223f9c3050e4204def7654a42596ef7654a4204f6f7554a4204f6f6554a42026ee6554a4204eec6554a4204f6c6554a4201dee7454a4201dec7454a4225f6f5454a4225f6d5454a42006ed6354a4258f6e5354a422476c5354a4225faf4354a42007ad4354a42005ef7154a422476f5154a422476f5054a42004ff7558642024fe7558642024fc7558642004ff7358642014fe7358642014fc7358642186bf4358642006bd435864204cfe725864204cfc725864204ebf425864204ebd425864204ef77158642236f6415864204ef7215864204ef42158642004ff705864202cfc7058642236f71058642004ff7558242024fe7558242024fc7558242004ff7358242014fe7358242014fc735824209ebf4358242006bd435824204cfc725824204ebf425824204ebd4258242004ff715824200cfe715824200cfc715824204eef215824204efb705824209efa405824204efb205824204ef82058242024fe76d954222e7e65d954204cff74d954204cfd74d95422767f54d95422767d54d9542014fe73d9542004fd73d9542014fc73d95420067e53d954222e7c53d954201cfd72d954222e7f52d954200cfe71d9542004fd71d954200cfc71d954222e7f51d954202cfe70d9542004fd70d954222e7f50d954222e7c6559542585ef7259542274ff75595420067f755954225cff7459542006bf7459542004ff7359542014fe735
  | 39 => 0xd2158e5204edc2158e52006df7058e52006de7058e52006dd7058e52006dc7058e521fedf5058e521fede5058e521fedd5058e521fedc5058e52006df4058e52006dc4058e5204edf2058e5204ede2058e5204edd2058e5204edc2058e52006df1058e52006dc1058e52004ff7650e52004fd7650e5204cfc7650e520057f7550e520257c7550e5201ebc6450e52016de6350e52006dd6350e5204dee7250e520067d7558652004ff745865201cfe745865201cfc7458652004ff7358652014fe7358652014fc735865204cfe725865204cfc725865204e7f525865204e7d525865204eee425865204eee325865204ef771586522667f5158652266f65158652266f6415865204ef7215865204ef42158652004ff705865202cfc7058652266f71058652004ff745825201cfe745825201cfc7458252004ff7358252014fe7358252014fc735825204cfc725825204e7f525825204e7d525825204eee3258252004ff715825200cfe715825200cfc71582520a67f515825204efb70582520a6fa505825204efb205825204ef8205825201cfe76d915225ebe64d915204cfd75d915225ebe54d9152246bd54d9152014fe73d9152004fd73d9152014fc73d915225ebf43d9152024fd72d915225ebf42d915200cfe71d9152004fd71d915200cfc71d91522467f51d9152006be41d915225ebc41d915202cfe70d9152004fd70d915225ebf40d915225ebc64591525a5ef725915204d7c765515201e7c765515204c7c76551520257f74551520273f74551520073f645515201e7e645515201e7c645515225f3c64551522557e73551522557c735515225f3f43551520076f725515204d7e725515204d7c72551520076c72551520267f62551520276f62551520057f71551520057f7055152014fe76d8d520257e75d8d52256de63d8d522575e53d8d5204cfd75d8d5204c7d75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d522567e53d8d52256de53d8d52216dd53d8d522567c53d8d52024fd72d8d52256df32d8d5200cfe71d8d52004fd71d8d5200cfc71d8d522167f51d8d5202cfe70d8d52004fd70d8d522167f50d8d52256dc6358d522575c5358d5259def7258d52004ff7650d52004fe7650d52004fc7650d520057f7550d520257c7550d52006bf6450d5201ebc6450d520073d5450d52016de6350d522575e5350d5200cfe76d855224ef661d85523167f75d855204cfd75d855201cfe74d8552004fd74d855201cfc74d85521a67f54d85520067d54d8552014fe73d8552004fd73d8552014fc73d85520067e53d85521a67c53d8552024fd72d85523167e52d85523167c52d855224e7f51d855224ef651d855224ef621d855202cfe70d8552004fd70d85521a67f50d8552005bf745855225dbc745855224ef4615855204cfd75d8152
  | 40 => 0x8943004fd75d8943024fc75d8943014fd74d8943546bd74d894301cfd73d8943576ee42d894333ebc42d8943546ee32d894300cfe71d8943004fd71d894300cfc71d8943576bf41d8943546df31d894302cfe70d8943004fd70d8943576bf40d89432857e75989430057d75989430067f65989430067c6598943006ef629894333fac42989430057f75589432857c75589430067f65589430067c65589431f7ac42589430067f65189430067c651894304eee6218943006ed621894300cfe76d85430067f65d85430067c65d854327ef661d85430067f75d8543024fe75d8543004fd75d8543024fc75d85430067c75d8543014fd74d854301cfd73d854304cfe72d8543004fd72d854346edf32d854327ef641d854327ef631d854302cfe70d8543004fd70d85434a6bf40d85430057f75585432857c75585430067f65585430067c655854327ef4615854302cfe76d81430067f65d81430067c65d8143024fe75d8143004fd75d8143024fc75d8143014fd74d814301cfd73d81433bedd73d814304cfe72d8143004fd72d8143366df32d814300cfe71d8143004fd71d814300cfc71d81433bebf41d8143366df31d81433befa40d8143366fa30d81432fedc30d81432857e75981430057d75981430067f65981430067c6598143006fb60981432ffd830981430057f75581432857c75581430067f65581430067c6558143127d830581430067f65181430067c651814302efa6018143006f9601814304ebf7459252276be545925222ebd5459252004ff7359252014fe7359252014fc735925204cfe725925204cfc725925204e7f525925204e7d525925204ebe425925204ebc4259252004ff715925200cfe715925200cfc715925222e7f5159252276bf4159252004ff705925202cfc7059252276bf4059252004ff7458e5201cfe7458e5201cfc7458e5204edf7358e5226ede5358e521fedd5358e52006df4358e5226ede4358e5226edc4358e5204cfe7258e5204cfc7258e5204ede3258e5204edc3258e52004ff7158e5200cfe7158e5200cfc7158e521fe7f5158e5226edf3158e52006de3158e5226edc3158e52004ff7058e5202cfc7058e5226edf3058e5226edc3058e521fede7558e521fedd7558e5226edc7558e52006df7458e52006de7458e52006dd7458e52006dc7458e521fedf5458e521fede5458e521fedd5458e521fedc5458e5204edf7258e5204ede7258e5204edc7258e5204edf5258e5204ede5258e5204edd5258e5204edc5258e5204edf4258e5204ede4258e5204edd4258e5204edc4258e52006df7158e52006de7158e52006dd7158e52006dc7158e521fedf5158e521fe5f5158e521fede5158e521fedd5158e521fedc5158e52006df4158e52006de4158e52006dc4158e5204edf2158e5204ede2158e5204ed
  | 41 => 0x5ad7e76d95430247e76d95435bf3f74d95435bf3c74d95435d75f73d95435bf5c73d95435d75f43d95435bf3e43d95435bf3c43d95435bf5c43d95435d73c42d95435bf5f32d95430057d71d95430067e61d95430067c61d95435d73f41d95435bf5f31d95435d73f40d95435bf5c30d95435be7f74d95435d67e74d95435be7d74d95435be7c74d95435be7f73d95435be7e73d95435be7d73d95435be7c73d95435be7f43d95435be7e43d95435be7c43d95430067f72d95430067e72d95430067d72d95430067c72d95435d67f42d95435d67e42d95435d67d42d95435d67c42d95435be7f32d95435be7e32d95435be7d32d95435be7c32d95430067f71d95430067e71d95430067d71d95430047d71d95430067c71d95435d67f41d95435d67e41d95435d67d41d95435d67c41d95435be7f31d95435be7e31d95435be7d31d95435be7c31d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95435d67f40d95435d67e40d95435d67d40d95435d67c40d95435be7f30d95435be7e30d95435be7d30d95435be7c30d95430067f10d95430067c10d9543024ff76595432867c65595435c5bf74595435cddf73595435bcff75595430067f75595435c4ff7459543006bf74595432a4ff7359543006df7359543004ff725954304cfc7259543004ff715954300cfe715954300cfc71595432867f5159543004ff705954302cfc70595435bd7e76195432867e76195435bc7e76195435b73e74195435af3d74195435ae7f64195435af5e73195435b75d73195435ae7f63195435b75f43195435af3e43195435af3c43195435af5c43195432876e72195432876d72195435b73c42195435af5f32195432877671195430057d71195432877571195430057571195430067e61195430067c61195435b73f41195435af5f31195432877a70195432877970195435b73f40195435af5c3019543015bc7655143026bc7655143014bc765514301dbf755514301f3f75551430073f6555143026be6555143026bc65551432873c65551430079f7355143015be7355143015bc73551432a79c735514301ebf635514301f9f63551432a79e535514333dbc72551432873f52551432a79f3255143005bf71551432873f51551432a79f3155143005bf70551432a79c305514301ddc7654d43026dc7654d4301cdc7654d43015df7554d430175f7554d430075f6554d43026de6554d43026dc6554d432875c6554d430079f7454d4301dde7454d4301ddc7454d432979c7454d43016df6454d430179f6454d432979e5454d432879d5454d43005df7254d432979c4254d43005df7154d432875f5154d432979f4154d432fddc7054d432875f5054d432979f4054d4304cfe76d89430067f65d89430067c65d8943024fe75d
  | 42 => 0xf51d8d5402cfe70d8d54004fd70d8d542a6dc6358d5404cfe76d895401cfd75d8954024fd74d8954014fe73d8954004fd73d8954014fc73d89545a6ee52d8954586ee42d895400cfe71d8954004fd71d895400cfc71d89545a67f51d895402cfe70d8954004fd70d89542a5de7398954005dd7398954006ef629895404eee6218954006ed621895400cfe76d855429ef661d85541e67f75d855401cfd75d8554024fd74d85541e67e54d85541e67c54d8554014fe73d8554004fd73d8554014fc73d85541e6bf43d855404cfe72d8554004fd72d855452e7f52d855429e7f51d855429ef651d855429ef641d855402cfe70d8554004fd70d855429ef4615855402cfe76d815401cfd75d8154024fd74d81543f6bf54d81543c67e54d81543c67c54d81543c6bc54d8154014fe73d8154004fd73d8154014fc73d81543c6bf43d815404cfe72d8154004fd72d81543f67f52d815400cfe71d8154004fd71d815400cfc71d81543f67f51d81543f6fa50d81543c6fa40d8154006fb609815402efa6018154006f9601815401cfe76d9153296be64d9153014fd75d9153296be54d91535e6bd54d9153024fd73d91535c6bf43d915304cfe72d9153004fd72d915300cfe71d9153004fd71d915300cfc71d91535e67f51d915302cfe70d9153004fd70d9153296bf40d9153296bc64591535dddf735915304cfe76d8953014fd75d895301cfe74d8953004fd74d895301cfc74d8953024fd73d895359edf53d89535567e53d89535567c53d8953556dc53d8953556de43d895359eee52d8953556ee32d895300cfe71d8953004fd71d895300cfc71d895359e7f51d895302cfe70d8953004fd70d895359e7f50d8953006ef629895304eee6218953006ed621895300cfe76d855328ef661d85531de7f75d8553014fd75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d85531de7e53d85531de7c53d85531dede43d855304cfe72d8553004fd72d855328e7f51d855328ef651d855328ef631d855302cfe70d8553004fd70d85535267f50d855328ef4615855302cfe76d8153014fd75d815301cfe74d8153004fd74d815301cfc74d8153024fd73d815304cfe72d8153004fd72d815300cfe71d8153004fd71d815300cfc71d81533ee7f51d81533eefa50d8153376fa30d8153295be7498153005bd7498153006fb609815302efa6018153006f96018153024fe76d95432867e65d95432a4fd75d9543014ff74d9543014fd74d95435d67f54d95435d67d54d954301cff73d954301cfd73d95435be7f53d95435be7d53d954304cfe72d9543004fd72d95432867f52d95432867c52d954300cfe71d9543004fd71d954300cfc71d95432867f51d95430067e51d95432867c51d954302cfe70d9543004fd70d95432867f50d95432867c50d9543
  | 43 => 0x4005002c00b0010009000800100240000000000001800000180000020003000400000040000000004001000100000010008001000000100000030010000004400300000020004003000c000000800000000000008004001000200000020000000000000000240010010002000c001000400a00080020008000000000100040000000000001400200240010000002000800000040000008001000400000000000000002000000400000000004000000000a000c001000000100040000000000001c002000000b00080010000005000400300000000004002000000100000010004001000c0030000002000000100000050044000000c0010000002000c0030000001000400c000000300000000000000001c000000400200040030000001000c00400000020010001000400200000020000000000000000000060000001000c0040000007000400100000000000000001c005000400800080060008000000000600000070000000000c002000c007001800600000000008000000800000000010000000000400100100060000004000c00000180040004002000c00000000000000003004000f0000000000c0030004002000000800080000004000000000100040030004000000000000100000008000000400600040010004003000000100280030004001002000000140000000002000400000040000008001000000000080000004000002c0000000001000c0000000000000400500040000000000000400200200000024000002400400000010004008000000700000000000007001800000000000010000000c000000c00000000020000003001c00a000000100380000014000000000000700010000000000c001002c001000400000040010004000001000100040020004009000400000000090014000000800100080010004000000c00100040010004000000c0000010000002800000000000000000000800100000000000000000c0030008003000000900080050004004000000500100000000005000800800000020014000000000000100000008001000000000000000028000000000000040040000000000000200040010008000000400500080000000002000000000140000000000000000000100000004002000c0070000002000c000000000100000000014000000000100040010000006000c004000000300000050014002000000300000000000000000c0020034000000c00000040000020001000000d0004000000400000000000020000002400b0000002000c001001800000000040000000000c0000000000001c0020008006014fe76d8d542a6de63d8d5401cfd75d8d54024fd74d8d542a6de53d8d542a6de43d8d5404cfe72d8d54004fd72d8d542a6df32d8d5400cfe71d8d54004fd71d8d5400cfc71d8d545de7
  | 44 => 0x4002000400300000010000001000c000000c0080000000000000000040000004001000400000080000000000002c0030000002000000000000150018002000c0000000000000000200080020014004001400400000020004000000000100000040008003000800000140000004006001400000380000014000001c00000040000004008000000000000000000002001400100040040004001001000000000000010000000c0040010000001000100080050000001000000b00000020004000000000400000030008000000000100040000000001000000400000000008005000800000040030014007001c000000000000200010014000000000000040020000000000400000000050000000000000d000000900040040024000000400100000000008000000000f00000000028002000c00000000010010002000000200040000014000003800f002c00100000000000007001802e000400800040060004000000c000001000300000000000005000000200000020018001002400600000010004003000000000000010004002001000000000000000006000400300040040010002000000000000060000001000400400040010018005000c003000000000040000000000000000000000000004002000000300040060008002000000000080030034007001c000000400000400010004002001c0000010002000000000000020004001000000100080000008002000000000000010010000000000100080000020006000c0010000000000c0000000004000c0000024002001c001001c00200040000008000000c0080004000000000000000020004000001c00d002400000080080000009000400000080010020001000800100080070018000000800000000000008005000000000000000000000000c009000400000200010004000000c0000008000000000000000000010005000c0000010001006400000100030000007000800700000040000007000400500100010010009001c0060020000000000000040030048009000000200000020000000000800500000000000000000000000100000008001002000200240000008005001400200040010004000001c0020000002000400000000000000009000800300000000000005000400000140000000002000000000140020004005000000900000050020001000400000000020010006000800f0014002002c00100140080008002000000000080010000003000000000040000000000001000000140000004004000800e0014002000800100000000000000000000000040000008001000000200080070018001000800000200000000000004c0000008005000000200040010014000000c0000004001000000000000000000000000400500000000000000000400000000040018007000c
  | 45 => 0x10010000000c000000c0000000000000400000000000014002000000100000030000009000c00100000000004004000400200000000000000000000000040020000000000400200080000000000000000200000000004000001400000040010020000000000300080000004000000c00000040030024003002400400400000004000000000400000010000002000c0060000000001400000040000008007000400200140020014001000000000000020004003000000400280030020000000000700080000000001001c0000000002000800100000020000000000000300040040000000000000000000000000001001000000000020044002000000c00280000008000000000000100000000004000400300000010008001000c00100000030000000000400200080000004000000c001000000000000000010001000000100000030004005001c00300080010004002000000100040000010002000000000040000000007000000100000020000001000c0010000004000000500080000004000001c005003000800000000000005001000100000000008003001400400000000024000000400000080000024006001000300040010000000000000700040000000007000400000000050000002000400500000010000001002000e0004000000400000000050000003000000100000000000000000000000000000000000002c0010000000000800000000000000002001000300040030004000000000300040010020005000800100340070004006000000d00100000000001000400300000000000000000000000180030004001000c002000000000100000008000000400000180020000000000c00e000400000000050004000001400300040010008000000400200000000000000000000100000090004000000400000080040000000001c0030000000000c000001c00000000010008000004c001000400300000000010003001000a00240000020006000000200000070008003002800100000000000007000400000140000000002000c000001400000000000008000000c008000c0000000001000400100000000000002002c0010004001000400200000000000000000800100000010004005000000400040020000002000800100080010008001000400000100010008000003c000000800100000000014001000c0030004001000800d00000010000000000400400080000004001001c000001000100000030008000000c000000c00100080030000006000400100000010000000000000000000020000003000400200000000018001000400100000000000000001c0010000001003400100000000008001001000000000000004001000c004000c007000000000000010008008000c00000000000000000000401500180000018001
  | 46 => 0x7000000300080020010008000000100040060008002000c00400040020000000001c000002000000000000004001001400d000000500000010000003000000100000010000000000800200000000008001001400100080020000002000000000180000004001001000000040000000000000000200000020004002000000000040000000004000000000040020014000000000100080010008001001c0040008002000c001002c0000000004000000000040020000000000000300000010024000000800000000010008002000800d0000003002000200080000000000000800000040030000002002c001000000c000c001000000200040000004001000000100040030018000000000100000000004000000000000000000000001000400300000010000001000000100000000000000000000000040030028000001400400000000020000000800000200040004000001400000000080000005000000e00000000008003000c0050008003000c00400080000008001000c001002c006000c015000000000000020000000000c001002c0000000004001c0000008000003c0050000001000400f000401200040110004000001400000080000000001000400000040030000000000400800000060000002001400200000000000000001c003000c0010004004000c0000004000000800100000010000002000400600080000000002000400300000050000002000400000080060000001000000000140020000001000400200040000004001005800000000000010001000000100000030010006000c000000c0000004001000400100200010004003000c00300240010000001000c000000000000100020000001000000000000000000000000c0000018000000800300000040010001000c0000004000000c001000c0030000000000000000000000000000000800000080030000000000000300000020000000000000000080010000004000000100000010014002000000100040030000002001c00100000010004000000800a00000010008012000000000040040010001000000000040010008002000c00200000060018000000c002000c000001400200000000000001000000100000000018000000800100000000004001000000100000000000009000c00300000000000000000c000000c004000c0110000003000c00100000010008000000c00300040030008000000000200000030000003001800100040000000002000400000040000008000000c00200000050000001001c003000c00e000000f0000000000c0010008000000400900000030000001001400000000020000000000000200100030020003000400000000000000000002000000000020000003000800100180000028000001c001000800000080000004000000
  | 47 => 0x43366000000000000000000000000193000000007cc80000002768b601bae00010f600000000000000000000041e8000a9737e80001aee15e0000e040000000051a0001baa95c2bb000000000000000b89000027580003cab75e0003752d78800080116a200000001cf0000dfd00009bf8000c77b084000333200017989e98180d8c0000a5f000000009dc000000096180003a580000001830bcc8000bab8000d3b32c00002c0e00000000000000281943c0000000000022e654800097c1fea0000000390800000000000002e4800037429bd2042c8f0000000375cae2000006c00001b300002d100000001b9ca3cac8e4b60000d608000d49b386ce8000000018d200000001de8000000000000000000000000220832a68c85520000000000000000008a0b47000036d00004b10cba00000007489b2a00000004be35680b6135a0000000000000000000007a7a9fc21800007608000df58000b70000026125120000666ccd8134000294c000000039f03e8dc3110e7f4067800db7c0829ab3c83480000000000b9a00000000a7aa7ba8407d90000119800000014f8a3600000000a520002cd8778000062f8000000000031c2e4600038da000000000000009cf8000000000000000003a880000000000e3b96520000000c5a9bde290800000022fa3e3000000000000000000000116647f0bf05c7800000000006fb00385f42b6c5f821da828000056212280000000ca90000000000000000003a72c9490493c065d0000418ab8647b8000874ac1c2989c4c3a09a7ab92800033d8a3e25f000000038e4329074c00037a20000000d3715b80002e160000ddebf600001f7ac00c352500000000086c80004c626a4000000000032f8845000093d19d29458b6cbfe939e88bb57404a1b0e2460000e01800000000000000722000000000008209fb8000e512d70289b2b8d8e0000000357a0a99684786264a7aa000000000001ba80005b017fe00023a85c080000001d860001d300000000000000022280009d70000000308aa272240bb9aff80002730000000000f8000000000000000000000002001800600000000004001001c007000000600140060010000000800000000000000000000400b00000010000006001400000000030018001000800100180000008006000000100180010004000000c0010004006000000100140000004002000000200040000010002000000200080020000007000800100040020000000002c00000040000000007002c00000000000004000000c0030000001000c0050004000000800000080000000000001800100000070000000000800000000000008000001400000080000020000000000100080010004001000c0020004000000400d00340050004001000800000040050004006003400000000010010002000000
  | 48 => 0xabc8000412000054b38ca0000000554293a000081283520401908000656adc8780289200005eebd82746000385c1d0956c56900001328000dc100000000000000000000000000001c8e65a15a0000019e000274c00000000000000000000000022520000000a42b662000262e00011d295d91686b3810a0000000cd6000058b00000000000a6c800000012ac00003b00001a6c000000088419c2d01a0229b5255200000004ca8d3641b974c0001906545800000034d40000000cda31c200000000001624000000078a000000000002568fb40000000000000070d800005300000001a30e4eb30acf3000000009b491a1b1e00036e2bb6083c3f3313400000000001b04d678b94a7881082fe80003b5000000000003700000d7b9b8acec0000000129c00029a600009800000f969e2800077f8000000150a500000007e2beac53b188000244266fb4e4ae580009230fda98300000001e62000000085e80008c7800062c28da0000000c0d80000000000b750000b69353262b0000dcd95ca5ab80005d8b94a1200faa0000000293237aaf90000db3000000000007891e1a0000000bcf95a2ce9b6509a431ba00000008d600000001c10d24800000000007ada880d962ff43d3000000000000000000000000000000000000000468000006d1a4cd82361627f25f88190000000315400028a825080000002606ba893a0bd3800074cb3f8e332636b75800000000005020da83278000000343676f00000000000d4d2fbe0002968c360ee640221a256400000000c44aea9728baeae1026b0e020000000a4b80003308000179800000000006a88000000000000000008171f580002db600000001a00000000000000000004f9000033b80000bc0000000127e11580000001bce00000007d2800067f800049c0000e51a4364562fe22c30000000000000036b45b300006738000c710fd60cd2a6c81c95fc4070656daf1a0c270a8fc3068ec0db91d586a4a1027623194842383e3a3a860309a04600000009f1000000000008d000000000000962b5beae6ac08921a79c67014ee8bd8000b3e0000bd23958d7800008ad8000a423890bca0000c91b444000003c0000000000000000013a2000000000000005570000c830000b2590ae000000066380000002fb200020c400027bc0a40f907f932d60000000000000014232542b080004e280002b636ca00006be000229a00000000001a98a6c06de0000000970202a0568000aca000000024aa000000000000004c48000b29800000000004c08b5200004da0000000e3a8000000299e894000000000007f80000b2700000000000a242614cfe9ed207f8000414887a0002b780000000000000000000001ae00000000000c78000000014060000000000000000027d82e2a4bad62b7b4374800000001d6ce60000d8
  | 49 => 0xf200000000000000202800011964c300002da800000039240000000a448000d0c371407f335c000034a000000000000008b2199a3a431440000930d4a8000639000026b8aa600020186f8873e000000000000000000000000000000033c0ad18000cddb88c0000c38000187a00022ee14e36902ad0990db10000af533d200000004e3885e00000000003164ac5000010606a2727334c47a0000d4e800000035fc37c1e227ce8a680f38000da1aec621e0586b1e8b9200000000000000000319e389800000000000000000e52000000000000001568b7b80000001aea1b5aaf01dab49ec600000cb115d6a592e3a00000001ba000000032ea000267e6fe8000000000083ab2b60000e607cd053430c0000b638db6a2a8efa96a8000000000000000007421cbebf9800029e000017cacee0000b3a0c6035662c800000013385d08000436017a3f894f0bc880000002894019800046180000b309480000fc40000000df22930caaa94a9760000000000000000003580516000000000022920000026000000000030708a50000b5da86e000158252a324408e00000001770d4680009d6914882680000002e0646300c0000000000025e6000000000007c2000228a7188728592a33cc190000000222a05b000000000000002ce6000000000038780d8084218a80000000d266a79f9c7f58000b0bb3b630629be2e9800000014b2000000000032421b42cc600003dc000000000000009fb0e36000000000010840000986835800000000005b5800000000000000000000000000000000000cb8000246c0000000000000000011ac00000000001c18b5700000518dc249900003bb962035c951a67c8000000236a09180007bf268e00032600000000000000079d9a8239d851200038be0000000bec22be7bdb1365c20000000127a31aa5e400000002d391fa00036401f700000000000b37102a000000071988e6b4236e090091500002b205b983e06a5b9508e726660000000000000016a29fa000000048e800000000003a78b4c5b80000000000023f868c0000dcc3400ab29ecb55082900007e909aa0de0000934b2cce3f93cc79228e40e1a21e000000006a00000000000000000000036027d105180000000143122000000006e0000010e96180000000000000012c00000001480000000000000000000000000000000000000001fb0000055c000000076b217c00000003ed8348000000099630280000d300000000000000050d14383fb00000001e3699b2532b38392cdd42d6e5dd359892d8362aff00000a3903c91fb5ba6630000b6bb290d51ad964309fc0bfa01266028000a30000020997826fc8000000000057c1f460003896c95a5be00000004c81f18da690eab630000000069aa99800000000004f18000abb844c1710000363af9600000005ff00
  | 50 => 0xd4e0002d342c6000000017b20000000b49800002e8f2e5920000d17202c5ef800000003aec47000026529843e881d87c6ae4c0000000c42205aaf000005950000000000051600000000000000061449d8000a2934ca000000030e836ae56813c00015d400035360002c565fb8000933800052f0000000099a4f7011c000297aa2f0000dcc000000023b293934c40000df884f04740001de20968000000091c40d80000090fce0000000000041caf6341c3d49444ccc37205f095e060480001c28f660000000000000000026a8000072c9d819663ae95fe89a091266cb17600000000712d90000000097b000088e1f720000000000000000035ae00000000000000000000000021ea00010806a1800096b121a1f128a049b8ecc0000000705264e0000000000000063d951424a00000000000a19077e0002d4800000005fe0dda00000000000000e2b0000c9c8000dea9a7000000000002514000000000000007c7000000000000000000d3421ba0000000a0b000000000000000000000000000035aa000196e00015c200000000000000000092e00000000001488872b8c675923e2024a9547e98848cdd216cab92fde0002b720001a9a00000000000ab0000000000000000e8000070800009be03200000000b35800000006f09092ef694703c40000bda0002a04c37142e5819cea00034cc2cc859e30f0000ab29f526e18d8a0002eee20e80002f21d269af8cae00035b60002702000089e515a19ae38167a000126878c0000000000000006c40000a76bea9510000197080d00008909c869840000000000045fa21a00007d4000285032b0000e05aa1c00000000000000000000071100000000640000167600000003198b0679d228600000009240d0a0002386000164400000000002db874aaa3a5ed9ad400000000002be6000030000014fc308a1400f2907600000000000f36000000000000000002c9aa8faf6eada0fc87491e6497a800044b800089289326b08000ab500008cc8000000199216b80007be8000000000000000000000000c6120da000000000000000000000bd1800097f0000000298898fb9260000000000000000000001659ab29c814d068d000000000000000f0c12b0000ce02d5000000000d38000c97b05ee2a00000000a344cbb1960000000338365e0000000b22b6e8970937c0000000680a8f6ce6915e0dc05c25a70000345000060eb42c38307c0e3b0b3e4a235f20000000aaa800018919d464d8426000000081834488b50698a5cb5bc76600000e221f0be280000000000000000000000000000e20000280800027e00001378745a73c03eb3ec000084e94ea0bc46c08c0b2230ca32d2bb40448030000108c16e800000000008bf820400028666370000000000022a80005eb8000000000000000005d6800000000009
  | 51 => 0x37134a600000000000000000000000025d40000000000000000000004ad973e0000000389000000012e087438408a880000002fe0000000000000000000000232146c00000007c5800000000004048b4085500005c6226c000000000034fa7a5000000000007e18a1067d0d422a799f606b8000c83800084aac540870000b6b000036516f4000078037ca14802c8114000263a000130a066914ecd68000d8d2052dc7033e90e0000819a4f012e000000002368589f80471000000001060000000000000000000000002d5400000000001b3a6b113b800007860002874b7b00000000000c2696e285b9ca08c58f9a29d151c082a20835e0dd410a062c186ac626aaac9e19c800086700000000000000095e00000006ea000000000000000000000159a00006000000000000285678410d2df80dd62681b8400000000002b1a000000090680000000000000000000020a8000114c000000000037d4d4f0cdeb4cb836e362448a260000e1c15b40000000000025c00000000000000000335200019fc000000024d87305d60f4e000000062580004f22928c6e0000a730000a5700000000bfc02580000000000c5e800000032d200000000001cd25bb00001939dce000132c2110b245f711f4000000037e8000be9800000000000000a8a45000000000000000000039c0eda0000000d2e9c38000000092e0000000000000000000cd800000000000000000000000000016c22e588b27ff96e839600008f7000015216160002a7ad08ad0aa719262000277ca278686ce32a446ba15180f8a1a638035a895c80001ec800000022fc55280e62f3085a5baa40ae0bb4bc00013c4000000000034d2cea0ce28cd0e0635b1eea000190e0002a74c98a0841359180070000037217c44051b4cd320226be1288a344000000000004268000c54b7f2d418906000340c4af80000001aa00003212ab7b73400000005960000c2f800000000b40000000000376e00000000000000e2704f000000007ec8000ab1000091b8000cb40000b9c80000000000636b1ce0400000000000000031c0000000036431ea851b36a00007a47c038dccfd31261530000000000055e8b9016836a436e80003940cec0000000000000000025f20000000b5f800086d800040c800000000002060000e2d9d8e761188c00012ce12a139a0002b9e0000000240004e00000000000000495000084100004a2a34a023800000024e8a600d926cfb33e49838e810c8a60c4699e6881800000000000001ac000006b0a71271a6682d52000000071280000000f9e00000000000000000000000000000000000000339000014daa6b38bc0000b7e75329f4000000000000005918000af6a722000000030aa52c0000000000015235a39660001212000000095e1d1444310cc0001d38151193400000004608
  | 52 => 0x80005670000000000000027e800000006f0b3bc000315e00029368f98000000205400000008328c560001be4bd01e06095b10066eb6da716212c3d600000f008a800000000000000000000000000000001042000000057e980e0001a60000000000011982cb38b229500004e40000687325072b80007b400006018830000000000000002af00001d416ac0000000937b0dac19986a00026b862193d600000008659a1400000000000000000000000000007d21aae711973a968ae620f627089ce8000000000000000000000a2a9cb80000002096acb868a00018ce21a93542cb8000612acc29f72c5c4dd0a84e0c8000413140eb138000932944a114000000000000002806aa81ab45a4a2786889ee400014ce87300008d136a810f2df60000000c1fb7a03c680005cf0cc600000000002ea4000000042d86f40752924cd400009e385dc00001680000000000000000000000000000bdd00007251a4eacd800064c8000000255c000000000026faa41057e5bb9faaaf7056a0000000155157800000000000000787800068b000098c82d0c0100002ee9fbcc5c80000001c722078ece00000000000000000021600000000001d5c0001bd416d000094b88b019c2b0060889220150762000000076c000000000003920000238800098880004d400002a706ae000000000016ca00000000001e6a000367600004f60c88000000219e9730000a9fac6628a00001b380003bc0000000000000034d855d00000001a660000f380ef80000000f8e0000000000111a000000000009d2c0b800014a800018980000002e1a00007f4356924e1970000000000000000000000000000000000000000000000000351236c1b28000189a0000000695000013b347e000309c114b22aca080006dd0000000000046690a0000007269b80002b000000588000c489cf600000006b8a8ba19f8eac000051400000000000000000380a0000000000172222e0f44000000035423d299d12780001ca4085000000000000002fd4cdc9c3200025227913862dea212631e2300861310c00024bc000000013e800066100000000000905a54e00000000000ce800007060001ecc000000000000000308000d9f8000a8f08d61649df612533381a9000000034aa00032fa61c365c354a98a240860abc48f24000309413f05bc000000002f80002cf2d746a009929800000e0e80005f631fc00000005a180007a6800081aa5680000000bb580002f4000052d04e0472355a2e900000000000a2b8000c730000a958000b6f88c21e8278295f00580000000b652312061b2deb1c376c93605b8426353e00000000000000000000000000000000000c0490f2b2a861c0000000000008200000000002b4c8580000698800030d911214e800096a12a600028c87230000d289ede184b2a2e47a094
  | 53 => 0x85a1908e14a43a243837c559000030b03faa0c345ade526b4c5ba2dc26a000000000005042d284810c8ea8b1d4e0003882c51800000027540000000bb1000061417920001c8494a368e00000000002e4eadd9f6065a8f26a3b335e00000003f4a254424b7b695833b41b8b552383a5b671e88000001c7c000195c3fab39e5bd8c1e0002654195000000000000002d6a2bf80009db3346000000000000000003814d2200000002106b580e10ad3800000000007721c4e0001be0a539496cc622b23cb33f0dac8000bf0b6fa302800070180003b098349ca37f00002d5856da16a1c502e4000022200022bc1128c5a00000000001b2200013c200000007f2069cb7f9c5c4301cf45ee9f24a4f8a4a62ea43420b28f038f00080000e4a00000006cc8000813000000039021af04c61c80000653800000000001d293aa00035f6000000056cb4b0c6400000000000938000000000009909f4000023840002cba966000000000000000000000000012822ca0000000a480000000000043900005d2a70a00000000000000cf20000b04b8642ed8000b31280c5bf800073880003ac80004110d9e25700000282e206058b8286a22f000030b80838000683a7a200015924be9aba000362058f0000000000000026c400033e8bf5a538cb88000519800000000000003708000000000006a6000306e5f300000000000000349400000000000000000000000000000000000cf5215645080000cb8000ce11346c92800050700005a6000000000004d996b2000000064e80000000000000000082b800000000004d20000a39a97005507588e91db20000000000000096ca2b8000289a0001b08c4780009de279804b8000dd500009bc0000000261c0001f0214900006dd80001598184000000037da3049890dd80000000aca80000002e8600000000000000000000000000000000000000000000016104a600002348a7e4b90a040000000000000000038ba0000000352abe81ec29660000000e4e2ce2000000000030f800023d040080003b7971a6d900007b208867470000000000013b800010d00b81e59b5a000098edabb486d439b50999103a000000030b9c04a4c800097280000001a760002f7e00000008ab06641478000000391c0000000c1580003e18000c6c2fe4cff177c00000004311d7e22400009b6a77435789e26c98000d1801ca4a4a934806ae6c68800003c500ca287314866097960950206caf891a67b81ee4cf921ea542ec067a00000001368000245a000000023180000002b06294235448900008a22f02270125add9000000024227502020d510000000201600000000000e1c05607b8b4c2d64c93000000000000000000000000000000000000afc000385052880003468cc40000bb8cec8000e20207e000000000000000000000429
  | 54 => 0x938b86c0003450531b77450980000000000be6176c914a6ce616000034f1eec394a4ea2690000000034c00000000000000000270c861a00a00033c400000000002124dc2b2a005a80007398a1e537000033f19f023e05d81d22f92395210ac22000000028d21402a920000000413800093708280002e8a27b00002bb8000df400000000000000311846e0564bd4195856e80000000000000170400000000002bfa000000000000003fc000048a80000000000530800000001ecb74262a49d000044daca833636dc74300000000000939abb80000000df1af900fd8000bda83e4bd68000000232400020f000000002bc8000000000000000000000000000000000000000002756000000085600002da000000000000000000cf3800000000000000000000000000000000002420000000063f00008fe000000011da000000000006e0000000000019540001bbe00000003740b800000c2800000000000000626330c0000c885971f3c9920000000000000000000000000000000000000002d7800063aa6d0000156ac5297d600000001c58fc6000141a9a8952049a9b7ed648000000058e00000000003898000000062e0d5cadf9e8e0c98ce4c4bb8a40a4b4168ee800057c800000000000000000b2f295ac34381a7fe1e3e0003824000175000000000002c7e880989475d27cc98a108e640ae848aa81da371a17200007c8000272c00000000000000335000000022c2000000025d00000002d781bba9d20002b40365b43e356138400010fa22f800091c800000018c642e00001330000648000051480005118000000075eb8000ee000000000000000000000000000000001d00ee0000000000000035cc0000a7080e0000d35800000000000000000000147000018002329696752800000024a20001b48000105e5e4000000000007552e1812586380000000cf28000000367a0000000aab00009fd800019336d0e03800000000000000000a7980001cd87f04380506c24a2d85270000cb905d2000000000016d8a80000080eb3ba0000000be30000000120870fb230dc380003ad875a00000004b4049263400000002d6c39bb2da0dd360c000000000000000000000947a608e030ac400000000000e84000a8b479f000000000003d80000000077200000009a58000000000000000000000000ab0800000033640000000ca5ad00c49000000030aa0000de4000332a00000000000000102000037f0000d8b000000000002c480000002f269a49a722ae800000027960000000d0e978c00008fa3231beaa97a0861581962041359cb378000000000000000000000488000000000000000000e1e13e045800035ce7e30000000000000023a60000f1e8a132c20000000000000045bb04a0001aac00022e4901a70e000000000000000000000000000
  | 55 => 0x1b080000000000000000093f80005900f7eb491b104402118dff12bca6f1caa6eb0ff6bbd00000000000000110a00034e80002e025448000000000000000009a6000000008540b00000000000000005f043220be0000000000106a000341e28c8000000158a27c0000751800000000009358000951000060080000000000dc9889a59e000000000000000000d6c98a038a800070280000001a1e0000000000000004c99960000000d999b4a3cf00007858000ac394f200000007659abe4eb0000494000061e2afece88bec00030265d380000001e08000000000032e6000000000011a200029480ca2dcc77480005400000499800037b2ba2a3100000f7b59000000000000000000000000000000000000000000000010281f80000000000000000008d98766028b4760000c3445b319880c8866da8000092593e2a6707ac0000000000000000000000000000000248e000000000000000000c109d2229c85300ae318b006000155800033d868180003da8000000160e3588000000061600001ce0000000c9c00000000000dfb8000df3800005299885db9c9808b102025130800a11e1c3359b46ca1a75e37380000632d9a83f80004a800000001bf600000000001ad2ab38b2a980824200000000000000000093c0000288351800000021b0b569da827f8000000000060a800014b2c8c0000000cbb8000000000000027beaa000000001a42000000000000000000e12bd62eb8cb6000000031e8000000000032b00002f2a0000000000006cc1e8000000000000035a035e87ae843b856b1a152aa23b208559800000009ca0000000000116a000049c6138000a55800020704600002640e26800005d97300001138000000056a80220002ab817d0000000000000000008e30000aa2800000000000002ddcac7000000000000000000d6380000000000a7d8c6e2fd2ecc20406d4ad60000a388000e558b1690b986c2c98000ba98fee000345492d000000012940001c02c2b02861e434a860237764e5add8722adde7db9b9e26daccc4fb84623280c12366096492c2036000223a00ca7760000000c449cc65d10000c1600000000000000000000000008162e7a00000000000cfec242232322800000016700000000000384a0000000537800000015f6000000000011d8c1d8d2ca68800099b8ad61f1a5b4a9a0000d48377200000000000000000336299e8f720000000cc4800000000000000000000326c0002a702350000000000036f05fc0000000d6880006aa03f800013aeb7800000000000d258000566000000000009a7acec0001db800000000002c3200000000001490000154400007e23102efa00000000001ec20001f6a00000003db25e0c6f00003a22b620000000473af660000b6e0001e2a00000000001b2c0001844477800000020ec00
  | 56 => 0x27805e99a8e73780000003102667b67000000002330000b4517b0000242a00000000000000000000000037da00002d2000000000000006fd2e5000000008b48000cf7aad807d0f7a576840200031c673300004c4000000000000000e2e0000000000146a00003a483c98840000000e3100ea000154000026c272a1c1c1878000a1e0000a7034e62e88000000305a00021bc000000000000003500000000000062d9746a000000c81a9f2b57a38e8889abc00007aa4209ba666a8000828800000000006e8887664e25da000000038280007b5028a1a2146400011348dd088e5ad8c080000000000000000000000002888000000000000000001c90000364cd8eb31edcca96abeda6c86c09d68000000058b8000000000079780008c09726a8780007c380000001a5e0002c30669a1eca6a800000000003b825fa650adfc00000006f9800000035d000013e60000000b11ab0400019d800000000000000a709e824919e70000000053f9b2400000704d700000000dfec1a37c48e5308657100008e800000000000000093e3fc80000002e9e000217e871821a8c280006e80118a94a3fc743951e00000005c5988e63231a8078ae14a858a6600037f63a518488a38000000060644b31f2000168a00000f0238001c28c06fe3eb0000c76800000036540002314141000000000000000000000111e029a492d7680000000000b1c8b4200017e6ca7a5de000000000000002740000c38000074d800000022ba0000000bdc14720000000a16a174000000000027aa00006ba00030440001852cbc9b5200011f69a3000000000000000000d8781e40000000b24973200000000000000ca10662d7780008ba8000a888000caf1dda9c78000448967cc4e80000001ea400000000ae0b7639e26340000000c230000000000003137fa6358c3e2b680007cf80005c282a89432d72312800000000000000000b90b046000000000000007a300000cb182c0000000bcc3310000000000000008090000000000076e80001660ee8a5e00000000000000000070b0000000227a7da0000c8530ae14b800000018a221d24f600026ee66d0b7a000000056115ea242000000000000002088d0603c22bd800000000000000000b7c8000000000074808b40988000d441038d1e1c0c00004c40001cce88380000000000000064800a0000000369eca5055e648800000018a6daf8000d6980000002f9400021900000000d42800095600000000000cde8000434000073e80000000000ca380005de2f10bb400005e83894b0e80007ab8af8a11150866ba9a800000009b4b0f6e419efebb680009d60b7c0000e7a927800000019a200010500001eca1ce232c7d880000262da0bda03c85fd000000031140002f2e0000000000000000030c06ec0000930a9601a78000000307c28900
  | 57 => 0x760088000000026fca441e0200000002c08000000074400000005dd8e1600000000000000e4cb796d242e3263b800016aa3aa8bb1b6618f303c0000000000230800000000000000ad90000a50312c000310eb2898e800000000000000b7ab8600000000000000000000003600000b4e9666cef806e88580000000000cd5096ec968000000000000026b6000364a2d1800000000000000d1687cb2167fb9880725b498986a482b6a83ee84798f8754b7e282e8000c6b86aa11685027b988e80000000000371a0000000000000000021423d9000000000000000000538000032c9d625568000000029e80b80000002862847148400000004088000000000000000000000000dc8a00800025260002e60000315c00000001fb800000000000001dae0000e0800016944ef81a2c0b07d8ae60000000083e00000007b731fa1d500000001de6dbb14d25558000000000000000007f38ee45e1959e73600006941fc400006348f786685d9000000000000000f043ca0aec0000ef882d9d5000000000000fe60002c984ff3576dd2aa0cbe000004bc8000000000000000004fd8000900000072b00000002c76e1fb34a00005280002d2c6ee2502000179a986100a81d94f47980000b5380000000926000000058f8000b7e0000000000056300009d9000003900000000000ab98000000000000033c6000000000034100000280000042aaa900000001a280000000000000000012024408260000000000000000000000000172400004b60002f0eb6609cc367347400000000000000000000000000000002f9c000000000000000000000000000000007d6000162204c2ea88751664d7900000001a1697f8f8411e9d8a000143670587087d52aaeb9c1d9037282f80001b7a66d9f7cdf60000d89256600010de676a3962b1afea5b108ee03d1e865522298c17183e783885653582d6000000000000000000a0a0002b440000a1a3d525486d500000000000696171c0000fde000000000000000001ade00033d62a680000000000000181c032142ab0885b260a0000000000000000000002cb87a4205e0000000000000069100000000000000000000000000000000000247cb2ca418000000003400000000000000000061d8000000190a7a98000003800000009b8000000012b80000000000cbc00000ba800000000000002ef048380005cba7900000ba8000355600000000000000de600000000000955191200036b607980000000000c0e8e7e0000000aa40000000000000000000000000000295800000000000000a632616000099e0001cc8000000000023fa00000008488ca8d50aeea178000000014e221a00000000c9663d178e341000000000000012f38000326400000007fc000000000000002d88dd8234600000000000000000000010db7b000000000
  | 58 => 0x590000a488c7c00000008d780000000000c750000dd603ec7220000000000000000000000000000225a0002296e549ab8661835013a02f20000000bb2b47095b0050ca30000c6180004e3348c0000000000000000000000000e220001d1a000000000023203c608dc83f2cc0000338e0001f2800000005f8800041a000000000000001372bdc800006f1df80002b7c00000005578000000340a6f700000000000d04a0c2df796f2c108000000191cb1794baa720abec8da45ec94a81a0000f8a50c078a25b00004fa000098f13f8d89ab1000000000002cc80000b720000000000000000009f40000000000000000000003f90e9215a000000030e8a7a800000000000002a4222980000b3a1800000bee00028d0000283400000000002a32ddaab8224318a869a04d42fd8000000000000000009de80000ed800000000000000000d5f00008fd0000000000000004a45b734e0000000000000008b1287a7ac80000001b9a00000004d4a996de6b142b960af09112e7e000052600000009b011600000000da8a86800014e8a72a710000000000000000000000734023400013bcddf800068f0000e538f627ee8000000382865e9db60000000000186800037cc0001d800001c3adbc80000001ce8bc78000c8e800000006d241c8000000000000000000002e0a0000000b122c745b380000000000000000047a80000000bb0e1a18420002f3c02d94c8aac2a840000c422921626c68b508000000091e8b543150000b3385fed0536800000f5e0000746000000000033403a680007e5000095880000002cd4000000080980000000000000194687e00009bc8000000000000036420000cce57e1bcc8f100000000000c1c909c000000000000000000000000000009fb3882ed00003b2001a71780001a0afacc3cb7ec8dc27340000000684ac180001b6e0000000a8399b8bb480002b7362a0c9086eddc0000a0e000000011cc00029b42bd00005010000dd98000000000000000000000000c3a80000ab0000e1a8000000000000000000000000000000073c33c20000000000213800012b812880000002af4000000033c000075c8d864652ad018121d600024c400000a400004dc000234e00033da91c30baad2a61ed10266882700002090f70a148000000016e4e08000000326e7410db840d27da000000000027ea000254c000168c00014ca0001b826da0000000115a000000000036600578000000000000018820000000a79000000000000000fb80000000000000000001100000000000211a105000043a000000005a20000000000000000025c400000000000000444175e0000000d5b87f8b0902feafc9f9e4fe8000332800000000005499284d72800000000000000000998000000020e20000000dd18000000162ab41965a42ca8a2000204e8458
  | 59 => 0x393e000000012100003969a1871b9e8800000008b300a800000009440000000368a0001fac8df28186969d5ac2d842e45180009332498c2880001208000000000085100000003584000000000001360000000a7e177a7d68000000000025c8000000000000000000000000000000000000007ef80000001f10000192609c8000000000000000000000000000000000026ba902180c000000049001b84f3a27000034fe00000000001dd6000000000000000000c5c000000000000000002c380000e3800000000000000d37835c0000000000000000000001b60c16000000000021ac000000000016b0872388e82e0000807b3563862952000000051000001c0000000002de000000000000000000000000000000022040000000174000013d0000000000000000000001c1240780000002a40000114400000006ff000000000007cd80000000000d1a00000c200003af3782000000000018365a0a91800280007e4950e878ac60d5e313e000000011d883800009b05c4166ac6d281687928022c28000000084a000000047088f60000000000000000022b4000000000000000001c74a0e80000000000000009aa6d80000001f08e5300002068000ba7318a241065285283fc4b28000b4e225e0c7022a21496be66c0000c56235200000003ef80186f41ac6000211212a9d120000e0457bb6780000000b0f80007ff358c0001dccbaa8000000000000000000002be0000000033e80489919eb42ba824e0000000ac600000000000c66800000000000000000314279e8cd83465008000da0913a9228e620000000cae800000026bcb50000000020f8000000000028ee00000008f380000b0924c4b88000bbc80000000000000002c44c8000aaca4aeabd9e4ec312b90e2c000089a92ea0000000000047e0000000000000000000000000000000301e0000000000000035c00000040000b47889600000006b81a4a0000000409a9d800012c200027920000000a1b1a36000000000017a400034be012b3d09f19df0d5210a40002c82e2b9058a8d8000e2a89400000000726848c00000004b702be0000000b7e931a0002bcad1335ec0000000108864424aa9d6000000000000000000000000000019d8fe8b7c00000001b960000000aa1986e578b3e24e98000e04800000000000001afe8050000000000056500000000000d09197209f09becde0270b8f0000000148a000293c136232a517373e0000e1400000009c4b91a84a03800000000000000000000004b180000000000000000000017840001bd20000000000000011e0000a89a2a40002c1400011300000000afb03f20b8aa8c0000000c4c800060400f20000000000000014283da11500001540000000000016b0000bbe00000000000000080269f000000000000001ece00000000000000
  | 60 => 0xd3f2612bb3800000018b400000000000000000000000007ea9c535e6d5829e87c311d0daeb0c62c881d2c258000bf10fc222923220dda1ce50cad2aa821e9600000000000000bc9078e46a00aa2eb324e94f0000000000000004c28248de62d2b2347c99c80c120a4e3902fec99718c43fd00007a828a6b8798f28efad86de000d2b031630b9e00ec8c62d3cdae0000c0900000000000643000000000000000000000147601004d06540000000236e54e000000024c00001cd60f59d94ac3239e000000033a8956d7f98f00001128000000000010ee00000000001b7800009a6000000000026aa0002b300000000000000000007a200027620000d440000ebe2cda6700000000912abae4daafbc00000007dd00009350a2cc06264cba3225600000000000000000189c0ac000072f0e1a00000006a20000000000000000000000ffa000000000000000000962000000009d1ee80001a0a0000000ab3000000000007b6823c9e100000001b0a0000000573a37655c000047e000077108f26f61756000021e00000004058000471b81e000000000000003770000c862258000000000027fc000224ec889b62000000000036d66c4919e259a3720000d2a000000028500000000000000000000023fe02b00000000000237b280196a9e000000008fa800000000000000000788000000028820000000697000000000000000000000000000015be0c417e808925c64691dde61f8000000000000000004aa80bc000000000000003018000000120cba380006400e3a00000008d80000c1d00004030d08a5bafa20e98d3238c0da66d7a3f2cba31d8c1e351cde3b060caa10cedc480001f438a09f40000b3f948e00000003aa000054a000029f0000000000043e19140000000c14000000007a631b000000000000002d68130000000000007958000cb2ae3e0002d2045d030400000002a080005139f3800000000000000af78df4c3b800000016de0002e2cda31daa71a866c00000007752eb2b1e0b560e48d0ca9638f800000000000000000000022f000083780004ba2990000341a1338000000000074ba7ba83e815c7c12098610149836816a61e22e8200000000000000a5b000063993fe764b7888fa2bb600031f80fc18389f3a662def943e00000003aa80009100000d8c9760307000003301cccb700008330000000235cbea2262295b95c5ad19c65f6ad62c459c3c0000000151ae34000000000533261a4adbc0000000ab0011ec59a8be7a2a70088b33ee0000000000139854f12344168d5421339640000000000000000000004c200008ef2a0a0130000b788000c000fd8000371881b38b8472b2889b7a6e0c8b00000771c5444f907400029ce00031ee020297402700000002eb4b098000000000000000002f913f2000160a000
  | 61 => 0x31ac0e095d2aba0832000270600021f40000000000000000009ce3f50000ca4800000000003ac02820000000000377c0000000062800099f02fc021a1b497583d4dc58000606073a170000000027d600000000001604c8080000000000000000089db10648bb1561e496f05a80000b7d24a61be80000d917ce12e80001d02680000390c000372a00000001961a26a160000b3f2bc4e099c5000e8e341ed000070d0000000042c2712ad6b8700000048000000000000000008008000abb17e4d57000000000000000000000031a15d2ee4458b82200000000000000debadc400000007aa96d4283b8c8000318c0000d1842f80005052822000000000000001a58000000252051f0000000220a00006f25aa9c2a000000077f23427f70000000255e00000000000000af88000000000000010244c7ab5a0000000bf3348098b00001b017b800033960001d78c3b000000000000bb000000000000000000cfd8000d7d000000023a20001bc40000000000287e777393c5029b6c9d2904ad860f089500a8c3e4a30e45490f40000000903800000038c0d45b56a00026e4000000000000000002a2410e00000000d9a0000976cc80e3e000000038a00000000000880000000000000000000000000083a0bfe7dd80000000000000000000002c400024100000000000000000020cedaa800013cb06a2192a100001bda0c780001100000000000000000006b202e60001054e218000c9f00000000628000375a00000008d20f46000142c0000000000301000000004a6b2260000000a07800000000000000000000206800000008f2b5dc0000000000000000000000949e9835f9f98399800000000000002a54b2f80000002c440002326000000017280003e700000000000cea800094ab48e1ac8000000153247800000000000000000011b2f2090b215202206e6a9835b4000000000023d400000000000f06000000000000000001450000000005c094c000000026292864f49da0d478000aba80000000000b018000000000085e0000000000000000008f62ff60001018455b2ae0000e8c9fc0034247800033c929e00000000000996d83977e0408000cd23724015ae0e47897520000000d7580001739ef24e51164c38a3c600000000000b1444504bc00035b80000000cb50f220000000a9e0000c14b16c30922c069931ca12630627be0000000000089200000000000000000000000000000000000000035bac84b738000d412e04d871bd6000000095b8c145cab5d400020ac00030fe000000000000002e80000000165e28f24a42549e4a000000000000000000000000000099a80001c38000d29000000039160000000000000086205fa96e2574000000000029820000000288903e0000b383bb00006b5800073900000002eb600000003193922000000
  | 62 => 0xd42f51f70e288000790000060b8000bf22e40000374863526501d904c8523355825a8000bb52f16d19199832089de13a8000000000052800000001f82c102cea0001bc80000c7600036c6d7c0ed6000112a75f1af882a800000024beaa880000000000000000000000009b880000000000d3e0000000293800030e60001b8e000000083000007f78000000013e0002c2c0000000000000000000004c58000acf8000000000000008ea694b6681d480006090000000000000015cc0339a56000000000022e6000191a67720d8000000000000000000000000000037b8000313000000000000000000000000000008e4988000000000000000000000009e76980000a831107099d3e0001f7a000030648180000000d84288000091180000000000000134e0003652ae112b200000000000000201800000019fad69396848e01569a08172a339ba46e529463bcb6c2b5ea5ce2b4b8f08d4249ade486c8000068eb2ba65aac780000000000000004465f991000000000000000000000032499e000000008c401be000000000000007c48b6200000000002942000000000026a647b0d2000000005fdb5220002cac000000094d000000007680000000ce9000000017aa0000000b4d8000000161200000004b0000000000000000602000136483819cc2d2327e000387c4460c48000136c00000000000000e448000e43800000004160000000b9da22400000000000000b99000027c93880002e4400000003e90000000000066021822c6800000000001a5000000015024e4ab50000260e85400fcd2cb21e71e349c530259a097b452a9a86dccb1ac860a32480000000000000007e2221c00000000002458ccb80da0000000000000020b800000000004b69fd400000009d383840000c00000000000000000001860b95000000000006d6068496500004d093b65108fa00002672000000000010940000000000369ccca2f0000000002fc80000003930000000088480000002b7a0000d76ae007bc01e2e5eafe000066b0000158b66c81d00000000000000005200000006bb0000a1180e01ea000062f0000946297e00000000000000b5f000000000000000000cbfb62ebf00000a638000000347c482800003180004f40000326a3c00058000036234c8a0a09e9540eea8ca04d200033ac7fa000059803320001c70d490000000108aaf310ba0000000a1c0e6ce1c8914c9e894ac5a143abc5000026312a200016720000000c78800000000000000000622b7fee338000e0d000065300000000000000000000000000002aa800000000000000000000000000002f194b6aa598925fb2080e130000175b0fa00000000000000803192e1ca9bc000004e4b9f14d4be080004d88000000000032100008ac000034380000000000183331400000000000000000000000
  | 63 => 0x3438b4410354c4c9b9540001e2ce4532980001944d9c827a0000000ca9800071d800000035c4ce5138645c8000d21097a0000000db200003a02bb2000359a00030e40002c2a000000000000f800000006ad800000000005250caa54d067c2fe03e6000281266f2044000230c17e00008be08348b412188ce2e9606600005da1e3a9fea84a00014cc5e8989053600000001ffa00017380000000d2b00000001cb4000315a74a345e3340000297000010298625ef038e0001772afc00f6a02800000000007909ec6521970c06daf7cb0d800000005ec00000000000eb894f8000d19a5d0946ad460a628e80000000000000030300000000000000301600036060000fca00001bab4080003c000000001e380000000000000000000000002e0c10c3392d4600007b120dc0000000512000000008621eea07a15b9eee4411ad80000000c34a91a4c113ca6bd8000c8a37906a106100e60000de90000b3900000000a725e722669a280001d5b432000000c2c8000000000006c820b21c985104b99dc27f19e04aaf195e0000000000000048b0000000000000036f00000d748690000279185a3d214b0e00224c000000027180000000000ce71a3a00000003e2084044f3854a3eb6ee0000d1c8b1b83c00014faab493228ee22da5d72e3000025e815eab6ad991a8c21180003690b0e0000000c8c8090000000051a0000c7d36f40000ef6c358a6e4a322f27bc2edc00000004cd0a1211b8000db380001de000000000000002f76c6482e80c58000d3882f60000000150b306a8baefe00000001481b8851310fcb2d12805088be8e440000bc2b5401dd8bcad5994780000000000000000000000002cd00000000000326a00010ec00000000000000ae2afce000131412c80000000000000000000000006458000b142a12a990d3a8a31a2e39311dc000000000000000000c320001e80bfc0000d2d8000000000000000006fba1340000a8818c00004570712000000000000000000000863a5560000000594000064902ba00000000000000000000000000007039c60dbf80000848cd2ba6000000000000000000a12040000028844c021d8000000028600001630b66d3b80005ae000092a000000000000000f74d3c1248000000048f2926000000000007820001a00000360a000000082295ac2e19d18000000000000000002c6e6a900000000000831800057a013a0000000d709ae61eda69428d829c85d945e0001cec000000094190e6cdf0ce6000000024820060002752c3f0000bba289610900004841ab07af2e52a93835e25539347d738d6000128e9a190b04389e7e07c80000000000d0b80000000bc239100007851ff2000000069e287647c38f60000f02a418000000072e043afae0db000000020ee0001b9080000000002d660000000000000000012
  | 64 => 0x2a460000000000000074d248869fae6600022209c100009c918460000442903000067e1d0a00015ec7d380007f30000352000044590ac21c858838b0b88e1380000001b3815b000006400002608000000210cc690aa290f80000000000000000000000006d3802a0001dd800035c60001fec000000022baf5e0000000000033c000040689f80005f000000000000000000000032000000aae0002d0eb6c00000001e92080a6ea1dd000000007f6a9f043e49126d873710da1822de8b61090a01d1fa21040b1e000193c619203c0001370d920000a98800046c800000000000f1b29a000000019d000000000003ddb0dedf900000002474c7fb00c0000b9e00014f614f80006172de4de2ad22000366a0001d5600000008c180008bd245094d8000bb229928340000000000000000000000000000000051800000000000d1ea36c000074e73f00000000000b2000001ff000000000004bf8000bac00000002a020fd0000853ab260001f7e00000005600000000000000029d4def0000d20b63600034020000d2844702280000000000169a0000b1c7ab00000001cc0000127200003cc000000000000004670622870800000000007a700000000000000099800027720000000000000000000000000000b2d8000000000086a817488fb8300003846000000000000000000000ba6a2deb6880004cdaf0ce3e80000000000be1800000000000c500000000aca9d000000000f82c8b95e40002fa40000000c920000225000000000000000000000000000000e2b328c5800012302ae08fc00003948e2000000000000001dee00000000002cf227e870c58680000002ac8a2300000942330a07062eb4f8f5c3dba7860000000139934cd95b300bd2800095fb644000000003736d25c3af1aaf20000000149231d060e5a7b90850800005f7a1980af25646f29e2eda61d3c7c1845e3cf8fe06558000aee80000000000000314c000321c0000000c3396ba000000000014acd12b72e00001fa60f16c6e0ab06c00021a01db8de269d00686cbb04e76fa3b40000000000000000020e40001f6c0001df2665000051b810c6291d06000000000000000000000017a5f40001c240000000216292a0002fba9f99ce01e11cb632019e426f15dc62a838c0001e26cf81602ac224b209b956e7d0b4c6e2298fa401859496c2da800000009cc9c48d7a0000000000000027b418d893858737b89c62832abf2ee0000164c1219b140000000cb3b4005392a3088d80006daa590b440000000290000009a2000000000000000000000bd080000000000000000000002d40001a6a0000000000131c00012320000000000000000000000000000000000071b0000b4680009a11fe60e718145821aa65e29b06d6186c67c8914a527a3e0d7619780d60f302
  | 65 => 0x598879ac0c98d8cc71ca2be6b1283ff89d442d1a467eb80005d98000000000000029da0000000d52b0a400018fe0000000000000093b31f00000000000000001080000000000000000000000000000000da9800000000000f431300a6925e6bf2d9c7b800000000000000192c0003360000000000002ae9a6826a000000000000005c015e600025800000000000136e000000000019c400013ecb4b80000000302b12800019a8000adc00000002b2c00026521fe80000000000818adc60001a94cc5800077430f090c00000001530000380200003bc4b3000088c1b440001ed82b780000000000ac4a530d5ca2a800000000002b322f60000000000083d20b0669246a967af34000000000000003990094820ac0a16d827804583d2bee0230ac596a407d80000000000bb88ccc0000000d7e24fc8f08fc00520000b2900004ec80000000000000000000000000000000000390a00000000bb800000000003b8a4940000000d4327e46ffb8de00008acc698000a5880000000352d36800000034a04df8000000000000013de0000000479800006a800000028540000cb0000000000000000000000b84ac02000283c3a199a80001c5a8e49d6e0000f566380000c0380000002bf693e0000af583b28910000dd894ec000000000015040000000cf71ee216f94be00000000082a4c00000000000a02ca700000002a72d8100000e880000000dbe00000000000000000000080fb8200002ada00031400001dec3d41cb800000001c085d4406a1de17a28fe0000000000000000000006b680000002a186fa0000000241c56bab74d62000000027d4cffa8cc0002644000000073080004ce800000000000001720000000000000000000000000000000000000c480000000000b528000c8f8000000205600000000002ba400000008fd80000002736000000000029a40000f680002dd20000000000000046f80000000000b04000064100006cd37a67f6231a00000005f4921c07a00001bf00002261b7200009467ed8b602c20000000152e00000008e2ac64205989e7ee2ae20002272152b6f800016fa9632f54d658000a7b372cd0d00000003274b559cb20002e2a86300002768000432b82c41e00000001e840001d48000000000000006c70000d10a23c4b5b85a59a079c0350f32dd0320a2f7049a000279490f0000000036e0000a96000000000032b400013b4ae72744000000000014e60001cc401180002ba0000affa4260000000a0380000000000348a4fa0002290000276a00000000000000d2e232e7c29afa475105c91705329eb8464c5d0f8072981ac4aea6e60000000308044e000000000030b27718000000000040b8000000073400000000000cf4a043104000290ed8a164ec0d0efe54d800000000004700000ae98a903620bd6dfe2f780000
  | 66 => 0x161e0ee80008a029862d42f64000000000000000ad8000000000000000000000f1000008d83b6118e0002da631e8c9c0000ae6000000000036f600000000000000dcf21c0000198a0000000000000000010dc740800091522d629180007af96f8c89181edb7ac589f7a27c000000000006e40be88ecc7b07d20002524000302a0002994000000048f800000000002dd0000000050e00000002b380000000000000000096380000000000000000000000000000000c4a957e652087e3300000000387a42a8000000000082d000000028dc3e60000c790ef44491c0800002b49321a9c75c239800036d4000000000000005618000000000000000000000000000000070bb36e0001b5600000009f8859a000134a00000009b5800052080ded5c2ffcc901690ba81600000239a0000eae0002b5c00000000000000758057200000000002f2c57d36fc1e7805a2221d4400015d8000000030100000000a64b4480000002a9c000300246222e0000000000000008f90000000071ac6f8c680001de40002070b28363e00000005c50fbcc8e07e60ce137a541aa8e7a8a65600033f2000301c00000004cc000079a388800000000e7a214000020803a000000000000df800000000000000000000154c8ec045c1929e0c7de2638553aa5a73ca4320002d4cc60800000000d6c580000000269c0000000000240415680001789acccd08000000360000000000000000000000033200000000000d84800063b342600000004550b780000000a1c80002c40000c5f8be600024f266700000000000c5f368423d077c0d0904641580002a18ad41012eac000000000012fc00000000000000000000000000000000000000000000030a8000000032400000003038706800013880000000000d8500000000a44000379c0000000000000000027f8018184c00000000000000bd8800071a14a60000000ac900000003756062000022492360000000c151e467479c928048cbc000000000000000000000000000000000000003554000346c000000079700000000000000000000000000002f5ce24a6ac4dd80000000000be3adb40003204000063e08fa048aad00000cc241e2ca215abd4800000007109ab800028e80000002a9abfb8000000327675b0000000000000010c6000094e0000000956800000025bc0000000e278ea04bd823adee8000000000000000008ed9e4cc20997c36c8d2e59d3844a0f827600004480000000a3180007f2800000000000510000000000000028360000000000225c0000000960837a6c69cfe00002a4d8880002f00b0000036880000000cc200000001cda00000003c70000000000000000001f3118a000000000018721bb08040000000000000000000000778ea600000009c9af06df480000000000000000049f000000000007cc1e52
  | 67 => 0xe1a41dca0000000000000052e000061d13d400000008e08b70c2c000000017401b6907c0002f180002a6e0b700000002b5e0000000000000000000000001d5e3250cb667a8000000168050780000001a9000000004bbb1aa2b8000041980003590000b8e229e0002bac00009f6c0f9f56840271600004906d080000000000a0bab92e582c28d6b1dea4f6b7ac00000000002a280001918000291c2021b180000000000000025c0000675978800000000000580b9b80000000000000000000000000000000000291634e000049700004ee800000008dac3d25887209226839a1e8000000016c365a0000000a432504000000000000004e026262c1223412d2a7667405e400000000000000000000000034c20000000000344e000163a00000000000000000000078c871e0000000000357e0000c5200007e4127b96c00001a00502246d15af5600000002ef00009a20268000000000010bcb8a000067b000000000008040f201a834f60000ca2000000000000000000000000087c1c90d7c37800007b58000000000000000000000000000000000000000000000000000000005ea00000000002db204b000000000003b100006cd80000000000857383843f98cc000000000000003b714eaa012d82934000000000004d7806a00000000000000a51213edb98138172256a0000000000017c7328000aa50e8a865208c000000000000009130000d1c8910e02000000027d200037c265900000000afa000057000000000000ac84aa00000001200cc8b03039580000001d3a1fb00000002ebeacd0daa000000000009240000000000000000000000001cba0002462d702a820000000dc00000dba97c8000363c00000000000000b76a03000035d2bd1039a36b1a243449060be20000c6d8c0202c2a4a796392881f2cda000000011a00000000000000000000000000000f3a00000000d9800056c0000000000037a258410482ca9b70446000000065b0f7c0000000a772d0c01f0000e160000000000041c0000af3a5dc000000000000000000000a6680000000000d7a8e5e0ed00007828000883000000000003b28000000134400000004850000b05b2e0000352846480000000000000300a000000000000005bf0fba00026e8000000000000000000000072018e55c80000001b8c79b00000000000ceb9af289d0d660002dbacc1000000000003cd0870a47806446a80000001e5000021361f2a12ed7e8f4a56f1fb4a3d1a8a00000000002e22d93a1700000200d4e3804ccd26b0ad48b5c1ff80001110000812830a000381800000006bc0000cce800000021f66ee8000000130e1628000000278c000191e8c710860000000000000000000000000cbe9db900046b8000000310a864b138da48000b34800000037060000c984f6000000021fc0000000000
  | 68 => 0xae800002ebb71ec7d8000969a37ee4a9a4800027b000000000000000177800000000000000000e3d00000001e783e98000000000000000008578000000000000000000002d923f41a0400037dc00000002798000000000096b871c0000000000008c296b6c00000000000007e25a0000c88359445d80000000fb249280000e424c60000000abe000058d0eb4d03858275082c8d0a021001880000000000000145a000000009b00002e10000000000081b8000cc0800000000000d12cf45c193400000000e38952200012226e6054049b194a24d201c00000000000e6ab240bbe000313c73e000000029de2859f20092800055891b400000000000000a2b34c00ce9d9c06c8f406df000000000005778000b0d0000000000000032f400000000489b706d02a202fab95e3fe00004ac0000000233e00015a8c08047015f024c00000000000000000162800039629ea23dab8d888c0000000000047c107967e2ad8a5e4288000000075c77a0000000285e00001c2a7f955208c8b64dce800000000000000000000000000000000002a8800000009d080007e10bb20000000000000000023622a017c60002fa0000000000000005508000965800000000000000000000000000000000000000672185e3f70000000000051e800000024da0002c400000000ce2b86600000003218000000384276690f03180e98a8e00000002b2200000003a91c5200028d4000000000028f82a4800000000000000000137800015600000002260000000000000000000d24b458000e3f0000bbb0794000000000000000000000972168800000000001e549e6800015dace8b1f000021b2f4c54300000000000000000000000002cd2356637814255d800000000004aba8b6a74000016900000a886ac6c00000cbb00006cf00000001c225e78bdecdf8000d2294ae7d41258de7b2c800025ee43503682a3800000000003d091787fd8000000082a11cb918000000000000000001108000000000026ca0000000c2f000026c80002960b5a33696c8aa6007a740080ad2bab48c588000000160cd8680004b2185414f00000001c1e000000000000000002130099a676bf49b30000000000006f6919000000000000000000c74000000000000000000715aa1a00000008fc158e0000000b1680000000000ba498c2d60000014c02584240000000112054934b400000005af00000002efcc749e7a00001f00ac80004bd00004c904fe329808a155a5081ad9282c8400001918ae400000006068d56d40000000000000000000000000067780000000efccd10000000000000000001c12078d5b32f600038d40000000bf28a089ac80000000000000000000000000000000a1f000000000000000000000000000000000002fd059b00006e4b52e18c8880af4000017680000000c7
  | 69 => 0xb01c612f059b92de3c4ab8e0002ab60003786a578000000318e05e0000000000000000004fd000000011260000000c280000571b09e86f800041914aab70b78492825a000001600000000c5e130619800000000000000000000000000000000000000000017ea0000000103b530000076c4bb15d00001a08000000000000008eb2ff2000000068431b2000386e1030000d082c52000000084400000000000e1d00005fc8000d588e68c720000e308372000000000000000002a5000000000001bf8a451db41cc9820df98000000000000000003938d3400000000001c64baf09f8000000000000002b41d6a000208e000226e0000000000000023c00006c33022b0100005f50000000000092b0000000277e000000059580000002c4cda580008140000e34800000000000000000aa9800087728260001f90bf6b36ca7c1ceeb0809ea04aa592290000070c1826000048e31cb2fc58da2a6b79aec2e07000000011ba05f800000000008ba0000000000000000007b000000000000000000038c838a0001d1064a0000231000024b11a6879949a630000016731200002c1a4f800007ae0000147000055f00004ad2b0a00000000d00000000367400000003d6aa340003008d918be20001cd4e178f0a1862466cac9bb4000000000000000000000abe8a386900000ce080000faabd241f863a000197600000005c480000002f360002226b89848a7e58000a2ca54a9138000a0529ae00033b80002e94d0f1d660002b3a00000008e009c878f000019e80009180000000222800000000001bc60003502000000000000003ff20f60000c0e58c819209113282aa8a2ea81a3782800000000000000000009ee2542ab1a3ee00026040003942aa7a33a00000000000000000000087122ce39182dab1a9f9a0001c9ec2d0006000000000017360001096000080e0000000a3a80000000bd20000d3e00026a00000194bc10b8cbc21cb040b12566ec8d020000000000000000000000002364000000000000000002abe47c91bc0000ed0cf9933200000002b300005e5081400005c6000035a0000000000000000015a6000331a0000b9c25414a40000000b462adcc77030cafb92a400011e42783900dca000012f9754aea00009fd366eba2000007a800000000000002e741f680000000000d72000079694120ff86ca00000000000000000000000014280c38000ad823cc00027c28d68f16000000087f80004e90000000000000000002e6117a00000000002cfa0002e6ac23b74cd0aa59c974800000000000000000ae500000000000a4b2cb000029a0d18800000000004a400000001a1a000000000005f600000001e3346ead083540000000c540000b0f21fa83200009d99ef40aa917000013600ea80000000000000000000000005fc0aacbed31d6000263000
  | 70 => 0xda129691d9fa86581e6ecab1ff458e00000000b8e0000000000000000000000001a38a37939c00014749ff8000000133c188321a9ce00000000b5877039361610bce00000000000000000000000000000000000000245600000000000be000000009438f940002166dac054e1aa1bb6a219f8ea32b4ea33700002f100002581358b96a2e2000000000000000000d6a0000000ad980000001fd20491c7e000377abff98880002e08000000026200000000000000000099780000000000cd3800000000000000000000370200010d603fa7acb1080005b404203530ae2000000000000000000836d3d0000dd12788000185600028421f3800000017a8982800054e812000000000000000000000000000000001f5e0900000000000000009780002ede9dc2aba0000d8c42a2e5c000000006907989bd8536506000000000000a58000b41000000033ea0001f2e0002a140000aa0c5c00000001ebacf9005c0000fa800014540000b301dc0000000000077e80000000ec60000000129ad8a0e58a6a7108a940001f140000000000285c00000000001e340000000000000000000000000000678a57a799af9ea8aab560b18000000097e23382e00002428638abf400b96da7688000c050000000000085929020000000000080c00037b23eb800054fb2682aa15c8dab325c05399ca11a80009ed85906b900000000000000041a00002646199d8c5e0346aba00248e2134ce0000000df280000000218000355e00000000000000000000000000000001df4518b19c45f01820003098000000000030c84ea11d600000000a52e2e00000000bd0000d02000000030c2ba4000000000000000b9aa5d9d2c3ec00008f22c1e7f680000002b0240391840000000000000000019900000000000000060c800000038f22762264000000000000000000000000000065000000000000000367c00000005cb25a47f8940c000000000010880002b6e000141600000000718000000065075e80000000000000000019b95468e400009bb001e227088400000005b9249c51f80005aa2678c33250a00028e0000000000006b4b728000000000000000000000000000332c97880007000a9829b0ed20000f0e0000000af1ab8c01dabbe48594c4c99800040c000000031a0bce80000000000d160e7284cad443119f1e000304c87b91060000000000000000000000000000000327800027506b2a86aace00004b4800000000000000dea000000039d27c0a30b8e60001424000000022d8baa0000000b3d9a3e494b710af0ae56000000000000000002b543139da4767b564aef15c02088196e5030a6a9200000000000000000000016d25908000b1b3848000000000007f27d9a1e000022a05feb28a00008ba000000071033700000000bc70000000284cdde27a400000006fc1e
  | 71 => 0x5980000003768d4b00000000000a66085c92117ac000213a0000000000000062b800000000000003446ab811b600035b0cc380000000000d3c8000000000002100000000000b67b74ea2e000068ab25839707be8481f4c0000000bdb0000000000078486f80001fc200008508ab800075d80007e80dae00000005a3800047f8000000106c64aacf00001e728f5800088621ae61f000000008a200027a027a0000000000097d8000a0ab9045ed29ba8eb80000000aa4000000000036d8169800000026cc0000da2490a18a4d5b9200000000000000000000005551adcd45000000024141fa0000000272a6ef00003de000019785cc0000000000247893b98ca341a5ba70a1b160541614dfaa824e29b6944fab1e64fc20909b18000803afc6a2c396ade3000000009ba000000000000000000000000000064f800000021b80000000000000000017ca00000002560000000019c00000000000000404000000000000000000e3400000000000d010a0cc069b60046a8d6a0a000000009168fb03ac7cb09ee24ea71ccc9000000000000000000bde899c401176a0001f2a5580000b508000d26b92e0000d1e5cd020c4ec0000000000000038760000000951a7f27e280006b40000565919000000005d2109e00000000002fdcd5381a6360b33c0000000000000000000000ea373800000000000000a6e0cf800028200001b5c0000000148800000000000000000000000000000009f280000003438a1380006bd01e06010c5e8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8de87d8d43440018b8ebb1a868800237e0d75d89100146e41aebb122000a6d8510b62440015cb02216c488002ba60042d891004e67312e631220008ef87588624400199ae6b10c4880263b209769491002c7a432e329220018f8865c2524400117f08bb2a48800e2f21176549100046fc1aeca9220028dc835d952440130f90eb2aa48812a9720d65549100247743ec4a9220058f4865c642440031f10cb8484880121fa1676509100043ec2ceca1220008ef825d942440131790eb228488026ab209645091004c77414ed19220058f4865c632440031f10cb8464880023ee01764c9100243f428ec992200087d851d9324400717d083b264880022f610764c91004c6e43ac699220028ec8758932440051e90eb2a628800b351d9434c510005d8c20e098a2000be1821c131440131e90eb2242880163d2197348510005d2c20c490a2000bc58318921440017c3012124288003a95914248510005f0c046490a2000ae4864c92144001763083824288002f460c70485101356c41acb20220268f8865ce404400b5e10c98c8088003745cd3190110006f0b92432022025a3e85d91404400757509b2a808800e3e21d65501105ef1c2a2caa022024ad88359540440ad6750bb2280880067c20773501102b59c42a86a022024e986350d40440033e103b92808800378887725011000755a16c4a0220038f88758940440033e50fb8a80880027c21d315011002d7843262a022000f91434c540440013e10e90a8088003e850921501100156c41acb18220019f0815d23044001bc2e490c60880167521d314c11002d6a432629822005bd0804c530440051f10eb2a60880063e219744c11000cf840ae89822005bd0874c53044003ba10e98a6088016f4a19314c11002de8432629822002ed0864c53044005da6ec98a6088007749d9314c11000ee83b2629822002ed0764c53044001da6ca98a6088003b4595314c110006e9ba2629822000dd1744c530440017a70498a608800374dc9314c110005e8c1a429822000fc132485304400b5c90c90e40880067c205748811004d74412c91022000dd1734c6204400b5e10c90c4088047785c9218811002c7b436e290220059e487485204400b5c90c90a4088016f8201214811000c7c432e890220019f0815d120440131f10eb2240880063e2197348110005e4c18c49022000be1818c92044001ba2e698a4088003f04c9314811002d78432429022001cf0764852044013dc0c490a4088016f821d214811000ef043a429022005be286485204400b7c10c90a4088027b8219214811004f71bb2429022001de2764852044003bc0ec90a4088027b81d92148110006f1ba2429022000de1744852044001dc6c890a4088003b85912148110005f1c1a429022000be1834852044001bc6e690a4088003785cd2148110
  | 1 => 0xae4b0ea2101879c9c161d442000738b82c3a884061e672058751080c3ce440b0ea2101879948161d442031738902c3a88400187d85dd9510800b0f90bbb2a21016a1f61d655442002c3e43acaa8840058f48758551080034e903bb2a2100031ddc776544200243fc0eeca884000c7781dd951080090fb03bb2a21016b1d20776544200063b20eeca884000c7631dd951080014ef02bb2a2100031ddc5765442030c3fc0aeca884000c77815d951080018ec82bb2a2100031d8c5765442000d3b40ac8a884000e36415915108001c6d02b22a2100038d605645442030e1fb8ac8a884000e37715915108001c6c62b22a21016b8e88164544203071c902c8a884001a768158d5108001cac62b1aa21000395a0563544200072ac0ac6a884061c5f7158d5108001caee2b1aa2100039590563544202d727902c6a88405ae4d2058d51080094ed0eb0aa2101871da1d61544202d63ac3ac2a884004a748758551080014ef08b0aa2100029de0d61544202d733902c2a88405ae722058551080b5cca40b0aa2101839c481615442002c5e426eca0840058bc875914108013998e4b1a82100032b593725042000666b1ee4a0840058f48758541080019cee4b0a8210027391c961504200053bc32a2a084000a758654541080018eeeca8a82100031d5d951504201d71b322a2a084000e35645454108125cacc6a8a82100039558d515042002c6e41eec98840058f481dd9310800b1f100bb262100172e1c1644c42002c6e43ac698840058f487585310800b9e0e0b0a62100029de19514c4200053ac32a29884000c777654531080018eaeca8a62102238d991514c4200071ab22a29884039e56635453108001caac6a8a62100032e593704c4200066cb1ee09884000cf161dc1310800b0fd0f2a2cb080162fa1f545921001c7cc06e6b24200587c8759553840071bb07bb287080163ea037650e100043fc2aeca1c200487c855d9438400b1790eb2287080030f1d56450e1002c3e43acaa9420058fa80dd9428400b1790eb228508026ab2096450a1002c7d406ec99420058dc8758d328400b1d90eb1265082fb8e15165502101247cc36e6a04205db388550d40840bfd30c6a1a81080023ee1973482105be2e39ca8b2a20028de87dcd65440018bea3b9aca880031754773595100053ac0cebb22200487f875d764440c30ff02baec88816a1f60575d911002c7c402e7b2220098ee87dc964440018dea3b92c8880031b54772591100043ec2cecaa220008df835d954440051b906bb2a8880023be09765511004c76412ecaa220008ef825d363440131d904ba6c68800237e0d7654d100143e43acaa9a200487e859d943440010fb0b3b286880021fe157650d100243e42aeca1a20008ef825d943440131d904bb2868800a2f21d6450d1033d56412c8a1a2003
  | 2 => 0x85458c2000566c10a8b184000ad68115163080015ab022a2c610016b6a005458c200056cc00a8b184000a5e859c563080014bb0b38ac610016b62017158c200052f428e2b184000a5d851c5630800153d0838ac610002a76107158c2004d67410e2b18400eacd821c5630800b5b50038ac61003ab66007158c2004d67416a2b184000acd82d45630800b5b501a8ac610002b66035158c200052f42c82b184000a5d8590563080011bd0e20ac6100023761c4158c200052f42882b184000a5d85105630801359d0420ac610002b36084158c2002d6d40082b184000ad980105630800b0f90eb2aa6100163721d6354c200243e42eeca18400087f855d943080090f90abb286100021f61b7550c205d61f326eaa1840b7c5e63dd543080018ecc3baa86100021fa1d6550c200043e43acaa1840058bc87591430800187eeab2286100030f1d56450c2002c6e43ac6a184000c5f7558d43080018b8eab1a861016a9d606755842030d3bc0aeab08400487e85dd161080010fb0bba2c2100121fa1773584200043ec2ee6b084009ae682d45610800b5e501a8ac210026b9a0a755842000572c14eab084005af2809d561080015e3013aac21018b99a0a755842000732c14eab084061e72809d56108001ce3013aac21018799c82755842030f39104eab084061e65209d561080c5ce2413aac2100031de1d75584202d733902eab08405ae72205d561080b5cca40baac2101839c48175584200053b42ee8b084000a7585dd161080018eaebba2c2100031d5d5745842004d72412e8b084000a76851d161080014eb0a3a2c210002b5a0c74584200056ac18e8b084009ae6821d1610801b5cb043a2c210016bca00745842006d78c00e8b0840008f68715161080011eb0e2a2c210002b5a0c54584200056ac18a8b084009ae68215161080015cb042a2c210016bca00545842000578c00a8b084000a7685dcd61080014eb0bb9ac2100031d5d773584200063abaae6b084005af0805cd61080014ed0a39ac2100029d61473584200055b420e6b084000ab5841cd61080135cd0439ac210036b9608735842002d79400e6b08400daf1801cd61080011ed0e29ac2100023d61c53584200055b420a6b084000ab58414d61080135cd0429ac210002b9608535842002d79400a6b084000af18014d610800b5e501a1ac210002bc603435842004d7341486b084000ae58290d61080014ef0aa1ac2100029d215435842030e3b40aeda884000c75815db51080c5c5ce4b26a2100038b5c964d44202d61eb8ac9a884061e3a705935108001c72e0b26a2101878e88164d44203171c902c9a884062e4e7258f5108001c9ae4b1ea21016b175c563d442030f2d382c7a884000e597058f51080c3c9e40b1ea2101879348163d442030d3bc3ac3a884062e66725875108001cc
  | 3 => 0x6a024024e986350d4048001793063928090002f8604725012002cdc43a84a024009cb8765094048013b50e4a1280900273a1da3250120004f443a64a024005ae8864c940480139d0ec9928090003e250d32501203163c3b6a2a024060c78765454048001ce6c2a8a8090003cc5454150120007d0a0a42a0240059cc874c9304800b5990c9926090016f2201324c12002c3f43ca8b28400587e8794d65080030f90bb8aca1000297a0c74594200052ec18e8b284009a6e821d165080214db043a2ca100029da0474594200053ac08e8b284005a7a801d165080214f3003a2ca100028fa1073594200051ec20e6b284009a6e821cd65080214db0439aca100029da0473594200053ac08e6b284005a7a801cd65080214f30039aca100169ea0343594200053cc0686b284009a6e8290d65080014db0521aca100021fa1e41594200043ec3c82b28400087e8710565080010fb0e20aca1000297a0c41594200052ec1882b284009a6e8210565080014db0420aca100169ea0041594200053cc0082b28400087e878c565080010fb0f18aca100021fa1c31594200043ec3862b284000a3e840c5650800147b0818aca100269ba08315942000536c1062b284005a7a800c565080014f30018aca100162fa1f545902002c5f43c86b204009aae8290d640800147d0b20ac8100028f61641590200054f418eab204000a9d831d5640801355d043aac81003eab60875590200055b408eab204000ab5811d5640800b575003aac81003eae600755902002d5d406e6b20400fab980dcd640801355d0539ac810002ab60a73590200051fc2ae6b204000a3c855cd640800117d0e29ac8100022f61c535902004d57410a6b204000aad8214d640800156d0229ac810002ad604535902002d5d400a6b204000ab98014d640800147d0b38ac8100028f616715902004d56412e2b204000a3e851c5640800147b0a38ac810002a7a0c71590200054ec18e2b204009aae821c5640801f55b0438ac810016aea00715902007d5cc00e2b204009aae82d45640800155b05a8ac810016aea0351590200055cc06a2b204000a3e858c5640800147b0b18ac8100022fa1c31590200045ec3862b204000a3e850c5640800147b0a18ac810026aba08315902000556c1062b204005aba800c564080015730018ac8100161f21d655502002c5e43ac8aa040028ed82dd1630800b1bd0fa9ac61001637a1f4358c2002d6d40686b184000a5e858c563080014bb0b18ac610002a7a107558c200054ec20eab184009ace821d5630801d59b043aac610002b5a047558c200056ac08eab184005ada801d5630801d5b3003aac610026b3a0b7458c2007566c16e8b184005ada809d163080015b3013a2c61000297e157458c200052e42ae8b1840008de8715163080011bb0e2a2c610026b3a0
  | 4 => 0x4c0059b0ec992a098003d254932541300263c3b2a2a826000d7371545504c001ea2a298aa0981b7a60c3645013004c3f43ca6b2e400987c8759554c80131bd0fa9ac79000a2f6137650f200043fc2aeca1e400487c855d943c80131b90eb1a8790003171d56350f206072629aca9964066b4c8550d32c80cfd18c8a1a65900121fa1773587200043ec2ee6b0e400187d85dd951c800117f08bb2a39000e2f211765472000c3e43acaa8e4000a3f845d951c807547908bb2a3900029de05765472000c5e43ac8a0e40098f48758541c8075c6cc8a8a83900038d591515072002c77416ec98e40018dc8758d31c8073cacc6a8a63900039558d514c720007a2992a298e4000dc932dc131c800b3d100b9a4390006b9205634872000752b228290e4009cac7259140c800b3990e99261900161fa1e545962002c5f43ea8b24400587c8759553880071bb07bb287100021fe157650e200243e42aeca1c40058bc875914388001878eab2287100121fa1774586200043ec2ee8b0c400187d85dd951880011bf06bb2a31000a3720d765462002c3e43acaa8c4000a5f835d951880734b906bb2a3100029de05765462002c7d406eca0c40058bc875914188075c6cc8a8a83100038d591515062002c6e43ac698c40058f4875853188073cacc6a8a63100039558d514c6205ff1c2a2caa044065b388550d40880bfd30c6a1a81100166e21d425022004ed439284a044000bab825054088001e62a2a0a81100263b20974d8d200243f42ceca1a400087d859d943480010ff0abb286900121f2157650d200047bc0aeca1a40018f4815d9434800517d0fb22869000e37a1f6350d200156741eca99240028ec875953248005998eca1a6490192d3215434c9201f746322869924000ba9841c132480017c30238264901869b21932d452000c3f43ecaa8a400187c8759551480034e902b2aa2900123da1f61545200053ac0ceca8a4000a3f845d9514807547908bb2a29000297e0d76545201cd2e41aeca8a4000a77815d951480034e903b22a2900029de05645452000d3a40ac8a8a4001a7481d8d51480014ef02b1aa2900069d20563545202d53643264a8a4001a7686d8551480094ed0fb0aa2900129d21f61545200053ac26c2a8a4000a7583d855148001ccc65b0aa290003994cb615452000c5e43ac8a0a4000c767654541480018e8eca8a82900eb8d99151505200071ab22a2a0a40018dc8758d31480018ececa8a62900031d1d9514c5201cf2b31aa298a4000e55635453148001e8a64a8a62900023be1d64c852000c7643ac890a40058ec865cd21480031d90eb1a4290006b9205634852000752b228290a4000ba9841c1214800b5d10c99480900039cd855190120006f0b8a432024003aba84d9540480071f10eb2a809000f2e1d9435012031d9c42a8
  | 5 => 0x3cc547705054000798a88e0a0a80058bc865d1315004b2790aba262a017f661c1434c5400069aba2a298a8039e56635453150001e2a86a8a62a01cfd4cc1514c54001c7d436e098a80018ee829db2150013958eca1642a00263e21970c85400243f428ec90a800087d851d921500051bd063b242a00023760c764854002c5e432e890a8000cac7650921500491f30fb1ca0a00026ee1d439414012d9c42a87282805fd987350e505000737508b94a0a00026ee1d429414001cdd422e3282803ad3a745465050001ae2e2a8ca0a00026ee1d419414000798a8a83282802bb3a85dd1505000b2f10ea9aa0a00aece2115354140004dc43a86a828025b388550d5050049b30e6a1aa0a0003c654d435414015d9c422a4a828025b38855095050001e52a4a12a0a02fb4e15371541400263c3b2a2a82802bb38845455050001ae6e2a8aa0a0096ce215415414000798a8a82a82800587e87951658c0014bb072a2cb180162fa1f54592305d62fbb6eaa1c60b6c5f761d5438c0016ab023aa8718003879516550e301256cc36e0a1c6003c9c7450d628c00193aeca1c8518026ab2096450a300243f42ee8b0c600087d85dd1618c0794bf0ca1ea3180061f617765463002c7d406eca8c600587c87595518c0b54f501bb2a3180029de057654630004ae43a86a8c603aa5f8650d518c0014ef02b12a3180069d20562546301cdac41ae0a8c6000d5b735c1518c0011df04bb283180263b209765063002c5e43ac8a0c6003a9f8650d418c075c6cc8a8a83180038d59151506300078aa1aa2a0c60058ec87589218c183c70a8b22a1181bfc69514354230005adc1aa2a846000d7371545508c00187ae92a6ca980121fa1f75591300043ec0eeab22600087f855d9544c0011df0eb10c4980263720e769493001c5f424eca9260008bd849d9524c01359d05b2264980263721d644c9301fd2e42ac89926000ace86949324c07fc98caa926498002d6614704c930005e8c08e0992600087f855d3614c0090f90aba6c2980021fe1d64d45300243e43ac9a8a600187e87d95514c0030f90eb2aa2980029d60676545300053bc0aeca8a600087f87591514c0010f90eb22a2980e69e219705453000c5e43ac8a0a603ae3664545414c001c6ac8a8a82980063721d644c5300072bc32a298a6000e5486545314c003caeeca8a6298007951d9514c5300072bb22a298a6000e5564545314c001caec4a8a6298003d4a01514c530007a8c02a298a6058e5760545314c073ea6c0a8a6298003d4547704c530005acc28e098a6000f51511c1314c0031dd053b642980121fa1776485300043ec2eec90a60058dc865cd214c0094f10ab24a0980035c5c55194130006e8b8a632826000f51514c6504c0094f50bb22a0980123e21d64541300263c3b2a4a8260009d8874c95
  | 6 => 0x43ec2ee4b0c8061c7a105db51900018f220bb6a3201869e20163d464000c3ec2eeca8c800587c85dd9519000b1f501bb2a3200161f21d65546402d53d406eca8c800487f81dd951900090fb03bb2a3200031d90776546400063aa0eeca8c8000c7631dd951900b58f501bb2a32016b0fd0376546402d61ea06eca8c805ac7a10dd951900018f221bb2a3200029de0576546400063bc0aeca8c8000c76415d951900018ea82bb2a3200031d8c576546402d53c402c6a8c8000a778158951900034e902b12a3200031edd970546403d5ac41ae0a8c80058f8805d9319000b1b90eb1a63200163d21d614c64002e78382c298c8000a778654531900014eb0ca8a63200e79598d514c6400072ab1aa298c807af5330545319000b1f501bb243200163b21d62486401347c43ac6a848004a7a8558d509000b2f10ea9aa1200029ee1953542400053dc32a4a848000a7b865455090001ae6e2a8aa1200028f61253d95400145e422e5b1a80038fa86dc1535016d27d0fbaa86a02df0f1db7550d4062f8c186eaa1a80b5c3c761d5435000166b023aa86a0313c60c07550d4012e1e3aecaa1a8000e1e53d9543500051790eb2a86a000e6721d5350d402fdcc402a6a1a8000d3875dc14350001a70ea38286a017ee620c7050d400043fc2ae7b12800487c855cf625000155b0810ec4a0002b360c21d894000574c0043b1280008ef8758862500139ccc4b88c4a000339589711894004c7c432e1292800987c87595525015f958c5b9a84a00166ea03735094004d57436c4a128000b2d85189425000174b0231284a000e6b21d525094000556432a4a1280098ec825da3250013958c4ba464a00263e219708c94004e74312e119280058bc865d1325004b2790aba264a019f2b189744c9400064e3b28699280c3b1c8550d32500cfd18c4a1a64a017f661c1434c9400147743ec499280038fa86dc132500010ff0ab9ec2a00121f21573d85401e53cc06c7a8a802593c8750f51500c34790ca1ea2a01d3c60c143d45403171631285a8a800187e87d9551500b547b09b2aa2a00061f21d65545400053ac0ceca8a8000a5f835d951500734b906bb2a2a00029be09765454030536412eca8a8000a77815d951500b547d0dba2a2a00ea9e60363545400049e43a86a8a805aa3c8650d51500e7e3060a1aa2a01838b18942545401d59d424e0a8a803aa78865c15150001a70e8b82a2a01ced620d705454002cdd406e6a0a8003ab980d8d4150001d4c43b1282a000e6d21d515054012e9bc3aa2a0a803ad34875454150001c6f0ca8a82a00038d219515054000f1bbb2a2a0a8001e34765454150001a6ee6a8a82a00038dd8d51505400071bb12a2a0a8000f32805454150001e6300a8a82a01678dd8151505401d799b02a2a0a80c2f33305454150185e6060a8a82a
  | 7 => 0x9d83085649400b5750010ac928002ae600215925001c5f426e4b1ca0008bd84dc963940071bb07bb287280163ea037650e505d61f326eaa1ca0058bc87591439400187eeab2287280970f1d56450e5004d56412c8a14a000c3e645d6329404b87ceab2465280030f5d5648ca5000636baac5194a0058ec8758932940c34ef02baac3280038d90564546500071b40ac8a8ca000e358159151940c387ee2b22a3280978ddc564546500071b18ac8a8ca000a778458551940014ef06b0aa32816b9c1c161546502d739202c2a8ca05ae72305855194001ce2c3b82a3280162f213765065002c5e43ac8a0ca000c75765454194075c6cc8a8a83280038d591515065002c6e43ac698ca0058f48758531940034ef0ca8a63280031d5d9514c6504471b322a298ca000e35645453194073cacc6a8a63280039558d514c65002c7c402ec90ca0058ec8758921940090f90a3b286a80030f9507650d505be2e31eeaa1aa0038de87d8d43540092b90ea9a86a800a972195350d5000477c3ac4312a0028de83dd942540011bb07bb284a80125b21d525095004c3e42ced192a0098ee829da32540018dceca9464a80161f219754c9502572631aa4992a00187c855d361540030f90ab9ec2a81861f21d53d855000c3e42ae5b0aa039c5c63dcd5154001cac63b1aa2a80069d21f61545500053ac26c2a8aa000a7583d8551540034f50db82a2a80039cd87705455000739b08e0a8aa0049748754541540018ececa8a82a80161f219754c5500063b3b2a298aa00587c865d5215405727908baa42a80123ea1b704855002d3c402e6b2c802ba3e841cd659000147b0839acb200029ba08735964000536c10e6b2c8000a76811cd65900014eb0239acb200169ea0073596401453cc00e6b2c8000a5e839c965900014bb07392cb200169ea02725964015d1f42664b2c8000a3d84cc9659000b4f500192cb200029e600325964002d3d404e2b2c8000a79809c565900010fd0f18acb200021f61e31596400043f43862b2c800087d870c5659005747d0818acb200028f61031596400053741062b2c8000a6d820c5659000b4f50018acb200029e60031596400043f43c42b2c800087d8788565900010fd0e10acb200021f61c215964015d1f42042b2c8000a3d8408565900014bd0610acb200029760c215964002d3d40042b2c8000a7980085659000b1f100bb2a7200161f21d6554e400063cb2ee0a9c800487e85dcd62900010fb0bb9ac520003179cd6594a401fe2f32ae72948000c5d655ce52900018f2cab84a5200163ea037654a400243f42aed194800087f865d632900010ff0eb2c65200021f61d658ca4002c7c402ec99480058ec87589329000b9d0e0b12652016a9d606755864030d3bc0aeab0c800487e85dcd61900010fb0bb9ac3200121fa1772586400
  | 8 => 0xa6b2a65908fa3b61b744cb2142da642a869964267e8c6450d32c840717d0fba2ca908030fd4774595210061ea8ee8b2a42bac3c7494d654840187aebaa6c8908023ee0173d912102c7c402e7b2242008bf845d954484070f90eb2aa8908029d60675d8d210243fc3aebb1a426287f815d763484c10fb02baec6908031ed477058d210063ca8ee0b1a420087d859d9534840117f08bb2a69080e2f2117654d210047dc02eca9a42058f8805d953484090fd0b3b286908021f6167650d210043fc2aeca1a420487c855d943484011f700bb286908163e2017650d210145f43ec8a1a4200c3c75d9143484071b90eb1a869097eb62016350d2101d56422cb21242019e4815ce42484071d90eb2a8490906ab211658c92120c76432e9192423fa5e85d8d324840559d07b2a649080a3b21d654c9211f556422ca99242c6e4c5359532484033c903ba264908063b219744c92100cf240ae8992427fb4e85d8d32484ff6990aa1a64908fba3191434c92100cf343ee299242019e481dc13248401bc621b82649080e3d21d655052101e5a3b286a0a4200bc5831c941484017c30039282908066d21d425052104e5a3b284a0a4209da47250941484037490ea1282908276921d425052100dd343284a0a4201ba4865094148407d490ca12829080fa9dd9425052104ed33b284a0a4209da4765094148407d48eca128290803a9d95425052100752b2a84a0a4200ba783509414840174f00a128290827391da3250521005d2c2464a0a42009e4874c941484139c8ec9928290802e96113250521007c2a1a64a0a4200da542dc1414840117f08baec09080e2f21175d81210076499661b024200a79850c360484015d304186c090802bc60430d812102e5d302e830242008fb875806048401972e8b00c090802aba0a435925000556c1486b24a000a3d85905649400b57501b9ac9280baae603735925000557414e6b24a000aad829cd649400b5750139ac928002ae60273592500051fc2ae6b24a02ea3e851c9649400147b0a392c928002a7a0c72592500054ec18e4b24a000cad721c9649400156d02392c928002ad604725925002d5d400e4b24a02eab9801c9649400117d0f992c9280022f61f325925002d5d40064b24a000ab9800c9649404b47d0b38ac9280028f61671592501751f428e2b24a000a3d851c5649400153d0638ac928002a760c715925000557410e2b24a000aad821c5649400b5750038ac9280baae600715925012d1f42c62b24a000a3d858c5649400117d0e18ac9280022f61c315925012d1f42862b24a000a3d850c5649400155d0418ac928002ab608315925002d5d40062b24a000ab9800c5649404b47d0b10ac9280028f61621592500045f43842b24a0008bd87085649404b47d0a10ac9280028f61421592500054f41842b24a000a
  | 9 => 0x43545311cdab41ca4a8a6200b5583949514c4098e8eca92a29880b351d93254531007a329264a8a6200f45524c9514c4736a907ba2a2988029de1974545311cd3a432e8a8a6200b57835d1514c4736a906ba2a298b278d99364545316653b43ec8a8a62a2a7487d91514c49f4eb09b22a2988069de0f645453100d3ac1ec8a8a62cbe3743d91514c597c6a87b22a298b2f95ccb6454531004bbc3ac8a8a623697487591514c5176af06b22a2988031de1d64545310253b43ac8a8a6204a7487591514c4018e90eb22a2988121d21d64545314653bc22c8a8a6200e3784591514c5174ef06b22a29880395e0d64545316572b992c8a8a62c9e3740591514c5436ad0fb9aa2988e755a1f735453100dab436e6a8a6201b5486dcd514c473aacedb9aa2988e7551db7354531005aac26e6a8a6200b5582dcd514c4016ab01b9aa29880355e1d4354531005ab43a86a8a6200b548750d514c401aa90ea1aa298806d5a19435453100daa43286a8a628cb578450d514c473e2f08a1aa298a23c59d143545310078aba286a8a6200f176450d514c511e28c8a1aa298802d5e0943545314478a21286a8a6200b578050d514c511e2e80a1aa298a7f1d1db72545311cdaa41ee4a8a6239a76869c9514c4014eb0d392a2988e6d5a0e7254531005aac1ce4a8a6200a77865c9514c4734e90cb92a2988c71d1d972545310059bc22e4a8a6288b34845c9514c4016af06b92a2988e6d520d72545311cdab418e4a8a6200b55831c9514c46d2ed0f312a2988025d61e62545311edaac1cc4a8a6240b5783589514c4016e700b12a298802dc201625453100732b10c4a8a6239b5683909514c4016ab07212a298803c550e42545311cdab41a84a8a6200b56874c9514c4016a90e992a298806d5a19325453100daa43264a8a623fe57764c9514c473ca8ec992a298802d5e113254531005aac2264a8a6200e57644c9514c401caac8992a298a0ad5e0932545311cfa3c1264a8a6200f46724c9514c401e8ae4992a298803d1d893254531007a231264a8a62c8f47424c9514c591e8884992a298802d5e0132545311cdaa41ee0a8a6200d5773dc1514c4734ed0d382a298a22cda1270545310059ac24e0a8a6239b56839c1514c4016ab07382a2988e69d2197054531005abc1ae0a8a6239b54835c1514c401aaee6b82a2988e6d5a0c7054531005aac18e0a8a620087f855d3604c4090f90aba6c098877555cd5198131106abb9aa2b02620097787544604c4732eb0ea88c098a234d9d151181310069aba2a23026200d6672544604c401acae4a88c0988023ee1d601813100738a8ac0302620987e8794d65c84130f90eb2aa99082637a1f5358f210145ec26eca1e42018ee82dd943c84010ff0abb287908121f2157650f2104c6e43ac6a1e4200c5c7558d43c858fc98
  | 10 => 0xa8a8200b55839495150401e4ca4a12a2a0803c9549425454151d9b43ee8a8a823ad3687dd1515040366d0dba2a2a0806cd21b74545411d69b3b6e8a8a823ad3476dd1515040166b07ba2a2a0802cd60b74545410059ac06e8a8a823ab3484dcd51504014ef0cb9aa2a08ea9d21973545410059bc22e6a8a823ab34845cd515059d4ed0fb1aa2a0a829d21f635454100d3ac26c6a8a82cae5643d8d515059bcaa87b1aa2a0b378dd036354541004bbc3ac6a8a82389748758d515051966f08b1aa2a08034de1d43545410059b43a86a8a8200b348750d5150401a690ea1aa2a0806cda19435454100d9a43286a8a828bb378350d5150475e2f06a1aa2a0a4bc59cd43545410078ab9a86a8a8200f176350d5150525e28c6a1aa2a0802cde0943545414978b99286a8a8200b378050d5150525e2860a1aa2a08eacd21372545410069bba6e4a8a823aa76869c951504014eb0d392a2a08eacda1272545410059ac24e4a8a8292b56839c951504016ab07392a2a08029de1972545411d53a432e4a8a8200b37845c9515047566908b92a2a08034ddd172545411d59b420e4a8a8200b35841c9515048766b09312a2a091acde116254541004bb438c4a8a823a9758718951505256ad06312a2a0802d560c625454100732b10c4a8a8200b728018951504016e300312a2a0802cda1d42545410059a43a84a8a8201b368650951504036690ca12a2a0802cde0d425454141d9bc1284a8a823af27825095150401e4ce4a12a2a0803c95c9425454100793b1284a8a8200f2462509515040166f00a12a2a08025da1e3254541004bac3c64a8a823ab36848c9515040166b09192a2a0a73c9d0a32545411d59b42264a8a8200b35844c95150401e2a86992a2a0a6fc9d0932545413e63a3b6e0a8a823ab3484dc151504754ed0d382a2a08eacda1270545410059ac24e0a8a823aa74865c151504118e8ecb82a2a0802cde1170545411d59a422e0a8a8200b57835c151505256a906b82a2a08eacda1070545410059ac20e0a8a8202c9e7350f60504712ef0ea8cc0a088f4d5d1519814113e9bba2a2b028200d67725456050401ac8e4a8ac0a08023ee1d601814100738a8ac03028200c3d74953654c4014bb072a6ca9880a3720d70d91310243f43eeab22620087f81dd5644c4010fb03baac8988021fe1576551315d62e3b6eaa1a62b6c5c761d5434c4016ab023aa8698803879536550d3101c6e43acaa1a6203c9e7450f624c4011df0eb10c4988063721973949310047dc02ed21262058f8805da424c4031b90cb9c849880a67e1d4390931014e6c16e899262018dc865d1324c41359d05b2264988263721d644c9311fd2e42ac89926200ace86949324c47fc98caa92649880374c43704c9310253b42ec8a8a62048f487591514c511e2ca8a1aa298803c5551
  | 11 => 0x544c1ac8c4b8cc4a8983599097198951306b3192e3312a23a93e87dd16254401a6f03ba2c4a88034d20774589510069bb0ee8b12a200d3631dd16254475878e9b22c4a89821f21d64589510061e3a4c6b12a200a3d8418d6254401878e831ac4a89829ba0863589510053cc00c6b12a200d3774dc56254401a68e9b8ac4a88025d6137158951004bac1ee2b12a200d6762dc562544012df0eb10c4a8802d9e056218951064bbc0ae0312a26096e829da42544012ef02bb484a88030f5db64909511cc9fc3a87212a200a3c8650e425447565908b1484a88038bd916290951005b3c0ac5212a200977815c242544032e902b8484a88025d6077650951004bbc0aeca12a200b658198942544752d90eb1284a8802d9e056250951304b7414ed192a260c6e829da32544c18be653b464a8983174ca768c9510243fc0ced192a20487d819da32544018ec833b464a88031d8c6768c9510063a98ced192a260c6f219da32544018da433b464a88025de05768c9510063bc0aed192a200c76415da32544018ec62bb464a89825b209748c951006373b2c5192a29cb2c8458a32544016cf02b1464a88025de05708c95100cba40ae1192a20097581dd9325440127f08bb264a88ea4f211764c951004bbc0aec992a20097b805d932544b52f100bb264a88e65b60b744c9510043fc32e8992a20087c865d132544c12bd0fb1a64a89825721d434c9510052e43286992a29bf0c4250d325447369d0731264a8802d9606624c9511ccb643ac4992a29bb2c845893254401c98c6b1264a8802d9e05624c9512d43ec38c9b02a200a5d8319360544014db04326c0a896a9ea0064d81512d43ec3ec7b02a25a87d87d8b605440147908b16c0a88034da0574981510069ac0ae9302a261c3f615d26054401a6ec2ba4c0a88034d8c5749815100cba40ee8b02a200c5c7399160544014bb06322c0a8803171cc645815100536c10c8b02a25aa7a8019160544032e903b9ac0a88e657a1f7358151006abc0ee6b02a200d5481dcd6054401aaec3b9ac0a88035590773581511ce2e39ec6b02a25a87c8758d60544018b8e7b12c0a88028f21162581510062e39ac4b02a200d5773dc56054401aa8e7b8ac0a88d25de057218151004bdc3ac0302a200a3d8494f655056f878edbaa86a0ad70f1d87550d410059ac08eaa1a8200e1e53d9543504051790eb2a86a08021fe1573d89410243e42ae7b1282008ef8758862504031790cba4a4a08263d219719494104c3e43acaa928200b2d85189425040174b0329284a08263b209768c94100c5e432e919282098f4865c632504139c8c4b8c64a08062f219744c94133f463128699282028ee87d8932504094ed0bb1aa2a0a4bc594d43545410078aa9a86a8a820197687949515047566d09292a2a0802cd6125254541495ab41ca4
  | 12 => 0x803174c77650f511dc9fc3a87216a262c6f215da32d44018da42bb465a898a5b209748cb511dcb6c16e8996a20087f865d132d44090f90cba265a898a5721d434cb511fd2e43286996a2a6f0c4250d32d44011bf06b86c8a880a3720d70d91510045fc22e5b1aa2038bc845cb635440187ca83b286a88031794c7650d5104c77410eca1aa2008ed821d9435440b1f5003b286a88023e6007650d5100c3f436eaa1aa20197681dd543544030f90cbaa86a88124f21d5450d51024ae43aa6a1aa2008ef875886254401aac62b9ca4a880355a057394951006aac0ae7292a262c5f615ce525447faaec2b9ca4a88035590573949510069b20ee8a92a23ac3c74d9152544030fb0b3b484a88263ba0a769095100c3e432eb212a200c3d75d924254401c5ec8a9484a88061fa1b755095100c3e432eaa12a20496c8754942544030fb0b3b464a88263ba0a768c95100c3e432eb192a200c6e7654a32544030fd0dbaa64a89825760f754c95100c3e432ea992a239b4e8394932544092d90ea9264a892b9318d524c9510047dc3ac0302a2a4977815cf64544032e902b9ec8a88d25de0572d915100cba40ae5b22a20095f835c364544732b906b86c8a88325de0570d915100cba40ae1b22a20497784dc564544092eb09b8ac8a88034dd9371591516869a326e2b22a20097583dc564545a1a6e87b8ac8a8a965de0574d8d5100cba40ae9b1aa20093f845cb635447527908b96c6a88d25de0572d8d5100cba40ae5b1aa20c977815c363544032e902b86c6a88025d6137158d51024bbc1ee2b1aa20497583dc56354401aaec7b8ac6a8b3f5518f7158d5167eab21ee2b1aa20097581dd943544018ece3bb286a88031d6077650d510063b20eeca1aa200c7631dd943544010fd0d3b286a88025de057650d51304b7410eca1aa20096d821d943544b52f5003b286a88025e6007650d510061f420eca1aa200c3d841d943544018bd063b286a88031760c7650d5100637410eca1aa200c6d821d94354401878843b286a880317cc87650d510243fc08eca1aa200c76811d943544090fb023b286a88031d6047650d510061fa08eca1aa200c76411d9435440187a823b286a88031d5047650d510062f988eca1aa200c76311d943544018ba623b286a88031d4c47650d510063d400eca1aa200c79801d9435440187e803b286a8803170c07650d511cc9e43ac8a1aa200b378159143544752b90eb1a86a8802d5e056350d5100cbb40ee4a1aa20097581dc943544a14e90cb8a86a88031d1d97150d5100cbb40ee0a1aa20097581dc143544c10fb0fb26c4a89821f61c63d89510051ec20c7b12a200a798018f6254401aad02b9cc4a88035560573989513162fb0ae7312a200d57615ce6254401aac82b9cc4a88025de117198951004bbc1ae3312a200d67625c662
  | 13 => 0x54ec2020b1ca409ace82041639480159b04082c72900a2f6137650e5204c77416eca1ca4b7c5e63dd543948131b90eb1a87290ff171d56350e523153bc0aeab0ca400a3d8590764548018bca63b286a92eb0f1937550d520145f43ec8a1aa40493c8755143548074790caa286a918a1f21d54d855200c3e42ae1b0aa4008fb87580605480147b0929acb212df0fddb7550e425ae1fbb0eaa1c8400b35811d54390801c3ca6b2a87210faab61b7250e4200697baee4a1c84d3e4c5358d5290963e1ca6a1aa5210121fa1773586420043ec2ee6b0c8402c9c7350d60908094dd0bb1aa4a10021fe1573d85420243e42ae7b0a84008fb8758060508130fd0f2a2cb190269b20974596322552f418e8b2c6400a5d831d1658c8134dd043a2cb1910a9b60874596320053b408e8b2c6400a75811d1658c8014f5003a2cb190029e600745963204d37414e2b2c6400a6d829c5658c8010fd0f20acb190021f61e41596320043f43882b2c640087d87105658c8954bd0620acb190029760c415963204d3741082b2c6400a6d82105658c8014f50020acb190029e60041596320051f424e0b2c6400a3d849c1658c8134dd05382cb1912a97a0f40596320052ec1e80b2c6409a6e82101658c8014db04202cb190021fa1f10596320043ec3e20b2c640087e87041658c8010fb0e082cb190028fa1010596320051ec2020b2c644aa5e83041658c8014bb06082cb190269ba08105963200536c1020b2c64098ec825d9548c8130f90eb2aa9190031b597725523220c7643ac8a946404a6e85591528c8132d90eaa2a5190029be195454a323053ac0ceab0c6462a77815d5618c8090fd0bba2c3190021f61774586320243f42ee0b0c640087d85dc1618c8090fd0bba2c1190021f61774582320061eba4a9b2a6400a5d83953654c8090fd0fbaac8990021f60775591320043fc2aecaa264098de86dcd544c8051dd0db92a8992d657a1f7550d325d62e3b6eaa1a64d2f0c42dd5434c96d8b8ec3aa8699347c31087550d32005aac08eaa1a643fc5c75d95434c801c3ca9b2a869900e3721d6550d32014ce43aa8a1a6467b8c82551434c801a98ebb928699003531d47250d3233dc6420e4a1a643e8ed87d92524c8094d90ab24a49900273e1d43949321fda642a872926467d8c7450e524c80539d06b8ca49900a73a0d70949320247643ac8a92640996c87551524c89569906aa2a49912ad3a177354932004e643a86a92643fb4c8550d524c87db18e8a1aa499003c3551435493263ea629ee2a9264afd8c42dcd424c8010ff0aba6c2990121f21574d85320043fc2ae9b02640487c855d3604c80157308086c099002b660c10d813200574c1021b026405cf2605c4604c8011f70eb00c0990033c5c560181320061fa0eeca1ea200c3d41dd943d44018be63bb287a8
  | 14 => 0xd84dcb6550d754bb06396caa18031ddc671d95435d51f420e3b2a86b7a3d841c76550d6f4bd0638ecaa1aea9760c71d954300537410e3b2a8600a6d821c76550c014f50038ecaa18029e60071d95430043f43c43b2a860087d878876550c010fd0e10ecaa18021f61c21d95435d51f42043b2a8600a3d840876550d6f4bd0610ecaa18029760c21d95430053d40043b2a8600a79800876550d754bb07b86caa1ade8f61070d95430043f43e21b2a860087d87c436550c010fd0e086caa18021f61c10d95435d51f42021b2a8600a3d840436550d6f4bd06086caa18029760c10d95430053741021b2a8600a6d820436550c01a6e82b88caa180355cc571195430063b432e232a8600d36845c46550c01a6b08b88caa1af31dd917119543006ab41ae232a8600d55835c46550d778eec6b88caa180355d0d71195430069b21ae232a8600d34435c46550c01aa886b88caa18034d1097119543006ab992e232a8600d37405c46550c01aa860b88caa18031d5c6611954300537410c232a8600a6d821846550c018eae2308caa18029ea0061195430053cc00c232a86b7c3c76d955450c0533d07b82a8a1aeb171db6554d4301ccf426e4a9a8600a75811976250da38bae632cc4a18029d60465989430043f43ecab1286d2e2c42d956250c010fd0e32ac4a18029d60465589435ae2f398ca3128600a75811946250c011df0eb10c4a18029d60775d85430053ac08ebb0a860087f855cb6150c090f90ab96c2a18021fe1570d85430243e42ae1b0a860087e87d956150c010fd0e32ac2a18029d60465d81436261eba0cb3028600a75811966050d6f0f90dbaac0a18021fa1f65581430043f438cab028600a75811956050d6d87ce8328c0a18029d60465181430047dc3ac030286028de83dc164948011bb07b82c929002b6a034358e520056cc0686b1ca400a5d858c5639481359d05ba2c729136b360b7458e5204d67414e8b1ca400acd829d163948015b5013a2c729002b66027458e520052fc2ae8b1ca43fa5e859c563948014bb0b38ac72913697a147158e520052ec28e2b1ca400a9e841c5639480153b0838ac729026b3a087158e5226d66c10e2b1ca400ada801c563948015b30038ac7290fe97a164158e520052ec2c82b1ca4008de8710563948011bb0e20ac7290fe97a144158e520052ec2882b1ca409ace82105639480159b0420ac729002b6a004158e520056cc0082b1ca44da5e851c163948014bb0a382c729002a7a107058e520054ec20e0b1ca409ace821c1639489b59b04382c729002b5a047058e520056ac08e0b1ca4008de87d0163948011bb0fa02c729026b3a084058e5200566c1080b1ca43fa5e85c4163948014bb0b882c72900237a1c1058e520046ec3820b1ca43fa5e8504163948014bb0a082c729002a7a101058e5200
  | 15 => 0x1c05001000003001000401007802c03804800c00402803800c02c04804400001000000400400c0d000001000402400403000000002002001400806000002801c00402400800404005000001c00400c00000c00000401001000c0b401800001403400800000400c01800c00000000006400400804800003c00400800008000000002c00000000c01c00001c02400000803000800000401c0040000840000500340bc0000080040000bc06405000400000400000c00000002408c01c0300140000080000380b800000000002004400001801000000801401002003000400400000c01000400c00405802c02000000800000000000400000c07805000000410c0c400001800800006001402004400802000c00c00005000c03c00403400000000000000801000400401000c00800400400801406c02401000805401800409000800000402001c00c00c01800007401807000001001c03000000004c00c00400c0380c000c01c00801401008006400001400c03c00803800002801c0040280080000140000100240b800400c06c00004800000800800000c00c00800801800401803002802000400007800402800c00000c00000000800800400c07c0300200e000c09c00400804800801c01400c0c802c0000200080a809800408c02400802801401800400401000002801000401800000003c00400400400c02800401401000401000004002c00001000000400001400001c00402800000c0040c800802c04001000401802000800800000004400002802400c02803c00403c0000000d800c00400406001800405400000400000801004c02c02000000801000001400401c01400400000c01c02400400000001000800400000400c01800000400400000002000000001000403c0a000c02c00800c02001400801000400801c00400000403c01001802c05402401800007000000401001400004800c00000400001400000003c0580ac00400801408006000001008c01402400003c00401001400402001c01402000001002409001800400004400000400004800002400000001400800000408000001809c00003800800800c07000400403800400000009800002808400000000401401000001800000c00400000c00c01800801001401c01c00800002c00000000000400c03802800000803004c00c00c024021750ff0ab9ec4aa02733189739895400666b9ec5312a8008ef8758862551750ff0ab9ec2aa35f1e5d760981546b65cba6c1302a8008fb8758060551ab8daebb14c4a9b53335cf629895300477c3ac4312a6b787f855d36154d6f0ff0aba6c0a98172e18174981530065cba6c1302a6008fb875806054c0147b0928ecaa19421f61c61d954300537410c3b2a8600a6d821876550c018eae230ecaa18029ea0061d95430053cc00c3b2a86b7a3
  | 16 => 0x6274e07580000000dc2c60028a807b513f8da40000bc19a80002540003ef15b80003b30001bfc8b01bc28d9ac43a65cb01f88acb86345034202c9860001689f9470077d3680000000000309044800029b368863c00047100000006be24a2d111dc0003e030a80bc0001b32cf0d010200493640e40c464c435f194423a05620f93c83840e41b30d58df401e0c19c2c10067f3670c44c5c7dd3ac818c000206000000100a0000d7106091619d2d20c880be49e0f18d440007482969460a5617e143a0190061ea2269408000328406873c0001780618c310342b13d102a05f00000001b7800000034c90f885e0000b798f000068b0000344fe477c00011ac97017b2f88398848542000000000000009f800093a0000000a485700061c484d02ba5d60390000c0e00010b173837652213e8a24aa674327a0000aa821430c80f8d301472fc9bf83ca0000f915f098e59500017541e20000000000a5e5624139978a827213f897600006a13e20000b5c00030795bcc2600000014c000061114b8f3475c3500000bc407035433d043000000035e999076e1741ad00000004753ff8f0800022f3d503b0fa40a02ce14448b838200016e0d020000001a30a1867c0948000000120252000000000000000009e208c3290c1cb6a0e32718000a1c00000008740003570431db86244743eb800000007b000129ccce2d40539228eb46f400390dc0005d00000d2c5b47060000bd400000000000002d411512b000053000010290fc154000096800093439405a0b2d0100b30c60844fd87d80cb1ba85902370529e1c2945ba3c480000005a500000000007120000000dd2412000017400000037d9e740004e038497788886b92668fec0002620000e14f0a00002285240004d13ef967c7ce6360c49718e2c4231828aa8d9828a3a693948c43f500000005fe2f90000ef4f683a200009ccb5841715f952c0ae6e52ca149861a45324e02841105a10cc87d84dc39a1df14b8cba7a519d15904541881511998dd02c91ee1dc0ba20bf1699b4c9ee1501c89578f043240630f005403482c90cfc4e80003ea92800002853b48aa41f05771f511187a063e0000058a382012f0000012624d26d00009a672308296a80960000e280000002d90000a0d0665213b600840b80040000040140b401400000800c00400003c00001003402001400000004c01c01408800007006400800000400000001800c00000000c01000000000800401400804403000000000c00800004001000000000405004c00401c01004000000800800000409400800802800000000006000800000000c00002002004804c0ec02801400403c0240040680bc00404800c01c00c00001800800000003c00400000800c00000400801c00c00c03000401400800400002001403000c03801c00402001c01c00001c00
  | 17 => 0x6d0eb02720340ec80748e614831598200007440920d3c46805e3b88d38d6c000000130072e18035b80000000003f392fceac0ce222959c29c0001ec15acb980000510a208cc6d8412000000057d182003cdee06118e1f1cd4e2693fc08a4e564342f11fe474800012a000000058700003749f200010a8bb8f1e2de3679f50574835000000018e00028597680000001a5121400023d0699e5800048317b8000fda3a91f695d8aaa00000000008b66931e09acce700461059c1c9be42c1fc9660a7679717081c0f1c73504295ec06e6a30e8194c8de7f01aa87b02260003371168d867323b519146e02810588cc0ff40733448efc2d077740096f0be447d1bb83d4bae1b80000000e4e49917200007e618d2519468e362433e80e5891a4ab29b0ebc7b4685159943412a81b16c06847d61621ed98d0d705d93bd990c71c38837e83e83ce61d4060bd0fcc5930108eac3527b30fe01b4ce066a33910e50148143711a6cd8823b2a68fd037a0f90ea80000003fc11907b446059b0cf9ed8afe29d3ab9d3cf7e72a29001300001f90628b04bc22bd08f8a544265820a882e8a240001d8000103200000000000007b2054858000000003a0000ac079b0000000f860001e98000eda0000bf80000000003c1870c00082c2a60be80b000000710cc00061417e1d1ca083b800000001ce55931215f840676510c80004b261f1459e1800041112e1c882f200017b1ccc46c45d38a16c0f7446d00000005c46ef34b96640000f20d111e0ec44f53501ac0a9c4d624800000000d831d8110e6c1e6000000054e000000190000016e00000000003df1f89880000000346869ce7e35e00000000007c600000000000001d90cb8f3e7ee1be1b0400075d36680801801b703b8f98af20001e205d82327a432782b079c7521f097acb1c0b226311209de4fb2f68c6c12031825702ecc923862fb208067022602d139c6f43831cf855063e54f2078cd87904d22e204d4a627500331144a527c234120448c806c1119364e7820d20690986c23ff12d87c47b25c83dc81c483a1693209568bde4ce1ce9014be66920001e68e2e4693001d4ca3e2be3bf1ec01983632048d8800000000003ccfc6000000071c1be0000000001038487097007000050303a924837e0003821d2428a000246000100400027e163c8b267810b8830a0e3c63430800e067dc27c15cc1ec5a03799b482784b9352826012c65c1fe98e105425e28c9f349924e623f9200b683140988000b921700000ac856c4360c593600001a3325800000024b0000b940000000b18ef00000000378000f400003b98c2c2025bd1d080005a443101d8c38000000313102827466c14c8000e7659100013880f43014079b0015e71100007b8b622902a50c2000036c0288000a7e47e000000000000040c05c86565573cf1dd06
  | 18 => 0xba600025f1bd400062d00000004040004158000f140a300008e400006b000000000000000000001de0000000fc832600d098102c00065a00018fc6866aa0000000036000000000000000009d8dc898a7100d306c059a45709f00000008250000000000000413010cbf00000000c1800000036380000006c212c12bccc20000ae12040001ef0049418ac613d0000d4c64a4b30001ef40001fa3b784700001ac13c1cbcd4c1f320c8000c540001bc03c00004db0002038c8c1ab2d910a838800007e0000cae1900c200000003b621580004d81a02281320cd60001da098054a1b437912ec00054723516a479209e06103f4e2a34924a9f14cb269f0000974a705e800000000000131f28748e3065421909f03c82682e08000d682753548900caa0151ae100800048f4001ef0fe800000000000005ab0d29e500002a13fb841023c76327d108491c00022a9dac04819e1880b2899e16c3d080004cc0002740b6c0000003ce075c6ca1263f4800076250f0d5000000001200000000002330000000000000122000000072c0000b588bc00015d99f4000000324000059842820b0000ef250028480001083d200016100003dd28b8000000000000102078e38a2098000fb40101bb10a43d63d100a19348944383aa000061e7e40000c4ce7a1070000dfc00052a00018cc6c058931900006fc6e0328115800026d00019380001dc3c6086c13a1590000f8c006030242078862e000000000000022c143100c00038c0ea1b6c9307fc0001bb80f855d000066c8f26ab39484207d82a329601a86c83cb38f8628b0021a393093c2c23a61d3894c2ae53226598e4aac7ca16a9bc0e3459d40b0aac96c06721382e058604141b9a742d61b50aa979432a57538714500b61912c0802c55c77a1e284d880c35d35f801075a1462df8534640552001010053e2841f20bec4a27fd17e8914a780ae23d095cf328320001aec6dc5e60000000884000029a05c00067104d95986662c51c91b184842e600015140002cf20396b465262f1168c743be5e936e97f0da86832fe998855a08a09987f425807f08b187855e4860151ac8b0a6740161ad40002092b6893872600008d0fd8a9051606a14d07080000ed1abcc6a06930e07a41040000800000c080003488000f2a23c0000690ffc0000000d186586e30651ab905e0001b9898c00015a0a913a8000000047899cd347ce0d88b18c6e60522705d4ab8319258938406a51e064137889e6dc20a9f80e385ca390034041c3d63f1175000009c2f800000dc08100016f800055136293740000002180000b8400011400007e00b60000000000000000000000000019a02dc00000000020240008070000000e3c00027600002ee705000103000021034a050cf5a60c12911c000003300007188be4490000fa030e0cd02a00680000003
  | 19 => 0x1d2cf964671b68a68df230a216815400000033c92b0d0829c0ce0000c7a00023e048c56a4f03a092a80000002ad800013e62928e90ec4f403d38020b8ec260920e1858952746244025cb761c913d90b905072e2cb9e007de7a71ac05c437254632d8a900a041e3471f580f00da0001628000000000000010e00000012e84700004020000b9a00000003640001ff00000000000c400011806fa0000001e4cf4c4970001b5451e0000000ce4a922553649080a484b009780000003591a603a8ad20002758af00003e90e41f30c840002840e6c9a82500000000b4612508507780000000001eac3ba000223884875400000000005ba00008800000001fb1c587280000000748d107865b7138800000000000000d8898596310800068e3ba37681888f67e826a8ba00006d62ed8a00d580923d180002cc23f2bc000073200024885b4e04768000043400012b2ff054cc4a61a36b800005204f2511dfc0c83ee03f074409c6271ea097cbb83740001e3443c836000020d04433b1dd8e1c0000001ba800058e4ff07d8e3464653e2b40000b340000000000e8a008200208400000024994dc60013801280f0ec84fe00000000001420000bb4fc200016f8dec0004c20000870fde41b4168bcc0001e000000008dc28c30800e44427c913c9d305c61e80a206388862460d78000c0423e3fb000038007d0000438ab0766387800039609100000983fc788000000000045237e032c59c4f30000730dc867e094046c3ea0003e98ee50624e90089a7065a20724112dcdcc0d50740760d7453d0888000b4c000202086000000000000000006d93df008c00000041490400005df0001ebc750000021198000058d00011d835a3160001d5400000000000001c20001790000ad404a25692d000073a36f80000000000cc07dcff649b1621cb4ebc4bd3e00c0800a4a62af9958d94665084888824235b3db9dd502604835680000002c221280005c073733986e85680000000000eb84ee0000e9507263a3738e54d1081f41c118c7bc0760ca1ea052814119b8238b8a7393180ba49b80893d705cce945333c908903b614f1329fd44ee58813596e4a725230770394aca1c13928a380304cc00015c000002d0ac1f3cb9e2702a820744de00005800001a42d721a8000ec00000001b8479e2760d41dd86f239e00000009c85431cc009c334000000000000000013f1e607ae04738988e864e69030080005ce6bc3c80000c0600029280000000001930dac00034100000000001e11778b00b0600014107c09782b904a059cfd444b000000020c6f620a182cbf400000000000001f4154164041034d08113f4f0824c1d18cf80f20e21b781489a07583f59eecd485b31e500306d44411ce0450000561000000000040e1759d6c0000001b894e85b866934a8cf420632a392022c
  | 20 => 0x191039c1562bd1838cc651500000000000fe3ec83d0560291000000062a0000000000cbe1be21d048800000031400000005b63840a4d0465c73e400000000ab000000080273e067860800023505a807c00062c00019bc00075f37c00000000d70000000c1a3d52c59c28a141d63d61ea405c0001fd000000010f000191c1bc0001079748c9422e1e6000000067700017b01481b624497d0fb6454398800000070d05317fc2ca0ed09900ac00000000009910684b500002e4ef06a8000065cb802311908a98cf649f1c798182bc00033a9a88ece31a1239fcc28049634f000026e57117f00000004a50000ba800057200010f40000000001b2c8ca6eb4091a1ce800002ba0a58e686223a891a0bd45f707b8000a200002a2016463c0003d8979c00001900b80000000000000264a0a2723dc00008e400000000004b40db2d78d9c00017c06b07341344941da94047c46f101413d800233c12483fc9942ec220135c15a6310001c6444e0bd00002f800071d000000004465800017eccec61b01d1bb0bdc0003a1000070222500000008d881e0000000cda0001b406c86a422000016a09641180001a2800008d0a601940005e40b20000d1e6170001c048340600c30fe02fa12700000003f00002c300009425dd32600009502b718480000000003b917d4c147c11209cc09da3f7000081000078b29a83045583fe1350324e186803940000d2c528000038102a00000001704c214b3c0857c000527000042c8c200000005e853c15b3c88c0c00061800020c0fa220a00000000000000c08e8000000026080c80002f0000000065e03121e092030a21f0c9045cb4e0000268000cd028d289978c684422168000066456c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x9a582d86dd77250e42006151d9811d5434c801b04426047550d320055164475dc9434c801545911d47250d32254c32615450d524c8cf50c9755143549320060b611821d94354401435911087650d510050e640421d9435440145591cc87650d5159e15607321d94354401835846047650d510061560d811d94354401866826047650d5100619609811d94354401c15414c47650d510061c606801d94354401859836007650d510061a609801d94354401871816007650d510050d647401d943544fd83581d007650d5100513648301d94354401455910c07650d510041da60765c5435440103d981d063589510060d6047418d6254401838746006358951006831088650d325440160d9418d624c951006832106358932544016499018d624c95100417660731916054401855811cc6458151006131cd82191605440181c841cd62581510060d1d9811d54350401317936037454541004c96488750d51504013319021d43545411d4c52617350d515047583486dd172545411d4c9261725095150475525971894254541006151d9811d5434c495c447654932545310241da6387591514c4013179460b7354531004d16488750d514c4013519021d43545311ccc52617450d514c4733179850e42545311ccd164b844c9514c4011549761132545311fd1525d644c9514c473646969c932545311ccd1261724c9514c58dc44765c93254531645c1251724c9514c47385486dcd7054531005156447558d43c8401435911d76450d2100c6925d844c941484cfc847650d3250521006295c9811c96494001834766047550d40006c40c1811d54350001531911d77050d400054c644751c143500019183021d43545400054664c745c15150001918831d170545400054a648745c1515007563190d8d51505401d54ca5e80545415017b9308760151505401d58c25980545415018571093601515054012c4d2617454531500573189854d43541402fd4625d5350d505005732898549425414015ccc261515055050001857766047550e301d585e5943545418c0012349859151505301cd9425980545314c07335198544704c530257121d9524c9504c001455911d56350f200050d64475591438800343497591515052000d1525d6354531480019888750d32501202fea2219434c940480cfc887650d32501206c5c2255434c9404800123591215735902000495644855d163080010759121d6550c200050d644755914308001455911d56350c200041d65c8550d6108001c29725c164d4420007125c97058f5108001c61725c161d44200050d644755914384001455911d76350d1004d2925d6450921440012a59421932485102fea4219434c540440011d19321d21501100066821d4248540440031d0985d1314c11000c782617448520440034e0965cd2148110
  | 1 => 0x1a421b800100000036853d960d867048a8b6000012c500613000e2661a1bc8a080ea0060002a80000610b00000212b918007e0c0ed0e72001e0085305014d074119c0007a3e920ba17318780051279f05c003c9a49c43239283229320c47c42248044462000385a3741100bc8143180d600100b00000000c81e750a17c005a129dc706a0e00c00520687cda07328545e001f80056361384c6611280f4004c209d8887f1d164720b26808e63c09170ac001220c00001a950180006010c0e000101022401160000020103000004023100000d0507020c05060346000001021c0024040002010100554a43435c46550c015269290d71195430050da58435c46550c014569610d71195430044d660425c46550c015169310971195430054c640425c46550c0151694cc9711954300545a4f405c46550c01155980c1711954300545a50305c46550c01545920c1711954300619a09711846550c01865825c461195430061c5c6801846550c01871716006119543006155cd811966250c018357460465981430060ddd9811d54390
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1860011c5681400ad003800c4804600060002305a9109811d5434c801580d0084c08eaa1a6400a8168442219434c951005413402110ca1a64a880220da9210635893254401902c890831ac4992a200c822119018d624c95100403b52420e6b12c0a8802311a90c1811d54350001580d1060c08eaa1a8000a426883021d4354540005223421810ea1aa2a0002119a920c745c15150001888c89063a2e0a8a8000c4220d921d17054540
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x3
  | 10 => 0x124c
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x8a
  | 14 => 0x8c
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x98a
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128a
  | 22 => 0x128c
  | 23 => 0x128d
  | 24 => 0x128e
  | 25 => 0x150a
  | 26 => 0x150c
  | 27 => 0x150d
  | 28 => 0x150e
  | 29 => 0x9ca
  | 30 => 0x9cd
  | 31 => 0x9ce
  | 32 => 0x12ca
  | 33 => 0x12cd
  | 34 => 0x12ce
  | 35 => 0xa0a
  | 36 => 0xa0c
  | 37 => 0xa0e
  | 38 => 0x130c
  | 39 => 0x130a
  | 40 => 0x130e
  | 41 => 0xa4a
  | 42 => 0xa4c
  | 43 => 0xa4d
  | 44 => 0x134a
  | 45 => 0x134c
  | 46 => 0x134d
  | 47 => 0xb0c
  | 48 => 0xb0d
  | 49 => 0xb0e
  | 50 => 0x154c
  | 51 => 0x154d
  | 52 => 0x154e
  | 53 => 0xb4d
  | 54 => 0xb4e
  | 55 => 0xb8c
  | 56 => 0xb8e
  | 57 => 0xbcc
  | 58 => 0xbcd
  | 59 => 0x19cc
  | 60 => 0x19cd
  | 61 => 0xcca
  | 62 => 0xccd
  | 63 => 0xcce
  | 64 => 0x15ca
  | 65 => 0x15cd
  | 66 => 0x15ce
  | 67 => 0xd0a
  | 68 => 0xd0c
  | 69 => 0xd0e
  | 70 => 0x160a
  | 71 => 0x160c
  | 72 => 0x160e
  | 73 => 0xd4a
  | 74 => 0xd4c
  | 75 => 0xd4d
  | 76 => 0x164a
  | 77 => 0x164c
  | 78 => 0x164d
  | 79 => 0xe8a
  | 80 => 0xe8e
  | 81 => 0xeca
  | 82 => 0xecd
  | 83 => 0x104a
  | 84 => 0x104c
  | 85 => 0xca
  | 86 => 0xa0956
  | 87 => 0x10a
  | 88 => 0x168a
  | 89 => 0x180a
  | 90 => 0xbc9
  | 91 => 0x198a
  | 92 => 0x4c
  | 93 => 0xa1256
  | 94 => 0x4d
  | 95 => 0xe89
  | 96 => 0xbcb
  | 97 => 0x19c9
  | 98 => 0x19cb
  | 99 => 0xa0996
  | 100 => 0xcc996
  | 101 => 0xa1296
  | 102 => 0xcd516
  | 103 => 0xe8b
  | 104 => 0xa49d5
  | 105 => 0x14c
  | 106 => 0x138c
  | 107 => 0xcc9d5
  | 108 => 0x180c
  | 109 => 0x1789
  | 110 => 0x198c
  | 111 => 0xa52d5
  | 112 => 0xce
  | 113 => 0x14d
  | 114 => 0xb8a14
  | 115 => 0xbca14
  | 116 => 0x19ca14
  | 117 => 0x138d
  | 118 => 0xd0a14
  | 119 => 0x168d
  | 120 => 0x198d
  | 121 => 0x10e
  | 122 => 0xbd314
  | 123 => 0x19d314
  | 124 => 0x138e
  | 125 => 0x168e
  | 126 => 0x180e
  | 127 => 0xccb16
  | 128 => 0x3ca
  | 129 => 0x40a
  | 130 => 0x170a
  | 131 => 0x188a
  | 132 => 0x1a0a
  | 133 => 0xcd556
  | 134 => 0x20c
  | 135 => 0x20d
  | 136 => 0xbcb55
  | 137 => 0xccb55
  | 138 => 0x140c
  | 139 => 0x18ca
  | 140 => 0x178a
  | 141 => 0x184c
  | 142 => 0x148c
  | 143 => 0x1a4a
  | 144 => 0x17ca
  | 145 => 0x14cc
  | 146 => 0xbcb94
  | 147 => 0x140d
  | 148 => 0x16cd
  | 149 => 0x144d
  | 150 => 0x1a8a
  | 151 => 0x194a
  | 152 => 0x14cd
  | 153 => 0x14a
  | 154 => 0x4e
  | 155 => 0xccbd5
  | 156 => 0x15cbd5
  | 157 => 0x44a
  | 158 => 0x20e
  | 159 => 0x140e
  | 160 => 0x144e
  | 161 => 0x5ca
  | 162 => 0x148e
  | 163 => 0x74a
  | 164 => 0x16ce
  | 165 => 0x184e
  | 166 => 0xcd9d5
  | 167 => 0x15d9d5
  | 168 => 0x188c
  | 169 => 0x44c
  | 170 => 0x1a0c
  | 171 => 0x3ce
  | 172 => 0xd4d14
  | 173 => 0x44d
  | 174 => 0x170d
  | 175 => 0x18cb
  | 176 => 0x1a0d
  | 177 => 0xd5614
  | 178 => 0x40e
  | 179 => 0x170e
  | 180 => 0x188e
  | 181 => 0x74c
  | 182 => 0x5cd
  | 183 => 0x194c
  | 184 => 0x1a8c
  | 185 => 0x1a4d
  | 186 => 0x17cd
  | 187 => 0x18ce
  | 188 => 0x178e
  | 189 => 0x94a16
  | 190 => 0x124a16
  | 191 => 0x128a16
  | 192 => 0x150cd6
  | 193 => 0x12ca55
  | 194 => 0xbcb8a1c
  | 195 => 0xcca16
  | 196 => 0x74a14
  | 197 => 0x194a14
  | 198 => 0xb0cd6
  | 199 => 0x154cd6
  | 200 => 0xccbcb5d
  | 201 => 0xb4bd5
  | 202 => 0xb8bd4
  | 203 => 0x148bd4
  | 204 => 0x28e
  | 205 => 0x144bd5
  | 206 => 0x24e
  | 207 => 0x19cbd4
  | 208 => 0x19cbd5
  | 209 => 0x5ccd5
  | 210 => 0x17ccd5
  | 211 => 0x160d54
  | 212 => 0x170cd6
  | 213 => 0x1a0d54
  | 214 => 0x180a16
  | 215 => 0x198a55
  | 216 => 0xcca099e
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
  | 6 => packedAt gbK6 (387148+((h/2450+packedAt gbK6 (352848+(h % 2450)*14) 14) % 14206)*14) 14
  | 5 => packedAt gbK5 (132678+((h/702+packedAt gbK5 (124254+(h % 702)*12) 12) % 2780)*13) 13
  | 4 => packedAt gbK4 (9880+((h/45+packedAt gbK4 (9520+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt gbK3 (1240+((h/5+packedAt gbK3 (1215+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe31c0e3f38c78e0e11f87f87fc60878e44cf
  | 1 => 0x703e00fc7c0f8f00ffe3f83f83c8119907b33
  | 2 => 0x7fc000ff8ff00fff01fc003ffc1061e638c3c
  | 3 => 0x7fffff000ffff00001ffffc000207e07c0fc0
  | 4 => 0xf800000000ffffffffe000000003f8007ff000
  | 5 => 0xffffffffff000000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x50410482091041824240485083186082864045
  | 1 => 0x82022104420008100502140120208109001112
  | 2 => 0x5a40228904900252014810a54810614208c28
  | 3 => 0x2128486000ea9200a099232810820220780e80
  | 4 => 0x3000004000b4e4c8c8c00230010a28005f6000
  | 5 => 0xc6d3938f24000001010004406631d5df800000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xffffffe8fefceee8ffffffe8fefceee8ffffffe8fefceee8ffffffe8fefceee8ffffffe8fefceee8ffffffe8fefceee8ffffffe8fefceee8ffffffe8fefceee8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27845
namespace PEqualNP.Outside.L_meta_27845
open PEqualNP.Outside.L_meta_27845.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_4_0 : Interval s2Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 4 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 4, 20),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 8, 40)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 4 zero,inputs.getD 3 zero,inputs.getD 2 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffffafefefefaffffffeafefeeeeafffffffafefefefaffffffe8fefceee8fffffffafefefefaffffffeafefeeeeafffffffafefefefaffffffe8fefceee8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,1,129)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27845.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,5]⟩,⟨.or,[8,6]⟩,⟨.and,[9,7]⟩,⟨.and,[4,6]⟩,⟨.or,[0,2]⟩,⟨.or,[6,7]⟩,⟨.and,[12,13]⟩,⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.and,[15,16]⟩,⟨.or,[10,11]⟩,⟨.or,[18,14]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27845

open PEqualNP.Outside.L_meta_27845 in
theorem PEqualNP.Outside.L_meta_27845 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
