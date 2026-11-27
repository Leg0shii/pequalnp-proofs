import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- The search tables below were regenerated for this graph.

namespace PEqualNP.Outside.L_meta_27831.Model
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


end PEqualNP.Outside.L_meta_27831.Model

namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_27831

namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x58f833ca4a0e1201b11748c2803a65500002c6104001c04600000000b8980003d32810cc02c72bc08d00d432700ac5020001b9b68c912d0e018bb305cd1542700002401280480200184101c100000018108000000c00180b7290876d5210eeca221dd54443bd28087795010eeca3a15d54742bd28485795090abea6a15714d429f2a0653d540caeca2195d54432bd2806579500cadca5a0db54b41af29c835d53906f6a0a0de14141bd286637950cc67ca918cf55231b7a92636c524c67ca810cf55021af298435d53086f4a010de54021af298815d53102dca4205b54840bb288817551102eca3985d54730b7294616d528c27ea8984f151309f2a6413d54c82bca7105754e20bba8a4174514827ca8084f55010af298215d53042dca4085b54810
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
  | 1 => 0x3e3c7fff071fe38e38e0e3fff1c1f83e21f673
  | 2 => 0xc03f8f8ff81ffff03f00fc707e01fffec6487f
  | 3 => 0x3ff00fffe3fc7fc000ff807ffe3fc1078f9c
  | 4 => 0xffc0000ffffc007fffff00007fffc001f80fe0
  | 5 => 0xfffffff00000007fffffffff80000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x844523013028440608222093304c488c209631
  | 2 => 0x188a441242518030310c442442109330c24846
  | 3 => 0x25110924940a00ca4010a90914a42485058298
  | 4 => 0x880226482200c9149a46000269190118680d60
  | 5 => 0x30204800c49312692498d24c00200621976000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffffcccffc0f0c0fffffcccffc0f0c0fffffcccffc0f0c0fffffcccffc0f0c0fffffcccffc0f0c0fffffcccffc0f0c0fffffcccffc0f0c0fffffcccffc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xc885ab928c4c00027340c513008918b3c150a8045490152ace84400002a283ce163e000170c00c00002521b1a00000003962f221c8000028108100054800200308b0ceff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xf001840805369cd0000030dc7e1a130889c4d3e00c76072b86cfe2e410442c691a8acb2503b0f89e45291a8cc6825994ba8528a04c66f321f8f648231d4b078198bc840d0f8e0be5e001c9086b300005a4c2e1542032238c4ac832184c104020950e2020a0e4f4282998814240008c9400220e87a00001d0e0002d800d8003e9b868000e0004a1e3c830163600218003c048005200338840000091240017000604e002d0c00000000380000000803a2c008550e2a0c9dc000600280e000601001209110002002b000d01350103290609260a170a003100041104000503020b2a001a020300bb28c87755190e7ca721cf54a43db28c87b55190e7aa121db94843b6a9087765110eeaa221de94043bca80873e5310f3ca621eb948439ea9087ad5210e5aa421ed94443daa8887ba5010e7aa021ee540439ca80873e53d0a7aa1a14f552429e29a85af5250a7ea0a14f950429faa6653c54ccaeca3995d547329f2a4653d548cb5a85194fd51329e2a265ad424ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53907388798cf952319eaa463b6548c76aa918dd54e31db21c63b4438c76e8518ed50a319faa2633c544c7388698edd5131da2a263d7534c7ae8698ed90d31da21a63d4434c7288698edd0931daa1263d7324c7aa6498dd944319f2a6433d54c867ca810cf55021af298435d53086f4a010de540219f29e813d52d036c63a06d4c7409eaa4813c535027ea4a06d8c540da98a81bb505027ca8204fd53309e2a6617651cc2eaa398754c7309f2a4613d548c37281184fd51309e2a261d5314c37280984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9904f952209eaa4413e544827aa8905dd4520ba28a413e540827aa8105794c20aea98417651082eaa2107a480209f2a4213d548427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x3000287148952558bd82700004a61a44d8000010863880aa84830b0e06a478000644003a4091e007c21a280568b265c02300b95826200600e2011c0045cc0000019a55865310f255294443c95495110f295294043ca9495010f295254043cc9455010f3151540438e5805350a3960153328b195424ca8d6210f31a658043cc6a56210e31ac580438c68d6210d31a6580434c69664d4d318d996434c6966390d318d994434c6a56210d31ac580434c6c56210d31b4580434c6966510d31c5994434c7866210d31a5588434c7856210d31a1588434c7926010d31a5580434c7916010d31a4580434c6946350931a5193324c694644c931e1509324c62d6214d40c514d315022d6215330c515131cc314544c5308e195404c39131501308718d54482556314520d254d20083615148020
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x14e000800000604048600001003a058a6010d31d04c4b008698e8162580434c648b80c6a1263245c064cc931908eca126498d057214d3150282b90a898e61841953150130
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 63)*7) 7
  | 4 => packedAt s1K4 (4032+((h/45+packedAt s1K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s1K3 (1996+((h/16+packedAt s1K3 (1900+(h % 16)*6) 6) % 61)*7) 7
  | 2 => packedAt s1K2 (456+((h/3+packedAt s1K2 (441+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xf1e3c7fc78ffe3f18e3838fe38ff87f10f1cf
  | 2 => 0xfe03f9ff80e3fc7e0fc03f1fc0e3f8f633933
  | 3 => 0xf0003fe3fff03ff8ff0003fe3ff03ff083ce3c
  | 4 => 0xffffc003ffffc000fffffc003fffc000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x41404600421408400840908240830824105045
  | 2 => 0xa20c89489128540860a42910a424930a612912
  | 3 => 0x9110112400a0019100422409402440828228
  | 4 => 0x2404010a010004922229080032288102240d80
  | 5 => 0xc8d82250364d3924dcd273c90041066cdbf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffffaa0ffaafaa0fffffaa0ffaafaa0fffffaa0ffaafaa0fffffaa0ffaafaa0fffffaa0ffaafaa0fffffaa0ffaafaa0fffffaa0ffaafaa0fffffaa0ffaafaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x990f631f531bf40bd40
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
  | 4 => packedAt s2K4 (67+((h/1+packedAt s2K4 (64+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3c38f1f8f3e3fffc631c38fc18e1ffff21c0ff
  | 1 => 0x3fc0fe7ffc038f1f83e03f1fff01c70f467c93
  | 3 => 0xc000ff80fffc0fe3fc003fe01ffe07f0878f1c
  | 4 => 0xffff0000fffff003ffffc0001ffff800f80fe0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x501180111060400220510250020614820c025
  | 1 => 0x8892253020c9122181208908d90c9226421c92
  | 3 => 0x82a441524a412806c4022a424a5404a2870518
  | 4 => 0x10100424808002490948800094891004480ac0
  | 5 => 0x232088400b124c9272933493001020c8b5e000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xffffeeccffaaaa88ffffeeccffaaaa88ffffeeccffaaaa88ffffeeccffaaaa88ffffeeccffaaaa88ffffeeccffaaaa88ffffeeccffaaaa88ffffeeccffaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x4032000df31dd31bf40bd40
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
  | 4 => packedAt s3K4 (67+((h/1+packedAt s3K4 (64+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7878f0f8f3fff8fc718e0c7e18fff87f11c3cf
  | 1 => 0x7f80ff3ffc38ff1f81f00f8fff1c3f87227d33
  | 2 => 0x8000ffc0ffc0ffe3fe000ff01fe03ff8c38e3c
  | 4 => 0xffff0000ffff0003fffff0001fffc000fc0fc0
  | 5 => 0xffffffff00000003ffffffffe0000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa01180111204100210284128026082410c045
  | 1 => 0x10122210208110208090208449089102201512
  | 2 => 0x56444a24a12a0075201492112412650c30a28
  | 4 => 0x213006948090324994a460005c918312640f80
  | 5 => 0x464088200b24c49269498e49800204649be000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xffffececeaeae8e8ffffececeaeae8e8ffffececeaeae8e8ffffececeaeae8e8ffffececeaeae8e8ffffececeaeae8e8ffffececeaeae8e8ffffececeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2d06842284a5d499565401a58248003e1878d44bd726020000000a8b0248708944e60e9b1c011800a2cf0a0e4840018000134000008038d0eb0830020c0002ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3b0285e81002184014000884c5b0007ca61a1c1b492610001c2083091f054414292c082927030a85607208fa081a890941327800d8842a9a0f400168e8005921000003d0e0d046002d180505d0c0240016058000073400c8000033800fc00000003c74330cc786f228005600001c4c827351fc864431970a24031094a4501d9c89a030e9947c17109205836000086e2e0786472000000000870000000000000000300d800d658000148c692f9e000002f000f2570a91cdc75380001a31260fc0c013d9dc22010d00030b00110b0a0111020100030b01000b0133110100030200560f080a020b070006001b13010509000d03bb28c87755190e7ca3a14f543429eaa485af5250a78a2a14fd41429f2a0853e548ca7aa9194f950329eaa06576510caeaa2195e94032bca80655e53906baa720e794e41cea9c833d529067ca320cf54241af298835d53106dca420db54841bd2808379501073ca620e754c41d7290833d521075aa420cb548419f28883b65110774a020cf54041dca808339501067ca998cf55331cf2a6639d54cc73e8598e750b31cf20e639c41cc6baa718ed106319faa2633c544c7688298e7d5131ce2a2639f424c73a8498f5d4531eba0a639e414c7388298f510531ca20a635e530c67ca990cf55321d6a16433f5488678a910d794e21aea9c43d5318867ea890cf15121d6a1243d5314867ca810cf55021af298435d53086f4a010de540219ea96813e51d033e63a0674c7409eaa4813f5250278a2a067cc540ce98a81bb505027ca8204f952309eaa4613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6413e548827aa9104f951209eaa2415f53482b8a6904f950209eaa0415e53082baa6105d94420baa8841e9200827ea9884f15310af29e215d53c43aa63884f952109eaa421b9408427ea8884f15110ea98a21b9404427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb211a54b9f5a005123c4c72c46a0ea74040ca40e7000b00c0d94000000c0000009000002f00604314a0158002000061e1088300b930252a82a2340400008040008100041051e440948e5805150b0e5354841c354d52106956394441ca54a501071a5354041c654d501072a5254041ca549501068d6210731a658041cc6a56210631ac580418c6a56210531ac580414c6946150931a5993514c61e6590531a5986414c61e6510531a3588414c6996010531b1588414c6d16010531a5994414c7166510531e1988414c6956210531e1588414c6856210531e4980414c6956010531e4580414c69160105318e5805488714544c6218b1954248714544c521e1509314862d6214540c5145315023461551209558453483495348020d8545200822d6215310c515131c4314544c5108e19540443913150110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xcc8100040800501c241245c06150931d02c53008298e8262580414c740b12c020a63445c0544c621a08eaa126290d05721453150282b90a898e21841953150110
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
  | 4 => packedAt s4K4 (4032+((h/45+packedAt s4K4 (3672+(h % 45)*8) 8) % 180)*9) 9
  | 3 => packedAt s4K3 (2012+((h/16+packedAt s4K3 (1900+(h % 16)*7) 7) % 67)*7) 7
  | 2 => packedAt s4K2 (453+((h/3+packedAt s4K2 (441+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1e3f87e3c7c7fe3f1c71f1f82387fe3f0dc1cf
  | 1 => 0x1fc7f9fff8071fc7e07e3e3ffc070fc7327933
  | 2 => 0xe007fe03fff81ff8ff803fc03ff80ff8c38e3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 5 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8280a004410a0840042050490081421404c045
  | 1 => 0x441110408090240820120210a4122482101912
  | 2 => 0x1220089120050014880248209200920430228
  | 3 => 0x4810555224840492b1548004b254a082b80d80
  | 5 => 0x91a4658037269924de6939270060c134efe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeecfeecfae8fae8feecfeecfae8fae8feecfeecfae8fae8feecfeecfae8fae8feecfeecfae8fae8feecfeecfae8fae8feecfeecfae8fae8feecfeecfae8fae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x40000486343c005540118a260080e3c341a14e940002a90e002200014321c901048901f186c02b1600b0800a0b804c60e80520800c24400062d7002141ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2000000005a7800728e0000480000008c0016003800a07c60002482000000006c00000000b6000000920000000000620084006e3c7a88184000000000803ea40ab0444a00000000000064220096060000000000860000ae76280042000e00009c5c7e000000007420002c52a24c4e00003a709e2a0000143600080090aa66302e001298465868a804b49a1c5e50ac1e1a326a8aa6b210002600009400000000000c5400563407030400000002010006040009000601010b00000a000000050001000100bb28c87755190edca421db54843bb28887755110ef4a021de54043bb28e857551d0b6ca3a16d547429eaa485af5250a7ca8215d94732baa8e653e548ca7aa9196b50a32d6a12653e540ca7aa8195d94432baa88657a500caf2a0195b94b41b6a96835e53906baa720cf952319eaa463b6548c76aa918dd54e31dba1463b5428c7aea698f5d0d31ea21a63b7424c76a8498f5cc931ea9926376510c67ca990cf55321d6a14433e540867aa810d794c21aea9843ad42086f4a010de54021af298815d53102dca4205b54840bb288817551102eca3985d54730ea98e613f544c278a898754c5309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6a1641ad42482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1464800261c250390f0100b1b44039229558e51d0a956394742a99875250a2d6295231a958a548c63565d0a31a5993534c6c56210d31b4580434c785424c931c354d420872942540218b588544c314544c5309558c51483254214520
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x80640090ae730ea4a148572993534c682b90a898a618158d4214520
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (2724+((h/30+packedAt s5K4 (2484+(h % 30)*8) 8) % 177)*8) 8
  | 3 => packedAt s5K3 (633+((h/5+packedAt s5K3 (608+(h % 5)*5) 5) % 20)*5) 5
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf1e78f3ffc71ff1f88c70c7fe38ff0f80f1cf
  | 1 => 0xf01f80fce3f818fe3f0f80f8e3c0e7f3b34933
  | 2 => 0xffe000ff03ffe0ffc7f000ff03ff07fc438e3c
  | 3 => 0xffffff0003ffff0007ffff0003fff8007c0fc0
  | 4 => 0xfffffffffc00000007fffffffc0000007ff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1020110004020020000100120082100001045
  | 1 => 0x10c4322a44925160430c86484a425263314912
  | 2 => 0x22014440892402800c90089210940488428228
  | 3 => 0x44481008520200249125220003229021140d80
  | 4 => 0x88916082803494c926ca4ce4980400ca6be000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8ffeafae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c180027fd5007fe54007f55007fc54027fd4c01fe53007f54c09fc5301ffd0c01fe43007f50c07fc43027fd4801fe52007f54809fc5201ffd0801fe42007f50807fc42007fcc801fe32007f4c801fc32027fd4405fe51007f54405fc5101ffd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc21027fd40017f5000ff94001fd50005f54003fc5001ffd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001ff0832000fd84190007ff10c8003ff0864001ff04320007feca90002ff6548017ff32a4004bf99520007faca90002fd6548017fe32a4004bf19520007fec890002ff6448015ff3224003bf99120007fac890002fd6448015fe3224003bf1912005ffea89002bfe5448001feaa2400aff15120007fec690002ff6348001ff31a4008bf98d20007fac690002fd6348001fe31a4008bf18d2005ffea690003fe5348001fea9a400bff14d20057fe8690003fe4348001fea1a400aff10d2000dfec49002fff524800fff2924000ff5492003ff8a49002bff424800fff2124000fb90920007fa8490003ed424800ffe2124000ffcc92003ffc6490003ee3248001fe9924000fb4c92003ff86490003ff61480017fb0a4009ff98520015fcc290003fd6148013fe30a4002bf1852005ffea290027fe5148001fea8a4009ff14520057fe8290027fe4148001fea0a4009ff10520007fe6290027fe3148001fe98a4009ff0c52003ffe4290003ef2148013ff10a4000ff48520007da429001ffc21480037fb024001ffd412000efea090007fe5048003fea824001df5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001fe8c12000ffa6090003f93048003fe1824001ffc812003ff64090007fe2048003f71024001ff0812000fd84090007f82048003ff8824001ff8412000ff42090007fc1048001ffb2a2000bfd9510037fcca88012fe6544001feb2a2000bf59510037f8ca88012fc6544001ffb222000bfd911002ffcc88800efe6444001feb222000bf5911002ff8c88800efc644400dffaa22005ff95110007faa888017fc5444001ffb1a2000bfd8d10007fcc688022fe6344001feb1a2000bf58d10007f8c688022fc634400dffa9a2000ff94d10007faa68801bfc534400bffa1a2000ff90d10007fa8688017fc4344001ffb122000bfd8910007fcc48801efe6244001feb122000bf58910007f8c48801efc624400dffa922000ff94910007faa48801bfc524400bffa122000ff90910007fa8488017fc4244001ff9922000ff8c910007fa6488003fc32440037fb0a2002ffd4510017fca28800bfd5144005fe28a2002ffd0510017fc828800bf64144005fea0a2000fd50510017f8828800bff3144005ff18a2002fd8c510017fa6288003f53144005fe18a2002ffc8510017fc428800bf62144005fe90a2000fd48510017f84288006ff6044003ffa822001dfd411000ffca088007fa5044003fea822001df54110007f2a088003795044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbfe21cc001fe90e6012ff0873000dfac198007ff50cc003bfa866001ff9433000ffaa1980077d50cc003fe2866001ffd033000ffc8198007fd40cc003fe2066001ff8c33000fbc6198007fa30cc003fe1866001f70c33000ffc4198007fc20cc003ff8866001ff8433000ff82198003ff654c0017fb2a6011ff99530025fcca98003fd654c0017eb2a6011ff19530025f8ca98003ff644c0017fb226010ff9913001dfcc898003fd644c0017eb226010ff1913001df8c898047ff544c021ff2a26000ff55130087f8a898006ff634c023ffa9a6008ff94d30007faa698023fc534c021ffa1a6008ff90d30007bc8698003fd434c001eea1a6008ff10d30007fec498002ff624c001ff3126000ff58930007f8c49801efc624c023ffa926000ff94930007faa498047fc524c021ffa126000ff90930007fa8498043fc424c011ff9926000f7cc930007fc6498003fd324c001ee9926008ff0c930007fec298002ff614c01fff30a6002bf98530007fac29803ffc614c0057e30a6011ffd453007ffca298003fd514c01ffe28a6010ffd053007ffc8298003fd414c01ffe20a6008ffcc530007be629803ffe314c001fe98a6000f74c530047f86298003ff214c01fff10a6000ff4853007ff84298006ff604c003ffa826001dfd413000ffca098007fd504c003bea826001ff1413000ffe8098007fe404c003fd2026001ff50130007f28098007fc404c003ff9826008fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fd1026001ff0813000ffe2098007fe104c003fe0826007ffd972003dfecb9001ffe65c80097f32e4007ff59720005facb9001ffc65c800f7e32e4007ffd932003dfec99001ffe64c80077f3264007ff59320005fac99001ffc64c800f7e326400effd532006ffca990003fd54c801bfe2a64007ffd8f2003dfec79001ffe63c80117f31e4007ff58f20005fac79001ffc63c800f7e31e400effd4f20007fca790003fd53c801dfe29e400dffd0f20007fc8790003fd43c801bfe21e4001bf98b2003ffea59001ffe52c800ffea964007ff14b2003ffe859001ffe42c800ff72164007ff50b20007da859001ffc42c800fff9964007ff8cb2003fdc659001ffd32c8001f69964007ff0cb2003ffec39001ffe61c80057f30e4007ff58720005fac39001ffc61c80057e30e400effd4720067fca390003fd51c8019fe28e400dffd0720067fc8390003fd41c8019fe20e4000ffcc720067fc6390003fd31c8019fe18e4007ffc872003fde439001ffe21c800ffe90e4000fb4872003ff84390006fd60c8003ffa864001dfd432000ffca190007fd50c8003bea864001ff1432000ffe8190007fe40c8003fea064001ff1032000ffe6190007fe30c8003fe9864001ff0c32000ffc4190007ee20c8003fd1
  | 2 => 0x50006fac6a80037c6354031bfa1aa000df90d50006fa86a80637c4354001bfb12a000df98950006fac4a80037c6254031bfa12a000df90950006fa84a80637c4254001bf992a000df8c950006fa64a80037c3254001bfb0aa017df98550006fac2a805f7c6154031bfa0aa017df90550006fa82a805f7c4154001bf98aa017df8c550006fa62a805f7c3154001bf90aa017df88550006fa42a805f7c2154003bfb02a0019fd8150026f6c0a80077f4054003bf202a001de9015000ef880a80077e3054003be182a001df8815000ef840a80077f1054003bf082a001de8415000ef820a8003ff65500017fb2a8016ff99540025fccaa0003fd65500017eb2a8016ff19540025f8caa0006ff6450007ffaa28003ff9514001ffaa8a000ffc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8008bf18d400b7fea6a0003fe5350001fea9a8016ff14d4001ffe86a000fbf4350007ff21a8003ff50d400077a86a000ffc4350001ffb128000bfd8940007fcc4a0003fd6250001fe3128007bf189400b7fea4a0003fe5250001fea928016ff1494001ffe84a000fbf4250007ff2128003ff509400077a84a000ffc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd85400affcc2a000afe6150001feb0a8015ff18540015f8c2a005bff515002bff28a8000ff545400aff8a2a000fff4150007dfa0a8003ff9054001ffa82a0003bd4150007fe20a8000ffcc5400affc62a0003fd315002bfe18a8000ffc85400affc42a0003fd215002bfe10a8001bfd814000ffea0a00077f5050003ff2828001fe9414000ffaa0a00077d5050001fca828000de5414000ff8a0a0007ff4050007fda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffc60a0007fa3050003fe1828001ff8814000ff840a0007ff1050003ff0828001ff04140047fecb98022ff65cc011ff32e6004bf99730047facb98002fd65cc011fe32e6008bf19730047fec998022ff64cc011ff3266003bf99330047fac998002fd64cc011fe3266008bf193300a7fea99804ffe54cc001feaa66013ff1533000dfcc798023ff53cc011ff29e6008ff54f30047f8a798023ff43cc011ff21e6008f790f30047fa8798003dd43cc011fe21e6008ffd8b30047fcc59801efe62cc011feb166000bf58b30047f8c598053ff52cc001ff2966000ff54b300a7f8a59804fff42cc001ff2166000ff50b3009ff88598023ff32cc011ef9966008ff8cb30047fa6598003dd32cc011fe1966008ffd8730047fcc39800afe61cc011feb0e6000bf58730047f8c39800afc61cc029ffa8e6012ff94730007faa39804bfc51cc027ffa0e6012ff90730007fa839804bfc41cc011ff98e6008f7cc730047fc6398023fd31cc001ee98e6008ff0c730007fe439804
  | 3 => 0xfa1a4200ff90d21007fa8690873fc43484057fb12421dffd492103ffca490803ee5248401fea924200fb5492103ff8a490873ff424840fff2124200ff5092103ff88490803ff324840fff1924200ff4c92103ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017fa829080bfc4148405ff98a4202ff8c521017ec629080bfd3148401fa98a4202ff0c521017fe429081ff72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec09086ffe60484037f3024200ff581210dff8c090806fc604843bffa82421bff941210dff8a090873ff4048437ff202421bff101210dffc609086ffc3048437ff1024207ff08121017fe209080bf71048405ff0824202ff04121026fec9a80137e64d4009beb26a004df19350026fec7a80137e63d4009beb1ea004df18f500d6fe87a80037e43d4001bea1ea01adf10f50026fec5a80137e62d4009beb16a004df18b500d6fe85a80037e42d4001bea16a01adf10b50006fe65a80037e32d4001be996a000df0cb50026fec3a80137e61d4009beb0ea004df187500d6fe83a80677e41d4001bea0ea019df10750006fe63a80677e31d4001be98ea019df0c750006fe43a80677e21d4001be90ea019df0875000cfac1a80077f40d4003bf206a001df1035000efc61a80077c30d4003bf106a001df0835000efe21a80077e10d4003be086a001bfd9550007fec8a8002ff6454031ff322a003bf99150007fac8a8063fc64540077e322a004ffd5150026fea8a8013fe5454031bf2a2a004ff55150006faa8a8013fc5454009be2a2a000ffd8d50005fec6a8003fe6354001feb1aa000ff18d50045f8c6a8013ff5354009bfa9aa004ff94d50006fca6a8013fd5354001bea9aa004ff14d50026f8a6a8063ff4354001ff21aa000ff50d500c7f886a8003ff62540017fb12a000ff98950007fac4a8003fc625400f7e312a004ffd4950026fea4a8013fe5254001bf292a004ff54950006faa4a8013fc5254009be292a018ffd0950007fc84a8003fd4254031fe212a000ffcc950007fc64a8003fd3254001fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc6154009ffa8aa004dfd4550027fca2a805f7e5154009fea8aa000df54550027f8a2a80137c5154031ffa0aa017ff90550007fa82a805ffc4154001ff98aa017ff8c550007fa62a805ffc3154001ff90aa017ff88550007fa42a805ffc21540037fb02a001ffd4150027f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff480a8007fc4054003ff182a001ff0c15000ffc40a8007fc2054003ff882a001ff8415000ff420a8007fc1054001bfb22a018df99150006fac8a80637c6454001bfb1aa000df98d
  | 4 => 0x80bfc10cc401ffb2a6200bfd953111ffcca98812fe654c401feb2a6200bf5953111ff8ca98812fc654c401ffb226200bfd9131117fcc89880efe644c401feb226200bf59131117f8c89880efc644c447ffaa26222ff95131007faa89888bfc544c4057fb1a6223ffd4d31047fca698803de534c401fea9a6200f754d31047f8a69888bff434c445efa1a6208ff90d31007fa8698823fc434c445ee21a6200ffd8931005fec498803fe624c401feb126200ff1893103df8c49888fff524c401ff2926200ff5493111ff8a49888bff424c401ff2126200ff50931117f88498823ff324c401ef9926200ff8c931007fa6498803dd324c411fe1926202bfd8531017fea29888ff7514c405ff28a6202ff54531017f8a29880bf4514c405ffa0a6202ff90531017ec829880bfd414c401faa0a6202ff10531017fe6298823f7314c405ff18a6202f78c531017f8629880bdc314c405fa18a6202ff88531017ec429880bfc214c401ffb026200bfd813110ffcc098806fe604c401feb026221ff1813100df8c09888fff504c443ff2826221ff14131117fe8098887fe404c443fe2026221ff8c131047f86098887fe204c443fe1026202ffc4131017ee209880bfe104c405fe0826207ffd972103dfecb9081ffe65c84097f32e4207ff59721005facb9081ffc65c840f7e32e4207ffd932103dfec99081ffe64c84077f3264207ff59321005fac99081ffc64c840f7e3264220ffd53210fffca990803fd54c843ffe2a64207ffd8f2103dfec79081ffe63c84117f31e4207ff58f21005fac79081ffc63c840f7e31e4220ffd4f21007fca790803fd53c8441fe29e421fffd0f21007fc8790803fd43c843ffe21e4202bf98b2103ffea59081ffe52c840ff72964207ff54b21007daa59081ffc52c840fffa164207ff90b2103ffa859081ffc42c840fff9964207ff8cb2103ffa659081ffc32c84057eb0e4202ffd4721017fca39080bfd51c8405fe28e4202ffd0721017fc839080bf641c8405fea0e4200fd50721017f8839080bff31c8405ff18e4202ff4c721017f8639080bfe21c8405f710e4202fd88721017f8439080bec21c840fffb064207ff9832100dfcc19081ffd60c84017eb064207ff1832100df8c190883ff50c843dff286421eff143210fffe819087bfe40c843dfe206421eff8c3210f7f8619081ffe20c840ffe1064202ffc4321017fc219080bfc10c8401ffb2a4200bfd95210effcca90812fe6548401feb2a4200bf595210eff8ca90812fc6548401ffb224200bfd91210e7fcc89080efe6448401feb224200bf591210e7f8c89080efc644843bffaa2421cff95121007faa890873fc5448401ffb1a4200bfd8d21007fcc690822fe6348401feb1a4200bf58d21007f8c690822fc634843bffa9a4200ff94d21007faa690877fc5348439f
  | 5 => 0x4551017f8a2a880b7c5154405fa28aa202ffd0551017fc82a880bf64154405fe20aa202ff8c551017f862a880bfe2154405fe10aa200ffd8151005fec0a88a7fe60544037f302a200ff5815114ff8c0a8806fc6054409ffa82a204dfd4151027fca0a8813fc5054455ffa02a229ff9015114ff880a88a7fe3054453fe182a229ff8815114ff840a880bff1054405ff082a202ff04151007fecaa0802ff6550401bfb2a82009fd9541147fccaa0812fe6550401feb2a8200bf59541147f8caa0812fc6550401be32a82049f19541015fec8a080fff5450407ff2a28203ef9514101ffaa8a0803bd5450407fe2a28200ffd8d41005fec6a0803fe6350401feb1a8200ff18d41045f8c6a08a3ff5350401ff29a8200ff54d41147f8a6a080fff4350407ff21a8200ef90d4101ffa86a080ffc4350407de21a8200ffd8941005fec4a0803fe6250401feb128200ff1894103df8c4a08a3ff5250401ff2928200ff54941147f8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe2128200ffcc941007fc64a0803fd3250401fe1928202bfd8541017fea2a080bfe5150405fb28a8202ff54541007eaa2a080bfc5150405ffa0a8203fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bfe3150405fb18a8202ff0c541017fc42a080bfc2150405fa10a8200ffd8141005fec0a089ffe60504037f3028200ff5814113ff8c0a0806fc6050451ffa828227ff9414113ff8a0a080fff4050407dfa028203ff9014101ff880a089ffe305044ffe1828227ff8814113ff840a080bff1050405fb8828202ff84141017f820a0823ff65cc4117fb2e6208ff99731025fccb988237e65cc4093f32e6208ff59731005facb988237d65cc4013eb2e6208ff19731045f8cb98823ff64cc4117fb266208ff9933101dfcc998823fd64cc4017eb266208ff19331045f8c99889bff54cc44bff2a66200ff5533112ff8a99880afe63cc411ffa9e6208ff94f31047bca798823fd53cc401eea9e6208ff14f31047fe8798897df43cc411ff21e6208ff50f31047f88798823dc43cc411ffb166208ff98b3103dfcc598823fd62cc4017eb166208ff18b31137fea598803fe52cc401fea966226ff14b3112ffe8598803fe42cc401fea166225ff10b31047fe6598823df32cc411ff1966208ff4cb31007ba6598823fc32cc4057eb0e6202ffd4731017fca39880bfd51cc405fe28e6202ffd0731017fc839880bfd41cc405fe20e6202ff8c731017bc639880bf631cc405fe18e6202f70c731017fc439880bfc21cc411ffb066208ff9833100dfcc198823fd60cc4017eb066208ff1833100df8c19889bff50cc449ff2866224ff1433112ffe8198893fe40cc449fe2066208ff8c331047f86198893fe20cc449fe1066202ffc4331017fc2198
  | 6 => 0x5fe32a6404bf19532007fec899002ff644c863ff3226403bf99132007fac899002fd644c863fe3226403bf19132197fea8990c7fe544c801feaa26431ff15132197fea699023fe534c801fea9a6408ff14d3218ffe8699023fe434c801fea1a6408ff10d32197fea49901ffe524c801fea926407ff1493218ffe849901ffe424c801f72126400ff50932007da849901ffc424c811ff9926408fbcc93203ffc649901fde324c801ffb0a6400bfd8532187fcc29900afe614c801feb0a6430ff18532015f8c2990cbff514c861ff28a6430ff1453218ffe82990c3fe414c861fe20a6430ff8c532047f862990c3fe214c80ffe10a6400ffd8132005fec0990bffe604c8037f3026400ff5813217ff8c099006fc604c865ffa82642fff9413217ff8a0990c7ff404c85fff202642fff1013217ffc6099023fc304c85fff1026407ff08132187fe20990bffe104c85ffe0826407ffd943203dfeca1901ffe650c8097f3286407df99432024fcca1901ffd650c8017eb286407df59432004faca1901ffc650c80f7e3286407ffd903203dfec81901ffe640c8077f3206407ef9903201d7cc81901ffd640c8017eb206407ef590320057ac81901ffc640c80f7e320642effd503216ffca819003fd540c85bfe2a06408bf98c32047fea619023fe530c811fea986408ff14c32047fe8619023fe430c811fea186408ff10c3203dfcc41901fff520c80fff2906407ff5483203ff8a41901fff420c80fff2106407ff5083203ff8841901fff320c80fef9906407ff8c83203fdc641901ffd320c80fee9906408fb4c83203ffec21901ffe610c8057f3086407fd98432015ecc21901ffd610c8017eb086407fd58432005eac21901ffc610c8057e308642effd4432167fca2190b3fc510c85bffa08642cff90432167f88219023fe310c811fe1886407ff8843203ff8421901fff600c80fff3006401bf9803203ff4c019006fa600c80ffeb006400bf5803203ff2c019002f9600c80ffe3006401bf18032177fea0190affe500c857fe280642dffd003215ffc80190affc400c811ff1806408ff0c03203ffc401901ffc200c859ff880642bff8403215ff8201900aff6554401ffb22a200bfd9151157fcc8a880efe6454401feb22a22aff1915101df8c8a8813ff5454409ff2a2a204ff55151027f8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc63544117e31aa204ffd4d51027fca6a8813fd5354409fe29aa22affd0d51007fc86a8803fd4354455fe21aa200ffd8951005fec4a8803fe6254401feb12a200ff1895103df8c4a8813ff5254409bfa92a204ff94951027faa4a88037d5254409fe292a22affd0951007fc84a8803fd4254455fe212a200ffcc951007fc64a8803fd3254401fe192a202bfd8551017fea2a8813f75154405ff28aa202df9
  | 7 => 0xa10f7fc5350807ffa1a8403efd0d4201ffc86a100ffd4350801dea1a8403ff10d4201dfec4a10f7ff525080fff2928400fb94942007faa4a1003ed525080ffe2928403ffd094201fde84a101ffe425080fdf2128407ff1094203f7884a100fec4250801ffb0a8400bfd85421e7fcc2a100afe6150801feb0a843cff18542015f8c2a10f7ff5150879ff28a843cff1454201ffe82a100fbf4150807ff20a8403ff105421e7fc62a10f3fc3150879ff10a843cfb8854203ff842a10f3ec2150801ffb028400bfd81421dffcc0a1006fe6050801feb02843bff1814200df8c0a10f7ff5050877ff282843bff1414201ffe80a100fbf4050807ff2028403ff101421dffc60a10effc3050877ff1028407ff081421e7fe20a10effe1050877fe0828408ffd9732045fecb99023fe65cc8097f32e6408ff59732005facb99023fc65cc8117e32e6408ffd9332045fec999023fe64cc8077f3266408ff59332005fac999023fc64cc8117e326643affd53321cffca999003fd54cc873fe2a66408ffd4f32047fca799023fd53cc811fe29e6408ffd0f32047fc8799023fd43cc811fe21e643affd4b3203ffca599003fd52cc80ffe2966439ffd0b3203ffc8599003fd42cc80ffe2166408ffd8732047fcc39900afe61cc811feb0e6400bf58732047f8c39900afc61cc875ffa8e6438ff947321c7f8a3990e7ff41cc871ff20e6438ff10732047fc6399023fc31cc871ff10e6407ff08732047fec199023fe60cc8037f3066408ff58332005fac199023fc60cc8037e306643affd43321bffca1990dffc50cc873ffa066437ff903321bff88199023fe30cc811fe1866437ff8833203ff841990e3ff10cc86fff0866437ff0433203ffecb1901eff658c80fff32c6404bf9963203ffacb19002fd658c80ffe32c6407bf1963203ffec91901eff648c80fff3246403bf9923203ffac919002fd648c80ffe3246407bf192321b7fea9190d7fe548c801feaa46435ff15232005fac7190dbff538c811ff29c6400ff54e32047f8a7190d7ff438c811ff21c6400ff50e32047f8871901efe628c80fffa946407ff94a3203ffaa51901ffc528c80fffa146407ff90a3203fdc851901ffd428c801f6a146407ff10a3203ffe651901fdf328c811f79946407ffd863203ffcc31900afe618c80ffeb0c6400bf5863203ff8c31900afc618c86dffa8c6434ff946321a7f8a3190d7ff418c869ff20c6434ff106321a7fc6319023fc318c80fff10c6407ff0863203ffec11901ffe608c8037f3046407ff58232005fac11901ffc608c8037e3046436ffd423219ffca1190cffc508c86bffa046433ff9023219ff881190cffe308c811fe1846407ff8823203ff841190d3ff108c867ff0846433ff04232007feca99002ff654c865ff32a6404bf99532007faca99002fd654c86
  | 8 => 0xf98652015fcc32901ffd61948017eb0ca407ff18652015f8c329013ff5194809ff28ca404ff14652237fe8329117fe419488bfe20ca445ff8c65222ff8632901ffe219480ffe10ca407ffd825203ffcc129006fe609480ffeb04a400bf5825203ff8c129006fc6094809ffa84a404dfd4252027fca129013fc509488dffa04a444ff90252227f88129113fe3094889fe184a407ff8825203ff84129117ff1094889ff084a444ff0425203dfecaa9003ff64548017fb22a443ff9915201dfcc8a9003fd6454887fe322a403bf19152027fea8a9013fe5454887bf2a2a404ff55152027f8a8a90137c5454801ffb1aa400bfd8d52007fcc6a9003fd6354801fe31aa408bf18d52027fea6a90137f5354809ff29aa404ff54d52006faa6a9013fc5354887ffa1aa400ff90d52007fa86a910ffc43548097fb12a404ffd4952027dea4a901ffe525480fbf292a407ff1495203ef8a4a9013ec5254887ffa12a407ff10952007fec2a9002ff6154885ff30aa402bf98552007fac2a910bfc61548057e30aa404ffd4552026fea2a9013fe5154809fe28aa443ffd0552217fc82a910bfc4154885ff18aa442ff0c552217fc42a901ffc2154801ffb02a400bfd815220ffcc0a9006fe6054801feb02a441ff1815200df8c0a9013ff5054809bfa82a404ff94152027f8a0a910fff4054883ff202a441ff1015220ffc60a9107fc3054883ff102a407ff08152217fe20a9107fe1054883fe082a407ffd964203dfecb2101ffe65908097f32c8407df99642024fccb2101ffd65908017eb2c8407df59642004facb2101ffc659080f7e32c8403bf5924201ffea92100ffe5490807feaa48403ff1524203ffec72101ffe63908117f31c8407ff58e42005fac72101ffc6390881ffa9c8400ff94e42007faa721103fc5390807ffa1c8403ff90e4201ffa872100ffc439080f7f3148407ffd4a4203ffca52101fee529080ffea948400fb54a4203ff8a52101fff429080fdfa148403fbd0a4203ff8852101fec429080fffb0c8407ff98642015fcc32101ffd61908017eb0c8407ff18642015f8c321103ff519087fff28c843fff1464201ffe832100ffe4190807fe20c843fff8c6421fff8632101ffe219087ff710c8407ff0864203fd8432101fff609080fff3048401bf9824203ffac121002fd609080ffe3048401bf18242207fea1210fbfe509087dfe2848403ffd024201ffc812100ffc409087dff184843eff0c24203ffc412101ffc209087fff884843eff842421f7f82121003ff65508017fb2a843dff99542025fccaa1003fd65508017eb2a843dff19542025f8caa101eff6450807ffaa2843defd514201ffca8a100ffd5450807fe2a28403ef15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1022fc635087bffa9a8400ff94d42007faa6
  | 9 => 0xc09ffa8aa604ff94553276fca2a9813fc5154c09be28aa64fffd0553277fc82a993bfc4154c9dff18aa608ff0c553277fc42a993bfc2154c01ffb02a600bfd815326ffcc0a9806fe6054c01feb02a64dff1815300df8c0a9813ff5054c09bfa82a604ff94153027f8a0a993fff4054c9bff202a64dff1015326ffc60a9823fc3054c9bff102a64dff08153277fe20a9937fe1054c9bfe082a608ffd9643045fecb21823fe6590c097f32c8608ff59643005facb21823fc6590c117e32c8603bf5924301ffea92180ffe5490c07feaa48603ff15243045fcc721823ff5390c11ff29c8608f794e43047faa721803dd5390c11fe29c8608ffd0e430477e872180fdf4390c11fe21c8608f710e43047fec521823fe6290c0f7f3148608ff58a43005fac521823fc6290c99ffa94864cff14a4301ffe852180ffc4290c11ffb0c8608ff98643015fcc321823fd6190c017eb0c8608ff18643015f8c321933ff5190c97ff28c864bff1464301ffe832180fbf4190c07ff20c8603ff10643047fc6321823fc3190c97ff10c864bff08643047fec121823fe6090c037f3048608ff58243005fac121823fc6090c037e304864cffd4243257fca12192bfc5090c07ffa048603ff9024301ff88121823fe3090c11fe184864aff88243257f8412192fff1090c95ff084864aff04243007fecaa1802ff6550c93ff32a8604bf99543007facaa1802fd6550c93fe32a8604bf19543045fec8a180fff5450c07ff2a28603ff5514301ff8a8a180eff6350c93ffa9a8608ff94d43007bca6a1803fd5350c01eea9a8608ff14d4301ffe86a180fdf4350c11ff21a8608ef90d43047f886a1823bc4350c07ee21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894303df8c4a1927ff5250c93fe2928603ffd094301f7e84a180ffc4250c01ffb0a8600bfd8543247fcc2a180afe6150c01feb0a8648ff18543015f8c2a1927ff5150c91ff28a8648ff1454301ffe82a180ffe4150c07fe20a8648ff8c543047f862a1923fe2150c91fe10a8600ffd8143005fec0a191ffe6050c037f3028600ff5814323ff8c0a1806fc6050c93ffa828647ff9414323ff8a0a180fff4050c07dfa028603ff9014301ff880a191ffe3050c11fe1828647ff8814323ff840a1923ff1050c8fff0828647ff04143025facb2901fff649480fff324a403bf9925203f7cc92900ebe649480ffeb24a400bf5925203f7ac929002bd649480ffe324a407bf19252027fea929013fe5494809feaa4a404ff1525203ffec72901ffe63948117f31ca407ff58e52005fac72901ffc6394809ffa9ca404ff94e52027faa729013fc539488dffa1ca400ff90e52007fa872911bfc439480f7f314a407ffd4a5203efea529013ef529480ffe294a407fb14a5203ffe852901ffc429480fffb0ca407f
  | 10 => 0x5801e00c00000201400a00000400000002600200001800002000000a00400000000e00200201400c01200002c00000a03000000000204400e00602000000800800000c00000400a00600400000000a02000400400200400600800000000a02801e00400e00800200a00000e00000e00200601201400a00800400000202200600000000000400000400a00402200800200800002600400200805c00000000a00400200200202801401400600e02200403bfd955401dfec8aa00fff5455009dfaa2a803ff9515401efca8aa00ffc5455007be2a2a803ef15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa022fc6355009ffa9aa804dfd4d54027f8a6aa00fff4355007fe21aa800ffd8954005fec4aa003fe6255001feb12a800ff1895403df8c4aa013ff5255009fe292a803ffd095401ff884aa003ff61550017fb0aa854ff98554015fcc2aa003fd61550a9fe30aa802bf18554027fea2aa013fe5155009fe28aa803ffd055401f7e82aa00ffe4155007fe20aa854ff8c5542a7f862aa153fe21550a9fe10aa800ffd8154005fec0aa14ffe60550037f302a800ff5815429ff8c0aa006fc6055009ffa82a804dfd4154027fca0aa013fc5055007ffa02a803ff9015401ff880aa14ffe30550a7fe182a853ff8815429ff840aa153ff10550a7ff082a853ff04154025facb29823ff6494c11ff324a603bf99253047fac929802fd6494c11fe324a608bf19253027fea929813fe5494c09feaa4a604ff15253045fcc729823ff5394c11bfa9ca604f7d4e53047f8a729823dc5394c11ffa1ca608ff10e53047fec529823fe6294c0f7f314a608ff58a53005fac529823fc6294c09ffa94a604ff14a53297fe852994bfc4294c11ffb0ca608ff98653015fcc329823f66194c057b30ca608ff58653005fac329823f56194c017ab0ca608ff18653015f8c329813ff5194c09ff28ca604ff14653297fe8329947fe4194ca3fe20ca608ff8c653047f86329947fe2194ca3fe10ca608ffd8253047fcc129806fe6094c11feb04a600bf58253047f8c129806fc6094c09ffa84a604dfd4253027fca129813fc5094ca5ffa04a650ff90253287f88129823fe3094c11fe184a650ff88253287f84129947ff1094ca1ff084a650ff04253045fecaa9803ff6454c017fb22a64fff9915301dfcc8a9803fd6454c9ffe322a603bf19153027fea8a98137f5454c09ff2a2a604ff55153006faa8a9813fc5454c097fb1aa604ffd4d53027bea6a9823fe5354c11bf29aa608ff14d53046f8a6a9813dc5354c9fffa1aa608ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a981efc6254c09ffa92a604dfd4953027f8a4a993fff4254c9ffe212a600ffd8553005fec2a993bfe6154c057f30aa600ff58553277f8c2a980afc6154
  | 11 => 0x47d800003000000000203800000000200001001a00401800000201e00400c03600600202400a03200201801403800401400401000000200000a01e00200200c00400a00600800c03200e02200000400000800401e00000600c00800003000200200600400e00201c07a01c00001000600401000001000000000400600400200200002601401601800000600600200e00200200000000000601403e00000600000c00000201800000000400200800200002800c01a01e01800804000001c01c04c01600400000a00200c00a00000800000000a00200401400200000600000a00200600e00002201400401400200200400600001401000600200600601800000201400000c00000000c00000002c01400a01800000000003800800200201000800200800600000a00400001001801e00005a00000000401400400201e01200200400000004c00200200001001400400200e00000400000400c00000000800800c00003e00200000801800a05600001c00a00601c00c00200400c00000601800e00400400e00000a01600200e00000402e01600a00e00201a01e01400002000200000a04000005600e00c01001600401c00000400201a00200600800202800000000000001400a00000004e00000000000800800000400400001a01000200000200000000400000200200600201007e00002000000401000201200000000e01000000200200000400000001400400001800000a00201401600000000600400400e00200a00401600200400602000000000000600001000800001000000000000001600200000a00400000006000201c00600600401c00001000000600200800000000200401401800002c01400400000202600000401400001000200400001401201200000200800403200800800000a00200a04402e02400600200000001400000800e00000000000001605a00200000200801200200200406000001800000802200000000400202400a02600600000200000e00001a00003000000e00000601200e00801801a00600200000e00601c00401600000000001c02600001a00600400c00000800600800201802a00401200402200600c03a02c00200400800000600000400003a00000800a00200a01a00002801600000400000201400801000000800200600000c00202200e01a00000600600200a00001e01000e00a00000401003000001200000000200000000000002402a02004000200600800400000004e00400000a00e00402200002200000400c00401400002a00a02e00200200000600202e00000000200200600201600600001000401200000201000000401000000001600c00203c00000400602a00a01200002c01200a00800000600c00200000a02400400800600002000000e01a0000000020240020100240120120160000040040
  | 12 => 0x3a48d317496083f267600021a40004c11888ef42948fc265147872a8932fc978c51a6f9363112c52c3a643a9da40006e914b8538a102220d2000000000004a02e8a747ec169935882a0002350dac5ee8cb2dc1a44000000000039462a000000000067800023aa394b3063907e1124a0e00000b03b000068300000000003741379ed0000677232829011286a0000000cf60000000000dac4e51de00004e200000014647ea00004610080002fa000109c0000003d088dcd5c8e40a696205584bc3401c784c40dc4748d3c86856c44c936caa64682281114bbe4e42909af022832104880003ae48e1c6000000049c000000023626134f193c0000001808000000000000101800007828b00007964ad0000aa800000046f869469200023700000005c800000004e00f007785f8cde4a01da0090be85d62b48de0b8058b39b018418435a2951d40eea3d24598524e6468e31d86589107303b9800901c68f1c917e8c7e3c5379002c7da8b428a9e440ee1654110294000885000222514658e36c10ec82071c38811ec7bc4bd00009540a464e41a847c0000002ec95a000000000000000006af07ca510cc48f102a000033641600006c874a2541c71c840000c348c000073a00035f1f3d2381483cb99410346ab00005dcfc078f0002520ce60000000af86ac7d90050e7834238a117000000010902595200000003380000e464950b4925cf166333e280010545dd00003c40005fe453027c00004515e14d000081847c9fb80000000001c3850494f00000000000000001bf40000000a79c5017c0f63988000c800003998a2c98e1f63928001060834000000000024347f8b8903c4f31650e34000000343100c00056126a1790a147160000d905c614725211f8ca43323fba168136012264057c8a265f3c29fe069425105009c89e40301bd0000b0c50205fa320fc42603cd134003823f45016c483e3a44791d04ebe000000000112267924c8ae00929170001a54e3200030f096c726327085097c9c26e326c8b0cfb429a3d72420cf42ef35b001c26e9033f306740001bb432a4d09fc19a387908428a63701f02c91109241370000d381a30000838d280001dc930c8b88af026246c00065a000000034e89718614e10e60094668000420000477000000000000012c01722ae32a96590c64e80000b20000000000000128230d00f80004da89a3e182b800038f00009784184c50ff84e48020003138e2c00000016fa2ed0f2665000050c5b400016c0b3c786000000031400084300021fc000361000155c00034b03395040008f50e620843ce8fd00024010000082a824b45726ad3589aa0e3407f000169c598050015878917c8c639d21110180002d4800000041b0000000996100040910913c39f3a59374f920000001c6c000954000220000028e0000000000000
  | 13 => 0x29108ec4685fb15f81000003e420f2240c063f236500fc07026b1a6918463a15729b1c482620003eb8b54f1864c2418000f6c55447d08500000003be800000000000000000006410a21f2ce1029416380001b200000000a92460003f380001085920000f391a486724900003882d20001e600006510b680000f465b00d077cfc2000302800000047f13b00010e40003f800000000000b080003183673fa00009b861b3ae000000089824c1eac000001000165400000000021340005c614c0238ce47c430e0d18eba8ac154a1a0f5833b00e963000042300000003c81e5000088000089222c8ea80000002508bcd0be000000000077007513f11685fc10e00005605d66c91fa08c400031300000003cc00006b06fc0003622aa800000015d10221389fa00006d249454a00027b000041094300022c80003550e4018000037d08080007c40002f70c1507660e299800000030900004f0000000059800085e0c8070a1800002771cca1840000004550000dc89472e380000000002168f18a084e045e093054858436f0f8cc7a02306b89ec79e1fe34c9b8011e4ea3bd00000006c70271a6113600000012f90806a21ff80000da4a531a0000a8483c0b906d0bce06e4a71888ddc0e91d5813501602500024f00004640ea07701920761969b340ba43844e07750f892e00000011720323179f009ee4d34639dc4b3c777330a52ca0254e345872cbca28741d0110de06090991d3400095a0e0984c2e853c2d9091806c2de3f992281e629b25da4bc7a68023bc2064b4a77f0f40ecd29417f0000f5800059a00011c468e95524320440008252ac1ae4000000115112819446b06f08987006df05a8000fb68d426c0868c7c8d03708c70d360732d5145c00809e00005acebc00018d8000000744402a2184021b60000000cdc73d0000e504e819c0001a9129851800015a800035300007808fa448000000040e04800020240007a0000068923233806598747c20003550900ad67ad0b5000067a00015d8c2049a85700000002300001d81eccea800040080002d05d53948200fa27400000000d8844441613c08b632e000025c1e83f10c01a1506680444b1bf043a0871fb00e81dc000000040886041a3679ae8a1c0003ad986800000045680001b07aa2b800000000df18800000000001e600000002d041f86e86542c40001d2400c074443a190a8817d0f58000e8c00037f92c46e64cf057916077e95711290cc69093f0c5971400006605b06f00404890071d68b921bd30c98904042523ca1c34c1e1ea3d487cc2d800000000008008eb045a4682f28503b3822838e4cc18c237033c3d50e8837404c2f6467a150cfa2ee08d0b6c00000522ba00c7dc0db2a296f8b6a4ee0c814bc0e46c51ae92a47020001a7000000000000000600005c137508791bc000000000
  | 14 => 0x88000000474167c0000001e89ec097022419d1a30d667a31239c8851419839604fd20885c17f89a08e032806690508381350998b2c3947580fd8fcc59c3af34d0c5c43072430ba11c4363be3d39e00c847151e80f807d45562dc81691607cd4159b44e4c0b01dd01451800864610000cd67883249ac800095606989a8fa85672b194401f65300539b4c8aa372058a080c501d005119b08648064768418a2848036b94c82440004558db000076a0000800e686fb2468db8e847b90a88a40abc0000000d60562093414253400003c306000000000021700000000001f3041c0000222ef21740001190001cec8cc0001cb8000000000461a36cf2a72e36aa01c2160001b0103528c0000000000f7a83200014f904e0000002120c9a78d48898b0e8a0000001db800054a09787f41ee1c30000000fb049402e0000d4008820c9c2800092c0001d0c00085e454a05c8be8c52691c08b4200010f80008da81f07f97e0d4c29d000094058a00000012100000150000d100000001890d9495400044780006e287438580006566251b693b12167f1110a4ec1a836f1279770784958000097527c0000eb0ff4000398000148c92c06c197800062800011610a4fda92221414349be00041710807d20032960d64bc267f07593f12b61f52d7947047c85100023740002360000b700001150860000ec65810000458f6a0001a900010e215a0468e18000134429103c64013605c19180d674c25d181cf444ab00c87b92661f006a873c6a0513438081427a04317503e0ba06040a1000041a53d34502410f62990000d1418e00016a02dc3f054b0002058acc6bb17817d4bd62f10000f9441e27904ca544bec3062cd8000d4e00001a80009ce66d17c00000005a229280000000000000ff91424b6393828cfe41d94731bd44ce47800009b002e57100003b40000002bd896520e2a625718e8aa202f0001f1d13e0000a080002dc00012c0618dda7762ba1c800000000000aa0000000000239c0004b541e800000000021d11e89d200011d1b0400081300001c120a00048787c80000000980d4400066a000153ca520000239cf80005d13c1a4c8e6a3761921a2040c7ce0250a9cc1a0002bf8000db46630000a4ca5a5a6183a2e0fbe1b1000163c0003752b92424f263851aa000019c4082db1f1803c8ca21b80002980002f3000032e0294a4947c2c86692e103c899282944e98c40de35f4951dd0ea41543729574f3811d43106dcb2013b2059c30c243634689f0870e441019800086c0000549bdc0000f50001f412a04d520c2290c10140000047102437c23a018d07c95349812742582163cf033c3100003788000d7007107f0a042967f920e85e80003962ed00000001b30000e68f0806900017f000030f19ca4d8e1200032281ecbb623508422dc28c01b000000060400
  | 15 => 0x5739b9474b9600009187d120c0000c2914cba40003339f204b488100000002bc29135f8a10ade0003468ea00000003a7094c0006ce41c80000008f70000000d2600000000003bc0000541b6c46629213202b00001670000000b9444e3be23040002f40e70cdc0006a10000040f32831000098ccf01ec11913d4e2e4cd30518f0d8091300009f11041823e5000056a0003191d4cc2c8e211e80c40001da3fd9ee08f81f11ec1bf8e3e00002c9d5d14479d0000a8cdc48781610a78f4c3260a99534e7e5261f3a1d8df400020521f418800000010b049692b0b982ec2f64a31ad85f00003f026120e000043512494248a857c33e1a5d26a0000d6949c2c05a400000ec4b865e0000000e0c0000000000a982832ad1400dd61af3978ab48242481db97a4b4600000024f4a480002be9ce12b86dc1098a3c15a0fa2d8061cb585ec48621f86cc01424f0b5c5102e4000170ca6a00016c9038dec6a347c000039a00000020552b2000223000000000038c000111c22900020912143a93a5000000030013e908850a00031b1aa479a6b400005543c60000000f7000087a0001edc8c44da471a118a223c745ea48421a0c64541ad474e3c90c9800000086b2c895909220001d8803c0000000889a1070408339e202800088b0000000ca812d000085c7d837915e8000e3a00044195e00005520922158b12275000000000002e00000007760000000000ffe000081849cbe257521f0000000000000205087844f021000000091e2f680347ae000000000046000000000002525bb00022290460bc0900da400000018f800054400000024e521c06a0000b580001c629c856445e0652e988540008840000fbd06e18a2bb0b940003a1114165c79075547f0f28f2427346d0f0123a0852ff944884a5034041d642b6658203933863415c0001850f481121591800cea18901406491c04a23058e10ae66182b28ec817a12108285980002782d6a0343b04d700000008127fe0001ea05ce0000000d0c6668770000b840ae19f1250b248a426622b05c00007812201b305e45b30231ab0ef665600021552522fb13d17c903a4ed1960994ce874f14a8bb117412b48b0ff07b62230d802585806351d68ae888e1714938000ff80003c390f506c0c0341000062c64800004f80000e819a1a047444e61169f7450c0004a91adc0000000001f4ca166f8374156c94c0001f580000000000001f3000002d000180838077e2461fa90da4f42b11a40358000031000000000015982981680000001970ef200034380000004e20b78c78d3a7e406614180008ea02f89a40007112e79fa10a6000000000000012e3ee0864fde2380490304c0c8e127f8adc75c24112101a000035c2621efc250104253a16d16c0390d49ff466c8591821dc01d417631702841a469604d12dcec21aa4880c
  | 16 => 0xdbca8600000000000000000001ef8d4a6ef000101056093148690a80008941d1800004237b00000004ac0002319cb4dcc1ae1bb96642c439c000000120246f08b87144566890ab00011ae4110001884bc436a46606d4e547d2000009ccae0002de8000c708d80f090e4ab23310ca8ed884c786323975000000000019980183901c1998073600021f92152740aa3821fe800000008f1ca0b560580d30cd4a3427f0ba8d009161381579af51ec76d315844cc201db36100000007bc00013ac4780003ef07a4bee5c41fc893868256d16300010d85b704e01f856812a36586ac8d86303b91f0464a0373f59378e905f300014300008583fb0ba01a01b832e9f9456c5fd49400000000981fd000000028907200009f634c0001fa431e8ef00024500002122398000c3e2e60d404e8b146b00c69d441cc57940e18045f872b25ca198dba5873b28c38ec009d1018b044389020001e7c3067f54379b9cc887af3828000c860000e10000f6400000007b41a25cc0558000da00001669e0800005317692a05ea20b2218bf489800036180008ba0002a300000005cd240a3b02f05d729701544225bc2410000b7e70018580008f2000000211516a18e00000000000000000f689f400000002080000001bf0000000405150000000057700022fcde83b529580003720001048001270000000043d036000000130048a0001af04947221911050a3114e4af2c6960000038818500d0d906ec25a07bcc46199310210837c8493b122944884312bd01f4ecc0002d70000f621500002040a0a00048a800104c3c1479838ce268f020b8a7c0006d22a4819000000036c80000005ef00011788182f9000095c00000025f96d11b20fd49b800000000000000006d04ef2d001050822d10001990000528000164ccd08b10ca07e80f2000425109128a54716e80005566d42ae00003a68c903e0000a624f83b40a8492657e493000005829c000000009e3422f4000000000000000007ba0560002358ed6583088178007a9421ea06045c01523dd0000c9662900022540008ae0001180f1480f380800109e6260000754c227d61fd80000b600029010ac0000003491e6cbe07892b01eecc9476c46218a892053f19f839c8ce4d124d9614a3694046a889cca67d5008a12d1188ce1f40f107b27e318c8cc0a6e44d0001d906fe0002b70eb0a8000000012cd1e801300007f08d288d4890000ce20002ce0000b283f80b19c0c91e49f24d1674f2c00038391c80000004370c0c71233e417a47c0000002e7000090e0e23c7000105a5ea02f11d909800000008e47be00020980003404e30001bcc00000049012b0cfc00000016e80000002d41d589e21c91919e949f26151948fdc0003a0000025400028000000003081262878000bb0000070000000079023b80000004c6000157c3ee3
  | 17 => 0x7470001a7ce7265925900006e062d29d9
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x2204c51000df4764851003ef4764851000cf47648510005f77448510005f57448510005f77348510005f57348510006f76348510006f56348510015f77248510017e77248510007e7624851003ef6624851003ef46248510007e46248510007e65248510007e55248510007f3704851000df6704851000df470485100dff07048510016f76048510017f360485100df7750485100dff250485100df7550485100dfe720485100dff220485100dfe52048510015f87654110026f87654110014f8765411000dfb755411000f7b75541100077b6554110026fa6554110026f86554110037786554110006fb6454110006f964541100377b54541102af7a54541100077954541100377854541100377b53541100077a5354110007795354110037785354110005fb72541100377b52541100077a5254110007795254110037785254110007f37154110015fa7154110015f871541100bff0715411000efb615411000ff361541100bf7b51541100bf7a51541100bf7951541100bf7851541100bff24154110007f141541100bff23154110007f131541100bff22154110007f121541100377b76541100267b76541100bf7876541100267876541100077b74541102af7a74541100077974541102af7874541100077b64541100067b64541102af7a64541100077964541100067964541102af7864541100077b73541100077a73541100077973541100077873541100077b63541100077a63541100077963541100077863541102af7b43541100077a43541100077943541102af7843541100077b72541100077a72541100077972541100077872541100077b62541100077a62541100077962541100077862541102af7b42541100077a42541100077942541102af7842541100077b32541100077a32541100077932541100077832541100bf7b71541100077371541100bf7a71541100bf7971541100bf7871541100bf70715411000f7b615411000e7b615411000f7361541100bf7b41541100bf7a41541100bf7241541100bf7941541100077141541100bf7841541100bf7b31541100bf7a31541100bf7231541100bf7931541100077131541100bf7831541100bf7b21541100bf7a21541100bf7221541100bf7921541100077121541100bf782154110015f8764811003ef87648110014f87648110005fb7548110005f97548110006fb6348110006f9634811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e86248110007ea4248110007e94248110007ea3248110007e93248110007f37148110015fa7148110015f8714811004ff0714811000efb614811000ff3614811004ff24148110007f1414811004ff23148110007f1314811004feb214811004ff2214811004fe92148110007f12148110007e12148110
  | 1 => 0x8910004ff7358910044fc7358910006ef72589100f4ff7158910006f7715891004ef631589100dcff7058910006fb70589100de7f50589100de7d50589102c4fe76189100357e75189100057d751891002dbe7418910005bd7418910005de7318910005dd731891003eee6218910006ed621891003cff7694910004fe7694910004fd769491003cfc769491002dbe7494910005bd7494910015f67194910005f5719491000dfa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100267e65549100067d655491000dfa705491003cff7690910004fe7690910004fd769091003cfc76909100357e75909100057d7590910006ef629091003eec6290910015f67190910005f571909101ffe6219091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc765091001ebe6450910006bd6450910006ef625091003eec6250910015f671509101e7e62150910044ff76cc910004fe76cc910004fd76cc910044fc76cc910046de63cc910006dd63cc910006ef62cc91003eec62cc910015f671cc910005f571cc91003cff768c910004fe768c910004fd768c91003cfc768c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c910046de634c910006dd634c910015f6714c91003cff760c910004fe760c910004fd760c91003cfc760c9100357e750c9100057d750c91002dbe740c910005bd740c910006ef620c91003eec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df4765051001ef4765051000cf47650510007777550510007747550510006f76550510006f56550510015f77450510017b77450510007b7645051001ef6645051001ef4645051002fb4645051002fb65450510007b55450510005f77350510006f76350510006f56350510007b6435051002fb44350510005f772505102bef662505102bef4625051002fb74250510007b54250510007f3705051000df6705051000df4705051013ff07050510016f76050510017f3605051013f77505051013ff2505051013f75505051013fb7405051013fb5405051013ff2205051000df4764c510046f4764c51000cf4764c51011ef6654c51011ef4654c510005f7744c510005f5744c510006f7644c510006f5644c510015f7734c510017d7734c510007d7634c510046f6634c510046f4634c510007d4634c510007d6534c510007d5534c5102b7d7434c5102b7d4434c510005f7724c510006f7624c510006f5624c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c51010ff0704c510016f7604c510017f3604c51010f77504c51010ff2504c51010f75504c51010fd7304c51010fd5304c51010ff
  | 2 => 0x4fd72d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102febf41d91102febd41d91102fef631d9110014ff70d911000cfe70d9110014fd70d911000cfc70d91102ee7f50d91102eefa50d91102ee7d50d91102eebf40d91102eebd40d911001cff76591100057f75591100357c755911002ebc64591102e5f771591102f5fb7059110004ff75591100067f75591100047f7559110024fe7559110024fc75591100067c75591100247c75591102ecff7459110006bf7459110004ff7359110044fc7359110004ff725911003cfc725911002ebf42591102e4ff7159110006f771591100aef6315911013cff7059110006fb705911013e7f505911013efa505911013e7d5059110004ff7655110004fe7655110004fd7655110004fc7655110044fe76d8d10024fe75d8d10004fd75d8d10024fc75d8d1001cfe74d8d10004fd74d8d1001cfc74d8d1003cfe72d8d10004fd72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d102def641d8d102dedf31d8d102dedd31d8d102def621d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d102d67f50d8d102d67d50d8d102d6df30d8d102d6dd30d8d102d6fa20d8d1010cfd7698d100357e7598d100057d7598d10006df6398d1010df57198d1007df97098d10044ff7658d10005ef7258d10005ec7258d10125f77158d10095fb7058d10004ff7558d10024fe7558d10024fc7558d10004ff7458d1001cfe7458d1001cfc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d10124ff7158d10006f77158d1007ef64158d1007ef62158d1010cff7058d10006fb7058d1010e7f5058d1010e7d5058d1010efa2058d102d4fe7618d10046de6318d10006dd6318d10044ff7694d10004fe7694d10004fd7694d10044fc7694d10015f67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10044ff7690d10004fe7690d10004fd7690d10044fc7690d10015f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10015f67150d1003cfe76d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910044fe73d8910004fd73d891000cff71d8910014fe71d891000cfd71d8910014fc71d89102cef631d89102ceef21d89102ceed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d89102c67f50d89102c67d50d89102c6ef20d89102c6ed20d89100dcfd7698910006ef62989100ddf5719891004df9709891003cff76589100f5f77158910065fb7058910004ff7558910024fe7558910024fc7558910004ff745891001cfe745891001cfc745
  | 3 => 0xd6450520007ad4250520006f76150520016f46150520004fe76cc520004fd76cc520044fc76cc52005d7e75cc5200057d75cc520046de63cc520006dd63cc52003dee72cc520005ed72cc520007cd32cc52000dfa70cc520005f970cc520004ff764c520004fe764c520004fc764c520046de634c520006dd634c520007cd324c520016f6614c52000dfa704c52031dee76c852003eee76c8520006ef65c8520006ed65c852003def74c8520005ed74c852003def73c8520005ed73c85200dded71c8520016ee61c8520016ec61c852004fe641c8520007e541c852003feb70c852000dee70c852000dec70c852003fe870c852003eef60c852003feb60c85200f76f50c85200f76d50c85200f7ea30c85200f7ea10c852000cfc7648520006f76148520016f4614852003fe42148520005fb704852000df8704852003fe8204852000dec7648520016ec764852000cec7648520006ef6548520006ed6548520005ef7448520005ed7448520005ef7348520005ed734852003def714852003fe77148520007e76148520016ee6148520016ec614852004fe4614852004fe63148520007e53148520007eb704852000dee704852000dec70485200dfe8704852003eef604852003feb60485200df6f50485200df6d50485200dfea30485200dfe710485200dfea104852003df8764c120046f8764c12003cf8764c120006fb644c120006f9644c12000dfb734c12000fdb734c120007db634c120046fa634c120046f8634c120007d8634c120007da434c120007d9434c120007eb724c12003dfa724c12003df8724c120007e8724c12000efb624c12000feb624c120007ea424c120007e9424c120007db324c120007ea324c120007d9324c120007e9324c120007c9324c120005fb714c120007db314c120007d9314c120007eb214c120007e9214c120024fe76d95100367e65d951014cfd75d951001cfe74d9510004fd74d951001cfc74d95100067e54d95100367c54d9510044fe73d9510004fd73d95100367f53d951003cfe72d9510004fd72d951000cff71d9510014fe71d951000cfd71d9510014fc71d95103167f51d95103167d51d9510316f641d9510014ff70d951000cfe70d9510014fd70d951000cfc70d951030e7f50d951030e7d50d9510024ff76595100367c6559510305f771595100cdfb705951030cff75595100067f7559510004ff745951001cfe745951001cfc7459510004ff7359510044fc7359510004ff725951003cfc72595100367f5259510304ff7159510006f771595100be7e51595100be7c51595100bef6415951014cff7059510006fb705951014e7f505951014e7d505951001cfe76d911002ebe64d9110024fe75d9110004fd75d9110024fc75d911013cfd74d9110044fe73d9110004fd73d911003cfe72d9110
  | 4 => 0x492020cfd765492000cfc76549200067f65549200267c6554920005fb705492000df8705492003fe8205492032dee769092003eee769092003f6e759092003f6d7590920006ef6590920006ed65909201dded749092001eee649092001eec6490920005ed7390920006ef6390920006ed6390920005ed71909201feee61909201feec619092000dee709092000dec709092003eef609092003feb60909201f76f50909201f76d50909201f7ea30909201f7ea109092001cff765092000cfe76509201dcfd765092000cfc7650920006bf645092001ebc645092003fac4250920005fb705092000df8705092000dec765092001eec765092000cec7650920006ef6550920006ed655092003def745092003faf7450920007af645092001eee645092001eec6450920057ac6450920327af5450920057ac5450920005ef7350920006ef6350920006ed6350920057af4350920007ad4350920005ef71509201e6ee61509201e6ec6150920057af4150920007eb705092000dee705092000dec70509201dfe8705092000de8705092003eef605092003feb60509201df6f50509201df6d50509201dfaf40509201dfad40509201dfea30509201dfea105092000cfe76cc92000cfc76cc920006df63cc920046dc63cc92000dfa70cc920005f970cc92015dee768c92003eee768c92003def748c920005ed748c920006ef648c920006ed648c92017ded738c920046ee638c920046ec638c920005ed718c92003feb708c92000dee708c92000dec708c92003fe8708c92003eef608c92003feb608c92019f6f508c92019f6d508c92019fea308c92019fea108c920044ff764c92000cfe764c92017cfd764c92000cfc764c920006df634c920046dc634c92003fcc324c920005fb704c92000df8704c92003fe8204c92000dec764c920046ec764c92000cec764c920005ef744c920005ed744c920006ef644c920006ed644c92003def734c92003fcf734c920007cf634c920046ee634c920046ec634c920007cc634c920005ef714c920007eb704c92000dee704c92000dec704c92017fe8704c92003eef604c92003feb604c92017f6f504c92017f6d504c92017fcf304c92017fea304c92017fcd304c92017fea104c920014fe76d852004ef661d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520044fe73d8520004fd73d852000cfd72d8520014fc72d8520006f751d852004ef451d852004ef641d852004ef621d852000cfe70d852003cfd70d852000cfc70d85200f67f50d85200f67d50d85200f6f710d852004ef46158520004ff7654520004fe7654520004fc76545200267e65545200067d6554520004ff7650520004fe7650520004fc76505200057f755052005d7c755052001ebe6450520006b
  | 5 => 0x5f7715952004df47159520224ff75595200067f7559520004ff745952001cfe745952001cfc74595200067e545952005e7c5459520004ff7359520044fc735952005e7f5359520344ff7259520006ef725952033e7e525952033e7c5259520004ff7159520006f77159520004f77159520014fe7159520014fc7159520006f47159520014f4715952005e7f515952020cff7059520006fb705952020e7f505952020e7d505952020efa105952001cfe76d912005d7e75d91200057d75d9120056be64d9120024fe75d91200067e75d91200247e75d9120004fd75d91200067d75d91200047d75d9120024fc75d9120044fe73d9120004fd73d912003cfe72d912000cfd72d912003cfc72d9120056bf42d9120014fe71d9120004fd71d9120014fc71d912003cff70d912003cfd70d91201f67f50d91201f67d50d91201f6bf40d91201f6bd40d91201f6fa30d9120056bc6459120005df7359120005dc7359120335ef7259120004ff7559120024fe7559120024fc75591201f4ff7459120006bf7459120004ff7359120006df7359120004df7359120044fc7359120006dc7359120044dc7359120056bf4359120334ff7259120006ef7259120004ff7159120014fe7159120014fc7159120056bf41591201dcff7059120006fb70591201de7f50591201de7d50591201defa3059120004ff7655120004fe7655120004fd7655120004fc7655120044fe76d8d20024fe75d8d20004fd75d8d20024fc75d8d2001cfe74d8d20004fd74d8d2001cfc74d8d20006df43d8d20006dc43d8d2003cfe72d8d2003cfc72d8d20014fe71d8d20004fd71d8d20014fc71d8d2003cff70d8d2003cfd70d8d2019e7f50d8d2019e7d50d8d2019edf30d8d2019edd30d8d20006df6398d2017ded7298d201bdef7258d20004ff7558d20024fe7558d20024fc7558d20004ff7458d2001cfe7458d2001cfc7458d20006df7358d201bcff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2017cff7058d20006fb7058d2017e7f5058d2017e7d5058d2019cfe7618d2005d7e7518d200057d7518d20055be7418d20005bd7418d20046de6318d20006dd6318d2004df67118d20005f57118d20044ff7694d20004fe7694d20004fd7694d20044fc7694d20006df6394d20046dc6394d2003dee7294d20005ed7294d2004df67194d20005f57194d2000dfa7094d20005f97094d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200267e6554d200067d6554d20006df6354d20046dc6354d20044ff7690d20004fe7690d20004fd7690d20044fc7690d2003dee7290d20005ed7290d2000dfa7090d20005f97090d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2001ebe6450d20006bd6450d20024ff765492000cfe765
  | 6 => 0xf3058f2017edd3058f2003efa2058f2003ef92058f20044ff7694f2003cfe7694f20004fd7694f2003cfc7694f2003dee7294f20005ed7294f20065f67194f20005f57194f20004ff7654f2003cfe7654f20004fd7654f2003cfc7654f200267e6554f200067d6554f20044ff7690f2003cfe7690f20004fd7690f2003cfc7690f2003dee7290f20005ed7290f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f2001ebe6450f20006bd6450f2003dee7250f2003def7650b2035eef7650b2003eef6550b20006ed6550b2003faf7450b2003faf6450b2001eee6450b2003eec6450b2003fac6450b20357af5450b2006fac5450b20005ef7350b2003eef6350b20006ed6350b2006faf4350b20007ad4350b20005ef7150b201e6ee6150b2003eec6150b2006faf4150b2000dee7050b2000dec7050b201df6f5050b201df6d5050b201dfaf4050b201dfad4050b2003def764cb20006ef764cb20005ef744cb20005ed744cb2003eef644cb20006ed644cb2003fcf734cb2003fcf634cb20046ee634cb2003eec634cb2003fcc634cb20005ef714cb2000dee704cb2000dec704cb2017f6f504cb2017f6d504cb2017fcf304cb2017fcd304cb20004ff7558720024fe7558720024fc7558720004ff745872001cfe745872001cfc7458720004ff7358720044fc735872000cfe7258720014fd725872000cfc725872003ef77158720066f6315872003ef7215872003ef421587200de7f50587200de7d505872003efa205872003ef920587200def71058720004ff7654720004fd765472003cfc76547200267e65547200067d6554720004ff7650720004fd765072003cfc76507200057f75507200757c755072001ebe6450720006bd645072003dee7250720007ad4250720016f461507202bfe72150720044ff76cc72003cfe76cc720004fd76cc7200757e75cc7200057d75cc720046de63cc720006dd63cc72003dee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c72003cfc764c720046de634c720006dd634c72003dee724c720007cd324c720016f6614c720006f5614c72003def764872034eef764872003eef6548720006ed6548720005ef7448720005ed7448720005ef7348720005ed734872003fe7714872003fe76148720016ee6148720016ec614872003fe46148720067e63148720007e5314872000dee704872000dec70487200df6f50487200df6d50487200dfe71048720024fe76d952005e7e65d952001cfe74d9520004fd74d952001cfc74d9520044fe73d9520004fd73d952003cfe72d952000cfd72d952003cfc72d952005e7f52d9520014fe71d9520004fd71d9520014fc71d952003cff70d952003cfd70d95202267f50d95202267d50d9520226fa10d952005e7c6559520345ef7259520
  | 7 => 0xc53012ede64cc53012edc64cc530005dd72cc530006df62cc53010ddd71cc530016de61cc530016dc61cc53000dde70cc53000ddc70cc530046df60cc530047db60cc5301275f50cc5301275d50cc530127da40cc530127da20cc53000cfc764c530006f7614c530016f4614c530047d4314c530005fb704c53000df8704c53000ddc764c530016dc764c53000cdc764c530006df654c530006dd654c530005df744c530005dd744c530116de644c530116dc644c530005df724c530006df624c530045df714c530047d7714c530007d7614c530016de614c530016dc614c53007fd4614c530367d7514c53007fd4514c53007fd6414c530007d5414c53007fd6214c530007db704c53000dde704c53000ddc704c53010fd8704c53000dd8704c530046df604c530047db604c53010f5f504c53010f5d504c53010fda404c53010fda204c53010fd7104c530004fe76c8530004fd76c853003cfc76c8530045de73c8530005dd73c853000dfa70c8530005f970c8530004ff7648530004fe7648530004fc7648530045de7348530005dd7348530016f66148530007d53148530045f8765013001ef87650130044f87650130006fb6550130006f9655013000dfb745013000fbb7450130007bb645013001efa645013001ef86450130087b86450130007db7350130045fa7350130045f87350130007d8735013000efb635013000fdb6350130087bb4350130087da4350130007b94350130087d94350130007994350130005fb7250130087bb4250130007b94250130007db3250130007d93250130087bb4150130007b94150130007db3150130007d9315013003e7f7559720004ff745972001cfe745972001cfc74597200067e54597200767c5459720004ff7359720044fc73597200767f535972003cff725972000cfe725972003cfd725972000cfc725972003e7e525972003e7c525972003eee4259720004ff7159720014fe7159720014fc71597200767f515972003eef215972020e7f505972020e7d5059720004ff7559320024fe7559320024fc755932003ebf7459320006bf545932006ebc5459320004ff7359320044fc735932006ebf435932003cff725932000cfe725932003cfd725932000cfc725932003ebe425932003ebc425932003eee3259320004ff7159320014fe7159320014fc715932006ebf41593201de7f50593201de7d50593201debf40593201debd4059320004ff765532003cfe7655320004fd765532003cfc7655320004ff7558f20024fe7558f20024fc7558f20004ff7458f2001cfe7458f2001cfc7458f2003edf7358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2003eee4258f2003ede3258f2003edc3258f20004ff7158f20014fe7158f20014fc7158f2017e7f5058f2017e7d5058f2017ed
  | 8 => 0x46df6050d30047db6050d3023f5f5050d3023f5d5050d3023f9f4050d3023fda4050d3023f9d4050d3023fda2050d3003cfe76d8930024fe75d8930004fd75d8930024fc75d893001cfe74d8930004fd74d893001cfc74d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d8930044fd70d89301be7f50d89301be7d50d89301beef20d8930006ef629893008d7e75189300057d7518930085be7418930005bd741893003eee6218930006ed621893007df67118930005f57118930004fe7694930004fd769493003cfc7694930085be7494930005bd7494930045de7394930005dd7394930006ef629493003eec629493000dfa7094930005f97094930004ff7654930004fe7654930004fc76549300267e65549300067d6554930006ef625493003eec6254930004fe7690930004fd769093003cfc769093008d7e75909300057d7590930045de7390930005dd739093003eee629093000dfa7090930005f97090930004ff7650930004fe7650930004fc765093001ebe6450930006bd64509300079d435093000dfa705093015dde76cc930046de76cc930045df74cc930005dd74cc93003ede62cc93003edc62cc930005dd71cc930047db70cc93000dde70cc93000ddc70cc930047d870cc930046df60cc930047db60cc9301bf5f50cc9301bf5d50cc9301bfda40cc9301bfda20cc93000cfe768c93017ddd738c930006ef628c93003eec628c93000dfa708c930005f9708c93000cfc764c930006ef624c93003eec624c930047cc324c930005fb704c93000df8704c930047d8304c93000ddc764c93003edc764c93000cdc764c930005df744c930005dd744c930045df724c930047cf724c930007cf624c93003ede624c93003edc624c930007cc624c930007ce424c930007cd424c930005df714c930007db704c93000dde704c93000ddc704c93017fd8704c930046df604c930047db604c93017f5f504c93017f5d504c93017fda404c93017fda204c930014fe76d853008d7e75d85300057d75d853007ef661d8530024fe75d85300067e75d85300247e75d8530004fd75d85300067d75d85300047d75d8530024fc75d853001cfe74d8530004fd74d853001cfc74d853000cfd73d8530014fc73d853003cfe72d8530004fd72d8530006df32d8530006dd32d853007ef631d8530044fd70d85301267f50d85301267d50d8530126fa20d8530126f710d8530005ef7258530005ec725853007ef46158530004ff7654530004fe7654530004fc7654530004ff7650530004fe7650530004fc76505300057f755053008d7c7550530006bf645053001ebc64505300079e4350530016f6615053036dde76cc530046de76cc5300475e75cc5300475d75cc530006df65cc530006dd65cc530045df74cc530005dd74c
  | 9 => 0xf504c73010f5d504c73010fd7104c73003cff76c8730044fe76c8730004fd76c8730045de73c8730005dd73c8730004ff7648730004fd7648730044fc7648730045de7348730005dd7348730016f66148730006f56148730007d53148730024fe76d953008e7e65d953001cfe74d9530004fd74d953001cfc74d9530044fe73d953000cfd73d9530044fc73d953008e7f53d953003cfe72d9530004fd72d9530014fe71d9530004fd71d9530014fc71d9530044ff70d9530044fd70d95302867f50d95302867d50d9530286fa40d953008e7c6559530005bf7459530085bc745953038ddf7359530284ff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe745953001cfc7459530006bc745953001cbc745953008e7f545953038cff7359530006df73595303867e53595303867c5359530004ff725953003cfc725953008e7f5259530004ff7159530014fe7159530014fc71595300067e515953008e7c515953026cff7059530006fb705953026e7f505953026e7d505953026efa405953001cfe76d9130086be64d9130024fe75d9130004fd75d9130024fc75d9130006bf54d9130086bc54d9130044fe73d913000cfd73d9130044fc73d9130086bf43d913003cfe72d9130004fd72d9130014fe71d9130004fd71d9130014fc71d9130086bf41d9130044ff70d9130044fd70d91302567f50d91302567d50d9130256bf40d9130256bd40d9130086bc645913037ddf7359130004ff7559130024fe7559130024fc7559130254ff7459130006bf745913037cff7359130006df7359130004ff725913003cfc7259130086bf4259130004ff7159130014fe7159130014fc715913023cff7059130006fb705913023e7f505913023e7d5059130004ff7655130004fe7655130004fd7655130004fc76551300267e65551300067d6555130024ff7654d3000cfe7654d3026cfd7654d3000cfc7654d300067f6554d300267c6554d30005fb7054d3000df87054d30047d83054d30375de7690d30046de7690d30006df6590d30006dd6590d3023ddd7490d3001ede6490d3001edc6490d30005dd7290d30005dd7190d300879f4190d30047db7090d3000dde7090d3000ddc7090d30047d87090d30046df6090d30047db6090d302575f5090d302575d5090d30257da4090d30257da2090d3001cff7650d3000cfe7650d3023cfd7650d3000cfc7650d30006bf6450d3001ebc6450d300479c4350d30005fb7050d3000df87050d30047d83050d3000ddc7650d3001edc7650d3000cdc7650d30006df6550d30006dd6550d30045df7450d300479f7450d300079f6450d3001ede6450d3001edc6450d300879c6450d30005df7250d300879f4250d30005df7150d30007db7050d3000dde7050d3000ddc7050d3023fd87050d30
  | 10 => 0x9730004ff7559330024fe7559330024fc7559330046bf7459330044ff735933000cfe7359330044fd735933000cfc7359330046be4359330046bc4359330004ff725933003cfc725933009ebf4259330004ff7159330014fe7159330014fc715933023e7f505933023e7d505933023ebf405933023ebd4059330046fa3059330046f93059330004ff7655330044fe7655330004fd7655330044fc76553300267e65553300067d6555330045df7650f303aedf7650f30046df6550f30006dd6550f300479f7450f300479f6450f3001ede6450f30046dc6450f300479c6450f30005df7250f3009f9f4250f30005df7150f3000dde7050f3000ddc7050f3023f5f5050f3023f5d5050f3023f9f4050f3023f9d4050f30004ff7558b30024fe7558b30024fc7558b30004ff7458b3001cfe7458b3001cfc7458b3000cfc7358b30046ef7258b30046ef3258b30046ec3258b30004ff7158b30014fe7158b30014fc7158b30046df3158b3017e7f5058b3017e7d5058b30046fa3058b30046f93058b3017eef2058b3003cff7694b30044fe7694b30004fd7694b3009dbe7494b30005bd7494b30045de7394b30005dd7394b30004ff7654b30004fd7654b30044fc7654b300267e6554b300067d6554b3003cff7690b30044fe7690b30004fd7690b300a57e7590b300057d7590b30045de7390b30005dd7390b3003eee6290b30006ed6290b30004ff7650b30004fd7650b30044fc7650b3001ebe6450b30006bd6450b30045de7350b300079d4350b3003eee6250b30006ed6250b30045df764cb30006df764cb30005df744cb30005dd744cb30047cf724cb30047cf624cb3003ede624cb3003edc624cb30047cc624cb30007ce424cb30007cd424cb30005df714cb3000dde704cb3000ddc704cb3017f5f504cb3017f5d504cb30004ff7558730024fe7558730024fc7558730004ff745873001cfe745873001cfc745873000cfe7358730014fd735873000cfc7358730004ff725873003cfc7258730046df3258730006dd3258730046f77158730006f75158730096f45158730096f64158730046f73158730046f43158730096f6215873010e7f505873010e7d505873010ef71058730004ff7654730004fd7654730044fc7654730004ff7650730004fd7650730044fc76507300057f75507300a57c75507303a6bf645073001ebc6450730045de73507303a79e4350730016f66150730006f56150730045df764c73039edf764c730046df654c730006dd654c730005df744c730005dd744c730116de644c730046dc644c730005df724c730006dd624c730047d7714c730047d7614c730016de614c730016dc614c730047d4614c730397d7514c730097d4514c730097d6414c730007d5414c730097d6214c73000dde704c73000ddc704c73010f5
  | 11 => 0x13fb8705054001ebf605054001fbb605054013f3f505054013fba505054013f3d505054013fba305054013fb71050540004fe76cc540004fd76cc540044fc76cc5400b57e75cc5400057d75cc54001dbe74cc540005bd74cc540006df63cc540046dc63cc54012f9f43cc54000dfa70cc540005f970cc540004ff764c540004fe764c540004fc764c54001dbe744c540005bd744c540006df634c540046dc634c5401179f434c540016f6614c540007b5414c540004fe76c8540004fd76c854003cfc76c854001dbe74c8540005bd74c8540007b541c8540004ff7648540004fe7648540004fc764854001dbe7448540005bd744854001df87654140026f8765414001cf8765414000dfb755414000f7b75541400077b6554140026fa6554140026f865541400b7786554140007bb745414001dfa745414001df874541400c7b8745414000efb645414000fbb64541400c77b54541400c77a54541400c77954541400c7785454140005fb73541400b77b53541400077a53541400077953541400b77853541400c7bb4354140007b943541400b77b52541400077a52541400077952541400b77852541400c7bb4254140007b94254140006fb61541400b77b51541403b77a51541400077951541400b77851541400c7bb4154140007b941541400b77b76541400267b76541400c77876541400267876541400c77b74541400073b74541400c77a74541400c77974541400c77874541400c738745414000f7b645414000e7b645414000f3b64541400077b73541400077a73541400077973541400077873541400077b63541400077a63541400077963541400077863541400c77b43541400c73b43541400c77a43541400c77943541400073943541400c77843541400077b72541400077a72541400077972541400077872541400077b62541400077a62541400077962541400077862541400c77b42541400c73b42541400c77a42541400c77942541400073942541400c77842541400077b32541400077a32541400077932541400077832541400077b71541403b77a71541400077971541403b77871541400077b61541400067b61541403b77a61541400077961541403b77861541400c77b41541400c73b41541400c77a41541400c77941541400073941541400c77841541400077b31541403b77a31541400077931541403b77831541400077b21541403b77a21541400077921541403b77821541400467f7559730004ff745973001cfe745973001cfc74597300a67f5459730044ff735973000cfe7359730044fd735973000cfc73597300467e53597300467c5359730046de4359730004ff725973003cfc72597300a67f5259730004ff7159730014fe7159730014fc71597300067e51597300a67c5159730046df315973026e7f505973026e7d505
  | 12 => 0xf6350d40046be6350d40046bc6350d400079c6350d400079e5350d400079d5350d40005bf7250d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d4023fb87050d4001ebf6050d4001fbb6050d4023f3f5050d4023fba5050d4023f3d5050d4023fba3050d4003cfe76d8940024fe75d8940004fd75d8940024fc75d894000cfd74d8940044fe73d8940004fd73d89403d6bf43d8940006bd43d89403d6ee42d89403d6ed42d8940014fe71d8940004fd71d8940014fc71d89403d6bf41d894001cfd70d89403367f50d89403367d50d8940336fa30d8940336ef20d89400b57e75989400057d7598940006ef6298940055f97098940005df7358940005dc735894006dfb705894003eee6218940006ed6218940004fe7694940004fd769494003cfc769494001dbe7494940005bd7494940004ff7654940004fe7654940004fc76549400067f65549400267c655494000dbc765094003ebc765094000cbc76509401eebe65509401eebc6550940005bf7350940006bf635094001dbf725094001faf7250940007af625094003ebe625094003ebc6250940007ac6250940007ae5250940007ad5250940005bf71509403cfae21509403cfac2150940007bb705094000dbe705094000dbc70509401dfb8705094001ebf605094001fbb60509401df3f50509401dfba50509401df3d50509401dfba3050940004fe76cc940004fd76cc940044fc76cc94001dbe74cc940005bd74cc94000dfa70cc940005f970cc940004fe768c940004fd768c94003cfc768c94001dbe748c940005bd748c940006df638c940046dc638c94003eee628c940007ad428c940004ff764c940004fe764c940004fc764c94001dbe744c940005bd744c940007ad424c940004fe760c940004fd760c94003cfc760c9400b57e750c9400057d750c94001dbe740c940005bd740c940006df630c940046dc630c9400adf6710c940005f5710c94000dfa700c940005f9700c940014fe76d85400aef661d8540024fe75d8540004fd75d8540024fc75d854000cfd74d8540014fc74d8540044fe73d8540004fd73d854003cfe72d8540004fd72d85403c6bf42d8540006bd42d85400aef641d85403c6f541d854001cfd70d85402e67f50d85402e6fa50d85402e67d50d85402e6f710d85400057f75585400b57c75585400aef461585403bdfb7058540004ff7654540004fe7654540004fc765454000dbc7650540016bc765054000cbc76505400073f75505400073c7550540006bf6550540006bd6550540005bf73505403a6bc6350540005bf7250540006bf625054001dbf715054001fb77150540007b76150540016be6150540016bc61505400afb461505400afb65150540007b551505400afb631505400afb42150540007bb705054000dbe705054000dbc7050540
  | 13 => 0xc55038777314c5500bf5e314c5500bf5c314c5500bf74314c5500bf76214c55010d7f704c55000d7e704c55000d7c704c55010e7f604c55011f7b604c55010f7a404c55010f77104c55010f7a104c55033d7f76c85500057e76c85500057d76c855033d7c76c855033d7f74c85500c57e74c85500057d74c855033d7c74c855033d7f73c85503857e73c85500057d73c855033d7c73c855031d7e72c855033f6e62c85500076d62c85500dd7d71c85500077761c85500bf7461c85500bf7641c85500077541c85500bf6e21c85500bf7621c85500bf6c21c85500f57f70c855000d7e70c85500f57d70c855000d7c70c85500f67f60c85501077b60c85500f77a40c85500f76f20c85500f77a10c85500057f76485500057e76485500057d76485500057c76485500057f74485500c57e74485500057d74485500c57c74485500057f73485503857e73485500057d73485503857c73485502c57f72485500076e62485500076d62485500f57f71485500bf76314855000775314855033f7721485500bf6e21485500bf6c21485500bf7421485500dd7f704855000d7e704855000d7c70485500de7f60485500ef7b60485500df7a40485500df7710485500df7a1048550024fe76d95400b67e65d954029cfd75d954000cff74d954001cfe74d954000cfd74d954001cfc74d95403f67f54d95403f67d54d9540044fe73d9540004fd73d954003cfe72d9540004fd72d95400b67f52d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400b67c51d95403f6bf41d954001cff70d954001cfd70d95403ee7f50d95403ee7d50d9540024ff76595400b67c65595403e5bf74595400d5fb70595403ecff75595400067f75595403e4ff7459540006bf74595400c67e54595400c67c5459540004ff7359540044fc73595400b67f5359540004ff725954003cfc7259540004ff7159540014fe7159540014fc71595400c6bf415954029cff7059540006fb705954029e7f505954029e7d5059540044fe76d8d40024fe75d8d40004fd75d8d40024fc75d8d4000cfd74d8d403dede43d8d403dedd43d8d4003cfe72d8d40004fd72d8d403debf42d8d40014fe71d8d40004fd71d8d40014fc71d8d4001cfd70d8d4037e7f50d8d4037e7d50d8d4037edf30d8d40006df6398d40085f97098d4009dfb7058d400b57e7518d400057d7518d40046de6318d40006dd6318d40005ee7218d40005ed7218d400adf67118d40005f57118d40004fe7694d40004fd7694d40044fc7694d4001dbe7494d40005bd7494d400adf67194d40005f57194d4000dfa7094d40005f97094d40004ff7654d40004fe7654d40004fc7654d400267e6554d400067d6554d4000dfa7054d4000dbc7650d40046bc7650d4000cbc7650d4001dbf7350d4001f9f7350d400079
  | 14 => 0x53d740c95033d7c740c9501bd7e730c95019d7e720c95033f5f320c95033f6e320c95033f5d320c9503876d320c9500bd7e710c95033f76710c9500bd76710c9500057d710c95033f75710c95000575710c9500bd7c710c95015d7f700c95000d7e700c95015f7a700c95000d7a700c95015d7d700c95033f79700c95000579700c95000d7c700c95015e7f600c9501777b600c95015f7a400c95015f7a100c9504157e76d85500c57e74d85500057d74d85500c57c74d85503857e73d85500057d73d855033d7e72d85500057d72d85500067f62d85500067d62d85500be7e61d85500bf7661d85500be7c61d85500bf7631d85500bf7421d85500257f70d855040f7b70d855000d7e70d85500257d70d855000d7c70d85503067f60d855040f7b60d85503077a40d85503077710d85503077a10d85503077510d855030d7f76585500057f74585500c57e74585500c57c74585500057f73585503857c73585500057f725855033d7c72585500067f62585500067d62585503057f71585500077761585500be7e61585500be7c61585500bf7461585500bf76415855014d7f70585500077b70585500057b70585500377b605855014f7a405855014f7a10585500057f76505500067f76505500047f76505500057e76505500057d76505500057c76505500067c76505500047c76505502ed7f74505500c73e64505500073d64505500057f73505503857c73505500073e43505500c73c43505500057f725055033d7c72505500c73f42505500073d42505502e57f71505500bf7661505500077561505500c77741505500bf3e41505500bf3c41505500bf7441505500bf7631505500bf74215055013d7f705055000d7e705055013f7a705055000d7a705055000779705055000d7c705055013e7f60505501477b605055013f3f405055013f7a405055013f77105055013f7a10505503857f76cc5500057e76cc5503867e76cc5500047e76cc5500057d76cc5503867d76cc5500047d76cc5503857c76cc5503857f74cc5500c57e74cc5500057d74cc5503857c74cc55036d7e73cc5503875e63cc5500075d63cc5504075f43cc5503875c43cc55033d7e72cc5500057d72cc5503875f32cc5500075d32cc55010d7d71cc5500bf5e31cc5500bf7631cc5500bf5c31cc5501257f70cc55000d7e70cc5501257d70cc55000d7c70cc5501267f60cc5501377b60cc5501277a40cc5501275f30cc5501277a10cc5500057f764c5500057e764c5500057d764c5500057c764c5500057f744c5500c57e744c5500057d744c5500c57c744c5502d57f734c5500075e634c5500075d634c5503ff5f434c5503ff5c434c5500057f724c55033d7c724c5500075f324c5500075d324c5501257f714c55000777614c5500bf74614c5500bf76414c55000775414
  | 15 => 0xd741895033d7c74189503857e73189500057d73189502257e721895033e7f621895033f6e621895033e7d62189500076d62189500bd7e71189500057d71189500bd7c71189500257f701895000d7e70189500257d701895000d7c701895042e7f60189504377b601895042f7a401895042f6f201895042f6d201895042f7a101895033d7f76909500057e769095033e7e76909500047e76909500057d769095033e7d76909500047d769095033d7c76909501dd7d74909503857e73909500057d739095032d7e729095033f6e62909500076d629095033f3f42909500c76f429095033f6c42909500bd7e71909500057d71909500bd7c71909504276e219095033f6c21909501f57f709095000d7e70909501f57d709095000d7c70909501f67f60909502077b60909501f77a40909501f76f20909501f77a10909500057f76509500057e76509500057d76509500057c76509501f57f74509500073f64509500c73c64509500057f73509503857c73509500c73f43509500073d43509503357f72509500076e62509500076d62509500c76f425095033f3e425095033f3c42509500c76c42509500057f71509500bd7e71509500bd7c71509500c73f415095041f6e215095041f6c21509501dd7f705095000d7e705095000d7c70509501de7f60509501ef7b60509501df3f40509501df7a40509501df7a10509503857f76cc9500057e76cc9500057d76cc9503857c76cc9503857f74cc9500c57e74cc9500057d74cc9503857c74cc9500bd7e71cc9500057d71cc9500bd7c71cc9501bd7f70cc95000d7e70cc9501bd7d70cc95000d7c70cc9501be7f60cc9501d77b60cc9501bf7a40cc9501bf5f30cc9501bf7a10cc95033d7f768c9500057e768c9500057d768c95033d7c768c95033d7f748c9500c57e748c9500057d748c95033d7c748c95017d7d738c95015d7e728c95033f6e428c9500076d428c95033f5f328c9503876f328c9500bd7e718c9500057d718c9500bd7c718c95019d7f708c95000d7e708c95019d7d708c95000d7c708c95019e7f608c9501b77b608c95019f7a408c95019f6f208c95019f7a108c9500057f764c9500057e764c9500057d764c9500057c764c9500057f744c9500c57e744c9500057d744c9500c57c744c9500076e424c9500076d424c9503876f324c95033f5e324c9500057f714c9500bd7e714c9500bd7c714c95017d7f704c9500077b704c9500057b704c95000d7e704c95000d7c704c95017f78704c95000d78704c95017e7f604c9501977b604c95017f7a404c95017f7a104c95033d7f760c9500057e760c95033e7e760c9500047e760c9500057d760c95033e7d760c9500047d760c95033d7c760c95033d7f740c9500c57e740c95033f3e740c9500c53e740c9500057d740c95033f3d740c950
  | 16 => 0x8d500057f7458d500073f7458d500053f7458d500c57e7458d500c57c7458d500073c7458d500c53c7458d500067f6458d500067d6458d500075f6358d503867e6358d500057f7258d5033d7c7258d500057f7158d500bd7e7158d500bd7c7158d500067e6158d500067c6158d5026d7f7058d500077b7058d500057b7058d5008f7b6058d5026f7a4058d5026f7a1058d5038d7e7618d500c57e7418d500057d7418d503857c7418d502857e7318d503867f6318d503875e6318d503867d6318d500075d6318d5033d7e7218d500057d7218d500bd7e7118d500057d7118d500bd7c7118d500257f7018d5000d7e7018d500257d7018d5000d7c7018d504467f6018d5044f7b6018d504477a4018d504475f3018d504475d3018d504477a1018d503857f7690d500057e7690d500057d7690d503857c7690d5023d7d7490d500073f6490d500c73c6490d503757e7390d503875e6390d500075d6390d503873f4390d500c75f4390d503875c4390d5033d7e7290d500057d7290d500bd7e7190d500057d7190d500bd7c7190d500c73f4190d502557f7090d5000d7e7090d502557d7090d5000d7c7090d502567f6090d502677b6090d502577a4090d502575f3090d502577a1090d500057f7650d500057e7650d500057d7650d500057c7650d502557f7450d5037d7f7350d500075e6350d500075d6350d500c75f4350d503873e4350d503873c4350d500c75c4350d500057f7250d5033d7c7250d500c73f4250d500057f7150d500bd7e7150d500bd7c7150d5023d7f7050d5000d7e7050d5000d7c7050d5023e7f6050d5024f7b6050d5023f3f4050d5023f7a4050d5023f7a1050d500c57e74d89500057d74d89500c57c74d89500067e64d89500067c64d89503857e73d89500057d73d89500067f63d89500067d63d89500bd7e71d89500057d71d89500bd7c71d89500257f70d89500257d70d89503467f60d895043f7b60d89503477a40d89503476f20d89503476d20d89503477a10d89500c57e749895033f3e74989500c53e74989500057d749895033f3d74989500053d749895033d7c74989503857e73989500057d739895042d7e729895033e7f62989500076f62989500bd7e71989500057d71989500bd7c71989502257d709895033f7970989500057970989502267f60989500777b60989502277a40989502277a10989500057f74589500c57e74589500c57c74589500067e64589500067c64589500057f73589503857c73589500067f63589500067d63589500076f625895033e7e62589500057f71589500077771589500057771589500bd7e71589500bd7c71589500077471589500bd74715895020d7f70589500077b70589500057b705895005f7b605895020f7a405895020f7a10589503457e76189500c57e74189500057
  | 17 => 0x46dfb705855000d7c76545500167c765455000c7c76545500057f74545500c57e74545500c57c74545500057f73545503857c73545500057f725455033d7c72545500067f62545500257f71545500277771545500077761545500167e61545500167c61545500bf7461545500bf7641545500077b705455000d7e705455000d7c705455014f7870545500267f60545500277b605455014f7a405455014f7a1054550004ff7650550004fe7650550004fc76505500057f75505500257e75505500057d75505500257c755055001ebe64505500c73e54505500073d5450550016f661505500bf76515055000775515055000dfa7050550004fe76cc550004fd76cc550044fc76cc5503857f75cc5500257e75cc5500057d75cc5500257c75cc550046de63cc5503875e53cc5500075d53cc550004ff764c550004fe764c550004fc764c5500057f754c5500257e754c5500057d754c5500257c754c5500075e534c5500075d534c550006f7614c550016f4614c55011f77514c5500bf74514c550004fe76c8550004fd76c855003cfc76c855033d7f75c85500257e75c85500057d75c85500257c75c855003eee62c855033f6e52c85500076d52c8550006f761c8550016f461c8550004ff7648550004fe7648550004fc76485500057f75485500257e75485500057d75485500257c75485500076e52485500076d52485504657e76d91500c67e64d91500c73e64d91500c67c64d91503857e73d91500057d73d91500c73c43d915033d7e72d91500057d72d91500c73f42d91500bd7e71d91500057d71d91500bd7c71d91500257f70d915045f7b70d915000d7e70d91500257d70d915000d7c70d91503e67f60d915045f7b60d91503e73f40d91503e77a40d91503e73d40d91503e77a10d91503ed7f76591503e57f74591500073f64591500c67e64591500c67c64591500c73c64591500057f73591503857c73591500057f725915033d7c72591500057f71591500bd7e71591500bd7c71591500c73f415915029d7f70591500077b70591500057b70591500b77b605915029f7a405915029f7a10591500c57e74d8d500057d74d8d500c57c74d8d500067f64d8d500067d64d8d5033d7e72d8d500057d72d8d500bd7e71d8d500057d71d8d500bd7c71d8d500067e61d8d500067c61d8d500257f70d8d500257d70d8d5038e7f60d8d504577b60d8d5038f7a40d8d5038f5f30d8d5038f5d30d8d5038f7a10d8d500c57e7498d500057d7498d503857c7498d504457e7398d503867f6398d500075f6398d5033d7e7298d500057d7298d500bd7e7198d50387767198d500bd767198d500057d7198d50387757198d50005757198d500bd7c7198d502857d7098d50387797098d50005797098d502867f6098d500a77b6098d502877a4098d502877a109
  | 18 => 0xd75d895001cfe74d8950004fd74d895001cfc74d89500067e54d895043e7c54d8950044fe73d8950004fd73d895043e7f53d89500067d53d895043eee52d895043eed52d895033e7c52d8950014fe71d8950004fd71d8950014fc71d895043e7f51d8950024fd70d8950346ef20d8950346fa10d89500c5be7498950005bd7498950006ef629895005df97098950005f771589500bdf47158950075fb705895003eee6218950006ed621895000d7e76949502267e769495000c7e76949500c57e749495033f3e74949500c53e74949500057d749495033f3d74949500053d749495033d7c74949503857e73949500057d73949500257e72949500276e729495033e7f62949500076f629495033f6c62949500bd7e71949500057d71949500bd7c719495000d7e70949502277a709495033f79709495000d7c70949500267f60949500277b60949502277a40949502277a109495000d7c765495003e7c765495000c7c76549500057f74549500c57e74549500c57c745495021e7e645495021e7c64549500057f73549503857c73549500067f63549500257f72549500276f72549500076f625495003e7e625495003e7c62549500076c62549500057f71549500bd7e71549500bd7c71549500077b705495000d7e705495000d7c705495020f7870549500267f60549500277b605495020f7a405495020f7a1054950004fe7690950004fd769095003cfc769095033d7f75909500257e75909500057d75909500257c759095003eee629095033f6e52909500076d5290950004ff7650950004fe7650950004fc76509500057f75509500257e75509500057d75509500257c7550950006bf645095001ebc64509501ef3f54509500c73c54509500076e52509500076d5250950004fe76cc950004fd76cc950044fc76cc9503857f75cc9500257e75cc9500057d75cc9500257c75cc950004fe768c950004fd768c95003cfc768c95033d7f758c9500257e758c9500057d758c9500257c758c950004ff764c950004fe764c950004fc764c9500057f754c9500257e754c9500057d754c9500257c754c950005fb704c95000df8704c950004fe760c950004fd760c95003cfc760c95033d7f750c9500257e750c9500057d750c9500257c750c9500c5be740c950005bd740c9500bdf6710c950005f5710c95000dfa700c950005f9700c950014fe76d85500257e75d855000d7d75d85500bef661d85500bf7651d855000cfd75d85503067d75d855000c7d75d8550014fc75d855001cfe74d8550004fd74d855001cfc74d8550044fe73d8550004fd73d855003cfe72d8550004fd72d855040e7f52d85500067d52d85500be7e51d85500bef651d855040ef551d85500be7c51d85500bef631d85500bef421d8550024fd70d8550306f710d85500bef46158550
  | 19 => 0x875047f7721487500cf6e21487500cf6c21487500cf7421487500dd7f704875000d7e704875000d7c70487500df77104875001cfe76d91500257e75d915000d7d75d91500c6be64d91500c73e54d915000cfd75d91503e67d75d915000c7d75d915001cfc75d91500c67e54d91500c6be54d915045ebd54d91500c67c54d9150044fe73d9150004fd73d915045e7f53d91500c6bc43d915003cfe72d9150004fd72d91500c6bf42d9150014fe71d9150004fd71d9150014fc71d9150024fd70d91503e6bf40d91500c6bc6459150475fb705915000d7c765515001e7c765515000c7c76551500257f74551500273f74551500073f645515001e7e645515001e7c64551500c73c64551500057f73551503857c73551500057f725515033d7c72551500057f71551500bd7e71551500bd7c71551500c73f41551500077b705515000d7e705515000d7c705515029f7870551500267f60551500277b605515029f7a405515029f7a1055150044fe76d8d5000cfd75d8d5038e7d75d8d5001cfe74d8d50004fd74d8d5001cfc74d8d504567f54d8d500067d54d8d50456de53d8d50456dd53d8d503867c53d8d5003cfe72d8d50004fd72d8d504567f52d8d50014fe71d8d50004fd71d8d50014fc71d8d500067e51d8d504567c51d8d50024fd70d8d5038efa40d8d5038edf30d8d50006df6398d500bdf67198d50005f57198d5008df97098d50005bf7458d500c5bc7458d500a5fb7058d50046de6318d50006dd6318d5000d7e7694d502867e7694d5000c7e7694d500c57e7494d500057d7494d503857c7494d500257e7394d500275e7394d503867f6394d500075f6394d503875c6394d5033d7e7294d500057d7294d500bd7e7194d50387767194d500bd767194d500057d7194d50387757194d50005757194d500bd7c7194d5000d7e7094d502877a7094d50387797094d5000d7c7094d500267f6094d500277b6094d502877a4094d502877a1094d5000d7c7654d500467c7654d5000c7c7654d500057f7454d500c57e7454d500c57c7454d500067f6454d500257f7354d500275f7354d500075f6354d500467e6354d500467c6354d500075c6354d500057f7254d5033d7c7254d500057f7154d500bd7e7154d500bd7c7154d502767e6154d502767c6154d500077b7054d5000d7e7054d5000d7c7054d5026f787054d500267f6054d500277b6054d5026f7a4054d5026f7a1054d50004fe7690d50004fd7690d50044fc7690d503857f7590d500257e7590d500057d7590d500257c7590d50006bf6490d5001ebc6490d50046de6390d503875e5390d500075d5390d50004ff7650d50004fe7650d50004fc7650d500057f7550d500257e7550d500057d7550d500257c7550d500075e5350d500075d5350d5003cfe76d895000cfd75d89503467
  | 20 => 0x247e760cb501757d760cb5047e7d760cb500047d760cb500257c760cb5047d7f740cb500d57e740cb5047f3e740cb500d53e740cb500057d740cb5047f3d740cb500053d740cb5047d7c740cb504875e630cb501775d630cb5047f6e620cb501776d620cb5047f5f320cb5047f6e320cb5047f5d320cb504876d320cb500cd7e710cb5047f76710cb500cd76710cb500057d710cb5047f75710cb5000575710cb500cd7c710cb5015d7f700cb5000d7e700cb5015f7a700cb5000d7a700cb5015d7d700cb5047f79700cb5000579700cb5000d7c700cb501457f76507500067f76507500047f76507500257e76507501457d76507500257c76507501467c76507500247c76507502ed7f74507500d73e64507501473d64507500057f73507504857c73507500073e43507500d73c43507500057f725075047d7c72507500d73f42507500073d42507502e57f71507500cf7661507501477561507500d77741507500cf3e41507500cf3c41507500cf7441507500cf7631507500cf74215075013d7f705075000d7e705075000d7c705075013e7d605075013f3f405075013f7710507504857f76cc7500257e76cc7504867e76cc7500247e76cc7501357d76cc7504867d76cc7500047d76cc7500257c76cc7504857f74cc7500d57e74cc7500057d74cc7504857c74cc75036d7e73cc7504875e63cc7501375d63cc7504975f43cc7504875c43cc75047d7e72cc7500057d72cc7504875f32cc7500075d32cc7500cf5e31cc7500cf7631cc7500cf5c31cc7501257f70cc75000d7e70cc7501257d70cc75000d7c70cc7501275f30cc75011d7f764c7500257e764c75011d7d764c7500257c764c7500057f744c7500d57e744c7500057d744c7500d57c744c7502d57f734c75011f5e634c75011f5d634c75048f5f434c75048f5c434c7500057f724c75047d7c724c7500075f324c7500075d324c75011f77614c7500cf74614c7500cf76414c75000775414c75048777314c7500cf5e314c7500cf5c314c7500cf74314c7500cf76214c75010d7f704c75000d7e704c75000d7c704c75010f77104c75047d7f76c87500257e76c87501057d76c87500257c76c875047d7f74c87500d57e74c87500057d74c875047d7c74c875047d7f73c87504857e73c87500057d73c875047d7c73c875031d7e72c875047f6e62c87501076d62c87500cf7641c87500077541c87500cf6e21c87500cf7621c87500cf6c21c87500f57f70c875000d7e70c87500f57d70c875000d7c70c87500f76f20c87500ed7f76487500257e76487500ed7d76487500257c76487500057f74487500d57e74487500057d74487500d57c74487500057f73487504857e73487500057d73487504857c73487502c57f72487500ef6e62487500ef6d62487500cf76314875000775314
  | 21 => 0xc75d812101cfe74d8121004fd74d812101cfc74d8121044fe73d8121004fd73d8121014fd72d812100cfc72d812103cfd71d812100cfc71d8121066f631d8121006f531d81210defa20d81210defa10d81210def860581214857f7690f500257e7690f502657d7690f500257c7690f503757e7390f504875e6390f502675d6390f504873f4390f500d75f4390f504875c4390f5047d7e7290f500057d7290f500cd7e7190f500057d7190f500cd7c7190f500d73f4190f502557f7090f5000d7e7090f502557d7090f5000d7c7090f502575f3090f5024d7f7650f500257e7650f5024d7d7650f500257c7650f5037d7f7350f5024f5e6350f5024f5d6350f500d75f4350f504873e4350f504873c4350f500d75c4350f500057f7250f5047d7c7250f500d73f4250f500057f7150f500cd7e7150f500cd7c7150f5023d7f7050f5000d7e7050f5000d7c7050f5023f3f4050f5047d7f7690b500257e7690b5047e7e7690b500247e7690b502057d7690b5047e7d7690b500047d7690b500257c7690b504857e7390b500057d7390b5032d7e7290b5047f6e6290b502076d6290b5047f3f4290b500d76f4290b5047f6c4290b500cd7e7190b500057d7190b500cd7c7190b504a76e2190b5047f6c2190b501f57f7090b5000d7e7090b501f57d7090b5000d7c7090b501f76f2090b501ed7f7650b500257e7650b501ed7d7650b500257c7650b501ef3f6450b500d73c6450b500057f7350b504857c7350b500d73f4350b500073d4350b503357f7250b501ef6e6250b501ef6d6250b500d76f4250b5047f3e4250b5047f3c4250b500d76c4250b500057f7150b500cd7e7150b500cd7c7150b500d73f4150b5049f6e2150b5049f6c2150b501dd7f7050b5000d7e7050b5000d7c7050b501df3f4050b504857f76ccb500257e76ccb501d57d76ccb500257c76ccb504857f74ccb500d57e74ccb500057d74ccb504857c74ccb501d76e62ccb501d76d62ccb500cd7e71ccb500057d71ccb500cd7c71ccb501bd7f70ccb5000d7e70ccb501bd7d70ccb5000d7c70ccb501bf5f30ccb5047d7f768cb500257e768cb501b57d768cb500257c768cb5047d7f748cb500d57e748cb500057d748cb5047d7c748cb501b75e638cb501b75d638cb5047f6e428cb500076d428cb5047f5f328cb504876f328cb500cd7e718cb500057d718cb500cd7c718cb5019d7f708cb5000d7e708cb5019d7d708cb5000d7c708cb5019f6f208cb501957f764cb500257e764cb501957d764cb500257c764cb500057f744cb500d57e744cb500057d744cb500d57c744cb500076e424cb500076d424cb504876f324cb5047f5e324cb500057f714cb500cd7e714cb500cd7c714cb5017d7f704cb5000d7e704cb5000d7c704cb5047d7f760cb500257e760cb5047e7e760cb50
  | 22 => 0x5121004fc7655121044fe76d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d2103cff71d8d2103cfd71d8d211a6df31d8d211a6dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d211a6f710d8d210ed7e7598d210057d7598d21006df6398d21185ed7298d211c5ef7258d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d21006df7358d211c4ff7258d21006ef7258d21184ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21186f71058d211a4fe7618d21046de6318d21006dd6318d21044ff7694d21004fe7694d21004fd7694d21044fc7694d21015f67194d21005f57194d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d210267c6554d21044ff7690d21004fe7690d21004fd7690d21044fc7690d21015f67190d21005f57190d21004ff7650d21004fe7650d21004fd7650d21004fc7650d214bdee769492103eee7694921215ed7594921026ee6594921026ec659492103fae749492103fad7494921006ef6494921006ed6494921015ee7194921015ec719492103eef619492103fe7619492122fe63194921005ed70949210ef6f509492122fe71094921024ff7654921014fe7654921214fd7654921014fc76549210067f65549210267c655492103f6c5254921005f77154921015f47154921015ec7654921026ec7654921014ec765492103def755492103f6f75549210076f6554921026ee6554921026ec65549210ef6c6554921006ef6454921006ed64549214b76e54549210ef6c54549210ef6f53549210076d5354921007e77154921015ee7154921015ec7154921217e4715492103eef615492103fe761549212176f51549212176d5154921217e63154921005ef70549210ef6f5054921217e7105492101cff7650921014fe76509211e4fd7650921014fc7650921006bf645092101ebc64509211e6ef6250921005f77150921015f4715092103fe42150921014fe76cc921014fc76cc921006df63cc921046dc63cc921015f671cc921005f571cc921044ff764c921014fe764c921184fd764c921014fc764c921006df634c921046dc634c921005f7714c921015f4714c92103df4764c521046f4764c52103cf4764c52111ef6654c52111ef4654c521006f7644c521006f5644c521015f7734c521017d7734c521007d7634c521046f6634c521046f4634c521007d4634c521007d6534c521007d5534c5214afd7434c5214afd4434c521007e7724c52103df6724c52103df4724c521007e4724c521016f7624c521017e7624c521007e6524c521007e5524c521007d7324c521007d5324c521005f7704c52100cfe76d81210defa60d8121024fe75d8121004fd75d8121024f
  | 23 => 0x67d6554f21044ff7690f2103cfe7690f21004fd7690f2103cfc7690f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f2101ebe6450f21006bd6450f2103def7654b214e6ef7654b2103f6f7554b2103f6f6554b21026ee6554b2103eec6554b2103f6c6554b2103eef6454b21006ed6454b214df6e5454b211076c5454b211076f5354b210076d5354b21015ee7154b21015ec7154b212176f5154b212176d5154b21217e64154b21005ef7054b211076f5054b212bdf7765072101ef7765072101cf776507210077775507210077475507212bef76550721006f56550721015f77450721017b7745072101ef664507212bfb664507212bfb5645072101ef464507210ffb65450721007b554507212bef76350721006f56350721007b643507210ffb443507212bdf77250721007e772507212bfe47250721016f66250721017e662507212bfe65250721007e552507212bfb742507212bfb542507210ffb74050721004ff7558321024fe7558321024fc7558321004ff745832101cfe745832101cfc7458321004ff7358321044fc7358321014fe725832100cfd7258321014fc725832104ef64158321006f5415832103ef6215832103ef5215832103efb70583210f6fa305832103efb205832103ef820583210f6fa1058321024fe76d95210ee7e65d952101cfe74d9521004fd74d952101cfc74d95210067e54d95210ee7c54d9521044fe73d9521004fd73d95210ee7f53d9521014fd72d95210ee7f52d952103cff71d952103cfd71d952122e7f51d952122e7d51d952100cfe70d9521004fd70d952100cfc70d95210ee7f50d95210ee7c65595214d5ef725952122cff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff7359521044fc73595214d4ff7259521006ef7259521214ff7159521006f77159521004ff705952100cfe705952100cfc70595210ee7f505952101cfe76d91210e6be64d9121024fe75d9121004fd75d9121024fc75d9121044fe73d9121004fd73d9121014fd72d91210e6bf42d912103cff71d912103cfd71d91211febf41d91211febd41d91211fef631d91214cef721d91211feee21d91211feec21d91211fef421d912100cfe70d9121004fd70d912100cfc70d91211fef710d91210057f75591210ed7c75591210e6bc64591214c5ef7259121004ff75591210067f75591210047f7559121024fe7559121024fc75591210067c75591210247c75591211fcff7459121006bf7459121004ff7359121044fc73591214c4ff7259121006ef72591211e4ff7159121006f771591211e6f631591212bef721591211e6ee21591211e6ec21591211e6f42159121004ff705912100cfe705912100cfc70591210e6bf40591211e6f71059121004ff7655121004fe7655121004fd765
  | 24 => 0xc624c931005f7714c931015f4714c931047d4314c931015dc764c93103edc764c931014dc764c931005df754c931005dd754c931115de744c931115dc744c931045df724c931047cf724c931007cf624c93103ede624c93103edc624c931007cc624c931007ce424c931007cd424c931007d7714c931015de714c931015dc714c931187d4714c931046df614c931047d7614c9314efd7514c931187d4514c931187d6414c931187d6214c931005df704c931187d7104c931045f4765053101ef47650531044f4765053100777755053111df6755053111df4755053100774755053111d747550531006f76550531006f56550531015f77450531017b77450531007b7645053101ef6645053101ef46450531117b46450531117b65450531007b55450531007d77350531045f67350531045f47350531007d47350531016f76350531017d76350531007d65350531007d55350531117d743505313a7b643505313a7b44350531117d44350531117944350531005f772505312bef46250531117b74250531007b54250531007d73250531007d53250531005f77050531117b7405053100cfe76d813110efa60d8131024fe75d8131004fd75d8131024fc75d813101cfe74d8131004fd74d813101cfc74d8131014fd73d813100cfc73d813103cfe72d8131004fd72d8131006df32d8131006dd32d8131044fd71d8131096f641d8131006f541d8131096f621d813110efa30d813110efa10d8131005ef7258131005ec725813110ef8605813103e7f7559721004ff745972101cfe745972101cfc74597210067e54597211067c5459721004ff7359721044fc73597211067f5359721014fe7259721014fc725972103e7e525972103e7c52597212167f51597212167d5159721216f64159721004ff705972100cfe705972100cfc70597211067f5059721004ff7559321024fe7559321024fc755932103ebf7459321006bf54593210febc5459321004ff7359321044fc73593210febf4359321014fe7259321014fc725932103eee525932103ebe425932103ebc42593211e6bf41593211e6bd41593211e6ee215932103eec2159321004ff705932100cfe705932100cfc70593210febf405932103eef2059321004ff765532103cfe7655321004fd765532103cfc7655321004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f2103edf7358f21014fe7258f21014fc7258f2103ede3258f2103edc3258f21186f64158f21186df3158f21186dd3158f2103ef62158f2103ef52158f21004ff7058f2100cfe7058f2100cfc7058f2103eef2058f21044ff7694f2103cfe7694f21004fd7694f2103cfc7694f21015f67194f21005f57194f21004ff7654f2103cfe7654f21004fd7654f2103cfc7654f210267e6554f21
  | 25 => 0x5131505de7694d31046de7694d31275dd7594d31026de6594d31026dc6594d31115de7494d31045dc7494d31006df6494d31006dd6494d31005dd7294d31015de7194d31047d67194d31015d67194d31047d57194d31015dc7194d31046df6194d31047d76194d3111fd75194d3128fd45194d3128fd64194d3128fd62194d31005dd7094d3111f5f5094d3128fd71094d31024ff7654d31014fe7654d31274fd7654d31014fc7654d310067f6554d310267c6554d31005f77154d31015f47154d31277745154d31015dc7654d31026dc7654d31014dc7654d31045df7554d310475f7554d310075f6554d31026de6554d31026dc6554d3111f5c6554d31115de7454d31115dc7454d31006df6454d31006dd6454d3111f5f5454d310075d5454d31005df7254d3111f5f5254d31007d77154d31015de7154d31015dc7154d31277d47154d31046df6154d31047d76154d3111fd75154d312775e5154d312775c5154d31277d45154d31277545154d31277d64154d31277d62154d31005df7054d3111f5f5054d31277d71054d3101cff7650d31014fe7650d31244fd7650d31014fc7650d31006bf6450d3101ebc6450d314fddf7350d310479c4350d31005f77150d31015f47150d3103cfe76d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d8931044fd71d89311c6ef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d89311c6f710d8931006ef629893111d7e75189310057d7518931115be7418931005bd741893103eee6218931006ed621893110dfa7018931005f97018931004fe7694931004fd769493103cfc7694931115be7494931005bd7494931045de7394931005dd7394931015f67194931005f57194931004ff7654931004fe7654931004fc76549310267e65549310067d65549310075d5354931005f77154931015f4715493111f775154931004fe7690931004fd769093103cfc769093111d7e75909310057d7590931045de7390931005dd7390931006ef629093103eec6290931015f67190931005f571909311ffe62190931004ff7650931004fe7650931004fc765093101ebe6450931006bd6450931005df7350931045dc73509311179f4350931006ef625093103eec6250931015f671509311e7e62150931165de76cc931046de76cc931045df75cc931005dd75cc931115de74cc931045dc74cc93103ede62cc93103edc62cc931047d771cc931015de71cc931015dc71cc931047d471cc931046df61cc931047d761cc9314f7d751cc9311c7d451cc9311c7d641cc9311c7d621cc931005dd70cc9311c7d710cc931014fe768c931185dd738c931006ef628c93103eec628c931015f6718c931005f5718c931014fc764c931006ef624c93103ee
  | 26 => 0x57d7590b312067e6590b310067d6590b31045de7390b31005dd7390b3103eee6290b31006ed6290b31004ff7650b31004fd7650b31044fc7650b311ee7e6550b310067d6550b3101ebe6450b31006bd6450b31005df7350b31045dc7350b3112f9f4350b3103eee6250b31006ed6250b31045df764cb31006df764cb31005df754cb31005dd754cb310475e654cb310475d654cb3112dde744cb3112ddc744cb31047cf724cb3103ede624cb3103edc624cb31007ce424cb31007cd424cb31015de714cb31015dc714cb31005df704cb31004ff7558331024fe75583310067e75583310067d7558331024fc7558331004ff745833101cfe745833101cfc7458331014fe735833100cfd7358331014fc7358331004ff725833103cfc7258331046df3258331006dd3258331046f63158331046f53158331046fb7058331126fa4058331046fb3058331046f83058331126fa2058331126fa1058331024fe76d953111e7e65d9531015f671d9531045f571d953111f7751d953101cfe74d9531004fd74d953101cfc74d95310067e54d953111e7c54d9531014fd73d953111e7f53d953103cfe72d9531004fd72d9531044ff71d9531044fd71d953111ef571d9531044f571d953128e7f51d953111ef751d953128e7d51d953128ef451d953128ef641d953100cfe70d9531004fd70d953100cfc70d953111e7f50d953111e7c655953150ddf735953127774515953128cff75595310067f7559531004ff745953101cfe745953101cfc745953150cff7359531006df7359531004ff725953103cfc725953111e7f5259531274ff7159531006f7715953111ef751595312767e51595312767c5159531276f45159531276f64159531004ff705953100cfe705953100cfc705953111e7f505953101cfe76d9131116be64d9131045de73d9131015dd73d91311179f43d9131024fe75d9131004fd75d9131024fc75d9131014fd73d913125edd73d9131014dd73d9131116bf43d9131116df43d9131116dc43d913103cfe72d9131004fd72d9131044ff71d9131044fd71d913125ebf41d913125ebd41d913100cfe70d9131004fd70d913100cfc70d913125ef710d91310057f755913111d7c7559131116bc64591314fddf73591311179c4359131004ff75591310067f75591310047f7559131024fe7559131024fc75591310067c75591310247c755913125cff7459131006bf74591314fcff7359131006df7359131116df43591313a6be43591313a6bc4359131116dc4359131004ff725913103cfc7259131116bf4259131244ff7159131006f77159131004ff705913100cfe705913100cfc7059131116bf4059131246f71059131004ff7655131004fe7655131004fd7655131004fc7655131005df7355131045dc7355131005f77155131015f4715
  | 27 => 0xf7559731004ff745973101cfe745973101cfc74597311367f54597310067e54597311367c5459731014fe7359731014fc73597310467e53597310467c5359731004ff725973103cfc72597311367f52597311367c52597312767f51597312767d5159731004ff705973100cfe705973100cfc70597311367f50597310067e50597311367c50597310067f74597310067e74597310067d74597310067c74597310467f73597310467e73597310467d73597310467c73597310467f43597310467e43597310467d43597310467c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067c42597310467f32597310467e32597310467d32597310467c32597312767f71597312767e71597312767d71597312767c71597312767f41597312767e41597312767d41597312767c41597310467f31597310467e31597310467d31597310467c31597312767f21597312767e21597312767d21597312767c21597310067f70597310047f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067c40597310467f30597310467e30597310467d30597310467c30597310067e20597310067c20597312767f10597312767e10597312767d10597312767c1059731004ff7559331024fe7559331024fc7559331046bf7459331014fe7359331014fc7359331046dc7359331014dc7359331046de535933112edf4359331046be4359331046bc4359331046dc4359331004ff725933103cfc725933112ebf4259331246bf4159331246bd4159331046f63159331046f53159331004ff705933100cfe705933100cfc705933112ebf4059331046df3059331004ff7655331044fe7655331004fd7655331044fc76553310267e65553310067d6555331005df7355331045dc7355331045df7654f31516df7654f310475f7554f31026de6554f310475e6554f310265e6554f310475d6554f31046dc6554f3112dde7454f3112ddc7454f31046df6454f31006dd6454f311375f5454f310075d5454f31005df7254f311375f5254f31015de7154f31015dc7154f312775e5154f312775c5154f31005df7054f311375f5054f31004ff7558b31024fe7558b31024fc7558b31004ff7458b3101cfe7458b3101cfc7458b31014fc7358b31046ef7258b31046ef3258b31046ec3258b31046f63158b31046f53158b31186ef2158b31004ff7058b3100cfe7058b3100cfc7058b31046df3058b3103cff7694b31044fe7694b31004fd7694b310267e6594b310067d6594b3112dbe7494b31005bd7494b31045de7394b31005dd7394b31004ff7654b31004fd7654b31044fc7654b310267e6554b310067d6554b31045de7354b310075d5354b3103cff7690b31044fe7690b31004fd7690b311357e7590b31
  | 28 => 0x89414c6f421d894100cfe70d8941004fd70d894100cfc70d894151ebf40d89414c6f710d89411457e75989410057d75989410067f65989410067c6598941006ef62989410e5f571989411ffe421989410057f75589411457c75589410067f65589410067c65589410fdf771589411e7e421589410067f65189410067c651894103eee6218941006ed6218941004fe7694941004fd769494103cfc76949410067f65949410267c659494101dbe7494941005bd749494103eee6294941015f47194941004ff7654941004fe7654941004fc76549410067f65549410267c655494101dbe745494121f3e5454941005f77154941015f47154941015bc765094103ebc7650941014bc7650941005bf7550941005bd75509410073f65509411eebe65509411eebc65509410073c65509411ee3c65509413a5bc7350941006bf635094101dbf725094101faf7250941007af625094103ebe625094103ebc6250941007ac6250941007ae5250941007ad5250941007b77150941015be7150941015bc71509411e7b4715094101ebf615094101fb761509411e7b651509411e7b631509411e7ae21509411e7ac21509411e7b421509411e7a42150941005bf70509411e7b71050941004fe76cc941004fd76cc941044fc76cc9410067f65cc9411d67c65cc9413a5bf74cc94101dbc74cc941015f671cc941005f571cc941004fe768c941004fd768c94103cfc768c9410067f658c9411b67c658c94101dbe748c941005bd748c941007ad428c941015f4718c941004ff764c941004fe764c941004fc764c9410067f654c9411967c654c941005bf744c94101dbc744c941007ad424c941005f7714c941015f4714c941004fe760c941004fd760c94103cfc760c9411457e750c9410057d750c9410067f650c9411767c650c94101dbe740c941005bd740c941015f6710c941005f5710c94113dfa700c941005f9700c94101df47654541026f4765454101cf47654541015f77554541017777554541007776554541026f66554541026f46554541147746554541007b7745454101df6745454101df47454541157b47454541016f76454541017b76454541157b65454541147b55454541005f77354541007b64354541157b443545412bdf47254541147775254541007755254541157b74254541007b54254541005f77054541147775054541157b7405454100cfe76d81410067f65d81410067c65d814113efa60d81410067f75d8141024fe75d8141004fd75d8141024fc75d81410067c75d8141014fd74d814100cfc74d8141044fe73d8141004fd73d814103cfe72d8141004fd72d81413bebf42d8141006bd42d814101cfd71d81412f6f631d814113efa40d814113efa10d81410057f75581411457c75581410067f65581410067c655814113ef860581410467
  | 29 => 0x53e7d10d954153e7c10d9541024ff76595411467c6559541545bf745954154df7715954153cff75595410067f7559541544ff7459541006bf7459541004ff7359541044fc7359541004ff725954103cfc72595412a4ff7159541006f77159541004ff705954100cfe705954100cfc70595411467f505954153d7e76195411467e761954153c7e76195415373e741954152f3d741954152e7f64195411475e73195411475d73195415373c43195411476e72195411476d72195415373f421954152f76711954153775711954152e7f611954153777411954152f3e411954152f3c411954152f74411954152f76311954152f7421195411477a70195410057d70195411477970195410057970195410067e60195410067c60195415373f401954152f771019541015bc7655141026bc7655141014bc765514101dbf755514101f3f75551410073f6555141026be6555141026bc65551411473c65551413a5bc73551411473f5355141005bf7255141007b77155141015be7155141015bc71551412a7b4715514101ebf615514101fb761551412a7b651551412a7b631551412a7b42155141005bf70551411473f50551412a7b71055141044fe76d8d410067f65d8d410067c65d8d41024fe75d8d41004fd75d8d41024fc75d8d41014fd74d8d414febd74d8d41526de43d8d41526dd43d8d413a6bc43d8d4103cfe72d8d41004fd72d8d41526bf42d8d4101cfd71d8d414fedf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41526bf40d8d414fef710d8d411457e7598d410057d7598d410067f6598d410067c6598d41006df6398d413a79c4398d41115f57198d410057f7558d411457c7558d410067f6558d410067c6558d411179c4358d4112df77158d410067f6518d410067c6518d41046de6318d41006dd6318d41004fe7694d41004fd7694d41044fc7694d410067f6594d410267c6594d4101dbc7494d41046de6394d41015f67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410067f6554d410267c6554d41005bf7454d4101dbc7454d410073d5454d41015f67154d41277765154d41015be7690d4125ebe7690d41014be7690d413a5bf7590d41005bd7590d410073f6590d410073c6590d4101dbe7390d4101f9e7390d413a6bf6390d410079f6390d413a79c6390d413a79e5390d410079d5390d41005bd7290d41015be7190d4125fb67190d413a7b57190d41015bc7190d4101ebf6190d4101fb76190d4125fb65190d4125fb63190d4125fb42190d41005bd7090d4125fb71090d4103cfe76d89410067f65d89410067c65d8941024fe75d8941004fd75d8941024fc75d8941014fd74d8941044fe73d8941004fd73d894151eee42d894151eed42d894101cfd71d894151ef571d89414c6f631d89414c6ef21d
  | 30 => 0xc64549510067f63549510257f72549510276f72549510076f625495103e7e625495103e7c62549510076c62549510077771549510157e71549510157c71549512177471549510267f61549510277761549512177641549510057f7054951004fe7690951004fd769095103cfc76909510257e75909510057d7590951006ef629095103eec62909510076d5290951004ff7650951004fe7650951004fc7650951006bf645095101ebc6450951006ef625095103eec62509510076d5250951004fe76cc951004fd76cc951044fc76cc951004fe768c951004fd768c95103cfc768c9510257e758c9510057d758c951004ff764c951004fe764c951004fc764c951004fe760c951004fd760c95103cfc760c9510257e750c9510057d750c951155be740c951005bd740c951015f6710c951005f5710c95114dfa700c951005f9700c95100cfe76d815114efa60d81510ce7f75d8151014fd75d815100cfc75d815100c7c75d815101cfe74d8151004fd74d815101cfc74d8151044fe73d8151004fd73d815103cfe72d8151004fd72d815146e7f52d81510067d52d8151024fd71d81510ce7e51d81510ce7c51d81510cef641d815114e7f50d815114efa50d815114efa10d815114ef86058151024fe76d95411467e65d95412a4fd75d9541014ff74d9541014fd74d95415567f54d95415567d54d9541044fe73d9541004fd73d95411467f53d95411467c53d954103cfe72d9541004fd72d95411467f52d95411467c52d954101cff71d954101cfd71d954153e7f51d954153e7d51d954100cfe70d9541004fd70d954100cfc70d95411467f50d95410067e50d95411467c50d954152d7e76d95410247e76d954153f3f74d954153f3c74d95415573c43d95415573f42d95415577771d954153f7471d95415577741d954153f3e41d954153f3c41d954153f7441d954153f7631d954153f7421d95410057d70d95410067e60d95410067c60d95415573f40d954153f7710d954153e7f74d95415567e74d954153e7d74d954153e7c74d95410067f73d95410067e73d95410067d73d95410067c73d95415567f43d95415567e43d95415567d43d95415567c43d95410067f72d95410067e72d95410067d72d95410067c72d95415567f42d95415567e42d95415567d42d95415567c42d954153e7f71d954153e7e71d954153e7d71d954153e7c71d954153e7f41d954153e7e41d954153e7c41d954153e7f31d954153e7e31d954153e7d31d954153e7c31d954153e7f21d954153e7e21d954153e7d21d954153e7c21d95410067f70d95410067e70d95410067d70d95410047d70d95410067c70d95415567f40d95415567e40d95415567d40d95415567c40d95410067e30d95410067c30d95410067e20d95410067c20d954153e7f10d954153e7e10d9541
  | 31 => 0x843203ef5205843203ef42058432004ff7558032024fe75580320067e75580320067d7558032024fc7558032004ff745803201cfe745803201cfc745803203edf325803203eee325803203edd3258032046ed3258032004ff7158032014fe7158032014fc715803203cff705803203efb7058032006fb505803215efa505803215ef85058032006fb405803215efa405803215ef84058032046fb3058032046f8305803203efb205803203ef82058032006fb105803215efa105803215ef81058032006fb7558032006fa75580320067a7558032006f97558032006797558032006f87558032006fb7458032006fa7458032006f97458032006f87458032006fb5458032006fa5458032006f95458032006f85458032046fb7358032046fa7358032046f87358032046fb5358032046fa5358032046f95358032046f85358032046fb4358032046fa4358032046f94358032046f8435803203efb725803203efa725803203ef8725803203efb525803203efa525803203ef9525803203ef8525803203efb425803203efa425803203ef9425803203ef8425803203efb325803203edb325803203efa325803203eea325803203ef9325803203ed93258032046e9325803203ef83258032006fb7158032006fa7158032006f97158032006f87158032006fb5158032006fa5158032006f85158032006fb4158032006fa4158032006f84158032046fb3158032046fa3158032046f93158032046f8315803203efb215803203efa215803203ef9215803203ef8215803201cfe76d9151156be64d9151014fd75d9151156be54d9151576bd54d9151044fe73d9151004fd73d915103cfe72d9151004fd72d9151156bf42d9151024fd71d9151546bf41d915100cfe70d9151004fd70d915100cfc70d91515767f50d9151156bc645915156df77159151044fe76d8d51014fd75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51566de53d8d51566dd53d8d5103cfe72d8d51004fd72d8d515667f52d8d51024fd71d8d51566f751d8d5150e7e51d8d5150e7c51d8d5150ef451d8d5150ef641d8d5150edf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d515667f50d8d51006df6398d5111df57198d51135f77158d51046de6318d51006dd6318d51004fe7690d51004fd7690d51044fc7690d51004ff7650d51004fe7650d51004fc7650d5103cfe76d8951014fd75d895101cfe74d8951004fd74d895101cfc74d8951044fe73d8951004fd73d895155eee52d895155eed52d8951024fd71d89514d6ef21d895100cfe70d8951004fd70d895100cfc70d895155e7f50d8951155be7498951005bd7498951006ef62989510edf57198951105f7715895103eee6218951006ed62189510157c765495103e7c76549510147c765495121e7e645495121e7
  | 32 => 0x46be4359032046bc435903203cfe725903203cfc725903203ebe425903203ebc425903203eee3259032046ed3259032004ff7159032014fe7159032014fc715903216ebf4159032006be415903216ebc4159032004ff705903200cfe705903200cfc705903216ebf4059032006be405903216ebc4059032006bf7559032006be7559032006bd7559032006bc7559032046bf7359032046be7359032046bd7359032046bc7359032046bf5359032046be5359032046bd5359032046bc535903203ebf725903203ebe725903203ebd725903203ebc725903203ebf525903203ebe525903203ebd525903203ebc525903203ebf325903203ebe325903203eae325903203ebd3259032046ad325903203ebc3259032006bf7159032006be7159032006bd7159032006bc7159032006bf5159032006be5159032006bc5159032046bf3159032046be3159032046bd3159032046bc315903203ebf215903203ebe215903203ebd215903203ebc2159032006bf7059032006be7059032006bd7059032006bc7059032006bf5059032006be5059032006bc5059032046bf3059032046be3059032046bd3059032046bc305903203ebf205903203ebe205903203ebd205903203ebc2059032006bf1059032006be1059032006bc1059032004ff765503203cfe7655032004fd765503203cfc76550320267e65550320067d655503201ebe6455032006bd64550322a6f6615503229efa6055032004ff7558432024fe7558432024fc7558432004ff745843201cfe745843201cfc745843203edf325843203edd325843203cff715843203ef77158432006f75158432166f65158432166f45158432006f74158432166f64158432166f44158432046f73158432046f4315843203ef7215843203ef42158432004ff705843200cfe705843200cfc7058432166f71058432006f61058432166f41058432006f77558432006f67558432006f57558432006f47558432006f77458432006f67458432006f57458432006f47458432006f75458432006f65458432006f55458432006f45458432046f77358432046f67358432046f47358432046f75358432046f65358432046f55358432046f45358432046f74358432046f64358432046f54358432046f4435843203ef7725843203ef6725843203ef4725843203ef7525843203ef6525843203ef5525843203ef4525843203ef7425843203ef6425843203ef5425843203ef4425843203ef7325843203ed7325843203ef6325843203ef5325843203ed5325843203ef43258432006f77058432006f67058432006f57058432006f47058432006f75058432006f65058432006f45058432006f74058432006f64058432006f44058432046f73058432046f63058432046f53058432046f4305843203ef7205843203ef6205
  | 33 => 0xf639093203fcf63909321feee61909321feec6190932005ed709093201cff765093218cfd7650932044fc7650932006bf645093201ebc6450932005df7350932045dc735093203fac4250932045ec765093201eec7650932044ec7650932006ef6550932006ed655093203def745093203faf7450932007af645093201eee645093201eec645093218fac645093257faf545093218fac5450932007cf7350932045ee7350932045ec7350932007cc735093203eef635093203fcf635093218faf4350932007ad43509321e6ee61509321e6ec615093218faf4150932005ef705093218faf4050932014fe76d8532186f661d8532024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853203cfd73d8532044fd72d8532186f641d8532186f631d8532186f621d853200cfe70d8532004fd70d853200cfc70d8532186f4615853200cfe76d813217efa60d8132024fe75d8132004fd75d8132024fc75d813201cfe74d8132004fd74d813201cfc74d813203cfd73d8132044fd72d8132006ee42d8132006ed42d8132014fe71d8132004fd71d8132014fc71d813217efa50d813217efa30d813217efa20d813217ef8605813203cff755943203e7f7559432004ff745943201cfe745943201cfc74594321767f54594320067e54594321767c5459432044fe7359432044fc73594320467e53594320467c535943203cfe725943203cfc725943203e7e525943203e7c5259432004ff7159432014fe7159432014fc71594321767f51594320067e51594321767c5159432004ff705943200cfe705943200cfc70594321767f50594320067e50594321767c50594320067f74594320067e74594320067d74594320067c74594320467f73594320467e73594320467d73594320467c73594320467f43594320467e43594320467d43594320467c435943203e7f725943203e7e725943203e7d725943203e7c725943203e7f425943203e7e425943203e7d425943203e7c425943203e7f325943203e7e325943203e7d325943203e7c32594320067f71594320067e71594320067d71594320067c71594320067f41594320067e41594320067c41594320467f31594320467e31594320467d31594320467c315943203e7f215943203e7e215943203e7d215943203e7c21594320067f70594320047f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067c40594320467f30594320467e30594320467d30594320467c305943203e7f205943203e7e205943203e7d205943203e7c20594320067f10594320067e10594320067c1059432004ff7559032024fe7559032024fc755903203cff745903203ebf7459032006bf545903216ebe545903216ebc5459032044fe7359032044fc7359032
  | 34 => 0x8e32024ff7654e3203cfc7654e320267e6554e320067d6554e32005ef7254e3203dec7254e3201cff7650e3203cfc7650e3201ebe6450e32006bd6450e320479c4350e32005ef7250e3203dec7250e3203def7650a3216eef7650a3203eef6550a32006ed6550a3203faf7450a3203faf6450a3201eee6450a3203eec6450a3203fac6450a32587af5450a321afac5450a32045ee7350a32045ec7350a321afaf4350a32007ad4350a321e6ee6150a3203eec6150a321afaf4150a32005ef7050a321afaf4050a32004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc745863203cfc725863203edf325863203edd325863203ef771586321a6f6315863203ef7215863203ef42158632004ff705863200cfe705863200cfc705863203eef20586321a6f71058632004ff7558232024fe7558232024fc7558232004ff745823201cfe745823201cfc745823203cfc725823203eee4258232006ed425823203edf325823203edd3258232004ff7158232014fe7158232014fc715823203efb705823219efa305823203efb205823203ef8205823219efa1058232024fe76d95321967e65d953201cfe74d9532004fd74d953201cfc74d953203cfd73d95321967f53d9532044fd72d95321967f52d9532014fe71d9532004fd71d9532014fc71d953200cfe70d9532004fd70d953200cfc70d95321967f50d95321967c6559532194ff75595320067f7559532004ff745953201cfe745953201cfc74595321b4ff7359532006df73595321d4ff7259532006ef7259532004ff7159532014fe7159532014fc7159532004ff705953200cfe705953200cfc70595321967f505953201cfe76d913218ebe64d9132024fe75d9132004fd75d9132024fc75d913203cfd73d913218ebf43d9132044fd72d913218ebf42d9132014fe71d9132004fd71d9132014fc71d913218ebf41d913200cfe70d9132004fd70d913200cfc70d913218ebc6459132004ff7559132024fe7559132024fc755913218cff7459132006bf74591321acff7359132006df73591321ccff7259132006ef7259132004ff7159132014fe7159132014fc7159132004ff705913200cfe705913200cfc705913218ebf4059132004ff7655132004fe7655132004fd7655132004fc765513203cfc7654d320067f6554d320267c6554d32005ef7254d3203dec7254d32047cc3254d3203cfc7650d32006bf6450d3201ebc6450d32005ef7250d3203dec7250d32024ff7654932194fd7654932044fc76549320067f65549320267c6554932005df7354932045dc735493203fcc3254932005ee769093203eee769093203f6e759093203f6d7590932006ef6590932006ed659093218ded749093201eee649093201eec6490932045ee739093203dec739093203ee
  | 35 => 0x6ed52d85421e6f641d85421e6ee21d85421e6f621d85421e6ec21d854200cfe70d8542004fd70d854200cfc70d85420febf40d85420057f75585421ed7c75585421e6f461585421e7e4215854200cfe76d81421defa60d8142024fe75d8142004fd75d8142024fc75d814203cfd74d8142044fe73d8142004fd73d814206ebf43d8142006bd43d814201cfd72d8142014fe71d8142004fd71d8142014fc71d814206ebf41d81421defa40d81421defa20d8142005df7358142005dc73581421def860581420467f7559732004ff745973201cfe745973201cfc74597321d67f545973203cfc73597320467e53597320467c53597321d67f5259732004ff7159732014fe7159732014fc71597320067e51597321d67c5159732046df3159732004ff705973200cfe705973200cfc70597321d67f5059732004ff7559332024fe7559332024fc7559332046bf745933203cfc7359332046be4359332046bc43593321cebf4259332046ee3259332046ed3259332004ff7159332014fe7159332014fc7159332004ff705933200cfe705933200cfc70593321cebf4059332046df3059332004ff7655332044fe7655332004fd7655332044fc76553320267e65553320067d6555332024ff7654b32044fc7654b320267e6554b320067d6554b32005df7354b32045dc7354b3201cff7650b32044fc7650b3201ebe6450b32006bd6450b32005df7350b32045dc7350b32004ff7558732024fe7558732024fc7558732004ff745873201cfe745873201cfc745873203cfc7358732046f77158732006f751587321c6f451587321c6f64158732046f73158732046f431587321c6f62158732004ff705873200cfe705873200cfc7058732046df30587321c6f71058732004ff7558332024fe7558332024fc7558332004ff745833201cfe745833201cfc745833203cfc7358332046ee3258332046ed3258332004ff7158332014fe7158332014fc7158332046df3158332046fb70583321befa4058332046fb3058332046f830583321befa205833203e7f7559632004ff745963201cfe745963201cfc74596320067e54596321b67c54596321b67f535963203cfc725963203e7e525963203e7c525963203eee4259632004ff7159632014fe7159632014fc71596321b67f5159632004ff705963200cfe705963200cfc70596321b67f5059632004ff7559232024fe7559232024fc755923203ebf7459232006bf54592321aebc54592321aebf435923203cfc725923203ebe425923203ebc4259232004ff7159232014fe7159232014fc71592321aebf4159232004ff705923200cfe705923200cfc70592321aebf405923203eef2059232004ff765523203cfe7655232004fd765523203cfc7655232046ef3258e3203ede3258e3203edc3258e3203eec325
  | 36 => 0xd70d954200cfc70d95421ee7f50d95421ee7c655954221f3c545954259def7259542234ff75595420067f755954221cff7459542006bf74595421eebf545954221e7e545954221e7c545954221ebc5459542004ff7359542044fc73595421ee7f535954259cff7259542006ef7259542004ff7159542014fe7159542014fc715954221ebf4159542004ff705954200cfe705954200cfc70595421ee7f5059542024fe75d8d42004fd75d8d42024fc75d8d4203cfd74d8d421aede43d8d421aedd43d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d421aebf40d8d42006de30d8d42006dc30d8d42006df6398d4218ded7298d421cdef7258d421ed7e7518d420057d7518d42046de6318d42006dd6318d421e5f67118d42005f57118d421ddfa7018d42005f97018d42004fe7694d42004fd7694d42044fc7694d4201dbe7494d42005bd7494d4203dee7294d42005ed7294d421e5f67194d42005f57194d42004ff7654d42004fe7654d42004fc7654d420267e6554d420067d6554d42005bf7454d4201dbc7454d421ef3f5454d4203cbc7650d421edbe7550d421edbc7550d4201dbf7350d4201f9f7350d420079f6350d42046be6350d42046bc6350d420079c6350d420469c6350d420079e5350d420079d5350d42007af7250d4203dbe7250d4203dbc7250d42007ac7250d4201ebf6250d4201faf6250d42005bf7150d42597ae2150d42597ac2150d42005bf7050d4258dee769494203eee769494221ded7594942026ee6594942026ec659494201dee749494203fae749494201dae749494203fad749494203dec749494203eef649494203faf64949421efaf5494942237ac5494942005ed7394942237af4394942007ad43949421e5ee719494203dec7194942237af4194942005ed70949421ef6f5094942237af4094942024ff765494201cfe765494221cfd765494201cfc76549420067f65549420267c6554942005bf745494201dbc745494221f3c545494201dec7654942026ec765494201cec765494203def755494203f6f75549420076f6554942026ee6554942026ec65549421ef6c6554942007af745494201dee745494201dec745494221fac745494203eef645494203faf64549421efaf545494221f6e545494221f6c545494221fac545494221f2c5454942005ef73549421ef6f53549420076d535494221faf4354942007ad43549421e5ee71549421e5ec71549421ef6f515494221faf4154942005ef70549421ef6f505494221faf4054942014fe76d854203dee72d854201ded72d85421e6f661d85421e7e621d8542024fe75d8542004fd75d8542024fc75d854203cfd74d8542044fe73d8542004fd73d854201cfd72d85421e6ed72d854201ced72d8542006ee52d8542
  | 37 => 0x964221e7e435964221e7d435964221e7c435964203e7f725964203e7e725964203e7d725964203e7c725964203e7f425964203e7e425964203e7d425964203e7c425964203e7f325964203e7e325964203e7d325964203e7c32596420067f71596420067e71596420067d71596420067c715964221e7f415964221e7e415964221e7d415964221e7c41596420067e31596420067c315964203e7f215964203e7e215964203e7d215964203e7c21596420067f70596420047f70596420067e70596420067d70596420067c705964221e7f405964221e7e405964221e7d405964221e7c40596420067e30596420067c305964203e7f205964203e7e205964203e7d205964203e7c20596420067f10596420067e10596420067c1059642004ff7558e42024fe7558e42024fc7558e4203edf7358e4218ede4358e4218edd4358e4203cfc7258e4203ebf4258e4203ebd4258e4203ede3258e4203edc3258e42004ff7158e42014fe7158e42014fc7158e42004ff7058e4200cfe7058e4200cfc7058e4203eef2058e42044ff7694e4203cfe7694e42004fd7694e420267e6594e420067d6594e4203dee7294e42005ed7294e421fdf67194e42005f57194e42004ff7654e42004fd7654e4203cfc7654e420267e6554e420067d6554e4203dee7254e4203def7654a425a6ef7654a4203f6f7554a42026ee6554a4203f6e6554a420266e6554a4203f6d6554a4203eec6554a4201dee7454a4201dec7454a4221f6e5454a4221f6c5454a42005ef7354a422076f5354a420076d5354a421fdee7154a421fdec7154a422076f5154a42005ef7054a422076f5054a42004ff7558642024fe7558642024fc7558642004ff7358642044fc735864203cfe725864203cfc725864203eec725864203cec725864203eee5258642006ed525864203ebf425864203ebd425864203ef771586421fef641586421fef6315864203ef721586421feee215864203eec215864203ef42158642004ff705864200cfe705864200cfc705864203eef20586421fef71058642004ff7558242024fe75582420067e75582420067d7558242024fc7558242004ff7358242044fc735824203cfe725824203cfc725824203ebf425824203ebd425824203eee3258242004ff7158242014fe7158242014fc715824203efb70582421f6fa40582421f6fa305824203efb205824203ef820582421f6fa1058242024fe76d95421ee7e65d954201dbe74d954203dbd74d95421ef3f54d954203cff74d954203cfd74d95421eebd74d954203cbd74d95422367f54d95421eebf54d95422367d54d9542236bc54d9542044fe73d9542004fd73d954201cfd72d95421ee7f52d9542014fe71d9542004fd71d9542014fc71d95420067e51d95421ee7c51d9542236bf41d954200cfe70d9542004f
  | 38 => 0x3cfe725825203cfc725825203e7f525825203e7d525825203eee4258252004ff7158252014fe7158252014fc715825203eef215825203efb70582522267f5058252226fa5058252226fa305825203efb205825203ef82058252226fa105825201cfe76d91520257e75d915221ebe64d915221f3e54d915203cfd75d915203c7d75d915221e7e54d915221ebe54d9152206bd54d915221e7c54d9152044fe73d9152004fd73d91522067f53d9152024fd72d915221ebf42d9152014fe71d9152004fd71d9152014fc71d915200cfe70d9152004fd70d915200cfc70d91522067f50d915221ebc645915221f3c54591525adef725915203cfd75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d521b6de53d8d521b6dd53d8d52014fe71d8d52004fd71d8d52014fc71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d521b67f50d8d52006df6398d52195ed7298d52215f67198d52005f57198d521d5ef7258d52046de6318d52006dd6318d5203c7c7654d5221d7e7454d5221d7c7454d520067f6454d520257f7354d520275f7354d520075f6354d520467e6354d520467c6354d520075c6354d520076f7254d5203d7e7254d5203d7c7254d520076c7254d520267f6254d520276f6254d520057f7154d522767e6154d522767c6154d520057f7054d52004fe7690d52004fd7690d52044fc7690d520257e7590d520057d7590d520075d5390d52004ff7650d52004fe7650d52004fc7650d520057f7550d520257c7550d520075d5350d52014fe76d8552216f661d855203cfd75d855201cfe74d8552004fd74d855201cfc74d8552044fe73d8552004fd73d8552024fd72d8552216f651d8552216f641d8552216f631d8552216f621d855200cfe70d8552004fd70d855200cfc70d85521067f50d8552006f610d8552216f410d8552216f4615855200cfe76d815220efa60d815247e7f75d815203cfd75d815201cfe74d8152004fd74d815201cfc74d81520067e54d81520767c54d8152044fe73d8152004fd73d81520767f53d81520067d53d8152024fd72d815247e7e52d815247e7c52d8152014fe71d8152004fd71d8152014fc71d81520767f51d815220e7f50d815220efa50d815220efa20d8152005f77158152215f4715815220ef8605815203e7f755964221e7f545964221e7d5459642004ff7359642044fc73596422067f53596422067c535964203cfe725964203cfc725964203e7e525964203e7c5259642004ff7159642014fe7159642014fc71596422067f51596420067e51596422067c5159642004ff705964200cfe705964200cfc70596422067f50596420067e50596422067c505964221e7f745964221e7e745964221e7d745964221e7c74596420067f73596420067e73596420067d73596420067c735964221e7f435
  | 39 => 0xe75d8543004fd75d8543024fc75d8543044fd74d854301cfd73d8543006de53d8543006dd53d854312edf43d85435b6be43d85435b6bc43d854312edc43d854303cfe72d8543004fd72d854312ebf42d8543246f641d8543246f631d854300cfe70d8543004fd70d854300cfc70d854312ebf40d85430057f755854324d7c7558543246f4615854300cfe76d814323efa60d8143024fe75d8143004fd75d8143024fc75d8143044fd74d814301cfd73d814303cfe72d8143004fd72d814309ebf42d8143014fe71d8143004fd71d8143014fc71d814323efa40d814323efa30d814323ef8605814303ebf7459252236be54592521eebd5459252004ff7359252044fc7359252236bf4359252236bc435925203cfe725925203cfc725925203ebe425925203ebc4259252004ff7159252014fe7159252014fc7159252236bf4159252006be4159252236bc4159252004ff705925200cfe705925200cfc70592521ee7f5059252236bf4059252006be4059252236bc40592521eebe75592521eebd7559252236bc7559252006bf7359252006be7359252006bd7359252006bc73592521eebf53592521eebe53592521eebd53592521eebc535925203ebf725925203ebe725925203ebc725925203ebf525925203ebe525925203ebd525925203ebc525925203ebf325925203ebe325925203ebd325925203ebc3259252006bf7159252006be7159252006bd7159252006bc71592521eebf51592521eebe51592521eebd51592521eebc5159252006be3159252006bc315925203ebf215925203ebe215925203ebd215925203ebc2159252006bf7059252006be7059252006bd7059252006bc70592521eebf50592521ee3f50592521eebe50592521eebd50592521eebc5059252006be3059252006bc305925203ebf205925203ebe205925203ebd205925203ebc2059252006bf1059252006be1059252006bc1059252004ff7458e5201cfe7458e5201cfc7458e5203edf7358e52196de5358e52196dd5358e5203cfc7258e5203e7f5258e5203e7d5258e5203eee4258e5203ede3258e5203edc3258e52004ff7158e52014fe7158e52014fc7158e52004ff7058e5200cfe7058e5200cfc7058e521967f5058e52044ff7690e5203cfe7690e52004fd7690e5201ebe6490e52006bd6490e52004ff7650e52004fd7650e5203cfc7650e5201ebe6450e52006bd6450e52004ff745865201cfe745865201cfc7458652004ff7358652044fc735865203cfe725865203cfc725865203e7f525865203e7d525865203ef7715865222ef6515865222ef6315865203ef7215865203ef42158652004ff705865200cfe705865200cfc70586520ee7f505865222ef710586520067d7558252004ff745825201cfe745825201cfc7458252004ff7358252044fc7358252
  | 40 => 0x4e432675f5254e435d75e5154e432675c5154e4327f9f4154e43005df7054e432675f5054e43004ff7558a43024fe7558a43024fc7558a43044fc7358a43046bf4358a43046bd4358a43046ef7258a4318eee4258a43046ef3258a43046ec3258a43004ff7158a43014fe7158a43014fc7158a4318ebf4158a43004ff7058a4300cfe7058a4300cfc7058a43046df3058a43004ff7558643024fe7558643024fc7558643044fe7358643044fc7358643046de5358643006dd5358643116df4358643046dc4358643004ff725864303cfc7258643046f77158643006f7515864325ef4515864325ef64158643046f73158643046f4315864325ef62158643004ff705864300cfe705864300cfc7058643046df305864325ef71058643004ff7558243024fe7558243024fc7558243044fe7358243044fc7358243046bf4358243046bd4358243004ff725824303cfc7258243004ff7158243014fe7158243014fc7158243086bf4158243046fb7058243256fa4058243046fb3058243046f83058243256fa2058243024fe76d954324e7e65d9543044ff74d9543044fd74d95432967f54d95432967d54d954301cfd73d954324e7f53d954303cfe72d9543004fd72d954324e7f52d9543014fe71d9543004fd71d9543014fc71d95430067e51d954324e7c51d954300cfe70d9543004fd70d954300cfc70d954324e7f50d954324e7c65595435cddf7359543294ff75595430067f755954327cff7459543006bf74595435ccff7359543006df7359543004ff725954303cfc7259543004ff7159543014fe7159543014fc7159543004ff705954300cfe705954300cfc705954324e7f50595435c5de7694d43046de7694d4327ddd7594d43026de6594d43026dc6594d4301dde7494d43045dc7494d43046df6494d430479f6494d432979f4294d43047d67194d43047d57194d43005dd7094d4324f5f5094d432979f4094d43024ff7654d4301cfe7654d4327cfd7654d4301cfc7654d430067f6554d430267c6554d43005bf7454d4301dbc7454d430475c5354d430479c4354d4301ddc7654d43026dc7654d4301cdc7654d43045df7554d430475f7554d430075f6554d43026de6554d43026dc6554d4324f5c6554d430079f7454d4301dde7454d4301ddc7454d4327f9c7454d43046df6454d430479f6454d4327f5f5454d4327f5d5454d4324f5f5254d4327f9f4254d435bf5e5154d4324f5c5154d43005df7054d4324f5f5054d4327f9f4054d43024fe75d8943004fd75d8943024fc75d8943044fd74d89431ceee42d8943014fe71d8943004fd71d8943014fc71d894300cfe70d8943004fd70d894300cfc70d89431cebf40d894324d7e75989430057d7598943006ef629894303eee6218943006ed6218943014fe76d8543246f661d8543024f
  | 41 => 0x11ef45058653006f74058653006f64058653006f44058653046f73058653046f63058653046f53058653046f43058653006f62058653006f420586530067d7558253004ff745825301cfe745825301cfc7458253044fe7358253044fc73582530467f53582530467d5358253046de4358253004ff725825303cfc7258253004ff7158253014fe7158253014fc7158253046df3158253046fb70582532867f5058253286fa5058253286fa4058253046fb3058253046f83058253286fa205825301cfe76d915327ebe64d9153044fd75d915327ebe54d9153266bd54d9153024fd73d915327ebf43d915303cfe72d9153004fd72d915327ebf42d9153014fe71d9153004fd71d9153014fc71d915327ebf41d915300cfe70d9153004fd70d915300cfc70d91532667f50d9153006be40d915327ebc40d915327ebc64591535e5df73591530457c765515301e7c76551530447c76551530257f74551530273f74551530073f645515301e7e645515301e7c645515327f3c64551530075f73551530457e73551530457c73551530075c73551530267f63551530275f63551530057f72551532757e71551532757c715515327f3f41551530057f7055153044fd75d895301cfe74d8953004fd74d895301cfc74d89531d6ee52d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d89531d67f50d895327dbe7498953005bd7498953006ef629895303eee6218953006ed6218953014fe76d85530257e75d8553276f661d85532777651d8553044fd75d85530447d75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d855303cfe72d8553004fd72d85531367f52d85532767e51d8553276f651d85532767c51d8553276f631d855300cfe70d8553004fd70d855300cfc70d85531367f50d8553276f4615855327774515855300cfe76d815326efa60d81534867f75d8153044fd75d815301cfe74d8153004fd74d815301cfc74d81530a67f54d81530067d54d8153024fd73d81534867e53d81534867c53d815303cfe72d8153004fd72d81530a67f52d8153014fe71d8153004fd71d8153014fc71d81530067e51d81530a67c51d815326e7f50d815326efa50d815326efa30d8153005bf745815327dbc745815326ef860581530467f755964327e7f545964327e7d5459643044fe7359643044fc73596430467e53596430467c5359643004ff725964303cfc72596432667f5259643004ff7159643014fe7159643014fc71596430067e51596432667c515964327ebf4159643004ff705964300cfe705964300cfc70596432667f5059643045df7654e435dedf7654e430475f7554e430475f6554e43026de6554e43046dc6554e430475c6554e4301dde7454e4301ddc7454e4327f5f5454e4327f5d545
  | 42 => 0xc70d8d545e67f50d8d54006df6398d542a5f67198d54005f57198d54046de6318d54006dd6318d5403cfe76d895401cfd75d8954024fd74d89545aebf54d895459e7e54d895459e7c54d895459ebc54d8954044fe73d8954004fd73d89545ae7f53d89545aeee52d895459eee42d8954014fe71d8954004fd71d8954014fc71d895459ebf41d895400cfe70d8954004fd70d895400cfc70d89545ae7f50d8954006ef629895403eee6218954006ed6218954014fe76d85542a6f661d855401cfd75d8554024fd74d8554044fe73d8554004fd73d855403cfe72d8554004fd72d85542a6f651d85542a6f641d85542a6f631d855400cfe70d8554004fd70d855400cfc70d855456e7f50d85542a6f4615855400cfe76d815429efa60d81540d67f75d815401cfd75d8154024fd74d81540d67e54d81540d67c54d8154044fe73d8154004fd73d81544767f53d815403cfe72d8154004fd72d8154014fe71d8154004fd71d8154014fc71d81540d6bf41d815429e7f50d815429efa50d815429efa40d815429ef86058154046bf7459253296be545925324ebd5459253044fe7359253044fc73592530467f53592530467d5359253046be4359253046bc4359253004ff725925303cfc7259253296bf4259253004ff7159253014fe7159253014fc7159253004ff705925300cfe705925300cfc705925324e7f5059253296bf4059253004ff7458a5301cfe7458a5301cfc7458a53044fc7358a530467f5358a530467d5358a53046ef7258a53196ee5258a53046ef3258a53046ec3258a53004ff7158a53014fe7158a53014fc7158a53046df3158a53004ff7058a5300cfe7058a5300cfc7058a531967f5058a53004ff745865301cfe745865301cfc7458653044fe7358653044fc7358653004ff725865303cfc7258653046f7715865328ef65158653006f7415865328ef6415865328ef44158653046f73158653046f4315865328ef6215865328ef42158653004ff705865300cfe705865300cfc705865311e7f505865328ef71058653006f6105865328ef4105865311ef6755865311ef5755865328ef47558653006f77458653006f67458653006f57458653006f4745865311ef7545865311ef6545865311ef5545865311ef45458653046f77358653046f67358653046f47358653046f75358653046f65358653046f55358653046f45358653046f74358653046f64358653046f54358653046f44358653006f77258653006f67258653006f57258653006f4725865311ef7525865311ef6525865311ef5525865311ef45258653006f74258653006f44258653046f73258653046f63258653046f53258653046f43258653006f77058653006f67058653006f57058653006f4705865311ef7505865311e77505865311ef6505865311ef55058653
  | 43 => 0x10004000000000300000010000013001400000000000010008000000a0010001000c007001000000000100004000000800000380000004003001000300600120000000003c0000000006000400200000020010003000c000004400200140000000000001c00600040010000006001c003002c0060004000001c002000800000040010010000000c0020004000000000000100000010000000000e0000000001400600000000014000002000d0000000000400000000000000003000000000100000000007001000400040010008008001c000000000300140010000001000000200000000010001001400000000000000000000c001000400500040000004001000c00400000000008003000c008000000200000030000025000000000140030004009001c00300040030018008000400200000020004004000400d0008004004000000100020024004000000100100100008000002c00100080000008000000000e0000006003000400040010058004001c007000000000300010000000000000200000030000007000400200100000000000000000300040030008001001800500000060024001001400000000020004000000000200000000000004000000100000010044000001800000080000010003005800000000000004001000400000000070004000002c0000000003000c004000800900000000000004000c0000010001001400200000000000000002c0020000010000800100100010010000000c007001800100080010000002000800d0014004003800300000000000003000000500080000028003002c0030000001000400400140030020008000000700080040000000000800f00000010000001001c00700140010004001000c00300200130000002000000100100000000005005c0050000000000400000080000000008000400300200040004001001000800000000014000000c01300140020000003002c01f0010000001400b000800400240000020002005401b00000020000000000c0010008001000c013002c0000014000000800200080050010002000000700000020008000000000200000000000004000400500000070004001000c00f00040000000002000c0040008001001c0000024000000400000000010004010001000200080000000000000c00000000030000000001800000240140000008001800700000040000001000000400000010020004000000000000010008000000c00300040030000000002001c000000000040030008004006800b0010000000400200b8004000c0460030003000000400000040000013044fe76d8d5401cfd75d8d54024fd74d8d545e6de53d8d545cede43d8d5403cfe72d8d54004fd72d8d54014fe71d8d54004fd71d8d54014fc71d8d5400cfe70d8d54004fd70d8d5400cf
  | 44 => 0x240000000000001c00000400080000000001400e000c000002000c000000300000050018007000c001000c0010000009005c0000000000000400000240000000001000c00900340010004001000000000240050004000001400000000000004002002800000040030028000000000d000000400200000000003000c00b002c00200200000000000000000100300010004000001c0000008001000c00500080060000000000400e0000003000400800040010000000000c00000100000000011000000000340000010000000000200080040024003000000500fc01b00240040000000000000200480040000000000800000080050020006000800d002c000000000000180000020003000c0020024000000c002000000200180030000001001c00000740030004005000000000080090004001000000000100020004000000000000000070000003000000100180000004006000000300000050000002000000400040030008003000000b00100000008000007c0010000002000000600040000004000000400200100010000003001000000040000000011003000a003400300000050028003000800600300020000004001400c003800000080030004009002400000040060000000000000a002800000180010040000000000c000400c000c00300100020010005002c00b008c002000000000000010004000000800200040020008002000800b0008017000400000000020000008000c0000008003000800600040020008002001c0060000001002c007000000100000020008001005c01000180020000003000c001000000700000020000001000000000040020014000000800800140030010000000000000480010018000000c005000c014005400700040030010001000c01300180030008005000c001000c0070010009000800200000020000000000400b00040000000000000000400380060000000000c001000800600000090000003000000500200010010004001800c0008007000c001000000e000000e00700000008000000800c000000000000000000001003c0020038002000c00700000040000000000000300000000008003000401300000000000002001c0000004000001c008003c0040000002000800000140080010009000c0040004001000000700180040010000001400c002c0010008000000000000180000000002000000400000010050000001c0010014001000800000000020018001000000500080040000000000800000040010028002001000c000000000080000004000001000000000000008000002c000003400100000050008000000400900280070020001000000100000010004001000000000000010028000000000100080010000006000c00700080020000001000c0040000006000c00200000020004
  | 45 => 0x4002001000100000100004008000800000000000000005000800400000030020001000000300000000000001001000000280000040000000000b000001500200010000000000000a00040010000001001000100240000000001000000900000060024000001800000000000018001000000600740080000001000800000140050000000000400000140030000008000000400040080000004000000f0008002000000000280130000000002000000180000018000000400f00240040008004000000100000010058001000c00200000020000002000400000040040000003000c00e000400e000000c00040010000000000000000000020014001000c000000800000000050008002001c0000038002000800700080010008000000000000080010004000001400200000000004001000000000000020004000001000c00000000010000001800400000050000010000400000180030000000000400000080010008002000c00700400040000002000000300000070004006001c00100040000000003000800200140060000000000000300100000024001000000500200000008003005800000000060008002001c003000c000000000300040000004010000c0000000001000c000000c005000800400100070000002000c0060000000001800000100030000001001000000080010004004000000000180010004008000000700000000010008000c0040008000000c00100040050000005000c000000c000000400300000000000007003c000000c002000000100040070014004001800d00280000004006000000100000030024002000000600040060004001000400c000000f00240010008002000800000000010004003002c001001c000007400e0014000002000200040000000000000400000040050038001000000100080000020000002000200080020000001000c00900000000010001000000600000000000005000c0000004002000c00000200020004000000000c000c00200040010014000000800c00300090000000002000b0034001000000b00000000020001000000f0010003000c000000c000000c00100000000010009000400200040010010003001c000001c000000c0020000001001c0020064002005c0010000000000000100000000000000000800100200000000000002800000180000000000000c00200040020000003000000400000030000000000800100000000008003000c00700100010004005001000800200020018018002800300100000014001001c0020000007000c0020044002000800000000080000005006c0100004000000c00b0004002000000000000000014000000400000000010014009000400e000001100080040000001000000100000070044002001400b000800700000230010002000c000
  | 46 => 0x3000000000000030000001000800000000040024005000c0020010004004c005000400000140110008009000c00100000000004003000800400040000000001000000500100070004001000801300100060004009001400300000000000000003000000280020000000000c009000001e0000000001c000001000800040010020000000c002000800b000000000200000014002000000300140000010003004c004000000000140020008011000800200080020000014000000c000000200080000010003000000400000050000003000c000001000300080050000008000800000100080004001000c007000400000000010008001000000200040000014008000400b0008001001c0000040009001000100100000000004001c00000080000058003001400f000800100040020000006000000000080040024007000400100080000000002000800100040060000000002c00a0008000003400100400030008004000800000140010040000000c001000c0010038004000401b000000d000000e00100020018001000c001000800000000000068000000000400240000008011002c0010000001001000100100040024005000800000040000000002000000800040010000001000c002000000400000020000001000000000000000000003000000b0000001000800000000020004001006c00500100000000003000c0130000009004c008000400000040040010000001000400080010000005000c0000000001000401200100000000009000000500000020000005000000d0000002001c003000c0000010000000c00a00200000004002000000000140030018000000000500000040004001000000100000010018002001800800040060000000001800d00000000024011000c000001c00f0004000000c0000008000000400000140100010001001800300040000004002000400000140010024006000000600000040000001000000d000800c000000000000030004004001400000140000000013007000900000090004000000c000002c0000000004000000900200070000000000400a000000000680040018002002800100400030000003000c002000c007001c00000000000024002001c00000180070000003000000200000010000000000000400040000000001000400000000010008001000800b00000000024009001800c00000010020002000000900040050000003000800500040000000009002000200180020000002001400100000050000000001800200100050000000000c00c00000000000000000c0000000002000c000000c0020004000002000000000000000000000001100540000000002000c012001000000040030000004000c000000400100000000008001000000000080070018006000800900000010018008004
  | 47 => 0xd8000674800016f80e27da117c37600000b2000000000000000000000000000022847e0084c000000072f29120000ebe0000ffcaea21f68fd886ed840000cf3800056800008882d22dc9059ab1814dc12611946c11dd489a38d40002976a968000b03000000035c000012c2b098000000000000000000000000dd88000cd18000000000000000000000000794800000024ba08e015ab552226797800056283f800028ac000384662900007e6800000000000002e680002b70c7217241e9041c6930e5a7271120a629986d902f36d6b0e1678b2bb6cb6000015c00000001ccc000279ad73ac8600016cc000000000000000002788ae80000d3f0d3c3d309920721d0a646b1cc638297a0001ff8ca7929625719dcaad042c1ca1fac000000000013cecd7af244f4a6da0002616443835862311aa73931040828e5200000002e104b8067800087a0000bbc800095a3142631800000027440000000000000000000000000994000000000026220003266a3980000002df20000000e3100000000000000000000008f20000000000000000011e40000dda82e02f4bbb800000009a099330288352dd2916937204b1ef65131c8ca3ea5b45828836e160116586b01874da674849b01457b298867200160f917fc723a01c3aeb6320000000adea61e0790b92ad80dac0000e3822a8c040000ed20000000abc0000000000019a8000d3a98fc77c04fa93db18e000027e1a19080000000065400000f015de000070a6758000708000000027c200018b466a94202042ebaaf4a134e2b00000003124a19a30275da8ca00013bec6e00000002730000000000029260000000000024a8508344b2f002c000380460303200001aca54585a4000198c0e60c56c8b08524b122ca00000002ee36de0000840000000091badd867f80003cc22d6000328800037a600013faa160000000000000000005c39042e358000191000000029924e92d10000261804088da00000000000000000000000000000003868000354a0000000058888a0002d6200003b80001890670809e1da844a9a2000000000020038001002c0090004004000000100080000000003000c000000c000000000000000010000000000000000080090010001001000000040020028002000000000000000034000003c021001c0010018002002400400040010000002000000400080000038001000000b000400400080020018003000000000140050020001000c002000000a000800000040090018000002800100000000018000000c0010008003001800000000010000000000800000040010030007000800900080000000000001000a00000000000005000c001000c00100000010014000000000400180000000008000400700340000000000002c00300040000000000000000400040030000000000000
  | 48 => 0xdc000268000034de10880003a2000000000007308efee3e97dadb4800000024ae000000000000004028000a47800000000c6000000000027640001546483000011aab6287793d6ccb239aa6c26a47bf80321ff80001b203ca98e80000002b2069daf06203acb664f14547aba9d801900000002e940000000b6f8272000000000019fa299aa7200000000d780000000000d600c0a2cb96700002c6ad63000096e000000007ac0000000000000037f2fe430b1ef000000002bb0000941156cafb8000cc222f8a5180000000000000000000000000002f3a9320000079800000000006ae151000000003a79a4200c1be86b60000847000000032ce9e611cc539a02c0001562995a084000387627c37ae71780000002afe00011f46b98b0e14890fc9c100000002b800000000cac000000032e60001ea255780000000000dc309d812200000001346ace80002bc800000000009d786bc0002b0eae28cf2a2e00002161c8ac4180001e60bd8d749e38c0c0000beb000074a0000d2e00008399ee4c851f46c4004d89163244789166e4a90b184e41c2815d000090e000000000006cf0000c55800081533ae37a35fc48b886820a8fac96b2aa83e52e969a3180e00000000002ef800000004528000be42784b95800037c1b2200001a81e700000000000870800000000000000000011224e8650f365ba9496d079b420000540d9c103000007421ba8dc200000000000d600000000227800000000000002518000000053d1476000302000000004490000418000079e8000de296c46b320a276f8000000358471e80008551d9e3940190dda08560002952ab698da59f38366c40aca2cf0000c79800000000007a4b09e84d89ac26683686729d1890c000000033bed56b33003033da000000000000000000000d5aa42c5f60000b5c922a046000011300002d583a08a320887c7935a27f1700b529d66000306ea2f2e2c00014fe310a4b0a59a82c8f632ea6a580000000000a4000006522b46cb2b09213a87a8a3d25946e38000262b6f6c028000bd18000def00003c500000001ad20000000ae428f6378380603d274e6b7803e42a3310874b4000cb8ac279a14ac3798496d752e28ae910c27e409763608000183a59a6340000d4fa11e24980004dd800000035b40002e30000000000030127d386d045db5241c60e9000015884f0a7d000034c000038b0aea8fea00000000000592dda80000001af6000369e00028c01682bda0000000b6d900e8c432cc00017f66c9914217eb450af9a80000010e27b49bc66f91d9c00009e882536dac2b0000361287c000013c0000000c0f00009ab0000d8500000001090e26081647c969cce635588da80000000000b78839e0219e5a0000ad200006001010cee8540aee8ea0000000366cc2d0000493800000005ae174800060
  | 49 => 0x3dc2ab87e289487b84942efa04724fa2a40a14399800020a0c6ad9b968658c296a0000000000015000028c6e371cc85611c6e462a6504fa80003718000da40000c1980000001b8600005a6c9c800075b0000000000047e80000001c9a9a1a3d4000000091580000001b4a8a980001eba31e95f21da5a98548de82b22b048ec059fa7284c505982cf95a4ab700000000000000000000796d8000000000000000001fd60000cf01420000d8e8000a360000b2d050e6a9000008900005c0893689ea6ec71f9e962dfb5a06513958000000000037ce0000b5eaf09c0a043147ed6b80000000000c8a19be34480929c81d1c000384e0ab8cb86f019964458000c44800097caa2200029ca9033518000204e14a00002e400de5b38000928800021a80000002a4c28200000b08af04e3800001620682fe80003c600005b4a168dfa10f4000363c49f800000000001d6160c0000000000000000000000002a9800000000000000000151c884112e000000081423d263032dc3ea0fe4dc12e6400015484418000622b94c6bf92f6dc01caa5feb3bc1101d82bf82b7c050ac684cd8bacb401216818091200020720001f04d4d930000023367fa000000023ac318800000000000003546276b37c00009b0000078a73ea7c88bf156637025727c433c40000d3e000000000000000001d049148890000036605f90145f5a7a8e051814afe990a7931a6600003d4c370d8c00038e60000e4ae28094600009060000000000112aae10cba84097be2322af2ded93f000000004ad0000dcab7ee4fc80005d600008ce3382000000000000000002f1800016000000000000228e9caac96d7c22c818e0000404800002605a800002dc367a23c98a173a665241a0001d5819700000000f0238d000000000002350dec773000079835ec0002f34e2da1ce000000000000000db0eac00000007961e3e0003692000323063e1534000209a7f3000068a80001be8000c80061e00030f0a200f3401025460000d42000000066220c886200721bb8000000000024c97f2000000000000000000000cd897c2b2600006e4000030c80004631a1e3ee80004ff0000000000081f000000000000000000e3a962c0000d920002c06baf3320acca5ae00000004cc800009b0314d1b80009f780000002c36bf99a160000d5c18d818a00031809fe986a0003784000000000017c4000001400025f0437adf6954a2b80001b7a9a414320000000b89a534774800000000000000000572301a2b18000000000000000003c880000000000000078c5728abc26d800000000000000000000000000030849a780001718000000000000017360000000000324600000001550ef20000c4a00000006d11d12000146800025a0bb92dac0000000cec8000290000051a8000000000000001
  | 50 => 0x26eea5a00009a1000035d800013b3828a0f00005b814f0d2fb3dc45f8000b2f847e4191806defb28a911a90c24a00000000e18000280a6be32520b50000bdc80003e680000000000000377a52a8e8cc000000000317200023ee3b9800000013b61feb7f6e3b2c3220d00000000000e4200005ae0000000000000020e28c5391cb09115c72e2b1c0002bacdc3aa0a10d36f0ae7166847c00006db1d6e4e2941400000000002e7a39085e271c927c0002e4200000000000000000000000030d200000000002b6c0000000000395c1ef04e6000000054500004c5b2a6a9200009fd9a326c20f4421e2edc00000000dd9594d810fbe91094ca03a859e1c02ca860f31aace49c4415295d62da16be6a1000047faf949b4ade6e46a348c6f1e327e080002180c8c4bb99b6000032c9530538000020260829440001470e0c30a6b530000000327000000000001fbe8cf00000002a2c0000000000364200032ba5f18f1e0001954707898034b19762f5831ed99000000000000000000000000050b0000743848600000000001fc075180000002bc85d9000000014ce1bfa2e4000235e7538156000197c5ccb54e88b157a000014a444800036980000001386d65b7984d600005d0387c49000000000000000000000009c2ac42d38000000054f95a86fa800074f293400031ea000000000000002dd9e625d7000045310369f980000001eded93b13800017ba9e1b15cc3a8000635aea85128000000000000014286ab98a80000000162a222d8d800000022980002f9811d80009949d5c52080000000000000000070e3046d3e177409d1154be7b8f4cc000006b09fd00000000000108c51c9d140001486000276c64880000000000000312a000000073b264e406a09807530b6515b83863a9b9220f80000d521d4771b04e00000000001688bc2a5a8b038000000104600000ae000000035400000002ae2d150000000056076c80000000000d20217c000000017a10240000000c3024f86950000439a20059591387b536ba1d203a6b3fa5b00000000000000000000006ddb48a668800063320a800000003180000a3690dc0002cae6cb00007f083be423ae9ac24000000000008aa9bf4c9b8000000000000021cc000000000001b00002d6c000130200000000002778000198e00000005210000100800049800003dd8000195800035d000089d1c400000000069062e000000000023e00d32b820200b8e000000000025360000000cdeb6064330000db4100c9e488865e080e8a47000000011ba000000000009fa3d51ef2000000000000002cc00000000000194034e585909a36d80000000000a3a931a0002f9c46b15bad7e13bc0002d7e0000b3640a2ee60001816526222e187261a00016f000000009ff800000025760000000000000075a8000b2480000
  | 51 => 0x20b260a000219e8a0a0f000004a6000186858ba4145a785526c7028045c80000170c50000344c0000000453b738de2250c3de80000000000879a9549901d7e21d97b4b1c9166323ad8874b14fa937a4361e6aae60bf2662e38817448b004a72fb75a9b780000003192d4f0802a98209c0003734025b4603c4117a0000a9665fa56e5e512c0e2e288833f194e8942a6847521645e4b3a650234126321268000000000019629c28000c221a8e9d1a23e0002c3a54c2f82bdab45cb6c00001bf19c6875a7244251c4cb9380001c880000000ea811ca0300002fcec1c000042e000026080000001b12810ae0a000000000000000000000000006600029d20000000000000060a0000000247205a24c61b7abc4c450000000000061e1a060000000000000000000000000000000244a5aa88c628f963800013ec324800010c984ea5907c85bd00006da2bf08edb6d869b1df86ae86d2d40190000009040001ee8000331c00000e49692938518044e03eb23a9502a54cf41e72d19352600016ec0000000000000000000000000000000000000000000000ffe777000091037a20001f02c3b8ad40001a7ac859b000002a5c338393a00000000000cca36a8000000149e00000000000000320000055baf1e1410000850000058601ec2ce3296000042400000000000000202a37200029e40001bc2000200000000000000f9800031fcb9780000000000c4e83a455fae3e1ea8e4896101ca14e8000df50ec4e09176800019a03430ba41030374bcc3618000000072098520003372d0186b09efafc6000000000032fc20500000000000ceb2496c9900005168000d9780002afa0d8bb0862c2c3231c5b213a600000000002404000000076e94dea64389600000000002296000000000000000003744000311009680001c1000000000a45dc2cba0000f388a2899611b3916ad01a44857a3c2a4a38a600003d65fb0e3c9f880000002e120002712bc398a679213a016da8960000b8800022dcb6aa0a4035800030785d600020fe5e2000000035c843cace67468fe08032e2e5be0d1e670120489a80004360000280acd08c5800065c80000002d209ce26d800000004639bb0652aa0604f8000000000068800004a2000000000000000000c68000000030ec8ab860a0000000d1e00004f90000ab0800000000007de87b00000000c1f021e917b8809aea5440001c7c00000004b2a5f4c6b92364b7b6ca3cb22420000000b47982208f36023c10000000174a48480007939d1000000000001ed84d4b608360327c13c8278c00b11a000287899780009a62b2c4f0394a00004fc0000000000299a235800000016faa822f006200000000000000000000000000c5b2c3c00017a00000e4e42c80000fa8000000000011b80003918000000000000000006a28
  | 52 => 0x536b92a960266a480070c000072e00000009ef00001b0b4b6c12000000034560002e92000045200024c0716abf60001e309d800009a2800000013e670c33aa4e080009dc00007be8842a18a31a0002eec00025be7af866e0eb000000000000001c4adeaa2140000ae66d786660000dea0002aacc3ea620639a8b0cd680000002cf4000000000000000000ff8000025c2c535822970000d0729f000000000002c3000005ea87ca5b215d800008d0cd400005421fe04ee5dbb1d8c9a8c3a000202236828f09448000611860c80a000060900002d20fde46dad4807a8000000000086f9cee2daaecad922fb20000c122ea8000bee353818a80006a711566168020233800000025a2593808ca1d84540002a62cdd8000000000000000000001e7e00032bcb32b0c68b500005d800007a21c785c6000003fa4dc00bb5523db9ef800032c8da187e44719b9e7591ca4c04344039b36f48ce800012b98848988c981f9ac6228a848e41680000a19f8a5ad8000186845085ca6ea283b8d2000000000022fa9d280009dd00000003832000000050580e0000212c000000097b854600000000002a8800000000000000bec213ab4100be1d400005e99f8e0f0aa40a1a8956000023a00000009e52280618b6e200000007299c460002c2e00000000000c100001f88d87164a00010065d480000000d5e60c0000753073281e80000002dda4d2aec600000000000000e56800081f9b40cf198560000000000000000000008c98000000000000028349eb0000322000000023fc00008c253c80009a500000000000000382a00000005aa0000685200634c092a686af54272b51e46730d628300002d7000000000000002f7a79b0000000067400000007ef314ae1c8000000230e353ad8479913f4649349e3a0000000019980002c0224b11bc00003b40000000749adb40002e0eb85af1a63b0d566c18612cb097d4b8a80000000ec600000000002f76a5405ec2328000c38039aa260000000000000015680000000447029c00000000001e1c0000000be5800200023980000000add80000000000c193208000159a8d3000000000000002ed4ce280000000336000372cd9a8cead3407a2d1786f69af99de0002c4a9660000000000000000000000c6e2d08000000000000000001a78000de400000000000598afdc00018d243b00007bb0000e5b0000000000000000000002f660152ac6cb529c6000000099911c8dbf1d50e438000a5e15646e69c36b3a8fee36913b25d32300de6942eb57007c77cafaa6a60a609d5a7360002276000000000026f88c924d48878000725a4982779438ceda90ab06800083e229045b8d28d3c8786000000000016c60000000aff933400033fae381e9c0000160cb4347c13787c41e400e625e00000a6000060e800000035ea
  | 53 => 0xe00007d600000000000000dd2b09600032e86dc2bce0002f4e4698478ba900007398000000256600000000000000bd000000000194000000033a34d600021c4d4300002e699e848e800000000003053674b8e9eea4349a5200016460002ea24c3203e6bd24b22b133cc3d9a7d46e28e20000307a2259f76a9c23628bc2614d12800000000002fb000027d23ba000000025d0000000000000000000000000cada7aecfaa3d000024706b83462413a88244fac8877e8000b720000bfe2ff2c01a29a4e71808cd0b6aea298a1000033440001744b251ccea5830fe5d584d0d08acf67d7a1a61fa80004bb00000002ec0788000000000000001378354a8aa00022ba0000000a412ad60000804bb812f2518ad0e000000032f00000000562a8eabe898c85f60003054538203c23e2ab212000000000000000112800028d00000cd843aaa1e3ba8482c3d80009d612d2d0f8fa633205e4731903cbc0a8ce00000006248000bc109e40001132000000000000000572486e3f0000000000019f940e4b69d980002aa4000352ad11a9ee00000aa82a800023a31986bcab5e5cb2b4a6cc01845c29cf6000197428d01f83c380000002d940f6187a5da8000a219da240c8000000390c0000000bd6800000000003070000c88b3668fa1290342a156852000000034a02e3327a00000004be13ca000000000000000000428900800082000000003008000374cd380cb03388000000329200016dce08000023d80000000000000000000000007c28000373000000000000000000000340a00000000000aa00000000934000077000001ec8a180000eaec16819c86b0000597303e00028b400006040d09e84000000000000000000000c67186e0fd000000032260001a884d9800023798f2000331ac9f8000d2880000000bc64b88000da600000000a1e0002efc00000000000000c7ba7c00000000105142a000000000029ae4fe039caa6800000000000000000000000000000000000000ca913d8c9d8000b2800000002f4454ca5207ed876cbfb0a527d104da98f0854d93285654eb1a2bff000000000009bd141c00000003000000709000073e00009a811860000b1a26aad9e5e2a5623e70000298985c20227540000000000352c0000000000162a0001d0000000000c4000000000006b58000000000000037302ee8000dee17f4000092e0001faade38418e368b527c381eeb312ca4000000029180000000000bba8000000000000000000000f0000000001b2a70000019e200024a60000000000000000024ec00000008b68000ada9308c2e80002978000000000000038c800006423bd0d5a00010e803f00000ff0000000000000011c000000000001238070b2b200032ded009dc400000002c280004c727ec000381a00032ec000000000000006a0255e0000000000
  | 54 => 0x4000081d80000000e1238db7160bd84cc550ac5295e201eb5780002ed04aa5700000000372032a8000a13b4a400010d60000000000195e11896de00002a0d9e3562093a558482008a57100001738000d550676492000088aa95a000111a3daa24c428800000000000000000000315a9d68042e3e32c600023665400000d3900000f9800000034c20000000db51cae592391ea07929ea3e0b1e5cd389e39bb0a4aed27a62063428ddb10f8ba7958600000000000024c209802d849e6670bb8fe000000086a9c1a00000008410000000000029a8000000365200036b600000000000000ba39b64ce300005b0356cb37b18679c00000002fe800000007d023cc3ca2fd83ed011057180005358000d0ab52ec7cb3705ea9d068d6374262c800094a0000000229e0f307d0bd716c25b9301c7043130b028000dc98000000377c93d0000c6439462880e56ab803122c981de1a4a3ae6601780564904486d9f8471c2c462ef167435b8e3ae21a682e3622b0362b36e00a1c580001e34b42a42656cb13600001d05788000b94801870a84e00001d80b17800000000000000e146532bf2c90038a0001aa022b112c554830ed44800000000000000000daf23700001c5c0000000000000017c80000000000000000000028d4000000028c17dce541f3600029c86902fa0c94029e3d802262d19a629730738000054e00000008e28f74531932cb60955a82396085a802403f422368640000e5a2d0272a000053225d2066aa242c23658d0e27660000000000184ccad25227aa00a627480003bf00000000000475800000020c6899800000000000001a6eacfac404082f52735a318b1c2bbe51191846caa3a6c75a4aad3b28ba42b06784322e50cca1b8c7e7378067a8186c2c1d38cf837ba8fb346805b8e1a1308182da7035609baa7cd76a8e239e19ce35e010e90808e663a0e5e7a809c69e5804c78b9c740000000168800000000000b58d2a00035faa5701c000000002dc000000000000001ec8000000083580009ec957000019c40c28b740001f34e2297a800021a400000000001c4e1ed8000e3b800000038880000000d629cb4e1b00002a08000b758000000000000000000000000000000037b85f8000000032c8c76df400000000a2c000267a0000f4e68280000000000000037a570a3dc6ce943ea7300000000b8000000000a0800000020a6a4d8000b1faf8a00025380001e560000000000311e00000005138000000017647823309fe00000000db8b9880000002fc446597d00bcb39a00030f40000000000000024f115ecb9282000000000000b06000370a860800000022080000000000167604bb26cd2228ee7daa9fe83b187c0490b5457cad3653a2e7800000009e00fd6719928ce16a130560326030c0000000000000019b8d09ad2c0000556b38323
  | 55 => 0x62fa7f40003656c71a8be00026ae0003650899383c000213c587a9dee40835017012e8b662a4600036802b936c2139254e42729b26d1898696d83167eb95a6b3695067f1990e90a3910d2431d200000003a19db418f00000001a725f2064adde00000001b5467600000002f78ddca91a3368000cf58000c48b3c0d2a1a2e9c8800c577378c70380481d8937e0002b160000000c7680009f100006f126dc0000000a558000000080c773936c2ab225a379101c000000000000000000e1c0000bbe000000000000009a98000de18000b4300000000000000068a000000000008644140e629cd0c96c310a44e4d00000c702b80fe87140429e0c9da06707d080004ed00007a5368c6af8bce45432785730000000022c000393600000000b8800023b96d048f072a02d8c9e8491264003a83e03293fe00011b200000004669db800000000002c180001494a789f60492967a91b31340da80380761636cc898f049e26420000000d4c0000cb4811a0000000ac200000000000a9f80000000000b9102d0000000000033b80000000d7caa04ae52cd2ae88000a0496fe30d1a0200033a000000000000796531259cb2c340e0000000e15000058d23521d2b7a879d000000000000000000000000000000000000e8a0d69b880000ab64b800000f42d3a00024e80e48000000000000000007e48000b1e192682d302c2e7800022ba7dc940b0f8e3d851c5d200003be992e30e1704a9900003e39fe42b69e864af9b58000000028da8c23a70b1200007120000050b14348e4b99ee237537b4801365c00010227b4299801da02a9dd950e5ba000000000009d08000b5d1ebaa07296e37c94e2cde0634ad9187e924b4f089c94104ec00000000a226df000052c2e06084b04a4e592520b7800040224ee6ea9e049292e1e0002f9a8b300000001ac000000004aa8000062013800031440000000973800085334ee2fa0000000006039f9624246a72c000095215a8000938b09a0000fb2b5eb3f67e599687fc800000000008ed0000944139e00011c45678000bff8000ad5282e89e0000422b4160000000a7980004bf9d08000000000030e2b51000000000000002fee2f68000acd91ee00027cc00000006fb00002622b560000000c979fa4696a0da2f9800046085b4bbc0000db9b6c86d3925e41d2924d63b8003a9196a7a2b21000000002089ad001e32f6d248a4a000126a000344e000115a650907600000000000e609b19e3c3ee1d3abdc171c1498000a010222e24b8aa0538782a7a16cad91a68e7073508bd626683e792dc6519ac664202924d9235041598de6612a2a74d3458cf5196ca958f6889604a0772a5e6ace06e667b93aa0789d725b9b5725e134cc000251e00000b29d00dc88529f1228100004f832eeb4b80000000000000000077f00f00000000dd
  | 56 => 0x38ae000000000010480000d4000000f60000564000226ee301afa0e580004e3259600000000000000267b6f8419b0a88068c4090e99ae00000002390332bac0a4cbf50000b9515ac0003522a610000000033a4870b2400000006c0815473f02e0e06000000014a000008700000000000270600000002be800000035f6a228000543000000037f40001eb8000000000000004ce0ca0765298ca0e1a561bd36be984a1b4a48ad7cb109dd05352f200000000351b28ce510872cf0abdea1121ba2069edc5fa853c4bc000014c105e1968000d6d800033f80000000000b51800000000008169730aa5b17e000000037d0710a853736c62800000029ea74c30449b40c08c9881e0a85a84a9bfaf6400012267a6b03452e2fc8c030ae86bb9e78ca020fa576800050c345282f000000028d20001bd492d075272c000028900003b6910858a322e17113da9ec00008fcb022cf7b0040922ab09bc2bd60000000d370e84db002ce5f88000000000006d9eb61eea40ab4584842d892023068bf800022544c63570d8017cc000371c0002170000000000009f800007c2000000000000009b9a716e12b1080003542b8080000000d2200000000000000000048c0000800abd00001b580000000000c36328eba28000d6200000000f561be00008d1010660fa4be00000000000000000000041880004a480000000000b870a164e5000000000000000ea60000000000000000000000003776de49d320000490000000000015fc0001fb8000254833d037ea7ea1603df9c5000002be47f16060000db00001e4ad71208600006649db80000000000a88040ec9680000000090040012a000000010432a20cd36241978000b23a1f8dbf80007fdb96000000006a980000000a8e000000000000000c2000000033e400000003fc1a860000000000000000000000000000e2300000000000d3980000000794000233e21200000002196b0a8f6cb46a89e699116c000310c16c80004dc35ba27fb16eb8d087ccd8001c970abbcbce35681aaa158696056609c00005510eaab56aa660001e44bc484a26c580000002de0000215c1b89d8a56886528348000000000000000000000000a7d1ab000001ac3fc80000a6932a0001f0c814899c936aa3823fa180000000000022125ca35660003472c8380004d0b384de5273200030420000000000354c000145000000000000000000000000032be3441750000151e9088000000000014d3904c0780004f2000000000002de000091e8d440002032b5a8000209b21a2d00594116a5740000ce4000000031720ca000093e00000006ba03a8d8f800081303ce0000b1c000230c000132600000000003146b45232800000000000cde7f88606d760000d0cb86200000008958fe65e90000449800026d000000000005660000cc0b4aa1f780
  | 57 => 0xe269c845c5851e00035a40002a9e97e00001c800000003662d1f874600005820000000b11000042b8000000259200d1bce330b576000257adecac58812a15a0002e860000f268378000dc20e30000286c000349c46a2890e549ce810e0e4ccbc96781d3a2bcb998a80dd01a00b460f900000000d29800022022deaa98ee800001f0094afbc000190c0001778c742b4c0000000d062c2cb7193a292d8000cdf800062a817035c0f5a7b3000072610c40002c4ce07b12c7ec2062000258e31e800077a9ace5e6182ccae323200000007c0184a000000000022a290926e0e3314fcb5b937c579849a86680000002aee0000000000000000000000001574cffb89011f29c400000009cf000000019160003352c8929109392f56d74000045d28d60998d244a889183b332e290d2db800019f6905a57ea0a800000037a4ab488b8bb6800000005167d9279eb16800000038f26b900000000000752a60c0000000baf800039a0d58a5d03ae00033b42870bdc000000032b8000b3000000ca9ee05540000ac98000000000000000007c2000063d35bc00025bacd21cc4211318c0af00c4923000000000a84d806d8a5c2fe291d14440000000c7a00000000f2e6238114b9ab61a736b24c22733ca585063e11783ee8158000b08a7d65fe3534000000000008bc57480005a6800088eac6e0003586000000002f000060e0000000000082080000000000000315e7db9400cb12d40069a2e6a090b7a0000000a9b800056f0000dca2b24d19ac563b60000000284c87829160001b9600e80000000000a67a9722d4000000000000000000000375c00028141df8e9a0c98000000016c296800003c937aadb8a3a0000134c408d6a33b000061caa4ed2d03f02e809020000448e1837e65880bf67a3073691894666f7924613702c027b8456b88a3880a31c6a00022921ae083c5849910451ad5000000004db80001a9800007ca676b4d0000883394299e15ee0000922000177c843934409d8000df30000b229c1600031bec30b2742c000008d700002990000c67b3d279f32ae084249a00021b299980000000000306266c9070000000000000024cc179913400001fac1718ae76c0338b98299cb1508bea2a373248d0000b3c0000cf9a13ee4f000019a08246ff800097b13200000000000000000000000002c8200000004b20000144800000000005db0000000140a920373a00025869b08000af40000d7300002cd08fc91117865ff80008008524a6f000000000008ec0000a1e80000c900008bd80000001d40000000011a00009ac946e000313c00039220001ba86c79e6e3d19a3a5aeb73e6f2059c979119e0ad800023b2f10b4c80000000000142a9b6a842a50977ad5808c17ae3f6232085e996e98999bc23816bc8a81c88548b8a82f90ed0000000000018960
  | 58 => 0x20780002170a7eb26981e1ce87f62129c000002ef4d859df626a09bedec2e7408b800011922c07768000000027acee8000000000003e11f823d00000a580000000000d0e95be9fb89383840000b2c80001e498c43dc8beacfc9fa60003158000000081000001721aa200024d694ca3ca000000000000004ae05fe88d0d1a000000000000000000cf63d60000d7b8000000000000020149398000a68296200000009c6000054080009aa94d25d98a702aea4fc0000000d458000d788000000000042f8fc8b9036e80a500008db0000dc8a2ece12000097636dcaa30000000000000000006e8800093380000000000599349a0000000000000027034fe06e258c234b76483d00007d7171ad2c800062eadae1f8147a431b7c2e23a0b2d58141a35f2490122b6a093c2e6c4ab22e2b5d8000dab0000a00a09eda10000000240e000000062c0a1a0000fc400010380000830c5dac144682f5e13d8e08c7b317a39600000001bb400029f60000000000000000011eab9200009b290ce5e688c4c4c8144a1827da2e6235a99b82a2d9991a40000e2400031640002b4229b9118161b5de39f123ed8c000041fb6fa0d2a8f293f80000000000da21c92cfd1cdc00000005f8392c65588b667324765bf0000e289f2abbd8984d2581d686b800056c1beea3f00001db929a52d0bfec1a887ad3eac100e19f660000e96000000014520ee0000000c81800005a805231fb1e20000000915000066a00000000000000000000000000002ad80d20000bc58a26c0993dcc280930d7a1d8499600000000000e591fc40000000476b7c80001882931000000017c00001fa00001d62000253ade78000000147c105ac840000000659935e82280000000000e1d2c3e617b20c8af8000d57a1788ec8000321314e0000000000000000014bc0002abad5f800000000005f4b7acc0d8000000305000000000000000000005a8df000000000006502e6e754a2ea000101e0978f120002bf4da98000b86913a07a2340e3a0000c0580009fa1b365dd80001dc34c84ea00002a6000000028ae00035aa182262c000181a00000007b08000000000004c000053b0000be3ab7400013800000dfa5f7b30abfdb3180003856000000021403840ba2e9c9f80000b698ea2cb0280e5899d7476f36f27cbae248791f1c7fc00000001a3e40f9c80564232e0000000000096c000000000011c25d180000000000d9da52a6011de80000000c880b6ea9e39660000ab20000000b59ad9009a000000000000000000000000000000000000000c520000d4cb41a00017cec7d0a560000000000007a817921022394b600026300002bf800000000000bd431312b2a50a5ea5ce24d8000000000000000000000160000037580000002e462c12b2e36e961c7b0000086707647df000012b27480002aa20880
  | 59 => 0x9a903970304000000098b8de20000c060001b6e2fc877ae3780000000000abe9b7e000011e95c371ebc73168745a3beb41ae9800028184f100000000000000000064e000000000000000000064a4d27b6800029c9362d5ba8e4331a8720000000000000064e8ece00000000000000a099528b8109165241f565179d4800029c0cbe83ec389800067e081c00000000000000000239e5ed924c000285ace18000d45374622680000000c9051e28480000000dfc80004c104f4d1c00009528f840002090000237421f80c8b670afe000000092725a600000008041c6830da7f03fd00006b6aa94a7e31baad41158000000000000000002e90a75aa128b4335000000008e52b98000000045a000000038343ce83724d586dc000000000000000000000ab223120001520000000000015f0000106cccf26e20000faa487b4d246029200000000848aa1a346000000000000000000a9ea2f22db072446400000002a00c2280006278000000000000006e03be07d838faabc000033e0000000acd000000007e8a059350086000067400060000a7862711223a4a406000000000000000001ae2727a77cae68000000000000030ae00007540ef1e421f30000cd738260000000a3b0000000000030f800000024b86c30cd076a80000000000c4b80000000000000000000000002b78726a1b875e4061b1a0002c7acc50af6c861bdc98f83ba00000000000000a860000bd4187600000003ac828e00022886e7294851d23081843290761b5ca000000000022ac00000003d92cc8000392878980000000000bbfa39010c1b604b90c4e0002fc02a7324a0000ad6755800075112182be0ebcc958506000178e0003766c6b1f284000ba2c8a80000002de8000277e000000037fa2c4a030bde0000d8e2478000000000064b00000000000a9d000068411140002a30c4a1dae5c1b8be7218c8abb3b502e418b7c2d6b4ca0000000b23067200000d036d0000000000000022f40c190ee6c80f1c58cac6cc4603221d0264a94213ba2bd212ec7291eca45021a5ca9cb29381eb073c9b0e28f0e826c90b4c4a80e0c705009ab7f21382699be20000cd29f4a60e05e8000d418e9400000004bf306c0001a9e7f20d6430a8000000000000000000001d420000dde002abb2dd62418000000076a0000000379ccbfb8940003038279a3c6c3c8000000000000000000002dba552a5c00000000034800000026ccaf3000000023aa0000000bdf8000482a56a000000000000000000000000000000000000000000000000078780000000ac8d35340cda29696050020e54a89baaa0208c0002ade0002eb47ea29be00025c89040010923800022e90b436a01c68fc14642a3134c00000000001af022500007f80000df1acac0ac168084a80001068000bf08000b63287e0000e220001842
  | 60 => 0x8dcc5f008e0aeb71a0000000000000000000000000120000015e1e10000555000052916da9f3b498b3b89bc000000041a800000006308bb800000027aae481392000006287a80001bc800015c800000000008cb141800010840000590a04193073600000ac80003feb82e60492d600018b6da0867aa0c000001b173cd648f8a606121a57a26d6a152b0a56a8e061111a1878025bc880a7ba1e7ad864a19c547dc1e224441bb8c481e363b0a9ba395133c12e8000cd384c45a28000573800030380000000000000000000026340000a68ac50000000226c4c48000000000000038660002fde00019ba1fca20a0d82c9c00015963118a3824d3058000000000011e600016d6ab30f520002b5ca9480000001512619972e97a23d600011ca9e8a5540000000000126cb842a340000d0000035100630862217a7627aa8a0a596800000000003ad800073aa3e4d83200826c80007d30000619000087f0000272000000032a85630d0886c0a280000000c8d851a7fb00002c0a21c00000003c8071e00008cc000000000000000000000a0208b016aafa4542a55a73526c061b37de2441274b171e909c7a1f4341979cc7500000000a9ea28302a633914400024883e895826920942e4f8fec0000b860001904000151aa5280004b300004a10000786a152b079cd2b3f000010b9a3057e00006ca00000000000a741e983f38a94a6b29d48ad8000000000000025d6958000031e04f0d6880000db800058f148ca9ab4d8ac0000067801bc0000a84b8db1f600000005f928927c80000c4fb1fa6478000337218ad792e5a0000000e34055eab536b074f80001dd0436922a9da04a3184c540000a708000b3c85ca00003880000000946800000000004f18000000000073d00000000000bb4800000009206ec80009c3321e1f4904a19321ec00028a48062d3c4c90000dc1800000000000002ff4a6099f01162d64d6c1bba42a9c02a23095ec5d0000d7089f66fc0ee4709800000025c68929258719354000018ca00015e0bef8f0ca2d80008588000baa9df4bcf8c26104800074ba0c20000000df4aa58bab00000000c44000000000000002bf00006eb0000aca1fca94b0d86bf318484292aec55011e263f907a4eb1c3e000238015619b0028a9f200000000000000e2700000001f1a000064e57ea02443502ea0be00000000000b02000054b000000000822ea000022c8806c438000000000000018e400000000000eeca63800044c0000000068edbb1262ac62ec40002df473000000000000000000079da6fc1ed00003300000a7b119200000000000c489a8b3063b7800039a83b208f800042f27f21f02f28000109800000000000f2ab3e80000000000bd80000b7300007011d0c000000000000008450000000367c7bf1e50ccca32a35b37607e50000842
  | 61 => 0xc800091e1d90000107c80580007a796b09b380000002c28a1734da000000000000000002fae889000094f0000d3a2cb899ca646000022a0000000c848400c6521c00b69d8c2f0308e6673556d092e705c4ae0055d9a2863eb08643fb0e61bb22d869f2d9658104d66070ca85560146000000000020e800031a8c1580001a89c42000312600000000000000000000000000000000000b60387e6e920d031ca45000000000000000ad227a03208d7200005d0000272e0002b583f480000001b940002790881b0be01383e2000000000034ae0000000000000000000000000bc894900003d08000cff0000000097a80986f0c622c7400000003ad331e41e1f9e40eb1a65171de057901326c29440b0d000086810c03473884b5c2112321a6b60561aace5786827d427fc8421ce075c37c0718040ac2f09d4cab19f4c95105c64a9e06000171e0002b5a98e2eb8000347a989005e10a964c00000005bb8950b6a08460b480005bcaf4277fa902000000041534ba000000000020dc50db3a80000000c3688a0d0c05da074800046228dc00017acb7426b8000000071200005288e407f68f86000008441033ec2b380005c2000000025306768000c459d8800000005238000000045ce2cb6ee000206e0000000ca600005149a2400009a4aa82f8c00037fc1ad002adf58000e19122236f3374000000000027b43f5000088e0000524aa0ee33873e000330c0aa000000000006aa000000011007583286ac7a50028b800008738ca0e335fe5a4b80cb2a80000601cbabd291d860400002eb9fdc2961990000282200000000001e2800000000000fc20a121d08868cb693083e842e80009da8000d889a4e9c717140002b88d20a03469c2b027db00000fd800000029188f0042623033e284000000002244b4980000001f1400020b0000000039d199a12c800000000007820000ccf975411e83900000000000224800012c600000008838000a908000dc400001b500000000e2cb392cce00000009020bcc38108a246c2ff00000000000000007f8000ba100000000000000093a000000001c0812d590a4ecd0000000029ce00032a00000f88a4c000000009680000e44d66852c2d800000000df600023786fe29804368d9a18ea59e25203622ca809c208380a000017cadcb86e00011e8a3136c6cbc0fc085b849ebccb0aa0002e142a18000765934053e2f84b68000000003000001f3c00033124ee0b4aaa0800000036942ae2e3c0003774683a5d471496420b2b85ede580004b6000000012ceb5a0378af0040621996a2c5529a268e3162000255cb6295d85c81ef4c691a942739398247189a00000000000000c1780000002b0c073a9b81fb9ca2c3326e8098b7ec00000000002828b27abec9872b0490c94ae7c1a5dac340000d9c9f220002fb497400007ad000
  | 62 => 0x36688b0abba7bbb1f812526c801d0000b7c1488ca6afb600021ca0000000000000000000006fe87721858000a6a20640000000c1f800069fb65a09f024240b16826cd18a2000182e00002641f3a39c00022b2a438f323e922b400014e4000000000000000c30000c7f800040428e0bab8000d5e8000af7348c345333ada6875a0002a8e4baa7029329d5400000000000000ce000004c78000093219883a987400000560002a90000000000012fa58fa6c42ed9ece59504be529926e6bb2c1c00006a400000000001434b29a908dffb644e022ed01a683c4aba0cf84950000d1b00004f7b852009800000000005a500004e200000000b440001b84b66a97c00033240002be200000006d437526a6aeb65a300002ca0000a41800091f9b72110a50e0b1311c000000030900000001b5a0000000000116400030767d8800029d9e100000a4200036a44908000b190000d4a0000328aed864f8ef0aca80ac0002514d6f80001a6234e6918640000000000000000001b180339480dd38ca68cd31c29810c546973484766a14601a16f6b3b1b66a268f3e891a52e90f2a5e13a0000b50ad1c98027d86f5857e00032aa0eda066dcf2be40950d9c6f60aaa0000a1200034f69c20000b4f800073f800000003e000005d835a028a0001328000210c00035a6b31a7e40000778000000063d8000d25000065c00d497d800000018260000ee052ca49489f800000023ea000000000000001aa12064ce80009198734687000051220f69590000ce382321b9020c0003930bb2308cbf58d349a486201e22fd080d904c216b75e8e392d00000e769281a1240100000002a1c258000000003d2ada00000000000d5d1374028205c2c4199e00031c01ef8c52d8b9ffc000288e0000db26f98000000000021d0000000199226e2e201f6a870a8db8c6748339085104460002542e4004087f384660002020ce5b282c87054ca53932e6e034e23d78000447843c1fb00000003718000170c0000000491000000000000002dec25980000000000000244c0002cdca65a45c7032bca00000009a699d4df90000a5600000002a320003914000381c599ad2425a829000003020000046000058e000057889000000000000598000075a0000000013a00000003c68000000206c7ab36c4dba8000621884e0000000000000066980002a685dc000000070e866c0592556e461f2434bb078500ad2aae180002a891d070f0000aad800000000000000000a831d0256380000001fba4bd000000009e0198b338a0d800000000008a91f520002058732a1d800000000000000000376e000125c6ef000007134ac133a1c68d900007699a26000362a03b80000000000a37800000036b400017e600000000000ae2000177a000319a510800046b80002950c2e0000000641ae7e900335838
  | 63 => 0xf8b24e63535944c4342ea2706da358a06a274031a3f32ea09190bd012900b46ba8000000000000006be0000000d51094000000005fa107000014c2000000000027ea00000000000000000000000000008c11cd0bcb094e7c980005910000000332a6928000ddf80007639c90229000059600000003634bdb0eb0d0d07085f2a392a2c81fc09412323ef1ea60c61148be201aa15700000000000000000057fa18edb38000000000000000004a6127038a129c00000000000000b0003804f40000da39f2cb7b897e000218cb8600000002a761c080000001dec000000079aa29c0001914764a3460002f92ab280005fb800000010b000000001b18000d48000016337d8c14800000002587ff80003df04d231d10f6c81178c0002ee87252d4e784b39c7d280000000000000320200004606e98088b1d85445048bc2bee80009f1800000006328f79722000000006582f0aae29868301abc00003a299100000000d040000000acc0c6c97e89ae7c5928081e17bc78608824fbb4c400030e80b603c853ba0ac3b8b840701abb0c6c0c02000000000000005cf80003c1800059a902eadf9a3465e00000002806e05909e000000048397b8a8f336800000000002dfa000000081d23face8a42a3528236659142267980006980000cf60f4a0000000715930a92a00000001d5a0001f320000000c770000b930000161152400000008c180000001bb64738eeea0ea116ab38f621c5a2863b529b4107ac4e7e61de600021921c6b0681a822cec738d1665eb09c9c4348647dadc4cb5813600016e20000000e2d01780000000bcb800000033f87ac80000002be0000273ed780c5ad7180000ea928e0000000000250a000294c000200a0d18000000236eb35275200033b0e0b285e0003032aabaea600023c80000000c5a8f5c12f096eb3e0000a19000000000009ceb1664222ae400000003c204ca00012286d734428d29eca60a800075e00003c580006b50000000000020e2d78000000000000002ec14a8000000072b1178c8e0a740000000000000000000001a5aa441540c0cdc08004000177200002aa55a8000aa2800000000000000d020000000000000000000000000000d67800000000000000000000345ab6f0602bc500003bda97e8bf9ac80000fe25b50000d9516900000f7818a04c0dd20000425adde4e120927189de2ca700007d6800085d8000df109cc0000000000000000028e8000000000000006f834bce0ea1a2b7a875600000001f5000054e293a73884e23a38a924daaeb23f6b67a1e39d24c8f053200009c41350000000000000000000000000aaf800000000000000c683b2000063b80006f400cc4eb9d2a00018bc4c3b504c428000439000036b80009f28ad844d80002fd0924859a382000157c669127a5d680000002f2627b000000000
  | 64 => 0x75ed8e0000000292e2f4afa2a782506ae4800056d0fe81b3800000000000000000b42062200000008d5986000000008f3a04664d2bae0000000000258200000000000c94000000052f80000001adc9d40e7000020ce0000c660e519ec00000004cf8000ce7800000000000000000000000000000004fa000000029dc0000000000002257a8e2e54d8000d770aa400026fa625070e0002bb800010d05dfa2c66941e16cc380000001102000000034e2f3c0002ccc00000000e39bd2972a8500002884000000023600000000000bfe8000000000000000001f2adc0000303a00000000001f720000b3a2ecab8c00000000000000a929c3200003407680b32db802a69d70000000125a96a8000ac19982aff15b60000000a4f0000000000014d84f81950d3a000000000034b03520000dd5964000000000000000000000071b00000002e4a00000004d50000000000044105f400039540000e0200000000002ecc0000000000347600000000bf902a0000000000377085d2f4c0000000000385c12c08d0cbe1a74e3c0000e55a3f8000000000025dc8e5800078a927618537543e30000945b4080000ddc00000006000f246371c222920000e498ac08deaca23d2000080b8000cd90000e448000000384290f9c2c00029aaa652cd60ad1858583988800000001248000000150869788845c400007dfa78c31917909c696ac5e5a4840be88880a22b1aaf1897299224601ac98acb3a2a2638387060fc8000000090e409952e17b8000a5b324200000000001424000148a9540000c3500000000000000167215b80000002e821890000bdb85180001a6882b81a2978800000016100002e5ce20a22800007f046faf802e0800000000000000000000000000000002c81348000000028000000000000000000025c06cc0000000374000000000002dcaa9ce3083fe803853e0001bfc00024f2e2f0a7a4c884b4b44a67e2d900006f28000574000000000000001f306822070e4c8d940000000000000000000002c580000002342000149c6cb800000000000002608df8a7724aba726000242e4958000c781ab2575340438a80b02d98fb68480000000277a00000000000000000143c6e8000038000000002aea0000000450110c3e802ec8ff84fe8fd35e600000000003844c1ca25c12d800014a80002b80000d050000399000033985d4ade10162530000ca100008d503c6ae58000177abea1cf0f70000000008a21e22299a3c000293e000000000000000000000000117075f2c6600000000002b12aa1000000036aa00000007e32e0c00026100b320c4bdf003c9e2800000000000002f860001a2c00000000000000000139aba00000000350a8981fe684c80003b700007b580007d2000000000007f7800000001ae000000000000004ae80002f10bee224a3b84
  | 65 => 0x1dd800012820002b66000350ee42a0440001870c6580000002f086cc80007ec837cc3280005ab8cd687f8000000248200001522ba8000df721a82a98000000068436880000002c045099a041a3318200000000ec18d8a8a02560000000a4ab2da60280003a600007ed00007fb8000d6411b8e500000d0f00000002dfe000043e000160215688b40002fca0000000c9a00000000000000000000021f0d6a2ce21da2a860002e387ce00000bb864812a00000000000000386a1b1000048915b89712da4000000000000d83d0000018631c40000a3283300008770108c502cc234d8000aa497f06a3344477b9556252b7ca6da8b9c8a5000000030e485a800061506ac00036260000000000176200022e80000000000000000028400000b58644800000004700000000000000000000001dd895800000002fc00000001f3a0000b4e5ec0fc6bd21e023d410e0000000084400000cc0cc47fd21ee69a800086f0e7a1fd0000cda80000000000400800006e80000000fb0000033c8049b981c70000a3202080002ddc00000000000ba600009dc00000000000000000000000020f20000000000392e3fda81a382800000034c60b9ab9e00019360000112000157800003da0002b52ccd80000000000b960c7062e000034c800082d890acf205cc658052e8e880000001a0c1a200000002a3e32708face90d0ebd88000326a6026f68fca474a37eb9da38641b94cc0000660000007e9ee107224514d09a581cc0000000e5a9404000069400001981621518000241ebc885100000000000113cbdd1f540000000e49364a00000001a00382c188000cc1000015a1898000000000009d6b202cd8000217ed52253e4298000000000097f000000000003e48000000000000000007b100000000000662800000002acb688000c5c00000000a8800000004208000000000000030740001c761f1aaf65942c480859ec632fa7825a38cfa00039620533394af5000000020e00002c909aa37f8ae9800039ca096000000088111dc000195a16e35b82f8aa0200001b4614077cb791d7accb954e0000000000000023c000055c800000032f4ba20ca488c23c43178000000000045a800098d8000000216c25f0000b6c85ac704afd2000362078e80007b980000000000000000000000000002fa8170b42042835d66b119f2d9f8f807c6355c20c81268da1b825d0ae7c000136806800007e898e289c03de17f0000063aac0c2018a022623e27f4882e5a1116000026e4b05800052eb410dcb9d227d607dc0000ecaa501dac00030fc000000000000009969e820001e1400000005530000e290104000000000028cc91f36280001cdecdb01da5671a3612709626aa800079500000000d9072db0a2349800000004c686e3248775806e081ad303e59bf2242300e000000064c9
  | 66 => 0x1152000153c00000006a487fc000265424018342c89e800000d88e0382e42ac27a400030ce40d000003699ac00001729818b9459b3474000238480e80000002a6c0d91a22000270ed98381000008a80000000772024400005966d20000000000000025e064810869622e8c4cc30b83551622ca5000080e33347579c3400000006d300000000000df819fce4e0b96263338824317b216c000000033161cb000084a325cdfe800000019b200000000000000782a30a030b160c8d1ffabfa9652e1c36cc16f0000000000000036b200000dcd3d359832b000091a000000000000d4812223ab42c000360a25130600000000c5e110aa148a6c83931f08612c7c000351c0002d567f6332600036b800005000001bae0000000000000000000001898328da880001b023da196042081200009af31e4499800094700000002dca4d700000000000e2e99524852f2a00003700001e405a60000af62d5219f00006d480940000000e04800060c800013200000020000000246a00020bec6da62a15f2360000000083f00009a71b5600000000000000000000000016b29bd8dce4248000d1a80000000c160000000c82965ead3a11a2940000cfa00008979f7802e0d20052128a5ad14d8bb5a3a01ab898e7f50bcadfa9da482837f0c322590d54050c76d8000a1197269499de40000000b0e0000000295e0000000da58b2ca0c9b3e000382209ab62c00005e031605204a98c3cacf000005988e20002b442b70000000271441a11b426400005161c08daa26704ad800016e80001d7095403b2f688aa0000be980007709f864fda58a43280001e025fe7af134eab41bf6006b34c4689bbe0000000000095a000256c35300000002a2e000286800009e28dd80004ac00007dd32e0000227c00000004c18012000086c36fa3bcaaa80000002d28885b4ce00000004a5000000000002b30000b820000b8cb59c4f3000000006e80000ccec779840747adf80002660886353a00000001d337dab738744372af0c281800000024ac53018c24149a78000035c37130409bc86900001844000335443e94ea15b00003c280001e9a44e997380200000004af1b6209800002e28000c260000cd2b5b200024489d324ea4aa00003b594f6000043a1d98502b75024637e00008e910b650e95f46ad0d9899f069c2aa0000cfc00003f700000001b7448820bac378000a4c85f0000000000022e07971ea472826d4c2c8e1eabf2ac435e8a7c5581918cd5a49e2b438780a919b49ac000000028940000730c250cccde0992800000ba8461e8e000000045889ea6791e0e6f309985e79fea20e800088cb04c0000000b638be0640a412a690000d5e16a4507b60e0002dc200000003ebafda5d3b84c00000000000000191b1b2e5224bcd5f1e46365800030880000003258
  | 67 => 0x6ba0003448bb89afcdb595f60000000d0d9c18853a106000155c000302e1e800001d800006de15ae00000000000000000383e0000000abe00000000ea00000000000315200000004f500000000000b9ca186466006a49c80366570000e390000501949adb92ede00000000000000000000048c000000000008f98dd200002040000000ae38000a4b163a000361e0000000000314ca1d0000872000015e8964dc4a322a10b94e51b1b1427c8200d468c7c2ff0000c6d385035f80006ce17a211d29fc73c28fe9eda2d20002c2035980007cf86b643c279cb6489a23e0b87adc526b4777a9a6cfb8cb43ae0000549991c6a0800000000002ad00006ad800007d0a8a0000c20b580000000195800000000000000000000006cb5f44b5302454100009e3940c00028a200001f63cf088c0b1800047780000000000000238c8cc8c2808521fa00001be416
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb3a849c9504400167309392a08805edca067254110005b8c0ce4a822000a7b865c9504402f4f10cb92a088002dce0572541100bdb840ae4a822017b72811c950440016e302392a08806edc60662541100f5b9c0ac4a82200097a87189504402f2f30e312a088156cea1062541100059cc20c4a822000b5a8318950440016b306312a0880039a5886254110004bd43c84a82200097987909504402f6e503212a088002dc6064254110427b110c84a822000e3964509504402f6e502a12a08820fd888542541100bdb940e64a822000b7181cc9504402f6e503192a088002dc60632541100053dc3264a822000a78864c9504402f6e502992a0880025ea1c3254110004bcc3864a822000a7a860c950440014f30c192a088156cea1032541100059cc2064a822017b72810c950440016e302192a08820adca1f71541100beb943ee2a822001b7286dc550440036e10db8aa08805f5c9db71541100beb83b6e2a822000b7184dc550440016e307b8aa088002dc60b7154110006b9b96e2a822000d7172dc55044001ae70ea0aa088002dca1d4154110005b843a82a822000d708750550440036e50ca0aa088006dc21941541102edb9c2282a822017f338450550440abe64e8a0aa088003cc5d1415411000799b2282a822055f306450550440016e706a0aa088003cc90d41541102af9821a82a822000b738250550440abe6684a0aa088003cc5094154110005b943a62a822000b70874c550440036e50c98aa088006dc219315411011f39bb262a822017e70764c550440016e70898aa088002dc611315411000739b2262a822000e71644c550440b56e70698aa08805fd4e0d3154110007a939a62a822000f51734c55044001ea6c698aa088003d418d31541105efa9a1a62a8220bdf50434c550440016e70498aa088003d4cc93154110007a899262a822000b728748550440016e10e90aa088006dca19215411000db843242a822000b738448550440016e30890aa088002dce0d2154110005b8c1a42a822058b7382485504402fec70490aa088003d89c92154110007b0b9242a822000f63624855044001ec0c490aa08800a3e219754811003c7c43ac69022000ba984189204400179306312408801f3a1da4248110005f0c0c849022000ae886509204400f9d0eca124088002f8606324811000764b1a649022002cf0765052044001f4284a0a4088003f04c9314811000d78432429022002cf076485204400fdc0c490a4088006f821d2148110016f043a429022001be28648520440037c10c90a408801fb8219214811003f71bb2429022002de2764852044005bc0ec90a408801fb81d92148110006f1baa429022000de17548520440017c70890a4088002f86112148110005f1c1a429022000be1834852044001dc6c690a4088003b858d2148110
  | 1 => 0x90cb8c86880021fe157650d100243e42aeca1a20008ef825d9434400f1d904bb286880021fe1574d89100243e42ae9b1220018fa87dc162440011df0eb10c4880063d21971949100147c432e129220008f7815d9524400f0f90eb2aa48801e3b209769091000c7a432e321220028f8865c2424400f9d0c4b8484880021fe1576509100243e42aeca1220008df835d942440111b906bb2848801e2f21d64509101ed1e42ac8a1220038ee87d89424400f1bd073b6648801eb320963cc91000c7a432e399220018f4865c632440051f10cb8464880023be09764c91003c6e43ac699220028f4819d832440031f1013b0648801e3b209760c91003e56312e81922000cad74d8832440031e90cb88648800339d89710c9100147c432e01922000ceb625c0324400f9d0c4b8064882ab1d1db75505105363a3b0eaa0a2000b71801d54144001c6ca9b2a828800e3d21d655051001d5b426c6a0a20038f48758d41440af5c904b1a828800a6da1e43505102bf5231284a0a20029d583dd131440031e90cba26288022b5a0f644c5100447a43ac898a2023a748559131440015ad0d29a628808f95195534c510006f1106e498a20088f4875893144001d8ec599262880063d219744851000c7a432e690a20078f48758d21440016cb0a3124288002f860252485100253d42ec8a8220048f887591504402f6e50329aa088002dc60653541100263c3b2a6a82200197a8794950440ab67509292a088002ce61252541100bdb940ca4a822000b718194950440abe64a8a0aa088003cc5514154110016783b262a822000f52534c55044001ea2a698aa088003d89492154110007b0a9242a822017b7081dd150440014f70cba2a08805e9e2197454110005b9c0ae8a822017b70815d1504417fc74c9b22a0883069ea1f645411045d3c43ec8a822027a7984d9150440034f703b22a0880069e60764541106071da0ec8a8220c0e3941d915044181ce463b22a0880025ee1d6454110034bc43ac8a82205cb738159150440018f70eb22a0880129ea1d64541100253c43ac8a822000c788759150440090f10eb22a0881769ee1164541100071dc22c8a8220bfe3b4259150440b94f702b22a0880039ce0564541105f73918ac8a82208ac7876dcd504402f6e103b9aa08805e9ea1a73541100053cc34e6a822017b72819cd50440016e30339aa0880029ee1973541100bd3c432e6a822011c78765cd504400167708b9aa088156ce2117354110005b9c0ae6a822017b70815cd504402f6e50239aa088002dc6047354110034bd43cc6a8220009798798d50440436e30331aa088002dae096354110005b4412c6a822024b738158d5044001cb2c631aa08805edca064354110005b8c0c86a822017b728150d504402f6e103b92a08805e9ea1a72541100053cc34e4a822055
  | 2 => 0x175d912003c76412e3b2240088de87dcd64480018bea1b9ac8900031754373591200043ec2cecaa240008df835d954480111b906bb2a8900023de0576551200147a40aecaa240008f7815d763480051e902baec6900029761443d8d2000566c1087b1a4000ad98010f63480011bf0eb18c6900233598d7118d200066ab1ae231a40088dc835da53480031d90cb94a69001e3e2197094d200045fc22eca9a40038bc845d953480011ef02bb2a69000a3d2057654d200443e43acaa9a404ea748159553480091bd0fb1aa6900063b2197290d2003c7c432e121a400487e859d943480010fb0b3b2869000237e0d7650d200445e43ac8a1a4008a9c83591434807f5c902b2c84900fe3b21971909201ed1f42ec8a124003aae84d9542480071d90eb2a849030b8b15165509201e57240acaa124064b2e85d9142480033d101b9a8490003728c3735092000747a1ec6a1240038ec8758d42480033d101b8a84900067aa1f705092000cf4402e91924008acc8359232480031d90cba264900067a201744c9200447643ac89924000bc58118d32480011bf06ba6c2900223720d74d85200143e43acaa8a400487e859d941480010fb0b3b2829000a2f21d64505203a54e41ac8a0a4064d2c755094148079d48c2a12829000e3da1f61505200063a3aec2a0a40028de839db31480031d90cb96629001e3e21970cc520006e4992e198a400487e851d931480010fb0a3b2629000e2fa10764c5200045ec20ec98a40028dc8758d31480055c902b2e42900067a20174c85200147643aca90a40018ec865d121480033d100ba242900063b21973485200447c43ac89824000b998418d30480017a30231a6090002f260a434c1200074cb22869824000ba9841c930480017c3023926090002f260e424c120004f443a849824000f8943509304800f9b0ed992609001f3a1da324c12017de4c1c6498240019d8874c9304800f9b0ec992609001f721c9324c12000d74432649824007ce8764c93048011d90c69926090006f221d324c12003ee443a649824001bca864c930480037910c9926090023b2219324c12004765bb2649824007dca764c9304800fb90ec9926090023b21d9324c120005e5c22649824000bc9844c93048001d96c89926090003b2591324c120005e5c0a649824000dc932dc530480017930598a6090002b6219314c120005e4c1e429824000bc9834853048001f826290a60900030f5d254d95100053ac0ca9b2a20028f4815cb64440090fd0fbaac8880021fe0375591100043ec06eab22200087f855d954440018dea1b92c6880031b5437258d100046fc3ac631a20028f4819da53440031e90cb8ca6880022fe117654d1001c5e422eca9a20008ef825d9534400f1d904bb2a6880221fa1f6554d1000477c12ed21a20078ec825da43440031e
  | 3 => 0xca0e60018de83dd941cc0010ff0abb283980121f21576507300447a43ac2a0e6000c747558541cc18bca8a2b2a639808a3761b744c730395aa42a8298e6074e946450531cc0031bd07bb2439800e2fa1f74595300061fa86e8b2a6000c3d50dd1654c155878e928aca980030f5d754d913000477c12e3b2260078ec825c7644c00117f08bb2a89800e1f21d655513001d4e422cb21a60019d8805c6434c0071b90eb2a86980022fe1175d893001c5e422ebb126000a6d85087624c00159b0610ec498002ba60021d893003e57312e831260008ef87588624c00195ae8b10c49801e3b209769493000c6e432e7292600787c87595524c08747908b2aa4980123ba1f625493003c77414ed21260018dc865ce424c0090fd0a3b284980021f61476509300147b408eca1260008f5811d9424c00f1790eb228498003271d9435093000cec402e399260018dc865d1324c00171b083126498002f2602424c9300053cc04ebb0a600487f875d7614c1210ff00baec2981c21f60175d85300146e41ae9b0a600087d859d9514c0090fd0b3b282980021f61676505300145f43ec8a0a6000c3c75d91414c04b53908b2e62980963721974cc53011d3b42ec298a6002ad681d95314c0051b90eb2a629808aa7211654c5306272a28aca98a60019d880dd1314c0031b90cba2629800676201744c53000cec406e498a6000dca20dc9314c001d8c43b1262981b2d5a17614c530365aa42a8298a6022e9464505314c0033b50fb8262980063721973c85300243f42cec90a600087d859d9214c0031b90cb9a429800676201734853001c7c43acaa026000bc9821cd404c0017a30239a80980066e21d43501300465c3b286a026008d987350d404c0037310ea1a80980236621d435013000dcd43286a026001b988650d404c007d310ca1a809800fa6dd94350130046cd3b286a026008d987650d404c007d30eca1a8098003a6d9543501300074cb2a86a026000b9b8250d404c00173702a1a80980036650f7250130005ccc2664a026000b99844c9404c001f1284992809800f2e1d941501300466c3b662a026000b9984cc5404c0013b10e98a8098023361d93150130005ccc2262a026000f91414c5404c00f0fd0f2a2cb9001e2fa1f545932001c76c16e2b26400787c8759553c80031dd05bb2879001e2f21d6450f200454e41ac8a1e40c3e2c5459542c80791db0db8a859000a1f21d655472000c77416eca0e40038f581dd941c80010ff0abb283900121f21576507200145e43ac8a0e4000c3c7559141c80d5a58eaa1283900f3a9185425072000c77416ec98e40028dc8758d31c800f1e90eb0a63900023be19734872053e3a38ca8b2a40028f687dc565480018eea1b8aca900031d54371595200053cc04ebb22400487f875d7644811f0ff00baec89019e1f60
  | 4 => 0x500ed6e50339aa0a0002dc60673541400053dc32e6a828018a78865cd505000167708b9aa0a0062ce21173541400069dba2e6a828018b3a841cd50500016730839aa0a011ece61263541402559dc22c6a82800097a8718d50500312f30e31aa0a00039658c6354140005b5410c6a828000b698218d50500ed6e50231aa0a0002dc60463541400059d43a86a828000b388750d50500036750ca1aa0a0006ce219435414037d9dc1a86a828018f1b8350d5050001e34e6a1aa0a0003c65cd43541400078db1a86a828000f186350d505000167704a1aa0a0002cee05435414043e3c3b6e4a828018b3884dc950500314f50d392a0a00029e61a72541400c59d424e4a828000b39849c950500014f70cb92a0a00629e219725414005e3c3b2e4a828000b3b845c9505003167108b92a0a0002dce0572541403b5b840ae4a828018b3a841c9505000167308392a0a005a5ea1e6254140004bcc3cc4a82803bb3984989505007d67708b12a0a0002d6e0d6254140005ac41ac4a828000e696218950500016750ea12a0a0002ce21d425414000d9d43284a828001b3886509505007bc76eca12a0a00638e1d942541400059dc1a84a828066b3b825095050031e5704a12a0a0003ca9c9425414000794b9284a828000f2b625095050001e50c4a12a0a0002cee0542541406479510a84a8280c8f2821509505003167509992a0a0002ce61332541400c59d42464a828000b39848c95050001e5285192a0a00029ee1932541400053c43264a828018b3a844c9505000167308992a0a0003ca5093254140004bd43864a828000979870c950500014f50c192a0a00029e61832541400c59d42064a828000b39840c950500ed6e502192a0a0002dc60432541400c59c426e2a828000a7b865c550500314f10cb8aa0a0002cee1171541400c59c422e2a8280c7a7a87d8550501034f10fb0aa0a00069e61361541406371da16c2a828000e3942d85505017dce483b0aa0a031b9c5076154140004bdc3ac2a8280169788758550500bb67708b0aa0a00034ee1d41541400059d43a82a828000b38875055050001a710ea0aa0a0006cea19415414000d9c43282a828000b3b83505505000167704a0aa0a0172cee0541541400c799c0a82a828076f32715055050001e62e2a0aa0a0003ccd8541541403b79830a82a828076f323150550500ede6042a0aa0a00025ea1f3154140004bcc3e62a828018b3a84cc550500016730998aa0a0203c6d0f31541400c59d42262a828000b39844c550500ffe368698aa0a0003cc50531541400c59d42642a828000b3984c855050001e628390aa0a0062cea1121541400059cc2242a82800887c8759554cc0031bd07bb28598023271d94350b300447643ac4a1660008df865d132cc0051bb07ba2c3980223da1f51587300145ec26e
  | 5 => 0x80121fe0276cc5500243ec04ed98aa000c7a409db31540e18be613b662a8003174c276cc5500063d084ed98aa000c79109db31540012f700bb662a80031ee0176cc5500063d202ed98aa000c7a105db315402f2b906ba662a8003179d963cc5504058e422c798aa000b5b8058f31540012f700b9662a80065e20172cc550005adc026598aa00097980dd9315400127f08bb262a80624f211764c550004b7c12ec98aa06796c825d931540012f700bb262a805e5760f744c5500043fc32e898aa00087c865d1315402f6ad0331a62a8002d6602634c5500bcae43ac698aa07fb1c8458d3154001ca8c2b1a62a8002d6e01634c5500bcae43a6498aa000b5b804c931540e12ed0fb0a62a81c25d21d414c5500053a4328298aa07ff1443505315402f2dd053b642a80025ee0176c8550004bdc02e790aa001978805cf215402f6c902b1642a8002dae0162c855000732b16c390aa0189778750721540014e90ca0e42a80025e6037648550004bdc02ec90aa00087f865d121540010f90cba242a80025ee01734855000cbc402e690aa000b6980989215402f2d90eb1242a8002dae01624855033cba43a6290aa000a3d8494765500010ff0ab8ec6a00121f21571d8d400046fc3ac631a80018bc865d253500111f10cb84a6a00221f21d6554d400058ec28c6a1a8000b998094d43500011df0eb10c4a001e2f212769494000c5e432e92928000d9a30dcd425000155d0d29284a00f78b195525094001cd6c16e2a1280018bc865d332500111f10cb8664a001e3ba0a768c94000c5e432e91928000e8f6350a32500031790cba264a001e2f212760c94000c5e432e81928000c9d74d8c32500019aec6b8864a00233518d710c94003c7c432e01928000cdb635c032500119b0c6b8064a000a2f21173d854003e5739285b0a80a7c3c76dd5415014b878ec3aa82a0002ce60075505400071b28ecaa0a80028bc87595415000556d03b1282a000a3720d76cc54000c5e432e998a80088f8865c331500119b0c6b8662a00062f219744c5400146f43ec698a8074e946350531500011bf06bb642a00223720d76c854000c5e432e990a80039b78750721500031790cba242a00065ea1e53541400c59d424a6a828000b398494d50500ed6e50329aa0a0002dc60653541400078d29a86a828000f195350d505003167509292a0a0002ce61252541400263c3b2a4a828003cb8765095050001e54a4a12a0a0003ca54942541400253d42ec2a828076f32515055050001e62a2a0aa0a0232cea1f74541400c69d43ee8a828001b3a86dd150500036710dba2a0a00634e9db74541400c69c3b6e8a828000b3983dd1505000167305ba2a0a0002ce60774541400c59c426e6a828000d3b74dcd50500314f50d39aa0a00029e61a73541400c59d424e6a828000b39849cd5
  | 6 => 0xc49e422ed992a00097b805db32540012ef02bb464a805e5d205768c950004bdc02ed192a00097980dd9325400127f08bb264a80624f211764c950004bbc0aec992a017974815d932540012f700bb264a80065e203744c950004bdc02e8992a001978805d132540e12d90ea1264a80065e203714c95000cbd43ee0992a00497a86dc132540092f10db8264a80025e613704c950006b5216e0992a000d6942dc132540012f303b8264a80065e202760c9500063db04ec192a00487f809d832540018f7013b064a80121f602760c95033e3c404ec192a000c7a409d832540018f4213b064a80025ee01760c9500063db02ec192a08f87f805d832540018f700bb064a80031e901760c9500063d082ec192a00197a805d03254001a7480ba064a819f4b8c9740c95038696992e8192a000d3a805d03254001a7300ba064a823f0fd81740c9500069db02e8192a000d3a105d032540032f500b8864a80035c841710c95033eab992e2192a067d55325c43254001ae500b8864a80035c601710c95047e3bb02e2192a000d73605c43254001ae480b8864a80125ea19700c95047e3d432e0192a067c79865c032540092f10cb8064a80025ee11700c95033ead992e0192a067d6a325c032540cfab264b8064a81c35a4c9700c950004bdc0ae0192a08e97b805d361540032f100ba6c2a80024fe1173d85500c49e422e7b0aa01497b805cf61540032f100b9ec2a803a5ee0172d855000cbc402e5b0aa01787d87d8b615402f4e902b16c2a80065e20374585500bc3e43ac4b0aa00197a86dc161540032f10db82c2a80025e6137058550024bdc0ee0b0aa00497981dc16154001ae6c3b82c2a83275c187705855064eb920ee0b0aa00097980dd941540018f4e1bb282a80031e60376505500063d206eca0aa000c7a10dd941540010fd0d3b282a80025ee017650550384af418eca0aa00095d831d941540cf2dd043b282a80025b60876505500061f420eca0aa000c3d841d941540018bd063b282a80031760c76505500061e218eca0aa000c6e821d941540018db043b282a80030fd0876505500063b408eca0aa000c75811d941540018ec623b282a80031d08476505500243fc00eca0aa000c7a801d941540090fb003b282a80031e60076505500061fa00eca0aa000c7a401d9415400187a803b282a80031e50076505500063b880eca0aa000c7a101d941540018ea203b282a80031e44076505500bc9e43ac8a0aa000b3b8059141540032f501b9a82a80025e60373505500bc9f43c86a0aa000c3c7690d41540032f501b9282a80025e60372505500bc9e43a84a0aa000c3c765094154107e4842a1282a80625d21d6150550005b9c02c2a0aa028a78865c141540018f0ecb8282a805e57a0e76cc5503862f41ced98aa070c76319db31540e18ea633b662a
  | 7 => 0x78805cf64540012ef02b96c8a805e5d20572d9150074bdc02e5b22a001978805cb645411b2f700b8ec8a80065e20171d9150024bdc26e0b22a00497984dc16454001a76c9b82c8a832b4e1937059150004bcc0ee0b22a0cad3b41dc164540e10fb0fb26c6a81c21f61c61d8d500051ec20c3b1aa000a6d821876354001ae500b8cc6a80035c6017198d504863bb02e331aa000d73605c66354001ae480b8cc6a80025ee117098d50006adb1ae131aa070d58635c263540e1ab486b84c6a80025ee057098d50386ad98ae131aa01893e87dd16354001a7701ba2c6a80034e2037458d500069db06e8b1aa000d3a10dd16354031878e9b22c6a81c21f21d6458d500061e3a4c2b1aa000a3d841856354001878e830ac6a81c297a0c6158d5000536c10c2b1aa000d3b74dc16354001a70e9b82c6a80025e6137058d50006adb1ee0b1aa00097981dc163540012bf0eb18c6a8002d6e016318d50074bdc02e431aa07095e839da43540012f700bb486a80030f5db6490d500c58e422c721aa000e1f6458e43540016b700b1c86a80025ee017290d5000cbc402e521aa00097980dd943540012f700bb286a8002d66026350d500c4ae43ac6a1aa000b5b8058d43540cf0fb0e326c4a80029760c64d895033d37410c9b12a000a758119362540cf0fb0fb1ec4a80028f21163d89500069d402e9312a000d39805d2625411f87ec0ba4c4a80034ed8174989500069d082e9312a00097b845c26254001ad6c4b84c4a819f5a189709895033eb5212e1312a00097b815c262540cfad642b84c4a80031d1c664589500052ec18c8b12a067a6e8219162540014eb02322c4a80031d1c464589500063a38ec6b12a06787c8758d625400147908b1ac4a80031d1c5635895000cbc406e2b12a01797687dc56254001ae701b8ac4a80035c2037158950006b9b06e2b12a000d7240dc56254001ae6e3b82c4a80035c1c77058950004bcc26e0b12a000d6b62dc162540012f303b82c4a80525ee017318950004b7c3ac4312a000b6b8058862540cf2dd053b484a819f1ba0a769095033e1fa14ed212a067c3d429da42540090ff013b484a80121f60276909500063d204ed212a000c79409da42540cf8de413b484a80031b48276909500063d084ed212a00097b805da42540018f700bb484a80031e90176909500063d082ed212a00097b805ce42540032f100b9c84a80031b9d96290950425b240ac5212a000b6b8058a42540cf2d904b8c84a80025e6037650950004afc1aeca12a07095c835d942540012ef02bb284a805e5d2057650950004bdc02eca12a06793e87d9142540cf2790ea1a84a81c3471cd43509500c597424c4a12a000b698098942540312d90eb1284a80038b191625095041db240ac4a12a000b6b8058942540312db05b8a84a80024fe1176cc9500
  | 8 => 0xaba6c090a3f1bc817690b5000636902ed216a08f96c825c642d4121a38e6a1a85a806a5b60b7150b50484b643a84996a08fc7a805d832d40018f300bb065a82434798d740cb500068eb1ae8196a08fd2e625d032d4001a5ac4ba065a823f4b8c9740cb5048696992e8196a090d56635c432d4001aaac6b8865a823f59989710cb50006b2b12e2196a08fd57325c432d411faaa64b8865a823e5ee19700cb50486ad31ae0196a000d59635c032d411fad4c4b8065a80035a589700cb5047ead992e0196a08fd6a325c032d411fab264b8065a82435a4c9700cb500061fa06eca0ea000c3d40dd941d40018ee21bb283a80031d44376507500cc9f43c86a0ea01993c8750941d407b878eca1283a824fc908542507504862f982ed98ea000c5d305db31d40332b906ba663a80665760f744c7500043fc32e898ea00487c865d131d40332b90e99263a82425d21d414c75011d3a4328298ea091f144350531d40352ef0ea0e43a80021fe1974487500243e432e890ea0008f7815cb64540051e902b96c8a800237e1d6318d50006b9082e329aa000d72805c65354001ae300b8ca6a82431dd817194d5011eb9b02e329aa000d72405c65354001a7481ba2a6a80630f1d36454d5000c3ec2ced21aa0088de839da43540030f90cbac86a80030f5d76490d500070fb22a721aa00187e86dd543540030f90cbaa86a80125721d5350d5000477c3ac4312a000d3a405d25254001a7500ba4a4a80034e601749495047e1fb02e9292a03dd3b605d25254001a7420ba4a4a80035c843715495000c3ec2ced212a00787c859da425400f1dd053b484a80061f2197590950006373b2a5212a00187e86dd542540cf27b09baa84a80061f21975509500c597424a4a12a00496c875494254087c58c8a9284a80061f61676cc9500045fc22ed992a0038bc845db32540030f90cbae64a80061f616768c9500047bc0aed192a0028f4815da32540030f90cbac64a80061fa1b754c95000c3e432ea992a001978805d532540091f50db8264a80061f616760c95003c3e42cec192a00187c865d4325400f1f10cb8064a80022fe1173d855001c5e422e7b0aa017a748154b61540090f90a3b282a80030f95076505500446f418eca0aa0008dd831d9415400f1dd043b282a80023b60876505500063b288eca0aa00187e86dd541540032f501baa82a80061f21975505500249e43aa8a0aa0049748754541540030fb0b3b662a80221f21676cc5500146f41ced98aa00187c865d731540018bceca9e62a80061fa1b754c550384bac0eea98aa00187c865d5315402f6ad0329a62a80125721d534c5502772a30aa698aa00187d859db21540051dd053b642a80061f21975c855000732a96c390aa00187e86dd521540030f90cbaa42a80125b21d52485500a4bdc02e7b22a0019
  | 9 => 0x6250b31044e643a849966270a79809d560cc5214f700baac1988121fa1774583310043ec2ee8b06620487e85dc960cc4010fb0bb92c1988030f5d254d95310053ac0ca9b2a620487e87dd5644c4010fb01baac8988021fe1576551310146f436e6aa262088f686dc5544c4451bb0fb24a698812972156494d31014eb40ae529a62029d6815c2534c4091b90eb22a6988225721d5454d31275aa40aa8a9a624eb5685dc5534c58baa8a3b82a698adb6510f7150d310043fc2ae9b12620487c855d3624c40155b08106c498802b360c20d893100572c0841b1262008ef87588624c40f9d4c4b80c4988033a58970189310146e432e7292620787c87595524c49daa8e2a9aa49881e3b20976909310146e432e72126207ccc625ce424c40f1790eb2284988f68f21564509313a64e39ac8a1262028de86dcd424c4071dd0fb128498a7b5514575cc931014eb40eea99262028dc865d5324c40171b083126498802f2600624c93103e663b48499262089cc87509324c4015990ca12649881f331d9424c93152cbb43eeaa0a62aac7476dd5414c59fe2887baa8298a9b1d1d875505316778a218eaa0a6200b71801d5414c4478e8ebb2a82988038d953655053101c7a43acaa0a62029b487551414c4e972906aa28298803551d77350531006aa3a8e6a0a62cdb94841cd414c4013ad0f29a829888f551d653505313a5ca424a6a0a62009d48754d414c447aa8eaa9a829888ae521153505310078aaa2a6a0a6200ab486509414c599a68eaa1282989d2e520d42505312bf5231284a0a629ed5475cc9414c4e972909992829880ab521932505314eeaa3aa64a0a6222b94844c9414c401f0a8499282988021fe1574d81310243e42ae9b02620787e8795165c84014eb032a2cb9081e2fa1f54593210447bc32e329e420787c8759553c840f1790eb228790822a720d6450f2165f162a2c8a9642aac7776dd541c854d8eeec3aa8390802dc60075507210071b2a2caa0e4203ab48458d41c840156b0d21a83908f2b961b72507214df932a2a4a0e420487e85dd160c84010fb0bba2c1908030f5d254d952100c3e42ee0b2a420487e87dd564484010fb01baac8908021fe1576551210046fc3ac631a42078f4865c6534840717d093b2a6908022f6127654d210443f43ecaa9a42078f4865c643484010ff0abb286908121f2157650d210047dc02eca1a42018f8805d943484094d90ab24a4908129ba1764549210247643ac8a924204c6c7654d5248533d4843b228490822b5a0f644c5210447a43ac898a4223a748559131484015ad0d29a629088f95195534c521005b2c28e498a4200be1801c931484013c90ea92629080ab9219524c521007a2a9aa498a4207cd476cc931484053a90e992629081f351d9324c52103ee23926498a420087f855d360484090f9
  | 10 => 0x29282aac3e74d9652504051790cba4a4a08030fd9574949411ee1e32ae92928200c3e541d9525054f8e8e3b2aa4a080e3da1b71549411ee1e32eeaa128200d3651dd542504051790cbaa84a0a9a8fa1b655094153e1e3b6caa1282d1f2421d95425054b878ec32a84a0b43c908465509410059cc00caa128200e2c65d894250401c58ca31284a0802aba1a52509411ef1632ca4a12823cba48194942504015590ca9284a08f78b19552509411e5d240aa4a12823cba682dc5425040517b093b664a08021fe1576cc9410243e42aed99282088f4865c732504018e8cab8e64a080e3d606768c9410043fc2aed192820487c855da32504051790cba464a08030f195748c9415871632a85192823cda47150a32504090fd0bbb264a08021f617764c9410145f436e899282039ac87509325055fc58caa1264a08f3691c5424c94101c7b436e2992820487c859d832504010ff0abb064a08121f215760c9410043e432ea192820087f87d9432504010fb0fb2864a0aab0f9d3650c94153e3b38eca1928200c7a70d9432504051790cba064a08030fd95740c9410061e32ae819282078f4865c432504018eecab8864a08031d195710c9410063db2ae01928200c78655c032505558e8edb2aa2a080e6da137354541014ba43aa4a8a8204c74765495150407968eca12a2a095f691c9425454100792a9284a8a8200a7980dd760504014f3003aec0a08021fe1573d81410243e42ae7b02820087f855cb60504090f90ab96c0a0a9e1f21b75581410043f43ecab02820087e8719560504110fd0f2a2cb988229720d74597310452f418e8b2e6226a5d831d165cc4014dd043a2cb988029b60874597312753b408e8b2e6200a75811d165cc4014f5003a2cb988029e60074597310051f424e4b2e6200a3d849c965cc4114bd07392cb9893a9da0742597310053ac0e84b2e6208a5e8310965cc4014bb06212cb9882297a0e70597310052ec1ce0b2e620087e8790165cc4010fb0f202cb988021fa1c40597310043ec3880b2e6208a5e8310165cc4014bb06202cb988029ba08405973100536c1080b2e624ea768110165cc4014eb02202cb988021fa1e20597310043ec3c40b2e620087e8708165cc4010fb0e102cb988028fa1020597310051ec2040b2e6208a5e8308165cc4014bb06102cb9893a9da0420597310053ac0840b2e62028dc835d954cc4110f90eb2aa99880317597735533112c6e43ac8a9e6204a5e8559153cc4112b90eaa2a79880297e195454f310243f42ee8b16620087d85dd162cc40187ce8b2ca5988f70f9957494b310061eb2ae92966200c5d655ce52cc4051bd07bb2a59880317dd95354b310243f42aed216620087f865d642cc4010ff0eb2c85988021f61d6590b310146e41aeca166208c9c7359142cc4111d90eb128598823331cd
  | 11 => 0xc8011f50e28ac0190023e61c51580320055d420a2b006400ab984145600c8115b50628ac019002b660c515803203d75410a2b006400ae982145600c80f5d505a0ac019002ba60b41580320456d41c82b006400ad983905600c9a78baebb1cc6a8b4b355c76398d510046fc3ac631aa2a787f855d3625440f958c4ba4c4a88032b5d3629895100477c3ac4312a2078ec825da42544050f90cbac84a88031b5d7629095103d36432a5212a200c6e7654a42544071dd0fb1284a881e9b219525095121f16322a4a12a20287c865d632544050f90cba864a881e3d219710c95153c3fc2ae9b02a20187c855d360544030f90ab9ec0a88061f21572d81510cc3e43aa5b02a200a3d8494365504510fb0e306caa080297a0c60d95410052ec18c1b2a8200a6e8218365504014db04306caa08031e5c060d954153d1ec26e7b2a82aaa75811cf65505554eb03b96caa0a9e8f61072d95410063db84e1b2a82aaa3e841c3655054f47b08386caa080297a0c70d95410052ec18e1b2a8200a6e821c365504014db04386caa0a9e9da0470d95415553ac08e1b2a820087e878c365504010fb0f186caa08021fa1c30d95410043ec3861b2a82aaa3e840c3655040147b08186caa08029ba0830d954100536c1061b2a82a7a76810c365504014eb02186caa08021fa1e20d95410043ec3c41b2a820087e8708365504010fb0e106caa0aaa8fa1020d95410051ec2041b2a8200a5e8308365504014bb06106caa0a9e9da0420d95410053ac0841b2a8200d3b405c06550401ae620b80caa08031ea1970195410069d422e032a8200d39845c0655055d8f6c8b80caa08034e10d70195410069da12e032a8200d72815c06550401ae302b80caa0ab71ed857019541006b9a0ae032a8200d3a415c06550401a7082b80caa08035c1057019541006b918ae032a8200d70215c065504018f2e1300caa080297a0c60195410052ec18c032a8200a6e8218065504014db04300caa08031e5c0601954153e1e3b6caaa282029b681dc954504014f30032ec6a0b3b1d5c46598d410053cc00cb31a820087e87d95635059fc3887b2ac6a08021fa1c6558d410053cc00cab1a82a5c767119463504014f300328c6a080237e1d6318d410145ec24ed29a82088de839da535054f8ece3b2ca6a08223d2197194d4111e3a32ae329a8200c76511d95350555878e9b2aa6a080a2fa1b7454d4101c9e43aa8a9a8204a3c865515350401a6ca2bac86a0a9f0f9db6590d4152e1f3b0cb21a8200b3980196435044533b0fb1c86a080387d976390d415d78b28aa721a82029b4815ca43504014f30032ec4a0b430f5d065989410053cc00cb312820087e87d9562504010fd0e32ac4a08029e60065589415361f3a0ca3128200a798019462504011df0eb10c4a081e3ba0a769494101c7ac0ced
  | 12 => 0x2ab60851590320055d400a2b206400ab980145640c80147d0b382c8190028f61670590320454e41ae0b206400a3e851c1640c80147b0a382c819022a7a0c705903216d4ec18e0b206407aae821c1640c85b55b04382c819002ada0470590320055ac08e0b206408a9e83d41640c80153b07a82c81901eaba0b505903200556c16a0b206400a3e85841640c80147b0b082c8190022fa1c10590320045ec3820b206400a3e85041640c80147b0a082c819022a7a0c10590320054ec1820b206407aae82041640c80155b04082c81901e1f21d655503203c5e43ac8aa06407ae682d05610c8014ed0b082c2190029d61610584320055b420eab086400ab5841d5610c8115ad063aac2190b2b560c755843203d73410eab08642cae5821d5610c8015e5003aac219002bc60075584320456b41ee8b08642cad583dd1610c80f5cd053a2c219002b960a74584320053bc2ae8b086400a74855d1610c8011ed0e2a2c2190023d61c54584320456b418a8b086400ad583151610c80f5cd042a2c219002b9608545843200579400a8b086400af180151610c8014ed0b382c2190029d616705843203d72412e0b086400a76851c1610c8014eb0a382c219002ada1070584320055ac20e0b086408ad6831c1610c8595ab06382c21901eb9a08705843216572c10e0b086408ad683d41610c8015ab07a82c21901eb9a0b505843200572c16a0b086400a7685901610c8014eb0b202c2190023da1c40584320047ac3880b086400a7685101610c8014eb0a202c219022b5a0c40584320056ac1880b086407ae682101610c8015cb04202c21919e9e602755803247d3dc02eab00640487e85dd1600c8010fb0bba2c0190121fa1771580320043ec2ee2b006408ada83d41600c80f5d505a82c019022b6a0e75580320056cc1ceab006407aea829d5600c8015d3053aac01924396a0e75580320072cc1ceab00648fe6a829d5600c801cd3053aac01923f96cca755803247f35194eab00648fe59329d5600c921cd2653aac0190031ee1d755803233f2d992eab006467e6a325d5600c8cfcb264baac0191c39a4c975580320053d42ee8b006400a7985dd1600c8018f2ebba2c0190031e5d574580320456c41ae8b006400a7a851d1600c8014f30a3a2c019022b6a0c745803215d6cc18e8b006407aea821d1600c8575d3043a2c019002bca04745803200578c08e8b0064008fa87151600c8011f30e2a2c019022b6a0c54580320056cc18a8b006407aea82151600c8015d3042a2c019002bca04545803200578c08a8b006400a7a85dc5600c8014f30bb8ac0190031e5d771580320063cbaae2b006407ae8825c5600c8014f50a38ac0190029e61471580320055d420e2b006400ab9841c5600c8115b50638ac0190aeb660c715803203d75410e2b00642bae9821c560
  | 13 => 0x53b40860b2c8400a75810c165908010fd0f082cb210021f61e10596420043f43820b2c840087d87041659088747d08082cb210028f61010596420052f41820b2c8400a5d83041659080f4dd04082cb210029b60810596420243f42ee2b1c840087d85dc563908018ece2b2ca7210031b5957294e4211e3b32ae329c8400c75655c6539080f1dd05bb2a7210029be195354a421fc7643aa4b0c8404c6e7554961908cf4f3013aac12123e9ee0175582420243f42ee6b04840087d85dcd60908090fd0bb8ac1210021f61771582420051ec24a3b2a840087f855c763508090f90ab8ec6a1002a761030d8d4200566c1061b1a8400ad5810c363508011bf0eb18c6a10233698d7018d420066cb1ae031a84088ec865ca53508110f90eb2aa6a1022a7a1b6350d420058ec28c6a1a8400b998018d43508073390ea9a86a1002a72195350d425b64e31ee2a1a84079ae82dc5435080735d08b9ca4a10026be1d439494201cd7422e12928443b2e85dd1525088765908a9aa4a10f6cb215435494200786a9a86a9284c3d2c54dc152508791db0f296c2a10021fe1571d81420243e42ae3b02840887c8759554cc811938e6b2285990121fa1771583320043ec2ee2b06640787e87951658c80f17d0faa2c9193538b1516550a3203cd643a86a146408d8c7350d428c8090fd0bba2c1190021f617745823201d57426caa1264038ec87595424c80178b0239a8499002f2600735093203cd643a86a126408cac7650d424c811b18e6a1a849901e1fa1e54594320452f418e8b28642ea5d831d1650c80f4dd043a2ca190ba9b60874594320053b408e8b286400a75811d1650c8014f5003a2ca190029e60074594320051f420e2b286400a3d841c5650c8114bd0638aca190ba9760c715943203d37410e2b28642ea6d821c5650c8014f50038aca190029e600715943203d3741682b286400a6d82d05650c8114bd0720aca190029760e41594320043f43c80b28640087d87901650c8010fd0e202ca190021f61c40594320452f41880b286400a5d83101650c80f4dd04202ca190029b60840594320053b40880b286400a7581101650c8010fd0f082ca190021f61e10594320043f43820b28640087d87041650c80147d08082ca190028f61010594320452f41820b286400a5d83041650c80f4dd04082ca190029b608105943203c5f43ea8b206408a9e83905640c80147d0b202c8190028f61640590320454f418eab20642da9d831d5640c80f55d043aac8190b6ab60875590320055b408eab206400ab5811d5640c801575003aac819002ae600755903203d57416e2b20642daad82dc5640c81153d0738ac819002a760e71590320051fc2ae2b206400a3c855c5640c80117d0e28ac8190022f61c51590320454f418a2b206400a9d83145640c80f55d0428ac819
  | 14 => 0x5841c96194c115ad06392c329946b560c725865300579400e4b0ca600af1801c96194c011ed0fa12c3298023d61f42586530456b41884b0ca600ad5831096194c474ed0b382c3298029d616705865328d3b428e0b0ca600a75851c16194c0156d08382c329802ad61070586530456b418e0b0ca651ad5831c16194c015cd04382c329802b9608705865311d3b42c80b0ca600a75859016194c011ed0e202c3298023d61c405865311d3b42880b0ca600a75851016194c115ad06202c329802b560c40586530057341080b0ca600ae5821016194c474ed0b102c3298029d61620586530047b43840b0ca6008f5870816194c474ed0a102c3298029d61420586530055b42040b0ca600ab5840816194c115ad06102c329802b560c20586534853dc02eab04a600a3d859036454c011df0eb10c4a9a421f21d54d81530051ec24a2b2c86bae545154d6190c090fd0bb8ac1218021f617715824300477c3ac43128604c5e7554f6150c010ff0ab8ec0a18121f21571d81430054f41c82b24a400a9d83905649480147b0b202c92911a8fa1473592520051ec28e6b24a400c9d731cd649480f55d0439ac92911aab60873592520055b408e6b24a400ab5811cd64948015750039ac929002ae600735925203d57416e2b24a446aad82dc5649480153d0738ac929002a760e715925203d57414e2b24a400aad829c5649480147f0ab8ac9290022fa1e31592520045ec3c62b24a407aae820c5649480155b0418ac9290f68fa1670592520051ec2ce0b24a446a3e851c1649480147b0a382c929002a7a0c70592520054ec18e0b24a407aae821c1649488d55b04382c929002ada0470592520055ac08e0b24a43da3e858c1649480147b0b182c9290022fa1c30592520045ec3860b24a43da3e850c1649480147b0a182c92901eaba08305925200556c1060b24a400ab6810c1649480156b02182c9290f68fa1610592520051ec2c20b24a4008be87041649480117b0e082c9290f68fa1410592520051ec2820b24a400a9e83041649480153b06082c92901eaba08105925200556c1020b24a408a9c83591439480717d09b9ac3290022f613735865247d3dc02eab04a4008df8758c63548051ed03bb286a90023d6077650d52024ae43aa6a1aa40187c855c7605480f4dd0539acb210029da0673596420053ac0ce6b2c8407a6c825c5659088747d0838acb210028f61071596420052f418e2b2c8400a5d831c5659080f4dd0438acb211029b60871596420053d400e2b2c8400a79801c5659088747d0918acb210028f612315964203d3741062b2c8400a6d820c5659080f4dd05382cb210029b60a70596420043f43c60b2c840087d878c165908010fd0e182cb210021f61c305964221d1f42060b2c8400a3d840c1659080f4dd04182cb210029b608305964200
  | 15 => 0x2001800002c00002c00004400c01001000000000c01000803c0a000000800401805400003c00800800c02000000401800001000000003000803400800401002801000400800400000001000002001003001000403400000000800000400000000000802400000c02401400000800401c0000300200000140000000780080b402400004c01000400401c00000800000801401400000c00c01000001000c03c00001006400000000800000800000001c02800c00006400c00800000001401c04400800001800002800c00805000804c02400400000000c00000003400000401001400000c01401800c00402800001400000001000400c00000000400c00000000c00000001001c00c01000000000001c00000400400802400400401800000800001c01003800400000000000004c00400000000402c00400400c01800002000006400c01000002802000c00002c00c00000001000801800001400000000000000800400000400400000000001800000400000000000c00000400c00800800000c00001401002800004801c00c00800000400001c00400000400401000c09c0a401000001c03c00800800c00800001c01800400001400402401800800005005000002c04800000001005801400800000000800001400800002c01c01001805401001400400000800400000400803008401401004c02400800400400400000c00000400000c03000402c00400401800c00400000000000001804000c02400800000000c00001003000000400000000803400000c01000402000803c04000802003000800400800002001c00001000c00000004000400003c01401000000000800003801802800c00000400001401c00400400001c00801001400c04c00c00000001c00000000000c00000401000802400000403400000402400c00000400402001000802003c01801c00c00000002800c01c01401c00000400800400000c01803c00001000000804c03002c00000000c00001c00000001000000403000000800800000400400801801c00c01003c01c01800c02000000000001000000c01c00401401401000800800406400001000001800800400000c01400c01400402000402800006400000000401c00400400c0040080000240380180000b800001800401802000800000c02c00002000801c00c004004054001550ff0ab8ec6aa00335d8d7198d540466a31ae331aa8008df8758c63551ad8daebb14c4aa3572b5d3629895400477c3ac4312a8aa87f855c760550051ed03b92c9298023d60772592530057341682b0ca600ae582d056194c014eb0b082c329822b5a0f745865328d6ac1ee8b0ca608ad6839d16194c015ab073a2c329802b9a0a745865300572c14e8b0ca600a77855d16194ca34ed0a392c3298029d61472586530055b420e4b0ca600ab
  | 16 => 0xf247719687140aa0fd1148f2ca226572908a9c71e4681b415c89944010000a40ddc82e27187e00005e913d91e804e1c73179288d762ec27a94982c60d83c910d06660001088bf02a200000000000005782878f680000610000cf85482972e0a07cc9479430220b0c5c0b015a800091633d31b9eb800030d1ed81a449a22300018e8da88123f80e003da7993b81a84ac200023381200000000e50000e844e600000007303ee05b82f40002053d41c3cc3402d25609749d218400018f420042f2b484d86b20003a894883cc53d0ce000000049a00e90888f20000001dfcc2a319305811c00035f0001bc80003d7002010c6384b91f5886c8124dc3cd001400000034c800106000011700002580000c6000102e51d00002680003d30000bc819220911a02b4f4a7a42971e705181fa02003b0d3626d408800026017440c0000a900d11d09c7444451f00018307626b83489f7c39640309301e06126253f91134f0e0003c1855c67827817300e8fd463c32e085c54000003f00003c62500dc16e80002ff0a79ddc00065911300000000002b380002a077e3e78000f1a7de00015c41e672000780001240002bc94a0b9a00008b02585b04131b0910800066b0001f6c1360001e7800034c0003cf80000006d300010c90404f430000004bc00000009b0f564ab0000584d0a7d01531804dbe2ed0d6878802651621c1db80484912c3800102652f0748000db406f2809b24b8c00013000000001f40a1800000037c0000000102037095000000033500018d803466c37307340005c51f79a9079a4b6000109c000000000000000000034d045cd9e44f00000008d42312669c001b200001a8c086a66c230e0f1c6542ae1ec02001966fc0fe00005b479613280d800082726c00000002691f989c4000789000000000052b00000006fe00025a94800000fa1e29074f2a6ff23588a8000202000000102c47005c9d8cd503140000a540000000a696706c03990000000000152000000000000002f80001900000000b78ca600020b00000061ac2259f240000001e30000d9c5a926480000003ae1688000fc81ff00015649266622c1834800073034a9cdc00059a1ba04c8b0c3693290ce05581113dd9ab80001ee0311c1c7c82b6017000000011a340804003000006401803000000000000400000c00801400c04400803802c00c02000001400403002800000c00000001401400000000400004000002c00400800000c00c00400400400008000400c00000400000000400400c01001005000400400802002c01001400000402400c03001000800400001804005002000c00001800801c01c00401001800800803c0640040040000cc00c00c00003800800000801c00800801801800807c00000000000000400c00000805809401400402001000802800c00000400000000
  | 17 => 0xd1000000000034f800070400000004405280563fe01047027c10001608f142080001e4d0160000000000b5651e1850000000000267841cd8672c0000454000000000103c0000000000000f840e00eb000000004f0001ec02d40022740308b2e3ab192976893064605095883642790c291f03a66cb1c806d0cc010e1d502f0e3671431390d885400018f00006086421e50f98abc3323b61ed0fa824f31c0db863608d0af9e44cf63d536317301525e42c5184056057e3238000b60000159188834a2ef30b9418f46000261990c42c0000000000a466dd3a789d80000000000b5cc6800000008c09c224a1881d24000000000091037438500000005fa0000b3000000000000003949184a420e000000000037480000001641138ee861e677365000000032c12e143897e0001fc93b402e00033c06fc50c3fd4001744f6441224293100006f501317840000000000000e2a60307c9ec4faa0000000000b5400000014ec0000004070304e344bc00000009641882ae89f41bc68f06a1f10d0800000016a075a42d0001c382ba0f03131f44bd639700000000000331a2800093e67e34680003787f43b513cca0a4ad07791d40002e130c1d40cbe1620e7800000024800000000000000000f8c28c00024e000000056b0001c180000000301c240008212030864cba00007f188107017922c00000000a01840e9871443c0a2083468445924a0690a0000000017cc88875e3e3000046e2040000ae80000002bb800004053c0af1a94e9606300c8ad07824502d28130000000000000000000000000000000001de00005666733851d580007dd08790ed0547c701082fc00000038819c04502c723896908da3173718e30de07c328901d49b25493b58d3c30e1d739785b435e23b000081c27637624104c4a805e70e800000000a53460d581620001a48c68d986332ca83a02ca58f37106280004db000028800013a08184e000077401e800000000000000000002752c898287280000000b3c60e071182939cf6a0002120aac3066b126385d474e03800000000004f10be117057e70b082153000073141a024c28e5bb23088e4bec0003df114c36a5ce17588d48a205200000000000000001ce800049034b958cfd200001f85e8e720003918e10b000000000648076000000000000000011283f0546000119129c18a3e53f89e740000001c1961005e0001aa80000005d83bd91bc0000000000000b186aa2fc00000000000421b5ce4c215000000033a0000e118480000003ac10e46de3720dc8000c766a203980385a650d00000000003b701c87f800057d00000000002fe00012d000000026080001c80002cd80007ee29f37400000002ee41489f05300000001c4c51c00005b1c78c8028237e80004c40000001c3034e7602c90ef4d288070aa8f30d305020e618fc3
  | 18 => 0xf0265124e870c3d636c0330b0c0001801478000000000011000000000022300005122c50001b0000045d01915604485cf022a068db8000000000000000000000000000000001f48000000000199833c0000000fd09ca0002dc80000007430001aaccbc000000033c15e82b3389d8400000009693e410475c11e80002a602b02c04b86fa68331900004203582a29924d147400000b048c632b0000000f52735000020c0000000000480c3e24317500000005b2000000015c0003e58448ed23222a813c0bd854e3598000d26313000027cb2c2cd26818a84cc18233d0d0492c00039b0000a3400039d8000ef00f63d6800000026814d000000000000000005965f10000000b9655c2f1800090855408e88d80003031809b100005ff29489c00006d526292e00003d9000111c00000000005cc00062b02813502ee5472ff0d1c3884330000c984ae3f60bb141081c5fc1fd145448a1a21c40e48d5a65500017204fc0512cc07dcc9a000000000000073d00007d452615429a01b83767440000f7c4e433406a800087425324d977cea65e02980000cfa0004130aa8000299171044c0b47ef2f71c20a4e119000065ca48539234a07400045b221954cca03b82081f88a8224625b80403bc32e00012005e65701df000000008700000008aa1e8000000031600041799942526b73821d9408c66909f97e813061921b90780000000001ef46ee0000000a143520b8382920502a0e306802e815058e2e11c5c0005ad3db93541283950ee00009e4000137800031a00007509fc0002f63500f480006a332d0000b3c000412000069c0003788000eec38d0e882200000000000a2c0000f72fd8f000007620000ca00003a400000000000003a600008fc46427f0000e421080ad00000003f507697c00005900000000f8080424c80009240000fd8a206ce5c4000145c00003120293780000000001e4072629b40a0000aa40c71c58d402725dc0000930a9a45a0e41d280000003d380000000002eb13900000000001b8400033b23a07380006920351bf863a000000001ce7c0004141e300000001d9800090609c06d8c840007e50000000000000000000000000000000007fe0000001cd000c00025180000000001259d54000000000043400028a000015000000012480000005ac2020000ae600000017d083473c1a6a0c87863e907a9e18f4200000600001e449532b132c0006b500019900000003fd06cc7403e700000500006c1000101c0922f11b29180aec3782f30000c3c00019b8b9002c82204f1eb01ba16700009b800000007110d400000000020dc0004a934e0000b3e73f000146031e19b0000aa00007dc0000000eea2f0000096ce3e2d00000000b942d23928f74d7279e00000000004bd000118800035c00015ec0007790000000000329000000079c28d3
  | 19 => 0x1a4135c18078827c0a003600000000ae40000003db18e45e87e70000000068000000000014800006b0000a7c7183ff00003460000f9000000041509399146960ee0000450e320000000be89d600002105ecebe5573aa16dc8fa20008d8044000000000037cbea0741319f3411200023b0000a2638900000000002b73040000a860000001464bb60000000680000000000000034206b2061d6ce5c0000000828bd44dd29a955476a39c00681c0000701000027467200037d0af0d8e5b51db1bdc4d64ce26012cca6204a07a00f077600000016f47522402ab10f48366ea0000cfce060000ac8000cb600005199b800000019380000000ab0001ff400000039417243e61490cb0b0800081b38e0754dc84140f7835c8567f50390c800005a73031b9c0b800000007a8c260003c200000005bf1058000998771109a028e4810a0001ac80000ce3e40000f0068000010c00007d316609386e23150000e1c0003a20b4177400000033b0fa8b5c000000000000063008c0a8400040800000001767e323d9fac0000002c483ecad44260000000f720000ed00209c46f90000508fac43e000000000001c32090080006d600018a40000003b795fc0d034300004f873a7113b91cb4c2878b0488000c2200035e0a88db63512ef00008404561a20ba0f2e7a02950c8c7a8000162112444239b12105b0d3a7ff276000000016b3cd8b7091c01f23293f4e9a00003b09640004290b704240008020001bd066c2730e300000001e93f01a404741fd14904942787982689b9498441f3141b483be0001700000a4a3910000b582f00002208490fae53a28515d0f780971a60a747e40000001a184c83dc327841901e51b00016985620000000fe10380002fb8000d740000259000ba600023319f00881352ce800087e64b2b3000000012300000000005942a585700006720269ad09ac29c2db0094a2058522b98589ee00000002a89d4000000000106a000004908c6a856e3be1148d7a6ef19207508e60000000000e5200033c9df4dda78f03d19a05d23570001fb476400038100004826bf29b181c59468817a81b023c0001a904cc0001901831a2400066f2e382549c01e016d83347fc0671030784f0a5e835314cc0002df13392187d030e2439b600000c63e29d98b4042e36884700007410000d9906674729905147e21f024f0b507da5bc3b21510ce800025414b42021210829a2c7d86233ae9ce07c431115c1fa00000000f28d889601f100010340005d500000000007453fb80000f6425198066502000000000000b20000e0800000000000015080000002e180004ac4f6376000011400002d8fc01ce0f114386680000000db847c1c200005a1128fd8000205000000000022f8dec00000000002b0434318000000037c0003e5000000008f00009d070c1dd0000e94
  | 20 => 0x3d85a21cf80b055200011f92ec0005ed000000041e61d00015e807c4ff1a30e682160000001d9c0000004019be0d5200000000000000000000d280000eb00000000000000000000bde0000000f240002c9000000095e00020c0538d8a0000000be401458d15d8c7c2b01483538dac28035d2ad0b9450212f2f91c348d81710118000bb256541b189000077a0e01ea833028423c201860001b0a6199ca0681919780486b407d2c40558c426580000af4000000000000011c3b40bea020e445143ec8880db237a11c174816a2140d501384023d02229c48aa22c823f93f0ed02831d6125cc627160621750e9c60d0001cccc583a802b99fc00000026980009107e625d1920000661000000000000000000000007f831693bcc1e5af18b1ac010c0002ad8488de672700000001fe0002a3000000007910900008dc0000001f3800025a2690000d9002a04c99a80006eb014974095c5681fd80003a400000000001181d80001ca800000017180000000c33e620b42502613dd15d43c800017b9f68b1622b00001f09b409000009500000000a08830eae27a41192244d44480d58dccb024fa116975ca6e14a347153c3265f9107182481600031a81740606f600000008225fd0002034d580002960b646fc000252800053c0001b21e380000000001d6400000005980000005be3f7000000000040485c80000000001ecca7e00012c06c489c507246887d0727af12f8f800006750bf08602964a00c890b10624c630100006e059309a1788fec4a10b78e8c6c639611601b400078200010640fe0002860b005f6000302800000025500000000001370000ec0000000000000000000000000000000000811e98000000000000000030c2b78000ff25380c492c435c36a3f98000000000198800000039e000034cd0e56c37d85803ce2ad00000000027b81239590b620002e001900000da0000000f7e63e2d088cc00000000000000000000000000000015000000052256035f16643ec0003a30d786800ca1e1000000056d0db137c82e48f000122800057c0c705c000000005312f87ac65411e1b78a123b91df93208a83e110e9b8014e0000000ce875e19f28400006f230b000108457c00000000000000003ad08f803038e22f1a08406000400800043c6af0590f4400000006e0000e56000014022c0bc00000000000002a5366800055e0000000000b701860ca0000c9c5e5000056cd2c21c1ef021400000000003980000be16719b48621bd00000003020003fd800000054a000000058c0cc0000194000000000000000025209e80002fe2e7000000000036d03b942c52c81e189198c3928252d18078da04fb1ad991000000000000005ba2d527711c800037535b1dcc94c3fc00000000000002140000c36000086014c3b600025516ccb683c434f05a43b23c8
  | 21 => 0x75239908bc00055f3f08654c980f8402983835000000000004ee7d828e000000000b226094501874817c00002560003b6910
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401869825c060195410061c5c580196635040183a766006590d4167e0761f65d8e43504018397460065989410060e1d9801954250401b202160065509410058a64065d8942504016299019462509410051c640655c7325040143990195748c9410041e640865d4325040143990195740c9410051c640655c4325040107998195700c9411e54925d525095150487c247654942545410061c1d9801d5414c401b104360075505310055464075dcd414c401551901d473505313a4c52615454d414c49d5149755153505313a4e1261424c9414c4016849650932505311e6a1219424c9414c5afd047550932505310061cdd9801d541c849da448654d524c5210070358d625d032d4001c4563589710cb500071258d625c032d4001839801d06158d500060b1d1821856354001855831c464589500061c600711916254001834841c563589500058364c6458942540016259119162509500068920464589425400181d8460c76505500040f660431d9415400142d9210c76505500050e640431d9415400184d8360876505500050e643421d9415416b83980d08765055000619609811d94154001471908c476505505661c602311d941540010759808476505500051564c211d941540014719008476505500060e611801d9415400185a8360076505500061660d801d9415400186a8260076505500061a609801d941540018718160076505500070c501101d94154001c24211d942505500041ea60765c1415400161594185634c550006852106158d315400164592185634c5500068510c86505315400183876600755054021f0a1d95250950500013339160b74541400c60e21b745cd5050031318985cd43541400c54665c6350d505003162a969c942541400c4ca261725095050185c28765c94254140645c824572509505003132992e05425414000c8e259844c950500013199321d4154140004ca648875055050031330985c541541400c4cce6141c8550500011389761121541400051c6407558541cc001439901d7645053000c6625d844c5404c0e9c907650531501300050e6407559141c8001471901d761505200452625d6450d30480011e19121d424c1200066221d4350930480031c897611324c120004a6650864c530480032c89660d214c1200061c1d9801d5414409dc507654d31541100241ea6387591504407b438975914254110004cce5183dc5504402f470965cb7154110004d464c8750550440013619221d41541100bccc26174505504402f3329890d41541100bcd464f844c5504400117097611315411011d1c25d644c5504402f652969cd31541100bcd4261734c55044189c50765cd31541105edc4251734c550440032709660d21541100bcd826172485504402f5619718921541101e7281d94250520440032e0966112148110
  | 1 => 0x48371bc52601396800840416400620000000021b00000533f9280000001a03a8600108ca382687ce4003c1007a450f0fd0e003c800205f10000000319970f641398448e5e098e4ac3c18824d6223b02c7c7d2788c1a510a8e8e269361906e000c8c0867c0d83c00050a0ec8c850c010184e400bc4c003d00088000e140921a160b8ce5d001610601000d4e84c3a98c007e258005000000185a162d828426a33090002a3ba05042b0b8d024703681caa6119094a80007148ae0600140700000c010102002e0b00111901000e020107060e001a020000570e011f1404000b000f0000050d020b006265cd801cd649488730c9854d43549420048e640855c5640c8012719021574584320044e660435c065504015299210d70195410054ca44435c0655040153291d09701954100558a4b415c0655040151a9390570195410050ea58415c065504014729610570195410054ca52315c065504011719808570195410054ca50215c0655040155193085701954100616a0d701806550401859835c060195410061aa09701806550
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5800c000200000440000009a001d403000000c0000000724a0000000000000840002321a9085801954250401580d1842c00caa1282008c46a44360075505310056034421b003aa8298802035a92107158d6254001902c9902322c4a12a000c8864081191625095000484b52108eca1282a8002c05a3084765094154001610d00423b284a0aa000c8464084185634c55000640908c90c2b1a62a8002215a910c865053154001502d10864328298aa000a8468043219414c550
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x98a
  | 10 => 0x98d
  | 11 => 0x98e
  | 12 => 0x150a
  | 13 => 0x150d
  | 14 => 0x150e
  | 15 => 0x9ca
  | 16 => 0x9cd
  | 17 => 0x9ce
  | 18 => 0x168a
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0a
  | 22 => 0xa0e
  | 23 => 0xa4a
  | 24 => 0xa4d
  | 25 => 0x198a
  | 26 => 0x198d
  | 27 => 0xb09
  | 28 => 0xb0d
  | 29 => 0xb0e
  | 30 => 0x1549
  | 31 => 0x154d
  | 32 => 0x154e
  | 33 => 0xb49
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x16c9
  | 37 => 0x16cd
  | 38 => 0x16ce
  | 39 => 0xb89
  | 40 => 0xb8e
  | 41 => 0xbc9
  | 42 => 0xbcd
  | 43 => 0x3c9
  | 44 => 0x3ca
  | 45 => 0x3cd
  | 46 => 0x3ce
  | 47 => 0xcc9
  | 48 => 0xcca
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0x15c9
  | 52 => 0x15ca
  | 53 => 0x15cd
  | 54 => 0x15ce
  | 55 => 0x1709
  | 56 => 0x170a
  | 57 => 0x170d
  | 58 => 0x170e
  | 59 => 0xd09
  | 60 => 0xd0a
  | 61 => 0xd0e
  | 62 => 0x1609
  | 63 => 0x160a
  | 64 => 0x160e
  | 65 => 0xd49
  | 66 => 0xd4a
  | 67 => 0xd4d
  | 68 => 0x1649
  | 69 => 0x164a
  | 70 => 0x164d
  | 71 => 0xe89
  | 72 => 0xe8a
  | 73 => 0xe8e
  | 74 => 0x1789
  | 75 => 0x178a
  | 76 => 0x178e
  | 77 => 0xec9
  | 78 => 0xeca
  | 79 => 0xecd
  | 80 => 0x17c9
  | 81 => 0x17ca
  | 82 => 0x17cd
  | 83 => 0x1049
  | 84 => 0x104a
  | 85 => 0xa4955
  | 86 => 0xb4955
  | 87 => 0xb8b
  | 88 => 0x1409
  | 89 => 0x128a
  | 90 => 0x1449
  | 91 => 0x12ca
  | 92 => 0x1849
  | 93 => 0x1489
  | 94 => 0x180a
  | 95 => 0x130a
  | 96 => 0x19c9
  | 97 => 0x14c9
  | 98 => 0x134a
  | 99 => 0x209
  | 100 => 0xd0996
  | 101 => 0x409
  | 102 => 0x1889
  | 103 => 0xa4b
  | 104 => 0x1a09
  | 105 => 0x8a
  | 106 => 0xd1516
  | 107 => 0x8d
  | 108 => 0xb49d6
  | 109 => 0x249
  | 110 => 0x589
  | 111 => 0x18c9
  | 112 => 0xa4c
  | 113 => 0x1a49
  | 114 => 0xb5696
  | 115 => 0xca
  | 116 => 0xb8c
  | 117 => 0xcd
  | 118 => 0xa4a12
  | 119 => 0x138d
  | 120 => 0x124d
  | 121 => 0xd0a12
  | 122 => 0x128d
  | 123 => 0x12cd
  | 124 => 0x1a89
  | 125 => 0x1949
  | 126 => 0x134d
  | 127 => 0xb4a55
  | 128 => 0x16ca55
  | 129 => 0x124e
  | 130 => 0x2c9
  | 131 => 0xd0a52
  | 132 => 0x160a52
  | 133 => 0x449
  | 134 => 0x8e
  | 135 => 0x128e
  | 136 => 0x5c9
  | 137 => 0xce
  | 138 => 0x12ce
  | 139 => 0x130e
  | 140 => 0x749
  | 141 => 0x138e
  | 142 => 0x180e
  | 143 => 0x198b
  | 144 => 0x198c
  | 145 => 0xb5995
  | 146 => 0x16d995
  | 147 => 0xd1992
  | 148 => 0x161992
  | 149 => 0xb4b15
  | 150 => 0xd4b15
  | 151 => 0x44a
  | 152 => 0x188a
  | 153 => 0x148b
  | 154 => 0x1a0a
  | 155 => 0xd5555
  | 156 => 0x20e
  | 157 => 0xccb56
  | 158 => 0x170b56
  | 159 => 0x18ca
  | 160 => 0x5ca
  | 161 => 0x1a4a
  | 162 => 0x24e
  | 163 => 0x140d
  | 164 => 0x144d
  | 165 => 0x74a
  | 166 => 0x2cd
  | 167 => 0x194a
  | 168 => 0x1a8a
  | 169 => 0x19cd
  | 170 => 0x14cd
  | 171 => 0x140e
  | 172 => 0x144e
  | 173 => 0x184e
  | 174 => 0x148e
  | 175 => 0xd0cd6
  | 176 => 0xd15d6
  | 177 => 0x44d
  | 178 => 0xe8d12
  | 179 => 0x1a0d
  | 180 => 0x40e
  | 181 => 0x188e
  | 182 => 0x184c
  | 183 => 0xece92
  | 184 => 0x5cd
  | 185 => 0x1a4d
  | 186 => 0xed792
  | 187 => 0x58e
  | 188 => 0x18ce
  | 189 => 0xb4a495d
  | 190 => 0xa0a52
  | 191 => 0x94a55
  | 192 => 0x130a52
  | 193 => 0x10e
  | 194 => 0x98d16
  | 195 => 0x150d16
  | 196 => 0x9cb56
  | 197 => 0x168b56
  | 198 => 0x124a55
  | 199 => 0x4e
  | 200 => 0xd0a4a1a
  | 201 => 0x198a52
  | 202 => 0x198a55
  | 203 => 0x154d55
  | 204 => 0xd0b56
  | 205 => 0x58a
  | 206 => 0x2cb55
  | 207 => 0x14cb55
  | 208 => 0x74d12
  | 209 => 0x194d12
  | 210 => 0x144b56
  | 211 => 0x1a4ed2
  | 212 => 0x15cd16
  | 213 => 0x188d16
  | 214 => 0x1a0d55
  | 215 => 0xd0ccb5e
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
  | 7 => packedAt gbK7 (98277+((h/799+packedAt gbK7 (88689+(h % 799)*12) 12) % 3164)*13) 13
  | 6 => packedAt gbK6 (387148+((h/2450+packedAt gbK6 (352848+(h % 2450)*14) 14) % 11741)*14) 14
  | 5 => packedAt gbK5 (132678+((h/702+packedAt gbK5 (124254+(h % 702)*12) 12) % 3058)*13) 13
  | 4 => packedAt gbK4 (9880+((h/45+packedAt gbK4 (9520+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt gbK3 (1245+((h/5+packedAt gbK3 (1215+(h % 5)*6) 6) % 46)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe38f8fc0118e0c7ff1c1ff83fc206e00f1cf
  | 1 => 0x703f1f1ffe1f00f8e1e01c3fc3c4193b34933
  | 2 => 0x7fc01fe00fe000ff01ffe03ffc1861c438e3c
  | 3 => 0x7fffe0000fffff0001ffffc000207e07c0fc0
  | 4 => 0xf800000000ffffffffe000000003f8007ff000
  | 5 => 0xffffffffff000000000000000003ffff800000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x40210282480002001300405081202026001045
  | 1 => 0x11009010866190648452048918184080b14912
  | 2 => 0xa2440124109200892084980262818218428228
  | 3 => 0x58aa4002224a52000192528080a05c0140d80
  | 4 => 0x3000000004d948ce48c008003090c8006be000
  | 5 => 0xc6f349c938000100010030304323377f000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffffeecffeafae8fffffeecffeafae8fffffeecffeafae8fffffeecffeafae8fffffeecffeafae8fffffeecffeafae8fffffeecffeafae8fffffeecffeafae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_27831
namespace PEqualNP.Outside.L_meta_27831
open PEqualNP.Outside.L_meta_27831.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 9 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 50 := (concat bs1_3_0 bs1_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 136 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 8, 24),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 16, 48)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 2 zero,inputs.getD 5 zero,inputs.getD 6 zero,inputs.getD 7 zero,inputs.getD 3 zero,inputs.getD 1 zero,inputs.getD 4 zero,inputs.getD 0 zero]
def fullWord : Sig := 0xfffffeeefffffeeefffffeecfffffae8fffffeeeffeefeeefffffeecffeafae8fffffeeefffffeeefffffeecfffffae8fffffeeeffeefeeefffffeecffeafae8
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
  have lift := lift_ok (u:=true) (ms:=fixRows 192 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 6 zero,1,65),(inputs.getD 7 zero,16,144)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 2 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 8 → Bool) := decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
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
  unfold PEqualNP.Outside.L_meta_27831.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[8,6]⟩,⟨.or,[1,7]⟩,⟨.or,[5,6]⟩,⟨.and,[10,11]⟩,⟨.or,[0,2]⟩,⟨.or,[5,7]⟩,⟨.and,[13,14]⟩,⟨.or,[0,7]⟩,⟨.and,[16,4]⟩,⟨.or,[9,12]⟩,⟨.or,[18,15]⟩,⟨.or,[19,17]⟩]
theorem monoShape : ∀ g ∈ mono, (g.op=.and ∨ g.op=.or) ∧ g.inputs.length≤2 := by simp [mono]
theorem monoEval : ∀ x, Circuit.eval ⟨mono,20⟩ (List.ofFn x)=posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 12) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
end PEqualNP.Outside.L_meta_27831

open PEqualNP.Outside.L_meta_27831 in
theorem PEqualNP.Outside.L_meta_27831 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 3, 6, 4, 6, 0, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
