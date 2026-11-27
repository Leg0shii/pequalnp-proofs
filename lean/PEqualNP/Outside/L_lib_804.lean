import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_804

open Polynomial in
theorem pm {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (M : Matrix ι ι R) :
    (1 + M).det = ∑ s ∈ (Finset.univ : Finset ι).powerset,
      (M.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have h1 : (1 + M).det = Polynomial.eval 1 (Matrix.det (1 + (X : R[X]) • M.map C)) := by
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [h]
  have hdeg : (Matrix.det (1 + (X : R[X]) • M.map C)).natDegree < Fintype.card ι + 1 := by
    apply Nat.lt_succ_of_le
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors,
      Finset.powersetCard_eq_empty.mpr (by simpa using hN)]
    simp
  rw [h1, Polynomial.eval_eq_sum_range' hdeg]
  simp only [one_pow, mul_one, Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  rw [← Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι).powerset)
    (g := Finset.card) (t := Finset.range (Fintype.card ι + 1))]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.powersetCard_eq_filter]
  · intro s _
    simpa [Nat.lt_succ_iff] using Finset.card_le_univ s

theorem z2 : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

end PEqualNP.Outside.L_lib_804
theorem PEqualNP.Outside.L_lib_804 :
let F := ZMod 2
∀ (n g : ℕ) (part : Fin n → Fin g) (H : Matrix (Fin n) (Fin n) F),
  let sub := fun (J : Finset (Fin n)) => H.submatrix (fun i : ↥J => i.val) (fun i : ↥J => i.val)
  let active := fun (S : Finset (Fin g)) => Finset.univ.filter (fun i => part i ∈ S)
  let coef := fun (U : Finset (Fin g)) =>
    ∑ J ∈ ((Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.image part = U)),
      (sub J).det
  (∃ S : Finset (Fin g), (1 + sub (active S)).det = 0) ↔
    ∃ U : Finset (Fin g), U.Nonempty ∧ coef U ≠ 0 := by
  intro F n g part H sub active coef
  have key : ∀ S : Finset (Fin g), (1 + sub (active S)).det = ∑ U ∈ S.powerset, coef U := by
    intro S
    rw [PEqualNP.Outside.L_lib_804.pm]
    have hre : ∑ J ∈ (Finset.univ : Finset (Fin n)).powerset.filter (fun J => J ⊆ active S),
        (sub J).det = ∑ s ∈ (Finset.univ : Finset ↥(active S)).powerset,
          ((sub (active S)).submatrix (Subtype.val : s → ↥(active S)) Subtype.val).det := by
      apply Finset.sum_nbij' (fun J => J.subtype (· ∈ active S))
        (fun s => s.map (Function.Embedding.subtype _))
      · intro J _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
      · intro s _
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_univ, true_and]
        intro x hx
        obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hx
        exact y.2
      · intro J hJ
        simp only [Finset.mem_filter] at hJ
        exact Finset.subtype_map_of_mem (fun x hx => hJ.2 hx)
      · intro s _
        ext x; simp
      · intro J hJ
        simp only [Finset.mem_filter] at hJ
        let e : ↥(J.subtype (· ∈ active S)) ≃ ↥J :=
          { toFun := fun i => ⟨i.1.1, (Finset.mem_subtype.mp i.2)⟩
            invFun := fun j => ⟨⟨j.1, hJ.2 j.2⟩, Finset.mem_subtype.mpr j.2⟩
            left_inv := fun i => rfl
            right_inv := fun j => rfl }
        rw [← Matrix.det_submatrix_equiv_self e (sub J)]
        rfl
    rw [← hre]
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun J => J.image part) (t := S.powerset)]
    · refine Finset.sum_congr rfl fun U hU => ?_
      simp only [coef]
      congr 1
      ext J
      simp only [Finset.mem_filter, Finset.mem_powerset] at hU ⊢
      constructor
      · rintro ⟨⟨a1, _⟩, a3⟩; exact ⟨a1, a3⟩
      · rintro ⟨a1, a3⟩
        refine ⟨⟨a1, fun x hx => ?_⟩, a3⟩
        simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hU (a3 ▸ Finset.mem_image_of_mem part hx)
    · intro J hJ
      simp only [Finset.mem_filter, Finset.mem_powerset] at hJ ⊢
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
      have := hJ.2 hx
      simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
  have hc0 : coef ∅ = 1 := by
    simp only [coef]
    have : (Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.image part = ∅) = {∅} := by
      ext J; simp [Finset.image_eq_empty]
    rw [this, Finset.sum_singleton]
    exact Matrix.det_isEmpty
  constructor
  · rintro ⟨S, hS⟩
    by_contra hall
    push Not at hall
    rw [key, Finset.sum_eq_single (∅ : Finset (Fin g))] at hS
    · rw [hc0] at hS; exact one_ne_zero hS
    · intro U _ hU
      exact hall U (Finset.nonempty_iff_ne_empty.mpr hU)
    · intro h; exact absurd (Finset.empty_mem_powerset S) h
  · rintro ⟨U0, hne0, hc⟩
    by_contra hall
    push Not at hall
    have hz : ∀ c, ∀ U : Finset (Fin g), U.card = c → U.Nonempty → coef U = 0 := by
      intro c
      induction c using Nat.strong_induction_on with
      | _ c ih =>
        intro U hU hne
        have h1 := PEqualNP.Outside.L_lib_804.z2 _ (hall U)
        rw [key, Finset.sum_eq_add (∅ : Finset (Fin g)) U
          (Finset.nonempty_iff_ne_empty.mp hne).symm] at h1
        · rw [hc0] at h1
          simpa using h1
        · intro V hV hV2
          simp only [Finset.mem_powerset] at hV
          exact ih V.card (hU ▸ Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hV, hV2.2⟩))
            V rfl (Finset.nonempty_iff_ne_empty.mpr hV2.1)
        · intro h; exact absurd (Finset.empty_mem_powerset U) h
        · intro h; exact absurd (Finset.mem_powerset_self U) h
    exact hc (hz _ U0 rfl hne0)
