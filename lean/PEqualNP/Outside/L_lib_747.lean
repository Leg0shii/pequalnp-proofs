import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_lib_747 : ∀ (E K : Type) [Field E] [Field K] [Algebra E K] [FiniteDimensional E K]
    (S : Finset K), (0 : K) ∉ S →
  ((∃ C : K →ₗ[E] K, Module.finrank E (LinearMap.range C) ≤ 1 ∧
    ∀ z ∈ S, ∃ x : K, x ≠ 0 ∧ C x = z*x) ↔
    (0 : K) ∉ affineSpan E (Set.image (fun z : K => z⁻¹) (↑S : Set K))) := by
  intro E K _ _ _ _ S h0S
  classical
  have hT : ∀ t ∈ ((fun z : K => z⁻¹) '' (↑S : Set K)), ∃ z ∈ S, t = z⁻¹ := by
    rintro t ⟨z, hz, rfl⟩; exact ⟨z, hz, rfl⟩
  constructor
  · rintro ⟨C, hrank, hC⟩ h0
    by_cases hS : S = ∅
    · subst hS
      simp only [Finset.coe_empty, Set.image_empty, AffineSubspace.span_empty] at h0
      exact AffineSubspace.notMem_bot E K _ h0
    obtain ⟨z0, hz0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    have hr : Module.finrank E (LinearMap.range C) = Module.finrank E E := by
      rw [Module.finrank_self]
      rcases Nat.lt_or_ge (Module.finrank E (LinearMap.range C)) 1 with h | h
      · exfalso
        have h0r : Module.finrank E (LinearMap.range C) = 0 := by omega
        rw [Submodule.finrank_eq_zero] at h0r
        obtain ⟨x, hx, hCx⟩ := hC z0 hz0
        have : C x = 0 := by
          have := LinearMap.mem_range_self C x
          rw [h0r] at this
          simpa using this
        rw [this] at hCx
        exact mul_ne_zero (fun h => h0S (h ▸ hz0)) hx hCx.symm
      · omega
    let e := LinearEquiv.ofFinrankEq (LinearMap.range C) E hr
    let φ : K →ₗ[E] E := e.toLinearMap ∘ₗ C.rangeRestrict
    let v : K := (e.symm 1 : K)
    have hCφ : ∀ y, C y = φ y • v := by
      intro y
      have h1 : C.rangeRestrict y = e.symm (φ y) := by simp [φ]
      have h2 : e.symm (φ y) = φ y • e.symm 1 := by
        rw [← map_smul, smul_eq_mul, mul_one]
      have := congrArg Subtype.val (h1.trans h2)
      simpa [v] using this
    let ψ : K →ₗ[E] E := φ ∘ₗ LinearMap.mulRight E v
    have hψ : ∀ z ∈ S, ψ z⁻¹ = 1 := by
      intro z hz
      obtain ⟨x, hx, hCx⟩ := hC z hz
      have hz0 : z ≠ 0 := fun h => h0S (h ▸ hz)
      have hφx : φ x ≠ 0 := by
        intro h
        rw [hCφ, h, zero_smul] at hCx
        exact mul_ne_zero hz0 hx hCx.symm
      have hx' : x = φ x • (z⁻¹ * v) := by
        calc x = z⁻¹ * (z * x) := (inv_mul_cancel_left₀ hz0 x).symm
          _ = z⁻¹ * (φ x • v) := by rw [← hCx, hCφ]
          _ = φ x • (z⁻¹ * v) := mul_smul_comm _ _ _
      have : φ x = φ x * ψ z⁻¹ := by
        conv_lhs => rw [hx']
        rw [map_smul, smul_eq_mul]
        rfl
      have := mul_left_cancel₀ hφx (this.symm.trans (mul_one _).symm)
      exact this
    have hmap : ψ.toAffineMap 0 ∈ (affineSpan E ((fun z : K => z⁻¹) '' (↑S : Set K))).map ψ.toAffineMap :=
      AffineSubspace.mem_map.2 ⟨0, h0, rfl⟩
    rw [AffineSubspace.map_span] at hmap
    have hsub : ψ.toAffineMap '' ((fun z : K => z⁻¹) '' (↑S : Set K)) ⊆ {(1 : E)} := by
      rintro y ⟨t, ht, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hT t ht
      simp [hψ z hz]
    have := affineSpan_mono E hsub hmap
    rw [AffineSubspace.mem_affineSpan_singleton] at this
    simp at this
  · intro h0
    by_cases hS : S = ∅
    · subst hS
      refine ⟨0, by rw [LinearMap.range_zero, finrank_bot]; omega, fun z hz => absurd hz (Finset.notMem_empty z)⟩
    obtain ⟨z0, hz0⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    set A := affineSpan E ((fun z : K => z⁻¹) '' (↑S : Set K)) with hA
    have ht0 : z0⁻¹ ∈ A := subset_affineSpan E _ ⟨z0, hz0, rfl⟩
    have hnot : z0⁻¹ ∉ A.direction := by
      intro h
      apply h0
      rw [← AffineSubspace.vsub_right_mem_direction_iff_mem ht0 0]
      simpa using A.direction.neg_mem h
    obtain ⟨f, hf0, hfD⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    let ψ : K →ₗ[E] E := (f z0⁻¹)⁻¹ • f
    have hψ : ∀ z ∈ S, ψ z⁻¹ = 1 := by
      intro z hz
      have hd : z⁻¹ -ᵥ z0⁻¹ ∈ A.direction :=
        AffineSubspace.vsub_mem_direction (subset_affineSpan E _ ⟨z, hz, rfl⟩) ht0
      have : f (z⁻¹ -ᵥ z0⁻¹) = 0 := by
        have := Submodule.mem_map_of_mem (f := f) hd
        rw [hfD] at this
        exact (Submodule.mem_bot E).1 this
      rw [vsub_eq_sub, map_sub, sub_eq_zero] at this
      simp [ψ, this, inv_mul_cancel₀ hf0]
    refine ⟨ψ.smulRight (1 : K), ?_, ?_⟩
    · have hle : LinearMap.range (ψ.smulRight (1 : K)) ≤ Submodule.span E {(1 : K)} := by
        rintro y ⟨x, rfl⟩
        exact Submodule.mem_span_singleton.2 ⟨ψ x, rfl⟩
      exact (Submodule.finrank_mono hle).trans (finrank_span_le_card ({1} : Set K) |>.trans (by simp))
    · intro z hz
      refine ⟨z⁻¹, inv_ne_zero (fun h => h0S (h ▸ hz)), ?_⟩
      rw [LinearMap.smulRight_apply, hψ z hz, one_smul, mul_inv_cancel₀ (fun h => h0S (h ▸ hz))]
