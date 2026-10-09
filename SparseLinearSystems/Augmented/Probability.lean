import SparseLinearSystems.Augmented.Walk

/-!
# Fixed-space projection, seed probability and extracted amplitude

For a walk satisfying Lemma `qls:lem:walk` whose Hamiltonian has the
one-dimensional kernel `ℂ u₀`, the eigenvalue-one space of the walk is the line
through `v₀ = R₀ J u₀` (`fixedSpace_eq_span`).  Consequently, for every public
seed `e`,

* `seed_probability`: `‖P J e‖² = |⟪u₀, e⟫|² / (‖u₀‖² + ‖K J u₀‖²)`;
* `extracted_amplitude`: `J† P J e = (⟪u₀, e⟫ / (‖u₀‖² + ‖K J u₀‖²)) u₀`.

These are the identities behind equations `qls:eq:probability` and
`qls:eq:finalprob`; the augmented specialisation is in
`SparseLinearSystems.Augmented.Solution`.
-/

namespace SparseLinearSystems.WalkGap

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [FiniteDimensional ℂ P] [CompleteSpace P]
variable {J : P →L[ℂ] V} {K : V →L[ℂ] V} {H : P →L[ℂ] P} {α μ k₀ : ℝ}

omit [FiniteDimensional ℂ P] in
/-- The fixed space of the walk is the line through `R₀ J u₀`. -/
theorem Hyp.fixedSpace_eq_span (h : Hyp J K H α μ k₀) (u₀ : P) (hu₀ : H u₀ = 0)
    (hker : ∀ u, H u = 0 → ∃ c : ℂ, u = c • u₀) :
    UnitaryFilter.fixedSpace (walk J h.cayley) = ℂ ∙ resolvent K (J u₀) := by
  apply le_antisymm
  · intro v hv
    rw [UnitaryFilter.mem_fixedSpace] at hv
    obtain ⟨hHv, hrec⟩ := h.kernel_of_fixed v hv
    obtain ⟨c, hc⟩ := hker _ hHv
    rw [Submodule.mem_span_singleton]
    refine ⟨(2 : ℂ) * c, ?_⟩
    rw [← hrec, hc, smul_smul, map_smul, map_smul]
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      UnitaryFilter.mem_fixedSpace]
    exact h.fixed_lift u₀ hu₀

omit [FiniteDimensional ℂ P] in
/-- The orthogonal projection onto the fixed space, explicitly. -/
theorem Hyp.fixedProj_apply (h : Hyp J K H α μ k₀) (u₀ : P) (hu₀ : H u₀ = 0)
    (hker : ∀ u, H u = 0 → ∃ c : ℂ, u = c • u₀) (x : V) :
    UnitaryFilter.fixedProj (walk J h.cayley) x =
      (inner ℂ (resolvent K (J u₀)) x / ((‖resolvent K (J u₀)‖ ^ 2 : ℝ) : ℂ)) •
        resolvent K (J u₀) := by
  have hspan := h.fixedSpace_eq_span u₀ hu₀ hker
  show (UnitaryFilter.fixedSpace (walk J h.cayley)).starProjection x = _
  rw [hspan, Submodule.starProjection_singleton]
  rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
/-- `⟪R₀ J u₀, J e⟫ = ⟪u₀, e⟫ / 2` for a kernel vector `u₀`. -/
theorem Hyp.inner_lift (h : Hyp J K H α μ k₀) (u₀ : P) (hu₀ : H u₀ = 0) (e : P) :
    inner ℂ (resolvent K (J u₀)) (J e) = (2 : ℂ)⁻¹ * inner ℂ u₀ e := by
  rw [resolvent_apply, inner_smul_left, inner_add_left, inner_smul_left]
  have h1 : inner ℂ (J u₀) (J e) = inner ℂ u₀ e := by
    rw [← adjoint_inner_right, isometry_apply h.isometry]
  have h2 : inner ℂ (K (J u₀)) (J e) = 0 := by
    rw [← adjoint_inner_right, h.selfAdjoint, ← adjoint_inner_right J, h.compression_apply,
      inner_smul_right]
    have hH : inner ℂ u₀ (H e) = inner ℂ (H u₀) e := by
      rw [← adjoint_inner_right, h.hamiltonian_selfAdjoint]
    rw [hH, hu₀, inner_zero_left, mul_zero]
  rw [h1, h2, mul_zero, add_zero, map_inv₀, map_ofNat]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ P] in
/-- `‖R₀ J u₀‖² = (‖u₀‖² + ‖K J u₀‖²)/4` as a complex scalar. -/
theorem Hyp.lift_norm_sq_complex (h : Hyp J K H α μ k₀) (u₀ : P) :
    ((‖resolvent K (J u₀)‖ ^ 2 : ℝ) : ℂ) = (((‖u₀‖ ^ 2 + ‖K (J u₀)‖ ^ 2) / 4 : ℝ) : ℂ) := by
  rw [h.lift_norm_sq]

omit [FiniteDimensional ℂ P] in
/-- **Seed probability.** -/
theorem Hyp.seed_probability (h : Hyp J K H α μ k₀) (u₀ : P) (hu₀ : H u₀ = 0)
    (hker : ∀ u, H u = 0 → ∃ c : ℂ, u = c • u₀) (hne : u₀ ≠ 0) (e : P) :
    ‖UnitaryFilter.fixedProj (walk J h.cayley) (J e)‖ ^ 2 =
      ‖inner ℂ u₀ e‖ ^ 2 / (‖u₀‖ ^ 2 + ‖K (J u₀)‖ ^ 2) := by
  rw [h.fixedProj_apply u₀ hu₀ hker, h.inner_lift u₀ hu₀ e, norm_smul, mul_pow,
    norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    h.lift_norm_sq u₀]
  have hpos : 0 < ‖u₀‖ ^ 2 + ‖K (J u₀)‖ ^ 2 := by
    have : 0 < ‖u₀‖ := norm_pos_iff.mpr hne
    positivity
  have hn : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
  rw [hn]
  field_simp
  ring

omit [FiniteDimensional ℂ P] in
/-- **Extracted amplitude** `J† P J e`. -/
theorem Hyp.extracted_amplitude (h : Hyp J K H α μ k₀) (u₀ : P) (hu₀ : H u₀ = 0)
    (hker : ∀ u, H u = 0 → ∃ c : ℂ, u = c • u₀) (hne : u₀ ≠ 0) (e : P) :
    (J†) (UnitaryFilter.fixedProj (walk J h.cayley) (J e)) =
      (inner ℂ u₀ e / ((‖u₀‖ ^ 2 + ‖K (J u₀)‖ ^ 2 : ℝ) : ℂ)) • u₀ := by
  rw [h.fixedProj_apply u₀ hu₀ hker, map_smul, h.lift_adjoint u₀ hu₀, h.inner_lift u₀ hu₀ e,
    h.lift_norm_sq_complex u₀, smul_smul]
  congr 1
  have hpos : 0 < ‖u₀‖ ^ 2 + ‖K (J u₀)‖ ^ 2 := by
    have : 0 < ‖u₀‖ := norm_pos_iff.mpr hne
    positivity
  have hne' : ((‖u₀‖ ^ 2 + ‖K (J u₀)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp
  ring

end

end SparseLinearSystems.WalkGap
