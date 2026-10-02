import SparseODE.ODEGaussianTail

/-!
# Whole-line Gaussian operator integrals and frequency truncation

The integrability of each weighted operator family is derived from the
scalar kernel and contractivity.  The discarded frequency range has a
uniform operator-norm bound, independent of duration and matrix dimension.
This section does not assert the continuous LCHS approximation to the ODE
propagator; that separate analytic obligation is kept explicit.

-/

namespace SparseHamiltonian.ODEGaussianIntegral

noncomputable section
open MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A contractive family cannot increase the scalar kernel norm. -/
theorem weighted_norm_le (w : ℝ) (U : ℝ → E)
    (hNorm : ∀ k, ‖U k‖ ≤ 1) (k : ℝ) :
    ‖ODEGaussianKernel.kernel w k • U k‖ ≤ ‖ODEGaussianKernel.kernel w k‖ := by
  rw [norm_smul]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hNorm k) (norm_nonneg (ODEGaussianKernel.kernel w k))

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- No separate integrability promise is needed for a continuous contractive
operator family weighted by the Gaussian kernel. -/
theorem weighted_integrable (w : ℝ) (hw : 0 < w) (U : ℝ → E)
    (hU : Continuous U) (hNorm : ∀ k, ‖U k‖ ≤ 1) :
    Integrable (fun k => ODEGaussianKernel.kernel w k • U k) := by
  apply (ODEGaussianTail.integrable_norm_kernel w hw).mono'
    ((ODEGaussianKernel.kernel_continuous w).smul hU).aestronglyMeasurable
  exact Filter.Eventually.of_forall (weighted_norm_le w U hNorm)

omit [CompleteSpace E] in
/-- The full-minus-truncated operator integral is bounded by the actual scalar
mass on the complement of the truncation interval. -/
theorem truncation_error_le_tail (w R : ℝ) (hw : 0 < w) (hR : 0 ≤ R)
    (U : ℝ → E) (hU : Continuous U) (hNorm : ∀ k, ‖U k‖ ≤ 1) :
    ‖(∫ k : ℝ, ODEGaussianKernel.kernel w k • U k) -
        (∫ k in (-R)..R, ODEGaussianKernel.kernel w k • U k)‖ ≤
      ∫ k in (Set.Ioc (-R) R)ᶜ, ‖ODEGaussianKernel.kernel w k‖ := by
  have hInt := weighted_integrable w hw U hU hNorm
  have hOrder : -R ≤ R := by linarith
  have hEq : (∫ k : ℝ, ODEGaussianKernel.kernel w k • U k) -
      (∫ k in (-R)..R, ODEGaussianKernel.kernel w k • U k) =
        ∫ k in (Set.Ioc (-R) R)ᶜ, ODEGaussianKernel.kernel w k • U k := by
    rw [intervalIntegral.integral_of_le hOrder]
    exact (MeasureTheory.setIntegral_compl measurableSet_Ioc hInt).symm
  rw [hEq]
  apply MeasureTheory.norm_integral_le_of_norm_le
    (ODEGaussianTail.integrable_norm_kernel w hw).integrableOn
  exact Filter.Eventually.of_forall (weighted_norm_le w U hNorm)

omit [CompleteSpace E] in
/-- At the Gaussian cutoff, the discarded operator integral is at most the
sharp scalar tail allocation `exp (1-w)/(2*pi)`. -/
theorem truncation_error (w R : ℝ) (hw : 2 ≤ w) (hR : 2 * w ≤ R)
    (U : ℝ → E) (hU : Continuous U) (hNorm : ∀ k, ‖U k‖ ≤ 1) :
    ‖(∫ k : ℝ, ODEGaussianKernel.kernel w k • U k) -
        (∫ k in (-R)..R, ODEGaussianKernel.kernel w k • U k)‖ ≤
      Real.exp (1 - w) / (2 * Real.pi) := by
  have hwPos : 0 < w := by linarith
  have hRNonneg : 0 ≤ R := by linarith
  exact (truncation_error_le_tail w R hwPos hRNonneg U hU hNorm).trans
    (ODEGaussianTail.exterior_mass_bound w R hw hR)

omit [CompleteSpace E] in
/-- A proved full-line approximation loses only the explicit scalar tail when
passed to the finite frequency interval. -/
theorem truncated_error_of_full (w R η : ℝ) (hw : 2 ≤ w) (hR : 2 * w ≤ R)
    (U : ℝ → E) (hU : Continuous U) (hNorm : ∀ k, ‖U k‖ ≤ 1) (Y : E)
    (hFull : ‖(∫ k : ℝ, ODEGaussianKernel.kernel w k • U k) - Y‖ ≤ η) :
    ‖(∫ k in (-R)..R, ODEGaussianKernel.kernel w k • U k) - Y‖ ≤
      Real.exp (1 - w) / (2 * Real.pi) + η := by
  have hTail := truncation_error w R hw hR U hU hNorm
  calc
    _ ≤ ‖(∫ k in (-R)..R, ODEGaussianKernel.kernel w k • U k) -
          (∫ k : ℝ, ODEGaussianKernel.kernel w k • U k)‖ +
        ‖(∫ k : ℝ, ODEGaussianKernel.kernel w k • U k) - Y‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Real.exp (1 - w) / (2 * Real.pi) + η := by
      apply add_le_add _ hFull
      simpa only [norm_sub_rev] using hTail

section Native

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Every exact native LCHS branch has a genuine whole-line Bochner integral. -/
theorem native_weighted_integrable
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (u w : ℝ) (hw : 0 < w) :
    Integrable (ODEWeightedLCHS.nativeWeighted D x u (ODEGaussianKernel.kernel w)) := by
  exact weighted_integrable w hw (ODEWeightedLCHS.nativeEvolution D x u)
    (ODEWeightedLCHS.native_evolution_continuous D x u)
    (ODEWeightedLCHS.native_evolution_norm_le_one D x u)

/-- Frequency truncation is uniform in the actual input matrix and time. -/
theorem native_truncation_error
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (u w R : ℝ)
    (hw : 2 ≤ w) (hR : 2 * w ≤ R) :
    ‖(∫ k : ℝ, ODEWeightedLCHS.nativeWeighted D x u
          (ODEGaussianKernel.kernel w) k) -
        (∫ k in (-R)..R, ODEWeightedLCHS.nativeWeighted D x u
          (ODEGaussianKernel.kernel w) k)‖ ≤ Real.exp (1 - w) / (2 * Real.pi) := by
  exact truncation_error w R hw hR (ODEWeightedLCHS.nativeEvolution D x u)
    (ODEWeightedLCHS.native_evolution_continuous D x u)
    (ODEWeightedLCHS.native_evolution_norm_le_one D x u)

/-- This bridge isolates precisely the continuous approximation that remains
to be proved for the ODE propagator. Integrability and truncation are derived. -/
theorem native_truncated_error_of_full
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (u w R η : ℝ)
    (hw : 2 ≤ w) (hR : 2 * w ≤ R)
    (hFull : ‖(∫ k : ℝ, ODEWeightedLCHS.nativeWeighted D x u
          (ODEGaussianKernel.kernel w) k) -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤ η) :
    ‖(∫ k in (-R)..R, ODEWeightedLCHS.nativeWeighted D x u
          (ODEGaussianKernel.kernel w) k) -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
      Real.exp (1 - w) / (2 * Real.pi) + η := by
  exact truncated_error_of_full w R η hw hR (ODEWeightedLCHS.nativeEvolution D x u)
    (ODEWeightedLCHS.native_evolution_continuous D x u)
    (ODEWeightedLCHS.native_evolution_norm_le_one D x u)
    (NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)) hFull

end Native
end
end SparseHamiltonian.ODEGaussianIntegral
