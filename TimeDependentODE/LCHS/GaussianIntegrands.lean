import SparseODE.ODEGaussianFull

/-!
# Gaussian LCHS integrands for a generic contractive entire family

Throughout, `F : ℂ → V →L[ℂ] V` is an entire operator-valued function
(`∀ z, AnalyticAt ℂ F z`) which is a contraction on the closed lower
half-plane (`z.im ≤ 0 → ‖F z‖ ≤ 1`). This replaces the specific
complex-frequency propagator `ODEComplexFrequency.evolution D H u` of the
released Gaussian LCHS chain.

This file proves the regularity and norm estimates of the contour integrands:

* the real-frequency integrand `k ↦ kernel w k • F k` is continuous and
  Bochner integrable (`integrand_continuous`, `integrand_integrable`);
* on the downward-shifted line `Im z = -2 w` the meromorphic Gaussian density
  times `F` is continuous and integrable, and its whole-line integral has
  norm at most `exp (1 - w)` (`shifted_integral_norm_le`);
* on the vertical edges of the contour rectangle the weighted family obeys
  the quadratic decay bound of the scalar kernel (`vertical_weighted_norm_le`).

These are generic copies of the operator-valued parts of
`SparseODE.ODEGaussianLimits`, `SparseODE.ODEGaussianShiftedIntegral` and
`SparseODE.ODEGaussianVertical`; all scalar estimates are reused directly.
-/

namespace SparseHamiltonian.TimeDependentODE.GaussianLCHS

noncomputable section
open MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

section Regularity

/-- An everywhere analytic family is complex differentiable. -/
theorem differentiable_of_analyticAt (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) : Differentiable ℂ F :=
  fun z => (hF z).differentiableAt

/-- An everywhere analytic family is continuous on the whole plane. -/
theorem continuous_of_analyticAt (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) : Continuous F :=
  (differentiable_of_analyticAt F hF).continuous

/-- Restriction of the family to the real frequency axis is continuous. -/
theorem real_continuous (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z) :
    Continuous (fun k : ℝ => F (k : ℂ)) :=
  (continuous_of_analyticAt F hF).comp Complex.continuous_ofReal

/-- The real axis lies in the closed lower half-plane, so the family is
contractive there. -/
theorem real_norm_le_one (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (k : ℝ) :
    ‖F (k : ℂ)‖ ≤ 1 :=
  hBound _ (by simp)

/-- Every downward horizontal translate of the real axis obeys the same bound. -/
theorem shifted_norm_le_one (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (k r : ℝ) (hr : 0 ≤ r) :
    ‖F ((k : ℂ) - (r : ℂ) * Complex.I)‖ ≤ 1 :=
  hBound _ (by simpa using neg_nonpos.mpr hr)

end Regularity

section RealLine

/-- The real-frequency Gaussian integrand of the generic family; this is the
upper side of the contour rectangle. -/
def topWeighted (F : ℂ → V →L[ℂ] V) (w k : ℝ) : V →L[ℂ] V :=
  ODEGaussianKernel.kernel w k • F (k : ℂ)

/-- The real-frequency integrand is continuous for every width. -/
theorem integrand_continuous (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (w : ℝ) :
    Continuous (fun k : ℝ => ODEGaussianKernel.kernel w k • F (k : ℂ)) :=
  (ODEGaussianKernel.kernel_continuous w).smul (real_continuous F hF)

/-- Contractivity on the real axis and the integrable scalar Gaussian envelope
make the real-frequency integrand Bochner integrable. -/
theorem integrand_integrable (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 0 < w) :
    Integrable (fun k : ℝ => ODEGaussianKernel.kernel w k • F (k : ℂ)) :=
  ODEGaussianIntegral.weighted_integrable w hw (fun k : ℝ => F (k : ℂ))
    (real_continuous F hF) (real_norm_le_one F hBound)

/-- The same integrability statement at the public widths `1 ≤ w`. -/
theorem integrand_integrable_of_one_le (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    Integrable (fun k : ℝ => ODEGaussianKernel.kernel w k • F (k : ℂ)) :=
  integrand_integrable F hF hBound w (by linarith)

theorem topWeighted_continuous (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (w : ℝ) : Continuous (topWeighted F w) :=
  integrand_continuous F hF w

theorem top_integrable (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 0 < w) :
    Integrable (topWeighted F w) :=
  integrand_integrable F hF hBound w hw

end RealLine

section ShiftedLine

/-- Gaussian-weighted family on the downward horizontal line `Im z = -2 w`;
this is the lower side of the contour rectangle. -/
def shiftedWeighted (F : ℂ → V →L[ℂ] V) (w k : ℝ) : V →L[ℂ] V :=
  ODEGaussianComplex.kernel w ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) •
    F ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)

/-- The shifted weighted family has no singularities on its line. -/
theorem shiftedWeighted_continuous (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w : ℝ) (hw : 1 ≤ w) :
    Continuous (shiftedWeighted F w) := by
  have hLine : Continuous
      (fun k : ℝ => (k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.sub continuous_const
  exact (ODEGaussianComplex.shifted_kernel_continuous w hw).smul
    ((continuous_of_analyticAt F hF).comp hLine)

/-- The scalar shifted-line Cauchy envelope also bounds the operator integrand. -/
theorem shiftedWeighted_norm_le (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 1 ≤ w) (k : ℝ) :
    ‖shiftedWeighted F w k‖ ≤ Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
  have hShift : 0 ≤ 2 * w := by linarith
  have hContraction := shifted_norm_le_one F hBound k (2 * w) hShift
  calc
    _ = ‖ODEGaussianComplex.kernel w
          ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ *
        ‖F ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ := norm_smul _ _
    _ ≤ ‖ODEGaussianComplex.kernel w
        ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ * 1 :=
      mul_le_mul_of_nonneg_left hContraction (norm_nonneg _)
    _ ≤ Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
      rw [mul_one]
      exact ODEGaussianComplex.shifted_kernel_norm_le w k hw

/-- The shifted contour residual is a genuine Bochner integral. -/
theorem shiftedWeighted_integrable (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    Integrable (shiftedWeighted F w) := by
  apply (ODEGaussianTail.integrable_cauchy (Real.exp (1 - w))).mono'
    (shiftedWeighted_continuous F hF w hw).aestronglyMeasurable
  exact Filter.Eventually.of_forall (shiftedWeighted_norm_le F hBound w hw)

/-- The entire shifted contour has operator norm at most `exp (1 - w)`. -/
theorem shifted_integral_norm_le (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 1 ≤ w) :
    ‖∫ k : ℝ, shiftedWeighted F w k‖ ≤ Real.exp (1 - w) := by
  calc
    _ ≤ ∫ k : ℝ, Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le
        (ODEGaussianTail.integrable_cauchy (Real.exp (1 - w)))
      exact Filter.Eventually.of_forall (shiftedWeighted_norm_le F hBound w hw)
    _ = Real.exp (1 - w) := ODEGaussianTail.cauchy_integral_univ _

end ShiftedLine

section Vertical

/-- Lower-half-plane contractivity preserves the scalar vertical-edge bound
after multiplication by the operator family. -/
theorem vertical_weighted_norm_le (F : ℂ → V →L[ℂ] V)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w x y : ℝ) (hw : 0 < w)
    (hx : x ≠ 0) (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I) •
        F ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 / (Real.pi * x ^ 2) := by
  have hContraction := hBound ((x : ℂ) + (y : ℂ) * Complex.I)
    (by simpa using hUpper)
  rw [norm_smul]
  calc
    _ ≤ ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I)‖ * 1 :=
      mul_le_mul_of_nonneg_left hContraction (norm_nonneg _)
    _ = ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I)‖ :=
      mul_one _
    _ ≤ _ := ODEGaussianVertical.kernel_norm_le w x y hw hx hLower hUpper

end Vertical

end
end SparseHamiltonian.TimeDependentODE.GaussianLCHS
