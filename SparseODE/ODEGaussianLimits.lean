import SparseODE.ODEReciprocalLineContinuation2

/-!
# Whole-line limits of the two Gaussian contour sides

Both horizontal integrands are genuinely Bochner integrable.  Their finite
symmetric integrals therefore converge to the whole-line integrals.  The
upper side needs only self-adjointness; the lower side additionally uses
positivity of the dissipative part and nonnegative duration.

Requires Mathlib.MeasureTheory.Integral.IntegralEqImproper.
-/

namespace SparseHamiltonian.ODEGaussianLimits

noncomputable section
open Filter MeasureTheory
open scoped Interval Topology InnerProduct

/-- Symmetric finite intervals exhaust a genuinely integrable function on
the real line; no principal-value interpretation is used here. -/
theorem symmetric_integral_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (hf : Integrable f) :
    Tendsto (fun R : ℝ => ∫ k in (-R)..R, f k) atTop (nhds (∫ k : ℝ, f k)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral hf
    (Filter.tendsto_neg_atTop_atBot : Tendsto (fun R : ℝ => -R) atTop atBot)
    (Filter.tendsto_id : Tendsto (fun R : ℝ => R) atTop atTop)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Actual real-frequency Gaussian integrand on the upper contour side. -/
def topWeighted (D H : V →L[ℂ] V) (u w k : ℝ) : V →L[ℂ] V :=
  ODEGaussianKernel.kernel w k • ODEWeightedLCHS.evolution D H u k

omit [CompleteSpace V] in
/-- The real-frequency integrand agrees with the meromorphic family on
the real axis, including its operator exponential. -/
theorem topWeighted_eq_complex (D H : V →L[ℂ] V) (u w k : ℝ) :
    topWeighted D H u w k =
      ODEGaussianComplex.kernel w (k : ℂ) •
        ODEComplexFrequency.evolution D H u (k : ℂ) := by
  rw [ODEGaussianComplex.kernel_ofReal, ODEComplexFrequency.evolution_ofReal] ; rfl

/-- Continuity of the upper integrand, with no positivity assumption. -/
theorem topWeighted_continuous (D H : V →L[ℂ] V) (u w : ℝ) :
    Continuous (topWeighted D H u w) :=
  (ODEGaussianKernel.kernel_continuous w).smul
    (ODEWeightedLCHS.evolution_continuous D H u)

/-- Self-adjointness makes each real-frequency evolution contractive, so
the scalar Gaussian envelope proves upper-side Bochner integrability. -/
theorem top_integrable (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (u w : ℝ) (hw : 0 < w) :
    Integrable (topWeighted D H u w) := by
  exact ODEGaussianIntegral.weighted_integrable w hw
    (ODEWeightedLCHS.evolution D H u)
    (ODEWeightedLCHS.evolution_continuous D H u)
    (ODEWeightedLCHS.evolution_norm_le_one D H hD hH u)

/-- The actual upper contour integrals converge as their width grows. -/
theorem top_integral_tendsto (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (u w : ℝ) (hw : 0 < w) :
    Tendsto (fun R : ℝ => ∫ k in (-R)..R, topWeighted D H u w k)
      atTop (nhds (∫ k : ℝ, topWeighted D H u w k)) :=
  symmetric_integral_tendsto _ (top_integrable D H hD hH u w hw)

/-- The shifted lower contour integrals converge using the already proved
contractive Cauchy envelope on the entire shifted line. -/
theorem shifted_integral_tendsto (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ => ∫ k in (-R)..R,
      ODEGaussianShiftedIntegral.weighted D H u w k)
      atTop (nhds (∫ k : ℝ, ODEGaussianShiftedIntegral.weighted D H u w k)) :=
  symmetric_integral_tendsto _
    (ODEGaussianShiftedIntegral.weighted_integrable D H hD hH hPSD u w hu hw)

/-- The difference of the two finite horizontal integrals converges to the
difference of their whole-line Bochner integrals. -/
theorem horizontal_difference_tendsto (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u w : ℝ) (hu : 0 ≤ u) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ =>
      (∫ k in (-R)..R, topWeighted D H u w k) -
        (∫ k in (-R)..R, ODEGaussianShiftedIntegral.weighted D H u w k))
      atTop (nhds ((∫ k : ℝ, topWeighted D H u w k) -
        (∫ k : ℝ, ODEGaussianShiftedIntegral.weighted D H u w k))) := by
  have hwPos : 0 < w := by linarith
  exact (top_integral_tendsto D H hD hH u w hwPos).sub
    (shifted_integral_tendsto D H hD hH hPSD u w hu hw)

end
end SparseHamiltonian.ODEGaussianLimits
