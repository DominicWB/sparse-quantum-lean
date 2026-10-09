import TimeDependentODE.LCHS.GaussianContour

/-!
# Gaussian LCHS identity for an arbitrary contractive entire family

Let `F : ℂ → V →L[ℂ] V` be entire and contractive on the closed lower
half-plane. Finite rectangles, the scalar reciprocal-line limits and
Gaussian integrability identify the full-line operator integral:

  `∫ k, kernel w k • F k - F (-I) = ∫ k, (shifted-line integrand)`,

whose norm is at most `exp (1 - w)`. This gives

* `full_line_error`: `‖∫ k, kernel w k • F k - F (-I)‖ ≤ exp (1 - w)` for
  every `1 ≤ w`;
* `truncated_error`: at the public width `ODEGaussianParameters.width g ε`
  the integral truncated to `[-R, R]`, `R = ImprovedODEQueryBudget.radius g ε`,
  approximates `F (-I)` to the public precision
  `ImprovedODEQueryBudget.precision g ε`.

This is the generic version of `SparseODE.ODEGaussianFull` and of the
truncation bridge in `SparseODE.ODEGaussianFiniteTableContinuation2`, with the
complex-frequency propagator `ODEComplexFrequency.evolution D H u` replaced by
`F`; its value at the pole is kept as `F (-I)`. No contour identity or
approximation is assumed.
-/

namespace SparseHamiltonian.TimeDependentODE.GaussianLCHS

noncomputable section
open Filter MeasureTheory
open scoped Topology Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- The clockwise lower-half-plane orientation cancels the residue
coefficient, leaving exactly the value of the family at the pole. -/
theorem residue_normalization (F : ℂ → V →L[ℂ] V) (w : ℝ) :
    ((-2 : ℂ) * (Real.pi : ℂ) * Complex.I) • weightedRegular F w (-Complex.I) =
      F (-Complex.I) := by
  rw [weightedRegular_neg_I, smul_smul,
    ODEGaussianFull.residue_scalar_normalization, one_smul]

/-- The finite Gaussian contour differences converge to `F (-I)`. -/
theorem finite_difference_tendsto (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ =>
      (∫ k in (-R)..R, topWeighted F w k) -
        (∫ k in (-R)..R, shiftedWeighted F w k))
      atTop (𝓝 (F (-Complex.I))) := by
  have hwPos : 0 < w := by linarith
  have hEdges := horizontal_difference_tendsto_zero F hF hBound w hwPos
  have hPrincipal := ODEReciprocalLine.horizontal_difference_tendsto w hw
  have hConstant : Tendsto
      (fun _ : ℝ => weightedRegular F w (-Complex.I))
      atTop (𝓝 (weightedRegular F w (-Complex.I))) :=
    tendsto_const_nhds
  have hLimit := hEdges.add (hPrincipal.smul hConstant)
  have hEq : (fun R : ℝ =>
      (∫ k in (-R)..R, topWeighted F w k) -
        (∫ k in (-R)..R, shiftedWeighted F w k)) =
      (fun R : ℝ =>
        (ODEContourRectangle.horizontal
            (dslope (weightedRegular F w) (-Complex.I)) (-R) R 0 -
          ODEContourRectangle.horizontal
            (dslope (weightedRegular F w) (-Complex.I)) (-R) R (-2 * w)) +
        ((∫ k in (-R)..R, ODEReciprocalLine.reciprocal 1 k) -
          (∫ k in (-R)..R, ODEReciprocalLine.reciprocal (1 - 2 * w) k)) •
          weightedRegular F w (-Complex.I)) := by
    funext R
    exact horizontal_difference F hF w R hw
  rw [hEq]
  simpa only [zero_add, residue_normalization] using hLimit

/-- Uniqueness of the operator-valued limit gives the full-line Gaussian
identity, including its explicit shifted residual. -/
theorem integral_difference_eq (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    (∫ k : ℝ, topWeighted F w k) - (∫ k : ℝ, shiftedWeighted F w k) =
      F (-Complex.I) :=
  tendsto_nhds_unique (integral_difference_tendsto F hF hBound w hw)
    (finite_difference_tendsto F hF hBound w hw)

/-- The error of the full real-frequency integral is exactly the shifted
Gaussian integral. -/
theorem full_line_error_eq_residual (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    (∫ k : ℝ, ODEGaussianKernel.kernel w k • F (k : ℂ)) - F (-Complex.I) =
      ∫ k : ℝ, shiftedWeighted F w k := by
  rw [← integral_difference_eq F hF hBound w hw]
  exact sub_sub_cancel _ _

/-- Full-line Gaussian LCHS error for an arbitrary entire operator family
that is contractive on the closed lower half-plane. -/
theorem full_line_error (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 1 ≤ w) :
    ‖(∫ k : ℝ, ODEGaussianKernel.kernel w k • F (k : ℂ)) - F (-Complex.I)‖ ≤
      Real.exp (1 - w) := by
  rw [full_line_error_eq_residual F hF hBound w hw]
  exact shifted_integral_norm_le F hBound w hw

/-- Truncating the frequency integral to the public radius costs only the
proved scalar tail; together with the full-line error this is exactly the
public precision budget. -/
theorem truncated_error (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (g ε : ℝ)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ‖(∫ k in (-ImprovedODEQueryBudget.radius g ε)..(ImprovedODEQueryBudget.radius g ε),
        ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F (k : ℂ)) -
      F (-Complex.I)‖ ≤ ImprovedODEQueryBudget.precision g ε := by
  have hTruncated := ODEGaussianIntegral.truncated_error_of_full
    (ODEGaussianParameters.width g ε) (ImprovedODEQueryBudget.radius g ε)
    (Real.exp (1 - ODEGaussianParameters.width g ε))
    (ODEGaussianParameters.width_ge_two g ε hg hε hεOne)
    (ODEGaussianParameters.cutoff_le_radius g ε hg hε hεOne)
    (fun k : ℝ => F (k : ℂ)) (real_continuous F hF) (real_norm_le_one F hBound)
    (F (-Complex.I))
    (full_line_error F hF hBound (ODEGaussianParameters.width g ε)
      (ODEGaussianParameters.width_ge_one g ε hg hε hεOne))
  rw [ODEGaussianParameters.integral_error_budget g ε hg hε] at hTruncated
  exact hTruncated

end
end SparseHamiltonian.TimeDependentODE.GaussianLCHS
