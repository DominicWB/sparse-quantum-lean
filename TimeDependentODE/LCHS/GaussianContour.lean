import TimeDependentODE.LCHS.GaussianResidue

/-!
# Finite Gaussian contour decomposition and whole-line limits

For an entire operator-valued `F` that is contractive on the closed lower
half-plane, this file proves:

* every finite horizontal integral of `kernel w z • F z` on a line avoiding
  both poles splits into the removed-pole integral and the scalar
  reciprocal-line integral times the residue coefficient
  (`horizontal_decomposition`); in particular the top-minus-bottom difference
  of the two contour sides at every finite cutoff `R` has an exact formula
  (`horizontal_difference`);
* both horizontal integrands are Bochner integrable, so their symmetric
  finite integrals converge to the whole-line integrals
  (`integral_difference_tendsto`).

These are generic copies of the operator-valued parts of
`SparseODE.ODEGaussianFiniteContour` and `SparseODE.ODEGaussianLimits`.
The principal part is only ever integrated over finite intervals.
-/

namespace SparseHamiltonian.TimeDependentODE.GaussianLCHS

noncomputable section
open Filter MeasureTheory
open scoped Topology Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

section FiniteContour

/-- The removed-pole integrand is continuous along every line below the
upper pole. -/
theorem regularized_line_continuous (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w y : ℝ) (hy : y < 1) :
    Continuous (fun k : ℝ =>
      dslope (weightedRegular F w) (-Complex.I)
        ((k : ℂ) + (y : ℂ) * Complex.I)) := by
  have hLine : Continuous (fun k : ℝ => (k : ℂ) + (y : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  exact (regularized_differentiableOn F hF w).continuousOn.comp_continuous
    hLine (fun k => by simpa using hy)

omit [CompleteSpace V] in
/-- Pointwise decomposition of the weighted family on a horizontal line. -/
theorem line_decomposition (F : ℂ → V →L[ℂ] V) (w y k : ℝ) (hy : y ≠ -1) :
    ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        F ((k : ℂ) + (y : ℂ) * Complex.I) =
      dslope (weightedRegular F w) (-Complex.I)
        ((k : ℂ) + (y : ℂ) * Complex.I) +
      ODEReciprocalLine.reciprocal (1 + y) k •
        weightedRegular F w (-Complex.I) := by
  rw [weighted_eq_poleQuotient,
    ODEContourRectangle.pole_decomposition _ _ _
      (ODEGaussianFiniteContour.line_ne_neg_I y k hy)]
  simp only [ODEContourRectangle.principalPart,
    ODEGaussianFiniteContour.line_sub_pole, ODEReciprocalLine.reciprocal]

/-- Exact finite horizontal decomposition, with the residue coefficient pulled
outside the integral after establishing interval integrability. -/
theorem horizontal_decomposition (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (w y a b : ℝ)
    (hyUpper : y < 1) (hyLower : y ≠ -1) :
    (∫ k in a..b, ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        F ((k : ℂ) + (y : ℂ) * Complex.I)) =
      ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) a b y +
      (∫ k in a..b, ODEReciprocalLine.reciprocal (1 + y) k) •
        weightedRegular F w (-Complex.I) := by
  have hNonzero : 1 + y ≠ 0 := by
    intro h
    apply hyLower
    linarith
  have hG := (regularized_line_continuous F hF w y hyUpper).intervalIntegrable
    (μ := volume) a b
  have hP : IntervalIntegrable (fun k : ℝ =>
      ODEReciprocalLine.reciprocal (1 + y) k •
        weightedRegular F w (-Complex.I)) volume a b :=
    ((ODEReciprocalLine.reciprocal_continuous (1 + y) hNonzero).smul
      (continuous_const : Continuous (fun _ : ℝ =>
        weightedRegular F w (-Complex.I)))).intervalIntegrable a b
  calc
    _ = ∫ k in a..b,
        dslope (weightedRegular F w) (-Complex.I)
          ((k : ℂ) + (y : ℂ) * Complex.I) +
        ODEReciprocalLine.reciprocal (1 + y) k •
          weightedRegular F w (-Complex.I) := by
      apply intervalIntegral.integral_congr
      intro k _
      exact line_decomposition F w y k hyLower
    _ = _ := by
      rw [intervalIntegral.integral_add hG hP, intervalIntegral.integral_smul_const]
      rfl

/-- The upper horizontal side is exactly the real-frequency integrand. -/
theorem top_decomposition (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (w R : ℝ) :
    (∫ k in (-R)..R, topWeighted F w k) =
      ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) (-R) R 0 +
      (∫ k in (-R)..R, ODEReciprocalLine.reciprocal 1 k) •
        weightedRegular F w (-Complex.I) := by
  have h := horizontal_decomposition F hF w 0 (-R) R (by norm_num) (by norm_num)
  simpa only [Complex.ofReal_zero, zero_mul, add_zero,
    ODEGaussianComplex.kernel_ofReal, topWeighted] using h

/-- The lower horizontal side is exactly the integrable shifted residual. -/
theorem shifted_decomposition (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (w R : ℝ) (hw : 1 ≤ w) :
    (∫ k in (-R)..R, shiftedWeighted F w k) =
      ODEContourRectangle.horizontal
        (dslope (weightedRegular F w) (-Complex.I)) (-R) R (-2 * w) +
      (∫ k in (-R)..R, ODEReciprocalLine.reciprocal (1 - 2 * w) k) •
        weightedRegular F w (-Complex.I) := by
  have h := horizontal_decomposition F hF w (-2 * w) (-R) R
    (by linarith) (by linarith)
  have hLine (k : ℝ) : (k : ℂ) + ((-2 * w : ℝ) : ℂ) * Complex.I =
      (k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  have hCoefficient : 1 + (-2 * w) = 1 - 2 * w := by ring
  simpa only [hLine, hCoefficient, shiftedWeighted] using h

/-- At every finite symmetric cutoff, the top-minus-bottom integral splits
into the regularized difference and the scalar principal-part difference. -/
theorem horizontal_difference (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (w R : ℝ) (hw : 1 ≤ w) :
    (∫ k in (-R)..R, topWeighted F w k) -
        (∫ k in (-R)..R, shiftedWeighted F w k) =
      (ODEContourRectangle.horizontal
          (dslope (weightedRegular F w) (-Complex.I)) (-R) R 0 -
        ODEContourRectangle.horizontal
          (dslope (weightedRegular F w) (-Complex.I)) (-R) R (-2 * w)) +
      ((∫ k in (-R)..R, ODEReciprocalLine.reciprocal 1 k) -
        (∫ k in (-R)..R, ODEReciprocalLine.reciprocal (1 - 2 * w) k)) •
        weightedRegular F w (-Complex.I) := by
  rw [top_decomposition F hF w R, shifted_decomposition F hF w R hw, sub_smul]
  abel

end FiniteContour

section Limits

omit [CompleteSpace V] in
/-- The upper contour integrals over `[-R, R]` converge to the whole-line
Bochner integral. -/
theorem top_integral_tendsto (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) (w : ℝ) (hw : 0 < w) :
    Tendsto (fun R : ℝ => ∫ k in (-R)..R, topWeighted F w k)
      atTop (𝓝 (∫ k : ℝ, topWeighted F w k)) :=
  ODEGaussianLimits.symmetric_integral_tendsto _ (top_integrable F hF hBound w hw)

omit [CompleteSpace V] in
/-- The shifted lower contour integrals converge likewise. -/
theorem shifted_integral_tendsto (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ => ∫ k in (-R)..R, shiftedWeighted F w k)
      atTop (𝓝 (∫ k : ℝ, shiftedWeighted F w k)) :=
  ODEGaussianLimits.symmetric_integral_tendsto _
    (shiftedWeighted_integrable F hF hBound w hw)

omit [CompleteSpace V] in
/-- The difference of the two finite horizontal integrals converges to the
difference of their whole-line Bochner integrals. -/
theorem integral_difference_tendsto (F : ℂ → V →L[ℂ] V)
    (hF : ∀ z, AnalyticAt ℂ F z) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) :
    Tendsto (fun R : ℝ =>
      (∫ k in (-R)..R, topWeighted F w k) -
        (∫ k in (-R)..R, shiftedWeighted F w k))
      atTop (𝓝 ((∫ k : ℝ, topWeighted F w k) -
        (∫ k : ℝ, shiftedWeighted F w k))) := by
  have hwPos : 0 < w := by linarith
  exact (top_integral_tendsto F hF hBound w hwPos).sub
    (shifted_integral_tendsto F hF hBound w hw)

end Limits

end
end SparseHamiltonian.TimeDependentODE.GaussianLCHS
