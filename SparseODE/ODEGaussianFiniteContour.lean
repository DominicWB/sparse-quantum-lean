import SparseODE.ODEGaussianEdges

/-!
# Finite horizontal Gaussian contour decomposition

Every finite horizontal integral is split into the removable divided
difference and its scalar principal part. All continuity and interval
integrability requirements follow from the established holomorphy and the
absence of poles on the two horizontal lines. The principal part is used
only on finite intervals; no whole-line integrability is asserted for it.

-/

namespace SparseHamiltonian.ODEGaussianFiniteContour

noncomputable section
open MeasureTheory
open scoped Interval

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- A horizontal line at height different from minus one avoids the lower pole. -/
theorem line_ne_neg_I (y k : ℝ) (hy : y ≠ -1) :
    (k : ℂ) + (y : ℂ) * Complex.I ≠ -Complex.I := by
  intro h
  apply hy
  have hi := congrArg Complex.im h
  simpa using hi

/-- Translate the lower-pole denominator to the scalar reciprocal-line form. -/
theorem line_sub_pole (y k : ℝ) :
    ((k : ℂ) + (y : ℂ) * Complex.I) - (-Complex.I) =
      (k : ℂ) + ((1 + y : ℝ) : ℂ) * Complex.I := by
  simp only [Complex.ofReal_add, Complex.ofReal_one]
  ring

/-- The removed-pole integrand is continuous along every line below the upper pole. -/
theorem regularized_line_continuous (D H : V →L[ℂ] V) (u w y : ℝ)
    (hy : y < 1) :
    Continuous (fun k : ℝ =>
      dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)
        ((k : ℂ) + (y : ℂ) * Complex.I)) := by
  have hLine : Continuous (fun k : ℝ => (k : ℂ) + (y : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.add continuous_const
  exact (ODEGaussianResidue.regularized_differentiableOn D H u w).continuousOn.comp_continuous
    hLine (fun k => by simpa using hy)

omit [CompleteSpace V] in
/-- Pointwise decomposition of the actual weighted propagator on a horizontal line. -/
theorem line_decomposition (D H : V →L[ℂ] V) (u w y k : ℝ)
    (hy : y ≠ -1) :
    ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        ODEComplexFrequency.evolution D H u ((k : ℂ) + (y : ℂ) * Complex.I) =
      dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)
        ((k : ℂ) + (y : ℂ) * Complex.I) +
      ODEReciprocalLine.reciprocal (1 + y) k •
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) := by
  rw [ODEGaussianResidue.weighted_eq_poleQuotient,
    ODEContourRectangle.pole_decomposition _ _ _ (line_ne_neg_I y k hy)]
  simp only [ODEContourRectangle.principalPart, line_sub_pole,
    ODEReciprocalLine.reciprocal]

/-- The actual horizontal Gaussian family is continuous when both poles are avoided. -/
theorem weighted_line_continuous (D H : V →L[ℂ] V) (u w y : ℝ)
    (hyUpper : y < 1) (hyLower : y ≠ -1) :
    Continuous (fun k : ℝ =>
      ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        ODEComplexFrequency.evolution D H u ((k : ℂ) + (y : ℂ) * Complex.I)) := by
  have hNonzero : 1 + y ≠ 0 := by
    intro h
    apply hyLower
    linarith
  have hEq :
      (fun k : ℝ => ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        ODEComplexFrequency.evolution D H u ((k : ℂ) + (y : ℂ) * Complex.I)) =
      (fun k : ℝ => dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)
        ((k : ℂ) + (y : ℂ) * Complex.I) +
        ODEReciprocalLine.reciprocal (1 + y) k •
          ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)) := by
    funext k
    exact line_decomposition D H u w y k hyLower
  rw [hEq]
  exact (regularized_line_continuous D H u w y hyUpper).add
    ((ODEReciprocalLine.reciprocal_continuous (1 + y) hNonzero).smul continuous_const)

/-- In particular, every finite horizontal Gaussian integral is well defined. -/
theorem weighted_line_intervalIntegrable (D H : V →L[ℂ] V) (u w y a b : ℝ)
    (hyUpper : y < 1) (hyLower : y ≠ -1) :
    IntervalIntegrable (fun k : ℝ =>
      ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        ODEComplexFrequency.evolution D H u ((k : ℂ) + (y : ℂ) * Complex.I))
      volume a b :=
  (weighted_line_continuous D H u w y hyUpper hyLower).intervalIntegrable a b

/-- Exact finite horizontal decomposition, with the scalar residue coefficient
pulled outside the integral only after establishing interval integrability. -/
theorem horizontal_decomposition (D H : V →L[ℂ] V) (u w y a b : ℝ)
    (hyUpper : y < 1) (hyLower : y ≠ -1) :
    (∫ k in a..b, ODEGaussianComplex.kernel w ((k : ℂ) + (y : ℂ) * Complex.I) •
        ODEComplexFrequency.evolution D H u ((k : ℂ) + (y : ℂ) * Complex.I)) =
      ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)) a b y +
      (∫ k in a..b, ODEReciprocalLine.reciprocal (1 + y) k) •
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) := by
  have hNonzero : 1 + y ≠ 0 := by
    intro h
    apply hyLower
    linarith
  have hG := (regularized_line_continuous D H u w y hyUpper).intervalIntegrable
    (μ := volume) a b
  have hP : IntervalIntegrable (fun k : ℝ =>
      ODEReciprocalLine.reciprocal (1 + y) k •
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)) volume a b := by
    convert! ((ODEReciprocalLine.reciprocal_continuous (1 + y) hNonzero).smul
      (continuous_const : Continuous (fun _ : ℝ =>
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I)))).intervalIntegrable
      (μ := volume) a b using 1
  calc
    _ = ∫ k in a..b,
        dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)
          ((k : ℂ) + (y : ℂ) * Complex.I) +
        ODEReciprocalLine.reciprocal (1 + y) k •
          ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) := by
      apply intervalIntegral.integral_congr
      intro k _
      exact line_decomposition D H u w y k hyLower
    _ = _ := by
      rw [intervalIntegral.integral_add hG hP, intervalIntegral.integral_smul_const]
      rfl

/-- The upper horizontal line is exactly the existing real-frequency family. -/
theorem top_decomposition (D H : V →L[ℂ] V) (u w R : ℝ) :
    (∫ k in (-R)..R, ODEGaussianLimits.topWeighted D H u w k) =
      ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)) (-R) R 0 +
      (∫ k in (-R)..R, ODEReciprocalLine.reciprocal 1 k) •
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) := by
  have h := horizontal_decomposition D H u w 0 (-R) R (by norm_num) (by norm_num)
  simpa only [Complex.ofReal_zero, zero_mul, add_zero, ODEGaussianComplex.kernel_ofReal,
    ODEComplexFrequency.evolution_ofReal, ODEGaussianLimits.topWeighted] using h

/-- The lower horizontal line is exactly the integrable shifted residual. -/
theorem shifted_decomposition (D H : V →L[ℂ] V) (u w R : ℝ) (hw : 1 ≤ w) :
    (∫ k in (-R)..R, ODEGaussianShiftedIntegral.weighted D H u w k) =
      ODEContourRectangle.horizontal
        (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)) (-R) R (-2 * w) +
      (∫ k in (-R)..R, ODEReciprocalLine.reciprocal (1 - 2 * w) k) •
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) := by
  have h := horizontal_decomposition D H u w (-2 * w) (-R) R
    (by linarith) (by linarith)
  have hLine (k : ℝ) : (k : ℂ) + ((-2 * w : ℝ) : ℂ) * Complex.I =
      (k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
    ring
  have hCoefficient : 1 + (-2 * w) = 1 - 2 * w := by ring
  simpa only [hLine, hCoefficient, ODEGaussianShiftedIntegral.weighted] using h

/-- At every finite symmetric cutoff, the actual top-minus-bottom integral
splits into the regularized difference and the scalar principal-part difference. -/
theorem horizontal_difference (D H : V →L[ℂ] V) (u w R : ℝ) (hw : 1 ≤ w) :
    (∫ k in (-R)..R, ODEGaussianLimits.topWeighted D H u w k) -
        (∫ k in (-R)..R, ODEGaussianShiftedIntegral.weighted D H u w k) =
      (ODEContourRectangle.horizontal
          (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)) (-R) R 0 -
        ODEContourRectangle.horizontal
          (dslope (ODEGaussianAnalytic.weightedRegular D H u w) (-Complex.I)) (-R) R (-2 * w)) +
      ((∫ k in (-R)..R, ODEReciprocalLine.reciprocal 1 k) -
        (∫ k in (-R)..R, ODEReciprocalLine.reciprocal (1 - 2 * w) k)) •
        ODEGaussianAnalytic.weightedRegular D H u w (-Complex.I) := by
  rw [top_decomposition D H u w R, shifted_decomposition D H u w R hw, sub_smul]
  abel

end
end SparseHamiltonian.ODEGaussianFiniteContour
