import SparseODE.ODEGaussianComplexContinuation2

namespace SparseHamiltonian.ODEGaussianAnalytic

noncomputable section

/-- The scalar factor after separating the pole at -I. -/
def regularizedFactor (w : ℝ) (z : ℂ) : ℂ :=
  ODEGaussianComplex.numerator w z / ((Real.pi : ℂ) * (z - Complex.I))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Operator-valued analytic factor of the pole quotient. -/
def weightedRegular (D H : V →L[ℂ] V) (u w : ℝ) (z : ℂ) : V →L[ℂ] V :=
  regularizedFactor w z • ODEComplexFrequency.evolution D H u z

/-- The regularized scalar factor has only the upper pole remaining. -/
theorem regularizedFactor_analyticAt (w : ℝ) (z : ℂ) (hz : z ≠ Complex.I) :
    AnalyticAt ℂ (regularizedFactor w) z := by
  have hDen : AnalyticAt ℂ
      (fun ζ : ℂ => (Real.pi : ℂ) * (ζ - Complex.I)) z :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) z).mul
      ((analyticAt_id : AnalyticAt ℂ (fun ζ : ℂ => ζ) z).sub
        (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => Complex.I) z))
  exact (ODEGaussianComplex.numerator_analyticAt w z).div hDen
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (sub_ne_zero.mpr hz))

/-- Multiplication by the entire operator evolution preserves analyticity.
No commutativity, positivity or self-adjointness hypotheses are needed. -/
theorem weightedRegular_analyticAt (D H : V →L[ℂ] V) (u w : ℝ) (z : ℂ)
    (hz : z ≠ Complex.I) : AnalyticAt ℂ (weightedRegular D H u w) z :=
  (regularizedFactor_analyticAt w z hz).smul
    (ODEComplexFrequency.evolution_analyticAt D H u z)

/-- Every point strictly below the upper pole has a neighborhood on which
the regularized operator factor is analytic. -/
theorem weightedRegular_analyticOnNhd (D H : V →L[ℂ] V) (u w : ℝ) :
    AnalyticOnNhd ℂ (weightedRegular D H u w) {z : ℂ | z.im < 1} := by
  intro z hz
  apply weightedRegular_analyticAt D H u w z
  intro h
  have hIm : z.im = 1 := by simpa only [Complex.I_im] using congrArg Complex.im h
  change z.im < 1 at hz
  linarith

/-- Concrete complex differentiability hypothesis for the rectangular
contour theorem, including the removable point at -I. -/
theorem weightedRegular_differentiableOn (D H : V →L[ℂ] V) (u w : ℝ) :
    DifferentiableOn ℂ (weightedRegular D H u w) {z : ℂ | z.im < 1} :=
  (weightedRegular_analyticOnNhd D H u w).differentiableOn

end
end SparseHamiltonian.ODEGaussianAnalytic
