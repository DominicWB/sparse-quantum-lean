import SparseODE.ODEComplexFrequencyContinuation2

/-!
# Analytic regularity of the Gaussian contour integrand

The scalar Gaussian numerator is entire.  Removing the lower pole leaves
an operator-valued factor analytic throughout Im z < 1, including z = -I.
These regularity facts supply the hypotheses of the rectangular Cauchy
argument; they do not assume its eventual integral identity.

-/

namespace SparseHamiltonian.ODEGaussianComplex

noncomputable section

/-- The exponent is a polynomial plus a constant scalar division, hence
entire for every real smoothing parameter. -/
theorem exponent_analyticAt (w : ℝ) (z : ℂ) :
    AnalyticAt ℂ (exponent w) z := by
  have hSquare : AnalyticAt ℂ (fun ζ : ℂ => ζ ^ 2 + 1) z :=
    ((analyticAt_id : AnalyticAt ℂ (fun ζ : ℂ => ζ) z).pow 2).add
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z)
  have hPhase : AnalyticAt ℂ (fun ζ : ℂ => Complex.I * ζ) z :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => Complex.I) z).mul
      (analyticAt_id : AnalyticAt ℂ (fun ζ : ℂ => ζ) z)
  exact ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z).sub
    (hSquare.div_const (c := ((4 * w : ℝ) : ℂ)))).sub hPhase

/-- The Gaussian numerator is entire. -/
theorem numerator_analyticAt (w : ℝ) (z : ℂ) :
    AnalyticAt ℂ (numerator w) z := by
  convert! (exponent_analyticAt w z).cexp using 1

/-- The only possible zeros of the rational denominator are the two
displayed poles. -/
theorem one_add_sq_ne_zero (z : ℂ) (hzPos : z ≠ Complex.I)
    (hzNeg : z ≠ -Complex.I) : 1 + z ^ 2 ≠ 0 := by
  have hFactor : (1 : ℂ) + z ^ 2 = (z - Complex.I) * (z + Complex.I) := by
    calc
      (1 : ℂ) + z ^ 2 = z ^ 2 - Complex.I ^ 2 := by
        rw [Complex.I_sq]
        ring
      _ = (z - Complex.I) * (z + Complex.I) := by ring
  have hPlus : z + Complex.I ≠ 0 := by
    intro h
    apply hzNeg
    calc
      z = (z + Complex.I) - Complex.I := by ring
      _ = -Complex.I := by rw [h]; simp
  rw [hFactor]
  exact mul_ne_zero (sub_ne_zero.mpr hzPos) hPlus

/-- The meromorphic density is complex analytic away from its two poles. -/
theorem kernel_analyticAt (w : ℝ) (z : ℂ) (hzPos : z ≠ Complex.I)
    (hzNeg : z ≠ -Complex.I) : AnalyticAt ℂ (kernel w) z := by
  have hDen : AnalyticAt ℂ
      (fun ζ : ℂ => (Real.pi : ℂ) * (1 + ζ ^ 2)) z :=
    (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Real.pi : ℂ)) z).mul
      ((analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (1 : ℂ)) z).add
        ((analyticAt_id : AnalyticAt ℂ (fun ζ : ℂ => ζ) z).pow 2))
  exact (numerator_analyticAt w z).div hDen
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      (one_add_sq_ne_zero z hzPos hzNeg))

/-- Pointwise complex differentiability in the complement of the poles. -/
theorem kernel_differentiableAt (w : ℝ) (z : ℂ) (hzPos : z ≠ Complex.I)
    (hzNeg : z ≠ -Complex.I) : DifferentiableAt ℂ (kernel w) z :=
  (kernel_analyticAt w z hzPos hzNeg).differentiableAt

end
end SparseHamiltonian.ODEGaussianComplex
