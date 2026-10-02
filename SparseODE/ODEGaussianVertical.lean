import SparseODE.ODEGaussianShiftedIntegral

/-!
# Uniform decay on the two vertical contour edges

The Gaussian numerator is bounded throughout the closed strip from zero
to imaginary height minus twice the squared width.  Factoring the two
poles gives a quadratic lower bound for the denominator in the real
coordinate.  These estimates are independent of the vertical position
and will control both vertical edges of an expanding rectangle.

-/

namespace SparseHamiltonian.ODEGaussianVertical

noncomputable section
open scoped Interval InnerProduct

/-- Each of the pole factors has norm at least the absolute real part. -/
theorem pole_product_norm_lower (z : ℂ) :
    z.re ^ 2 ≤ ‖1 + z ^ 2‖ := by
  have hminus : |z.re| ≤ ‖z - Complex.I‖ := by
    simpa only [Complex.sub_re, Complex.I_re, sub_zero] using
      Complex.abs_re_le_norm (z - Complex.I)
  have hplus : |z.re| ≤ ‖z + Complex.I‖ := by
    simpa only [Complex.add_re, Complex.I_re, add_zero] using
      Complex.abs_re_le_norm (z + Complex.I)
  have hfactor : 1 + z ^ 2 = (z - Complex.I) * (z + Complex.I) := by
    calc
      _ = z ^ 2 - Complex.I ^ 2 := by rw [Complex.I_sq]; ring
      _ = _ := by ring
  rw [hfactor, norm_mul]
  calc
    z.re ^ 2 = |z.re| * |z.re| := by rw [← pow_two, sq_abs]
    _ ≤ ‖z - Complex.I‖ * ‖z + Complex.I‖ :=
      mul_le_mul hminus hplus (abs_nonneg _) (norm_nonneg _)

/-- The full denominator retains the quadratic real-coordinate lower bound. -/
theorem denominator_norm_lower (z : ℂ) :
    Real.pi * z.re ^ 2 ≤ ‖(Real.pi : ℂ) * (1 + z ^ 2)‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left (pole_product_norm_lower z) Real.pi_pos.le

/-- On the lower strip the Gaussian exponent never exceeds one in real part. -/
theorem exponent_re_le_one (w x y : ℝ) (hw : 0 < w)
    (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    (ODEGaussianComplex.exponent w ((x : ℂ) + (y : ℂ) * Complex.I)).re ≤ 1 := by
  rw [ODEGaussianComplex.exponent_re]
  have hProduct : y * (y + 4 * w) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hUpper (by linarith)
  have hFraction : y ≤ (x ^ 2 - y ^ 2 + 1) / (4 * w) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * w)).2
    nlinarith [sq_nonneg x]
  linarith

/-- A uniform numerator bound, including the endpoints of the strip. -/
theorem numerator_norm_le (w x y : ℝ) (hw : 0 < w)
    (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    ‖ODEGaussianComplex.numerator w ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 := by
  rw [ODEGaussianComplex.numerator, Complex.norm_exp]
  exact Real.exp_le_exp.mpr (exponent_re_le_one w x y hw hLower hUpper)

/-- The complex Gaussian kernel decays quadratically along each vertical
edge.  A nonzero real coordinate keeps the entire edge away from both poles. -/
theorem kernel_norm_le (w x y : ℝ) (hw : 0 < w) (hx : x ≠ 0)
    (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 / (Real.pi * x ^ 2) := by
  have hDenom : Real.pi * x ^ 2 ≤
      ‖(Real.pi : ℂ) * (1 + ((x : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖ := by
    simpa using denominator_norm_lower ((x : ℂ) + (y : ℂ) * Complex.I)
  have hPositive : 0 < Real.pi * x ^ 2 :=
    mul_pos Real.pi_pos (sq_pos_of_ne_zero hx)
  have hDenomPositive := hPositive.trans_le hDenom
  rw [ODEGaussianComplex.kernel, norm_div]
  calc
    _ ≤ Real.exp 1 /
        ‖(Real.pi : ℂ) * (1 + ((x : ℂ) + (y : ℂ) * Complex.I) ^ 2)‖ :=
      div_le_div_of_nonneg_right (numerator_norm_le w x y hw hLower hUpper)
        hDenomPositive.le
    _ ≤ Real.exp 1 / (Real.pi * x ^ 2) :=
      div_le_div_of_nonneg_left (Real.exp_pos 1).le hPositive hDenom

section Operators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- Lower-half-plane contractivity preserves the scalar vertical-edge bound
after multiplication by the generally noncommuting propagator. -/
theorem weighted_norm_le (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (w x y : ℝ) (hw : 0 < w) (hx : x ≠ 0)
    (hLower : -2 * w ≤ y) (hUpper : y ≤ 0) :
    ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I) •
        ODEComplexFrequency.evolution D H u ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      Real.exp 1 / (Real.pi * x ^ 2) := by
  have hContraction := ODEComplexFrequency.evolution_norm_le_one D H hD hH hPSD
    u hu ((x : ℂ) + (y : ℂ) * Complex.I) (by simpa using hUpper)
  rw [norm_smul]
  calc
    _ ≤ ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I)‖ * 1 :=
      mul_le_mul_of_nonneg_left hContraction (norm_nonneg _)
    _ = ‖ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I)‖ := mul_one _
    _ ≤ _ := kernel_norm_le w x y hw hx hLower hUpper

/-- A parametrized vertical contour integral is bounded by its length times
the uniform kernel estimate.  The factor `I` is the derivative of the
vertical parametrization. -/
theorem vertical_integral_norm_le (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H)
    (hPSD : ∀ v : V, 0 ≤ (inner ℂ v (D v)).re)
    (u : ℝ) (hu : 0 ≤ u) (w x : ℝ) (hw : 0 < w) (hx : x ≠ 0) :
    ‖∫ y in (-2 * w)..0,
        Complex.I • (ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I) •
          ODEComplexFrequency.evolution D H u ((x : ℂ) + (y : ℂ) * Complex.I))‖ ≤
      (2 * w) * (Real.exp 1 / (Real.pi * x ^ 2)) := by
  have horder : -2 * w ≤ 0 := by linarith
  have hBound (y : ℝ) (hy : y ∈ Set.uIoc (-2 * w) 0) :
      ‖Complex.I •
        (ODEGaussianComplex.kernel w ((x : ℂ) + (y : ℂ) * Complex.I) •
          ODEComplexFrequency.evolution D H u ((x : ℂ) + (y : ℂ) * Complex.I))‖ ≤
        Real.exp 1 / (Real.pi * x ^ 2) := by
    have hy' : y ∈ Set.Ioc (-2 * w) 0 := by
      simpa only [Set.uIoc_of_le horder] using hy
    rw [norm_smul, Complex.norm_I, one_mul]
    exact weighted_norm_le D H hD hH hPSD u hu w x y hw hx hy'.1.le hy'.2
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hBound
  calc
    _ ≤ (Real.exp 1 / (Real.pi * x ^ 2)) * |0 - (-2 * w)| := h
    _ = _ := by rw [abs_of_nonneg (by linarith : 0 ≤ 0 - (-2 * w))]; ring

end Operators

end
end SparseHamiltonian.ODEGaussianVertical
