import SparseODE.ODEGaussianFiniteTableContinuation2

/-!
# Complex Gaussian density and its shifted horizontal line

This is the meromorphic scalar continuation of the concrete real-frequency
density.  The pole at -I has numerator one.  At imaginary height -2w the
Gaussian numerator has norm at most exp(1-w), and the denominator retains
a Cauchy envelope.  These estimates do not assume a contour identity.

-/

namespace SparseHamiltonian.ODEGaussianComplex

noncomputable section

/-- Entire exponent of the Gaussian-smoothed Cauchy density. -/
def exponent (w : ℝ) (z : ℂ) : ℂ :=
  1 - (z ^ 2 + 1) / ((4 * w : ℝ) : ℂ) - Complex.I * z

/-- Entire numerator; the rational denominator is kept separate. -/
def numerator (w : ℝ) (z : ℂ) : ℂ := Complex.exp (exponent w z)

/-- Meromorphic continuation of the real-frequency Gaussian density. -/
def kernel (w : ℝ) (z : ℂ) : ℂ :=
  numerator w z / ((Real.pi : ℂ) * (1 + z ^ 2))

/-- Real part throughout the complex plane, with both coordinates explicit. -/
theorem exponent_re (w x y : ℝ) :
    (exponent w ((x : ℂ) + (y : ℂ) * Complex.I)).re =
      1 - (x ^ 2 - y ^ 2 + 1) / (4 * w) + y := by
  simp only [exponent, Complex.sub_re, Complex.one_re,
    Complex.div_ofReal_re, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, pow_two]
  ring

/-- On the real axis the entire numerator splits into the old amplitude
numerator and its unit-modulus Fourier phase. -/
theorem exponent_ofReal (w k : ℝ) :
    exponent w (k : ℂ) =
      ((1 - (k ^ 2 + 1) / (4 * w) : ℝ) : ℂ) +
        (-Complex.I * (k : ℂ)) := by
  simp only [exponent, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow]
  ring

/-- The complex continuation agrees exactly with the already constructed
real-frequency Gaussian kernel, including its normalization. -/
theorem kernel_ofReal (w k : ℝ) :
    kernel w (k : ℂ) = ODEGaussianKernel.kernel w k := by
  rw [kernel, numerator, exponent_ofReal, Complex.exp_add,
    ← Complex.ofReal_exp]
  simp only [ODEGaussianKernel.kernel, ODEGaussianKernel.amplitude,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_one, Complex.ofReal_pow]
  ring

/-- The numerator equals one at the enclosed simple pole. -/
theorem numerator_neg_I (w : ℝ) : numerator w (-Complex.I) = 1 := by
  simp [numerator, exponent, Complex.I_sq, Complex.I_mul_I]

/-- The entire scalar numerator is continuous on the complex plane. -/
theorem numerator_continuous (w : ℝ) : Continuous (numerator w) := by
  have hExponent : Continuous (exponent w) :=
    (continuous_const.sub
      (((continuous_id.pow 2).add continuous_const).div_const
        ((4 * w : ℝ) : ℂ))).sub
      (continuous_const.mul continuous_id)
  exact Complex.continuous_exp.comp hExponent

/-- Completing the real part of the square on the downward horizontal line. -/
theorem shifted_exponent_re (w k : ℝ) (hw : 0 < w) :
    (exponent w ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)).re =
      1 - w - (k ^ 2 + 1) / (4 * w) := by
  have hz : (k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I =
      (k : ℂ) + ((-(2 * w) : ℝ) : ℂ) * Complex.I := by
    simp only [Complex.ofReal_neg]
    ring
  rw [hz, exponent_re]
  field_simp [hw.ne'] ; ring

/-- The Gaussian numerator gains the exponentially small shifted-line factor. -/
theorem shifted_numerator_norm_le (w k : ℝ) (hw : 0 < w) :
    ‖numerator w ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp (1 - w) := by
  rw [numerator, Complex.norm_exp, shifted_exponent_re w k hw]
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ (k ^ 2 + 1) / (4 * w) := by positivity
  linarith

/-- A horizontal line at depth at least two stays uniformly beyond both poles. -/
theorem norm_one_add_sq_lower (k r : ℝ) (hr : 2 ≤ r) :
    1 + k ^ 2 ≤ ‖(1 : ℂ) + ((k : ℂ) - (r : ℂ) * Complex.I) ^ 2‖ := by
  have hrSq : 4 ≤ r ^ 2 := by nlinarith [sq_nonneg (r - 2)]
  have hFactor : 0 ≤ r ^ 2 * (r ^ 2 - 2 + 2 * k ^ 2) :=
    mul_nonneg (sq_nonneg r) (by nlinarith [sq_nonneg k])
  apply (sq_le_sq₀ (by positivity : 0 ≤ 1 + k ^ 2) (norm_nonneg _)).mp
  have hId :
      ‖(1 : ℂ) + ((k : ℂ) - (r : ℂ) * Complex.I) ^ 2‖ ^ 2 =
        (1 + k ^ 2) ^ 2 + r ^ 2 * (r ^ 2 - 2 + 2 * k ^ 2) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two, Complex.mul_re, Complex.mul_im] ; ring
  rw [hId]
  linarith

/-- Cauchy-sized lower bound for the full normalized denominator. -/
theorem shifted_denominator_norm_lower (w k : ℝ) (hw : 1 ≤ w) :
    Real.pi * (1 + k ^ 2) ≤
      ‖(Real.pi : ℂ) *
        (1 + ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) ^ 2)‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact mul_le_mul_of_nonneg_left
    (norm_one_add_sq_lower k (2 * w) (by linarith)) Real.pi_pos.le

/-- Pointwise integrable bound along the downward-shifted horizontal line. -/
theorem shifted_kernel_norm_le (w k : ℝ) (hw : 1 ≤ w) :
    ‖kernel w ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
  have hwpos : 0 < w := by linarith
  have hden := shifted_denominator_norm_lower w k hw
  have hdenpos := ODEGaussianKernel.denominator_pos k
  rw [kernel, norm_div]
  calc
    _ ≤ Real.exp (1 - w) /
        ‖(Real.pi : ℂ) *
          (1 + ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) ^ 2)‖ :=
      div_le_div_of_nonneg_right (shifted_numerator_norm_le w k hwpos)
        (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.exp_pos _).le hdenpos hden

/-- The shifted contour contains no poles, so its scalar density is continuous. -/
theorem shifted_kernel_continuous (w : ℝ) (hw : 1 ≤ w) :
    Continuous (fun k : ℝ =>
      kernel w ((k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I)) := by
  have hz : Continuous (fun k : ℝ =>
      (k : ℂ) - ((2 * w : ℝ) : ℂ) * Complex.I) :=
    Complex.continuous_ofReal.sub continuous_const
  apply ((numerator_continuous w).comp hz).div
    (continuous_const.mul (continuous_const.add (hz.pow 2)))
  intro k
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (ODEGaussianKernel.denominator_pos k)
    (shifted_denominator_norm_lower w k hw)

end
end SparseHamiltonian.ODEGaussianComplex
