import SparseODE.ODEFiniteLCHSConstruction

/-!
# Scalar Gaussian LCHS kernel

The positive width parameter `w` is the squared Gaussian parameter.  The
kernel includes the Fourier normalization and uses the shift `c = 1`.
This section proves only scalar properties; the operator integral identity
and its truncation estimate are separate obligations.

-/

namespace SparseHamiltonian.ODEGaussianKernel

noncomputable section

/-- Positive amplitude of the Gaussian-smoothed Cauchy kernel. -/
def amplitude (w k : ℝ) : ℝ :=
  Real.exp (1 - (k ^ 2 + 1) / (4 * w)) / (Real.pi * (1 + k ^ 2))

/-- Fourier-normalized Gaussian LCHS kernel with contour shift one. -/
def kernel (w k : ℝ) : ℂ :=
  (amplitude w k : ℂ) * Complex.exp (-Complex.I * (k : ℂ))

theorem denominator_pos (k : ℝ) : 0 < Real.pi * (1 + k ^ 2) := by
  exact mul_pos Real.pi_pos (by positivity)

theorem amplitude_pos (w k : ℝ) : 0 < amplitude w k := by
  exact div_pos (Real.exp_pos _) (denominator_pos k)

theorem amplitude_nonneg (w k : ℝ) : 0 ≤ amplitude w k :=
  (amplitude_pos w k).le

theorem phase_norm (k : ℝ) :
    ‖Complex.exp (-Complex.I * (k : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

theorem norm_kernel_eq_amplitude (w k : ℝ) :
    ‖kernel w k‖ = amplitude w k := by
  rw [kernel, norm_mul, phase_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (amplitude_pos w k)]

theorem amplitude_neg (w k : ℝ) : amplitude w (-k) = amplitude w k := by
  simp only [amplitude, neg_sq]

theorem norm_kernel_neg (w k : ℝ) : ‖kernel w (-k)‖ = ‖kernel w k‖ := by
  rw [norm_kernel_eq_amplitude, norm_kernel_eq_amplitude, amplitude_neg]

/-- The Gaussian damping never increases the Cauchy envelope. -/
theorem amplitude_le_cauchy (w k : ℝ) (hw : 0 < w) :
    amplitude w k ≤ Real.exp 1 / (Real.pi * (1 + k ^ 2)) := by
  apply div_le_div_of_nonneg_right _ (denominator_pos k).le
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ (k ^ 2 + 1) / (4 * w) := by positivity
  linarith

theorem norm_kernel_le_cauchy (w k : ℝ) (hw : 0 < w) :
    ‖kernel w k‖ ≤ Real.exp 1 / (Real.pi * (1 + k ^ 2)) := by
  rw [norm_kernel_eq_amplitude]
  exact amplitude_le_cauchy w k hw

theorem norm_kernel_le (w k : ℝ) (hw : 0 < w) :
    ‖kernel w k‖ ≤ Real.exp 1 / Real.pi := by
  refine (norm_kernel_le_cauchy w k hw).trans ?_
  apply div_le_div_of_nonneg_left (Real.exp_pos 1).le Real.pi_pos
  calc
    Real.pi = Real.pi * 1 := by ring
    _ ≤ Real.pi * (1 + k ^ 2) :=
      mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg k]) Real.pi_pos.le

/-- Outside a symmetric interval, the Gaussian factor can be bounded at
the endpoint while retaining the integrable Cauchy denominator. -/
theorem norm_kernel_le_exterior (w R k : ℝ) (hw : 0 < w)
    (hR : 0 ≤ R) (hRk : R ≤ |k|) :
    ‖kernel w k‖ ≤
      Real.exp (1 - (R ^ 2 + 1) / (4 * w)) / (Real.pi * (1 + k ^ 2)) := by
  have hSquare : R ^ 2 ≤ k ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hRk) (add_nonneg (abs_nonneg k) hR)
    nlinarith [sq_abs k]
  rw [norm_kernel_eq_amplitude]
  apply div_le_div_of_nonneg_right _ (denominator_pos k).le
  apply Real.exp_le_exp.mpr
  have hq : (R ^ 2 + 1) / (4 * w) ≤ (k ^ 2 + 1) / (4 * w) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- At radius at least twice the squared Gaussian width, the remaining
tail envelope has the exponentially small factor `exp (1 - w)`. -/
theorem norm_kernel_le_width_tail (w R k : ℝ) (hw : 0 < w)
    (hR : 2 * w ≤ R) (hRk : R ≤ |k|) :
    ‖kernel w k‖ ≤ Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
  have hRnonneg : 0 ≤ R := by linarith
  have hSquare : 4 * w ^ 2 ≤ R ^ 2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hR)
      (add_nonneg hRnonneg (by positivity : 0 ≤ 2 * w))
    nlinarith
  refine (norm_kernel_le_exterior w R k hw hRnonneg hRk).trans ?_
  apply div_le_div_of_nonneg_right _ (denominator_pos k).le
  apply Real.exp_le_exp.mpr
  have hq : w ≤ (R ^ 2 + 1) / (4 * w) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * w)).mpr
    nlinarith
  linarith

theorem amplitude_continuous (w : ℝ) : Continuous (amplitude w) := by
  have hSquare : Continuous (fun k : ℝ => k ^ 2 + 1) :=
    (continuous_id.pow 2).add continuous_const
  have hExponent : Continuous (fun k : ℝ => 1 - (k ^ 2 + 1) / (4 * w)) :=
    continuous_const.sub (hSquare.div_const (4 * w))
  have hDenominator : Continuous (fun k : ℝ => Real.pi * (1 + k ^ 2)) :=
    continuous_const.mul (continuous_const.add (continuous_id.pow 2))
  exact (Real.continuous_exp.comp hExponent).div hDenominator
    (fun k => ne_of_gt (denominator_pos k))

theorem kernel_continuous (w : ℝ) : Continuous (kernel w) := by
  have hPhase : Continuous (fun k : ℝ => -Complex.I * (k : ℂ)) :=
    continuous_const.mul Complex.continuous_ofReal
  exact (Complex.continuous_ofReal.comp (amplitude_continuous w)).mul
    (Complex.continuous_exp.comp hPhase)

end
end SparseHamiltonian.ODEGaussianKernel
