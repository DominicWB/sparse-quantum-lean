import SparseODE.ODEGaussianMass

/-!
# Global regularity of the Gaussian LCHS kernel

The derivative estimate is uniform on the whole frequency line. The constant
is deliberately loose: refining this query-free mesh does not change the
native sparse-oracle complexity.
-/

namespace SparseHamiltonian.ODEGaussianKernel

noncomputable section

/-- A factored real derivative, keeping the Cauchy denominator visible. -/
def amplitudeDerivative (w k : ℝ) : ℝ :=
  -(k / (2 * w)) * amplitude w k -
    (2 * k / (1 + k ^ 2)) * amplitude w k

theorem amplitude_hasDerivAt (w k : ℝ) (hw : 0 < w) :
    HasDerivAt (amplitude w) (amplitudeDerivative w k) k := by
  have hden : 0 < 1 + k ^ 2 := by positivity
  have hExponent : HasDerivAt (fun z : ℝ => 1 - (z ^ 2 + 1) / (4 * w))
      (-(k / (2 * w))) k := by
    have hScalar : -(k / (2 * w)) = -((2 : ℝ) * k ^ (2 - 1) * 1 / (4 * w)) := by
      field_simp [hw.ne'] ; ring
    convert! ((((hasDerivAt_id k).pow 2).add_const 1).div_const (4 * w)).const_sub 1
      using 1
  have hDenominator : HasDerivAt (fun z : ℝ => Real.pi * (1 + z ^ 2))
      (Real.pi * (2 * k)) k := by
    have hScalar : Real.pi * (2 * k) = Real.pi * ((2 : ℝ) * k ^ (2 - 1) * 1) := by
      ring
    convert! (((hasDerivAt_id k).pow 2).const_add 1).const_mul Real.pi
      using 1
  have hScalar : amplitudeDerivative w k =
      (Real.exp (1 - (k ^ 2 + 1) / (4 * w)) * (-(k / (2 * w))) *
          (Real.pi * (1 + k ^ 2)) -
        Real.exp (1 - (k ^ 2 + 1) / (4 * w)) * (Real.pi * (2 * k))) /
        (Real.pi * (1 + k ^ 2)) ^ 2 := by
    dsimp only [amplitudeDerivative, amplitude]
    field_simp [hw.ne', Real.pi_pos.ne', hden.ne']
  convert! hExponent.exp.div hDenominator
    (mul_ne_zero Real.pi_pos.ne' hden.ne') using 1

/-- The single frequency factor is absorbed by the Cauchy denominator. -/
theorem weighted_amplitude_le (w k : ℝ) (hw : 0 < w) :
    |k| * amplitude w k ≤ Real.exp 1 / Real.pi := by
  have hden : 0 < 1 + k ^ 2 := by positivity
  have habs : |k| ≤ 1 + k ^ 2 := by
    have hs := sq_nonneg (|k| - 1)
    have hk := sq_abs k
    nlinarith [abs_nonneg k, sq_nonneg k]
  have hEnvelope : amplitude w k ≤
      (Real.exp 1 / Real.pi) / (1 + k ^ 2) := by
    have h := norm_kernel_le_cauchy w k hw
    rw [norm_kernel_eq_amplitude] at h
    simpa only [div_div] using h
  calc
    _ ≤ (1 + k ^ 2) * amplitude w k :=
      mul_le_mul_of_nonneg_right habs (amplitude_nonneg w k)
    _ ≤ Real.exp 1 / Real.pi := by
      have h := (le_div_iff₀ hden).mp hEnvelope
      simpa only [mul_comm] using h

theorem amplitudeDerivative_bound (w k : ℝ) (hw : 0 < w) :
    ‖amplitudeDerivative w k‖ ≤
      (Real.exp 1 / Real.pi) * (2 + 1 / (2 * w)) := by
  have hden : 0 < 1 + k ^ 2 := by positivity
  have hw2 : 0 < 2 * w := by positivity
  have hC : 0 ≤ Real.exp 1 / Real.pi := by positivity
  have hWeighted := weighted_amplitude_le w k hw
  have hFirst : (|k| * amplitude w k) / (2 * w) ≤
      (Real.exp 1 / Real.pi) / (2 * w) :=
    div_le_div_of_nonneg_right hWeighted hw2.le
  have hSecond : (|k| * amplitude w k) / (1 + k ^ 2) ≤
      Real.exp 1 / Real.pi := by
    apply (div_le_iff₀ hden).mpr
    exact hWeighted.trans (by nlinarith [mul_nonneg hC (sq_nonneg k)])
  calc
    _ ≤ ‖-(k / (2 * w)) * amplitude w k‖ +
        ‖(2 * k / (1 + k ^ 2)) * amplitude w k‖ := norm_sub_le _ _
    _ = (|k| * amplitude w k) / (2 * w) +
        2 * ((|k| * amplitude w k) / (1 + k ^ 2)) := by
      simp only [norm_mul, Real.norm_eq_abs, abs_neg, abs_div, abs_mul,
        abs_of_nonneg (amplitude_nonneg w k), abs_of_pos hw2,
        abs_of_pos hden, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (Real.exp 1 / Real.pi) / (2 * w) +
        2 * (Real.exp 1 / Real.pi) := by linarith
    _ = _ := by ring

theorem phase_hasDerivAt (k : ℝ) :
    HasDerivAt (fun z : ℝ => Complex.exp (-Complex.I * (z : ℂ)))
      (Complex.exp (-Complex.I * (k : ℂ)) * (-Complex.I)) k := by
  convert! ((hasDerivAt_id k).ofReal_comp.const_mul (-Complex.I)).cexp using 1 ;
    first | rfl | simp only [id_eq, Complex.ofReal_one, mul_one]

/-- The explicit complex derivative, in its product-rule form. -/
def kernelDerivative (w k : ℝ) : ℂ :=
  (amplitudeDerivative w k : ℂ) * Complex.exp (-Complex.I * (k : ℂ)) +
    (amplitude w k : ℂ) *
      (Complex.exp (-Complex.I * (k : ℂ)) * (-Complex.I))

theorem kernel_hasDerivAt (w k : ℝ) (hw : 0 < w) :
    HasDerivAt (kernel w) (kernelDerivative w k) k := by
  exact (amplitude_hasDerivAt w k hw).ofReal_comp.mul (phase_hasDerivAt k)

/-- A public global Lipschitz envelope, valid for every positive width. -/
def lipschitzConstant (w : ℝ) : ℝ :=
  (Real.exp 1 / Real.pi) * (3 + 1 / (2 * w))

theorem lipschitzConstant_nonneg (w : ℝ) (hw : 0 < w) :
    0 ≤ lipschitzConstant w := by
  unfold lipschitzConstant
  positivity

theorem kernelDerivative_bound (w k : ℝ) (hw : 0 < w) :
    ‖kernelDerivative w k‖ ≤ lipschitzConstant w := by
  have hphase := phase_norm k
  have ha : amplitude w k ≤ Real.exp 1 / Real.pi := by
    simpa only [norm_kernel_eq_amplitude] using norm_kernel_le w k hw
  calc
    _ ≤ ‖(amplitudeDerivative w k : ℂ) *
          Complex.exp (-Complex.I * (k : ℂ))‖ +
        ‖(amplitude w k : ℂ) *
          (Complex.exp (-Complex.I * (k : ℂ)) * (-Complex.I))‖ := norm_add_le _ _
    _ = ‖amplitudeDerivative w k‖ + amplitude w k := by
      simp only [norm_mul, hphase, norm_neg, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amplitude_nonneg w k)]
    _ ≤ (Real.exp 1 / Real.pi) * (2 + 1 / (2 * w)) +
        Real.exp 1 / Real.pi := add_le_add (amplitudeDerivative_bound w k hw) ha
    _ = lipschitzConstant w := by unfold lipschitzConstant; ring

/-- The exact regularity premise required by the public frequency table. -/
theorem kernel_lipschitz (w : ℝ) (hw : 0 < w) (k l : ℝ) :
    ‖kernel w k - kernel w l‖ ≤ lipschitzConstant w * |k - l| := by
  have htime (r : ℝ) : HasDerivAt (fun q : ℝ => (1 - q) * l + q * k)
      (k - l) r := by
    have hScalar : k - l = (-1 : ℝ) * l + 1 * k := by ring
    convert! (((hasDerivAt_id r).const_sub 1).mul_const l).add
      ((hasDerivAt_id r).mul_const k) using 1
  have hderiv (r : ℝ) :
      HasDerivAt (fun q : ℝ => kernel w ((1 - q) * l + q * k))
        ((k - l) • kernelDerivative w ((1 - r) * l + r * k)) r := by
    simpa only [Function.comp_def] using
      (kernel_hasDerivAt w ((1 - r) * l + r * k) hw).scomp r (htime r)
  have hbound (r : ℝ) :
      ‖(k - l) • kernelDerivative w ((1 - r) * l + r * k)‖ ≤
        lipschitzConstant w * |k - l| := by
    rw [norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ |k - l| * lipschitzConstant w :=
        mul_le_mul_of_nonneg_left (kernelDerivative_bound w _ hw) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun r _ => (hderiv r).hasDerivWithinAt) (fun r _ => hbound r)
  simpa only [sub_self, zero_mul, one_mul, zero_add, sub_zero, add_zero] using h

end
end SparseHamiltonian.ODEGaussianKernel
