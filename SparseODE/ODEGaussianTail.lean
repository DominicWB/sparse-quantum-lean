import SparseODE.ODEGaussianParametersContinuation2

/-!
# Integrated Gaussian tail

The density is integrable on the whole line.  Outside the public cutoff,
its Gaussian factor is bounded by exp(1-w), while exact Cauchy integration
and arctangent reciprocity supply the additional reciprocal-radius factor.
No operator integral representation is assumed or proved in this section.

Requires Mathlib.Analysis.SpecialFunctions.ImproperIntegrals.
-/

namespace SparseHamiltonian.ODEGaussianTail

noncomputable section
open MeasureTheory
open scoped Interval

private theorem cauchy_factor (C k : ℝ) :
    C / (Real.pi * (1 + k ^ 2)) =
      (C / Real.pi) * (1 + k ^ 2)⁻¹ := by
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Integrability of every constant multiple of the Cauchy envelope. -/
theorem integrable_cauchy (C : ℝ) :
    Integrable (fun k : ℝ => C / (Real.pi * (1 + k ^ 2))) := by
  simp_rw [cauchy_factor]
  exact integrable_inv_one_add_sq.const_mul (C / Real.pi)

/-- Exact whole-line mass of the normalized Cauchy envelope. -/
theorem cauchy_integral_univ (C : ℝ) :
    (∫ k : ℝ, C / (Real.pi * (1 + k ^ 2))) = C := by
  simp_rw [cauchy_factor]
  rw [integral_const_mul, integral_univ_inv_one_add_sq]
  exact div_mul_cancel₀ C Real.pi_ne_zero

/-- The complex Gaussian density is genuinely Bochner integrable. -/
theorem integrable_kernel (w : ℝ) (hw : 0 < w) :
    Integrable (ODEGaussianKernel.kernel w) := by
  apply (integrable_cauchy (Real.exp 1)).mono'
    (ODEGaussianKernel.kernel_continuous w).aestronglyMeasurable
  exact Filter.Eventually.of_forall
    (fun k => ODEGaussianKernel.norm_kernel_le_cauchy w k hw)

/-- Its absolute mass is also integrable, so exterior integrals are finite. -/
theorem integrable_norm_kernel (w : ℝ) (hw : 0 < w) :
    Integrable (fun k : ℝ => ‖ODEGaussianKernel.kernel w k‖) :=
  (integrable_kernel w hw).norm

/-- An elementary upper bound for arctangent on the positive half-line. -/
theorem arctan_le_self (x : ℝ) (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hIntegral :
      (∫ k in (0 : ℝ)..x, Real.pi / (Real.pi * (1 + k ^ 2))) ≤
        ∫ k in (0 : ℝ)..x, (1 : ℝ) := by
    apply intervalIntegral.integral_mono_on hx
      ((ODEGaussianMass.cauchy_continuous Real.pi).intervalIntegrable
        (μ := volume) 0 x)
      (continuous_const.intervalIntegrable (μ := volume) 0 x)
    intro k _
    apply (div_le_one (ODEGaussianKernel.denominator_pos k)).mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg k)]
  simpa only [ODEGaussianMass.cauchy_integral, div_self Real.pi_ne_zero,
    Real.arctan_zero, sub_zero, one_mul, intervalIntegral.integral_const,
    smul_eq_mul, mul_one] using hIntegral

/-- Exact Cauchy mass outside the symmetric half-open interval. -/
theorem cauchy_exterior_eq (C R : ℝ) (hR : 0 < R) :
    (∫ k in (Set.Ioc (-R) R)ᶜ, C / (Real.pi * (1 + k ^ 2))) =
      2 * (C / Real.pi) * Real.arctan R⁻¹ := by
  have horder : -R ≤ R := by linarith
  rw [setIntegral_compl measurableSet_Ioc (integrable_cauchy C),
    cauchy_integral_univ, ← intervalIntegral.integral_of_le horder,
    ODEGaussianMass.cauchy_integral, Real.arctan_neg,
    Real.arctan_inv_of_pos hR]
  field_simp [Real.pi_ne_zero] ; ring

/-- The two Cauchy tails are bounded by twice the reciprocal radius. -/
theorem cauchy_exterior_le (C R : ℝ) (hC : 0 ≤ C) (hR : 0 < R) :
    (∫ k in (Set.Ioc (-R) R)ᶜ, C / (Real.pi * (1 + k ^ 2))) ≤
      2 * C / (Real.pi * R) := by
  rw [cauchy_exterior_eq C R hR]
  calc
    _ ≤ 2 * (C / Real.pi) * R⁻¹ :=
      mul_le_mul_of_nonneg_left (arctan_le_self R⁻¹ (inv_nonneg.mpr hR.le))
        (by positivity)
    _ = _ := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The integrated Gaussian tail, retaining its cutoff-dependent prefactor. -/
theorem exterior_mass_le_radius (w R : ℝ) (hw : 0 < w) (hR : 2 * w ≤ R) :
    (∫ k in (Set.Ioc (-R) R)ᶜ, ‖ODEGaussianKernel.kernel w k‖) ≤
      2 * Real.exp (1 - w) / (Real.pi * R) := by
  have hRpos : 0 < R := by linarith
  calc
    _ ≤ ∫ k in (Set.Ioc (-R) R)ᶜ,
        Real.exp (1 - w) / (Real.pi * (1 + k ^ 2)) := by
      apply setIntegral_mono_on (integrable_norm_kernel w hw).integrableOn
        (integrable_cauchy (Real.exp (1 - w))).integrableOn
        measurableSet_Ioc.compl
      intro k hk
      apply ODEGaussianKernel.norm_kernel_le_width_tail w R k hw hR
      by_contra h
      have ha : |k| < R := lt_of_not_ge h
      have hmem : k ∈ Set.Ioc (-R) R :=
        ⟨(abs_lt.mp ha).1, (abs_lt.mp ha).2.le⟩
      exact hk hmem
    _ ≤ _ := cauchy_exterior_le _ _ (Real.exp_pos _).le hRpos

/-- At squared width at least two the tail uses only the reserved
`exp(1-w)/(2*pi)` error budget. -/
theorem exterior_mass_bound (w R : ℝ) (hw : 2 ≤ w) (hR : 2 * w ≤ R) :
    (∫ k in (Set.Ioc (-R) R)ᶜ, ‖ODEGaussianKernel.kernel w k‖) ≤
      Real.exp (1 - w) / (2 * Real.pi) := by
  have hwpos : 0 < w := by linarith
  have hRfour : 4 ≤ R := by linarith
  have hRpos : 0 < R := by linarith
  refine (exterior_mass_le_radius w R hwpos hR).trans ?_
  apply (div_le_div_iff₀ (mul_pos Real.pi_pos hRpos)
    (mul_pos (by norm_num) Real.pi_pos)).mpr
  have hp := mul_nonneg
    (mul_nonneg (Real.exp_pos (1 - w)).le Real.pi_pos.le)
    (sub_nonneg.mpr hRfour)
  nlinarith

end
end SparseHamiltonian.ODEGaussianTail
