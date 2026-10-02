import SparseODE.ODEGaussianKernel

/-!
# Constant mass bound for the Gaussian LCHS density

The complex phase of the density has unit modulus.  Its magnitude is
bounded by a scaled Cauchy density, whose finite-interval integral is
computed from the arctangent derivative.  This proves the mass input of
the public quadrature theorem without assuming an integral representation
for the ODE propagator or an error-function formula.

Requires Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv.
-/

namespace SparseHamiltonian.ODEGaussianMass

noncomputable section
open scoped Interval

/-- The elementary Cauchy envelope is continuous on the whole real line. -/
theorem cauchy_continuous (C : ℝ) :
    Continuous (fun k : ℝ => C / (Real.pi * (1 + k ^ 2))) := by
  apply continuous_const.div
    (continuous_const.mul (continuous_const.add (continuous_id.pow 2)))
  intro k
  exact ne_of_gt (ODEGaussianKernel.denominator_pos k)

/-- Exact integration of a scalar multiple of the normalized Cauchy
density, using the fundamental theorem of calculus. -/
theorem cauchy_integral (C a b : ℝ) :
    (∫ k in a..b, C / (Real.pi * (1 + k ^ 2))) =
      (C / Real.pi) * (Real.arctan b - Real.arctan a) := by
  have hderiv (k : ℝ) :
      HasDerivAt (fun y : ℝ => (C / Real.pi) * Real.arctan y)
        (C / (Real.pi * (1 + k ^ 2))) k := by
    simpa only [div_eq_mul_inv, mul_inv_rev, one_mul,
      mul_assoc, mul_comm, mul_left_comm] using
      (Real.hasDerivAt_arctan k).const_mul (C / Real.pi)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun k (_ : k ∈ Set.uIcc a b) => hderiv k)
    ((cauchy_continuous C).intervalIntegrable
      (μ := MeasureTheory.volume) a b)
  calc
    _ = (C / Real.pi) * Real.arctan b -
        (C / Real.pi) * Real.arctan a := h
    _ = _ := by ring

/-- Every oriented finite-interval integral of a nonnegative Cauchy
envelope is bounded by its full-line mass. -/
theorem cauchy_integral_le (C a b : ℝ) (hC : 0 ≤ C) :
    (∫ k in a..b, C / (Real.pi * (1 + k ^ 2))) ≤ C := by
  rw [cauchy_integral]
  have hangle : Real.arctan b - Real.arctan a ≤ Real.pi := by
    have hUpper := Real.arctan_lt_pi_div_two b
    have hLower := Real.neg_pi_div_two_lt_arctan a
    linarith
  calc
    _ ≤ (C / Real.pi) * Real.pi :=
      mul_le_mul_of_nonneg_left hangle (div_nonneg hC Real.pi_pos.le)
    _ = C := div_mul_cancel₀ C Real.pi_ne_zero

/-- A uniform bound for the truncated Gaussian coefficient mass. -/
theorem kernel_mass_le_exp (w R : ℝ) (hw : 0 < w) (hR : 0 ≤ R) :
    (∫ k in (-R)..R, ‖ODEGaussianKernel.kernel w k‖) ≤ Real.exp 1 := by
  have horder : -R ≤ R := by linarith
  calc
    _ ≤ ∫ k in (-R)..R, Real.exp 1 / (Real.pi * (1 + k ^ 2)) := by
      apply intervalIntegral.integral_mono_on horder
        ((ODEGaussianKernel.kernel_continuous w).norm.intervalIntegrable
          (μ := MeasureTheory.volume) (-R) R)
        ((cauchy_continuous (Real.exp 1)).intervalIntegrable
          (μ := MeasureTheory.volume) (-R) R)
      intro k _
      exact ODEGaussianKernel.norm_kernel_le_cauchy w k hw
    _ ≤ Real.exp 1 := cauchy_integral_le _ _ _ (Real.exp_pos _).le

/-- A rational upper bound with enough slack for finite-grid error.
This uses the same scalar Taylor remainder estimate as the verified
Cayley approximation, rather than a numerical oracle. -/
theorem exp_one_le_eleven_fourths : Real.exp 1 ≤ (11 / 4 : ℝ) := by
  have h := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (1 : ℝ) ≤ 1) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The continuous density leaves room for the full quadrature precision
while keeping the padded finite coefficient mass equal to three. -/
theorem kernel_mass_budget (w R g ε : ℝ)
    (hw : 0 < w) (hR : 0 ≤ R) (hg : 1 ≤ g) (hε1 : ε ≤ 1) :
    (∫ k in (-R)..R, ‖ODEGaussianKernel.kernel w k‖) ≤
      3 - ImprovedODEQueryBudget.precision g ε := by
  have hMass := kernel_mass_le_exp w R hw hR
  have he := exp_one_le_eleven_fourths
  have hν := ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hε1
  linarith

end
end SparseHamiltonian.ODEGaussianMass
