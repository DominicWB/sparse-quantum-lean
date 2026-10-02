import SparseODE.ODEGaussianKernelContinuation2

/-!
# Public Gaussian width and frequency cutoff

The width is beta squared in the Gaussian kernel. These scalar identities
fix its dependence on the already verified ODE precision allocation and
cutoff. They do not assert a contour formula for the propagator.

-/

namespace SparseHamiltonian.ODEGaussianParameters

noncomputable section

/-- Squared Gaussian width at the public error allocation. -/
def width (g ε : ℝ) : ℝ :=
  1 + Real.log ((1 + 1 / (2 * Real.pi)) / ImprovedODEQueryBudget.precision g ε)

theorem width_ge_one (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    1 ≤ width g ε := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hνOne := ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne
  have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have harg : 1 ≤ (1 + 1 / (2 * Real.pi)) /
      ImprovedODEQueryBudget.precision g ε := by
    apply (le_div_iff₀ hν).2
    linarith
  have hl := Real.log_nonneg harg
  unfold width
  linarith

theorem width_pos (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < width g ε := lt_of_lt_of_le (by norm_num) (width_ge_one g ε hg hε hεOne)

/-- The chosen public radius contains the Gaussian cutoff `2 beta^2`. -/
theorem cutoff_le_radius (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    2 * width g ε ≤ ImprovedODEQueryBudget.radius g ε :=
  ImprovedODEQueryBudget.gaussian_radius_le g ε hg hε hεOne

/-- Exact exponential factor entering the later tail and contour estimates.
This scalar identity alone is not a truncation-error theorem. -/
theorem residual_factor (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    Real.exp (1 - width g ε) =
      ImprovedODEQueryBudget.precision g ε / (1 + 1 / (2 * Real.pi)) := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hc : 0 < 1 + 1 / (2 * Real.pi) := by positivity
  have heq : 1 - width g ε =
      -Real.log ((1 + 1 / (2 * Real.pi)) / ImprovedODEQueryBudget.precision g ε) := by
    unfold width
    ring
  rw [heq, Real.exp_neg, Real.exp_log (div_pos hc hν), inv_div]

end
end SparseHamiltonian.ODEGaussianParameters
