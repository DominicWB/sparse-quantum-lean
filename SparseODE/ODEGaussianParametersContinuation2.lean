import SparseODE.ODEGaussianFiniteTable

/-!
# Gaussian integral error allocation

The selected width is large enough for the integrated Cauchy-tail bound.
The two remaining exponential contributions add to exactly the public
precision budget. These are scalar identities, independent of any contour
representation of the evolution operator.

-/

namespace SparseHamiltonian.ODEGaussianParameters

noncomputable section

theorem width_ge_two (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    2 ≤ width g ε := by
  have hg0 : 0 < g := by linarith
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hArgument : 0 < 10000 * g / ε := by positivity
  have hInverse : 10000 * g / ε = 1 / ImprovedODEQueryBudget.precision g ε := by
    unfold ImprovedODEQueryBudget.precision
    field_simp [hg0.ne', hε.ne']
  have hComparison : 10000 * g / ε ≤
      (1 + 1 / (2 * Real.pi)) / ImprovedODEQueryBudget.precision g ε := by
    rw [hInverse]
    apply div_le_div_of_nonneg_right _ hν.le
    have hpi : 0 ≤ 1 / (2 * Real.pi) := by positivity
    linarith
  have hLog := Real.log_le_log hArgument hComparison
  have hBudget := ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hεOne
  unfold ImprovedODEQueryBudget.logBudget at hBudget
  unfold width
  linarith

theorem radius_ge_four (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    4 ≤ ImprovedODEQueryBudget.radius g ε := by
  have hw := width_ge_two g ε hg hε hεOne
  have hR := cutoff_le_radius g ε hg hε hεOne
  linarith

/-- The tail allowance and the proposed shifted-contour allowance together
equal the chosen public precision; neither allowance is assumed proved here. -/
theorem integral_error_budget (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    Real.exp (1 - width g ε) / (2 * Real.pi) + Real.exp (1 - width g ε) =
      ImprovedODEQueryBudget.precision g ε := by
  have hc : (1 + 1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
  calc
    _ = Real.exp (1 - width g ε) * (1 + 1 / (2 * Real.pi)) := by ring
    _ = _ := by rw [residual_factor g ε hg hε, div_mul_cancel₀ _ hc]

end
end SparseHamiltonian.ODEGaussianParameters
