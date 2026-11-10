import OptimalSparseSimulation.Regimes
import SparseHamiltonian.ImprovedPrecisionBudget

set_option autoImplicit false

/-!
# Scalar comparisons for the regimes of Theorem `hs:thm:two-norm`

With `σ = sμ²/η²`, `θ = η²|t|/μ`, `L = log(1/ε)`, `h_μ = log(e + L/θ)` and `r_μ = L/h_μ`
(`hs:eq:two-norm-parameters`):

* `bounded_shape_le`: for `h_μ < 10⁴`, the bound `√σ θ + √(σθ ℓ) + ℓ` of the baseline Cayley
  simulation, with `ℓ = log(2/ε)`, is at most `1.2·10⁴ (√σ θ + √(σθ r_μ) + r_μ)`.
-/

namespace TwoNormSimulation

noncomputable section

open SparseHamiltonian LargeSparsityCore.Parameters OptimalSparseSimulation

/-- `log(2/ε) ≤ (7/6) log(1/ε)` for `ε ≤ 1/64`. -/
theorem targetLog_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    ImprovedPrecisionBudget.targetLog ε ≤ 7 / 6 * Lval ε := by
  unfold ImprovedPrecisionBudget.targetLog Lval
  have h2 : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
    rw [show (2 : ℝ) / ε = 2 * (1 / ε) by ring, Real.log_mul (by norm_num) (by positivity)]
  have h64 : 6 * Real.log 2 ≤ Real.log (1 / ε) := by
    have : Real.log 64 = 6 * Real.log 2 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      norm_num
    rw [← this]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hε]
    linarith
  rw [h2]
  linarith

/-- **Bounded `h_μ`.** For `h_μ < 10⁴`, `√σ θ + √(σθ ℓ) + ℓ ≤ 1.2·10⁴ (√σ θ + √(σθ r_μ) + r_μ)`
with `ℓ = log(2/ε)`. -/
theorem bounded_shape_le {σ θ ε : ℝ} (hσ : 0 ≤ σ) (hθ : 1 ≤ θ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hh : hval θ ε < 10 ^ 4) :
    ImprovedPrecisionBudget.shape σ θ (ImprovedPrecisionBudget.targetLog ε) ≤
      12000 * (Real.sqrt σ * θ + Real.sqrt (σ * θ * rval θ ε) + rval θ ε) := by
  have hr := r_pos hθ hε hε1
  have hh0 := h_pos hθ hε hε1
  have hL := L_eq hθ hε hε1
  have hℓ := targetLog_le hε hε1
  have hℓ0 : 0 ≤ ImprovedPrecisionBudget.targetLog ε := by
    unfold ImprovedPrecisionBudget.targetLog
    apply Real.log_nonneg
    rw [le_div_iff₀ hε]
    linarith
  have hσθ : 0 ≤ σ * θ := mul_nonneg hσ (by linarith)
  have hℓr : ImprovedPrecisionBudget.targetLog ε ≤ 12000 * rval θ ε := by
    have : Lval ε ≤ 10 ^ 4 * rval θ ε := by
      rw [hL]
      exact mul_le_mul_of_nonneg_right hh.le hr.le
    linarith
  unfold ImprovedPrecisionBudget.shape
  have h1 : Real.sqrt (σ * θ * ImprovedPrecisionBudget.targetLog ε) ≤
      110 * Real.sqrt (σ * θ * rval θ ε) := by
    have h110 : (110 : ℝ) = Real.sqrt 12100 := by
      rw [show (12100 : ℝ) = 110 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h110, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    have := mul_le_mul_of_nonneg_left hℓr hσθ
    nlinarith
  have h2 : 0 ≤ Real.sqrt σ * θ := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have h3 := Real.sqrt_nonneg (σ * θ * rval θ ε)
  nlinarith

end

end TwoNormSimulation
