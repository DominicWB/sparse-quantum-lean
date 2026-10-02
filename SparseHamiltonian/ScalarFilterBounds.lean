import SparseHamiltonian.TransferConnection

/-!
# Scalar estimates for the contour filter

The geometric average is at most one half when the radius is at most
`1 + 1/L` and the separation from one obeys `L * ‖1-z‖ ≥ 8`.
Its `k`th power consequently decays as `2⁻ᵏ`. This module concerns scalar
polynomial values; it does not assert a contour functional-calculus estimate.
-/

namespace SparseHamiltonian.ScalarFilterBounds

open scoped BigOperators
open FilterCoefficients

/-- The finite geometric cancellation underlying the contour estimate. -/
theorem average_cancellation (L : ℕ) (z : ℂ) :
    ((L : ℂ) * FilterCoefficients.geometricAverage L z) * (1 - z) = 1 - z ^ L := by
  rw [length_mul_geometricAverage]
  exact geom_sum_mul_neg z L

/-- A denominator-free norm estimate, valid even for `L=0` or `z=1`. -/
theorem average_norm_mul_le (L : ℕ) (z : ℂ) :
    (L : ℝ) * ‖FilterCoefficients.geometricAverage L z‖ * ‖1 - z‖ ≤ 1 + ‖z‖ ^ L := by
  have h := congrArg norm (average_cancellation L z)
  simp only [norm_mul, Complex.norm_natCast] at h
  calc
    _ = ‖1 - z ^ L‖ := h
    _ ≤ ‖(1 : ℂ)‖ + ‖z ^ L‖ := norm_sub_le _ _
    _ = 1 + ‖z‖ ^ L := by rw [norm_one, norm_pow]

theorem average_norm_le_fraction (L : ℕ) (hL : 1 ≤ L) (z : ℂ)
    (hz : z ≠ 1) :
    ‖FilterCoefficients.geometricAverage L z‖ ≤ (1 + ‖z‖ ^ L) / ((L : ℝ) * ‖1 - z‖) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hzpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz.symm)
  apply (le_div_iff₀ (mul_pos hLpos hzpos)).mpr
  nlinarith [average_norm_mul_le L z]

/-- The elementary exponential bound controls the outer contour radius. -/
theorem radius_power_le_three (L : ℕ) (z : ℂ)
    (hradius : ‖z‖ ≤ 1 + (L : ℝ)⁻¹) : ‖z‖ ^ L ≤ 3 := by
  calc
    ‖z‖ ^ L ≤ (1 + (L : ℝ)⁻¹) ^ L :=
      pow_le_pow_left₀ (norm_nonneg z) hradius L
    _ ≤ Real.exp 1 := Real.one_add_inv_pow_le_exp
    _ ≤ 3 := Real.exp_one_lt_three.le

/-- An abstract radius-power bound and separation suffice for half-decay. -/
theorem average_norm_le_half_of_power (L : ℕ) (z : ℂ)
    (hpower : ‖z‖ ^ L ≤ 3) (hseparation : 8 ≤ (L : ℝ) * ‖1 - z‖) :
    ‖FilterCoefficients.geometricAverage L z‖ ≤ (1 / 2 : ℝ) := by
  have h := mul_le_mul_of_nonneg_right hseparation (norm_nonneg (FilterCoefficients.geometricAverage L z))
  nlinarith [average_norm_mul_le L z]

/-- Scalar half-decay on the radius-and-separation contour region. -/
theorem average_norm_le_half (L : ℕ) (z : ℂ)
    (hradius : ‖z‖ ≤ 1 + (L : ℝ)⁻¹)
    (hseparation : 8 ≤ (L : ℝ) * ‖1 - z‖) :
    ‖FilterCoefficients.geometricAverage L z‖ ≤ (1 / 2 : ℝ) :=
  average_norm_le_half_of_power L z (radius_power_le_three L z hradius) hseparation

/-- The clock-scale separation and a length at least `32Q` imply the scalar
separation condition used by the filter estimate. -/
theorem clock_scale_separation (L : ℕ) (Q : ℝ) (hQ : 0 < Q) (z : ℂ)
    (hL : 32 * Q ≤ (L : ℝ)) (hz : 1 / (4 * Q) ≤ ‖1 - z‖) :
    8 ≤ (L : ℝ) * ‖1 - z‖ := by
  have hdenom : 0 < 4 * Q := by positivity
  have hsep := (div_le_iff₀ hdenom).mp hz
  have hlength := mul_le_mul_of_nonneg_right hL (norm_nonneg (1 - z))
  nlinarith

theorem average_norm_le_half_of_clock_scale (L : ℕ) (Q : ℝ) (hQ : 0 < Q)
    (z : ℂ) (hL : 32 * Q ≤ (L : ℝ))
    (hradius : ‖z‖ ≤ 1 + (L : ℝ)⁻¹) (hz : 1 / (4 * Q) ≤ ‖1 - z‖) :
    ‖FilterCoefficients.geometricAverage L z‖ ≤ (1 / 2 : ℝ) :=
  average_norm_le_half L z hradius (clock_scale_separation L Q hQ z hL hz)

/-- Repetition gives exponential decay in the filter repetition count. -/
theorem average_power_norm_le (L k : ℕ) (z : ℂ)
    (hradius : ‖z‖ ≤ 1 + (L : ℝ)⁻¹)
    (hseparation : 8 ≤ (L : ℝ) * ‖1 - z‖) :
    ‖FilterCoefficients.geometricAverage L z ^ k‖ ≤ (1 / 2 : ℝ) ^ k := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (average_norm_le_half L z hradius hseparation) k

/-- The decay estimate applies to the concrete real-coefficient polynomial. -/
theorem filter_eval_norm_le (L k : ℕ) (z : ℂ)
    (hradius : ‖z‖ ≤ 1 + (L : ℝ)⁻¹)
    (hseparation : 8 ≤ (L : ℝ) * ‖1 - z‖) :
    ‖(AveragingPolynomial.filter L k).eval₂ (algebraMap ℝ ℂ) z‖ ≤
      (1 / 2 : ℝ) ^ k := by
  rw [AveragingPolynomial.filter_eval₂]
  exact average_power_norm_le L k z hradius hseparation

end SparseHamiltonian.ScalarFilterBounds
