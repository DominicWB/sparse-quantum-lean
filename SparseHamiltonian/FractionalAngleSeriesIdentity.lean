import SparseHamiltonian.FractionalSineSeries

/-!
# Identification of the explicit fractional-angle coefficient series

Termwise differentiation and the coefficient recurrence give the fractional
Chebyshev equation. Conserved-energy uniqueness then identifies the actual
series with `sin(a * arcsin y) / a`, without assuming that identity.
-/
namespace SparseHamiltonian.FractionalAngleSeriesIdentity
noncomputable section
open FractionalAngleCoefficients FractionalAngleSeriesDifferentiation
open scoped BigOperators

/-- Clear the strictly positive recurrence denominators. -/
theorem coefficient_recurrence (a : ℝ) (k : ℕ) :
    coefficient a (k + 1) * (2 * (k : ℝ) + 3) * (2 * k + 2) =
      coefficient a k * ((2 * (k : ℝ) + 1) ^ 2 - a ^ 2) := by
  rw [coefficient]
  have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  field_simp

/-- Reindexing the second derivative multiplies it by the square of the signal. -/
theorem second_shift (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    (∑' k : ℕ, coefficient a k * (2 * (k : ℝ) + 1) * (2 * k) * y ^ (2 * k + 1)) =
      y ^ 2 * secondDerivative a y := by
  let q : ℕ → ℝ := fun k => coefficient a k * (2 * (k : ℝ) + 1) * (2 * k) * y ^ (2 * k + 1)
  have hshift (k : ℕ) : q (k + 1) = y ^ 2 *
      (coefficient a (k + 1) * (2 * (k : ℝ) + 3) * (2 * k + 2) * y ^ (2 * k + 1)) := by
    dsimp [q]
    push_cast
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
    ring
  have htail : Summable (fun k => q (k + 1)) := by
    simp_rw [hshift]
    exact (summable_second a ha y hy).mul_left _
  have hq : Summable q := (summable_nat_add_iff 1).mp htail
  change (∑' k, q k) = _
  rw [hq.tsum_eq_zero_add]
  simp only [q, Nat.cast_zero, mul_zero, zero_mul, zero_add]
  change (∑' k, q (k + 1)) = _
  simp_rw [hshift]
  rw [tsum_mul_left]
  rfl

/-- The actual convergent series, not merely its formal coefficients, solves the ODE. -/
theorem series_ode (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    (1 - y ^ 2) * secondDerivative a y - y * firstDerivative a y + a ^ 2 * series a y = 0 := by
  let q : ℕ → ℝ := fun k => coefficient a k * (2 * (k : ℝ) + 1) * (2 * k) * y ^ (2 * k + 1)
  have hq : Summable q := by
    apply (summable_nat_add_iff 1).mp
    apply ((summable_second a ha y hy).mul_left (y ^ 2)).congr
    intro k
    dsimp [q]
    push_cast
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, pow_add]
    ring
  have hf := (summable_first a ha y hy).mul_left y
  have hs := (summable_series a ha y hy.le).mul_left (a ^ 2)
  have hid : secondDerivative a y = (∑' k, q k) + y * firstDerivative a y - a ^ 2 * series a y := by
    calc
      secondDerivative a y = ∑' k : ℕ, (q k +
          y * (coefficient a k * (2 * (k : ℝ) + 1) * y ^ (2 * k)) -
          a ^ 2 * (coefficient a k * y ^ (2 * k + 1))) := by
        unfold secondDerivative
        apply tsum_congr
        intro k
        rw [coefficient_recurrence]
        dsimp [q]
        rw [pow_succ]
        ring
      _ = _ := by
        rw [(hq.add hf).tsum_sub hs, hq.tsum_add hf, tsum_mul_left, tsum_mul_left]
        rfl
  rw [show (∑' k, q k) = y ^ 2 * secondDerivative a y from second_shift a ha y hy] at hid
  nlinarith

/-- Kernel-checked analytic identification of the explicit coefficient sequence. -/
theorem series_eq_target (a : ℝ) (ha : |a| ≤ 1) (ha0 : a ≠ 0)
    (y : ℝ) (hy : |y| < 1) :
    series a y = Real.sin (a * Real.arcsin y) / a :=
  FractionalSineSeries.eq_target_of_ode a ha0 (series a) (firstDerivative a) (secondDerivative a)
    (hasDerivAt_series a ha) (hasDerivAt_firstDerivative a ha) (series_ode a ha)
    (series_zero a) (firstDerivative_zero a ha) y hy

end
end SparseHamiltonian.FractionalAngleSeriesIdentity
