import SparseHamiltonian.GlobalResolvent

/-!
# Averaging filters through powers of the inverse at one

The exact geometric cancellation reduces operator filter decay to bounds on
powers of the inverse of `1-D`. All identities allow noncommutative algebras.
-/

namespace SparseHamiltonian.AveragingResolvent

open scoped BigOperators
open FilterCoefficients

section Algebra

variable {A : Type*} [Ring A] [Algebra ℂ A]

omit [Algebra ℂ A] in
/-- A two-sided inverse of `1-D` commutes with `D`. -/
theorem commute_inverse (D R : A) (hRight : (1 - D) * R = 1)
    (hLeft : R * (1 - D) = 1) : Commute D R := by
  have hRight' : R - D * R = 1 := by simpa only [sub_mul, one_mul] using hRight
  have hLeft' : R - R * D = 1 := by simpa only [mul_sub, mul_one] using hLeft
  show D * R = R * D
  apply neg_injective
  apply add_left_cancel (a := R)
  simpa only [sub_eq_add_neg] using hRight'.trans hLeft'.symm

omit [Algebra ℂ A] in
/-- The geometric sum factors through any right inverse of `1-D`. -/
theorem geometricSum_eq (D R : A) (L : ℕ) (hRight : (1 - D) * R = 1) :
    FilterCoefficients.geometricSum L D = (1 - D ^ L) * R := by
  calc
    FilterCoefficients.geometricSum L D = FilterCoefficients.geometricSum L D * ((1 - D) * R) := by rw [hRight, mul_one]
    _ = (1 - D ^ L) * R := by rw [← mul_assoc]; exact congrArg (· * R) (geom_sum_mul_neg D L)

/-- Exact factorisation of one averaging filter. -/
theorem average_eq (D R : A) (L : ℕ) (hRight : (1 - D) * R = 1) :
    operatorGeometricAverage (K := ℂ) L D =
      (L : ℂ)⁻¹ • ((1 - D ^ L) * R) := by
  rw [operatorGeometricAverage, geometricSum_eq D R L hRight]

/-- Exact factorisation of the repeated filter, including exponent zero. -/
theorem average_pow_eq (D R : A) (L k : ℕ)
    (hRight : (1 - D) * R = 1) (hLeft : R * (1 - D) = 1) :
    operatorGeometricAverage (K := ℂ) L D ^ k =
      ((L : ℂ)⁻¹) ^ k • ((1 - D ^ L) ^ k * R ^ k) := by
  have hc : Commute (1 - D ^ L) R :=
    ((Commute.one_right R).sub_right ((commute_inverse D R hRight hLeft).symm.pow_right L)).symm
  rw [average_eq D R L hRight, smul_pow, hc.mul_pow]

end Algebra

section Norm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [NormOneClass A]

/-- Only the inverse-power factor needs analytic control. -/
theorem average_pow_norm_le (D R : A) (L k : ℕ) (hD : ‖D‖ ≤ 1)
    (hRight : (1 - D) * R = 1) (hLeft : R * (1 - D) = 1) :
    ‖operatorGeometricAverage (K := ℂ) L D ^ k‖ ≤
      (2 / (L : ℝ)) ^ k * ‖R ^ k‖ := by
  have hterm : ‖1 - D ^ L‖ ≤ 2 := by
    calc
      ‖1 - D ^ L‖ ≤ ‖(1 : A)‖ + ‖D ^ L‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (le_of_eq norm_one)
        (OperatorResolvent.contraction_pow_norm D hD L)
      _ = 2 := by norm_num
  rw [average_pow_eq D R L k hRight hLeft, norm_smul, norm_pow, norm_inv,
    Complex.norm_natCast]
  calc
    _ ≤ ((L : ℝ)⁻¹) ^ k * (‖(1 - D ^ L) ^ k‖ * ‖R ^ k‖) := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((L : ℝ)⁻¹) ^ k * (2 ^ k * ‖R ^ k‖) := by
      gcongr
      exact (norm_pow_le _ k).trans (pow_le_pow_left₀ (norm_nonneg _) hterm k)
    _ = _ := by rw [← mul_assoc, ← mul_pow]; congr 2; ring

end Norm

end SparseHamiltonian.AveragingResolvent
