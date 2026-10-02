import SparseHamiltonian.OperatorFilter

/-!
# The actual averaging polynomial evaluated on operators

This connects the real coefficient list used by signed LCU to the repeated
complex-scalar operator average used in the analytic bound.
-/

namespace SparseHamiltonian.OperatorPolynomial

open scoped BigOperators
open Polynomial FilterCoefficients

section RealAlgebra

variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem average_aeval (L : ℕ) (D : A) :
    aeval D (AveragingPolynomial.average L) =
      operatorGeometricAverage (K := ℝ) L D := by
  simp only [AveragingPolynomial.average, map_mul, map_sum, map_pow,
    aeval_C, aeval_X, operatorGeometricAverage, FilterCoefficients.geometricSum, Algebra.smul_def]

theorem filter_aeval (L k : ℕ) (D : A) :
    aeval D (AveragingPolynomial.filter L k) =
      operatorGeometricAverage (K := ℝ) L D ^ k := by
  rw [AveragingPolynomial.filter, map_pow, average_aeval]

theorem filter_operator_coefficient_sum (L k : ℕ) (D : A) :
    (∑ j ∈ Finset.range (k * (L - 1) + 1),
      (AveragingPolynomial.filter L k).coeff j • D ^ j) =
        operatorGeometricAverage (K := ℝ) L D ^ k := by
  have h := congrArg (aeval D) (AveragingPolynomial.filter_eq_coefficient_sum L k)
  simpa only [filter_aeval, map_sum, map_mul, map_pow, aeval_C, aeval_X,
    Algebra.smul_def] using h.symm

end RealAlgebra

section Operators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem complex_average_eq (L : ℕ) (D : V →L[ℂ] V) :
    operatorGeometricAverage (K := ℂ) L D = averagedGeometricFilter D L := rfl

theorem real_average_eq (L : ℕ) (D : V →L[ℂ] V) :
    operatorGeometricAverage (K := ℝ) L D = averagedGeometricFilter D L := by
  simp only [operatorGeometricAverage, averagedGeometricFilter, FilterCoefficients.geometricSum]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
  exact (Complex.coe_smul _ _).symm

theorem filter_operator_eq (L k : ℕ) (D : V →L[ℂ] V) :
    (∑ j ∈ Finset.range (k * (L - 1) + 1),
      (AveragingPolynomial.filter L k).coeff j • D ^ j) =
        averagedGeometricFilter D L ^ k := by
  rw [filter_operator_coefficient_sum, real_average_eq]

/-- The inverse-power bound applies also to the zero-dimensional operator space. -/
theorem filter_norm_le_inverse_power (D R : V →L[ℂ] V) (L k : ℕ) (hD : ‖D‖ ≤ 1)
    (hRight : (1 - D) * R = 1) (hLeft : R * (1 - D) = 1) :
    ‖averagedGeometricFilter D L ^ k‖ ≤ (2 / (L : ℝ)) ^ k * ‖R ^ k‖ := by
  rcases subsingleton_or_nontrivial V with h | h
  · letI := h
    have hzero : averagedGeometricFilter D L ^ k = 0 := Subsingleton.elim _ _
    rw [hzero, norm_zero]
    positivity
  · letI := h
    exact AveragingResolvent.average_pow_norm_le D R L k hD hRight hLeft

end Operators

end SparseHamiltonian.OperatorPolynomial
