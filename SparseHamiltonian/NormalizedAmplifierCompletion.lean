import SparseHamiltonian.PolynomialCompletionReal

/-!
# Direct completion of the normalized positive-coefficient amplifier

Normalizing by the finite coefficient mass gives exact endpoint saturation.
Positive odd-power coefficients and the exterior Chebyshev bound then supply
both sides of real QSP admissibility. Consequently this explicit amplifier has
a constructed complementary polynomial and phase list without a real-part or
extra-ancilla reduction.
-/
namespace SparseHamiltonian.NormalizedAmplifierCompletion

noncomputable section
open Polynomial PolynomialUnitarity PolynomialCompletion
open FractionalAngleCoefficients
open scoped BigOperators

/-- The finite, input-independent normalization of the correction polynomial. -/
def mass (a : ℝ) (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, coefficient a k

/-- A nonempty prefix has mass between one and two. -/
theorem mass_bounds (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) (hN : 0 < N) :
    1 ≤ mass a N ∧ mass a N ≤ 2 := by
  constructor
  · have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.range N) =>
      coefficient_nonneg a ha k) (Finset.mem_range.mpr hN)
    simpa [mass] using h
  · exact sum_coefficient_le_two a ha N

/-- The normalization is strictly positive, so its inverse is legitimate. -/
theorem mass_pos (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) (hN : 0 < N) :
    0 < mass a N := lt_of_lt_of_le zero_lt_one (mass_bounds a ha N hN).1

/-- Positivity gives the exact absolute-value formula for the odd-power correction. -/
theorem correction_abs (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) (y : ℝ) :
    |(correction a N).eval y| =
      ∑ k ∈ Finset.range N, coefficient a k * |y| ^ (2 * k + 1) := by
  by_cases hy : 0 ≤ y
  · rw [correction_eval, abs_of_nonneg (Finset.sum_nonneg (fun k _ =>
      mul_nonneg (coefficient_nonneg a ha k) (pow_nonneg hy _))), abs_of_nonneg hy]
  · have hodd : (correction a N).eval y = -(correction a N).eval (-y) := by
      have h := congrArg (fun p : ℝ[X] => p.eval (-y)) (correction_parity a N)
      simpa using h
    rw [hodd, abs_neg, correction_eval,
      abs_of_nonneg (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (coefficient_nonneg a ha k) (pow_nonneg (by linarith : 0 ≤ -y) _))),
      abs_of_neg (lt_of_not_ge hy)]

/-- On the unit interval the correction is bounded by its own coefficient mass. -/
theorem correction_le_mass (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (y : ℝ) (hy : |y| ≤ 1) : |(correction a N).eval y| ≤ mass a N := by
  rw [correction_abs a ha N y]
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_of_le_one_right (coefficient_nonneg a ha k)
    (pow_le_one₀ (abs_nonneg y) hy)

/-- Outside the unit interval the positive correction is at least its mass. -/
theorem mass_le_correction (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (y : ℝ) (hy : 1 ≤ |y|) : mass a N ≤ |(correction a N).eval y| := by
  rw [correction_abs a ha N y]
  apply Finset.sum_le_sum
  intro k _
  exact le_mul_of_one_le_right (coefficient_nonneg a ha k) (one_le_pow₀ hy)

/-- The Chebyshev signal has magnitude at least one outside the physical interval. -/
theorem signal_exterior (k : ℕ) (x : ℝ) (hx : 1 ≤ |x|) :
    1 ≤ |(AmplifierPolynomialConstruction.signal k).eval x| := by
  simp only [AmplifierPolynomialConstruction.signal, eval_mul, eval_C, abs_mul,
    abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact Polynomial.Chebyshev.one_le_abs_eval_T_real _ hx

/-- Explicit polynomial with exact endpoint saturation and constant normalization. -/
def polynomial (a : ℝ) (k N : ℕ) : ℝ[X] :=
  C (mass a N)⁻¹ * (correction a N).comp (AmplifierPolynomialConstruction.signal k)

@[simp] theorem polynomial_eval (a : ℝ) (k N : ℕ) (x : ℝ) :
    (polynomial a k N).eval x =
      (correction a N).eval ((AmplifierPolynomialConstruction.signal k).eval x) / mass a N := by
  simp [polynomial, div_eq_mul_inv, mul_comm]

/-- Exact odd parity of the normalized composition. -/
theorem polynomial_parity (a : ℝ) (k N : ℕ) :
    (polynomial a k N).comp (-X) = -(polynomial a k N) := by
  unfold polynomial
  rw [mul_comp, C_comp, comp_assoc, AmplifierPolynomialConstruction.signal_parity]
  have he : (-X : ℝ[X]).comp (AmplifierPolynomialConstruction.signal k) =
      -(AmplifierPolynomialConstruction.signal k) := by simp
  rw [← he, ← comp_assoc, correction_parity, neg_comp]
  ring

/-- Degree is linear in signal order and correction cutoff. -/
theorem polynomial_degree (a : ℝ) (k N : ℕ) :
    (polynomial a k N).natDegree ≤ 2 * N * (2 * k + 1) := by
  unfold polynomial
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  apply natDegree_comp_le.trans
  exact Nat.mul_le_mul (correction_degree a N) (AmplifierPolynomialConstruction.signal_degree k)

/-- Upper admissibility bound on the physical interval. -/
theorem polynomial_bounded (a : ℝ) (ha : |a| ≤ 1) (k N : ℕ) (hN : 0 < N)
    (x : ℝ) (hx : |x| ≤ 1) : |(polynomial a k N).eval x| ≤ 1 := by
  rw [polynomial_eval, abs_div, abs_of_pos (mass_pos a ha N hN)]
  apply (div_le_one (mass_pos a ha N hN)).mpr
  exact correction_le_mass a ha N _ (AmplifierPolynomialConstruction.signal_bounded k x hx)

/-- Exterior admissibility follows from positivity, without a separate approximation. -/
theorem polynomial_exterior (a : ℝ) (ha : |a| ≤ 1) (k N : ℕ) (hN : 0 < N)
    (x : ℝ) (hx : 1 ≤ |x|) : 1 ≤ |(polynomial a k N).eval x| := by
  rw [polynomial_eval, abs_div, abs_of_pos (mass_pos a ha N hN)]
  apply (one_le_div (mass_pos a ha N hN)).mpr
  exact mass_le_correction a ha N _ (signal_exterior k x hx)

/-- The complementary polynomial is constructed for every nonempty truncation. -/
theorem completion (a : ℝ) (ha : |a| ≤ 1) (k N : ℕ) (hN : 0 < N) :
    ∃ q : ℂ[X], IsNormalized (complexify (polynomial a k N)) q ∧
      q.comp (-X) = q ∧ q.natDegree ≤ 2 * (N * (2 * k + 1)) := by
  apply PolynomialCompletionReal.completion (polynomial a k N) (N * (2 * k + 1))
  · have h := polynomial_degree a k N
    rw [Nat.mul_assoc] at h
    omega
  · exact polynomial_parity a k N
  · exact polynomial_bounded a ha k N hN
  · exact polynomial_exterior a ha k N hN

/-- Exact native phase count from the fully constructed normalized amplifier. -/
theorem phase_list (a : ℝ) (ha : |a| ≤ 1) (k N : ℕ) (hN : 0 < N) :
    ∃ v u : AmplitudePolynomialSequence.UnitPhase,
      ∃ ss : List AmplitudePolynomialSequence.Phases,
      ss.length = N * (2 * k + 1) ∧ complexify (polynomial a k N) =
        C ((v : ℂ) * (u : ℂ)) * (AmplitudePolynomialSequence.polynomials ss).1 := by
  apply PolynomialCompletionReal.phase_list (polynomial a k N) (N * (2 * k + 1))
  · have h := polynomial_degree a k N
    rw [Nat.mul_assoc] at h
    omega
  · exact polynomial_parity a k N
  · exact polynomial_bounded a ha k N hN
  · exact polynomial_exterior a ha k N hN

end
end SparseHamiltonian.NormalizedAmplifierCompletion
