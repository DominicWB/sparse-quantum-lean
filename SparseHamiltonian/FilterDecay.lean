import SparseHamiltonian.OperatorPolynomial

/-!
# Exponential operator decay of the averaging filter

Contractivity, the geometric factorisation, and Cauchy's estimates for inverse
powers give an operator-norm filter bound directly. The inverse at one is
constructed from the resolvent-disk premise. No contour identity or normality
hypothesis is assumed.
-/

namespace SparseHamiltonian.FilterDecay

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-- A uniform resolvent bound in the radius-`r` disk gives exponential decay of
the actual repeated averaging polynomial on a contraction. -/
theorem filter_norm_le (D : V →L[ℂ] V) (L k : ℕ) (r M : ℝ)
    (hr : 0 < r) (hL : 0 < L) (hk : 0 < k) (hD : ‖D‖ ≤ 1)
    (hdisk : ∀ z : ℂ, ‖z - 1‖ ≤ r → ∃ S : V →L[ℂ] V,
      (z • (1 : V →L[ℂ] V) - D) * S = 1 ∧
      S * (z • (1 : V →L[ℂ] V) - D) = 1 ∧ ‖S‖ ≤ M) :
    ‖averagedGeometricFilter D L ^ k‖ ≤ M * r * (2 / ((L : ℝ) * r)) ^ k := by
  obtain ⟨R, hRight, hLeft, _⟩ := hdisk 1 (by simpa using hr.le)
  simp only [one_smul] at hRight hLeft
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  have hp := OperatorFilter.inverse_power_norm_le_of_resolvent_disk D R r M hr
    hRight hLeft hdisk n
  have hLreal : (0 : ℝ) < L := by exact_mod_cast hL
  calc
    ‖averagedGeometricFilter D L ^ (n + 1)‖ ≤
        (2 / (L : ℝ)) ^ (n + 1) * ‖R ^ (n + 1)‖ :=
      OperatorPolynomial.filter_norm_le_inverse_power D R L (n + 1) hD hRight hLeft
    _ ≤ (2 / (L : ℝ)) ^ (n + 1) * (M / r ^ n) := by gcongr
    _ = M * r * (2 / ((L : ℝ) * r)) ^ (n + 1) := by
      rw [div_pow, div_pow, mul_pow, pow_succ r]
      field_simp

/-- At the clock length `L ≥ 32Q`, the filter has decay factor at most one
quarter per repetition, including for the zero-dimensional Hilbert space. -/
theorem filter_norm_le_clock_scale (D : V →L[ℂ] V) (L k : ℕ) (Q M : ℝ)
    (hQ : 0 < Q) (hL : 32 * Q ≤ (L : ℝ)) (hk : 0 < k) (hD : ‖D‖ ≤ 1)
    (hdisk : ∀ z : ℂ, ‖z - 1‖ ≤ 1 / (4 * Q) → ∃ S : V →L[ℂ] V,
      (z • (1 : V →L[ℂ] V) - D) * S = 1 ∧
      S * (z • (1 : V →L[ℂ] V) - D) = 1 ∧ ‖S‖ ≤ M) :
    ‖averagedGeometricFilter D L ^ k‖ ≤ (M / (4 * Q)) * (1 / 4 : ℝ) ^ k := by
  have hr : 0 < 1 / (4 * Q) := by positivity
  have hLreal : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL
  have hLnat : 0 < L := by exact_mod_cast hLreal
  obtain ⟨R, _, _, hRM⟩ := hdisk 1 (by simpa using hr.le)
  have hM : 0 ≤ M := (norm_nonneg R).trans hRM
  have hratio : 2 / ((L : ℝ) * (1 / (4 * Q))) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (mul_pos hLreal hr)).mpr
    have hden : 0 < 4 * Q := by positivity
    have hs : 8 ≤ (L : ℝ) / (4 * Q) := (le_div_iff₀ hden).mpr (by nlinarith)
    nlinarith [show (L : ℝ) * (1 / (4 * Q)) = (L : ℝ) / (4 * Q) by ring]
  calc
    ‖averagedGeometricFilter D L ^ k‖ ≤
        M * (1 / (4 * Q)) * (2 / ((L : ℝ) * (1 / (4 * Q)))) ^ k :=
      filter_norm_le D L k _ M hr hLnat hk hD hdisk
    _ ≤ M * (1 / (4 * Q)) * (1 / 4 : ℝ) ^ k := by
      apply mul_le_mul_of_nonneg_left
      · exact pow_le_pow_left₀ (by positivity) hratio k
      · positivity
    _ = (M / (4 * Q)) * (1 / 4 : ℝ) ^ k := by ring

end SparseHamiltonian.FilterDecay
