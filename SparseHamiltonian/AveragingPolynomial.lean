import SparseHamiltonian.FilterCoefficients

/-!
# Coefficients of the repeated averaging filter

The actual polynomial power has nonnegative coefficients, total mass one,
and reflection symmetry about degree `k * (L - 1)`. These facts discharge
the coefficient hypotheses in the signed-LCU smoothing normalization.
-/

namespace SparseHamiltonian.AveragingPolynomial

open scoped BigOperators
open Polynomial

/-- The length-`L` geometric average as a real polynomial. -/
noncomputable def average (L : ℕ) : ℝ[X] :=
  C (L : ℝ)⁻¹ * ∑ j ∈ Finset.range L, X ^ j

/-- Repeating the averaging filter `k` times. -/
noncomputable def filter (L k : ℕ) : ℝ[X] := (average L) ^ k

theorem average_coeff (L n : ℕ) :
    (average L).coeff n = if n < L then (L : ℝ)⁻¹ else 0 := by
  simp [average, finsetSum_coeff, coeff_X_pow]

theorem average_coeff_nonneg (L n : ℕ) : 0 ≤ (average L).coeff n := by
  rw [average_coeff]
  split_ifs <;> positivity

theorem average_natDegree_le (L : ℕ) : (average L).natDegree ≤ L - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [average_coeff, if_neg]
  omega

theorem average_eval_one (L : ℕ) (hL : 1 ≤ L) : (average L).eval 1 = 1 := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp [average, eval_finsetSum, hL']

theorem average_reflect (L : ℕ) (hL : 1 ≤ L) :
    (average L).reflect (L - 1) = average L := by
  ext n
  rw [coeff_reflect, average_coeff, average_coeff]
  by_cases hn : n ≤ L - 1
  · rw [revAt_le hn, if_pos (by omega), if_pos (by omega)]
  · rw [revAt_eq_self_of_lt (by omega)]

theorem filter_natDegree_le (L k : ℕ) :
    (filter L k).natDegree ≤ k * (L - 1) := by
  exact natDegree_pow_le_of_le k (average_natDegree_le L)

/-- Multiplication preserves coefficient nonnegativity. -/
theorem mul_coeff_nonneg (p q : ℝ[X])
    (hp : ∀ n, 0 ≤ p.coeff n) (hq : ∀ n, 0 ≤ q.coeff n) (n : ℕ) :
    0 ≤ (p * q).coeff n := by
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp ij.1) (hq ij.2)

theorem filter_coeff_nonneg (L k n : ℕ) : 0 ≤ (filter L k).coeff n := by
  induction k generalizing n with
  | zero =>
      simp only [filter, pow_zero, coeff_one]
      split_ifs <;> norm_num
  | succ k ih =>
      change 0 ≤ ((average L) ^ (k + 1)).coeff n
      rw [pow_succ]
      exact mul_coeff_nonneg _ _ ih (average_coeff_nonneg L) n

theorem filter_eval_one (L k : ℕ) (hL : 1 ≤ L) : (filter L k).eval 1 = 1 := by
  simp [filter, average_eval_one L hL]

theorem filter_reflect (L k : ℕ) (hL : 1 ≤ L) :
    (filter L k).reflect (k * (L - 1)) = filter L k := by
  induction k with
  | zero => simp [filter]
  | succ k ih =>
      change ((average L) ^ (k + 1)).reflect ((k + 1) * (L - 1)) = _
      rw [pow_succ, Nat.add_mul, one_mul]
      rw [reflect_mul _ _
        (show ((average L) ^ k).natDegree ≤ k * (L - 1) from filter_natDegree_le L k)
        (average_natDegree_le L)]
      rw [show ((average L) ^ k).reflect (k * (L - 1)) = (average L) ^ k from ih,
        average_reflect L hL]
      rfl

theorem filter_coeff_palindromic (L k : ℕ) (hL : 1 ≤ L)
    (j : ℕ) (hj : j ≤ k * (L - 1)) :
    (filter L k).coeff (k * (L - 1) - j) = (filter L k).coeff j := by
  have h := congrArg (fun p : ℝ[X] => p.coeff j) (filter_reflect L k hL)
  simpa only [coeff_reflect, revAt_le hj] using h

theorem filter_coeff_sum (L k : ℕ) (hL : 1 ≤ L) :
    ∑ j ∈ Finset.range (k * (L - 1) + 1), (filter L k).coeff j = 1 := by
  have h := eval_eq_sum_range'
    (Nat.lt_succ_of_le (filter_natDegree_le L k)) (1 : ℝ)
  simpa only [filter_eval_one L k hL, one_pow, mul_one] using h.symm

theorem filter_coeff_eq_zero (L k n : ℕ) (hn : k * (L - 1) < n) :
    (filter L k).coeff n = 0 :=
  coeff_eq_zero_of_natDegree_lt ((filter_natDegree_le L k).trans_lt hn)

/-- The coefficient list reconstructs the actual polynomial power. -/
theorem filter_eq_coefficient_sum (L k : ℕ) :
    filter L k = ∑ j ∈ Finset.range (k * (L - 1) + 1),
      C ((filter L k).coeff j) * X ^ j :=
  (filter L k).as_sum_range_C_mul_X_pow'
    (Nat.lt_succ_of_le (filter_natDegree_le L k))

/-- Evaluation after any real-to-field homomorphism gives the intended filter.
In particular this applies to complex arguments via the standard inclusion. -/
theorem filter_eval₂ {K : Type*} [Field K] (f : ℝ →+* K) (L k : ℕ) (z : K) :
    (filter L k).eval₂ f z = (FilterCoefficients.geometricAverage L z) ^ k := by
  simp only [filter, average, eval₂_pow, eval₂_mul, eval₂_C, eval₂_finsetSum,
    eval₂_X, map_inv₀, map_natCast, FilterCoefficients.geometricAverage,
    FilterCoefficients.geometricSum, div_eq_mul_inv]
  rw [mul_comm]

/-- Signed weight one also holds for the concrete averaging filter. -/
theorem smoothing_signed_mass_one (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < k * (L - 1)) :
    ∑ j ∈ Finset.range (k * (L - 1) + 1),
      (FilterCoefficients.positiveWeight (k * (L - 1)) (filter L k).coeff j +
        FilterCoefficients.negativeWeight (k * (L - 1)) (filter L k).coeff j) = 1 := by
  exact FilterCoefficients.smoothing_signed_mass _ _ hd (filter_coeff_sum L k hL)

/-- The concrete repeated average has signed-LCU normalization exactly two. -/
theorem smoothing_absolute_mass_two (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < k * (L - 1)) :
    ∑ j ∈ Finset.range (k * (L - 1) + 1),
      (|FilterCoefficients.positiveWeight (k * (L - 1)) (filter L k).coeff j| +
        |FilterCoefficients.negativeWeight (k * (L - 1)) (filter L k).coeff j|) = 2 := by
  exact FilterCoefficients.smoothing_absolute_mass_two _ _ hd
    (fun j _ => filter_coeff_nonneg L k j)
    (filter_coeff_palindromic L k hL) (filter_coeff_sum L k hL)

end SparseHamiltonian.AveragingPolynomial
