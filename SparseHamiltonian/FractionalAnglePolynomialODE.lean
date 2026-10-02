import SparseHamiltonian.EncodedLabeledProgram

/-!
# Exact differential residual of fractional-angle truncations

The concrete correction polynomials satisfy the fractional Chebyshev equation
up to a single highest-degree monomial. This follows by telescoping their
explicit recurrence. The residual has a geometric pointwise bound on a fixed
small-signal interval. These are finite polynomial identities; no interchange
of differentiation with an infinite sum is assumed here.
-/

namespace SparseHamiltonian.FractionalAnglePolynomialODE

noncomputable section
open Polynomial FractionalAngleCoefficients
open scoped BigOperators Topology

/-- The polynomial differential operator for the fractional-angle equation. -/
def residual (a : ℝ) (P : ℝ[X]) : ℝ[X] :=
  (1 - X ^ 2) * derivative (derivative P) - X * derivative P + C (a ^ 2) * P

/-- The differential residual is additive. -/
theorem residual_add (a : ℝ) (P Q : ℝ[X]) :
    residual a (P + Q) = residual a P + residual a Q := by
  simp only [residual, derivative_add]
  ring

/-- The degree-one endpoint has only its original odd monomial. -/
theorem residual_linear (a c : ℝ) :
    residual a (C c * X) = C (c * (a ^ 2 - 1)) * X := by
  simp only [residual, derivative_C_mul_X, derivative_C, mul_zero, zero_sub,
    map_mul, map_sub, map_pow, map_one]
  ring

/-- A monomial contributes one lower and one original-degree term. -/
theorem residual_monomial (a c : ℝ) (n : ℕ) :
    residual a (C c * X ^ (n + 2)) =
      C (c * ((n : ℝ) + 2) * ((n : ℝ) + 1)) * X ^ n +
        C (c * (a ^ 2 - ((n : ℝ) + 2) ^ 2)) * X ^ (n + 2) := by
  have hn : n + 2 - 1 = n + 1 := by omega
  simp only [residual, derivative_C_mul_X_pow, hn, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  simp only [map_mul, map_sub, map_pow, map_add, map_ofNat, map_one, pow_add]
  ring

/-- The explicit coefficient recurrence clears its positive denominator. -/
theorem coefficient_balance (a : ℝ) (N : ℕ) :
    coefficient a (N + 1) * ((2 * (N : ℝ) + 2) * (2 * N + 3)) =
      coefficient a N * ((2 * (N : ℝ) + 1) ^ 2 - a ^ 2) := by
  rw [coefficient]
  have hd : ((2 * (N : ℝ) + 2) * (2 * N + 3)) ≠ 0 := by positivity
  field_simp

/-- The actual finite correction gains exactly its next explicit monomial. -/
theorem correction_succ (a : ℝ) (N : ℕ) :
    correction a (N + 1) = correction a N + C (coefficient a N) * X ^ (2 * N + 1) := by
  simp only [correction, Finset.sum_range_succ]

/-- Exact residual: all interior coefficients cancel, leaving only the top odd term. -/
theorem correction_residual (a : ℝ) (N : ℕ) :
    residual a (correction a (N + 1)) =
      C (coefficient a N * (a ^ 2 - (2 * (N : ℝ) + 1) ^ 2)) * X ^ (2 * N + 1) := by
  induction N with
  | zero =>
      simp only [correction, Finset.sum_range_one, coefficient_zero,
        zero_add, pow_one, Nat.cast_zero, mul_zero, one_pow, one_mul]
      simpa only [one_mul] using residual_linear a 1
  | succ N ih =>
      rw [correction_succ a (N + 1), residual_add, ih]
      have he : 2 * (N + 1) + 1 = (2 * N + 1) + 2 := by omega
      rw [he, residual_monomial]
      have hb := coefficient_balance a N
      have hz : coefficient a N * (a ^ 2 - (2 * (N : ℝ) + 1) ^ 2) +
          coefficient a (N + 1) * ((2 * (N : ℝ) + 3) * (2 * N + 2)) = 0 := by
        nlinarith
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      have hc : C (coefficient a N * (a ^ 2 - (2 * (N : ℝ) + 1) ^ 2)) +
          C (coefficient a (N + 1) * ((2 * (N : ℝ) + 3) * (2 * N + 2))) =
          (0 : ℝ[X]) := by rw [← C_add, hz, map_zero]
      simp only [map_mul, map_add, map_sub, map_pow, map_ofNat, map_one] at hc ⊢
      linear_combination (X ^ (2 * N + 1)) * hc

/-- Equivalent residual coefficient expressed entirely through the next omitted term. -/
theorem correction_residual_next (a : ℝ) (N : ℕ) :
    residual a (correction a (N + 1)) =
      -C (coefficient a (N + 1) * (2 * (N : ℝ) + 2) * (2 * N + 3)) *
        X ^ (2 * N + 1) := by
  rw [correction_residual, ← map_neg]
  congr 2
  have h := coefficient_balance a N
  nlinarith

/-- The polynomial residual never exceeds the actual truncation degree. -/
theorem correction_residual_degree (a : ℝ) (N : ℕ) :
    (residual a (correction a (N + 1))).natDegree ≤ 2 * N + 1 := by
  rw [correction_residual]
  exact (natDegree_C_mul_le _ _).trans (by simp)

/-- Sharp odd degree budget for each nonempty correction truncation. -/
theorem correction_degree_sharp (a : ℝ) (N : ℕ) :
    (correction a (N + 1)).natDegree ≤ 2 * N + 1 := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add, natDegree_X_pow]
  have h := Finset.mem_range.mp hk
  omega

/-- Each explicit coefficient is bounded by the proved total positive mass. -/
theorem coefficient_le_two (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) :
    coefficient a N ≤ 2 := by
  have hs := sum_coefficient_le_two a ha (N + 1)
  rw [Finset.sum_range_succ] at hs
  have hn : 0 ≤ ∑ k ∈ Finset.range N, coefficient a k :=
    Finset.sum_nonneg (fun k _ => coefficient_nonneg a ha k)
  linarith

/-- Pointwise residual identity, including the zero input. -/
theorem correction_residual_eval (a : ℝ) (N : ℕ) (y : ℝ) :
    (residual a (correction a (N + 1))).eval y =
      coefficient a N * (a ^ 2 - (2 * (N : ℝ) + 1) ^ 2) * y ^ (2 * N + 1) := by
  simp only [correction_residual, eval_mul, eval_C, eval_pow, eval_X]

/-- Explicit relative residual bound on an interval of nonnegative radius. -/
theorem correction_residual_bound (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (ρ y : ℝ) (hy : |y| ≤ ρ) :
    |(residual a (correction a (N + 1))).eval y| ≤
      2 * (2 * (N : ℝ) + 1) ^ 2 * ρ ^ (2 * N) * |y| := by
  have ha2 : a ^ 2 ≤ 1 := by have h := abs_le.mp ha; nlinarith
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hsign : a ^ 2 - (2 * (N : ℝ) + 1) ^ 2 ≤ 0 := by nlinarith
  have hfac : |a ^ 2 - (2 * (N : ℝ) + 1) ^ 2| ≤ (2 * (N : ℝ) + 1) ^ 2 := by
    rw [abs_of_nonpos hsign]
    nlinarith [sq_nonneg a]
  rw [correction_residual_eval, abs_mul, abs_mul,
    abs_of_nonneg (coefficient_nonneg a ha N), abs_pow, pow_succ]
  calc
    coefficient a N * |a ^ 2 - (2 * (N : ℝ) + 1) ^ 2| *
        (|y| ^ (2 * N) * |y|) ≤
        2 * (2 * (N : ℝ) + 1) ^ 2 * (ρ ^ (2 * N) * |y|) := by
      gcongr
      · exact coefficient_le_two a ha N
    _ = _ := by ring

/-- Quadratic degree growth is dominated by a fixed geometric factor. -/
theorem odd_degree_square_le (N : ℕ) : (2 * (N : ℝ) + 1) ^ 2 ≤ 9 * (2 : ℝ) ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rcases N with _ | N
      · norm_num
      rcases N with _ | N
      · norm_num
      have hN : 2 ≤ ((N + 2 : ℕ) : ℝ) := by norm_num
      have hstep : (2 * ((N + 2 : ℕ) : ℝ) + 3) ^ 2 ≤
          2 * (2 * ((N + 2 : ℕ) : ℝ) + 1) ^ 2 := by
        nlinarith [sq_nonneg (((N + 2 : ℕ) : ℝ) - 2)]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] at ih ⊢
      push_cast at hstep
      nlinarith

/-- On the half interval the finite ODE residual decays geometrically, with
an explicit constant and a retained factor `|y|`. -/
theorem correction_residual_half (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (y : ℝ) (hy : |y| ≤ 1 / 2) :
    |(residual a (correction a (N + 1))).eval y| ≤
      18 * (1 / 2 : ℝ) ^ N * |y| := by
  have h := correction_residual_bound a ha N (1 / 2) y hy
  apply h.trans
  have hmul : (2 : ℝ) ^ N * (1 / 2 : ℝ) ^ N = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    2 * (2 * (N : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (2 * N) * |y| ≤
        2 * (9 * (2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ (2 * N) * |y| := by
      gcongr
      exact odd_degree_square_le N
    _ = 18 * ((2 : ℝ) ^ N * (1 / 2 : ℝ) ^ N) * (1 / 2 : ℝ) ^ N * |y| := by
      rw [show 2 * N = N + N by omega, pow_add]
      ring
    _ = _ := by rw [hmul, mul_one]

/-- Every nonempty finite correction already has the target's exact initial slope. -/
theorem correction_derivative_zero (a : ℝ) (N : ℕ) :
    (derivative (correction a (N + 1))).eval 0 = 1 := by
  induction N with
  | zero => simp [correction]
  | succ N ih =>
      rw [correction_succ a (N + 1), derivative_add, eval_add, ih]
      simp

/-- Evaluation of the polynomial residual is the classical differential expression. -/
theorem residual_eval (a y : ℝ) (P : ℝ[X]) :
    (residual a P).eval y =
      (1 - y ^ 2) * (derivative (derivative P)).eval y -
        y * (derivative P).eval y + a ^ 2 * P.eval y := by
  simp only [residual, eval_add, eval_sub, eval_mul, eval_one, eval_pow, eval_X, eval_C]

/-- The explicit residual tends to zero on the entire closed half interval. -/
theorem correction_residual_tendsto (a : ℝ) (ha : |a| ≤ 1)
    (y : ℝ) (hy : |y| ≤ 1 / 2) :
    Filter.Tendsto (fun N : ℕ => (residual a (correction a (N + 1))).eval y)
      Filter.atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun N => by
    simpa only [Real.norm_eq_abs] using correction_residual_half a ha N y hy)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  simpa only [mul_zero, zero_mul] using (h.const_mul 18).mul_const |y|

end
end SparseHamiltonian.FractionalAnglePolynomialODE
