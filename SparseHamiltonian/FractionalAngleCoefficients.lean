import SparseHamiltonian.AmplifierSignalGeometry

/-!
# Explicit positive coefficients for fractional-angle correction

The coefficients below are the candidate odd-power coefficients of
`sin(a * arcsin y) / a`. Their recurrence, nonnegativity, coefficient mass,
and uniform relative truncation bounds are proved directly, without assuming
an approximation theorem. Identifying their sum with the trigonometric target
is a separate analytic obligation.
-/
namespace SparseHamiltonian.FractionalAngleCoefficients

noncomputable section
open Polynomial
open scoped BigOperators

/-- Explicit fractional-angle coefficient recurrence, including the limit `a=0`. -/
def coefficient (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => coefficient a k *
      (((2 * (k : ℝ) + 1) ^ 2 - a ^ 2) / ((2 * k + 2) * (2 * k + 3)))

@[simp] theorem coefficient_zero (a : ℝ) : coefficient a 0 = 1 := rfl

/-- The recurrence has only nonnegative factors when `|a|≤1`. -/
theorem coefficient_nonneg (a : ℝ) (ha : |a| ≤ 1) (k : ℕ) :
    0 ≤ coefficient a k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [coefficient]
      apply mul_nonneg ih
      apply div_nonneg _ (by positivity)
      have ha2 : a ^ 2 ≤ 1 := by
        have hab := abs_le.mp ha
        nlinarith
      have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith [sq_nonneg (k : ℝ)]

/-- A decreasing potential makes the total coefficient mass explicit. -/
def potential (a : ℝ) (k : ℕ) : ℝ := (2 * (k : ℝ) + 1) * coefficient a k

/-- Exact one-step potential drop; no special-function identity is used. -/
theorem potential_drop (a : ℝ) (k : ℕ) :
    potential a k - potential a (k + 1) =
      coefficient a k * (2 * (k : ℝ) + 1 + a ^ 2) / (2 * k + 2) := by
  unfold potential
  rw [coefficient]
  push_cast
  have h2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
  have h3 : (2 * (k : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-- Each coefficient consumes at most twice the potential drop. -/
theorem coefficient_le_drop (a : ℝ) (ha : |a| ≤ 1) (k : ℕ) :
    coefficient a k ≤ 2 * (potential a k - potential a (k + 1)) := by
  rw [potential_drop]
  have hb := coefficient_nonneg a ha k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hd : 0 < 2 * (k : ℝ) + 2 := by positivity
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hd).mpr
  nlinarith [sq_nonneg a, mul_nonneg hb (sq_nonneg a), mul_nonneg hb hk]

/-- Every finite prefix has coefficient mass at most two. -/
theorem sum_coefficient_le (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, coefficient a k) ≤ 2 - 2 * potential a N := by
  induction N with
  | zero => simp [potential]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have h := coefficient_le_drop a ha N
      linarith

/-- The coefficient mass bound is independent of the inverse gain and cutoff. -/
theorem sum_coefficient_le_two (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, coefficient a k) ≤ 2 := by
  have h := sum_coefficient_le a ha N
  have hp : 0 ≤ potential a N := mul_nonneg (by positivity) (coefficient_nonneg a ha N)
  linarith

/-- The entire explicit coefficient family is absolutely summable. -/
theorem summable_coefficient (a : ℝ) (ha : |a| ≤ 1) :
    Summable (coefficient a) :=
  summable_of_sum_range_le (coefficient_nonneg a ha) (sum_coefficient_le_two a ha)

/-- A constant LCU normalization works for every truncation simultaneously. -/
theorem tsum_coefficient_le_two (a : ℝ) (ha : |a| ≤ 1) :
    (∑' k : ℕ, coefficient a k) ≤ 2 :=
  (summable_coefficient a ha).tsum_le_of_sum_range_le (sum_coefficient_le_two a ha)

/-- An actual finite odd polynomial with the explicit coefficients. -/
def correction (a : ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range N, C (coefficient a k) * X ^ (2 * k + 1)

@[simp] theorem correction_eval (a : ℝ) (N : ℕ) (y : ℝ) :
    (correction a N).eval y =
      ∑ k ∈ Finset.range N, coefficient a k * y ^ (2 * k + 1) := by
  simp [correction, Polynomial.eval_finsetSum]

@[simp] theorem correction_eval_zero (a : ℝ) (N : ℕ) :
    (correction a N).eval 0 = 0 := by simp

/-- Algebraic odd parity, the form required by polynomial synthesis. -/
theorem correction_parity (a : ℝ) (N : ℕ) :
    (correction a N).comp (-X) = -(correction a N) := by
  simp only [correction, Polynomial.sum_comp, Polynomial.mul_comp, C_comp,
    Polynomial.pow_comp, X_comp, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have ho : Odd (2 * k + 1) := ⟨k, by omega⟩
  rw [ho.neg_pow]
  ring

/-- Degree at most `2N-1`, with a convenient bound covering the empty truncation. -/
theorem correction_degree (a : ℝ) (N : ℕ) :
    (correction a N).natDegree ≤ 2 * N := by
  apply natDegree_sum_le_of_forall_le
  intro k hk
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add, natDegree_X_pow]
  have hkN := Finset.mem_range.mp hk
  omega

/-- The polynomial's global norm is bounded directly by positive coefficient mass. -/
theorem correction_bounded (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (y : ℝ) (hy : |y| ≤ 1) : |(correction a N).eval y| ≤ 2 := by
  rw [correction_eval]
  calc
    |∑ k ∈ Finset.range N, coefficient a k * y ^ (2 * k + 1)| ≤
        ∑ k ∈ Finset.range N, |coefficient a k * y ^ (2 * k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, coefficient a k := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (coefficient_nonneg a ha k), abs_pow]
      exact mul_le_of_le_one_right (coefficient_nonneg a ha k)
        (pow_le_one₀ (abs_nonneg y) hy)
    _ ≤ 2 := sum_coefficient_le_two a ha N

/-- The concrete target series. -/
def series (a y : ℝ) : ℝ := ∑' k : ℕ, coefficient a k * y ^ (2 * k + 1)

/-- Summability is valid at both endpoints as well as in the interior. -/
theorem summable_series (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| ≤ 1) :
    Summable (fun k : ℕ => coefficient a k * y ^ (2 * k + 1)) := by
  apply (summable_coefficient a ha).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (coefficient_nonneg a ha k), abs_pow]
  exact mul_le_of_le_one_right (coefficient_nonneg a ha k)
    (pow_le_one₀ (abs_nonneg y) hy)

/-- A full-series bound follows from the same constant coefficient mass. -/
theorem series_bounded (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| ≤ 1) :
    |series a y| ≤ 2 := by
  rw [series, ← Real.norm_eq_abs]
  apply (le_trans (tsum_of_norm_bounded (summable_coefficient a ha).hasSum ?_)
    (tsum_coefficient_le_two a ha))
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (coefficient_nonneg a ha k), abs_pow]
  exact mul_le_of_le_one_right (coefficient_nonneg a ha k)
    (pow_le_one₀ (abs_nonneg y) hy)


/-- The omitted coefficient mass is bounded by the same absolute constant. -/
theorem tail_coefficient_le_two (a : ℝ) (ha : |a| ≤ 1) (N : ℕ) :
    (∑' k : ℕ, coefficient a (k + N)) ≤ 2 := by
  have h := (summable_coefficient a ha).sum_add_tsum_nat_add N
  have hs : 0 ≤ ∑ k ∈ Finset.range N, coefficient a k :=
    Finset.sum_nonneg (fun k _ => coefficient_nonneg a ha k)
  have ht := tsum_coefficient_le_two a ha
  linarith

/-- Relative geometric tail, including zero. The constant is independent of `a`. -/
theorem relative_tail (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (ρ y : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hy : |y| ≤ ρ) :
    |series a y - (correction a N).eval y| ≤ 2 * ρ ^ (2 * N) * |y| := by
  have hy1 := hy.trans hρ1
  have hs := summable_series a ha y hy1
  have he : series a y - (correction a N).eval y =
      ∑' k : ℕ, coefficient a (k + N) * y ^ (2 * (k + N) + 1) := by
    rw [series, correction_eval]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using
      (hs.sum_add_tsum_nat_add N).symm)
  have hb : Summable (fun k : ℕ => coefficient a (k + N)) :=
    (summable_coefficient a ha).comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hn (k : ℕ) :
      ‖coefficient a (k + N) * y ^ (2 * (k + N) + 1)‖ ≤
        coefficient a (k + N) * (ρ ^ (2 * N) * |y|) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (coefficient_nonneg a ha _), abs_pow,
      pow_succ]
    apply mul_le_mul_of_nonneg_left _ (coefficient_nonneg a ha _)
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg y)
    exact (pow_le_pow_left₀ (abs_nonneg y) hy _).trans
      (pow_le_pow_of_le_one hρ0 hρ1 (by omega))
  rw [he, ← Real.norm_eq_abs]
  have h := tsum_of_norm_bounded (hb.hasSum.mul_right (ρ ^ (2 * N) * |y|)) hn
  apply h.trans
  have ht := tail_coefficient_le_two a ha N
  nlinarith [mul_le_mul_of_nonneg_right ht (show 0 ≤ ρ ^ (2 * N) * |y| by positivity)]

/-- Each finite correction is bounded by `2|y|`, also at zero. -/
theorem correction_relative_bound (a : ℝ) (ha : |a| ≤ 1) (N : ℕ)
    (y : ℝ) (hy : |y| ≤ 1) : |(correction a N).eval y| ≤ 2 * |y| := by
  rw [correction_eval]
  calc
    |∑ k ∈ Finset.range N, coefficient a k * y ^ (2 * k + 1)| ≤
        ∑ k ∈ Finset.range N, |coefficient a k * y ^ (2 * k + 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range N, coefficient a k * |y| := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_of_nonneg (coefficient_nonneg a ha k), abs_pow]
      apply mul_le_mul_of_nonneg_left _ (coefficient_nonneg a ha k)
      exact (pow_le_pow_of_le_one (abs_nonneg y) hy (by omega : 1 ≤ 2 * k + 1)).trans_eq
        (pow_one _)
    _ = (∑ k ∈ Finset.range N, coefficient a k) * |y| := by rw [Finset.sum_mul]
    _ ≤ 2 * |y| := mul_le_mul_of_nonneg_right (sum_coefficient_le_two a ha N) (abs_nonneg y)

end
end SparseHamiltonian.FractionalAngleCoefficients
