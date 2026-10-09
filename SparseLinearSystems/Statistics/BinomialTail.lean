import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Binomial tail bounds

Elementary exponential-moment (Chernoff) bounds for the binomial law, used for
the repeated probability tests of Section `qls`, equation `qls:eq:hoeffding`.
For `0 ≤ t ≤ 2`,

`P(|S - n p| ≥ n t) ≤ 2 exp(-n t² / 4)`,

where `S` has the binomial law with parameters `n, p`.  The constant `1/4`
is weaker than Hoeffding's `2`; only absolute constants change.
-/

namespace SparseLinearSystems.BinomialTail

open Finset Real

noncomputable section

/-- Binomial probability of `k` successes in `n` independent trials. -/
def binom (n : ℕ) (p : ℝ) (k : ℕ) : ℝ := (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

theorem binom_nonneg (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ binom n p k := by
  unfold binom
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The exponential moment of the binomial law. -/
theorem sum_binom_mul_pow (n : ℕ) (p x : ℝ) :
    ∑ k ∈ range (n + 1), binom n p k * x ^ k = (p * x + (1 - p)) ^ n := by
  rw [add_pow]
  apply sum_congr rfl
  intro k _
  unfold binom
  rw [mul_pow]
  ring

theorem sum_binom (n : ℕ) (p : ℝ) : ∑ k ∈ range (n + 1), binom n p k = 1 := by
  have h := sum_binom_mul_pow n p 1
  simp only [one_pow, mul_one] at h
  rw [h]; ring_nf

/-- `1 - p + p e^θ ≤ exp(p (e^θ - 1))`. -/
theorem mgf_base_le (p θ : ℝ) :
    p * exp θ + (1 - p) ≤ exp (p * (exp θ - 1)) := by
  have := add_one_le_exp (p * (exp θ - 1))
  linarith

/-- `e^θ - 1 - θ ≤ θ²` for `|θ| ≤ 1`. -/
theorem exp_sub_le_sq {θ : ℝ} (h : |θ| ≤ 1) : exp θ - 1 - θ ≤ θ ^ 2 :=
  (le_abs_self _).trans (abs_exp_sub_one_sub_id_le h)

theorem mgf_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1) :
    ∑ k ∈ range (n + 1), binom n p k * exp (θ * k) ≤ exp (n * (p * θ + θ ^ 2)) := by
  have hrw : ∀ k : ℕ, exp (θ * k) = exp θ ^ k := by
    intro k; rw [← exp_nat_mul, mul_comm]
  simp_rw [hrw]
  rw [sum_binom_mul_pow]
  have hbase : 0 ≤ p * exp θ + (1 - p) := by
    have := exp_pos θ; nlinarith
  calc (p * exp θ + (1 - p)) ^ n ≤ exp (p * (exp θ - 1)) ^ n :=
        pow_le_pow_left₀ hbase (mgf_base_le p θ) n
    _ = exp (n * (p * (exp θ - 1))) := by rw [← exp_nat_mul]
    _ ≤ exp (n * (p * θ + θ ^ 2)) := by
        apply exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        have h1 := exp_sub_le_sq hθ
        have h2 : p * (exp θ - 1 - θ) ≤ p * θ ^ 2 := mul_le_mul_of_nonneg_left h1 hp0
        have h3 : p * θ ^ 2 ≤ θ ^ 2 := by
          have := sq_nonneg θ; nlinarith
        nlinarith

/-- Upper tail: `P(S ≥ n(p + t)) ≤ exp(-n t²/4)` for `0 ≤ t ≤ 2`. -/
theorem upper_tail (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ∑ k ∈ range (n + 1), (if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) ≤
      exp (-(n * t ^ 2 / 4)) := by
  set θ := t / 2 with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith
  have hθ1 : |θ| ≤ 1 := by rw [abs_of_nonneg hθ0, hθ]; linarith
  have hterm : ∀ k ∈ range (n + 1),
      (if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) ≤
        exp (-(θ * (n * (p + t)))) * (binom n p k * exp (θ * k)) := by
    intro k _
    have hb := binom_nonneg n hp0 hp1 k
    split_ifs with hk
    · have : 1 ≤ exp (-(θ * (n * (p + t)))) * exp (θ * k) := by
        rw [← exp_add]
        apply one_le_exp
        nlinarith
      nlinarith [exp_pos (-(θ * (n * (p + t)))), exp_pos (θ * k)]
    · positivity
  calc _ ≤ ∑ k ∈ range (n + 1), exp (-(θ * (n * (p + t)))) * (binom n p k * exp (θ * k)) :=
        sum_le_sum hterm
    _ = exp (-(θ * (n * (p + t)))) * ∑ k ∈ range (n + 1), binom n p k * exp (θ * k) := by
        rw [mul_sum]
    _ ≤ exp (-(θ * (n * (p + t)))) * exp (n * (p * θ + θ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mgf_le n hp0 hp1 hθ1) (exp_pos _).le
    _ = exp (-(n * t ^ 2 / 4)) := by
        rw [← exp_add]; congr 1; rw [hθ]; ring

/-- Lower tail: `P(S ≤ n(p - t)) ≤ exp(-n t²/4)` for `0 ≤ t ≤ 2`. -/
theorem lower_tail (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ∑ k ∈ range (n + 1), (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0) ≤
      exp (-(n * t ^ 2 / 4)) := by
  set θ := -(t / 2) with hθ
  have hθ1 : |θ| ≤ 1 := by
    rw [hθ, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t / 2)]; linarith
  have hterm : ∀ k ∈ range (n + 1),
      (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0) ≤
        exp (-(θ * (n * (p - t)))) * (binom n p k * exp (θ * k)) := by
    intro k _
    have hb := binom_nonneg n hp0 hp1 k
    split_ifs with hk
    · have : 1 ≤ exp (-(θ * (n * (p - t)))) * exp (θ * k) := by
        rw [← exp_add]
        apply one_le_exp
        rw [hθ]
        nlinarith
      nlinarith [exp_pos (-(θ * (n * (p - t)))), exp_pos (θ * k)]
    · positivity
  calc _ ≤ ∑ k ∈ range (n + 1), exp (-(θ * (n * (p - t)))) * (binom n p k * exp (θ * k)) :=
        sum_le_sum hterm
    _ = exp (-(θ * (n * (p - t)))) * ∑ k ∈ range (n + 1), binom n p k * exp (θ * k) := by
        rw [mul_sum]
    _ ≤ exp (-(θ * (n * (p - t)))) * exp (n * (p * θ + θ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mgf_le n hp0 hp1 hθ1) (exp_pos _).le
    _ = exp (-(n * t ^ 2 / 4)) := by
        rw [← exp_add]; congr 1; rw [hθ]; ring

/-- Two-sided tail: `P(|S - n p| ≥ n t) ≤ 2 exp(-n t²/4)` for `0 ≤ t ≤ 2`. -/
theorem two_sided (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    ∑ k ∈ range (n + 1), (if (n : ℝ) * t ≤ |(k : ℝ) - n * p| then binom n p k else 0) ≤
      2 * exp (-(n * t ^ 2 / 4)) := by
  have hu := upper_tail n hp0 hp1 ht0 ht2
  have hl := lower_tail n hp0 hp1 ht0 ht2
  have hterm : ∀ k ∈ range (n + 1),
      (if (n : ℝ) * t ≤ |(k : ℝ) - n * p| then binom n p k else 0) ≤
        (if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) +
          (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0) := by
    intro k _
    have hb := binom_nonneg n hp0 hp1 k
    by_cases h1 : (n : ℝ) * t ≤ |(k : ℝ) - n * p|
    · rw [if_pos h1]
      rcases le_abs'.mp h1 with h | h
      · have hk : (k : ℝ) ≤ n * (p - t) := by linarith
        rw [if_pos hk]
        split_ifs <;> linarith
      · have hk : (n : ℝ) * (p + t) ≤ k := by linarith
        rw [if_pos hk]
        split_ifs <;> linarith
    · rw [if_neg h1]
      split_ifs <;> linarith
  calc _ ≤ ∑ k ∈ range (n + 1), ((if (n : ℝ) * (p + t) ≤ k then binom n p k else 0) +
          (if (k : ℝ) ≤ n * (p - t) then binom n p k else 0)) := sum_le_sum hterm
    _ = _ := sum_add_distrib
    _ ≤ exp (-(n * t ^ 2 / 4)) + exp (-(n * t ^ 2 / 4)) := add_le_add hu hl
    _ = 2 * exp (-(n * t ^ 2 / 4)) := by ring

/-- Number of repetitions sufficient for failure probability `ζ` at accuracy `t`. -/
theorem two_sided_le_of_count (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {t ζ : ℝ}
    (ht0 : 0 < t) (ht2 : t ≤ 2) (hζ : 0 < ζ) (hn : 4 * Real.log (2 / ζ) / t ^ 2 ≤ n) :
    ∑ k ∈ range (n + 1), (if (n : ℝ) * t ≤ |(k : ℝ) - n * p| then binom n p k else 0) ≤ ζ := by
  refine (two_sided n hp0 hp1 ht0.le ht2).trans ?_
  have ht2' : 0 < t ^ 2 := by positivity
  have h1 : Real.log (2 / ζ) ≤ n * t ^ 2 / 4 := by
    rw [div_le_iff₀ ht2'] at hn; linarith
  have h2 : exp (-(n * t ^ 2 / 4)) ≤ ζ / 2 := by
    rw [show ζ / 2 = exp (Real.log (ζ / 2)) from (Real.exp_log (by positivity)).symm]
    apply exp_le_exp.mpr
    have : Real.log (ζ / 2) = -Real.log (2 / ζ) := by
      rw [← Real.log_inv, inv_div]
    linarith
  linarith

end

end SparseLinearSystems.BinomialTail
