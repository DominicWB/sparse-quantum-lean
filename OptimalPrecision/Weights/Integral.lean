import OptimalPrecision.Weights.LaguerreL2
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential-polynomial integrals on the half line

* `integral_pow_mul_exp_neg`: `∫_0^∞ t^n e^{-ct} dt = n!/c^{n+1}`;
* `integral_eval_mul_exp_neg_two`: the moment functional `J` of
  `Weights.LaguerreL2` is the Lebesgue integral `∫_0^∞ e^{-2t} π(t) dt`;
* `setIntegral_Ioi_shift`: translation of a half-line integral.
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open MeasureTheory Set Polynomial Finset Nat
open scoped Polynomial

theorem integrableOn_pow_mul_exp_neg (n : ℕ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(c * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n : ℝ)) (p := 1) (b := c)
    (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) le_rfl hc
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast, Real.rpow_one, neg_mul]

/-- `∫_0^∞ t^n e^{-ct} dt = n!/c^{n+1}`. -/
theorem integral_pow_mul_exp_neg (n : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi 0, t ^ n * Real.exp (-(c * t)) = (n ! : ℝ) / c ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n : ℝ) + 1) (r := c) (by positivity) hc
  have e : ∫ t in Ioi 0, t ^ n * Real.exp (-(c * t)) =
      ∫ t in Ioi (0 : ℝ), t ^ ((n : ℝ) + 1 - 1) * Real.exp (-(c * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [add_sub_cancel_right, Real.rpow_natCast]
  rw [e, h, Real.Gamma_nat_eq_factorial, ← Nat.cast_add_one, Real.rpow_natCast, div_pow, one_pow]
  ring

theorem integrableOn_eval_mul_exp_neg (π : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => π.eval t * Real.exp (-(c * t))) (Ioi 0) := by
  have : (fun t : ℝ => π.eval t * Real.exp (-(c * t))) = fun t =>
      ∑ i ∈ range (π.natDegree + 1), π.coeff i * (t ^ i * Real.exp (-(c * t))) := by
    funext t
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  exact integrable_finsetSum _ fun i _ => (integrableOn_pow_mul_exp_neg i hc).const_mul _

theorem integral_eval_mul_exp_neg (π : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi 0, π.eval t * Real.exp (-(c * t)) =
      ∑ i ∈ range (π.natDegree + 1), π.coeff i * ((i ! : ℝ) / c ^ (i + 1)) := by
  have : (fun t : ℝ => π.eval t * Real.exp (-(c * t))) = fun t =>
      ∑ i ∈ range (π.natDegree + 1), π.coeff i * (t ^ i * Real.exp (-(c * t))) := by
    funext t
    rw [eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, integral_finsetSum _ fun i _ => (integrableOn_pow_mul_exp_neg i hc).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_pow_mul_exp_neg i hc]

theorem J_eq_sum (π : ℝ[X]) :
    J π = ∑ i ∈ range (π.natDegree + 1), π.coeff i * ((i ! : ℝ) / 2 ^ (i + 1)) := by
  rw [J, Polynomial.lsum_apply, Polynomial.sum_over_range]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro n; simp

/-- **`J` is the half-line integral** `∫_0^∞ e^{-2t} π(t) dt`. -/
theorem integral_eval_mul_exp_neg_two (π : ℝ[X]) :
    ∫ t in Ioi 0, π.eval t * Real.exp (-(2 * t)) = J π := by
  rw [integral_eval_mul_exp_neg π two_pos, J_eq_sum]

/-- `∫_0^∞ (e^{-t} π(t))² dt = J(π²)`. -/
theorem integral_sq_eq_J (π : ℝ[X]) :
    ∫ t in Ioi 0, (Real.exp (-t) * π.eval t) ^ 2 = J (π * π) := by
  rw [← integral_eval_mul_exp_neg_two]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  rw [eval_mul, mul_pow, sq (Real.exp (-t)), ← Real.exp_add]
  ring_nf

theorem integrableOn_sq (π : ℝ[X]) :
    IntegrableOn (fun t : ℝ => (Real.exp (-t) * π.eval t) ^ 2) (Ioi 0) := by
  refine (integrableOn_eval_mul_exp_neg (π * π) two_pos).congr_fun (fun t _ => ?_)
    measurableSet_Ioi
  dsimp only
  rw [eval_mul, mul_pow, sq (Real.exp (-t)), ← Real.exp_add]
  ring_nf

/-- Translation of a half-line integral. -/
theorem setIntegral_Ioi_shift (f : ℝ → ℝ) (a : ℝ) :
    ∫ t in Ioi a, f t = ∫ u in Ioi 0, f (u + a) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (μ := volume) (Set.indicator (Ioi a) f) a]
  congr 1
  funext u
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases h : 0 < u
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by linarith)]

end

end OptimalPrecision.ExpPoly
