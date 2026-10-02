import SparseHamiltonian.FractionalAngleCoefficients

/-!
# Concrete bounded amplifier polynomials

An odd Chebyshev signal is composed with an explicit positive-coefficient
fractional-angle truncation. Every constructed polynomial is globally bounded
by one half, and the truncation has a logarithmic precision schedule. The
comparison here is to the explicitly defined infinite series; its identification
with the inverse-angle function is kept separate.
-/
namespace SparseHamiltonian.AmplifierPolynomialConstruction

noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- An exact globally bounded odd multiple-angle sine polynomial. -/
def signal (k : ℕ) : ℝ[X] := C ((-1 : ℝ) ^ k) * T ℝ (2 * (k : ℤ) + 1)

/-- The sign choice makes the slope positive at zero. -/
theorem signal_eval (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    (signal k).eval x = Real.sin ((2 * (k : ℝ) + 1) * Real.arcsin x) := by
  rw [signal, eval_mul, eval_C, OddChebyshevApproximation.odd_chebyshev_sine k x hx]
  have hsq : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, hsq, one_mul]

/-- Exact degree budget for the multiple-angle signal. -/
theorem signal_degree (k : ℕ) : (signal k).natDegree ≤ 2 * k + 1 := by
  unfold signal
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add, natDegree_T]
  have he : (2 * (k : ℤ) + 1).natAbs = 2 * k + 1 := by omega
  rw [he]

/-- Odd parity holds as a polynomial identity. -/
theorem signal_parity (k : ℕ) : (signal k).comp (-X) = -(signal k) := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_neg, eval_X, signal, eval_mul, eval_C]
  have ho : Odd (2 * (k : ℤ) + 1) := ⟨k, by ring⟩
  rw [T_eval_neg, Int.negOnePow_odd _ ho]
  norm_num


/-- Every real signal in `[-1,1]` stays in that interval. -/
theorem signal_bounded (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(signal k).eval x| ≤ 1 := by rw [signal_eval k x hx]; exact Real.abs_sin_le_one _

/-- The signal map retains a relative bound at the origin. -/
theorem signal_relative (k : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |(signal k).eval x| ≤ (2 * (k : ℝ) + 1) * |x| := by
  simp only [signal, eval_mul, eval_C, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact OddChebyshevApproximation.abs_odd_chebyshev_le k x hx

/-- The explicit bounded composition; no phase-existence premise is used. -/
def amplifier (a : ℝ) (k N : ℕ) : ℝ[X] :=
  C (1 / 4 : ℝ) * (FractionalAngleCoefficients.correction a N).comp (signal k)

@[simp] theorem amplifier_eval (a : ℝ) (k N : ℕ) (x : ℝ) :
    (amplifier a k N).eval x =
      (1 / 4 : ℝ) * (FractionalAngleCoefficients.correction a N).eval ((signal k).eval x) := by
  simp [amplifier]

/-- Constant global slack is obtained for every cutoff and every inverse gain. -/
theorem amplifier_bounded (a : ℝ) (ha : |a| ≤ 1) (k N : ℕ)
    (x : ℝ) (hx : |x| ≤ 1) : |(amplifier a k N).eval x| ≤ 1 / 2 := by
  rw [amplifier_eval, abs_mul]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have h := FractionalAngleCoefficients.correction_bounded a ha N ((signal k).eval x)
    (signal_bounded k x hx)
  linarith

/-- The actual polynomial is odd. -/
theorem amplifier_parity (a : ℝ) (k N : ℕ) :
    (amplifier a k N).comp (-X) = -(amplifier a k N) := by
  unfold amplifier
  rw [mul_comp, C_comp, comp_assoc, signal_parity]
  have hc := FractionalAngleCoefficients.correction_parity a N
  have he : (-X : ℝ[X]).comp (signal k) = -(signal k) := by simp
  rw [← he, ← comp_assoc, hc, neg_comp]
  ring

/-- Composition multiplies the logarithmic correction degree by the signal order. -/
theorem amplifier_degree (a : ℝ) (k N : ℕ) :
    (amplifier a k N).natDegree ≤ 2 * N * (2 * k + 1) := by
  unfold amplifier
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  apply natDegree_comp_le.trans
  exact Nat.mul_le_mul (FractionalAngleCoefficients.correction_degree a N) (signal_degree k)

/-- Relative error against the concrete infinite fractional-angle series. -/
theorem amplifier_series_error (a : ℝ) (ha : |a| ≤ 1) (k N : ℕ)
    (x : ℝ) (hx : |x| ≤ 1) (hsmall : |(signal k).eval x| ≤ 1 / 2) :
    |(amplifier a k N).eval x -
      (1 / 4 : ℝ) * FractionalAngleCoefficients.series a ((signal k).eval x)| ≤
      ((2 * (k : ℝ) + 1) / 2) * (1 / 4 : ℝ) ^ N * |x| := by
  have h := FractionalAngleCoefficients.relative_tail a ha N (1 / 2) ((signal k).eval x)
    (by norm_num) (by norm_num) hsmall
  have hp : (1 / 2 : ℝ) ^ (2 * N) = (1 / 4 : ℝ) ^ N := by rw [pow_mul]; norm_num
  rw [hp] at h
  have hs := signal_relative k x hx
  rw [amplifier_eval, ← mul_sub, abs_mul, abs_sub_comm]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hh' := mul_le_mul_of_nonneg_left hs (show 0 ≤ (1 / 4 : ℝ) ^ N by positivity)
  nlinarith

/-- An explicit logarithmic cutoff, uniform in the unknown sparse entries. -/
def precisionCutoff (δ : ℝ) : ℕ :=
  OddChebyshevApproximation.cutoff 2 (Real.log 4) δ

/-- The scheduled scalar relative error has no inverse-polynomial precision factor. -/
theorem precision_cutoff_bound (δ : ℝ) (hδ : 0 < δ) :
    2 * (1 / 4 : ℝ) ^ precisionCutoff δ ≤ δ := by
  have h := OddChebyshevApproximation.cutoff_tail 2 (Real.log 4) δ
    (by norm_num) (Real.log_pos (by norm_num)) hδ
  have he : Real.exp (-Real.log 4) = (1 / 4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  simpa only [precisionCutoff, he] using h

/-- Explicit combined degree: linear in the signal order and logarithmic in precision. -/
theorem scheduled_degree (a : ℝ) (k : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    ((amplifier a k (precisionCutoff δ)).natDegree : ℝ) <
      2 * (Real.log (2 / δ) / Real.log 4 + 1) * (2 * (k : ℝ) + 1) := by
  have hd : ((amplifier a k (precisionCutoff δ)).natDegree : ℝ) ≤
      2 * (precisionCutoff δ : ℝ) * (2 * (k : ℝ) + 1) := by
    exact_mod_cast amplifier_degree a k (precisionCutoff δ)
  have hn := OddChebyshevApproximation.cutoff_lt 2 (Real.log 4) δ
    (Real.log_pos (by norm_num)) hδ hδ2
  change (precisionCutoff δ : ℝ) < _ at hn
  have hp : 0 < 2 * (k : ℝ) + 1 := by positivity
  nlinarith [mul_lt_mul_of_pos_right hn hp]

end
end SparseHamiltonian.AmplifierPolynomialConstruction
