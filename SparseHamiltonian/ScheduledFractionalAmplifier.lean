import SparseHamiltonian.AmplifierPolynomialConstruction

/-!
# Publicly scheduled bounded amplifier polynomials

This fixes both integer parameters from a known amplitude bound A and error δ.
Global boundedness, odd parity, and the O(A⁻¹ log(1/δ)) degree estimate are
unconditional. The relative linear-gain theorem states the precise remaining
series-identification obligation; it does not assume a polynomial or phase list.
-/
namespace SparseHamiltonian.ScheduledFractionalAmplifier

noncomputable section
open Polynomial

abbrev index (A : ℝ) : ℕ := ⌊1 / (4 * A)⌋₊

/-- The inverse odd order lies in the coefficient recurrence's positive range. -/
def inverseOrder (A : ℝ) : ℝ := 1 / (AmplifierSignalGeometry.order A : ℝ)

theorem inverseOrder_pos (A : ℝ) : 0 < inverseOrder A := by
  unfold inverseOrder
  exact one_div_pos.mpr (Nat.cast_pos.mpr (AmplifierSignalGeometry.order_pos A))

theorem inverseOrder_le_one (A : ℝ) : inverseOrder A ≤ 1 := by
  have hn : (1 : ℝ) ≤ AmplifierSignalGeometry.order A := by
    exact_mod_cast AmplifierSignalGeometry.order_pos A
  unfold inverseOrder
  apply (div_le_iff₀ (show 0 < (AmplifierSignalGeometry.order A : ℝ) by positivity)).2
  simpa using hn

theorem abs_inverseOrder_le_one (A : ℝ) : |inverseOrder A| ≤ 1 := by
  rw [abs_of_pos (inverseOrder_pos A)]
  exact inverseOrder_le_one A

/-- One explicit polynomial selected only by the public amplitude and precision. -/
def polynomial (A δ : ℝ) : ℝ[X] :=
  AmplifierPolynomialConstruction.amplifier (inverseOrder A) (index A)
    (AmplifierPolynomialConstruction.precisionCutoff δ)

theorem polynomial_odd (A δ : ℝ) :
    (polynomial A δ).comp (-X) = -(polynomial A δ) :=
  AmplifierPolynomialConstruction.amplifier_parity _ _ _

theorem polynomial_bounded (A δ x : ℝ) (hx : |x| ≤ 1) :
    |(polynomial A δ).eval x| ≤ 1 / 2 :=
  AmplifierPolynomialConstruction.amplifier_bounded _ (abs_inverseOrder_le_one A) _ _ _ hx

theorem degree_bound (A δ : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    ((polynomial A δ).natDegree : ℝ) <
      (3 / A) * (Real.log (2 / δ) / Real.log 4 + 1) := by
  have h := AmplifierPolynomialConstruction.scheduled_degree (inverseOrder A) (index A) δ hδ hδ2
  have hn := AmplifierSignalGeometry.order_le A hA hA1
  have he : (AmplifierSignalGeometry.order A : ℝ) = 2 * (index A : ℝ) + 1 := by
    simp [AmplifierSignalGeometry.order, index]
  rw [he] at hn
  have hl : 0 ≤ Real.log (2 / δ) / Real.log 4 + 1 := by
    have hratio : 1 ≤ 2 / δ := (le_div_iff₀ hδ).mpr (by linarith)
    have hlog := Real.log_nonneg hratio
    have hden : 0 < Real.log 4 := Real.log_pos (by norm_num)
    positivity
  change ((polynomial A δ).natDegree : ℝ) < _ at h
  apply h.trans_le
  have hm := mul_le_mul_of_nonneg_left hn hl
  have hd : 2 * (3 / (2 * A)) = 3 / A := by field_simp
  nlinarith

theorem signal_eq (A x : ℝ) (hx : |x| ≤ 1) :
    (AmplifierPolynomialConstruction.signal (index A)).eval x =
      AmplifierSignalGeometry.signal (AmplifierSignalGeometry.order A) x := by
  rw [AmplifierPolynomialConstruction.signal_eval _ _ hx]
  simp [AmplifierSignalGeometry.signal, AmplifierSignalGeometry.order, index]

/-- The polynomial's gain is Θ(1/A), with explicit absolute constants. -/
def gain (A : ℝ) : ℝ := (AmplifierSignalGeometry.order A : ℝ) / 4

theorem gain_pos (A : ℝ) : 0 < gain A := by
  unfold gain
  exact div_pos (Nat.cast_pos.mpr (AmplifierSignalGeometry.order_pos A)) (by norm_num)

theorem gain_mul_bounds (A : ℝ) (hA : 0 < A) (hA1 : A ≤ 1) :
    1 / 16 ≤ gain A * A ∧ gain A * A ≤ 3 / 8 := by
  have h := AmplifierSignalGeometry.order_mul_bounds A hA hA1
  unfold gain
  constructor <;> nlinarith [h.1, h.2]

/-- Relative gain from the exact analytic identification, including zero signal. -/
theorem relative_error_of_series (A δ : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hδ : 0 < δ)
    (hseries : ∀ y : ℝ, |y| ≤ 3 / 8 →
      FractionalAngleCoefficients.series (inverseOrder A) y =
        AmplifierSignalGeometry.correction (AmplifierSignalGeometry.order A) y)
    (x : ℝ) (hx : |x| ≤ A / 4) :
    |(polynomial A δ).eval x - gain A * x| ≤ δ * gain A * |x| := by
  obtain ⟨hx1, _⟩ := AmplifierSignalGeometry.quarter_signal_margin A x hA hA1 hx
  have hsig := AmplifierSignalGeometry.scheduled_signal_bound A x hA hA1 hx
  have hsmall : |(AmplifierPolynomialConstruction.signal (index A)).eval x| ≤ 1 / 2 := by
    rw [signal_eq A x hx1]
    linarith
  have h := AmplifierPolynomialConstruction.amplifier_series_error (inverseOrder A)
    (abs_inverseOrder_le_one A) (index A) (AmplifierPolynomialConstruction.precisionCutoff δ)
    x hx1 hsmall
  rw [signal_eq A x hx1, hseries _ hsig,
    AmplifierSignalGeometry.scheduled_correction A x hA hA1 hx] at h
  have he : 2 * (index A : ℝ) + 1 = (AmplifierSignalGeometry.order A : ℝ) := by
    simp [AmplifierSignalGeometry.order, index]
  rw [he] at h
  have hg : (1 / 4 : ℝ) * ((AmplifierSignalGeometry.order A : ℝ) * x) = gain A * x := by
    unfold gain; ring
  rw [hg] at h
  have hp := AmplifierPolynomialConstruction.precision_cutoff_bound δ hδ
  have hmul := mul_le_mul_of_nonneg_right hp
    (mul_nonneg (gain_pos A).le (abs_nonneg x))
  change |(polynomial A δ).eval x - gain A * x| ≤ _ at h
  unfold gain at h hmul ⊢
  nlinarith

/-- Positive precision cutoffs are forced by the explicit tail bound. -/
theorem precisionCutoff_pos (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < AmplifierPolynomialConstruction.precisionCutoff δ := by
  have h := AmplifierPolynomialConstruction.precision_cutoff_bound δ hδ
  by_contra hn
  have hz : AmplifierPolynomialConstruction.precisionCutoff δ = 0 := by omega
  rw [hz, pow_zero] at h
  linarith

/-- A common phase-pair budget also covers the normalized version of the polynomial. -/
def phaseBudget (A δ : ℝ) : ℕ :=
  AmplifierPolynomialConstruction.precisionCutoff δ * AmplifierSignalGeometry.order A

/-- Exact six-query overlap accounting with an explicit logarithmic upper bound. -/
theorem query_budget (A δ : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((6 * (2 * phaseBudget A δ + 1) : ℕ) : ℝ) <
      (24 / A) * (Real.log (2 / δ) / Real.log 4 + 1) := by
  let L : ℝ := Real.log (2 / δ) / Real.log 4 + 1
  have hlog : 0 ≤ Real.log (2 / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).mpr (by linarith))
  have hL : 1 ≤ L := by
    have hq : 0 ≤ Real.log (2 / δ) / Real.log 4 :=
      div_nonneg hlog (Real.log_pos (by norm_num)).le
    dsimp [L]
    linarith
  have hN := OddChebyshevApproximation.cutoff_lt 2 (Real.log 4) δ
    (Real.log_pos (by norm_num)) hδ (by linarith : δ ≤ 2)
  change (AmplifierPolynomialConstruction.precisionCutoff δ : ℝ) < L at hN
  have hn : 0 < (AmplifierSignalGeometry.order A : ℝ) :=
    Nat.cast_pos.mpr (AmplifierSignalGeometry.order_pos A)
  have hna := (AmplifierSignalGeometry.order_mul_bounds A hA hA1).2
  have hp := mul_lt_mul_of_pos_right hN (mul_pos hn hA)
  have hq := mul_le_mul_of_nonneg_left hna (show 0 ≤ L by linarith)
  have hm : (phaseBudget A δ : ℝ) * A < 3 / 2 * L := by
    simp only [phaseBudget, Nat.cast_mul]
    nlinarith
  have hcast : ((6 * (2 * phaseBudget A δ + 1) : ℕ) : ℝ) =
      12 * (phaseBudget A δ : ℝ) + 6 := by push_cast; ring
  rw [hcast]
  change 12 * (phaseBudget A δ : ℝ) + 6 < 24 / A * L
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ hA).mpr
  nlinarith

end
end SparseHamiltonian.ScheduledFractionalAmplifier
