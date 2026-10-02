import SparseHamiltonian.AmplifiedBandBudget

/-!
# Public precision allocation for amplified magnitude bands

A single precision is chosen from time, sparsity, the matrix energy bound and
the final error. Its denominator stays positive at zero time or zero energy.
The budget allocates at most one quarter of the final output error to band
approximation and makes every logarithm explicit.
-/
namespace SparseHamiltonian.AmplifiedBandPrecision

noncomputable section
open AmplifiedBandBudget
open scoped BigOperators

/-- Public relative accuracy for each amplified band. -/
def precision (s η t ε : ℝ) : ℝ := ε / (60 * (|t| * η * Real.sqrt s + 1))

/-- One logarithmic envelope serves both the amplifier degree and the band count. -/
def logBudget (s η t ε : ℝ) : ℝ :=
  Real.log (120 * (|t| * η + 1) * (s + 1) / ε) / Real.log 2 + 1

theorem denominator_pos (s η t : ℝ) (hη : 0 ≤ η) :
    0 < 60 * (|t| * η * Real.sqrt s + 1) := by positivity

theorem precision_pos (s η t ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    0 < precision s η t ε := div_pos hε (denominator_pos s η t hη)

theorem precision_le_one (s η t ε : ℝ) (hη : 0 ≤ η) (hε1 : ε ≤ 1) :
    precision s η t ε ≤ 1 := by
  unfold precision
  apply (div_le_one (denominator_pos s η t hη)).mpr
  have hU : 0 ≤ |t| * η * Real.sqrt s := by positivity
  linarith

/-- The scalar band-error sum is at most `15 η sqrt(s) δ`. -/
theorem band_error_sum_le (s η δ : ℝ) (hs : 1 ≤ s) (hη : 0 < η)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (b : ℕ)
    (hbLower : Real.sqrt s ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    (∑ j ∈ Finset.range b, BandCost.normalization s η j * (2 * δ + δ ^ 2)) ≤
      15 * η * Real.sqrt s * δ := by
  have hβ := BandCost.normalization_sum_le hs hη b hbLower hbUpper
  have htail := BandCost.tail_nonneg hs hη.le b
  have hsum : (∑ j ∈ Finset.range b, BandCost.normalization s η j) ≤
      5 * η * Real.sqrt s := by linarith
  have hδpoly : 2 * δ + δ ^ 2 ≤ 3 * δ := by nlinarith
  rw [← Finset.sum_mul]
  calc
    _ ≤ (5 * η * Real.sqrt s) * (2 * δ + δ ^ 2) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ ≤ (5 * η * Real.sqrt s) * (3 * δ) :=
      mul_le_mul_of_nonneg_left hδpoly (by positivity)
    _ = _ := by ring

/-- The chosen precision pays for band perturbation with one quarter of the error. -/
theorem precision_time_error (s η t ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    |t| * (15 * η * Real.sqrt s * precision s η t ε) ≤ ε / 4 := by
  have hδ := (precision_pos s η t ε hη hε).le
  have hden : |t| * η * Real.sqrt s + 1 ≠ 0 := by positivity
  have he : (|t| * η * Real.sqrt s + 1) * precision s η t ε = ε / 60 := by
    unfold precision
    field_simp
  calc
    _ = 15 * ((|t| * η * Real.sqrt s) * precision s η t ε) := by ring
    _ ≤ 15 * ((|t| * η * Real.sqrt s + 1) * precision s η t ε) := by gcongr; linarith
    _ = ε / 4 := by rw [he]; ring

/-- The precision logarithm has an exact formula in public parameters. -/
theorem precisionFactor_eq (s η t ε : ℝ) (hη : 0 ≤ η) (hε : 0 < ε) :
    precisionFactor (precision s η t ε) =
      Real.log (120 * (|t| * η * Real.sqrt s + 1) / ε) / Real.log 4 + 1 := by
  unfold precisionFactor
  congr 3
  unfold precision
  field_simp
  ring

/-- A useful lower bound on the logarithm's argument. -/
theorem logArgument_ge_two_mul (s η t ε : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 * s ≤ 120 * (|t| * η + 1) * (s + 1) / ε := by
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have htη : 0 ≤ |t| * η := mul_nonneg (abs_nonneg t) hη
  apply (le_div_iff₀ hε).mpr
  have h := mul_le_mul_of_nonneg_left hε1 (show 0 ≤ 2 * s by positivity)
  nlinarith [mul_nonneg htη hs0]

theorem logBudget_ge_one (s η t ε : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ logBudget s η t ε := by
  have harg := logArgument_ge_two_mul s η t ε hs hη hε hε1
  have hlog := Real.log_nonneg (show 1 ≤ 120 * (|t| * η + 1) * (s + 1) / ε by linarith)
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold logBudget
  linarith [div_nonneg hlog hd.le]

/-- The amplifier precision factor fits in the single public logarithmic envelope. -/
theorem precisionFactor_le_logBudget (s η t ε : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    precisionFactor (precision s η t ε) ≤ logBudget s η t ε := by
  rw [precisionFactor_eq s η t ε hη hε]
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have htη : 0 ≤ |t| * η := mul_nonneg (abs_nonneg t) hη
  have hroot : Real.sqrt s ≤ s := Real.sqrt_le_self_iff.mpr (Or.inr hs)
  have hU : |t| * η * Real.sqrt s + 1 ≤ (|t| * η + 1) * (s + 1) := by
    have h := mul_le_mul_of_nonneg_left hroot htη
    nlinarith
  have harg : 120 * (|t| * η * Real.sqrt s + 1) / ε ≤
      120 * (|t| * η + 1) * (s + 1) / ε := by
    apply div_le_div_of_nonneg_right _ hε.le
    nlinarith
  have hl := Real.log_le_log (by positivity :
    (0 : ℝ) < 120 * (|t| * η * Real.sqrt s + 1) / ε) harg
  have harg2 := logArgument_ge_two_mul s η t ε hs hη hε hε1
  have hlog : 0 ≤ Real.log (120 * (|t| * η + 1) * (s + 1) / ε) :=
    Real.log_nonneg (by linarith)
  have hd2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hd : Real.log 2 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  unfold logBudget
  exact add_le_add ((div_le_div_of_nonneg_right hl hd4.le).trans
    (div_le_div_of_nonneg_left hlog hd2 hd)) le_rfl

/-- The same envelope also absorbs the logarithmic number of magnitude bands. -/
theorem band_count_le_logBudget (s η t ε : ℝ) (hs : 1 ≤ s) (hη : 0 ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (b : ℕ)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    (b : ℝ) + 1 ≤ logBudget s η t ε := by
  have hb := AmplifiedBandBudget.band_count_le_log s hs b hbUpper
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have harg := logArgument_ge_two_mul s η t ε hs hη hε hε1
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2 * s) harg
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne'] at hl
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hl hd.le
  rw [add_div, div_self hd.ne'] at hdiv
  unfold logBudget
  linarith

end
end SparseHamiltonian.AmplifiedBandPrecision
