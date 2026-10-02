import SparseHamiltonian.ActualAmplifiedBands

/-!
# Explicit resource accounting for amplified magnitude bands

These scalar lemmas retain the normalization inflation, the integer query
count and the two fixed clock links. The actual native program family is
instantiated in `ActualAmplifiedBandResources`.
-/
namespace SparseHamiltonian.AmplifiedBandBudget

noncomputable section
open scoped BigOperators

/-- Precision factor in the constructed amplifier's primitive-query bound. -/
def precisionFactor (δ : ℝ) : ℝ := Real.log (2 / δ) / Real.log 4 + 1

theorem precisionFactor_ge_one (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ precisionFactor δ := by
  have hlog : 0 ≤ Real.log (2 / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have hd : 0 < Real.log 4 := Real.log_pos (by norm_num)
  unfold precisionFactor
  linarith [div_nonneg hlog hd.le]

/-- Each band's bare query ratio is at least one. -/
theorem queryRatio_ge_one (s η : ℝ) (hs : 1 ≤ s) (hη : 0 < η) (j : ℕ) :
    1 ≤ BandCost.queryRatio s η j := by
  have hβ := BandCost.normalization_pos hs hη j
  unfold BandCost.queryRatio
  apply Real.one_le_sqrt.mpr
  apply (one_le_div hβ).2
  exact min_le_left _ _

/-- The two fixed clock links change the per-band constant from 24 to 26. -/
theorem clock_count_le (s η δ : ℝ) (hs : 1 ≤ s) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j q : ℕ)
    (hq : (q : ℝ) < 24 * BandCost.queryRatio s η j * precisionFactor δ) :
    ((q + 2 : ℕ) : ℝ) ≤ 26 * precisionFactor δ * BandCost.queryRatio s η j := by
  have hr := queryRatio_ge_one s η hs hη j
  have hL := precisionFactor_ge_one δ hδ hδ1
  have hprod : 1 ≤ precisionFactor δ * BandCost.queryRatio s η j :=
    one_le_mul_of_one_le_of_one_le hL hr
  push_cast
  nlinarith

/-- A common real upper bound for every actual clock length. -/
theorem max_clock_count_le (s η δ : ℝ) (hs : 1 ≤ s) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j q : ℕ)
    (hq : (q : ℝ) < 24 * BandCost.queryRatio s η j * precisionFactor δ) :
    ((q + 2 : ℕ) : ℝ) ≤ 26 * precisionFactor δ * Real.sqrt s := by
  have hL := precisionFactor_ge_one δ hδ hδ1
  exact (clock_count_le s η δ hs hη hδ hδ1 j q hq).trans
    (mul_le_mul_of_nonneg_left (BandCost.queryRatio_le hs hη j) (by positivity))

/-- The exact six-query tail and its two fixed clock links obey the same common bound. -/
theorem tail_clock_count_le (s δ : ℝ) (hs : 1 ≤ s)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (8 : ℝ) ≤ 26 * precisionFactor δ * Real.sqrt s := by
  have hL := precisionFactor_ge_one δ hδ hδ1
  have hr := Real.one_le_sqrt.mpr hs
  nlinarith [one_le_mul_of_one_le_of_one_le hL hr]

/-- The per-band weighted clock cost includes actual normalization inflation. -/
theorem weighted_band_le (s η δ α : ℝ) (hs : 1 ≤ s) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j q : ℕ)
    (hα : α ≤ 1024 * BandCost.normalization s η j)
    (hq : (q : ℝ) < 24 * BandCost.queryRatio s η j * precisionFactor δ) :
    α * ((q + 2 : ℕ) : ℝ) ≤
      26624 * precisionFactor δ *
        (BandCost.normalization s η j * BandCost.queryRatio s η j) := by
  have hcount := clock_count_le s η δ hs hη hδ hδ1 j q hq
  have hβ := BandCost.normalization_pos hs hη j
  calc
    α * ((q + 2 : ℕ) : ℝ) ≤ 1024 * BandCost.normalization s η j * ((q + 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)
    _ ≤ 1024 * BandCost.normalization s η j *
        (26 * precisionFactor δ * BandCost.queryRatio s η j) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

/-- Weighted cost of the finite family, including the exact tail. -/
theorem weighted_sum_le (s η δ : ℝ) (hs : 1 ≤ s) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (b : ℕ)
    (hb : Real.sqrt s ≤ (2 : ℝ) ^ b) (α : Fin b → ℝ) (q : Fin b → ℕ)
    (hα : ∀ j, α j ≤ 1024 * BandCost.normalization s η j)
    (hq : ∀ j, (q j : ℝ) < 24 * BandCost.queryRatio s η j * precisionFactor δ) :
    (∑ j, α j * ((q j + 2 : ℕ) : ℝ)) + 8 * BandCost.tailNormalization s η b ≤
      26624 * precisionFactor δ * ((Real.sqrt 2 * (b : ℝ) + 1) * η * Real.sqrt s) := by
  have hsum : (∑ j, α j * ((q j + 2 : ℕ) : ℝ)) ≤
      26624 * precisionFactor δ *
        ∑ j ∈ Finset.range b, BandCost.normalization s η j * BandCost.queryRatio s η j := by
    calc
      _ ≤ ∑ j : Fin b, 26624 * precisionFactor δ *
          (BandCost.normalization s η j * BandCost.queryRatio s η j) :=
        Finset.sum_le_sum (fun j _ => weighted_band_le s η δ (α j) hs hη hδ hδ1 j (q j)
          (hα j) (hq j))
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun j =>
          BandCost.normalization s η j * BandCost.queryRatio s η j) b
  have htail := BandCost.tail_nonneg hs hη.le b
  have hL := precisionFactor_ge_one δ hδ hδ1
  have htailcost : 8 * BandCost.tailNormalization s η b ≤
      26624 * precisionFactor δ * BandCost.tailNormalization s η b := by
    nlinarith
  calc
    _ ≤ 26624 * precisionFactor δ *
        ((∑ j ∈ Finset.range b, BandCost.normalization s η j * BandCost.queryRatio s η j) +
          BandCost.tailNormalization s η b) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (BandCost.weighted_sum_le hs hη b hb) (by positivity)

/-- Total actual normalization is still bounded independently of the band count. -/
theorem normalization_sum_le (s η : ℝ) (hs : 1 ≤ s) (hη : 0 < η) (b : ℕ)
    (hbLower : Real.sqrt s ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) (α : Fin b → ℝ)
    (hα : ∀ j, α j ≤ 1024 * BandCost.normalization s η j) :
    (∑ j, α j) + BandCost.tailNormalization s η b ≤ 5120 * η * Real.sqrt s := by
  have hsum : (∑ j, α j) ≤ 1024 * ∑ j ∈ Finset.range b, BandCost.normalization s η j := by
    calc
      _ ≤ ∑ j : Fin b, 1024 * BandCost.normalization s η j :=
        Finset.sum_le_sum (fun j _ => hα j)
      _ = _ := by rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
  have htail := BandCost.tail_nonneg hs hη.le b
  have hbudget := BandCost.normalization_sum_le hs hη b hbLower hbUpper
  nlinarith

/-- The dyadic endpoint promise itself certifies a logarithmic band count. -/
theorem band_count_le_log (s : ℝ) (hs : 1 ≤ s) (b : ℕ)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    (b : ℝ) ≤ 1 + Real.log s / Real.log 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hroot : Real.sqrt s ≤ s := Real.sqrt_le_self_iff.mpr (Or.inr hs)
  have hpow : (2 : ℝ) ^ b ≤ 2 * s := hbUpper.trans (by linarith)
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ b) hpow
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs0.ne'] at hlog
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (b : ℝ) ≤ (Real.log 2 + Real.log s) / Real.log 2 :=
      (le_div_iff₀ hd).mpr hlog
    _ = 1 + Real.log s / Real.log 2 := by rw [add_div, div_self hd.ne']

end
end SparseHamiltonian.AmplifiedBandBudget
