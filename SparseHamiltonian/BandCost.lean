import SparseHamiltonian.MagnitudeBands

/-!
# Finite magnitude-band cost accounting

This file proves scalar inequalities used in the magnitude-band argument.
It does not construct a block encoding or a Hamiltonian simulation circuit.
The integer band count is supplied together with its dyadic sandwich;
no implementation or asymptotic-complexity statement is assumed.
-/

namespace SparseHamiltonian.BandCost

open scoped BigOperators

/-- A dyadic endpoint with the required sandwich always exists.  Minimality is not needed. -/
theorem exists_dyadic_endpoint {s : ℝ} (hs : 1 ≤ s) :
    ∃ b : ℕ, Real.sqrt s ≤ (2 : ℝ) ^ b ∧ (2 : ℝ) ^ b ≤ 2 * Real.sqrt s := by
  obtain ⟨b, hbLower, hbUpper⟩ :=
    exists_nat_pow_near (Real.one_le_sqrt.mpr hs) (by norm_num : (1 : ℝ) < 2)
  refine ⟨b + 1, hbUpper.le, ?_⟩
  rw [pow_succ]
  nlinarith

noncomputable def threshold (η : ℝ) (j : ℕ) : ℝ := η / (2 : ℝ) ^ j

noncomputable def normalization (s η : ℝ) (j : ℕ) : ℝ :=
  min (s * threshold η j) (2 * η ^ 2 / threshold η j)

noncomputable def tailNormalization (s η : ℝ) (b : ℕ) : ℝ :=
  s * η / (2 : ℝ) ^ b

noncomputable def queryRatio (s η : ℝ) (j : ℕ) : ℝ :=
  Real.sqrt (s * threshold η j / normalization s η j)

lemma threshold_pos {η : ℝ} (hη : 0 < η) (j : ℕ) :
    0 < threshold η j := by
  unfold threshold
  positivity

lemma threshold_le {η : ℝ} (hη : 0 ≤ η) (j : ℕ) :
    threshold η j ≤ η := by
  exact div_le_self hη (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

lemma normalization_pos {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η) (j : ℕ) :
    0 < normalization s η j := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have ha := threshold_pos hη j
  unfold normalization
  exact lt_min (by positivity) (by positivity)

lemma threshold_le_normalization {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η)
    (j : ℕ) : threshold η j ≤ normalization s η j := by
  have ha := threshold_pos hη j
  have haη := threshold_le hη.le j
  unfold normalization
  refine le_min ?_ ?_
  · simpa using mul_le_mul_of_nonneg_right hs ha.le
  · apply (le_div_iff₀ ha).2
    have hsq := mul_self_le_mul_self ha.le haη
    nlinarith [sq_nonneg η]

lemma normalization_le_dyadic {s η : ℝ} (hη : 0 < η) (j : ℕ) :
    normalization s η j ≤ 2 * η * (2 : ℝ) ^ j := by
  calc
    normalization s η j ≤ 2 * η ^ 2 / threshold η j := min_le_right _ _
    _ = 2 * η * (2 : ℝ) ^ j := by
      unfold threshold
      field_simp [hη.ne']

lemma sum_two_pow (b : ℕ) :
    (∑ j ∈ Finset.range b, (2 : ℝ) ^ j) = (2 : ℝ) ^ b - 1 := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

lemma tail_nonneg {s η : ℝ} (hs : 1 ≤ s) (hη : 0 ≤ η) (b : ℕ) :
    0 ≤ tailNormalization s η b := by
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  unfold tailNormalization
  positivity

lemma tail_le {s η : ℝ} (hs : 1 ≤ s) (hη : 0 ≤ η) (b : ℕ)
    (hb : Real.sqrt s ≤ (2 : ℝ) ^ b) :
    tailNormalization s η b ≤ η * Real.sqrt s := by
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have hp : 0 < (2 : ℝ) ^ b := by positivity
  unfold tailNormalization
  apply (div_le_iff₀ hp).2
  have hprod := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg s)
  rw [Real.mul_self_sqrt hs0] at hprod
  have hprodη := mul_le_mul_of_nonneg_left hprod hη
  nlinarith

/-- Explicit normalization bound, including the untruncated tail. -/
theorem normalization_sum_le {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η) (b : ℕ)
    (hbLower : Real.sqrt s ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    (∑ j ∈ Finset.range b, normalization s η j) + tailNormalization s η b ≤
      5 * η * Real.sqrt s := by
  have hsum : (∑ j ∈ Finset.range b, normalization s η j) ≤
      2 * η * ((2 : ℝ) ^ b - 1) := by
    calc
      (∑ j ∈ Finset.range b, normalization s η j) ≤
          ∑ j ∈ Finset.range b, 2 * η * (2 : ℝ) ^ j :=
        Finset.sum_le_sum (fun j _ => normalization_le_dyadic hη j)
      _ = 2 * η * ((2 : ℝ) ^ b - 1) := by
        rw [← Finset.mul_sum, sum_two_pow]
  have htail := tail_le hs hη.le b hbLower
  have hmul := mul_le_mul_of_nonneg_left hbUpper hη.le
  nlinarith

/-- The normalization-query tradeoff for one band. -/
theorem weighted_band_le {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η) (j : ℕ) :
    Real.sqrt (s * threshold η j * normalization s η j) ≤
      Real.sqrt 2 * η * Real.sqrt s := by
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  have ha := threshold_pos hη j
  have hβ := min_le_right (s * threshold η j) (2 * η ^ 2 / threshold η j)
  change normalization s η j ≤ 2 * η ^ 2 / threshold η j at hβ
  have hmul := mul_le_mul_of_nonneg_left hβ (show 0 ≤ s * threshold η j by positivity)
  have hcancel : s * threshold η j * (2 * η ^ 2 / threshold η j) =
      2 * s * η ^ 2 := by
    field_simp [ha.ne']
  rw [hcancel] at hmul
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsq : (Real.sqrt 2 * η * Real.sqrt s) ^ 2 = 2 * s * η ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hs0]
    ring
  rw [hsq]
  exact hmul

lemma normalization_mul_queryRatio {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η)
    (j : ℕ) :
    normalization s η j * queryRatio s η j =
      Real.sqrt (s * threshold η j * normalization s η j) := by
  have hβ := normalization_pos hs hη j
  unfold queryRatio
  calc
    normalization s η j * Real.sqrt (s * threshold η j / normalization s η j) =
        Real.sqrt ((normalization s η j) ^ 2) *
          Real.sqrt (s * threshold η j / normalization s η j) := by
      rw [Real.sqrt_sq hβ.le]
    _ = Real.sqrt ((normalization s η j) ^ 2 *
          (s * threshold η j / normalization s η j)) :=
      (Real.sqrt_mul (sq_nonneg _) _).symm
    _ = Real.sqrt (s * threshold η j * normalization s η j) := by
      congr 1
      field_simp [hβ.ne']

/-- The per-band query multiplier never exceeds `sqrt s`. -/
theorem queryRatio_le {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η) (j : ℕ) :
    queryRatio s η j ≤ Real.sqrt s := by
  have hβ := normalization_pos hs hη j
  have haβ := threshold_le_normalization hs hη j
  have hs0 : 0 ≤ s := le_trans zero_le_one hs
  apply Real.sqrt_le_sqrt
  apply (div_le_iff₀ hβ).2
  exact mul_le_mul_of_nonneg_left haβ hs0

/-- The weighted costs of all bands plus the exact tail have a linear band-count bound. -/
theorem weighted_sum_le {s η : ℝ} (hs : 1 ≤ s) (hη : 0 < η) (b : ℕ)
    (hbLower : Real.sqrt s ≤ (2 : ℝ) ^ b) :
    (∑ j ∈ Finset.range b, normalization s η j * queryRatio s η j) +
        tailNormalization s η b ≤
      (Real.sqrt 2 * (b : ℝ) + 1) * η * Real.sqrt s := by
  have hsum : (∑ j ∈ Finset.range b, normalization s η j * queryRatio s η j) ≤
      (b : ℝ) * (Real.sqrt 2 * η * Real.sqrt s) := by
    calc
      (∑ j ∈ Finset.range b, normalization s η j * queryRatio s η j) ≤
          ∑ _j ∈ Finset.range b, Real.sqrt 2 * η * Real.sqrt s := by
        apply Finset.sum_le_sum
        intro j _
        rw [normalization_mul_queryRatio hs hη j]
        exact weighted_band_le hs hη j
      _ = (b : ℝ) * (Real.sqrt 2 * η * Real.sqrt s) := by simp
  have htail := tail_le hs hη.le b hbLower
  nlinarith

/-- Conditional scalar accounting: a supplied query-cost estimate yields a uniform bound.
This theorem does not assert the existence of a circuit with the supplied estimate. -/
theorem query_cost_le {s η C ℓ q : ℝ} (hs : 1 ≤ s) (hη : 0 < η)
    (hC : 0 ≤ C) (hℓ : 0 ≤ ℓ) (j : ℕ)
    (hq : q ≤ C * ℓ * queryRatio s η j) :
    q ≤ C * ℓ * Real.sqrt s := by
  exact hq.trans (mul_le_mul_of_nonneg_left (queryRatio_le hs hη j) (mul_nonneg hC hℓ))

/-- Conditional finite accounting for supplied band and tail query costs.
The hypotheses are scalar cost bounds, not an assertion that oracle circuits exist. -/
theorem weighted_query_cost_sum_le {s η C ℓ qTail : ℝ}
    (hs : 1 ≤ s) (hη : 0 < η) (hC : 0 ≤ C) (hℓ : 0 ≤ ℓ)
    (b : ℕ) (hbLower : Real.sqrt s ≤ (2 : ℝ) ^ b) (q : ℕ → ℝ)
    (hq : ∀ j ∈ Finset.range b, q j ≤ C * ℓ * queryRatio s η j)
    (hTail : qTail ≤ C * ℓ) :
    (∑ j ∈ Finset.range b, normalization s η j * q j) +
        tailNormalization s η b * qTail ≤
      C * ℓ * ((Real.sqrt 2 * (b : ℝ) + 1) * η * Real.sqrt s) := by
  have hsum : (∑ j ∈ Finset.range b, normalization s η j * q j) ≤
      C * ℓ * (∑ j ∈ Finset.range b, normalization s η j * queryRatio s η j) := by
    calc
      (∑ j ∈ Finset.range b, normalization s η j * q j) ≤
          ∑ j ∈ Finset.range b, normalization s η j *
            (C * ℓ * queryRatio s η j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hq j hj) (normalization_pos hs hη j).le
      _ = C * ℓ * (∑ j ∈ Finset.range b,
          normalization s η j * queryRatio s η j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have htail := mul_le_mul_of_nonneg_left hTail (tail_nonneg hs hη.le b)
  calc
    (∑ j ∈ Finset.range b, normalization s η j * q j) +
        tailNormalization s η b * qTail ≤
        C * ℓ * ((∑ j ∈ Finset.range b,
          normalization s η j * queryRatio s η j) + tailNormalization s η b) := by
      nlinarith
    _ ≤ C * ℓ * ((Real.sqrt 2 * (b : ℝ) + 1) * η * Real.sqrt s) :=
      mul_le_mul_of_nonneg_left (weighted_sum_le hs hη b hbLower) (mul_nonneg hC hℓ)

end SparseHamiltonian.BandCost
