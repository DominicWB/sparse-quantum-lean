import SparseHamiltonian.NormalizedAmplifierCompletion

/-!
# Termwise derivatives of the explicit fractional-angle series
-/
namespace SparseHamiltonian.FractionalAngleSeriesDifferentiation

noncomputable section
open FractionalAngleCoefficients
open scoped BigOperators

/-- First derivative written without negative exponents. -/
def firstDerivative (a y : ℝ) : ℝ :=
  ∑' k : ℕ, coefficient a k * (2 * (k : ℝ) + 1) * y ^ (2 * k)

/-- Second derivative, omitting the identically zero initial term. -/
def secondDerivative (a y : ℝ) : ℝ :=
  ∑' k : ℕ, coefficient a (k + 1) * (2 * (k : ℝ) + 3) *
    (2 * k + 2) * y ^ (2 * k + 1)

/-- Individual coefficients are uniformly bounded by the full positive mass. -/
theorem coefficient_le_two (a : ℝ) (ha : |a| ≤ 1) (k : ℕ) : coefficient a k ≤ 2 := by
  exact ((summable_coefficient a ha).le_tsum k (fun _ _ => coefficient_nonneg a ha _)).trans
    (tsum_coefficient_le_two a ha)

/-- A polynomially weighted geometric majorant, used by both derivative series. -/
theorem summable_majorant (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun k : ℕ => (8 * (k : ℝ) ^ 2 + 20 * k + 12) * (ρ ^ 2) ^ k) := by
  have hr : ‖ρ ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ρ)]
    nlinarith
  have h0 := summable_geometric_of_norm_lt_one hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hs : Summable (fun k : ℕ => 8 * ((k : ℝ) ^ 2 * (ρ ^ 2) ^ k) +
      20 * ((k : ℝ) ^ 1 * (ρ ^ 2) ^ k) + 12 * (ρ ^ 2) ^ k) :=
    ((h2.mul_left 8).add (h1.mul_left 20)).add (h0.mul_left 12)
  exact hs.congr (fun k => by ring)

/-- The first-derivative terms have a summable uniform bound on each smaller interval. -/
theorem first_bound (a : ℝ) (ha : |a| ≤ 1) (ρ y : ℝ)
    (_hρ0 : 0 ≤ ρ) (hy : |y| ≤ ρ) (k : ℕ) :
    ‖coefficient a k * (2 * (k : ℝ) + 1) * y ^ (2 * k)‖ ≤
      (8 * (k : ℝ) ^ 2 + 20 * k + 12) * (ρ ^ 2) ^ k := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (coefficient_nonneg a ha k),
    abs_of_nonneg (by positivity : 0 ≤ 2 * (k : ℝ) + 1), abs_pow]
  have hc := coefficient_le_two a ha k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hp : |y| ^ (2 * k) ≤ (ρ ^ 2) ^ k := by
    rw [← pow_mul]
    exact pow_le_pow_left₀ (abs_nonneg y) hy _
  apply mul_le_mul _ hp (by positivity) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_right hc (show 0 ≤ 2 * (k : ℝ) + 1 by positivity),
    sq_nonneg (k : ℝ)]

/-- The second derivative obeys the same majorant. -/
theorem second_bound (a : ℝ) (ha : |a| ≤ 1) (ρ y : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hy : |y| ≤ ρ) (k : ℕ) :
    ‖coefficient a (k + 1) * (2 * (k : ℝ) + 3) * (2 * k + 2) * y ^ (2 * k + 1)‖ ≤
      (8 * (k : ℝ) ^ 2 + 20 * k + 12) * (ρ ^ 2) ^ k := by
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (coefficient_nonneg a ha (k + 1)),
    abs_of_nonneg (by positivity : 0 ≤ 2 * (k : ℝ) + 3),
    abs_of_nonneg (by positivity : 0 ≤ 2 * (k : ℝ) + 2), abs_pow]
  have hc := coefficient_le_two a ha (k + 1)
  have hp : |y| ^ (2 * k + 1) ≤ (ρ ^ 2) ^ k := by
    calc
      |y| ^ (2 * k + 1) ≤ ρ ^ (2 * k + 1) := pow_le_pow_left₀ (abs_nonneg y) hy _
      _ ≤ ρ ^ (2 * k) := pow_le_pow_of_le_one hρ0 hρ1 (by omega)
      _ = (ρ ^ 2) ^ k := pow_mul _ _ _
  apply mul_le_mul _ hp (by positivity) (by positivity)
  have hm := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ (2 * (k : ℝ) + 3) * (2 * k + 2) by positivity)
  nlinarith

/-- Both derivative series converge absolutely at every interior signal. -/
theorem summable_first (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    Summable (fun k : ℕ => coefficient a k * (2 * (k : ℝ) + 1) * y ^ (2 * k)) :=
  (summable_majorant |y| (abs_nonneg y) hy).of_norm_bounded
    (first_bound a ha |y| y (abs_nonneg y) le_rfl)

theorem summable_second (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    Summable (fun k : ℕ => coefficient a (k + 1) * (2 * (k : ℝ) + 3) *
      (2 * k + 2) * y ^ (2 * k + 1)) :=
  (summable_majorant |y| (abs_nonneg y) hy).of_norm_bounded
    (second_bound a ha |y| y (abs_nonneg y) hy.le le_rfl)

/-- The first termwise derivative is justified on a neighborhood of each interior point. -/
theorem hasDerivAt_series (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    HasDerivAt (series a) (firstDerivative a y) y := by
  let ρ := (|y| + 1) / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hyρ : |y| < ρ := by dsimp [ρ]; linarith
  unfold series firstDerivative
  apply hasDerivAt_tsum_of_isPreconnected (g := fun k z => coefficient a k * z ^ (2 * k + 1))
    (g' := fun k z => coefficient a k * (2 * (k : ℝ) + 1) * z ^ (2 * k))
    (y₀ := 0) (summable_majorant ρ hρ0.le hρ1)
    isOpen_Ioo (convex_Ioo (-ρ) ρ).isPreconnected
  · intro k z _
    simpa [mul_assoc] using (hasDerivAt_pow (2 * k + 1) z).const_mul (coefficient a k)
  · intro k z hz
    exact first_bound a ha ρ z hρ0.le (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) k
  · exact ⟨neg_neg_of_pos hρ0, hρ0⟩
  · simp
  · exact abs_lt.mp hyρ

/-- Reindexing the first derivative isolates its constant term. -/
theorem first_eq_one_add (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    firstDerivative a y = 1 +
      ∑' k : ℕ, coefficient a (k + 1) * (2 * (k : ℝ) + 3) * y ^ (2 * k + 2) := by
  have h := (summable_first a ha y hy).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, coefficient_zero,
    mul_one, pow_zero] at h
  rw [firstDerivative]
  rw [← h]
  congr 1
  apply tsum_congr
  intro k
  push_cast
  congr 2
  ring

/-- The second termwise derivative, justified without endpoint differentiability claims. -/
theorem hasDerivAt_firstDerivative (a : ℝ) (ha : |a| ≤ 1) (y : ℝ) (hy : |y| < 1) :
    HasDerivAt (firstDerivative a) (secondDerivative a y) y := by
  let ρ := (|y| + 1) / 2
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hyρ : |y| < ρ := by dsimp [ρ]; linarith
  have hd : HasDerivAt
      (fun z : ℝ => ∑' k : ℕ,
        coefficient a (k + 1) * (2 * (k : ℝ) + 3) * z ^ (2 * k + 2))
      (secondDerivative a y) y := by
    unfold secondDerivative
    apply hasDerivAt_tsum_of_isPreconnected
      (g := fun k z => coefficient a (k + 1) * (2 * (k : ℝ) + 3) * z ^ (2 * k + 2))
      (g' := fun k z => coefficient a (k + 1) * (2 * (k : ℝ) + 3) *
        (2 * k + 2) * z ^ (2 * k + 1))
      (y₀ := 0) (summable_majorant ρ hρ0.le hρ1)
      isOpen_Ioo (convex_Ioo (-ρ) ρ).isPreconnected
    · intro k z _
      simpa [mul_assoc] using (hasDerivAt_pow (2 * k + 2) z).const_mul
        (coefficient a (k + 1) * (2 * (k : ℝ) + 3))
    · intro k z hz
      exact second_bound a ha ρ z hρ0.le hρ1.le (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) k
    · exact ⟨neg_neg_of_pos hρ0, hρ0⟩
    · simp
    · exact abs_lt.mp hyρ
  apply (hd.const_add 1).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (show y ∈ Set.Ioo (-1 : ℝ) 1 from abs_lt.mp hy)] with z hz
  exact first_eq_one_add a ha z (abs_lt.mpr hz)

@[simp] theorem series_zero (a : ℝ) : series a 0 = 0 := by simp [series]

@[simp] theorem firstDerivative_zero (a : ℝ) (ha : |a| ≤ 1) : firstDerivative a 0 = 1 := by
  rw [first_eq_one_add a ha 0 (by norm_num)]
  simp

end
end SparseHamiltonian.FractionalAngleSeriesDifferentiation
