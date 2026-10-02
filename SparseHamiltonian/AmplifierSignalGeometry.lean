import SparseHamiltonian.NativeVariableGainCertificate

/-!
# Explicit small-signal geometry and odd amplification order

The integer order is chosen from the known signal bound A, independently of
unknown row sums. Quarter attenuation leaves enough room for the multiple-angle
sine to stay on the principal inverse-sine branch. These lemmas give the exact
analytic linear target and an O(1/A) integer order; polynomial approximation
and its circuit realization are separate constructions.
-/

namespace SparseHamiltonian.AmplifierSignalGeometry

noncomputable section

/-- Multiple-angle sine used by an odd Chebyshev signal. -/
def signal (n : ℕ) (x : ℝ) : ℝ := Real.sin ((n : ℝ) * Real.arcsin x)

/-- The analytic inverse-angle correction, normalized to derivative one. -/
def correction (n : ℕ) (y : ℝ) : ℝ :=
  (n : ℝ) * Real.sin (Real.arcsin y / (n : ℝ))

/-- A uniform elementary inverse-sine estimate on the whole signal interval. -/
theorem abs_arcsin_le_two_mul (x : ℝ) (hx : |x| ≤ 1) :
    |Real.arcsin x| ≤ 2 * |x| := by
  have ha : |Real.arcsin x| ≤ Real.pi / 2 :=
    abs_le.mpr ⟨Real.neg_pi_div_two_le_arcsin x, Real.arcsin_le_pi_div_two x⟩
  have h := Real.mul_abs_le_abs_sin ha
  rw [Real.sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2] at h
  have h' := mul_le_mul_of_nonneg_left h Real.pi_pos.le
  have he : Real.pi * (2 / Real.pi * |Real.arcsin x|) =
      2 * |Real.arcsin x| := by field_simp
  rw [he] at h'
  nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith [Real.pi_lt_four])
    (abs_nonneg x)]

theorem signal_relative_bound (n : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    |signal n x| ≤ (n : ℝ) * |x| := by
  have h := OddChebyshevApproximation.abs_sin_nat_mul n (Real.arcsin x)
  simpa only [signal, Real.sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2] using h

/-- If n|x|≤3/8 then inverse sine recovers the multiple angle exactly. -/
theorem inverse_signal (n : ℕ) (x : ℝ) (hx : |x| ≤ 1)
    (hsmall : (n : ℝ) * |x| ≤ 3 / 8) :
    Real.arcsin (signal n x) = (n : ℝ) * Real.arcsin x := by
  have hb : |(n : ℝ) * Real.arcsin x| ≤ 3 / 4 := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
    have h := mul_le_mul_of_nonneg_left (abs_arcsin_le_two_mul x hx) (Nat.cast_nonneg n)
    nlinarith
  have hpi : (3 : ℝ) / 4 ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  exact Real.arcsin_sin (abs_le.mp (hb.trans hpi)).1 (abs_le.mp (hb.trans hpi)).2

/-- The inverse correction gives an exact linear gain on the promised interval. -/
theorem correction_signal (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : |x| ≤ 1)
    (hsmall : (n : ℝ) * |x| ≤ 3 / 8) :
    correction n (signal n x) = (n : ℝ) * x := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  unfold correction
  rw [inverse_signal n x hx hsmall, mul_div_cancel_left₀ _ hn0,
    Real.sin_arcsin (abs_le.mp hx).1 (abs_le.mp hx).2]

/-- A fixed odd order chosen from the public upper bound A. -/
def order (A : ℝ) : ℕ := 2 * ⌊1 / (4 * A)⌋₊ + 1

theorem order_pos (A : ℝ) : 0 < order A := by unfold order; omega

theorem order_odd (A : ℝ) : Odd (order A) := by
  exact ⟨⌊1 / (4 * A)⌋₊, by unfold order; omega⟩

/-- The integer schedule retains both constant gain and inverse-threshold cost. -/
theorem order_mul_bounds (A : ℝ) (hA : 0 < A) (hA1 : A ≤ 1) :
    1 / 4 ≤ (order A : ℝ) * A ∧ (order A : ℝ) * A ≤ 3 / 2 := by
  have hq : 0 ≤ 1 / (4 * A) := by positivity
  have hlo := Nat.floor_le hq
  have hhi := Nat.lt_floor_add_one (1 / (4 * A))
  have hmul := mul_le_mul_of_nonneg_right hlo hA.le
  have hmul' := mul_lt_mul_of_pos_right hhi hA
  have hid : 1 / (4 * A) * A = 1 / 4 := by field_simp
  rw [hid] at hmul hmul'
  have hn : (order A : ℝ) = 2 * (⌊1 / (4 * A)⌋₊ : ℝ) + 1 := by simp [order]
  rw [hn]
  constructor
  · by_cases ha : A ≤ 1 / 4
    · nlinarith
    · have hf : 0 ≤ (⌊1 / (4 * A)⌋₊ : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hf hA.le]
  · nlinarith

theorem order_le (A : ℝ) (hA : 0 < A) (hA1 : A ≤ 1) :
    (order A : ℝ) ≤ 3 / (2 * A) := by
  have h := (order_mul_bounds A hA hA1).2
  apply (le_div_iff₀ (show 0 < 2 * A by positivity)).2
  nlinarith

/-- Actual quarter-attenuated signals satisfy the strict multiple-angle margin. -/
theorem quarter_signal_margin (A x : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hx : |x| ≤ A / 4) :
    |x| ≤ 1 ∧ (order A : ℝ) * |x| ≤ 3 / 8 := by
  have hn : 0 ≤ (order A : ℝ) := Nat.cast_nonneg _
  have h := mul_le_mul_of_nonneg_left hx hn
  have hu := (order_mul_bounds A hA hA1).2
  constructor <;> nlinarith

theorem scheduled_signal_bound (A x : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hx : |x| ≤ A / 4) : |signal (order A) x| ≤ 3 / 8 := by
  obtain ⟨hx1, hnx⟩ := quarter_signal_margin A x hA hA1 hx
  exact (signal_relative_bound (order A) x hx1).trans hnx

theorem scheduled_correction (A x : ℝ) (hA : 0 < A) (hA1 : A ≤ 1)
    (hx : |x| ≤ A / 4) :
    correction (order A) (signal (order A) x) = (order A : ℝ) * x := by
  obtain ⟨hx1, hnx⟩ := quarter_signal_margin A x hA hA1 hx
  exact correction_signal (order A) (order_pos A) x hx1 hnx

end
end SparseHamiltonian.AmplifierSignalGeometry
