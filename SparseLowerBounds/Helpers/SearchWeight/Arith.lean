import SparseLowerBounds.Helpers.SearchWeight.Query

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Real arithmetic for `SparseLowerBounds.Query.SearchWeight`

Helper module of group search-weight: the scalar inequalities of lines
2183-2203 of the manuscript. The weight parameter `a = 2 β₀^{-1/(2n)}` is
written out as `2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))` (the term of
`SearchWeight.searchA`).
-/

namespace SparseLowerBounds.Helpers.SearchWeight

noncomputable section

/-- `4√2 a/√m + 4a²/m ≤ 12 a/√m` for `0 ≤ a ≤ √m`. -/
theorem fine_le_twelve {m : ℕ} {a : ℝ} (ha : 0 ≤ a) (ham : a ≤ Real.sqrt m) :
    1 + 4 * Real.sqrt 2 * a / Real.sqrt m + 4 * a ^ 2 / m ≤ 1 + 12 * a / Real.sqrt m := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt m := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
  have hm : (m : ℝ) = s ^ 2 := by rw [hs, Real.sq_sqrt (Nat.cast_nonneg m)]
  rw [← hs] at ham ⊢
  rw [hm]
  rcases hs0.eq_or_lt with h0 | hpos
  · have : a = 0 := by linarith
    subst this
    simp
  · have h2 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    have k1 : 4 * Real.sqrt 2 * a / s ≤ 8 * a / s := by
      rw [div_le_div_iff_of_pos_right hpos]
      nlinarith
    have k2 : 4 * a ^ 2 / s ^ 2 ≤ 4 * a / s := by
      rw [div_le_div_iff₀ (by positivity) hpos]
      nlinarith [mul_nonneg (mul_nonneg ha hpos.le) (sub_nonneg.mpr ham)]
    have k3 : 8 * a / s + 4 * a / s = 12 * a / s := by ring
    linarith

/-- `(1 + 12a/√m)^{2q} ≤ e^{24aq/√m}`. -/
theorem lam_pow_le {a : ℝ} (ha : 0 ≤ a) (m q : ℕ) :
    (1 + 12 * a / Real.sqrt m) ^ (2 * q) ≤ Real.exp (24 * a * q / Real.sqrt m) := by
  have h0 : 0 ≤ 12 * a / Real.sqrt m := by positivity
  calc (1 + 12 * a / Real.sqrt m) ^ (2 * q) ≤ Real.exp (12 * a / Real.sqrt m) ^ (2 * q) := by
        gcongr
        linarith [Real.add_one_le_exp (12 * a / Real.sqrt m)]
    _ = Real.exp (24 * a * q / Real.sqrt m) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring

/-- `a² = 4 β₀^{-1/n}` for `a = 2 β₀^{-1/(2n)}` (every `n`). -/
theorem searchA_sq {n : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    (2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))) ^ 2 = 4 * β₀ ^ (-(1 : ℝ) / n) := by
  have hexp : -(1 : ℝ) / (2 * (n : ℝ)) * ((2 : ℕ) : ℝ) = -(1 : ℝ) / n := by
    rw [Nat.cast_ofNat, show (2 * (n : ℝ)) = n * 2 by ring, ← div_div,
      div_mul_cancel₀ _ two_ne_zero]
  rw [mul_pow, ← Real.rpow_natCast (β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))) 2,
    ← Real.rpow_mul hβ₀.le, hexp]
  norm_num

/-- `a ≥ 1` once `β₀ ≤ 1`. -/
theorem one_le_searchA {n : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ1 : β₀ ≤ 1) :
    1 ≤ 2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ))) := by
  have he : -(1 : ℝ) / (2 * (n : ℝ)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
  have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hβ₀ hβ1 he
  linarith

/-- `a ≤ √m` from `m ≥ 4 β₀^{-1/n}`. -/
theorem searchA_le_sqrt {n m : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀)
    (hmβ : 4 * β₀ ^ (-(1 : ℝ) / n) ≤ m) :
    2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ))) ≤ Real.sqrt m := by
  have hA : 0 ≤ 2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ))) := by positivity
  rw [← Real.sqrt_sq hA, searchA_sq hβ₀]
  exact Real.sqrt_le_sqrt hmβ

/-- `a^{-2n} = 4^{-n} β₀` for `n ≥ 1`. -/
theorem searchA_sq_inv_pow {n : ℕ} (hn : 1 ≤ n) {β₀ : ℝ} (hβ₀ : 0 < β₀) :
    (((2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))) ^ 2)⁻¹) ^ n = ((4 : ℝ) ^ n)⁻¹ * β₀ := by
  rw [searchA_sq hβ₀, mul_inv, mul_pow, inv_pow, neg_div, Real.rpow_neg hβ₀.le, inv_inv,
    one_div, Real.rpow_inv_natCast_pow hβ₀.le (by omega)]

/-- The logarithm step (lines 2200-2203). -/
theorem search_final {n m : ℕ} (hn : 1 ≤ n) {β₀ t : ℝ} (hβ₀ : 0 < β₀)
    (h : β₀ ≤ (((2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))) ^ 2)⁻¹) ^ n *
      Real.exp (24 * (2 * β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ)))) * t / Real.sqrt m)) :
    Real.log 2 / 24 * n * Real.sqrt m * β₀ ^ (1 / (2 * (n : ℝ))) ≤ t := by
  rw [searchA_sq_inv_pow hn hβ₀] at h
  have hA : β₀ ^ (-(1 : ℝ) / (2 * (n : ℝ))) = (β₀ ^ (1 / (2 * (n : ℝ))))⁻¹ := by
    rw [neg_div, Real.rpow_neg hβ₀.le]
  rw [hA] at h
  have hB : 0 < β₀ ^ (1 / (2 * (n : ℝ))) := Real.rpow_pos_of_pos hβ₀ _
  set B := β₀ ^ (1 / (2 * (n : ℝ))) with hBdef
  set X := 24 * (2 * B⁻¹) * t / Real.sqrt m with hX
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  have h1 : (4 : ℝ) ^ n ≤ Real.exp X := by
    have : β₀ * 4 ^ n ≤ β₀ * Real.exp X := by
      calc β₀ * 4 ^ n ≤ (((4 : ℝ) ^ n)⁻¹ * β₀ * Real.exp X) * 4 ^ n :=
            mul_le_mul_of_nonneg_right h h4.le
        _ = β₀ * Real.exp X := by field_simp
    exact le_of_mul_le_mul_left this hβ₀
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) * (2 * Real.log 2) ≤ X := by
    have := Real.log_le_log h4 h1
    rwa [Real.log_exp, Real.log_pow, hlog4] at this
  have hs : 0 < Real.sqrt m := by
    rcases (Real.sqrt_nonneg (m : ℝ)).eq_or_lt with h0 | h0
    · exfalso
      rw [hX, ← h0, div_zero] at h2
      nlinarith
    · exact h0
  have h3 : (n : ℝ) * (2 * Real.log 2) * Real.sqrt m ≤ 24 * (2 * B⁻¹) * t :=
    (le_div_iff₀ hs).mp h2
  have h5 : (n : ℝ) * (2 * Real.log 2) * Real.sqrt m * B ≤ 48 * t := by
    calc _ ≤ 24 * (2 * B⁻¹) * t * B := mul_le_mul_of_nonneg_right h3 hB.le
      _ = 48 * t := by field_simp; ring
  linarith
end
end SparseLowerBounds.Helpers.SearchWeight
end
