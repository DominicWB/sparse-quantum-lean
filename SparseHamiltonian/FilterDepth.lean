import SparseHamiltonian.ScalarFilterBounds

/-!
# Logarithmic repetition schedule

This is scalar precision bookkeeping: a quantity bounded by `C * (1/2)^k`
is at most `δ` after logarithmically many repetitions. No operator filter
estimate is assumed or derived in this module.
-/

namespace SparseHamiltonian.FilterDepth

/-- The real-valued repetition threshold, clipped at zero. -/
noncomputable def realDepth (C δ : ℝ) : ℝ :=
  max 0 (Real.log (C / δ) / Real.log 2)

/-- A concrete natural repetition count. -/
noncomputable def depth (C δ : ℝ) : ℕ := ⌈realDepth C δ⌉₊

theorem realDepth_nonneg (C δ : ℝ) : 0 ≤ realDepth C δ := le_max_left _ _

theorem depth_ge_log_ratio (C δ : ℝ) :
    Real.log (C / δ) / Real.log 2 ≤ (depth C δ : ℝ) :=
  (le_max_right _ _).trans (Nat.le_ceil (realDepth C δ))

theorem depth_lt_log_ratio_add_one (C δ : ℝ) :
    (depth C δ : ℝ) < max 0 (Real.log (C / δ) / Real.log 2) + 1 :=
  Nat.ceil_lt_add_one (realDepth_nonneg C δ)

/-- Any natural repetition count above the logarithmic threshold suffices. -/
theorem decay_le_of_log_depth (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ)
    (k : ℕ) (hk : Real.log (C / δ) / Real.log 2 ≤ (k : ℝ)) :
    C * (1 / 2 : ℝ) ^ k ≤ δ := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hratio : 0 < C / δ := div_pos hC hδ
  have hpow : (0 : ℝ) < 2 ^ k := pow_pos (by norm_num) _
  have hthreshold : Real.log (C / δ) ≤ (k : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog).mp hk
  have hratio_le : C / δ ≤ (2 : ℝ) ^ k := by
    apply (Real.log_le_log_iff hratio hpow).mp
    rw [Real.log_pow]
    exact hthreshold
  have hC_le : C ≤ δ * (2 : ℝ) ^ k := by
    have h := (div_le_iff₀ hδ).mp hratio_le
    simpa only [mul_comm] using h
  rw [one_div_pow, one_div, ← div_eq_mul_inv]
  exact (div_le_iff₀ hpow).mpr hC_le

theorem depth_decay_le (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    C * (1 / 2 : ℝ) ^ depth C δ ≤ δ :=
  decay_le_of_log_depth C δ hC hδ (depth C δ) (depth_ge_log_ratio C δ)

/-- The schedule exists with the claimed logarithmic upper bound. -/
theorem exists_logarithmic_depth (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ k : ℕ, C * (1 / 2 : ℝ) ^ k ≤ δ ∧
      (k : ℝ) < max 0 (Real.log (C / δ) / Real.log 2) + 1 :=
  ⟨depth C δ, depth_decay_le C δ hC hδ, depth_lt_log_ratio_add_one C δ⟩

end SparseHamiltonian.FilterDepth
