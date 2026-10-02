import SparseHamiltonian.FilterDecay

/-!
# Concrete precision and degree schedule

This module supplies the scalar bookkeeping for a filter whose norm is bounded
by `prefactor Q W * (1/4)^k`.  It proves the stronger precision estimate with
`(1/2)^k`, a sufficient degree for smoothing, and an explicit upper degree bound.
The operator estimate is proved separately in `FilterDecay` and `GlobalFilter`.
-/

namespace SparseHamiltonian.FilterSchedule

noncomputable section

def logBudget (Q W δ : ℝ) : ℝ := Real.log ((Q + W + 2) / δ)

def realDepth (Q W δ : ℝ) : ℝ := 2 * W / Q + 2 * logBudget Q W δ

def length (Q : ℝ) : ℕ := ⌈32 * Q⌉₊

def depth (Q W δ : ℝ) : ℕ := 1 + ⌈realDepth Q W δ⌉₊

def degree (Q W δ : ℝ) : ℕ := depth Q W δ * (length Q - 1)

def prefactor (Q W : ℝ) : ℝ :=
  (3 * (Q + W) / (4 * Q)) * Real.exp (3 * W / (4 * Q))

theorem logBudget_nonneg (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ logBudget Q W δ := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hδ).mpr
  linarith

theorem realDepth_nonneg (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ realDepth Q W δ := by
  unfold realDepth
  exact add_nonneg (div_nonneg (by positivity) (by linarith))
    (mul_nonneg (by norm_num) (logBudget_nonneg Q W δ hQ hW hδ hδ1))

theorem depth_pos (Q W δ : ℝ) : 0 < depth Q W δ := by
  unfold depth
  omega

theorem length_ge (Q : ℝ) : 32 * Q ≤ (length Q : ℝ) := Nat.le_ceil _

theorem depth_ge (Q W δ : ℝ) : realDepth Q W δ ≤ (depth Q W δ : ℝ) := by
  have h := Nat.le_ceil (realDepth Q W δ)
  simp only [depth, Nat.cast_add, Nat.cast_one]
  linarith

theorem depth_lt (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (depth Q W δ : ℝ) < realDepth Q W δ + 2 := by
  have h := Nat.ceil_lt_add_one (realDepth_nonneg Q W δ hQ hW hδ hδ1)
  simp only [depth, Nat.cast_add, Nat.cast_one]
  linarith

theorem prefactor_pos (Q W : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W) :
    0 < prefactor Q W := by
  unfold prefactor
  apply mul_pos
  · apply div_pos <;> nlinarith
  · exact Real.exp_pos _

theorem log_prefactor_ratio_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) :
    Real.log (prefactor Q W / δ) ≤ 3 * W / (4 * Q) + logBudget Q W δ := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < 3 * (Q + W) / (4 * Q) := by positivity
  have ha_le : 3 * (Q + W) / (4 * Q) ≤ Q + W + 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * Q)).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ Q - 1) (by linarith : 0 ≤ Q + W)]
  have hratio : 0 < (3 * (Q + W) / (4 * Q)) / δ := div_pos ha hδ
  have hlog := Real.log_le_log hratio (div_le_div_of_nonneg_right ha_le (le_of_lt hδ))
  have heq : prefactor Q W / δ =
      ((3 * (Q + W) / (4 * Q)) / δ) * Real.exp (3 * W / (4 * Q)) := by
    unfold prefactor
    ring
  rw [heq, Real.log_mul (ne_of_gt hratio) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  unfold logBudget
  linarith

/-- The logarithmic count controls even the weaker geometric decay factor. -/
theorem half_decay_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) :
    prefactor Q W * (1 / 2 : ℝ) ^ depth Q W δ ≤ δ := by
  apply FilterDepth.decay_le_of_log_depth _ _ (prefactor_pos Q W hQ hW) hδ
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2pos : 0 < Real.log (2 : ℝ) := by linarith
  apply (div_le_iff₀ hlog2pos).mpr
  have hbound := log_prefactor_ratio_le Q W δ hQ hW hδ
  have hk := depth_ge Q W δ
  have hproduct := mul_le_mul_of_nonneg_left hlog2 (show (0 : ℝ) ≤ depth Q W δ by positivity)
  have hWQ : 0 ≤ W / Q := div_nonneg hW (by linarith)
  unfold realDepth at hk
  have hquarter : 3 * W / (4 * Q) = (3 / 4 : ℝ) * (W / Q) := by ring
  have htwo : 2 * W / Q = 2 * (W / Q) := by ring
  rw [hquarter] at hbound
  rw [htwo] at hk
  nlinarith

/-- Precision bound for the expected analytic filter estimate. -/
theorem quarter_decay_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) :
    prefactor Q W * (1 / 4 : ℝ) ^ depth Q W δ ≤ δ := by
  apply le_trans _ (half_decay_le Q W δ hQ hW hδ)
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (prefactor_pos Q W hQ hW))
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

theorem length_sub_one_bounds (Q : ℝ) (hQ : 1 ≤ Q) :
    Q ≤ ((length Q - 1 : ℕ) : ℝ) ∧ ((length Q - 1 : ℕ) : ℝ) < 32 * Q := by
  have hlen : 1 ≤ length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  rw [Nat.cast_sub hlen, Nat.cast_one]
  have hlo := length_ge Q
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 32 * Q by linarith)
  change (length Q : ℝ) < 32 * Q + 1 at hhi
  constructor <;> linarith

theorem degree_pos (Q W δ : ℝ) (hQ : 1 ≤ Q) : 1 ≤ degree Q W δ := by
  have hL : (1 : ℝ) ≤ ((length Q - 1 : ℕ) : ℝ) :=
    hQ.trans (length_sub_one_bounds Q hQ).1
  have hLnat : 1 ≤ length Q - 1 := by exact_mod_cast hL
  exact Nat.mul_pos (depth_pos Q W δ) hLnat

/-- The polynomial degree is sufficient for a smoothing budget of `2W`. -/
theorem degree_ge (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * W ≤ (degree Q W δ : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hk := depth_ge Q W δ
  have hlog := logBudget_nonneg Q W δ hQ hW hδ hδ1
  have hklo : 2 * W / Q ≤ (depth Q W δ : ℝ) := by
    unfold realDepth at hk
    linarith
  have hlen := (length_sub_one_bounds Q hQ).1
  have hprod := mul_le_mul hklo hlen (show 0 ≤ Q by linarith)
    (show (0 : ℝ) ≤ depth Q W δ by positivity)
  have heq : (2 * W / Q) * Q = 2 * W := by field_simp
  rw [heq] at hprod
  simpa only [degree, Nat.cast_mul] using hprod

/-- The chosen length leaves substantial slack in the smoothing degree. -/
theorem degree_ge_sixtyTwo (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    62 * W ≤ (degree Q W δ : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hk := depth_ge Q W δ
  have hlog := logBudget_nonneg Q W δ hQ hW hδ hδ1
  have hklo : 2 * W / Q ≤ (depth Q W δ : ℝ) := by
    unfold realDepth at hk
    linarith
  have hlen : 1 ≤ length Q := Nat.one_le_ceil_iff.mpr (by linarith)
  have hlenlo : 31 * Q ≤ ((length Q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlen, Nat.cast_one]
    have h := length_ge Q
    linarith
  have hprod := mul_le_mul hklo hlenlo (show 0 ≤ 31 * Q by positivity)
    (show (0 : ℝ) ≤ depth Q W δ by positivity)
  have heq : (2 * W / Q) * (31 * Q) = 62 * W := by
    field_simp
    ring
  rw [heq] at hprod
  simpa only [degree, Nat.cast_mul] using hprod

/-- In particular the schedule also supports a catalyst budget bounded by `3W`. -/
theorem degree_ge_six (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    6 * W ≤ (degree Q W δ : ℝ) := by
  have h := degree_ge_sixtyTwo Q W δ hQ hW hδ hδ1
  linarith

/-- Explicit degree bound: the linear budget and logarithmic precision term
have a common absolute constant of 64. -/
theorem degree_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (degree Q W δ : ℝ) ≤ 64 * (W + Q * (1 + logBudget Q W δ)) := by
  have hQ0 : 0 < Q := by linarith
  have hkhi := (depth_lt Q W δ hQ hW hδ hδ1).le
  have hlenhi := (length_sub_one_bounds Q hQ).2.le
  have hknonneg : 0 ≤ realDepth Q W δ + 2 := by
    have h := realDepth_nonneg Q W δ hQ hW hδ hδ1
    linarith
  have hprod := mul_le_mul hkhi hlenhi
    (show (0 : ℝ) ≤ (length Q - 1 : ℕ) by positivity) hknonneg
  have heq : (realDepth Q W δ + 2) * (32 * Q) =
      64 * (W + Q * (1 + logBudget Q W δ)) := by
    unfold realDepth
    field_simp
    ring
  rw [heq] at hprod
  simpa only [degree, Nat.cast_mul] using hprod

/-- All constraints are met by the same concrete natural parameters. -/
theorem schedule_spec (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    32 * Q ≤ (length Q : ℝ) ∧
    1 ≤ depth Q W δ ∧
    prefactor Q W * (1 / 4 : ℝ) ^ depth Q W δ ≤ δ ∧
    2 * W ≤ (degree Q W δ : ℝ) ∧
    (degree Q W δ : ℝ) ≤ 64 * (W + Q * (1 + logBudget Q W δ)) := by
  exact ⟨length_ge Q, depth_pos Q W δ, quarter_decay_le Q W δ hQ hW hδ,
    degree_ge Q W δ hQ hW hδ hδ1, degree_le Q W δ hQ hW hδ hδ1⟩

end
end SparseHamiltonian.FilterSchedule
