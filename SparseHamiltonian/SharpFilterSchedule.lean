import SparseHamiltonian.ODEControlledLCU

/-!
# A precision schedule without the extraneous logarithm of the clock budget

This module is appended after the existing development.  It changes only the
natural-valued filter schedule: the established resolvent and averaging-filter
estimates are reused unchanged.  In particular, no new analytic premise is
introduced.  The final degree is `O(W + Q * (1 + log (1 / δ)))`.
-/

namespace SparseHamiltonian.SharpFilterSchedule

noncomputable section

/-- The precision contribution is independent of the clock and time budgets. -/
def logBudget (δ : ℝ) : ℝ := Real.log (1 / δ)

def realDepth (Q W δ : ℝ) : ℝ := 4 * W / Q + 2 * logBudget δ

def length (Q : ℝ) : ℕ := FilterSchedule.length Q

def depth (Q W δ : ℝ) : ℕ := 1 + ⌈realDepth Q W δ⌉₊

def degree (Q W δ : ℝ) : ℕ := depth Q W δ * (length Q - 1)

theorem logBudget_nonneg (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 ≤ logBudget δ := by
  apply Real.log_nonneg
  exact (le_div_iff₀ hδ).mpr (by simpa using hδ1)

theorem realDepth_nonneg (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 ≤ realDepth Q W δ := by
  unfold realDepth
  exact add_nonneg (div_nonneg (by positivity) (by linarith))
    (mul_nonneg (by norm_num) (logBudget_nonneg δ hδ hδ1))

theorem depth_pos (Q W δ : ℝ) : 0 < depth Q W δ := by
  unfold depth
  omega

theorem length_ge (Q : ℝ) : 32 * Q ≤ (length Q : ℝ) :=
  FilterSchedule.length_ge Q

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

/-- Keeping the division by `Q` in the resolvent prefactor removes a spurious
`log (Q + W)` from the required number of filter repetitions. -/
theorem log_prefactor_ratio_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) :
    Real.log (FilterSchedule.prefactor Q W / δ) ≤
      2 * W / Q + logBudget δ := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < 3 * (Q + W) / (4 * Q) := by positivity
  have he : 0 < Real.exp (3 * W / (4 * Q)) := Real.exp_pos _
  have hi : 0 < 1 / δ := by positivity
  have hcoef := Real.log_le_sub_one_of_pos ha
  have hcoef_eq : 3 * (Q + W) / (4 * Q) =
      (3 / 4 : ℝ) * (1 + W / Q) := by
    field_simp
  rw [hcoef_eq] at hcoef
  have hWQ : 0 ≤ W / Q := div_nonneg hW hQ0.le
  have heq : FilterSchedule.prefactor Q W / δ =
      (3 * (Q + W) / (4 * Q)) * Real.exp (3 * W / (4 * Q)) * (1 / δ) := by
    unfold FilterSchedule.prefactor
    ring
  have hexp_eq : 3 * W / (4 * Q) = (3 / 4 : ℝ) * (W / Q) := by ring
  have htwo_eq : 2 * W / Q = 2 * (W / Q) := by ring
  rw [heq, Real.log_mul (mul_ne_zero (ne_of_gt ha) (ne_of_gt he)) (ne_of_gt hi),
    Real.log_mul (ne_of_gt ha) (ne_of_gt he), Real.log_exp,
    hexp_eq, htwo_eq, hcoef_eq]
  unfold logBudget
  nlinarith

/-- The sharper depth still controls the weaker decay factor `1/2`. -/
theorem half_decay_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) :
    FilterSchedule.prefactor Q W * (1 / 2 : ℝ) ^ depth Q W δ ≤ δ := by
  apply FilterDepth.decay_le_of_log_depth _ _
    (FilterSchedule.prefactor_pos Q W hQ hW) hδ
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2pos : 0 < Real.log (2 : ℝ) := by linarith
  apply (div_le_iff₀ hlog2pos).mpr
  have hbound := log_prefactor_ratio_le Q W δ hQ hW hδ
  have hk := depth_ge Q W δ
  have hproduct := mul_le_mul_of_nonneg_left hlog2
    (show (0 : ℝ) ≤ depth Q W δ by positivity)
  unfold realDepth at hk
  have htwo : 2 * W / Q = 2 * (W / Q) := by ring
  have hfour : 4 * W / Q = 4 * (W / Q) := by ring
  rw [htwo] at hbound
  rw [hfour] at hk
  nlinarith

theorem quarter_decay_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) :
    FilterSchedule.prefactor Q W * (1 / 4 : ℝ) ^ depth Q W δ ≤ δ := by
  apply le_trans _ (half_decay_le Q W δ hQ hW hδ)
  apply mul_le_mul_of_nonneg_left _
    (le_of_lt (FilterSchedule.prefactor_pos Q W hQ hW))
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

theorem length_sub_one_bounds (Q : ℝ) (hQ : 1 ≤ Q) :
    Q ≤ ((length Q - 1 : ℕ) : ℝ) ∧ ((length Q - 1 : ℕ) : ℝ) < 32 * Q :=
  FilterSchedule.length_sub_one_bounds Q hQ

theorem degree_pos (Q W δ : ℝ) (hQ : 1 ≤ Q) : 1 ≤ degree Q W δ := by
  have hL : (1 : ℝ) ≤ ((length Q - 1 : ℕ) : ℝ) :=
    hQ.trans (length_sub_one_bounds Q hQ).1
  have hLnat : 1 ≤ length Q - 1 := by exact_mod_cast hL
  exact Nat.mul_pos (depth_pos Q W δ) hLnat

/-- There is ample smoothing slack in the natural-valued degree. -/
theorem degree_ge_oneHundredTwentyFour (Q W δ : ℝ)
    (hQ : 1 ≤ Q) (_hW : 0 ≤ W) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    124 * W ≤ (degree Q W δ : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  have hk := depth_ge Q W δ
  have hlog := logBudget_nonneg δ hδ hδ1
  have hklo : 4 * W / Q ≤ (depth Q W δ : ℝ) := by
    unfold realDepth at hk
    linarith
  have hlen : 1 ≤ length Q := by
    change 1 ≤ FilterSchedule.length Q
    unfold FilterSchedule.length
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hlenlo : 31 * Q ≤ ((length Q - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlen, Nat.cast_one]
    have h := length_ge Q
    linarith
  have hprod := mul_le_mul hklo hlenlo (show 0 ≤ 31 * Q by positivity)
    (show (0 : ℝ) ≤ depth Q W δ by positivity)
  have heq : (4 * W / Q) * (31 * Q) = 124 * W := by
    field_simp; ring
  rw [heq] at hprod
  simpa only [degree, Nat.cast_mul] using hprod

theorem degree_ge_six (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    6 * W ≤ (degree Q W δ : ℝ) := by
  have h := degree_ge_oneHundredTwentyFour Q W δ hQ hW hδ hδ1
  linarith

theorem degree_ge (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    2 * W ≤ (degree Q W δ : ℝ) := by
  have h := degree_ge_six Q W δ hQ hW hδ hδ1
  linarith

/-- Explicit improved degree bound, retaining the two different constants. -/
theorem degree_le_refined (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (degree Q W δ : ℝ) ≤ 64 * (2 * W + Q * (1 + logBudget δ)) := by
  have hQ0 : 0 < Q := by linarith
  have hkhi := (depth_lt Q W δ hQ hW hδ hδ1).le
  have hlenhi := (length_sub_one_bounds Q hQ).2.le
  have hknonneg : 0 ≤ realDepth Q W δ + 2 := by
    have h := realDepth_nonneg Q W δ hQ hW hδ hδ1
    linarith
  have hprod := mul_le_mul hkhi hlenhi
    (show (0 : ℝ) ≤ (length Q - 1 : ℕ) by positivity) hknonneg
  have heq : (realDepth Q W δ + 2) * (32 * Q) =
      64 * (2 * W + Q * (1 + logBudget δ)) := by
    unfold realDepth
    field_simp; ring
  rw [heq] at hprod
  simpa only [degree, Nat.cast_mul] using hprod

/-- The improved schedule has no logarithm of `Q`, `W`, or their sum. -/
theorem degree_le (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (degree Q W δ : ℝ) ≤ 128 * (W + Q * (1 + logBudget δ)) := by
  have h := degree_le_refined Q W δ hQ hW hδ hδ1
  have hlog := logBudget_nonneg δ hδ hδ1
  have hnonneg : 0 ≤ Q * (1 + logBudget δ) :=
    mul_nonneg (by linarith) (by linarith)
  linarith

/-- All precision, positivity, and smoothing constraints hold simultaneously. -/
theorem schedule_spec (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    32 * Q ≤ (length Q : ℝ) ∧
    1 ≤ depth Q W δ ∧
    FilterSchedule.prefactor Q W * (1 / 4 : ℝ) ^ depth Q W δ ≤ δ ∧
    6 * W ≤ (degree Q W δ : ℝ) ∧
    (degree Q W δ : ℝ) ≤ 128 * (W + Q * (1 + logBudget δ)) := by
  exact ⟨length_ge Q, depth_pos Q W δ, quarter_decay_le Q W δ hQ hW hδ,
    degree_ge_six Q W δ hQ hW hδ hδ1, degree_le Q W δ hQ hW hδ hδ1⟩

end
end SparseHamiltonian.SharpFilterSchedule
