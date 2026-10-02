import SparseHamiltonian.WeightedGlobalResolvent

/-!
# Time subdivision without increasing the weighted clock budget

A concrete natural subdivision count makes the step size at most one quarter
and the accumulated cubic error at most the requested tolerance. The total
weighted clock budget is exactly independent of that subdivision count.
This is scalar scheduling, not a statement about an implemented circuit.
-/

namespace SparseHamiltonian.TimeSchedule

noncomputable section

/-- A sufficient real subdivision threshold. -/
def threshold (τ ε : ℝ) : ℝ := max (4 * τ) (Real.sqrt (τ ^ 3 / ε))

/-- The extra step ensures positivity, including at zero evolution time. -/
def steps (τ ε : ℝ) : ℕ := 1 + ⌈threshold τ ε⌉₊

/-- Time increment for the concrete subdivision count. -/
def stepSize (τ ε : ℝ) : ℝ := τ / (steps τ ε : ℝ)

theorem steps_pos (τ ε : ℝ) : 0 < steps τ ε := by
  unfold steps
  omega

theorem threshold_le_steps (τ ε : ℝ) : threshold τ ε ≤ (steps τ ε : ℝ) := by
  have h := Nat.le_ceil (threshold τ ε)
  simp only [steps, Nat.cast_add, Nat.cast_one]
  linarith

theorem four_time_le_steps (τ ε : ℝ) : 4 * τ ≤ (steps τ ε : ℝ) :=
  (le_max_left _ _).trans (threshold_le_steps τ ε)

theorem sqrt_error_le_steps (τ ε : ℝ) :
    Real.sqrt (τ ^ 3 / ε) ≤ (steps τ ε : ℝ) :=
  (le_max_right _ _).trans (threshold_le_steps τ ε)

theorem stepSize_nonneg (τ ε : ℝ) (hτ : 0 ≤ τ) : 0 ≤ stepSize τ ε :=
  div_nonneg hτ (Nat.cast_nonneg _)

theorem stepSize_le_quarter (τ ε : ℝ) : stepSize τ ε ≤ 1 / 4 := by
  have hT : (0 : ℝ) < steps τ ε := by exact_mod_cast steps_pos τ ε
  apply (div_le_iff₀ hT).mpr
  have h := four_time_le_steps τ ε
  linarith

/-- The cubic sum is the usual inverse-square subdivision error. -/
theorem accumulated_cubic_eq (τ ε : ℝ) :
    (steps τ ε : ℝ) * stepSize τ ε ^ 3 = τ ^ 3 / (steps τ ε : ℝ) ^ 2 := by
  have hT : (steps τ ε : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (steps_pos τ ε))
  unfold stepSize
  field_simp

/-- The chosen integer subdivision count meets the cubic error tolerance. -/
theorem accumulated_cubic_le (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    (steps τ ε : ℝ) * stepSize τ ε ^ 3 ≤ ε := by
  have hT : (0 : ℝ) < steps τ ε := by exact_mod_cast steps_pos τ ε
  have hratio : 0 ≤ τ ^ 3 / ε := div_nonneg (pow_nonneg hτ 3) hε.le
  have hsq : τ ^ 3 / ε ≤ (steps τ ε : ℝ) ^ 2 := by
    calc
      τ ^ 3 / ε = (Real.sqrt (τ ^ 3 / ε)) ^ 2 := (Real.sq_sqrt hratio).symm
      _ ≤ (steps τ ε : ℝ) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_error_le_steps τ ε) 2
  have hnumerator : τ ^ 3 ≤ ε * (steps τ ε : ℝ) ^ 2 := by
    have h := (div_le_iff₀ hε).mp hsq
    simpa only [mul_comm] using h
  rw [accumulated_cubic_eq]
  exact (div_le_iff₀ (sq_pos_of_pos hT)).mpr hnumerator

/-- Increasing the subdivision count does not increase the weighted budget. -/
theorem weighted_budget_eq (τ ε qbar : ℝ) :
    (steps τ ε : ℝ) * stepSize τ ε * qbar = τ * qbar := by
  have hT : (steps τ ε : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (steps_pos τ ε))
  unfold stepSize
  field_simp

/-- One concrete natural schedule meets every scalar subdivision requirement. -/
theorem schedule_spec (τ ε qbar : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) :
    0 < steps τ ε ∧
    0 ≤ stepSize τ ε ∧
    stepSize τ ε ≤ 1 / 4 ∧
    (steps τ ε : ℝ) * stepSize τ ε ^ 3 ≤ ε ∧
    (steps τ ε : ℝ) * stepSize τ ε * qbar = τ * qbar := by
  exact ⟨steps_pos τ ε, stepSize_nonneg τ ε hτ, stepSize_le_quarter τ ε,
    accumulated_cubic_le τ ε hτ hε, weighted_budget_eq τ ε qbar⟩

end
end SparseHamiltonian.TimeSchedule
