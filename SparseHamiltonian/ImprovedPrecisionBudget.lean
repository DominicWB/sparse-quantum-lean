import SparseHamiltonian.ImprovedSimulationBudget

/-!
# Conversion to the manuscript precision parameter

The circuit splits the error into thirds and the filter degree contains
`1 + log (3 / ε)`. These scalar lemmas compare that quantity with the
manuscript's `log (2 / ε)` without changing the logarithmic exponent.
They make no assertion that the sparse Cayley implementation has been built.
-/

namespace SparseHamiltonian.ImprovedPrecisionBudget

noncomputable section

def circuitLog (ε : ℝ) : ℝ := 1 + Real.log (3 / ε)

def targetLog (ε : ℝ) : ℝ := Real.log (2 / ε)

def shape (s τ ℓ : ℝ) : ℝ :=
  Real.sqrt s * τ + Real.sqrt (s * τ * ℓ) + ℓ

theorem targetLog_ge_half (ε : ℝ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    (1 / 2 : ℝ) ≤ targetLog ε := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have harg : (2 : ℝ) ≤ 2 / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  exact hlog2.trans (Real.log_le_log (by norm_num) harg)

theorem circuitLog_pos (ε : ℝ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < circuitLog ε := by
  have harg : (1 : ℝ) ≤ 3 / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hlog := Real.log_nonneg harg
  unfold circuitLog
  linarith

theorem circuitLog_le_four_targetLog (ε : ℝ)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    circuitLog ε ≤ 4 * targetLog ε := by
  have harg : (3 : ℝ) / ε = (3 / 2 : ℝ) * (2 / ε) := by ring
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  have hlower := targetLog_ge_half ε hε hεOne
  unfold circuitLog
  rw [harg, Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0)
    (ne_of_gt (by positivity : (0 : ℝ) < 2 / ε))]
  change 1 + (Real.log (3 / 2) + targetLog ε) ≤ 4 * targetLog ε
  linarith

/-- The mixed square-root term gains only an absolute factor when the
precision budget is changed from the circuit convention to the manuscript. -/
theorem shape_circuitLog_le (s τ ε : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    shape s τ (circuitLog ε) ≤ 4 * shape s τ (targetLog ε) := by
  have hB : 0 ≤ circuitLog ε := (circuitLog_pos ε hε hεOne).le
  have hL : 0 ≤ targetLog ε := by
    have h := targetLog_ge_half ε hε hεOne
    linarith
  have hBL := circuitLog_le_four_targetLog ε hε hεOne
  have hprod := mul_le_mul_of_nonneg_left hBL (mul_nonneg hs hτ)
  have hsqB := Real.sq_sqrt (mul_nonneg (mul_nonneg hs hτ) hB)
  have hsqL := Real.sq_sqrt (mul_nonneg (mul_nonneg hs hτ) hL)
  have hrootB := Real.sqrt_nonneg (s * τ * circuitLog ε)
  have hrootL := Real.sqrt_nonneg (s * τ * targetLog ε)
  have hroot : Real.sqrt (s * τ * circuitLog ε) ≤
      2 * Real.sqrt (s * τ * targetLog ε) := by
    nlinarith
  have htime : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg s) hτ
  unfold shape
  nlinarith

/-- A proved query estimate in the circuit precision convention implies
the same target scaling, with an explicit factor four. -/
theorem count_le_target (q C s τ ε : ℝ) (hC : 0 ≤ C)
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hq : q ≤ C * shape s τ (circuitLog ε)) :
    q ≤ (4 * C) * shape s τ (targetLog ε) := by
  have h := mul_le_mul_of_nonneg_left
    (shape_circuitLog_le s τ ε hs hτ hε hεOne) hC
  calc
    q ≤ C * shape s τ (circuitLog ε) := hq
    _ ≤ C * (4 * shape s τ (targetLog ε)) := h
    _ = (4 * C) * shape s τ (targetLog ε) := by ring

/-- Choose the rescaling using the actual circuit error budget, and express
its resulting catalyst-plus-filter cost in the manuscript precision parameter.
This is still scalar bookkeeping: native sparse-oracle construction remains
a separate proof obligation. -/
theorem exists_rescaling_for_precision (s τ ε : ℝ) (hs : 1 ≤ s)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt s ∧
      τ * Real.sqrt s / γ * ((1 + γ ^ 2) / 2) +
        (⌈max 1 (γ * Real.sqrt s)⌉₊ : ℝ) * circuitLog ε ≤
          12 * shape s τ (targetLog ε) := by
  obtain ⟨γ, hγ, hγOne, hwidth, hcost⟩ :=
    ImprovedSimulationBudget.exists_rescaling_moment_budget hs hτ
      (circuitLog_pos ε hε hεOne)
  refine ⟨γ, hγ, hγOne, hwidth, ?_⟩
  have hshape := shape_circuitLog_le s τ ε (by linarith) hτ hε hεOne
  change τ * Real.sqrt s / γ * ((1 + γ ^ 2) / 2) +
    (⌈max 1 (γ * Real.sqrt s)⌉₊ : ℝ) * circuitLog ε ≤
      3 * shape s τ (circuitLog ε) at hcost
  linarith

end
end SparseHamiltonian.ImprovedPrecisionBudget
