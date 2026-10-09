import SparseLinearSystems.Foundations.KernelWalk

/-!
# Geometric stage budget: scalar arithmetic

The scalar arithmetic behind equation `qls:eq:geometriccost`:
`Σ_{j ≤ m} 2^j (L + m - j) ≤ 4 · 2^m L` (`stageCost_le`), failure budgets
summing to at most `ε/500` (`stageFailure_sum_le`), and `2^m ≤ 2κ` for
`m = ⌈log₂ κ⌉` (`dyadic_bracket`, `sparse_stageCost_le`).  The query bound for
the concrete parameters of the algorithm is proved in `Endpoint.Cost`.
-/

namespace SparseLinearSystems.GeometricBudget

noncomputable section

open scoped BigOperators

/-- Exact dyadic mass of the first `m` powers, including the empty schedule. -/
theorem dyadic_sum (m : ℕ) :
    (∑ j ∈ Finset.range m, (2 : ℝ) ^ j) = (2 : ℝ) ^ m - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

/-- A dimension-free bound for the dyadic schedule mass. -/
theorem dyadic_sum_le (m : ℕ) :
    (∑ j ∈ Finset.range m, (2 : ℝ) ^ j) ≤ (2 : ℝ) ^ m := by
  rw [dyadic_sum]
  linarith

/-- Exact sum accounting for the confidence overhead at earlier stages. -/
theorem weighted_dyadic_sum (m : ℕ) :
    (∑ j ∈ Finset.range m, (2 : ℝ) ^ j * ((m : ℝ) - (j : ℝ))) =
      2 * (2 : ℝ) ^ m - (m : ℝ) - 2 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have hsum :
          (∑ j ∈ Finset.range m,
            (2 : ℝ) ^ j * ((m.succ : ℝ) - (j : ℝ))) =
          (∑ j ∈ Finset.range m,
            (2 : ℝ) ^ j * ((m : ℝ) - (j : ℝ))) +
          (∑ j ∈ Finset.range m, (2 : ℝ) ^ j) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [Nat.cast_succ]
        ring
      rw [hsum, ih, dyadic_sum, Nat.cast_succ, pow_succ]
      ring

/-- The same overhead bound with literal natural-number stage distances. -/
theorem weighted_dyadic_sum_le (m : ℕ) :
    (∑ j ∈ Finset.range m, (2 : ℝ) ^ j * ((m - j : ℕ) : ℝ)) ≤
      2 * (2 : ℝ) ^ m := by
  have heq :
      (∑ j ∈ Finset.range m, (2 : ℝ) ^ j * ((m - j : ℕ) : ℝ)) =
      (∑ j ∈ Finset.range m, (2 : ℝ) ^ j * ((m : ℝ) - (j : ℝ))) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hj))]
  rw [heq, weighted_dyadic_sum]
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- The manuscript's stages `1,...,m`, indexed by `range m` via `j+1`. -/
def stageCost (m : ℕ) (L : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m,
    (2 : ℝ) ^ (j + 1) * (L + (m : ℝ) - ((j : ℝ) + 1))

/-- Exact total stage cost; no extra factor of the number of stages appears. -/
theorem stageCost_eq (m : ℕ) (L : ℝ) :
    stageCost m L =
      (2 * L + 2) * (2 : ℝ) ^ m - 2 * L - 2 * (m : ℝ) - 2 := by
  unfold stageCost
  calc
    (∑ j ∈ Finset.range m,
        (2 : ℝ) ^ (j + 1) * (L + (m : ℝ) - ((j : ℝ) + 1))) =
        ∑ j ∈ Finset.range m,
          (2 * L * (2 : ℝ) ^ j +
            2 * ((2 : ℝ) ^ j * ((m : ℝ) - (j : ℝ))) -
            2 * (2 : ℝ) ^ j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ]
      ring
    _ = 2 * L * ((2 : ℝ) ^ m - 1) +
        2 * (2 * (2 : ℝ) ^ m - (m : ℝ) - 2) -
        2 * ((2 : ℝ) ^ m - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        dyadic_sum, weighted_dyadic_sum]
    _ = (2 * L + 2) * (2 : ℝ) ^ m - 2 * L - 2 * (m : ℝ) - 2 := by
      ring

/-- Explicit constant in the geometric-confidence cost bound. -/
theorem stageCost_le (m : ℕ) (L : ℝ) (hL : 1 ≤ L) :
    stageCost m L ≤ 4 * (2 : ℝ) ^ m * L := by
  rw [stageCost_eq]
  have hp : 0 ≤ (2 : ℝ) ^ m := by positivity
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hprod := mul_le_mul_of_nonneg_right hL hp
  nlinarith

/-- Failure allowance at stage `j+1`; the ratio uses only natural powers. -/
def stageFailure (ε : ℝ) (m j : ℕ) : ℝ :=
  (ε / 1000) * (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ m

theorem stageFailure_nonneg (ε : ℝ) (m j : ℕ) (hε : 0 ≤ ε) :
    0 ≤ stageFailure ε m j := by
  unfold stageFailure
  positivity

/-- Total failure allowance is at most `ε/500`, even for the empty schedule. -/
theorem stageFailure_sum_le (ε : ℝ) (m : ℕ) (hε : 0 ≤ ε) :
    (∑ j ∈ Finset.range m, stageFailure ε m j) ≤ ε / 500 := by
  unfold stageFailure
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have hsum : (∑ j ∈ Finset.range m, (2 : ℝ) ^ (j + 1)) =
      2 * ((2 : ℝ) ^ m - 1) := by
    simp only [pow_succ]
    rw [← Finset.sum_mul, dyadic_sum]
    ring
  rw [hsum]
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  apply (div_le_iff₀ hp).2
  nlinarith

/-- A minimal dyadic bracket gives both the cost and terminal-regularization
bounds. The disjunct `m=0` preserves the condition-number-one endpoint. -/
theorem dyadic_bracket (m : ℕ) (κ : ℝ) (hκ : 1 ≤ κ)
    (hupper : κ ≤ (2 : ℝ) ^ m)
    (hminimal : m = 0 ∨ (2 : ℝ) ^ (m - 1) < κ) :
    (2 : ℝ) ^ m ≤ 2 * κ ∧ 1 / (2 : ℝ) ^ m ≤ 1 / κ := by
  have hκpos : 0 < κ := by linarith
  have hp : 0 < (2 : ℝ) ^ m := by positivity
  constructor
  · cases m with
    | zero =>
        norm_num
        linarith
    | succ m =>
        have hprev : (2 : ℝ) ^ m < κ := by
          simpa only [Nat.add_sub_cancel] using
            hminimal.resolve_left (Nat.succ_ne_zero m)
        rw [pow_succ]
        linarith
  · apply (div_le_div_iff₀ hp hκpos).2
    simpa only [one_mul] using hupper

/-- Scheduling contribution to the desired sparse-query scaling.
This is arithmetic for a stage schedule, not an implementation theorem. -/
theorem sparse_stageCost_le (s κ L : ℝ) (m : ℕ) (hκ : 1 ≤ κ)
    (hL : 1 ≤ L) (hupper : κ ≤ (2 : ℝ) ^ m)
    (hminimal : m = 0 ∨ (2 : ℝ) ^ (m - 1) < κ) :
    Real.sqrt s * stageCost m L ≤ 8 * Real.sqrt s * κ * L := by
  have hpow := (dyadic_bracket m κ hκ hupper hminimal).1
  calc
    Real.sqrt s * stageCost m L ≤
        Real.sqrt s * (4 * (2 : ℝ) ^ m * L) :=
      mul_le_mul_of_nonneg_left (stageCost_le m L hL) (Real.sqrt_nonneg s)
    _ ≤ 8 * Real.sqrt s * κ * L := by
      have hLnonneg : 0 ≤ L := by linarith
      have hfactor : 0 ≤ 4 * Real.sqrt s * L := by positivity
      have hscaled := mul_le_mul_of_nonneg_left hpow hfactor
      nlinarith

end
end SparseLinearSystems.GeometricBudget
