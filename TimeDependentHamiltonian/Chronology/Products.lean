import TimeDependentHamiltonian.Chronology.Colligation

/-!
# Ordered products of contractions

Telescoping bounds for the ordered products `evolution A n = A (n-1) ⋯ A 0`.
They compare the Cayley clock with the product of sampled exponentials and the
product of sampled exponentials with the exact time-ordered propagator.
-/

namespace SparseHamiltonian.TimeDependent

open ContinuousLinearMap
open scoped BigOperators

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Ordered products of contractions are contractions. -/
theorem evolution_norm_le_one (A : ℕ → P →L[ℂ] P) (hA : ∀ k, ‖A k‖ ≤ 1) (n : ℕ) :
    ‖evolution A n‖ ≤ 1 := by
  induction n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
      rw [evolution_succ]
      calc
        ‖A n * evolution A n‖ ≤ ‖A n‖ * ‖evolution A n‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hA n) ih (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1

/-- Telescoping: the ordered products of two families of contractions differ by
at most the sum of the stepwise differences. -/
theorem evolution_sub_norm_le (A B : ℕ → P →L[ℂ] P) (hA : ∀ k, ‖A k‖ ≤ 1)
    (hB : ∀ k, ‖B k‖ ≤ 1) (n : ℕ) :
    ‖evolution A n - evolution B n‖ ≤ ∑ k ∈ Finset.range n, ‖A k - B k‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [evolution_succ, evolution_succ, Finset.sum_range_succ]
      have hsplit : A n * evolution A n - B n * evolution B n =
          A n * (evolution A n - evolution B n) + (A n - B n) * evolution B n := by
        noncomm_ring
      rw [hsplit]
      calc
        ‖A n * (evolution A n - evolution B n) + (A n - B n) * evolution B n‖ ≤
            ‖A n * (evolution A n - evolution B n)‖ + ‖(A n - B n) * evolution B n‖ :=
          norm_add_le _ _
        _ ≤ ‖A n‖ * ‖evolution A n - evolution B n‖ + ‖A n - B n‖ * ‖evolution B n‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 1 * (∑ k ∈ Finset.range n, ‖A k - B k‖) + ‖A n - B n‖ * 1 := by
          apply add_le_add
          · exact mul_le_mul (hA n) ih (norm_nonneg _) zero_le_one
          · exact mul_le_mul_of_nonneg_left (evolution_norm_le_one B hB n) (norm_nonneg _)
        _ = ∑ k ∈ Finset.range n, ‖A k - B k‖ + ‖A n - B n‖ := by ring

/-- A uniform stepwise bound accumulates linearly. -/
theorem evolution_sub_norm_le_mul (A B : ℕ → P →L[ℂ] P) (hA : ∀ k, ‖A k‖ ≤ 1)
    (hB : ∀ k, ‖B k‖ ≤ 1) {e : ℝ} (he : ∀ k, ‖A k - B k‖ ≤ e) (n : ℕ) :
    ‖evolution A n - evolution B n‖ ≤ n * e := by
  calc
    ‖evolution A n - evolution B n‖ ≤ ∑ k ∈ Finset.range n, ‖A k - B k‖ :=
      evolution_sub_norm_le A B hA hB n
    _ ≤ ∑ _k ∈ Finset.range n, e := Finset.sum_le_sum (fun k _ => he k)
    _ = n * e := by simp

end SparseHamiltonian.TimeDependent
