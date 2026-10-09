import GeneralODE.Analysis.ExpBounds

/-!
# Affine recursions with bounded propagators

`z (j+1) = F (z j) + g (j+1)` unrolls to
`z j = F^j (z 0) + ∑_{i<j} F^(j-1-i) (g (i+1))`, and uniform bounds on the
powers of `F` bound the whole trajectory.  This is the block row/column-sum
estimate for the inverse of the history matrix in Theorem `ode:thm:general`.
-/

namespace SparseHamiltonian.GeneralODE.Recursion

noncomputable section
open scoped BigOperators

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Unrolled affine recursion. -/
theorem unroll (F : P →L[ℂ] P) (z g : ℕ → P)
    (hz : ∀ j, z (j + 1) = F (z j) + g (j + 1)) (j : ℕ) :
    z j = (F ^ j) (z 0) +
      ∑ i ∈ Finset.range j, (F ^ (j - 1 - i)) (g (i + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [hz j, ih, map_add, map_sum, Finset.sum_range_succ]
      have hpow : F ((F ^ j) (z 0)) = (F ^ (j + 1)) (z 0) := by
        rw [pow_succ']; rfl
      have hsum : ∑ i ∈ Finset.range j, F ((F ^ (j - 1 - i)) (g (i + 1))) =
          ∑ i ∈ Finset.range j, (F ^ (j + 1 - 1 - i)) (g (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        rw [show j + 1 - 1 - i = (j - 1 - i) + 1 by omega, pow_succ']
        rfl
      rw [hpow, hsum, show j + 1 - 1 - j = 0 by omega, pow_zero]
      simp only [one_apply_eq_self]
      abel

/-- A trajectory bound from uniformly bounded propagator powers. -/
theorem norm_le_of_unroll (F : P →L[ℂ] P) (z g : ℕ → P)
    (hz : ∀ j, z (j + 1) = F (z j) + g (j + 1)) (c : ℝ) (N : ℕ)
    (hF : ∀ k, k ≤ N → ‖F ^ k‖ ≤ c) (j : ℕ) (hj : j ≤ N) :
    ‖z j‖ ≤ c * (‖z 0‖ + ∑ i ∈ Finset.range j, ‖g (i + 1)‖) := by
  rw [unroll F z g hz j, mul_add, Finset.mul_sum]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((F ^ j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF j hj) (norm_nonneg _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i hi
    exact ((F ^ (j - 1 - i)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF _ (by omega)) (norm_nonneg _))

/-- Difference of two affine recursions. -/
theorem norm_sub_le_of_recursions (F E : P →L[ℂ] P) (y x : ℕ → P) (s t : P)
    (hy : ∀ j, y (j + 1) = F (y j) + s) (hx : ∀ j, x (j + 1) = E (x j) + t)
    (c : ℝ) (N : ℕ) (hF : ∀ k, k ≤ N → ‖F ^ k‖ ≤ c) (j : ℕ) (hj : j ≤ N) :
    ‖y j - x j‖ ≤ c * (‖y 0 - x 0‖ +
      ∑ i ∈ Finset.range j, (‖F - E‖ * ‖x i‖ + ‖s - t‖)) := by
  have hrec : ∀ k, (y (k + 1) - x (k + 1)) =
      F (y k - x k) + ((F - E) (x k) + (s - t)) := by
    intro k
    rw [hy k, hx k, map_sub, sub_apply]
    abel
  have h := norm_le_of_unroll F (fun k => y k - x k)
    (fun k => (F - E) (x (k - 1)) + (s - t)) (fun k => by simpa using hrec k) c N hF j hj
  refine h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) ?_)
  · apply Finset.sum_le_sum
    intro i _
    simp only [Nat.add_sub_cancel]
    exact (norm_add_le _ _).trans (add_le_add ((F - E).le_opNorm _) le_rfl)
  · exact (norm_nonneg _).trans (hF 0 (Nat.zero_le N))

/-- Unrolled affine recursion on an initial segment. -/
theorem unroll_le (F : P →L[ℂ] P) (z g : ℕ → P) (N : ℕ)
    (hz : ∀ j, j < N → z (j + 1) = F (z j) + g (j + 1)) (j : ℕ) (hj : j ≤ N) :
    z j = (F ^ j) (z 0) +
      ∑ i ∈ Finset.range j, (F ^ (j - 1 - i)) (g (i + 1)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [hz j (by omega), ih (by omega), map_add, map_sum, Finset.sum_range_succ]
      have hpow : F ((F ^ j) (z 0)) = (F ^ (j + 1)) (z 0) := by
        rw [pow_succ']; rfl
      have hsum : ∑ i ∈ Finset.range j, F ((F ^ (j - 1 - i)) (g (i + 1))) =
          ∑ i ∈ Finset.range j, (F ^ (j + 1 - 1 - i)) (g (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hij : i < j := Finset.mem_range.mp hi
        rw [show j + 1 - 1 - i = (j - 1 - i) + 1 by omega, pow_succ']
        rfl
      rw [hpow, hsum, show j + 1 - 1 - j = 0 by omega, pow_zero]
      simp only [one_apply_eq_self]
      abel

/-- Trajectory bound on an initial segment. -/
theorem norm_le_of_unroll_le (F : P →L[ℂ] P) (z g : ℕ → P) (N : ℕ)
    (hz : ∀ j, j < N → z (j + 1) = F (z j) + g (j + 1)) (c : ℝ)
    (hF : ∀ k, k ≤ N → ‖F ^ k‖ ≤ c) (j : ℕ) (hj : j ≤ N) :
    ‖z j‖ ≤ c * (‖z 0‖ + ∑ i ∈ Finset.range j, ‖g (i + 1)‖) := by
  rw [unroll_le F z g N hz j hj, mul_add, Finset.mul_sum]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact ((F ^ j).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF j hj) (norm_nonneg _))
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro i hi
    exact ((F ^ (j - 1 - i)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hF _ (by omega)) (norm_nonneg _))

/-- Difference of two affine recursions on an initial segment. -/
theorem norm_sub_le_of_recursions_le (F E : P →L[ℂ] P) (y x : ℕ → P) (s t : P) (N : ℕ)
    (hy : ∀ j, j < N → y (j + 1) = F (y j) + s)
    (hx : ∀ j, j < N → x (j + 1) = E (x j) + t)
    (c : ℝ) (hF : ∀ k, k ≤ N → ‖F ^ k‖ ≤ c) (j : ℕ) (hj : j ≤ N) :
    ‖y j - x j‖ ≤ c * (‖y 0 - x 0‖ +
      ∑ i ∈ Finset.range j, (‖F - E‖ * ‖x i‖ + ‖s - t‖)) := by
  have hrec : ∀ k, k < N → (y (k + 1) - x (k + 1)) =
      F (y k - x k) + ((F - E) (x k) + (s - t)) := by
    intro k hk
    rw [hy k hk, hx k hk, map_sub, sub_apply]
    abel
  have h := norm_le_of_unroll_le F (fun k => y k - x k)
    (fun k => (F - E) (x (k - 1)) + (s - t)) N (fun k hk => by simpa using hrec k hk) c hF j hj
  refine h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl ?_) ?_)
  · apply Finset.sum_le_sum
    intro i _
    simp only [Nat.add_sub_cancel]
    exact (norm_add_le _ _).trans (add_le_add ((F - E).le_opNorm _) le_rfl)
  · exact (norm_nonneg _).trans (hF 0 (Nat.zero_le N))

end

end SparseHamiltonian.GeneralODE.Recursion
