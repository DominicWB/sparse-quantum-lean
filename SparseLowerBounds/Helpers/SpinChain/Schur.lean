import SparseLowerBounds.Helpers.SpinChain.Flow

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The Schur test for the `L²` operator norm of a matrix

Helper module of group spin-chain (`SparseLowerBounds.Hamiltonian.SpinChain`).
If `|A_{ij}| ≤ w_{ij}` with `w` symmetric and `Σ_j w_{ij} v_j ≤ r v_i` for a
positive vector `v`, then `‖A‖ ≤ r` (weighted Cauchy–Schwarz per row, then the
row bound again after exchanging the sums). Also: a fixed vector `A v = v`,
`v ≠ 0`, forces `1 ≤ ‖A‖`.
-/

namespace SparseLowerBounds.Helpers.SpinChain

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Components of `toEuclideanCLM A x`. -/
theorem toEuclideanCLM_apply_apply (A : Matrix S S ℂ) (x : EuclideanSpace ℂ S) (i : S) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) A x) i = ∑ j, A i j * x j := by
  rfl

omit [DecidableEq S] in
/-- Weighted Cauchy–Schwarz for one row. -/
theorem sq_sum_le_of_weight {w : S → ℝ} (hw : ∀ j, 0 ≤ w j) {v : S → ℝ} (hv : ∀ j, 0 < v j)
    (y : S → ℝ) :
    (∑ j, w j * y j) ^ 2 ≤ (∑ j, w j * v j) * ∑ j, w j * (y j ^ 2 / v j) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => mul_nonneg (hw j) (hv j).le)
    (fun j _ => mul_nonneg (hw j) (div_nonneg (sq_nonneg _) (hv j).le)) fun j _ => le_of_eq ?_
  have := (hv j).ne'
  field_simp

theorem norm_le_of_schur (A : Matrix S S ℂ) (w : S → S → ℝ) (hw : ∀ i j, w i j = w j i)
    (hA : ∀ i j, ‖A i j‖ ≤ w i j) (v : S → ℝ) (hv : ∀ i, 0 < v i) {r : ℝ} (hr : 0 ≤ r)
    (hwv : ∀ i, ∑ j, w i j * v j ≤ r * v i) : ‖A‖ ≤ r := by
  have hw0 : ∀ i j, 0 ≤ w i j := fun i j => (norm_nonneg _).trans (hA i j)
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hr fun x => ?_
  set y : EuclideanSpace ℂ S := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) A x with hy
  have hcomp : ∀ i, ‖y i‖ ≤ ∑ j, w i j * ‖x j‖ := by
    intro i
    rw [hy, toEuclideanCLM_apply_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
  set g : S → ℝ := fun j => ‖x j‖ ^ 2 / v j with hg
  have hg0 : ∀ j, 0 ≤ g j := fun j => div_nonneg (sq_nonneg _) (hv j).le
  have hsq : ‖y‖ ^ 2 ≤ (r * ‖x‖) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖y i‖ ^ 2
        ≤ ∑ i, (∑ j, w i j * ‖x j‖) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2
      _ ≤ ∑ i, (r * v i) * ∑ j, w i j * g j := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine (sq_sum_le_of_weight (hw0 i) hv _).trans ?_
          exact mul_le_mul_of_nonneg_right (hwv i)
            (Finset.sum_nonneg fun j _ => mul_nonneg (hw0 i j) (hg0 j))
      _ = r * ∑ j, g j * ∑ i, w j i * v i := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
          rw [hw i j]
          ring
      _ ≤ r * ∑ j, g j * (r * v j) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hr
          exact mul_le_mul_of_nonneg_left (hwv j) (hg0 j)
      _ = r ^ 2 * ∑ j, ‖x j‖ ^ 2 := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          have := (hv j).ne'
          rw [hg]
          field_simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hr (norm_nonneg _)) two_ne_zero).1 hsq

/-- A nonzero fixed vector forces operator norm at least one. -/
theorem one_le_norm_of_mulVec_eq (A : Matrix S S ℂ) (v : S → ℂ) (hv : v ≠ 0)
    (h : A *ᵥ v = v) : 1 ≤ ‖A‖ := by
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  set x : EuclideanSpace ℂ S := WithLp.toLp 2 v with hx
  have hx0 : 0 < ‖x‖ := by
    rw [norm_pos_iff]
    intro h0
    apply hv
    have := congrArg WithLp.ofLp h0
    simpa [hx] using this
  have hAx : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) A x = x := by
    rw [hx, Matrix.toEuclideanCLM_toLp, h]
  have := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) A).le_opNorm x
  rw [hAx] at this
  nlinarith

end

end SparseLowerBounds.Helpers.SpinChain
end
