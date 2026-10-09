import SparseLowerBounds.LinearSystems.Gadget
import SparseLowerBounds.LinearSystems.Parameters

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Generic facts about the `L²` operator norm of square matrices

Helpers for `SparseLowerBounds.LinearSystems.OpenClock`: `‖1‖ ≤ 1`, the bound
`‖A w‖ ≤ ‖A‖ ‖w‖` on plain vectors (and `‖A w‖ ≤ ‖w‖` for contractions), the converse criterion `‖A‖ ≤ c`, and
`‖A^k‖ ≤ 1` for contractions.
-/

namespace SparseLowerBounds.LinearSystems

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

namespace OpenClock

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `‖1‖ ≤ 1` (an equality unless the index type is empty). -/
theorem norm_one_le : ‖(1 : Matrix κ κ ℂ)‖ ≤ 1 := by
  rw [Matrix.cstar_norm_def, map_one]
  exact ContinuousLinearMap.norm_id_le

/-- `‖A w‖ ≤ ‖A‖ ‖w‖` for plain vectors. -/
theorem norm_toLp_mulVec_le (A : Matrix κ κ ℂ) (w : κ → ℂ) :
    ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 w‖ :=
  (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 w)

/-- A contraction does not increase the norm of plain vectors. -/
theorem norm_toLp_mulVec_le_self {A : Matrix κ κ ℂ} (hA : ‖A‖ ≤ 1) (w : κ → ℂ) :
    ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ ‖WithLp.toLp 2 w‖ :=
  ((norm_toLp_mulVec_le A w).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))).trans_eq
    (one_mul _)

/-- A matrix whose action on plain vectors is bounded by `c` has norm at most `c`. -/
theorem norm_le_of_mulVec {A : Matrix κ κ ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w : κ → ℂ, ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ c * ‖WithLp.toLp 2 w‖) : ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  have := h (WithLp.ofLp v)
  rw [WithLp.toLp_ofLp] at this
  exact this

/-- `‖T^k‖ ≤ 1` for a contraction `T`. -/
theorem norm_pow_le_one {A : Matrix κ κ ℂ} (hA : ‖A‖ ≤ 1) (k : ℕ) : ‖A ^ k‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using norm_one_le (κ := κ)
  · exact (norm_pow_le' A hk).trans (pow_le_one₀ (norm_nonneg _) hA)

end OpenClock

end

end SparseLowerBounds.LinearSystems
end
