import SparseLinearSystems.Foundations.HilbertAugmentationGap

/-!
# Four-branch augmented moment arithmetic

The scalar part of the compressed second-moment bound of the four-branch
construction: `(s (1 - σ²) + σ² + r⁻² + 1) / (256 s) ≤ 66/256` for `s ≥ 1` and
`r ≥ 1/8` (`four_branch_moment_le`).  The operator statement is part of
`Augmented.augmented_hyp`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.AugmentedMoments

noncomputable section

/-- The sparse and regularization branch weights together never exceed the
original sparsity.  This is the `s - sigma²(s-1)` observation. -/
theorem sparse_regularization_weight_le
    (s σ : ℝ) (hs : 1 ≤ s) :
    s * (1 - σ ^ 2) + σ ^ 2 ≤ s := by
  have hprod : 0 ≤ σ ^ 2 * (s - 1) :=
    mul_nonneg (sq_nonneg σ) (sub_nonneg.mpr hs)
  nlinarith

/-- The norm-guess promise `r >= 1/8` gives the required reciprocal-square
bound for the appended-column branch. -/
theorem reciprocal_square_le_sixty_four
    (r : ℝ) (hr : (1 : ℝ) / 8 ≤ r) :
    1 / r ^ 2 ≤ 64 := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hr2 : ((1 : ℝ) / 8) ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (by norm_num) hrpos.le).2 hr
  apply (div_le_iff₀ (sq_pos_of_pos hrpos)).2
  norm_num at hr2 ⊢
  nlinarith

/-- The complete four-branch scalar second moment is at most `66/256`.
No positivity or upper-bound assumption on `sigma` is actually needed for
this arithmetic estimate. -/
theorem four_branch_moment_le
    (s σ r : ℝ) (hs : 1 ≤ s) (hr : (1 : ℝ) / 8 ≤ r) :
    (s * (1 - σ ^ 2) + σ ^ 2 + 1 / r ^ 2 + 1) / (256 * s) ≤
      (66 : ℝ) / 256 := by
  have hmain := sparse_regularization_weight_le s σ hs
  have hrinv := reciprocal_square_le_sixty_four r hr
  have hnum :
      s * (1 - σ ^ 2) + σ ^ 2 + 1 / r ^ 2 + 1 ≤ s + 65 := by
    nlinarith
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hden : 0 < 256 * s := mul_pos (by norm_num) hspos
  apply (div_le_iff₀ hden).2
  have hs65 : s + 65 ≤ 66 * s := by nlinarith
  calc
    s * (1 - σ ^ 2) + σ ^ 2 + 1 / r ^ 2 + 1 ≤ s + 65 := hnum
    _ ≤ 66 * s := hs65
    _ = (66 / 256) * (256 * s) := by ring

/-- The advertised constant is a contraction bound. -/
theorem sixty_six_over_two_fifty_six_le_one :
    (66 : ℝ) / 256 ≤ 1 := by norm_num

end
end SparseLinearSystems.AugmentedMoments
