import SparseLinearSystems.Foundations.HilbertBlocks

/-!
# The scalar regularization gap

`gap κ σ = √(σ² + (1 - σ²)/κ²)` is the lower bound for the singular values of
the regularized dilation (equation `qls:eq:regularizedsquare`).  For
`0 ≤ σ ≤ 1 ≤ κ` it satisfies `max(σ, 1/κ) ≤ gap κ σ ≤ 1` (`sigma_le_gap`,
`reciprocal_le_gap`, `gap_le_one`), is monotone in `σ` (`gap_mono`) and loses
at most a factor two under halving (`gap_halving`).  The operator statements
are in `Foundations.HilbertRegularization` and
`Foundations.HilbertAugmentationGap`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.RegularizationGap

noncomputable section

/-- The squared lower singular-value bound for regularization. -/
def square (κ σ : ℝ) : ℝ := σ ^ 2 + (1 - σ ^ 2) / κ ^ 2

/-- The scalar lower singular-value bound from the manuscript. -/
def gap (κ σ : ℝ) : ℝ := Real.sqrt (square κ σ)

theorem square_nonneg (κ σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 ≤ square κ σ := by
  have hweight : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ0 hσ1]
  exact add_nonneg (sq_nonneg σ) (div_nonneg hweight (sq_nonneg κ))

theorem gap_nonneg (κ σ : ℝ) : 0 ≤ gap κ σ :=
  Real.sqrt_nonneg (square κ σ)

theorem gap_sq (κ σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    gap κ σ ^ 2 = square κ σ :=
  Real.sq_sqrt (square_nonneg κ σ hσ0 hσ1)

/-- A form in which the inverse-condition-number contribution is explicit. -/
theorem square_rewrite (κ σ : ℝ) :
    square κ σ = 1 / κ ^ 2 + σ ^ 2 * (1 - 1 / κ ^ 2) := by
  unfold square
  ring

theorem reciprocal_square_le_one (κ : ℝ) (hκ : 1 ≤ κ) :
    1 / κ ^ 2 ≤ 1 := by
  have hκpos : 0 < κ := by linarith
  have hκsq : 0 < κ ^ 2 := sq_pos_of_pos hκpos
  apply (div_le_iff₀ hκsq).2
  nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hκ]

theorem sigma_le_gap (κ σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    σ ≤ gap κ σ := by
  have hsq := gap_sq κ σ hσ0 hσ1
  have hg := gap_nonneg κ σ
  have hweight : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ0 hσ1]
  have hterm := div_nonneg hweight (sq_nonneg κ)
  unfold square at hsq
  apply (sq_le_sq₀ hσ0 hg).mp
  nlinarith only [hsq, hterm]

theorem reciprocal_le_gap (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    1 / κ ≤ gap κ σ := by
  have hκpos : 0 < κ := by linarith
  have hinv : 0 ≤ 1 / κ := le_of_lt (one_div_pos.mpr hκpos)
  have hg := gap_nonneg κ σ
  have hsq := gap_sq κ σ hσ0 hσ1
  rw [square_rewrite] at hsq
  have hweight : 0 ≤ 1 - 1 / κ ^ 2 :=
    sub_nonneg.mpr (reciprocal_square_le_one κ hκ)
  have hterm := mul_nonneg (sq_nonneg σ) hweight
  have hinvsq : (1 / κ) ^ 2 = 1 / κ ^ 2 := by rw [div_pow, one_pow]
  apply (sq_le_sq₀ hinv hg).mp
  nlinarith only [hsq, hterm, hinvsq]

theorem gap_pos (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 < gap κ σ := by
  have hκpos : 0 < κ := by linarith
  exact lt_of_lt_of_le (one_div_pos.mpr hκpos)
    (reciprocal_le_gap κ σ hκ hσ0 hσ1)

theorem gap_le_one (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    gap κ σ ≤ 1 := by
  have hsq := gap_sq κ σ hσ0 hσ1
  have hweight : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ0 hσ1]
  have hterm := mul_le_mul_of_nonneg_left
    (reciprocal_square_le_one κ hκ) hweight
  have hdiv : (1 - σ ^ 2) / κ ^ 2 =
      (1 - σ ^ 2) * (1 / κ ^ 2) := by ring
  unfold square at hsq
  rw [hdiv] at hsq
  apply (sq_le_sq₀ (gap_nonneg κ σ) (by norm_num : (0 : ℝ) ≤ 1)).mp
  nlinarith only [hsq, hterm]

/-- Together these are the scalar promise used by the subsequent walk gap. -/
theorem gap_bounds (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 < gap κ σ ∧ gap κ σ ≤ 1 ∧ max σ (1 / κ) ≤ gap κ σ := by
  exact ⟨gap_pos κ σ hκ hσ0 hσ1, gap_le_one κ σ hκ hσ0 hσ1,
    max_le (sigma_le_gap κ σ hσ0 hσ1)
      (reciprocal_le_gap κ σ hκ hσ0 hσ1)⟩

/-- Regularization parameters decrease with the dyadic schedule. -/
theorem gap_mono (κ σ τ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hστ : σ ≤ τ) (hτ1 : τ ≤ 1) :
    gap κ σ ≤ gap κ τ := by
  have hτ0 : 0 ≤ τ := le_trans hσ0 hστ
  have hσ1 : σ ≤ 1 := le_trans hστ hτ1
  have hσsq := gap_sq κ σ hσ0 hσ1
  have hτsq := gap_sq κ τ hτ0 hτ1
  have hdiff : 0 ≤ τ ^ 2 - σ ^ 2 :=
    sub_nonneg.mpr ((sq_le_sq₀ hσ0 hτ0).2 hστ)
  have hweight : 0 ≤ 1 - 1 / κ ^ 2 :=
    sub_nonneg.mpr (reciprocal_square_le_one κ hκ)
  have hprod := mul_nonneg hdiff hweight
  rw [square_rewrite] at hσsq hτsq
  apply (sq_le_sq₀ (gap_nonneg κ σ) (gap_nonneg κ τ)).mp
  nlinarith only [hσsq, hτsq, hprod]

/-- Halving regularization reduces the scalar gap by at most a factor two. -/
theorem gap_halving (κ σ : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    gap κ σ / 2 ≤ gap κ (σ / 2) := by
  have hhalf0 : 0 ≤ σ / 2 := by positivity
  have hhalf1 : σ / 2 ≤ 1 := by linarith
  have hsq := gap_sq κ σ hσ0 hσ1
  have hhalfsq := gap_sq κ (σ / 2) hhalf0 hhalf1
  have hid : 4 * square κ (σ / 2) - square κ σ = 3 / κ ^ 2 := by
    unfold square
    ring
  have hright : 0 ≤ 3 / κ ^ 2 := by positivity
  apply (sq_le_sq₀
    (div_nonneg (gap_nonneg κ σ) (by norm_num : (0 : ℝ) ≤ 2))
    (gap_nonneg κ (σ / 2))).mp
  nlinarith only [hsq, hhalfsq, hid, hright]

/-- At the terminal schedule scale the gap is within a constant factor of
the unregularized lower singular-value bound. -/
theorem terminal_gap_le (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hterminal : σ ≤ 1 / κ) :
    gap κ σ ≤ Real.sqrt 2 / κ := by
  have hκpos : 0 < κ := by linarith
  have hinv : 0 ≤ 1 / κ := le_of_lt (one_div_pos.mpr hκpos)
  have hσsq : σ ^ 2 ≤ (1 / κ) ^ 2 :=
    (sq_le_sq₀ hσ0 hinv).2 hterminal
  have hsq := gap_sq κ σ hσ0 hσ1
  have hweight : 1 - σ ^ 2 ≤ 1 := by nlinarith [sq_nonneg σ]
  have hterm := div_le_div_of_nonneg_right hweight (sq_nonneg κ)
  have hinvsq : (1 / κ) ^ 2 = 1 / κ ^ 2 := by rw [div_pow, one_pow]
  have hroot : (Real.sqrt 2 / κ) ^ 2 = 2 / κ ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hrootnonneg : 0 ≤ Real.sqrt 2 / κ :=
    div_nonneg (Real.sqrt_nonneg 2) (le_of_lt hκpos)
  unfold square at hsq
  apply (sq_le_sq₀ (gap_nonneg κ σ) hrootnonneg).mp
  rw [hinvsq] at hσsq
  rw [hroot]
  calc
    gap κ σ ^ 2 = σ ^ 2 + (1 - σ ^ 2) / κ ^ 2 := hsq
    _ ≤ 1 / κ ^ 2 + 1 / κ ^ 2 := add_le_add hσsq hterm
    _ = 2 / κ ^ 2 := by ring

/-- The terminal norm-comparison factor in the manuscript is at most
`sqrt 2` once the regularization parameter is at most `1 / κ`. -/
theorem terminal_weight_le_sqrt_two (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hσ0 : 0 ≤ σ) (hterminal : σ ≤ 1 / κ) :
    Real.sqrt (1 + κ ^ 2 * σ ^ 2) ≤ Real.sqrt 2 := by
  have hκpos : 0 < κ := by linarith
  have hprod : σ * κ ≤ 1 := (le_div_iff₀ hκpos).mp hterminal
  have hprod0 : 0 ≤ σ * κ := mul_nonneg hσ0 (le_of_lt hκpos)
  have hprodsq := (sq_le_sq₀ hprod0 (by norm_num : (0 : ℝ) ≤ 1)).2 hprod
  apply Real.sqrt_le_sqrt
  nlinarith only [hprodsq]

end
end SparseLinearSystems.RegularizationGap
