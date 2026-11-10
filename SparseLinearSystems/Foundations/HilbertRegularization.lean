import SparseLinearSystems.Foundations.RegularizationGap

/-!
# Hilbert-space dilation and regularization

On `Double V = V ⊕ V` with the Hilbert direct-sum norm: the Hermitian dilation
`B = [[0, A], [A†, 0]]` (`dilation`, `dilation_norm_le_one`), the signed
diagonal `Z ⊗ B`, the exchange `X` and the regularized operator
`M_σ = √(1 - σ²) (Z ⊗ B) + σ X` of equation `qls:eq:regularization`.
`regularized_square_apply` is equation `qls:eq:regularizedsquare`.  If
`‖B v‖ ≥ ‖v‖/κ`, then `M_σ` is self-adjoint, `‖M_σ‖ ≤ 1` and
`‖M_σ v‖ ≥ gap κ σ ‖v‖` (`regularized_condition_lower`).

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.HilbertRegularization

noncomputable section
open ContinuousLinearMap HilbertBlocks
open scoped InnerProduct

abbrev Double (V : Type*) := WithLp 2 (V × V)

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The block realization of `Z ⊗ B`. -/
def signedDiagonal (B : V →L[ℂ] V) : Double V →L[ℂ] Double V :=
  blockMap B 0 0 (-B)

/-- The block realization of `X ⊗ I`. -/
def exchange : Double V →L[ℂ] Double V := blockMap 0 1 1 0

/-- The real-weighted regularization, before choosing the public angle. -/
def weighted (B : V →L[ℂ] V) (a σ : ℝ) : Double V →L[ℂ] Double V :=
  blockMap ((a : ℂ) • B) ((σ : ℂ) • 1)
    ((σ : ℂ) • 1) (-((a : ℂ) • B))

/-- The actual regularized operator from the manuscript. -/
def regularized (B : V →L[ℂ] V) (σ : ℝ) : Double V →L[ℂ] Double V :=
  weighted B (Real.sqrt (1 - σ ^ 2)) σ

@[simp] theorem weighted_apply (B : V →L[ℂ] V) (a σ : ℝ) (v : Double V) :
    weighted B a σ v = WithLp.toLp 2
      ((a : ℂ) • B v.fst + (σ : ℂ) • v.snd,
       (σ : ℂ) • v.fst - (a : ℂ) • B v.snd) := by
  simp [weighted, blockMap_apply, sub_eq_add_neg]

/-- The two Pauli block actions anticommute exactly. -/
theorem signedDiagonal_exchange (B : V →L[ℂ] V) :
    signedDiagonal B * exchange = -(exchange * signedDiagonal B) := by
  ext v
  simp only [signedDiagonal, exchange, mul_apply_eq_comp, blockMap_apply,
    WithLp.fst, WithLp.snd, zero_apply, one_def, id_apply, neg_apply,
    add_zero, zero_add]
  change WithLp.toLp 2 (B v.snd, -B v.fst) =
    WithLp.toLp 2 (-(-B v.snd), -B v.fst)
  rw [neg_neg]

/-- The continuous Hilbert operator has the same square as its algebraic model. -/
theorem weighted_square_apply (B : V →L[ℂ] V) (a σ : ℝ) (v : Double V) :
    weighted B a σ (weighted B a σ v) = WithLp.toLp 2
      ((a : ℂ) ^ 2 • B (B v.fst) + (σ : ℂ) ^ 2 • v.fst,
       (a : ℂ) ^ 2 • B (B v.snd) + (σ : ℂ) ^ 2 • v.snd) := by
  simp only [weighted_apply, WithLp.fst, WithLp.snd]
  congr 1
  apply Prod.ext
  · simp only [map_add, map_smul]
    module
  · simp only [map_sub, map_smul]
    module

/-- Substitution of the square-root coefficient gives the advertised square. -/
theorem regularized_square_apply (B : V →L[ℂ] V) (σ : ℝ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : Double V) :
    regularized B σ (regularized B σ v) = WithLp.toLp 2
      (((1 - σ ^ 2 : ℝ) : ℂ) • B (B v.fst) + ((σ ^ 2 : ℝ) : ℂ) • v.fst,
       ((1 - σ ^ 2 : ℝ) : ℂ) • B (B v.snd) + ((σ ^ 2 : ℝ) : ℂ) • v.snd) := by
  have hnonneg : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  have hsquare : (Real.sqrt (1 - σ ^ 2) : ℂ) ^ 2 = ((1 - σ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hnonneg]
  have h := weighted_square_apply B (Real.sqrt (1 - σ ^ 2)) σ v
  rw [hsquare] at h
  simpa only [regularized, Complex.ofReal_pow] using h

/-- Squared norms of real scalar multiples, also for negative coefficients. -/
theorem norm_real_smul_sq (a : ℝ) (v : V) :
    ‖(a : ℂ) • v‖ ^ 2 = a ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

end Normed

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

private theorem block_star (A B C D : V →L[ℂ] V) :
    star (blockMap A B C D) = blockMap (star A) (star C) (star B) (star D) :=
  block_adjoint A B C D

/-- The Hermitian dilation uses the actual Hilbert-space adjoint. -/
def dilation (A : V →L[ℂ] V) : Double V →L[ℂ] Double V :=
  blockMap 0 A (star A) 0

@[simp] theorem dilation_apply (A : V →L[ℂ] V) (v : Double V) :
    dilation A v = WithLp.toLp 2 (A v.snd, (star A) v.fst) := by
  simp only [dilation, blockMap_apply, zero_apply, zero_add, add_zero]

/-- No normality assumption on A is needed for its dilation to be Hermitian. -/
theorem dilation_selfAdjoint (A : V →L[ℂ] V) :
    star (dilation A) = dilation A := by
  simp only [dilation, block_star, star_zero, star_star]

/-- The square separates the two ordered Gram operators. -/
theorem dilation_square (A : V →L[ℂ] V) :
    dilation A * dilation A = blockMap (A * star A) 0 0 (star A * A) := by
  simp only [dilation, block_mul, zero_mul, mul_zero, zero_add, add_zero]

/-- Exact energy law for the Hermitian dilation. -/
theorem dilation_norm_sq (A : V →L[ℂ] V) (v : Double V) :
    ‖dilation A v‖ ^ 2 = ‖A v.snd‖ ^ 2 + ‖(star A) v.fst‖ ^ 2 := by
  simp only [dilation_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.fst, WithLp.snd]

/-- The dilation preserves the operator-norm bound of its input. -/
theorem dilation_norm_le_one (A : V →L[ℂ] V) (hA : ‖A‖ ≤ 1) :
    ‖dilation A‖ ≤ 1 := by
  have hAstar : ‖star A‖ ≤ 1 := by
    change ‖ContinuousLinearMap.adjoint A‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact hA
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  have h₁ : ‖A v.snd‖ ≤ ‖v.snd‖ := by
    calc
      _ ≤ ‖A‖ * ‖v.snd‖ := A.le_opNorm v.snd
      _ ≤ 1 * ‖v.snd‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
      _ = _ := one_mul _
  have h₂ : ‖(star A) v.fst‖ ≤ ‖v.fst‖ := by
    calc
      _ ≤ ‖star A‖ * ‖v.fst‖ := (star A).le_opNorm v.fst
      _ ≤ 1 * ‖v.fst‖ := mul_le_mul_of_nonneg_right hAstar (norm_nonneg _)
      _ = _ := one_mul _
  have hs₁ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 h₁
  have hs₂ := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 h₂
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [dilation_norm_sq, WithLp.prod_norm_sq_eq_of_L2]
  linarith

/-- Squared lower singular bounds for A and its adjoint pass to the dilation. -/
theorem dilation_lower_sq (A : V →L[ℂ] V) (μ : ℝ)
    (hA : ∀ v, μ ^ 2 * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2)
    (hAstar : ∀ v, μ ^ 2 * ‖v‖ ^ 2 ≤ ‖(star A) v‖ ^ 2)
    (v : Double V) : μ ^ 2 * ‖v‖ ^ 2 ≤ ‖dilation A v‖ ^ 2 := by
  rw [dilation_norm_sq, WithLp.prod_norm_sq_eq_of_L2]
  nlinarith [hA v.snd, hAstar v.fst]

/-- The signed diagonal remains Hermitian. -/
theorem signedDiagonal_selfAdjoint (B : V →L[ℂ] V) (hB : star B = B) :
    star (signedDiagonal B) = signedDiagonal B := by
  simp only [signedDiagonal, block_star, star_zero, star_neg, hB]

/-- The exchange is a Hermitian involution. -/
theorem exchange_selfAdjoint :
    star (exchange : Double V →L[ℂ] Double V) = exchange := by
  simp only [exchange, block_star, star_zero, star_one]

omit [CompleteSpace V] in
theorem exchange_square : (exchange : Double V →L[ℂ] Double V) * exchange = 1 := by
  simp only [exchange, block_mul, zero_mul, mul_zero, one_mul,
    add_zero, zero_add, block_identity]

/-- Every real-weighted regularization is Hermitian when B is Hermitian. -/
theorem weighted_selfAdjoint (B : V →L[ℂ] V) (hB : star B = B) (a σ : ℝ) :
    star (weighted B a σ) = weighted B a σ := by
  simp only [weighted, block_star, star_smul, star_neg, star_one, hB,
    Complex.star_def, Complex.conj_ofReal]

/-- The manuscript's chosen regularization is therefore Hermitian. -/
theorem regularized_selfAdjoint (B : V →L[ℂ] V) (hB : star B = B) (σ : ℝ) :
    star (regularized B σ) = regularized B σ :=
  weighted_selfAdjoint B hB _ _

/-- Self-adjointness cancels exactly the two mixed inner-product terms. -/
theorem weighted_norm_sq (B : V →L[ℂ] V) (hB : star B = B)
    (a σ : ℝ) (v : Double V) :
    ‖weighted B a σ v‖ ^ 2 =
      a ^ 2 * (‖B v.fst‖ ^ 2 + ‖B v.snd‖ ^ 2) + σ ^ 2 * ‖v‖ ^ 2 := by
  have hi : inner ℂ (B v.fst) v.snd = inner ℂ v.fst (B v.snd) := by
    have h := adjoint_inner_left B v.snd v.fst
    rw [show (ContinuousLinearMap.adjoint B) = B from hB] at h
    exact h
  rw [weighted_apply, WithLp.prod_norm_sq_eq_of_L2,
    WithLp.prod_norm_sq_eq_of_L2]
  change ‖(a : ℂ) • B v.fst + (σ : ℂ) • v.snd‖ ^ 2 +
    ‖(σ : ℂ) • v.fst - (a : ℂ) • B v.snd‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  simp only [norm_real_smul_sq, inner_smul_left, inner_smul_right,
    RCLike.re_to_complex, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, hi]
  ring

/-- Exact squared norm identity, now with the actual regularization parameter. -/
theorem regularized_norm_sq (B : V →L[ℂ] V) (hB : star B = B) (σ : ℝ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : Double V) :
    ‖regularized B σ v‖ ^ 2 =
      (1 - σ ^ 2) * (‖B v.fst‖ ^ 2 + ‖B v.snd‖ ^ 2) + σ ^ 2 * ‖v‖ ^ 2 := by
  have hnonneg : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  rw [regularized, weighted_norm_sq B hB, Real.sq_sqrt hnonneg]

/-- A contraction remains a contraction under regularization. -/
theorem regularized_norm_le_one (B : V →L[ℂ] V) (hB : star B = B)
    (hBound : ‖B‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    ‖regularized B σ‖ ≤ 1 := by
  have hpoint (x : V) : ‖B x‖ ≤ ‖x‖ := by
    calc
      _ ≤ ‖B‖ * ‖x‖ := B.le_opNorm x
      _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hBound (norm_nonneg _)
      _ = _ := one_mul _
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hf := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hpoint v.fst)
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hpoint v.snd)
  have hw : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hf hs) hw
  rw [regularized_norm_sq B hB σ hσ₀ hσ₁]
  simp only [WithLp.prod_norm_sq_eq_of_L2]
  nlinarith

/-- The squared singular lower bound improves by the public regularization. -/
theorem regularized_lower_sq (B : V →L[ℂ] V) (hB : star B = B)
    (μ σ : ℝ) (hLower : ∀ x, μ ^ 2 * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : Double V) :
    (σ ^ 2 + (1 - σ ^ 2) * μ ^ 2) * ‖v‖ ^ 2 ≤ ‖regularized B σ v‖ ^ 2 := by
  have hw : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  have hsum := mul_le_mul_of_nonneg_left
    (add_le_add (hLower v.fst) (hLower v.snd)) hw
  rw [regularized_norm_sq B hB σ hσ₀ hσ₁]
  simp only [WithLp.prod_norm_sq_eq_of_L2]
  nlinarith

/-- An explicit square-root gap follows from the proved squared-norm bound. -/
theorem regularized_lower (B : V →L[ℂ] V) (hB : star B = B)
    (μ σ : ℝ) (hLower : ∀ x, μ ^ 2 * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : Double V) :
    Real.sqrt (σ ^ 2 + (1 - σ ^ 2) * μ ^ 2) * ‖v‖ ≤ ‖regularized B σ v‖ := by
  have hw : 0 ≤ 1 - σ ^ 2 := by
    nlinarith [mul_self_le_mul_self hσ₀ hσ₁]
  have hrad : 0 ≤ σ ^ 2 + (1 - σ ^ 2) * μ ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hw (sq_nonneg _))
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (norm_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt hrad]
  exact regularized_lower_sq B hB μ σ hLower hσ₀ hσ₁ v

/-- The actual regularized map has the manuscript's named lower gap. -/
theorem regularized_condition_lower (B : V →L[ℂ] V) (hB : star B = B)
    (κ σ : ℝ) (hLower : ∀ x, (1 / κ) ^ 2 * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : Double V) :
    RegularizationGap.gap κ σ * ‖v‖ ≤ ‖regularized B σ v‖ := by
  have h := regularized_lower B hB (1 / κ) σ hLower hσ₀ hσ₁ v
  have hrad : σ ^ 2 + (1 - σ ^ 2) * (1 / κ) ^ 2 =
      RegularizationGap.square κ σ := by
    unfold RegularizationGap.square
    ring
  rw [hrad] at h
  exact h

/-- Positivity of the derived gap proves injectivity without assuming it. -/
theorem regularized_injective (B : V →L[ℂ] V) (hB : star B = B)
    (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hLower : ∀ x, (1 / κ) ^ 2 * ‖x‖ ^ 2 ≤ ‖B x‖ ^ 2)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    Function.Injective (regularized B σ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have h := regularized_condition_lower B hB κ σ hLower hσ₀ hσ₁ (x - y)
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hg := RegularizationGap.gap_pos κ σ hκ hσ₀ hσ₁
  have hn := norm_nonneg (x - y)
  nlinarith

end Hilbert
end
end SparseLinearSystems.HilbertRegularization
