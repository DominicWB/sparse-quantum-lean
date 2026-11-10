import SparseLinearSystems.Augmented.Solution

/-!
# The solution-norm ladder (equation `qls:eq:normladder`)

For `r_σ = ‖M_σ⁻¹ β‖` with `‖A‖ ≤ 1`, `‖A⁻¹‖ ≤ κ` and `‖β‖ = 1`:

* `rSigma_one`: `r_1 = 1`;
* `one_le_rSigma`, `rSigma_le_kappa`: `1 ≤ r_σ ≤ κ`;
* `rSigma_anti`: `r_σ ≤ r_{σ'}` for `σ' ≤ σ` (in particular `r_σ ≤ r_{σ/2}`, `r_σ ≤ r_0`);
* `rSigma_half_le`: `r_{σ/2} ≤ 2 r_σ`;
* `rSigma_zero_le`: `r_0 ≤ √(1 + κ²σ²) r_σ`.

The proof is variational rather than spectral: for a self-adjoint invertible
`M`, `‖M⁻¹ β‖² = max_z (2 Re⟪β, z⟫ - ‖M z‖²)`, so a pointwise inequality
`‖M y‖² ≤ c ‖M' y‖²` gives `‖M'⁻¹ β‖² ≤ c ‖M⁻¹ β‖²` (`inv_norm_sq_le`).
The quadratic forms are explicit: `‖M_σ y‖² = (1 - σ²) Q(y) + σ² ‖y‖²` with
`‖y‖²/κ² ≤ Q(y) ≤ ‖y‖²`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Augmented

noncomputable section
open ContinuousLinearMap HilbertBlocks HilbertRegularization HilbertAugmentation
open scoped InnerProduct ComplexConjugate

/-! ### Variational comparison -/

section Variational

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- For self-adjoint `M`: `2 Re⟪β, z⟫ - ‖M z‖² ≤ ‖M⁻¹ β‖²`. -/
theorem inv_norm_sq_ge (M : W ≃L[ℂ] W) (hM : ∀ u v, inner ℂ (M u) v = inner ℂ u (M v))
    (β z : W) : 2 * (inner ℂ β z).re - ‖M z‖ ^ 2 ≤ ‖M.symm β‖ ^ 2 := by
  have hβ : β = M (M.symm β) := (M.apply_symm_apply β).symm
  have h1 : inner ℂ β z = inner ℂ (M.symm β) (M z) := by
    conv_lhs => rw [hβ]
    exact hM _ _
  have h2 := norm_sub_sq (𝕜 := ℂ) (M.symm β) (M z)
  have h3 : 0 ≤ ‖M.symm β - M z‖ ^ 2 := sq_nonneg _
  rw [h1]
  rw [RCLike.re_to_complex] at h2
  linarith

/-- **Variational comparison.**  If `‖M y‖² ≤ c ‖M' y‖²` for all `y`, then
`‖M'⁻¹ β‖² ≤ c ‖M⁻¹ β‖²`. -/
theorem inv_norm_sq_le (M M' : W ≃L[ℂ] W) (hM : ∀ u v, inner ℂ (M u) v = inner ℂ u (M v))
    (hM' : ∀ u v, inner ℂ (M' u) v = inner ℂ u (M' v)) (c : ℝ) (hc : 0 < c)
    (hcmp : ∀ y, ‖M y‖ ^ 2 ≤ c * ‖M' y‖ ^ 2) (β : W) :
    ‖M'.symm β‖ ^ 2 ≤ c * ‖M.symm β‖ ^ 2 := by
  set w' := M'.symm β with hw'
  set y := M'.symm w' with hy
  have hMy : M' y = w' := M'.apply_symm_apply w'
  have hβ : β = M' w' := (M'.apply_symm_apply β).symm
  have hinner : (inner ℂ β y).re = ‖w'‖ ^ 2 := by
    have h : inner ℂ β y = inner ℂ w' (M' y) := by
      conv_lhs => rw [hβ]
      exact hM' _ _
    rw [h, hMy, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hv := inv_norm_sq_ge M hM β (((c⁻¹ : ℝ) : ℂ) • y)
  rw [inner_smul_right, Complex.re_ofReal_mul, hinner, map_smul, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), mul_pow] at hv
  have hcm := hcmp y
  rw [hMy] at hcm
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  -- `‖M (c⁻¹ y)‖² = c⁻² ‖M y‖² ≤ c⁻¹ ‖w'‖²`
  have hq : c⁻¹ ^ 2 * ‖M y‖ ^ 2 ≤ c⁻¹ * ‖w'‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hcm (sq_nonneg c⁻¹)
    calc c⁻¹ ^ 2 * ‖M y‖ ^ 2 ≤ c⁻¹ ^ 2 * (c * ‖w'‖ ^ 2) := this
      _ = c⁻¹ * ‖w'‖ ^ 2 := by field_simp
  have hfinal : c⁻¹ * ‖w'‖ ^ 2 ≤ ‖M.symm β‖ ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hfinal hc.le
  rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at this

end Variational

/-! ### The regularized quadratic form -/

variable {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [FiniteDimensional ℂ V₀]
  [CompleteSpace V₀]

section Ladder

variable (A : V₀ ≃L[ℂ] V₀) (κ : ℝ) (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)

omit [FiniteDimensional ℂ V₀] in
/-- The dilation part of the quadratic form. -/
theorem dilation_form_le (hA : ‖A.toContinuousLinearMap‖ ≤ 1) (y : Sys V₀) :
    ‖dilation A.toContinuousLinearMap y.fst‖ ^ 2 + ‖dilation A.toContinuousLinearMap y.snd‖ ^ 2 ≤
      ‖y‖ ^ 2 := by
  have hD := dilation_norm_le_one A.toContinuousLinearMap hA
  have h1 : ‖dilation A.toContinuousLinearMap y.fst‖ ≤ ‖y.fst‖ :=
    ((dilation A.toContinuousLinearMap).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans (le_of_eq (one_mul _)))
  have h2 : ‖dilation A.toContinuousLinearMap y.snd‖ ≤ ‖y.snd‖ :=
    ((dilation A.toContinuousLinearMap).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right hD (norm_nonneg _)).trans (le_of_eq (one_mul _)))
  rw [WithLp.prod_norm_sq_eq_of_L2 y]
  have := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

include hκ hInv in
omit [FiniteDimensional ℂ V₀] in
theorem dilation_form_ge (y : Sys V₀) :
    (1 / κ) ^ 2 * ‖y‖ ^ 2 ≤
      ‖dilation A.toContinuousLinearMap y.fst‖ ^ 2 + ‖dilation A.toContinuousLinearMap y.snd‖ ^ 2 := by
  have h1 := InputInverseBounds.dilation_lower_sq A κ hκ hInv y.fst
  have h2 := InputInverseBounds.dilation_lower_sq A κ hκ hInv y.snd
  rw [WithLp.prod_norm_sq_eq_of_L2 y]
  linarith

theorem Mσ_norm_sq (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (y : Sys V₀) :
    ‖Mσ A κ σ hκ hInv hσ₀ hσ₁ y‖ ^ 2 =
      (1 - σ ^ 2) * (‖dilation A.toContinuousLinearMap y.fst‖ ^ 2 +
        ‖dilation A.toContinuousLinearMap y.snd‖ ^ 2) + σ ^ 2 * ‖y‖ ^ 2 :=
  regularized_norm_sq _ (dilation_selfAdjoint _) σ hσ₀ hσ₁ y

theorem Mσ_selfAdjoint (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (u v : Sys V₀) :
    inner ℂ (Mσ A κ σ hκ hInv hσ₀ hσ₁ u) v = inner ℂ u (Mσ A κ σ hκ hInv hσ₀ hσ₁ v) := by
  have hs := regularized_selfAdjoint (dilation A.toContinuousLinearMap)
    (dilation_selfAdjoint _) σ
  change inner ℂ (regularized (dilation A.toContinuousLinearMap) σ u) v =
    inner ℂ u (regularized (dilation A.toContinuousLinearMap) σ v)
  rw [← adjoint_inner_left, show ContinuousLinearMap.adjoint
    (regularized (dilation A.toContinuousLinearMap) σ) =
      regularized (dilation A.toContinuousLinearMap) σ from hs]

theorem rSigma_congr {σ σ' : ℝ} (h : σ = σ') (h₀ : 0 ≤ σ) (h₁ : σ ≤ 1) (h₀' : 0 ≤ σ')
    (h₁' : σ' ≤ 1) (β : Sys V₀) :
    rSigma A κ σ hκ hInv h₀ h₁ β = rSigma A κ σ' hκ hInv h₀' h₁' β := by
  subst h
  rfl

/-- `r_1 = ‖β‖`. -/
theorem rSigma_one (β : Sys V₀) (h0 : (0 : ℝ) ≤ 1) (h1 : (1 : ℝ) ≤ 1) :
    rSigma A κ 1 hκ hInv h0 h1 β = ‖β‖ := by
  have h := Mσ_norm_sq A κ hκ hInv 1 h0 h1 ((Mσ A κ 1 hκ hInv h0 h1).symm β)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  have h' : ‖β‖ ^ 2 = ‖(Mσ A κ 1 hκ hInv h0 h1).symm β‖ ^ 2 := by rw [h]; ring
  rw [rSigma]
  exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h').symm

/-- `r_σ ≤ r_{σ'}` whenever `σ' ≤ σ`. -/
theorem rSigma_anti (hA : ‖A.toContinuousLinearMap‖ ≤ 1) (σ σ' : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (hσ'₀ : 0 ≤ σ') (hσ'₁ : σ' ≤ 1) (hσσ' : σ' ≤ σ) (β : Sys V₀) :
    rSigma A κ σ hκ hInv hσ₀ hσ₁ β ≤ rSigma A κ σ' hκ hInv hσ'₀ hσ'₁ β := by
  have h := inv_norm_sq_le (Mσ A κ σ' hκ hInv hσ'₀ hσ'₁) (Mσ A κ σ hκ hInv hσ₀ hσ₁)
    (Mσ_selfAdjoint A κ hκ hInv σ' hσ'₀ hσ'₁) (Mσ_selfAdjoint A κ hκ hInv σ hσ₀ hσ₁) 1 one_pos
    (fun y => by
      rw [Mσ_norm_sq, Mσ_norm_sq, one_mul]
      have hQ := dilation_form_le A hA y
      have hss : σ' ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hσ'₀ hσσ' 2
      nlinarith) β
  rw [one_mul] at h
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- `r_{σ/2} ≤ 2 r_σ`. -/
theorem rSigma_half_le (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (h₀ : 0 ≤ σ / 2) (h₁ : σ / 2 ≤ 1)
    (β : Sys V₀) :
    rSigma A κ (σ / 2) hκ hInv h₀ h₁ β ≤ 2 * rSigma A κ σ hκ hInv hσ₀ hσ₁ β := by
  have h := inv_norm_sq_le (Mσ A κ σ hκ hInv hσ₀ hσ₁) (Mσ A κ (σ / 2) hκ hInv h₀ h₁)
    (Mσ_selfAdjoint A κ hκ hInv σ hσ₀ hσ₁) (Mσ_selfAdjoint A κ hκ hInv (σ / 2) h₀ h₁) 4
    (by norm_num)
    (fun y => by
      rw [Mσ_norm_sq, Mσ_norm_sq]
      have hQ := dilation_form_ge A κ hκ hInv y
      have hQ0 : 0 ≤ (1 / κ) ^ 2 * ‖y‖ ^ 2 := by positivity
      nlinarith) β
  unfold rSigma
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  linarith

/-- `r_0 ≤ √(1 + κ²σ²) r_σ`. -/
theorem rSigma_zero_le (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (h₀ : (0 : ℝ) ≤ 0) (h₁ : (0 : ℝ) ≤ 1)
    (β : Sys V₀) :
    rSigma A κ 0 hκ hInv h₀ h₁ β ≤
      Real.sqrt (1 + κ ^ 2 * σ ^ 2) * rSigma A κ σ hκ hInv hσ₀ hσ₁ β := by
  have hκ0 : 0 < κ := by linarith
  have h := inv_norm_sq_le (Mσ A κ σ hκ hInv hσ₀ hσ₁) (Mσ A κ 0 hκ hInv h₀ h₁)
    (Mσ_selfAdjoint A κ hκ hInv σ hσ₀ hσ₁) (Mσ_selfAdjoint A κ hκ hInv 0 h₀ h₁)
    (1 + κ ^ 2 * σ ^ 2) (by positivity)
    (fun y => by
      rw [Mσ_norm_sq, Mσ_norm_sq]
      have hQ := dilation_form_ge A κ hκ hInv y
      set Q := ‖dilation A.toContinuousLinearMap y.fst‖ ^ 2 +
        ‖dilation A.toContinuousLinearMap y.snd‖ ^ 2
      have hy : ‖y‖ ^ 2 ≤ κ ^ 2 * Q := by
        have e : (1 / κ) ^ 2 * ‖y‖ ^ 2 = ‖y‖ ^ 2 / κ ^ 2 := by field_simp
        rw [e, div_le_iff₀ (by positivity)] at hQ
        linarith
      have hQ0 : 0 ≤ Q := by positivity
      have hs2 : 0 ≤ σ ^ 2 := sq_nonneg σ
      norm_num
      nlinarith [mul_le_mul_of_nonneg_left hy hs2]) β
  unfold rSigma
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  linarith

/-- `‖β‖ ≤ r_σ`. -/
theorem one_le_rSigma (hA : ‖A.toContinuousLinearMap‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : Sys V₀) : ‖β‖ ≤ rSigma A κ σ hκ hInv hσ₀ hσ₁ β := by
  rw [← rSigma_one A κ hκ hInv β zero_le_one le_rfl]
  exact rSigma_anti A κ hκ hInv hA 1 σ zero_le_one le_rfl hσ₀ hσ₁ hσ₁ β

/-- `r_σ ≤ κ ‖β‖`. -/
theorem rSigma_le_kappa (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (β : Sys V₀) :
    rSigma A κ σ hκ hInv hσ₀ hσ₁ β ≤ κ * ‖β‖ := by
  have hκ0 : 0 < κ := by linarith
  have h := inv_norm_sq_le (Mσ A κ 1 hκ hInv zero_le_one le_rfl) (Mσ A κ σ hκ hInv hσ₀ hσ₁)
    (Mσ_selfAdjoint A κ hκ hInv 1 zero_le_one le_rfl) (Mσ_selfAdjoint A κ hκ hInv σ hσ₀ hσ₁)
    (κ ^ 2) (by positivity)
    (fun y => by
      rw [Mσ_norm_sq, Mσ_norm_sq]
      have hQ := dilation_form_ge A κ hκ hInv y
      set Q := ‖dilation A.toContinuousLinearMap y.fst‖ ^ 2 +
        ‖dilation A.toContinuousLinearMap y.snd‖ ^ 2
      have hy : ‖y‖ ^ 2 ≤ κ ^ 2 * Q := by
        have e : (1 / κ) ^ 2 * ‖y‖ ^ 2 = ‖y‖ ^ 2 / κ ^ 2 := by field_simp
        rw [e, div_le_iff₀ (by positivity)] at hQ
        linarith
      have hσw : 0 ≤ 1 - σ ^ 2 := by nlinarith
      have hκ1 : 1 ≤ κ ^ 2 := by nlinarith
      norm_num
      have hyy : 0 ≤ ‖y‖ ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hy hσw, mul_le_mul_of_nonneg_right hκ1
        (mul_nonneg (sq_nonneg σ) hyy)]) β
  have h1 := rSigma_one A κ hκ hInv β zero_le_one le_rfl
  unfold rSigma at h1 ⊢
  rw [h1] at h
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow]
  linarith

end Ladder

end

end SparseLinearSystems.Augmented
