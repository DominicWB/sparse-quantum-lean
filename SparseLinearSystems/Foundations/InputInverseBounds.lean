import SparseLinearSystems.Foundations.HilbertCayley

/-!
# Input inverse bounds and the regularized dilation

From the input promise, stated as a continuous linear equivalence `A` with
`‖A⁻¹‖ ≤ κ`: the lower bounds `‖A v‖ ≥ ‖v‖/κ` and `‖A† v‖ ≥ ‖v‖/κ` (the latter
from the adjoint of the inverse identity), the lower bound for the Hermitian
dilation, and the regularized dilation `M_σ` as a continuous linear
equivalence with `‖M_σ⁻¹‖ ≤ 1 / gap κ σ` (`regularizedDilationEquiv`,
`regularizedDilationEquiv_inverse_norm_le`).

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.InputInverseBounds

noncomputable section

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A bounded left inverse turns its norm bound into a pointwise lower bound. -/
theorem left_inverse_lower
    (T S : V →L[ℂ] V) (hST : S * T = 1)
    (κ : ℝ) (hκ : 0 < κ) (hNorm : ‖S‖ ≤ κ) (x : V) :
    (1 / κ) * ‖x‖ ≤ ‖T x‖ := by
  have hid := congrArg (fun F : V →L[ℂ] V => F x) hST
  change S (T x) = x at hid
  have hx : ‖x‖ ≤ κ * ‖T x‖ := by
    calc
      ‖x‖ = ‖S (T x)‖ := by rw [hid]
      _ ≤ ‖S‖ * ‖T x‖ := S.le_opNorm (T x)
      _ ≤ κ * ‖T x‖ :=
        mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
  calc
    (1 / κ) * ‖x‖ = ‖x‖ / κ := by ring
    _ ≤ ‖T x‖ := (div_le_iff₀ hκ).2 (by
      simpa only [mul_comm] using hx)

/-- Squared form of `left_inverse_lower`, matching the dilation energy law. -/
theorem left_inverse_lower_sq
    (T S : V →L[ℂ] V) (hST : S * T = 1)
    (κ : ℝ) (hκ : 0 < κ) (hNorm : ‖S‖ ≤ κ) (x : V) :
    (1 / κ) ^ 2 * ‖x‖ ^ 2 ≤ ‖T x‖ ^ 2 := by
  have h := left_inverse_lower T S hST κ hκ hNorm x
  have hinv : 0 ≤ 1 / κ := (one_div_pos.mpr hκ).le
  have hs := (sq_le_sq₀
    (mul_nonneg hinv (norm_nonneg x)) (norm_nonneg (T x))).2 h
  simpa only [mul_pow] using hs

/-- The inverse equivalence is a left inverse as a continuous linear map. -/
theorem equiv_inverse_mul (A : V ≃L[ℂ] V) :
    A.symm.toContinuousLinearMap * A.toContinuousLinearMap = 1 := by
  ext x
  change A.symm (A x) = x
  exact A.symm_apply_apply x

/-- The inverse equivalence is also a right inverse. -/
theorem equiv_mul_inverse (A : V ≃L[ℂ] V) :
    A.toContinuousLinearMap * A.symm.toContinuousLinearMap = 1 := by
  ext x
  change A (A.symm x) = x
  exact A.apply_symm_apply x

/-- The theorem's inverse-norm promise gives the ordinary singular lower bound. -/
theorem equiv_lower (A : V ≃L[ℂ] V) (κ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (x : V) :
    (1 / κ) * ‖x‖ ≤ ‖A.toContinuousLinearMap x‖ :=
  left_inverse_lower A.toContinuousLinearMap A.symm.toContinuousLinearMap
    (equiv_inverse_mul A) κ (lt_of_lt_of_le zero_lt_one hκ) hInv x

/-- Squared ordinary singular lower bound. -/
theorem equiv_lower_sq (A : V ≃L[ℂ] V) (κ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (x : V) :
    (1 / κ) ^ 2 * ‖x‖ ^ 2 ≤ ‖A.toContinuousLinearMap x‖ ^ 2 :=
  left_inverse_lower_sq A.toContinuousLinearMap A.symm.toContinuousLinearMap
    (equiv_inverse_mul A) κ (lt_of_lt_of_le zero_lt_one hκ) hInv x

end Normed

section Hilbert

variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Taking adjoints of the right-inverse law supplies the needed left inverse
for the actual Hilbert adjoint of the input map. -/
theorem equiv_adjoint_inverse_mul (A : V ≃L[ℂ] V) :
    star A.symm.toContinuousLinearMap * star A.toContinuousLinearMap = 1 := by
  have h := congrArg star (equiv_mul_inverse A)
  simpa only [star_mul, star_one] using h

/-- The adjoint singular lower bound follows from the same inverse promise. -/
theorem equiv_adjoint_lower (A : V ≃L[ℂ] V) (κ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (x : V) :
    (1 / κ) * ‖x‖ ≤ ‖(star A.toContinuousLinearMap) x‖ := by
  apply left_inverse_lower (star A.toContinuousLinearMap)
    (star A.symm.toContinuousLinearMap)
    (equiv_adjoint_inverse_mul A) κ (lt_of_lt_of_le zero_lt_one hκ)
  change ‖ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap‖ ≤ κ
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact hInv

/-- Squared adjoint singular lower bound. -/
theorem equiv_adjoint_lower_sq (A : V ≃L[ℂ] V) (κ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (x : V) :
    (1 / κ) ^ 2 * ‖x‖ ^ 2 ≤ ‖(star A.toContinuousLinearMap) x‖ ^ 2 := by
  apply left_inverse_lower_sq (star A.toContinuousLinearMap)
    (star A.symm.toContinuousLinearMap)
    (equiv_adjoint_inverse_mul A) κ (lt_of_lt_of_le zero_lt_one hκ)
  change ‖ContinuousLinearMap.adjoint A.symm.toContinuousLinearMap‖ ≤ κ
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact hInv

/-- The Hermitian dilation inherits the lower singular bound from the one
inverse-norm promise on the original input. -/
theorem dilation_lower_sq (A : V ≃L[ℂ] V) (κ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (v : HilbertRegularization.Double V) :
    (1 / κ) ^ 2 * ‖v‖ ^ 2 ≤
      ‖HilbertRegularization.dilation A.toContinuousLinearMap v‖ ^ 2 :=
  HilbertRegularization.dilation_lower_sq A.toContinuousLinearMap (1 / κ)
    (equiv_lower_sq A κ hκ hInv)
    (equiv_adjoint_lower_sq A κ hκ hInv) v

/-- The concrete double regularization has exactly the manuscript gap
`sqrt (σ² + (1-σ²)/κ²)`. -/
theorem regularized_dilation_lower
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (v : HilbertRegularization.Double (HilbertRegularization.Double V)) :
    RegularizationGap.gap κ σ * ‖v‖ ≤
      ‖HilbertRegularization.regularized
        (HilbertRegularization.dilation A.toContinuousLinearMap) σ v‖ :=
  HilbertRegularization.regularized_condition_lower
    (HilbertRegularization.dilation A.toContinuousLinearMap)
    (HilbertRegularization.dilation_selfAdjoint A.toContinuousLinearMap)
    κ σ (dilation_lower_sq A κ hκ hInv) hσ₀ hσ₁ v

section FiniteDimensional

variable [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- The regularized dilation is injective using only the original inverse-norm
promise.  This is the concrete injectivity statement needed before passing to
the augmented kernel construction. -/
theorem regularized_dilation_injective
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    Function.Injective
      (HilbertRegularization.regularized
        (HilbertRegularization.dilation A.toContinuousLinearMap) σ) :=
  HilbertRegularization.regularized_injective
    (HilbertRegularization.dilation A.toContinuousLinearMap)
    (HilbertRegularization.dilation_selfAdjoint A.toContinuousLinearMap)
    κ σ hκ (dilation_lower_sq A κ hκ hInv) hσ₀ hσ₁

/-- In finite dimension the concrete regularized dilation is surjective as
well as injective. -/
theorem regularized_dilation_surjective
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    Function.Surjective
      (HilbertRegularization.regularized
        (HilbertRegularization.dilation A.toContinuousLinearMap) σ) :=
  (LinearMap.injective_iff_surjective
    (f := (HilbertRegularization.regularized
      (HilbertRegularization.dilation A.toContinuousLinearMap) σ).toLinearMap)).mp
    (regularized_dilation_injective A κ σ hκ hInv hσ₀ hσ₁)

/-- The algebraic equivalence underlying the regularized principal block. -/
def regularizedDilationLinearEquiv
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    HilbertRegularization.Double (HilbertRegularization.Double V) ≃ₗ[ℂ]
      HilbertRegularization.Double (HilbertRegularization.Double V) :=
  LinearEquiv.ofBijective
    (HilbertRegularization.regularized
      (HilbertRegularization.dilation A.toContinuousLinearMap) σ).toLinearMap
    ⟨regularized_dilation_injective A κ σ hκ hInv hσ₀ hσ₁,
      regularized_dilation_surjective A κ σ hκ hInv hσ₀ hσ₁⟩

/-- The continuous equivalence used as the principal block of the augmented
Hamiltonian.  Continuity of the inverse is supplied by finite dimensionality,
not postulated. -/
def regularizedDilationEquiv
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    HilbertRegularization.Double (HilbertRegularization.Double V) ≃L[ℂ]
      HilbertRegularization.Double (HilbertRegularization.Double V) :=
  (regularizedDilationLinearEquiv A κ σ hκ hInv hσ₀ hσ₁).toContinuousLinearEquiv

@[simp] theorem regularizedDilationEquiv_apply
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (v : HilbertRegularization.Double (HilbertRegularization.Double V)) :
    regularizedDilationEquiv A κ σ hκ hInv hσ₀ hσ₁ v =
      HilbertRegularization.regularized
        (HilbertRegularization.dilation A.toContinuousLinearMap) σ v := rfl

/-- Pointwise inverse bound for the constructed regularized equivalence. -/
theorem regularizedDilationEquiv_symm_norm_le
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (y : HilbertRegularization.Double (HilbertRegularization.Double V)) :
    ‖(regularizedDilationEquiv A κ σ hκ hInv hσ₀ hσ₁).symm y‖ ≤
      (1 / RegularizationGap.gap κ σ) * ‖y‖ := by
  let E := regularizedDilationEquiv A κ σ hκ hInv hσ₀ hσ₁
  have hgap := RegularizationGap.gap_pos κ σ hκ hσ₀ hσ₁
  have hlower := regularized_dilation_lower A κ σ hκ hInv hσ₀ hσ₁ (E.symm y)
  have happly :
      HilbertRegularization.regularized
        (HilbertRegularization.dilation A.toContinuousLinearMap) σ (E.symm y) = y := by
    change E (E.symm y) = y
    exact E.apply_symm_apply y
  rw [happly] at hlower
  have hdiv : ‖E.symm y‖ ≤ ‖y‖ / RegularizationGap.gap κ σ :=
    (le_div_iff₀ hgap).2 (by simpa only [mul_comm] using hlower)
  calc
    ‖E.symm y‖ ≤ ‖y‖ / RegularizationGap.gap κ σ := hdiv
    _ = (1 / RegularizationGap.gap κ σ) * ‖y‖ := by ring

/-- Operator-norm form of the inverse bound.  This is the precise condition
number estimate consumed by the augmented-system lemmas. -/
theorem regularizedDilationEquiv_inverse_norm_le
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    ‖(regularizedDilationEquiv A κ σ hκ hInv hσ₀ hσ₁).symm.toContinuousLinearMap‖ ≤
      1 / RegularizationGap.gap κ σ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (one_div_nonneg.mpr (RegularizationGap.gap_nonneg κ σ))
  intro y
  exact regularizedDilationEquiv_symm_norm_le A κ σ hκ hInv hσ₀ hσ₁ y

end FiniteDimensional

end Hilbert
end
end SparseLinearSystems.InputInverseBounds
