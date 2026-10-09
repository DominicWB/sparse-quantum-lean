import SparseLinearSystems.Foundations.InputInverseBounds

/-!
# The nonzero-eigenvalue gap of the augmented Hamiltonian

The dense appended column does not reduce the nonzero singular values below
those of the invertible principal block.  The proof constructs the bounded
right inverse `y ↦ (M⁻¹ y, 0)` of `[M, -cβ]`, takes its adjoint and applies a
bounded-left-inverse estimate.  For the regularized augmentation `H_σ` this
gives: `H_σ` is self-adjoint, its kernel is the line through the normalized
generator, and every nonzero eigenvalue has modulus at least `gap κ σ`
(`regularizedAugmentedHamiltonian_nonzero_eigenvalue_gap`, equation
`qls:eq:auggap`).
-/

namespace SparseLinearSystems.HilbertAugmentationGap

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Isometric inclusion into the principal coordinate of the augmented
right-hand sector. -/
def firstEmbedding : V →ₗᵢ[ℂ] HilbertAugmentation.RightSpace V where
  toLinearMap :=
    { toFun := fun y => WithLp.toLp 2 (y, 0)
      map_add' := by
        intro x y
        change WithLp.toLp 2 (x + y, 0) =
          WithLp.toLp 2 (x + y, (0 : ℂ) + 0)
        rw [zero_add]
      map_smul' := by
        intro z y
        change WithLp.toLp 2 (z • y, 0) =
          WithLp.toLp 2 (z • y, z • (0 : ℂ))
        rw [smul_zero] }
  norm_map' := WithLp.norm_toLp_fst 2 V ℂ

omit [CompleteSpace V] in
@[simp] theorem firstEmbedding_apply (y : V) :
    firstEmbedding y = WithLp.toLp 2 (y, 0) := rfl

/-- The explicit bounded right inverse of the augmented row. -/
def columnRightInverse (M : V ≃L[ℂ] V) :
    V →L[ℂ] HilbertAugmentation.RightSpace V :=
  firstEmbedding.toContinuousLinearMap ∘L M.symm.toContinuousLinearMap

omit [CompleteSpace V] in
@[simp] theorem columnRightInverse_apply (M : V ≃L[ℂ] V) (y : V) :
    columnRightInverse M y = WithLp.toLp 2 (M.symm y, 0) := rfl

omit [CompleteSpace V] in
/-- The appended dense column disappears on the chosen right inverse. -/
theorem column_comp_rightInverse
    (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    HilbertAugmentation.column M β c ∘L columnRightInverse M = 1 := by
  ext y
  change M (M.symm y) - (0 : ℂ) • (c • β) = y
  rw [M.apply_symm_apply, zero_smul, sub_zero]

omit [CompleteSpace V] in
/-- Adding the scalar coordinate does not increase the norm of the constructed
right inverse beyond the norm of the principal inverse. -/
theorem columnRightInverse_norm_le (M : V ≃L[ℂ] V) :
    ‖columnRightInverse M‖ ≤ ‖M.symm.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro y
  change ‖firstEmbedding (M.symm y)‖ ≤
    ‖M.symm.toContinuousLinearMap‖ * ‖y‖
  rw [firstEmbedding.norm_map]
  exact M.symm.toContinuousLinearMap.le_opNorm y

/-- Taking adjoints of the explicit right-inverse equation gives the left
inverse used to bound the augmented column adjoint. -/
theorem rightInverse_adjoint_comp_column_adjoint
    (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    (ContinuousLinearMap.adjoint (columnRightInverse M)) ∘L (ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) = 1 := by
  have h := congrArg
    (fun T : V →L[ℂ] V => (ContinuousLinearMap.adjoint T)) (column_comp_rightInverse M β c)
  simpa only [adjoint_comp, adjoint_one] using h

/-- Quantitative lower singular bound for the adjoint of the augmented row.
It is independent of the appended vector and scalar coefficient. -/
theorem column_adjoint_lower
    (M : V ≃L[ℂ] V) (β : V) (c : ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hInv : ‖M.symm.toContinuousLinearMap‖ ≤ 1 / δ)
    (y : V) :
    δ * ‖y‖ ≤ ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y‖ := by
  have hAdjNorm : ‖(ContinuousLinearMap.adjoint (columnRightInverse M))‖ ≤ 1 / δ := by
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (columnRightInverse_norm_le M).trans hInv
  have hid := congrArg (fun T : V →L[ℂ] V => T y)
    (rightInverse_adjoint_comp_column_adjoint M β c)
  change (ContinuousLinearMap.adjoint (columnRightInverse M))
    ((ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y) = y at hid
  have hn : ‖y‖ ≤ (1 / δ) *
      ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y‖ := by
    calc
      ‖y‖ = ‖(ContinuousLinearMap.adjoint (columnRightInverse M))
          ((ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y)‖ :=
        congrArg norm hid.symm
      _ ≤ ‖ContinuousLinearMap.adjoint (columnRightInverse M)‖ *
          ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y‖ :=
        (ContinuousLinearMap.adjoint (columnRightInverse M)).le_opNorm _
      _ ≤ _ := mul_le_mul_of_nonneg_right hAdjNorm (norm_nonneg _)
  calc
    δ * ‖y‖ ≤ δ * ((1 / δ) *
        ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y‖) :=
      mul_le_mul_of_nonneg_left hn hδ.le
    _ = _ := by field_simp [ne_of_gt hδ]

/-- Squared form of the augmented column-adjoint lower bound. -/
theorem column_adjoint_lower_sq
    (M : V ≃L[ℂ] V) (β : V) (c : ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hInv : ‖M.symm.toContinuousLinearMap‖ ≤ 1 / δ)
    (y : V) :
    δ ^ 2 * ‖y‖ ^ 2 ≤ ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y‖ ^ 2 := by
  have h := column_adjoint_lower M β c δ hδ hInv y
  have hs := (sq_le_sq₀
    (mul_nonneg hδ.le (norm_nonneg y))
    (norm_nonneg ((ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y))).2 h
  simpa only [mul_pow] using hs

/-- The Gram operator of the augmented row is bounded below by `δ²` in
quadratic-form sense.  This is the coordinate-free statement behind
`C C† = M M† + |c|² |β><β|`. -/
theorem column_gram_rayleigh_lower
    (M : V ≃L[ℂ] V) (β : V) (c : ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hInv : ‖M.symm.toContinuousLinearMap‖ ≤ 1 / δ)
    (y : V) :
    δ ^ 2 * ‖y‖ ^ 2 ≤
      (inner ℂ
        (HilbertAugmentation.column M β c
          ((ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y)) y).re := by
  calc
    δ ^ 2 * ‖y‖ ^ 2 ≤
        ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y‖ ^ 2 :=
      column_adjoint_lower_sq M β c δ hδ hInv y
    _ = (inner ℂ
        (HilbertAugmentation.column M β c
          ((ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y)) y).re := by
      have h := congrArg (RCLike.re : ℂ → ℝ)
        (adjoint_inner_right
          (HilbertAugmentation.column M β c)
          ((ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) y) y)
      simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] at h
      simpa only [RCLike.re_to_complex] using h

/-- Every nonzero eigenvalue of the full Hermitian augmentation has modulus
at least the lower singular bound of the principal block.  The two sectors of
a nonzero-eigenvalue eigenvector have equal norm; this follows directly from
the rectangular adjoint identity and does not invoke a spectral theorem. -/
theorem hamiltonian_nonzero_eigenvalue_gap
    (M : V ≃L[ℂ] V) (β : V) (c : ℂ) (δ : ℝ)
    (hδ : 0 < δ)
    (hInv : ‖M.symm.toContinuousLinearMap‖ ≤ 1 / δ)
    (x : HilbertAugmentation.FullSpace V) (eigenvalue : ℂ)
    (hx : x ≠ 0) (hEigenvalue : eigenvalue ≠ 0)
    (hEig : HilbertAugmentation.hamiltonian M β c x = eigenvalue • x) :
    δ ≤ ‖eigenvalue‖ := by
  have hEig' := hEig
  rw [HilbertAugmentation.hamiltonian_apply] at hEig'
  have hC := congrArg
    (fun w : HilbertAugmentation.FullSpace V => w.fst) hEig'
  have hCadj := congrArg
    (fun w : HilbertAugmentation.FullSpace V => w.snd) hEig'
  change HilbertAugmentation.column M β c x.snd = eigenvalue • x.fst at hC
  change (ContinuousLinearMap.adjoint (HilbertAugmentation.column M β c)) x.fst = eigenvalue • x.snd at hCadj
  have hLeft : x.fst ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hCadj
    have hRight : x.snd = 0 :=
      (smul_eq_zero.mp hCadj.symm).resolve_left hEigenvalue
    apply hx
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hzero
    · exact hRight
  have hInner := adjoint_inner_right
    (HilbertAugmentation.column M β c) x.snd x.fst
  rw [hCadj, hC] at hInner
  have hNorm := congrArg norm hInner
  simp only [inner_smul_left, inner_smul_right,
    inner_self_eq_norm_sq_to_K, norm_mul, Complex.norm_conj, norm_pow,
    RCLike.norm_ofReal, abs_norm] at hNorm
  have hEigenvaluePos : 0 < ‖eigenvalue‖ := norm_pos_iff.mpr hEigenvalue
  have hSector : ‖x.snd‖ = ‖x.fst‖ := by
    have hsq : ‖x.snd‖ ^ 2 = ‖x.fst‖ ^ 2 :=
      mul_left_cancel₀ (ne_of_gt hEigenvaluePos) hNorm
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hLower := column_adjoint_lower M β c δ hδ hInv x.fst
  rw [hCadj, norm_smul, hSector] at hLower
  have hLeftPos : 0 < ‖x.fst‖ := norm_pos_iff.mpr hLeft
  apply (mul_le_mul_iff_right₀ hLeftPos).mp
  simpa only [mul_comm] using hLower

section FiniteDimensional

variable [FiniteDimensional ℂ V]

/-- Specialization to the actual regularized dilation: the dense augmented
column adjoint retains the manuscript gap `g_sigma`. -/
theorem regularized_column_adjoint_lower
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ)
    (y : HilbertRegularization.Double (HilbertRegularization.Double V)) :
    RegularizationGap.gap κ σ * ‖y‖ ≤
      ‖(ContinuousLinearMap.adjoint (HilbertAugmentation.column
        (InputInverseBounds.regularizedDilationEquiv
          A κ σ hκ hInv hσ₀ hσ₁) β c)) y‖ := by
  apply column_adjoint_lower
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c (RegularizationGap.gap κ σ)
    (RegularizationGap.gap_pos κ σ hκ hσ₀ hσ₁)
  exact InputInverseBounds.regularizedDilationEquiv_inverse_norm_le
    A κ σ hκ hInv hσ₀ hσ₁

/-- Concrete Gram inequality `C C† >= g_sigma² I` for the manuscript's
regularized augmented row. -/
theorem regularized_column_gram_rayleigh_lower
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ)
    (y : HilbertRegularization.Double (HilbertRegularization.Double V)) :
    RegularizationGap.gap κ σ ^ 2 * ‖y‖ ^ 2 ≤
      (inner ℂ
        (HilbertAugmentation.column
          (InputInverseBounds.regularizedDilationEquiv
            A κ σ hκ hInv hσ₀ hσ₁) β c
          ((ContinuousLinearMap.adjoint (HilbertAugmentation.column
            (InputInverseBounds.regularizedDilationEquiv
              A κ σ hκ hInv hσ₀ hσ₁) β c)) y)) y).re := by
  apply column_gram_rayleigh_lower
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c (RegularizationGap.gap κ σ)
    (RegularizationGap.gap_pos κ σ hκ hσ₀ hσ₁)
  exact InputInverseBounds.regularizedDilationEquiv_inverse_norm_le
    A κ σ hκ hInv hσ₀ hσ₁

/-- The actual augmented Hamiltonian for the regularized sparse linear system. -/
def regularizedAugmentedHamiltonian
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ) :
    HilbertAugmentation.FullSpace
      (HilbertRegularization.Double (HilbertRegularization.Double V)) →L[ℂ]
    HilbertAugmentation.FullSpace
      (HilbertRegularization.Double (HilbertRegularization.Double V)) :=
  HilbertAugmentation.hamiltonian
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c

/-- The specialized augmentation is genuinely self-adjoint. -/
theorem regularizedAugmentedHamiltonian_selfadjoint
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ) :
    (ContinuousLinearMap.adjoint (regularizedAugmentedHamiltonian
      A κ σ hκ hInv hσ₀ hσ₁ β c)) =
      regularizedAugmentedHamiltonian
        A κ σ hκ hInv hσ₀ hσ₁ β c :=
  HilbertAugmentation.hamiltonian_selfadjoint
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c

/-- The full specialized Hermitian augmentation has nonzero eigenvalue gap
at least `g_sigma`, exactly as used in the walk construction. -/
theorem regularizedAugmentedHamiltonian_nonzero_eigenvalue_gap
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ)
    (x : HilbertAugmentation.FullSpace
      (HilbertRegularization.Double (HilbertRegularization.Double V)))
    (eigenvalue : ℂ) (hx : x ≠ 0) (hEigenvalue : eigenvalue ≠ 0)
    (hEig : regularizedAugmentedHamiltonian
      A κ σ hκ hInv hσ₀ hσ₁ β c x = eigenvalue • x) :
    RegularizationGap.gap κ σ ≤ ‖eigenvalue‖ := by
  apply hamiltonian_nonzero_eigenvalue_gap
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c (RegularizationGap.gap κ σ)
    (RegularizationGap.gap_pos κ σ hκ hσ₀ hσ₁)
    (InputInverseBounds.regularizedDilationEquiv_inverse_norm_le
      A κ σ hκ hInv hσ₀ hσ₁) x eigenvalue hx hEigenvalue
  exact hEig

/-- Its normalized intended state is in the exact kernel. -/
theorem regularizedAugmentedHamiltonian_normalizedGenerator
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ) :
    regularizedAugmentedHamiltonian A κ σ hκ hInv hσ₀ hσ₁ β c
      (HilbertAugmentation.normalizedGenerator
        (InputInverseBounds.regularizedDilationEquiv
          A κ σ hκ hInv hσ₀ hσ₁) β c) = 0 :=
  HilbertAugmentation.hamiltonian_normalizedGenerator
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c

/-- The full kernel remains exactly one scalar line after specializing the
principal block to the input matrix and regularization. -/
theorem regularizedAugmentedHamiltonian_kernel_unique
    (A : V ≃L[ℂ] V) (κ σ : ℝ)
    (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : HilbertRegularization.Double (HilbertRegularization.Double V))
    (c : ℂ)
    (x : HilbertAugmentation.FullSpace
      (HilbertRegularization.Double (HilbertRegularization.Double V))) :
    regularizedAugmentedHamiltonian A κ σ hκ hInv hσ₀ hσ₁ β c x = 0 ↔
      ∃! z : ℂ,
        HilbertAugmentation.parameter
          (InputInverseBounds.regularizedDilationEquiv
            A κ σ hκ hInv hσ₀ hσ₁) β c z = x :=
  HilbertAugmentation.kernel_unique_parameter
    (InputInverseBounds.regularizedDilationEquiv
      A κ σ hκ hInv hσ₀ hσ₁) β c x

end FiniteDimensional
end
end SparseLinearSystems.HilbertAugmentationGap
