import SparseLinearSystems.Augmented.Probability

/-!
# Kernel, seed probability and extracted solution of the augmented walk

Specialisation of `Augmented.Probability` to `H_{σ,r}`.  With
`q = r_σ / r`, `r_σ = ‖M_σ⁻¹ β‖` and `a = ‖K J u‖²` for the kernel vector `u`
with appended coordinate one:

* `probability_eq`: `p_σ(r) = 1/(1 + q² + a)`, with `0 ≤ a ≤ μ (1 + q²)`,
  hence equation `qls:eq:probability`;
* `solution_amplitude`: at `σ = 0`, the selected solution coordinates of
  `J† P J e` equal `(1/(1 + q² + a)) r⁻¹ A⁻¹ b`, a positive multiple of the
  normalised solution (equation `qls:eq:finalprob`).
-/

namespace SparseLinearSystems.Augmented

noncomputable section
open ContinuousLinearMap HilbertBlocks HilbertRegularization HilbertAugmentation
open scoped InnerProduct ComplexConjugate

variable {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [FiniteDimensional ℂ V₀] [CompleteSpace V₀]

/-- The regularized principal block `M_σ`. -/
abbrev Mσ (A : V₀ ≃L[ℂ] V₀) (κ σ : ℝ) (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)
    (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) : Sys V₀ ≃L[ℂ] Sys V₀ :=
  InputInverseBounds.regularizedDilationEquiv A κ σ hκ hInv hσ₀ hσ₁

/-- `r_σ = ‖M_σ⁻¹ β‖`. -/
def rSigma (A : V₀ ≃L[ℂ] V₀) (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (β : Sys V₀) : ℝ :=
  ‖(Mσ A κ σ hκ hInv hσ₀ hσ₁).symm β‖

theorem Mσ_coe (A : V₀ ≃L[ℂ] V₀) (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) :
    ((Mσ A κ σ hκ hInv hσ₀ hσ₁ : Sys V₀ ≃L[ℂ] Sys V₀) : Sys V₀ →L[ℂ] Sys V₀) =
      regularized (dilation A.toContinuousLinearMap) σ := by
  ext y; rfl

/-- The augmented Hamiltonian equals the three-branch form. -/
theorem hamiltonian_eq_branches (A : V₀ ≃L[ℂ] V₀) (κ σ : ℝ) (hκ : 1 ≤ κ)
    (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (β : Sys V₀) (c : ℝ) :
    hamiltonian (Mσ A κ σ hκ hInv hσ₀ hσ₁) β (c : ℂ) =
      ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 A.toContinuousLinearMap + (σ : ℂ) • T1 +
        (c : ℂ) • T2 β :=
  hamiltonian_decomp _ _ σ (Mσ_coe A κ σ hκ hInv hσ₀ hσ₁) β c

omit [FiniteDimensional ℂ V₀] in
/-- The kernel line of `H_{σ,r}`. -/
theorem hamiltonian_kernel (M : Sys V₀ ≃L[ℂ] Sys V₀) (β : Sys V₀) (c : ℂ) (u : Pub V₀)
    (hu : hamiltonian M β c u = 0) : ∃ z : ℂ, u = z • generator M β c := by
  obtain ⟨z, hz, _⟩ := (kernel_unique_parameter M β c u).mp hu
  exact ⟨z, by rw [← hz, parameter_eq_smul_generator]⟩

omit [FiniteDimensional ℂ V₀] [CompleteSpace V₀] in
theorem inner_generator_eVec (M : Sys V₀ ≃L[ℂ] Sys V₀) (β : Sys V₀) (c : ℂ) :
    inner ℂ (generator M β c) (eVec : Pub V₀) = 1 := by
  rw [inner_pub]
  simp [generator, eVec]

omit [FiniteDimensional ℂ V₀] [CompleteSpace V₀] in
theorem generator_norm_sq_real (M : Sys V₀ ≃L[ℂ] Sys V₀) (β : Sys V₀) (c : ℝ) :
    ‖generator M β (c : ℂ)‖ ^ 2 = (c * ‖M.symm β‖) ^ 2 + 1 := by
  rw [generator_norm_sq, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]

/-- At `σ = 0`, `M₀⁻¹ β = |0⟩_reg |1⟩_dil A⁻¹ b` (equation `qls:eq:qrange`). -/
theorem M0_symm_beta (A : V₀ ≃L[ℂ] V₀) (κ : ℝ) (hκ : 1 ≤ κ)
    (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ) (b : V₀) :
    (Mσ A κ 0 hκ hInv le_rfl zero_le_one).symm (betaOf b) =
      WithLp.toLp 2 (WithLp.toLp 2 (0, A.symm b), 0) := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  change betaOf b = regularized (dilation A.toContinuousLinearMap) 0
    (WithLp.toLp 2 (WithLp.toLp 2 (0, A.symm b), 0))
  simp [regularized, weighted_apply, dilation_apply, betaOf]

theorem rSigma_zero (A : V₀ ≃L[ℂ] V₀) (κ : ℝ) (hκ : 1 ≤ κ)
    (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ) (b : V₀) :
    rSigma A κ 0 hκ hInv le_rfl zero_le_one (betaOf b) = ‖A.symm b‖ := by
  rw [rSigma, M0_symm_beta]
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp

end

end SparseLinearSystems.Augmented
