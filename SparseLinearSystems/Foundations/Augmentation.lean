import SparseLinearSystems.Foundations.Regularization

/-!
# The augmented row and its kernel: algebra

For an invertible `M` and a vector `β`, the augmented row `[M, -c β]` on
`V × ℂ` is surjective, and its kernel is the line through `(c M⁻¹ β, 1)`
(`ker_eq_span`, `kernelEquiv`).  The scalar `c` is the reciprocal norm guess;
the kernel calculation needs only invertibility of `M`.  The Hilbert-space
version is `Foundations.HilbertAugmentation`.
-/

namespace SparseLinearSystems.Augmentation

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The augmented row operator `[M, -c β]`. -/
def column (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) : V × ℂ →ₗ[ℂ] V where
  toFun p := M p.1 - p.2 • (c • β)
  map_add' p q := by
    change M (p.1 + q.1) - (p.2 + q.2) • (c • β) =
      (M p.1 - p.2 • (c • β)) + (M q.1 - q.2 • (c • β))
    rw [map_add, add_smul]
    abel
  map_smul' a p := by
    change M (a • p.1) - (a * p.2) • (c • β) =
      a • (M p.1 - p.2 • (c • β))
    rw [map_smul, smul_sub, mul_smul]

theorem column_apply (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) (p : V × ℂ) :
    column M β c p = M p.1 - p.2 • (c • β) := rfl

/-- The added column preserves surjectivity of the invertible principal block. -/
theorem column_surjective (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    Function.Surjective (column M β c) := by
  intro y
  refine ⟨(M.symm y, 0), ?_⟩
  change M (M.symm y) - (0 : ℂ) • (c • β) = y
  rw [M.apply_symm_apply, zero_smul, sub_zero]

/-- The augmented null vector with appended coordinate exactly one. -/
def generator (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) : V × ℂ :=
  (c • M.symm β, 1)

/-- Parameterization of the full kernel by its appended coordinate. -/
def parameter (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) : ℂ →ₗ[ℂ] V × ℂ where
  toFun z := (z • (c • M.symm β), z)
  map_add' z w := by
    apply Prod.ext
    · exact add_smul z w (c • M.symm β)
    · rfl
  map_smul' a z := by
    apply Prod.ext
    · exact mul_smul a z (c • M.symm β)
    · rfl

theorem parameter_apply (M : V ≃ₗ[ℂ] V) (β : V) (c z : ℂ) :
    parameter M β c z = (z • (c • M.symm β), z) := rfl

theorem parameter_eq_smul_generator (M : V ≃ₗ[ℂ] V) (β : V) (c z : ℂ) :
    parameter M β c z = z • generator M β c := by
  apply Prod.ext
  · rfl
  · change z = z * 1
    exact (mul_one z).symm

theorem generator_ne_zero (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    generator M β c ≠ 0 := by
  intro h
  have h' : (1 : ℂ) = 0 := congrArg Prod.snd h
  exact one_ne_zero h'

/-- The augmented equation is equivalent to an explicit solution coordinate. -/
theorem column_eq_zero_iff (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) (p : V × ℂ) :
    column M β c p = 0 ↔ p.1 = p.2 • (c • M.symm β) := by
  change M p.1 - p.2 • (c • β) = 0 ↔ _
  constructor
  · intro h
    have hM : M p.1 = p.2 • (c • β) := sub_eq_zero.mp h
    calc
      p.1 = M.symm (M p.1) := (M.symm_apply_apply p.1).symm
      _ = M.symm (p.2 • (c • β)) := congrArg M.symm hM
      _ = p.2 • (c • M.symm β) := by rw [map_smul, map_smul]
  · intro h
    rw [h, map_smul, map_smul, M.apply_symm_apply, sub_self]

theorem column_parameter (M : V ≃ₗ[ℂ] V) (β : V) (c z : ℂ) :
    column M β c (parameter M β c z) = 0 :=
  (column_eq_zero_iff M β c (parameter M β c z)).mpr rfl

theorem column_generator (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    column M β c (generator M β c) = 0 := by
  apply (column_eq_zero_iff M β c (generator M β c)).mpr
  change c • M.symm β = (1 : ℂ) • (c • M.symm β)
  exact (one_smul ℂ (c • M.symm β)).symm

theorem parameter_injective (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    Function.Injective (parameter M β c) := by
  intro z w h
  exact congrArg Prod.snd h

/-- Every augmented null vector is determined by its appended coordinate. -/
theorem kernel_parameterization (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ)
    (p : V × ℂ) :
    column M β c p = 0 ↔ p = parameter M β c p.2 := by
  constructor
  · intro h
    apply Prod.ext
    · exact (column_eq_zero_iff M β c p).mp h
    · rfl
  · intro h
    rw [h]
    exact column_parameter M β c p.2

theorem kernel_unique_parameter (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ)
    (p : V × ℂ) :
    column M β c p = 0 ↔ ∃! z : ℂ, parameter M β c z = p := by
  constructor
  · intro h
    have hp := (kernel_parameterization M β c p).mp h
    refine ⟨p.2, hp.symm, ?_⟩
    intro z hz
    exact parameter_injective M β c (hz.trans hp)
  · rintro ⟨z, hz, _⟩
    rw [← hz]
    exact column_parameter M β c z

/-- An equality of submodules, not merely containment of the proposed vector. -/
theorem ker_eq_range (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    LinearMap.ker (column M β c) = LinearMap.range (parameter M β c) := by
  ext p
  change column M β c p = 0 ↔ ∃ z, parameter M β c z = p
  constructor
  · intro h
    exact ⟨p.2, ((kernel_parameterization M β c p).mp h).symm⟩
  · rintro ⟨z, rfl⟩
    exact column_parameter M β c z

/-- The augmented operator has exactly the one-dimensional kernel used in the
linear-system algorithm.  The generator is nonzero even if β vanishes. -/
theorem ker_eq_span (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    LinearMap.ker (column M β c) = Submodule.span ℂ {generator M β c} := by
  apply le_antisymm
  · intro p hp
    have hp' := (kernel_parameterization M β c p).mp hp
    rw [hp', parameter_eq_smul_generator]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro p hp
    have hp' : p = generator M β c := Set.mem_singleton_iff.mp hp
    rw [hp']
    exact column_generator M β c

/-- A concrete linear equivalence exhibits the kernel as one copy of ℂ. -/
def kernelEquiv (M : V ≃ₗ[ℂ] V) (β : V) (c : ℂ) :
    ℂ ≃ₗ[ℂ] LinearMap.ker (column M β c) where
  toFun z := ⟨parameter M β c z, column_parameter M β c z⟩
  invFun p := p.val.2
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact ((kernel_parameterization M β c p.val).mp p.property).symm
  map_add' z w := by
    apply Subtype.ext
    exact map_add (parameter M β c) z w
  map_smul' a z := by
    apply Subtype.ext
    exact map_smul (parameter M β c) a z

theorem kernelEquiv_apply (M : V ≃ₗ[ℂ] V) (β : V) (c z : ℂ) :
    (kernelEquiv M β c z).val = parameter M β c z := rfl

/-- The paper's operator `C_{σ,r}`, with the already invertible regularized
matrix supplied as M.  No norm or phase-gap claim is assumed here. -/
def withNormGuess (M : V ≃ₗ[ℂ] V) (β : V) (r : ℝ) : V × ℂ →ₗ[ℂ] V :=
  column M β ((r : ℂ)⁻¹)

theorem withNormGuess_apply (M : V ≃ₗ[ℂ] V) (β : V) (r : ℝ)
    (p : V × ℂ) :
    withNormGuess M β r p = M p.1 - (p.2 / (r : ℂ)) • β := by
  simp only [withNormGuess, column_apply, div_eq_mul_inv, mul_smul]

theorem withNormGuess_eq_zero_iff (M : V ≃ₗ[ℂ] V) (β : V) (r : ℝ)
    (p : V × ℂ) :
    withNormGuess M β r p = 0 ↔ p.1 = (p.2 / (r : ℂ)) • M.symm β := by
  simp only [withNormGuess, column_eq_zero_iff, div_eq_mul_inv, mul_smul]

end
end SparseLinearSystems.Augmentation
