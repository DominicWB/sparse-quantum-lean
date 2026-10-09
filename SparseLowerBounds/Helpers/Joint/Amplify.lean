import SparseLowerBounds.Query.PhaseOracle

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Amplification of matrix norm bounds to Hilbert-space valued vectors

Helper for `SparseLowerBounds.Query.Joint`. For a matrix `A` on `ℂ^ι` with the
`L²` operator norm and any family `v : ι → K` of vectors in a complex inner
product space,

  `Σ_i ‖Σ_{i'} A i i' • v i'‖² ≤ ‖A‖² Σ_i ‖v i‖²`,

i.e. `‖A ⊗ 1_K‖ ≤ ‖A‖`. The proof expands the `v i` in an orthonormal basis of
their (finite-dimensional) span and applies the matrix bound to each
coordinate vector. A second lemma does the same for a matrix acting on one
register `k` of `Fin n → Fin m`, by summing over the involution
`(j, b) ↦ (update j k b, j k)`.
-/

namespace SparseLowerBounds.Helpers.Joint

noncomputable section
open scoped InnerProductSpace Matrix Matrix.Norms.L2Operator

/-- `‖A ⊗ 1_K‖ ≤ ‖A‖`, in squared form, for vectors in any inner product space. -/
theorem sum_norm_sq_mulVec_le {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] (A : Matrix ι ι ℂ) (v : ι → K) :
    ∑ i, ‖∑ i', A i i' • v i'‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
  classical
  set V : Submodule ℂ K := Submodule.span ℂ (Set.range v) with hV
  haveI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  let b := stdOrthonormalBasis ℂ V
  let c : Fin (Module.finrank ℂ V) → ι → ℂ := fun r i => ⟪(b r : K), v i⟫_ℂ
  have hmem : ∀ i, v i ∈ V := fun i => Submodule.subset_span ⟨i, rfl⟩
  have parseval : ∀ x ∈ V, ‖x‖ ^ 2 = ∑ r, ‖⟪(b r : K), x⟫_ℂ‖ ^ 2 := by
    intro x hx
    have h := b.sum_sq_norm_inner_right ⟨x, hx⟩
    simpa [Submodule.coe_inner] using h.symm
  have hAv : ∀ i, ∑ i', A i i' • v i' ∈ V := fun i =>
    Submodule.sum_mem _ fun i' _ => Submodule.smul_mem _ _ (hmem i')
  have hinner : ∀ r i, ⟪(b r : K), ∑ i', A i i' • v i'⟫_ℂ = (A *ᵥ c r) i := by
    intro r i
    simp [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct, c]
  have hEuc : ∀ x : ι → ℂ, ‖(EuclideanSpace.equiv ι ℂ).symm x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  calc ∑ i, ‖∑ i', A i i' • v i'‖ ^ 2
      = ∑ i, ∑ r, ‖(A *ᵥ c r) i‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [parseval _ (hAv i)]
        simp_rw [hinner]
    _ = ∑ r, ‖(EuclideanSpace.equiv ι ℂ).symm (A *ᵥ c r)‖ ^ 2 := by
        rw [Finset.sum_comm]
        simp_rw [hEuc]
    _ ≤ ∑ r, (‖A‖ * ‖(EuclideanSpace.equiv ι ℂ).symm (c r)‖) ^ 2 := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _)
          (A.l2_opNorm_mulVec ((EuclideanSpace.equiv ι ℂ).symm (c r))) 2
    _ = ‖A‖ ^ 2 * ∑ i, ‖v i‖ ^ 2 := by
        simp_rw [mul_pow, ← Finset.mul_sum, hEuc]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [parseval _ (hmem i)]

/-- The involution `(j, b) ↦ (update j k b, j k)` of `(Fin n → Fin m) × Fin m`. -/
def swapReg {n m : ℕ} (k : Fin n) : (Fin n → Fin m) × Fin m ≃ (Fin n → Fin m) × Fin m :=
  Function.Involutive.toPerm (fun p => (Function.update p.1 k p.2, p.1 k)) (by
    rintro ⟨j, b⟩
    simp)

/-- Reindexing a double sum along `swapReg`. -/
theorem sum_swapReg {n m : ℕ} {M : Type*} [AddCommMonoid M] (k : Fin n)
    (f : (Fin n → Fin m) → Fin m → M) :
    ∑ j, ∑ b, f (Function.update j k b) (j k) = ∑ j, ∑ b, f j b := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  exact Equiv.sum_comp (swapReg k) (fun p => f p.1 p.2)

/-- `‖A ⊗ 1‖ ≤ ‖A‖` for a matrix acting on register `k`, in squared form. -/
theorem sum_norm_sq_onReg_le {n m : ℕ} {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (k : Fin n) (A : Matrix (Fin m) (Fin m) ℂ)
    (Ψ : (Fin n → Fin m) → K) :
    ∑ j, ‖∑ b, A (j k) b • Ψ (Function.update j k b)‖ ^ 2 ≤ ‖A‖ ^ 2 * ∑ j, ‖Ψ j‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    haveI : IsEmpty (Fin n → Fin 0) := ⟨fun j => (j k).elim0⟩
    simp
  have h1 : (m : ℝ) * ∑ j, ‖∑ b, A (j k) b • Ψ (Function.update j k b)‖ ^ 2 =
      ∑ j, ∑ a, ‖∑ b, A a b • Ψ (Function.update j k b)‖ ^ 2 := by
    rw [← sum_swapReg k (fun j a => ‖∑ b, A a b • Ψ (Function.update j k b)‖ ^ 2)]
    simp [Finset.mul_sum]
  have h2 : (m : ℝ) * ∑ j, ‖Ψ j‖ ^ 2 = ∑ j, ∑ a, ‖Ψ (Function.update j k a)‖ ^ 2 := by
    rw [sum_swapReg k (fun j _ => ‖Ψ j‖ ^ 2)]
    simp [Finset.mul_sum]
  have key : (m : ℝ) * ∑ j, ‖∑ b, A (j k) b • Ψ (Function.update j k b)‖ ^ 2 ≤
      (m : ℝ) * (‖A‖ ^ 2 * ∑ j, ‖Ψ j‖ ^ 2) := by
    rw [h1, mul_left_comm, h2, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ =>
      sum_norm_sq_mulVec_le A (fun b => Ψ (Function.update j k b))
  exact le_of_mul_le_mul_left key (by exact_mod_cast hm)

end

end SparseLowerBounds.Helpers.Joint
end
