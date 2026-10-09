import GateEfficientBinary.Sparse.Lift

/-!
# The qubit lift is norm contractive

For an identification `φ : Cfg V ≃ ι` and an operator `A` on `ℓ²(ι) = EuclideanSpace ℂ ι`, the
qubit lift `qlift φ A` acts on `Reg V R` by the configuration-basis matrix of `A`, tensored with
the identity of the payload Hilbert space `R`. We show `‖qlift φ A‖ ≤ ‖A‖` (`norm_qlift_le`).

The payload `R` may be infinite dimensional, so the estimate is reduced to finitely many payload
coordinates. Fix `ψ : Reg V R`. Its finitely many components `ψ c` span a finite-dimensional
subspace `F` of `R`; choose an orthonormal basis `(e α)` of `F`. The coordinates `⟪e α, ψ c⟫`
define vectors `v α ∈ ℓ²(ι)` with `(v α) (φ c) = ⟪e α, ψ c⟫`. Every component of `qlift φ A ψ`
again lies in `F`, with coordinates `⟪e α, (qlift φ A ψ) b⟫ = (A (v α)) (φ b)`. Parseval's
identity in `F`, applied to the components of `qlift φ A ψ` and of `ψ`, gives
`‖qlift φ A ψ‖² = ∑ α, ‖A (v α)‖² ≤ ‖A‖² ∑ α, ‖v α‖² = ‖A‖² ‖ψ‖²`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBinary

open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative ContinuousLinearMap

noncomputable section

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The qubit lift is norm contractive. -/
theorem norm_qlift_le (φ : Cfg V ≃ ι) (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    ‖qlift (R := R) φ A‖ ≤ ‖A‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (fun ψ => ?_)
  -- The finite-dimensional span of the payload components and an orthonormal basis of it.
  let F : Submodule ℂ R := Submodule.span ℂ (Set.range fun c : Cfg V => ψ c)
  have : FiniteDimensional ℂ F := Module.Finite.span_of_finite ℂ (Set.finite_range _)
  let e := stdOrthonormalBasis ℂ F
  have parseval : ∀ y ∈ F, ‖y‖ ^ 2 = ∑ α, ‖inner ℂ (e α : R) y‖ ^ 2 := by
    intro y hy
    exact (e.sum_sq_norm_inner_right ⟨y, hy⟩).symm
  have hmem : ∀ c, ψ c ∈ F := fun c => Submodule.subset_span ⟨c, rfl⟩
  -- The coordinate vectors `v α ∈ ℓ²(ι)`, with `(v α) (φ c) = ⟪e α, ψ c⟫`.
  let v := fun α => (WithLp.toLp 2 (fun i => inner ℂ (e α : R) (ψ (φ.symm i))) :
    EuclideanSpace ℂ ι)
  have hv : ∀ α, ‖v α‖ ^ 2 = ∑ c, ‖inner ℂ (e α : R) (ψ c)‖ ^ 2 := by
    intro α
    rw [EuclideanSpace.norm_sq_eq]
    exact φ.symm.sum_comp (fun c => ‖inner ℂ (e α : R) (ψ c)‖ ^ 2)
  have hAv : ∀ α b, A (v α) (φ b) = ∑ c, toMat φ A b c * inner ℂ (e α : R) (ψ c) := by
    intro α b
    conv_lhs => rw [euclid_eq_sum (v α)]
    rw [map_sum]
    simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← φ.sum_comp]
    apply Finset.sum_congr rfl
    intro c _
    simp [v, toMat, mul_comm]
  -- Parseval for each output component, whose coordinates are those of the `A (v α)`.
  have hout : ∀ b, ‖qlift (R := R) φ A ψ b‖ ^ 2 = ∑ α, ‖A (v α) (φ b)‖ ^ 2 := by
    intro b
    have hmemb : qlift (R := R) φ A ψ b ∈ F := by
      rw [qlift_eq, matOp_apply]
      exact Submodule.sum_mem _ (fun c _ => Submodule.smul_mem _ _ (hmem c))
    rw [parseval _ hmemb]
    apply Finset.sum_congr rfl
    intro α _
    rw [hAv, qlift_eq, matOp_apply, inner_sum]
    simp only [inner_smul_right]
  have key : ‖qlift (R := R) φ A ψ‖ ^ 2 ≤ (‖A‖ * ‖ψ‖) ^ 2 := by
    calc ‖qlift (R := R) φ A ψ‖ ^ 2 = ∑ b, ‖qlift (R := R) φ A ψ b‖ ^ 2 :=
          PiLp.norm_sq_eq_of_L2 _ _
      _ = ∑ b, ∑ α, ‖A (v α) (φ b)‖ ^ 2 := Finset.sum_congr rfl (fun b _ => hout b)
      _ = ∑ α, ‖A (v α)‖ ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro α _
        rw [EuclideanSpace.norm_sq_eq]
        exact φ.sum_comp (fun i => ‖A (v α) i‖ ^ 2)
      _ ≤ ∑ α, ‖A‖ ^ 2 * ‖v α‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro α _
        rw [← mul_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
      _ = ‖A‖ ^ 2 * ∑ c, ‖ψ c‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [hv]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        exact (parseval _ (hmem c)).symm
      _ = (‖A‖ * ‖ψ‖) ^ 2 := by
        rw [mul_pow, PiLp.norm_sq_eq_of_L2 _ ψ]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp key

end

end SparseHamiltonian.GateBinary
