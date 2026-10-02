import SparseHamiltonian.WeightedLookupSimulation

/-!
# A fixed clean value register with an arbitrary Hilbert payload

The clean value is a fixed basis label, not an input-dependent state.  This
isometry retains the complete payload and gives an explicit encoding on which
compute/use/uncompute circuits can be certified.
-/

namespace SparseHamiltonian.CleanValueEmbedding

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {I Z K : Type*} [Fintype I] [Fintype Z] [DecidableEq Z]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- Append a value register in a fixed computational basis state. -/
def embedding (z0 : Z) :
    PiLp 2 (fun _ : I => K) →ₗᵢ[ℂ] PiLp 2 (fun _ : I × Z => K) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun w => if w.2 = z0 then v w.1 else 0)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro i
        by_cases hi : i.2 = z0 <;> simp [hi]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro i
        by_cases hi : i.2 = z0 <;> simp [hi] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    classical
    simp [Fintype.sum_prod_type, apply_ite]

@[simp] theorem embedding_apply (z0 : Z) (v : PiLp 2 (fun _ : I => K))
    (i : I) (z : Z) :
    embedding z0 v (i, z) = if z = z0 then v i else 0 := rfl

/-- The clean encoding preserves the full Hilbert-space norm. -/
theorem embedding_adjoint_comp [CompleteSpace K] (z0 : Z) :
    (embedding (I := I) (K := K) z0).toContinuousLinearMap† ∘L
      (embedding (I := I) (K := K) z0).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

end
end SparseHamiltonian.CleanValueEmbedding
