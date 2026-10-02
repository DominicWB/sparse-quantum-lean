import SparseHamiltonian.FlatMaskedAccess

namespace SparseHamiltonian.SingletonPrivateEncoding

noncomputable section
open ContinuousLinearMap
open scoped BigOperators

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- A singleton index lets the general active-clock compiler accept any
already constructed clean private embedding, without duplication of data. -/
def embedding (e : V →ₗᵢ[ℂ] W) : V →ₗᵢ[ℂ] PiLp 2 (fun _ : PUnit.{1} => W) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun _ : PUnit.{1} => e v)
      map_add' := by
        intro u v
        apply PiLp.ext
        intro i
        exact e.map_add u v
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro i
        exact e.map_smul z v }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    change (∑ _ : PUnit.{1}, ‖e v‖ ^ 2) = ‖v‖ ^ 2
    simp

variable [CompleteSpace V] [CompleteSpace W]

omit [CompleteSpace V] [CompleteSpace W] in
/-- Passing to a singleton family preserves the exact clean private action. -/
theorem intertwines (e : V →ₗᵢ[ℂ] W) (U : W →L[ℂ] W) (D : V →L[ℂ] V)
    (h : U ∘L e.toContinuousLinearMap = e.toContinuousLinearMap ∘L D) :
    WeightedClock.diagonal (fun _ : PUnit.{1} => U) ∘L (embedding e).toContinuousLinearMap =
      (embedding e).toContinuousLinearMap ∘L D := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change U (e v) = e (D v)
  exact congrArg (fun A : V →L[ℂ] W => A v) h

end
end SparseHamiltonian.SingletonPrivateEncoding
