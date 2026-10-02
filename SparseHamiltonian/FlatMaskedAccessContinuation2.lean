import SparseHamiltonian.SingletonPrivateEncoding

namespace SparseHamiltonian.FlatMaskedAccess

noncomputable section
open ContinuousLinearMap

variable {V B : Type*} [Fintype B]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The singleton private adapter for the native active-clock interface. -/
abbrev singleton (e : V →ₗᵢ[ℂ] EuclideanSpace ℂ B) :
    V →ₗᵢ[ℂ] NativeMaskedOracle.Logical PUnit.{1} B :=
  SingletonPrivateEncoding.embedding e

variable [CompleteSpace V]

omit [CompleteSpace V] in
theorem singleton_intertwines (U : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (D : V →L[ℂ] V) (e : V →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (h : U ∘L e.toContinuousLinearMap = e.toContinuousLinearMap ∘L D) :
    WeightedClock.diagonal (fun _ : PUnit.{1} => U) ∘L (singleton e).toContinuousLinearMap =
      (singleton e).toContinuousLinearMap ∘L D :=
  SingletonPrivateEncoding.intertwines e U D h

end
end SparseHamiltonian.FlatMaskedAccess
