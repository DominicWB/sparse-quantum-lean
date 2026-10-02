import SparseODE.ODENativeCircuitShape

/-!
Generic direct-sum identities used to avoid unfolding concrete native
circuits during elaboration of componentwise congruence proofs.
-/

namespace SparseHamiltonian.CoherentQuerySchedule

noncomputable section
open ContinuousLinearMap

variable {ι P K : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Fintype ι] [CompleteSpace K] in
/-- Branchwise intertwining lifts to a coherent direct sum. The proof uses
only abstract maps, so application does not unfold the native circuit. -/
theorem diagonal_rectangular_intertwines
    (A : ι → K →L[ℂ] K) (E : ι → P →L[ℂ] K) (B : ι → P →L[ℂ] P)
    (h : ∀ i, A i ∘L E i = E i ∘L B i) :
    WeightedClock.diagonal A ∘L rectangular E =
      rectangular E ∘L WeightedClock.diagonal B := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change A i (E i (v i)) = E i (B i (v i))
  exact congrArg (fun F : P →L[ℂ] K => F (v i)) (h i)

omit [CompleteSpace K] in
/-- Scalar multiplication distributes over a finite diagonal family. -/
theorem smul_diagonal (c : ℂ) (A : ι → K →L[ℂ] K) :
    c • WeightedClock.diagonal A = WeightedClock.diagonal (fun i => c • A i) := by
  ext v i
  rfl

end
end SparseHamiltonian.CoherentQuerySchedule
