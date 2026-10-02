import SparseHamiltonian.ChronologicalContraction

namespace SparseHamiltonian.GlobalResolvent

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The actual global private block is contractive. This follows from local
clock and boundary isometries and the rotation relations, independently of
the resolvent promises. -/
theorem globalPrivateBlock_norm_le_one (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (T : ℕ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1) :
    ‖globalPrivateBlock D J c κ σ T‖ ≤ 1 := by
  exact ChronologicalContraction.chronologicalOperator_norm_le_one
    (localPrivateBlock D J κ) ((σ : ℂ) • J) ((c : ℂ) • 1)
    ((-(σ : ℂ)) • (J† ∘L D))
    (LocalRotation.local_step_energy D J c κ σ hκ hσ hD hJ) T

end

end SparseHamiltonian.GlobalResolvent
