import SparseHamiltonian.CayleyCoisometry

namespace SparseHamiltonian.GlobalResolvent

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The actual public map of the clock transduction is unitary in both
orientations. This strengthens norm preservation to the coisometry needed by
the exit identity, without requiring finite-dimensional public spaces. -/
theorem local_public_unitary (D R1 : V →L[ℂ] V) (J Γ : P →L[ℂ] V)
    (H U : P →L[ℂ] P) (w : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hJ : J† ∘L J = 1)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hPrivate : (CayleyTransfer.sigma w : ℂ) • J +
      localPrivateBlock D J (CayleyTransfer.kappa w) ∘L Γ = Γ)
    (hPublic : (CayleyTransfer.c w : ℂ) • 1 +
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L Γ = U) :
    U† ∘L U = 1 ∧ U ∘L U† = 1 := by
  obtain ⟨R, hRRight, hRLeft, hU⟩ := local_public_is_cayley D R1 J Γ H U w hw
    hwQuarter hRight hLeft hJ hBoundary hSelf hH hPrivate hPublic
  rw [hU]
  exact CayleyTransfer.cayley_unitary w H R hSelf hRRight hRLeft

end
end SparseHamiltonian.GlobalResolvent
