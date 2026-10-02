import SparseHamiltonian.ClockCatalyst

/-!
# Identifying the constructed transducer's public action

The stationary private response is unique, so every catalyst satisfying the
constructed clock transduction equations induces exactly the Cayley transform
of the compressed Hamiltonian.
-/

namespace SparseHamiltonian.GlobalResolvent

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Eliminating any stationary catalyst gives the same boundary transfer. -/
theorem local_public_eq_transfer (D R1 : V →L[ℂ] V) (J Γ : P →L[ℂ] V)
    (U K : P →L[ℂ] P) (c κ σ : ℝ)
    (hLeft : R1 ∘L (1 - D) = 1)
    (hK : K ∘L (1 + (κ : ℂ) • ((J† ∘L D) ∘L R1 ∘L J)) = 1)
    (hPrivate : (σ : ℂ) • J + localPrivateBlock D J κ ∘L Γ = Γ)
    (hPublic : (c : ℂ) • 1 + ((-(σ : ℂ)) • (J† ∘L D)) ∘L Γ = U) :
    U = BoundaryTransfer.transfer (c : ℂ) (σ ^ 2) ((J† ∘L D) ∘L R1 ∘L J) K := by
  let S := woodburyInverse R1 J K (J† ∘L D) (κ : ℂ)
  have hS : S ∘L (1 - localPrivateBlock D J κ) = 1 := by
    have h := woodbury_left_inverse (1 - D) R1 J K (J† ∘L D) (κ : ℂ) hLeft hK
    have hDen := localPrivateBlock_denominator D J κ (1 : ℂ)
    simp only [one_smul] at hDen
    rw [hDen]
    exact h
  rw [CatalystConstruction.publicAction_eq_of_transduction
    (localPrivateBlock D J κ) S ((σ : ℂ) • J) Γ ((c : ℂ) • 1) U
    ((-(σ : ℂ)) • (J† ∘L D)) hS hPrivate hPublic]
  simpa only [CatalystConstruction.publicAction, CatalystConstruction.catalyst,
    S, comp_assoc] using
    woodbury_chronological_transfer R1 J K (J† ∘L D) (κ : ℂ) c σ hK

/-- With the concrete rotation coefficients, the actual public action is the
Cayley transform, whose denominator has a constructed two-sided inverse. -/
theorem local_public_is_cayley (D R1 : V →L[ℂ] V) (J Γ : P →L[ℂ] V)
    (H U : P →L[ℂ] P) (w : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hJ : J† ∘L J = 1)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hPrivate : (CayleyTransfer.sigma w : ℂ) • J +
      localPrivateBlock D J (CayleyTransfer.kappa w) ∘L Γ = Γ)
    (hPublic : (CayleyTransfer.c w : ℂ) • 1 +
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L Γ = U) :
    ∃ R : P →L[ℂ] P,
      CayleyTransfer.cayleyDenominator w H ∘L R = 1 ∧
      R ∘L CayleyTransfer.cayleyDenominator w H = 1 ∧
      U = CayleyTransfer.cayleyNumerator w H ∘L R := by
  obtain ⟨hκ, hκUpper, _hκc, _hσc, _hσw⟩ :=
    CayleyTransfer.scalar_promises w hw hwQuarter
  have hF : (J† ∘L D) ∘L R1 ∘L J = BaseTransfer.halfGenerator H := by
    simpa only [boundaryCompression, BaseTransfer.halfGenerator, comp_assoc] using
      boundaryCompression_at_one D R1 J H hRight hJ hBoundary
  have hFnorm : ‖BaseTransfer.halfGenerator H‖ ≤ 1 := by
    have h := UnitaryResolvent.boundary_generator_norm H hSelf hH
    change ‖BaseTransfer.halfGenerator H‖ ≤ 3 / 4 at h
    linarith
  obtain ⟨K, hKRight, hKLeft, _hKnorm⟩ :=
    exists_public_feedback_inverse (BaseTransfer.halfGenerator H) hκ hκUpper hFnorm
  have hKR : BaseTransfer.denominator (CayleyTransfer.kappa w)
      (BaseTransfer.halfGenerator H) * K = 1 := hKRight
  have hKL : K * BaseTransfer.denominator (CayleyTransfer.kappa w)
      (BaseTransfer.halfGenerator H) = 1 := hKLeft
  refine ⟨CayleyTransfer.cayleyInverse w K,
    CayleyTransfer.cayley_right_inverse w hw H K hKR,
    CayleyTransfer.cayley_left_inverse w hw H K hKL, ?_⟩
  have hK : K ∘L (1 + (CayleyTransfer.kappa w : ℂ) •
      ((J† ∘L D) ∘L R1 ∘L J)) = 1 := by rw [hF]; exact hKLeft
  rw [local_public_eq_transfer D R1 J Γ U K (CayleyTransfer.c w)
    (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) hLeft hK hPrivate hPublic, hF]
  exact CayleyTransfer.transfer_eq_cayley w hw H K hKR

end

end SparseHamiltonian.GlobalResolvent
