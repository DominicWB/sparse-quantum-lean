import SparseHamiltonian.GlobalResolventContinuation3

/-!
# The exit identity for the actual chronological clock transducer

Local energy conservation and stationary transduction imply the finite
chronological exit identity.  The concrete Cayley-clock specialization derives
the required public coisometry from the clock promises rather than assuming it.
-/

namespace SparseHamiltonian.GlobalExit

noncomputable section

open ContinuousLinearMap
open ChronologicalResolvent ChronologicalCatalyst GlobalColligation
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The finite chronological exit identity follows from local conservation and
stationarity. Its Gram identities and global transduction equations are all
derived from the actual chronological blocks. -/
theorem chronological_exit_block_eq
    (D : V →L[ℂ] V) (A Γ : P →L[ℂ] V) (U u : P →L[ℂ] P) (B : V →L[ℂ] P)
    (hStep : ∀ x p, ‖D x + A p‖ ^ 2 + ‖u p + B x‖ ^ 2 = ‖x‖ ^ 2 + ‖p‖ ^ 2)
    (hPrivate : A + D ∘L Γ = Γ) (hPublic : u + B ∘L Γ = U)
    (hCoiso : U ∘L U† = 1) (T : ℕ) :
    publicExit u B T = (U ^ T) ∘L ((stackedResponse Γ U T)† ∘L
      (1 - chronologicalOperator D A u B T)) := by
  have hEnergy := chronological_full_energy D A u B hStep T
  have hMixed := block_gram_mixed _ _ _ _ hEnergy
  have hPrivateGram := block_gram_private _ _ _ _ hEnergy
  have hGlobalPrivate := catalyst_private_transduction D A Γ U u B hPrivate hPublic T
  have hGlobalPublic := catalyst_public_transduction Γ U u B hPublic T
  have hGlobalCoiso : (U ^ T) ∘L (U ^ T)† = 1 :=
    CayleyTransfer.coisometry_pow U hCoiso T
  exact ExitIdentity.exit_block_eq (u ^ T) (U ^ T) (publicExit u B T)
    (stackedResponse A u T) (stackedResponse Γ U T) (chronologicalOperator D A u B T)
    hMixed hPrivateGram hGlobalPublic hGlobalPrivate hGlobalCoiso

/-- For the concrete Cayley coefficients, all conservation and coisometry
premises of the chronological exit identity follow from the clock promises.
The stationary catalyst may be the explicitly constructed clock catalyst. -/
theorem clock_exit_block_eq (D R1 : V →L[ℂ] V) (J Γ : P →L[ℂ] V)
    (H U : P →L[ℂ] P) (w : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hPrivate : (CayleyTransfer.sigma w : ℂ) • J +
      GlobalResolvent.localPrivateBlock D J (CayleyTransfer.kappa w) ∘L Γ = Γ)
    (hPublic : (CayleyTransfer.c w : ℂ) • 1 +
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) ∘L Γ = U) (T : ℕ) :
    publicExit ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T =
    (U ^ T) ∘L ((stackedResponse Γ U T)† ∘L
      (1 - GlobalResolvent.globalPrivateBlock D J (CayleyTransfer.c w)
        (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T)) := by
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ :=
    CayleyTransfer.scalar_promises w hw hwQuarter
  have hCoiso := (GlobalResolvent.local_public_unitary D R1 J Γ H U w hw hwQuarter
    hRight hLeft hJ hBoundary hSelf hH hPrivate hPublic).2
  exact chronological_exit_block_eq
    (GlobalResolvent.localPrivateBlock D J (CayleyTransfer.kappa w))
    ((CayleyTransfer.sigma w : ℂ) • J) Γ U ((CayleyTransfer.c w : ℂ) • 1)
    ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D))
    (LocalRotation.local_step_energy D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) hκc hσc hD hJ) hPrivate hPublic hCoiso T

end
end SparseHamiltonian.GlobalExit
