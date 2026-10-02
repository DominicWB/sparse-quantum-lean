import SparseHamiltonian.GlobalColligation

/-!
# Exit identity for bounded Hilbert-space transducers

The two column Gram identities of an isometric colligation and its stationary
catalyst determine the exit block.  The public action must be a coisometry;
this is an explicit hypothesis, independently discharged for Cayley actions.
-/

namespace SparseHamiltonian.ExitIdentity

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Stationarity and the mixed/private column Gram identities give the exit
identity before multiplication by the public action. -/
theorem adjoint_public_comp_exit
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hMixed : A† ∘L B + C† ∘L D = 0)
    (hPrivateGram : B† ∘L B + D† ∘L D = 1)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ) :
    U† ∘L B = Γ† ∘L (1 - D) := by
  have hCancel : U† ∘L B + Γ† ∘L D = Γ† := by
    calc
      U† ∘L B + Γ† ∘L D =
          (A + B ∘L Γ)† ∘L B + (C + D ∘L Γ)† ∘L D := by
            rw [hPublic, hPrivate]
      _ = (A† ∘L B + C† ∘L D) + Γ† ∘L (B† ∘L B + D† ∘L D) := by
        simp only [map_add, adjoint_comp, add_comp, comp_add, comp_assoc]
        abel
      _ = Γ† := by rw [hMixed, hPrivateGram, zero_add, one_def, comp_id]
  have h := eq_sub_of_add_eq hCancel
  simpa only [comp_sub, one_def, comp_id] using h

/-- Exact exit block in independently typed public and private Hilbert spaces.
Only isometry of the full colligation and coisometry of the public action are
needed; no finite-dimensionality or spectral assumption is used. -/
theorem exit_block_eq
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hMixed : A† ∘L B + C† ∘L D = 0)
    (hPrivateGram : B† ∘L B + D† ∘L D = 1)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (hCoiso : U ∘L U† = 1) :
    B = U ∘L (Γ† ∘L (1 - D)) := by
  have h := adjoint_public_comp_exit A U B C Γ D hMixed hPrivateGram hPublic hPrivate
  calc
    B = (U ∘L U†) ∘L B := by rw [hCoiso, one_def, id_comp]
    _ = U ∘L (U† ∘L B) := comp_assoc _ _ _
    _ = U ∘L (Γ† ∘L (1 - D)) := by rw [h]

end
end SparseHamiltonian.ExitIdentity
