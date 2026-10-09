import GateEfficientHamiltonian.GateFilterHilbert

/-!
# The amplified error depends only on the successful block

For isometries `J, T : P → K` the reflection round
`reflectedAmplification J T` is an isometry whose public block is
`3B - 4BB†B`, `B = J† T` (`reflectedAmplification_compression`).  For a
unitary target `U`, the full-output error satisfies

`‖(X - J U) ψ‖² = 2 ‖ψ‖² - 2 Re ⟪(J† X) ψ, U ψ⟫`,

so two constructions with the same block `J† T` have exactly the same
full-output error, even when they act on different workspaces.  This is how
the gate-level circuit inherits the error bound of the released analysis.
-/

namespace SparseHamiltonian.GateBlockTransfer

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {P K K' : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

theorem norm_apply_of_isometry (A : P →L[ℂ] K) (hA : A† ∘L A = 1) (v : P) :
    ‖A v‖ = ‖v‖ :=
  (A.norm_map_iff_adjoint_comp_self).mpr hA v

/-- Pointwise squared error of an isometry against `J U`. -/
theorem error_sq (X J : P →L[ℂ] K) (U : P →L[ℂ] P)
    (hX : X† ∘L X = 1) (hJ : J† ∘L J = 1) (hU : U† ∘L U = 1) (v : P) :
    ‖(X - J ∘L U) v‖ ^ 2 =
      2 * ‖v‖ ^ 2 - 2 * RCLike.re (inner ℂ (((J†) ∘L X) v) (U v)) := by
  have hXv := norm_apply_of_isometry X hX v
  have hJU : ‖J (U v)‖ = ‖v‖ := by
    rw [norm_apply_of_isometry J hJ, norm_apply_of_isometry U hU]
  have hinner : inner ℂ (X v) (J (U v)) = inner ℂ (((J†) ∘L X) v) (U v) := by
    rw [comp_apply, adjoint_inner_left]
  rw [sub_apply, comp_apply, @norm_sub_sq ℂ, hXv, hJU, hinner]
  ring

/-- **Block transfer.** Constructions with the same successful block have the
same full-output error against every unitary target. -/
theorem amplified_error_le (J T : P →L[ℂ] K) (J' T' : P →L[ℂ] K')
    (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1)
    (hJ' : J'† ∘L J' = 1) (hT' : T'† ∘L T' = 1)
    (hB : J'† ∘L T' = J† ∘L T) (U : P →L[ℂ] P) (hU : U† ∘L U = 1) :
    ‖reflectedAmplification J' T' - J' ∘L U‖ ≤
      ‖reflectedAmplification J T - J ∘L U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  have h1 := error_sq (reflectedAmplification J' T') J' U
    (reflectedAmplification_isometry J' T' hJ' hT') hJ' hU v
  have h2 := error_sq (reflectedAmplification J T) J U
    (reflectedAmplification_isometry J T hJ hT) hJ hU v
  have hc : J'† ∘L reflectedAmplification J' T' = J† ∘L reflectedAmplification J T := by
    rw [reflectedAmplification_compression J' T' hJ' hT',
      reflectedAmplification_compression J T hJ hT, hB]
  rw [hc] at h1
  have heq : ‖(reflectedAmplification J' T' - J' ∘L U) v‖ =
      ‖(reflectedAmplification J T - J ∘L U) v‖ := by
    have hsq : ‖(reflectedAmplification J' T' - J' ∘L U) v‖ ^ 2 =
        ‖(reflectedAmplification J T - J ∘L U) v‖ ^ 2 := by rw [h1, h2]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  rw [heq]
  exact (reflectedAmplification J T - J ∘L U).le_opNorm v

end

end SparseHamiltonian.GateBlockTransfer
