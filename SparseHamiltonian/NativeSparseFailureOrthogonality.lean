import SparseHamiltonian.ProjectedGainOverlap

/-!
# Orthogonality of the actual sparse preparation failure spaces

The row and column failure flags are different. This remains true for
independently padded location lists and after embedding into the full native
oracle workspace. The theorems below provide the concrete original overlap
and failure orthogonality needed to apply the generic polynomial-gain Gram
identity to actual native circuits.
-/

namespace SparseHamiltonian.NativeSparseFailureOrthogonality

noncomputable section
open ContinuousLinearMap SparseSlotStates SparseSuccessProjection
open NativeSparsePhaseSequence
open scoped InnerProduct BigOperators ComplexConjugate

section IsometricTransport
variable {E K V : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- An isometric workspace embedding preserves the cross failure overlap. -/
theorem failure_overlap_lift (J : K →L[ℂ] V) (hJ : J† ∘L J = 1)
    (Q : K →L[ℂ] K) (R C : E →L[ℂ] K) :
    (J ∘L R)† ∘L (1 - J ∘L Q ∘L J†) ∘L (J ∘L C) =
      R† ∘L (1 - Q) ∘L C := by
  have hJv (v : K) : (J†) (J v) = v := congrArg (fun f : K →L[ℂ] K => f v) hJ
  ext v
  simp only [adjoint_comp, comp_apply, sub_apply, one_def, id_apply, map_sub, hJv]

/-- The same embedding preserves the complete row-column overlap. -/
theorem overlap_lift (J : K →L[ℂ] V) (hJ : J† ∘L J = 1) (R C : E →L[ℂ] K) :
    (J ∘L R)† ∘L (J ∘L C) = R† ∘L C := by
  have hJv (v : K) : (J†) (J v) = v := congrArg (fun f : K →L[ℂ] K => f v) hJ
  ext v
  simp only [adjoint_comp, comp_apply, hJv]

end IsometricTransport

section Native
variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Actual native preparations have exactly orthogonal old failure spaces. -/
theorem native_failure_overlap (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (rowState D x)† ∘L (1 - goodProjection) ∘L columnState D x = 0 := by
  rw [rowState, columnState, goodProjection,
    failure_overlap_lift _ (LinearIsometry.adjoint_comp_self _)]
  exact SparseFreshAttenuation.old_failure_orthogonal (D.matrix x) D.scale (D.rowloc x) (D.colloc x)

/-- Native prepared states have the exact sparse normalization `s * scale`. -/
theorem native_overlap (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (rowState D x)† ∘L columnState D x =
      SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  rw [rowState, columnState, overlap_lift _ (LinearIsometry.adjoint_comp_self _)]
  exact SparseSlotStates.overlap_eq_matrix (D.matrix x) D.scale D.scale_pos
    (D.rowloc x) (D.colloc x) (D.row_covers x) (D.column_covers x)

end Native
end
end SparseHamiltonian.NativeSparseFailureOrthogonality
