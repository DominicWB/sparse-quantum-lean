import SparseHamiltonian.HermitianSuccessSignals

/-!
# Full overlap after separate success and failure gains

An amplitude polynomial changes both parts of a preparation. This module
proves that arbitrary new gains on the two old failure spaces contribute
no overlap when those spaces were initially orthogonal. The full transformed
overlap is therefore the adjoint sandwich of the original overlap by the
success gains, including arbitrary complex gains.
-/

namespace SparseHamiltonian.ProjectedGainOverlap

noncomputable section
open ContinuousLinearMap PhaseSubspaceGates
open scoped InnerProduct ComplexConjugate

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Separate analytical gains on the success and failure parts of a preparation. -/
def transformed (Q : K →L[ℂ] K) (R : E →L[ℂ] K) (G B : E →L[ℂ] E) : E →L[ℂ] K :=
  Q ∘L R ∘L G + (1 - Q) ∘L R ∘L B

/-- Orthogonal projection identities eliminate every mixed success/failure term. -/
theorem projection_products (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q) :
    Q ∘L Q = Q ∧ Q ∘L (1 - Q) = 0 ∧ (1 - Q) ∘L Q = 0 ∧
      (1 - Q) ∘L (1 - Q) = 1 - Q := by
  have hQQ : Q ∘L Q = Q := hQ.2
  refine ⟨hQQ, ?_, ?_, ?_⟩
  · rw [comp_sub, one_def, comp_id, hQQ, sub_self]
  · rw [sub_comp, one_def, id_comp, hQQ, sub_self]
  · simp only [comp_sub, sub_comp, one_def, comp_id, id_comp, hQQ]
    abel

/-- Full transformed overlap is the sum of success and failure sandwiches. -/
theorem transformed_overlap_split (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (R C : E →L[ℂ] K) (GR BR GC BC : E →L[ℂ] E) :
    (transformed Q R GR BR)† ∘L transformed Q C GC BC =
      GR† ∘L (R† ∘L Q ∘L C) ∘L GC +
        BR† ∘L (R† ∘L (1 - Q) ∘L C) ∘L BC := by
  have hQa : Q† = Q := hQ.1
  have hQQ (v : K) : Q (Q v) = Q v := congrArg (fun f : K →L[ℂ] K => f v) hQ.2
  ext v
  simp only [transformed, map_add, adjoint_comp, map_sub, adjoint_one, hQa]
  simp only [comp_apply, add_apply, map_add, sub_apply, one_def, id_apply, map_sub, hQQ]
  abel

/-- Initially orthogonal failure spaces remain irrelevant under arbitrary
linear changes on their input labels. -/
theorem transformed_overlap_good (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (R C : E →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0)
    (GR BR GC BC : E →L[ℂ] E) :
    (transformed Q R GR BR)† ∘L transformed Q C GC BC =
      GR† ∘L (R† ∘L Q ∘L C) ∘L GC := by
  rw [transformed_overlap_split Q hQ R C GR BR GC BC, hbad]
  simp

/-- Orthogonality identifies the original overlap with its good part. -/
theorem original_overlap_good (Q : K →L[ℂ] K) (R C : E →L[ℂ] K)
    (hbad : R† ∘L (1 - Q) ∘L C = 0) : R† ∘L Q ∘L C = R† ∘L C := by
  have h : R† ∘L C - R† ∘L Q ∘L C = 0 := by
    simpa only [sub_comp, one_def, id_comp, comp_sub] using hbad
  exact (sub_eq_zero.mp h).symm

/-- The complete transformed states have precisely the desired success-gain
overlap; the failure gains need not agree or be real. -/
theorem transformed_overlap (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (R C : E →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0)
    (GR BR GC BC : E →L[ℂ] E) :
    (transformed Q R GR BR)† ∘L transformed Q C GC BC =
      GR† ∘L (R† ∘L C) ∘L GC := by
  rw [transformed_overlap_good Q hQ R C hbad GR BR GC BC,
    original_overlap_good Q R C hbad]

/-- A shared complex target gain leaves a nonnegative real normalization. -/
theorem target_sandwich (H D : E →L[ℂ] E) (target : ℂ) :
    (target • (1 + D))† ∘L H ∘L (target • (1 + D)) =
      ((‖target‖ ^ 2 : ℝ) : ℂ) • RelativeAmplitudeError.conjugateScaled H D := by
  simp only [map_smulₛₗ, comp_smul, smul_comp, smul_smul]
  have hscalar : target * conj target = ((‖target‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hscalar]
  rfl

/-- The normalized Hamiltonian is the same relative-error sandwich even when
the successful amplitudes and target gain have complex phases. -/
theorem transformed_overlap_relative (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (R C : E →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0)
    (D BR BC : E →L[ℂ] E) (target : ℂ) :
    (transformed Q R (target • (1 + D)) BR)† ∘L
        transformed Q C (target • (1 + D)) BC =
      ((‖target‖ ^ 2 : ℝ) : ℂ) •
        RelativeAmplitudeError.conjugateScaled (R† ∘L C) D := by
  rw [transformed_overlap Q hQ R C hbad, target_sandwich]

/-- Shared good gains preserve self-adjointness of the full physical overlap. -/
theorem transformed_overlap_adjoint (Q : K →L[ℂ] K) (hQ : IsOrthogonalProjection Q)
    (R C : E →L[ℂ] K) (hbad : R† ∘L (1 - Q) ∘L C = 0)
    (hH : (R† ∘L C)† = R† ∘L C) (G BR BC : E →L[ℂ] E) :
    ((transformed Q R G BR)† ∘L transformed Q C G BC)† =
      (transformed Q R G BR)† ∘L transformed Q C G BC := by
  rw [transformed_overlap Q hQ R C hbad]
  have hH' : C† ∘L R = R† ∘L C := by
    simpa only [adjoint_comp, adjoint_adjoint] using hH
  rw [adjoint_comp, adjoint_comp, adjoint_adjoint, adjoint_comp, adjoint_adjoint]
  simp only [comp_assoc] at hH' ⊢
  rw [← comp_assoc (C†) R G, hH']
  exact comp_assoc _ _ _

/-- The perturbation budget depends on the original overlap norm and has no
dimension factor or contribution from either failure gain. -/
theorem norm_transformed_overlap_sub_le (Q : K →L[ℂ] K)
    (hQ : IsOrthogonalProjection Q) (R C : E →L[ℂ] K)
    (hbad : R† ∘L (1 - Q) ∘L C = 0) (D BR BC : E →L[ℂ] E)
    (target : ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hD : ‖D‖ ≤ δ) :
    ‖(transformed Q R (target • (1 + D)) BR)† ∘L
        transformed Q C (target • (1 + D)) BC -
      ((‖target‖ ^ 2 : ℝ) : ℂ) • (R† ∘L C)‖ ≤
      ‖target‖ ^ 2 * ((2 * δ + δ ^ 2) * ‖R† ∘L C‖) := by
  rw [transformed_overlap_relative Q hQ R C hbad, ← smul_sub, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left
    (RelativeAmplitudeError.norm_conjugateScaled_sub_le (R† ∘L C) D δ hδ hD)
    (sq_nonneg _)

end
end SparseHamiltonian.ProjectedGainOverlap
