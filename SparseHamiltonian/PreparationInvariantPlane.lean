import SparseHamiltonian.InvariantPhaseSequence

/-!
# Invariant output planes of an isometric preparation

The compression of the fixed good projection determines the two-dimensional
action of the transported input projection. The preparation itself need not
preserve this plane. Zero and unit success are included: the coordinate map
may be degenerate and no nonzero success amplitude is assumed.
-/

namespace SparseHamiltonian.PreparationInvariantPlane

noncomputable section
open ContinuousLinearMap ComplexAmplitudeRotation
open scoped InnerProduct ComplexConjugate

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- A pair of output directions, with no nondegeneracy requirement. -/
def plane (g b : K) : Qubit →L[ℂ] K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => z false • g + z true • b
      map_add' := by intro z w; simp only [PiLp.add_apply, add_smul]; module
      map_smul' := by
        intro c z
        simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul] }

omit [CompleteSpace K] in
@[simp] theorem plane_apply (g b : K) (z : Qubit) :
    plane g b z = z false • g + z true • b := rfl

/-- A projected vector is zero when its compression through its source vanishes. -/
theorem projected_zero (R : E →L[ℂ] K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (e : E)
    (h : (R†) (Q (R e)) = 0) : Q (R e) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  have hQQ : Q (Q (R e)) = Q (R e) :=
    congrArg (fun T : K →L[ℂ] K => T (R e)) hQ.2
  calc
    inner ℂ (Q (R e)) (Q (R e)) = inner ℂ (R e) ((Q†) (Q (R e))) :=
      (adjoint_inner_right Q (R e) (Q (R e))).symm
    _ = inner ℂ (R e) (Q (R e)) := by rw [show Q† = Q from hQ.1, hQQ]
    _ = inner ℂ e ((R†) (Q (R e))) := (adjoint_inner_right R e _).symm
    _ = 0 := by rw [h, inner_zero_right]

/-- The complementary projection is again orthogonal. -/
theorem complement_projection (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) :
    PhaseSubspaceGates.IsOrthogonalProjection (1 - Q) := by
  constructor
  · simp [star_sub, hQ.1]
  · simp only [sub_mul, mul_sub, one_mul, mul_one, hQ.2]; abel

/-- Directions normalized only in mathematical analysis, never prepared by an oracle. -/
def goodDirection (R : E →L[ℂ] K) (Q : K →L[ℂ] K) (e : E) (x : ℝ) : K :=
  (x : ℂ)⁻¹ • Q (R e)

def badDirection (R : E →L[ℂ] K) (Q : K →L[ℂ] K) (e : E) (x : ℝ) : K :=
  (badAmplitude (x : ℂ) : ℂ)⁻¹ • ((1 - Q) (R e))

theorem good_scale (R : E →L[ℂ] K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (e : E) (x : ℝ)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e) :
    (x : ℂ) • goodDirection R Q e x = Q (R e) := by
  by_cases hx : (x : ℂ) = 0
  · have hz : Q (R e) = 0 := projected_zero R Q hQ e (by simpa [hx] using he)
    simp [goodDirection, hx, hz]
  · simp [goodDirection, smul_smul, hx]

theorem bad_scale (R : E →L[ℂ] K) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e) :
    (badAmplitude (x : ℂ) : ℂ) • badDirection R Q e x = (1 - Q) (R e) := by
  have hRe : (R†) (R e) = e := congrArg (fun T : E →L[ℂ] E => T e) hR
  have hcomp : (R†) ((1 - Q) (R e)) = (1 - (x : ℂ) ^ 2) • e := by
    simp only [sub_apply, one_def, id_apply, map_sub, hRe, he, sub_smul, one_smul]
  by_cases hμ : (badAmplitude (x : ℂ) : ℂ) = 0
  · have hs := AmplitudePolynomialSequence.badAmplitude_square x hx
    have hz : (1 - Q) (R e) = 0 := projected_zero R (1 - Q)
      (complement_projection Q hQ) e (by rw [hcomp, ← hs, hμ]; simp)
    simp [badDirection, hμ, hz]
  · simp [badDirection, smul_smul, hμ]

omit [CompleteSpace E] in
/-- The good flag fixes the first direction. -/
theorem good_fixed (R : E →L[ℂ] K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (e : E) (x : ℝ) :
    Q (goodDirection R Q e x) = goodDirection R Q e x := by
  have hQQ : Q (Q (R e)) = Q (R e) :=
    congrArg (fun T : K →L[ℂ] K => T (R e)) hQ.2
  simp [goodDirection, hQQ]

omit [CompleteSpace E] in
/-- The good flag kills the second direction, including degenerate endpoints. -/
theorem bad_kernel (R : E →L[ℂ] K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (e : E) (x : ℝ) :
    Q (badDirection R Q e x) = 0 := by
  have hQQ : Q (Q (R e)) = Q (R e) :=
    congrArg (fun T : K →L[ℂ] K => T (R e)) hQ.2
  simp [badDirection, hQQ]

/-- The range projector has the required action on the good direction. -/
theorem range_good (R : E →L[ℂ] K) (Q : K →L[ℂ] K) (e : E) (x : ℝ)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e) :
    (R ∘L R†) (goodDirection R Q e x) = (x : ℂ) • R e := by
  by_cases hx : (x : ℂ) = 0
  · simp [goodDirection, hx]
  · simp only [goodDirection, comp_apply, map_smul, he, smul_smul]
    congr 1
    field_simp

/-- The range projector has the complementary action on the bad direction. -/
theorem range_bad (R : E →L[ℂ] K) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e) :
    (R ∘L R†) (badDirection R Q e x) =
      (badAmplitude (x : ℂ) : ℂ) • R e := by
  have hRe : (R†) (R e) = e := congrArg (fun T : E →L[ℂ] E => T e) hR
  have hcomp : (R†) ((1 - Q) (R e)) = (1 - (x : ℂ) ^ 2) • e := by
    simp only [sub_apply, one_def, id_apply, map_sub, hRe, he, sub_smul, one_smul]
  by_cases hμ : (badAmplitude (x : ℂ) : ℂ) = 0
  · simp [badDirection, hμ]
  · simp only [badDirection, comp_apply, map_smul, hcomp, smul_smul]
    rw [← AmplitudePolynomialSequence.badAmplitude_square x hx]
    congr 1
    field_simp

/-- The initial state is the real signal rotation mapped into its output plane. -/
theorem initial (R : E →L[ℂ] K) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e) :
    plane (goodDirection R Q e x) (badDirection R Q e x)
      (rotation (x : ℂ) clean) = R e := by
  simp only [plane_apply, rotation_clean_good, rotation_clean_bad]
  rw [good_scale R Q hQ e x he, bad_scale R hR Q hQ e x hx he]
  simp

omit [CompleteSpace E] in
/-- The fixed good projector is diagonal on the output coordinates. -/
theorem good_intertwines (R : E →L[ℂ] K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (e : E) (x : ℝ) :
    Q ∘L plane (goodDirection R Q e x) (badDirection R Q e x) =
      plane (goodDirection R Q e x) (badDirection R Q e x) ∘L
        AmplitudePolynomialSequence.cleanProjection := by
  ext z
  simp [plane_apply, good_fixed R Q hQ e x, bad_kernel R Q hQ e x,
    AmplitudePolynomialSequence.cleanProjection]

/-- The transported input projector is exactly the real rotated clean projector.
This conclusion holds at zero and unit success without an injective plane map. -/
theorem range_intertwines (R : E →L[ℂ] K) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e) :
    (R ∘L R†) ∘L plane (goodDirection R Q e x) (badDirection R Q e x) =
      plane (goodDirection R Q e x) (badDirection R Q e x) ∘L
        (rotation (x : ℂ) * AmplitudePolynomialSequence.cleanProjection *
          star (rotation (x : ℂ))) := by
  have hsplit : (x : ℂ) • goodDirection R Q e x +
      (badAmplitude (x : ℂ) : ℂ) • badDirection R Q e x = R e := by
    simpa only [plane_apply, rotation_clean_good, rotation_clean_bad] using
      initial R hR Q hQ e x hx he
  ext z
  change (R ∘L R†) (plane (goodDirection R Q e x) (badDirection R Q e x) z) = _
  rw [plane_apply, map_add, map_smul, map_smul,
    range_good R Q e x he, range_bad R hR Q e x hx he, ← hsplit]
  simp only [comp_apply, plane_apply, mul_apply_eq_comp, star_eq_adjoint,
    rotation_adjoint, AmplitudePolynomialSequence.cleanProjection,
    rotation_false, rotation_true, matrix_false, matrix_true,
    Complex.conj_ofReal, zero_mul, add_zero, one_mul, mul_zero, sub_zero]
  module

/-- An isometry's range operator is an orthogonal projection. -/
theorem range_projection (R : E →L[ℂ] K) (hR : R† ∘L R = 1) :
    PhaseSubspaceGates.IsOrthogonalProjection (R ∘L R†) := by
  constructor
  · simp only [star_eq_adjoint, adjoint_comp, adjoint_adjoint]
  · have hRe (e : E) : (R†) (R e) = e :=
      congrArg (fun T : E →L[ℂ] E => T e) hR
    ext v
    simp only [mul_apply_eq_comp, comp_apply, hRe]

/-- The concrete preparation identifies its transported clean projector. -/
theorem transported_input (U : K →L[ℂ] K) (F : E →L[ℂ] K) :
    U * (F ∘L F†) * star U = (U ∘L F) ∘L (U ∘L F)† := by
  simp only [star_eq_adjoint, adjoint_comp, comp_assoc]
  rfl

/-- A concrete clean preparation inherits the exact polynomial output identity. -/
theorem prepared_column (U : K →L[ℂ] K) (hU : OracleCircuit.IsUnitary U)
    (F R : E →L[ℂ] K) (hprep : U ∘L F = R) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e)
    (ss : List AmplitudePolynomialSequence.Phases) :
    (PhaseSubspaceGates.sequence U (F ∘L F†) Q ss * U) (F e) =
      plane (goodDirection R Q e x) (badDirection R Q e x)
        (AmplitudePolynomialSequence.column x
          (AmplitudePolynomialSequence.polynomials ss).1
          (AmplitudePolynomialSequence.polynomials ss).2) := by
  apply InvariantPhaseSequence.prepared_column U (F ∘L F†) Q hU x hx
    (plane (goodDirection R Q e x) (badDirection R Q e x)) ?_
    (good_intertwines R Q hQ e x) (F e) ?_ ss
  · rw [transported_input, hprep]
    exact range_intertwines R hR Q hQ e x hx he
  · rw [← comp_apply, hprep]
    exact (initial R hR Q hQ e x hx he).symm

/-- The good polynomial multiplies the normalized good direction. -/
theorem prepared_good (U : K →L[ℂ] K) (hU : OracleCircuit.IsUnitary U)
    (F R : E →L[ℂ] K) (hprep : U ∘L F = R) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e)
    (ss : List AmplitudePolynomialSequence.Phases) :
    Q ((PhaseSubspaceGates.sequence U (F ∘L F†) Q ss * U) (F e)) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (x : ℂ) •
        goodDirection R Q e x := by
  have h := InvariantPhaseSequence.prepared_good U (F ∘L F†) Q hU x hx
    (plane (goodDirection R Q e x) (badDirection R Q e x))
    (by rw [transported_input, hprep]; exact range_intertwines R hR Q hQ e x hx he)
    (good_intertwines R Q hQ e x) (F e)
    (by rw [← comp_apply, hprep]; exact (initial R hR Q hQ e x hx he).symm) ss
  simpa [plane_apply] using h

/-- A scalar relative-error bound transfers to the concrete prepared output. -/
theorem prepared_good_error (U : K →L[ℂ] K) (hU : OracleCircuit.IsUnitary U)
    (F R : E →L[ℂ] K) (hprep : U ∘L F = R) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e)
    (ss : List AmplitudePolynomialSequence.Phases) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (x : ℂ) -
      gain * (x : ℂ)‖ ≤ δ * |x|) :
    ‖Q ((PhaseSubspaceGates.sequence U (F ∘L F†) Q ss * U) (F e)) -
      gain • Q (R e)‖ ≤ δ * ‖Q (R e)‖ := by
  have h := InvariantPhaseSequence.prepared_good_error U (F ∘L F†) Q hU x hx
    (plane (goodDirection R Q e x) (badDirection R Q e x))
    (by rw [transported_input, hprep]; exact range_intertwines R hR Q hQ e x hx he)
    (good_intertwines R Q hQ e x) (F e)
    (by rw [← comp_apply, hprep]; exact (initial R hR Q hQ e x hx he).symm)
    ss gain δ herr
  have hp : U (F e) = R e := congrArg (fun T : E →L[ℂ] K => T e) hprep
  simpa only [hp] using h

end
end SparseHamiltonian.PreparationInvariantPlane
