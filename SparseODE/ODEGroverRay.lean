import SparseODE.ODENativeSourceCertificate

/-!
# Rank-one preparation geometry for ODE amplification

The input to Grover amplification is the actual implemented unit vector.
Its rank-one projector is derived from that vector.  In an implementation,
the corresponding reflection is conjugated from the fixed seed reflection
by the actual preparation circuit; it is not a free input-dependent gate.
-/

namespace SparseHamiltonian.ODEGroverRay

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct ComplexConjugate

variable {K : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The linear map from a scalar amplitude to its vector on a given ray. -/
def ray (ψ : K) : ℂ →L[ℂ] K :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => z • ψ
      map_add' := by intro z w; exact add_smul z w ψ
      map_smul' := by
        intro z w
        simp only [RingHom.id_apply, smul_eq_mul, smul_smul] }

omit [CompleteSpace K] in
@[simp] theorem ray_apply (ψ : K) (z : ℂ) : ray ψ z = z • ψ := rfl

/-- The adjoint extracts the usual complex overlap. -/
theorem ray_adjoint_apply (ψ v : K) : ((ray ψ)†) v = inner ℂ ψ v := by
  have h := adjoint_inner_right (ray ψ) (1 : ℂ) v
  simpa only [ray_apply, one_smul, RCLike.inner_apply, map_one, one_mul, mul_one] using h

/-- Unit vectors give isometric preparations of a one-dimensional seed. -/
theorem ray_isometry (ψ : K) (hψ : ‖ψ‖ = 1) : (ray ψ)† ∘L ray ψ = 1 := by
  apply (ray ψ).norm_map_iff_adjoint_comp_self.mp
  intro z
  simp only [ray_apply, norm_smul, hψ, mul_one]

/-- The rank-one range operator of the actual prepared vector. -/
def projector (ψ : K) : K →L[ℂ] K := ray ψ ∘L (ray ψ)†

@[simp] theorem projector_apply (ψ v : K) :
    projector ψ v = inner ℂ ψ v • ψ := by
  simp only [projector, comp_apply, ray_apply, ray_adjoint_apply]

theorem projector_isOrthogonalProjection (ψ : K) (hψ : ‖ψ‖ = 1) :
    PhaseSubspaceGates.IsOrthogonalProjection (projector ψ) :=
  PreparationInvariantPlane.range_projection (ray ψ) (ray_isometry ψ hψ)

/-- The preparation ray contains the actual unit vector. -/
theorem projector_self (ψ : K) (hψ : ‖ψ‖ = 1) : projector ψ ψ = ψ := by
  have h := congrArg (fun T : ℂ →L[ℂ] ℂ => T 1) (ray_isometry ψ hψ)
  have hAdj : ((ray ψ)†) ψ = 1 := by
    simpa only [comp_apply, ray_apply, one_smul, one_def, id_apply] using h
  simp only [projector, comp_apply, hAdj, ray_apply, one_smul]

/-- Orthogonality of the herald gives its exact scalar compression on any ray.
This identity is proved, rather than supplied as a singular-value hypothesis. -/
theorem ray_adjoint_good (ψ : K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) :
    ((ray ψ)†) (Q ψ) = (‖Q ψ‖ : ℂ) ^ 2 := by
  have hQQ : Q (Q ψ) = Q ψ :=
    congrArg (fun T : K →L[ℂ] K => T ψ) hQ.2
  rw [ray_adjoint_apply]
  calc
    inner ℂ ψ (Q ψ) = inner ℂ ψ ((Q†) (Q ψ)) := by
      rw [show Q† = Q from hQ.1, hQQ]
    _ = inner ℂ (Q ψ) (Q ψ) := adjoint_inner_right Q ψ (Q ψ)
    _ = (‖Q ψ‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _

/-- This is the rank-one hypothesis required by the two-dimensional Grover
recurrence, discharged directly from the actual herald probability. -/
theorem projector_good (ψ : K) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) :
    projector ψ (Q ψ) = (‖Q ψ‖ : ℂ) ^ 2 • ψ := by
  simp only [projector, comp_apply, ray_adjoint_good ψ Q hQ, ray_apply]

omit [CompleteSpace K] in
/-- Preparation of a ray commutes with applying its physical linear map. -/
theorem ray_transport (W : K →L[ℂ] K) (ψ : K) :
    ray (W ψ) = W ∘L ray ψ := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [ray_apply, comp_apply, map_smul]

/-- The actual-state projector is obtained by conjugating the seed projector.
In particular, it requires preparation and inverse-preparation calls when W
is an oracle circuit; no state-dependent fixed gate is postulated. -/
theorem projector_transport (W : K →L[ℂ] K) (ψ : K) :
    projector (W ψ) = W * projector ψ * star W := by
  simpa only [projector, ← ray_transport W ψ] using
    (PreparationInvariantPlane.transported_input W (ray ψ)).symm

end
end SparseHamiltonian.ODEGroverRay
