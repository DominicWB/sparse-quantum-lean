import SparseODE.ODEFinitePropagator

/-!
# The actual heralded component of a finite ODE preparation

The output encoding specifies a genuine orthogonal projection in the physical
workspace. The successful vector is decoded from the actual implemented
unitary, so its direction and probability include all simulation errors.
The finite-LCHS/source vector error is an explicit premise here; the Gaussian
approximation and randomized amplification are separate obligations.

-/

namespace SparseHamiltonian.ODEHeraldedSuccess

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct
set_option maxHeartbeats 1000000

section Direction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Multiplication by a positive normalization leaves the output direction
unchanged, including the total definition at the zero vector. -/
theorem unitDirection_pos_smul (a : ℝ) (ha : 0 < a) (v : E) :
    unitDirection (a • v) = unitDirection v := by
  unfold unitDirection
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_inv_rev, smul_smul]
  simp only [mul_assoc, inv_mul_cancel₀ ha.ne', mul_one]

end Direction

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The herald is the range of the fixed clean output encoding. -/
def successProjector (F : E →L[ℂ] K) : K →L[ℂ] K := F ∘L F†

/-- The actual public vector conditioned on the clean output coordinates. -/
def decoded (F : E →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) : E := (F†) (W ψ)

/-- This vector is the physical projected component before normalization. -/
def successfulComponent (F : E →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) : K :=
  successProjector F (W ψ)

/-- For a unit input and unitary preparation this is the herald probability. -/
def successProbability (F : E →L[ℂ] K) (W : K →L[ℂ] K) (ψ : K) : ℝ :=
  ‖successfulComponent F W ψ‖ ^ 2

theorem successProjector_isOrthogonalProjection (F : E →L[ℂ] K)
    (hF : F† ∘L F = 1) :
    PhaseSubspaceGates.IsOrthogonalProjection (successProjector F) :=
  PreparationInvariantPlane.range_projection F hF

/-- Decoding the successful component loses no norm. -/
theorem successfulComponent_norm (F : E →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (ψ : K) :
    ‖successfulComponent F W ψ‖ = ‖decoded F W ψ‖ := by
  change ‖F (decoded F W ψ)‖ = ‖decoded F W ψ‖
  exact F.norm_map_iff_adjoint_comp_self.mpr hF (decoded F W ψ)

theorem successProbability_eq (F : E →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (ψ : K) :
    successProbability F W ψ = ‖decoded F W ψ‖ ^ 2 := by
  rw [successProbability, successfulComponent_norm F hF W ψ]

variable [NormedSpace ℝ E]

/-- These are promises about the actual implemented preparation and actual
herald. The supplied finite-sum error is applied to its decoded vector, not
an ideal circuit. This is the starting point for amplification that preserves
the actual successful direction. -/
theorem actual_preparation_certificate
    (F : E →L[ℂ] K) (hF : F† ∘L F = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (ψ : K) (hψ : ‖ψ‖ = 1)
    (x : E) (B g ε : ℝ)
    (hx : x ≠ 0) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hNorm : ‖x‖ ≤ B) (hBudget : B ≤ g * ‖x‖)
    (hError : ‖(3 * B) • decoded F W ψ - x‖ ≤
      6 * ImprovedODEQueryBudget.precision g ε * B) :
    ‖W ψ‖ = 1 ∧
    PhaseSubspaceGates.IsOrthogonalProjection (successProjector F) ∧
    decoded F W ψ ≠ 0 ∧
    ‖unitDirection (decoded F W ψ)‖ = 1 ∧
    ‖unitDirection (decoded F W ψ) - unitDirection x‖ ≤ ε / 500 ∧
    1 / (4 * g) ≤ ‖successfulComponent F W ψ‖ ∧
    ‖successfulComponent F W ψ‖ < 1 / 2 ∧
    1 / (16 * g ^ 2) ≤ successProbability F W ψ ∧
    successProbability F W ψ < 1 / 4 := by
  have hB : 0 < B := (norm_pos_iff.mpr hx).trans_le hNorm
  have h3B : 0 < 3 * B := by positivity
  have hg0 : 0 < g := by linarith
  have hScale : ‖(3 * B) • decoded F W ψ‖ / (3 * B) = ‖decoded F W ψ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h3B]
    exact mul_div_cancel_left₀ ‖decoded F W ψ‖ h3B.ne'
  have hCert := ImprovedODEOutput.output_certificate x ((3 * B) • decoded F W ψ)
    B g ε hx hg hε hεHalf hNorm hBudget hError
  rw [unitDirection_pos_smul (3 * B) h3B, hScale] at hCert
  obtain ⟨hy, hUnit, hDirection, hLowerDecoded, hUpperDecoded⟩ := hCert
  have hDecoded : decoded F W ψ ≠ 0 := by
    intro hz
    exact hy (by rw [hz, smul_zero])
  have hLower : 1 / (4 * g) ≤ ‖successfulComponent F W ψ‖ := by
    rw [successfulComponent_norm F hF W ψ]
    exact hLowerDecoded
  have hUpper : ‖successfulComponent F W ψ‖ < 1 / 2 := by
    rw [successfulComponent_norm F hF W ψ]
    exact hUpperDecoded
  have hLowerSq := pow_le_pow_left₀
    (show (0 : ℝ) ≤ 1 / (4 * g) by positivity) hLower 2
  have hScalar : (1 / (4 * g)) ^ 2 = (1 : ℝ) / (16 * g ^ 2) := by
    field_simp [hg0.ne']
    ring
  rw [hScalar] at hLowerSq
  have hUpperSq : ‖successfulComponent F W ψ‖ ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).mpr hUpper
  norm_num at hUpperSq
  refine ⟨?_, successProjector_isOrthogonalProjection F hF, hDecoded, hUnit,
    hDirection, hLower, hUpper, hLowerSq, hUpperSq⟩
  rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hψ]

end
end SparseHamiltonian.ODEHeraldedSuccess
