import SparseODE.ODEHeraldedSuccess

/-!
# Initial and source preparations under one actual joint simulation

The branch preparations are explicit isometries. They share a public seed;
the joint physical simulator is used once, independently of the branch count.
This fragment derives the decoded vector from the actual simulated output.
Preparing or compiling the supplied branch isometries is a separate input
access obligation. No analytic LCHS or source-quadrature approximation is
assumed in the simulation-error lemmas below.

-/

namespace SparseHamiltonian.ODEJointSourceLCU

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct
set_option synthInstance.maxSize 2048

variable {ι P K : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Coefficient-weighted source preparation, followed by the simulator's
fixed clean encoding. The preparations may differ on every branch. -/
def input (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (J : ι → P →L[ℂ] P) : P →L[ℂ] K :=
  E ∘L ODECoherentLCU.inputEmbedding c J

/-- The exact finite operator selected by the branch coefficient and source
preparations, before any normalization. -/
def targetSum (c : ι → ℂ) (U J : ι → P →L[ℂ] P) : P →L[ℂ] P :=
  ∑ i, c i • (U i ∘L J i)

def normalizedTarget (c : ι → ℂ) (U J : ι → P →L[ℂ] P) : P →L[ℂ] P :=
  (ODECoherentLCU.coefficientMass c : ℂ)⁻¹ • targetSum c U J

/-- Decoding uses the actual physical output and the phase-corrected output
isometry. It is the public vector of the heralded component. -/
def decoded (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (J : ι → P →L[ℂ] P) (W : K →L[ℂ] K) (v : P) : P :=
  ODEHeraldedSuccess.decoded (ODEJointLCU.output E c) W (input E c J v)

theorem input_isometry (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K)
    (c : ι → ℂ) (J : ι → P →L[ℂ] P)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (hJ : ∀ i, (J i)† ∘L J i = 1) :
    (input E c J)† ∘L input E c J = 1 := by
  change (E ∘L ODECoherentLCU.inputEmbedding c J)† ∘L
    (E ∘L ODECoherentLCU.inputEmbedding c J) = 1
  exact NativeSparseAttenuation.isometry_comp
    (A := P) (B := ODEJointLCU.BranchSpace ι P) (C := K)
    (ODECoherentLCU.inputEmbedding c J) E
    (ODECoherentLCU.inputEmbedding_isometry c hc J hJ) hE

/-- A unit seed is genuinely prepared as a unit physical input; any actual
unitary simulator preserves that normalization. -/
theorem physical_unit_vectors (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K)
    (c : ι → ℂ) (J : ι → P →L[ℂ] P)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (hJ : ∀ i, (J i)† ∘L J i = 1)
    (W : K →L[ℂ] K) (hW : IsUnitary W) (v : P) (hv : ‖v‖ = 1) :
    ‖input E c J v‖ = 1 ∧ ‖W (input E c J v)‖ = 1 ∧
      (ODEJointLCU.output E c)† ∘L ODEJointLCU.output E c = 1 := by
  have hInput : ‖input E c J v‖ = 1 := by
    rw [(input E c J).norm_map_iff_adjoint_comp_self.mpr
      (input_isometry E c J hE hc hJ), hv]
  refine ⟨hInput, ?_, ODEJointLCU.output_isometry E c hE hc⟩
  rw [W.norm_map_iff_adjoint_comp_self.mpr hW.1, hInput]

/-- A global full-output simulation bound passes through the source
preparation and coefficient unpreparation without growing with their count. -/
theorem compression_error (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K)
    (c : ι → ℂ) (J : ι → P →L[ℂ] P)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (hJ : ∀ i, (J i)† ∘L J i = 1)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (δ : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ) :
    ‖(ODEJointLCU.output E c)† ∘L W ∘L input E c J -
      normalizedTarget c U J‖ ≤ δ := by
  let B : ODEJointLCU.BranchSpace ι P →L[ℂ] ODEJointLCU.BranchSpace ι P :=
    E† ∘L W ∘L E
  have hB : ‖B - WeightedClock.diagonal U‖ ≤ δ :=
    ODEControlledLCU.branch_compression_error W E E
      (WeightedClock.diagonal U) δ hE hError
  have hInputNorm : ‖ODECoherentLCU.inputEmbedding c J‖ ≤ 1 :=
    ODECoherentLCU.isometry_norm_le_one _
      (ODECoherentLCU.inputEmbedding_isometry c hc J hJ)
  have hPrepared :
      ‖B ∘L ODECoherentLCU.inputEmbedding c J -
        WeightedClock.diagonal U ∘L ODECoherentLCU.inputEmbedding c J‖ ≤ δ := by
    rw [← sub_comp]
    calc
      _ ≤ ‖B - WeightedClock.diagonal U‖ *
          ‖ODECoherentLCU.inputEmbedding c J‖ := opNorm_comp_le _ _
      _ ≤ ‖B - WeightedClock.diagonal U‖ * 1 :=
        mul_le_mul_of_nonneg_left hInputNorm
          (ContinuousLinearMap.opNorm_nonneg (B - WeightedClock.diagonal U))
      _ ≤ δ := by simpa only [mul_one] using hB
  have hCompressed := ODECoherentLCU.successful_compression_error_le c hc U J
    (fun _ : ι => (1 : P →L[ℂ] P))
    (fun _ => by simp only [one_def, adjoint_id, id_comp])
    (B ∘L ODECoherentLCU.inputEmbedding c J) δ hPrepared
  have hBlock : (ODEJointLCU.output E c)† ∘L W ∘L input E c J =
      (ODEJointLCU.coefficientOutput c)† ∘L
        (B ∘L ODECoherentLCU.inputEmbedding c J) := by
    simp only [input, ODEJointLCU.output, B, adjoint_comp, comp_assoc]
  rw [hBlock]
  simpa only [normalizedTarget, targetSum, ODEJointLCU.coefficientOutput,
    one_def, adjoint_id, id_comp] using hCompressed

/-- Multiplication by the true coefficient mass restores the finite source
sum and scales only the simulation error. -/
theorem scaled_compression_error (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K)
    (c : ι → ℂ) (J : ι → P →L[ℂ] P)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (hJ : ∀ i, (J i)† ∘L J i = 1)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (δ : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ) :
    ‖(ODECoherentLCU.coefficientMass c : ℂ) •
        ((ODEJointLCU.output E c)† ∘L W ∘L input E c J) - targetSum c U J‖ ≤
      ODECoherentLCU.coefficientMass c * δ := by
  have hC : (ODECoherentLCU.coefficientMass c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hNormalize :
      (ODECoherentLCU.coefficientMass c : ℂ) • normalizedTarget c U J =
        targetSum c U J := by
    rw [normalizedTarget, smul_smul, mul_inv_cancel₀ hC, one_smul]
  calc
    _ = ‖(ODECoherentLCU.coefficientMass c : ℂ) •
        ((ODEJointLCU.output E c)† ∘L W ∘L input E c J -
          normalizedTarget c U J)‖ := by rw [smul_sub, hNormalize]
    _ = ODECoherentLCU.coefficientMass c *
        ‖(ODEJointLCU.output E c)† ∘L W ∘L input E c J -
          normalizedTarget c U J‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.le]
    _ ≤ ODECoherentLCU.coefficientMass c * δ :=
      mul_le_mul_of_nonneg_left (compression_error E c J hE hc hJ W U δ hError) hc.le

omit [CompleteSpace P] in
/-- Exact action of the target operator on the shared seed. -/
theorem targetSum_apply (c : ι → ℂ) (U J : ι → P →L[ℂ] P) (v : P) :
    targetSum c U J v = ∑ i, c i • U i (J i v) := by
  simp [targetSum]

/-- Error of the actual decoded physical output, before assuming any
Gaussian LCHS formula or any source quadrature. -/
theorem actual_vector_error (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K)
    (c : ι → ℂ) (J : ι → P →L[ℂ] P)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (hJ : ∀ i, (J i)† ∘L J i = 1)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (δ : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ) (v : P) :
    ‖(ODECoherentLCU.coefficientMass c : ℂ) • decoded E c J W v -
        ∑ i, c i • U i (J i v)‖ ≤
      ODECoherentLCU.coefficientMass c * δ * ‖v‖ := by
  have hApplied := ODEErrorBudget.applied_error_le
    ((ODECoherentLCU.coefficientMass c : ℂ) •
      ((ODEJointLCU.output E c)† ∘L W ∘L input E c J))
    (targetSum c U J) v (ODECoherentLCU.coefficientMass c * δ)
    (scaled_compression_error E c J hE hc hJ W U δ hError)
  simpa only [decoded, ODEHeraldedSuccess.decoded, smul_apply, comp_apply,
    targetSum_apply] using hApplied

theorem actual_unit_vector_error (E : ODEJointLCU.BranchSpace ι P →L[ℂ] K)
    (c : ι → ℂ) (J : ι → P →L[ℂ] P)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (hJ : ∀ i, (J i)† ∘L J i = 1)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (δ : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ)
    (v : P) (hv : ‖v‖ = 1) :
    ‖(ODECoherentLCU.coefficientMass c : ℂ) • decoded E c J W v -
        ∑ i, c i • U i (J i v)‖ ≤ ODECoherentLCU.coefficientMass c * δ := by
  simpa only [hv, mul_one] using actual_vector_error E c J hE hc hJ W U δ hError v

end
end SparseHamiltonian.ODEJointSourceLCU
