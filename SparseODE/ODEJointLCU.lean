import SparseODE.ODECoherentSimulation

/-!
# Complex LCU through a single joint clean encoding

The coherent simulator already acts on the whole branch register. Its
physical circuit need not be a diagonal family of branch circuits. The
existing complex coefficient preparations are composed with its one clean
encoding, and the full-output error bounds the resulting successful block.

-/

namespace SparseHamiltonian.ODEJointLCU

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct
set_option synthInstance.maxSize 2048

variable {ι P K : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev BranchSpace (ι P : Type*) [Fintype ι]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] :=
  PiLp 2 (fun _ : ι => P)

def coefficientInput (c : ι → ℂ) : P →L[ℂ] BranchSpace ι P :=
  ODECoherentLCU.inputEmbedding c (fun _ : ι => (1 : P →L[ℂ] P))

def coefficientOutput (c : ι → ℂ) : P →L[ℂ] BranchSpace ι P :=
  ODECoherentLCU.outputEmbedding c (fun _ : ι => (1 : P →L[ℂ] P))

def input (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ) : P →L[ℂ] K :=
  E ∘L coefficientInput c

def output (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ) : P →L[ℂ] K :=
  E ∘L coefficientOutput c

def normalizedSum (c : ι → ℂ) (U : ι → P →L[ℂ] P) : P →L[ℂ] P :=
  (ODECoherentLCU.coefficientMass c : ℂ)⁻¹ • ∑ i, c i • U i

theorem coefficientInput_isometry (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c) :
    (coefficientInput (P := P) c)† ∘L coefficientInput c = 1 :=
  ODECoherentLCU.inputEmbedding_isometry c hc
    (fun _ : ι => (1 : P →L[ℂ] P))
    (fun _ => by simp only [one_def, adjoint_id, id_comp])

theorem coefficientOutput_isometry (c : ι → ℂ)
    (hc : 0 < ODECoherentLCU.coefficientMass c) :
    (coefficientOutput (P := P) c)† ∘L coefficientOutput c = 1 :=
  ODECoherentLCU.outputEmbedding_isometry c hc
    (fun _ : ι => (1 : P →L[ℂ] P))
    (fun _ => by simp only [one_def, adjoint_id, id_comp])

theorem input_isometry (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c) :
    (input E c)† ∘L input E c = 1 := by
  change (E ∘L coefficientInput (P := P) c)† ∘L
    (E ∘L coefficientInput (P := P) c) = 1
  exact NativeSparseAttenuation.isometry_comp
    (A := P) (B := BranchSpace ι P) (C := K)
    (coefficientInput (P := P) c) E (coefficientInput_isometry (P := P) c hc) hE

theorem output_isometry (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c) :
    (output E c)† ∘L output E c = 1 := by
  change (E ∘L coefficientOutput (P := P) c)† ∘L
    (E ∘L coefficientOutput (P := P) c) = 1
  exact NativeSparseAttenuation.isometry_comp
    (A := P) (B := BranchSpace ι P) (C := K)
    (coefficientOutput (P := P) c) E (coefficientOutput_isometry (P := P) c hc) hE

/-- Successful compression of an implemented joint SELECT has the same
normalized operator error, irrespective of the number of coefficient nodes. -/
theorem compression_error (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (δ : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ) :
    ‖(output E c)† ∘L W ∘L input E c - normalizedSum c U‖ ≤ δ := by
  let B : BranchSpace ι P →L[ℂ] BranchSpace ι P := E† ∘L W ∘L E
  have hB : ‖B - WeightedClock.diagonal U‖ ≤ δ :=
    ODEControlledLCU.branch_compression_error W E E
      (WeightedClock.diagonal U) δ hE hError
  have hInputNorm : ‖coefficientInput (P := P) c‖ ≤ 1 :=
    ODECoherentLCU.isometry_norm_le_one _ (coefficientInput_isometry c hc)
  have hPrepared :
      ‖B ∘L coefficientInput c - WeightedClock.diagonal U ∘L coefficientInput c‖ ≤ δ := by
    rw [← sub_comp]
    calc
      ‖(B - WeightedClock.diagonal U) ∘L coefficientInput c‖ ≤
          ‖B - WeightedClock.diagonal U‖ * ‖coefficientInput (P := P) c‖ :=
        opNorm_comp_le _ _
      _ ≤ ‖B - WeightedClock.diagonal U‖ * 1 :=
        mul_le_mul_of_nonneg_left hInputNorm
          (ContinuousLinearMap.opNorm_nonneg (B - WeightedClock.diagonal U))
      _ ≤ δ := by simpa only [mul_one] using hB
  have hCompressed := ODECoherentLCU.successful_compression_error_le c hc U
    (fun _ : ι => (1 : P →L[ℂ] P)) (fun _ : ι => (1 : P →L[ℂ] P))
    (fun _ => by simp only [one_def, adjoint_id, id_comp])
    (B ∘L coefficientInput c) δ hPrepared
  have hBlock : (output E c)† ∘L W ∘L input E c =
      (coefficientOutput c)† ∘L (B ∘L coefficientInput c) := by
    simp only [input, output, B, adjoint_comp, comp_assoc]
  rw [hBlock]
  simpa only [normalizedSum, coefficientOutput,
    one_def, adjoint_id, id_comp, comp_id] using hCompressed

/-- Restoring the coefficient mass multiplies the implementation error by
that mass, and does not alter the physical circuit. -/
theorem scaled_compression_error (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (δ : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ) :
    ‖(ODECoherentLCU.coefficientMass c : ℂ) •
        ((output E c)† ∘L W ∘L input E c) - ∑ i, c i • U i‖ ≤
      ODECoherentLCU.coefficientMass c * δ := by
  have hC : (ODECoherentLCU.coefficientMass c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  have hNormalize : (ODECoherentLCU.coefficientMass c : ℂ) • normalizedSum c U =
      ∑ i, c i • U i := by
    rw [normalizedSum, smul_smul, mul_inv_cancel₀ hC, one_smul]
  calc
    ‖(ODECoherentLCU.coefficientMass c : ℂ) •
        ((output E c)† ∘L W ∘L input E c) - ∑ i, c i • U i‖ =
        ‖(ODECoherentLCU.coefficientMass c : ℂ) •
          ((output E c)† ∘L W ∘L input E c - normalizedSum c U)‖ := by
      rw [smul_sub, hNormalize]
    _ = ODECoherentLCU.coefficientMass c *
        ‖(output E c)† ∘L W ∘L input E c - normalizedSum c U‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.le]
    _ ≤ ODECoherentLCU.coefficientMass c * δ :=
      mul_le_mul_of_nonneg_left (compression_error E c hE hc W U δ hError) hc.le

/-- A separately proved finite-LCHS approximation adds its analytic error. -/
theorem lchs_error (E : BranchSpace ι P →L[ℂ] K) (c : ι → ℂ)
    (hE : E† ∘L E = 1) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (W : K →L[ℂ] K) (U : ι → P →L[ℂ] P) (S : P →L[ℂ] P) (δ ν : ℝ)
    (hError : ‖W ∘L E - E ∘L WeightedClock.diagonal U‖ ≤ δ)
    (hLCHS : ‖(∑ i, c i • U i) - S‖ ≤ ν) :
    ‖(ODECoherentLCU.coefficientMass c : ℂ) •
        ((output E c)† ∘L W ∘L input E c) - S‖ ≤
      ν + ODECoherentLCU.coefficientMass c * δ := by
  calc
    _ ≤ ‖(ODECoherentLCU.coefficientMass c : ℂ) •
          ((output E c)† ∘L W ∘L input E c) - ∑ i, c i • U i‖ +
        ‖(∑ i, c i • U i) - S‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ODECoherentLCU.coefficientMass c * δ + ν :=
      add_le_add (scaled_compression_error E c hE hc W U δ hError) hLCHS
    _ = _ := add_comm _ _

end
end SparseHamiltonian.ODEJointLCU
