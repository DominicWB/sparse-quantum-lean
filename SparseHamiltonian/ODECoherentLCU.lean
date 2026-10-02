import SparseHamiltonian.ODEStateNormalization

/-!
# Complex-coefficient coherent linear combinations for ODE solvers

Finite LCHS quadrature uses complex coefficients. This module constructs its
input and output preparations, proves that both are isometries, and derives
the successful block of the actual diagonal operator. Branch workspaces may
vary with the quadrature index. This operator construction does not grant a
free native-query implementation of SELECT; such an implementation must be
proved separately.
-/

namespace SparseHamiltonian.ODECoherentLCU

noncomputable section
open scoped BigOperators ComplexConjugate
open ContinuousLinearMap

variable {ι : Type*} [Fintype ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]

/-- Absolute coefficient mass, the normalization of the LCU block. -/
def coefficientMass (c : ι → ℂ) : ℝ := ∑ i, ‖c i‖

theorem coefficientMass_nonneg (c : ι → ℂ) : 0 ≤ coefficientMass c :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Unit-modulus coefficient phase, with phase one at zero. -/
def coefficientPhase (z : ℂ) : ℂ := if z = 0 then 1 else z / (‖z‖ : ℂ)

omit [Fintype ι] in
@[simp] theorem coefficientPhase_zero : coefficientPhase 0 = 1 := by
  simp [coefficientPhase]

omit [Fintype ι] in
theorem norm_coefficientPhase (z : ℂ) : ‖coefficientPhase z‖ = 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [coefficientPhase, if_neg hz, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    exact div_self (norm_ne_zero_iff.mpr hz)

omit [Fintype ι] in
theorem conjugate_phase_mul (z : ℂ) :
    (starRingEnd ℂ) (coefficientPhase z) * coefficientPhase z = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
    norm_coefficientPhase]
  norm_num

omit [Fintype ι] in
theorem phase_mul_conjugate (z : ℂ) :
    coefficientPhase z * (starRingEnd ℂ) (coefficientPhase z) = 1 := by
  rw [mul_comm]
  exact conjugate_phase_mul z

omit [Fintype ι] in
theorem norm_mul_coefficientPhase (z : ℂ) :
    (‖z‖ : ℂ) * coefficientPhase z = z := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [coefficientPhase, if_neg hz]
    have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hz)
    field_simp

/-- Probabilities are normalized absolute coefficient magnitudes. -/
def coefficientProbability (c : ι → ℂ) (i : ι) : ℝ :=
  ‖c i‖ / coefficientMass c

theorem coefficientProbability_nonneg (c : ι → ℂ) (i : ι) :
    0 ≤ coefficientProbability c i :=
  div_nonneg (norm_nonneg _) (coefficientMass_nonneg c)

theorem coefficientProbability_sum (c : ι → ℂ) (hc : 0 < coefficientMass c) :
    ∑ i, coefficientProbability c i = 1 := by
  simp only [coefficientProbability, ← Finset.sum_div]
  change coefficientMass c / coefficientMass c = 1
  exact div_self hc.ne'

/-- The input places square-root absolute weights on the branch encodings. -/
def inputEmbedding (c : ι → ℂ) (J : ∀ i, H →L[ℂ] V i) : H →L[ℂ] PiLp 2 V :=
  WeightedClock.boundary (coefficientProbability c) J

/-- The output includes conjugate phases, so its adjoint supplies the desired
complex coefficients without conjugating them. -/
def outputEmbedding (c : ι → ℂ) (K : ∀ i, H →L[ℂ] V i) : H →L[ℂ] PiLp 2 V :=
  WeightedClock.boundary (coefficientProbability c)
    (fun i => (starRingEnd ℂ) (coefficientPhase (c i)) • K i)

omit [Fintype ι] in
theorem phased_injection_isometry (z : ℂ) (J : H →L[ℂ] V i)
    (hJ : J.adjoint.comp J = 1) :
    (((starRingEnd ℂ) (coefficientPhase z)) • J).adjoint.comp
      (((starRingEnd ℂ) (coefficientPhase z)) • J) = 1 := by
  simp only [map_smulₛₗ, starRingEnd_self_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, conjugate_phase_mul, hJ, one_smul]

theorem inputEmbedding_isometry (c : ι → ℂ) (hc : 0 < coefficientMass c)
    (J : ∀ i, H →L[ℂ] V i) (hJ : ∀ i, (J i).adjoint.comp (J i) = 1) :
    (inputEmbedding c J).adjoint.comp (inputEmbedding c J) = 1 :=
  WeightedClock.boundary_isometry _ (coefficientProbability_nonneg c)
    (coefficientProbability_sum c hc) J hJ

theorem outputEmbedding_isometry (c : ι → ℂ) (hc : 0 < coefficientMass c)
    (K : ∀ i, H →L[ℂ] V i) (hK : ∀ i, (K i).adjoint.comp (K i) = 1) :
    (outputEmbedding c K).adjoint.comp (outputEmbedding c K) = 1 :=
  WeightedClock.boundary_isometry _ (coefficientProbability_nonneg c)
    (coefficientProbability_sum c hc) _
    (fun i => phased_injection_isometry (c i) (K i) (hK i))

/-- Exact block identity for arbitrary complex coefficients and independent
input and output branch preparations. No block-encoding premise is used. -/
theorem successful_compression (c : ι → ℂ)
    (U : ∀ i, V i →L[ℂ] V i) (J K : ∀ i, H →L[ℂ] V i) :
    (outputEmbedding c K).adjoint.comp
        ((WeightedClock.diagonal U).comp (inputEmbedding c J)) =
      (coefficientMass c : ℂ)⁻¹ •
        ∑ i, c i • ((K i).adjoint.comp ((U i).comp (J i))) := by
  unfold outputEmbedding inputEmbedding
  rw [CoherentLCU.cross_boundary_compression _ (coefficientProbability_nonneg c)]
  simp only [map_smulₛₗ, starRingEnd_self_apply, ContinuousLinearMap.smul_comp,
    smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [coefficientProbability, Complex.ofReal_div]
  calc
    (‖c i‖ : ℂ) / (coefficientMass c : ℂ) * coefficientPhase (c i) =
        (coefficientMass c : ℂ)⁻¹ * ((‖c i‖ : ℂ) * coefficientPhase (c i)) := by ring
    _ = _ := by rw [norm_mul_coefficientPhase]

/-- A family of genuine unitary branch operators has a genuine unitary SELECT. -/
theorem select_unitary (U : ∀ i, V i →L[ℂ] V i)
    (hUl : ∀ i, (U i).adjoint.comp (U i) = 1)
    (hUr : ∀ i, (U i).comp (U i).adjoint = 1) :
    (WeightedClock.diagonal U).adjoint.comp (WeightedClock.diagonal U) = 1 ∧
    (WeightedClock.diagonal U).comp (WeightedClock.diagonal U).adjoint = 1 := by
  refine ⟨WeightedClock.diagonal_isometry U hUl, ?_⟩
  rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
  simpa only [hUr] using (WeightedClock.diagonal_one (V := V))

/-- Full operator-level certificate for the finite complex LCU. -/
theorem coherent_lcu_certificate (c : ι → ℂ) (hc : 0 < coefficientMass c)
    (U : ∀ i, V i →L[ℂ] V i) (J K : ∀ i, H →L[ℂ] V i)
    (hJ : ∀ i, (J i).adjoint.comp (J i) = 1)
    (hK : ∀ i, (K i).adjoint.comp (K i) = 1)
    (hUl : ∀ i, (U i).adjoint.comp (U i) = 1)
    (hUr : ∀ i, (U i).comp (U i).adjoint = 1) :
    (inputEmbedding c J).adjoint.comp (inputEmbedding c J) = 1 ∧
    (outputEmbedding c K).adjoint.comp (outputEmbedding c K) = 1 ∧
    (WeightedClock.diagonal U).adjoint.comp (WeightedClock.diagonal U) = 1 ∧
    (WeightedClock.diagonal U).comp (WeightedClock.diagonal U).adjoint = 1 ∧
    (outputEmbedding c K).adjoint.comp
        ((WeightedClock.diagonal U).comp (inputEmbedding c J)) =
      (coefficientMass c : ℂ)⁻¹ •
        ∑ i, c i • ((K i).adjoint.comp ((U i).comp (J i))) :=
  ⟨inputEmbedding_isometry c hc J hJ, outputEmbedding_isometry c hc K hK,
    (select_unitary U hUl hUr).1, (select_unitary U hUl hUr).2,
    successful_compression c U J K⟩

section Compression

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

omit [Fintype ι] in
/-- An isometric encoding is a contraction, also on the trivial public space. -/
theorem isometry_norm_le_one (K : H →L[ℂ] B) (hK : K.adjoint.comp K = 1) :
    ‖K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [K.norm_map_iff_adjoint_comp_self.mpr hK, one_mul]

omit [Fintype ι] in
/-- Compression by an isometric output encoding does not amplify a
full-output approximation error. -/
theorem compression_error (K : H →L[ℂ] B) (hK : K.adjoint.comp K = 1)
    (P : H →L[ℂ] B) (U : H →L[ℂ] H) (δ : ℝ)
    (hP : ‖P - K.comp U‖ ≤ δ) : ‖K.adjoint.comp P - U‖ ≤ δ := by
  have heq : K.adjoint.comp (P - K.comp U) = K.adjoint.comp P - U := by
    rw [ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.comp_assoc, hK]
    simp only [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  rw [← heq]
  calc
    _ ≤ ‖K.adjoint‖ * ‖P - K.comp U‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖P - K.comp U‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [adjoint.norm_map]
      exact isometry_norm_le_one K hK
    _ ≤ δ := by simpa only [one_mul] using hP

omit [Fintype ι] in
/-- Branch form of `compression_error`, convenient for actual implemented
branch operators with their separate input and output isometries. -/
theorem branch_compression_error (J K : H →L[ℂ] B) (hK : K.adjoint.comp K = 1)
    (W : B →L[ℂ] B) (U : H →L[ℂ] H) (δ : ℝ)
    (hW : ‖W.comp J - K.comp U‖ ≤ δ) :
    ‖K.adjoint.comp (W.comp J) - U‖ ≤ δ :=
  compression_error K hK (W.comp J) U δ hW

end Compression

/-- Isometric coherent output preparation has operator norm at most one,
including the zero-dimensional public-space case. -/
theorem outputEmbedding_norm_le_one (c : ι → ℂ) (hc : 0 < coefficientMass c)
    (K : ∀ i, H →L[ℂ] V i) (hK : ∀ i, (K i).adjoint.comp (K i) = 1) :
    ‖outputEmbedding c K‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [(outputEmbedding c K).norm_map_iff_adjoint_comp_self.mpr
    (outputEmbedding_isometry c hc K hK), one_mul]

/-- Passing to the successful block cannot increase a full-output error.
The map `P` may be the actual program followed by its fixed input encoding. -/
theorem full_output_compression_error_le (c : ι → ℂ) (hc : 0 < coefficientMass c)
    (U : ∀ i, V i →L[ℂ] V i) (J K : ∀ i, H →L[ℂ] V i)
    (hK : ∀ i, (K i).adjoint.comp (K i) = 1)
    (P : H →L[ℂ] PiLp 2 V) :
    ‖(outputEmbedding c K).adjoint.comp P -
      (coefficientMass c : ℂ)⁻¹ •
        ∑ i, c i • ((K i).adjoint.comp ((U i).comp (J i)))‖ ≤
      ‖P - (WeightedClock.diagonal U).comp (inputEmbedding c J)‖ := by
  rw [← successful_compression c U J K, ← ContinuousLinearMap.comp_sub]
  calc
    _ ≤ ‖(outputEmbedding c K).adjoint‖ *
        ‖P - (WeightedClock.diagonal U).comp (inputEmbedding c J)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖P - (WeightedClock.diagonal U).comp (inputEmbedding c J)‖ := by
      have hOut : ‖(outputEmbedding c K).adjoint‖ ≤ 1 := by
        rw [adjoint.norm_map]
        exact outputEmbedding_norm_le_one c hc K hK
      have hn : 0 ≤ ‖P - (WeightedClock.diagonal U).comp (inputEmbedding c J)‖ :=
        ContinuousLinearMap.opNorm_nonneg _
      nlinarith
    _ = _ := one_mul _

/-- A certified full-output implementation of SELECT yields the advertised
complex LCU block with the same error tolerance. -/
theorem successful_compression_error_le (c : ι → ℂ) (hc : 0 < coefficientMass c)
    (U : ∀ i, V i →L[ℂ] V i) (J K : ∀ i, H →L[ℂ] V i)
    (hK : ∀ i, (K i).adjoint.comp (K i) = 1)
    (P : H →L[ℂ] PiLp 2 V) (δ : ℝ)
    (hP : ‖P - (WeightedClock.diagonal U).comp (inputEmbedding c J)‖ ≤ δ) :
    ‖(outputEmbedding c K).adjoint.comp P -
      (coefficientMass c : ℂ)⁻¹ •
        ∑ i, c i • ((K i).adjoint.comp ((U i).comp (J i)))‖ ≤ δ :=
  (full_output_compression_error_le c hc U J K hK P).trans hP

end
end SparseHamiltonian.ODECoherentLCU
