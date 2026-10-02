import SparseHamiltonian.ReuseWeights

/-!
# A coherent signed linear combination on a finite Hilbert sum

The input and output maps prepare square-root absolute coefficient weights.
A real sign is placed in the output preparation. The SELECT operator is the
actual diagonal operator on `PiLp 2`; its successful compression is derived
from the coordinate formula, not postulated as a block encoding.
-/

namespace SparseHamiltonian.CoherentLCU

noncomputable section
open scoped BigOperators
open ContinuousLinearMap

variable {ι : Type*} [Fintype ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The phase of a real coefficient, with phase one at zero. -/
def coefficientPhase (a : ℝ) : ℂ := if a < 0 then -1 else 1

@[simp] theorem coefficientPhase_conj (a : ℝ) :
    (starRingEnd ℂ) (coefficientPhase a) = coefficientPhase a := by
  unfold coefficientPhase
  split <;> simp

@[simp] theorem coefficientPhase_sq (a : ℝ) :
    coefficientPhase a * coefficientPhase a = 1 := by
  unfold coefficientPhase
  split <;> norm_num

theorem abs_mul_coefficientPhase (a : ℝ) :
    ((|a| : ℝ) : ℂ) * coefficientPhase a = (a : ℂ) := by
  unfold coefficientPhase
  split_ifs with h
  · rw [abs_of_neg h]
    simp
  · rw [abs_of_nonneg (le_of_not_gt h)]
    simp

/-- Coefficient probabilities for normalization two. -/
def coefficientProbability (a : ι → ℝ) (i : ι) : ℝ := |a i| / 2

omit [Fintype ι] in
theorem coefficientProbability_nonneg (a : ι → ℝ) (i : ι) :
    0 ≤ coefficientProbability a i := div_nonneg (abs_nonneg _) (by norm_num)

theorem coefficientProbability_sum (a : ι → ℝ) (ha : ∑ i, |a i| = 2) :
    ∑ i, coefficientProbability a i = 1 := by
  simp only [coefficientProbability, ← Finset.sum_div, ha]
  norm_num

/-- Coherent input preparation with square-root absolute weights. -/
def inputEmbedding (a : ι → ℝ) : H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  WeightedClock.boundary (coefficientProbability a) (fun _ => 1)

/-- Coherent output preparation also carries the coefficient signs. -/
def outputEmbedding (a : ι → ℝ) : H →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  WeightedClock.boundary (coefficientProbability a)
    (fun i => coefficientPhase (a i) • 1)

/-- Controlled branch selection on the actual finite Hilbert direct sum. -/
def select (U : ι → H →L[ℂ] H) :
    PiLp 2 (fun _ : ι => H) →L[ℂ] PiLp 2 (fun _ : ι => H) :=
  WeightedClock.diagonal U

omit [Fintype ι] [CompleteSpace H] in
@[simp] theorem select_apply (U : ι → H →L[ℂ] H)
    (x : PiLp 2 (fun _ : ι => H)) (i : ι) : select U x i = U i (x i) := rfl

theorem phase_isometry (a : ℝ) :
    ((coefficientPhase a • (1 : H →L[ℂ] H)).adjoint).comp
      (coefficientPhase a • (1 : H →L[ℂ] H)) = 1 := by
  unfold coefficientPhase
  split <;> simp [ContinuousLinearMap.one_def]

theorem inputEmbedding_isometry (a : ι → ℝ) (ha : ∑ i, |a i| = 2) :
    (inputEmbedding (H := H) a).adjoint.comp (inputEmbedding a) = 1 := by
  apply WeightedClock.boundary_isometry
    (coefficientProbability a) (coefficientProbability_nonneg a)
    (coefficientProbability_sum a ha)
  intro i
  simp [ContinuousLinearMap.one_def]

theorem outputEmbedding_isometry (a : ι → ℝ) (ha : ∑ i, |a i| = 2) :
    (outputEmbedding (H := H) a).adjoint.comp (outputEmbedding a) = 1 := by
  exact WeightedClock.boundary_isometry
    (coefficientProbability a) (coefficientProbability_nonneg a)
    (coefficientProbability_sum a ha) _ (fun i => phase_isometry (a i))

theorem select_isometry (U : ι → H →L[ℂ] H)
    (hU : ∀ i, (U i).adjoint.comp (U i) = 1) :
    (select U).adjoint.comp (select U) = 1 :=
  WeightedClock.diagonal_isometry U hU

theorem select_coisometry (U : ι → H →L[ℂ] H)
    (hU : ∀ i, (U i).comp (U i).adjoint = 1) :
    (select U).comp (select U).adjoint = 1 := by
  unfold select
  rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
  simpa only [hU] using (WeightedClock.diagonal_one (V := fun _ : ι => H))

/-- Exact successful compression of the concrete preparation and SELECT maps. -/
theorem successful_compression (a : ι → ℝ) (U : ι → H →L[ℂ] H) :
    (outputEmbedding a).adjoint.comp ((select U).comp (inputEmbedding a)) =
      (2 : ℂ)⁻¹ • ∑ i, (a i : ℂ) • U i := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, outputEmbedding, inputEmbedding,
    select, WeightedClock.boundary_adjoint_apply, WeightedClock.diagonal_apply,
    WeightedClock.boundary_apply, map_smul, map_smulₛₗ, ContinuousLinearMap.one_def,
    coefficientPhase_conj, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply,
    smul_smul, _root_.sum_apply, _root_.smul_apply,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hsqrt : (Real.sqrt (coefficientProbability a i) : ℂ) *
      (Real.sqrt (coefficientProbability a i) : ℂ) =
      (coefficientProbability a i : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (coefficientProbability_nonneg a i)
  have habs := abs_mul_coefficientPhase (a i)
  congr 1
  calc
    _ = ((Real.sqrt (coefficientProbability a i) : ℂ) *
        (Real.sqrt (coefficientProbability a i) : ℂ)) * coefficientPhase (a i) := by ring
    _ = (2 : ℂ)⁻¹ * (a i : ℂ) := by
      rw [hsqrt]
      simp only [coefficientProbability, Complex.ofReal_div, Complex.ofReal_ofNat]
      calc
        ((|a i| : ℝ) : ℂ) / 2 * coefficientPhase (a i) =
            (2 : ℂ)⁻¹ * (((|a i| : ℝ) : ℂ) * coefficientPhase (a i)) := by ring
        _ = _ := by rw [habs]

/-- The full LCU certificate contains actual embeddings and a SELECT operator,
with both SELECT inverse identities and the exact successful compression. -/
theorem coherent_lcu_certificate (a : ι → ℝ) (ha : ∑ i, |a i| = 2)
    (U : ι → H →L[ℂ] H)
    (hUl : ∀ i, (U i).adjoint.comp (U i) = 1)
    (hUr : ∀ i, (U i).comp (U i).adjoint = 1) :
    (inputEmbedding (H := H) a).adjoint.comp (inputEmbedding a) = 1 ∧
    (outputEmbedding (H := H) a).adjoint.comp (outputEmbedding a) = 1 ∧
    (select U).adjoint.comp (select U) = 1 ∧
    (select U).comp (select U).adjoint = 1 ∧
    (outputEmbedding a).adjoint.comp ((select U).comp (inputEmbedding a)) =
      (2 : ℂ)⁻¹ • ∑ i, (a i : ℂ) • U i := by
  exact ⟨inputEmbedding_isometry a ha, outputEmbedding_isometry a ha,
    select_isometry U hUl, select_coisometry U hUr, successful_compression a U⟩

section BranchSpaces

variable {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]

/-- Cross compression permits different coherent input and output preparations. -/
theorem cross_boundary_compression (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (A : ∀ i, V i →L[ℂ] V i) (J K : ∀ i, H →L[ℂ] V i) :
    (WeightedClock.boundary p K).adjoint.comp
        ((WeightedClock.diagonal A).comp (WeightedClock.boundary p J)) =
      ∑ i, (p i : ℂ) • ((K i).adjoint.comp ((A i).comp (J i))) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, WeightedClock.boundary_adjoint_apply,
    WeightedClock.diagonal_apply, WeightedClock.boundary_apply, map_smul,
    smul_smul, _root_.sum_apply, _root_.smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact_mod_cast Real.mul_self_sqrt (hp i)

/-- Input preparation into branches whose private spaces may differ. -/
def branchInput (a : ι → ℝ) (J : ∀ i, H →L[ℂ] V i) : H →L[ℂ] PiLp 2 V :=
  WeightedClock.boundary (coefficientProbability a) J

/-- Output preparation into the same varying branch spaces with real signs. -/
def branchOutput (a : ι → ℝ) (J : ∀ i, H →L[ℂ] V i) : H →L[ℂ] PiLp 2 V :=
  WeightedClock.boundary (coefficientProbability a)
    (fun i => coefficientPhase (a i) • J i)

omit [Fintype ι] in
theorem signed_injection_isometry (a : ℝ) (J : H →L[ℂ] V i)
    (hJ : J.adjoint.comp J = 1) :
    (coefficientPhase a • J).adjoint.comp (coefficientPhase a • J) = 1 := by
  simp only [map_smulₛₗ, coefficientPhase_conj, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, coefficientPhase_sq, hJ, one_smul]

theorem branchInput_isometry (a : ι → ℝ) (ha : ∑ i, |a i| = 2)
    (J : ∀ i, H →L[ℂ] V i) (hJ : ∀ i, (J i).adjoint.comp (J i) = 1) :
    (branchInput a J).adjoint.comp (branchInput a J) = 1 :=
  WeightedClock.boundary_isometry (coefficientProbability a)
    (coefficientProbability_nonneg a) (coefficientProbability_sum a ha) J hJ

theorem branchOutput_isometry (a : ι → ℝ) (ha : ∑ i, |a i| = 2)
    (J : ∀ i, H →L[ℂ] V i) (hJ : ∀ i, (J i).adjoint.comp (J i) = 1) :
    (branchOutput a J).adjoint.comp (branchOutput a J) = 1 :=
  WeightedClock.boundary_isometry (coefficientProbability a)
    (coefficientProbability_nonneg a) (coefficientProbability_sum a ha) _
    (fun i => signed_injection_isometry (a i) (J i) (hJ i))

/-- The successful branch block is derived for arbitrary branch Hilbert spaces.
In particular, reuse circuits with different lengths need no common padding. -/
theorem branch_successful_compression (a : ι → ℝ)
    (U : ∀ i, V i →L[ℂ] V i) (J : ∀ i, H →L[ℂ] V i) :
    (branchOutput a J).adjoint.comp
        ((WeightedClock.diagonal U).comp (branchInput a J)) =
      (2 : ℂ)⁻¹ • ∑ i, (a i : ℂ) • ((J i).adjoint.comp ((U i).comp (J i))) := by
  unfold branchOutput branchInput
  rw [cross_boundary_compression _ (coefficientProbability_nonneg a)]
  simp only [map_smulₛₗ, coefficientPhase_conj, ContinuousLinearMap.smul_comp,
    smul_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  simp only [coefficientProbability, Complex.ofReal_div, Complex.ofReal_ofNat]
  calc
    ((|a i| : ℝ) : ℂ) / 2 * coefficientPhase (a i) =
        (2 : ℂ)⁻¹ * (((|a i| : ℝ) : ℂ) * coefficientPhase (a i)) := by ring
    _ = _ := by rw [abs_mul_coefficientPhase]

/-- Complete coherent LCU certificate with varying branch private dimensions. -/
theorem branch_lcu_certificate (a : ι → ℝ) (ha : ∑ i, |a i| = 2)
    (U : ∀ i, V i →L[ℂ] V i) (J : ∀ i, H →L[ℂ] V i)
    (hJ : ∀ i, (J i).adjoint.comp (J i) = 1)
    (hUl : ∀ i, (U i).adjoint.comp (U i) = 1)
    (hUr : ∀ i, (U i).comp (U i).adjoint = 1) :
    (branchInput a J).adjoint.comp (branchInput a J) = 1 ∧
    (branchOutput a J).adjoint.comp (branchOutput a J) = 1 ∧
    (WeightedClock.diagonal U).adjoint.comp (WeightedClock.diagonal U) = 1 ∧
    (WeightedClock.diagonal U).comp (WeightedClock.diagonal U).adjoint = 1 ∧
    (branchOutput a J).adjoint.comp
        ((WeightedClock.diagonal U).comp (branchInput a J)) =
      (2 : ℂ)⁻¹ • ∑ i, (a i : ℂ) • ((J i).adjoint.comp ((U i).comp (J i))) := by
  refine ⟨branchInput_isometry a ha J hJ, branchOutput_isometry a ha J hJ,
    WeightedClock.diagonal_isometry U hUl, ?_, branch_successful_compression a U J⟩
  rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
  simpa only [hUr] using (WeightedClock.diagonal_one (V := V))

end BranchSpaces

section Padding

/-- Two identity branches with opposite coefficients fill unused absolute mass. -/
def paddedCoefficient (a : ι → ℝ) : ι ⊕ Bool → ℝ
  | .inl i => a i
  | .inr false => (2 - ∑ i, |a i|) / 2
  | .inr true => -((2 - ∑ i, |a i|) / 2)

/-- Both padding branches select the identity and therefore cancel exactly. -/
def paddedOperator (U : ι → H →L[ℂ] H) : ι ⊕ Bool → H →L[ℂ] H
  | .inl i => U i
  | .inr _ => 1

theorem padded_absolute_mass_two (a : ι → ℝ) (ha : ∑ i, |a i| ≤ 2) :
    ∑ i, |paddedCoefficient a i| = 2 := by
  have hδ : 0 ≤ (2 - ∑ i, |a i|) / 2 := by linarith
  simp only [Fintype.sum_sum_type, paddedCoefficient, Fintype.sum_bool, abs_neg,
    abs_of_nonneg hδ]
  ring

omit [CompleteSpace H] in
theorem padded_weighted_sum (a : ι → ℝ) (U : ι → H →L[ℂ] H) :
    ∑ i, (paddedCoefficient a i : ℂ) • paddedOperator U i =
      ∑ i, (a i : ℂ) • U i := by
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, paddedCoefficient,
    paddedOperator, Complex.ofReal_neg, neg_smul, neg_add_cancel, add_zero]

/-- Padding produces a genuine normalization-two LCU for any smaller mass. -/
theorem subnormalized_lcu_certificate (a : ι → ℝ) (ha : ∑ i, |a i| ≤ 2)
    (U : ι → H →L[ℂ] H)
    (hUl : ∀ i, (U i).adjoint.comp (U i) = 1)
    (hUr : ∀ i, (U i).comp (U i).adjoint = 1) :
    (inputEmbedding (H := H) (paddedCoefficient a)).adjoint.comp
        (inputEmbedding (paddedCoefficient a)) = 1 ∧
    (outputEmbedding (H := H) (paddedCoefficient a)).adjoint.comp
        (outputEmbedding (paddedCoefficient a)) = 1 ∧
    (select (paddedOperator U)).adjoint.comp (select (paddedOperator U)) = 1 ∧
    (select (paddedOperator U)).comp (select (paddedOperator U)).adjoint = 1 ∧
    (outputEmbedding (paddedCoefficient a)).adjoint.comp
        ((select (paddedOperator U)).comp (inputEmbedding (paddedCoefficient a))) =
      (2 : ℂ)⁻¹ • ∑ i, (a i : ℂ) • U i := by
  have hPl : ∀ i, (paddedOperator U i).adjoint.comp (paddedOperator U i) = 1 := by
    intro i
    cases i with
    | inl i => exact hUl i
    | inr b => simp [paddedOperator, ContinuousLinearMap.one_def]
  have hPr : ∀ i, (paddedOperator U i).comp (paddedOperator U i).adjoint = 1 := by
    intro i
    cases i with
    | inl i => exact hUr i
    | inr b => simp [paddedOperator, ContinuousLinearMap.one_def]
  simpa only [padded_weighted_sum] using
    coherent_lcu_certificate (paddedCoefficient a) (padded_absolute_mass_two a ha)
      (paddedOperator U) hPl hPr

end Padding

end
end SparseHamiltonian.CoherentLCU
