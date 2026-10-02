import SparseHamiltonian.AmplifiedBandPrecision

/-!
# Resources and total approximation of the actual native band family

The family below contains constructed native programs, all acting through one
oracle family and one clean input. Its complete weighted clock budget and
Hamiltonian perturbation are derived from their counted implementations.
-/
namespace SparseHamiltonian.ActualAmplifiedBandResources

noncomputable section
open ContinuousLinearMap ActualAmplifiedBands AmplifiedBandBudget
open NativeSparseBlockEncoding (Data)
open scoped BigOperators InnerProduct
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s b : ℕ} {η δ : ℝ}

/-- All bands and the retained tail form one indexed family. -/
def termNormalization {D : Data X n Z s} (F : Family D η b δ) : Fin (b + 1) → ℝ :=
  Fin.lastCases (BandCost.tailNormalization s η b) F.normalization

/-- Every indexed term retains the original physical oracle family. -/
def termProgram {D : Data X n Z s} (F : Family D η b δ) :
    Fin (b + 1) → MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D) :=
  Fin.lastCases F.tailProgram F.program

/-- The common finite normalization sum of the actual encoded terms. -/
def totalNormalization {D : Data X n Z s} (F : Family D η b δ) : ℝ :=
  ∑ j, termNormalization F j

/-- Actual weighted length, including both fixed links of each program clock. -/
def weightedLength {D : Data X n Z s} (F : Family D η b δ) : ℝ :=
  ∑ j, termNormalization F j * (((termProgram F j).count + 2 : ℕ) : ℝ)

/-- Explicit public integer upper bound, independent of the matrix input. -/
def clockBound (s : ℕ) (δ : ℝ) : ℕ := ⌈26 * precisionFactor δ * Real.sqrt s⌉₊

@[simp] theorem totalNormalization_eq {D : Data X n Z s} (F : Family D η b δ) :
    totalNormalization F = (∑ j, F.normalization j) + BandCost.tailNormalization s η b := by
  simp [totalNormalization, termNormalization, Fin.sum_univ_castSucc]

@[simp] theorem weightedLength_eq {D : Data X n Z s} (F : Family D η b δ) :
    weightedLength F = (∑ j, F.normalization j * (((F.program j).count + 2 : ℕ) : ℝ)) +
      8 * BandCost.tailNormalization s η b := by
  norm_num [weightedLength, termNormalization, termProgram, Fin.sum_univ_castSucc,
    F.tail_count, mul_comm]

theorem termNormalization_pos {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η)
    (j : Fin (b + 1)) : 0 < termNormalization F j := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp only [termNormalization, Fin.lastCases_last]
    unfold BandCost.tailNormalization
    have hs : (0 : ℝ) < s := Nat.cast_pos.mpr D.slots_pos
    positivity
  · simpa only [termNormalization, Fin.lastCases_castSucc] using F.normalization_pos i

theorem totalNormalization_pos {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η) :
    0 < totalNormalization F := by
  unfold totalNormalization
  exact Finset.sum_pos (fun j _ => termNormalization_pos F hη j) Finset.univ_nonempty

theorem term_unitary {D : Data X n Z s} (F : Family D η b δ) (j : Fin (b + 1)) (x : X) :
    OracleCircuit.IsUnitary ((termProgram F j).eval x) := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [termProgram, Fin.lastCases_last] using F.tail_unitary x
  · simpa only [termProgram, Fin.lastCases_castSucc] using F.unitary i x

theorem term_selfadjoint {D : Data X n Z s} (F : Family D η b δ)
    (j : Fin (b + 1)) (x : X) :
    (block D (termProgram F j) x)† = block D (termProgram F j) x := by
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [termProgram, Fin.lastCases_last] using F.tail_selfadjoint x
  · simpa only [termProgram, Fin.lastCases_castSucc] using F.selfadjoint i x

/-- Every term, including the exact tail, satisfies the public integer clock bound. -/
theorem term_count_le_clockBound {D : Data X n Z s} (F : Family D η b δ)
    (hη : 0 < η) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (j : Fin (b + 1)) :
    (termProgram F j).count + 2 ≤ clockBound s δ := by
  have h : (((termProgram F j).count + 2 : ℕ) : ℝ) ≤
      26 * precisionFactor δ * Real.sqrt s := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [termProgram, Fin.lastCases_last, F.tail_count, Nat.reduceAdd, Nat.cast_ofNat] using
        AmplifiedBandBudget.tail_clock_count_le s δ (one_le_s D) hδ hδ1
    · simpa only [termProgram, Fin.lastCases_castSucc] using
        AmplifiedBandBudget.max_clock_count_le s η δ (one_le_s D) hη hδ hδ1
          i (F.program i).count (F.count_lt i)
  exact_mod_cast h.trans (Nat.le_ceil _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Rounding the common clock bound adds only one to its absolute constant. -/
theorem clockBound_le (D : Data X n Z s) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (clockBound s δ : ℝ) ≤ 27 * precisionFactor δ * Real.sqrt s := by
  have hL := precisionFactor_ge_one δ hδ hδ1
  have hs := Real.one_le_sqrt.mpr (one_le_s D)
  have hp := one_le_mul_of_one_le_of_one_le hL hs
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 26 * precisionFactor δ * Real.sqrt s by positivity)
  change (clockBound s δ : ℝ) < _ at hc
  nlinarith

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem clockBound_pos (D : Data X n Z s) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < clockBound s δ := by
  have hL := precisionFactor_ge_one δ hδ hδ1
  have hs := Real.one_le_sqrt.mpr (one_le_s D)
  unfold clockBound
  apply Nat.ceil_pos.mpr
  positivity

/-- Actual normalization sum, with no hypothetical encoding parameters. -/
theorem totalNormalization_le {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    totalNormalization F ≤ 5120 * η * Real.sqrt s := by
  rw [totalNormalization_eq]
  exact AmplifiedBandBudget.normalization_sum_le s η (one_le_s D) hη b
    hbLower hbUpper F.normalization F.normalization_upper

/-- Weighted query complexity of the complete actual native family. -/
theorem weightedLength_le {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b) :
    weightedLength F ≤ 26624 * precisionFactor δ *
      ((Real.sqrt 2 * (b : ℝ) + 1) * η * Real.sqrt s) := by
  rw [weightedLength_eq]
  exact AmplifiedBandBudget.weighted_sum_le s η δ (one_le_s D) hη hδ hδ1 b hbLower
    F.normalization (fun j => (F.program j).count) F.normalization_upper F.count_lt

/-- The actual sum of rescaled compressed native circuits. -/
def approximateHamiltonian {D : Data X n Z s} (F : Family D η b δ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ∑ j, (termNormalization F j : ℂ) • block D (termProgram F j) x

/-- The exact tail contributes no approximation error. -/
theorem approximateHamiltonian_eq {D : Data X n Z s} (F : Family D η b δ) (x : X) :
    approximateHamiltonian F x =
      (∑ j, (F.normalization j : ℂ) • block D (F.program j) x) + tailOperator D η b x := by
  simp only [approximateHamiltonian, Fin.sum_univ_castSucc, termNormalization,
    termProgram, Fin.lastCases_castSucc, Fin.lastCases_last, F.tail_exact]

/-- The combined approximate Hamiltonian is exactly Hermitian. -/
theorem approximateHamiltonian_selfadjoint {D : Data X n Z s} (F : Family D η b δ) (x : X) :
    star (approximateHamiltonian F x) = approximateHamiltonian F x := by
  unfold approximateHamiltonian
  rw [star_eq_adjoint, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smulₛₗ]
  have hc : star (termNormalization F j : ℂ) = (termNormalization F j : ℂ) := by
    exact Complex.conj_ofReal _
  change star (termNormalization F j : ℂ) • (block D (termProgram F j) x)† = _
  rw [hc, term_selfadjoint]

/-- Per-band operator errors sum with the normalization budget, not the dimension. -/
theorem approximateHamiltonian_error {D : Data X n Z s} (F : Family D η b δ)
    (hη : 0 < η) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) (x : X) :
    ‖approximateHamiltonian F x - SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤
      15 * η * Real.sqrt s * δ := by
  rw [approximateHamiltonian_eq, ← operator_decomposition D η hη.le hRow b x,
    add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin b, ‖(F.normalization j : ℂ) • block D (F.program j) x - bandOperator D η j x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin b, BandCost.normalization s η j * (2 * δ + δ ^ 2) :=
      Finset.sum_le_sum (fun j _ => F.error j x)
    _ = ∑ j ∈ Finset.range b, BandCost.normalization s η j * (2 * δ + δ ^ 2) :=
      Fin.sum_univ_eq_sum_range (fun j => BandCost.normalization s η j * (2 * δ + δ ^ 2)) b
    _ ≤ _ := AmplifiedBandPrecision.band_error_sum_le s η δ (one_le_s D) hη hδ hδ1 b hbLower hbUpper

/-- The scheduled family incurs at most one quarter of the final evolution error. -/
theorem scheduled_evolution_error {D : Data X n Z s} (η t ε : ℝ)
    (F : Family D η b (AmplifiedBandPrecision.precision s η t ε))
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) (x : X) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • approximateHamiltonian F x) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε / 4 := by
  have hδ := AmplifiedBandPrecision.precision_pos s η t ε hη.le hε
  have hδ1 := AmplifiedBandPrecision.precision_le_one s η t ε hη.le hε1
  exact ((HamiltonianStability.evolution_error_le _ _ t
    (approximateHamiltonian_selfadjoint F x) (SparseValuePrecision.matrixOperator_star_eq _ (hH x))).trans
      (mul_le_mul_of_nonneg_left
        (approximateHamiltonian_error F hη hδ.le hδ1 hRow hbLower hbUpper x) (abs_nonneg t))).trans
      (AmplifiedBandPrecision.precision_time_error s η t ε hη.le hε)


omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The publicly scheduled integer bound has one logarithmic factor. -/
theorem scheduled_clockBound_le (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (clockBound s (AmplifiedBandPrecision.precision s η t ε) : ℝ) ≤
      27 * Real.sqrt s * AmplifiedBandPrecision.logBudget s η t ε := by
  have hδ := AmplifiedBandPrecision.precision_pos s η t ε hη hε
  have hδ1 := AmplifiedBandPrecision.precision_le_one s η t ε hη hε1
  have hL := AmplifiedBandPrecision.precisionFactor_le_logBudget s η t ε (one_le_s D) hη hε hε1
  have h := clockBound_le D _ hδ hδ1
  exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg (s : ℝ))])

/-- Actual weighted cost has the two stated logarithmic factors and square-root sparsity. -/
theorem scheduled_weightedLength_le {D : Data X n Z s} (η t ε : ℝ)
    (F : Family D η b (AmplifiedBandPrecision.precision s η t ε))
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    weightedLength F ≤ 53248 * η * Real.sqrt s * (AmplifiedBandPrecision.logBudget s η t ε) ^ 2 := by
  let B := AmplifiedBandPrecision.logBudget s η t ε
  let δ := AmplifiedBandPrecision.precision s η t ε
  have hδ := AmplifiedBandPrecision.precision_pos s η t ε hη.le hε
  have hδ1 := AmplifiedBandPrecision.precision_le_one s η t ε hη.le hε1
  have hL : precisionFactor δ ≤ B :=
    AmplifiedBandPrecision.precisionFactor_le_logBudget s η t ε (one_le_s D) hη.le hε hε1
  have hB : 1 ≤ B := AmplifiedBandPrecision.logBudget_ge_one s η t ε (one_le_s D) hη.le hε hε1
  have hb : (b : ℝ) + 1 ≤ B :=
    AmplifiedBandPrecision.band_count_le_logBudget s η t ε (one_le_s D) hη.le hε hε1 b hbUpper
  have hroot : Real.sqrt 2 ≤ 2 := by apply Real.sqrt_le_iff.mpr; norm_num
  have hb' : Real.sqrt 2 * (b : ℝ) + 1 ≤ 2 * B := by
    nlinarith [mul_le_mul_of_nonneg_right hroot (Nat.cast_nonneg b)]
  have h := weightedLength_le F hη hδ hδ1 hbLower
  calc
    _ ≤ 26624 * precisionFactor δ * ((Real.sqrt 2 * (b : ℝ) + 1) * η * Real.sqrt s) := h
    _ ≤ 26624 * B * ((2 * B) * η * Real.sqrt s) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hL (by norm_num)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb' hη.le) (Real.sqrt_nonneg _)
      · positivity
      · positivity
    _ = _ := by dsimp [B]; ring

end
end SparseHamiltonian.ActualAmplifiedBandResources
