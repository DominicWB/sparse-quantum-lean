import SparseHamiltonian.SparseSpectralEnergy

/-!
# Actual native sparse Hamiltonian simulation

This module assembles the constructed amplified bands, their native Hermitian
dilations, unequal distributed clocks and the complete smoothing circuit.
The physical program uses only original row, column and value primitives with
spectator registers. The full-output approximation includes the band errors.
-/
namespace SparseHamiltonian.NativeSparseSimulation
noncomputable section
open ContinuousLinearMap OracleCircuit ActualAmplifiedBands ActualAmplifiedBandResources
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2500000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z]
  [AddCommGroup Z] [DecidableEq Z] {s b : ℕ} {η δ : ℝ}
open NativeSparseBlockEncoding (Data)

/-- The weighted clock average of the actual reflected band programs. -/
def averageLength {D : Data X n Z s} (F : Family D η b δ) : ℝ :=
  MultiWeightedProgramClockBounds.averageLength (ActualDilatedBands.weights F)
    (ActualDilatedBands.program F)

/-- A public maximum length that includes the genuine sixfold native dilation. -/
def maximumLength (s : ℕ) (δ : ℝ) : ℝ := 6 * (clockBound s δ : ℝ)

/-- Complete finite physical workspace for the public simulation schedule. -/
abbrev Physical {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ) :=
  NativeMaskedOracle.Physical
    (ActiveRegisterLayout.Label
      (NativeHeterogeneousActiveClock.Slot (ActualDilatedBands.oracle D) (ActualDilatedBands.program F))
      (TimeSchedule.steps (t * totalNormalization F) (ε / 4 / 3))
      (NativeWeightedSimulation.scheduleDegree (t * totalNormalization F)
        (maximumLength s δ) (averageLength F) (ε / 4)))
    (ActualDilatedBands.Basis n Z)

/-- The actual native query family on the scheduled simulation workspace. -/
abbrev oracle {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ) :
    NativeSparseBlockEncoding.Query → X → Physical F t ε →L[ℂ] Physical F t ε :=
  NativeWeightedSimulation.evolutionOracle (ActualDilatedBands.oracle D)
    (ActualDilatedBands.program F) (t * totalNormalization F) (maximumLength s δ)
    (averageLength F) (ε / 4)

/-- Fixed physical input for the constructed native circuit. -/
def input {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical F t ε :=
  NativeWeightedSimulation.simulationInput (ActualDilatedBands.oracle D)
    (ActualDilatedBands.program F) (ActualDilatedBands.inputIsometry D)
    (ActualDilatedBands.cleanBasis D) (t * totalNormalization F) (maximumLength s δ)
    (averageLength F) (ε / 4)

/-- Fixed physical output, including the complete ancillary state. -/
def output {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical F t ε :=
  NativeWeightedSimulation.simulationOutput (ActualDilatedBands.oracle D)
    (ActualDilatedBands.program F) (ActualDilatedBands.inputIsometry D)
    (ActualDilatedBands.cleanBasis D) (t * totalNormalization F) (maximumLength s δ)
    (averageLength F) (ε / 4)

/-- The true weighted-time budget, before its square-root-sparsity bound. -/
def weightedTime {D : Data X n Z s} (F : Family D η b δ) (t : ℝ) : ℝ :=
  (t * totalNormalization F) * averageLength F

/-- Full native simulation with every implementation premise discharged.
The only family input is the already constructed finite magnitude-band family;
its approximation error and all native reflection/clock overheads are included. -/
theorem family_simulation (D : Data X n Z s) (η t ε : ℝ)
    (F : Family D η b (AmplifiedBandPrecision.precision s η t ε))
    (hη : 0 < η) (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    ∃ p : MultiOracleCircuit.Program (K := Physical F t ε) (oracle F t ε),
      (p.count : ℝ) ≤ 6912 * (weightedTime F t +
        maximumLength s (AmplifiedBandPrecision.precision s η t ε) *
          (1 + Real.log (3 * (maximumLength s (AmplifiedBandPrecision.precision s η t ε) +
            weightedTime F t + 2) / (ε / 4)))) ∧
      (input F t ε)† ∘L input F t ε = 1 ∧
      (output F t ε)† ∘L output F t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input F t ε - output F t ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  let δ := AmplifiedBandPrecision.precision s η t ε
  have hδ : 0 < δ := AmplifiedBandPrecision.precision_pos s η t ε hη.le hε
  have hδ1 : δ ≤ 1 := AmplifiedBandPrecision.precision_le_one s η t ε hη.le hε1
  have hα := totalNormalization_pos F hη
  have hQ : 1 ≤ maximumLength s δ := by
    have hpos := clockBound_pos D δ hδ hδ1
    have hpos' : (1 : ℝ) ≤ (clockBound s δ : ℝ) := by exact_mod_cast hpos
    unfold maximumLength
    linarith
  have hInv : ∀ i x v, (ActualDilatedBands.program F i).eval x
      ((ActualDilatedBands.program F i).eval x v) = v := by
    intro i x v
    exact congrArg (fun U => U v) (ActualDilatedBands.program_involution F i x)
  have hSlots : ∀ i, (MultiQueryClock.slots (ActualDilatedBands.program F i) : ℝ) ≤
      maximumLength s δ := by
    intro i
    change (MultiQueryClock.slots (ActualDilatedBands.program F i) : ℝ) ≤
      6 * (clockBound s δ : ℝ)
    exact_mod_cast ActualDilatedBands.slots_le F hη hδ hδ1 i
  obtain ⟨p, _hNat, hCount, hInput, hOutput, hEval⟩ :=
    NativeWeightedSimulation.evolution_query_certificate
      (ActualDilatedBands.oracle D) (ActualDilatedBands.oracle_unitary D)
      (ActualDilatedBands.program F) hInv (ActualDilatedBands.weights F)
      (fun i => (ActualDilatedBands.weights_pos F hη i).le)
      (ActualDilatedBands.weights_sum F hη)
      (fun _ => ActualDilatedBands.inputIsometry D) (ActualDilatedBands.inputIsometry D)
      (ActualDilatedBands.cleanBasis D) (ActualDilatedBands.image D) (ActualDilatedBands.valid D)
      (t * totalNormalization F) (maximumLength s δ) (ε / 4)
      (mul_nonneg ht hα.le) hQ hSlots (by positivity) (by linarith)
  change MultiOracleCircuit.Program (K := Physical F t ε) (oracle F t ε) at p
  refine ⟨p, ?_, hInput, hOutput, fun x => ⟨(hEval x).1, ?_⟩⟩
  · norm_num only [NativeSparseClock.card_query, Nat.cast_mul, Nat.cast_ofNat] at hCount
    convert hCount using 1 <;> rfl
  · have hSim : ‖p.eval x ∘L input F t ε - output F t ε ∘L
        NormedSpace.exp ((-Complex.I * (t : ℂ)) • approximateHamiltonian F x)‖ ≤ ε / 4 := by
      have h := (hEval x).2
      rw [LabeledSimulationTransfer.evolution_rescale, ActualDilatedBands.generator_scale F hη] at h
      exact h
    have hErr := HamiltonianStability.output_error_le (p.eval x ∘L input F t ε)
      (output F t ε) (SparseStateOverlap.matrixOperator (D.matrix x))
      (approximateHamiltonian F x) t (ε / 4) (15 * η * Real.sqrt s * δ)
      (LabeledSimulationTransfer.isometry_norm_le_one _ hOutput)
      (SparseValuePrecision.matrixOperator_star_eq _ (hH x))
      (approximateHamiltonian_selfadjoint F x) hSim
      (approximateHamiltonian_error F hη hδ.le hδ1 hRow hbLower hbUpper x)
    have hBand := AmplifiedBandPrecision.precision_time_error s η t ε hη.le hε
    exact hErr.trans (by linarith)

/-- The actual weighted time of the constructed circuits has the claimed
square-root-sparsity and square-logarithmic envelope. -/
theorem weightedTime_le (D : Data X n Z s) (η t ε : ℝ)
    (F : Family D η b (AmplifiedBandPrecision.precision s η t ε))
    (hη : 0 < η) (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    weightedTime F t ≤ 319488 * |t| * η * Real.sqrt s *
      (AmplifiedBandPrecision.logBudget s η t ε) ^ 2 := by
  have hAvg := ActualDilatedBands.averageLength_scale_le F hη
  have hWeight := scheduled_weightedLength_le η t ε F hη hε hε1 hbLower hbUpper
  unfold weightedTime averageLength
  calc
    _ = t * (totalNormalization F * MultiWeightedProgramClockBounds.averageLength
        (ActualDilatedBands.weights F) (ActualDilatedBands.program F)) := by ring
    _ ≤ t * (6 * weightedLength F) := mul_le_mul_of_nonneg_left hAvg ht
    _ ≤ t * (6 * (53248 * η * Real.sqrt s *
        (AmplifiedBandPrecision.logBudget s η t ε) ^ 2)) := by gcongr
    _ = _ := by rw [abs_of_nonneg ht]; ring

/-- Full native query bound for an actual amplified family, with the exact tail. -/
theorem family_simulation_bound (D : Data X n Z s) (η t ε : ℝ)
    (F : Family D η b (AmplifiedBandPrecision.precision s η t ε))
    (hη : 0 < η) (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hbLower : Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ b)
    (hbUpper : (2 : ℝ) ^ b ≤ 2 * Real.sqrt s) :
    ∃ p : MultiOracleCircuit.Program (K := Physical F t ε) (oracle F t ε),
      (p.count : ℝ) ≤ 2235174912 * (1 + |t| * η) * Real.sqrt s *
        (AmplifiedBandPrecision.logBudget s η t ε) ^ 2 ∧
      (input F t ε)† ∘L input F t ε = 1 ∧
      (output F t ε)† ∘L output F t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input F t ε - output F t ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨p, hCount, hInput, hOutput, hEval⟩ :=
    family_simulation D η t ε F hη ht hε hε1 hH hRow hbLower hbUpper
  refine ⟨p, ?_, hInput, hOutput, hEval⟩
  have hAvg : 0 ≤ averageLength F :=
    MultiWeightedProgramClockBounds.averageLength_nonneg _ _
      (fun i => (ActualDilatedBands.weights_pos F hη i).le)
  have hW : 0 ≤ weightedTime F t :=
    mul_nonneg (mul_nonneg ht (totalNormalization_pos F hη).le) hAvg
  have hQ : maximumLength s (AmplifiedBandPrecision.precision s η t ε) ≤
      162 * Real.sqrt s * AmplifiedBandPrecision.logBudget s η t ε := by
    have h := scheduled_clockBound_le D η t ε hη.le hε hε1
    unfold maximumLength
    nlinarith
  exact AmplifiedSimulationBudget.native_count_le s η t ε _ _ _ (one_le_s D) hη.le hε hε1
    (by unfold maximumLength; positivity) hW hQ
    (weightedTime_le D η t ε F hη ht hε hε1 hbLower hbUpper)
    (by convert hCount using 1; norm_num)

/-- Public dyadic cutoff exists solely from the positive sparsity bound. -/
def cutoff (D : Data X n Z s) : ℕ :=
  Classical.choose (BandCost.exists_dyadic_endpoint (one_le_s D))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Both endpoint bounds follow from the fixed public cutoff construction. -/
theorem cutoff_bounds (D : Data X n Z s) :
    Real.sqrt (s : ℝ) ≤ (2 : ℝ) ^ cutoff D ∧
      (2 : ℝ) ^ cutoff D ≤ 2 * Real.sqrt s :=
  Classical.choose_spec (BandCost.exists_dyadic_endpoint (one_le_s D))

/-- Constructed band family at the chosen public cutoff and precision. -/
def preparedFamily (D : Data X n Z s) (η t ε : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Family D η (cutoff D) (AmplifiedBandPrecision.precision s η t ε) :=
  family D η hη hH hRow hCol (cutoff D) (AmplifiedBandPrecision.precision s η t ε)
    (AmplifiedBandPrecision.precision_pos s η t ε hη.le hε)
    (AmplifiedBandPrecision.precision_le_one s η t ε hη.le hε1)

/-- Sparse input promises alone produce the physical simulation program with
square-root-sparsity query complexity and polylogarithmic inverse precision.
The absolute constant is deliberately not optimized. -/
theorem simulation (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    let F := preparedFamily D η t ε hη hH hRow hCol hε hε1
    ∃ p : MultiOracleCircuit.Program (K := Physical F t ε) (oracle F t ε),
      (p.count : ℝ) ≤ 2235174912 * (1 + |t| * η) * Real.sqrt s *
        (AmplifiedBandPrecision.logBudget s η t ε) ^ 2 ∧
      (input F t ε)† ∘L input F t ε = 1 ∧
      (output F t ε)† ∘L output F t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input F t ε - output F t ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  exact family_simulation_bound D η t ε
    (preparedFamily D η t ε hη hH hRow hCol hε hε1) hη ht hε hε1 hH hRow
    (cutoff_bounds D).1 (cutoff_bounds D).2

/-- The final scheduled query family consists of unitary original primitives
with spectators, in both forward and inverse directions. -/
theorem oracle_unitary {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ)
    (l : NativeSparseBlockEncoding.Query) (x : X) : IsUnitary (oracle F t ε l x) :=
  NativeMaskedOracle.oracle_unitary (ActualDilatedBands.oracle D l)
    (ActualDilatedBands.oracle_unitary D l) x

/-- Fixed input preparation for either time direction. -/
def signedInput {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical F |t| ε :=
  LabeledAdjointSimulation.signedInput (input F |t| ε) (output F |t| ε) t

/-- Fixed output preparation for either time direction. -/
def signedOutput {D : Data X n Z s} (F : Family D η b δ) (t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical F |t| ε :=
  LabeledAdjointSimulation.signedOutput (input F |t| ε) (output F |t| ε) t

/-- Complete sparse simulation for every real time. Reversal exchanges the
fixed input/output encodings and preserves every native query count exactly. -/
theorem simulation_signed (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    let F := preparedFamily D η |t| ε hη hH hRow hCol hε hε1
    ∃ p : MultiOracleCircuit.Program (K := Physical F |t| ε) (oracle F |t| ε),
      (p.count : ℝ) ≤ 2235174912 * (1 + |t| * η) * Real.sqrt s *
        (AmplifiedBandPrecision.logBudget s η t ε) ^ 2 ∧
      (signedInput F t ε)† ∘L signedInput F t ε = 1 ∧
      (signedOutput F t ε)† ∘L signedOutput F t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L signedInput F t ε - signedOutput F t ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  let F := preparedFamily D η |t| ε hη hH hRow hCol hε hε1
  obtain ⟨p, hCount, hInput, hOutput, hEval⟩ :=
    simulation D η |t| ε hη (abs_nonneg t) hε hε1 hH hRow hCol
  change MultiOracleCircuit.Program (K := Physical F |t| ε) (oracle F |t| ε) at p
  have hIso := LabeledAdjointSimulation.signed_isometries
    (input F |t| ε) (output F |t| ε) hInput hOutput t
  refine ⟨LabeledAdjointSimulation.signedProgram p t, ?_, hIso.1, hIso.2, fun x => ?_⟩
  · rw [LabeledAdjointSimulation.signedProgram_count]
    simpa only [AmplifiedBandPrecision.logBudget, abs_abs] using hCount
  · refine ⟨(LabeledAdjointSimulation.signedProgram p t).eval_unitary
      (oracle_unitary F |t| ε) x, ?_⟩
    exact LabeledAdjointSimulation.signed_program_error p (oracle_unitary F |t| ε)
      (input F |t| ε) (output F |t| ε)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (fun x => SparseValuePrecision.matrixOperator_star_eq _ (hH x)) t ε
      (fun x => (hEval x).2) x

/-- The family construction can use the usual spectral bound as its only
matrix-size bound; separate row and column energy bounds are then derived. -/
def spectralFamily (D : Data X n Z s) (η t ε : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ η)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :=
  preparedFamily D η t ε hη hH (SparseSpectralEnergy.native_energies D η hH hNorm).1
    (SparseSpectralEnergy.native_energies D η hH hNorm).2 hε hε1

/-- Public endpoint: exact finite native sparse access, Hermiticity and a known
positive spectral-norm bound imply a uniform full-output simulation program.
The explicit bound is O((1+|t|η)√s log²(2s(1+|t|η)/ε)); no block-encoding,
polynomial, phase list, clock implementation or analytic promise is assumed. -/
theorem simulation_spectral (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ η) :
    let F := spectralFamily D η |t| ε hη hH hNorm hε hε1
    ∃ p : MultiOracleCircuit.Program (K := Physical F |t| ε) (oracle F |t| ε),
      (p.count : ℝ) ≤ 2235174912 * (1 + |t| * η) * Real.sqrt s *
        (AmplifiedBandPrecision.logBudget s η t ε) ^ 2 ∧
      (signedInput F t ε)† ∘L signedInput F t ε = 1 ∧
      (signedOutput F t ε)† ∘L signedOutput F t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L signedInput F t ε - signedOutput F t ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  exact simulation_signed D η t ε hη hε hε1 hH
    (SparseSpectralEnergy.native_energies D η hH hNorm).1
    (SparseSpectralEnergy.native_energies D η hH hNorm).2

end
end SparseHamiltonian.NativeSparseSimulation
