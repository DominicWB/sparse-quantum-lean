import SparseHamiltonian.ScalarPhaseError

/-!
# Actual sparse phase circuits and their complete matrix overlap

The polynomial action determines the entire output maps, including failure.
Orthogonality removes those failure contributions. Shared complex polynomial
gains therefore produce the same Hermitian adjoint sandwich whose relative
error is controlled without a dimension factor. Approximation is an explicit
scalar premise here; no unknown row sum enters the circuit.
-/

namespace SparseHamiltonian.NativePolynomialOverlap

noncomputable section
set_option maxRecDepth 2000
open ContinuousLinearMap NativeSparseBlockEncoding NativeSparsePhaseSequence
open PolynomialGainError RelativeAmplitudeError ProjectedGainOverlap
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The actual complete row output, including its failure component. -/
def rowOutput (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  (NativeSparsePhaseSequence.rowProgram D ss).eval x ∘L (input D).toContinuousLinearMap

def columnOutput (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  (NativeSparsePhaseSequence.columnProgram D ss).eval x ∘L (input D).toContinuousLinearMap

omit [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Oddness supplies the exact zero required by the gain convention. -/
theorem good_polynomial_zero (ss : List AmplitudePolynomialSequence.Phases) :
    (AmplitudePolynomialSequence.polynomials ss).1.eval 0 = 0 := by
  have h := AmplitudePolynomialSequence.good_odd ss (0 : ℂ)
  simp only [neg_zero] at h
  linear_combination (1 / 2 : ℂ) * h

/-- The whole row map has separate success and failure diagonal gains. -/
theorem row_decomposition (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X) (target : ℂ) :
    rowOutput D ss x = transformed goodProjection (rowState D x)
      (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1
        (rowSignal D x i)))
      (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
        (rowSignal D x i : ℂ))) := by
  apply map_decomposition (rowOutput D ss x) (rowState D x) (rowState_isometry D x)
    goodProjection goodProjection_orthogonal (rowSignal D x) (rowSignal_bound D x)
    (rowSignal_eigen D x) target (AmplitudePolynomialSequence.polynomials ss).1
    (AmplitudePolynomialSequence.polynomials ss).2 (good_polynomial_zero ss)
  intro i
  exact rowProgram_output D ss x i

theorem column_decomposition (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X) (target : ℂ) :
    columnOutput D ss x = transformed goodProjection (columnState D x)
      (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1
        (columnSignal D x i)))
      (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
        (columnSignal D x i : ℂ))) := by
  apply map_decomposition (columnOutput D ss x) (columnState D x) (columnState_isometry D x)
    goodProjection goodProjection_orthogonal (columnSignal D x) (columnSignal_bound D x)
    (columnSignal_eigen D x) target (AmplitudePolynomialSequence.polynomials ss).1
    (AmplitudePolynomialSequence.polynomials ss).2 (good_polynomial_zero ss)
  intro i
  exact columnProgram_output D ss x i

/-- Hermiticity makes both actual good gains the same diagonal operator. -/
theorem column_decomposition_common (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X)
    (hH : (D.matrix x).IsHermitian) (target : ℂ) :
    columnOutput D ss x = transformed goodProjection (columnState D x)
      (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1
        (rowSignal D x i)))
      (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
        (rowSignal D x i : ℂ))) := by
  rw [column_decomposition D ss x target]
  simp only [HermitianSuccessSignals.rowSignal_eq_columnSignal D x hH]

/-- The actual inverse-row/column circuit; no successful-state oracle is granted. -/
def program (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    MultiOracleCircuit.Program (oracles D) :=
  PreparedOverlapProgram.program (NativeSparsePhaseSequence.rowProgram D ss)
    (NativeSparsePhaseSequence.columnProgram D ss)

@[simp] theorem program_count (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    (program D ss).count = 6 * (2 * ss.length + 1) := by
  simp only [program, PreparedOverlapProgram.program_count,
    NativeSparsePhaseSequence.rowProgram_count, NativeSparsePhaseSequence.columnProgram_count]
  ring

theorem program_cost (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (w : Query → ℕ) :
    (program D ss).cost w = (2 * ss.length + 1) *
      (w .rowLocation + w .columnLocation + 4 * w .value) := by
  simp only [program, PreparedOverlapProgram.program_cost,
    NativeSparsePhaseSequence.rowProgram_cost, NativeSparsePhaseSequence.columnProgram_cost]
  ring

theorem program_unitary (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) : OracleCircuit.IsUnitary ((program D ss).eval x) :=
  (program D ss).eval_unitary (oracles_unitary D) x

/-- Compression is the overlap of the complete physical outputs. -/
theorem compression (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    (input D).toContinuousLinearMap† ∘L (program D ss).eval x ∘L
      (input D).toContinuousLinearMap = (rowOutput D ss x)† ∘L columnOutput D ss x :=
  PreparedOverlapProgram.compression _ _ _ x

/-- The realized relative perturbation is analytical and uses the common signal. -/
def errorDiagonal (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (target : ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  complexDiagonal (fun i => relativeError target (AmplitudePolynomialSequence.polynomials ss).1
    (rowSignal D x i))

/-- Full circuit compression has the desired complex relative-error sandwich. -/
theorem compression_relative (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X)
    (hH : (D.matrix x).IsHermitian) (target : ℂ) (ht : target ≠ 0) :
    (input D).toContinuousLinearMap† ∘L (program D ss).eval x ∘L
      (input D).toContinuousLinearMap =
      ((‖target‖ ^ 2 : ℝ) : ℂ) • conjugateScaled
        (SparseStateOverlap.matrixOperator
          (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)))
        (errorDiagonal D ss x target) := by
  rw [compression, row_decomposition D ss x target,
    column_decomposition_common D ss x hH target,
    gainDiagonal_eq target ht]
  have h := transformed_overlap_relative
    (E := EuclideanSpace ℂ n) (K := SparseFlagEmbedding.Space (n × n) Z)
    goodProjection goodProjection_orthogonal
    (rowState D x) (columnState D x)
    (NativeSparseFailureOrthogonality.native_failure_overlap D x)
    (errorDiagonal D ss x target)
    (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
      (rowSignal D x i : ℂ)))
    (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
      (rowSignal D x i : ℂ))) target
  simpa only [errorDiagonal, NativeSparseFailureOrthogonality.native_overlap] using h

/-- Scalar relative approximation gives a dimension-independent matrix error. -/
theorem compression_error (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X)
    (hH : (D.matrix x).IsHermitian) (target : ℂ) (ht : target ≠ 0)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ∀ i, ‖(AmplitudePolynomialSequence.polynomials ss).1.eval
        (rowSignal D x i : ℂ) - target * (rowSignal D x i : ℂ)‖ ≤
      (δ * ‖target‖) * |rowSignal D x i|) :
    ‖(input D).toContinuousLinearMap† ∘L (program D ss).eval x ∘L
        (input D).toContinuousLinearMap -
      ((‖target‖ ^ 2 : ℝ) : ℂ) • SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale))‖ ≤
      ‖target‖ ^ 2 * ((2 * δ + δ ^ 2) * ‖SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale))‖) := by
  rw [compression_relative D ss x hH target ht, ← smul_sub, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact norm_conjugateScaled_sub_le _ _ δ hδ
    (norm_relativeDiagonal_le target ht _ (rowSignal D x) δ hδ herr)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The original positive real sparse normalization preserves Hermiticity. -/
theorem normalized_isHermitian (D : Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) :
    Matrix.IsHermitian (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [hH.apply i j]

/-- The full compressed circuit is Hermitian for every supplied phase list. -/
theorem compression_adjoint (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X)
    (hH : (D.matrix x).IsHermitian) :
    ((input D).toContinuousLinearMap† ∘L (program D ss).eval x ∘L
      (input D).toContinuousLinearMap)† =
    (input D).toContinuousLinearMap† ∘L (program D ss).eval x ∘L
      (input D).toContinuousLinearMap := by
  rw [compression_relative D ss x hH 1 one_ne_zero]
  simp only [norm_one, one_pow, Complex.ofReal_one, one_smul]
  apply conjugateScaled_adjoint
  exact SparseValuePrecision.matrixOperator_star_eq _ (normalized_isHermitian D x hH)

/-- An admissible approximating pair yields one uniform native sparse program.
The phase list is constructed, not assumed, and no success-probability query
is required. Constructing such a pair with the desired degree remains separate. -/
theorem exists_program_of_pair (D : Data X n Z s) (m : ℕ) (P B : Polynomial ℂ)
    (hP : P.natDegree ≤ 2 * m + 1) (hB : B.natDegree ≤ 2 * m)
    (hp : P.comp (-Polynomial.X) = -P) (hb : B.comp (-Polynomial.X) = B)
    (hnorm : PolynomialUnitarity.IsNormalized P B)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (target : ℂ) (ht : target ≠ 0) (δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ∀ x i, ‖P.eval (rowSignal D x i : ℂ) - target * (rowSignal D x i : ℂ)‖ ≤
      (δ * ‖target‖) * |rowSignal D x i|) :
    ∃ p : MultiOracleCircuit.Program (oracles D), p.count = 6 * (2 * m + 1) ∧
      (∀ x, OracleCircuit.IsUnitary (p.eval x)) ∧
      ∀ x, ‖(input D).toContinuousLinearMap† ∘L p.eval x ∘L
          (input D).toContinuousLinearMap -
        ((‖target‖ ^ 2 : ℝ) : ℂ) • SparseStateOverlap.matrixOperator
          (fun i j => D.matrix x i j / ((s : ℂ) * D.scale))‖ ≤
        ‖target‖ ^ 2 * ((2 * δ + δ ^ 2) * ‖SparseStateOverlap.matrixOperator
          (fun i j => D.matrix x i j / ((s : ℂ) * D.scale))‖) := by
  obtain ⟨v, u, ss, hlen, hgood, _hbad⟩ :=
    PhysicalPhaseSynthesis.paired_synthesis m P B hP hB hp hb hnorm
  let a := ScalarPhaseError.productPhase v u
  let adjusted : ℂ := star (a : ℂ) * target
  have ha : ‖adjusted‖ = ‖target‖ := ScalarPhaseError.norm_phased_target a target
  have hta : adjusted ≠ 0 := ScalarPhaseError.phased_target_ne_zero a target ht
  refine ⟨program D ss, by rw [program_count, hlen], program_unitary D ss, ?_⟩
  intro x
  have happrox (i : n) :
      ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) -
        adjusted * (rowSignal D x i : ℂ)‖ ≤ (δ * ‖adjusted‖) * |rowSignal D x i| := by
    rw [ha]
    exact ScalarPhaseError.paired_relative_error v u ss P hgood target
      (rowSignal D x i) δ (herr x i)
  have h := compression_error D ss x (hH x) adjusted hta δ hδ happrox
  simpa only [ha] using h

end
end SparseHamiltonian.NativePolynomialOverlap
