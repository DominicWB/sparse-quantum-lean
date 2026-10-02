import SparseHamiltonian.NativeAttenuatedPhaseSequence

/-!
# Quarter-attenuated sparse phase circuits and their complete matrix overlap

The polynomial action determines the entire output maps, including failure.
Orthogonality removes those failure contributions. Shared complex polynomial
gains therefore produce the same Hermitian adjoint sandwich whose relative
error is controlled without a dimension factor. Approximation is an explicit
scalar premise here; no unknown row sum enters the circuit.
-/

namespace SparseHamiltonian.NativeAttenuatedPolynomialOverlap

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 800000
open ContinuousLinearMap NativeSparseAttenuation NativeAttenuatedPhaseSequence
open NativeSparseBlockEncoding (Data Query)
open PolynomialGainError RelativeAmplitudeError ProjectedGainOverlap
open scoped InnerProduct

/-- A generic complete-map bridge avoids unfolding native oracle circuits
when assembling the attenuation certificate. -/
theorem prepared_map_decomposition {Y L n K : Type*}
    [Fintype n] [DecidableEq n]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : L → Y → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O)
    (hO : ∀ l y, OracleCircuit.IsUnitary (O l y))
    (F R : EuclideanSpace ℂ n →L[ℂ] K) (y : Y) (hprep : p.eval y ∘L F = R)
    (hR : R† ∘L R = 1) (Q : K →L[ℂ] K)
    (hP : PhaseSubspaceGates.IsOrthogonalProjection (F ∘L F†))
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (z : n → ℝ) (hz : ∀ i, |z i| ≤ 1)
    (he : ∀ i, (R†) (Q (R (EuclideanSpace.single i 1))) =
      (z i : ℂ) ^ 2 • EuclideanSpace.single i 1)
    (ss : List AmplitudePolynomialSequence.Phases) (target : ℂ) :
    (InvariantPhaseSequence.nativePrepared p (F ∘L F†) Q hP hQ ss).eval y ∘L F =
      transformed Q R
        (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1 (z i)))
        (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval (z i : ℂ))) := by
  apply map_decomposition _ R hR Q hQ z hz he target
    (AmplitudePolynomialSequence.polynomials ss).1
    (AmplitudePolynomialSequence.polynomials ss).2 (NativePolynomialOverlap.good_polynomial_zero ss)
  intro i
  exact counted_output p hO F R y hprep hR Q hP hQ
    (EuclideanSpace.single i 1) (z i) (hz i) (he i) ss

/-- Real scalar multiplication preserves the adjoint identity. -/
theorem real_smul_adjoint {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (H : E →L[ℂ] E) (hH : H† = H) (a : ℝ) :
    ((a : ℂ) • H)† = (a : ℂ) • H := by
  rw [map_smulₛₗ, hH]
  simp

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Quarter attenuation keeps the original matrix divided by sixteen. -/
def baseMatrix (D : Data X n Z s) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (1 / 16 : ℂ) • SparseStateOverlap.matrixOperator
    (fun i j => D.matrix x i j / ((s : ℂ) * D.scale))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The two attenuated success signals agree for a Hermitian input. -/
theorem rowSignal_eq_columnSignal (D : Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (i : n) : rowSignal D x i = columnSignal D x i := by
  simp only [rowSignal, columnSignal,
    HermitianSuccessSignals.rowSignal_eq_columnSignal D x hH]

/-- The retained good block is independent of the two fresh failure sectors. -/
theorem retained_good_overlap (_D : Data X n Z s) (c : ℝ) :
    (FreshFlagAttenuation.rowPreparation NativeSparsePhaseSequence.goodProjection c)† ∘L
      (goodProjection (n := n) (Z := Z)) ∘L
      FreshFlagAttenuation.columnPreparation NativeSparsePhaseSequence.goodProjection c =
      ((c : ℂ) ^ 2) • NativeSparsePhaseSequence.goodProjection := by
  let Q : SparseFlagEmbedding.Space (n × n) Z →L[ℂ]
      SparseFlagEmbedding.Space (n × n) Z := NativeSparsePhaseSequence.goodProjection
  change (FreshFlagAttenuation.rowPreparation Q c)† ∘L
    (fresh.toContinuousLinearMap ∘L Q ∘L fresh.toContinuousLinearMap†) ∘L
      FreshFlagAttenuation.columnPreparation Q c = _
  calc
    _ = (fresh.toContinuousLinearMap† ∘L FreshFlagAttenuation.rowPreparation Q c)† ∘L Q ∘L
        (fresh.toContinuousLinearMap† ∘L FreshFlagAttenuation.columnPreparation Q c) := by
      simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
    _ = _ := by
      rw [row_retained, column_retained]
      exact diagonal_success_gram Q NativeSparsePhaseSequence.goodProjection_orthogonal c

/-- Old and fresh failures have exactly zero overlap after attenuation. -/
theorem failure_overlap (D : Data X n Z s) (x : X) :
    (rowState D (1 / 4) x)† ∘L (1 - goodProjection) ∘L
      columnState D (1 / 4) x = 0 := by
  have hg : (rowState D (1 / 4) x)† ∘L goodProjection ∘L columnState D (1 / 4) x =
      (rowState D (1 / 4) x)† ∘L columnState D (1 / 4) x := by
    unfold rowState columnState
    calc
      _ = (NativeSparsePhaseSequence.rowState D x)† ∘L
          ((FreshFlagAttenuation.rowPreparation NativeSparsePhaseSequence.goodProjection (1 / 4))† ∘L
            goodProjection ∘L
            FreshFlagAttenuation.columnPreparation NativeSparsePhaseSequence.goodProjection (1 / 4)) ∘L
          NativeSparsePhaseSequence.columnState D x := by
        simp only [adjoint_comp, comp_assoc]
      _ = _ := by
        rw [retained_good_overlap D (1 / 4)]
        have h := FreshFlagAttenuation.prepared_overlap _
          NativeSparsePhaseSequence.goodProjection_orthogonal (1 / 4) _ _
          (old_failure_orthogonal D x)
        simpa only [comp_smul, smul_comp, comp_assoc] using h.symm
  rw [sub_comp, one_def, id_comp, comp_sub, hg, sub_self]

theorem base_overlap (D : Data X n Z s) (x : X) :
    (rowState D (1 / 4) x)† ∘L columnState D (1 / 4) x = baseMatrix D x := by
  rw [overlap]
  norm_num [baseMatrix]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem baseMatrix_adjoint (D : Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) : (baseMatrix D x)† = baseMatrix D x := by
  have h : (SparseStateOverlap.matrixOperator
      (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)))† =
      SparseStateOverlap.matrixOperator (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) :=
    SparseValuePrecision.matrixOperator_star_eq _ (NativePolynomialOverlap.normalized_isHermitian D x hH)
  simpa only [baseMatrix, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    real_smul_adjoint _ h (1 / 16)


/-- The actual complete row output, including its failure component. -/
def rowOutput (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] Workspace n Z :=
  (NativeAttenuatedPhaseSequence.rowProgram D ss).eval x ∘L (input D).toContinuousLinearMap

def columnOutput (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] Workspace n Z :=
  (NativeAttenuatedPhaseSequence.columnProgram D ss).eval x ∘L (input D).toContinuousLinearMap

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
    rowOutput D ss x = transformed goodProjection (rowState D (1 / 4) x)
      (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1
        (rowSignal D x i)))
      (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
        (rowSignal D x i : ℂ))) := by
  unfold rowOutput NativeAttenuatedPhaseSequence.rowProgram inputProjection
  have h := prepared_map_decomposition
    (Y := X) (L := Query) (n := n) (K := Workspace n Z)
    (O := NativeSparseAttenuation.oracles D)
    (NativeSparseAttenuation.rowProgram D (1 / 4) (by norm_num))
    (NativeSparseAttenuation.oracles_unitary D)
    (input D).toContinuousLinearMap (rowState D (1 / 4) x) x
    (row_preparation D (1 / 4) (by norm_num) x)
    (rowState_isometry D (1 / 4) (by norm_num) x)
    goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal
    (rowSignal D x) (rowSignal_bound D x) (rowSignal_eigen D x) ss target
  with_reducible exact h

theorem column_decomposition (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X) (target : ℂ) :
    columnOutput D ss x = transformed goodProjection (columnState D (1 / 4) x)
      (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1
        (columnSignal D x i)))
      (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
        (columnSignal D x i : ℂ))) := by
  unfold columnOutput NativeAttenuatedPhaseSequence.columnProgram inputProjection
  have h := prepared_map_decomposition
    (Y := X) (L := Query) (n := n) (K := Workspace n Z)
    (O := NativeSparseAttenuation.oracles D)
    (NativeSparseAttenuation.columnProgram D (1 / 4) (by norm_num))
    (NativeSparseAttenuation.oracles_unitary D)
    (input D).toContinuousLinearMap (columnState D (1 / 4) x) x
    (column_preparation D (1 / 4) (by norm_num) x)
    (columnState_isometry D (1 / 4) (by norm_num) x)
    goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal
    (columnSignal D x) (columnSignal_bound D x) (columnSignal_eigen D x) ss target
  with_reducible exact h

/-- Hermiticity makes both actual good gains the same diagonal operator. -/
theorem column_decomposition_common (D : Data X n Z s)
    (ss : List AmplitudePolynomialSequence.Phases) (x : X)
    (hH : (D.matrix x).IsHermitian) (target : ℂ) :
    columnOutput D ss x = transformed goodProjection (columnState D (1 / 4) x)
      (complexDiagonal (fun i => gain target (AmplitudePolynomialSequence.polynomials ss).1
        (rowSignal D x i)))
      (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
        (rowSignal D x i : ℂ))) := by
  rw [column_decomposition D ss x target]
  simp only [rowSignal_eq_columnSignal D x hH]

/-- The actual inverse-row/column circuit; no successful-state oracle is granted. -/
def program (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    MultiOracleCircuit.Program (oracles D) :=
  PreparedOverlapProgram.program (NativeAttenuatedPhaseSequence.rowProgram D ss)
    (NativeAttenuatedPhaseSequence.columnProgram D ss)

@[simp] theorem program_count (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    (program D ss).count = 6 * (2 * ss.length + 1) := by
  simp only [program, PreparedOverlapProgram.program_count,
    NativeAttenuatedPhaseSequence.rowProgram_count, NativeAttenuatedPhaseSequence.columnProgram_count]
  ring

theorem program_cost (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (w : Query → ℕ) :
    (program D ss).cost w = (2 * ss.length + 1) *
      (w .rowLocation + w .columnLocation + 4 * w .value) := by
  simp only [program, PreparedOverlapProgram.program_cost,
    NativeAttenuatedPhaseSequence.rowProgram_cost, NativeAttenuatedPhaseSequence.columnProgram_cost]
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
        (baseMatrix D x)
        (errorDiagonal D ss x target) := by
  rw [compression, row_decomposition D ss x target,
    column_decomposition_common D ss x hH target,
    gainDiagonal_eq target ht]
  have h := transformed_overlap_relative
    (E := EuclideanSpace ℂ n) (K := Workspace n Z)
    goodProjection goodProjection_orthogonal
    (rowState D (1 / 4) x) (columnState D (1 / 4) x)
    (failure_overlap D x)
    (errorDiagonal D ss x target)
    (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
      (rowSignal D x i : ℂ)))
    (complexDiagonal (fun i => (AmplitudePolynomialSequence.polynomials ss).2.eval
      (rowSignal D x i : ℂ))) target
  simpa only [errorDiagonal, base_overlap] using h

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
      ((‖target‖ ^ 2 : ℝ) : ℂ) • baseMatrix D x‖ ≤
      ‖target‖ ^ 2 * ((2 * δ + δ ^ 2) * ‖baseMatrix D x‖) := by
  rw [compression_relative D ss x hH target ht, ← smul_sub, norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact norm_conjugateScaled_sub_le _ _ δ hδ
    (norm_relativeDiagonal_le target ht _ (rowSignal D x) δ hδ herr)

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
  exact baseMatrix_adjoint D x hH

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
      (∀ x, ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap)† =
        (input D).toContinuousLinearMap† ∘L p.eval x ∘L (input D).toContinuousLinearMap) ∧
      ∀ x, ‖(input D).toContinuousLinearMap† ∘L p.eval x ∘L
          (input D).toContinuousLinearMap -
        ((‖target‖ ^ 2 : ℝ) : ℂ) • baseMatrix D x‖ ≤
        ‖target‖ ^ 2 * ((2 * δ + δ ^ 2) * ‖baseMatrix D x‖) := by
  obtain ⟨v, u, ss, hlen, hgood, _hbad⟩ :=
    PhysicalPhaseSynthesis.paired_synthesis m P B hP hB hp hb hnorm
  let a := ScalarPhaseError.productPhase v u
  let adjusted : ℂ := star (a : ℂ) * target
  have ha : ‖adjusted‖ = ‖target‖ := ScalarPhaseError.norm_phased_target a target
  have hta : adjusted ≠ 0 := ScalarPhaseError.phased_target_ne_zero a target ht
  refine ⟨program D ss, by rw [program_count, hlen], program_unitary D ss,
    fun x => compression_adjoint D ss x (hH x), ?_⟩
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
end SparseHamiltonian.NativeAttenuatedPolynomialOverlap
