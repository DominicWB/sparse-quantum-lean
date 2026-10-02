import SparseHamiltonian.NativePolynomialOverlap

/-!
# Counted native sparse preparations with fresh attenuation flags

Every native oracle acts identically on all three fresh-flag sectors. Thus a
lifted query is the original query with an untouched spectator flag. The fixed
row and column attenuation gates have disjoint new failure sectors, and the
resulting six-query block encoding has normalization `16 * s * a` at quarter
gain. There is no orthogonality assumption left to supply.
-/

namespace SparseHamiltonian.NativeSparseAttenuation

noncomputable section
open ContinuousLinearMap OracleCircuit FreshFlagAttenuation
open NativeSparseBlockEncoding
open scoped InnerProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 2000

section Spectator
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Append the common fresh flag, initially in its first sector. -/
def fresh : K →ₗᵢ[ℂ] Triple K := rowEmbedding.comp clean

omit [CompleteSpace K] in
@[simp] theorem fresh_apply (v : K) :
    fresh v = WithLp.toLp 2 (v, WithLp.toLp 2 (0, 0)) := rfl

/-- A genuine spectator extension: the same operator on all three sectors. -/
def spectator (U : K →L[ℂ] K) : Triple K →L[ℂ] Triple K :=
  GlobalColligation.blockMap U 0 0 (GlobalColligation.blockMap U 0 0 U)

omit [CompleteSpace K] in
@[simp] theorem spectator_apply (U : K →L[ℂ] K) (v : Triple K) :
    spectator U v = WithLp.toLp 2
      (U v.fst, WithLp.toLp 2 (U v.snd.fst, U v.snd.snd)) := by
  simp [spectator, GlobalColligation.blockMap_apply]

/-- The adjoint has the same spectator action. -/
theorem spectator_adjoint (U : K →L[ℂ] K) : (spectator U)† = spectator (U†) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℂ
  intro w
  simp only [adjoint_inner_left, spectator_apply, WithLp.prod_inner_apply]
  rfl

omit [CompleteSpace K] in
/-- Composition acts independently in every fresh sector. -/
theorem spectator_comp (U V : K →L[ℂ] K) :
    spectator U ∘L spectator V = spectator (U ∘L V) := by
  ext v
  simp only [comp_apply, spectator_apply, WithLp.toLp_fst, WithLp.toLp_snd]

omit [CompleteSpace K] in
@[simp] theorem spectator_one : spectator (1 : K →L[ℂ] K) = 1 := by
  ext v
  simp only [spectator_apply, one_def, id_apply]
  rfl

/-- Native unitarity holds even in the non-clean fresh sectors. -/
theorem spectator_unitary (U : K →L[ℂ] K) (hU : IsUnitary U) :
    IsUnitary (spectator U) := by
  have hleft : U† ∘L U = 1 := hU.1
  have hright : U ∘L U† = 1 := hU.2
  constructor
  · change (spectator U)† ∘L spectator U = 1
    rw [spectator_adjoint, spectator_comp, hleft, spectator_one]
  · change spectator U ∘L (spectator U)† = 1
    rw [spectator_adjoint, spectator_comp, hright, spectator_one]

omit [CompleteSpace K] in
/-- The common clean encoding intertwines the actual spectator query. -/
theorem spectator_fresh (U : K →L[ℂ] K) :
    spectator U ∘L fresh.toContinuousLinearMap = fresh.toContinuousLinearMap ∘L U := by
  ext v
  simp [spectator_apply, fresh_apply]

/-- Old-failure orthogonality survives a common isometric workspace encoding. -/
theorem failure_lift {A P : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (J : A →L[ℂ] K) (hJ : J† ∘L J = 1)
    (Q : A →L[ℂ] A) (R C : P →L[ℂ] A) :
    (J ∘L R)† ∘L (1 - J ∘L Q ∘L J†) ∘L (J ∘L C) =
      R† ∘L (1 - Q) ∘L C := by
  have hJv (a : A) : (J†) (J a) = a := congrArg (fun f : A →L[ℂ] A => f a) hJ
  ext v
  simp only [adjoint_comp, comp_apply, sub_apply, one_def, id_apply, map_sub, hJv]

/-- Erase the clean fresh encoding by projecting onto its first sector. -/
@[simp] theorem fresh_adjoint_apply (v : Triple K) :
    (fresh.toContinuousLinearMap†) v = v.fst := by
  apply ext_inner_right ℂ
  intro w
  simp only [adjoint_inner_left, LinearIsometry.coe_toContinuousLinearMap,
    fresh_apply, WithLp.prod_inner_apply, inner_zero_right, add_zero]
  rfl

/-- Retained old workspace after the row attenuator. -/
theorem row_retained (Q : K →L[ℂ] K) (c : ℝ) :
    fresh.toContinuousLinearMap† ∘L rowPreparation Q c = diagonal Q c := by
  ext v
  simp only [comp_apply, fresh_adjoint_apply, rowPreparation_apply, WithLp.toLp_fst]

/-- The same retained workspace after the column attenuator. -/
theorem column_retained (Q : K →L[ℂ] K) (c : ℝ) :
    fresh.toContinuousLinearMap† ∘L columnPreparation Q c = diagonal Q c := by
  ext v
  simp only [comp_apply, fresh_adjoint_apply, columnPreparation_apply, WithLp.toLp_fst]

/-- Exact success Gram operator after attenuation. -/
theorem diagonal_success_gram (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (c : ℝ) :
    (diagonal Q c)† ∘L Q ∘L diagonal Q c = ((c : ℂ) ^ 2) • Q := by
  have hQD : Q ∘L diagonal Q c = (c : ℂ) • Q := by
    ext v
    exact diagonal_good Q hQ.2 c v
  have hDQ : diagonal Q c ∘L Q = (c : ℂ) • Q := by
    ext v
    simp only [comp_apply, diagonal_apply, smul_apply, projection_twice Q hQ.2]
    module
  have hadj : (diagonal Q c)† = diagonal Q c := diagonal_adjoint Q hQ.1 c
  rw [hadj, hQD, comp_smul, hDQ, smul_smul, pow_two]

/-- Any preparation retaining the diagonal attenuation has this success Gram
operator; it applies to both fresh-failure orientations. -/
theorem success_gram (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (c : ℝ)
    (A : K →L[ℂ] Triple K)
    (hA : fresh.toContinuousLinearMap† ∘L A = diagonal Q c) :
    A† ∘L (fresh.toContinuousLinearMap ∘L Q ∘L fresh.toContinuousLinearMap†) ∘L A =
      ((c : ℂ) ^ 2) • Q := by
  calc
    _ = (fresh.toContinuousLinearMap† ∘L A)† ∘L Q ∘L
        (fresh.toContinuousLinearMap† ∘L A) := by
      simp only [adjoint_comp, adjoint_adjoint, comp_assoc]
    _ = _ := by rw [hA, diagonal_success_gram Q hQ c]

/-- Composing two isometries preserves the adjoint identity. -/
theorem isometry_comp {A B C : Type*}
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]
    (R : A →L[ℂ] B) (S : B →L[ℂ] C) (hR : R† ∘L R = 1) (hS : S† ∘L S = 1) :
    (S ∘L R)† ∘L (S ∘L R) = 1 := by
  have hSv (b : B) : (S†) (S b) = b := congrArg (fun f : B →L[ℂ] B => f b) hS
  have hRv (a : A) : (R†) (R a) = a := congrArg (fun f : A →L[ℂ] A => f a) hR
  ext a
  simp only [adjoint_comp, comp_apply, hSv, hRv, one_def, id_apply]

theorem rowPreparation_isometry (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (c : ℝ) (hc : |c| ≤ 1) :
    (rowPreparation Q c)† ∘L rowPreparation Q c = 1 :=
  isometry_comp (preparation Q c) (rowEmbedding (K := K)).toContinuousLinearMap
    (preparation_isometry Q hQ c hc) (LinearIsometry.adjoint_comp_self _)

theorem columnPreparation_isometry (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) (c : ℝ) (hc : |c| ≤ 1) :
    (columnPreparation Q c)† ∘L columnPreparation Q c = 1 :=
  isometry_comp (preparation Q c) (columnEmbedding (K := K)).toContinuousLinearMap
    (preparation_isometry Q hQ c hc) (LinearIsometry.adjoint_comp_self _)

end Spectator

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Workspace (n Z : Type*) [Fintype n] [Fintype Z] :=
  Triple (SparseFlagEmbedding.Space (n × n) Z)

/-- Native oracles leave the fresh flag unchanged in every sector. -/
def oracles (D : Data X n Z s) : Query → X → Workspace n Z →L[ℂ] Workspace n Z :=
  fun q x => spectator (NativeSparseBlockEncoding.oracles D q x)

omit [DecidableEq Z] in
theorem oracles_unitary (D : Data X n Z s) (q : Query) (x : X) :
    IsUnitary (oracles D q x) :=
  spectator_unitary _ (NativeSparseBlockEncoding.oracles_unitary D q x)

/-- All query-free operations in this lifted circuit are fixed independently
of the matrix oracle input. -/
def lifted (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseBlockEncoding.oracles D)) :
    MultiOracleCircuit.Program (oracles D) :=
  EncodedMultiOracle.liftProgram fresh.toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self _) p

omit [DecidableEq Z] in
theorem lifted_prepares (D : Data X n Z s)
    (p : MultiOracleCircuit.Program (NativeSparseBlockEncoding.oracles D)) (x : X) :
    (lifted D p).eval x ∘L fresh.toContinuousLinearMap =
      fresh.toContinuousLinearMap ∘L p.eval x :=
  EncodedMultiOracle.liftProgram_eval _ (LinearIsometry.adjoint_comp_self _)
    (oracles_unitary D) (NativeSparseBlockEncoding.oracles_unitary D)
    (fun q x => spectator_fresh (NativeSparseBlockEncoding.oracles D q x)) p x

/-- One native row locator, two value calls, and a fixed attenuation gate. -/
def rowProgram (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    MultiOracleCircuit.Program (oracles D) :=
  .seq (.fixed (rowGate NativeSparsePhaseSequence.goodProjection c)
    (rowGate_unitary _ NativeSparsePhaseSequence.goodProjection_orthogonal c hc))
    (lifted D (NativeSparseBlockEncoding.rowProgram D))

/-- Column attenuation uses the distinct fresh column-failure sector. -/
def columnProgram (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    MultiOracleCircuit.Program (oracles D) :=
  .seq (.fixed (columnGate NativeSparsePhaseSequence.goodProjection c)
    (columnGate_unitary _ NativeSparsePhaseSequence.goodProjection_orthogonal c hc))
    (lifted D (NativeSparseBlockEncoding.columnProgram D))

@[simp] theorem rowProgram_count (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    (rowProgram D c hc).count = 3 := by simp [rowProgram, lifted]

@[simp] theorem columnProgram_count (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    (columnProgram D c hc).count = 3 := by simp [columnProgram, lifted]

theorem rowProgram_cost (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (w : Query → ℕ) :
    (rowProgram D c hc).cost w = w .rowLocation + 2 * w .value := by
  simpa [rowProgram, lifted] using NativeSparseBlockEncoding.rowProgram_cost D w

theorem columnProgram_cost (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (w : Query → ℕ) :
    (columnProgram D c hc).cost w = w .columnLocation + 2 * w .value := by
  simpa [columnProgram, lifted] using NativeSparseBlockEncoding.columnProgram_cost D w

/-- The complete initialization, with both fresh failure sectors empty. -/
def input (D : Data X n Z s) : EuclideanSpace ℂ n →ₗᵢ[ℂ] Workspace n Z :=
  fresh.comp (NativeSparseBlockEncoding.input D)

theorem input_adjoint_comp (D : Data X n Z s) :
    (input D).toContinuousLinearMap† ∘L (input D).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- Actual row and column output maps, including every failure amplitude. -/
def rowState (D : Data X n Z s) (c : ℝ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] Workspace n Z :=
  rowPreparation NativeSparsePhaseSequence.goodProjection c ∘L
    NativeSparsePhaseSequence.rowState D x

def columnState (D : Data X n Z s) (c : ℝ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] Workspace n Z :=
  columnPreparation NativeSparsePhaseSequence.goodProjection c ∘L
    NativeSparsePhaseSequence.columnState D x

theorem row_preparation (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    (rowProgram D c hc).eval x ∘L (input D).toContinuousLinearMap = rowState D c x := by
  change (rowGate _ c ∘L (lifted D (NativeSparseBlockEncoding.rowProgram D)).eval x) ∘L
    (fresh.toContinuousLinearMap ∘L (NativeSparseBlockEncoding.input D).toContinuousLinearMap) = _
  rw [comp_assoc, ← comp_assoc ((lifted D _).eval x), lifted_prepares,
    comp_assoc, NativeSparsePhaseSequence.row_prepares, ← comp_assoc]
  change (rowGate _ c ∘L rowEmbedding.toContinuousLinearMap ∘L clean.toContinuousLinearMap) ∘L _ = _
  rw [rowGate_preparation]
  rfl

theorem column_preparation (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    (columnProgram D c hc).eval x ∘L (input D).toContinuousLinearMap = columnState D c x := by
  change (columnGate _ c ∘L (lifted D (NativeSparseBlockEncoding.columnProgram D)).eval x) ∘L
    (fresh.toContinuousLinearMap ∘L (NativeSparseBlockEncoding.input D).toContinuousLinearMap) = _
  rw [comp_assoc, ← comp_assoc ((lifted D _).eval x), lifted_prepares,
    comp_assoc, NativeSparsePhaseSequence.column_prepares, ← comp_assoc]
  change (columnGate _ c ∘L rowEmbedding.toContinuousLinearMap ∘L clean.toContinuousLinearMap) ∘L _ = _
  rw [columnGate_preparation]
  rfl

/-- The physical clean-value encoding preserves the sparse failure separation. -/
theorem old_failure_orthogonal (D : Data X n Z s) (x : X) :
    (NativeSparsePhaseSequence.rowState D x)† ∘L
      (1 - NativeSparsePhaseSequence.goodProjection) ∘L
        NativeSparsePhaseSequence.columnState D x = 0 := by
  rw [NativeSparsePhaseSequence.rowState, NativeSparsePhaseSequence.columnState,
    NativeSparsePhaseSequence.goodProjection,
    failure_lift _ (LinearIsometry.adjoint_comp_self _)]
  exact SparseFreshAttenuation.old_failure_orthogonal _ _ _ _

/-- Exact full-state overlap after attenuation, without a residual orthogonality premise. -/
theorem overlap (D : Data X n Z s) (c : ℝ) (x : X) :
    (rowState D c x)† ∘L columnState D c x =
      ((c : ℂ) ^ 2) • SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  rw [rowState, columnState, prepared_overlap_full _
    NativeSparsePhaseSequence.goodProjection_orthogonal c _ _ (old_failure_orthogonal D x)]
  congr 1
  rw [← NativeSparsePhaseSequence.row_prepares, ← NativeSparsePhaseSequence.column_prepares,
    ← PreparedOverlapProgram.compression]
  exact NativeSparseBlockEncoding.compression D x

/-- The full six-query attenuated block encoding. -/
def program (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    MultiOracleCircuit.Program (oracles D) :=
  PreparedOverlapProgram.program (rowProgram D c hc) (columnProgram D c hc)

@[simp] theorem program_count (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    (program D c hc).count = 6 := by simp [program]

theorem program_cost (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (w : Query → ℕ) :
    (program D c hc).cost w = w .rowLocation + w .columnLocation + 4 * w .value := by
  rw [program, PreparedOverlapProgram.program_cost, rowProgram_cost, columnProgram_cost]
  omega

@[simp] theorem program_row_count (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    (program D c hc).labelCount .rowLocation = 1 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

@[simp] theorem program_column_count (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    (program D c hc).labelCount .columnLocation = 1 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

@[simp] theorem program_value_count (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) :
    (program D c hc).labelCount .value = 4 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

theorem program_unitary (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    IsUnitary ((program D c hc).eval x) :=
  (program D c hc).eval_unitary (oracles_unitary D) x

theorem compression (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    (input D).toContinuousLinearMap† ∘L (program D c hc).eval x ∘L
      (input D).toContinuousLinearMap =
      ((c : ℂ) ^ 2) • SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  rw [program, PreparedOverlapProgram.compression, row_preparation, column_preparation]
  exact overlap D c x

/-- Quarter-gain normalization of the actual native-query circuit. -/
theorem quarter_compression (D : Data X n Z s) (x : X) :
    (input D).toContinuousLinearMap† ∘L (program D (1 / 4) (by norm_num)).eval x ∘L
      (input D).toContinuousLinearMap =
      (1 / 16 : ℂ) • SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  rw [compression]
  norm_num

/-- Fixed success projector: original success with both fresh flags still clean. -/
def goodProjection : Workspace n Z →L[ℂ] Workspace n Z :=
  fresh.toContinuousLinearMap ∘L NativeSparsePhaseSequence.goodProjection ∘L
    fresh.toContinuousLinearMap†

omit [DecidableEq n] in
theorem goodProjection_orthogonal :
    PhaseSubspaceGates.IsOrthogonalProjection (goodProjection (n := n) (Z := Z)) :=
  NativeSparsePhaseSequence.projection_lift _ (LinearIsometry.adjoint_comp_self _)
    _ NativeSparsePhaseSequence.goodProjection_orthogonal

/-- Attenuation preserves the full row output norm. -/
theorem rowState_isometry (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    (rowState D c x)† ∘L rowState D c x = 1 :=
  isometry_comp (NativeSparsePhaseSequence.rowState D x)
    (rowPreparation NativeSparsePhaseSequence.goodProjection c)
    (NativeSparsePhaseSequence.rowState_isometry D x)
    (rowPreparation_isometry _ NativeSparsePhaseSequence.goodProjection_orthogonal c hc)

/-- Attenuation also preserves the complete column output norm. -/
theorem columnState_isometry (D : Data X n Z s) (c : ℝ) (hc : |c| ≤ 1) (x : X) :
    (columnState D c x)† ∘L columnState D c x = 1 :=
  isometry_comp (NativeSparsePhaseSequence.columnState D x)
    (columnPreparation NativeSparsePhaseSequence.goodProjection c)
    (NativeSparsePhaseSequence.columnState_isometry D x)
    (columnPreparation_isometry _ NativeSparsePhaseSequence.goodProjection_orthogonal c hc)

/-- The actual native row success spectrum is attenuated by exactly `c²`. -/
theorem row_compression (D : Data X n Z s) (c : ℝ) (x : X) :
    (rowState D c x)† ∘L goodProjection ∘L rowState D c x =
      ((c : ℂ) ^ 2) • SparseSuccessProjection.diagonal
        (SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x)) := by
  unfold rowState goodProjection
  rw [adjoint_comp]
  calc
    _ = (NativeSparsePhaseSequence.rowState D x)† ∘L
        ((rowPreparation NativeSparsePhaseSequence.goodProjection c)† ∘L
          (fresh.toContinuousLinearMap ∘L NativeSparsePhaseSequence.goodProjection ∘L
            fresh.toContinuousLinearMap†) ∘L
          rowPreparation NativeSparsePhaseSequence.goodProjection c) ∘L
        NativeSparsePhaseSequence.rowState D x := by simp only [comp_assoc]
    _ = _ := by
      rw [success_gram _ NativeSparsePhaseSequence.goodProjection_orthogonal c _
        (row_retained _ c), smul_comp, comp_smul, NativeSparsePhaseSequence.row_compression]

/-- Column success has the same gain, retaining its own analytical column sum. -/
theorem column_compression (D : Data X n Z s) (c : ℝ) (x : X) :
    (columnState D c x)† ∘L goodProjection ∘L columnState D c x =
      ((c : ℂ) ^ 2) • SparseSuccessProjection.diagonal
        (SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x)) := by
  unfold columnState goodProjection
  rw [adjoint_comp]
  calc
    _ = (NativeSparsePhaseSequence.columnState D x)† ∘L
        ((columnPreparation NativeSparsePhaseSequence.goodProjection c)† ∘L
          (fresh.toContinuousLinearMap ∘L NativeSparsePhaseSequence.goodProjection ∘L
            fresh.toContinuousLinearMap†) ∘L
          columnPreparation NativeSparsePhaseSequence.goodProjection c) ∘L
        NativeSparsePhaseSequence.columnState D x := by simp only [comp_assoc]
    _ = _ := by
      rw [success_gram _ NativeSparsePhaseSequence.goodProjection_orthogonal c _
        (column_retained _ c), smul_comp, comp_smul, NativeSparsePhaseSequence.column_compression]

end
end SparseHamiltonian.NativeSparseAttenuation
