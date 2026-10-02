import SparseHamiltonian.PreparationInvariantPlane

/-!
# Counted phase circuits for native sparse preparations

The fixed input projector and fixed good-flag projector act on the complete
native-oracle workspace. Their compressed success eigenvalues are calculated
from the actual sparse preparations. Analytical row sums are never circuit
inputs. Any supplied phase list produces an explicit native-oracle circuit
with all location and value calls separately counted.
-/

namespace SparseHamiltonian.NativeSparsePhaseSequence

noncomputable section
set_option maxRecDepth 2000
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct

section Transport
variable {A B C : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup C] [InnerProductSpace ℂ C] [CompleteSpace C]

/-- Isometric encoding transports orthogonal projectors, with zero action
outside the encoded workspace. -/
theorem projection_lift (J : A →L[ℂ] B) (hJ : J† ∘L J = 1)
    (Q : A →L[ℂ] A) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q) :
    PhaseSubspaceGates.IsOrthogonalProjection (J ∘L Q ∘L J†) := by
  constructor
  · simp only [star_eq_adjoint, adjoint_comp, adjoint_adjoint]
    have h := hQ.1
    change Q† = Q at h
    rw [h]
    exact comp_assoc _ _ _
  · have hJv (a : A) : (J†) (J a) = a := congrArg (fun f : A →L[ℂ] A => f a) hJ
    have hQQ (a : A) : Q (Q a) = Q a := congrArg (fun f : A →L[ℂ] A => f a) hQ.2
    ext v
    simp only [mul_apply_eq_comp, comp_apply, hJv, hQQ]

/-- Success compression is unchanged by a common clean-workspace isometry. -/
theorem compression_lift (J : A →L[ℂ] B) (hJ : J† ∘L J = 1)
    (Q : A →L[ℂ] A) (R : C →L[ℂ] A) :
    (J ∘L R)† ∘L (J ∘L Q ∘L J†) ∘L (J ∘L R) = R† ∘L Q ∘L R := by
  have hJv (a : A) : (J†) (J a) = a := congrArg (fun f : A →L[ℂ] A => f a) hJ
  ext v
  simp only [adjoint_comp, comp_apply, hJv]

end Transport

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Projection onto the common fixed uniform-slot initialization. -/
def inputProjection (D : Data X n Z s) :
    SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  (input D).toContinuousLinearMap ∘L (input D).toContinuousLinearMap†

/-- Projection onto a clean value register and the shared good flag. -/
def goodProjection :
    SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  SparseFlagEmbedding.clean.toContinuousLinearMap ∘L SparseSuccessProjection.good ∘L
    SparseFlagEmbedding.clean.toContinuousLinearMap†

theorem inputProjection_orthogonal (D : Data X n Z s) :
    PhaseSubspaceGates.IsOrthogonalProjection (inputProjection D) := by
  have h := projection_lift (input D).toContinuousLinearMap (input_adjoint_comp D)
    1 (by constructor <;> simp)
  simpa only [one_def, id_comp, inputProjection] using h

omit [DecidableEq n] in
theorem goodProjection_orthogonal :
    PhaseSubspaceGates.IsOrthogonalProjection (goodProjection (n := n) (Z := Z)) :=
  projection_lift (A := SparseSlotStates.Space n)
    (SparseFlagEmbedding.clean (A := n × n) (Z := Z)).toContinuousLinearMap
    (LinearIsometry.adjoint_comp_self _) SparseSuccessProjection.good
    SparseSuccessProjection.good_orthogonal

/-- Row preparation as a complete physical output map. -/
def rowState (D : Data X n Z s) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  SparseFlagEmbedding.clean.toContinuousLinearMap ∘L
    SparseSlotStates.row (D.matrix x) D.scale (D.rowloc x)

/-- Column preparation in the same physical output space. -/
def columnState (D : Data X n Z s) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  SparseFlagEmbedding.clean.toContinuousLinearMap ∘L
    SparseSlotStates.column (D.matrix x) D.scale (D.colloc x)

theorem row_prepares (D : Data X n Z s) (x : X) :
    (NativeSparseBlockEncoding.rowProgram D).eval x ∘L (input D).toContinuousLinearMap =
      rowState D x := row_preparation D x

theorem column_prepares (D : Data X n Z s) (x : X) :
    (NativeSparseBlockEncoding.columnProgram D).eval x ∘L (input D).toContinuousLinearMap =
      columnState D x := column_preparation D x

theorem rowState_isometry (D : Data X n Z s) (x : X) :
    (rowState D x)† ∘L rowState D x = 1 := by
  apply (rowState D x).norm_map_iff_adjoint_comp_self.mp
  intro v
  change ‖SparseFlagEmbedding.clean
    (SparseSlotStates.row (D.matrix x) D.scale (D.rowloc x) v)‖ = ‖v‖
  rw [LinearIsometry.norm_map]
  exact SparseSlotStates.row_norm D.slots_pos (D.matrix x) D.scale D.scale_pos
    (fun i j => by rw [← D.decoded x i j]; exact D.decode_bound _ _)
    (D.rowloc x) (D.row_injective x) v

theorem columnState_isometry (D : Data X n Z s) (x : X) :
    (columnState D x)† ∘L columnState D x = 1 := by
  apply (columnState D x).norm_map_iff_adjoint_comp_self.mp
  intro v
  change ‖SparseFlagEmbedding.clean
    (SparseSlotStates.column (D.matrix x) D.scale (D.colloc x) v)‖ = ‖v‖
  rw [LinearIsometry.norm_map]
  exact SparseSlotStates.column_norm D.slots_pos (D.matrix x) D.scale D.scale_pos
    (fun i j => by rw [← D.decoded x i j]; exact D.decode_bound _ _)
    (D.colloc x) (D.column_injective x) v

/-- The physical row success spectrum is exactly the analytical sparse row sum. -/
theorem row_compression (D : Data X n Z s) (x : X) :
    (rowState D x)† ∘L goodProjection ∘L rowState D x =
      SparseSuccessProjection.diagonal (SparseSuccessProjection.rowSuccess
        (D.matrix x) D.scale (D.rowloc x)) := by
  rw [rowState, goodProjection, compression_lift _ (LinearIsometry.adjoint_comp_self _)]
  exact SparseSuccessProjection.row_compression _ _ D.scale_pos _

theorem column_compression (D : Data X n Z s) (x : X) :
    (columnState D x)† ∘L goodProjection ∘L columnState D x =
      SparseSuccessProjection.diagonal (SparseSuccessProjection.columnSuccess
        (D.matrix x) D.scale (D.colloc x)) := by
  rw [columnState, goodProjection, compression_lift _ (LinearIsometry.adjoint_comp_self _)]
  exact SparseSuccessProjection.column_compression _ _ D.scale_pos _

theorem row_compression_basis (D : Data X n Z s) (x : X) (i : n) :
    ((rowState D x)†) (goodProjection (rowState D x (EuclideanSpace.single i 1))) =
      (SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i : ℂ) •
        EuclideanSpace.single i 1 := by
  have h := congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n =>
    f (EuclideanSpace.single i 1)) (row_compression D x)
  apply PiLp.ext
  intro j
  have hj := congrArg (fun v : EuclideanSpace ℂ n => v j) h
  by_cases hij : i = j
  · subst j; simpa using hj
  · simpa [hij] using hj

theorem column_compression_basis (D : Data X n Z s) (x : X) (j : n) :
    ((columnState D x)†) (goodProjection (columnState D x (EuclideanSpace.single j 1))) =
      (SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) j : ℂ) •
        EuclideanSpace.single j 1 := by
  have h := congrArg (fun f : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n =>
    f (EuclideanSpace.single j 1)) (column_compression D x)
  apply PiLp.ext
  intro i
  have hi := congrArg (fun v : EuclideanSpace ℂ n => v i) h
  by_cases hji : j = i
  · subst i; simpa using hi
  · simpa [hji] using hi

/-- The scalar row signal is a proof parameter, not a supplied row-sum oracle. -/
def rowSignal (D : Data X n Z s) (x : X) (i : n) : ℝ :=
  Real.sqrt (SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i)

def columnSignal (D : Data X n Z s) (x : X) (j : n) : ℝ :=
  Real.sqrt (SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) j)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rowSignal_sq (D : Data X n Z s) (x : X) (i : n) :
    rowSignal D x i ^ 2 =
      SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i :=
  Real.sq_sqrt (SparseSuccessProjection.rowSuccess_nonneg _ _ D.scale_pos.le _ _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem columnSignal_sq (D : Data X n Z s) (x : X) (j : n) :
    columnSignal D x j ^ 2 =
      SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) j :=
  Real.sq_sqrt (SparseSuccessProjection.columnSuccess_nonneg _ _ D.scale_pos.le _ _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem rowSignal_bound (D : Data X n Z s) (x : X) (i : n) : |rowSignal D x i| ≤ 1 := by
  have h := SparseSuccessProjection.rowSuccess_le_one D.slots_pos (D.matrix x) D.scale D.scale_pos
    (fun i j => by rw [← D.decoded x i j]; exact D.decode_bound _ _) (D.rowloc x)
    (D.row_injective x) i
  have hn : 0 ≤ rowSignal D x i := Real.sqrt_nonneg _
  rw [abs_of_nonneg hn]
  nlinarith [rowSignal_sq D x i]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem columnSignal_bound (D : Data X n Z s) (x : X) (j : n) : |columnSignal D x j| ≤ 1 := by
  have h := SparseSuccessProjection.columnSuccess_le_one D.slots_pos (D.matrix x) D.scale D.scale_pos
    (fun i j => by rw [← D.decoded x i j]; exact D.decode_bound _ _) (D.colloc x)
    (D.column_injective x) j
  have hn : 0 ≤ columnSignal D x j := Real.sqrt_nonneg _
  rw [abs_of_nonneg hn]
  nlinarith [columnSignal_sq D x j]

/-- Amplification phases are fixed and all location/value calls remain explicit. -/
def rowProgram (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    MultiOracleCircuit.Program (oracles D) :=
  InvariantPhaseSequence.nativePrepared (NativeSparseBlockEncoding.rowProgram D)
    (inputProjection D) goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal ss

def columnProgram (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    MultiOracleCircuit.Program (oracles D) :=
  InvariantPhaseSequence.nativePrepared (NativeSparseBlockEncoding.columnProgram D)
    (inputProjection D) goodProjection (inputProjection_orthogonal D) goodProjection_orthogonal ss

@[simp] theorem rowProgram_count (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    (rowProgram D ss).count = (2 * ss.length + 1) * 3 := by simp [rowProgram]

@[simp] theorem columnProgram_count (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) :
    (columnProgram D ss).count = (2 * ss.length + 1) * 3 := by simp [columnProgram]

theorem rowProgram_cost (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (w : Query → ℕ) :
    (rowProgram D ss).cost w = (2 * ss.length + 1) * (w .rowLocation + 2 * w .value) := by
  rw [rowProgram, InvariantPhaseSequence.nativePrepared_cost, NativeSparseBlockEncoding.rowProgram_cost]

theorem columnProgram_cost (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (w : Query → ℕ) :
    (columnProgram D ss).cost w = (2 * ss.length + 1) * (w .columnLocation + 2 * w .value) := by
  rw [columnProgram, InvariantPhaseSequence.nativePrepared_cost, NativeSparseBlockEncoding.columnProgram_cost]

theorem rowProgram_unitary (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    IsUnitary ((rowProgram D ss).eval x) := (rowProgram D ss).eval_unitary (oracles_unitary D) x

theorem columnProgram_unitary (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases) (x : X) :
    IsUnitary ((columnProgram D ss).eval x) := (columnProgram D ss).eval_unitary (oracles_unitary D) x

/-- The physical success compression has the square of the scalar signal as eigenvalue. -/
theorem rowSignal_eigen (D : Data X n Z s) (x : X) (i : n) :
    ((rowState D x)†) (goodProjection (rowState D x (EuclideanSpace.single i 1))) =
      (rowSignal D x i : ℂ) ^ 2 • EuclideanSpace.single i 1 := by
  have hs : (rowSignal D x i : ℂ) ^ 2 =
      (SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i : ℂ) := by
    exact_mod_cast rowSignal_sq D x i
  rw [hs]
  exact row_compression_basis D x i

/-- The analytical output plane is allowed to degenerate at zero or unit success. -/
def rowPlane (D : Data X n Z s) (x : X) (i : n) :
    ComplexAmplitudeRotation.Qubit →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  PreparationInvariantPlane.plane
    (PreparationInvariantPlane.goodDirection (rowState D x) goodProjection
      (EuclideanSpace.single i 1) (rowSignal D x i))
    (PreparationInvariantPlane.badDirection (rowState D x) goodProjection
      (EuclideanSpace.single i 1) (rowSignal D x i))

/-- Full output identity for the actual native sparse phase circuit. -/
theorem rowProgram_output (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    (rowProgram D ss).eval x ((input D).toContinuousLinearMap (EuclideanSpace.single i 1)) =
      rowPlane D x i (AmplitudePolynomialSequence.column (rowSignal D x i)
        (AmplitudePolynomialSequence.polynomials ss).1
        (AmplitudePolynomialSequence.polynomials ss).2) := by
  rw [rowProgram, InvariantPhaseSequence.nativePrepared_eval, inputProjection]
  have h := PreparationInvariantPlane.prepared_column
    (E := EuclideanSpace ℂ n) (K := SparseFlagEmbedding.Space (n × n) Z)
    ((NativeSparseBlockEncoding.rowProgram D).eval x)
    ((NativeSparseBlockEncoding.rowProgram D).eval_unitary (oracles_unitary D) x)
    (input D).toContinuousLinearMap (rowState D x) (row_prepares D x)
    (rowState_isometry D x) goodProjection goodProjection_orthogonal
    (EuclideanSpace.single i 1) (rowSignal D x i) (rowSignal_bound D x i)
    (rowSignal_eigen D x i) ss
  simpa only [rowPlane] using h

/-- Exact good polynomial on each original label; no row-sum query is supplied. -/
theorem rowProgram_good (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    goodProjection ((rowProgram D ss).eval x ((input D).toContinuousLinearMap (EuclideanSpace.single i 1))) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) •
        PreparationInvariantPlane.goodDirection (rowState D x) goodProjection
          (EuclideanSpace.single i 1) (rowSignal D x i) := by
  rw [rowProgram_output]
  simp only [rowPlane, PreparationInvariantPlane.plane_apply, map_add, map_smul,
    PreparationInvariantPlane.good_fixed _ _ goodProjection_orthogonal,
    PreparationInvariantPlane.bad_kernel _ _ goodProjection_orthogonal,
    AmplitudePolynomialSequence.column_false, smul_zero, add_zero]

/-- A supplied scalar relative approximation bounds the actual good-output error. -/
theorem rowProgram_good_error (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (rowSignal D x i : ℂ) -
      gain * (rowSignal D x i : ℂ)‖ ≤ δ * |rowSignal D x i|) :
    ‖goodProjection ((rowProgram D ss).eval x ((input D).toContinuousLinearMap (EuclideanSpace.single i 1))) -
      gain • goodProjection (rowState D x (EuclideanSpace.single i 1))‖ ≤
      δ * ‖goodProjection (rowState D x (EuclideanSpace.single i 1))‖ := by
  have hg := (PreparationInvariantPlane.good_scale (rowState D x) goodProjection
    goodProjection_orthogonal (EuclideanSpace.single i 1) (rowSignal D x i)
    (rowSignal_eigen D x i)).symm
  rw [rowProgram_good, hg, smul_smul, ← sub_smul, norm_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (δ * |rowSignal D x i|) *
        ‖PreparationInvariantPlane.goodDirection (rowState D x) goodProjection
          (EuclideanSpace.single i 1) (rowSignal D x i)‖ :=
      mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = _ := by ring

/-- The physical success compression has the square of the scalar signal as eigenvalue. -/
theorem columnSignal_eigen (D : Data X n Z s) (x : X) (i : n) :
    ((columnState D x)†) (goodProjection (columnState D x (EuclideanSpace.single i 1))) =
      (columnSignal D x i : ℂ) ^ 2 • EuclideanSpace.single i 1 := by
  have hs : (columnSignal D x i : ℂ) ^ 2 =
      (SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) i : ℂ) := by
    exact_mod_cast columnSignal_sq D x i
  rw [hs]
  exact column_compression_basis D x i

/-- The analytical output plane is allowed to degenerate at zero or unit success. -/
def columnPlane (D : Data X n Z s) (x : X) (i : n) :
    ComplexAmplitudeRotation.Qubit →L[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  PreparationInvariantPlane.plane
    (PreparationInvariantPlane.goodDirection (columnState D x) goodProjection
      (EuclideanSpace.single i 1) (columnSignal D x i))
    (PreparationInvariantPlane.badDirection (columnState D x) goodProjection
      (EuclideanSpace.single i 1) (columnSignal D x i))

/-- Full output identity for the actual native sparse phase circuit. -/
theorem columnProgram_output (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    (columnProgram D ss).eval x ((input D).toContinuousLinearMap (EuclideanSpace.single i 1)) =
      columnPlane D x i (AmplitudePolynomialSequence.column (columnSignal D x i)
        (AmplitudePolynomialSequence.polynomials ss).1
        (AmplitudePolynomialSequence.polynomials ss).2) := by
  rw [columnProgram, InvariantPhaseSequence.nativePrepared_eval, inputProjection]
  have h := PreparationInvariantPlane.prepared_column
    (E := EuclideanSpace ℂ n) (K := SparseFlagEmbedding.Space (n × n) Z)
    ((NativeSparseBlockEncoding.columnProgram D).eval x)
    ((NativeSparseBlockEncoding.columnProgram D).eval_unitary (oracles_unitary D) x)
    (input D).toContinuousLinearMap (columnState D x) (column_prepares D x)
    (columnState_isometry D x) goodProjection goodProjection_orthogonal
    (EuclideanSpace.single i 1) (columnSignal D x i) (columnSignal_bound D x i)
    (columnSignal_eigen D x i) ss
  simpa only [columnPlane] using h

/-- Exact good polynomial on each original label; no row-sum query is supplied. -/
theorem columnProgram_good (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) :
    goodProjection ((columnProgram D ss).eval x ((input D).toContinuousLinearMap (EuclideanSpace.single i 1))) =
      (AmplitudePolynomialSequence.polynomials ss).1.eval (columnSignal D x i : ℂ) •
        PreparationInvariantPlane.goodDirection (columnState D x) goodProjection
          (EuclideanSpace.single i 1) (columnSignal D x i) := by
  rw [columnProgram_output]
  simp only [columnPlane, PreparationInvariantPlane.plane_apply, map_add, map_smul,
    PreparationInvariantPlane.good_fixed _ _ goodProjection_orthogonal,
    PreparationInvariantPlane.bad_kernel _ _ goodProjection_orthogonal,
    AmplitudePolynomialSequence.column_false, smul_zero, add_zero]

/-- A supplied scalar relative approximation bounds the actual good-output error. -/
theorem columnProgram_good_error (D : Data X n Z s) (ss : List AmplitudePolynomialSequence.Phases)
    (x : X) (i : n) (gain : ℂ) (δ : ℝ)
    (herr : ‖(AmplitudePolynomialSequence.polynomials ss).1.eval (columnSignal D x i : ℂ) -
      gain * (columnSignal D x i : ℂ)‖ ≤ δ * |columnSignal D x i|) :
    ‖goodProjection ((columnProgram D ss).eval x ((input D).toContinuousLinearMap (EuclideanSpace.single i 1))) -
      gain • goodProjection (columnState D x (EuclideanSpace.single i 1))‖ ≤
      δ * ‖goodProjection (columnState D x (EuclideanSpace.single i 1))‖ := by
  have hg := (PreparationInvariantPlane.good_scale (columnState D x) goodProjection
    goodProjection_orthogonal (EuclideanSpace.single i 1) (columnSignal D x i)
    (columnSignal_eigen D x i)).symm
  rw [columnProgram_good, hg, smul_smul, ← sub_smul, norm_smul, norm_smul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (δ * |columnSignal D x i|) *
        ‖PreparationInvariantPlane.goodDirection (columnState D x) goodProjection
          (EuclideanSpace.single i 1) (columnSignal D x i)‖ :=
      mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    _ = _ := by ring

end
end SparseHamiltonian.NativeSparsePhaseSequence
