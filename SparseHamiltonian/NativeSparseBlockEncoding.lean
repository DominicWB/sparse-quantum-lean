import SparseHamiltonian.PreparedOverlapProgram

/-!
# A six-query block encoding from native sparse oracles

The original `s` slots are prepared uniformly. One native in-place location
query and two ordinary value queries prepare each of the row and column
states. Their complete outputs share one physical space, with distinct local
failure flags. The adjoint row program followed by the column program has
exactly one row-location query, one column-location query, and four value
queries; its fixed-input compression is `H / (s * a)`.
-/

namespace SparseHamiltonian.NativeSparseBlockEncoding

noncomputable section
set_option maxHeartbeats 400000
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

/-- Input data and valid-basis promises for the native sparse oracle model.
The decoder and original slot labels are fixed independently of `x`. The
location oracles may act arbitrarily off their promised valid basis states,
provided they are unitary on the complete physical address space. -/
structure Data (X n Z : Type*) [Fintype n] [DecidableEq n] (s : ℕ) where
  slot : Fin s ↪ n
  slots_pos : 0 < s
  scale : ℝ
  scale_pos : 0 < scale
  matrix : X → Matrix n n ℂ
  table : X → (n × n) → Z
  decode : (n × n) → Z → ℂ
  decode_bound : ∀ a z, ‖decode a z‖ ≤ scale
  decoded : ∀ x i j, decode (i, j) (table x (i, j)) = matrix x i j
  rowloc : X → n → Fin s → n
  colloc : X → n → Fin s → n
  row_injective : ∀ x i, Function.Injective (rowloc x i)
  column_injective : ∀ x j, Function.Injective (colloc x j)
  row_covers : ∀ x i j, matrix x i j ≠ 0 → SparseSlotStates.selected (rowloc x) i j
  column_covers : ∀ x i j, matrix x i j ≠ 0 → SparseSlotStates.selected (colloc x) j i
  rowOracle : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n)
  columnOracle : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n)
  row_unitary : ∀ x, IsUnitary (rowOracle x)
  column_unitary : ∀ x, IsUnitary (columnOracle x)
  row_valid : ∀ x i k, rowOracle x (EuclideanSpace.single (i, slot k) 1) =
    EuclideanSpace.single (i, rowloc x i k) 1
  column_valid : ∀ x j k, columnOracle x (EuclideanSpace.single (j, slot k) 1) =
    EuclideanSpace.single (colloc x j k, j) 1

/-- Each syntactic query names exactly one native primitive. -/
inductive Query where
  | rowLocation
  | columnLocation
  | value
  deriving DecidableEq

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  {s : ℕ}

/-- All six calls act on the same address, value, and three-flag space. -/
def oracles (D : Data X n Z s) : Query → X →
    SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z
  | .rowLocation => SparseFlagEmbedding.location D.rowOracle
  | .columnLocation => SparseFlagEmbedding.location D.columnOracle
  | .value => LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) D.table

/-- Native unitarity, including all unpromised inputs, survives spectator
extension to the complete physical workspace. -/
theorem oracles_unitary (D : Data X n Z s) (q : Query) (x : X) :
    IsUnitary (oracles D q x) := by
  cases q with
  | rowLocation => exact SparseFlagEmbedding.location_unitary D.rowOracle D.row_unitary x
  | columnLocation => exact SparseFlagEmbedding.location_unitary D.columnOracle D.column_unitary x
  | value => exact LookupControlledGate.oracle_unitary D.table x

/-- The fixed row rotation decoder. -/
def rowDecode (D : Data X n Z s) (a : n × n) (z : Z) : ℂ :=
  SparseEntryAmplitudes.rowAmplitude D.scale (D.decode a z)

/-- The fixed column rotation decoder includes the complex entry phase. -/
def columnDecode (D : Data X n Z s) (a : n × n) (z : Z) : ℂ :=
  SparseEntryAmplitudes.columnAmplitude D.scale (D.decode a z)

omit [Fintype Z] [AddCommGroup Z] in
theorem rowDecode_bound (D : Data X n Z s) (a : n × n) (z : Z) :
    ‖rowDecode D a z‖ ≤ 1 :=
  SparseSlotStates.rowAmplitude_norm_le D.scale D.scale_pos _ (D.decode_bound a z)

omit [Fintype Z] [AddCommGroup Z] in
theorem columnDecode_bound (D : Data X n Z s) (a : n × n) (z : Z) :
    ‖columnDecode D a z‖ ≤ 1 :=
  SparseSlotStates.columnAmplitude_norm_le D.scale D.scale_pos _ (D.decode_bound a z)

/-- The two preparation labels map to ordinary common-workspace query labels. -/
def rowLabel : SparseSlotPreparation.Query → Query
  | .location => .rowLocation
  | .value => .value

def columnLabel : SparseSlotPreparation.Query → Query
  | .location => .columnLocation
  | .value => .value

/-- The actual row program, after a fixed flag encoding and syntactic relabeling. -/
def rowProgram (D : Data X n Z s) : MultiOracleCircuit.Program (oracles D) :=
  MultiOracleCircuit.Program.relabel rowLabel
    (EncodedMultiOracle.liftProgram
      (F := fun q => oracles D (rowLabel q))
      SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap
      (LinearIsometry.adjoint_comp_self _)
      (SparseSlotPreparation.program D.rowOracle (rowDecode D) (rowDecode_bound D) D.table))

/-- The actual column program uses the same physical space and value oracle. -/
def columnProgram (D : Data X n Z s) : MultiOracleCircuit.Program (oracles D) :=
  MultiOracleCircuit.Program.relabel columnLabel
    (EncodedMultiOracle.liftProgram
      (F := fun q => oracles D (columnLabel q))
      SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap
      (LinearIsometry.adjoint_comp_self _)
      (SparseSlotPreparation.program D.columnOracle (columnDecode D) (columnDecode_bound D) D.table))

@[simp] theorem rowProgram_count (D : Data X n Z s) : (rowProgram D).count = 3 := by
  simp [rowProgram]

@[simp] theorem columnProgram_count (D : Data X n Z s) : (columnProgram D).count = 3 := by
  simp [columnProgram]

/-- Row preparation costs one row-location call and two value calls. -/
theorem rowProgram_cost (D : Data X n Z s) (w : Query → ℕ) :
    (rowProgram D).cost w = w .rowLocation + 2 * w .value := by
  simp only [rowProgram, MultiOracleCircuit.Program.cost_relabel,
    EncodedMultiOracle.liftProgram_cost, SparseSlotPreparation.program_cost]
  rfl

/-- Column preparation costs one column-location call and two value calls. -/
theorem columnProgram_cost (D : Data X n Z s) (w : Query → ℕ) :
    (columnProgram D).cost w = w .columnLocation + 2 * w .value := by
  simp only [columnProgram, MultiOracleCircuit.Program.cost_relabel,
    EncodedMultiOracle.liftProgram_cost, SparseSlotPreparation.program_cost]
  rfl

/-- The counted block-encoding program is the inverse row preparation after
the forward column preparation. -/
def program (D : Data X n Z s) : MultiOracleCircuit.Program (oracles D) :=
  PreparedOverlapProgram.program (rowProgram D) (columnProgram D)

@[simp] theorem program_count (D : Data X n Z s) : (program D).count = 6 := by
  simp [program]

/-- Every physical oracle call remains explicit after composition. -/
theorem program_cost (D : Data X n Z s) (w : Query → ℕ) :
    (program D).cost w = w .rowLocation + w .columnLocation + 4 * w .value := by
  rw [program, PreparedOverlapProgram.program_cost, rowProgram_cost, columnProgram_cost]
  omega

@[simp] theorem program_row_count (D : Data X n Z s) :
    (program D).labelCount .rowLocation = 1 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

@[simp] theorem program_column_count (D : Data X n Z s) :
    (program D).labelCount .columnLocation = 1 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

@[simp] theorem program_value_count (D : Data X n Z s) :
    (program D).labelCount .value = 4 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

/-- The complete six-query circuit is unitary, with no postselection. -/
theorem program_unitary (D : Data X n Z s) (x : X) :
    IsUnitary ((program D).eval x) :=
  (program D).eval_unitary (oracles_unitary D) x

/-- Row encoding intertwines every actual primitive; no controlled location
oracle or coherent choice of oracle label is assumed. -/
theorem rowOracles_intertwine (D : Data X n Z s) (q : SparseSlotPreparation.Query) (x : X) :
    oracles D (rowLabel q) x ∘L SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap =
      SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap ∘L
        SparseSlotPreparation.oracles D.rowOracle D.table q x := by
  cases q with
  | location => exact SparseFlagEmbedding.location_rowEmbedding D.rowOracle x
  | value => exact SparseFlagEmbedding.value_rowEmbedding D.table x

/-- Column encoding uses its native location primitive and the same value call. -/
theorem columnOracles_intertwine (D : Data X n Z s) (q : SparseSlotPreparation.Query) (x : X) :
    oracles D (columnLabel q) x ∘L SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap =
      SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap ∘L
        SparseSlotPreparation.oracles D.columnOracle D.table q x := by
  cases q with
  | location => exact SparseFlagEmbedding.location_columnEmbedding D.columnOracle x
  | value => exact SparseFlagEmbedding.value_columnEmbedding D.table x

/-- Correctness of the complete lifted row program on its fixed flag encoding. -/
theorem rowProgram_intertwines (D : Data X n Z s) (x : X) :
    (rowProgram D).eval x ∘L SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap =
      SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap ∘L
        (SparseSlotPreparation.program D.rowOracle (rowDecode D) (rowDecode_bound D) D.table).eval x := by
  have hO : ∀ q x, IsUnitary (SparseSlotPreparation.oracles D.rowOracle D.table q x) := by
    intro q x
    cases q with
    | location => exact SparseSlotPreparation.location_unitary D.rowOracle D.row_unitary x
    | value => exact LookupControlledGate.oracle_unitary D.table x
  unfold rowProgram
  rw [MultiOracleCircuit.Program.eval_relabel]
  exact EncodedMultiOracle.liftProgram_eval (F := fun q => oracles D (rowLabel q)) SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap
      (LinearIsometry.adjoint_comp_self _)
      (fun q x => oracles_unitary D (rowLabel q) x) hO (rowOracles_intertwine D)
      (SparseSlotPreparation.program D.rowOracle (rowDecode D) (rowDecode_bound D) D.table) x

/-- Correctness of the complete lifted column program on its fixed flag encoding. -/
theorem columnProgram_intertwines (D : Data X n Z s) (x : X) :
    (columnProgram D).eval x ∘L SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap =
      SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap ∘L
        (SparseSlotPreparation.program D.columnOracle (columnDecode D) (columnDecode_bound D) D.table).eval x := by
  have hO : ∀ q x, IsUnitary (SparseSlotPreparation.oracles D.columnOracle D.table q x) := by
    intro q x
    cases q with
    | location => exact SparseSlotPreparation.location_unitary D.columnOracle D.column_unitary x
    | value => exact LookupControlledGate.oracle_unitary D.table x
  unfold columnProgram
  rw [MultiOracleCircuit.Program.eval_relabel]
  exact EncodedMultiOracle.liftProgram_eval (F := fun q => oracles D (columnLabel q)) SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap
      (LinearIsometry.adjoint_comp_self _)
      (fun q x => oracles_unitary D (columnLabel q) x) hO (columnOracles_intertwine D)
      (SparseSlotPreparation.program D.columnOracle (columnDecode D) (columnDecode_bound D) D.table) x

variable [DecidableEq Z]

/-- Fixed initial uniform slots, clean value, and common good flag zero. -/
def input (D : Data X n Z s) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  SparseFlagEmbedding.rowEmbedding.comp
    (SparseSlotPreparation.input (UniformSlotPreparation.embedding D.slot D.slots_pos))

/-- Either flag encoding gives the same fixed initial state. -/
theorem input_eq_column (D : Data X n Z s) :
    input D = SparseFlagEmbedding.columnEmbedding.comp
      (SparseSlotPreparation.input (UniformSlotPreparation.embedding D.slot D.slots_pos)) := by
  apply LinearIsometry.ext
  intro v
  exact SparseFlagEmbedding.embeddings_input _

/-- The fixed initialization is a genuine isometry. -/
theorem input_adjoint_comp (D : Data X n Z s) :
    (input D).toContinuousLinearMap† ∘L (input D).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- The physical row program prepares the complete sparse-slot row state on
the common fixed initialization, with a clean value register. -/
theorem row_preparation (D : Data X n Z s) (x : X) :
    (rowProgram D).eval x ∘L (input D).toContinuousLinearMap =
      SparseFlagEmbedding.clean.toContinuousLinearMap ∘L
        SparseSlotStates.row (D.matrix x) D.scale (D.rowloc x) := by
  calc
    _ = SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap ∘L
        SparseSlotPreparation.preparation D.rowOracle (rowDecode D) (rowDecode_bound D)
          D.table (UniformSlotPreparation.embedding D.slot D.slots_pos) x := by
      change (rowProgram D).eval x ∘L
        (SparseFlagEmbedding.rowEmbedding.toContinuousLinearMap ∘L
          (SparseSlotPreparation.input (UniformSlotPreparation.embedding D.slot D.slots_pos)).toContinuousLinearMap) = _
      rw [← comp_assoc, rowProgram_intertwines, comp_assoc,
        ← SparseSlotPreparation.preparation_eq_program]
    _ = _ := SparseFlagEmbedding.row_preparation D.matrix D.scale D.rowOracle
      (rowDecode D) (rowDecode_bound D) D.table D.slot D.slots_pos D.rowloc
      D.row_injective D.row_valid (fun x i j => by simp [rowDecode, D.decoded]) x

/-- The physical column program prepares the complete sparse-slot column
state from that same initialization and uses a separate failure flag. -/
theorem column_preparation (D : Data X n Z s) (x : X) :
    (columnProgram D).eval x ∘L (input D).toContinuousLinearMap =
      SparseFlagEmbedding.clean.toContinuousLinearMap ∘L
        SparseSlotStates.column (D.matrix x) D.scale (D.colloc x) := by
  rw [input_eq_column]
  calc
    _ = SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap ∘L
        SparseSlotPreparation.preparation D.columnOracle (columnDecode D) (columnDecode_bound D)
          D.table (UniformSlotPreparation.embedding D.slot D.slots_pos) x := by
      change (columnProgram D).eval x ∘L
        (SparseFlagEmbedding.columnEmbedding.toContinuousLinearMap ∘L
          (SparseSlotPreparation.input (UniformSlotPreparation.embedding D.slot D.slots_pos)).toContinuousLinearMap) = _
      rw [← comp_assoc, columnProgram_intertwines, comp_assoc,
        ← SparseSlotPreparation.preparation_eq_program]
    _ = _ := SparseFlagEmbedding.column_preparation D.matrix D.scale D.columnOracle
      (columnDecode D) (columnDecode_bound D) D.table D.slot D.slots_pos D.colloc
      D.column_injective D.column_valid (fun x i j => by simp [columnDecode, D.decoded]) x

/-- Exact block encoding of the matrix divided by `s * a`, produced by the
actual six-query circuit rather than an existential matrix dilation. -/
theorem compression (D : Data X n Z s) (x : X) :
    (input D).toContinuousLinearMap† ∘L (program D).eval x ∘L
        (input D).toContinuousLinearMap =
      SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) :=
  PreparedOverlapProgram.sparse_compression (rowProgram D) (columnProgram D)
    (input D).toContinuousLinearMap SparseFlagEmbedding.clean
    (D.matrix x) D.scale D.scale_pos (D.rowloc x) (D.colloc x)
    (D.row_covers x) (D.column_covers x) x (row_preparation D x) (column_preparation D x)

/-- One explicit uniform program, one fixed isometric initialization, exact
normalization, and all three native query counts in a single certificate. -/
theorem certificate (D : Data X n Z s) :
    (input D).toContinuousLinearMap† ∘L (input D).toContinuousLinearMap = 1 ∧
    (program D).count = 6 ∧
    (program D).labelCount .rowLocation = 1 ∧
    (program D).labelCount .columnLocation = 1 ∧
    (program D).labelCount .value = 4 ∧
    ∀ x, IsUnitary ((program D).eval x) ∧
      (input D).toContinuousLinearMap† ∘L (program D).eval x ∘L
        (input D).toContinuousLinearMap =
      SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) :=
  ⟨input_adjoint_comp D, program_count D, program_row_count D, program_column_count D,
    program_value_count D, fun x => ⟨program_unitary D x, compression D x⟩⟩

end
end SparseHamiltonian.NativeSparseBlockEncoding
