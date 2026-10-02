import SparseHamiltonian.NativeSparseBlockEncoding

/-!
# Hermitian sparse input with one native location oracle

Hermiticity makes the row slot map cover columns as well. A fixed swap after
one call to the supplied row oracle implements the required column oracle.
This only uses the promised action on original slots; the supplied oracle's
unitary action elsewhere remains arbitrary. Substitution then gives a genuine
two-label block-encoding circuit with two location and four value calls.
-/

namespace SparseHamiltonian.NativeHermitianOracle

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

/-- Native Hermitian input requires only one in-place location oracle. -/
structure Data (X n Z : Type*) [Fintype n] [DecidableEq n] (s : ℕ) where
  slot : Fin s ↪ n
  slots_pos : 0 < s
  scale : ℝ
  scale_pos : 0 < scale
  matrix : X → Matrix n n ℂ
  hermitian : ∀ x, (matrix x).IsHermitian
  table : X → (n × n) → Z
  decode : (n × n) → Z → ℂ
  decode_bound : ∀ a z, ‖decode a z‖ ≤ scale
  decoded : ∀ x i j, decode (i, j) (table x (i, j)) = matrix x i j
  loc : X → n → Fin s → n
  injective : ∀ x i, Function.Injective (loc x i)
  covers : ∀ x i j, matrix x i j ≠ 0 → SparseSlotStates.selected (loc x) i j
  oracle : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n)
  unitary : ∀ x, IsUnitary (oracle x)
  valid : ∀ x i k, oracle x (EuclideanSpace.single (i, slot k) 1) =
    EuclideanSpace.single (i, loc x i k) 1

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The fixed address-coordinate swap, independent of the sparse input. -/
def coordinateSwap : EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  (LookupOracle.permutationUnitary (Equiv.prodComm n n)).toLinearIsometry.toContinuousLinearMap

omit [DecidableEq n] in
theorem coordinateSwap_unitary : IsUnitary (coordinateSwap (n := n)) :=
  LookupOracle.permutationUnitary_unitary (Equiv.prodComm n n)

@[simp] theorem coordinateSwap_single (i j : n) (z : ℂ) :
    coordinateSwap (EuclideanSpace.single (i,j) z) = EuclideanSpace.single (j,i) z :=
  LookupOracle.permutationUnitary_single (Equiv.prodComm n n) (i,j) z

/-- One row-location call followed by a fixed swap is the column primitive. -/
def columnOracle (D : Data X n Z s) (x : X) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  coordinateSwap * D.oracle x

theorem columnOracle_unitary (D : Data X n Z s) (x : X) :
    IsUnitary (columnOracle D x) := coordinateSwap_unitary.mul (D.unitary x)

theorem columnOracle_valid (D : Data X n Z s) (x : X) (j : n) (k : Fin s) :
    columnOracle D x (EuclideanSpace.single (j, D.slot k) 1) =
      EuclideanSpace.single (D.loc x j k, j) 1 := by
  change coordinateSwap (D.oracle x (EuclideanSpace.single (j, D.slot k) 1)) = _
  rw [D.valid, coordinateSwap_single]

/-- Hermiticity transfers nonzero coverage without changing any slot. -/
theorem column_covers (D : Data X n Z s) (x : X) (i j : n)
    (hij : D.matrix x i j ≠ 0) : SparseSlotStates.selected (D.loc x) j i := by
  apply D.covers x j i
  intro hji
  have h := (D.hermitian x).apply i j
  rw [hji, star_zero] at h
  exact hij h.symm

/-- Native row/column data derived from one oracle and a fixed coordinate swap. -/
def toNative (D : Data X n Z s) : NativeSparseBlockEncoding.Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := D.matrix
  table := D.table
  decode := D.decode
  decode_bound := D.decode_bound
  decoded := D.decoded
  rowloc := D.loc
  colloc := D.loc
  row_injective := D.injective
  column_injective := D.injective
  row_covers := D.covers
  column_covers := column_covers D
  rowOracle := D.oracle
  columnOracle := columnOracle D
  row_unitary := D.unitary
  column_unitary := columnOracle_unitary D
  row_valid := D.valid
  column_valid := columnOracle_valid D

/-- These are the only two native input access primitives. -/
inductive Query where
  | location
  | value
  deriving DecidableEq

variable [Fintype Z]

/-- The physical common-workspace implementation of the fixed coordinate swap. -/
def physicalSwap : SparseFlagEmbedding.Space (n × n) Z →L[ℂ]
    SparseFlagEmbedding.Space (n × n) Z :=
  SparseFlagEmbedding.location (fun _ : Unit => coordinateSwap (n := n)) ()

omit [DecidableEq n] in
theorem physicalSwap_unitary : IsUnitary (physicalSwap (n := n) (Z := Z)) := by
  exact SparseFlagEmbedding.location_unitary
    (fun _ : Unit => coordinateSwap (n := n)) (fun _ => coordinateSwap_unitary) ()

/-- Extending the native column oracle preserves its one-query factorization
on the entire workspace, including unpromised address inputs. -/
theorem physical_columnOracle (D : Data X n Z s) (x : X) :
    SparseFlagEmbedding.location (Z := Z) (columnOracle D) x =
      physicalSwap * SparseFlagEmbedding.location D.oracle x := by
  simp only [SparseFlagEmbedding.location, physicalSwap, columnOracle]
  rw [← map_mul]
  congr 1

variable [AddCommGroup Z]

/-- Both oracle families act on the same address, value, and flag registers. -/
def oracles (D : Data X n Z s) : Query → X →
    SparseFlagEmbedding.Space (n × n) Z →L[ℂ] SparseFlagEmbedding.Space (n × n) Z
  | .location => SparseFlagEmbedding.location D.oracle
  | .value => LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) D.table

theorem oracles_unitary (D : Data X n Z s) (q : Query) (x : X) :
    IsUnitary (oracles D q x) := by
  cases q with
  | location => exact SparseFlagEmbedding.location_unitary D.oracle D.unitary x
  | value => exact LookupControlledGate.oracle_unitary D.table x

/-- A column query is a syntax tree with one location call and one free fixed swap. -/
def adapter (D : Data X n Z s) : NativeSparseBlockEncoding.Query →
    MultiOracleCircuit.Program (oracles D)
  | .rowLocation => .query .location
  | .columnLocation => .seq (.fixed physicalSwap physicalSwap_unitary) (.query .location)
  | .value => .query .value

@[simp] theorem adapter_count (D : Data X n Z s) (q : NativeSparseBlockEncoding.Query) :
    (adapter D q).count = 1 := by
  cases q <;> rfl

theorem adapter_eval (D : Data X n Z s) (q : NativeSparseBlockEncoding.Query) (x : X) :
    (adapter D q).eval x = NativeSparseBlockEncoding.oracles (toNative D) q x := by
  cases q with
  | rowLocation => rfl
  | columnLocation => exact (physical_columnOracle D x).symm
  | value => rfl

/-- The native block encoding compiled to the two actually supplied oracles. -/
def program (D : Data X n Z s) : MultiOracleCircuit.Program (oracles D) :=
  (NativeSparseBlockEncoding.program (toNative D)).substitute (adapter D)

/-- Syntactic compilation preserves the full native operator. -/
@[simp] theorem program_eval (D : Data X n Z s) (x : X) :
    (program D).eval x = (NativeSparseBlockEncoding.program (toNative D)).eval x :=
  MultiOracleCircuit.Program.eval_substitute _ _ (adapter_eval D) x

/-- Exact cost in terms of the one location and one value access primitive. -/
theorem program_cost (D : Data X n Z s) (w : Query → ℕ) :
    (program D).cost w = 2 * w .location + 4 * w .value := by
  rw [program, MultiOracleCircuit.Program.cost_substitute,
    NativeSparseBlockEncoding.program_cost]
  simp only [adapter, MultiOracleCircuit.Program.cost_query,
    MultiOracleCircuit.Program.cost_seq, MultiOracleCircuit.Program.cost_fixed, zero_add]
  omega

@[simp] theorem program_count (D : Data X n Z s) : (program D).count = 6 := by
  have h := program_cost D (fun _ => 1)
  simpa using h

@[simp] theorem program_location_count (D : Data X n Z s) :
    (program D).labelCount .location = 2 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

@[simp] theorem program_value_count (D : Data X n Z s) :
    (program D).labelCount .value = 4 := by
  rw [MultiOracleCircuit.Program.labelCount, program_cost]
  rfl

/-- The actual two-oracle implementation is unitary on all physical inputs. -/
theorem program_unitary (D : Data X n Z s) (x : X) : IsUnitary ((program D).eval x) :=
  (program D).eval_unitary (oracles_unitary D) x

variable [DecidableEq Z]

/-- The fixed uniform-slot initialization, with clean value and shared good flag. -/
def input (D : Data X n Z s) :
    EuclideanSpace ℂ n →ₗᵢ[ℂ] SparseFlagEmbedding.Space (n × n) Z :=
  NativeSparseBlockEncoding.input (toNative D)

/-- The physical initialization is independent of the matrix input and is isometric. -/
theorem input_adjoint_comp (D : Data X n Z s) :
    (input D).toContinuousLinearMap† ∘L (input D).toContinuousLinearMap = 1 :=
  NativeSparseBlockEncoding.input_adjoint_comp (toNative D)

/-- The actual two-oracle circuit encodes `H / (s * a)` exactly. -/
theorem compression (D : Data X n Z s) (x : X) :
    (input D).toContinuousLinearMap† ∘L (program D).eval x ∘L
        (input D).toContinuousLinearMap =
      SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  rw [program_eval]
  exact NativeSparseBlockEncoding.compression (toNative D) x

/-- A complete certificate using only the supplied location and value oracles. -/
theorem certificate (D : Data X n Z s) :
    (input D).toContinuousLinearMap† ∘L (input D).toContinuousLinearMap = 1 ∧
    (program D).count = 6 ∧
    (program D).labelCount .location = 2 ∧
    (program D).labelCount .value = 4 ∧
    ∀ x, IsUnitary ((program D).eval x) ∧
      (input D).toContinuousLinearMap† ∘L (program D).eval x ∘L
        (input D).toContinuousLinearMap =
      SparseStateOverlap.matrixOperator
        (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) :=
  ⟨input_adjoint_comp D, program_count D, program_location_count D,
    program_value_count D, fun x => ⟨program_unitary D x, compression D x⟩⟩

end
end SparseHamiltonian.NativeHermitianOracle
