import SparseHamiltonian.NativeHermitianOracle

/-!
# Band and tail encodings with the original sparse oracles

Magnitude filtering is performed by the fixed value decoder. The original
location oracles, slot lists and value table are unchanged. Each resulting
encoding therefore still uses one row-location query, one column-location
query and four calls to the original value oracle. Its normalization is s*a;
reducing that normalization by amplitude multiplication remains separate.
-/

namespace SparseHamiltonian.NativeBandEncoding

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Fixed complex-value mask for a single magnitude band. -/
def bandValue (a : ℝ) (z : ℂ) : ℂ :=
  if a / 2 < ‖z‖ ∧ ‖z‖ ≤ a then z else 0

/-- Fixed complex-value mask retaining the complete low-magnitude tail. -/
def tailValue (a : ℝ) (z : ℂ) : ℂ := if ‖z‖ ≤ a then z else 0

theorem bandValue_bound (a : ℝ) (ha : 0 ≤ a) (z : ℂ) : ‖bandValue a z‖ ≤ a := by
  unfold bandValue
  split_ifs with h
  · exact h.2
  · simpa using ha

theorem tailValue_bound (a : ℝ) (ha : 0 ≤ a) (z : ℂ) : ‖tailValue a z‖ ≤ a := by
  unfold tailValue
  split_ifs with h
  · exact h
  · simpa using ha

@[simp] theorem bandValue_zero (a : ℝ) : bandValue a 0 = 0 := by simp [bandValue]
@[simp] theorem tailValue_zero (a : ℝ) : tailValue a 0 = 0 := by simp [tailValue]

/-- The actual sparse band data changes only the fixed decoder, matrix and
normalization; every native oracle and every original location is retained. -/
def band (D : Data X n Z s) (a : ℝ) (ha : 0 < a) : Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := a
  scale_pos := ha
  matrix := fun x => bandMatrix a (D.matrix x)
  table := D.table
  decode := fun b z => bandValue a (D.decode b z)
  decode_bound := fun b z => bandValue_bound a ha.le _
  decoded := by intro x i j; simp [bandValue, bandMatrix, magnitudeBand, D.decoded]
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := by
    intro x i j h
    apply D.row_covers x i j
    intro hz
    simp [bandMatrix, magnitudeBand, hz] at h
  column_covers := by
    intro x i j h
    apply D.column_covers x i j
    intro hz
    simp [bandMatrix, magnitudeBand, hz] at h
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

/-- The tail also retains every padded slot and uses the original value table. -/
def tail (D : Data X n Z s) (a : ℝ) (ha : 0 < a) : Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := a
  scale_pos := ha
  matrix := fun x => tailMatrix a (D.matrix x)
  table := D.table
  decode := fun b z => tailValue a (D.decode b z)
  decode_bound := fun b z => tailValue_bound a ha.le _
  decoded := by intro x i j; simp [tailValue, tailMatrix, magnitudeTail, D.decoded]
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := by
    intro x i j h
    apply D.row_covers x i j
    intro hz
    simp [tailMatrix, magnitudeTail, hz] at h
  column_covers := by
    intro x i j h
    apply D.column_covers x i j
    intro hz
    simp [tailMatrix, magnitudeTail, hz] at h
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

variable [Fintype Z] [AddCommGroup Z]

/-- All band thresholds use literally the same native oracle families. -/
@[simp] theorem band_oracles (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    oracles (band D a ha) = oracles D := rfl

@[simp] theorem tail_oracles (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    oracles (tail D a ha) = oracles D := rfl

variable [DecidableEq Z]

/-- The fixed input encoding is common to the entire band decomposition. -/
@[simp] theorem band_input (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    input (band D a ha) = input D := rfl

@[simp] theorem tail_input (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    input (tail D a ha) = input D := rfl

/-- A concrete six-query encoding of each actual magnitude band. -/
theorem band_certificate (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    (program (band D a ha)).count = 6 ∧
      ∀ x, OracleCircuit.IsUnitary ((program (band D a ha)).eval x) ∧
        (input D).toContinuousLinearMap† ∘L (program (band D a ha)).eval x ∘L
          (input D).toContinuousLinearMap =
        SparseStateOverlap.matrixOperator
          (fun i j => bandMatrix a (D.matrix x) i j / ((s : ℂ) * a)) := by
  refine ⟨program_count _, fun x => ⟨program_unitary _ x, ?_⟩⟩
  exact compression (band D a ha) x

/-- A concrete six-query encoding of the retained tail, with no truncation. -/
theorem tail_certificate (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    (program (tail D a ha)).count = 6 ∧
      ∀ x, OracleCircuit.IsUnitary ((program (tail D a ha)).eval x) ∧
        (input D).toContinuousLinearMap† ∘L (program (tail D a ha)).eval x ∘L
          (input D).toContinuousLinearMap =
        SparseStateOverlap.matrixOperator
          (fun i j => tailMatrix a (D.matrix x) i j / ((s : ℂ) * a)) := by
  refine ⟨program_count _, fun x => ⟨program_unitary _ x, ?_⟩⟩
  exact compression (tail D a ha) x

end
end SparseHamiltonian.NativeBandEncoding
