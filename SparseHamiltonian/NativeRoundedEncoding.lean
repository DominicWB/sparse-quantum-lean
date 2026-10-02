import SparseHamiltonian.LabeledAdjointSimulation

/-!
# Dyadic rounding with the original finite native value oracle

When native sparse data already have a finite additive value alphabet, dyadic
rounding changes only the fixed decoder. All original location and value
queries, their common workspace and their exact counts are retained. The
all-code decoder bound follows from magnitude contraction of symmetric
rounding; no promised basis code is silently omitted.
-/

namespace SparseHamiltonian.NativeRoundedEncoding

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding SparseDyadicRounding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Every original matrix entry obeys the data's all-code decoder bound. -/
theorem entry_bound (D : Data X n Z s) (x : X) (i j : n) :
    ‖D.matrix x i j‖ ≤ D.scale := by
  rw [← D.decoded x i j]
  exact D.decode_bound _ _

/-- Coverage by the supplied list gives the actual support cardinality bound. -/
theorem sparse_of_covers (f : n → ℂ) (loc : Fin s → n)
    (h : ∀ i, f i ≠ 0 → i ∈ Finset.univ.image loc) :
    (nonzeroPositions f).card ≤ s := by
  have hs : nonzeroPositions f ⊆ Finset.univ.image loc := by
    intro i hi
    exact h i (by simpa [nonzeroPositions] using hi)
  exact (Finset.card_le_card hs).trans ((Finset.card_image_le).trans (by simp))

theorem row_sparse (D : Data X n Z s) (x : X) (i : n) :
    (nonzeroPositions (D.matrix x i)).card ≤ s :=
  sparse_of_covers _ (D.rowloc x i) (D.row_covers x i)

theorem column_sparse (D : Data X n Z s) (x : X) (j : n) :
    (nonzeroPositions (fun i => D.matrix x i j)).card ≤ s :=
  sparse_of_covers _ (D.colloc x j) (fun i => D.column_covers x i j)

/-- Rounding preserves the native interface exactly: only its fixed decoder
and represented matrix change. No processed-value oracle is granted. -/
def rounded (D : Data X n Z s) (b : ℕ) : Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale
  scale_pos := D.scale_pos
  matrix := fun x => SparseDyadicRounding.matrix b D.scale (D.matrix x)
  table := D.table
  decode := fun a z => value b (capacity b D.scale) (D.decode a z)
  decode_bound := fun a z => (norm_value_le b _ _).trans (D.decode_bound a z)
  decoded := by intro x i j; simp [D.decoded]
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := by
    intro x i j h
    apply D.row_covers x i j
    intro hz
    simp [hz] at h
  column_covers := by
    intro x i j h
    apply D.column_covers x i j
    intro hz
    simp [hz] at h
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

@[simp] theorem rounded_matrix (D : Data X n Z s) (b : ℕ) (x : X) :
    (rounded D b).matrix x = SparseDyadicRounding.matrix b D.scale (D.matrix x) := rfl

@[simp] theorem rounded_scale (D : Data X n Z s) (b : ℕ) :
    (rounded D b).scale = D.scale := rfl

@[simp] theorem rounded_table (D : Data X n Z s) (b : ℕ) :
    (rounded D b).table = D.table := rfl

/-- The decoded matrix retains exact Hermiticity. -/
theorem rounded_isHermitian (D : Data X n Z s) (b : ℕ) (x : X)
    (hH : (D.matrix x).IsHermitian) : ((rounded D b).matrix x).IsHermitian :=
  SparseDyadicRounding.isHermitian b D.scale (D.matrix x) hH

/-- No row absolute-sum bound is enlarged by decoder rounding. -/
theorem rounded_row_sum_le (D : Data X n Z s) (b : ℕ) (x : X) (i : n) :
    ∑ j, ‖(rounded D b).matrix x i j‖ ≤ ∑ j, ‖D.matrix x i j‖ := by
  exact Finset.sum_le_sum (fun j _ => norm_value_le b _ _)

/-- No column absolute-sum bound is enlarged either. -/
theorem rounded_column_sum_le (D : Data X n Z s) (b : ℕ) (x : X) (j : n) :
    ∑ i, ‖(rounded D b).matrix x i j‖ ≤ ∑ i, ‖D.matrix x i j‖ := by
  exact Finset.sum_le_sum (fun i _ => norm_value_le b _ _)

/-- The row Euclidean-energy bound used by the magnitude-band scheduler also
contracts, so rounding needs no enlarged spectral resource parameter. -/
theorem rounded_row_energy_le (D : Data X n Z s) (b : ℕ) (x : X) (i : n) :
    ∑ j, ‖(rounded D b).matrix x i j‖ ^ 2 ≤ ∑ j, ‖D.matrix x i j‖ ^ 2 := by
  exact Finset.sum_le_sum (fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_value_le b _ _) 2)

theorem rounded_column_energy_le (D : Data X n Z s) (b : ℕ) (x : X) (j : n) :
    ∑ i, ‖(rounded D b).matrix x i j‖ ^ 2 ≤ ∑ i, ‖D.matrix x i j‖ ^ 2 := by
  exact Finset.sum_le_sum (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_value_le b _ _) 2)

/-- The native data constructor carries the actual operator approximation. -/
theorem rounded_operator_error (D : Data X n Z s) (b : ℕ) (x : X) :
    ‖SparseStateOverlap.matrixOperator (D.matrix x) -
      SparseStateOverlap.matrixOperator ((rounded D b).matrix x)‖ ≤
      (s : ℝ) * (2 / SparseDyadicRounding.scale b) :=
  SparseDyadicRounding.operator_error_le b D.scale (D.matrix x) s
    (entry_bound D x) (row_sparse D x) (column_sparse D x)

/-- The concrete logarithmic precision schedule gives the requested evolution
allowance for the matrix represented by the same native oracle calls. -/
theorem scheduled_evolution_error (D : Data X n Z s) (x : X) (t ε : ℝ)
    (hε : 0 < ε) (hH : (D.matrix x).IsHermitian) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x)) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator
        ((rounded D (precisionBits s t ε)).matrix x))‖ ≤ ε :=
  SparseDyadicRounding.scheduled_evolution_error D.scale (D.matrix x) s t ε hε
    (entry_bound D x) hH (row_sparse D x) (column_sparse D x)

/-- The explicit precision schedule can also be used directly for an operator
error allowance by taking unit time. -/
theorem scheduled_operator_error (D : Data X n Z s) (x : X) (ε : ℝ)
    (hε : 0 < ε) :
    ‖SparseStateOverlap.matrixOperator (D.matrix x) -
      SparseStateOverlap.matrixOperator ((rounded D (precisionBits s 1 ε)).matrix x)‖ ≤ ε := by
  apply (rounded_operator_error D (precisionBits s 1 ε) x).trans
  simpa using precisionBits_error s 1 ε hε

/-- A full-output simulation certificate for the rounded native data transfers
to the original matrix with precisely the allocated rounding allowance. -/
theorem scheduled_output_error {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (D : Data X n Z s) (x : X) (S F : EuclideanSpace ℂ n →L[ℂ] K)
    (t εround εsim : ℝ) (hε : 0 < εround) (hH : (D.matrix x).IsHermitian)
    (hF : ‖F‖ ≤ 1)
    (hSim : ‖S - F ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      SparseStateOverlap.matrixOperator ((rounded D (precisionBits s t εround)).matrix x))‖ ≤
      εsim) :
    ‖S - F ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ εsim + εround := by
  exact (SparseDyadicRounding.output_error_le (precisionBits s t εround) D.scale
    (D.matrix x) S F s t εsim (entry_bound D x) hH hF (row_sparse D x)
    (column_sparse D x) hSim).trans
      (add_le_add le_rfl (precisionBits_error s t εround hε))

variable [Fintype Z] [AddCommGroup Z]

/-- Rounding already finite values uses literally the same native queries. -/
@[simp] theorem rounded_oracles (D : Data X n Z s) (b : ℕ) :
    oracles (rounded D b) = oracles D := rfl

variable [DecidableEq Z]

@[simp] theorem rounded_input (D : Data X n Z s) (b : ℕ) :
    input (rounded D b) = input D := rfl

/-- A six-query rounded encoding over the original finite value oracle. -/
theorem certificate (D : Data X n Z s) (b : ℕ) :
    (program (rounded D b)).count = 6 ∧
      ∀ x, OracleCircuit.IsUnitary ((program (rounded D b)).eval x) ∧
        (input D).toContinuousLinearMap† ∘L (program (rounded D b)).eval x ∘L
          (input D).toContinuousLinearMap =
        SparseStateOverlap.matrixOperator (fun i j =>
          SparseDyadicRounding.matrix b D.scale (D.matrix x) i j / ((s : ℂ) * D.scale)) := by
  exact ⟨program_count _, fun x => ⟨program_unitary _ x, compression (rounded D b) x⟩⟩

end
end SparseHamiltonian.NativeRoundedEncoding
