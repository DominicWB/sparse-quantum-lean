import SparseHamiltonian.NativeRoundedEncoding

/-!
# Native sparse data from rounded finite values and supplied native locators

The locator interface below is independent of a value representation. An
explicit finite additive dyadic table and a globally bounded decoder turn it
into `NativeSparseBlockEncoding.Data`. Its matrix is exactly the proved
symmetric rounding of the original complex matrix, with the same entry bound,
locator coverage and Hermiticity.

The primitive value oracle here is the finite additive lookup of the rounded
table. Constructing a finite code does not give free oracle access to an
arbitrary exact real matrix. When an original finite value oracle is already
available, `NativeRoundedEncoding` instead keeps that oracle literally
unchanged and performs rounding only in its fixed decoder.
-/

namespace SparseHamiltonian.NativeDyadicEncoding

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

/-- Native location access and coverage, before choosing any value alphabet. -/
structure Locations (X n : Type*) [Fintype n] [DecidableEq n] (s : ℕ)
    (H : X → Matrix n n ℂ) where
  slot : Fin s ↪ n
  slots_pos : 0 < s
  rowloc : X → n → Fin s → n
  colloc : X → n → Fin s → n
  row_injective : ∀ x i, Function.Injective (rowloc x i)
  column_injective : ∀ x j, Function.Injective (colloc x j)
  row_covers : ∀ x i j, H x i j ≠ 0 → SparseSlotStates.selected (rowloc x) i j
  column_covers : ∀ x i j, H x i j ≠ 0 → SparseSlotStates.selected (colloc x) j i
  rowOracle : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n)
  columnOracle : X → EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n)
  row_unitary : ∀ x, OracleCircuit.IsUnitary (rowOracle x)
  column_unitary : ∀ x, OracleCircuit.IsUnitary (columnOracle x)
  row_valid : ∀ x i k, rowOracle x (EuclideanSpace.single (i, slot k) 1) =
    EuclideanSpace.single (i, rowloc x i k) 1
  column_valid : ∀ x j k, columnOracle x (EuclideanSpace.single (j, slot k) 1) =
    EuclideanSpace.single (colloc x j k, j) 1

variable {X n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
  {H : X → Matrix n n ℂ}

/-- The actual finite cyclic-group alphabet selected by public precision/range. -/
abbrev Value (b : ℕ) (A : ℝ) :=
  DyadicAdditiveAlphabet.Word (SparseDyadicRounding.capacity b A)

/-- The explicit rounded finite value table. -/
def table (H : X → Matrix n n ℂ) (b : ℕ) (A : ℝ) : X → (n × n) → Value b A :=
  fun x a => DyadicAdditiveAlphabet.encode b _ (H x a.1 a.2)

omit [Fintype n] [DecidableEq n] in
/-- Exactly the ordinary additive lookup promised as the rounded value query. -/
theorem table_lookup (H : X → Matrix n n ℂ) (b : ℕ) (A : ℝ)
    (x : X) (a : n × n) (z : Value b A) :
    LookupOracle.basisEquiv (table H b A) x (a, z) =
      (a, z + DyadicAdditiveAlphabet.encode b _ (H x a.1 a.2)) := rfl

omit [Fintype n] [DecidableEq n] in
/-- Every true zero matrix entry uses additive zero, not just a zero decoder. -/
theorem table_zero (H : X → Matrix n n ℂ) (b : ℕ) (A : ℝ)
    (x : X) (i j : n) (h : H x i j = 0) : table H b A x (i, j) = 0 := by
  simp [table, h]

/-- Construct the complete native interface. All-code bounds are proved by
zeroing unused codes, with no scale inflation and no new locator promise. -/
def data (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) : Data X n (Value b A) s where
  slot := L.slot
  slots_pos := L.slots_pos
  scale := A
  scale_pos := hA
  matrix := fun x => SparseDyadicRounding.matrix b A (H x)
  table := table H b A
  decode := fun _ z => DyadicAdditiveAlphabet.decode b A z
  decode_bound := fun _ z => DyadicAdditiveAlphabet.decode_bound b A hA.le z
  decoded := fun x i j => DyadicAdditiveAlphabet.decode_encode b _ A (H x i j) (hH x i j)
  rowloc := L.rowloc
  colloc := L.colloc
  row_injective := L.row_injective
  column_injective := L.column_injective
  row_covers := by
    intro x i j h
    apply L.row_covers x i j
    intro hz
    simp [hz] at h
  column_covers := by
    intro x i j h
    apply L.column_covers x i j
    intro hz
    simp [hz] at h
  rowOracle := L.rowOracle
  columnOracle := L.columnOracle
  row_unitary := L.row_unitary
  column_unitary := L.column_unitary
  row_valid := L.row_valid
  column_valid := L.column_valid

@[simp] theorem data_matrix (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) :
    (data L b A hA hH).matrix x = SparseDyadicRounding.matrix b A (H x) := rfl

@[simp] theorem data_scale (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) : (data L b A hA hH).scale = A := rfl

/-- The constructor does not require a second sparsity promise beyond coverage. -/
theorem row_sparse (L : Locations X n s H) (x : X) (i : n) :
    (nonzeroPositions (H x i)).card ≤ s :=
  NativeRoundedEncoding.sparse_of_covers _ (L.rowloc x i) (L.row_covers x i)

theorem column_sparse (L : Locations X n s H) (x : X) (j : n) :
    (nonzeroPositions (fun i => H x i j)).card ≤ s :=
  NativeRoundedEncoding.sparse_of_covers _ (L.colloc x j) (fun i => L.column_covers x i j)

/-- The original entry bound is retained by the actual represented matrix. -/
theorem data_entry_bound (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (i j : n) :
    ‖(data L b A hA hH).matrix x i j‖ ≤ A :=
  SparseDyadicRounding.matrix_entry_bound b A (H x) (hH x) i j

/-- Symmetric complex rounding retains exact Hermiticity. -/
theorem data_isHermitian (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (hHerm : (H x).IsHermitian) :
    ((data L b A hA hH).matrix x).IsHermitian :=
  SparseDyadicRounding.isHermitian b A (H x) hHerm

/-- Absolute row sums contract under this concrete native data representation. -/
theorem data_row_sum_le (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (i : n) :
    ∑ j, ‖(data L b A hA hH).matrix x i j‖ ≤ ∑ j, ‖H x i j‖ := by
  exact Finset.sum_le_sum (fun j _ => SparseDyadicRounding.norm_value_le b _ _)

theorem data_column_sum_le (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (j : n) :
    ∑ i, ‖(data L b A hA hH).matrix x i j‖ ≤ ∑ i, ‖H x i j‖ := by
  exact Finset.sum_le_sum (fun i _ => SparseDyadicRounding.norm_value_le b _ _)

/-- The rounded native matrix retains every original row energy bound. -/
theorem data_row_energy_le (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (i : n) :
    ∑ j, ‖(data L b A hA hH).matrix x i j‖ ^ 2 ≤ ∑ j, ‖H x i j‖ ^ 2 := by
  exact Finset.sum_le_sum (fun j _ =>
    pow_le_pow_left₀ (norm_nonneg _) (SparseDyadicRounding.norm_value_le b _ _) 2)

theorem data_column_energy_le (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (j : n) :
    ∑ i, ‖(data L b A hA hH).matrix x i j‖ ^ 2 ≤ ∑ i, ‖H x i j‖ ^ 2 := by
  exact Finset.sum_le_sum (fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (SparseDyadicRounding.norm_value_le b _ _) 2)

/-- Operator error for the matrix of the concrete native additive interface. -/
theorem data_operator_error (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) :
    ‖SparseStateOverlap.matrixOperator (H x) -
      SparseStateOverlap.matrixOperator ((data L b A hA hH).matrix x)‖ ≤
      (s : ℝ) * (2 / SparseDyadicRounding.scale b) :=
  SparseDyadicRounding.operator_error_le b A (H x) s (hH x)
    (row_sparse L x) (column_sparse L x)

/-- The specified logarithmic bit schedule bounds the actual evolution error. -/
theorem data_scheduled_evolution_error (L : Locations X n s H) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) (x : X) (t ε : ℝ) (hε : 0 < ε)
    (hHerm : (H x).IsHermitian) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (H x)) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator
        ((data L (SparseDyadicRounding.precisionBits s t ε) A hA hH).matrix x))‖ ≤ ε :=
  SparseDyadicRounding.scheduled_evolution_error A (H x) s t ε hε
    (hH x) hHerm (row_sparse L x) (column_sparse L x)

/-- Any complete-output simulation of this concrete finite native data incurs
only the allocated additive rounding error when targeting the original matrix. -/
theorem data_scheduled_output_error {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (L : Locations X n s H) (A : ℝ) (hA : 0 < A) (hH : ∀ x i j, ‖H x i j‖ ≤ A)
    (x : X) (S F : EuclideanSpace ℂ n →L[ℂ] K) (t εround εsim : ℝ)
    (hε : 0 < εround) (hHerm : (H x).IsHermitian) (hF : ‖F‖ ≤ 1)
    (hSim : ‖S - F ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      SparseStateOverlap.matrixOperator
        ((data L (SparseDyadicRounding.precisionBits s t εround) A hA hH).matrix x))‖ ≤
      εsim) :
    ‖S - F ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      SparseStateOverlap.matrixOperator (H x))‖ ≤ εsim + εround := by
  exact (SparseDyadicRounding.output_error_le (SparseDyadicRounding.precisionBits s t εround)
    A (H x) S F s t εsim (hH x) hHerm hF (row_sparse L x)
    (column_sparse L x) hSim).trans
      (add_le_add le_rfl (SparseDyadicRounding.precisionBits_error s t εround hε))

/-- An actual six-query unitary encoding over the rounded finite additive value
oracle and the two supplied native locators. -/
theorem certificate (L : Locations X n s H) (b : ℕ) (A : ℝ) (hA : 0 < A)
    (hH : ∀ x i j, ‖H x i j‖ ≤ A) :
    (program (data L b A hA hH)).count = 6 ∧
      ∀ x, OracleCircuit.IsUnitary ((program (data L b A hA hH)).eval x) ∧
        (input (data L b A hA hH)).toContinuousLinearMap† ∘L
          (program (data L b A hA hH)).eval x ∘L
          (input (data L b A hA hH)).toContinuousLinearMap =
        SparseStateOverlap.matrixOperator (fun i j =>
          SparseDyadicRounding.matrix b A (H x) i j / ((s : ℂ) * A)) := by
  exact ⟨program_count _, fun x => ⟨program_unitary _ x, compression (data L b A hA hH) x⟩⟩

end
end SparseHamiltonian.NativeDyadicEncoding
