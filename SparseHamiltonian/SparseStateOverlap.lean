import SparseHamiltonian.SparseEntryAmplitudes

/-!
# Exact row and column state overlaps

Row and column state preparations share their good basis labels `(i,j)`, while
all row failures and column failures occupy disjoint basis sectors. Residual
amplitudes complete subnormalized coefficient arrays into genuine isometries.
The overlap is the matrix with entries `conj(r i j) * c i j`. No oracle-query
implementation or preparation cost is assumed or concluded here.
-/

namespace SparseHamiltonian.SparseStateOverlap

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Shared good entries and separate row/column failure labels. -/
abbrev Basis (I J : Type*) := (I × J) ⊕ (I ⊕ J)

/-- The common preparation workspace, including all failure amplitudes. -/
abbrev Space (I J : Type*) [Fintype I] [Fintype J] := EuclideanSpace ℂ (Basis I J)

/-- Squared coefficient mass in one row. -/
def rowMass (r : I → J → ℂ) (i : I) : ℝ := ∑ j, ‖r i j‖ ^ 2

/-- Squared coefficient mass in one column. -/
def columnMass (c : I → J → ℂ) (j : J) : ℝ := ∑ i, ‖c i j‖ ^ 2

/-- The nonnegative amplitude completing a row to norm one. -/
def rowResidual (r : I → J → ℂ) (i : I) : ℝ := Real.sqrt (1 - rowMass r i)

/-- The nonnegative amplitude completing a column to norm one. -/
def columnResidual (c : I → J → ℂ) (j : J) : ℝ := Real.sqrt (1 - columnMass c j)

omit [Fintype I] in
theorem rowResidual_sq (r : I → J → ℂ) (i : I) (h : rowMass r i ≤ 1) :
    rowResidual r i ^ 2 = 1 - rowMass r i :=
  Real.sq_sqrt (sub_nonneg.mpr h)

omit [Fintype J] in
theorem columnResidual_sq (c : I → J → ℂ) (j : J) (h : columnMass c j ≤ 1) :
    columnResidual c j ^ 2 = 1 - columnMass c j :=
  Real.sq_sqrt (sub_nonneg.mpr h)

/-- Coherent row preparation, with its failure amplitude on a row-only label. -/
def row (r : I → J → ℂ) : EuclideanSpace ℂ I →L[ℂ] Space I J :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun b => match b with
        | Sum.inl (i, j) => r i j * v i
        | Sum.inr (Sum.inl i) => (rowResidual r i : ℂ) * v i
        | Sum.inr (Sum.inr _) => 0)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro b
        rcases b with ⟨i, j⟩ | (i | j) <;> simp [mul_add]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro b
        rcases b with ⟨i, j⟩ | (i | j) <;> simp [mul_left_comm] }

/-- Coherent column preparation, with a disjoint column-only failure label. -/
def column (c : I → J → ℂ) : EuclideanSpace ℂ J →L[ℂ] Space I J :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun b => match b with
        | Sum.inl (i, j) => c i j * v j
        | Sum.inr (Sum.inl _) => 0
        | Sum.inr (Sum.inr j) => (columnResidual c j : ℂ) * v j)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro b
        rcases b with ⟨i, j⟩ | (i | j) <;> simp [mul_add]
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro b
        rcases b with ⟨i, j⟩ | (i | j) <;> simp [mul_left_comm] }

@[simp] theorem row_good (r : I → J → ℂ) (v : EuclideanSpace ℂ I) (i : I) (j : J) :
    row r v (Sum.inl (i, j)) = r i j * v i := rfl

@[simp] theorem row_failure (r : I → J → ℂ) (v : EuclideanSpace ℂ I) (i : I) :
    row r v (Sum.inr (Sum.inl i)) = (rowResidual r i : ℂ) * v i := rfl

@[simp] theorem row_column_failure (r : I → J → ℂ) (v : EuclideanSpace ℂ I) (j : J) :
    row r v (Sum.inr (Sum.inr j)) = 0 := rfl

@[simp] theorem column_good (c : I → J → ℂ) (v : EuclideanSpace ℂ J) (i : I) (j : J) :
    column c v (Sum.inl (i, j)) = c i j * v j := rfl

@[simp] theorem column_failure (c : I → J → ℂ) (v : EuclideanSpace ℂ J) (j : J) :
    column c v (Sum.inr (Sum.inr j)) = (columnResidual c j : ℂ) * v j := rfl

@[simp] theorem column_row_failure (c : I → J → ℂ) (v : EuclideanSpace ℂ J) (i : I) :
    column c v (Sum.inr (Sum.inl i)) = 0 := rfl

/-- The row map's total norm includes both the good mass and residual mass. -/
theorem row_norm_sq (r : I → J → ℂ) (v : EuclideanSpace ℂ I) :
    ‖row r v‖ ^ 2 = ∑ i, (rowMass r i + rowResidual r i ^ 2) * ‖v i‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Fintype.sum_prod_type,
    row_good, row_failure, row_column_failure, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, add_zero]
  simp only [rowMass, add_mul, Finset.sum_add_distrib, Finset.sum_mul]

/-- Column mass and its residual likewise account for the complete output. -/
theorem column_norm_sq (c : I → J → ℂ) (v : EuclideanSpace ℂ J) :
    ‖column c v‖ ^ 2 = ∑ j, (columnMass c j + columnResidual c j ^ 2) * ‖v j‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type, Fintype.sum_prod_type,
    column_good, column_failure, column_row_failure, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero, zero_add]
  simp only [columnMass, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Every subnormalized row array defines a genuine isometry. -/
theorem row_norm (r : I → J → ℂ) (h : ∀ i, rowMass r i ≤ 1)
    (v : EuclideanSpace ℂ I) : ‖row r v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [row_norm_sq, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro i _
  rw [rowResidual_sq r i (h i)]
  ring

/-- Every subnormalized column array defines a genuine isometry. -/
theorem column_norm (c : I → J → ℂ) (h : ∀ j, columnMass c j ≤ 1)
    (v : EuclideanSpace ℂ J) : ‖column c v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [column_norm_sq, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [columnResidual_sq c j (h j)]
  ring

/-- Row preparation satisfies the Hilbert isometry identity. -/
theorem row_adjoint_comp (r : I → J → ℂ) (h : ∀ i, rowMass r i ≤ 1) :
    (row r)† ∘L row r = 1 :=
  (row r).norm_map_iff_adjoint_comp_self.mp (row_norm r h)

/-- Column preparation satisfies the Hilbert isometry identity. -/
theorem column_adjoint_comp (c : I → J → ℂ) (h : ∀ j, columnMass c j ≤ 1) :
    (column c)† ∘L column c = 1 :=
  (column c).norm_map_iff_adjoint_comp_self.mp (column_norm c h)

/-- Disjoint failure sectors make no contribution to the row-column overlap. -/
theorem inner_row_column (r c : I → J → ℂ)
    (u : EuclideanSpace ℂ I) (v : EuclideanSpace ℂ J) :
    inner ℂ (row r u) (column c v) =
      ∑ i, ∑ j, star (r i j * u i) * (c i j * v j) := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    mul_comm, mul_assoc]

/-- The exact overlap action, including all phases and all failure sectors. -/
theorem adjoint_column_apply (r c : I → J → ℂ) (v : EuclideanSpace ℂ J) (i : I) :
    (((row r)†) (column c v)) i = ∑ j, (star (r i j) * c i j) * v j := by
  classical
  calc
    (((row r)†) (column c v)) i =
        inner ℂ (EuclideanSpace.single i (1 : ℂ)) (((row r)†) (column c v)) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (row r (EuclideanSpace.single i (1 : ℂ))) (column c v) :=
      adjoint_inner_right _ _ _
    _ = ∑ j, (star (r i j) * c i j) * v j := by
      rw [inner_row_column]
      simp [PiLp.single_apply, mul_assoc, apply_ite]

/-- The bounded operator represented by a finite complex matrix. -/
def matrixOperator (M : Matrix I J ℂ) : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ I :=
  by
    classical
    exact (Matrix.toEuclideanLin M).toContinuousLinearMap

@[simp] theorem matrixOperator_apply (M : Matrix I J ℂ) (v : EuclideanSpace ℂ J) (i : I) :
    matrixOperator M v i = ∑ j, M i j * v j := rfl

/-- The complete compressed operator is the explicit coefficient-overlap matrix. -/
theorem adjoint_column_eq_matrix (r c : I → J → ℂ) :
    (row r)† ∘L column c = matrixOperator (fun i j => star (r i j) * c i j) := by
  ext v i
  exact adjoint_column_apply r c v i

/-- A single overlap matrix entry is the conjugated row amplitude times the
column amplitude, without any contribution from the residual amplitudes. -/
theorem overlap_entry (r c : I → J → ℂ) [DecidableEq J] (i : I) (j : J) :
    (((row r)†) (column c (EuclideanSpace.single j (1 : ℂ)))) i = star (r i j) * c i j := by
  rw [adjoint_column_apply]
  simp [PiLp.single_apply]

/-- Concrete row and column isometries exactly realize the specified overlap. -/
theorem overlap_certificate (r c : I → J → ℂ)
    (hr : ∀ i, rowMass r i ≤ 1) (hc : ∀ j, columnMass c j ≤ 1) :
    (row r)† ∘L row r = 1 ∧ (column c)† ∘L column c = 1 ∧
      (row r)† ∘L column c = matrixOperator (fun i j => star (r i j) * c i j) :=
  ⟨row_adjoint_comp r hr, column_adjoint_comp c hc, adjoint_column_eq_matrix r c⟩

/-- Row states for an actual matrix, with nonnegative good amplitudes. -/
def normalizedRow (H : Matrix I J ℂ) (α : ℝ) : EuclideanSpace ℂ I →L[ℂ] Space I J :=
  row (fun i j => SparseEntryAmplitudes.rowAmplitude α (H i j))

/-- Column states carry the phases of the actual matrix entries. -/
def normalizedColumn (H : Matrix I J ℂ) (α : ℝ) : EuclideanSpace ℂ J →L[ℂ] Space I J :=
  column (fun i j => SparseEntryAmplitudes.columnAmplitude α (H i j))

/-- Row absolute-sum bounds make the normalized matrix row states isometric. -/
theorem normalizedRow_adjoint_comp (H : Matrix I J ℂ) (α : ℝ) (hα : 0 < α)
    (hRow : ∀ i, ∑ j, ‖H i j‖ ≤ α) :
    (normalizedRow H α)† ∘L normalizedRow H α = 1 := by
  apply row_adjoint_comp
  intro i
  exact SparseEntryAmplitudes.row_sum_sq_le_one α hα (H i) (hRow i)

/-- Column absolute-sum bounds give a second, independently normalized isometry. -/
theorem normalizedColumn_adjoint_comp (H : Matrix I J ℂ) (α : ℝ) (hα : 0 < α)
    (hCol : ∀ j, ∑ i, ‖H i j‖ ≤ α) :
    (normalizedColumn H α)† ∘L normalizedColumn H α = 1 := by
  apply column_adjoint_comp
  intro j
  exact SparseEntryAmplitudes.column_sum_sq_le_one α hα (fun i => H i j) (hCol j)

/-- The normalized preparations overlap to exactly the matrix divided by α. -/
theorem normalized_overlap (H : Matrix I J ℂ) (α : ℝ) (hα : 0 < α) :
    (normalizedRow H α)† ∘L normalizedColumn H α =
      matrixOperator (fun i j => H i j / (α : ℂ)) := by
  rw [normalizedRow, normalizedColumn, adjoint_column_eq_matrix]
  congr 1
  funext i j
  exact SparseEntryAmplitudes.overlap α hα (H i j)

/-- Exact matrix overlap certificate with concrete row and column preparations.
This is a state-overlap construction, with no oracle preparation cost asserted. -/
theorem normalized_overlap_certificate (H : Matrix I J ℂ) (α : ℝ) (hα : 0 < α)
    (hRow : ∀ i, ∑ j, ‖H i j‖ ≤ α) (hCol : ∀ j, ∑ i, ‖H i j‖ ≤ α) :
    (normalizedRow H α)† ∘L normalizedRow H α = 1 ∧
      (normalizedColumn H α)† ∘L normalizedColumn H α = 1 ∧
      (normalizedRow H α)† ∘L normalizedColumn H α =
        matrixOperator (fun i j => H i j / (α : ℂ)) :=
  ⟨normalizedRow_adjoint_comp H α hα hRow,
    normalizedColumn_adjoint_comp H α hα hCol, normalized_overlap H α hα⟩

end
end SparseHamiltonian.SparseStateOverlap
