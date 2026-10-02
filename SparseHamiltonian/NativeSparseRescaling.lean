import SparseHamiltonian.ImprovedNativeSimulation

/-!
# Positive spectral-energy normalization with unchanged native access

Only the public decoder and the represented matrix are rescaled. The supplied
row and column locators, their arbitrary full-unitary extensions, and the value
table are exactly unchanged. Thus all primitive oracle families and all public
input/output embeddings are the same before and after normalization.
-/

namespace SparseHamiltonian.NativeSparseRescaling

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Positive normalization changes fixed decoder arithmetic but no queried data. -/
def normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η) : Data X n Z s where
  slot := D.slot
  slots_pos := D.slots_pos
  scale := D.scale / η
  scale_pos := div_pos D.scale_pos hη
  matrix := fun x i j => ((η⁻¹ : ℝ) : ℂ) * D.matrix x i j
  table := D.table
  decode := fun a z => ((η⁻¹ : ℝ) : ℂ) * D.decode a z
  decode_bound := by
    intro a z
    calc
      ‖((η⁻¹ : ℝ) : ℂ) * D.decode a z‖ = η⁻¹ * ‖D.decode a z‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hη)]
      _ ≤ η⁻¹ * D.scale :=
        mul_le_mul_of_nonneg_left (D.decode_bound a z) (inv_nonneg.mpr hη.le)
      _ = D.scale / η := by rw [div_eq_mul_inv]; ring
  decoded := by
    intro x i j
    rw [D.decoded]
  rowloc := D.rowloc
  colloc := D.colloc
  row_injective := D.row_injective
  column_injective := D.column_injective
  row_covers := by
    intro x i j h
    apply D.row_covers x i j
    intro hz
    exact h (by rw [hz, mul_zero])
  column_covers := by
    intro x i j h
    apply D.column_covers x i j
    intro hz
    exact h (by rw [hz, mul_zero])
  rowOracle := D.rowOracle
  columnOracle := D.columnOracle
  row_unitary := D.row_unitary
  column_unitary := D.column_unitary
  row_valid := D.row_valid
  column_valid := D.column_valid

@[simp] theorem normalize_matrix (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (x : X) (i j : n) :
    (normalize D η hη).matrix x i j = ((η⁻¹ : ℝ) : ℂ) * D.matrix x i j := rfl

/-- Real scalar normalization preserves the exact Hermitian symmetry. -/
theorem normalize_hermitian (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (x : X) (hH : (D.matrix x).IsHermitian) :
    ((normalize D η hη).matrix x).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [normalize_matrix, hH.apply i j]

/-- Dividing entry norms by a positive energy bound normalizes their square sum. -/
theorem normalized_energy {I : Type*} [Fintype I] (f : I → ℂ)
    (η : ℝ) (hη : 0 < η) (h : ∑ i, ‖f i‖ ^ 2 ≤ η ^ 2) :
    ∑ i, ‖((η⁻¹ : ℝ) : ℂ) * f i‖ ^ 2 ≤ 1 := by
  calc
    ∑ i, ‖((η⁻¹ : ℝ) : ℂ) * f i‖ ^ 2 =
        (η⁻¹) ^ 2 * ∑ i, ‖f i‖ ^ 2 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hη), mul_pow, Finset.mul_sum]
    _ ≤ (η⁻¹) ^ 2 * η ^ 2 := mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = 1 := by field_simp [hη.ne']

/-- Row energies normalize without a sparsity or dimension loss. -/
theorem normalized_row_energy (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (x : X) (i : n) (h : ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∑ j, ‖(normalize D η hη).matrix x i j‖ ^ 2 ≤ 1 :=
  normalized_energy (D.matrix x i) η hη h

/-- The same normalization applies to columns, including independent padding. -/
theorem normalized_column_energy (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (x : X) (j : n) (h : ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∑ i, ‖(normalize D η hη).matrix x i j‖ ^ 2 ≤ 1 :=
  normalized_energy (fun i => D.matrix x i j) η hη h

/-- Entry normalization is exactly scalar multiplication of the represented operator. -/
theorem matrixOperator_normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (x : X) :
    SparseStateOverlap.matrixOperator ((normalize D η hη).matrix x) =
      ((η⁻¹ : ℝ) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  ext v i
  simp only [SparseStateOverlap.matrixOperator_apply, normalize_matrix,
    smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Increasing the duration by eta cancels the matrix normalization exactly. -/
theorem exponent_cancel (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (x : X) (t : ℝ) :
    (-Complex.I * ((η * t : ℝ) : ℂ)) •
        SparseStateOverlap.matrixOperator ((normalize D η hη).matrix x) =
      (-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  rw [matrixOperator_normalize, smul_smul]
  have hηc : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  congr 1
  push_cast
  field_simp [hηc]

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

omit [DecidableEq Z] in
/-- The primitive row, column and value calls are literally unchanged. -/
@[simp] theorem raw_oracles_normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η) :
    NativeSparseBlockEncoding.oracles (normalize D η hη) =
      NativeSparseBlockEncoding.oracles D := rfl

omit [DecidableEq Z] in
/-- Fixed spectator extensions and register layouts preserve that identity. -/
@[simp] theorem oracle_normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (γ τ ε : ℝ) :
    ImprovedNativeSimulation.oracle (normalize D η hη) γ τ ε =
      ImprovedNativeSimulation.oracle D γ τ ε := rfl

/-- The whole physical clean encoding depends only on the original public slots. -/
@[simp] theorem embedding_normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (γ τ ε : ℝ) :
    ImprovedNativeSimulation.embedding (normalize D η hη) γ τ ε =
      ImprovedNativeSimulation.embedding D γ τ ε := rfl

@[simp] theorem input_normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (γ τ ε : ℝ) :
    ImprovedNativeSimulation.input (normalize D η hη) γ τ ε =
      ImprovedNativeSimulation.input D γ τ ε := rfl

@[simp] theorem output_normalize (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (γ τ ε : ℝ) :
    ImprovedNativeSimulation.output (normalize D η hη) γ τ ε =
      ImprovedNativeSimulation.output D γ τ ε := rfl

end
end SparseHamiltonian.NativeSparseRescaling
