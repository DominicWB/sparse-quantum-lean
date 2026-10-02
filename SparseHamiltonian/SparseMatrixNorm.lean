import SparseHamiltonian.SparseStateOverlap

/-!
# Operator-norm bounds from exact sparse-state overlaps

The concrete row/column isometries give a Schur bound for the actual Euclidean
matrix operator. Applying this bound to the proved row and column absolute sums
establishes the magnitude-band and tail operator normalizations. No query or
state-preparation implementation is asserted.
-/

namespace SparseHamiltonian.SparseMatrixNorm

noncomputable section
open ContinuousLinearMap SparseStateOverlap
open scoped BigOperators InnerProduct

section Isometries
variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- An isometry is a contraction, including when its domain is trivial. -/
theorem norm_le_one_of_adjoint_comp (R : P →L[ℂ] K) (hR : R† ∘L R = 1) :
    ‖R‖ ≤ 1 := by
  apply R.opNorm_le_bound (by norm_num)
  intro v
  rw [R.norm_map_iff_adjoint_comp_self.mpr hR]
  simp

end Isometries

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The normalized matrix operator is a contraction because it is the overlap
of the two explicitly constructed isometries. -/
theorem normalized_norm_le_one (H : Matrix I J ℂ) (α : ℝ) (hα : 0 < α)
    (hRow : ∀ i, ∑ j, ‖H i j‖ ≤ α) (hCol : ∀ j, ∑ i, ‖H i j‖ ≤ α) :
    ‖matrixOperator (fun i j => H i j / (α : ℂ))‖ ≤ 1 := by
  obtain ⟨hR, hC, hOverlap⟩ := normalized_overlap_certificate H α hα hRow hCol
  rw [← hOverlap]
  have hRn := norm_le_one_of_adjoint_comp _ hR
  have hCn := norm_le_one_of_adjoint_comp _ hC
  have hAdj : ‖(normalizedRow H α)†‖ = ‖normalizedRow H α‖ :=
    LinearIsometryEquiv.norm_map _ _
  calc
    ‖(normalizedRow H α)† ∘L normalizedColumn H α‖ ≤
        ‖(normalizedRow H α)†‖ * ‖normalizedColumn H α‖ := opNorm_comp_le _ _
    _ = ‖normalizedRow H α‖ * ‖normalizedColumn H α‖ := by rw [hAdj]
    _ ≤ 1 * 1 := mul_le_mul hRn hCn (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Scalar normalization of matrix entries agrees with scalar normalization of
the actual operator on finite Euclidean Hilbert spaces. -/
theorem matrixOperator_scale_normalized (H : Matrix I J ℂ) (α : ℝ) (hα : α ≠ 0) :
    matrixOperator H = (α : ℂ) • matrixOperator (fun i j => H i j / (α : ℂ)) := by
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  ext v i
  simp only [smul_apply, PiLp.smul_apply, smul_eq_mul, matrixOperator_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp

/-- The actual matrix operator has norm at most any positive common bound on
its row and column absolute sums. -/
theorem norm_matrixOperator_le (H : Matrix I J ℂ) (α : ℝ) (hα : 0 < α)
    (hRow : ∀ i, ∑ j, ‖H i j‖ ≤ α) (hCol : ∀ j, ∑ i, ‖H i j‖ ≤ α) :
    ‖matrixOperator H‖ ≤ α := by
  rw [matrixOperator_scale_normalized H α hα.ne', norm_smul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (normalized_norm_le_one H α hα hRow hCol) hα.le

section Bands
variable {n : Type*} [Fintype n]

/-- The sparsity/energy normalization bounds the spectral norm of each actual
magnitude band, rather than merely its entrywise row and column sums. -/
theorem norm_bandMatrix_le (H : Matrix n n ℂ) (s : ℕ) (a η : ℝ)
    (hs : 1 ≤ s) (ha : 0 < a) (hη : 0 < η)
    (hRowSparse : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hColSparse : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s)
    (hRowEnergy : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ η ^ 2)
    (hColEnergy : ∀ j, ∑ i, ‖H i j‖ ^ 2 ≤ η ^ 2) :
    ‖matrixOperator (bandMatrix a H)‖ ≤ min ((s : ℝ) * a) (2 * η ^ 2 / a) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  apply norm_matrixOperator_le
  · exact lt_min (mul_pos hs' ha) (by positivity)
  · exact bandMatrix_row_sum_le H a η s ha hRowSparse hRowEnergy
  · exact bandMatrix_column_sum_le H a η s ha hColSparse hColEnergy

/-- The retained sparse tail has spectral norm at most its sparsity times the
entry threshold, so no discarded-tail approximation is introduced here. -/
theorem norm_tailMatrix_le (H : Matrix n n ℂ) (s : ℕ) (a : ℝ)
    (hs : 1 ≤ s) (ha : 0 < a)
    (hRowSparse : ∀ i, (nonzeroPositions (H i)).card ≤ s)
    (hColSparse : ∀ j, (nonzeroPositions (fun i => H i j)).card ≤ s) :
    ‖matrixOperator (tailMatrix a H)‖ ≤ (s : ℝ) * a := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  apply norm_matrixOperator_le _ _ (mul_pos hs' ha)
  · exact tailMatrix_row_sum_le H a s ha.le hRowSparse
  · exact tailMatrix_column_sum_le H a s ha.le hColSparse

end Bands
end
end SparseHamiltonian.SparseMatrixNorm
