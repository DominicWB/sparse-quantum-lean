import SparseODE.ODEMatrixEnergy
import SparseODE.ODEPublicSourceMesh

/-!
# The generator as a combination of two LCHS Hamiltonians

With `M` the sparse matrix (`A = -M`), `L = (M + M†)/2`, `H = (M - M†)/(2i)` and
`K_± = H ± L` (the released tagged Hamiltonians at `k = ±1`),
`A = -((1+i)/2) K₊ + ((1-i)/2) K₋`.  If `‖A‖ ≤ Λ`, then `‖K_±‖ ≤ 2Λ`, and every
row and column of `H` and of `L` has Euclidean norm at most `Λ`; these are the
row/column energies required by the released native simulator.  No
dissipativity is used.
-/

namespace SparseHamiltonian.GeneralODE.NativeMatrix

noncomputable section
open ContinuousLinearMap ODEMatrixEnergy SparseStateOverlap
open scoped BigOperators InnerProduct ComplexConjugate

variable {n : Type} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- Entrywise decomposition of `-M`. -/
theorem neg_eq_lchs_combination (M : Matrix n n ℂ) :
    -M = (-(1 + Complex.I) / 2) • lchsHamiltonian M 1 +
      ((1 - Complex.I) / 2) • lchsHamiltonian M (-1) := by
  ext i j
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    lchsHamiltonian_apply, hamiltonianPart_apply, dissipativePart_apply]
  push_cast
  linear_combination (-(M i j - star (M j i)) / 2) * Complex.I_sq

omit [DecidableEq n] in
/-- The operator form of the decomposition. -/
theorem neg_matrixOperator_eq (M : Matrix n n ℂ) :
    -matrixOperator M =
      (-(1 + Complex.I) / 2) • matrixOperator (lchsHamiltonian M 1) +
        ((1 - Complex.I) / 2) • matrixOperator (lchsHamiltonian M (-1)) := by
  rw [← matrixOperator_smul, ← matrixOperator_smul, ← matrixOperator_add,
    ← neg_eq_lchs_combination]
  ext v i
  simp [matrixOperator_apply, Finset.sum_neg_distrib]

omit [DecidableEq n] in
theorem norm_dissipativePart_op_le (M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ‖ODEHermitianReduction.dissipativePart M‖ ≤ ‖M‖ := by
  unfold ODEHermitianReduction.dissipativePart HermitianDilation.hermitianPart
  rw [norm_smul, norm_inv, Complex.norm_two]
  calc 2⁻¹ * ‖M + M†‖ ≤ 2⁻¹ * (‖M‖ + ‖M†‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = ‖M‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

omit [DecidableEq n] in
theorem norm_hamiltonianPart_op_le (M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ‖ODEHermitianReduction.hamiltonianPart M‖ ≤ ‖M‖ := by
  unfold ODEHermitianReduction.hamiltonianPart
  rw [norm_smul, norm_div, norm_neg, Complex.norm_I, Complex.norm_two]
  calc 1 / 2 * ‖M - M†‖ ≤ 1 / 2 * (‖M‖ + ‖M†‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = ‖M‖ := by rw [ContinuousLinearMap.adjoint.norm_map]; ring

omit [DecidableEq n] in
/-- `‖K_k‖ ≤ (1 + |k|) ‖M‖`. -/
theorem norm_lchs_le (M : Matrix n n ℂ) (k : ℝ) :
    ‖matrixOperator (lchsHamiltonian M k)‖ ≤ (1 + |k|) * ‖matrixOperator M‖ := by
  rw [matrixOperator_lchsHamiltonian]
  unfold ODEHermitianReduction.lchsHamiltonian
  calc ‖(k : ℂ) • ODEHermitianReduction.dissipativePart (matrixOperator M) +
        ODEHermitianReduction.hamiltonianPart (matrixOperator M)‖
      ≤ |k| * ‖matrixOperator M‖ + ‖matrixOperator M‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ (norm_hamiltonianPart_op_le _))
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_dissipativePart_op_le _) (abs_nonneg k)
    _ = (1 + |k|) * ‖matrixOperator M‖ := by ring

/-- Columns of a matrix are bounded by its operator norm. -/
theorem column_energy_le (N : Matrix n n ℂ) (j : n) :
    ∑ i, ‖N i j‖ ^ 2 ≤ ‖matrixOperator N‖ ^ 2 := by
  have h : matrixOperator N (EuclideanSpace.single j 1) = WithLp.toLp 2 (fun i => N i j) := by
    ext i
    simp [matrixOperator_apply]
  have hle : ‖matrixOperator N (EuclideanSpace.single j 1)‖ ≤ ‖matrixOperator N‖ := by
    refine ((matrixOperator N).le_opNorm _).trans ?_
    simp
  rw [h] at hle
  have := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [EuclideanSpace.norm_sq_eq] at this
  simpa using this

/-- Rows of a matrix are bounded by its operator norm. -/
theorem row_energy_le (N : Matrix n n ℂ) (i : n) :
    ∑ j, ‖N i j‖ ^ 2 ≤ ‖matrixOperator N‖ ^ 2 := by
  have h := column_energy_le N.conjTranspose i
  have hadj : ‖matrixOperator N.conjTranspose‖ = ‖matrixOperator N‖ := by
    rw [← SparseValuePrecision.matrixOperator_adjoint, ContinuousLinearMap.adjoint.norm_map]
  rw [hadj] at h
  refine le_of_eq_of_le ?_ h
  apply Finset.sum_congr rfl
  intro j _
  simp [Matrix.conjTranspose_apply]

theorem hamiltonian_energy_le (M : Matrix n n ℂ) (Λ : ℝ) (hM : ‖matrixOperator M‖ ≤ Λ) :
    (∀ i, ∑ j, ‖hamiltonianPart M i j‖ ^ 2 ≤ Λ ^ 2) ∧
      (∀ j, ∑ i, ‖hamiltonianPart M i j‖ ^ 2 ≤ Λ ^ 2) := by
  have hop : ‖matrixOperator (hamiltonianPart M)‖ ≤ Λ := by
    rw [matrixOperator_hamiltonianPart]
    exact (norm_hamiltonianPart_op_le _).trans hM
  have hsq : ‖matrixOperator (hamiltonianPart M)‖ ^ 2 ≤ Λ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hop 2
  exact ⟨fun i => (row_energy_le _ i).trans hsq, fun j => (column_energy_le _ j).trans hsq⟩

theorem dissipative_energy_le (M : Matrix n n ℂ) (Λ : ℝ) (hM : ‖matrixOperator M‖ ≤ Λ) :
    (∀ i, ∑ j, ‖dissipativePart M i j‖ ^ 2 ≤ Λ ^ 2) ∧
      (∀ j, ∑ i, ‖dissipativePart M i j‖ ^ 2 ≤ Λ ^ 2) := by
  have hop : ‖matrixOperator (dissipativePart M)‖ ≤ Λ := by
    rw [matrixOperator_dissipativePart]
    exact (norm_dissipativePart_op_le _).trans hM
  have hsq : ‖matrixOperator (dissipativePart M)‖ ^ 2 ≤ Λ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hop 2
  exact ⟨fun i => (row_energy_le _ i).trans hsq, fun j => (column_energy_le _ j).trans hsq⟩

end

end SparseHamiltonian.GeneralODE.NativeMatrix
