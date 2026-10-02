import SparseHamiltonian.NativeWeightedSimulation

/-!
# Entry-energy bounds from the actual spectral operator norm

A column is the image of a unit computational basis vector. Its squared entry
norms therefore sum to at most the squared spectral norm. Hermitian symmetry
supplies the row statement. These lemmas turn the usual spectral normalization
into the row/column energy premises of the sparse band construction.

The same energy bounds survive concrete dyadic rounding. This does not assert
that entrywise rounding contracts the spectral norm, which is unnecessary.
-/

namespace SparseHamiltonian.SparseSpectralEnergy

noncomputable section
open SparseStateOverlap ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

section Columns
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Applying the actual matrix operator to a standard basis vector selects its
column, including all complex phases. -/
@[simp] theorem matrixOperator_single [DecidableEq J] (H : Matrix I J ℂ)
    (j : J) (i : I) : matrixOperator H (EuclideanSpace.single j 1) i = H i j := by
  simp [matrixOperator_apply, PiLp.single_apply]

/-- Column entry energy is exactly the squared Hilbert-space output norm. -/
theorem column_energy_eq [DecidableEq J] (H : Matrix I J ℂ) (j : J) :
    ∑ i, ‖H i j‖ ^ 2 = ‖matrixOperator H (EuclideanSpace.single j 1)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [matrixOperator_single]

/-- Every column has Euclidean energy bounded by the squared spectral norm.
No Hermitian assumption is needed for this direction. -/
theorem column_energy_le_norm_sq (H : Matrix I J ℂ) (j : J) :
    ∑ i, ‖H i j‖ ^ 2 ≤ ‖matrixOperator H‖ ^ 2 := by
  classical
  rw [column_energy_eq]
  have h : ‖matrixOperator H (EuclideanSpace.single j 1)‖ ≤ ‖matrixOperator H‖ := by
    simpa using (matrixOperator H).le_opNorm (EuclideanSpace.single j 1)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- A supplied spectral upper bound gives the column-energy premise directly. -/
theorem column_energy_le (H : Matrix I J ℂ) (η : ℝ)
    (hNorm : ‖matrixOperator H‖ ≤ η) (j : J) :
    ∑ i, ‖H i j‖ ^ 2 ≤ η ^ 2 :=
  (column_energy_le_norm_sq H j).trans (pow_le_pow_left₀ (norm_nonneg _) hNorm 2)

end Columns

section Hermitian
variable {n : Type*} [Fintype n]

/-- Hermitian rows and columns have exactly the same squared entry energy. -/
theorem row_energy_eq_column (H : Matrix n n ℂ) (hH : H.IsHermitian) (i : n) :
    ∑ j, ‖H i j‖ ^ 2 = ∑ j, ‖H j i‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro j _
  rw [← hH.apply i j, norm_star]

/-- Hermitian symmetry supplies the spectral bound for each row as well. -/
theorem row_energy_le_norm_sq (H : Matrix n n ℂ) (hH : H.IsHermitian) (i : n) :
    ∑ j, ‖H i j‖ ^ 2 ≤ ‖matrixOperator H‖ ^ 2 := by
  rw [row_energy_eq_column H hH i]
  exact column_energy_le_norm_sq H i

/-- A supplied spectral upper bound gives the Hermitian row-energy premise. -/
theorem row_energy_le (H : Matrix n n ℂ) (hH : H.IsHermitian) (η : ℝ)
    (hNorm : ‖matrixOperator H‖ ≤ η) (i : n) :
    ∑ j, ‖H i j‖ ^ 2 ≤ η ^ 2 := by
  rw [row_energy_eq_column H hH i]
  exact column_energy_le H η hNorm i

/-- Both energy premises follow together from the usual Hermitian spectral
normalization; the conclusion covers zero norm and zero-dimensional spaces. -/
theorem energies_of_spectral_bound (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (η : ℝ) (hNorm : ‖matrixOperator H‖ ≤ η) :
    (∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ η ^ 2) ∧
      (∀ j, ∑ i, ‖H i j‖ ^ 2 ≤ η ^ 2) :=
  ⟨row_energy_le H hH η hNorm, column_energy_le H η hNorm⟩

end Hermitian

section Native
variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- One public spectral promise supplies both native band-energy hypotheses
uniformly over every unknown oracle input. -/
theorem native_energies (D : Data X n Z s) (η : ℝ)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ η) :
    (∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) ∧
      (∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :=
  ⟨fun x => row_energy_le _ (hH x) η (hNorm x),
    fun x => column_energy_le _ η (hNorm x)⟩

/-- The same spectral parameter bounds every rounded row energy, without a
claim that the rounded matrix itself has no larger spectral norm. -/
theorem rounded_native_row_energy (D : Data X n Z s) (b : ℕ) (η : ℝ)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ η) (x : X) (i : n) :
    ∑ j, ‖(NativeRoundedEncoding.rounded D b).matrix x i j‖ ^ 2 ≤ η ^ 2 :=
  (NativeRoundedEncoding.rounded_row_energy_le D b x i).trans
    (row_energy_le _ (hH x) η (hNorm x) i)

/-- Rounded columns likewise retain the original spectral energy parameter. -/
theorem rounded_native_column_energy (D : Data X n Z s) (b : ℕ) (η : ℝ)
    (hNorm : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ η) (x : X) (j : n) :
    ∑ i, ‖(NativeRoundedEncoding.rounded D b).matrix x i j‖ ^ 2 ≤ η ^ 2 :=
  (NativeRoundedEncoding.rounded_column_energy_le D b x j).trans
    (column_energy_le _ η (hNorm x) j)

end Native
end
end SparseHamiltonian.SparseSpectralEnergy
