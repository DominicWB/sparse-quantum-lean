import SparseHamiltonian.ImprovedSparseHamiltonian

/-!
# ODE Hermitian branches with separate row and column energy budgets

This appendix defines the actual matrices D, H and H+kD from the original
possibly nonnormal generator M. It proves the two-entry reconstruction and
support-union property, and derives the common energy bound
`(etaH + R * etaD)^2` without replacing H and D by entrywise absolute values.
These are mathematical input lemmas for a tagged native implementation;
this appendix alone does not construct that implementation or an ODE solver.
-/

namespace SparseHamiltonian.ODEMatrixEnergy

noncomputable section
open ContinuousLinearMap SparseStateOverlap
open scoped BigOperators ComplexConjugate InnerProduct
set_option maxHeartbeats 1000000

section Matrices
variable {n : Type*}

/-- The Hermitian real part of the matrix supplied by the original oracle. -/
def dissipativePart (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (M + M.conjTranspose)

/-- The Hermitian imaginary part of the same matrix. -/
def hamiltonianPart (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (-Complex.I / 2) • (M - M.conjTranspose)

/-- The matrix appearing at a real LCHS quadrature node. -/
def lchsHamiltonian (M : Matrix n n ℂ) (k : ℝ) : Matrix n n ℂ :=
  hamiltonianPart M + (k : ℂ) • dissipativePart M

@[simp] theorem dissipativePart_apply (M : Matrix n n ℂ) (i j : n) :
    dissipativePart M i j = (2 : ℂ)⁻¹ * (M i j + star (M j i)) := rfl

@[simp] theorem hamiltonianPart_apply (M : Matrix n n ℂ) (i j : n) :
    hamiltonianPart M i j = (-Complex.I / 2) * (M i j - star (M j i)) := rfl

@[simp] theorem lchsHamiltonian_apply (M : Matrix n n ℂ) (k : ℝ) (i j : n) :
    lchsHamiltonian M k i j =
      hamiltonianPart M i j + (k : ℂ) * dissipativePart M i j := rfl

/-- Hermiticity is derived from the original entries, not assumed. -/
theorem dissipativePart_isHermitian (M : Matrix n n ℂ) :
    (dissipativePart M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hHalf : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  simp only [dissipativePart_apply, star_mul, star_add, star_star, hHalf]
  ring

theorem hamiltonianPart_isHermitian (M : Matrix n n ℂ) :
    (hamiltonianPart M).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hCoeff : star (-Complex.I / 2) = Complex.I / 2 := by
    simp
  simp only [hamiltonianPart_apply, star_mul, star_sub, star_star, hCoeff]
  ring

theorem lchsHamiltonian_isHermitian (M : Matrix n n ℂ) (k : ℝ) :
    (lchsHamiltonian M k).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have hk : star (k : ℂ) = (k : ℂ) := by simp
  simp only [lchsHamiltonian_apply, star_add, star_mul, hk,
    (dissipativePart_isHermitian M).apply i j,
    (hamiltonianPart_isHermitian M).apply i j]
  ring

/-- The decomposition is exact even for a nonnormal original matrix. -/
theorem decomposition (M : Matrix n n ℂ) :
    dissipativePart M + Complex.I • hamiltonianPart M = M := by
  have hI : Complex.I * (-Complex.I / 2) = (2 : ℂ)⁻¹ := by
    rw [← mul_div_assoc, mul_neg, Complex.I_mul_I]
    norm_num
  ext i j
  change (2 : ℂ)⁻¹ * (M i j + star (M j i)) +
    Complex.I * ((-Complex.I / 2) * (M i j - star (M j i))) = M i j
  rw [← mul_assoc, hI]
  ring

/-- A node needs only the two original values `M i j` and `M j i`.
The public real node changes coefficients, not the set of requested entries. -/
theorem lchsHamiltonian_entry (M : Matrix n n ℂ) (k : ℝ) (i j : n) :
    lchsHamiltonian M k i j =
      (((k : ℂ) - Complex.I) / 2) * M i j +
        (((k : ℂ) + Complex.I) / 2) * star (M j i) := by
  simp only [lchsHamiltonian_apply, hamiltonianPart_apply, dissipativePart_apply]
  ring

/-- Zero original entries in both orientations give a zero branch entry. -/
theorem lchsHamiltonian_eq_zero (M : Matrix n n ℂ) (k : ℝ) (i j : n)
    (hij : M i j = 0) (hji : M j i = 0) : lchsHamiltonian M k i j = 0 := by
  simp [hij, hji]

/-- The branch support is contained in the union of the two original supports.
This is a support statement, not an assumption of a support-union locator. -/
theorem lchsHamiltonian_support (M : Matrix n n ℂ) (k : ℝ) (i j : n)
    (h : lchsHamiltonian M k i j ≠ 0) : M i j ≠ 0 ∨ M j i ≠ 0 := by
  by_cases hij : M i j = 0
  · right
    intro hji
    exact h (lchsHamiltonian_eq_zero M k i j hij hji)
  · exact Or.inl hij

/-- When D vanishes, every quadrature node has the same Hamiltonian.
In particular, the following energy estimates do not introduce an R penalty. -/
theorem lchsHamiltonian_of_dissipative_zero (M : Matrix n n ℂ) (k : ℝ)
    (hD : dissipativePart M = 0) : lchsHamiltonian M k = hamiltonianPart M := by
  simp [lchsHamiltonian, hD]

end Matrices

section Energy
variable {ι : Type*} [Fintype ι]

/-- The Euclidean triangle inequality in entry-energy form. The estimate is
dimension independent and uses the actual complex sums, including cancellation. -/
theorem combination_energy_le (f g : ι → ℂ) (a b k : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∑ i, ‖f i‖ ^ 2 ≤ a ^ 2) (hg : ∑ i, ‖g i‖ ^ 2 ≤ b ^ 2) :
    ∑ i, ‖f i + (k : ℂ) * g i‖ ^ 2 ≤ (a + |k| * b) ^ 2 := by
  let u : EuclideanSpace ℂ ι := WithLp.toLp 2 f
  let v : EuclideanSpace ℂ ι := WithLp.toLp 2 g
  have hu : ‖u‖ ≤ a := by
    apply (sq_le_sq₀ (norm_nonneg u) ha).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact hf
  have hv : ‖v‖ ≤ b := by
    apply (sq_le_sq₀ (norm_nonneg v) hb).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact hg
  have hk : ‖(k : ℂ)‖ = |k| := by simp [Complex.norm_real, Real.norm_eq_abs]
  have hNorm : ‖u + (k : ℂ) • v‖ ≤ a + |k| * b := by
    calc
      ‖u + (k : ℂ) • v‖ ≤ ‖u‖ + ‖(k : ℂ) • v‖ := norm_add_le _ _
      _ = ‖u‖ + |k| * ‖v‖ := by rw [norm_smul, hk]
      _ ≤ a + |k| * b :=
        add_le_add hu (mul_le_mul_of_nonneg_left hv (abs_nonneg k))
  have hSquare := pow_le_pow_left₀ (norm_nonneg (u + (k : ℂ) • v)) hNorm 2
  rw [PiLp.norm_sq_eq_of_L2] at hSquare
  exact hSquare

/-- One known cutoff controls all the entry-energy bounds simultaneously. -/
theorem combination_energy_le_radius (f g : ι → ℂ) (a b k R : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hk : |k| ≤ R)
    (hf : ∑ i, ‖f i‖ ^ 2 ≤ a ^ 2) (hg : ∑ i, ‖g i‖ ^ 2 ≤ b ^ 2) :
    ∑ i, ‖f i + (k : ℂ) * g i‖ ^ 2 ≤ (a + R * b) ^ 2 := by
  have hBound : a + |k| * b ≤ a + R * b :=
    add_le_add (le_refl a) (mul_le_mul_of_nonneg_right hk hb)
  exact (combination_energy_le f g a b k ha hb hf hg).trans
    (pow_le_pow_left₀ (add_nonneg ha (mul_nonneg (abs_nonneg k) hb)) hBound 2)

end Energy

section MatrixEnergy
variable {n : Type*} [Fintype n]

/-- Each row has the refined separate-H-and-D budget. -/
theorem lchs_row_energy_le (M : Matrix n n ℂ) (etaH etaD k : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hRowH : ∀ i, ∑ j, ‖hamiltonianPart M i j‖ ^ 2 ≤ etaH ^ 2)
    (hRowD : ∀ i, ∑ j, ‖dissipativePart M i j‖ ^ 2 ≤ etaD ^ 2) (i : n) :
    ∑ j, ‖lchsHamiltonian M k i j‖ ^ 2 ≤ (etaH + |k| * etaD) ^ 2 :=
  combination_energy_le (hamiltonianPart M i) (dissipativePart M i)
    etaH etaD k hH hD (hRowH i) (hRowD i)

/-- The identical argument applies to columns, without a factor of dimension. -/
theorem lchs_column_energy_le (M : Matrix n n ℂ) (etaH etaD k : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hColH : ∀ j, ∑ i, ‖hamiltonianPart M i j‖ ^ 2 ≤ etaH ^ 2)
    (hColD : ∀ j, ∑ i, ‖dissipativePart M i j‖ ^ 2 ≤ etaD ^ 2) (j : n) :
    ∑ i, ‖lchsHamiltonian M k i j‖ ^ 2 ≤ (etaH + |k| * etaD) ^ 2 :=
  combination_energy_le (fun i => hamiltonianPart M i j)
    (fun i => dissipativePart M i j) etaH etaD k hH hD (hColH j) (hColD j)

/-- The common branch normalization is `rho = etaH + R * etaD`.
All four matrix-energy premises concern D and H, not a pre-split oracle. -/
theorem lchs_energies_le_radius (M : Matrix n n ℂ) (etaH etaD k R : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hk : |k| ≤ R)
    (hRowH : ∀ i, ∑ j, ‖hamiltonianPart M i j‖ ^ 2 ≤ etaH ^ 2)
    (hColH : ∀ j, ∑ i, ‖hamiltonianPart M i j‖ ^ 2 ≤ etaH ^ 2)
    (hRowD : ∀ i, ∑ j, ‖dissipativePart M i j‖ ^ 2 ≤ etaD ^ 2)
    (hColD : ∀ j, ∑ i, ‖dissipativePart M i j‖ ^ 2 ≤ etaD ^ 2) :
    (∀ i, ∑ j, ‖lchsHamiltonian M k i j‖ ^ 2 ≤ (etaH + R * etaD) ^ 2) ∧
      (∀ j, ∑ i, ‖lchsHamiltonian M k i j‖ ^ 2 ≤ (etaH + R * etaD) ^ 2) := by
  constructor
  · intro i
    exact combination_energy_le_radius (hamiltonianPart M i) (dissipativePart M i)
      etaH etaD k R hH hD hk (hRowH i) (hRowD i)
  · intro j
    exact combination_energy_le_radius (fun i => hamiltonianPart M i j)
      (fun i => dissipativePart M i j) etaH etaD k R hH hD hk (hColH j) (hColD j)

/-- The same common energy budget bounds every individual branch entry. -/
theorem lchs_entry_norm_le_radius (M : Matrix n n ℂ) (etaH etaD k R : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hk : |k| ≤ R)
    (hRowH : ∀ i, ∑ j, ‖hamiltonianPart M i j‖ ^ 2 ≤ etaH ^ 2)
    (hRowD : ∀ i, ∑ j, ‖dissipativePart M i j‖ ^ 2 ≤ etaD ^ 2) (i j : n) :
    ‖lchsHamiltonian M k i j‖ ≤ etaH + R * etaD := by
  have hR : 0 ≤ R := (abs_nonneg k).trans hk
  exact norm_le_of_energy_le (etaH + R * etaD) (lchsHamiltonian M k i)
    (add_nonneg hH (mul_nonneg hR hD))
    (combination_energy_le_radius (hamiltonianPart M i) (dissipativePart M i)
      etaH etaD k R hH hD hk (hRowH i) (hRowD i)) j

end MatrixEnergy

section OperatorCompatibility
variable {n : Type*} [Fintype n]

/-- Matrix addition agrees with addition of the actual Euclidean operators. -/
theorem matrixOperator_add (M N : Matrix n n ℂ) :
    matrixOperator (M + N) = matrixOperator M + matrixOperator N := by
  ext v i
  simp [matrixOperator_apply, add_mul, Finset.sum_add_distrib]

theorem matrixOperator_smul (c : ℂ) (M : Matrix n n ℂ) :
    matrixOperator (c • M) = c • matrixOperator M := by
  ext v i
  simp [matrixOperator_apply, mul_assoc, Finset.mul_sum]

/-- The entry-level dissipative part is the previously formalized operator. -/
theorem matrixOperator_dissipativePart (M : Matrix n n ℂ) :
    matrixOperator (dissipativePart M) =
      ODEHermitianReduction.dissipativePart (matrixOperator M) := by
  rw [dissipativePart, matrixOperator_smul, matrixOperator_add]
  simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart,
    SparseValuePrecision.matrixOperator_adjoint]

/-- The entry-level Hamiltonian part has the same compatibility. -/
theorem matrixOperator_hamiltonianPart (M : Matrix n n ℂ) :
    matrixOperator (hamiltonianPart M) =
      ODEHermitianReduction.hamiltonianPart (matrixOperator M) := by
  rw [hamiltonianPart, matrixOperator_smul, SparseValuePrecision.matrixOperator_sub]
  simp only [ODEHermitianReduction.hamiltonianPart,
    SparseValuePrecision.matrixOperator_adjoint]

/-- The tagged-entry target is exactly the operator in the LCHS reduction. -/
theorem matrixOperator_lchsHamiltonian (M : Matrix n n ℂ) (k : ℝ) :
    matrixOperator (lchsHamiltonian M k) =
      ODEHermitianReduction.lchsHamiltonian (matrixOperator M) k := by
  rw [lchsHamiltonian, matrixOperator_add, matrixOperator_smul,
    matrixOperator_hamiltonianPart, matrixOperator_dissipativePart,
    ODEHermitianReduction.lchsHamiltonian]
  exact add_comm _ _

end OperatorCompatibility
end
end SparseHamiltonian.ODEMatrixEnergy
