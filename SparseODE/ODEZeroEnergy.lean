import SparseODE.ODEFinalNativeSourceContinuation2

/-!
# Exact reduction when the public effective matrix energy vanishes

Nonnegative Hermitian-part bounds and the strictly positive public radius
force both part bounds to vanish. The row-energy promises then force every
entry of the original matrix to vanish, and the actual ODE solution is the
two-source vector `v + T • b`. No matrix-zero promise is added to the solver.

-/

namespace SparseHamiltonian.ODEZeroEnergy

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding
open scoped BigOperators Interval InnerProduct

/-- A positive weighting cannot conceal either of two nonnegative zero
energy budgets. -/
theorem parts_zero_of_effective_zero (etaH etaD r : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hr : 0 < r)
    (hρ : etaH + r * etaD = 0) : etaH = 0 ∧ etaD = 0 := by
  have hProduct : 0 ≤ r * etaD := mul_nonneg hr.le hD
  have hHzero : etaH = 0 := by linarith
  have hProductZero : r * etaD = 0 := by linarith
  exact ⟨hHzero, (mul_eq_zero.mp hProductZero).resolve_left hr.ne'⟩

section Matrices

variable {n : Type*} [Fintype n]

/-- A matrix whose row squared norms vanish is exactly zero. -/
theorem matrix_zero_of_row_energy (M : Matrix n n ℂ)
    (hRow : ∀ i, ∑ j, ‖M i j‖ ^ 2 ≤ 0) : M = 0 := by
  ext i j
  have h := SparseHamiltonian.norm_le_of_energy_le 0 (M i) le_rfl
    (by simpa using hRow i) j
  exact norm_le_zero_iff.mp h

/-- Vanishing energy of both Hermitian parts forces the supplied matrix
to vanish, without a normality or commutativity hypothesis. -/
theorem matrix_zero_of_zero_part_energy (M : Matrix n n ℂ)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart M i j‖ ^ 2 ≤ 0)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart M i j‖ ^ 2 ≤ 0) :
    M = 0 := by
  have hH := matrix_zero_of_row_energy (ODEMatrixEnergy.hamiltonianPart M) hrH
  have hD := matrix_zero_of_row_energy (ODEMatrixEnergy.dissipativePart M) hrD
  simpa only [hH, hD, smul_zero, zero_add] using (ODEMatrixEnergy.decomposition M).symm

/-- The public zero-effective-energy condition discharges the original
matrix-zero conclusion directly from its two row-energy promises. -/
theorem matrix_zero_of_effective_energy (M : Matrix n n ℂ) (etaH etaD r : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hr : 0 < r)
    (hρ : etaH + r * etaD = 0)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart M i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart M i j‖ ^ 2 ≤ etaD ^ 2) :
    M = 0 := by
  obtain ⟨hHzero, hDzero⟩ := parts_zero_of_effective_zero etaH etaD r hH hD hr hρ
  apply matrix_zero_of_zero_part_energy M
  · intro i
    simpa only [hHzero, zero_pow (by norm_num : 2 ≠ 0)] using hrH i
  · intro i
    simpa only [hDzero, zero_pow (by norm_num : 2 ≠ 0)] using hrD i

omit [Fintype n] in
/-- Every Hermitian frequency branch of the zero matrix is itself zero. -/
theorem lchsHamiltonian_zero (k : ℝ) :
    ODEMatrixEnergy.lchsHamiltonian (0 : Matrix n n ℂ) k = 0 := by
  ext i j
  change (-Complex.I / 2) * ((0 : ℂ) - star 0) +
    (k : ℂ) * ((2 : ℂ)⁻¹ * (0 + star 0)) = 0
  simp

end Matrices

section ZeroGenerator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

omit [CompleteSpace V] in
/-- Homogeneous propagation under the zero generator is the identity. -/
theorem trajectory_zero_generator (v : V) (t : ℝ) :
    ODEDissipative.trajectory (0 : V →L[ℂ] V) v t = v := by
  simp [ODEDissipative.trajectory]

/-- Constant forcing accumulates exactly linearly under the zero generator. -/
theorem response_zero_generator (b : V) (t : ℝ) :
    ODEConstantForcing.response (0 : V →L[ℂ] V) b t = t • b := by
  simp only [ODEConstantForcing.response, trajectory_zero_generator,
    intervalIntegral.integral_const, sub_zero]

/-- The actual zero-generator ODE solution is the two-source target. -/
theorem solution_zero_generator (v b : V) (t : ℝ) :
    ODEConstantForcing.solution (0 : V →L[ℂ] V) v b t = v + t • b := by
  rw [ODEConstantForcing.solution, trajectory_zero_generator, response_zero_generator]

omit [CompleteSpace V] in
/-- Every source-duration propagator is the identity in the zero-generator case. -/
theorem propagation_zero_generator (T : ℝ) (N : ℕ) (a : Option (Fin N)) :
    ODESourceBranches.propagation (0 : V →L[ℂ] V) T N a = 1 := by
  rw [ODESourceBranches.propagation, smul_zero, NormedSpace.exp_zero]

end ZeroGenerator

section Native

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The public Gaussian radius is strictly positive throughout the algorithm's
precision range, so zero effective energy forces the native generator to zero. -/
theorem native_generator_zero (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (x : X) : ODEPublicSourceMesh.generator D x = 0 := by
  have hRadius : 0 < ImprovedODEQueryBudget.radius g ε :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
      (ODEGaussianParameters.radius_ge_four g ε hg hε hεOne)
  have hMatrix := matrix_zero_of_effective_energy (D.matrix x) etaH etaD
    (ImprovedODEQueryBudget.radius g ε) hH hD hRadius hρ (hrH x) (hrD x)
  rw [ODEPublicSourceMesh.generator, hMatrix, NativeZeroSimulation.matrixOperator_zero,
    neg_zero]

/-- The original sparse instance therefore has the exact source-only target. -/
theorem native_solution_of_zero_energy (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hg : 1 ≤ g)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (v b : EuclideanSpace ℂ n) (T : ℝ) (x : X) :
    ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T = v + T • b := by
  rw [native_generator_zero D etaH etaD g ε hH hD hg hε hεOne hρ hrH hrD x,
    solution_zero_generator]

/-- All coherent Hamiltonian branches become identity operators when the
original matrix vanishes; no simulation query is needed for any duration. -/
theorem branchEvolution_eq_one_of_matrix_zero {ι : Type*}
    (D : Data X n Z s) (k u : ι → ℝ) (x : X) (hMatrix : D.matrix x = 0) (i : ι) :
    ODENativeLCU.branchEvolution D k u x i = 1 := by
  rw [ODENativeLCU.branchEvolution, hMatrix, lchsHamiltonian_zero,
    NativeZeroSimulation.matrixOperator_zero]
  have hZero : (-Complex.I * (u i : ℂ)) •
      (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) = 0 := by
    ext v j
    simp only [_root_.smul_apply, zero_apply, PiLp.smul_apply, PiLp.zero_apply,
      smul_eq_mul, mul_zero]
  have hExp := congrArg
    (fun A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n => NormedSpace.exp A) hZero
  convert! (hExp.trans NormedSpace.exp_zero) using 1

end Native
end
end SparseHamiltonian.ODEZeroEnergy
