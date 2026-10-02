import SparseHamiltonian.NativeSparseSimulation

/-!
# Exact zero-query sparse simulation at zero energy

A zero public row-energy or operator-norm bound forces the actual Hamiltonian
to vanish. The identity native program then implements its evolution exactly
for every real time, with the same fixed clean input and output isometry.
No positive normalization or band decomposition is invoked in this case.
-/
namespace SparseHamiltonian.NativeZeroSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

omit [DecidableEq n] in
/-- The zero matrix gives the zero operator on the public Euclidean space. -/
theorem matrixOperator_zero : SparseStateOverlap.matrixOperator (0 : Matrix n n ℂ) = 0 := by
  ext v i
  simp [SparseStateOverlap.matrixOperator_apply]

/-- A nonpositive public operator-norm bound forces every matrix entry to vanish. -/
theorem matrix_zero_of_norm (D : Data X n Z s)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 0) :
    ∀ x, D.matrix x = 0 := by
  intro x
  have hz : SparseStateOverlap.matrixOperator (D.matrix x) = 0 := norm_le_zero_iff.mp (hNorm x)
  ext i j
  have h := congrArg (fun T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n =>
    T (EuclideanSpace.single j 1) i) hz
  simpa [SparseStateOverlap.matrixOperator_apply] using h

/-- The original row-energy promise also discharges the zero-Hamiltonian case. -/
theorem matrix_zero_of_energy (D : Data X n Z s)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 0) :
    ∀ x, D.matrix x = 0 := ActualAmplifiedBands.matrix_zero_of_energy_zero D hRow

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- An actual uniform program containing no original sparse-oracle calls. -/
def program (D : Data X n Z s) :
    MultiOracleCircuit.Program (NativeSparseAttenuation.oracles D) := .identity

/-- The same clean native sparse input is retained. -/
def input (D : Data X n Z s) := (NativeSparseAttenuation.input D).toContinuousLinearMap

/-- Exact zero evolution returns every ancillary register to its original encoding. -/
def output (D : Data X n Z s) := input D

omit [DecidableEq Z] in
@[simp] theorem count (D : Data X n Z s) : (program D).count = 0 := rfl

omit [DecidableEq Z] in
@[simp] theorem cost (D : Data X n Z s) (w : Query → ℕ) : (program D).cost w = 0 := rfl

omit [DecidableEq Z] in
@[simp] theorem eval (D : Data X n Z s) (x : X) : (program D).eval x = 1 := rfl

omit [DecidableEq Z] in
/-- Global physical unitarity holds independently of any matrix promise. -/
theorem unitary (D : Data X n Z s) (x : X) : IsUnitary ((program D).eval x) := isUnitary_one

/-- The fixed public input is isometric. -/
theorem input_isometry (D : Data X n Z s) : (input D)† ∘L input D = 1 :=
  NativeSparseAttenuation.input_adjoint_comp D

/-- The entire fixed output, including all ancillas, is isometric. -/
theorem output_isometry (D : Data X n Z s) : (output D)† ∘L output D = 1 :=
  input_isometry D

/-- Exact full-output evolution for arbitrary real time and a zero Hamiltonian. -/
theorem exact_output (D : Data X n Z s) (t : ℝ) (x : X) (hZero : D.matrix x = 0) :
    (program D).eval x ∘L input D = output D ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x)) := by
  rw [hZero, matrixOperator_zero]
  have hz : (-Complex.I * (t : ℂ)) •
      (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) = 0 := by
    ext v i
    simp only [_root_.smul_apply, zero_apply, PiLp.smul_apply, PiLp.zero_apply,
      smul_eq_mul, mul_zero]
  have he : NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)) = 1 := by
    rw [hz]
    exact NormedSpace.exp_zero
  rw [he]
  change 1 ∘L input D = input D ∘L 1
  ext v
  rfl

/-- The full output-isometry error is exactly zero. -/
theorem error_zero (D : Data X n Z s) (t : ℝ) (x : X) (hZero : D.matrix x = 0) :
    ‖(program D).eval x ∘L input D - output D ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 := by
  rw [exact_output D t x hZero, sub_self, norm_zero]

/-- Complete exact native-query certificate for the zero-norm promise. -/
theorem norm_certificate (D : Data X n Z s)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 0) (t : ℝ) :
    (program D).count = 0 ∧ (input D)† ∘L input D = 1 ∧ (output D)† ∘L output D = 1 ∧
      ∀ x, IsUnitary ((program D).eval x) ∧
        ‖(program D).eval x ∘L input D - output D ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 :=
  ⟨count D, input_isometry D, output_isometry D,
    fun x => ⟨unitary D x, error_zero D t x (matrix_zero_of_norm D hNorm x)⟩⟩

/-- Complete exact native-query certificate for the zero row-energy promise. -/
theorem energy_certificate (D : Data X n Z s)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 0) (t : ℝ) :
    (program D).count = 0 ∧ (input D)† ∘L input D = 1 ∧ (output D)† ∘L output D = 1 ∧
      ∀ x, IsUnitary ((program D).eval x) ∧
        ‖(program D).eval x ∘L input D - output D ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 :=
  ⟨count D, input_isometry D, output_isometry D,
    fun x => ⟨unitary D x, error_zero D t x (matrix_zero_of_energy D hRow x)⟩⟩

end
end SparseHamiltonian.NativeZeroSimulation
