import SparseHamiltonian.FiniteReferenceLift

/-!
# Exact degenerate branches of the improved simulation theorem

The zero-time and zero-energy cases use an actual identity program over the
original sparse primitive family with fixed spectator registers. They have
zero queries and exactly one common clean input/output encoding.
-/

namespace SparseHamiltonian.ImprovedZeroSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Zero time is exact for every matrix, without a norm or Hermitian promise. -/
theorem zero_time_exact (D : Data X n Z s) (x : X) :
    (NativeZeroSimulation.program D).eval x ∘L NativeZeroSimulation.input D =
      NativeZeroSimulation.input D ∘L
        NormedSpace.exp ((-Complex.I * (0 : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x)) := by
  have hz : (0 : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x) = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply PiLp.ext
    intro i
    simp only [_root_.smul_apply, PiLp.smul_apply, smul_eq_mul, zero_mul,
      zero_apply, PiLp.zero_apply]
  rw [mul_zero, hz, NormedSpace.exp_zero]
  change 1 ∘L NativeZeroSimulation.input D = NativeZeroSimulation.input D ∘L 1
  apply ContinuousLinearMap.ext
  intro v
  rfl

/-- A literal zero-query circuit implements zero time with exact clean output. -/
theorem zero_time_certificate (D : Data X n Z s) :
    (NativeZeroSimulation.program D).count = 0 ∧
      (NativeZeroSimulation.input D)† ∘L NativeZeroSimulation.input D = 1 ∧
      ∀ x, IsUnitary ((NativeZeroSimulation.program D).eval x) ∧
        ‖(NativeZeroSimulation.program D).eval x ∘L NativeZeroSimulation.input D -
          NativeZeroSimulation.input D ∘L
            NormedSpace.exp ((-Complex.I * (0 : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 := by
  refine ⟨NativeZeroSimulation.count D, NativeZeroSimulation.input_isometry D,
    fun x => ⟨NativeZeroSimulation.unitary D x, ?_⟩⟩
  rw [zero_time_exact, sub_self, norm_zero]

/-- Zero row energy makes the matrix vanish, so the identity works at any time.
This is the same clean embedding at both ends, with no positive normalization. -/
theorem zero_energy_certificate (D : Data X n Z s)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 0) (t : ℝ) :
    (NativeZeroSimulation.program D).count = 0 ∧
      (NativeZeroSimulation.input D)† ∘L NativeZeroSimulation.input D = 1 ∧
      ∀ x, IsUnitary ((NativeZeroSimulation.program D).eval x) ∧
        ‖(NativeZeroSimulation.program D).eval x ∘L NativeZeroSimulation.input D -
          NativeZeroSimulation.input D ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 := by
  refine ⟨NativeZeroSimulation.count D, NativeZeroSimulation.input_isometry D,
    fun x => ⟨NativeZeroSimulation.unitary D x, ?_⟩⟩
  exact NativeZeroSimulation.error_zero D t x
    (NativeZeroSimulation.matrix_zero_of_energy D hRow x)

/-- The degenerate spectral-bound promise has the same exact identity branch. -/
theorem zero_spectral_certificate (D : Data X n Z s)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 0) (t : ℝ) :
    (NativeZeroSimulation.program D).count = 0 ∧
      (NativeZeroSimulation.input D)† ∘L NativeZeroSimulation.input D = 1 ∧
      ∀ x, IsUnitary ((NativeZeroSimulation.program D).eval x) ∧
        ‖(NativeZeroSimulation.program D).eval x ∘L NativeZeroSimulation.input D -
          NativeZeroSimulation.input D ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ = 0 := by
  refine ⟨NativeZeroSimulation.count D, NativeZeroSimulation.input_isometry D,
    fun x => ⟨NativeZeroSimulation.unitary D x, ?_⟩⟩
  exact NativeZeroSimulation.error_zero D t x
    (NativeZeroSimulation.matrix_zero_of_norm D hNorm x)

end
end SparseHamiltonian.ImprovedZeroSimulation
