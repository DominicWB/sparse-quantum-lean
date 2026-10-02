import SparseHamiltonian.ImprovedZeroSimulation

/-!
# Improved sparse Hamiltonian simulation with one common clean encoding

This endpoint joins the actual original-oracle circuit, positive norm
normalization, signed time, and query-free clean-output alignment. The extra
Boolean register is a spectator of every native query and is zero in the target clean output.
The precision dependence is the explicit three-term manuscript bound.
-/

namespace SparseHamiltonian.ImprovedSparseHamiltonian

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Complete physical space, including the one alignment spectator. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z]
    (s : ℕ) (γ η t ε : ℝ) :=
  CleanOutputAlignment.Double (NativeCayleyActive.Physical n Z
    (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
    (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε))

/-- Each query is an original native primitive with untouched spectators. -/
abbrev oracle (D : Data X n Z s) (γ η t ε : ℝ) :
    Query → X → Physical n Z s γ η t ε →L[ℂ] Physical n Z s γ η t ε :=
  AlignedMultiOracleProgram.oracle (ScaledNativeSimulation.oracle D γ η t ε)

/-- The same known clean preparation occurs at both ends of the circuit. -/
def input (D : Data X n Z s) (γ η t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical n Z s γ η t ε :=
  AlignedMultiOracleProgram.input (ScaledNativeSimulation.signedInput D γ η t ε)

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (γ η t ε : ℝ) (l : Query) (x : X) :
    IsUnitary (oracle D γ η t ε l x) :=
  CoherentQuerySchedule.oracle_unitary (ScaledNativeSimulation.oracle D γ η t ε)
    (ScaledNativeSimulation.oracle_unitary D γ η t ε) l x

/-- The improved primitive sparse-query theorem for every real time. There is
one fixed clean input/output isometry and one actual unitary native program,
uniformly over the unknown matrix instance. The numerical constant is absolute.
No block encoding, controlled oracle, polynomial, phase sequence, moment bound,
Cayley inverse, or active-layer implementation is supplied as an extra hypothesis. -/
theorem simulation (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := Physical n Z s γ η t ε) (oracle D γ η t ε),
        (p.count : ℝ) ≤ 497664 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (2 / ε)) + Real.log (2 / ε)) ∧
        (input D γ η t ε)† ∘L input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ η t ε - input D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hOut, hAction⟩ :=
    ScaledNativeSimulation.exists_native_simulation D η hη hH hrow hcol t ε hε hεOne
  obtain ⟨q, hCountEq, _hCosts, hInput, hAligned⟩ :=
    AlignedMultiOracleProgram.exists_aligned_program
      (P := EuclideanSpace ℂ n)
      (K := NativeCayleyActive.Physical n Z
        (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
        (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε))
      (ScaledNativeSimulation.oracle D γ η t ε)
      (ScaledNativeSimulation.oracle_unitary D γ η t ε)
      (ScaledNativeSimulation.signedInput D γ η t ε)
      (ScaledNativeSimulation.signedOutput D γ η t ε) hIn hOut p
      (fun x => NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x))) ε (fun x => (hAction x).2)
  refine ⟨γ, hγ, hγOne, hWidth, q, ?_, hInput, hAligned⟩
  rw [hCountEq]
  exact hCount

/-- A Hermitian spectral-norm bound alone supplies both energy bounds. -/
theorem simulation_spectral (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ η) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := Physical n Z s γ η t ε) (oracle D γ η t ε),
        (p.count : ℝ) ≤ 497664 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (2 / ε)) + Real.log (2 / ε)) ∧
        (input D γ η t ε)† ∘L input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ η t ε - input D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε :=
  simulation D η t ε hη hε hεOne hH
    (SparseSpectralEnergy.native_energies D η hH hNorm).1
    (SparseSpectralEnergy.native_energies D η hH hNorm).2

/-- The very same circuit and common clean encoding obey their full-output
bound on any finite untouched reference, for arbitrary entangled amplitudes. -/
theorem reference_error {R : Type*} [Fintype R]
    (D : Data X n Z s) (γ η t ε : ℝ)
    (p : MultiOracleCircuit.Program
      (K := Physical n Z s γ η t ε) (oracle D γ η t ε))
    (hError : ∀ x, ‖p.eval x ∘L input D γ η t ε - input D γ η t ε ∘L
      NormedSpace.exp ((-Complex.I * (t : ℂ)) •
        SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε)
    (x : X) (ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)) :
    ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift (input D γ η t ε) ψ) -
      FiniteReferenceLift.lift (input D γ η t ε)
        (FiniteReferenceLift.lift (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix x))) ψ)‖ ≤ ε * ‖ψ‖ :=
  FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D γ η t ε)
    (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))) ε (hError x) ψ

/-- Existence of the same-query simulation with a normalized entangled input
guarantee. The reference dimension does not enter the query bound. -/
theorem simulation_with_reference {R : Type*} [Fintype R]
    (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := Physical n Z s γ η t ε) (oracle D γ η t ε),
        (p.count : ℝ) ≤ 497664 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (2 / ε)) + Real.log (2 / ε)) ∧
        (input D γ η t ε)† ∘L input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
            ‖FiniteReferenceLift.lift (p.eval x)
                (FiniteReferenceLift.lift (input D γ η t ε) ψ) -
              FiniteReferenceLift.lift (input D γ η t ε)
                (FiniteReferenceLift.lift (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                  SparseStateOverlap.matrixOperator (D.matrix x))) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D η t ε hη hε hεOne hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro ψ hψ
  simpa only [hψ, mul_one] using
    reference_error D γ η t ε p (fun x => (hAction x).2) x ψ

end
end SparseHamiltonian.ImprovedSparseHamiltonian
