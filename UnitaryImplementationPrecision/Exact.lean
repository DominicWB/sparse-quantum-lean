import SparseHamiltonian.UnitaryImplementation
import UnitaryImplementationPrecision.Budget

/-!
# Corollary `hs:cor:unitary` with exact entries, at every precision

The released `UnitaryImplementation.implementation` reaches the constant error `1/4`. Here the
same construction runs with an arbitrary precision `0 < ε ≤ 1/2`, through the formalised
Theorem `hs:thm:main` (`ImprovedSparseHamiltonian.simulation_log_one`), as in the proof of
Corollary `hs:cor:unitary`: the released Hermitian dilation `H_U = [[0, U], [U†, 0]]`
(`UnitaryEntryData.dilationMatrix`, native data `UnitaryEntryData.toNative` with the known
locators, sparsity `s = N = card n` and row and column norms `η = 1`) is simulated for
`t = π/2`. As `H_U² = 1` (`UnitaryEntryData.dilation_sq`), `e^{-i(π/2)H_U} = -i H_U`, and
`H_U` maps the `true` sector to the `false` sector by `U`
(`UnitaryEntryData.dilation_includeOne`); the released
`UnitaryDilationTransfer.exists_clean_unitary_program` adds the known flag flip and phase
correction as one fixed gate, and `UnitaryEntryOracle.compile` replaces the known locators by
fixed gates and each value query by one ordinary entry query between fixed routing gates.

* `native_implementation`: over the native labels, at most
  `497664 π (√N + √(N ℓ) + ℓ)` queries, `ℓ = log(1/ε)`, operator-norm error at most `ε`.
* `implementation`: the same with entry-oracle queries only (inverse calls counted).
* `reference_error`, `implementation_with_reference`: arbitrary inputs entangled with an
  untouched finite reference.
* `implementation_two_term`: the count `497664 π (1 + (log 2)^{-1/2}) (√(N ℓ) + ℓ)`, after
  absorbing `√N` into `√(N ℓ)` (`sqrt_le_absorb`).
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

namespace SparseHamiltonian.UnitaryPrecision

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The simulator workspace at `η = 1`, `t = π/2` and precision `ε`, with the final alignment
spectator: the released `UnitaryEntryOracle.Physical`. -/
abbrev Physical (n Z : Type*) [Fintype n] [Fintype Z] (γ ε : ℝ) :=
  UnitaryEntryOracle.Physical n Z γ 1 (Real.pi / 2) ε

/-- The only unknown primitive: one ordinary entry-oracle call of the released model
(`UnitaryEntryOracle.oracle`), with spectators (`UnitaryEntryOracle.flatEntry_eq_original`). -/
abbrev oracle (D : UnitaryEntryData.Data X n Z) (γ ε : ℝ) :=
  UnitaryEntryOracle.oracle D γ 1 (Real.pi / 2) ε

set_option maxHeartbeats 3000000 in
/-- The common clean encoding of input and output: the input `|1⟩ ⊗ ψ` of the dilation
(`UnitaryEntryData.includeOne`) in the clean simulator input, with the alignment spectator. -/
def input (D : UnitaryEntryData.Data X n Z) (γ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] Physical n Z γ ε :=
  AlignedMultiOracleProgram.input
    (ImprovedSparseHamiltonian.input (UnitaryEntryData.toNative D) γ 1 (Real.pi / 2) ε ∘L
      UnitaryEntryData.includeOne)

/-- Corollary `hs:cor:unitary` with exact entries, before the known locators are compiled away:
the released dilation simulated by Theorem `hs:thm:main` at `t = π/2`, then the flag flip and
the phase correction. -/
theorem native_implementation (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : MultiOracleCircuit.Program (UnitaryEntryOracle.nativeOracle D γ 1 (Real.pi / 2) ε),
        (p.count : ℝ) ≤ 497664 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
            SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, _hWidth, p, hCount, hInput, hAction⟩ :=
    ImprovedSparseHamiltonian.simulation_log_one (UnitaryEntryData.toNative D)
      1 (Real.pi / 2) ε one_pos hε hεHalf
      (UnitaryEntryData.dilation_hermitian D)
      (UnitaryEntryData.dilation_row_energy D)
      (UnitaryEntryData.dilation_column_energy D)
  obtain ⟨q, hCountEq, _hCosts, hClean, hResult⟩ :=
    UnitaryDilationTransfer.exists_clean_unitary_program
      (ImprovedSparseHamiltonian.oracle (UnitaryEntryData.toNative D) γ 1 (Real.pi / 2) ε)
      (ImprovedSparseHamiltonian.oracle_unitary (UnitaryEntryData.toNative D)
        γ 1 (Real.pi / 2) ε)
      (ImprovedSparseHamiltonian.input (UnitaryEntryData.toNative D) γ 1 (Real.pi / 2) ε)
      UnitaryEntryData.includeOne UnitaryEntryData.includeZero
      hInput UnitaryEntryData.includeOne_isometry UnitaryEntryData.includeZero_isometry
      (fun x => SparseStateOverlap.matrixOperator (UnitaryEntryData.dilationMatrix D x))
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (UnitaryEntryData.dilation_sq D) (UnitaryEntryData.dilation_includeOne D)
      p ε (fun x => (hAction x).2)
  refine ⟨γ, hγ, hγOne, q, ?_, hClean, hResult⟩
  rw [hCountEq]
  exact hCount.trans (exact_shape_le _ _ (log_one_nonneg ε hε hεHalf))

/-- Corollary `hs:cor:unitary` with exact entries, for every `0 < ε ≤ 1/2`: one clean unitary
circuit, uniform over the instances `x`, with full-output operator-norm error at most `ε`, using
at most `497664 π (√N + √(N ℓ) + ℓ)` ordinary entry-oracle queries, `N = card n`,
`ℓ = log(1/ε)`, inverse calls counted. The known locators are fixed gates: no location oracle
is used. -/
theorem implementation (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (oracle D γ ε),
        (p.count : ℝ) ≤ 497664 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
            SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
    native_implementation D ε hε hεHalf
  refine ⟨γ, hγ, hγOne, UnitaryEntryOracle.compile D γ 1 (Real.pi / 2) ε p, ?_, hInput, ?_⟩
  · have hCompile :
        ((UnitaryEntryOracle.compile D γ 1 (Real.pi / 2) ε p).count : ℝ) ≤ (p.count : ℝ) := by
      exact_mod_cast UnitaryEntryOracle.compile_count_le D γ 1 (Real.pi / 2) ε p
    exact hCompile.trans hCount
  · intro x
    simpa only [UnitaryEntryOracle.compile_eval] using hAction x

set_option maxHeartbeats 3000000 in
/-- Corollary `hs:cor:unitary` on inputs entangled with an untouched finite reference: any such
circuit keeps its error bound, times `‖ψ‖`. -/
theorem reference_error {R : Type*} [Fintype R]
    (D : UnitaryEntryData.Data X n Z) (γ ε : ℝ)
    (p : OracleCircuit.Program (oracle D γ ε))
    (hError : ∀ x, ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
      SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε)
    (x : X) (ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)) :
    ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift (input D γ ε) ψ) -
      FiniteReferenceLift.lift (input D γ ε)
        (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (D.matrix x)) ψ)‖ ≤
          ε * ‖ψ‖ :=
  FiniteReferenceLift.same_embedding_error_le (p.eval x) (input D γ ε)
    (SparseStateOverlap.matrixOperator (D.matrix x)) ε (hError x) ψ

/-- Corollary `hs:cor:unitary` with exact entries, on normalised inputs entangled with an
untouched finite reference `R`; the reference does not enter the query bound. -/
theorem implementation_with_reference {R : Type*} [Fintype R]
    (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (oracle D γ ε),
        (p.count : ℝ) ≤ 497664 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
            ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift (input D γ ε) ψ) -
              FiniteReferenceLift.lift (input D γ ε)
                (FiniteReferenceLift.lift
                  (SparseStateOverlap.matrixOperator (D.matrix x)) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ := implementation D ε hε hεHalf
  refine ⟨γ, hγ, hγOne, p, hCount, hInput, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro ψ hψ
  simpa only [hψ, mul_one] using
    reference_error D γ ε p (fun x => (hAction x).2) x ψ

/-- Corollary `hs:cor:unitary` with exact entries and the two-term count
`497664 π (1 + (log 2)^{-1/2}) (√(N ℓ) + ℓ)`: the first term `√N` is absorbed into `√(N ℓ)`
since `ℓ ≥ log 2` (`sqrt_le_absorb`). -/
theorem implementation_two_term (D : UnitaryEntryData.Data X n Z) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (oracle D γ ε),
        (p.count : ℝ) ≤ 497664 * Real.pi * (1 + (Real.sqrt (Real.log 2))⁻¹) *
          (Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ ε)† ∘L input D γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ ε - input D γ ε ∘L
            SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ := implementation D ε hε hεHalf
  refine ⟨γ, hγ, hγOne, p, ?_, hInput, hAction⟩
  exact hCount.trans (three_term_le_two_term _ _ ε (by positivity) (Nat.cast_nonneg _)
    hε hεHalf)

end
end SparseHamiltonian.UnitaryPrecision
