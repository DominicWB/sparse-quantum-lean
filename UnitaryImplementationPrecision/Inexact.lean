import UnitaryImplementationPrecision.TableOracle
import UnitaryImplementationPrecision.Exact

/-!
# Corollary `hs:cor:unitary` with inexact entries

The entry oracle is an inexact table `T : Table X n Z` (the released entry model without the
unitarity promise), whose represented matrix `Ũ = T.matrix x` is within `ξ = ε/(π N)` of the
intended unitary `U x` in every entry, `N = card n`. As in the proof of Corollary
`hs:cor:unitary`:

* the represented dilation `H̃_U = [[0, Ũ], [Ũ†, 0]]` (`Table.dilationMatrix`) is Hermitian,
  `N`-sparse with the known locators, and has row and column norms at most `η = 2`
  (`Table.dilation_row_energy_two`, from `N ξ² ≤ 1`);
* Theorem `hs:thm:main` (`ImprovedSparseHamiltonian.simulation_log_one`) simulates it for
  `t = π/2` to error `ε/2`;
* Duhamel's bound (`HamiltonianStability.output_error_le`) with
  `‖H̃_U - H_U‖ ≤ N ξ = ε/π` (`Table.dilation_sub_norm_le`) gives error
  `ε/2 + (π/2) N ξ = ε` for the true dilation `H_U` (`duhamel_step`);
* the released transfer (`UnitaryDilationTransfer.exists_clean_unitary_program`) with the true
  involution `H_U` (released lemmas through `exactData`) adds the flag flip and the phase
  correction, and `Table.compile` leaves only table queries.

Endpoints: `native_implementation_inexact`, `implementation_inexact` (at most
`995328 π (√N + √(N ℓ) + ℓ)` table queries, `ℓ = log(1/ε)`, error at most `ε` against the
intended `U`), `reference_error_inexact`, `implementation_inexact_with_reference` and
`implementation_inexact_two_term`.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

namespace SparseHamiltonian.UnitaryPrecision

noncomputable section
open ContinuousLinearMap OracleCircuit
open UnitaryEntryData (Index)
open scoped BigOperators InnerProduct

section Duhamel
variable {X n Z : Type*} [Fintype n]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Duhamel step of Corollary `hs:cor:unitary`: with entries within `ε/(π N)` of `U`, any
circuit that simulates the represented dilation `H̃_U` for `t = π/2` to error `ε/2`, in a fixed
isometric encoding `E`, simulates the true dilation `H_U` to error `ε`. -/
theorem duhamel_step [Nonempty n] (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n))
    (S : X → EuclideanSpace ℂ (Index n) →L[ℂ] K) (E : EuclideanSpace ℂ (Index n) →L[ℂ] K)
    (hE : E† ∘L E = 1)
    (hSim : ∀ x, ‖S x - E ∘L NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator (Table.dilationMatrix T x))‖ ≤ ε / 2) (x : X) :
    ‖S x - E ∘L NormedSpace.exp ((-Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) •
      SparseStateOverlap.matrixOperator
        (UnitaryEntryData.dilationMatrix (exactData U hU) x))‖ ≤ ε := by
  have hN : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hξ : 0 ≤ ε / (Real.pi * Fintype.card n) := by
    have := Real.pi_pos
    positivity
  have h := HamiltonianStability.output_error_le (S x) E
    (SparseStateOverlap.matrixOperator (UnitaryEntryData.dilationMatrix (exactData U hU) x))
    (SparseStateOverlap.matrixOperator (Table.dilationMatrix T x)) (Real.pi / 2) (ε / 2)
    ((Fintype.card n : ℝ) * (ε / (Real.pi * Fintype.card n)))
    (LabeledSimulationTransfer.isometry_norm_le_one E hE)
    (SparseValuePrecision.matrixOperator_star_eq _
      (UnitaryEntryData.dilation_hermitian (exactData U hU) x))
    (SparseValuePrecision.matrixOperator_star_eq _ (Table.dilation_hermitian T x))
    (hSim x) (Table.dilation_sub_norm_le T U hU _ hξ hEntry x)
  rw [duhamel_term_eq_half _ ε hN] at h
  linarith

end Duhamel

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- The simulator workspace of the inexact case, at `η = 2`, `t = π/2` and precision `ε/2`,
with the final alignment spectator. -/
abbrev InexactPhysical (n Z : Type*) [Fintype n] [Fintype Z] (γ ε : ℝ) :=
  UnitaryEntryOracle.Physical n Z γ 2 (Real.pi / 2) (ε / 2)

/-- The only unknown primitive: one ordinary call of the inexact table, with spectators
(`Table.flatEntry_eq_original`). -/
abbrev inexactOracle (T : Table X n Z) (γ ε : ℝ) :=
  Table.oracle T γ 2 (Real.pi / 2) (ε / 2)

set_option maxHeartbeats 3000000 in
/-- The common clean encoding of input and output in the inexact case. -/
def inexactInput (T : Table X n Z) (γ ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] InexactPhysical n Z γ ε :=
  AlignedMultiOracleProgram.input
    (ImprovedSparseHamiltonian.input (Table.toNative T) γ 2 (Real.pi / 2) (ε / 2) ∘L
      UnitaryEntryData.includeOne)

/-- Corollary `hs:cor:unitary` with inexact entries, before the known locators are compiled
away. -/
theorem native_implementation_inexact (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : MultiOracleCircuit.Program (Table.nativeOracle T γ 2 (Real.pi / 2) (ε / 2)),
        (p.count : ℝ) ≤ 995328 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (inexactInput T γ ε)† ∘L inexactInput T γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L inexactInput T γ ε - inexactInput T γ ε ∘L
            SparseStateOverlap.matrixOperator (U x)‖ ≤ ε := by
  have hN : (1 : ℝ) ≤ Fintype.card n := by exact_mod_cast Fintype.card_pos
  have hξ := card_mul_sq_le_one (Fintype.card n : ℝ) ε hN hε hεHalf
  obtain ⟨γ, hγ, hγOne, _hWidth, p, hCount, hInput, hAction⟩ :=
    ImprovedSparseHamiltonian.simulation_log_one (Table.toNative T) 2 (Real.pi / 2) (ε / 2)
      two_pos (half_pos hε) (by linarith) (Table.dilation_hermitian T)
      (Table.dilation_row_energy_two T U hU _ hEntry hξ)
      (Table.dilation_column_energy_two T U hU _ hEntry hξ)
  obtain ⟨q, hCountEq, _hCosts, hClean, hResult⟩ :=
    UnitaryDilationTransfer.exists_clean_unitary_program
      (ImprovedSparseHamiltonian.oracle (Table.toNative T) γ 2 (Real.pi / 2) (ε / 2))
      (ImprovedSparseHamiltonian.oracle_unitary (Table.toNative T) γ 2 (Real.pi / 2) (ε / 2))
      (ImprovedSparseHamiltonian.input (Table.toNative T) γ 2 (Real.pi / 2) (ε / 2))
      UnitaryEntryData.includeOne UnitaryEntryData.includeZero
      hInput UnitaryEntryData.includeOne_isometry UnitaryEntryData.includeZero_isometry
      (fun x => SparseStateOverlap.matrixOperator
        (UnitaryEntryData.dilationMatrix (exactData U hU) x))
      (fun x => SparseStateOverlap.matrixOperator (U x))
      (UnitaryEntryData.dilation_sq (exactData U hU))
      (UnitaryEntryData.dilation_includeOne (exactData U hU))
      p ε
      (duhamel_step T U hU ε hε hEntry
        (fun x => p.eval x ∘L
          ImprovedSparseHamiltonian.input (Table.toNative T) γ 2 (Real.pi / 2) (ε / 2))
        (ImprovedSparseHamiltonian.input (Table.toNative T) γ 2 (Real.pi / 2) (ε / 2))
        hInput (fun x => (hAction x).2))
  refine ⟨γ, hγ, hγOne, q, ?_, hClean, hResult⟩
  rw [hCountEq]
  exact hCount.trans (inexact_shape_le _ ε (Nat.cast_nonneg _) hε hεHalf)

/-- Corollary `hs:cor:unitary` with inexact entries: if every represented entry is within
`ε/(π N)` of the intended unitary `U`, one clean unitary circuit, uniform over the instances,
has full-output operator-norm error at most `ε` against `U`, using at most
`995328 π (√N + √(N ℓ) + ℓ)` ordinary table queries, `ℓ = log(1/ε)`, inverse calls counted, and
no location oracle. -/
theorem implementation_inexact (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (inexactOracle T γ ε),
        (p.count : ℝ) ≤ 995328 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (inexactInput T γ ε)† ∘L inexactInput T γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L inexactInput T γ ε - inexactInput T γ ε ∘L
            SparseStateOverlap.matrixOperator (U x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
    native_implementation_inexact T U hU ε hε hεHalf hEntry
  refine ⟨γ, hγ, hγOne, Table.compile T γ 2 (Real.pi / 2) (ε / 2) p, ?_, hInput, ?_⟩
  · have hCompile :
        ((Table.compile T γ 2 (Real.pi / 2) (ε / 2) p).count : ℝ) ≤ (p.count : ℝ) := by
      exact_mod_cast Table.compile_count_le T γ 2 (Real.pi / 2) (ε / 2) p
    exact hCompile.trans hCount
  · intro x
    simpa only [Table.compile_eval] using hAction x

set_option maxHeartbeats 3000000 in
/-- Corollary `hs:cor:unitary` with inexact entries, on inputs entangled with an untouched finite
reference: any such circuit keeps its error bound, times `‖ψ‖`. -/
theorem reference_error_inexact {R : Type*} [Fintype R]
    (T : Table X n Z) (U : X → Matrix n n ℂ) (γ ε : ℝ)
    (p : OracleCircuit.Program (inexactOracle T γ ε))
    (hError : ∀ x, ‖p.eval x ∘L inexactInput T γ ε - inexactInput T γ ε ∘L
      SparseStateOverlap.matrixOperator (U x)‖ ≤ ε)
    (x : X) (ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)) :
    ‖FiniteReferenceLift.lift (p.eval x)
        (FiniteReferenceLift.lift (inexactInput T γ ε) ψ) -
      FiniteReferenceLift.lift (inexactInput T γ ε)
        (FiniteReferenceLift.lift (SparseStateOverlap.matrixOperator (U x)) ψ)‖ ≤
          ε * ‖ψ‖ :=
  FiniteReferenceLift.same_embedding_error_le (p.eval x) (inexactInput T γ ε)
    (SparseStateOverlap.matrixOperator (U x)) ε (hError x) ψ

/-- Corollary `hs:cor:unitary` with inexact entries, on normalised inputs entangled with an
untouched finite reference `R`. -/
theorem implementation_inexact_with_reference {R : Type*} [Fintype R]
    (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (inexactOracle T γ ε),
        (p.count : ℝ) ≤ 995328 * Real.pi *
          (Real.sqrt (Fintype.card n : ℝ) +
            Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (inexactInput T γ ε)† ∘L inexactInput T γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
            ‖FiniteReferenceLift.lift (p.eval x)
                (FiniteReferenceLift.lift (inexactInput T γ ε) ψ) -
              FiniteReferenceLift.lift (inexactInput T γ ε)
                (FiniteReferenceLift.lift
                  (SparseStateOverlap.matrixOperator (U x)) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
    implementation_inexact T U hU ε hε hεHalf hEntry
  refine ⟨γ, hγ, hγOne, p, hCount, hInput, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro ψ hψ
  simpa only [hψ, mul_one] using
    reference_error_inexact T U γ ε p (fun x => (hAction x).2) x ψ

/-- Corollary `hs:cor:unitary` with inexact entries and the two-term count
`995328 π (1 + (log 2)^{-1/2}) (√(N ℓ) + ℓ)`. -/
theorem implementation_inexact_two_term (T : Table X n Z) (U : X → Matrix n n ℂ)
    (hU : ∀ x, IsUnitary (SparseStateOverlap.matrixOperator (U x))) (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2)
    (hEntry : ∀ x i j, ‖T.matrix x i j - U x i j‖ ≤ ε / (Real.pi * Fintype.card n)) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ p : OracleCircuit.Program (inexactOracle T γ ε),
        (p.count : ℝ) ≤ 995328 * Real.pi * (1 + (Real.sqrt (Real.log 2))⁻¹) *
          (Real.sqrt ((Fintype.card n : ℝ) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (inexactInput T γ ε)† ∘L inexactInput T γ ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L inexactInput T γ ε - inexactInput T γ ε ∘L
            SparseStateOverlap.matrixOperator (U x)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, p, hCount, hInput, hAction⟩ :=
    implementation_inexact T U hU ε hε hεHalf hEntry
  refine ⟨γ, hγ, hγOne, p, ?_, hInput, hAction⟩
  exact hCount.trans (three_term_le_two_term _ _ ε (by positivity) (Nat.cast_nonneg _)
    hε hεHalf)

end
end SparseHamiltonian.UnitaryPrecision
