import ChebyshevLinearSystem.Correctness
import ChebyshevLinearSystem.Cost
import SparseLinearSystems.Endpoint.Main

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Theorem `qls:thm:main` with the positive Chebyshev filter

The data `D : NativeSparseBlockEncoding.Data X n Z s` supply, for every input `x : X`, an
`s`-sparse matrix `A_x = Aop D x` (exact finite-word entries, padded injective in-place row and
column locators with full unitary extensions), and `Ub x` is the state preparation
`U_b |0⟩ = |b⟩` with public reference state `sv = |0⟩`. The promise of equation
`qls:eq:promise` for one input is the released `Endpoint.Promise D κ x`: `‖A‖ ≤ 1`, `A`
invertible and `‖A⁻¹‖ ≤ κ`.

`algorithm D Ub sv κ ε` is one bounded adaptive protocol, built from the public parameters
`s, κ, ε` only, whose circuits call the primitive matrix oracles and the controlled source
preparation (the released `Step.physOracle`). Its filters are the positive Chebyshev filters
of Proposition `qls:prop:chebyshev`, implemented by LCU circuits of signed walk steps (Lemma
`qls:lem:signedwalk`). Theorem `main`:

* every transcript makes at most `4.4·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and
  `1.7·10⁹ √s κ log(1/ε)` calls of the controlled `U_b` or `U_b†`;
* for every input satisfying the promise, every run is unitary, the heralded success
  probability is at least `2/3`, and the conditional output is a density operator within trace
  distance `ε` of `|x⟩⟨x|`, `x = A⁻¹ b / ‖A⁻¹ b‖` (`Endpoint.solutionState`).

`main_exists` states the same with the protocol existentially quantified before all unknown
inputs.
-/

namespace ChebyshevLinearSystem

noncomputable section
open SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk Step Protocol Endpoint

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Theorem `qls:thm:main` with the positive Chebyshev filter.** One public bounded
protocol: worst-case query counts over all transcripts, and for every input satisfying the
promise, unitary runs, success probability at least `2/3` and conditional trace distance at
most `ε` from the normalised solution. -/
theorem main (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
        44 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
        17 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (algorithm D Ub sv κ ε).RunsUnitary x ∧
        2 / 3 ≤ (algorithm D Ub sv κ ε).successMass x ∧
        ODEMixedOutput.IsDensity ((algorithm D Ub sv κ ε).conditionalDensity x) ∧
        ∃ h : ((algorithm D Ub sv κ ε).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((algorithm D Ub sv κ ε).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε := by
  refine ⟨algorithm_matrix_queries D Ub sv κ ε hκ hε hε1,
    algorithm_source_queries D Ub sv κ ε hκ hε hε1, ?_⟩
  intro x hx
  have hU : (algorithm D Ub sv κ ε).RunsUnitary x :=
    Estimator.stages_runsUnitary x _ _ _ _ κ (fun j r => testRun_unitary D Ub hUb sv κ ε j r x)
      _ _
  obtain ⟨hM, hout⟩ := correctness D Ub hUb sv hsv κ ε hκ hε hε1 x hx.norm_le hx.lower
  obtain ⟨hdens, hsym, hdist⟩ := hout _ (hx.apply_inverse (Ub x sv))
  exact ⟨hU, hM, hdens, hsym, hdist⟩

/-- **Theorem `qls:thm:main` with the positive Chebyshev filter, existential form**: one
counter size and one protocol, chosen before every unknown input, satisfy all guarantees. -/
theorem main_exists (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∃ (T : ℕ) (P : Tree (physOracle D Ub T) (PrivO n) V0),
      (P.worstCost wMat : ℝ) ≤ 44 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      (P.worstCost wSrc : ℝ) ≤ 17 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        P.RunsUnitary x ∧ 2 / 3 ≤ P.successMass x ∧
        ODEMixedOutput.IsDensity (P.conditionalDensity x) ∧
        ∃ h : (P.conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance (P.conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  ⟨Tc s κ ε, algorithm D Ub sv κ ε, main D Ub hUb sv hsv κ ε hκ hε hε1⟩

end

end ChebyshevLinearSystem
