import ChebyshevLinearSystemFinite.Correctness
import ChebyshevLinearSystemFinite.Cost
import ChebyshevLinearSystem.Main

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

/-!
# Theorem `qls:thm:main` with approximate known gates

The access model, the promise and the oracle family are those of the released theorems
(`SparseLinearSystems.Endpoint.main`, `ChebyshevLinearSystem.main`): native sparse primitives
and the controlled source preparation (`Step.physOracle`), every call counted (`Step.wMat`,
`Step.wSrc`), the promise `Endpoint.Promise D κ x`.

The protocol is the Chebyshev protocol with the finite degrees `d + 1` of equation
`qls:eq:finitedegree` (`testRunF`, `finalRunF`), and its known gates may be implemented
approximately. An implementation is given by arbitrary public runs `test j r` (tests) and
`fin r` (final attempts) over the same oracle family; the classical control is unchanged
(`implAlgorithm`). The accuracy requirement is the manuscript's (`AmpApprox`): each implemented
run has the weighted costs of the ideal run, and on every input satisfying the promise it
changes the unnormalised success vector by at most

* `e_test(s, j) = (10⁻⁴ - δ₀(σ_j)²)/2` for a test at stage `j`
  (`≥ 1/(825000 √s 2^j)`, `eTest_ge_sharp`);
* `e_fin(s, κ, ε) = ε/1000 - δ₀` for a final attempt (`≥ ε/(41250 √s κ)`, `eFin_ge_sharp`),

with `δ₀ = sech(2 d^fin artanh b)` the residual amplitude at the finite degree. `RunApprox`
splits the allowance into the errors of the approximate known gates (each known gate replaced
by any finite circuit of known gates, `GateApprox`), the seed and the flag; this bounds the
change of the success vector (`RunApprox.ampApprox`).

* `main_amp`: for every such implementation, every transcript makes at most
  `2.7·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and `10⁹ √s κ log(1/ε)` source calls, and for
  every input satisfying the promise every run is unitary, the success probability is at least
  `2/3` and the conditional output is within trace distance `ε` of the normalised solution.
* `main`: the same for every implementation within `e_test` and `e_fin` in the sense of
  `RunApprox` (the special case of `main_amp`).
* `main_uniform`: the same under the uniform explicit requirements `1/(3.6·10⁷ s κ²)` for
  every test and `ε/(9·10⁵ s κ²)` for every final attempt; `main_uniform_sharp`: under the
  sharper uniform requirements `1/(1.65·10⁶ √s κ)` and `ε/(41250 √s κ)`.
* `main_exact`: the finite-degree protocol with exact gates (`algorithmF`).
* `main_improved`, `main_improved_exists`: the released exact-gate Chebyshev algorithm
  (`ChebyshevLinearSystem.algorithm`) with the improved constants `2.7·10¹⁰` and `10⁹`
  (released: `4.4·10¹⁰` and `1.7·10⁹`).
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk Step Protocol Endpoint
  ChebyshevLinearSystem

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Theorem `qls:thm:main` with approximate known gates, the manuscript's hypothesis**
(equations `qls:eq:finitedegree`, `qls:eq:bernoulli`). For every implementation of the
finite-degree Chebyshev protocol whose runs have the weighted costs of the ideal runs and, on
every input satisfying the promise, change the unnormalised success vector by at most
`e_test = (10⁻⁴ - δ₀²)/2` (tests) and `e_fin = ε/1000 - δ₀` (final attempts) (`AmpApprox`):
worst-case query counts over all transcripts, and for every input satisfying the promise,
unitary runs, success probability at least `2/3` and conditional trace distance at most `ε`
from the normalised solution. -/
theorem main_amp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, AmpApprox (Promise D κ) (testRunF D Ub sv κ ε j r) (test j r)
      (eTest s (stageOf κ j)))
    (hfin : ∀ r, AmpApprox (Promise D κ) (finalRunF D Ub sv κ ε r) (fin r) (eFin s κ ε)) :
    ((implAlgorithm κ ε test fin).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((implAlgorithm κ ε test fin).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (implAlgorithm κ ε test fin).RunsUnitary x ∧
        2 / 3 ≤ (implAlgorithm κ ε test fin).successMass x ∧
        ODEMixedOutput.IsDensity ((implAlgorithm κ ε test fin).conditionalDensity x) ∧
        ∃ h : ((implAlgorithm κ ε test fin).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((implAlgorithm κ ε test fin).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε := by
  refine ⟨impl_matrix_queries D Ub sv κ ε hκ hε hε1 test fin
      (fun j r => (htest j r).cost_eq wMat) (fun r => (hfin r).cost_eq wMat),
    impl_source_queries D Ub sv κ ε hκ hε hε1 test fin
      (fun j r => (htest j r).cost_eq wSrc) (fun r => (hfin r).cost_eq wSrc), ?_⟩
  intro x hx
  obtain ⟨hU, hM, hout⟩ := impl_correctness D Ub hUb sv hsv κ ε hκ hε hε1 test fin x
    hx.norm_le hx.lower (fun j r => (htest j r).amp_sub_le hx) (fun r => (hfin r).amp_sub_le hx)
  obtain ⟨hdens, hsym, hdist⟩ := hout _ (hx.apply_inverse (Ub x sv))
  exact ⟨hU, hM, hdens, hsym, hdist⟩

/-- **Theorem `qls:thm:main` with approximate known gates** (equations
`qls:eq:finitedegree`, `qls:eq:bernoulli`). For every implementation of the finite-degree
Chebyshev protocol whose tests are within `e_test = (10⁻⁴ - δ₀²)/2` and whose final attempts
are within `e_fin = ε/1000 - δ₀` of the ideal runs (`RunApprox`: the same oracle calls, and the
errors of the approximate known gates, the seed and the flag add up to at most the allowance,
so the success vector changes by at most it): worst-case query counts over all transcripts,
and for every input satisfying the promise, unitary runs, success probability at least `2/3`
and conditional trace distance at most `ε` from the normalised solution. The special case of
`main_amp` given by `RunApprox.ampApprox`. -/
theorem main (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, RunApprox (testRunF D Ub sv κ ε j r) (test j r) (eTest s (stageOf κ j)))
    (hfin : ∀ r, RunApprox (finalRunF D Ub sv κ ε r) (fin r) (eFin s κ ε)) :
    ((implAlgorithm κ ε test fin).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((implAlgorithm κ ε test fin).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (implAlgorithm κ ε test fin).RunsUnitary x ∧
        2 / 3 ≤ (implAlgorithm κ ε test fin).successMass x ∧
        ODEMixedOutput.IsDensity ((implAlgorithm κ ε test fin).conditionalDensity x) ∧
        ∃ h : ((implAlgorithm κ ε test fin).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((implAlgorithm κ ε test fin).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  main_amp D Ub hUb sv hsv κ ε hκ hε hε1 test fin
    (fun j r => (htest j r).ampApprox (physOracle_unitary D Ub hUb _) _)
    (fun r => (hfin r).ampApprox (physOracle_unitary D Ub hUb _) _)

/-- **Theorem `qls:thm:main` with approximate known gates, uniform explicit requirements**:
the conclusions of `main` for every implementation whose tests are within
`1/(3.6·10⁷ s κ²)` and whose final attempts are within `ε/(9·10⁵ s κ²)` of the ideal runs
(`RunApprox`). -/
theorem main_uniform (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, RunApprox (testRunF D Ub sv κ ε j r) (test j r)
      (1 / (36 * 10 ^ 6 * (s : ℝ) * κ ^ 2)))
    (hfin : ∀ r, RunApprox (finalRunF D Ub sv κ ε r) (fin r)
      (ε / (9 * 10 ^ 5 * (s : ℝ) * κ ^ 2))) :
    ((implAlgorithm κ ε test fin).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((implAlgorithm κ ε test fin).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (implAlgorithm κ ε test fin).RunsUnitary x ∧
        2 / 3 ≤ (implAlgorithm κ ε test fin).successMass x ∧
        ODEMixedOutput.IsDensity ((implAlgorithm κ ε test fin).conditionalDensity x) ∧
        ∃ h : ((implAlgorithm κ ε test fin).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((implAlgorithm κ ε test fin).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  main D Ub hUb sv hsv κ ε hκ hε hε1 test fin
    (fun j r => (htest j r).mono (eTest_ge_uniform s D.slots_pos κ hκ j))
    (fun r => (hfin r).mono (eFin_ge s D.slots_pos κ ε hκ hε hε1))

/-- **Theorem `qls:thm:main` with approximate known gates, sharper uniform requirements**: the
conclusions of `main` for every implementation whose tests are within `1/(1.65·10⁶ √s κ)` and
whose final attempts are within `ε/(41250 √s κ)` of the ideal runs (`RunApprox`;
`eTest_ge_uniform_sharp`, `eFin_ge_sharp`). -/
theorem main_uniform_sharp (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, RunApprox (testRunF D Ub sv κ ε j r) (test j r)
      (1 / (165 * 10 ^ 4 * Real.sqrt s * κ)))
    (hfin : ∀ r, RunApprox (finalRunF D Ub sv κ ε r) (fin r)
      (ε / (41250 * Real.sqrt s * κ))) :
    ((implAlgorithm κ ε test fin).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((implAlgorithm κ ε test fin).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (implAlgorithm κ ε test fin).RunsUnitary x ∧
        2 / 3 ≤ (implAlgorithm κ ε test fin).successMass x ∧
        ODEMixedOutput.IsDensity ((implAlgorithm κ ε test fin).conditionalDensity x) ∧
        ∃ h : ((implAlgorithm κ ε test fin).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((implAlgorithm κ ε test fin).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  main D Ub hUb sv hsv κ ε hκ hε hε1 test fin
    (fun j r => (htest j r).mono (eTest_ge_uniform_sharp s D.slots_pos κ hκ j))
    (fun r => (hfin r).mono (eFin_ge_sharp s D.slots_pos κ ε hκ hε hε1))

/-- **Theorem `qls:thm:main` with the finite degrees and exact gates** (the corollary of `main`
for the ideal implementation). -/
theorem main_exact (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithmF D Ub sv κ ε).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((algorithmF D Ub sv κ ε).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (algorithmF D Ub sv κ ε).RunsUnitary x ∧
        2 / 3 ≤ (algorithmF D Ub sv κ ε).successMass x ∧
        ODEMixedOutput.IsDensity ((algorithmF D Ub sv κ ε).conditionalDensity x) ∧
        ∃ h : ((algorithmF D Ub sv κ ε).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((algorithmF D Ub sv κ ε).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  main D Ub hUb sv hsv κ ε hκ hε hε1 _ _
    (fun _ _ => (RunApprox.refl _).mono (eTest_pos s _ D.slots_pos).le)
    (fun _ => (RunApprox.refl _).mono (eFin_pos s D.slots_pos κ ε hκ hε hε1).le)

/-- **Theorem `qls:thm:main` with the positive Chebyshev filter, improved constants**: the
released exact-gate algorithm `ChebyshevLinearSystem.algorithm` makes at most
`2.7·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and `10⁹ √s κ log(1/ε)` source calls (released:
`4.4·10¹⁰`, `1.7·10⁹`), with the guarantees of `ChebyshevLinearSystem.main`. -/
theorem main_improved (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
        27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
        10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (ChebyshevLinearSystem.algorithm D Ub sv κ ε).RunsUnitary x ∧
        2 / 3 ≤ (ChebyshevLinearSystem.algorithm D Ub sv κ ε).successMass x ∧
        ODEMixedOutput.IsDensity
          ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).conditionalDensity x) ∧
        ∃ h : ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance
            ((ChebyshevLinearSystem.algorithm D Ub sv κ ε).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  ⟨algorithm_matrix_queries_sharp D Ub sv κ ε hκ hε hε1,
    algorithm_source_queries_sharp D Ub sv κ ε hκ hε hε1,
    (ChebyshevLinearSystem.main D Ub hUb sv hsv κ ε hκ hε hε1).2.2⟩

/-- **Existential form with the improved constants**: one counter size and one protocol,
chosen before every unknown input, with at most `2.7·10¹⁰ √s κ log(1/ε)` matrix-oracle and
`10⁹ √s κ log(1/ε)` source calls and the guarantees of Theorem `qls:thm:main`. -/
theorem main_improved_exists (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∃ (T : ℕ) (P : Tree (physOracle D Ub T) (PrivO n) V0),
      (P.worstCost wMat : ℝ) ≤ 27 * 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      (P.worstCost wSrc : ℝ) ≤ 10 ^ 9 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        P.RunsUnitary x ∧ 2 / 3 ≤ P.successMass x ∧
        ODEMixedOutput.IsDensity (P.conditionalDensity x) ∧
        ∃ h : (P.conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance (P.conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  ⟨Tc s κ ε, ChebyshevLinearSystem.algorithm D Ub sv κ ε,
    main_improved D Ub hUb sv hsv κ ε hκ hε hε1⟩

end

end ChebyshevLinearSystemFinite
