import QLSHoeffding.Cost
import ChebyshevLinearSystemFinite.Main

/-!
# Theorem `qls:thm:main` with the repetition count of equation `qls:eq:hoeffding`

The access model, the promise and the oracle family are those of the released theorems
(`SparseLinearSystems.Endpoint.main`, `ChebyshevLinearSystemFinite.main`). The protocol is the
finite-degree Chebyshev protocol of `ChebyshevLinearSystemFinite` (the degrees of equation
`qls:eq:finitedegree`, possibly approximate known gates within the manuscript's allowances
`e_test`, `e_fin`), with the manuscript's repetition counts
`n_j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉`, `ζ_j = (ε/1000) 2^{j-m}` the combined budget of the five
tests of stage `j` (`repsH`, `repsH_eq_ms`), justified by Hoeffding's inequality
(`two_sided_sharp`).

* `main_ampH`: for every implementation within the allowances in the sense of `AmpApprox`,
  every transcript makes at most `3.4·10⁹ √s κ log(1/ε)` matrix-oracle calls and
  `1.25·10⁸ √s κ log(1/ε)` source calls, and for every input satisfying the promise every run is
  unitary, the success probability is at least `2/3` and the conditional output is within
  trace distance `ε` of the normalised solution;
* `mainH`: the same for every implementation within the allowances in the sense of
  `RunApprox`; `main_exactH`, `main_exactH_exists`: the protocol with exact gates
  (`algorithmFH`).

With the released counts `⌈4 log(2/ζ)/t²⌉` the constants are `2.7·10¹⁰` and `10⁹`
(`ChebyshevLinearSystemFinite.main`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

namespace QLSHoeffding

noncomputable section
open SparseHamiltonian SparseLinearSystems OracleCircuit LogicalWalk Step Protocol Endpoint
  ChebyshevLinearSystem ChebyshevLinearSystemFinite

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **Theorem `qls:thm:main` with Hoeffding's repetition counts and approximate known gates**
(equations `qls:eq:hoeffding`, `qls:eq:finitedegree`, `qls:eq:bernoulli`). For every
implementation of the finite-degree Chebyshev protocol whose runs have the weighted costs of the
ideal runs and, on every input satisfying the promise, change the unnormalised success vector by
at most `e_test` (tests) and `e_fin` (final attempts) (`AmpApprox`), with
`n_j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉` fresh runs per candidate: worst-case query counts over all
transcripts, and for every input satisfying the promise, unitary runs, success probability at
least `2/3` and conditional trace distance at most `ε` from the normalised solution. -/
theorem main_ampH (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, AmpApprox (Promise D κ) (testRunF D Ub sv κ ε j r) (test j r)
      (eTest s (stageOf κ j)))
    (hfin : ∀ r, AmpApprox (Promise D κ) (finalRunF D Ub sv κ ε r) (fin r) (eFin s κ ε)) :
    ((implAlgorithmH κ ε test fin).worstCost wMat : ℝ) ≤
        34 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((implAlgorithmH κ ε test fin).worstCost wSrc : ℝ) ≤
        125 * 10 ^ 6 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (implAlgorithmH κ ε test fin).RunsUnitary x ∧
        2 / 3 ≤ (implAlgorithmH κ ε test fin).successMass x ∧
        ODEMixedOutput.IsDensity ((implAlgorithmH κ ε test fin).conditionalDensity x) ∧
        ∃ h : ((implAlgorithmH κ ε test fin).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance
            ((implAlgorithmH κ ε test fin).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε := by
  refine ⟨impl_matrix_queriesH D Ub sv κ ε hκ hε hε1 test fin
      (fun j r => (htest j r).cost_eq wMat) (fun r => (hfin r).cost_eq wMat),
    impl_source_queriesH D Ub sv κ ε hκ hε hε1 test fin
      (fun j r => (htest j r).cost_eq wSrc) (fun r => (hfin r).cost_eq wSrc), ?_⟩
  intro x hx
  obtain ⟨hU, hM, hout⟩ := impl_correctnessH D Ub hUb sv hsv κ ε hκ hε hε1 test fin x
    hx.norm_le hx.lower (fun j r => (htest j r).amp_sub_le hx) (fun r => (hfin r).amp_sub_le hx)
  obtain ⟨hdens, hsym, hdist⟩ := hout _ (hx.apply_inverse (Ub x sv))
  exact ⟨hU, hM, hdens, hsym, hdist⟩

/-- **Theorem `qls:thm:main` with Hoeffding's repetition counts and approximate known gates**,
the allowances in the sense of `RunApprox` (the errors of the approximate known gates, the seed
and the flag add up to at most `e_test` and `e_fin`). -/
theorem mainH (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10)
    (test : ℕ → ℝ → TestRun (physOracle D Ub (TcF s κ ε)) (PrivO n))
    (fin : ℝ → TestRun (physOracle D Ub (TcF s κ ε)) V0)
    (htest : ∀ j r, RunApprox (testRunF D Ub sv κ ε j r) (test j r) (eTest s (stageOf κ j)))
    (hfin : ∀ r, RunApprox (finalRunF D Ub sv κ ε r) (fin r) (eFin s κ ε)) :
    ((implAlgorithmH κ ε test fin).worstCost wMat : ℝ) ≤
        34 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((implAlgorithmH κ ε test fin).worstCost wSrc : ℝ) ≤
        125 * 10 ^ 6 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (implAlgorithmH κ ε test fin).RunsUnitary x ∧
        2 / 3 ≤ (implAlgorithmH κ ε test fin).successMass x ∧
        ODEMixedOutput.IsDensity ((implAlgorithmH κ ε test fin).conditionalDensity x) ∧
        ∃ h : ((implAlgorithmH κ ε test fin).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance
            ((implAlgorithmH κ ε test fin).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  main_ampH D Ub hUb sv hsv κ ε hκ hε hε1 test fin
    (fun j r => (htest j r).ampApprox (physOracle_unitary D Ub hUb _) _)
    (fun r => (hfin r).ampApprox (physOracle_unitary D Ub hUb _) _)

/-- **Theorem `qls:thm:main` with Hoeffding's repetition counts, finite degrees and exact
gates** (the ideal implementation). -/
theorem main_exactH (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithmFH D Ub sv κ ε).worstCost wMat : ℝ) ≤
        34 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((algorithmFH D Ub sv κ ε).worstCost wSrc : ℝ) ≤
        125 * 10 ^ 6 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (algorithmFH D Ub sv κ ε).RunsUnitary x ∧
        2 / 3 ≤ (algorithmFH D Ub sv κ ε).successMass x ∧
        ODEMixedOutput.IsDensity ((algorithmFH D Ub sv κ ε).conditionalDensity x) ∧
        ∃ h : ((algorithmFH D Ub sv κ ε).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((algorithmFH D Ub sv κ ε).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  mainH D Ub hUb sv hsv κ ε hκ hε hε1 _ _
    (fun _ _ => (RunApprox.refl _).mono (eTest_pos s _ D.slots_pos).le)
    (fun _ => (RunApprox.refl _).mono (eFin_pos s D.slots_pos κ ε hκ hε hε1).le)

/-- **Existential form**: one counter size and one protocol with Hoeffding's repetition counts,
chosen before every unknown input, with at most `3.4·10⁹ √s κ log(1/ε)` matrix-oracle and
`1.25·10⁸ √s κ log(1/ε)` source calls and the guarantees of Theorem `qls:thm:main`. -/
theorem main_exactH_exists (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∃ (T : ℕ) (P : Tree (physOracle D Ub T) (PrivO n) V0),
      (P.worstCost wMat : ℝ) ≤ 34 * 10 ^ 8 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      (P.worstCost wSrc : ℝ) ≤ 125 * 10 ^ 6 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        P.RunsUnitary x ∧ 2 / 3 ≤ P.successMass x ∧
        ODEMixedOutput.IsDensity (P.conditionalDensity x) ∧
        ∃ h : (P.conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance (P.conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  ⟨TcF s κ ε, algorithmFH D Ub sv κ ε, main_exactH D Ub hUb sv hsv κ ε hκ hε hε1⟩

end

end QLSHoeffding
