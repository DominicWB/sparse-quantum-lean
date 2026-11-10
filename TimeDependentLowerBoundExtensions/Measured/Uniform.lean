import DeferredMeasurementLowerBounds.Corollaries.Hamiltonian
import TimeDependentLowerBoundExtensions.Calls.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for measured algorithms over the released uniform-mesh oracles

The lower bound of Theorem `hsl:thm:main` (the manuscript, eq. `hsl:eq:main`) applies to the
time-dependent class with time-independent hard instances (the paragraphs after the proof of Theorem
`hs:thm:time`), and randomised or adaptive algorithms are covered by purification and deferred
measurement (proof of Lemma `hsl:lem:precision`). This module states it for **measured algorithms**
(`DeferredMeasurementLowerBounds.Model.Measured`: mid-run and multi-outcome measurements, classical
control, randomness and resets) whose oracle calls are the physical oracle family of the released
uniform-mesh simulator `SparseHamiltonian.TimeDependent.simulation`,
`TimeDependent.oracle (constData D M) γ η t ε'` (any number `M` of samples and schedule), on the
constant time, mixed and precision data, and over its call forms (plain, inverse, controlled and
controlled inverse, `AdaptiveODELowerBound.Access.callFamily`; native access with inverses and the
controls of Lemma `access:lem:control`, Section `hsl:sec:main`).

* `main_max_measured_uniform`, `main_max_measured_calls_uniform`:
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`, `Q` the worst-case number
  of value calls over all transcripts (location calls free, every call form of a value call
  counted once).

Proof: the labels are admissible (`TimeDependentHamiltonianLowerBound.admissible_uniform`,
`Calls.admissible_callFamily_uniform`), accuracy against every propagator of the constant path
is accuracy for `exp(-iτH_x) ψ_in`
(`TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`), and
`DeferredMeasurementLowerBounds.Corollaries.main_max_measured` applies; its deferral makes every
record-selected call of admissible labels one native call, so no constant is lost.

The family is the released one, with slot count `M` and the released degree of
`TimeDependent.oracle`; the aligned sampled family with any slot count and degree
(`TimeDependentHamiltonianLowerBound.main_max_sampled`) has no measured form here. The
hypotheses are met by the released simulator: on constant data its program, run as a measured
algorithm, succeeds with probability one and meets the accuracy hypothesis
(`released_uniform_measured`).
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open TimeDependentHamiltonianLowerBound (constData constPath)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily)
open DeferredMeasurementLowerBounds.Model (Measured)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for measured algorithms over the released uniform-mesh oracles**
(eq. `hsl:eq:main`, max form): for any three measured algorithms whose oracle calls are the
labels of `TimeDependent.oracle (constData D M) γ η t ε'` on the constant time, mixed and
precision data (any numbers of samples and schedules), with unit initial vectors, success
probability at least `2/3` on every input and conditional output `ε`-accurate for `U(τ) ψ_in`
for every propagator `U` of the constant path from the identity,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `Q` the worst-case number of value calls. -/
theorem main_max_measured_uniform (h : HSRange τ s ε) (MT MM MP : ℕ)
    (γT ηT tT εT γM ηM tM εM γP ηP tP εP : ℝ) {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT) γT ηT tT εT) ET)
    (φT : TimeDependent.Workspace (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT γT ηT tT εT)
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured
      (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM) γM ηM tM εM) EM)
    (φM : TimeDependent.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM γM ηM tM εM)
    (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (AM.conditionalDensity j φM)
        (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (AP : Measured
      (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP) γP ηP tP εP) EP)
    (φP : TimeDependent.Workspace (ScalarIndex (precN τ ε) s) (Word (scalarBits (precN τ ε) s τ))
      s MP γP ηP tP εP)
    (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (AP.conditionalDensity x φP) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.worstCost valueWeight : ℝ)
        (max (AM.worstCost valueWeight : ℝ) (AP.worstCost valueWeight)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact DeferredMeasurementLowerBounds.Corollaries.main_max_measured h _ valueWeight
    (TimeDependentHamiltonianLowerBound.admissible_uniform _
      (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT γT ηT tT εT) AT φT hφT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ valueWeight
    (TimeDependentHamiltonianLowerBound.admissible_uniform _
      (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM γM ηM tM εM) AM φM hφM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ valueWeight
    (TimeDependentHamiltonianLowerBound.admissible_uniform _
      (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP γP ηP tP εP) AP φP hφP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

set_option synthInstance.maxSize 8192 in
/-- **Theorem `hsl:thm:main` for measured algorithms over the call forms of the released
uniform-mesh oracles** (eq. `hsl:eq:main`, max form): as `main_max_measured_uniform`, with
oracle calls the plain, inverse, controlled and controlled-inverse forms
(`AdaptiveODELowerBound.Access.callFamily`) of `TimeDependent.oracle (constData D M) γ η t ε'`,
each value form counted as one value call. -/
theorem main_max_measured_calls_uniform (h : HSRange τ s ε) (MT MM MP : ℕ)
    (γT ηT tT εT γM ηM tM εM γP ηP tP εP : ℝ) {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured
      (callFamily (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT) γT ηT tT εT)) ET)
    (φT : Joint Bool (TimeDependent.Workspace (SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT γT ηT tT εT))
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (callFamily
      (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM) γM ηM tM εM)) EM)
    (φM : Joint Bool (TimeDependent.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM γM ηM tM εM))
    (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (AM.conditionalDensity j φM)
        (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (AP : Measured (callFamily
      (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP) γP ηP tP εP)) EP)
    (φP : Joint Bool (TimeDependent.Workspace (ScalarIndex (precN τ ε) s)
      (Word (scalarBits (precN τ ε) s τ)) s MP γP ηP tP εP))
    (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (AP.conditionalDensity x φP) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (AT.worstCost (fun c => valueWeight c.1) : ℝ)
        (max (AM.worstCost (fun c => valueWeight c.1) : ℝ)
          (AP.worstCost (fun c => valueWeight c.1))) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact DeferredMeasurementLowerBounds.Corollaries.main_max_measured h _
    (fun c => valueWeight c.1)
    (Calls.admissible_callFamily_uniform _
      (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT γT ηT tT εT) AT φT hφT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (fun c => valueWeight c.1)
    (Calls.admissible_callFamily_uniform _
      (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM γM ηM tM εM) AM φM hφM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (fun c => valueWeight c.1)
    (Calls.admissible_callFamily_uniform _
      (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP γP ηP tP εP) AP φP hφP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

end

end TimeDependentLowerBoundExtensions.Measured
