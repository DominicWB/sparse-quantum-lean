import TimeDependentLowerBoundExtensions.Measured.BlockCompile
import TimeDependentLowerBoundExtensions.BlockEncoding.Bound
import TimeDependentHamiltonianLowerBound.Trees

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for measured algorithms over time-indexed block encodings

The model of eqs. `hs:eq:blockspecial` and `hs:eq:blockadditive` supplies coherent and controlled
access to Hermitian unitaries `O_r` with
`J† O_r J = H̃_r / α_BE`; the lower bound of Theorem `hsl:thm:main` (eq. `hsl:eq:main`) applies to
the time-dependent class with time-independent hard instances (the paragraphs after the proof of
Theorem `hs:thm:time`), and randomised or adaptive algorithms are covered by purification and
deferred measurement (proof of Lemma `hsl:lem:precision`). This module states the block-encoding
form of `TimeDependentLowerBoundExtensions.BlockEncoding` for **measured algorithms**
(`DeferredMeasurementLowerBounds.Model.Measured`) on the constant Hermitian block encodings
`beConst D M` of the time, mixed and precision families:

* `main_max_measured_block`: over the released aligned block-encoding family
  `TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) N α T ε'`, the oracle family
  of both `TimeDependentExtensions.BlockEncoding.simulation` and
  `IntegrablePathSimulation.BlockEncoding.simulation`;
* `main_max_measured_block_primitive`: over the controlled time-indexed oracle
  `TimeDependentExtensions.BlockEncoding.primitive (beConst D M)`
  (`|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`);
* `main_max_measured_calls_block`: over all call forms of the aligned family.

In each case `c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`, `Q` the
worst-case number of block-encoding calls over all transcripts (inverse calls and every call
form counted once). The factor `8` is the number of value calls of one block-encoding call in
the reduction (`beOp`, the dilation of the six-query block encoding), not a constant of the
manuscript, which states no lower bound in block-encoding calls.

The constant hard paths belong to the block-encoding class: `beConst D M` has `α_BE J† O_r J = H_x`
with `J = beJ D` and `α_BE = beAlpha D` (`beJ_compress`, `blockSample_beOp`), so the sample error is
zero. The bound concerns these specific block encodings, each call two masked runs of the released
six-query block encoding (`8` value calls), with normalisation `beAlpha D = s·scale`, the
`α_BE = sη` of a standard sparse block encoding (the text after eq. `hs:eq:blockadditive`); it is
consistent with eq. `hs:eq:blockadditive` for that normalisation and is
not claimed for block encodings of smaller normalisation. The accuracy hypothesis is eq.
`hsl:eq:accuracy` against every propagator `U` of the constant path from the identity, `U(τ) ψ_in`,
as in the `TimeDependentHamiltonianLowerBound` tree forms; it is the manuscript's own accuracy
condition, and it replaces the program criterion `BECriterion` of `main_max_block`, which a measured
algorithm has no output operator to state. Accuracy against every propagator of the constant path is
accuracy for `exp(-iτH_x) ψ_in`
(`TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`), the target whose endpoint
error `BECriterion` controls for programs (`beCriterion_endpoint`).

Proof: every block-encoding call is a fixed product of masked native calls with `8` value calls
(`nativeCompiles_aligned`, `nativeCompiles_primitive`, `nativeCompiles_calls_aligned`), so
`main_max_measured_compiled` applies, with
`TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff` for the accuracy.

The hypotheses of `main_max_measured_block` are met by the released block-encoding simulator:
on the constant block encodings its program, run as a measured algorithm, succeeds with
probability one and meets the accuracy hypothesis (`released_block_measured`).
-/

namespace TimeDependentLowerBoundExtensions.Measured

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout
open TimeDependentLowerBoundExtensions.BlockEncoding
open TimeDependentHamiltonianLowerBound (constPath)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveODELowerBound.Access (callFamily)
open DeferredMeasurementLowerBounds.Model (Measured)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for measured algorithms over time-indexed block encodings** (eq.
`hsl:eq:main`, max form; an extension of the remark after the proof of Theorem `hs:thm:time` to the
model of eqs. `hs:eq:blockspecial` and `hs:eq:blockadditive`): for any three
measured algorithms whose oracle calls are the released aligned block-encoding families
`TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) N α T ε'` (the oracle family of
`TimeDependentExtensions.BlockEncoding.simulation` and
`IntegrablePathSimulation.BlockEncoding.simulation`) of the constant Hermitian block encodings of
the time, mixed and precision families (any numbers of samples, slot counts and schedules), with
unit initial vectors, success probability at least `2/3` on every input and conditional output
`ε`-accurate for `U(τ) ψ_in` for every propagator `U` of the constant path from the identity,
`c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`, `Q` the worst-case number of block-encoding
calls, inverses included. The factor `8` comes from the reduction. The bound concerns the block
encodings `beConst D M`, each call two masked runs of the released six-query block encoding (`8`
value calls), with normalisation `beAlpha D = s·scale`, the `α_BE = sη` of a standard sparse block
encoding (the manuscript, the text after eq. `hs:eq:blockadditive`); it
is consistent with eq. `hs:eq:blockadditive` for that normalisation and is not claimed for block
encodings of smaller normalisation. -/
theorem main_max_measured_block (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (αT TT εT αM TM εM αP TP εP : ℝ) {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (timeData τ s h.s_ge) MT) NT αT TT εT) ET)
    (φT : BETimeWork τ s MT NT αT TT εT) (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM) EM)
    (φM : BEMixedWork τ ε s MM NM αM TM εM) (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (AM.conditionalDensity j φM)
        (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (AP : Measured (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP) EP)
    (φP : BEPrecisionWork τ ε s MP NP αP TP εP) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (AP.conditionalDensity x φP) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (AT.worstCost (fun _ => 1) : ℝ)
        (max (AM.worstCost (fun _ => 1) : ℝ) (AP.worstCost (fun _ => 1))) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  have key := main_max_measured_compiled h 8 _
    (nativeCompiles_aligned _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT NT αT TT εT) AT φT hφT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (nativeCompiles_aligned _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM NM αM TM εM) AM φM hφM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (nativeCompiles_aligned _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP NP αP TP εP) AP φP hφP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)
  exact_mod_cast key

/-- **Theorem `hsl:thm:main` for measured algorithms over the controlled time-indexed oracle** (eq.
`hsl:eq:main`, max form; an extension of the remark after the proof of Theorem `hs:thm:time` to the
access model of eqs. `hs:eq:blockspecial` and `hs:eq:blockadditive`): as
`main_max_measured_block`, with oracle calls the controlled time-indexed oracle
`TimeDependentExtensions.BlockEncoding.primitive (beConst D M)` (`|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`,
the formalisation of the coherent and controlled access of those lines; any number `M` of
samples). -/
theorem main_max_measured_block_primitive (h : HSRange τ s ε) (MT MM MP : ℕ)
    {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (TimeDependentExtensions.BlockEncoding.primitive
      (beConst (timeData τ s h.s_ge) MT)) ET)
    (φT : BETimePrim τ s MT) (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (TimeDependentExtensions.BlockEncoding.primitive
      (beConst (mixedMainData τ ε s h.s_ge) MM)) EM)
    (φM : BEMixedPrim τ ε s MM) (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (AM.conditionalDensity j φM)
        (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (AP : Measured (TimeDependentExtensions.BlockEncoding.primitive
      (beConst (precisionMainData τ ε s h.s_ge) MP)) EP)
    (φP : BEPrecisionPrim τ ε s MP) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (AP.conditionalDensity x φP) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (AT.worstCost (fun _ => 1) : ℝ)
        (max (AM.worstCost (fun _ => 1) : ℝ) (AP.worstCost (fun _ => 1))) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  have key := main_max_measured_compiled h 8 _
    (nativeCompiles_primitive _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT) AT φT hφT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (nativeCompiles_primitive _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM) AM φM hφM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (nativeCompiles_primitive _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP) AP φP hφP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)
  exact_mod_cast key

set_option synthInstance.maxSize 8192 in
/-- **Theorem `hsl:thm:main` for measured algorithms over all call forms of the aligned
block-encoding family** (eq. `hsl:eq:main`, max form; an extension of the manuscript's the
paragraphs after the proof of Theorem `hs:thm:time`): as `main_max_measured_block`, with oracle
calls the plain, inverse, controlled and controlled-inverse calls
(`AdaptiveODELowerBound.Access.callFamily`) of the aligned family, every call form counted once. -/
theorem main_max_measured_calls_block (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (αT TT εT αM TM εM αP TP εP : ℝ) {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (callFamily (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (timeData τ s h.s_ge) MT) NT αT TT εT)) ET)
    (φT : Joint Bool (BETimeWork τ s MT NT αT TT εT)) (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (callFamily (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM)) EM)
    (φM : Joint Bool (BEMixedWork τ ε s MM NM αM TM εM)) (hφM : ‖φM‖ = 1)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ AM.successMass j φM)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (AM.conditionalDensity j φM)
        (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (AP : Measured (callFamily (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP)) EP)
    (φP : Joint Bool (BEPrecisionWork τ ε s MP NP αP TP εP)) (hφP : ‖φP‖ = 1)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ AP.successMass x φP)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (AP.conditionalDensity x φP) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (AT.worstCost (fun _ => 1) : ℝ)
        (max (AM.worstCost (fun _ => 1) : ℝ) (AP.worstCost (fun _ => 1))) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  have key := main_max_measured_compiled h 8 _
    (nativeCompiles_calls_aligned _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT NT αT TT εT) AT φT hφT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (nativeCompiles_calls_aligned _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM NM αM TM εM) AM φM hφM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (nativeCompiles_calls_aligned _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP NP αP TP εP) AP φP hφP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)
  exact_mod_cast key

end

end TimeDependentLowerBoundExtensions.Measured
