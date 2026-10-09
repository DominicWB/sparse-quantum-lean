import DeferredMeasurementLowerBounds.Corollaries.Hamiltonian
import TimeDependentHamiltonianLowerBound.Trees

set_option autoImplicit false

/-!
# Theorem `hsl:thm:main` for measured algorithms over the time-dependent access

The remark after the proof of Theorem `hs:thm:time` (the lower bound of Theorem `hsl:thm:main`
applies to the time-dependent class) for algorithms with measurements inside a run. The library
`TimeDependentHamiltonianLowerBound` proves it for adaptive protocols over the coherent
sampled-time native access of the constant hard data and over its call forms
(`TimeDependentHamiltonianLowerBound.main_max_tree_access`, `main_max_tree_calls`). Both access
families are admissible (`TimeDependentHamiltonianLowerBound.admissible_coherentAccess`,
`admissible_callFamily_coherentAccess`), and accuracy against every propagator of the constant
path is accuracy for `exp(-iτH_x) ψ_in`
(`TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`), so
`Corollaries.main_max_measured` gives the same bound, with the same constant, for measured
algorithms (`main_max_measured_access`, `main_max_measured_calls`).
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Readout SparseLowerBounds.Hamiltonian
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open TimeDependentHamiltonianLowerBound
open DeferredMeasurementLowerBounds.Model
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for measured algorithms over the coherent sampled-time native
access** (eq. `hsl:eq:main`, max form; the class of Theorem `hs:thm:time` on the constant hard
data): for any three measured algorithms whose oracle calls are the coherent sampled-time native
oracles of the constant time, mixed and precision data, with unit initial vectors, success
probability at least `2/3` on every input and conditional output `ε`-accurate for `U(τ) ψ_in`
for every propagator `U` of the constant path, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`,
where `Q` is the worst-case number of value calls over all transcripts. -/
theorem main_max_measured_access (h : HSRange τ s ε) (MT MM MP : ℕ) (ιT ιM ιP : Type)
    [Fintype ιT] [Fintype ιM] [Fintype ιP] {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (coherentAccess ιT (constData (timeData τ s h.s_ge) MT)) ET)
    (φT : Joint (ιT × Fin MT) (SparseFlagEmbedding.Space
      (SearchIndex (timeN τ) (hsMu s) s × SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ))))
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (coherentAccess ιM (constData (mixedMainData τ ε s h.s_ge) MM)) EM)
    (φM : Joint (ιM × Fin MM) (SparseFlagEmbedding.Space
      (SearchIndex (precN τ ε) (hsMu s) s × SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ))))
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
    (AP : Measured (coherentAccess ιP (constData (precisionMainData τ ε s h.s_ge) MP)) EP)
    (φP : Joint (ιP × Fin MP) (SparseFlagEmbedding.Space
      (ScalarIndex (precN τ ε) s × ScalarIndex (precN τ ε) s)
      (Word (scalarBits (precN τ ε) s τ))))
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
  exact main_max_measured h _ valueWeight
    (admissible_coherentAccess ιT _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT) AT φT hφT eT heT hsuccT
    ((densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ valueWeight
    (admissible_coherentAccess ιM _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM) AM φM hφM eM heM hsuccM
    ((densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ valueWeight
    (admissible_coherentAccess ιP _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP) AP φP hφP eP heP hsuccP
    ((densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

set_option synthInstance.maxSize 8192 in
/-- **Theorem `hsl:thm:main` for measured algorithms over the call forms of the coherent
sampled-time native access** (eq. `hsl:eq:main`, max form; the class of Theorem `hs:thm:time`
on the constant hard data): as `main_max_measured_access`, with oracle calls the plain,
inverse, controlled and controlled-inverse forms
(`AdaptiveODELowerBound.Access.callFamily`) of the coherent sampled-time native oracles, each
value form counted as one value call. -/
theorem main_max_measured_calls (h : HSRange τ s ε) (MT MM MP : ℕ) (ιT ιM ιP : Type)
    [Fintype ιT] [Fintype ιM] [Fintype ιP] {ET GT EM GM EP GP : Type*}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : Measured (AdaptiveODELowerBound.Access.callFamily
      (coherentAccess ιT (constData (timeData τ s h.s_ge) MT))) ET)
    (φT : Joint Bool (Joint (ιT × Fin MT) (SparseFlagEmbedding.Space
      (SearchIndex (timeN τ) (hsMu s) s × SearchIndex (timeN τ) (hsMu s) s)
      (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)))))
    (hφT : ‖φT‖ = 1)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ AT.successMass j φT)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (AT.conditionalDensity j φT)
        (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (AM : Measured (AdaptiveODELowerBound.Access.callFamily
      (coherentAccess ιM (constData (mixedMainData τ ε s h.s_ge) MM))) EM)
    (φM : Joint Bool (Joint (ιM × Fin MM) (SparseFlagEmbedding.Space
      (SearchIndex (precN τ ε) (hsMu s) s × SearchIndex (precN τ ε) (hsMu s) s)
      (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)))))
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
    (AP : Measured (AdaptiveODELowerBound.Access.callFamily
      (coherentAccess ιP (constData (precisionMainData τ ε s h.s_ge) MP))) EP)
    (φP : Joint Bool (Joint (ιP × Fin MP) (SparseFlagEmbedding.Space
      (ScalarIndex (precN τ ε) s × ScalarIndex (precN τ ε) s)
      (Word (scalarBits (precN τ ε) s τ)))))
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
  exact main_max_measured h _ (fun c => valueWeight c.1)
    (admissible_callFamily_coherentAccess ιT _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT) AT φT hφT eT heT hsuccT
    ((densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_coherentAccess ιM _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM) AM φM hφM eM heM hsuccM
    ((densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_coherentAccess ιP _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP) AP φP hφP eP heP hsuccP
    ((densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

end

end DeferredMeasurementLowerBounds.Corollaries
