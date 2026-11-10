import TimeDependentLowerBoundExtensions.Coherent.Bound

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for adaptive algorithms with coherent selection

The proof of Theorem `hs:thm:time` permits coherent selection of known durations and start
times (the manuscript), and the lower bound of Theorem `hsl:thm:main` applies
to the time-dependent class with time-independent hard instances.

* `main_max_tree_select`: adaptive algorithms (`SparseLinearSystems.Protocol.Tree`) whose
  oracle calls are the labels of the released selection family
  `TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε'` on the
  constant time, mixed and precision data, accurate against every propagator of the constant
  path (as `TimeDependentHamiltonianLowerBound.main_max_tree_access`):
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `Q` the worst-case number of value calls.
-/

namespace TimeDependentLowerBoundExtensions.Coherent

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout HsRelease
open SparseLinearSystems.Protocol
open TimeDependentHamiltonianLowerBound (constData constPath)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open scoped InnerProduct InnerProductSpace

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for adaptive algorithms over the selection family** (eq.
`hsl:eq:main`, max form): as `TimeDependentHamiltonianLowerBound.main_max_tree_access`, with
oracle calls the labels of
`TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε'` on the
constant time, mixed and precision data, accuracy against every propagator of the constant path
from the identity, `Q` the worst-case number of value calls. -/
theorem main_max_tree_select (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT] [DecidableEq ιT]
    [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (MT MM MP NT NM NP : ℕ) (γT ρT TT εT γM ρM TM εM γP ρP TP εP : ℝ)
    {FT ET GT FM EM GM FP EP GP : Type*}
    [NormedAddCommGroup FT] [InnerProductSpace ℂ FT] [CompleteSpace FT]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup FM] [InnerProductSpace ℂ FM] [CompleteSpace FM]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup FP] [InnerProductSpace ℂ FP] [CompleteSpace FP]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (TrT : Tree (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιT)
      (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TrT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TrT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TrM : Tree (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιM)
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TrM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TrM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TrP : Tree (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιP)
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP) FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TrP.successMass x)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (TrP.conditionalDensity x) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TrT.worstCost valueWeight : ℝ)
        (max (TrM.worstCost valueWeight : ℝ) (TrP.worstCost valueWeight)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ valueWeight
    (admissible_select _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT NT γT ρT TT εT) TrT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ valueWeight
    (admissible_select _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM NM γM ρM TM εM) TrM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ valueWeight
    (admissible_select _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP NP γP ρP TP εP) TrP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

end

end TimeDependentLowerBoundExtensions.Coherent
