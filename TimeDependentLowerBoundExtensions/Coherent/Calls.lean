import TimeDependentLowerBoundExtensions.Coherent.Bound
import TimeDependentLowerBoundExtensions.Core.Cost

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Call forms of the coherent-selection family

The native access of the lower bound comes with inverses and the controls of Lemma
`access:lem:control` (the manuscript, Section `hsl:sec:main`). This module admits every call form
(`AdaptiveODELowerBound.Access.callFamily`: plain, inverse, controlled on a control qubit,
controlled inverse) of every label of the released selection family
`TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε'` on the
constant time, mixed and precision data (the paragraphs after the proof of Theorem `hs:thm:time`),
each value call counted once:

* `main_max_calls_select`, `main_max_calls_windows`: programs over the call forms with
  isometric encodings `E` of `ℂ^ι ⊗ ℂ^n` into `ℂ² ⊗ workspace`, meeting `SelectCriterion`
  (respectively `WindowsCriterion`) with a branch of total duration (window length) `τ`;
  certificates `Core.callAccess` of `nonempty_selectAccess`;
* `main_max_tree_calls_select`: adaptive algorithms over the call forms, through
  `admissible_callFamily_select`.

In each case `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `Q` the number of value calls in
any form (for programs, also the number of calls).
-/

namespace TimeDependentLowerBoundExtensions.Coherent

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout HsRelease
open SparseLinearSystems.Protocol
open TimeDependentHamiltonianLowerBound (constData constPath)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Access (callFamily CallForm)
open scoped InnerProduct InnerProductSpace

section Branch

variable {ι N : Type} [Fintype ι] [DecidableEq ι] [Fintype N] [DecidableEq N]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [DecidableEq N] in
/-- An isometric encoding of `ℂ^ι ⊗ ℂ^n` restricted to one branch `|i₀⟩` is isometric. -/
theorem branch_encoding_isometry (E : ODEJointNative.Public ι N →L[ℂ] K) (hE : E† ∘L E = 1)
    (i₀ : ι) : (E ∘L branchInj ι N i₀)† ∘L (E ∘L branchInj ι N i₀) = 1 := by
  have h : (E ∘L branchInj ι N i₀)† ∘L (E ∘L branchInj ι N i₀) =
      (branchInj ι N i₀)† ∘L ((E† ∘L E) ∘L branchInj ι N i₀) := by
    rw [adjoint_comp]; rfl
  rw [h, hE]
  exact branchInj_isometry i₀

end Branch

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for all call forms of the selection family, coherent durations**
(eq. `hsl:eq:main`, max form): as `main_max_select`, for programs over
`callFamily (MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε')` with isometric
encodings into `ℂ² ⊗ workspace`; `Q` the number of value calls in any form, and the same for
the numbers of calls. -/
theorem main_max_calls_select (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (MT MM MP NT NM NP ST SM SP : ℕ) (γT ρT TT εT γM ρM TM εM γP ρP TP εP : ℝ)
    (σT : ℕ → Fin MT) (σM : ℕ → Fin MM) (σP : ℕ → Fin MP)
    (uT : ιT → Fin MT → ℝ) (uM : ιM → Fin MM → ℝ) (uP : ιP → Fin MP → ℝ)
    (iT : ιT) (iM : ιM) (iP : ιP)
    (hdT : ∑ k ∈ Finset.range ST, uT iT (σT k) / (ST : ℝ) = τ)
    (hdM : ∑ k ∈ Finset.range SM, uM iM (σM k) / (SM : ℝ) = τ)
    (hdP : ∑ k ∈ Finset.range SP, uP iP (σP k) / (SP : ℝ) = τ)
    (pT : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle
      (ι := ιT) (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT)))
    (ET : ODEJointNative.Public ιT (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (SelTimeWork ιT τ s MT NT γT ρT TT εT)) (hET : ET† ∘L ET = 1)
    (hT : SelectCriterion pT.eval ET (constData (timeData τ s h.s_ge) MT) σT ST uT ε)
    (pM : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle
      (ι := ιM) (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM)))
    (EM : ODEJointNative.Public ιM (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (SelMixedWork ιM τ ε s MM NM γM ρM TM εM)) (hEM : EM† ∘L EM = 1)
    (hM : SelectCriterion pM.eval EM (constData (mixedMainData τ ε s h.s_ge) MM) σM SM uM ε)
    (pP : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle
      (ι := ιP) (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP)))
    (EP : ODEJointNative.Public ιP (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (SelPrecisionWork ιP τ ε s MP NP γP ρP TP εP)) (hEP : EP† ∘L EP = 1)
    (hP : SelectCriterion pP.eval EP (constData (precisionMainData τ ε s h.s_ge) MP) σP SP uP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.cost (fun c => valueWeight c.1) : ℝ)
          (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hs2 : 2 ≤ s := by have := h.s_ge; omega
  obtain ⟨AT⟩ := nonempty_selectAccess (ι := ιT) (timeData τ s h.s_ge)
    (searchAccess (n := timeN τ) (a := timeC τ) (τ := τ) (one_le_hsMu h.s_ge)
      (two_mul_hsM_le h.s_ge)) MT NT γT ρT TT εT
  obtain ⟨AM⟩ := nonempty_selectAccess (ι := ιM) (mixedMainData τ ε s h.s_ge)
    (searchAccess (n := precN τ ε) (a := 1) (τ := τ) (one_le_hsMu h.s_ge)
      (two_mul_hsM_le h.s_ge)) MM NM γM ρM TM εM
  obtain ⟨AP⟩ := nonempty_selectAccess (ι := ιP) (precisionMainData τ ε s h.s_ge)
    (scalarAccess (n := precN τ ε) (τ := τ) hs2) MP NP γP ρP TP εP
  have oT := fun l x => TimeDependentExtensions.MeshSelect.alignedOracle_unitary (ι := ιT)
    (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT l x
  have oM := fun l x => TimeDependentExtensions.MeshSelect.alignedOracle_unitary (ι := ιM)
    (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM l x
  have oP := fun l x => TimeDependentExtensions.MeshSelect.alignedOracle_unitary (ι := ιP)
    (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP l x
  have key := Core.main_max_access h _
    (AdaptiveODELowerBound.Access.callFamily_unitary oT) (fun c => hardCost c.1)
    ⟨Core.callAccess AT oT⟩ pT (ET ∘L branchInj ιT _ iT) (branch_encoding_isometry ET hET iT)
    (fun j => select_endpoint _ MT ST σT uT iT hdT pT.eval ET hT j) _
    (AdaptiveODELowerBound.Access.callFamily_unitary oM) (fun c => hardCost c.1)
    ⟨Core.callAccess AM oM⟩ pM (EM ∘L branchInj ιM _ iM) (branch_encoding_isometry EM hEM iM)
    (fun j => select_endpoint _ MM SM σM uM iM hdM pM.eval EM hM j) _
    (AdaptiveODELowerBound.Access.callFamily_unitary oP) (fun c => hardCost c.1)
    ⟨Core.callAccess AP oP⟩ pP (EP ∘L branchInj ιP _ iP) (branch_encoding_isometry EP hEP iP)
    (fun x => select_endpoint _ MP SP σP uP iP hdP pP.eval EP hP x)
  exact Core.max_calls_of_hardCost pT pM pP key

/-- **Theorem `hsl:thm:main` for all call forms of the selection family, coherent start times
and durations** (eq. `hsl:eq:main`, max form): as `main_max_windows`, for programs over
`callFamily (MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε')` with isometric
encodings into `ℂ² ⊗ workspace`; `Q` the number of value calls in any form, and the same for
the numbers of calls. -/
theorem main_max_calls_windows (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (MT MM MP NT NM NP : ℕ) (γT ρT TT εT γM ρM TM εM γP ρP TP εP : ℝ) (tT tM tP : ℕ → ℝ)
    (aT bT : ιT → ℕ) (aM bM : ιM → ℕ) (aP bP : ιP → ℕ) (iT : ιT) (iM : ιM) (iP : ιP)
    (hlT : tT (bT iT) - tT (aT iT) = τ) (hlM : tM (bM iM) - tM (aM iM) = τ)
    (hlP : tP (bP iP) - tP (aP iP) = τ)
    (pT : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle
      (ι := ιT) (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT)))
    (ET : ODEJointNative.Public ιT (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (SelTimeWork ιT τ s MT NT γT ρT TT εT)) (hET : ET† ∘L ET = 1)
    (hT : WindowsCriterion pT.eval ET (constData (timeData τ s h.s_ge) MT) tT aT bT ε)
    (pM : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle
      (ι := ιM) (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM)))
    (EM : ODEJointNative.Public ιM (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (SelMixedWork ιM τ ε s MM NM γM ρM TM εM)) (hEM : EM† ∘L EM = 1)
    (hM : WindowsCriterion pM.eval EM (constData (mixedMainData τ ε s h.s_ge) MM) tM aM bM ε)
    (pP : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle
      (ι := ιP) (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP)))
    (EP : ODEJointNative.Public ιP (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (SelPrecisionWork ιP τ ε s MP NP γP ρP TP εP)) (hEP : EP† ∘L EP = 1)
    (hP : WindowsCriterion pP.eval EP (constData (precisionMainData τ ε s h.s_ge) MP) tP aP bP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.cost (fun c => valueWeight c.1) : ℝ)
          (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  have hs2 : 2 ≤ s := by have := h.s_ge; omega
  obtain ⟨AT⟩ := nonempty_selectAccess (ι := ιT) (timeData τ s h.s_ge)
    (searchAccess (n := timeN τ) (a := timeC τ) (τ := τ) (one_le_hsMu h.s_ge)
      (two_mul_hsM_le h.s_ge)) MT NT γT ρT TT εT
  obtain ⟨AM⟩ := nonempty_selectAccess (ι := ιM) (mixedMainData τ ε s h.s_ge)
    (searchAccess (n := precN τ ε) (a := 1) (τ := τ) (one_le_hsMu h.s_ge)
      (two_mul_hsM_le h.s_ge)) MM NM γM ρM TM εM
  obtain ⟨AP⟩ := nonempty_selectAccess (ι := ιP) (precisionMainData τ ε s h.s_ge)
    (scalarAccess (n := precN τ ε) (τ := τ) hs2) MP NP γP ρP TP εP
  have oT := fun l x => TimeDependentExtensions.MeshSelect.alignedOracle_unitary (ι := ιT)
    (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT l x
  have oM := fun l x => TimeDependentExtensions.MeshSelect.alignedOracle_unitary (ι := ιM)
    (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM l x
  have oP := fun l x => TimeDependentExtensions.MeshSelect.alignedOracle_unitary (ι := ιP)
    (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP l x
  have key := Core.main_max_access h _
    (AdaptiveODELowerBound.Access.callFamily_unitary oT) (fun c => hardCost c.1)
    ⟨Core.callAccess AT oT⟩ pT (ET ∘L branchInj ιT _ iT) (branch_encoding_isometry ET hET iT)
    (fun j => windows_endpoint _ hTi.isHermitian MT tT aT bT iT h.eps_pos.le hlT pT.eval ET hT j) _
    (AdaptiveODELowerBound.Access.callFamily_unitary oM) (fun c => hardCost c.1)
    ⟨Core.callAccess AM oM⟩ pM (EM ∘L branchInj ιM _ iM) (branch_encoding_isometry EM hEM iM)
    (fun j => windows_endpoint _ hMi.isHermitian MM tM aM bM iM h.eps_pos.le hlM pM.eval EM hM j) _
    (AdaptiveODELowerBound.Access.callFamily_unitary oP) (fun c => hardCost c.1)
    ⟨Core.callAccess AP oP⟩ pP (EP ∘L branchInj ιP _ iP) (branch_encoding_isometry EP hEP iP)
    (fun x => windows_endpoint _ hPi.isHermitian MP tP aP bP iP h.eps_pos.le hlP pP.eval EP hP x)
  exact Core.max_calls_of_hardCost pT pM pP key

/-- **Theorem `hsl:thm:main` for adaptive algorithms over all call forms of the selection
family** (eq. `hsl:eq:main`, max form): as `main_max_tree_select`, with oracle calls the call
forms `callFamily (MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε')`, weight
`valueWeight c.1`. -/
theorem main_max_tree_calls_select (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
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
    (TrT : Tree (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιT)
      (constData (timeData τ s h.s_ge) MT) NT γT ρT TT εT)) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TrT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TrT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TrM : Tree (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιM)
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ρM TM εM)) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TrM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TrM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TrP : Tree (callFamily (TimeDependentExtensions.MeshSelect.alignedOracle (ι := ιP)
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ρP TP εP)) FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TrP.successMass x)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (TrP.conditionalDensity x) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TrT.worstCost (fun c => valueWeight c.1) : ℝ)
        (max (TrM.worstCost (fun c => valueWeight c.1) : ℝ)
          (TrP.worstCost (fun c => valueWeight c.1))) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hTi, hMi, hPi, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ (fun c => valueWeight c.1)
    (admissible_callFamily_select _ (fun x x' => (hTi.locators_const x x').2.2.1)
      (fun x x' => (hTi.locators_const x x').2.2.2) MT NT γT ρT TT εT) TrT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_select _ (fun x x' => (hMi.locators_const x x').2.2.1)
      (fun x x' => (hMi.locators_const x x').2.2.2) MM NM γM ρM TM εM) TrM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_select _ (fun x x' => (hPi.locators_const x x').2.2.1)
      (fun x x' => (hPi.locators_const x x').2.2.2) MP NP γP ρP TP εP) TrP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

end

end TimeDependentLowerBoundExtensions.Coherent
