import TimeDependentHamiltonianLowerBound.Adaptive
import TimeDependentHamiltonianLowerBound.Class

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for adaptive algorithms over the time-dependent access

The adaptive form of Theorem `hsl:thm:main` (`AdaptiveHamiltonianLowerBound.main_max_tree`:
adaptive protocols `SparseLinearSystems.Protocol.Tree`, fresh measured runs with classical
branching, uniformly random trial labels and repeats, a heralded output; success probability at
least `2/3` on every input and conditional output `ε`-accurate in trace distance,
`AdaptiveHamiltonianLowerBound.DensityAccurate`; count `T.worstCost w`) for algorithms whose
oracle calls are the time-dependent access of Theorem `hs:thm:time` on the constant hard data.
The labels are admissible with the value-query weight (module `Adaptive`), so
`AdaptiveHamiltonianLowerBound.main_max_tree` applies; with
`AdaptiveHamiltonianLowerBound.Access.valueWeight` the count is the worst-case number of value
queries over all transcripts (location queries free).

The target is the time-dependent one: the conditional output must be `ε`-accurate for
`U(τ) ψ_in` for every propagator `U` of the constant path (`U 0 = 1`, `U' = -iH_x U` on
`[0, τ]`). All these propagators equal `exp(-iτH_x)` at `τ` (`propagator_constPath_eq`), so
this hypothesis is equivalent to the accuracy hypothesis of
`AdaptiveHamiltonianLowerBound.main_max_tree` (`densityAccurate_propagator_iff`).

* `main_max_tree_access`: over the coherent sampled-time native access `coherentAccess ι D`
  (`∑_{(i,r)} |i,r⟩⟨i,r| ⊗ O_l(x, r)`, any branch registers `ι` and numbers of samples `M`).
* `main_max_tree_calls`: over all call forms of that access (plain, inverse, controlled and
  controlled inverse, `AdaptiveODELowerBound.Access.callFamily`; weight `valueWeight c.1`).
* `main_max_tree_uniform`, `main_max_tree_mesh`: over the oracle families of the released
  uniform-mesh and general-mesh simulators (`TimeDependent.oracle`,
  `TimeDependentExtensions.Hamiltonian.oracle`, any schedules).

In each case: `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`.
-/

namespace TimeDependentHamiltonianLowerBound

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLinearSystems.Protocol
open SparseLowerBounds SparseLowerBounds.Readout SparseLowerBounds.Hamiltonian
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open scoped InnerProduct InnerProductSpace

/-! ### Accuracy against the propagators of the constant path -/

section Accuracy

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}
variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **Accuracy against every propagator of the constant path is accuracy for
`exp(-iτH_x) ψ`** (the target of the adaptive lower bound): all propagators of the constant
path agree at `τ ≥ 0`. -/
theorem densityAccurate_propagator_iff (D : Data X N Z s) (e : E →L[ℂ] SysGarb N G)
    (ρ : X → E →L[ℂ] E) (ψ : EuclideanSpace ℂ N) {τ ε : ℝ} (hτ : 0 ≤ τ) :
    (∀ x, ∀ U : ℝ → (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator (constPath D x u)) U
        0 τ → DensityAccurate e (ρ x) (U τ ψ) ε) ↔
    ∀ x, DensityAccurate e (ρ x) (evolve (D.matrix x) τ ψ) ε := by
  constructor
  · intro h x
    exact h x (constProp (SparseStateOverlap.matrixOperator (D.matrix x))) (constProp_zero _)
      (solvesOn_constPath D x 0 τ)
  · intro h x U hU0 hU
    rw [propagator_constPath_eq D x hτ hU0 hU]
    exact h x

end Accuracy

/-! ### Adaptive algorithms -/

variable {τ ε : ℝ} {s : ℕ}

/-- **Theorem `hsl:thm:main` for adaptive algorithms over the coherent sampled-time native
access** (eq. `hsl:eq:main`, max form): for any three adaptive algorithms whose oracle calls are
the coherent sampled-time native oracles `∑_{(i,r)} |i,r⟩⟨i,r| ⊗ O_l(x, r)` of the constant
time, mixed and precision data (any branch registers `ι` and numbers of samples `M`), with
inverse calls, success probability at least `2/3` on every input and conditional output
`ε`-accurate for `U(τ) ψ_in` for every propagator `U` of the constant path,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, where `Q` is the worst-case number of value
queries over all transcripts. -/
theorem main_max_tree_access (h : HSRange τ s ε) (MT MM MP : ℕ) (ιT ιM ιP : Type)
    [Fintype ιT] [Fintype ιM] [Fintype ιP] {FT ET GT FM EM GM FP EP GP : Type*}
    [NormedAddCommGroup FT] [InnerProductSpace ℂ FT] [CompleteSpace FT]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup FM] [InnerProductSpace ℂ FM] [CompleteSpace FM]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup FP] [InnerProductSpace ℂ FP] [CompleteSpace FP]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (TT : Tree (coherentAccess ιT (constData (timeData τ s h.s_ge) MT)) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TM : Tree (coherentAccess ιM (constData (mixedMainData τ ε s h.s_ge) MM)) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TP : Tree (coherentAccess ιP (constData (precisionMainData τ ε s h.s_ge) MP)) FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TP.successMass x)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (TP.conditionalDensity x) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TT.worstCost valueWeight : ℝ)
        (max (TM.worstCost valueWeight : ℝ) (TP.worstCost valueWeight)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ valueWeight
    (admissible_coherentAccess ιT _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT) TT eT heT hsuccT
    ((densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ valueWeight
    (admissible_coherentAccess ιM _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM) TM eM heM hsuccM
    ((densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ valueWeight
    (admissible_coherentAccess ιP _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP) TP eP heP hsuccP
    ((densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

/-- **Theorem `hsl:thm:main` for adaptive algorithms over all call forms of the coherent
sampled-time native access** (eq. `hsl:eq:main`, max form; with inverses and the controls of Lemma
`access:lem:control`): as `main_max_tree_access`, with oracle calls `1 ⊗ O_l`, `1 ⊗ O_l†`,
`|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l` and `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l†` of the coherent sampled-time oracles
`O_l` of the constant data (`AdaptiveODELowerBound.Access.callFamily`), each value call counted
once. -/
theorem main_max_tree_calls (h : HSRange τ s ε) (MT MM MP : ℕ) (ιT ιM ιP : Type)
    [Fintype ιT] [Fintype ιM] [Fintype ιP]
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
    (TT : Tree (AdaptiveODELowerBound.Access.callFamily
      (coherentAccess ιT (constData (timeData τ s h.s_ge) MT))) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TM : Tree (AdaptiveODELowerBound.Access.callFamily
      (coherentAccess ιM (constData (mixedMainData τ ε s h.s_ge) MM))) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TP : Tree (AdaptiveODELowerBound.Access.callFamily
      (coherentAccess ιP (constData (precisionMainData τ ε s h.s_ge) MP))) FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TP.successMass x)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (TP.conditionalDensity x) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TT.worstCost (fun c => valueWeight c.1) : ℝ)
        (max (TM.worstCost (fun c => valueWeight c.1) : ℝ)
          (TP.worstCost (fun c => valueWeight c.1))) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ (fun c => valueWeight c.1)
    (admissible_callFamily_coherentAccess ιT _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT) TT eT heT hsuccT
    ((densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_coherentAccess ιM _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM) TM eM heM hsuccM
    ((densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_coherentAccess ιP _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP) TP eP heP hsuccP
    ((densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

/-- **Theorem `hsl:thm:main` for adaptive algorithms over the released uniform-mesh oracles**
(eq. `hsl:eq:main`, max form): as `main_max_tree_access`, with oracle calls the labels of
`TimeDependent.oracle (constData D M) γ η t ε'` (the physical oracle family of
`TimeDependent.simulation`, any numbers of samples `M` and schedules) on the constant time,
mixed and precision data. -/
theorem main_max_tree_uniform (h : HSRange τ s ε) (MT MM MP : ℕ)
    (γT ηT tT εT γM ηM tM εM γP ηP tP εP : ℝ)
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
    (TT : Tree (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT) γT ηT tT εT) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TM : Tree (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM) γM ηM tM εM)
      FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TP : Tree
      (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP) γP ηP tP εP) FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TP.successMass x)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (TP.conditionalDensity x) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TT.worstCost valueWeight : ℝ)
        (max (TM.worstCost valueWeight : ℝ) (TP.worstCost valueWeight)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ valueWeight
    (admissible_uniform _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT γT ηT tT εT) TT eT heT hsuccT
    ((densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ valueWeight
    (admissible_uniform _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM γM ηM tM εM) TM eM heM hsuccM
    ((densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ valueWeight
    (admissible_uniform _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP γP ηP tP εP) TP eP heP hsuccP
    ((densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

/-- **Theorem `hsl:thm:main` for adaptive algorithms over the released general-mesh oracles**
(eq. `hsl:eq:main`, max form): as `main_max_tree_access`, with oracle calls the labels of
`TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε'` (the physical oracle
family of the general-mesh and integrable-path simulators, any numbers of mesh intervals,
slots and schedules) on the constant time, mixed and precision data. -/
theorem main_max_tree_mesh (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (γT ηT TT' εT γM ηM TM' εM γP ηP TP' εP : ℝ)
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
    (TT : Tree (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT ηT TT' εT) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TM : Tree (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM' εM) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TP : Tree (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP' εP) FP EP)
    (eP : EP →L[ℂ] SysGarb (ScalarIndex (precN τ ε) s) GP) (heP : eP† ∘L eP = 1)
    (hsuccP : ∀ x, 2 / 3 ≤ TP.successMass x)
    (haccP : ∀ x, ∀ U : ℝ → (EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
        EuclideanSpace ℂ (ScalarIndex (precN τ ε) s)), U 0 = 1 →
      TimeDependent.SolvesOn (fun u => SparseStateOverlap.matrixOperator
        (constPath (precisionMainData τ ε s h.s_ge) x u)) U 0 τ →
      DensityAccurate eP (TP.conditionalDensity x) (U τ (scalarInput (precN τ ε) s)) ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      max (TT.worstCost valueWeight : ℝ)
        (max (TM.worstCost valueWeight : ℝ) (TP.worstCost valueWeight)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ valueWeight
    (admissible_mesh _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT NT γT ηT TT' εT) TT eT heT hsuccT
    ((densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ valueWeight
    (admissible_mesh _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM NM γM ηM TM' εM) TM eM heM hsuccM
    ((densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ valueWeight
    (admissible_mesh _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP NP γP ηP TP' εP) TP eP heP hsuccP
    ((densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

end

end TimeDependentHamiltonianLowerBound
