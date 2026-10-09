import TimeDependentLowerBoundExtensions.Core.Cost
import TimeDependentHamiltonianLowerBound.Trees

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Theorem `hsl:thm:main` for all call forms of the released time-dependent oracle families

The native access of the lower bound comes "with inverses and coherent controls" (the
manuscript, lines 2078-2082), and the lower bound applies to the time-dependent class with
time-independent hard instances (lines 1512-1516). For the physical oracle families of the
released time-dependent simulators, `TimeDependent.oracle` (uniform meshes, Theorem
`hs:thm:time`) and `TimeDependentExtensions.Hamiltonian.oracle` (general meshes and integrable
paths), on the constant hard data, this module admits every call form of every label
(`AdaptiveODELowerBound.Access.callFamily`: plain, inverse, controlled on a control qubit,
controlled inverse), each value call counted once:

* programs: `main_max_calls_uniform`, `main_max_calls_mesh`, `main_max_calls_integrable`,
  under the error criteria of the released theorems on the constant paths (`UniformGuarantee`,
  `MeshCriterion`, `IntegrableCriterion`), with `Q = p.cost (valueWeight ∘ fst)` the number of
  value calls in any form, and the same for the numbers of calls; the Boolean certificates are
  `Core.callAccess` of the released certificates;
* adaptive algorithms: `main_max_tree_calls_uniform`, `main_max_tree_calls_mesh`, with the
  hypotheses of `TimeDependentHamiltonianLowerBound.main_max_tree_uniform` and
  `main_max_tree_mesh` and the admissibility `admissible_callFamily_uniform`,
  `admissible_callFamily_mesh` (normal forms
  `TimeDependentHamiltonianLowerBound.uniform_normal_form`, `mesh_normal_form` and
  `Core.admissible_callFamily_of_normal_form`).

In each case `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`. The call forms of the selection
family are in `Coherent.Calls`; endpoint forms for any certified family follow from
`Core.main_max_access` with `Core.callAccess`.
-/

namespace TimeDependentLowerBoundExtensions.Calls

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open SparseLowerBounds SparseLowerBounds.Hamiltonian SparseLowerBounds.Readout HsRelease
open SparseLinearSystems.Protocol
open TimeDependentHamiltonianLowerBound (constData constPath UniformGuarantee MeshCriterion
  IntegrableCriterion)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (valueWeight Admissible)
open AdaptiveODELowerBound.Access (callFamily CallForm)
open scoped InnerProduct InnerProductSpace

/-! ### Admissibility of the call forms -/

section Admissible

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- **Every call form of the uniform-mesh released family on constant data is admissible** with
the value-query weight of its label. -/
theorem admissible_callFamily_uniform (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M : ℕ) (γ η t ε : ℝ)
    (c : Query × CallForm) :
    Admissible D (callFamily (TimeDependent.oracle (constData D M) γ η t ε) c) (valueWeight c.1) :=
  Core.admissible_callFamily_of_normal_form D hrow hcol
    (TimeDependentHamiltonianLowerBound.uniform_normal_form D M γ η t ε) c

/-- **Every call form of the general-mesh released family on constant data is admissible** with
the value-query weight of its label. -/
theorem admissible_callFamily_mesh (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (M Nsl : ℕ) (γ η T ε : ℝ)
    (c : Query × CallForm) :
    Admissible D
      (callFamily (TimeDependentExtensions.Hamiltonian.oracle (constData D M) Nsl γ η T ε) c)
      (valueWeight c.1) :=
  Core.admissible_callFamily_of_normal_form D hrow hcol
    (TimeDependentHamiltonianLowerBound.mesh_normal_form D M Nsl γ η T ε) c

end Admissible

variable {τ ε : ℝ} {s : ℕ}

/-! ### Programs over the call forms -/

/-- **Theorem `hsl:thm:main` for programs over all call forms of the uniform-mesh released
family** (eq. `hsl:eq:main`, max form): for any three programs over
`callFamily (TimeDependent.oracle (constData D M) γ η t ε')` of the constant time, mixed and
precision data (any numbers of samples and schedules) and isometric encodings into
`ℂ² ⊗ workspace`, each meeting the criterion of `TimeDependent.simulation` on the constant path
(`UniformGuarantee`, time `τ`), `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `Q` the number of
value calls in any form, and the same for the numbers of calls. -/
theorem main_max_calls_uniform (h : HSRange τ s ε) (MT MM MP : ℕ)
    (γT ηT tT εT γM ηM tM εM γP ηP tP εP : ℝ)
    (pT : MultiOracleCircuit.Program
      (callFamily (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT) γT ηT tT εT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependent.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT γT ηT tT εT))
    (hιT : ιT† ∘L ιT = 1)
    (hT : UniformGuarantee pT.eval ιT (constPath (timeData τ s h.s_ge)) τ ε)
    (pM : MultiOracleCircuit.Program
      (callFamily (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM) γM ηM tM εM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependent.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM γM ηM tM εM))
    (hιM : ιM† ∘L ιM = 1)
    (hM : UniformGuarantee pM.eval ιM (constPath (mixedMainData τ ε s h.s_ge)) τ ε)
    (pP : MultiOracleCircuit.Program
      (callFamily (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP)
        γP ηP tP εP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (TimeDependent.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s MP γP ηP tP εP))
    (hιP : ιP† ∘L ιP = 1)
    (hP : UniformGuarantee pP.eval ιP (constPath (precisionMainData τ ε s h.s_ge)) τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.cost (fun c => valueWeight c.1) : ℝ)
          (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have AT : PhaseAccess _ oneHotPattern (oracles (timeData τ s h.s_ge)) hardCost :=
    searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)
  have AM : PhaseAccess _ oneHotPattern (oracles (mixedMainData τ ε s h.s_ge)) hardCost :=
    searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)
  have AP : PhaseAccess _ bitPattern (oracles (precisionMainData τ ε s h.s_ge)) hardCost :=
    scalarAccess (by have := h.s_ge; omega)
  have uT := SparseHamiltonian.TimeDependent.oracle_unitary
    (constData (timeData τ s h.s_ge) MT) γT ηT tT εT
  have uM := SparseHamiltonian.TimeDependent.oracle_unitary
    (constData (mixedMainData τ ε s h.s_ge) MM) γM ηM tM εM
  have uP := SparseHamiltonian.TimeDependent.oracle_unitary
    (constData (precisionMainData τ ε s h.s_ge) MP) γP ηP tP εP
  exact Core.max_calls_of_hardCost pT pM pP <| Core.main_max_access h _
    (AdaptiveODELowerBound.Access.callFamily_unitary uT) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.uniformAccess _ AT MT γT ηT tT εT)
      uT⟩ pT ιT hιT
      ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ pT.eval ιT hτ).1 hT)
    _ (AdaptiveODELowerBound.Access.callFamily_unitary uM) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.uniformAccess _ AM MM γM ηM tM εM)
      uM⟩ pM ιM hιM
      ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ pM.eval ιM hτ).1 hM)
    _ (AdaptiveODELowerBound.Access.callFamily_unitary uP) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.uniformAccess _ AP MP γP ηP tP εP)
      uP⟩ pP ιP hιP
      ((TimeDependentHamiltonianLowerBound.uniform_criterion_iff _ pP.eval ιP hτ).1 hP)

/-- **Theorem `hsl:thm:main` for programs over all call forms of the general-mesh released
family** (eq. `hsl:eq:main`, max form): as `main_max_calls_uniform`, for
`callFamily (TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε')` under the
criterion of `TimeDependentExtensions.Hamiltonian.simulation` on the constant pieces
(`MeshCriterion`, any mesh `t`, final time `τ`). -/
theorem main_max_calls_mesh (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ) (tT tM tP : ℕ → ℝ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT NT γT ηT TT εT))
    (hιT : ιT† ∘L ιT = 1)
    (hT : MeshCriterion pT.eval ιT (constPath (timeData τ s h.s_ge)) tT MT τ ε)
    (pM : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM NM γM ηM TM εM))
    (hιM : ιM† ∘L ιM = 1)
    (hM : MeshCriterion pM.eval ιM (constPath (mixedMainData τ ε s h.s_ge)) tM MM τ ε)
    (pP : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s MP NP γP ηP TP εP))
    (hιP : ιP† ∘L ιP = 1)
    (hP : MeshCriterion pP.eval ιP (constPath (precisionMainData τ ε s h.s_ge)) tP MP τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.cost (fun c => valueWeight c.1) : ℝ)
          (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have AT : PhaseAccess _ oneHotPattern (oracles (timeData τ s h.s_ge)) hardCost :=
    searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)
  have AM : PhaseAccess _ oneHotPattern (oracles (mixedMainData τ ε s h.s_ge)) hardCost :=
    searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)
  have AP : PhaseAccess _ bitPattern (oracles (precisionMainData τ ε s h.s_ge)) hardCost :=
    scalarAccess (by have := h.s_ge; omega)
  have uT := TimeDependentExtensions.Hamiltonian.oracle_unitary
    (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT
  have uM := TimeDependentExtensions.Hamiltonian.oracle_unitary
    (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM
  have uP := TimeDependentExtensions.Hamiltonian.oracle_unitary
    (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP
  exact Core.max_calls_of_hardCost pT pM pP <| Core.main_max_access h _
    (AdaptiveODELowerBound.Access.callFamily_unitary uT) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.meshAccess _ AT MT NT γT ηT TT εT)
      uT⟩ pT ιT hιT
      (TimeDependentHamiltonianLowerBound.endpoint_of_mesh _ pT.eval ιT hT)
    _ (AdaptiveODELowerBound.Access.callFamily_unitary uM) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.meshAccess _ AM MM NM γM ηM TM εM)
      uM⟩ pM ιM hιM
      (TimeDependentHamiltonianLowerBound.endpoint_of_mesh _ pM.eval ιM hM)
    _ (AdaptiveODELowerBound.Access.callFamily_unitary uP) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.meshAccess _ AP MP NP γP ηP TP εP)
      uP⟩ pP ιP hιP
      (TimeDependentHamiltonianLowerBound.endpoint_of_mesh _ pP.eval ιP hP)

/-- **Theorem `hsl:thm:main` for programs over all call forms of the integrable-path released
family** (eq. `hsl:eq:main`, max form): as `main_max_calls_mesh`, for
`callFamily (TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε')` under the
integrable-path criterion of `TimeDependentExtensions.Hamiltonian` on the constant path
(`IntegrableCriterion`, every integral-sense propagator, final time `τ`), as
`TimeDependentHamiltonianLowerBound.main_max_integrable`. -/
theorem main_max_calls_integrable (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
    (pT : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT)))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (timeN τ) (hsMu s) s)
        (Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ)) s MT NT γT ηT TT εT))
    (hιT : ιT† ∘L ιT = 1)
    (hT : IntegrableCriterion pT.eval ιT (constPath (timeData τ s h.s_ge)) τ ε)
    (pM : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM)))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (SearchIndex (precN τ ε) (hsMu s) s)
        (Word (searchBits (precN τ ε) (hsMu s) s 1 τ)) s MM NM γM ηM TM εM))
    (hιM : ιM† ∘L ιM = 1)
    (hM : IntegrableCriterion pM.eval ιM (constPath (mixedMainData τ ε s h.s_ge)) τ ε)
    (pP : MultiOracleCircuit.Program (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP)))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      Joint Bool (TimeDependentExtensions.Hamiltonian.Workspace (ScalarIndex (precN τ ε) s)
        (Word (scalarBits (precN τ ε) s τ)) s MP NP γP ηP TP εP))
    (hιP : ιP† ∘L ιP = 1)
    (hP : IntegrableCriterion pP.eval ιP (constPath (precisionMainData τ ε s h.s_ge)) τ ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.cost (fun c => valueWeight c.1) : ℝ)
          (max (pM.cost (fun c => valueWeight c.1) : ℝ) (pP.cost (fun c => valueWeight c.1))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have AT : PhaseAccess _ oneHotPattern (oracles (timeData τ s h.s_ge)) hardCost :=
    searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)
  have AM : PhaseAccess _ oneHotPattern (oracles (mixedMainData τ ε s h.s_ge)) hardCost :=
    searchAccess (one_le_hsMu h.s_ge) (two_mul_hsM_le h.s_ge)
  have AP : PhaseAccess _ bitPattern (oracles (precisionMainData τ ε s h.s_ge)) hardCost :=
    scalarAccess (by have := h.s_ge; omega)
  have uT := TimeDependentExtensions.Hamiltonian.oracle_unitary
    (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT
  have uM := TimeDependentExtensions.Hamiltonian.oracle_unitary
    (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM
  have uP := TimeDependentExtensions.Hamiltonian.oracle_unitary
    (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP
  exact Core.max_calls_of_hardCost pT pM pP <| Core.main_max_access h _
    (AdaptiveODELowerBound.Access.callFamily_unitary uT) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.meshAccess _ AT MT NT γT ηT TT εT)
      uT⟩ pT ιT hιT
      ((TimeDependentHamiltonianLowerBound.integrable_criterion_iff _ pT.eval ιT hτ).1 hT)
    _ (AdaptiveODELowerBound.Access.callFamily_unitary uM) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.meshAccess _ AM MM NM γM ηM TM εM)
      uM⟩ pM ιM hιM
      ((TimeDependentHamiltonianLowerBound.integrable_criterion_iff _ pM.eval ιM hτ).1 hM)
    _ (AdaptiveODELowerBound.Access.callFamily_unitary uP) _
    ⟨Core.callAccess (TimeDependentHamiltonianLowerBound.meshAccess _ AP MP NP γP ηP TP εP)
      uP⟩ pP ιP hιP
      ((TimeDependentHamiltonianLowerBound.integrable_criterion_iff _ pP.eval ιP hτ).1 hP)

/-! ### Adaptive algorithms over the call forms -/

/-- **Theorem `hsl:thm:main` for adaptive algorithms over all call forms of the uniform-mesh
released family** (eq. `hsl:eq:main`, max form): as
`TimeDependentHamiltonianLowerBound.main_max_tree_uniform`, with oracle calls the call forms
`callFamily (TimeDependent.oracle (constData D M) γ η t ε')`, weight `valueWeight c.1`. -/
theorem main_max_tree_calls_uniform (h : HSRange τ s ε) (MT MM MP : ℕ)
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
    (TrT : Tree (callFamily (TimeDependent.oracle (constData (timeData τ s h.s_ge) MT)
      γT ηT tT εT)) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TrT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TrT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TrM : Tree (callFamily (TimeDependent.oracle (constData (mixedMainData τ ε s h.s_ge) MM)
      γM ηM tM εM)) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TrM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TrM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TrP : Tree (callFamily (TimeDependent.oracle (constData (precisionMainData τ ε s h.s_ge) MP)
      γP ηP tP εP)) FP EP)
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
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ (fun c => valueWeight c.1)
    (admissible_callFamily_uniform _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT γT ηT tT εT) TrT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_uniform _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM γM ηM tM εM) TrM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_uniform _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP γP ηP tP εP) TrP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

/-- **Theorem `hsl:thm:main` for adaptive algorithms over all call forms of the general-mesh
released family** (eq. `hsl:eq:main`, max form): as `main_max_tree_calls_uniform`, for
`callFamily (TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε')`. -/
theorem main_max_tree_calls_mesh (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (γT ηT TT εT γM ηM TM εM γP ηP TP εP : ℝ)
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
    (TrT : Tree (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (timeData τ s h.s_ge) MT) NT γT ηT TT εT)) FT ET)
    (eT : ET →L[ℂ] SysGarb (SearchIndex (timeN τ) (hsMu s) s) GT) (heT : eT† ∘L eT = 1)
    (hsuccT : ∀ j, 2 / 3 ≤ TrT.successMass j)
    (haccT : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (timeData τ s h.s_ge) j u)) U 0 τ →
      DensityAccurate eT (TrT.conditionalDensity j) (U τ (searchInput (timeN τ) (hsMu s) s)) ε)
    (TrM : Tree (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (mixedMainData τ ε s h.s_ge) MM) NM γM ηM TM εM)) FM EM)
    (eM : EM →L[ℂ] SysGarb (SearchIndex (precN τ ε) (hsMu s) s) GM) (heM : eM† ∘L eM = 1)
    (hsuccM : ∀ j, 2 / 3 ≤ TrM.successMass j)
    (haccM : ∀ j, ∀ U : ℝ → (EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
        EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s)), U 0 = 1 →
      TimeDependent.SolvesOn
        (fun u => SparseStateOverlap.matrixOperator (constPath (mixedMainData τ ε s h.s_ge) j u))
        U 0 τ →
      DensityAccurate eM (TrM.conditionalDensity j) (U τ (searchInput (precN τ ε) (hsMu s) s)) ε)
    (TrP : Tree (callFamily (TimeDependentExtensions.Hamiltonian.oracle
      (constData (precisionMainData τ ε s h.s_ge) MP) NP γP ηP TP εP)) FP EP)
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
  obtain ⟨hT, hM, hP, -⟩ := hard_instances h
  exact AdaptiveHamiltonianLowerBound.main_max_tree h _ (fun c => valueWeight c.1)
    (admissible_callFamily_mesh _ (fun x x' => (hT.locators_const x x').2.2.1)
      (fun x x' => (hT.locators_const x x').2.2.2) MT NT γT ηT TT εT) TrT eT heT hsuccT
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eT _ _ hτ).1 haccT)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_mesh _ (fun x x' => (hM.locators_const x x').2.2.1)
      (fun x x' => (hM.locators_const x x').2.2.2) MM NM γM ηM TM εM) TrM eM heM hsuccM
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eM _ _ hτ).1 haccM)
    _ (fun c => valueWeight c.1)
    (admissible_callFamily_mesh _ (fun x x' => (hP.locators_const x x').2.2.1)
      (fun x x' => (hP.locators_const x x').2.2.2) MP NP γP ηP TP εP) TrP eP heP hsuccP
    ((TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff _ eP _ _ hτ).1 haccP)

end

end TimeDependentLowerBoundExtensions.Calls
