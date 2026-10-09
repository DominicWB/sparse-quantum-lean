import PhysicalODELowerBound.Const.Herald
import PhysicalODELowerBound.Const.Psd
import ReleasedODESolverLowerBounds.Const.Upgrade

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Measured solvers over the constant-coefficient physical oracle: the ODE lower bounds

Manuscript Section `odel:sec:main`, lines 3669-3681 ("The lower bounds thus apply to Theorems
`ode:thm:main` and `ode:thm:time`"), with measurements inside a run (line 2364): eq.
`odel:eq:hsbound` and Lemma `odel:lem:herald` (line 3967), the precision terms of Theorem
`odel:thm:combined` (lines 3705-3708) and Theorem `odel:thm:psd` (line 4016), over the physical
oracle of the released constant-coefficient solver of Theorem `ode:thm:main` (line 2584) and
over its call forms. The time-dependent families (joint, homogeneous) are not
constant-coefficient equations (lines 3717-3719) and are not stated here.

Every statement is the corresponding statement of `PhysicalODELowerBound.Const` with
`MeasuredConstWitnesses` in place of `ConstWitnesses` (`measuredConstWitnesses_of_constWitnesses`), or, for the
max forms, with realised measured counts (`MeasuredConstCost.exists_constCost_le`); hypotheses
and constants are those of the lifted statements. `herald_max_release_measured_const` and
`psd_max_release_measured_const` are the measured forms of
`PhysicalODELowerBound.Const.herald_max_const_tree_of_const` and `psd_max_const_tree_of_const`
(named measured solvers over the physical oracle, both the value and the matrix count).
-/

namespace ReleasedODESolverLowerBounds.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Psd
open ODELowerBoundExtensions.Padding (timePadFamilyAt mixedPadFamilyAt precisionPadFamilyAt)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle (constOracle PublicConstSources)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Eq. `odel:eq:hsbound` for measured solvers over the constant-coefficient physical oracle,
family form**: on `HSRange` and for any `ḡ ≥ 1`, one of the time, mixed and precision families
witnesses `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. -/
theorem herald_witness_measured_const (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    MeasuredConstWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar
        ε (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) :=
  (PhysicalODELowerBound.Const.herald_witness_const h hg).imp
    measuredConstWitnesses_of_constWitnesses
    (Or.imp measuredConstWitnesses_of_constWitnesses measuredConstWitnesses_of_constWitnesses)

/-- **The zero-padded `g = 1` families for measured solvers** (any known padding registers). -/
theorem herald_witness_pad_measured_const (h : HSRange τ s ε) (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    MeasuredConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ
        gbar ε (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP)
        τ gbar ε (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) :=
  (PhysicalODELowerBound.Const.herald_witness_pad_const h hg PT PM PP).imp
    measuredConstWitnesses_of_constWitnesses
    (Or.imp measuredConstWitnesses_of_constWitnesses measuredConstWitnesses_of_constWitnesses)

/-- **The precision terms of Theorem `odel:thm:combined` for measured solvers over the
constant-coefficient physical oracle**: on `HSRange` with `ḡ ≥ 1`, a `g = 1` family witnesses
`c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_measured_const (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    MeasuredConstWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredConstWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar
        ε (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) :=
  (PhysicalODELowerBound.Const.precision_terms_witness_const h hg).imp
    measuredConstWitnesses_of_constWitnesses
    (Or.imp measuredConstWitnesses_of_constWitnesses measuredConstWitnesses_of_constWitnesses)

/-- **Theorem `odel:thm:psd` for measured solvers over the constant-coefficient physical
oracle**: on `PsdRange` and for `ḡ ≥ √2`, the gadget or the scalar family witnesses
`psdConst (√(sτr) + r)`. -/
theorem psd_measured_const (h : PsdRange τ s ε) (hg : Real.sqrt 2 ≤ gbar) :
    MeasuredConstWitnesses (psdSearchFamilyAt h) τ gbar ε (psdBound s τ ε) ∨
      MeasuredConstWitnesses (psdScalarFamilyAt h) τ gbar ε (psdBound s τ ε) :=
  (PhysicalODELowerBound.Const.psd_const h hg).imp measuredConstWitnesses_of_constWitnesses
    measuredConstWitnesses_of_constWitnesses

/-- **Eq. `odel:eq:hsbound` for measured solvers over the constant-coefficient physical oracle,
max form over realised counts.** -/
theorem herald_max_measured_const (h : HSRange τ s ε) {qT qM qP : ℝ}
    (hT : MeasuredConstCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε qT)
    (hM : MeasuredConstCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qM)
    (hP : MeasuredConstCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  obtain ⟨qT', hT', hT''⟩ := hT.exists_constCost_le
  obtain ⟨qM', hM', hM''⟩ := hM.exists_constCost_le
  obtain ⟨qP', hP', hP''⟩ := hP.exists_constCost_le
  exact (PhysicalODELowerBound.Const.herald_max_cost_const h hT' hM' hP').trans
    (max_le_max hT'' (max_le_max hM'' hP''))

/-- **Theorem `odel:thm:psd` for measured solvers over the constant-coefficient physical oracle,
max form over realised counts.** -/
theorem psd_max_measured_const (h : PsdRange τ s ε) {qG qS : ℝ}
    (hG : MeasuredConstCost (psdSearchFamilyAt h) ε qG)
    (hS : MeasuredConstCost (psdScalarFamilyAt h) ε qS) :
    psdBound s τ ε ≤ max qG qS := by
  obtain ⟨qG', hG', hG''⟩ := hG.exists_constCost_le
  obtain ⟨qS', hS', hS''⟩ := hS.exists_constCost_le
  exact (PhysicalODELowerBound.Const.psd_max_cost_const h hG' hS').trans (max_le_max hG'' hS'')

/-- **Eq. `odel:eq:hsbound` at three measured solvers over the constant-coefficient physical
oracle**: the measured form of `PhysicalODELowerBound.Const.herald_max_const_tree_of_const`, for
the value counts and for the matrix counts. -/
theorem herald_max_release_measured_const (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (NT TT dT NM TM dM NP TP dP : ℕ)
    {J₀T JbT : _ → SysOp _} (hJT : PublicConstSources J₀T JbT)
    {J₀M JbM : _ → SysOp _} (hJM : PublicConstSources J₀M JbM)
    {J₀P JbP : _ → SysOp _} (hJP : PublicConstSources J₀P JbP)
    {ET EM EP GT GM GP : Type}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : MeasuredSolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ιT NT TT dT J₀T JbT)
      ET GT ε)
    (AM : MeasuredSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ιM NM TM dM J₀M
        JbM) EM GM ε)
    (AP : MeasuredSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ιP NP TP dP J₀P
        JbP) EP GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) := by
  have hw := ODELowerBoundExtensions.Release.matrixWeight_value_le
  have hv := herald_max_measured_const h (MeasuredConstCost.of_measured ιT NT TT dT hJT AT)
    (MeasuredConstCost.of_measured ιM NM TM dM hJM AM)
    (MeasuredConstCost.of_measured ιP NP TP dP hJP AP)
  exact ⟨hv, hv.trans (max_le_max
    (by exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono AT.alg hw)
    (max_le_max
      (by exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono AM.alg hw)
      (by exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono AP.alg hw)))⟩

/-- **Theorem `odel:thm:psd` at two measured solvers over the constant-coefficient physical
oracle**: the measured form of `PhysicalODELowerBound.Const.psd_max_const_tree_of_const`, for the
value counts and for the matrix counts. -/
theorem psd_max_release_measured_const (h : PsdRange τ s ε) (ιG ιS : Type) [Fintype ιG]
    [DecidableEq ιG] [Fintype ιS] [DecidableEq ιS] (NG TG dG NS TS dS : ℕ)
    {J₀G JbG : _ → SysOp _} (hJG : PublicConstSources J₀G JbG)
    {J₀S JbS : _ → SysOp _} (hJS : PublicConstSources J₀S JbS)
    {EG ES GG GS : Type}
    [NormedAddCommGroup EG] [InnerProductSpace ℂ EG] [CompleteSpace EG] [FiniteDimensional ℂ EG]
    [NormedAddCommGroup ES] [InnerProductSpace ℂ ES] [CompleteSpace ES] [FiniteDimensional ℂ ES]
    [NormedAddCommGroup GG] [InnerProductSpace ℂ GG] [CompleteSpace GG]
    [NormedAddCommGroup GS] [InnerProductSpace ℂ GS] [CompleteSpace GS]
    (AG : MeasuredSolver (psdSearchFamilyAt h)
      (constOracle (psdSearchFamilyAt h) ιG NG TG dG J₀G JbG) EG GG ε)
    (AS : MeasuredSolver (psdScalarFamilyAt h)
      (constOracle (psdScalarFamilyAt h) ιS NS TS dS J₀S JbS) ES GS ε) :
    psdBound s τ ε ≤
        max (AG.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (AS.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) ∧
      psdBound s τ ε ≤
        max (AG.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (AS.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) := by
  have hw := ODELowerBoundExtensions.Release.matrixWeight_value_le
  have hv := psd_max_measured_const h (MeasuredConstCost.of_measured ιG NG TG dG hJG AG)
    (MeasuredConstCost.of_measured ιS NS TS dS hJS AS)
  exact ⟨hv, hv.trans (max_le_max
    (by exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono AG.alg hw)
    (by exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono AS.alg hw))⟩

end

end ReleasedODESolverLowerBounds.Const
