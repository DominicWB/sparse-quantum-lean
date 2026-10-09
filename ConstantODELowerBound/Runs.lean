import ConstantODELowerBound.Solver
import ConstantODELowerBound.Herald
import ConstantODELowerBound.Psd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The lower bounds at the released constant-coefficient solver's runs

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`"), Theorem `ode:thm:main` (lines 3013-3033) and lines 3048-3050 ("When `η_D = 0`,
eq. `ode:eq:main` has exactly the improved Hamiltonian structure, multiplied by the
source/normalisation cost `ḡ`").

A **run** of the released constant-coefficient solver on a one-stage family (`ConstRun F τ ḡ ε η_H
η_D`) is a released protocol (`Protocol.ConstProtocol`) over the released oracle with public
source interfaces, branch register `Solver.RunIndex F τ ḡ ε`, mesh size `Solver.runMesh F τ ḡ ε`,
`Θ = theta(τ η_H, τ η_D, ḡ, ε)`, `ℓ = logBudget(ḡ, ε) = log(10⁴ ḡ/ε)` and `g = ḡ`. The protocol
of the released solver's positive-time branch (`T = τ > 0`, `η_H + R(ḡ, ε) η_D > 0`), with
public source interfaces that prepare `x₀/‖x₀‖` and `b/‖b‖` from a unit seed, is a run
(`Solver.constProtocol_of_certificate`; the solver takes that branch by
`Solver.exists_constProtocol`); the structure does not require the solver's own preconditions
or that the degree is the solver's output, so it is a superset of the solver's outputs, which
only strengthens the statements quantified over it. `ConstRun` is the counterpart, for the
oracle `ODEFinalNativeSource.physicalOracle` of `ODECompleteEndpoint.solver`, of
`ODELowerBoundExtensions.Release.ReleaseRun`, which is stated for the general-mesh oracle
`ODELowerBoundExtensions.Release.releaseOracle`.

* `herald_const_bounds`: for runs on the time, mixed and precision families (`η_H = 1`,
  `η_D = 0`, so `Θ = τ`), with `S = √s τ + √(sτr) + r`:
  `c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ 1274019840 ḡ (√s τ + √(sτℓ) + ℓ)` (`c₀ = log 2/(4096π)`, the lower
  half from `Herald.herald_max_const_tree` at the runs' adaptive solvers, the upper half the
  released certificate), the same lower bound for the value counts, and `max V ≤ max Q`.
* `psd_const_bounds`: for runs on the two PSD families (`η_H = 0`,
  `η_D = 1`, so `Θ = τ ℓ`), `psdConst (√(sτr) + r) ≤ max(Q_G, Q_S)` and each count is at most
  `1274019840 ḡ queryShape(s, τℓ, ℓ)`; the same lower bound for the value counts, and
  `max V ≤ max Q`. The two bounds are stated side by side only: the manuscript proves no
  matching bound for the dissipative subclass (lines 4573-4578).

Runs on all five families exist (`Instances`).

**Scope.** The lower halves are max forms over one solver per family: the families have
different input, index and word types, so they are not bounds on one program. Padding to a
common known dimension (manuscript lines 4441-4442) and a family form (one family forcing the
bound on every solver) are not formalised in this library for the released
constant-coefficient oracle; controlled calls, padding and family forms over this oracle are in
the library `PhysicalODELowerBound`. The homogeneous variant of Remark `odel:rem:homogeneous` is
time dependent and is not a constant-coefficient reduction (lines 4385-4387), so it does not
apply here.
-/

namespace ConstantODELowerBound.Runs

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open SparseLowerBounds.Hamiltonian (HSRange hsR c0)
open ODELowerBoundExtensions.Release (SysOp)
open ODELowerBoundExtensions.Psd (PsdRange psdSearchFamilyAt psdScalarFamilyAt psdBound)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Model (TreeSolver)
open ConstantODELowerBound.Oracle ConstantODELowerBound.Protocol ConstantODELowerBound.Solver

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

/-- **A run of the released constant-coefficient solver** on a one-stage family at time `τ`,
promise `ḡ`, accuracy `ε` and split bounds `η_H`, `η_D`: public source interfaces, a slot count,
a degree and a released protocol over the released oracle with the released complete certificate
for every input, `Θ = theta(τ η_H, τ η_D, ḡ, ε)`, `ℓ = logBudget(ḡ, ε)`, `g = ḡ`. The
protocol of the released solver's positive-time branch on `constData F` (`T = τ > 0`,
`η_H + R(ḡ, ε) η_D > 0`), with public source interfaces that prepare `x₀/‖x₀‖` and `b/‖b‖` from
a unit seed, is one (`Solver.constProtocol_of_certificate`; the solver takes that branch by
`Solver.exists_constProtocol`, and runs exist by `Instances.constRun_nonempty`); the structure
does not require the solver's own preconditions, that `η_H`, `η_D` bound the generator's parts, or
that `degree` is the solver's output, so it is a superset of the solver's outputs, which only
strengthens the statements quantified over it. -/
structure ConstRun {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
    [DecidableEq Z] {s : ℕ} (F : Family X N Z 1 s) (τ gbar ε etaH etaD : ℝ) where
  /-- A system index, the clean garbage register of the readout `endpointReadout 1 i₀`. -/
  i₀ : N
  /-- The slot count of the released run. -/
  slots : ℕ
  /-- A degree for which the released certificate holds. -/
  degree : ℕ
  /-- The initial-state interface. -/
  J₀ : X → SysOp N
  /-- The forcing interface. -/
  Jb : X → SysOp N
  /-- The source interfaces are public (unitary and input-independent). -/
  sources_public : PublicConstSources J₀ Jb
  /-- A four-attempt protocol of the released form. -/
  prot : ODERepeatProtocol.Protocol
    (constOracle F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) slots degree J₀ Jb)
    (EuclideanSpace ℂ N)
  /-- The released complete certificate for every input. -/
  release : ConstProtocol F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) slots degree J₀ Jb prot
    (ImprovedODEQueryBudget.theta (τ * etaH) (τ * etaD) gbar ε)
    (ImprovedODEQueryBudget.logBudget gbar ε) gbar ε

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ} {F : Family X N Z 1 s} {τ gbar ε etaH etaD : ℝ}

/-- The worst-case number of matrix queries of a run (row, column and value calls, inverses
included, over all transcripts). -/
def ConstRun.matrixQueries (A : ConstRun F τ gbar ε etaH etaD) : ℕ :=
  A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))

/-- The worst-case number of value queries of a run (value calls, inverses included; location
and source calls weigh `0`). -/
def ConstRun.valueQueries (A : ConstRun F τ gbar ε etaH etaD) : ℕ :=
  A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)

/-- A run makes at most as many value queries as matrix queries. -/
theorem ConstRun.valueQueries_le (A : ConstRun F τ gbar ε etaH etaD) :
    A.valueQueries ≤ A.matrixQueries := by
  exact ODELowerBoundExtensions.Release.worstCost_mono A.prot
    ODELowerBoundExtensions.Release.matrixWeight_value_le

/-- **The released query bound of a run**: at most `1274019840 ḡ · queryShape(s, Θ, ℓ)` matrix
queries, `Θ = theta(τ η_H, τ η_D, ḡ, ε)`, `ℓ = logBudget(ḡ, ε)`, on a family with a solved
input. -/
theorem ConstRun.matrixQueries_le (A : ConstRun F τ gbar ε etaH etaD) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    (A.matrixQueries : ℝ) ≤ 1274019840 * gbar * ImprovedODEQueryBudget.queryShape s
      (ImprovedODEQueryBudget.theta (τ * etaH) (τ * etaD) gbar ε)
      (ImprovedODEQueryBudget.logBudget gbar ε) :=
  A.release.worstCost_le x sol hs

/-- **A run as an adaptive solver** of a family all of whose inputs have a solution. -/
def ConstRun.toTreeSolver (A : ConstRun F τ gbar ε etaH etaD)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    TreeSolver F (constOracle F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) A.slots A.degree A.J₀
      A.Jb) ℂ (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) ε :=
  A.release.toTreeSolver hsol A.i₀

/-- **Lower and upper bounds at the released runs on the `g = 1` families**: for runs on the
time, mixed and precision families with `η_H = 1`, `η_D = 0` (so `Θ = τ`), with
`S = √s τ + √(sτr) + r`: `c₀ S ≤ max(Q_T, Q_M, Q_P)`, `max(Q_T, Q_M, Q_P) ≤
1274019840 ḡ (√s τ + √(sτℓ) + ℓ)` with `ℓ = log(10⁴ ḡ/ε)`, `c₀ S ≤ max(V_T, V_M, V_P)` and
`max(V_T, V_M, V_P) ≤ max(Q_T, Q_M, Q_P)` (from `V ≤ Q` run by run, `ConstRun.valueQueries_le`).
-/
theorem herald_const_bounds (h : HSRange τ s ε)
    (AT : ConstRun (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0)
    (AM : ConstRun (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0)
    (AP : ConstRun (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε 1 0) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ∧
      max (AT.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) ≤
        1274019840 * gbar *
          ImprovedODEQueryBudget.queryShape s τ (ImprovedODEQueryBudget.logBudget gbar ε) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.valueQueries : ℝ) (max (AM.valueQueries : ℝ) AP.valueQueries) ∧
      max (AT.valueQueries : ℝ) (max (AM.valueQueries : ℝ) AP.valueQueries) ≤
        max (AT.matrixQueries : ℝ) (max (AM.matrixQueries : ℝ) AP.matrixQueries) := by
  have hsolT : ∀ x, ∃ sol,
      (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])).Solves x sol := fun x =>
    ((timeFamilyAt_inClass h le_rfl).solution x).elim fun sol hs => ⟨sol, hs.1⟩
  have hsolM : ∀ x, ∃ sol,
      (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Solves x sol := fun x =>
    ((mixedFamilyAt_inClass h le_rfl).solution x).elim fun sol hs => ⟨sol, hs.1⟩
  have hsolP : ∀ x, ∃ sol,
      (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])).Solves x sol := fun x =>
    ((precisionFamilyAt_inClass h le_rfl).solution x).elim fun sol hs => ⟨sol, hs.1⟩
  obtain ⟨hval, hlow⟩ := Herald.herald_max_const_tree h _ _ _ _ _ _ _ _ _ _ _ _
    AT.sources_public AM.sources_public AP.sources_public
    (AT.toTreeSolver hsolT) (AM.toTreeSolver hsolM) (AP.toTreeSolver hsolP)
  have e : ImprovedODEQueryBudget.theta (τ * 1) (τ * 0) gbar ε = τ := by
    rw [mul_one, mul_zero, ImprovedODEQueryBudget.theta_zero_dissipation]
  obtain ⟨solT, hsT⟩ := hsolT (fun _ => 0)
  obtain ⟨solM, hsM⟩ := hsolM (fun _ => 0)
  obtain ⟨solP, hsP⟩ := hsolP (fun _ => false)
  have uT := AT.matrixQueries_le _ solT hsT
  have uM := AM.matrixQueries_le _ solM hsM
  have uP := AP.matrixQueries_le _ solP hsP
  rw [e] at uT uM uP
  have cT : (AT.valueQueries : ℝ) ≤ AT.matrixQueries := by exact_mod_cast AT.valueQueries_le
  have cM : (AM.valueQueries : ℝ) ≤ AM.matrixQueries := by exact_mod_cast AM.valueQueries_le
  have cP : (AP.valueQueries : ℝ) ≤ AP.matrixQueries := by exact_mod_cast AP.valueQueries_le
  exact ⟨hlow, max_le uT (max_le uM uP), hval, max_le_max cT (max_le_max cM cP)⟩

/-- **Lower and upper bounds at the released runs on the PSD families**: for runs on the gadget
and scalar families with `η_H = 0`, `η_D = 1` (so `Θ = τ ℓ`): `psdConst (√(sτr) + r) ≤
max(Q_G, Q_S)`, `max(Q_G, Q_S) ≤ 1274019840 ḡ · queryShape(s, τℓ, ℓ)` with
`ℓ = log(10⁴ ḡ/ε)`, `psdConst (√(sτr) + r) ≤ max(V_G, V_S)` and `max(V_G, V_S) ≤ max(Q_G, Q_S)`
(from `V ≤ Q` run by run, `ConstRun.valueQueries_le`). -/
theorem psd_const_bounds (h : PsdRange τ s ε)
    (AG : ConstRun (psdSearchFamilyAt h) τ gbar ε 0 1)
    (AS : ConstRun (psdScalarFamilyAt h) τ gbar ε 0 1) :
    psdBound s τ ε ≤ max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) ∧
      max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) ≤
        1274019840 * gbar * ImprovedODEQueryBudget.queryShape s
          (τ * ImprovedODEQueryBudget.logBudget gbar ε) (ImprovedODEQueryBudget.logBudget gbar ε) ∧
      psdBound s τ ε ≤ max (AG.valueQueries : ℝ) (AS.valueQueries : ℝ) ∧
      max (AG.valueQueries : ℝ) (AS.valueQueries : ℝ) ≤
        max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) := by
  have hg0 : Real.sqrt 2 ≤ Real.sqrt 2 := le_rfl
  have hsolG : ∀ x, ∃ sol, (psdSearchFamilyAt h).Solves x sol := fun x =>
    ((ODELowerBoundExtensions.Psd.psdSearchFamilyAt_inClass h hg0).solution x).elim
      fun sol hs => ⟨sol, hs.1⟩
  have hsolS : ∀ x, ∃ sol, (psdScalarFamilyAt h).Solves x sol := fun x =>
    ((ODELowerBoundExtensions.Psd.psdScalarFamilyAt_inClass h hg0).solution x).elim
      fun sol hs => ⟨sol, hs.1⟩
  obtain ⟨hval, hlow⟩ := Psd.psd_max_const_tree h _ _ _ _ _ _ _ _
    AG.sources_public AS.sources_public (AG.toTreeSolver hsolG) (AS.toTreeSolver hsolS)
  have e : ImprovedODEQueryBudget.theta (τ * 0) (τ * 1) gbar ε =
      τ * ImprovedODEQueryBudget.logBudget gbar ε := by
    rw [ImprovedODEQueryBudget.theta, mul_zero, mul_one, zero_add]
  obtain ⟨solG, hsG⟩ := hsolG (fun _ => 0)
  obtain ⟨solS, hsS⟩ := hsolS (fun _ => false)
  have uG := AG.matrixQueries_le _ solG hsG
  have uS := AS.matrixQueries_le _ solS hsS
  rw [e] at uG uS
  have cG : (AG.valueQueries : ℝ) ≤ AG.matrixQueries := by exact_mod_cast AG.valueQueries_le
  have cS : (AS.valueQueries : ℝ) ≤ AS.matrixQueries := by exact_mod_cast AS.valueQueries_le
  exact ⟨hlow, max_le uG uS, hval, max_le_max cG cS⟩

end

end ConstantODELowerBound.Runs
