import ConstantODELowerBound.Instances

set_option autoImplicit false

/-!
# ODE lower bounds for the released constant-coefficient solver: paper-to-Lean entry point

Section `odel:sec:main` of the manuscript states that the dissipative-ODE lower bounds apply to
both released ODE solvers (lines 4114-4115: "The lower bounds thus apply to Theorems
`ode:thm:main` and `ode:thm:time`"). The libraries `ODELowerBoundExtensions` and
`AdaptiveODELowerBound` connect them to the general-mesh solver of Theorem `ode:thm:time`. This
library connects them to the released constant-coefficient solver
`SparseHamiltonian.ODECompleteEndpoint.solver` of Theorem `ode:thm:main` (lines 3013-3033), on
the hard families that are constant-coefficient equations: the three `g = 1` Hamiltonian
families of eq. `odel:eq:hsbound` and Lemma `odel:lem:herald` (lines 4392-4406) and the two
positive semidefinite families of Theorem `odel:thm:psd` (lines 4452-4466). All declarations
below are in the namespace `ConstantODELowerBound`.

* Eq. `odel:eq:hsbound` and Lemma `odel:lem:herald` over the released solver's oracle:
  `Herald.herald_max_const_tree` (adaptive solvers, max form) and
  `Herald.herald_max_const_retry` (retry protocols), from the per-family bounds
  `Herald.time_const_tree`, `Herald.mixed_const_tree`, `Herald.precision_const_tree`.
* Theorem `odel:thm:psd` over the released solver's oracle: `Psd.psd_max_const_tree` and
  `Psd.psd_max_const_retry`, from `Psd.psd_search_const_tree` (eq. `odel:eq:psdmixedlocal`) and
  `Psd.psd_scalar_const_tree`.
* Theorem `ode:thm:main` on the hard families: `Solver.constProtocol_of_certificate` (every
  certificate family of the released solver's positive-time branch on `constData F` gives a
  released protocol over the released oracle) and `Solver.exists_constProtocol` (the released
  solver takes that branch, with its hypotheses), the runs `Runs.ConstRun`, and the two-sided
  statements at the runs `Runs.herald_const_bounds`, `Runs.psd_const_bounds`.
* Non-vacuity: `Instances.herald_const_runs_exist`, `Instances.herald_const_bracket`,
  `Instances.psd_const_runs_exist`.
* The access model (lines 4105-4109): `Normal.physicalOracle_normal_form` (every matrix label
  of the released oracle is one native call in a fixed isometric layout) and
  `Access.searchGrowth_const` (search-weight growth on hard data).

**Released solver and oracle.** On a one-stage family `F : SparseLowerBounds.ODE.Family X N Z 1
s` the released solver runs on the stage-`0` data `Oracle.constData F` (generator `-G_0(x)`, no
time address) and calls the physical oracle family
`Oracle.constOracle F ι Nm Tsl d J₀ Jb = ODEFinalNativeSource.physicalOracle (constData F) Nm
Tsl d J₀ Jb`, labelled by `Query ⊕ Bool` (matrix calls and the two source interfaces), with
branch register `ι`, mesh size `Nm`, slot count `Tsl`, degree `d` and source interfaces `J₀`,
`Jb`. Source interfaces are public (`Oracle.PublicConstSources J₀ Jb`: unitary and
input-independent, lines 4119-4122).

**Algorithm model.** `AdaptiveODELowerBound.Model.TreeSolver F O Fl E G ε` over
`O = constOracle F ι Nm Tsl d J₀ Jb`, for any branch register, mesh size, slot count, degree and
public source interfaces: an adaptive protocol `SparseLinearSystems.Protocol.Tree O Fl E` (a
finite classical tree of fresh measured runs, branching on the outcomes, then a heralded final
protocol), an isometric readout `E → ℂ^N ⊗ G`, success mass at least `2/3` on every input and
conditional output within trace distance `ε` of `x(T)/‖x(T)‖` in the observable form
`AdaptiveHamiltonianLowerBound.DensityAccurate` (lines 4111-4113). Retry protocols
(`ODELowerBoundExtensions.Release.RetrySolver`) are the trees `Tree.final`
(`AdaptiveODELowerBound.Model.retryToTree`), with the same counts. A run of the released solver
(`Runs.ConstRun F τ ḡ ε η_H η_D`) consists of public source interfaces, a slot count, a degree,
a system index `i₀` and a released four-attempt protocol (`Protocol.ConstProtocol`) over the
released oracle with branch register `Solver.RunIndex F τ ḡ ε`, mesh size
`Solver.runMesh F τ ḡ ε`, `Θ = theta(τ η_H, τ η_D, ḡ, ε) = τ η_H + τ η_D ℓ`,
`ℓ = logBudget(ḡ, ε) = log(10⁴ ḡ/ε)` and `g = ḡ`; it is a retry solver, hence a tree solver
(`Runs.ConstRun.toTreeSolver`, readout `Hamiltonian.endpointReadout 1 i₀`).

**Counts.** Two worst-case counts over all transcripts, every run, attempt and inverse call
counted, source calls weighing `0`: the value count
`Tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)` and the released matrix count
`Tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))` (row, column and value calls).
At a run these are `Runs.ConstRun.valueQueries ≤ Runs.ConstRun.matrixQueries`
(`Runs.ConstRun.valueQueries_le`).

**Hypotheses.** Those of the lifted statements: `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`,
`0 < ε ≤ 1/64`), with `L ≥ 64τ` for the precision family and also `s ≥ 64n/τ` for the mixed
family (`n = precN τ ε`); `PsdRange τ s ε` (`s ≥ 32`, `τ ≥ 1`, `0 < ε`, `L = log(1/ε) ≥ 64τ`),
with `s ≥ 512n/τ` for the gadget family. `PsdRange` contains the manuscript's range `τ ≥ 2`
(line 4454, `ODELowerBoundExtensions.Psd.PsdRange.of_paper`). `Solver.exists_constProtocol`
keeps the hypotheses of the released solver: a family in the class at any row and column
bound `η` (`F.InClass η ḡ`), `T = τ > 0`, `0 < ε ≤ 1/2`, split bounds `η_H, η_D ≥ 0` on the
rows and columns of the Hermitian and dissipative parts of every generator, the branch
condition `η_H + R(ḡ, ε) η_D > 0`, unitary source interfaces and a unit seed mapped to
`x₀/‖x₀‖` and `b/‖b‖`; publicity of the source interfaces is required only of runs and of the
solvers of the lower bounds. `Solver.constProtocol_of_certificate` needs only the class
(`F.InClass η ḡ`), `T = τ`, the seed conditions, the certificate family and one solved input.
Non-vacuity needs `ḡ ≥ 1` on the `g = 1` families and `ḡ ≥ √2`
on the positive semidefinite families.

**Guarantees** (`r = hsR τ ε`, `S = √s τ + √(sτr) + r`, `Q` a matrix count, `V` a value count).

* `Herald.time_const_tree`: `(log 2/(192π)) √s τ ≤ V` on the time family;
  `Herald.mixed_const_tree`: `(log 2/(384√2)) √(sτr) ≤ V`; `Herald.precision_const_tree`:
  `r/32 ≤ V`, and `√(sτr)/(64√2) ≤ V` when `s < 64n/τ`; each also for `Q`.
* `Herald.herald_max_const_tree`, `Herald.herald_max_const_retry`: for any three solvers, each
  accurate on its own family, `c₀ S ≤ max(V_T, V_M, V_P)` and `c₀ S ≤ max(Q_T, Q_M, Q_P)`,
  `c₀ = log 2/(4096π)`.
* `Psd.psd_search_const_tree`: `(log 2/(1536√2)) √(sτr) ≤ V` on the gadget family;
  `Psd.psd_scalar_const_tree`: `r/32 ≤ V`, and `√(sτr)/256 ≤ V` when `s < 512n/τ`.
* `Psd.psd_max_const_tree`, `Psd.psd_max_const_retry`: `psdConst (√(sτr) + r) ≤ max(V_G, V_S)`
  and `≤ max(Q_G, Q_S)`, `psdConst = log 2/(3072√2)`.
* `Runs.herald_const_bounds`: for runs on the time, mixed and precision families with
  `η_H = 1`, `η_D = 0` (so `Θ = τ`),
  `c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ 1274019840 ḡ (√s τ + √(sτℓ) + ℓ)`, `c₀ S ≤ max(V_T, V_M, V_P)` and
  `max(V_T, V_M, V_P) ≤ max(Q_T, Q_M, Q_P)` (from `V ≤ Q` run by run,
  `Runs.ConstRun.valueQueries_le`).
* `Runs.psd_const_bounds`: for runs on the two positive semidefinite families with `η_H = 0`,
  `η_D = 1` (so `Θ = τ ℓ`), `psdConst (√(sτr) + r) ≤ max(Q_G, Q_S)`,
  `max(Q_G, Q_S) ≤ 1274019840 ḡ (√s τ ℓ + √(s τ ℓ²) + ℓ)` (`queryShape(s, τℓ, ℓ)`), the same
  lower bound for the value counts and `max(V_G, V_S) ≤ max(Q_G, Q_S)` (from `V ≤ Q` run by run,
  `Runs.ConstRun.valueQueries_le`). The two halves are stated side by side; the manuscript
  proves no matching bound for this subclass (lines 4573-4578).
* `Instances.herald_const_bracket`: for `ḡ ≥ 1` runs on the three `g = 1` families exist, and
  they satisfy `c₀ S ≤ max(Q_T, Q_M, Q_P) ≤ 1274019840 ḡ (√s τ + √(sτℓ) + ℓ)`;
  `Instances.psd_const_runs_exist`: for `ḡ ≥ √2` runs on both positive semidefinite families
  exist.

**Proof map.** Module paths are relative to `ConstantODELowerBound/`.

* `Oracle`: `constData`, `constOracle`, `PublicConstSources`; the native primitives of
  `constData` (`oracles_constData_ham`, `oracles_constData_heat`) and the transfer of the hard
  access conditions (`hardAccess_constData_ham`, `hardAccess_constData_heat`).
* `Normal`: the outer layers of the released oracle as a spectator wrapper (`constWrap`,
  `isWrap_constWrap`, `physicalOracle_inl_eq`), `physicalOracle_normal_form` and the public
  source labels (`physicalOracle_inr_const`).
* `Solution`: a one-stage family as a constant-coefficient equation (`oneStage_T`,
  `oneStage_mass`, `constSolution_solves`, `endpoint_eq_constSolution`) and the split parts of
  Hermitian and accretive generators.
* `Access`: `searchGrowth_const` and its instances `searchGrowth_const_ham`,
  `searchGrowth_const_heat`, through `AdaptiveHamiltonianLowerBound.searchGrowth_admissible`.
* `Protocol`: `ConstProtocol`, its success, accuracy and query bound, and the retry and tree
  solvers it defines (`ConstProtocol.toRetrySolver`, `ConstProtocol.toTreeSolver`).
* `Solver`: `constProtocol_of_certificate` and `exists_constProtocol`, from the positive-time
  branch `ODECompleteEndpoint.PositiveOutcome` of the released solver.
* `Herald`, `Psd`: the lower bounds, from `AdaptiveHamiltonianLowerBound.time_tree_general`,
  `mixed_tree_general`, `precision_tree_general` and `AdaptiveODELowerBound.Psd`'s
  `psd_search_tree_general`, `psd_scalar_tree_general`, assembled by
  `SparseLowerBounds.Hamiltonian.assembly` and `ODELowerBoundExtensions.Psd.psd_assembly`.
* `Runs`, `Instances`: the runs, the two-sided statements and their non-vacuity.

Every theorem of the library, and every `Prop`-valued field of `Runs.ConstRun`, is
axiom-audited in `ConstantODELowerBound/Audit.lean`.

**Formalisation choices.**

* Only the constant-coefficient hard families are used: the time, mixed and precision families
  with `g = 1` and the two positive semidefinite families. The joint family of Theorem
  `odel:thm:joint` is time dependent, and the manuscript does not prove the joint `ḡ √s τ`
  bound for constant-coefficient equations (lines 4151-4155); the homogeneous variant of Remark
  `odel:rem:homogeneous` "is homogeneous but still time dependent; it is not a
  constant-coefficient reduction" (lines 4385-4387). In the constant class the time family is
  the only source of the `√s τ` term.
* The solvers here call the released oracle itself, with inverse calls, as the released solver
  does; this is the scope of `AdaptiveODELowerBound.Release.combined_max_release_tree` for the
  general-mesh solver. The call forms of `constOracle`
  (`AdaptiveODELowerBound.Access.callFamily`: controlled and controlled-inverse calls), padding
  to a common dimension and family forms over `constOracle` are in the library
  `PhysicalODELowerBound` (`Const.ConstForces`, `Const.herald_witness_const`,
  `Const.herald_common_dimension_const`, `Const.psd_const`).
* The lower bounds are stated for public source interfaces, as for the general-mesh solver;
  the released solver itself accepts any unitary source interfaces.
* The solver's input is `constData F`; the released certificate's target, the explicit
  solution, is identified with the family's endpoint by uniqueness
  (`Solution.endpoint_eq_constSolution`).
* `ConstRun` is a superset of the released solver's outputs: the protocol of the released
  solver's positive-time branch (`T = τ > 0`, `η_H + R(ḡ, ε) η_D > 0`), with public source
  interfaces that prepare `x₀/‖x₀‖` and `b/‖b‖` from a unit seed, is a run
  (`Solver.constProtocol_of_certificate`), and the structure requires neither the solver's
  preconditions, nor that `η_H`, `η_D` bound the generator, nor that the degree is the solver's
  output. This only strengthens the statements quantified over runs. Runs use the
  promise parameter `g = ḡ`.
* `Protocol.ConstProtocol`, `Runs.ConstRun`, `Normal.constWrap`,
  `Normal.physicalOracle_normal_form` and `Access.searchGrowth_const` are the counterparts, for
  the oracle `ODEFinalNativeSource.physicalOracle` and the workspace
  `ODEFinalNativeSource.Physical` of the constant-coefficient solver, of
  `ODELowerBoundExtensions.Release.ReleaseProtocol`, `Release.ReleaseRun`, `Release.outerWrap`,
  `Release.physicalOracle_normal_form` and `Release.searchGrowth_release_ham`, which are stated
  for the general-mesh oracle `Release.releaseOracle` and its workspace; the bodies agree except
  for the oracle and workspace types and the parameters (no refinement count; split bounds
  `η_H`, `η_D` in place of a ratio). `Protocol.ConstProtocol.worstCost_toTreeSolver` is
  `AdaptiveODELowerBound.Model.worstCost_retryToTree` at the released protocol.
* The lower halves are max forms over one solver per family: the families have different input,
  index and word types, so the bounds are not bounds on one program (lines 4443-4444: "It does
  not assert that one instance witnesses all terms").
* The two-sided statements are conjunctions of the lower bound and the released upper bound at
  the same runs. They are not `Θ` statements and contain no comparison within a factor `ℓ`;
  the comparison of lines 4147-4155 concerns the whole time-dependent class.
* The positivity of the LCHS cutoff on the positive semidefinite runs comes from
  `ODEGaussianParameters.width_ge_two` and `ODEGaussianParameters.cutoff_le_radius`.
* Hypotheses are those of the lifted statements, not the manuscript's (`τ ≥ 1` in `PsdRange`,
  where the manuscript has `τ ≥ 2`).

**Not formalised.**

* In this library: controlled calls of the released constant-coefficient oracle, padding to a
  common known dimension and family forms over that oracle (they are in
  `PhysicalODELowerBound`). The positive semidefinite families used here already carry the
  dense padding to maximum sparsity exactly `s`
  (`ODELowerBoundExtensions.Psd.psd_family_hardInstance`), and the `g = 1` families attain
  sparsity `s`.
* The joint `ḡ √s τ` lower bound for constant-coefficient equations, which the manuscript does
  not prove (lines 4151-4155), and any comparison within a factor `ℓ` for `ode:thm:main`, or any
  matching upper and lower bound for the positive semidefinite subclass (lines 4573-4578).
* Remark `odel:rem:homogeneous` for `ode:thm:main` (its family is time dependent).
* The `O(ḡ)` input and source preparation calls of `ode:thm:main` are not counted (source labels
  weigh `0`).
* Measurements inside a run followed by classically controlled operations, measurements with
  more than two outcomes, and circuit, workspace and classical costs (as for the adaptive ODE
  lower bounds).

**Provenance.** No result from another paper is used. The libraries `SparseHamiltonian`,
`SparseODE`, `SparseLinearSystems`, `SparseLowerBounds`, `ODELowerBoundExtensions`,
`AdaptiveHamiltonianLowerBound` and `AdaptiveODELowerBound` are only imported; no released
module is changed.
`SparseLowerBounds/ODE/Statements.lean`, `ODELowerBoundExtensions/Statements.lean` and
`AdaptiveODELowerBound/Statements.lean` predate this library: their notes that the
constant-coefficient solver of `ode:thm:main` is not connected to the lower bounds (the first
says that neither released solver is, the other two that only the general-mesh solver of
`ode:thm:time` is) are superseded here for the `g = 1` Hamiltonian families and the positive
semidefinite families; the joint `ḡ √s τ` term remains outside. Line numbers in this guide and
in the module docstrings refer to an earlier manuscript version (in Part `odel` they are about
550 lines lower than in the v15 manuscript accompanying this release); the paper labels are the
stable references.
-/
