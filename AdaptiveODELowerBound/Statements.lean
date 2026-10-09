import AdaptiveODELowerBound.Retry
import AdaptiveODELowerBound.Release.Bridge

set_option autoImplicit false

/-!
# Dissipative-ODE lower bounds for adaptive solvers: paper-to-Lean entry point

The lower bounds of Section `part:odel` of the manuscript (Section `odel:sec:main` from line
4091) are formalised in `SparseLowerBounds.ODE` for single heralded programs and in
`ODELowerBoundExtensions` for single programs and the release's bounded retry protocols. This
library proves them for **adaptive solvers**, the protocol model of the adaptive
Hamiltonian-simulation lower bound, over the sampled-time access **with inverses and controls**
(line 4106), and adds a named lemma for the reduction of inverse and controlled value calls to
Boolean queries (lines 4289-4294). All declarations below are in the namespace
`AdaptiveODELowerBound`.

* Theorem `odel:thm:combined` (lines 4133-4145, proof 4437-4445): `combined_max_tree` (max form
  over the sampled-time access), `combined_max_cost_tree` (max form over realised value counts
  of either access shape) and `combined_tree` (family form); over the physical oracle of the
  released general-mesh solver, `Release.combined_max_release_tree` (per-family forms
  `Release.joint_release_tree`, `mixed_release_tree`, `precision_release_tree`).
* Theorem `odel:thm:joint` (lines 4296-4304) and Lemma `odel:lem:outer` (line 4181):
  `Joint.joint_witness_tree`, `Joint.joint_forces_tree`, `Joint.outer_count_ge_tree`.
* Remark `odel:rem:homogeneous` (line 4343): `Joint.hom_witness_tree`, `Joint.hom_forces_tree`.
* Lemma `odel:lem:herald` and eq. `odel:eq:hsbound` (lines 4393-4406): `herald_max_tree`,
  `herald_max_cost_tree`, `herald_witness_tree`, and the fourth sentence of Theorem
  `odel:thm:combined` (the two precision terms are witnessed by homogeneous
  constant-coefficient families with `D = 0`, `g = 1`), `precision_terms_witness_tree`.
* Theorem `odel:thm:psd` (lines 4452-4466, eq. `odel:eq:psd`): `Psd.psd_tree` (family form),
  `Psd.psd_max_tree`, `Psd.psd_max_cost_tree`; eq. `odel:eq:psdmixedlocal` (line 4543) is
  `Psd.psd_search_forces_local_tree`.
* The padding remarks (maximum sparsity exactly `s`, common dimension, qubit registers; lines
  4335-4340 and 4437-4445): `Padding.combined_pad_tree`, `Padding.combined_common_dimension_tree`,
  `Padding.combined_qubit_register_tree`, `Padding.joint_witness_pad_tree`,
  `Padding.joint_common_dimension_tree`, `Padding.joint_qubit_register_tree`,
  `Padding.herald_witness_pad_tree`.
* Inverse and controlled calls (lines 4105-4108, 4289-4294, and lines 2594-2597 for the
  Hamiltonian families): `Access.implementsOn_callFamily`, with the instances
  `Access.implementsOn_calls_joint`, `Access.implementsOn_calls_hom` (at most two Boolean
  membership queries per value call, none per location call), the public locators
  `Access.calls_locator_const_joint`, `Access.calls_locator_const_hom`, and the admissibility
  of every call form of the spectated native primitives, `Access.admissible_callFamily_spec`.
* Retry-protocol forms: `psd_retry`, `hom_witness_retry`, `joint_witness_pad_retry`,
  `herald_witness_pad_retry`, `combined_pad_retry`, `joint_common_dimension_retry`,
  `joint_qubit_register_retry`, `combined_common_dimension_retry`,
  `combined_qubit_register_retry`.

**Algorithm model** (lines 4105-4118; adaptivity, line 2673). `Model.TreeSolver F O Fl E G ε`:
an adaptive protocol `SparseLinearSystems.Protocol.Tree O Fl E` over a labelled oracle family
`O` on the inputs of the family `F` (a finite classical decision tree of fresh measured runs,
branching on the outcomes, then a final fresh-trial protocol that heralds its output in `E`),
an isometric readout `E → ℂ^N ⊗ G`, success mass at least `2/3` on every input and, for every
solution, conditional output within trace distance `ε` of `x(T)/‖x(T)‖` (observable form,
`AdaptiveHamiltonianLowerBound.DensityAccurate`). It mirrors
`ODELowerBoundExtensions.Release.RetrySolver` field for field. The flag space `Fl` is any
Hilbert space, `E` is finite-dimensional, the garbage `G` is any Hilbert space. A retry protocol
is the tree `Tree.final` (`Model.retryToTree`, the same counts, `Model.worstCost_retryToTree`),
so every tree witness is a retry witness and a single-program witness
(`Model.treeWitnesses_retryWitnesses`, `Model.treeWitnesses_witnesses`).

**Access and count.** `Model.TreeForces F ε b`: every adaptive solver over the sampled-time
access `F.access ι` of `SparseLowerBounds.ODE`, and every adaptive solver over its call forms
`Access.callFamily (F.access ι)` (labels `L × CallForm`: plain `1 ⊗ O_l`, inverse `1 ⊗ O_l†`,
controlled `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l`, controlled inverse; the controlled operator is the
package's identity mask `SparseHamiltonian.MaskedProgram.masked`), with any branch register `ι`,
flag, output and garbage spaces (types in `Type`), makes at least `b` value calls
(`Tree.worstCost valueWeight`, with `fun c => valueWeight c.1` on the call forms) and at least
`b` calls in total (`Tree.worstCost (fun _ => 1)`) in the worst case over all transcripts; every
run, attempt, inverse call and controlled call is counted.
`Model.TreeWitnesses F τ ḡ ε b`: `F` is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and
tree-forces `b`. Over the released solver's oracle (`ODELowerBoundExtensions.Release.meshOracle`,
any placement of mesh pieces into stages, public source interfaces
`ODELowerBoundExtensions.Release.PublicSources`) the counts are
`Tree.worstCost (matrixWeight valueWeight)` and `Tree.worstCost (matrixWeight (fun _ => 1))`.

**Hypotheses.** Those of the released statements that are lifted: `CombinedRange` (`s ≥ 32`,
`τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`), `JointRange` (`s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`),
`HomRange` (`s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20 (1 + log ḡ)`, `0 < ε ≤ 1/64`), `HSRange` (`τ ≥ 1`,
`s ≥ 32`, `0 < ε ≤ 1/64`) with `ḡ ≥ 1`, and `PsdRange` (`s ≥ 32`, `τ ≥ 1`, `0 < ε`,
`L = log(1/ε) ≥ 64τ`) with `ḡ ≥ √2`; `PsdRange` contains the manuscript's `τ ≥ 2`.

**Guarantees** (`r = hsR τ ε`).

* `combined_tree`: one of the joint, mixed and precision families tree-witnesses
  `combinedConst (ḡ √s τ + √(sτr) + r)`, `combinedConst = log 2/(8192π)`;
  `combined_max_tree`, `combined_max_cost_tree`: the same bound is at most the largest of the
  three worst-case value counts.
* `Release.combined_max_release_tree`: the same bound for the value counts and for the matrix
  counts of adaptive solvers over the released solver's oracle.
* `Joint.joint_witness_tree`: `ḡ √s τ/400`; `Joint.hom_witness_tree`: `ḡ √s τ/500`.
* `herald_witness_tree`: `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`.
* `Psd.psd_tree`: `psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`.
* `Padding.combined_common_dimension_tree`: for every `Nd` at least the three dimensions, the
  three families padded to dimension exactly `Nd` have maximum sparsity exactly `s` (the joint
  family with the dense block, `dense = true`), and one of them tree-witnesses the combined
  bound; `Padding.combined_qubit_register_tree`: `Nd = 2^q` for every `q` with `3 ḡ² s ≤ 2^q`
  and `4 s (τ + r + 1) ≤ 2^q`.
* `Access.implementsOn_callFamily`: if every label `l` of a unitary family is implemented on an
  encoding by at most `w l` queries of a Boolean phase oracle, then every call form of every
  label is implemented by at most `w l` queries of one Boolean phase oracle (`callBoolean P`) on
  one encoding (`callEncoding Enc`).

The instance properties are the released lemmas: in `SparseLowerBounds.ODE`,
`jointFamily_skew` (`D = 0`), `jointFamilyAt_g` and `joint_instance_props`
(`g = √M ∈ [ḡ/√2, ḡ]`, dimension at most `3 ḡ² s`) and `hamFamily_props`;
`SparseLowerBounds.Hamiltonian.hard_instances`; in `ODELowerBoundExtensions`,
`Homogeneous.homFamily_g`, `Homogeneous.hom_instance_props`, `Psd.psdSearchFamilyAt_props`,
`Psd.psdScalarFamilyAt_props`, `Padding.jointPadFamilyAt_g` and `Padding.herald_pad_props`.

**Proof map.** Module paths are relative to `AdaptiveODELowerBound/`.

* `Access/Calls`, `Access/Control`: the call family and its unitarity; the controlled program
  is the package's mask compiler with the identity mask (`implementsOn_plainForm`,
  `implementsOn_controlledForm`, `implementsOn_active`, `activeEmbed`, `flipD`, `alignCtrl`);
  `implementsOn_callFamily`.
* `Access/HardCalls`, `Access/Admissible`: the joint and homogeneous instances and the
  admissibility of the call forms of `specOracles`.
* `Model/Solver`: `TreeSolver`, `TreeForces`, `TreeWitnesses`, `TreeCost`, the max-to-family
  steps `treeForces_of_cost`, `forces_or_of_cost₂`, `forces_or_of_cost₃`, and the containments.
* `Bound`: `combinedBound_le_max`, the arithmetic of every max form.
* `Adversary/Weighted`, `Adversary/Kernel`, `Adversary/Purify`, `Adversary/Decision`: a
  positive-weight adversary for trees (weighted multiplier progress, the tree Gram kernel of the
  deferred-measurement purification, an explicit purification and the decision bound
  `tree_decision_count_ge`).
* `Joint/General`, `Joint/Families`: `outer_count_ge_tree`, `outer_general_tree`,
  `joint_general_tree` and the joint and homogeneous family bounds.
* `Herald/Transfer`, `Theorem`: the `g = 1` families through
  `AdaptiveHamiltonianLowerBound.time_tree`, `mixed_tree`, `precision_tree`
  (`Herald.treeForces_of_ham`), and the assembly.
* `Psd/Transfer`, `Psd/Theorem`: the positive semidefinite families by the weight method
  (`psd_search_tree_general`, `psd_scalar_tree_general`, `psdAmp_le_one`,
  `psd_scalar_forces_half_tree`).
* `Padding/Readout`, `Padding/Joint`, `Padding/Herald`, `Padding/Combined`: the padded families
  (`treeAccurate_of_zeroPad`, `valueCalls_of_hardCost_tree`).
* `Release/Bridge`: the released solver's oracle (`worstCost_value_le_matrix_tree`).
* `Retry`: the retry-protocol forms.

Every theorem of the library, and every `Prop`-valued field of `Model.TreeSolver` and
`Model.TreeWitnesses`, is axiom-audited in `AdaptiveODELowerBound/Audit.lean`.

**Formalisation choices.**

* The access shapes are the sampled-time access and its call forms, which realises lines
  4105-4106 (inverses and controls). The one-stage families also admit any
  `AdaptiveHamiltonianLowerBound.Access.Admissible` labels (`Herald.treeForces_of_ham`,
  `Psd.treeForces_of_heat` and the `*_tree_general` statements); `Admissible` over the inputs
  does not cover the time-addressed calls of the multi-stage families, so `TreeForces` fixes the
  two shapes. For the multi-stage families a call that applies different labels or forms on
  different branches (one `AdaptiveHamiltonianLowerBound.Access.NativeCall`) is therefore not one
  call but a product of controlled calls, at most two of them value calls, so such algorithms
  are covered with half the constants (a reduction that is not formalised).
* No combined max form over an arbitrary oracle family is stated; it follows from
  `Joint.joint_general_tree`, `AdaptiveHamiltonianLowerBound.mixed_tree_general`,
  `precision_tree_general` and `combinedBound_le_max`.
* `TreeCost` (a realised worst-case value count of a solver of either shape) is bookkeeping
  over `Tree.worstCost`; with two access shapes the family forms are derived from max forms over
  realised counts.
* `Access.implementsOn_callFamily` has no isometry hypothesis on the encoding. Controls are
  single-qubit controls on the extra register of the call-form workspace `ℂ^Bool ⊗ W`; a control
  on another qubit is a conjugation by known swaps, and multi-controls reduce to single controls
  with free known gates and one ancilla in `ι`. The query-control register is `Bool`, active at
  `true` (`activeEmbed`), the convention of the identity-mask compiler.
* The joint and homogeneous families are bounded by a new positive-weight adversary for trees,
  with the constants of the retry and single-program versions (`1/400`, `1/500`); the released
  retry adversary, in which all attempts run non-adaptively, does not extend to branching
  trees. It needs finite-dimensional workspaces, as the retry version; the sampled-time
  workspaces, their call-form spaces and the released physical space are finite-dimensional.
* The positive semidefinite families are bounded by the weight method of the adaptive
  Hamiltonian lower bound (one growth factor per value call) instead of the Boolean
  small-correlation lemma, so the general bounds `(log 2/96) √(mnu)` and `n/2` on value calls
  equal the released Boolean-cost bounds (`ODELowerBoundExtensions.Psd.psd_search_cost`,
  `psd_scalar_cost`) and are twice the value-call bounds derived from them; the manuscript's
  constant `(log 2/192) √(mnu)` of eq. `odel:eq:psdmixedlocal` is
  `Psd.psd_search_forces_local_tree`, and the downstream constants are the released ones.
* Hypotheses are those of the released theorems, not the manuscript's (for example `τ ≥ 1` in
  `PsdRange`, where the manuscript has `τ ≥ 2`).
* The workspace universe of `Herald.treeForces_of_ham` and `Psd.treeForces_of_heat` is
  `Type (max uN uZ)`, that of the sampled-time workspaces and their call forms; padding
  registers are `Type*`, as in the released statements.
* `TreeForces` quantifies over branch registers, flag, output and garbage spaces in `Type`, as
  the released `Forces` and `RetryForces`. A tree has one flag space `Fl` for all its measured
  runs, so all their success projectors `F F†` have rank `dim Fl`; a run with a projector of
  smaller rank is padded to that rank on a spare qubit of `ι` that the run never populates.
* Over the released solver's oracle there are only max forms, as in the released library: a
  run there carries per-run parameters. The comparison with eq. `odel:eq:upper` (line 4148) is
  `ODELowerBoundExtensions.Release.release_theta` (in `ODELowerBoundExtensions/Release/Theta.lean`,
  outside this library's imports); a release run is a retry protocol, hence the
  tree `Tree.final`, so its lower half is also `Release.combined_max_release_tree` at
  `Model.retryToTree`, with the same counts; this is not restated.
* Plain and inverse call forms are `SparseLowerBounds.Joint.fiber`, the all-active mask; only
  the controlled forms use the identity mask.

**Not formalised.**

* The application to the constant-coefficient released solver
  `SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem `ode:thm:main`, line 4115); only the
  general-mesh solver of `ode:thm:time` is connected, on the same hard families.
* Controlled calls of the released physical oracle (`Access.callFamily` of
  `ODELowerBoundExtensions.Release.meshOracle`; the released solver does not use them); family
  forms over that oracle; and released-oracle forms of Theorem `odel:thm:psd`, Remark
  `odel:rem:homogeneous` and the padded families.
* Adaptive forms of Lemma `odel:lem:dyson` and eq. `odel:eq:fixed`: they are upper bounds, and a
  retry solver is a tree (`Model.retryToTree`), so
  `ODELowerBoundExtensions.Dyson.no_retry_witnesses` with `Model.treeWitnesses_retryWitnesses`
  also excludes tree witnesses of `c ḡ √s τ log(ḡ/ε)`; this consequence is not restated here.
* Infinite-dimensional workspaces in the tree adversary; measurements inside a run followed by
  classically controlled operations, and measurements with more than two outcomes (as for the
  adaptive Hamiltonian lower bound).
* Gate, workspace and classical circuit-generation costs.

**Provenance.** No result from another paper is used. The libraries `SparseHamiltonian`,
`SparseODE`, `SparseLinearSystems`, `LinearSystemLowerBound`, `SparseLowerBounds` (with
`ODELowerBounds`), `AdaptiveHamiltonianLowerBound`, `LowerBoundRemarks`,
`TimeDependentExtensions` and `ODELowerBoundExtensions` are only imported; no released module
is changed. `ODELowerBoundExtensions/Statements.lean`, `SparseLowerBounds/ODE/Statements.lean`
and `SparseLowerBounds/ODE/Model.lean` predate this library: their notes that controlled oracle
calls are covered only by a documented reduction, that Theorem `odel:thm:psd`, Remark
`odel:rem:homogeneous` and the padded families hold only for single programs, and that adaptive
solvers (and, for the joint family, general adaptive trees) are outside them, are superseded
here for the sampled-time access. Line numbers in this guide refer to the manuscript used by
this library; the module docstrings of the imported libraries cite another manuscript version,
and the paper labels are the stable references.
-/
