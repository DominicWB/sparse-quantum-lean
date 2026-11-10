import PhysicalODELowerBound.Mesh.Combined
import PhysicalODELowerBound.Mesh.Psd
import PhysicalODELowerBound.Const.Herald
import PhysicalODELowerBound.Const.Psd

set_option autoImplicit false

/-!
# ODE lower bounds over the released solvers' physical oracles: paper-to-Lean entry point

Section `odel:sec:main` of the manuscript states the access model of the dissipative-ODE lower
bounds ("The value oracle and in-place row and column locators have the canonical reversible access,
including inverses, controls and coherent time addresses where needed") and that "the lower bounds
apply to the upper bounds of the preceding section". The library `AdaptiveODELowerBound` proves the
lower bounds against adaptive solvers over the sampled-time access of the lower-bound class, with
inverse and controlled calls, and connects Theorem `odel:thm:combined` to the physical oracle of the
released general-mesh solver (`AdaptiveODELowerBound.Release.combined_max_release_tree`);
`ConstantODELowerBound` connects the `g = 1` and positive semidefinite families to the physical
oracle of the released constant-coefficient solver, without controlled calls. This library proves,
over the released general-mesh physical oracle and its controlled and controlled-inverse call forms,
Theorem `odel:thm:psd`, Proposition `odel:rem:homogeneous`, eq. `odel:eq:hsbound` and Lemma
`odel:lem:herald`, Theorem `odel:thm:joint` and Theorem `odel:thm:combined`, and over the released
constant-coefficient physical oracle and its call forms the constant-coefficient results (Theorem
`odel:thm:psd`, eq. `odel:eq:hsbound` and Lemma `odel:lem:herald`), all in family form; over the
general-mesh oracle also the padded joint families (dense block and zero padding, proof of
`odel:thm:joint`) and, over both oracles, the zero-padded `g = 1` families (proof of
`odel:thm:combined`). All declarations below are in the namespace `PhysicalODELowerBound`.

* Theorem `odel:thm:psd` (eq. `odel:eq:psd`): `Mesh.psd_mesh` (general-mesh oracle) and
  `Const.psd_const` (constant-coefficient oracle); max forms `Mesh.psd_max_cost_mesh`,
  `Const.psd_max_cost_const`; the max form of `ConstantODELowerBound`, restated:
  `Const.psd_max_const_tree_of_const`.
* Proposition `odel:rem:homogeneous`: `Mesh.hom_forces_mesh`, `Mesh.hom_witness_mesh`.
* Theorem `odel:thm:joint` and its padding: `Mesh.joint_forces_mesh`,
  `Mesh.joint_witness_mesh`, `Mesh.joint_forces_pad_mesh`, `Mesh.joint_witness_pad_mesh`,
  `Mesh.joint_common_dimension_mesh`, `Mesh.joint_qubit_register_mesh`.
* Eq. `odel:eq:hsbound` and Lemma `odel:lem:herald`: `Mesh.herald_witness_mesh`,
  `Mesh.herald_witness_pad_mesh`, `Const.herald_witness_const`, `Const.herald_witness_pad_const`,
  `Const.herald_common_dimension_const`, `Const.herald_qubit_register_const`; max forms
  `Mesh.herald_max_cost_mesh`, `Mesh.herald_max_cost_pad_mesh`, `Const.herald_max_cost_const`,
  `Const.herald_max_cost_pad_const`; the max form of `ConstantODELowerBound`, restated:
  `Const.herald_max_const_tree_of_const`.
* Theorem `odel:thm:combined` and the padding of its proof: `Mesh.combined_mesh`,
  `Mesh.combined_pad_mesh`, `Mesh.combined_common_dimension_mesh`,
  `Mesh.combined_qubit_register_mesh`; max forms `Mesh.combined_max_cost_mesh`,
  `Mesh.combined_max_cost_pad_mesh`; the released max form, restated:
  `Mesh.combined_max_release_tree_of_mesh`. Its fourth sentence (Theorem `odel:thm:combined`, the
  precision terms witnessed by `g = 1` families): `Mesh.precision_terms_witness_mesh`,
  `Mesh.precision_terms_witness_pad_mesh`, `Const.precision_terms_witness_const`,
  `Const.precision_terms_witness_pad_const`.
* Controlled and inverse calls (the construction before Theorem `odel:thm:joint`: a value query
  "uses at most two membership queries, also for inverse and controlled calls"):
  `Access.implementsOn_mesh_calls` (Boolean programs for every call form of the general-mesh
  oracle), `Access.searchGrowth_mesh_calls`, `Const.searchGrowth_const_calls` and
  `Access.searchGrowth_callFamily` (search-weight growth of every call form).
* Retry protocols, released protocols and the released runs: `Mesh.MeshForces.retry`,
  `Mesh.MeshForces.retry_calls`, `Mesh.MeshForces.releaseProtocol`, `Mesh.MeshForces.releaseRun`,
  `Const.ConstForces.retry`, `Const.ConstForces.retry_calls`, `Const.ConstForces.constRun`.

**Oracles.** The general-mesh oracle is
`ODELowerBoundExtensions.Release.meshOracle F σ ι Nsl d J₀ J_b`, the physical oracle of the
released solver `TimeDependentExtensions.ODE.solver` on the data of a family
`F : SparseLowerBounds.ODE.Family X N Z K s` along a placement `σ : Fin M → Fin K` of mesh pieces
into stages, with spectator index `ι`, slot count `Nsl`, degree `d` and public source interfaces
(`ODELowerBoundExtensions.Release.PublicSources J₀ J_b`). The constant-coefficient oracle is
`ConstantODELowerBound.Oracle.constOracle F ι Nm Tsl d J₀ J_b` on a one-stage family (`K = 1`),
with public source interfaces `ConstantODELowerBound.Oracle.PublicConstSources J₀ J_b`. Each is
used in two access shapes: the oracle family itself (with inverse calls) and its call forms
`AdaptiveODELowerBound.Access.callFamily` (plain, inverse, controlled
`SparseHamiltonian.MaskedProgram.masked (fun c => c)` and controlled inverse, on control ⊗
workspace), every call form weighted as its label.

**Algorithm model.** `AdaptiveODELowerBound.Model.TreeSolver F O Fl E G ε`: an adaptive protocol
`SparseLinearSystems.Protocol.Tree O Fl E` (fresh measured runs, branching on the outcomes, then a
heralded final protocol), an isometric readout, success mass at least `2/3` on every input and
conditional output within trace distance `ε` of the normalised endpoint
(`AdaptiveHamiltonianLowerBound.DensityAccurate`, Section `odel:sec:main`). Retry protocols
(`ODELowerBoundExtensions.Release.RetrySolver`) are the trees `Tree.final`
(`AdaptiveODELowerBound.Model.retryToTree`).

**Forcing.** `Mesh.MeshForces F ε b`: for every placement, spectator index, slot count, degree,
public source interfaces and flag, output and garbage spaces, every tree solver over the
general-mesh oracle and every tree solver over its call forms make at least `b` value calls
(`Tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)`) and at least `b` matrix calls
(`matrixWeight (fun _ => 1)`) in the worst case over all transcripts. `Mesh.MeshWitnesses F τ ḡ ε
b`: `F.InClass 1 ḡ`, `F.T = τ` and `MeshForces F ε b`. `Mesh.MeshCost F ε q`: `q` is the
worst-case value count of some such solver. `Const.ConstForces`, `Const.ConstWitnesses`,
`Const.ConstCost` are the same over the constant-coefficient oracle (any branch register, mesh
size, slot count, degree, public source interfaces).

**Hypotheses.** Those of the lifted statements: `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`,
`0 < ε ≤ 1/64`), with `L ≥ 64τ` for the precision family and also `s ≥ 64n/τ` for the mixed
family; `PsdRange τ s ε` (`s ≥ 32`, `τ ≥ 1`, `0 < ε`, `L = log(1/ε) ≥ 64τ`; the manuscript has
`τ ≥ 2`), with `s ≥ 512n/τ` for the gadget family; `JointRange s τ ḡ ε` (`s ≥ 4`, `τ ≥ 4`,
`ḡ ≥ 2`, `0 < ε ≤ 1/64`); `HomRange s τ ḡ ε` (`s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)`,
`0 < ε ≤ 1/64`); `CombinedRange s τ ḡ ε` (`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`). The
family forms on `HSRange` need `ḡ ≥ 1`, those on `PsdRange` need `ḡ ≥ √2`.

**Guarantees** (`r = hsR τ ε`, `n = precN τ ε`; each bound holds for the value count and for the
matrix count, in both access shapes).

* `Mesh.psd_mesh`, `Const.psd_const`: on `PsdRange`, for `ḡ ≥ √2`, the gadget or the scalar
  positive semidefinite family witnesses `psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`;
  per family `psdGadgetConst √(sτr)` for `s ≥ 512n/τ` (`psdGadgetConst = log 2/(1536√2)`),
  `r/32`, and `√(sτr)/256` for `s < 512n/τ` (`psd_search_forces_*`, `psd_scalar_forces_*`,
  `psd_scalar_forces_sqrt_*`). The families have `D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`,
  `1 ≤ g ≤ √2` and maximum sparsity exactly `s`.
* `Mesh.hom_witness_mesh`: on `HomRange` the homogeneous time-dependent family witnesses
  `ḡ √s τ / 500` (`homConst = 1/500`).
* `Mesh.joint_witness_mesh`: on `JointRange` the joint family witnesses `ḡ √s τ / 400`
  (`jointConst = 1/400`); `Mesh.joint_witness_pad_mesh`: the same for every dense flag and known
  padding `P`, with maximum sparsity exactly `s` when the dense block is present;
  `Mesh.joint_common_dimension_mesh`, `Mesh.joint_qubit_register_mesh`: dimension exactly `Nd` for
  every `Nd` at least the unpadded dimension, in particular `Nd = 2^q` when `3 ḡ² s ≤ 2^q`.
* `Mesh.herald_witness_mesh`, `Const.herald_witness_const`: on `HSRange`, for `ḡ ≥ 1`, one of
  the time, mixed and precision families (`D = 0`, `g = 1`) witnesses
  `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`; per family `(log 2/(192π)) √s τ`,
  `(log 2/(384√2)) √(sτr)`, `r/32` and `√(sτr)/(64√2)` when `s < 64n/τ`. The padded forms
  `*_pad_mesh`, `*_pad_const` hold for any known paddings; `Const.herald_common_dimension_const`
  and `Const.herald_qubit_register_const` pad to one common dimension `Nd`, in particular
  `Nd = 2^q` when `4 s (τ + r + 1) ≤ 2^q`, with maximum sparsity exactly `s`.
* `Mesh.combined_mesh`: on `CombinedRange` one of the joint, mixed and precision families
  witnesses `c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)` (`SparseLowerBounds.ODE.combinedBound`);
  `Mesh.combined_pad_mesh`, `Mesh.combined_common_dimension_mesh` and
  `Mesh.combined_qubit_register_mesh` (`3 ḡ² s ≤ 2^q` and `4 s (τ + r + 1) ≤ 2^q`) for the padded
  families. The precision terms `c₀ (√(sτr) + r)` alone are witnessed by a `g = 1` family
  (`precision_terms_witness_*`, on `HSRange` with `ḡ ≥ 1`).
* `Access.implementsOn_mesh_calls`: if the sampled-time access of `F` is implemented by a Boolean
  phase oracle with costs `w` on an isometric encoding, every call form of every label of the
  general-mesh oracle is implemented with at most `matrixWeight w` of its label queries; with the
  costs of the hard families a controlled or controlled-inverse value call costs at most two
  Boolean queries and a controlled location or source call none (with `w = hardCost`,
  `matrixWeight hardCost = 2 · matrixWeight valueWeight`,
  `ODELowerBoundExtensions.Release.matrixWeight_hardCost`; the hypothesis is met by the joint,
  homogeneous and padded joint families through the released certificates
  `SparseLowerBounds.ODE.implementsOn_joint`,
  `ODELowerBoundExtensions.Homogeneous.implementsOn_hom`,
  `ODELowerBoundExtensions.Padding.implementsOn_jointPad`, as in `Mesh.joint_forces_mesh`,
  `hom_forces_mesh`, `joint_forces_pad_mesh`).
* `Mesh.MeshForces.releaseRun`, `Const.ConstForces.constRun`: the bounds hold at every
  `ODELowerBoundExtensions.Release.ReleaseRun` (the released general-mesh solver's runs on
  families with `D = 0`: `ReleaseRun` fixes `Θ = τ` and
  `ODELowerBoundExtensions.Release.exists_releaseProtocol` needs `D = 0`, so it covers the joint,
  `g = 1` and padded families, not the positive semidefinite and homogeneous ones), at every
  released protocol of that solver at any parameters (`Mesh.MeshForces.releaseProtocol`), and at
  every run of the released constant-coefficient solver (`ConstantODELowerBound.Runs.ConstRun`,
  any split bounds `η_H`, `η_D`, so also on the positive semidefinite families), on a family all
  of whose inputs are solvable.

**Proof map.** Module paths are relative to `PhysicalODELowerBound/`.

* `Access/Growth`: `searchGrowth_callFamily` (every call form has the search-weight growth of its
  label: block diagonals and branch masks, adjoints for the inverse forms).
* `Access/MeshBoolean`: `implementsOn_mesh`, the generic form of
  `ODELowerBoundExtensions.Release.implementsOn_release_joint` for any family with a Boolean
  certificate, through `ODELowerBoundExtensions.Release.physicalOracle_normal_form`, and
  `implementsOn_mesh_calls` through `AdaptiveODELowerBound.Access.implementsOn_callFamily`.
* `Access/MeshGrowth`: `stageAccess_oneStage` and `searchGrowth_mesh`, the generic form of
  `ODELowerBoundExtensions.Release.searchGrowth_release_ham` for one-stage families with
  `AdaptiveHamiltonianLowerBound.Access.HardAccess` data.
* `Families/Herald`, `Families/Psd`: the `g = 1` and positive semidefinite bounds for one tree
  solver over any oracle with search-weight growth, from
  `AdaptiveHamiltonianLowerBound.time_tree_general`, `mixed_tree_general`,
  `precision_tree_general` and `AdaptiveODELowerBound.Psd.psd_search_tree_general`,
  `psd_scalar_tree_general`.
* `Families/Joint`: the joint, homogeneous and padded joint bounds for one tree solver over any
  Boolean-implemented oracle on a finite-dimensional workspace, from
  `AdaptiveODELowerBound.Joint.joint_general_tree` and `outer_general_tree`.
* `Mesh/Model`, `Const/Model`: the forcing predicates, `MeshCost.of_tree`, `ConstCost.of_tree`,
  the passage from max forms to family forms (`meshForces_of_cost`, `constForces_of_cost` with
  `AdaptiveODELowerBound.Model.forces_or_of_cost₂`, `forces_or_of_cost₃`) and the retry,
  released-protocol and run containments.
* `Mesh/Transfer`, `Const/Transfer`: `meshForces_of_growth`, `meshForces_of_boolean`,
  `constForces_of_growth` (both access shapes at once).
* `Mesh/Herald`, `Mesh/HeraldPad`, `Mesh/Psd`, `Mesh/Joint`, `Mesh/JointPad`, `Mesh/Combined`,
  `Const/Herald`, `Const/Psd`: the family statements, assembled by
  `SparseLowerBounds.Hamiltonian.assembly`, `ODELowerBoundExtensions.Psd.psd_assembly` and
  `AdaptiveODELowerBound.combinedBound_le_max`.

Every theorem of the library, and every `Prop`-valued field of `Mesh.MeshWitnesses` and
`Const.ConstWitnesses`, is axiom-audited in `PhysicalODELowerBound/Audit.lean`.

**Formalisation choices.**

* Forcing over a physical oracle is bookkeeping over the existing `Tree.worstCost`:
  `MeshForces`/`MeshWitnesses`/`MeshCost` and `ConstForces`/`ConstWitnesses`/`ConstCost` have the
  shape of `AdaptiveODELowerBound.Model.TreeForces`, `TreeWitnesses`, `TreeCost` with the physical
  oracle in place of the sampled-time access. No new cost notion, oracle model or accuracy
  predicate is introduced. The two oracles have different parameters, so both predicates are kept.
* Both access shapes are covered: the oracle itself with inverse calls (the released solvers'
  access) and its call forms, which add the controlled and controlled-inverse calls that the
  released solvers do not use. Every call form is counted as its label. The total count
  including source calls is not stated separately; it is at least the matrix count.
* The max forms over explicitly given solvers
  `AdaptiveODELowerBound.Release.combined_max_release_tree`,
  `ConstantODELowerBound.Herald.herald_max_const_tree` and
  `ConstantODELowerBound.Psd.psd_max_const_tree` are restated with identical statements
  (`Mesh.combined_max_release_tree_of_mesh`, `Const.herald_max_const_tree_of_const`,
  `Const.psd_max_const_tree_of_const`) and rederived from the max forms over realised counts
  (`MeshCost.of_tree`, `ConstCost.of_tree`). The released per-family bounds over the oracles
  themselves are the first conjuncts of the corresponding `*_forces_*` lemmas.
* Retry protocols, the released protocols of the general-mesh solver and the released runs are
  covered by the containment lemmas `MeshForces.retry`, `retry_calls`, `releaseProtocol`,
  `releaseRun` and `ConstForces.retry`, `retry_calls`, `constRun`, not by one retry theorem per
  family; the retry form of each family statement is these lemmas applied to its forcing
  conclusion. `MeshForces.releaseProtocol` covers the general-mesh solver's released protocols
  at any `Θ`, so also on the positive semidefinite and homogeneous families, where `ReleaseRun`
  (which fixes `Θ = τ`) does not apply.
* Generic certificates replace family-specific ones: `Access.searchGrowth_mesh` holds for every
  one-stage family with hard data and `Access.implementsOn_mesh` for every family with a Boolean
  certificate of its sampled-time access. The Boolean transfer `Mesh.meshForces_of_boolean` and
  `Families.joint_solver`, `hom_solver`, `joint_pad_solver` quantify over finite-dimensional
  oracle workspaces, as the package adversary does; both physical access shapes are
  finite-dimensional.
* The time-dependent families (the joint family, its paddings and the homogeneous variant) are
  treated over the general-mesh oracle only: they are not constant-coefficient equations (Section
  `odel:sec:main` and Proposition `odel:rem:homogeneous`). The constant-coefficient families
  (`g = 1` and positive semidefinite, and their zero paddings) are treated over both oracles.
* Known padding registers range over `Type`, the universe of the families in `MeshForces` and
  `ConstForces` and of the released normal-form lemma
  `ODELowerBoundExtensions.Release.physicalOracle_normal_form` (the released physical oracles
  are universe polymorphic); the sampled-time forms in `AdaptiveODELowerBound` allow any
  universe. Nothing is lost: the common-dimension forms use
  `LowerBoundRemarks.HamiltonianPadding.PadTo S Nd : Type`.
* Hypotheses are those of the lifted statements, not the manuscript's (`τ ≥ 1` in `PsdRange`,
  where the manuscript has `τ ≥ 2`).
* As in the manuscript (proof of Theorem `odel:thm:combined`), the max and family forms are
  worst-case statements over the class: the terms are witnessed by different families and are not
  multiplied.

**Not formalised.**

* One named retry theorem per family over the physical oracles (the retry forms are the
  containment lemmas above applied to the family statements).
* Common-dimension and qubit-register forms of the padded `g = 1` families alone over the
  general-mesh oracle (the mixed and precision families are padded to a common dimension in
  `Mesh.combined_common_dimension_mesh` and `Mesh.combined_qubit_register_mesh`; the time family
  is padded by any known register in `Mesh.herald_witness_pad_mesh`).
* Runs of the released general-mesh solver on the positive semidefinite and homogeneous families
  as `ReleaseRun`s (`ReleaseRun` is the `D = 0` run structure); every released protocol of that
  solver over `meshOracle` is bounded by `Mesh.MeshForces.releaseProtocol`.
* Input-dependent source interfaces (the released solvers accept them; the lower bounds, like
  Section `odel:sec:main`, require public ones).
* One call applying different labels or call forms on different branches (as in
  `AdaptiveODELowerBound`).
* The time-dependent families over the constant-coefficient oracle of `ode:thm:main`, and the joint
  `ḡ √s τ` lower bound for constant-coefficient equations, which the manuscript does not prove
  (Section `odel:sec:main`); no constant-error `Ω(√s τ)` bound for the purely dissipative subclass
  (Theorem `odel:thm:psd`).
* Measurements inside a run followed by classically controlled operations, measurements with
  more than two outcomes, and circuit, workspace and classical costs (as for the adaptive ODE
  lower bounds); source preparation calls weigh `0`.

**Provenance.** No result from another paper is used. The libraries `SparseHamiltonian`,
`SparseLowerBounds`, `TimeDependentExtensions`, `ODELowerBoundExtensions`,
`AdaptiveHamiltonianLowerBound`, `AdaptiveODELowerBound` and `ConstantODELowerBound` are only
imported; no released module is changed. `ODELowerBoundExtensions/Statements.lean`
(released-oracle forms of Theorem `odel:thm:psd`, Proposition `odel:rem:homogeneous` and the padded
families) and `AdaptiveODELowerBound/Statements.lean` (controlled calls of the released physical
oracle, family forms and those forms over it) predate this library; the notes of these two that
these are not formalised are superseded here, and `ConstantODELowerBound/Statements.lean` points
to this library for controlled calls, padding and family forms over the constant-coefficient
oracle. References to the manuscript use its labels.
-/
