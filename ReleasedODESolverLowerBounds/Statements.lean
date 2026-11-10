import ReleasedODESolverLowerBounds.Mesh.Padded
import ReleasedODESolverLowerBounds.Const.Padded
import ReleasedODESolverLowerBounds.Runs.Instances
import ReleasedODESolverLowerBounds.Runs.Const

set_option autoImplicit false

/-!
# Measured solvers over the released ODE solvers' oracles: paper-to-Lean entry point

Section `odel:sec:main` of the manuscript fixes the access of the ODE lower bounds (a reversible
value oracle and in-place row/column locators, their inverses and controls), the output requirement
(success flag of probability at least `2/3` on every input, conditional trace distance `ε`) and
concludes "the lower bounds apply to the upper bounds of the preceding section". Randomised or
adaptive algorithms are covered by purification and deferred measurement (proof of Lemma
`hsl:lem:precision`). The library `PhysicalODELowerBound` proves
the ODE lower bounds for adaptive solvers over the physical oracles of the released solvers of
Theorems `ode:thm:main` and `ode:thm:time`; this library proves them for algorithms with
measurements inside a run over the same oracles, and gives runs of the released `ode:thm:time`
solver on the families of Theorem `odel:thm:psd` and Proposition `odel:rem:homogeneous`. All
declarations below are in the namespace `ReleasedODESolverLowerBounds`.

* Access: `Access.SpectatorForm`, `Access.exists_absorb` (absorption of a spectator register by an
  isometry), `Access.meshOracle_absorb`, `Access.constOracle_absorb`, and the inverse value call as
  a conjugated value call, `Access.meshOracle_valueConj`, `Access.constOracle_valueConj`.
* Transport: `Transport.Absorbs`, `Transport.exists_treeSolver_plain`,
  `Transport.exists_treeSolver_call` (a measured solver over an oracle gives an adaptive solver
  over the call forms of an absorbing oracle with the same success, accuracy and at most its
  worst-case count of the counted label); `Transport.formSel_eq_formSelOf`,
  `Transport.callOpt_callFamily_apply_query` (the package's forms at the matrix labels `Query`
  as instances).
* General-mesh oracle (`ode:thm:time`): `Mesh.MeasuredMeshForces`, `Mesh.MeasuredMeshWitnesses`,
  `Mesh.MeasuredMeshCost`; `Mesh.measuredMeshForces_of_meshForces`,
  `Mesh.meshForces_of_measuredMeshForces`, `Mesh.measuredMeshWitnesses_of_meshWitnesses`,
  `Mesh.MeasuredMeshCost.exists_meshCost_le`. Theorem `odel:thm:combined`:
  `Mesh.combined_measured_mesh`, `Mesh.combined_max_measured_mesh`,
  `Mesh.combined_max_release_measured_mesh`; at one measured solver over the released oracle,
  `Mesh.joint_release_measured_mesh`, `Mesh.mixed_release_measured_mesh` (eq. `hsl:eq:mixrbound`),
  `Mesh.precision_release_measured_mesh` (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`); Theorem
  `odel:thm:joint`: `Mesh.joint_witness_measured_mesh`; Proposition `odel:rem:homogeneous`:
  `Mesh.hom_witness_measured_mesh`; Lemma `odel:lem:herald`, eq. `odel:eq:hsbound`:
  `Mesh.herald_witness_measured_mesh`, `Mesh.herald_max_measured_mesh`,
  `Mesh.precision_terms_witness_measured_mesh`; Theorem `odel:thm:psd`: `Mesh.psd_measured_mesh`,
  `Mesh.psd_max_measured_mesh`. Padded forms, a common dimension and a qubit register (proof of
  Theorem `odel:thm:joint` and proof of Theorem `odel:thm:combined`): the `*_pad_*`,
  `*_common_dimension_*` and `*_qubit_register_*` declarations of `Mesh.Padded` and
  `Mesh.Corollaries`.
* Constant-coefficient oracle (`ode:thm:main`): `Const.MeasuredConstForces`,
  `Const.MeasuredConstWitnesses`, `Const.MeasuredConstCost`,
  `Const.measuredConstForces_of_constForces`, `Const.constForces_of_measuredConstForces`,
  `Const.measuredConstWitnesses_of_constWitnesses`; eq. `odel:eq:hsbound`:
  `Const.herald_witness_measured_const`, `Const.herald_max_measured_const`,
  `Const.herald_max_release_measured_const`, `Const.precision_terms_witness_measured_const`; Theorem
  `odel:thm:psd`: `Const.psd_measured_const`, `Const.psd_max_measured_const`,
  `Const.psd_max_release_measured_const`; padded, common-dimension and qubit-register forms (the end
  of the proof of Theorem `hsl:thm:main` and proof of Theorem `odel:thm:combined`): `Const.Padded`.
* Runs: `Runs.exists_meshProtocol` (with `Runs.exists_releaseProtocol_of_meshProtocol`),
  `Runs.MeshRun` (`Runs.MeshRun.ofReleaseRun`, `Runs.MeshRun.toReleaseRun`),
  `Runs.meshForces_meshRun`, `Runs.meshCost_meshRun`; on the positive semidefinite families
  `Runs.psd_meshRuns_exist`, `Runs.psd_meshRun_bounds`, `Runs.psd_meshRun_bracket`; on the
  homogeneous family `Runs.hom_meshRun_exists`, `Runs.hom_meshRun_bounds`,
  `Runs.hom_meshRun_bracket`; runs as measured solvers, on a family with an input, all of whose
  inputs are solvable: `Runs.MeshRun.exists_measuredSolver`, `Runs.constRun_exists_measuredSolver`.

**Quantifiers.** `MeasuredMeshForces F ε b` quantifies over every placement, spectator index, slot
count, degree and public source interfaces of `ODELowerBoundExtensions.Release.meshOracle`, over
every finite-dimensional output space and every garbage space, and over every measured solver
(`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver`: input-independent unit initial
vector, mid-run and multi-outcome measurements, classical control, success at least `2/3` on
every input, `DensityAccurate` conditional output), in both access shapes (the oracle with
inverse calls, and its call forms `AdaptiveODELowerBound.Access.callFamily` with plain, inverse,
controlled and controlled-inverse calls); it bounds the worst-case value count
`matrixWeight valueWeight` and matrix count `matrixWeight (fun _ => 1)` over all transcripts.
`MeasuredConstForces` is the same over `ConstantODELowerBound.Oracle.constOracle`.

**Hypotheses.** Those of the lifted statements: `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`),
with `ḡ ≥ 1` for the `g = 1` families; `PsdRange τ s ε` (`s ≥ 32`, `τ ≥ 1`, `0 < ε`, `64 τ ≤ L`,
where the manuscript has `τ ≥ 2` in Theorem `odel:thm:psd`), with `ḡ ≥ √2`; `JointRange s τ ḡ ε`
(`s ≥ 4`, `τ ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`); `HomRange s τ ḡ ε` (`s ≥ 4`, `ḡ ≥ 2`,
`τ ≥ 20 (1 + log ḡ)`, `0 < ε ≤ 1/64`); `CombinedRange s τ ḡ ε` (`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`,
`0 < ε ≤ 1/64`); `[DecidableEq Z]` on the constant-coefficient side. The per-family named forms keep
the package's sub-range conditions: `64 τ ≤ L` (`hL`) for `Mesh.mixed_release_measured_mesh` and
`Mesh.precision_release_measured_mesh`, and `64 n/τ ≤ s` (`hs`, `n = precN τ ε`) for
`Mesh.mixed_release_measured_mesh`.

**Guarantees** (`r = hsR τ ε`, `n = precN τ ε`, `L = hsL ε`; each bound holds for the worst-case
value count and the worst-case matrix count of every measured solver, in both access shapes).

* `Mesh.herald_witness_measured_mesh`, `Const.herald_witness_measured_const` and their padded
  forms: on `HSRange`, for `ḡ ≥ 1`, one of the time, mixed and precision families witnesses
  `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)` (`SparseLowerBounds.c0`);
  `*.precision_terms_witness_measured_*`: `c₀ (√(sτr) + r)`; `*.herald_max_measured_*` and
  `Const.herald_max_release_measured_const`: the same bound for the maximum of the three counts.
* `Mesh.psd_measured_mesh`, `Const.psd_measured_const` and the max forms: on `PsdRange`, for
  `ḡ ≥ √2`, `psdBound s τ ε = psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`.
* `Mesh.joint_witness_measured_mesh`, `Mesh.joint_release_measured_mesh`: on `JointRange`,
  `jointConst ḡ √s τ`, `jointConst = 1/400`.
* `Mesh.hom_witness_measured_mesh`: on `HomRange`, `homConst ḡ √s τ`, `homConst = 1/500`.
* `Mesh.combined_measured_mesh` and its padded and max forms: on `CombinedRange`,
  `combinedBound s τ ḡ ε = c (ḡ √s τ + √(sτr) + r)`, `c = c₀/2 = log 2/(8192π)`.
* `Mesh.mixed_release_measured_mesh`: `(log 2/(384√2)) √(sτr)`; `Mesh.precision_release_measured_mesh`:
  `r/32`, and `√(sτr)/(64√2)` when `s < 64 n/τ`.
* Runs (`ℓ = releaseLog ḡ ε = log(40000 ḡ/ε)`, ratio `2ḡ`): `Runs.psd_meshRun_bounds`,
  `Runs.psd_meshRun_bracket`: `psdBound s τ ε ≤ max` of the counts of the two runs
  `≤ 1274019840 · ratio ḡ · queryShape(s, τℓ, ℓ)`; `Runs.hom_meshRun_bounds`,
  `Runs.hom_meshRun_bracket`: `homConst ḡ √s τ ≤` value count `≤` matrix count
  `≤ 1274019840 · ratio ḡ · queryShape(s, τ + τℓ, ℓ)`.

**Proof map.** A measured solver is deferred (`DeferredMeasurementLowerBounds.Deferral`); its
record-selected calls are compiled into controlled calls of the spectator lift `1_{DRec} ⊗ O`
(`DeferredMeasurementLowerBounds.Access.ctrlCircuits`, `selCircuit`), and the spectator lift is
absorbed into the same released oracle with spectator index `DRec × ι` (respectively
`(DRec × Bool) × ι`) by an isometry (`Access.exists_absorb`, from the dimension count
`Access.card_mul_finrank_meshPhysical_le`). The result is an adaptive solver over the call forms
of a released oracle, to which `PhysicalODELowerBound` applies.

**Formalisation choices.**

* The deferral's record register (and control bit for the call shape) is absorbed into the
  spectator index of the same released oracle; `MeshForces` and `ConstForces` quantify over every
  spectator index, so they cover the enlarged oracle. The absorption is an isometry (extension by
  zero along an injection of spectator registers), not an equivalence.
* Only the value label's inverse is compiled by conjugation (by the known negation of the value
  register), so the value count is transported without loss of a constant. Locators have no such
  conjugation and weigh 0 in the value count; the matrix-count bounds follow from the value-count
  bounds, the matrix count being at least the value count.
* Source-interface calls are compiled as known gates (public sources, Section `odel:sec:main`) and
  weigh 0 in both counts, as in the package.
* Max forms are stated over realised measured counts, and at named measured solvers
  (`Mesh.combined_max_release_measured_mesh`, `Const.herald_max_release_measured_const`,
  `Const.psd_max_release_measured_const`).
* Per-family statements at one named measured solver are given for the released general-mesh
  oracle's `joint_release_tree`, `mixed_release_tree` and `precision_release_tree`
  (`Mesh.joint_release_measured_mesh`, `Mesh.mixed_release_measured_mesh`,
  `Mesh.precision_release_measured_mesh`). The other per-family forcing statements of
  `PhysicalODELowerBound` (`time_`, `mixed_`, `precision_`, `joint_`, `hom_`, `psd_search_`,
  `psd_scalar_*forces_mesh`, the `*_forces_const` and `*_forces_pad_*` forms) transfer to
  measured solvers by one application of `Mesh.measuredMeshForces_of_meshForces` or
  `Const.measuredConstForces_of_constForces`, with the same hypotheses and constants; they are
  not restated.
* The hypotheses are those of the lifted statements (see **Hypotheses**); in particular
  `PsdRange` has `τ ≥ 1` where the manuscript has `τ ≥ 2` (Theorem `odel:thm:psd`).
* The constant-coefficient oracle carries the `g = 1` and positive semidefinite families only;
  the joint and homogeneous families are time dependent (Section `odel:sec:main`).
* Runs on the positive semidefinite and homogeneous families are `Runs.MeshRun F τ ḡ ε η_H η_D`,
  not `ODELowerBoundExtensions.Release.ReleaseRun`: `ReleaseRun` fixes `Θ = τ`; the package
  obtains such runs from the solver only for `D = 0`
  (`ODELowerBoundExtensions.Release.exists_releaseProtocol`), and on the positive semidefinite
  and homogeneous families the solver's certified `Θ = τ η_H + τ η_D ℓ` (`Runs.meshTheta_eq`)
  is at least `τ ℓ > τ` (`η_D = 1`). `ReleaseRun` is `MeshRun … 1 0` in both directions. The positive
  semidefinite runs use `(η_H, η_D) = (0, 1)` (`Θ = τ ℓ`); the homogeneous runs use the class
  bound `(1, 1)` (`Θ = τ + τ ℓ`).
* `η_H`, `η_D` bound the row and column Euclidean norms of the Hermitian and dissipative parts of
  every generator piece (the released solver's hypotheses), not the operator norm `‖D_X‖` of the
  manuscript. The upper-bound constants are the release's: ratio `2ḡ`
  (`TimeDependentODE.ratio`) and `ℓ = releaseLog ḡ ε = log(40000 ḡ/ε)`.
* For the positive semidefinite and homogeneous runs the lower and upper bounds are stated side by
  side; the manuscript proves no matching bound for these subclasses.
* `Runs.exists_meshProtocol` generalises `ODELowerBoundExtensions.Release.exists_releaseProtocol`
  from `D = 0` to split bounds `η_H`, `η_D`; `Runs.exists_releaseProtocol_of_meshProtocol`
  recovers the package theorem, with its hypotheses and conclusion, as the instance
  `(η_H, η_D) = (1, 0)` (`Runs.meshTheta_one_zero`).
* `Transport.plainEncOf`, `Transport.plainCircuitsOf` and the call-shape `Transport.callCountedOf`,
  `callPatOf`, `callEncOf`, `callCircuitsOf` are label-generic counterparts of
  `DeferredMeasurementLowerBounds.Access.plainEnc`, `plainCircuit`, `callCounted`, `callPat`,
  `callEnc` and `callCircuit`.
  Those are fixed to the sampled-time access `F.access` with the labels `Query` and no source
  labels, and identify its spectator register by the equivalence `targetEquiv`; the physical
  oracles have the source labels `Sum.inr` and need an absorbing isometry (`Transport.Absorbs`),
  so neither form is an instance of the other. The call-form selectors are shared:
  `Transport.formSel_eq_formSelOf` and `Transport.callOpt_callFamily_apply_query` recover the
  package's forms at the labels `Query`.

**Not formalised.** The joint and homogeneous lower bounds for the constant-coefficient solver of
Theorem `ode:thm:main` (the manuscript disclaims them, Section `odel:sec:main`); runs of the
constant-coefficient solver on time-dependent families. Common-dimension and qubit-register forms
of the padded `g = 1` families alone over the general-mesh oracle: `PhysicalODELowerBound` has
them only on the constant-coefficient side, so they have no measured counterpart here.

**Provenance.** No result from another paper is used. The modules use declarations of the libraries
they import (`PhysicalODELowerBound`, `DeferredMeasurementLowerBounds`, `AdaptiveODELowerBound`,
`ODELowerBoundExtensions`, `ConstantODELowerBound`, `TimeDependentExtensions`); no released module
is changed. References to the manuscript use its labels.

**Audits.** `ReleasedODESolverLowerBounds/Audit.lean` fixes the exact axiom report of every
theorem of the library and of every `Prop`-valued structure field (142 audits).
-/
