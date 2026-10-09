import DysonGeneralAccess.Corollaries
import DysonGeneralAccess.Family

set_option autoImplicit false

/-!
# A single heralded program for the Dyson solver on its general access: paper-to-Lean entry point

Lemma `odel:lem:dyson` of the manuscript (lines 4155-4168, eq. `odel:eq:dyson` at lines
4162-4165, proof 4169-4254) assumes coherent time queries, certified time discretisation, the source
quadrature/preparation access of Theorem `ode:thm:time` and coherent matrix access on every
finite mesh selected from the public regularity certificate, and gives a generic sparse-oracle
solver with `Q_A = O(ḡ e^z [1 + z + L_g/log(e + L_g/z)])` matrix queries, `z = s η T`,
`L_g = log(C ḡ/ε)`; its proof ends with amplitude amplification and constant heralded success
(lines 4251-4253). The library `ODELowerBoundExtensions` proves the lemma on this general access
as a public trial family with the released complete certificate
(`ODELowerBoundExtensions.Dyson.dyson`); `DysonSingleProgram` gives one heralded program on the
class of the ODE lower bounds (`SparseLowerBounds.ODE.Solver`). This library gives one heralded
program on the general access. All declarations below are in the namespace
`DysonGeneralAccess`.

* Single-program class over a general access: `Model.HeraldedSolver`; the ODE lower-bound class
  as its specialisation: `Model.ofSolver`, `Model.toSolver`.
* Lemma `odel:lem:dyson`, eq. `odel:eq:dyson`, single program on the general access:
  `Dyson.single_dyson` (outcome `Dyson.SingleOutcome`, valid instances `Dyson.Valid`).
* The general construction: `Core.single` (named program `Assemble.flatProg (Core.attempts …)`),
  `Core.single_success` (the released success mass), `Core.single_cost`,
  `Core.single_matrix_le`.
* The released time-dependent class (lines 4150-4152): `Dyson.single_release_class`.
* Eq. `odel:eq:fixed` and its consequence (lines 4256-4265), on the larger time-dependent class
  that the lemma is included to cover (lines 4266-4268): `Dyson.single_fixed`,
  `Dyson.single_no_uniform`.
* The ODE lower-bound class: `Family.solver_dyson_of_core` (the conclusion of
  `DysonSingleProgram.solver_dyson` from `Core.single`), `Family.heralded_dyson_family`,
  `Family.fourAttempts_eq`.

**Input class and access.** The released general access
`ODELowerBoundExtensions.Dyson.oracle D K M J₀ Jb` (masked coherent sampled-time native calls,
labels `Sum.inl`, and the supplied source interfaces, labels `Sum.inr`) for a public time-indexed
native input `D : Data (X × Fin Kₛ) n Z s` (entries bounded by `Λ = D.scale`), a public mesh `t`
with `M` cells and a public cell-to-sample map `σ : Fin M → Fin Kₛ`, public source norms `r₀`,
`rb`, unitary source interfaces `J₀`, `Jb`, a unit seed, and `K = dysonDegree D T ḡ ε`. The
program runs over `Register.fiberOracle J` of this access (spectator register `J`, chosen by the
algorithm). Valid instances (`Dyson.Valid`): `y = x(T)` for an instance meeting the premises of
`ODELowerBoundExtensions.Dyson.Outcome` verbatim.

**Algorithm model.** `Model.HeraldedSolver O Valid G ε`: one program over `O`, an
input-independent seed of norm at most one, an isometric readout onto system `ℂ^n` ⊗ garbage
`G`, an input-independent herald projection; on every valid instance `(x, y)` success
probability at least `2/3` and conditional accuracy `ε` for `y/‖y‖`
(`Readout.HeraldedAccurate`, the observable form of conditional trace distance, lines
3675-3677). The query count is `prog.cost (matrixWeight 1)`: row, column and value calls,
inverses included; source calls are not counted (line 4166). The controls of the access (lines
3669-3671) are part of the released access itself: `Dyson.oracle` is built by
`ODECoordinateNativeControl.physicalOracle` on the workspace
`NativeControlledOracle.Workspace`, and the program language
(`MultiOracleCircuit.Program`: fixed maps, calls and inverse calls) has no further controlled
call. For an upper bound this only restricts the algorithm.

**Quantifiers.** For every public input `D`, mesh `t` with `M` cells, cell-to-sample map `σ`,
source norms and source interfaces meeting the hypotheses below, and every `T`, `ḡ`, `ε` in
range, there exist a spectator register `J`, a garbage space `G` and one program; that program
then serves every valid instance `(x, y)` of the access at once (one program for all instances,
not one per instance). The constants `C`, `ε₀` of `Dyson.single_fixed` depend only on `z`
and `ḡ`, and the `ε₀` of `Dyson.single_no_uniform` only on `s`, `τ`, `ḡ` and `c`; both are
uniform over all inputs with those parameters.

**Guarantees.**

* `Dyson.single_dyson`: under the hypotheses of `ODELowerBoundExtensions.Dyson.dyson`
  (`0 < M`, a mesh `t` of `[0, T]`, `T > 0`, `ḡ ≥ 1`, `0 < ε ≤ 1`, `r₀ ≥ 0`, `rb ≥ 0`, positive
  mass, unitary source interfaces, unit seed) there are `J`, `G` and a heralded single program
  over `fiberOracle J (oracle D K M J₀ Jb)` for `Dyson.Valid` with
  `cost (matrixWeight 1) ≤ dysonBound (s Λ T) ḡ ε = 16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))`,
  `z = s Λ T`, `L_g = log(4000 ḡ/ε)`.
* `Core.single`: for any unitary access `O`, a trial family `q` over a source-labelled access
  with the amplification shape (`DysonSingleProgram.GroverShape`, matrix weight) of a
  preparation `a` over `O`, cutoff `M > 0`, unit seed, isometric output, and a relation `Valid`
  all of whose instances carry `ODECompleteTrial.Certificate q M ψ out x y s' Θ ℓ g' ε`, the
  four-attempt program is a heralded single program for `Valid`; its heralded success equals
  the success mass of the released wrapper `ODERepeatProtocol.fourTrials q M ψ out` on every
  input (`Core.single_success`), it costs `4 (2(M − 1) + 1)` times `a` for every weight
  (`Core.single_cost`), and at most `1274019840 g' queryShape s' Θ ℓ` in `a`'s weight once one
  valid instance exists (`Core.single_matrix_le`).
* `Dyson.single_release_class`: under the hypotheses of
  `ODELowerBoundExtensions.Dyson.dyson_release_class`, one heralded program (`σ = id`) solves
  every instance accepted by the released `TimeDependentExtensions.ODE.solver`
  (`Dyson.ReleaseValid`) within `dysonBound`.
* `Dyson.single_fixed`: for `z > 0`, `ḡ ≥ 1` there are `C` and `ε₀ ∈ (0, 1)` such that for all
  `ε ∈ (0, ε₀]` and every input with `rate D * T = z` there is a heralded single program with at
  most `C log(1/ε)/log log(1/ε)` matrix queries.
* `Dyson.single_no_uniform`: for every sparsity `s` (inputs have `s > 0`), `τ > 0`, `ḡ ≥ 1`,
  `c > 0` there is `ε₀ > 0` such that
  for all `ε ∈ (0, ε₀]` and every input with `Λ T = τ` there is a heralded single program with
  fewer than `c ḡ √s τ log(ḡ/ε)` matrix queries.
* `Family.solver_dyson_of_core`: the statement of `DysonSingleProgram.solver_dyson`, re-derived
  from `Core.single` at the access `F.access ι`. It duplicates that theorem on purpose: it checks
  that the general construction contains the class of the ODE lower bounds.
  `Family.heralded_dyson_family`: the same class as heralded single programs over `F.access ι`
  for `Model.familyValid F`.

**Proof map.** Module paths are relative to `DysonGeneralAccess/`.

* `Model`: the class, `mono`, `map` (transport along a program map conjugating evaluations by a
  fixed isometric equivalence), `trivial` (identity program when no instance is valid),
  `ofSolver`, `toSolver`.
* `Cost`: weighted counts of `Register.reflatten`, `Coherent.steps`, `Coherent.trial`,
  `Parallel.Stage.step`, `Parallel.Stage.four`.
* `Assemble`: a stage as a heralded single program in the layout `Release.jointFlatten`
  (`ofStage`, `ofGood`), the general-access form of `DysonSingleProgram.exists_solver_of_stage`
  and `exists_solver_of_good`.
* `Core`: `attempts`, `good_attempts` (from `Coherent.trial_eval_labelSeed` and
  `Parallel.Stage.good_four`), `single` (with `DysonSingleProgram.certificate_observable` and
  `Certificate.success_two_thirds`), `single_matrix_le` (from `Certificate.trial.matrix_queries`
  at the largest cutoff and `GroverShape.cost_eq`).
* `Valid`, `Theorem`: `Dyson.Valid`, `oracle_unitary`, `exists_shape` (the `Valid` form of
  `DysonSingleProgram.Explicit.dyson_grover`, by destructuring it); `single_dyson` (case split on
  the existence of a valid instance: `Core.single` with `Explicit.bound_le_dysonBound`, or
  `HeraldedSolver.trivial` with `dysonBound_nonneg`).
* `Corollaries`: `releaseValid_valid` (`MeshSampling.generator_accretive`,
  `quadrature_le_publicError`), `single_release_class` (`HeraldedSolver.mono`), `single_fixed`
  (`Dyson.dyson_fixed`), `single_no_uniform` (`Dyson.eventually_lt`).
* `Family`: `solver_dyson_of_core` (from `Explicit.family_dyson_grover`, `Core.single`,
  `Register.eval_toAccess`, `HeraldedSolver.map`, `toSolver`, and
  `DysonSingleProgram.exists_solver_of_isEmpty` for families without inputs);
  `heralded_dyson_family` (from `DysonSingleProgram.solver_dyson` and `Model.ofSolver`, which
  keeps the program).

Every theorem of the library, and every `Prop`-valued field of `Model.HeraldedSolver`, is
axiom-audited in `DysonGeneralAccess/Audit.lean`.

**Formalisation choices.**

* The mesh, its cell-to-sample map and the source norms are public parameters of the access, as
  in `Dyson.dyson`: the manuscript chooses the mesh classically from the public regularity
  certificate before the run (lines 4178-4196), and register sizes may depend on it (lines
  4166-4167). "Coherent matrix access on every finite mesh" is the universal quantification over
  meshes. The program-internal coherent choices are the amplification cutoff (`Coherent.trial`,
  label register `Fin M`) and the first-success selection of the herald and readout
  (`Parallel.Stage.four`).
* `Model.HeraldedSolver` copies the fields of `SparseLowerBounds.ODE.Solver` with the access and
  the valid-instance relation as parameters; success and accuracy are required on valid
  instances (the manuscript's "on every input", lines 3675-3676, read for a promise class whose
  inputs are the instances meeting the promises), so no hypothesis that every input has a valid
  instance is added to those of `Dyson.dyson`. With every input having a solution, `Solver` is the
  specialisation (`ofSolver`, `toSolver`).
* The count is the matrix-weighted cost (line 4166); the program's source calls are counted by
  `Core.single_cost` for every weight but not bounded.
* `Dyson.single_dyson` is existential: when no instance is valid the identity program is used.
  The program on the inputs with valid instances is `Core.single` of the released Dyson trials.
  `Dyson.Valid` is not empty in general: when the sampled matrices `D.matrix (x, σ r)` are
  accretive, the generator equal to the sampled matrix on each cell, no forcing (`b = 0`,
  `bs = 0`, `rb = 0`), `x(0) = r₀ J₀ x seed` with `r₀ > 0`, and `ḡ ≥ r₀/‖x(T)‖` give a valid
  instance, every error term being zero. The released class embeds through
  `Dyson.releaseValid_valid`.
* `Family.solver_dyson_of_core` restates `DysonSingleProgram.solver_dyson` and proves it through
  `Core.single`; this checks that the class of the ODE lower bounds is a specialisation of the
  general construction.
* Hypotheses are those of the lifted statements (`Dyson.dyson`, `Dyson.dyson_release_class`,
  `Dyson.dyson_fixed`, `Dyson.eventually_lt`).
* `Dyson.Valid` and `Dyson.ReleaseValid` restate verbatim the premise lists of the released
  `Dyson.dyson` outcome and of `Dyson.dyson_release_class`, which have no named predicate;
  `Dyson.exists_shape` and `Dyson.releaseValid_valid` check the match by compilation.

**Not formalised.**

* A source-call bound for the single program (the manuscript counts only matrix queries).
* Circuit size and time-register size of the single program (lines 4166-4167).
* An adaptive-tree form of the upper bound on the general access.
* Selection of the mesh inside the program (the manuscript selects it classically from the
  public certificate).
* The remark of lines 4269-4271 (no improved comparison with eq. `ode:eq:simple` in a joint
  large-parameter regime; no circuit-size or time-register-size bound is claimed).

**Provenance.** No result from another paper is used. The modules import `DysonSingleProgram`
and `ODELowerBoundExtensions` and use declarations of the libraries they import; no released
module is changed. Line numbers in this guide refer to the manuscript version accompanying this
library, as do those of `ODELowerBoundExtensions`; the guide of `DysonSingleProgram` cites an
earlier numbering, and the paper labels are the stable references.
-/
