import DysonSingleProgram.Fixed

set_option autoImplicit false

/-!
# A single heralded program for the Dyson solver: paper-to-Lean entry point

Lemma `odel:lem:dyson` of the manuscript (eq. `odel:eq:dyson` and its proof) gives a generic
sparse-oracle solver with `Q_A = O(ḡ e^z [1 + z + L_g/log(e + L_g/z)])`, `z = s η T`,
`L_g = log(C ḡ/ε)`; its proof ends with amplitude amplification and constant heralded success. Eq.
`odel:eq:fixed` and the following sentences conclude that at fixed `s, τ, ḡ` the query count is
`O(log(1/ε)/log log(1/ε))`, so that a
uniform worst-case lower bound proportional to `ḡ √s τ log(ḡ/ε)` is false under these access
assumptions. The library `ODELowerBoundExtensions` proves the lemma (with the source access of the
released time-dependent solver, a special case of the source interface used in the manuscript's
proof; see the guide of `ODELowerBoundExtensions`) as a public trial family with the released
complete certificate (`ODELowerBoundExtensions.Dyson.dyson`, `Dyson.family_dyson`) and as a retry
protocol (`Dyson.retrySolver_dyson`, `Dyson.retry_fixed`, `Dyson.no_retry_witnesses`). This library
gives the single-program form: one heralded program in the solver class of the ODE lower bounds,
`SparseLowerBounds.ODE.Solver`, and the consequences of eq. `odel:eq:fixed` for that class. All
declarations below are in the namespace `DysonSingleProgram`.

* Lemma `odel:lem:dyson`, eq. `odel:eq:dyson`, single program: `solver_dyson`, from
  `exists_solver_of_shape` (the program is named: `fourAttempts`).
* Non-vacuity: `solver_dyson_joint`.
* Eq. `odel:eq:fixed` for single programs: `solver_fixed`; the consequence stated after it:
  `DysonSingleProgram.no_uniform_lower_bound` (the released
  `ODELowerBoundExtensions.Dyson.no_uniform_lower_bound` is its retry-protocol counterpart),
  `no_witnesses` (single-program witnesses `Family.Witnesses`) and `no_tree_witnesses`
  (adaptive-tree witnesses `AdaptiveODELowerBound.Model.TreeWitnesses`).
* The amplification shape of the released Dyson trials (proof of Lemma `odel:lem:dyson`):
  `Explicit.dyson_grover`, `Explicit.family_dyson_grover`; the bound of eq. `odel:eq:dyson` on
  the released query shape, `Explicit.bound_le_dysonBound`; the released statements recovered as
  corollaries `Explicit.dyson_of_grover`, `Explicit.family_dyson_of_grover` (without
  `Dyson.dyson` or `Dyson.family_dyson`).

**Input class and access.** A family `F : SparseLowerBounds.ODE.Family X N Z K s` in the class
`F.InClass η ḡ` (row and column Euclidean norms at most `η`, dissipative generators, `g ≤ ḡ`),
with `T = F.T > 0`, and its sampled-time access `F.access ι` (value oracle and row/column
locators with a coherent time address, any branch register `ι`).

**Algorithm model.** `SparseLowerBounds.ODE.Solver ι F G ε`: one program `prog` over `F.access ι`,
an input-independent seed of norm at most one, an isometric readout onto system `ℂ^N` ⊗ garbage `G`,
an input-independent herald projection with success probability at least `2/3` on every input and,
for every solution, conditional accuracy `ε` for `x(T)/‖x(T)‖` (`Readout.HeraldedAccurate`, the
observable form of conditional trace distance, Section `odel:sec:main`). The count is `prog.count`:
all oracle calls, inverse calls included; it also bounds `prog.labelCount .value`.

**Guarantees.**

* `solver_dyson`: for `η > 0`, `T > 0`, `ḡ ≥ 1` and `0 < ε ≤ 1`, every family of
  `InClass η ḡ` has a branch register `ι`, a garbage space `G` and a solver
  `A : Solver ι F G ε` with
  `A.prog.count ≤ dysonBound (s η T) ḡ ε = 16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))`,
  `z = s η T`, `L_g = log(4000 ḡ/ε)` (`ODELowerBoundExtensions.Dyson.dysonBound`).
* `solver_dyson_joint` (non-vacuity): the joint hard family of Theorem `odel:thm:joint`
  (`SparseLowerBounds.ODE.joint_witness`) has an input and meets the hypotheses of `solver_dyson`
  with `η = 1`, and its single program makes between `jointConst ḡ √s τ` and
  `dysonBound (s τ) ḡ ε` calls, so the lower and upper bounds coexist.
* `exists_solver_of_shape`: for a family with an input `x₀` and a system index `i₀ : N`, every
  input having a solution, and a trial family over the lower-bound access (idle source
  vocabulary) with the amplification shape of a preparation `a` over `F.access ι` and the
  released complete certificate on every instance, the program of `fourAttempts` (branch
  register `ι × (I × Fin M)`) is the program of a `Solver` with
  `count ≤ 1274019840 g' queryShape(s', Θ, ℓ)`, the released worst-case count of the four-attempt
  wrapper, where `s'`, `Θ`, `ℓ`, `g'` are the real parameters of the released certificate
  `ODECompleteTrial.Certificate` (not the family sparsity `s`).
* `solver_fixed` (eq. `odel:eq:fixed`): for fixed `s`, `τ > 0` and `ḡ ≥ 1` there are `C` and
  `ε₀ ∈ (0, 1)` such that for every `ε ∈ (0, ε₀]`, every `η > 0` and every family of
  `InClass η ḡ` with `T η = τ` there is a solver with `count ≤ C log(1/ε)/log log(1/ε)`.
* `DysonSingleProgram.no_uniform_lower_bound`: for every `c > 0` there is `ε₀ > 0` such that for
  every `ε ∈ (0, ε₀]`, every `η > 0` and every family of `InClass η ḡ` with `T η = τ` there is a
  solver with `count < c ḡ √s τ log(ḡ/ε)`. Its retry-protocol counterpart is the released
  `ODELowerBoundExtensions.Dyson.no_uniform_lower_bound` (release-style retry solvers, worst-case
  query count).
* `no_witnesses`: for every `c > 0` and all `ε ∈ (0, ε₀]`, no family satisfies
  `Family.Witnesses τ ḡ ε (c ḡ √s τ log(ḡ/ε))`; `no_tree_witnesses`: no family satisfies
  `AdaptiveODELowerBound.Model.TreeWitnesses F τ ḡ ε (c ḡ √s τ log(ḡ/ε))`.

**Proof map.** Module paths are relative to `DysonSingleProgram/`.

* `Shape`: `GroverShape` (preparation `a`, fixed unitaries `U₁ U₂ U₃`, trial `j` evaluating to
  `(U₁ a U₂ a† U₃)^j a` with `(2j + 1)` times the cost of `a`) and its transport `GroverShape.map`.
* `Explicit/Compile`, `Explicit/Dyson`, `Explicit/Family`: the compiled released trials have the
  shape (`groverShape_compile`); `dyson_grover` and `family_dyson_grover` re-prove the released
  statements with the shape, `bound_le_dysonBound` is the bound of eq. `odel:eq:dyson` from the
  released `shape_eq`, `lcuMass_le` and `cost_le_dysonBound`, and `sourceFree_grover` is the
  explicit transport of `ODELowerBoundExtensions.Dyson.exists_sourceFree`.
* `Register/Fiber`: spectator registers (`fiberOracle`, `spectate`, `reflatten`, `toAccess`): a
  program over `F.access ι` with an untouched spectator register `J` is a program over
  `F.access (ι × J)` with the same calls.
* `Coherent`: one attempt with its randomized cutoff `j < M` held coherently in a label register
  `Fin M` in uniform superposition; the reflections of step `i` are controlled on `i < j`, the
  preparation and its inverse are not (`trial_eval_labelSeed`: the attempt prepares the purified
  released attempt `ODELowerBoundExtensions.Release.trialVec`; `count_trial`: `(2(M − 1) + 1)`
  times the calls of the preparation).
* `Parallel/Swap`, `Parallel/Stage`, `Parallel/ReadoutSupport`, `Parallel/Readout`,
  `Parallel/Four`: each attempt runs on the main register and is parked by the fixed basis
  permutation `swapMain`; the herald is the OR of the attempt flags (`heraldStep`) and the fixed
  readout `outStep` decodes the first heralded attempt; `Stage.good_four`: the four-attempt stage
  reproduces the released law `repeatTrials t 4`, with four times the calls of one attempt
  (`Stage.count_four`).
* `Accuracy`, `Solver`: `certificate_observable` (the released certificate gives `2ε`-accurate
  conditional expectations), `heraldedAccurate_of_corr`, `exists_solver_of_good`,
  `exists_solver_of_shape`.
* `Theorem`, `Fixed`: `solver_dyson` (with `exists_solver_of_isEmpty` for families without
  inputs), `solver_dyson_joint` (from `SparseLowerBounds.ODE.joint_witness`) and the
  fixed-parameter statements, from `ODELowerBoundExtensions.Dyson.dyson_fixed` and
  `Dyson.eventually_lt`.

Every theorem of the library, and every `Prop`-valued field of `GroverShape` and
`Parallel.Stage.Good`, is axiom-audited in `DysonSingleProgram/Audit.lean`.

**Formalisation choices.**

* The single program is stated in `SparseLowerBounds.ODE.Solver` over the class's own access
  `F.access ι`, the class that the lower bounds and eq. `odel:eq:fixed` quantify over; the input
  class, accuracy and constants are those of `ODELowerBoundExtensions.Dyson.retrySolver_dyson`.
  For the general certified-mesh class of Lemma `odel:lem:dyson` the package has the trial-family
  form `ODELowerBoundExtensions.Dyson.dyson` and its shape `Explicit.dyson_grover`.
* The randomized amplification cutoff of the released trials is made coherent with a uniform
  label register `Fin M`; only fixed unitaries are controlled, no oracle call is. The released
  trial circuits and cutoff `M` are unchanged (this is not fixed-point amplification), so each
  attempt costs the largest-cutoff count, the released worst case, and the label register
  becomes garbage.
* The known unitary moving the first heralded output to the output register is the solver's
  fixed, query-free readout isometry (`Parallel.outStep`); in `Solver` the readout is an
  arbitrary fixed isometry, so the two forms are equivalent. The herald is the OR of the four
  attempt flags.
* Attempts run on separate registers: the oracle acts on one main register, finished attempts are
  parked by a fixed basis permutation, and the parked attempts and cutoff labels sit in the
  branch register `ι × (I × Fin M)`, which `Solver` quantifies over. The stage and readout are
  the program form of the vector-level step `ODELowerBoundExtensions.Release.purification_step`,
  rebuilt because `Solver` needs one herald projection and one isometric readout for all
  observables.
* `Register.spectate` is the program lift `MultiOracleCircuit.Program.mapHom` along
  `GeneralODE.Registers.diagHom` on `Joint J W`; it plays the role of
  `ChebyshevFilter.lift` without importing that library.
* The released statements are existential and hide the amplification shape, so
  `Explicit.dyson_grover` and `Explicit.family_dyson_grover` re-prove them with an added shape
  conjunct; `Explicit.dyson_of_grover` and `Explicit.family_dyson_of_grover` recover the released
  conclusions, with the bound from `Explicit.bound_le_dysonBound` and without using
  `Dyson.dyson` or `Dyson.family_dyson`. The released files are unchanged.
* The occupation-number configurations of the released proof are kept, not the manuscript's
  literal sorted labels (proof of Lemma `odel:lem:dyson`).
* `no_witnesses` refutes the uniform bound for the single-program class; through
  `ODELowerBoundExtensions.Release.retryWitnesses_witnesses` it implies
  `ODELowerBoundExtensions.Dyson.no_retry_witnesses`, which is not restated. `no_tree_witnesses`
  is an additional corollary for adaptive-tree witnesses (via
  `AdaptiveODELowerBound.Model.treeWitnesses_witnesses`).
* Hypotheses are those of the lifted statements (`Dyson.retrySolver_dyson`, `Dyson.retry_fixed`,
  `Dyson.no_uniform_lower_bound`, `Dyson.no_retry_witnesses`); a family without inputs is solved
  by the empty program (`exists_solver_of_isEmpty`).

**Not formalised.**

* Circuit size and time-register size of the single program (Lemma `odel:lem:dyson`;
  the manuscript claims no bound on them).
* A single-program form for the general certified-mesh class of Lemma `odel:lem:dyson`
  (time-indexed native input, mesh, cell-to-sample map, source interfaces): the package has no
  single-program solver class for that access.
* An adaptive-tree statement of the upper bound (`AdaptiveODELowerBound.Model.TreeSolver`); it
  follows from `Dyson.retrySolver_dyson` through `AdaptiveODELowerBound.Model.retryToTree`, and
  only the negative consequence `no_tree_witnesses` is stated.
* The literal sorted-label sampling of the manuscript's proof (proof of Lemma `odel:lem:dyson`).
* The remark that a constant-coefficient upper bound alone would not exclude the worst-case
  assertion for the time-dependent class (the text after eq. `odel:eq:fixed`).
* A comparison with eq. `ode:eq:simple` in a joint large-parameter regime (the text after eq.
  `odel:eq:fixed`; the manuscript notes that the lemma's exponential `e^{sτ}`
  cost gives no improved comparison there).
* Witnesses outside `SparseLowerBounds.ODE.Family` (generators that are not piecewise constant
  with public breakpoints): `no_witnesses` refutes the witness notion of the package's lower
  bounds.

**Provenance.** No result from another paper is used. The modules import `SparseHamiltonian`,
`SparseODE`, `GeneralODE`, `SparseLowerBounds`, `ODELowerBoundExtensions` and
`AdaptiveODELowerBound` directly, and use declarations of `TimeDependentODE`,
`TimeDependentExtensions`, `LinearSystemLowerBound` and `AdaptiveHamiltonianLowerBound` through
them; these libraries are only imported, and no released module is changed.
`ODELowerBoundExtensions/Statements.lean` predates this library: its notes that no single-program
`Solver` form of the Dyson algorithm is given, and that the uniform bound is not refuted for the
single-program `Family.Forces`/`Family.Witnesses` class alone, are superseded here (as is the scope
remark of `ODELowerBoundExtensions/Dyson/Family/Retry.lean`).
`AdaptiveODELowerBound/Statements.lean` notes that the adaptive-tree form of the consequence of eq.
`odel:eq:fixed` follows from `Dyson.no_retry_witnesses` and
`AdaptiveODELowerBound.Model.treeWitnesses_retryWitnesses` but does not restate it; it is stated
here as `no_tree_witnesses` (from `no_witnesses`). References to the manuscript use its labels.
-/
