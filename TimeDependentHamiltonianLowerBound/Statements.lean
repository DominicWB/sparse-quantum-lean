import TimeDependentHamiltonianLowerBound.NonVacuity

set_option autoImplicit false

/-!
# The lower bound of `hsl:thm:main` for the time-dependent classes: paper-to-Lean entry point

The paragraphs after the proof of Theorem `hs:thm:time` of the manuscript end: "Finally, this input
class contains the constant hard instances of Theorem `hsl:thm:main`, with `β = δ_val = 0`, so the
lower bounds of that theorem continue to apply." The class is that of Theorem `hs:thm:time`
(coherent sampled-time access, eq. `hs:eq:timeaccess`; error against the propagator, eq.
`hs:eq:timeerror`) and of its generalisations in that paragraph (piecewise paths on general meshes,
integrable paths with an integrated sample-error certificate). This library formalises the remark
for the released time-dependent theorems, without results from other papers. All declarations below
are in the namespace `TimeDependentHamiltonianLowerBound`; the hard families `timeData`,
`mixedMainData`, `precisionMainData`, the range `HSRange τ s ε`, `c0`, `hsL`, `hsH`, `hsR` and
`hardCost` are those of `SparseLowerBounds.Hamiltonian` (`SparseLowerBounds` for `hardCost`), and
`TimeDependent.*` abbreviates `SparseHamiltonian.TimeDependent.*`.

* **Class statements** (the remark): `uniform_class_max` (uniform meshes,
  `SparseHamiltonian.TimeDependent.simulation`), `mesh_class_max` (general meshes,
  `TimeDependentExtensions.Hamiltonian.simulation`) and `integrable_class_max` (integrable
  paths, `IntegrablePathSimulation.Hamiltonian.simulation`); the membership of the constant hard
  data and paths: `uniform_class_members`, `mesh_class_members`, `uniformHyp_hard`,
  `meshHyp_hard`, `uniformHyp_const_zero` (`β = δ_val = 0`), `meshPath_const`,
  `integrablePath_const`.
* **Programs over the released oracle families** (the analogue of
  `SparseLowerBounds.Hamiltonian.main_max_release`): `main_max_uniform`
  (`SparseHamiltonian.TimeDependent.oracle`), `main_max_mesh` and `main_max_integrable`
  (`TimeDependentExtensions.Hamiltonian.oracle`), from the endpoint form `main_max_sampled` and
  the per-family bounds `time_sampled`, `mixed_sampled`, `precision_sampled`.
* **Adaptive algorithms** (the analogue of `AdaptiveHamiltonianLowerBound.main_max_tree`):
  `main_max_tree_access` (coherent sampled-time native access with the time register),
  `main_max_tree_calls` (all its call forms: inverse, controlled, controlled inverse),
  `main_max_tree_uniform`, `main_max_tree_mesh` (the released oracle families); admissibility:
  `admissible_coherentAccess`, `admissible_callFamily_coherentAccess`,
  `admissible_sampledOracle`, `admissible_aligned`, `admissible_uniform`, `admissible_mesh`.
* **The identification** of the time-dependent access on constant data with the
  time-independent primitives and a spectator time register: `sampledOracle_constData`,
  `coherentAccess_constData`, and the normal forms `sampled_normal_form`,
  `aligned_normal_form`, `uniform_normal_form`, `mesh_normal_form`; the Boolean certificates
  `time_sampled_implementsOn`, `mixed_sampled_implementsOn`, `precision_sampled_implementsOn`.
* **Bracket** with the released upper bound (eq. `hsl:eq:upper`): `uniform_theta`,
  `uniform_theta_bracket` (uniform-mesh simulator), `mesh_theta`, `mesh_theta_bracket`
  (general-mesh simulator).
* **Embedding**: `constData`, `constPath`, `constProp`; `solvesOn_constProp`,
  `isPropagator_constProp`, `propagator_eq_constProp`, `isPropagator_eq_constProp`; the
  criteria `uniform_criterion_iff`, `mesh_criterion_iff`, `integrable_criterion_iff`,
  `densityAccurate_propagator_iff`.
* **Non-vacuity**: `uniformGuarantee_of_zero`, `uniform_class_nonvacuous`,
  `mesh_class_nonvacuous`, `integrable_class_nonvacuous`; for adaptive algorithms
  `single_tree_hyps`, `access_of_uniform`, `calls_of_access`.

**Hard instances and their embedding.** The hard families of Theorem `hsl:thm:main` are the released
native sparse data `timeData τ s _`, `mixedMainData τ ε s _`, `precisionMainData τ ε s _`
(`SparseHamiltonian.NativeSparseBlockEncoding.Data X N (Word B) s`, real symmetric, operator norm
and row and column norms one, sparsity `s`, input-independent locators:
`SparseLowerBounds.Hamiltonian.hard_instances`). For data `D : Data X N Z s` and any number `M` of
samples, `constData D M : Data (X × Fin M) N Z s` has every sample equal to the instance
(`constData_matrix`), and `constPath D x u = D.matrix x` is the constant path. Its propagator is
`constProp H u = exp(-iuH)`: it solves `U' = -iHU` on every interval (`solvesOn_constProp`, the
propagator notion `SparseHamiltonian.TimeDependent.SolvesOn` of the uniform and general-mesh
theorems) and is an integral-sense propagator (`isPropagator_constProp`, the notion
`IntegrablePathSimulation.Propagator.IsPropagator` of the integrable-path theorem); every propagator
of a constant path on `[0, T]` equals it at `T` (`propagator_eq_constProp`,
`isPropagator_eq_constProp`, from the released uniqueness
`IntegrablePathSimulation.Propagator.IsPropagator.eqOn`). The time-independent target
`SparseLowerBounds.Hamiltonian.evolve H τ` is `constProp` by definition (`evolve_eq_constProp`).

**Access model.** The coherent sampled-time oracle `∑_r |r⟩⟨r| ⊗ O_r` (eq.
`hs:eq:timeaccess`), one call per invocation with `r` in superposition, inverse calls counted,
in three forms:

* the bare access `coherentAccess ι D`: the native primitives
  `SparseHamiltonian.NativeSparseBlockEncoding.oracles D l (x, r)` of the samples on
  `ℂ^{ι × Fin M} ⊗ NSpace` with an untouched branch register `ι` (the released
  `SparseHamiltonian.TimeDependentODE.labelOracle` with `TimeDependentODE.sample`, as the
  access `SparseLowerBounds.ODE.Family.access` of the ODE lower bounds, outside this library's
  imports); on constant data it is
  `SparseLowerBounds.specOracles (ι × Fin M) D` (`coherentAccess_constData`), a direct sum of
  copies of the native query space, one per branch and time slot;
* the released coherent sampled-time oracle `SparseHamiltonian.TimeDependent.sampledOracle D`
  (native Cayley layout); on constant data it is the time-independent Cayley-layout oracle
  with the spectator `Fin M` (`sampledOracle_constData`, by `rfl`);
* the physical oracle families of the released simulators,
  `SparseHamiltonian.TimeDependent.oracle D γ η t ε` (uniform mesh, `M` slots) and
  `TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε` (general meshes and integrable
  paths), both `AlignedMultiOracleProgram.oracle (TimeDependent.Sampled.oracle D T d)`. On
  constant data every label is `U⁻¹ (1_Ω ⊗ oracles D l x) U` for one fixed isometric
  identification `U` of the workspace with `ℂ^Ω ⊗ NSpace` (`aligned_normal_form`, through the
  released spectator wrappers `ODELowerBoundExtensions.Release.IsWrap`).

Location calls are free (input-independent locators); `Q = p.labelCount .value` counts value
calls, inverses included, `p.count` all calls, `p.cost hardCost = 2Q` is the Boolean cost; for
adaptive algorithms `Q = T.worstCost Access.valueWeight` is the worst-case number of value calls
over all transcripts (`AdaptiveHamiltonianLowerBound.Access.valueWeight`).

**Algorithms.**

* Non-adaptive: `SparseHamiltonian.MultiOracleCircuit.Program`s over a released family on the
  constant data, with any schedule (`γ η t ε'`, slot count, degree) of the physical workspace
  and any isometric input encoding `ι` (`ι† ι = 1`), as
  `SparseLowerBounds.Hamiltonian.main_max_release`.
* Adaptive: `SparseLinearSystems.Protocol.Tree`s (fresh measured runs with classical branching,
  uniformly random trial labels and repeats, a heralded output) over the access, with any flag
  and garbage Hilbert spaces, a finite-dimensional output space and an isometric readout `e`,
  success probability at least `2/3` on every input, as
  `AdaptiveHamiltonianLowerBound.main_max_tree`.

**Error criteria.** Those of the released theorems on the constant path at time `τ`, error `ε`:
`UniformGuarantee run ι (constPath D) τ ε` (every classical propagator from the identity on
`[0, τ]`), `MeshCriterion run ι (constPath D) t M τ ε` (every piecewise propagator on the mesh
intervals of `t`), `IntegrableCriterion run ι (constPath D) τ ε` (every integral-sense
propagator); each is equivalent to the endpoint error
`‖p.eval x ∘ ι - ι ∘ exp(-iτH_x)‖ ≤ ε` of the released lower bounds (`uniform_criterion_iff`,
`mesh_criterion_iff` on a mesh, `integrable_criterion_iff`). For adaptive algorithms the
conditional output is `ε`-accurate (`AdaptiveHamiltonianLowerBound.DensityAccurate`) for
`U(τ) ψ_in` for every propagator `U` of the constant path, equivalently for
`exp(-iτH_x) ψ_in` (`densityAccurate_propagator_iff`).

**Classes.** `UniformHyp D Hpath η t β δ ε` bundles the sixteen hypotheses of
`SparseHamiltonian.TimeDependent.simulation` (`UniformHyp.simulation` is that theorem);
`MeshHyp D t η T ε N` the data-level hypotheses of
`TimeDependentExtensions.Hamiltonian.simulation` and
`IntegrablePathSimulation.Hamiltonian.simulation` (`MeshHyp.simulation`,
`MeshHyp.simulation_integrable`); `MeshPath` and `IntegrablePath` their path conditions, and
`MeshGuarantee`, `IntegrableGuarantee` their guarantees for every path of the class.

**Hypotheses.** `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`), `η = 1` and evolution time `τ`
(normalised units, Section `hsl:sec:main`). The class statements fix the public parameters of the
class: for `uniform_class_max` and `uniform_class_members`, `β, δ ≥ 0` and a number `M` of samples
with the mesh conditions `4 s τ ≤ M`, `9 β τ² ≤ ε M`, `9 (√s τ)³ ≤ ε M²` and `τ δ ≤ ε/12` of
`TimeDependent.simulation` (with `β = δ = 0` only the first and third remain); for `mesh_class_max`
and `integrable_class_max` a mesh `t` with `M` intervals (the bound holds for every `t`, and its
hypotheses can be met when `t` is a mesh; `mesh_class_members` adds `0 < M`, `0 < N`,
`TimeDependentExtensions.IsMesh t M τ` and the slot conditions `4 s τ ≤ N`, `9 (√s τ)³ ≤ ε N²`,
`9 M √s τ ≤ ε N`). The mixed and precision families are used only for `L ≥ 64τ` (and the mixed one
for `s ≥ 64n/τ`), as in `SparseLowerBounds.Hamiltonian.main_max`.

**Guarantees** (`S = √s τ + √(sτr) + r`, `L = log(1/ε)`, `h = log(e + L/τ)`, `r = L/h`,
`c₀ = log 2/(4096π)`).

* `uniform_class_max`: for any three programs over `TimeDependent.oracle (constData D M) …`
  of the constant time, mixed and precision data (any schedules) and isometric encodings, each
  meeting `UniformGuarantee … Hpath τ ε` for every path `Hpath` with
  `UniformHyp (constData D M) Hpath 1 τ β δ ε`: `c₀ S ≤ max(Q_T, Q_M, Q_P)` and
  `c₀ S ≤ max(count_T, count_M, count_P)`. `uniform_class_members`: the constant paths satisfy
  `UniformHyp` with these parameters.
* `mesh_class_max`, `integrable_class_max`: the same for programs over
  `TimeDependentExtensions.Hamiltonian.oracle (constData D M) N …` (any slot counts and
  schedules) meeting `MeshGuarantee` resp. `IntegrableGuarantee` on the mesh `t` at time `τ`.
  `mesh_class_members`: `MeshHyp` holds on every admissible mesh.
* `main_max_uniform`, `main_max_mesh`, `main_max_integrable`: the same bounds from the criteria
  on the constant paths alone (`UniformGuarantee`, `MeshCriterion`, `IntegrableCriterion`);
  `main_max_sampled`: from the endpoint error, for the aligned family with any `M`, slot count
  and degree.
* `time_sampled`: `c_T √s τ ≤ Q` (`c_T = log 2/(192π)`); `mixed_sampled`: for `L ≥ 64τ` and
  `s ≥ 64n/τ`, `(log 2/(384√2)) √(sτr) ≤ Q`; `precision_sampled`: for `L ≥ 64τ`, `r/32 ≤ Q` and,
  when `s < 64n/τ`, `√(sτr)/(64√2) ≤ Q` (`n = precN τ ε`). The bounds `c_T √s τ`,
  `(log 2/(384√2)) √(sτr)` and `r/32` also hold for `p.count` and, doubled, for the Boolean
  cost.
* `main_max_tree_access`, `main_max_tree_calls`, `main_max_tree_uniform`,
  `main_max_tree_mesh`: `c₀ S ≤ max(Q_T, Q_M, Q_P)` for adaptive algorithms, `Q` the worst-case
  number of value calls (for the call forms, weight `valueWeight c.1`).
* `uniform_theta`: for any released uniform-mesh simulators of the three constant families
  (`UniformSimulates`, the conclusion of `TimeDependent.simulation` with `η = 1`, `t = τ`):
  `c₀ S ≤ max Q`, `2 c₀ S ≤ max cost`, `max Q ≤ max count`,
  `max count ≤ 995328 (√s τ + √(sτL) + L) ≤ 995328 h S`; `uniform_theta_bracket`: such
  simulators exist at the mesh size `SparseHamiltonian.TimeDependent.meshSize s 1 τ 0 ε`
  (`exists_uniformSimulates`). `mesh_theta`, `mesh_theta_bracket`: the same for the
  general-mesh simulator (`MeshSimulates`; on the uniform mesh with any `M > 0` intervals and
  `TimeDependentExtensions.Hamiltonian.slotCount s M 1 τ ε` slots, `exists_meshSimulates`).
* `uniform_class_nonvacuous`, `mesh_class_nonvacuous`, `integrable_class_nonvacuous`: the
  released simulators of the three constant families, with their isometric clean inputs, meet
  the hypotheses of `uniform_class_max` (with `β = δ = 0`, every admissible `M`),
  `mesh_class_max` and `integrable_class_max` (every mesh with admissible slot counts).
  `single_tree_hyps`: a program meeting the uniform-mesh criterion on the constant path, run as
  one trial (`AdaptiveHamiltonianLowerBound.Single.tree`) and read through `endpointReadout`,
  meets the hypotheses of the tree theorems; `access_of_uniform` transports a program over the
  uniform-mesh family to the bare coherent access `coherentAccess Ω (constData D 1)`, and
  `calls_of_access` a program over any family to its plain call forms (`plainLift`), keeping
  the criterion; with `exists_uniformSimulates` and `exists_meshSimulates` the hypotheses of
  `main_max_tree_access`, `main_max_tree_calls`, `main_max_tree_uniform` and
  `main_max_tree_mesh` can therefore be met.

**Proof map.** Module paths are relative to `TimeDependentHamiltonianLowerBound/`.

* `Constant`: `constData`, `oracles_constData`, `cayley_constData`, `sampledOracle_constData`
  (all `rfl`), `constPath`, `constProp` and the propagator lemmas (`hasDerivAt_constProp` from
  Mathlib's `hasDerivAt_exp_smul_const'`; uniqueness from the released
  `IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn` and
  `IntegrablePathSimulation.Propagator.IsPropagator.eqOn`).
* `Class`: the class predicates, the released theorems in their terms, membership, the criteria
  and their equivalence with the endpoint error (`mesh_criterion_iff` through
  `IntegrablePathSimulation.Propagator.isPropagator_glue`), and the class-to-criterion lemmas
  `uniformGuarantee_const`, `MeshGuarantee.criterion_const`,
  `IntegrableGuarantee.criterion_const`.
* `Access`: the wrappers `timeWrap`, `alignedWrap` (`isWrap_timeWrap`, `isWrap_alignedWrap`,
  `sampled_eq_wrap`, `aligned_eq_wrap`) and the normal forms; the Boolean certificates by the
  released layer transport of `SparseLowerBounds.Hamiltonian.HsRelease` (`cayleyAccess`,
  `spectatorAccess`, `nativeMaskedAccess`,
  `SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess.spectate`): `timeCayleyAccess`,
  `sampledAccess`, `alignedAccess`, `uniformAccess`, `meshAccess`, `timeSampledAccess`,
  `mixedSampledAccess`, `precisionSampledAccess`.
* `Release`: `SparseLowerBounds.Hamiltonian.accurate_of_endpoint_program`, the general family
  lemmas `SparseLowerBounds.Hamiltonian.time_general`, `mixed_general`, `precision_general`
  with these certificates, `native_bound_of_cost` and `assembly` (as
  `SparseLowerBounds.Hamiltonian.main_max_release`).
* `Adaptive`: `nativeCall_conj`, `admissible_conj`, `admissible_of_normal_form` and the
  released `AdaptiveHamiltonianLowerBound.Access.admissible_specOracles`,
  `AdaptiveODELowerBound.Access.admissible_callFamily_spec`.
* `Trees`: `AdaptiveHamiltonianLowerBound.main_max_tree` with these admissibility lemmas.
* `ClassBound`: membership (`uniformHyp_hard`, `meshHyp_hard`) and the class-to-criterion
  lemmas, then the `Release` max forms.
* `Theta`: `UniformHyp.simulation`, `MeshHyp.simulation` on the constant hard data, the
  `Release` max forms and `SparseLowerBounds.Hamiltonian.release_shape_le`.
* `NonVacuity`: `uniformGuarantee_of_zero` (module `Class`) with the existence lemmas of
  `Theta` and the membership lemmas; `single_tree_hyps` through
  `AdaptiveHamiltonianLowerBound.Single` (`successMass_tree`, `conditionalDensity_tree`);
  `access_of_uniform` through `uniform_normal_form` and `coherentAccess_constData`.

**Formalisation choices.**

* Constant data read every field of `D` at the first component, as the released
  `SparseLowerBounds.ODE.hamData` (outside this library's imports; without its factor `i`), so
  the native primitives of a sample are literally those of the instance; any number `M` of
  samples is allowed (the uniform-mesh class statements need `M > 0`, which follows from
  `4 s τ ≤ M`; `mesh_class_members` assumes `0 < M` and `0 < N`; `mesh_class_max` and
  `integrable_class_max` need neither).
* Normalised units: `η = 1` and evolution time `t = τ`, as Theorem `hsl:thm:main` is stated
  (`‖H‖ = 1`, `τ = η |t|`). The schedule of the algorithm's physical workspace
  (`γ η t ε'` of the oracle family, slot count, degree) is arbitrary; only the error criterion
  fixes the time `τ` and the accuracy `ε`.
* Error criteria are those of the released theorems on the constant path; by uniqueness of
  propagators of constant paths they are equivalent to the endpoint form, so nothing is lost
  against the released endpoint lower bounds.
* Class statements: an algorithm for a class is given, on each hard family, by a program over the
  released oracle family of that family's constant data; it meets the released guarantee for every
  path of the class compatible with its data (for the uniform mesh every `Hpath` with `UniformHyp`,
  for the general mesh every family of pieces with `MeshPath`, for integrable paths every path with
  `IntegrablePath`), and the membership of the constant hard paths is proved inside the proofs. The
  three terms are witnessed by different families, so the bound is in max form ("We need not find
  one matrix on which all three mechanisms are simultaneously difficult"), as
  `SparseLowerBounds.Hamiltonian.main_max`.
* For the uniform mesh the released theorem chooses the program after the path
  (`∀ Hpath, ∃ γ p`), so its conclusion does not give the path-uniform hypothesis of
  `uniform_class_max` (the paper's reading, in which the circuit depends on public data only);
  at `β = δ = 0` every path of the class agrees with the constant path on `[0, τ]`
  (`uniformGuarantee_of_zero`), so the released simulators meet it, and `main_max_uniform`,
  which needs the guarantee on the constant path only, also covers programs chosen for that
  path. The general-mesh and integrable theorems choose one program for all paths of their
  classes, as `MeshGuarantee` and `IntegrableGuarantee` do.
* `Access` keeps the released layer-by-layer Boolean certificates (data) and adds the normal
  form (a `Prop`), which gives admissibility directly; the time register is a spectator only
  because the data are constant in time.
* The general-mesh criterion `MeshCriterion` uses the same path on every mesh interval; the
  general-mesh guarantee `MeshGuarantee` quantifies over all families of pieces.
* The bracket quantifies over every program with the conclusion of the released theorem on the
  constant data (`UniformSimulates`, `MeshSimulates`), with existence from the class
  membership, as `SparseLowerBounds.Hamiltonian.release_theta`; it is on the maximum over the
  three families, and the gap is the factor `h` of
  `SparseLowerBounds.Hamiltonian.release_shape_le`.
* The `Prop`-valued fields of `UniformHyp`, `MeshHyp`, `MeshPath` and `IntegrablePath` are
  audited with the theorems.

**Not formalised.**

* Time-indexed block encodings (eqs. `hs:eq:blockspecial`, `hs:eq:blockadditive`,
  `TimeDependentExtensions.BlockEncoding.simulation`, outside this library's imports): a
  different access model (controlled time-indexed Hermitian unitaries `O_r` with
  `J† O_r J = H̃_r/α`); the hard instances of `hsl:thm:main` are given by native sparse oracles,
  and a lower bound in that model is not claimed by the remark.
* Coherent selection of durations and windows (namespaces `TimeDependentExtensions.Coherent`
  and `IntegrablePathSimulation.Coherent`, outside this library's imports), the piecewise
  Lipschitz corollary `TimeDependentExtensions.Hamiltonian.simulation_lipschitz` (its class also
  contains the constant paths, with `β_r = δ_r = 0`), the gate-level time-dependent theorems and
  their supplied private operations, and the time-dependent ODE classes (covered by the ODE
  lower-bound libraries).
* Family forms (`SparseLowerBounds.Hamiltonian.main_exists`,
  `AdaptiveHamiltonianLowerBound.main_exists_tree`) over the released time-dependent oracle
  families (a few-line consequence of the max forms) and a max form in the Boolean cost (the
  per-family theorems bound `p.cost hardCost`); separate heralded forms (the adaptive forms
  cover heralded algorithms); controlled calls of the released physical families
  (`main_max_tree_calls` covers the call forms of the bare coherent access); a bracket for the
  integrable-path simulator (it uses the oracle family of `mesh_theta`); padding the three
  families to one common instance class (as for the released bracket); genuinely
  time-dependent hard instances.
* As for the adaptive Hamiltonian lower bound: measurements inside a run followed by classically
  controlled operations, and workspaces that are not direct sums of copies of the native space.

**Provenance.** No result from another paper is used. The libraries `SparseHamiltonian`,
`SparseODE`, `SparseLinearSystems` (the protocol model `SparseLinearSystems.Protocol.Tree`),
`TimeDependentHamiltonian`, `TimeDependentODE`, `TimeDependentExtensions`,
`IntegrablePathSimulation`, `SparseLowerBounds`, `LinearSystemLowerBound`,
`AdaptiveHamiltonianLowerBound`, `AdaptiveODELowerBound` and `ODELowerBoundExtensions` are only
imported; no released module is changed. The statement guides
`TimeDependentHamiltonian/Statements.lean`, `TimeDependentExtensions/Statements.lean` and
`IntegrablePathSimulation/Statements.lean` predate this library and list lower bounds for these
classes as not formalised; this is superseded here for the classes of `hs:thm:time` on uniform and
general meshes and of integrable paths. References to the manuscript use its labels.

**Audits.** `TimeDependentHamiltonianLowerBound/Audit.lean` fixes the exact axiom report of
every theorem of the library and of every `Prop`-valued field of `UniformHyp`, `MeshHyp`,
`MeshPath` and `IntegrablePath`.
-/
