import ZeroTimeRemarks.Hamiltonian
import ZeroTimeRemarks.TimeUniform
import ZeroTimeRemarks.TimeMesh
import ZeroTimeRemarks.TimeBlock
import ZeroTimeRemarks.Gates
import ZeroTimeRemarks.ODEConstant
import ZeroTimeRemarks.ODETime
import ZeroTimeRemarks.ODEMesh

/-!
# Zero-time and zero-generator remarks: paper-to-Lean entry point

The accompanying paper remarks after several upper-bound theorems that the degenerate cases
need no matrix query (for the dissipative solvers, none outside the supplied input and source
preparations):

* Theorem `hs:thm:main`: "For `t = 0` or a known zero Hamiltonian, the identity circuit
  suffices."
* Theorem `hs:thm:time`: "For zero evolution time or a Hamiltonian known to vanish throughout
  the evolution, the evolution operator is the identity, so we can implement it without any
  matrix queries."
* Theorem `hs:thm:gates`, stated under the assumptions of Theorem `hs:thm:main`.
* Theorem `ode:thm:main` (the remark after eq. `ode:eq:simple`): "At zero time or for a known zero
  generator, the solver assembles the initial and source terms directly. It makes no matrix
  queries outside the supplied input and source preparations." The source interfaces here are
  separate query-only oracles, so the matrix-query count is zero. Theorem `ode:thm:time`
  extends the bound of `ode:thm:main` to time-dependent generators, and the same remark is
  stated for it here.
* Theorem `ode:thm:gates`: "At `T = 0` only the initial preparation is needed. For a known zero
  generator the solver assembles the source quadrature directly. Neither case needs a propagator
  query; any matrix queries inside the supplied preparations still count."

The released endpoints of `hs:thm:main` and `hs:thm:time` assume a positive norm bound (`η > 0`,
`α > 0`), those on general meshes and for time-indexed block encodings also `T > 0`, and those of
`ode:thm:time` assume `T > 0` and `ρ = η_H + R η_D > 0`; at zero time the endpoints of
`hs:thm:main`, `hs:thm:time` (uniform meshes) and `hs:thm:gates` still charge their positive query
and gate bounds, and the endpoint of `ode:thm:main` treats the degenerate cases in separate,
source-only oracle families. This library states the remarks in the oracle family, cost weights,
clean encodings and output guarantees of each released endpoint, with zero matrix queries, and gives
combined forms for every time and every bound; the released libraries are unchanged. No result from
another paper is used. References to the manuscript use its labels.

**Naming convention.** All new declarations are in the namespace
`SparseHamiltonian.ZeroTimeRemarks`, one sub-namespace per module of `ZeroTimeRemarks/`
(`Hamiltonian`, `TimeUniform`, `TimeMesh`, `TimeBlock`, `Gates`, `ODEConstant`, `ODETime`,
`ODEMesh`). In the section of a module its declarations are named relative to its
sub-namespace, elsewhere relative to `SparseHamiltonian.ZeroTimeRemarks`. Released declarations
are named relative to `SparseHamiltonian`, except those starting with `TimeDependentExtensions`
(a top-level namespace) and, in the section on `hs:thm:gates`, the gate-model names, which are
relative to `SparseHamiltonian.GateCircuit`, `SparseHamiltonian.GateCircuit.Sim`,
`SparseHamiltonian.GateCircuit.SlotSim` and `SparseHamiltonian.GateNative`.

**What was already released (cited, not redone).**

* `hs:thm:main`: `ImprovedZeroSimulation.zero_time_certificate`,
  `ImprovedZeroSimulation.zero_energy_certificate` and
  `ImprovedZeroSimulation.zero_spectral_certificate` (with `NativeZeroSimulation.*`) give an exact
  zero-query identity program in the smaller family `NativeSparseAttenuation.oracles D` with the
  encoding
  `NativeSparseAttenuation.input D`, not in the family of the endpoint
  `ImprovedSparseHamiltonian.simulation_log_one`.
* `hs:thm:time` on uniform meshes: `TimeDependent.zero_certificate` (zero time or a path that
  vanishes on `[0, t]`: the identity program over the oracles of `TimeDependent.simulation`,
  exact) and `TimeDependent.input_isometry`.
* `ode:thm:main`: the endpoint `ODECompleteEndpoint.solver` already has a zero-time branch
  (`ODECompleteEndpoint.ZeroTimeOutcome`: trials that make no matrix and no forcing call and
  succeed with probability one, with the complete certificate for every instance with a
  prepared initial direction and `x(0) ≠ 0`) and a zero-energy branch
  (`ODECompleteEndpoint.ZeroEnergyOutcome`, from `ODEDegenerateSource`), both without matrix
  queries, in source-only oracle families whose matrix oracle is an unused placeholder
  (`ODEMainEndpoint.unusedMatrixOracle`, `ODEDegenerateSource.dummyOracle`).
* `ode:thm:general` at `T = 0`: library `GeneralODEZeroTime` (`GeneralODE.general_zero`,
  `GeneralODE.general_nonneg`).

**Endpoints of this library.**

* `hs:thm:main` (`Hamiltonian`): `Hamiltonian.zero_certificate`, `Hamiltonian.simulation_zero`,
  `Hamiltonian.simulation_log_one_nonneg`, `Hamiltonian.simulation_spectral_log_one_nonneg`,
  `Hamiltonian.simulation_with_reference_log_one_nonneg`.
* `hs:thm:time`, uniform meshes (`TimeUniform`): `TimeUniform.zero_bound` (public bound
  `η = 0`), `TimeUniform.simulation_nonneg`, `TimeUniform.simulation_with_reference_nonneg`.
* `hs:thm:time`, general meshes (`TimeMesh`): `TimeMesh.zero_certificate`, `TimeMesh.zero_bound`,
  `TimeMesh.simulation_nonneg`, `TimeMesh.simulation_with_reference_nonneg`; time-indexed block
  encodings, equation `hs:eq:blockadditive` (`TimeBlock`): `TimeBlock.zero_bound`,
  `TimeBlock.simulation_nonneg`.
* `hs:thm:gates` (`Gates`): `Gates.simulation_nonneg`, `Gates.time_simulation_nonneg` (exact
  gates), `Gates.native_simulation_nonneg`, `Gates.native_simulation_signed_zero`,
  `Gates.native_time_simulation_nonneg` (native gates).
* `ode:thm:main` (`ODEConstant`): `ODEConstant.zero_solver`, `ODEConstant.native_solver`,
  `ODEConstant.solver_nonneg` (outcome `ODEConstant.BudgetOutcome`).
* `ode:thm:time`, uniform meshes (`ODETime`): `ODETime.zero_solver`, `ODETime.solver_nonneg`
  (outcome `ODETime.BudgetOutcome`); general meshes (`ODEMesh`): `ODEMesh.zero_solver`,
  `ODEMesh.solver_nonneg` (outcome `ODEMesh.BudgetOutcome`).

**Theorem `hs:thm:main`** (namespace `ZeroTimeRemarks.Hamiltonian`; model of
`SparseHamiltonian/Statements.lean`: native sparse data
`D : NativeSparseBlockEncoding.Data X n Z s`, the program family
`ImprovedSparseHamiltonian.oracle D γ η t ε` of original primitive queries with untouched
spectators, the clean encoding `ι = ImprovedSparseHamiltonian.input D γ η t ε`, query counts
including inverse calls, and the full-output error `‖p ι - ι e^{-itH}‖`).

* `input_isometry`: `ι† ι = 1` for all `γ η t ε` (from the released clock preparations,
  `native_input_isometry`, `native_output_isometry`).
* `zero_certificate`: for every `γ η t ε`, if `t = 0` or every instance matrix vanishes, the
  identity program over `ImprovedSparseHamiltonian.oracle D γ η t ε` makes `0` queries, is
  unitary, `ι` is an isometry, and `‖1 ι - ι e^{-itH}‖ = 0` for every instance.
* `simulation_zero`: if `t = 0` or `η = 0`, under the row promise `∑_j |H_ij|² ≤ η²` only,
  there are an admissible `γ` (`0 < γ ≤ 1 ≤ γ √s`) and a program over
  `ImprovedSparseHamiltonian.oracle D γ η t ε` with `0` queries, unitary evaluations, `ι† ι = 1`
  and error `0` for every instance (the proof takes `γ = 1`, `one_admissible`, and the identity
  program of `zero_certificate`).
* `simulation_log_one_nonneg`: the hypotheses of the released
  `ImprovedSparseHamiltonian.simulation_log_one` with `0 ≤ η` in place of `0 < η`
  (`0 < ε ≤ 1/2`, Hermitian instances, row and column promises). Conclusion: an admissible `γ`
  and one program over `ImprovedSparseHamiltonian.oracle D γ η t ε`, uniform over the instances,
  with at most `if t = 0 ∨ η = 0 then 0 else 995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`,
  `τ = η |t|`, queries, `ι† ι = 1`, unitary evaluations and `‖p ι - ι e^{-itH}‖ ≤ ε`.
  `simulation_spectral_log_one_nonneg`: the same from a Hermitian spectral bound `‖H‖ ≤ η`,
  `η ≥ 0`. `simulation_with_reference_log_one_nonneg`: the same bound on every normalized input
  entangled with an untouched finite reference.

**Theorem `hs:thm:time` on uniform meshes** (namespace `ZeroTimeRemarks.TimeUniform`; model of
`TimeDependentHamiltonian/Statements.lean`: samples
`D : NativeSparseBlockEncoding.Data (X × Fin M) n Z s`, coherent sampled-time oracles
`TimeDependent.oracle D γ η t ε`, clean encoding `TimeDependent.input D hM γ η t ε`, the path
`Hpath` and its propagators `U` with `U 0 = 1` and `TimeDependent.SolvesOn` on `[0, t]`).

* `zero_bound`: if `η = 0` (with the row promise, so every sample vanishes), `0 ≤ t`, `0 ≤ β`,
  `0 < M` and a Hermitian `β`-Lipschitz path with `‖H(r t/M) - H̃_r‖ ≤ δ`: for every `γ`, the
  identity program over `TimeDependent.oracle D γ η t ε` makes `0` queries, the encoding is an
  isometry, and for every instance and every propagator `U` the full output is within
  `β t²/M + t δ` of `ι U(t)`, by the released `TimeDependent.mesh_error` with zero samples.
  `freeze_value_le`: under the released mesh conditions `9 β t² ≤ ε M` and `t δ ≤ ε/12`,
  `β t²/M + t δ ≤ ε`.
* `simulation_nonneg`: the hypotheses of the released `TimeDependent.simulation` with `0 ≤ η`.
  Conclusion: as in `TimeDependent.simulation`, with at most
  `if t = 0 ∨ η = 0 then 0 else 995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η t`,
  queries. For `t = 0` the program is the released `TimeDependent.zero_certificate`, for
  `η = 0` it is `zero_bound` with `freeze_value_le`, both at `γ = 1`.
  `simulation_with_reference_nonneg`: the same bound on every normalized input entangled with
  an untouched finite reference, as in the released `TimeDependent.simulation_with_reference`.

**Theorem `hs:thm:time` on general meshes** (namespace `ZeroTimeRemarks.TimeMesh`; model of
`TimeDependentExtensions/Statements.lean`: a mesh `TimeDependentExtensions.IsMesh t M T`, `N`
slots, oracles
`TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε`, encoding
`TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε`, one piece `H_r` per interval and
piecewise propagators).

* `input_isometry`: the encoding is an isometry for all public parameters.
* `zero_certificate`: for every `γ η ε` and every mesh, the identity program makes `0` queries
  and, for every instance, every family of pieces and every propagator (`U 0 = 1`,
  `TimeDependent.SolvesOn` on every closed mesh interval), `‖1 ι - ι U(T)‖ = 0` if `T = 0` or
  every piece vanishes on its interval (`piecewise_zero_eq_one`, from `solvesOn_zero_eq`).
* `zero_bound`: if `η = 0` (row promise), for Hermitian interval-integrable pieces,
  `‖1 ι - ι U(T)‖ ≤ ∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du`, by the released
  `TimeDependentExtensions.mesh_error_integral` with zero samples.
* `simulation_nonneg`: the hypotheses of `TimeDependentExtensions.Hamiltonian.simulation` with
  `0 ≤ η` and `0 ≤ T` (and `0 < N`). Conclusion: as in the released theorem, with at most
  `if T = 0 ∨ η = 0 then 0 else 995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η T`,
  queries, for every piecewise path whose certificate is at most `ε/9`
  (`certificate_nonneg`). `simulation_with_reference_nonneg`: the same bound with an untouched
  finite reference, as in the released
  `TimeDependentExtensions.Hamiltonian.simulation_with_reference`.

**Equation `hs:eq:blockadditive`** (namespace `ZeroTimeRemarks.TimeBlock`; model of the
block-encoding part of `TimeDependentExtensions/Statements.lean`: controlled time-indexed
oracles `TimeDependentExtensions.BlockEncoding.alignedOracle O N α T ε`, encoding
`TimeDependentExtensions.BlockEncoding.alignedInput hM b₀ J hJ t N α T ε`, samples
`H̃_r = α J† O_r J`).

* `alignedInput_isometry`; `blockSample_zero` (`α = 0` gives `H̃_r = 0`, a known zero
  Hamiltonian).
* `zero_bound`: the identity program makes `0` queries; for every instance, self-adjoint
  interval-integrable pieces and propagator, the error is `0` if `T = 0`, and at most
  `∑_r ∫ ‖H_r(u) - H̃_r‖ du` if `α = 0`.
* `simulation_nonneg`: the hypotheses of `TimeDependentExtensions.BlockEncoding.simulation` with
  `0 ≤ α`, `0 ≤ T`, and at most `if T = 0 ∨ α = 0 then 0 else 2304 (α T + 1 + log(3/ε))`
  queries.

**Theorem `hs:thm:gates`** (namespace `ZeroTimeRemarks.Gates`; gate models of
`GateEfficientHamiltonian/Statements.lean`, `GateEfficientTimeDependent/Statements.lean` and
`GateEfficientNative/Statements.lean`, whose names are relative to the four gate namespaces of
the naming convention: instruction lists on the released wires, run by `run`, `SlotSim.runT`
or `nrun`, counts `nGates`, `nPriv`, `nUJ`, `nGatesN`, `nCallsN`, filter degree `fDeg`, and the
clean embeddings `io` and `sysEmb io`). The circuits `circuit`, `circuitT`, `nativeCircuit`,
`nativeCircuitSigned` and `nativeCircuitT` are the empty circuit at zero time and the released
`simCircuit`, `SlotSim.simCircuitT`, `nativeSim`, `nativeSimSigned` and `nativeSimT` otherwise,
on the same wires. Each combined form keeps every conclusion of the released theorem; those that
do not depend on the circuit (wire counts, degree and schedule bounds, existence of a
propagator) are unchanged. Each adds the conjunct that at zero time the full-output error is
exactly `0` (`identity_comp_error_eq_zero`).

* `simulation_nonneg`: the hypotheses of `GateCircuit.Sim.gate_efficient_simulation`
  (`τ ≥ 0`, clock promises). The instructions are valid; `nPriv = if τ = 0 then 0 else 6 d`,
  `nUJ = if τ = 0 then 0 else 12 d`, `nGates ≤ if τ = 0 then 0 else 200 (d+1)(a+m+r+1)`, and
  `‖run (simSem U_J D) circuit ∘ io - io ∘ e^{-iτH}‖ ≤ ε` (`= 0` at `τ = 0`).
* `time_simulation_nonneg`: the hypotheses of `GateCircuit.SlotSim.gate_efficient_time_simulation`
  (`t ≥ 0`); the same counts with `d = fDeg Q (α t) qbar (ε/2)`, and error at most `ε` against
  `U(t)` for every propagator (`= 0` at `t = 0`).
* `native_simulation_nonneg`: the hypotheses of `GateNative.native_simulation` (`τ ≥ 0`): valid
  instructions, `nCallsN p = if τ = 0 then 0 else 12 d nCallsN p V`,
  `nGatesN ≤ if τ = 0 then 0 else 200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C`, error at most `ε`
  against `e^{-iτH}` on `sysEmb io` (`= 0` at `τ = 0`).
* `native_simulation_signed_zero`: the hypotheses of `GateNative.native_simulation_signed`
  (every real `t`), with the same form of counts (`d` computed from `|t|`) and error at most `ε`
  against `e^{-itH}` (`= 0` at `t = 0`).
* `native_time_simulation_nonneg`: the hypotheses of `GateNative.native_time_simulation`
  (`t ≥ 0`), with the same form of counts and error at most `ε` against `U(t)` (`= 0` at
  `t = 0`).

**Theorem `ode:thm:main`** (namespace `ZeroTimeRemarks.ODEConstant`; model of
`SparseODE/Statements.lean`: `x' = A x + b`, `A = -M`, `M = D.matrix x`, source interfaces
`J₀ x`, `J_b x`, public norms `r₀`, `r_b`, mass `B = r₀ + T r_b`, the native physical oracle
family `ODEFinalNativeSource.physicalOracle` of the released positive branch, matrix weight
`ODESourceQueryBudget.matrixWeight (fun _ => 1)`, source weights
`ODESourceQueryBudget.sourceWeight b`, and the complete certificate
`ODECompleteTrial.Certificate`: four attempts, success at least `175/256 > 2/3`, conditional
density within trace distance `ε` of `x(T)/‖x(T)‖`, at most `40 g` calls of each source
interface and `80 g` in total in every history).

* `BudgetOutcome D η_H η_D T g ε r₀ r_b J₀ J_b seed Q`: the released
  `ODECompleteEndpoint.PositiveOutcome` (one public trial family over
  `ODEFinalNativeSource.physicalOracle`, with the released public seed and output flag, chosen
  before the instance; for every instance with `‖x₀‖ = r₀`, `‖b‖ = r_b`, prepared directions,
  `x(T) ≠ 0` and `r₀ + T r_b ≤ g ‖x(T)‖`, the complete certificate) in which, in addition, the
  certified protocol `ODECompleteTrial.algorithm h.trial` has worst-case matrix-query count at
  most `Q` (hence every history, `ODERepeatProtocol.Protocol.History.cost_le_worstCost`).
  `outcome_of_budget` and `budget_of_outcome` relate it to
  `ODECompleteEndpoint.PositiveOutcome`.
* `zero_solver`: `0 ≤ η_H`, `0 ≤ η_D`, `0 ≤ T`, `T = 0 ∨ η_H + R η_D = 0`
  (`R = ImprovedODEQueryBudget.radius g ε`), `1 ≤ g`, `0 < ε ≤ 1/2`, `r₀, r_b ≥ 0`,
  `0 < r₀ + T r_b`, the row promises of both Hermitian parts, a positive semidefinite
  dissipative part, unitary sources and a unit seed. Conclusion: `BudgetOutcome … 0`. The
  target is `x(0) = x₀` at `T = 0` and `x₀ + T b` for a zero generator; the column promises are
  not used.
* `native_solver`: the public hypotheses of the released
  `ODEUniformPositiveEndpoint.positive_time_solver` with `0 ≤ T` and without `ρ > 0`.
  Conclusion: `BudgetOutcome … Q` with
  `Q = if T = 0 ∨ η_H + R η_D = 0 then 0 else 1274019840 g (√s Θ + √(s Θ ℓ) + ℓ)`,
  `Θ = T η_H + T η_D ℓ`, `ℓ = log(10000 g/ε)`.
* `solver_nonneg`: the hypotheses of the released `ODECompleteEndpoint.solver` (one instance
  with `x(T) ≠ 0` and `(r₀ + T r_b)/‖x(T)‖ ≤ g` certifies `g ≥ 1` and `B > 0`). Conclusion: the
  same `BudgetOutcome … Q`.

**Theorem `ode:thm:time` on uniform meshes** (namespace `ZeroTimeRemarks.ODETime`; model of
`TimeDependentODE/Statements.lean`: samples `D : NativeSparseBlockEncoding.Data (X × Fin M) n Z s`,
the family
`TimeDependentODE.NativeSource.physicalOracle`, `g' = 2 g`, `ε' = ε/2`, source mass
`B = r₀ + (T/M) ∑ r_b(r)`).

* `BudgetOutcome … Q`: the released `TimeDependentODE.Outcome` (instance hypotheses: accretive
  `β_G`-Lipschitz generator path with sample errors `δ_G`, `β_b`-Lipschitz forcing bounded by
  `b_max` with sample errors `δ_b`, a solution, public norms, prepared directions, `x(T) ≠ 0`,
  `B ≤ g ‖x(T)‖` and `discretisation ≤ ε B/(2000 g)`) in which the certified protocol has
  worst-case matrix-query count at most `Q`; `outcome_of_budget`, `budget_of_outcome`.
* `zero_solver`: `0 ≤ T`, `T = 0 ∨ η_H + R η_D = 0` (`R = TimeDependentODE.radius g ε`),
  `1 ≤ g`, `0 < ε ≤ 1`, `0 < M`, `r₀ ≥ 0`, `r_b ≥ 0`, `B > 0`, the row promises, positive
  semidefinite dissipative samples, unitary sources and a unit seed. Conclusion:
  `BudgetOutcome … 0`; the mesh conditions and column promises are not needed.
* `solver_nonneg`: the hypotheses of the released `TimeDependentODE.solver` with `0 ≤ T` and
  without `ρ > 0`. Conclusion: `BudgetOutcome … Q` with
  `Q = if T = 0 ∨ η_H + R η_D = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`.

**Theorem `ode:thm:time` on general meshes** (namespace `ZeroTimeRemarks.ODEMesh`; model of
`TimeDependentExtensions/Statements.lean`: mesh `TimeDependentExtensions.IsMesh t M T`, `N`
slots, the family
`TimeDependentExtensions.MeshSource.physicalOracle`, pieces `G_r`, `b_r`, mass
`B = r₀ + ∑_q Δ_q r_b(q)`, integrated certificates and
`TimeDependentExtensions.ODE.publicError`).

* `BudgetOutcome … Q`: the released `TimeDependentExtensions.ODE.Outcome` in which the
  certified protocol has worst-case matrix-query count at most `Q`; `outcome_of_budget`,
  `budget_of_outcome`.
* `zero_solver`: as for `ODETime.zero_solver`, with a mesh and `0 < N`; conclusion
  `BudgetOutcome … 0`.
* `solver_nonneg`: the hypotheses of the released `TimeDependentExtensions.ODE.solver` with
  `0 ≤ T` and without `ρ > 0`; conclusion `BudgetOutcome … Q` with the same `Q` as in
  `ODETime.solver_nonneg`.

**Proof map** (module paths relative to `ZeroTimeRemarks/`).

* Identity programs and isometric encodings for all public parameters: `Hamiltonian`
  (`Hamiltonian.input_isometry`, from the released `SharpClockQuery.input_isometry` and
  `SharpClockSimulation.evolutionOutput_isometry`), `TimeMesh.input_isometry`,
  `TimeBlock.alignedInput_isometry`, `ODEConstant.encoding_isometry`,
  `ODETime.alignedInput_isometry`, `ODEMesh.alignedInput_isometry`.
* Exactness at zero time or zero matrix: `Hamiltonian.exp_eq_one`,
  `TimeUniform.evolution_one`, `TimeMesh.piecewise_zero_eq_one`, `Gates.exp_zero_time`,
  `Gates.identity_comp_error_eq_zero`.
* Discretisation bounds with zero samples: `TimeUniform.zero_bound` (released
  `TimeDependent.mesh_error`, with `TimeUniform.freeze_value_le`), `TimeMesh.zero_bound` and
  `TimeBlock.zero_bound` (released `TimeDependentExtensions.mesh_error_integral`), with
  `TimeUniform.identity_error_le`.
* Direct source assembly: every branch evolution is the identity
  (`ODEConstant.branchEvolution_eq_one_of_time`, the released
  `ODEZeroEnergy.branchEvolution_eq_one_of_matrix_zero`, `ODETime.branchEvolution_eq_one`,
  `ODEMesh.branchEvolution_eq_one`), so the identity program
  is an exact SELECT for the clean encoding, and the released LCHS tables, quadratures and
  `ODEActualSourceError.actual_source_certificate` give its source certificates. The generic
  lemmas `ODEConstant.identity_trials`, `ODETime.identity_trials` and
  `ODEMesh.identity_trials` (any finite label type and isometric clean encoding) build the
  released public trial family on the identity program and turn these certificates into the
  released complete certificate (`ODECompleteTrial.of_trialCertificate`); the released
  compilers give zero matrix cost per trial (`ODEConstant.trial_matrix_cost`,
  `ODETime.trial_matrix_cost`, `ODEMesh.trial_matrix_cost`), so every history makes no matrix
  query (`ODERepeatProtocol.fourTrials_worstCost_le`). At `T = 0` on a general mesh the
  discretised target is the initial state (`ODEMesh.target_zero`), so the target error is `0`,
  which is at most the certified error (`ODEMesh.certified_error_nonneg`).
* Combined forms: case split on the degenerate condition, the released endpoint otherwise.

Every theorem of the library is axiom-audited in `ZeroTimeRemarks/Audit.lean`.

**Formalisation choices.**

* Sample positivity (a formal restriction): the time-dependent ODE forms (`ODETime`,
  `ODEMesh`) keep the positivity hypothesis of the released solvers (positive semidefinite
  dissipative parts of all represented samples), which Theorem `ode:thm:time` of the
  manuscript does not make (see `TimeDependentODE/Statements.lean`).
* Each degenerate case uses the oracle family, clean encoding and guarantee of the released
  endpoint; where the released statement chooses a rescaling `γ` existentially, the zero cases
  use the admissible `γ = 1` (the encodings are isometries for every public parameter).
* "Known zero Hamiltonian" or "known zero generator" is the public bound `η = 0`
  (`η_H = η_D = 0`, `α = 0`), which forces every represented sample to vanish through the row
  promises; for `hs:thm:time` it also includes a path that vanishes on every mesh interval. On
  meshes the intended path is only certified close to the represented samples, so for `η = 0`
  (or `α = 0`) the identity program has the certified discretisation error (at most `ε` under
  the released mesh conditions) rather than error `0`.
* ODE cases keep the released source assembly (initial and forcing preparations, the padded
  LCHS coefficient table and the released source quadrature) and replace only the native
  SELECT by the identity program; source-call counts are therefore the released ones (`40 g`
  per interface, `40 g'` in the time-dependent cases). At `T = 0` the forcing interface is still
  called once per preparation, with zero amplitude.
* The ODE zero cases keep the instance class, trial schedule and four-attempt wrapper of the
  positive branch: the public norms `‖x₀‖ = r₀`, `‖b‖ = r_b`, a positive public mass and both
  direction promises are assumed also at `T = 0`, and the certificate gives success at least
  `175/256` (the released `ODECompleteEndpoint.ZeroTimeOutcome` has success probability one and
  needs no norm or forcing promise).
* Gate-level circuits at zero time are the empty instruction list on the released wires.
* The gate-level combined forms keep all hypotheses of the released theorems (clock promises
  included) and their wire counts, which the empty circuit does not need.

**Not formalised.** The gate-level remark of `ode:thm:gates` (direct source assembly at gate
level): the released gate-level preparations (`GateEfficientODE`, `GateEfficientNative`) embed
the released simulator circuit as their SELECT, their public data assume `T > 0` and
`λ_H + R λ_D > 0`, and a zero case would need a new source-assembly circuit with its own
agreement and certificate proofs. The zero-time forms of the binary-data and finite-gate-set
variants of `hs:thm:gates` (`GateBinary.*`, `GateSynth.*`), whose circuits are built from the
native circuits above; the empty circuit is again valid there, but those statements are not
repeated. The direct preparation with no forcing call at `T = 0` in the native ODE families
(it exists in the released source-only family `ODECompleteEndpoint.ZeroTimeOutcome`). The hybrid
corollary `hs:cor:hybrid` for `τ > 0`, which relies on other papers (its remark that for `τ = 0`
the identity circuit uses no queries is the zero case of `hs:thm:main` and `hs:thm:time` above,
`τ = η|t|` or `η T`). The zero cases of the other corollaries of the time-dependent theorems
(propagator existence, Lipschitz pieces, coherent selection) beyond the forms listed above.
Lower bounds are unaffected.
-/
