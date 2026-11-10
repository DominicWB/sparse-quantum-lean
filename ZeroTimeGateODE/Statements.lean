import ZeroTimeGateODE.Grover
import ZeroTimeGateODE.Certificate
import ZeroTimeGateODE.Assembly
import ZeroTimeGateODE.Constant
import ZeroTimeGateODE.Combined
import ZeroTimeGateODE.TimeAssembly
import ZeroTimeGateODE.Time
import ZeroTimeGateODE.TimeCombined
import ZeroTimeGateODE.Synth
import ZeroTimeGateODE.Binary
import ZeroTimeGateODE.BinaryTime
import ZeroTimeGateODE.SynthCombined
import ZeroTimeGateODE.BinarySynth
import ZeroTimeGateODE.ExactCircuit
import ZeroTimeGateODE.Exact
import ZeroTimeGateODE.ExactTime
import ZeroTimeGateODE.ExactTimeSolver
import ZeroTimeGateODE.ExactCombined
import GateEfficientSynthesis.ODESolver
import GateEfficientBinaryODE.Synth
import GateEfficientBinaryODETime.Synth

/-!
# Zero time or a known zero generator at gate level: paper-to-Lean entry point

Theorem `ode:thm:gates` of the accompanying paper (gate-efficient dissipative equations) ends
with the remark: "At `T = 0` only the initial preparation is needed. For a known zero generator
the solver assembles the source quadrature directly. Neither case needs a propagator query; any
matrix queries inside the supplied preparations still count."  For `x' = A x + b`,
`A = -(L + iH)`, the target `x(T)` is `x₀` at `T = 0` and `x₀ + T b` for a known zero generator
(public bounds `λ_H = λ_D = 0`, so `A = 0`); direct source assembly is the two-term LCU of the
source preparations with the weights `r₀ = ‖x₀‖` and `T r_b = T ‖b‖` (successful amplitude
`‖x(T)‖ / B`, `B = r₀ + T r_b ≤ g ‖x(T)‖`), followed by the released bounded amplification, with
no private Cayley operation, no `U_J` and no matrix-oracle call outside the source preparations.

The released gate-level endpoints of `ode:thm:gates` assume `T > 0` and `λ_H + R λ_D > 0`
(`GateODE.Params.PublicOK`, `GateODE.Time.TParams.PublicOK`; `η_H + η_D > 0` for binary data,
`GateBinaryODE.Pub.OK`, `GateBinaryODETime.PubT.OK`), and their preparations embed the released
simulator as SELECT, with private operations, `U_J` and matrix-oracle calls.  This library
builds the direct source assembly as a new preparation circuit in the native model and in the
exact-gate model, proves its agreement with the released instruction model, its decoded vector
and a direct certificate (amplitude up to one), and states the zero case of the exact-gate and
native solvers, their combined forms for every `T ≥ 0`, and their binary-data and
finite-gate-set (per-trial) forms, the latter a partial formalisation, under this package's format
hypotheses, of the finite-set form of the remark of Theorem `ode:thm:gates`.  The released libraries
are
unchanged.  No result from another paper is used.  References to the manuscript use its labels.

**Naming convention.** All new declarations are in the namespace
`SparseHamiltonian.ZeroTimeGateODE` (one namespace for all modules of `ZeroTimeGateODE/`) and
are named relative to it.  Released declarations are named relative to `SparseHamiltonian`
(for example `GateNative.nprotocol`, `GateODE.Params.target`,
`GateSynthTrials.native_ode_solver_trials`).

**What was already released (cited, not redone).** The query-level remarks (library
`ZeroTimeRemarks`; its guide lists this gate-level remark as not formalised).  The gate-level
endpoints of `ode:thm:gates` for `T > 0` and `λ_H + R λ_D > 0`: exact gates
`GateODE.solver`, `GateODE.Time.solver`; native gates `GateNative.native_ode_solver`,
`GateNative.native_ode_time_solver`; binary data `GateBinaryODE.binary_ode_solver`,
`GateBinaryODETime.binary_ode_time_solver`; finite gate sets (a partial formalisation, under this
package's format hypotheses, of the finite-set statement) with the per-trial
claim `GateSynthTrials.native_ode_solver_trials`, `GateSynthTrials.native_ode_time_solver_trials`,
`GateSynthTrials.binary_ode_solver_trials`, `GateSynthTrials.binary_ode_time_solver_trials`.
Reused without change: the native gate model (`GateNative.NInstr`, `GateNative.nrun`,
`GateNative.nGatesN`, `GateNative.nCallsN`, the full-output error `GateNative.ApproxOn` with
`GateNative.CleanX` and `GateNative.liftB`), the released four-attempt protocol
`GateNative.nprotocol` with its trials `GateNative.trialN`, its agreement
`GateNative.trialN_seed`, its worst-case counts `GateNative.nprotocol_worst` and its guarantees
`GateNative.NOutcome` (`GateNative.noutcome_of_bounds`), the controlled source interfaces
`GateNative.srcIdeal` and `GateNative.loadIdeal`, the released instruction model
(`GateODE.OInstr`, `GateODE.run`, `GateODE.wiring`, `GateODE.Oracles`, `GateODE.seedState`,
`GateODE.goodF`, the time semantics `GateODE.Time.trun`), the source rotation
`GateCircuit.rotC` (`GateODE.Params.srcMat` at the initial label), the released targets,
source vectors, masses and discretisation budget (`GateODE.Params.target`,
`GateODE.Time.TParams.target`, `GateODE.Time.TParams.zsrc`, `GateODE.Time.TParams.mass`,
`GateODE.Time.TParams.discretisation_error`, `TimeDependentODE.Sampling.target_budget`), the
synthesis of the preparation (`GateSynthTrials.synthPrep`, `GateSynthTrials.synthPrep_approx`)
and the Grover analysis (`ODEGroverActual.randomized_certificate`,
`ODEGroverAverage.sum_identity`).

**Endpoints of this library.**

* Exact gates: `exact_ode_solver_zero`, `exact_ode_time_solver_zero` (zero case),
  `exact_ode_solver_nonneg`, `exact_ode_time_solver_nonneg` (every `T ≥ 0`).
* Native gates, constant coefficients: `native_ode_solver_zero` (zero case) and
  `native_ode_solver_nonneg` (every `T ≥ 0`).
* Native gates, time-dependent coefficients: `native_ode_time_solver_zero` and
  `native_ode_time_solver_nonneg`.
* Finite gate sets with the per-trial claim: `native_ode_solver_zero_trials`,
  `native_ode_time_solver_zero_trials` (zero case), `native_ode_solver_nonneg_trials`,
  `native_ode_time_solver_nonneg_trials` (every `T ≥ 0`).
* Binary sparse data: `binary_ode_solver_nonneg`, `binary_zero_no_matrix_calls`
  (constant coefficients), `binary_ode_time_solver_nonneg`, `binary_time_zero_no_matrix_calls`
  (time-indexed data), and over finite gate sets `binary_ode_solver_nonneg_trials`,
  `binary_ode_time_solver_nonneg_trials`.

**Native model** (that of `GateEfficientNative/Statements.lean`).  A native circuit is a list of
`GateNative.NInstr` on the native ODE register `GateNative.HWO a m r K k l f S Zs nP Z bT bP A`
(the released solver wires, the system qubits `S`, the private work wires, the source scratch
`Zs`, a native flag and a pool of `nP` clean wires), run by `GateNative.nrun prim` for primitive
oracles `prim : J → GateCircuit.Reg Y ℂ →L[ℂ] GateCircuit.Reg Y ℂ`; `GateNative.nGatesN C`
(written `|C|`) counts the elementary gates of a circuit `C` and `GateNative.nCallsN q C`
(written `calls_q(C)`) its calls of the primitive kinds selected by `q : J → Bool`; `srcC 0`,
`srcC 1` stand for `srcC false`, `srcC true`.  The protocol `GateNative.nprotocol prepN g hg`
makes up to four attempts; an attempt draws a uniform trial count
`j < ODEGroverAverage.chosenIterations g ≤ 5 g` and runs the trial `GateNative.trialN prepN j`
(the preparation followed by `j` amplification steps with exact zero tests).
`ODERepeatProtocol.Protocol.worstCost` with the weights `GateNative.wGateN`,
`GateNative.wCallN q` is the worst-case count over every history, including four failures.
`GateNative.NOutcome prepN g ε hg prim x`: unitary trials, mean success at least `1/4`, every
successful trial within `ε/500` of `x/‖x‖` up to a global phase, success probability at least
`175/256 > 2/3`, and a conditional output density operator within trace distance `ε` of `x/‖x‖`.
`ν` is the released precision unit `ImprovedODEQueryBudget.precision g ε = ε / (10000 g)`
(`GateODE.Params.nu`; `GateODE.Time.TParams.nu` with ratio `2g` and accuracy `ε/2`).

**The circuits.** `zprepC u srcC` (`Assembly`): the rotation `u` on the source-label wire `ini`,
the supplied source circuits `srcC false` and `srcC true` (controlled on `ini`, placed by
`GateNative.srcPl` as in the released preparation), and `u†` on `ini`; with
`u = srcRot T r₀ r_b = GateCircuit.rotC √(r₀/B) √(T r_b/B)` (`srcMat_zero`: the released source
rotation of the initial label).  Its released counterpart `zrelC u` replaces the source circuits
by the instructions `src false`, `src true` of `GateODE.OInstr`.  Time-dependent coefficients
(`TimeAssembly`): `tzprepC loadC wpC` is the supplied weight-preparation circuit, the supplied
loading circuit and the inverse weight-preparation circuit (counterpart `tzrelC`).  Combined
circuits:
`cprepC p … = if ZeroCase p then zprepC (srcRot T r₀ r_b) srcC else GateNative.nprepC p …`,
`ctprepC p … = if TZeroCase p then tzprepC loadC wpC else GateNative.tnprepC p …`, and for
binary data `bprepC q srcC`, `btprepC q loadC wpC` (with the released `GateBinaryODE.Pub.prep`,
`GateBinaryODETime.PubT.prep`).

**Exact gates** (`ExactCircuit`, `Exact`, `ExactTime`, `ExactTimeSolver`, `ExactCombined`; model
of `GateEfficientODE/Statements.lean`: instruction lists `GateODE.OInstr` on the released wires
`GateODE.Params.W`, run by `GateODE.run (GateODE.wiring v) σ` (time-dependent coefficients:
`GateODE.Time.trun v σ`) for supplied operations `σ` (`U_J`, the private Cayley operations and
the source interfaces; for time-dependent coefficients the loading `J` and the weight matrix
`Wp`), the weights `GateODE.Params.wGate`, `GateODE.Params.wPriv`, `GateODE.Params.wUJ`,
`GateODE.Params.wSrc`, `GateODE.Params.wSeed` (`GateODE.Time.TParams.wLoad`,
`GateODE.Time.TParams.wPrep`), and the released four-attempt wrapper
`ODERepeatProtocol.fourTrials`; the outcome structures have the fields of the released
`GateODE.Params.Outcome` and `GateODE.Time.TParams.Outcome`).

* `exact_ode_solver_zero`: for `p : GateODE.Params` with `PublicOK0 p` and `ZeroCase p` and a
  unit seed `v`, the protocol `zprotocol p v` around the trials `ztrialE p j` (the preparation
  `zprepE p = zrelC (srcRot T r₀ r_b)` followed by `j` steps with the released reflections and
  sign): valid trials; in every history at most `40 g · 2 + 20 g · p.reflGates` gates, no
  private call, no call of `U_J` or `U_J†`, at most `40 g` calls of each source interface and
  `20 g` seed reflections; the released `GateODE.Params.reflGates` and wire count.  For all
  supplied operations `σ` (no condition on `U_J` and the private operations) and every instance
  with `ZInstanceOK p v σ.J H L x₀ b`: the guarantees `ZOutcome` (unitary trials, mean success at
  least `1/4`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a phase, success
  at least `175/256`, conditional output density within trace distance `ε`) against
  `GateODE.Params.target H L x₀ b`.
* `exact_ode_time_solver_zero`: for `p : GateODE.Time.TParams` with `TPublicOK0 p` and
  `TZeroCase p`, the protocol `tzprotocol p v` (ratio `2g`) around `tztrialE p j`
  (`tzprepE p = tzrelC`): valid trials; in every history at most `40 g · p.reflGates` gates, no
  private call, no `U_J` call, at most `80 g` loading calls, `160 g` weight-preparation calls
  and `40 g` seed reflections; the released `GateODE.Time.TParams.reflGates` and wire count;
  the guarantees `TZOutcome` against `x(T)` under `TZInstanceOK p v σ.J σ.Wp …`.
* `exact_ode_solver_nonneg`, `exact_ode_time_solver_nonneg`: for every `T ≥ 0`, the trials
  `ctrialE`, `ctrialET` and protocols `cprotocolE`, `cprotocolET` (zero case or released);
  worst-case counts `if <zero case> then <zero counts> else <released counts>` (gates, private
  calls, `U_J` calls) and the released source, loading, weight-preparation and seed bounds;
  every size conclusion of the released `GateODE.solver` (`GateODE.Time.solver`): the explicit
  `GateODE.Params.prepGates`, `GateODE.Params.reflGates` and wire count, the degree bound of the
  filter, the mesh, reuse-pointer, label and node registers and the grid size
  (`sizes_of_publicOK0`, `tsizes_of_publicOK0`, for every `T ≥ 0`); the guarantees `COutcome`,
  `CTOutcome` under `ZInstanceOK` (`TZInstanceOK`) in the zero case and the released
  `GateODE.Params.InstanceOK` (`GateODE.Time.TParams.InstanceOK`) otherwise.
* Supporting: `ztrialE_counts`, `tztrialE_counts`, `ztrialE_valid`, `tztrialE_valid`,
  `run_eq_srcOracles`, `trun_eq_srcOracles`, `pres2_zprepE`, `pres2_tzprepE`, `ztrialE_seed`,
  `tztrialE_seed`, `zprepE_decoded`, `ztrial_bounds`, `tztrial_bounds`, `zprotocol_worst`,
  `tzprotocol_worst`.

**Constant coefficients, native gates** (`Constant`, `Combined`).

* `native_ode_solver_zero`: for `T ≥ 0`, `g ≥ 1`, `0 < ε ≤ 1/2`, `r₀, r_b ≥ 0`, `B > 0` and valid
  source circuits, on every native register `ZNW a m r K k l f S Zs Z bT bP A` (the released
  kinds of wires with the released pool; `nw_eq_znw`: the released register `GateNative.NW p`
  is `ZNW` of its parameters), the protocol
  `GateNative.nprotocol (zprepC (srcRot T r₀ r_b) srcC) g`: valid trials; exactly
  `|srcC 0| + |srcC 1| + 2` gates and, for every `q`, exactly `calls_q(srcC 0) + calls_q(srcC 1)`
  calls per preparation; in every history at most
  `40 g (|srcC 0| + |srcC 1| + 2) + 20 g (4 n + 3)` gates, `n = |AW| + |XW| + |Zs| + |S|` with
  `AW = GateODE.AW a m r K k l f`, `XW = GateNative.XW Z bT bP A`, and
  `40 g (calls_q(srcC 0) + calls_q(srcC 1))` calls, hence none of a kind that the source circuits
  do not call; the qubit count `|S| + 2 (|AW| + (|Z| + bT + bP + A + 3) + |Zs|) + |S| + 1`
  (`card_ZNW`).  For every instance with unitary primitive oracles, unitary source interfaces
  `J_c` approximated by `srcC c` within `ζs` (`GateNative.srcIdeal`), `2 ζs ≤ ν`, `‖x₀‖ = r₀`,
  `‖b‖ = r_b`, the seed promises `J₀ v = x₀/‖x₀‖`, `J_b v = b/‖b‖` (when nonzero),
  `x₀ + T b ≠ 0` and `r₀ + T r_b ≤ g ‖x₀ + T b‖`: `GateNative.NOutcome` against `x₀ + T b`.
  No condition on `U_J`, private operations, arithmetic or matrix data.
* `zero_target`: `ODEConstantForcing.solution (GateODE.gen H L) x₀ b T = x₀ + T b` if `T = 0` or
  `H = L = 0`; `generator_zero`: `‖H‖ ≤ λ_H = 0` and `‖L‖ ≤ λ_D = 0` give `H = L = 0`.
* `native_ode_solver_nonneg`: public data `p : GateODE.Params` with `PublicOK0 p` (the released
  `GateODE.Params.PublicOK` with `0 ≤ T` and without `0 < λ_H + R λ_D`; `publicOK_of`) and the
  released public native data (`U_J` gates `UJg`, a public native private operation `nd`,
  arithmetic `ar` with `GateNative.ArithOK` at accuracy `ζ`, valid source circuits).  The
  protocol `GateNative.nprotocol (cprepC p UJg nd ar srcC) g` on the released register
  `GateNative.NW p`: valid trials; per preparation at most
  `if ZeroCase p then |srcC 0| + |srcC 1| + 2 else p.prepGates + 84 d |UJg| +
  6 d GateNative.privGates nd ar + |srcC 0| + |srcC 1|` gates and
  `if ZeroCase p then calls_q(srcC 0) + calls_q(srcC 1) else 12 d calls_q(nd.V) +
  calls_q(srcC 0) + calls_q(srcC 1)` calls; in every history at most `40 g` times the counts of
  the preparation plus `20 g (4 n + 3)` gates (the released worst-case bounds); the released
  qubit count.  Instance: for unitary primitive oracles and source circuits within `ζs`,
  `GateNative.NOutcome` against the released target `GateODE.Params.target H L x₀ b`, under
  `2 ζs ≤ ν` and `ZInstanceOK` (unitary sources, `‖H‖ ≤ λ_H`, `‖L‖ ≤ λ_D`, public norms, seed
  promises, nonzero target, `B ≤ g ‖x(T)‖`; `zInstanceOK_of`: implied by the released
  `GateODE.Params.InstanceOK`) if `ZeroCase p` (`T = 0 ∨ λ_H + R λ_D = 0`), and under the
  released conditions (`GateNative.NativeOK`, `24 d ζ + 2 ζs ≤ ν`, `GateODE.Params.InstanceOK`)
  otherwise.  `target_zero`: in the zero case the released target is `x₀ + T b`.

**Time-dependent coefficients, native gates** (`Time`, `TimeCombined`).

* `ttarget_zero`: at `T = 0` or with zero represented samples on every slot, the released
  discretised target `GateODE.Time.TParams.target` is `x₀ + (T/M) ∑_{r < M} b_r`;
  `zsrc_sum`: the released source vectors add up to the same vector; `tz_decoded`: the
  decoded vector of `tzrelC` is `(∑_s z_s)/B`, `B` the released source mass
  (`GateODE.Time.TParams.mass`), under the released weight and loading promises;
  `tzero_samples`: zero public bounds force zero samples.
* `native_ode_time_solver_zero`: for `p : GateODE.Time.TParams` with `T ≥ 0`, `g ≥ 1`,
  `0 < ε ≤ 1/2`, `λ_H, λ_D ≥ 0` and `T = 0 ∨ λ_H + R λ_D = 0`, valid loading and
  weight-preparation circuits, on every native register `ZNW a m r K p.m l f …`: the protocol
  `GateNative.nprotocol (tzprepC loadC wpC) (2g)` has valid trials, exactly
  `|loadC| + 2 |wpC|` gates and `calls_q(loadC) + 2 calls_q(wpC)` calls per preparation, at most
  `40 · 2g` times these in every history plus `20 · 2g (4 n + 3)` gates, no call of a kind that
  the supplied circuits do not call, the qubit count of `card_ZNW`; and for every instance with
  unitary primitive oracles, circuits within `ζs` of the selected loading
  (`GateNative.loadIdeal`) and of `Wp`, `3 ζs ≤ ν` and `TZInstanceOK` (the released
  `GateODE.Time.TParams.InstanceOK` without the conditions on `U_J`, the private operations and
  the clock promises and the self-adjointness of the samples `L_r`; `tzInstanceOK_of`),
  `GateNative.NOutcome` against `x(T)`.
* `native_ode_time_solver_nonneg`: `TPublicOK0 p` (the released `GateODE.Time.TParams.PublicOK`
  with `0 ≤ T`, without `0 < λ_H + R λ_D`, with the released mesh condition, which holds in the
  zero case, `mesh_of_zeroCase`); circuit `ctprepC`; conclusions as in
  `native_ode_solver_nonneg` with ratio `2g`, the instance hypothesis
  `3 ζs ≤ ν ∧ TZInstanceOK …` if `TZeroCase p` and the released `GateNative.NativeOK`,
  `24 d ζ + 3 ζs ≤ ν`, `GateODE.Time.TParams.InstanceOK` otherwise, and `GateNative.NOutcome`
  against `x(T)`.

**Finite gate sets with the per-trial claim** (`Synth`, `SynthCombined`; model of
`GateEfficientSynthesisTrials/Statements.lean`: `GateSynth.Synthesis 𝒢 X len`, an
adjoint-closed `𝒢` (`GateSynthTrials.AdjClosed`) containing the kinds of the exact zero tests
(`GateSynthTrials.zeroTestKinds`); only the preparation is synthesised,
`GateSynthTrials.synthPrep hS (ν/3)`, its inverse is the adjoint of the synthesised circuit and
the zero tests and the sign stay exact, on the trial register `GateSynthTrials.SWO`).

* `native_ode_solver_zero_trials`, `native_ode_time_solver_zero_trials`: the protocol
  `GateNative.nprotocol (GateSynthTrials.synthPrep hS (ν/3) (zprepC …)) g` (resp. of
  `tzprepC loadC wpC`, ratio `2g`): every trial consists of valid gates of `𝒢`
  (`GateSynth.GateOf`) and primitive calls; the synthesised preparation has
  `N_S ≤ N len(ν/3/(N+1))` gates, `N = |srcC 0| + |srcC 1| + 2` (resp. `|loadC| + 2 |wpC|`), and
  exactly the calls of the supplied circuits; with `g' = g` (resp. `2g`), in every history at
  most `40 g'` times these calls and at most `40 g' N_S + 20 g' (4 n + 3)` gates (`n` with the
  trial scratch `GateSynthTrials.SX` in place of `Zs`), and
  `40 g' N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g' (4 n + 3)` gates if `len ζ ≤ c₁ log(1/ζ) + c₀`;
  the qubit count of the trial register; `GateNative.NOutcome` under the hypotheses of the
  native zero-case solvers.
* `native_ode_solver_nonneg_trials`, `native_ode_time_solver_nonneg_trials`: for every `T ≥ 0`,
  the protocol of `GateSynthTrials.synthPrep hS (ν/3) (cprepC …)` (resp. `ctprepC …`) on the
  released trial register `GateSynthTrials.SNW p … X` (resp. `GateSynthTrials.STW`): the
  conclusions of the released `GateSynthTrials.native_ode_solver_trials` (resp.
  `GateSynthTrials.native_ode_time_solver_trials`) with the counts of `cprepC` (resp.
  `ctprepC`), which are `if ZeroCase p then <direct source assembly> else <released>`, and
  `GateNative.NOutcome` under the case-dependent instance hypotheses of
  `native_ode_solver_nonneg` (resp. `native_ode_time_solver_nonneg`).

**Binary sparse data** (`Binary`, `BinaryTime`, `BinarySynth`; models of
`GateEfficientBinaryODE/Statements.lean` and `GateEfficientBinaryODETime/Statements.lean`).

* `BPublicOK0 q`, `BTPublicOK0 q`: the released `GateBinaryODE.Pub.OK`,
  `GateBinaryODETime.PubT.OK` with `0 ≤ T` and without `0 < η_H + η_D`; `BZeroCase q`,
  `BTZeroCase q`: `T = 0 ∨ η_H + η_D = 0`.
* `binary_target_zero`: in the zero case, under the row-energy promises,
  `ODEConstantForcing.solution (-M̂) x₀ b T = x₀ + T b` (zero energy bounds force the matrix to
  vanish, `ODEZeroEnergy.matrix_zero_of_effective_energy`).
* `binary_ode_solver_nonneg`: the hypotheses of the released `GateBinaryODE.binary_ode_solver`
  with `BPublicOK0 q`; the protocol `GateNative.nprotocol (bprepC q srcC) g` on the released
  binary register has its conclusions with the counts `if BZeroCase q then |srcC 0| + |srcC 1| +
  2 else <released>` and `if BZeroCase q then calls_c(srcC 0) + calls_c(srcC 1) else
  12 d (2 [row] + 2 [column] + 2 [value]) + calls_c(srcC 0) + calls_c(srcC 1)`, and
  `GateNative.NOutcome` against the solution `x(T)` of `x' = -M̂ x + b` under the released
  instance hypotheses (energy and accretivity promises, sources within `ζs`,
  `24 d ζ + 2 ζs ≤ ν`, public norms, seed promises, `x(T) ≠ 0`, `r₀ + T r_b ≤ g ‖x(T)‖`).
  `binary_zero_no_matrix_calls`: in the zero case, if the source circuits make no call of the
  oracle kinds selected by `c`, the protocol makes none in any history (the kinds of
  `NativeSparseBlockEncoding.Query` are exactly the row-location, column-location and value
  oracles; for `c = fun _ => true`: if the source circuits are oracle-free).
* `binary_ode_time_solver_nonneg`: the hypotheses of the released
  `GateBinaryODETime.binary_ode_time_solver` with `BTPublicOK0 q`; circuit `btprepC`; ratio
  `2g`; the same form of counts with `|loadC| + 2 |wpC|`; `GateNative.NOutcome` against `x(T)`
  under the released hypotheses (`24 d ζ + 3 ζs ≤ ν`, `GateBinaryODETime.PubT.Rest`).  In the
  zero case the instance conditions are `binary_tzInstanceOK` (self-adjointness and norm bounds
  of the lifted samples from the energy promises, `sqrt_le_lam0`); `btzeroCase_params`: the
  binary zero case is the zero case of the released parameters; `btparams_ok0`.
  `binary_time_zero_no_matrix_calls`: as for constant coefficients.
* `binary_ode_solver_nonneg_trials`, `binary_ode_time_solver_nonneg_trials`: the conclusions of
  the released `GateSynthTrials.binary_ode_solver_trials` and
  `GateSynthTrials.binary_ode_time_solver_trials` for every `T ≥ 0`, with the protocol of
  `GateSynthTrials.synthPrep hS (ν/3) (bprepC q srcC)` (resp. `btprepC q loadC wpC`) and the
  counts of `bprepC` (resp. `btprepC`).

**Proof map** (module paths relative to `ZeroTimeGateODE/`).

* Amplification for amplitudes up to one (`Grover`): `meanSuccess_high` (uniform average of
  `sin² ((2j+1)θ)` over `j < M`, `M ≥ 2`, at least `1/4` for `θ ∈ [π/6, π/2)`, from
  `ODEGroverAverage.sum_identity` and Jordan's inequality), `promised_amplitude_full`, the
  invariant-plane formula below amplitude one (`trial_probability_lt_one`,
  `decoded_multiple_lt_one`), every trial `= ±` the prepared state at amplitude one
  (`trial_of_amplitude_one`), and `randomized_certificate_full`: the released
  `ODEGroverActual.randomized_certificate` without the hypothesis `a ≤ 1/2`.
* The direct certificate (`Certificate`): `output_certificate_direct` (a vector within `2νB` of
  the target with `B ≤ g ‖x‖` has amplitude at least `1/(4g)` and direction error at most
  `ε/500`), `native_trial_bounds_direct`, `noutcome_direct`, `noutcome_direct_retarget`
  (direction errors add, for the time-dependent retargeting), `vector_error_direct`,
  `noutcome_of_released` (from a full-output bound against a lifted released unitary).
* The circuits and their agreement (`Assembly`, `TimeAssembly`): validity, exact counts and
  untouched flag and pool (`zprepC_valid`, `zprepC_counts`, `zprepC_pres`, `tzprepC_valid`,
  `tzprepC_counts`, `tzprepC_pres`); the gates are exact and the source circuits contribute
  `ζs` each (`zprepC_approx`: within `2 ζs` of the lifted `zrelC`; `tzprepC_approx`: within
  `3 ζs` of the lifted `tzrelC`, both through the generic `macro_flatMap_approx`); the decoded
  vectors (`zrelC_decoded`: `c² J₀ v + s² J_b v`; `tzrelC_decoded`).
* Targets and decoded vectors (`Constant`, `Time`): `srcRot_decoded` (`B · decoded = x₀ + T b`),
  `zero_target`, `tz_decoded`, `ttarget_zero`; the time-dependent target is reached with the
  released discretisation budget (`GateODE.Time.TParams.discretisation_error`,
  `TimeDependentODE.Sampling.target_budget`) and `noutcome_direct_retarget`.
* Solvers: `native_zero_outcome`, `native_time_zero_outcome` (one instance), the counts from
  `GateNative.nprotocol_worst`; synthesised forms through `GateSynthTrials.synthPrep_approx`
  (`ν/3 + 2 ζs ≤ 2ν`, resp. `ν/3 + 3 ζs ≤ 2ν`).
* Exact gates (`ExactCircuit`, `Exact`, `ExactTime`, `ExactTimeSolver`): the zero-case
  preparation and its adjoint keep the work wires clean (`pres2_zprepE`, `pres2_tzprepE`), so
  the released agreement argument of `GateODE.Params.trialC_seed` (with `GateODE.rgood_agrees`,
  `GateODE.rseed_agrees`, `GateODE.Time.rseedT_agrees`) makes every trial the released actual
  Grover trial of the preparation (`ztrialE_seed`, `tztrialE_seed`); circuits without `U_J` and
  private instructions do not depend on them (`run_eq_srcOracles`, `trun_eq_srcOracles`); the
  outcome follows the released `GateODE.Params.outcome` with `randomized_certificate_full`
  (`ztrial_bounds`, `tztrial_bounds`, `zoutcome`, `tzoutcome`).
* Combined forms: case split on the zero case, the released endpoint otherwise
  (`publicOK_of`, `tpublicOK_of`, `bpublicOK_of`, `btpublicOK_of`); validity and synthesis
  counts of the combined circuits are uniform.

Every theorem of the library is axiom-audited in `ZeroTimeGateODE/Audit.lean`.

**Formalisation choices.**

* Sample positivity (a formal restriction): the time-dependent ODE solvers assume `L_r ≥ 0` (for
  binary data: accretive dissipative parts) for every represented sample, the hypothesis of the
  formal versions of Theorem `ode:thm:time`, which that theorem of the manuscript does not make (it
  asks of the represented samples only the uniform moment and norm promises; see
  `TimeDependentODE/Statements.lean`). The manuscript's theorems are not changed.
* Direct source assembly is a new preparation, not the released one with an empty SELECT: no
  LCHS coefficient register, no simulator, no private operation, no `U_J`, no arithmetic.  Its
  successful amplitude is `‖x(T)‖/B ∈ [1/g, 1]` (time-dependent coefficients: `‖y‖/B ∈
  [1/(2g), 1]` for the discretised target `y`), which can exceed the range `≤ 1/2` of the
  released amplification theorem; `randomized_certificate_full` covers it with the same public
  cutoff, so the protocol is the released `GateNative.nprotocol` with the same `g` (constant
  coefficients) or `2g` (time-dependent coefficients, the released ratio).
* The zero case keeps the released four-attempt protocol, cutoff and guarantees
  (`GateNative.NOutcome`, success at least `175/256`), although at amplitude one (`T = 0` with
  exact source preparations) every trial succeeds (`trial_of_amplitude_one`).
* The zero-case circuits live on every native ODE register with the released pool (`ZNW`), so
  the combined forms use the released register (`GateNative.NW p`, `GateNative.TNW p`, the
  released binary registers) in both cases; the zero case does not use the private work wires.
* The circuit is uniform in `T`: at `T = 0` the forcing circuit is still applied (with weight
  `T r_b / B = 0`), and the counts include it.
* "Neither case needs a propagator query; any matrix queries inside the supplied preparations
  still count": in the exact-gate model the matrix enters only through `U_J` and the
  private Cayley operations, and no history of the zero-case protocols calls them
  (`exact_ode_solver_zero`, `exact_ode_time_solver_zero`); in the native model no propagator
  query is needed and the calls of every primitive kind are exactly those of the source circuits
  (hypotheses, as in the released theorem), so matrix queries inside the source circuits remain
  counted, and the protocol makes no matrix-oracle call when the source circuits make none
  (`binary_zero_no_matrix_calls` for the binary oracles).
* A known zero generator is the public bound `λ_H + R λ_D = 0` (`λ_H = λ_D = 0`), with
  `‖H‖ ≤ λ_H`, `‖L‖ ≤ λ_D` (resp. the norm bounds of every represented sample); for binary data
  `η_H + η_D = 0` with the row-energy promises.
* Error budgets: `2 ζs ≤ ν` (constant) and `3 ζs ≤ ν` (time-dependent) in the zero case, for the
  source circuits only; the binary forms keep the released `24 d ζ + 2 ζs ≤ ν`
  (`24 d ζ + 3 ζs ≤ ν`) in both cases.
* The time-dependent zero case keeps the released target `x(T)` and its certified
  discretisation error (ratio `2g`, accuracy `ε/2`); for a zero generator the exact target of
  the circuit is the left-endpoint quadrature `x₀ + (T/M) ∑ b_r` (`ttarget_zero`), and `x(T)` is
  reached within the released budget, as in the released solver.
* The zero-case instance conditions keep the released conditions on the sources and on the
  normalisation (public norms, seed promises, `x(T) ≠ 0`, `B ≤ g ‖x(T)‖`; for time-dependent
  coefficients also the sample, path, forcing and discretisation conditions) and drop those on
  `U_J`, the private operations (`GateNative.NativeOK`, clock promises) and the arithmetic, and
  those the zero case does not use: for constant coefficients self-adjointness of `H` and `L`
  and `L ≥ 0` (only `‖H‖ ≤ λ_H`, `‖L‖ ≤ λ_D` are kept), for time-dependent coefficients
  self-adjointness of the samples `L_r` (`GateODE.Time.TParams.SelectHypT.selfL`).
* The combined forms state the counts as `if <zero case> then … else …` and keep every released
  public conclusion of the native and binary endpoints; the instance hypothesis is
  case-dependent for the generic native and exact-gate forms and the released one for the
  binary forms.
* Exact gates: the released protocol `GateODE.Params.protocol` and outcome
  `GateODE.Params.Outcome` are tied to the released trials, so the zero case has its own
  protocol and outcome structure with the same fields (`zprotocol`, `ZOutcome`, `tzprotocol`,
  `TZOutcome`), and the combined forms restate the fields for the combined trials (`COutcome`,
  `CTOutcome`).  The combined exact forms carry every conclusion of the released theorems: the
  counts as `if`-forms and the released size conclusions (`GateODE.Params.prepGates`,
  `GateODE.Params.reflGates`, wire count, degree, mesh, register, grid and node bounds), which
  hold for every `T ≥ 0` (`sizes_of_publicOK0`, `tsizes_of_publicOK0`) and in the zero case
  concern the released circuit, which the zero-case protocol does not use.

**Not formalised.**

* The finite-gate-set forms that synthesise every trial (`GateSynth.native_ode_solver_synth`,
  `GateSynth.native_ode_time_solver_synth`, `GateBinaryODE.binary_ode_solver_synth`,
  `GateBinaryODETime.binary_ode_time_solver_synth`) are not restated for the zero case; they
  would follow from the `GateNative.NOutcome` statements here by the released
  `GateSynth.soutcome`.
* The construction of the source circuits (hypotheses with accuracy `ζs`, as in the released
  theorem), and a preparation that skips the forcing circuit at `T = 0`.
* The absolute-constant forms of equations `ode:eq:gate-main` and `ode:eq:gate-space` for the
  zero case, and the explicit-constant budgets of the library `GateEfficientODEBudget` for it
  (the explicit counts above are stated instead).
-/
