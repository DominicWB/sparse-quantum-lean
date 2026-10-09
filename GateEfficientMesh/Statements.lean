import GateEfficientMesh.Slots
import GateEfficientMesh.Exact
import GateEfficientMesh.Native
import GateEfficientMesh.Binary
import GateEfficientMesh.BinaryTheorem
import GateEfficientMesh.BinaryMesh
import GateEfficientMesh.Synth
import GateEfficientMesh.ODE.Core
import GateEfficientMesh.ODE.Target
import GateEfficientMesh.ODE.Exact
import GateEfficientMesh.ODE.Native
import GateEfficientMesh.ODE.Binary
import GateEfficientMesh.ODE.MeshScheme
import GateEfficientMesh.ODE.MeshTarget
import GateEfficientMesh.ODE.Mesh
import GateEfficientMesh.ODE.BinaryMesh
import GateEfficientMesh.ODE.Synth
import GateEfficientMesh.ODE.Trials
import GateEfficientMesh.NonVacuity

/-!
# Certified and nonuniform meshes at gate level: paper-to-Lean entry point

Theorem `hs:thm:gates` of the accompanying paper (manuscript lines 2754-2799) states, for the
time-dependent setting of Theorem `hs:thm:time` on a uniform mesh of `M = 2^m ≥ 2` slots, that
the circuit with slot-selected private Cayley operations has full-output error at most `ε`
relative to `U_H(T, 0)` (lines 2789-2797; proof lines 3022-3040). Theorem `ode:thm:gates`
(lines 4335-4377) requires, for time-dependent generators, "the Lipschitz bounds and
represented-sample certificates of Lemma `ode:lem:gate-select`; more generally, a certificate
for the same uniform meshes suffices" (lines 4341-4343). The paragraph "Regularity and coherent
parameters" after Theorem `hs:thm:time` (lines 2420-2434) covers piecewise Lipschitz paths with
the breakpoints in the mesh and, for an integrable Hermitian path, a certified bound on
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du`. The released gate-level endpoints prove the
time-dependent parts of both theorems for Lipschitz paths with uniform sample errors on uniform
meshes (formalisation summary, lines 1380-1500); the gate analyses do not cover "nonuniform
meshes" (lines 1628-1645), and the scope paragraph after the proof of `ode:thm:gates`
(lines 4573-4587) notes that "an arbitrary nonuniform mesh obtained by inserting breakpoints does
not automatically supply the equal-angle boundary circuit used here".

This library proves the gate-level time-dependent theorems, for Hamiltonians and for
dissipative equations, with exact gates, native implementations, binary sparse data and over
finite gate sets, (1) under the integrated sample-error certificate on the uniform slots of the
released circuits, against integral-sense and classical piecewise propagators (Hamiltonians)
and classical piecewise solutions (dissipative equations), with the released circuits and
counts and only the subdivision condition on the slot exponent, and (2) beyond the paper's gate
theorems, which are stated on uniform meshes, on nonuniform meshes with breakpoints, as
corollaries: the mesh is refined into the uniform clock of the released circuits (so the
equal-angle boundary circuit is the released one), every slot uses the samples of the mesh
interval containing it, and the counts are the released counts with this `m`, without a factor
`M`. The certified error is the integrated certificate on the mesh plus a rounding term of
order `M T Λ / 2^m` for Hamiltonians; for dissipative equations it also contains the
left-endpoint source quadrature of the mesh (at most `2 Λ ∑_q Δ_q² ‖b̃_q‖`, independent of `m`).
The released libraries are unchanged. No result from another paper is used. Manuscript lines
refer to `sparse_quantum_algorithms.tex` (v15); the labels are the stable references.

**Naming convention.** The Hamiltonian declarations are in the namespace
`SparseHamiltonian.GateMesh`, the ODE declarations in `SparseHamiltonian.GateMesh.ODE`; they are
named relative to `SparseHamiltonian.GateMesh` below (for example `ODE.ode_time_solver_mesh`).
Released declarations are named relative to `SparseHamiltonian` (for example
`GateCircuit.SlotSim.simCircuitT`, `TimeDependentODE.SolvesODE`); `TimeDependentExtensions`,
`IntegrablePathSimulation` and `ODELowerBoundExtensions` are top-level namespaces of the package.

**What was already released (cited, not redone).**

* The gate-level time-dependent endpoints for Lipschitz paths on uniform meshes:
  `GateCircuit.SlotSim.gate_efficient_time_simulation` (exact gates),
  `GateNative.native_time_simulation`, `GateBinary.binary_time_simulation`,
  `GateBinary.binary_time_simulation_budget`, `GateSynth.native_time_simulation_synth`,
  `GateSynth.binary_time_simulation_synth`, `GateSynth.binary_time_simulation_budget_synth`;
  `GateODE.Time.solver`, `GateNative.native_ode_time_solver`,
  `GateBinaryODETime.binary_ode_time_solver`, `GateSynth.native_ode_time_solver_synth`,
  `GateBinaryODETime.binary_ode_time_solver_synth`,
  `GateSynthTrials.native_ode_time_solver_trials`,
  `GateSynthTrials.binary_ode_time_solver_trials`,
  `GateODEBudget.binary_ode_time_budget_trials`.
* The query-level mesh layer: meshes `TimeDependentExtensions.IsMesh`, the slot-to-sample map
  `TimeDependentExtensions.slotPiece` (`TimeDependentExtensions.pieceOf` as an element of
  `Fin M`), blocks `TimeDependentExtensions.blockLength`, piecewise propagators
  `TimeDependentExtensions.IsPiecewisePropagator`, the refined certificate estimate
  `TimeDependentExtensions.refined_error`, existence
  `TimeDependentExtensions.exists_piecewise_propagator`; for the ODE
  `TimeDependentExtensions.ODEMesh.meshRecurrence`, `TimeDependentExtensions.ODEMesh.mesh_error`,
  `TimeDependentExtensions.ODEMesh.piecewise_norm_le`; integral-sense propagators
  `IntegrablePathSimulation.Propagator.IsPropagator` with
  `IntegrablePathSimulation.Propagator.IsPropagator.refined_error` and
  `IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn`, and for glued piecewise paths
  `IntegrablePathSimulation.Propagator.glue`,
  `IntegrablePathSimulation.Propagator.isPropagator_glue`,
  `IntegrablePathSimulation.Propagator.ae_star_glue`,
  `IntegrablePathSimulation.Propagator.intervalIntegrable_glue`,
  `IntegrablePathSimulation.Propagator.sum_integral_glue`; classical piecewise ODE solutions
  `TimeDependentExtensions.ODE.exists_piecewise_solution`; reindexed sampled-time data
  `ODELowerBoundExtensions.Release.reindexData`, `ODELowerBoundExtensions.Release.stageData`.
* Reused without change: the circuits and protocols with all their counts
  (`GateCircuit.SlotSim.simCircuitT`, `GateNative.nativeSimT`, `GateBinary.binaryTimeSim`,
  `GateODE.Time.TParams.protocol`, `GateNative.nprotocol` with `GateNative.tnprepC`,
  `GateBinaryODETime.PubT.prep`, `GateSynth.synthBudget`, `GateSynth.sprotocol`,
  `GateSynthTrials.synthPrep`); the simulation estimate `GateCircuit.SlotSim.simulationT`; the
  native circuit lemmas `GateNative.hcirc_valid`, `GateNative.hcirc_nCalls`,
  `GateNative.hcirc_nGates`, `GateNative.hcirc_error`, `GateNative.card_HW`; the ODE proof
  chain `GateODE.Time.TParams.select_error`, `GateODE.Time.TParams.lchs_error`,
  `GateODE.Time.TParams.source_sum`, `GateODE.Time.TParams.coeffW_mass`,
  `GateODE.Time.TParams.target_norm_le`, `GateODE.Time.TParams.decoded_eq`,
  `GateODE.Time.TParams.trialC_seed`, `ODEActualSourceError.actual_source_certificate`,
  `ODEGroverActual.randomized_certificate`, `TimeDependentODE.Sampling.target_budget`,
  `GateODE.Time.recurrence_congr`; the native ODE lemmas `GateNative.oprep_approx`,
  `GateNative.tsrcMacro_approx`, `GateNative.native_trial_bounds`,
  `GateNative.noutcome_of_bounds`; the binary-data constructions
  `GateBinaryODETime.PubT.selectHyp`, `GateBinaryODETime.PubT.nativeOK`,
  `GateBinaryODETime.binary_ode_time_counts`; the synthesis lemmas
  `GateSynth.synthBudget_spec`, `GateSynth.synthBudget_error`, `GateSynth.gates_log_le`,
  `GateSynth.soutcome`, `GateSynthTrials.synthPrep_approx`,
  `GateSynthTrials.native_trial_bounds10`, `GateODEBudget.binary_ode_time_sizes`.

**Endpoints of this library.**

* Hamiltonians, exact gates: `time_simulation_certified` (uniform slots),
  `time_simulation_mesh` (nonuniform mesh), `time_simulation_lipschitz` (the released Lipschitz
  conclusion as a corollary); slot exponents `meshExponent` (`mesh_exponent_spec`).
* Hamiltonians, native gates: `native_time_simulation_certified`,
  `native_time_simulation_mesh`.
* Hamiltonians, binary sparse data: `binary_time_simulation_certified`,
  `binary_time_simulation_budget_certified`, `binary_time_simulation_mesh`,
  `binary_time_simulation_budget_mesh`; the clock data `clockData` and the oracle identity
  `primsT_clockData`; slot exponents `slotExponent` (`slotExponent_round_spec`).
* Hamiltonians, finite gate sets: `native_time_simulation_certified_synth`,
  `native_time_simulation_mesh_synth`, `binary_time_simulation_certified_synth`,
  `binary_time_simulation_mesh_synth`, `binary_time_simulation_budget_certified_synth`.
* ODEs, exact gates: `ODE.ode_time_solver_certified`, `ODE.ode_time_solver_mesh`;
  satisfiability `ODE.certified_of_instanceOK`.
* ODEs, native gates: `ODE.native_ode_time_solver_certified`, `ODE.native_ode_time_solver_mesh`.
* ODEs, binary sparse data: `ODE.binary_ode_time_solver_certified`,
  `ODE.binary_ode_time_solver_mesh`.
* ODEs, finite gate sets, every trial synthesised: `ODE.native_ode_time_solver_certified_synth`,
  `ODE.native_ode_time_solver_mesh_synth`, `ODE.binary_ode_time_solver_certified_synth`,
  `ODE.binary_ode_time_solver_mesh_synth`.
* ODEs, finite gate sets with the per-trial claim: `ODE.native_ode_time_solver_certified_trials`,
  `ODE.native_ode_time_solver_mesh_trials`, `ODE.binary_ode_time_solver_certified_trials`,
  `ODE.binary_ode_time_solver_mesh_trials`, and the budget forms
  `ODE.binary_ode_time_budget_certified_trials`, `ODE.binary_ode_time_budget_mesh_trials`.
* Non-vacuity (module `NonVacuity`): `time_simulation_mesh_piecewise_constant`,
  `time_simulation_mesh_glued`, `slotExponent_native_mesh_spec`,
  `slotExponent_binary_mesh_spec`, `ODE.released_time_solver_outcome`,
  `ODE.meshCertificate_samples_zero_forcing`, `ODE.meshCertificate_zero_forcing_le`,
  `ODE.meshCertificate_one_interval`, `ODE.slotCertificate_samples`, `ODE.exists_mesh_solution`.

**Clock, paths, propagators and certificates.**

* The uniform clock of the released circuits has `2^m` slots, slot `k` being
  `[slotMesh t m k, slotMesh t m (k + 1)] = [k t/2^m, (k+1) t/2^m]`; its ideal output is the
  ordered product `slotEvolution Hs t m = ∏_k exp(-i (t/2^m) H̃_k)` (later slots to the left).
* A mesh is `tm : ℕ → ℝ` with `TimeDependentExtensions.IsMesh tm M T` (`t_0 = 0`, `t_M = T`,
  monotone; empty intervals are allowed). Slot `k` reads the samples of the interval
  `σ k = TimeDependentExtensions.slotPiece tm T 2^m M k` that contains `k T/2^m`.
* Integral-sense propagators `IntegrablePathSimulation.Propagator.IsPropagator H U T`
  (`U(s) = 1 - i ∫_0^s H(u) U(u) du` on `[0, T]`) of paths self-adjoint at almost every time and
  interval integrable as operator paths (discontinuities anywhere); classical piecewise
  propagators `TimeDependentExtensions.IsPiecewisePropagator Hp tm M U` (`U 0 = 1`, a classical
  solution of `U' = -i Hp_r U` on every closed interval, one-sided derivatives at the
  breakpoints) of pieces self-adjoint and interval integrable on the closed intervals.
* Hamiltonian certificates: `∑_{k < 2^m} ∫_{kt/2^m}^{(k+1)t/2^m} ‖H(u) - H̃_k‖ du` on the
  uniform slots and `∑_{r < M} ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` on a mesh (with `H_r(u)` for
  piecewise paths). For binary data the paths are matrix paths, the norms are those of
  `SparseStateOverlap.matrixOperator`, and the propagators are those of the lifted path
  `u ↦ qlift en (H u)`.
* ODE solutions are classical piecewise: `x' = -G_q(u) x + b_q(u)` on every closed interval
  (`TimeDependentODE.SolvesODE`, one-sided derivatives at the breakpoints) with accretive,
  interval-integrable generator pieces and interval-integrable forcing pieces,
  `‖b_q(u)‖ ≤ b_max`. Uniform slots: `ODE.slotCertificate p Hs Ls b̃ G b ‖x(0)‖ b_max`
  `= (r₀ + b_max T) ∑_k ∫ ‖G_k - (L_k + i H_k)‖ + ∑_k ∫ ‖b_k - b̃_k‖ + Λ h²/2 ∑_k ‖b̃_k‖`,
  with `r₀ = ‖x(0)‖`, `h = T/2^m`, `Λ = λ_H + λ_D`. Mesh of `Mm` intervals:
  `ODE.meshCertificate p tm Mm H L b̃ G b r₀ b_max = (r₀ + b_max T) ∑_q ∫ ‖G_q - (L_q + i H_q)‖`
  `+ ∑_q ∫ ‖b_q - b̃_q‖ + ∑_q (Λ (Δ_q + h)² + h) ‖b̃_q‖ + Mm h Λ (r₀ + ∑_q Δ_q ‖b̃_q‖)`,
  `Δ_q = t_{q+1} - t_q`; `ODE.meshCertificate_le` bounds it by the integrated certificates, the
  quadrature term `2 Λ ∑_q Δ_q² ‖b̃_q‖` and the refinement cost
  `h ((2 Λ T + 1) ∑_q ‖b̃_q‖ + Mm Λ (r₀ + ∑_q Δ_q ‖b̃_q‖))`. The mesh certificate compares the
  slot scheme with the solution through the mesh scheme, so it keeps the left-endpoint source
  quadrature of the mesh, which does not decrease with `m`: for one interval and data equal to
  the samples it contains `Λ (T + h)² ‖b̃‖` (`ODE.meshCertificate_one_interval`), against
  `Λ T h ‖b̃‖/2` in `ODE.slotCertificate` (`ODE.slotCertificate_samples`); inserting breakpoints
  decreases it.
* Notation below: `runT` is the exact-gate semantics `GateCircuit.SlotSim.runT` and `io` the
  clean input `GateCircuit.Sim.io`; `sysEmb`, `cleanEmb` are `GateNative.sysEmb`,
  `GateNative.cleanEmb`; `primsT`, `prims`, `slotPrim`, `qlift` are `GateBinary.primsT`,
  `GateBinary.prims`, `GateBinary.slotPrim`, `GateBinary.qlift`; `steps` is
  `TimeSchedule.steps`, `time s t γ = √s t/γ` is `CayleyClockInterface.time`, and `d`, `r` are
  the released filter degree `GateCircuit.Sim.fDeg` and reuse-register size
  `GateCircuit.Sim.simR` (`2d + 2 ≤ 2^r ≤ 4 (d+1)`).

**Hypotheses and guarantees: Hamiltonians.**

* `time_simulation_certified`: `t ≥ 0`, `α > 0`, `1 ≤ Q`, `q̄ ≤ Q`, `0 < ε ≤ 1`, the subdivision
  condition `steps (α t) (ε/6) ≤ 2^m`, `U_J` unitary and, at every slot `k < 2^m`, a unitary
  private operation `D k` with the clock promises of the released analysis for `H̃_k/α`
  (`(1 - D k) R1 k = 1 = R1 k (1 - D k)`, `‖R1 k‖ ≤ Q`, the boundary identity
  `(U_J ι₀)† R1 k (U_J ι₀) = (1 + i H̃_k/α)/2`, the endpoint bound `b` with `b² ≤ q̄/2`), for
  self-adjoint samples with `‖H̃_k‖ ≤ α`. The released circuit `simCircuitT a (α t) Q q̄ (ε/2) m`
  has valid instructions, exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`, at most
  `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits,
  `d ≤ 128 (α t q̄ + Q (1 + log(6/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`, and its full output
  `runT U_J D C ∘ io` is within `ε` of `io ∘ U(t)` for every integral-sense propagator and
  every classical piecewise propagator (one piece per slot) whose certificate is at most `ε/2`.
* `time_simulation_mesh`: a mesh of `M ≥ 1` intervals on `[0, T]`, `T > 0`, the promises for
  the supplied operations and samples `D_r`, `H̃_r` of the intervals (`r < M`),
  `steps (α T) (ε/6) ≤ 2^m` and the rounding condition `4 M α T ≤ ε 2^m`: the same circuit and
  counts, slot `k` running `D_{σ k}` (`runT U_J (fun k => D (slotPiece tm T 2^m M k))`), and
  error `ε` for every integral-sense and every classical piecewise propagator (one piece per
  mesh interval) with mesh certificate at most `ε/4`. `meshExponent α T ε M` (the released
  `GateCircuit.SlotSim.meshExp` with the rate `M α / T`) meets both conditions with
  `2^m < 2 max(steps (α T) (ε/6), ⌈4 M α T/ε⌉)` (`mesh_exponent_spec`).
* `time_simulation_lipschitz`: the error conclusion of the released
  `GateCircuit.SlotSim.gate_efficient_time_simulation` (Lipschitz path, sample errors `δ`,
  `4 β t² ≤ ε 2^m`, `4 t δ ≤ ε`, so that the certificate is at most `3ε/8`), for every classical
  propagator, from `time_simulation_certified`; the counts are those of
  `time_simulation_certified`, and the existence of a classical propagator is not restated.
* `native_time_simulation_certified`: the hypotheses of `GateNative.native_time_simulation`
  without the path (unitary primitive oracles, `U_J` given by gates `UJg` with `GateOK 3`, a
  public native operation `nd` with `GateNative.NativeOK` for the slot-selected family,
  arithmetic `ar` with `GateNative.ArithOK` at accuracy `ζ ≥ 0`, the clock promises at every
  slot), `steps (α t) (ε/12) ≤ 2^m` and `48 d ζ ≤ ε`: the native circuit
  `nativeSimT a m (α t) Q q̄ ε UJg nd ar` has valid instructions, exactly `12 d` times the
  primitive calls of `nd.V` of every kind, at most
  `200 (d+1)(a+m+r+1) + 84 d |UJg| + 6 d (2 |V| + 2 |circ| + 2 bP + bT + 1)` elementary gates,
  the stated qubits, the degree and register bounds, and full-output error `ε` on the system
  embedding `sysEmb io` against every integral-sense and every classical piecewise propagator
  with certificate at most `ε/4`.
* `native_time_simulation_mesh`: a mesh, operations and samples per interval, `NativeOK` for the
  slot-selected family `w ↦ D_{σ w}` on the uniform clock, `steps (α T) (ε/12) ≤ 2^m`,
  `8 M α T ≤ ε 2^m` and `48 d ζ ≤ ε`: the counts of the uniform theorem and error `ε` with mesh
  certificate at most `ε/8`. An admissible exponent is
  `m = slotExponent (steps (α T) (ε/12)) (8 M α T/ε)` (`slotExponent_round_spec`,
  `slotExponent_native_mesh_spec`).
* `binary_time_simulation_certified`: the released binary format (`k`-bit indices `en`,
  `s = 2^σ` slots on the lowest `σ` bits, `hrange`, `b ≥ 1`, entries `c₀ (X + i Y)`), Hermitian
  samples `D.matrix (x, r)` with row and column norms at most `1`, `0 < γ ≤ 1`, `0 < ε ≤ 1`,
  `0 < ζ ≤ 1`, `steps τ' (ε/12) ≤ 2^m` (`τ' = time s t γ = √s t/γ`) and `48 d ζ ≤ ε`:
  `binaryTimeSim k b m σ hσ s γ c₀ t ε ζ` has valid instructions, exactly `12 d` times `2`
  row-location, `2` column-location and `1` value calls, the released gate and qubit counts and
  degree bounds, and full-output error `ε` against every integral-sense propagator of the lift
  of a matrix path Hermitian almost everywhere and interval integrable, and every classical
  piecewise propagator of the lift of a piecewise matrix path, with certificate at most `ε/4`.
* `binary_time_simulation_budget_certified`: for `s ≥ 1`, `t ≥ 0`, `0 < ε ≤ 1` there is one
  `γ ∈ (0, 1]` with `γ √s ≥ 1` and `d ≤ 4608 q`, `q = ImprovedPrecisionBudget.shape s t
  (log(2/ε)) = √s t + √(s t log(2/ε)) + log(2/ε)`, chosen before the data, the path and `m`;
  for all data, inputs and slot exponents with the subdivision condition alone, and
  `221184 q ζ ≤ ε`: at most `55296 q` times `2 + 2 + 1` calls,
  `200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)` gates (`G_C = GateNative.privGates`),
  `2^r ≤ 4 (4608 q + 1)`, and error `ε` against integral-sense propagators with certificate at
  most `ε/4`.
* `binary_time_simulation_mesh`: mesh data `D_m : Data (X × Fin M)` in the same format with the
  same promises, `T > 0`, `steps τ' (ε/12) ≤ 2^m`, `8 M τ' ≤ ε 2^m` and `48 d ζ ≤ ε`: the
  circuit `binaryTimeSim` run on the clock data `clockData D_m hM tm T m` (the released
  `ODELowerBoundExtensions.Release.stageData` along `TimeDependentExtensions.pieceOf`), whose
  time-indexed oracles are the coherent sampled-time oracles of the mesh data,
  `primsT (clockData D_m) en x = slotPrim (w ↦ prims D_m en (x, σ w))`
  (`primsT_clockData`, `prims_reindexData`); the counts and qubits of the uniform theorem; error
  `ε` against every integral-sense and every classical piecewise propagator of the lifted path
  with mesh certificate at most `ε/8`.
* `binary_time_simulation_budget_mesh`: the budget form on a mesh. For `s ≥ 1`, `T > 0` and
  `0 < ε ≤ 1` the rescaling `γ` of `binary_time_simulation_budget_certified` (`d ≤ 4608 q`) is
  chosen before the mesh, the data and the slot exponent; for every mesh of `M ≥ 1` intervals,
  mesh data with the promises above, `steps τ' (ε/12) ≤ 2^m`, `8 M τ' ≤ ε 2^m` and
  `221184 q ζ ≤ ε`, the circuit on the clock data has at most `55296 q` times `2 + 2 + 1`
  calls, at most `200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)` gates and
  `2^r ≤ 4 (4608 q + 1)`, and error `ε` against integral-sense propagators of the lifted path
  with mesh certificate at most `ε/8`. An admissible exponent is
  `m = slotExponent (steps τ' (ε/12)) (8 M τ'/ε)` (`slotExponent_binary_mesh_spec`).
* Finite gate sets (`GateSynth.Synthesis 𝒢 X L`, synthesis budget `ε' > 0`, every elementary
  gate synthesised at accuracy `ε'/(N+1)`): the `*_synth` theorems state that the synthesised
  circuit consists of valid gates of `𝒢` (`GateSynth.GateOf`) and primitive calls, makes the
  calls of the native circuit, has at most `N L(ε'/(N+1))` gates for the native gate count `N`
  (bounded as above) and `|X|` more qubits, and has full-output error `ε + ε'` on the clean
  system embedding `cleanEmb ∘ sysEmb io` under the respective certificate.
  `binary_time_simulation_budget_certified_synth`: for `L ζ ≤ c₁ log(1/ζ) + c₀` and
  `0 < ε' ≤ 1`, at most `G (c₁ log((G+1)/ε') + c₀)` gates with
  `G = 200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`.

**Hypotheses and guarantees: dissipative ODEs** (`x' = -(L + i H) x + b`).

* Public data `p : GateODE.Time.TParams` with `p.PublicOK` (the released public conditions,
  including the released subdivision condition on `p.m`); supplied operations
  `σ : GateODE.Time.TOracles` (`U_J`, the private operations `D z r` of every label and slot,
  the loading `J` and the weight preparation `Wp`); a unit seed `v`.
* `ODE.SourceOK p v J Wp x₀ b̃`: unitary loading and weight preparation, the released zero
  column `Wp |0⟩ = ∑_s √(‖z_s‖/B) |s⟩` of the source mass `B = p.mass x₀ b̃`, and the loaded
  directions `J (false, 0) v = x₀/‖x₀‖`, `J (true, w) v = b̃_w/‖b̃_w‖` (when nonzero).
  `ODE.CoreOK p v σ Hs Ls x₀ b̃`: the released `GateODE.Time.TParams.SelectHypT` (unitarity,
  self-adjoint samples with `‖H_r‖ ≤ λ_H`, `‖L_r‖ ≤ λ_D`, the clock promises at every label and
  slot), `L_r ≥ 0` and `ODE.SourceOK`: the released `GateODE.Time.TParams.InstanceOK` without the
  path, the solution and the budget. `ODE.TargetOK p Hs Ls x₀ b̃ x_T`: `x_T ≠ 0`,
  `B ≤ g ‖x_T‖` and `‖x_T - y‖ ≤ ε B/(2000 g)` for the discretised target
  `y = p.target Hs Ls x₀ b̃` (the exponential left-endpoint recurrence of the slot data).
* `ODE.ode_time_solver_certified`: the released protocol `p.protocol v` and all sixteen count
  and size conclusions of `GateODE.Time.solver`; for every instance with `ODE.CoreOK` and every
  classical piecewise solution on the uniform slots with `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and
  `ODE.slotCertificate ≤ ε B/(2000 g)`, the released `GateODE.Time.TParams.Outcome`: unitary
  trials, mean success at least `1/4`, success probability at least `175/256 > 2/3`, every
  successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a phase, conditional output density
  within trace distance `ε`. `ODE.certified_of_instanceOK`: every instance of the released
  theorem satisfies these hypotheses, with the restricted paths as pieces
  (`ODE.slotCertificate_le_discretisation`: the released budget bounds the certificate).
* `ODE.ode_time_solver_mesh`: the same protocol and counts; for a mesh of `Mm ≥ 1` intervals on
  `[0, T]`, mesh samples `H_q` (self-adjoint, `‖H_q‖ ≤ λ_H`), `L_q` (`L_q ≥ 0`,
  `‖L_q‖ ≤ λ_D`) and forcing samples `b̃_q` on every interval, `ODE.CoreOK` for the slot data
  `(H_{σ k}, L_{σ k}, b̃_{σ k})`, one generator and one forcing piece per mesh interval,
  `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` (the source mass of the slot data) and
  `ODE.meshCertificate ≤ ε B/(2000 g)`: the released `Outcome`.
* `ODE.native_ode_time_solver_certified`, `ODE.native_ode_time_solver_mesh`: the native protocol
  `GateNative.nprotocol (GateNative.tnprepC p UJg nd ar loadC wpC) (2g)` with the counts of
  `GateNative.native_ode_time_solver`; for unitary primitive oracles, `NativeOK` for the label-
  and slot-selected private operations, loading and weight-preparation circuits within `ζs` of
  `J` and `Wp`, `24 d ζ + 3 ζs ≤ ν`, and the conditions of the exact-gate theorems:
  `GateNative.NOutcome` (unitary trials, mean success at least `1/4`, every successful trial
  within `ε/500` of `x(T)/‖x(T)‖` up to a phase, success at least `175/256`, conditional output
  within trace distance `ε`).
* `ODE.binary_ode_time_solver_certified`, `ODE.binary_ode_time_solver_mesh`: the protocol of
  `GateBinaryODETime.PubT.prep` with the counts of `GateBinaryODETime.binary_ode_time_counts`;
  for inputs whose samples have Hamiltonian and dissipative parts with row and column energies
  at most `η_H²`, `η_D²` and accretive dissipative parts, sources with `ODE.SourceOK` and the path
  conditions: `NOutcome`, the certificates being taken against the lifted samples
  `L_r + i H_r = M̂_r` (on a mesh: `ODE.meshH`, `ODE.meshL` with `ODE.meshGens_eq`, the protocol
  run on the clock data `clockData D_m`; `ODE.binary_coreOK`, `ODE.mesh_promises`,
  `ODE.binary_mesh_targetOK`).
* `*_synth`: the protocol `GateSynth.sprotocol hS (ε/200)` with the counts of
  `GateSynth.native_ode_time_solver_synth`, resp. `GateBinaryODETime.binary_ode_time_solver_synth`,
  and `GateSynth.SOutcome` (success at least `2/3`, conditional output within `ε`).
* `*_trials` (`GateSynthTrials.AdjClosed 𝒢`, `GateSynthTrials.zeroTestKinds ⊆ 𝒢`): the protocol
  `GateNative.nprotocol (GateSynthTrials.synthPrep hS (ν/3) …) (2g)` with the counts of
  `GateSynthTrials.native_ode_time_solver_trials`, resp.
  `GateSynthTrials.binary_ode_time_solver_trials`, and `NOutcome` (every successful trial
  within `ε/500`). The budget forms have the budget of
  `GateODEBudget.binary_ode_time_budget_trials` (`γ = GateODEBudget.gammaOf …`,
  `B = GateODEBudget.prepBoundT q loadC wpC`, at most `7864320 g q*` calls of each sampled-time
  oracle besides the source calls) under `98304 q* ζ + 3 ζs ≤ ν`.

**Proof map** (module paths relative to `GateEfficientMesh/`).

* `Slots`: the uniform clock (`slotMesh`, `isMesh_slotMesh`, `slotEvolution`), the slot
  product as the released refined product (`refinedEvolution_eq_slotEvolution`), the
  certificate bounds `slot_error_integral`, `slot_error_piecewise` and on meshes
  `mesh_slot_error`, `mesh_slot_error_piecewise` (from the released
  `IntegrablePathSimulation.Propagator.IsPropagator.refined_error` and
  `TimeDependentExtensions.refined_error`, with the rounding `M (T/2^m) Λ`), satisfiability
  (`exists_slot_propagator`, `slot_certificate_le_of_lipschitz`).
* `Exact`: `slot_product_error` (the released `GateCircuit.SlotSim.simulationT` against any
  operator), the endpoints and slot exponents. `Native`: `native_slot_bounds` (the released
  circuit lemmas and `slot_product_error`), endpoints. `Binary`: contractive operator maps
  (`intervalIntegrable_map`, `integral_map_le`), the lifted samples (`lifted_sample`,
  `intervalIntegrable_qlift`, `lifted_integral_le`), `binary_slot_bounds` (the released
  discharge of the native hypotheses for binary data), `binary_slot_error_integral`,
  `binary_slot_error_piecewise`. `BinaryTheorem`: endpoints, the budget through the released
  `GateCircuit.SlotSim.sparse_counts`. `BinaryMesh`: `clockData`, `clockData_matrix`,
  `clockData_slot`, `clockData_decode`, `prims_reindexData`, `primsT_clockData`,
  `meshSample`, the mesh endpoint and its budget form `binary_time_simulation_budget_mesh`
  (the counts of `binary_time_simulation_budget_certified` for the clock data). `Synth`: the
  synthesis budget lemmas.
* `ODE/Core`: `ODE.SourceOK`, `ODE.CoreOK`, `ODE.TargetOK`, `ODE.CoreOK.unitary` and the
  released proof chain restated for these conditions: `ODE.target_facts_of` (the released
  `TimeDependentODE.Sampling.target_budget`), `ODE.prep_certificate_of`, `ODE.trial_bounds_of`,
  `ODE.outcome_of`.
* `ODE/Target`: `ODE.slotCertificate`, `ODE.slot_target_error` (the released
  `TimeDependentExtensions.ODEMesh.mesh_error` and
  `TimeDependentExtensions.ODEMesh.piecewise_norm_le` on the slot mesh,
  `ODE.meshRecurrence_const`).
  `ODE/Exact`: `ODE.slotCertificate_le_discretisation`, `ODE.certified_of_instanceOK`, the
  endpoint. `ODE/Native`: `ODE.native_outcome_of` (the released native lemmas with
  `ODE.prep_certificate_of`), the endpoint. `ODE/Binary`: `ODE.binary_coreOK`, the endpoint.
* `ODE/MeshScheme`: the refinement of the mesh recurrence into slots, block by block
  (`ODE.sum_mask`, `ODE.sum_blocks`, `ODE.sum_range_le_sq`, `ODE.mask_blockStart`,
  `ODE.maskedPropagator_blockStart`, `ODE.maskedPropagator_sub_le`, `ODE.block_error`) and
  `ODE.slot_mesh_recurrence`: the slot recurrence of the slot data is within
  `Mm h Λ ‖y₀‖ + ∑_q (Λ (n_q h)²/2 + |n_q h - Δ_q| + Δ_q Mm h Λ) ‖b̃_q‖` of the mesh recurrence,
  `n_q = blockLength tm T 2^m q` the number of slots of interval `q`.
* `ODE/MeshTarget`: `ODE.meshCertificate`, `ODE.meshCertificate_le`, `ODE.mesh_target_error`.
  `ODE/Mesh`: `ODE.target_congr`, the exact and native mesh endpoints. `ODE/BinaryMesh`:
  `ODE.meshH`, `ODE.meshL`, `ODE.meshGens_eq`, `ODE.HsT_clockData`, `ODE.LsT_clockData`,
  `ODE.mesh_promises`, `ODE.binary_mesh_targetOK`, the binary mesh endpoint.
* `ODE/Synth`: the `*_synth` endpoints through `GateSynth.soutcome`. `ODE/Trials`:
  `ODE.trials_outcome_of` (the released per-trial chain with `ODE.prep_certificate_of` and
  `ODE.target_facts_of`), the `*_trials` endpoints and the budget forms (with
  `GateODEBudget.binary_ode_time_sizes`).
* `NonVacuity`: the satisfiability of the hypotheses beyond the released ones (see the
  formalisation choices).

Every theorem of the library is axiom-audited in `GateEfficientMesh/Audit.lean`.

**Formalisation choices.**

* Nonuniform meshes are refined into the uniform clock of the released circuits through the
  slot-to-sample map `slotPiece`; all slots keep the released Cayley step `α T/2^m`, so the
  boundary circuit, the counts and the subdivision condition are the released ones, and the mesh
  enters the counts only through `m`. The rounding of the interval lengths to multiples of
  `T/2^m` costs `M (T/2^m) Λ` (Hamiltonians, `Λ` the sample bound) and the `O(2^{-m})` terms of
  `ODE.meshCertificate` (ODE, with the per-slot forcing).
* On a mesh, slot `k` uses the supplied operation of the sample of its interval: exact gates
  `D (slotPiece tm T 2^m M k)`; native gates `NativeOK` for this slot-selected family (the
  presentation of the mesh data on the uniform clock is part of the native implementation, as
  the slot selection is in the released theorem); binary data the clock data `clockData`, the
  released `ODELowerBoundExtensions.Release.stageData` (reindexed data
  `(x, k) ↦ D_m (x, σ k)`), with the oracle identity `primsT_clockData`. The slot-to-sample map
  is not a counted circuit.
* Error budgets: exact gates `ε/2` for the released circuit at accuracy `ε/2` and `ε/2` for the
  certificate (mesh: `ε/4` certificate and `ε/4` rounding); native and binary `3ε/4` for the
  circuit (simulation at `ε/4`, private calls with `48 d ζ ≤ ε`) and `ε/4` for the certificate
  (mesh: `ε/8` and `ε/8`). The released freezing and sample-error conditions are replaced by the
  certificate, and on a mesh by the certificate and the rounding condition. ODE: the released
  budget `ε B/(2000 g)` for `‖x(T) - y‖`, now with the certificates.
* Both propagator notions are covered for Hamiltonians: integral-sense propagators (merely
  integrable self-adjoint paths) and classical piecewise propagators (one piece per slot or
  mesh interval). The budget forms state the integral-sense guarantee.
* The hypotheses are satisfiable. Hamiltonians: piecewise constant paths equal to the samples
  have a piecewise propagator and certificate `0` (`exists_slot_propagator`; on a mesh the
  released `TimeDependentExtensions.exists_piecewise_propagator`, whose propagator is also an
  integral-sense propagator of the glued path by
  `IntegrablePathSimulation.Propagator.isPropagator_glue`), a `β`-Lipschitz path with sample
  errors `δ` has certificate at most `β t²/(2 · 2^m) + t δ`
  (`slot_certificate_le_of_lipschitz`), the released exact-gate Lipschitz theorem is a special
  case (`time_simulation_lipschitz`; the native, binary-data and finite-gate-set Lipschitz
  theorems are special cases by the same estimate, the certificate being at most `3ε/16` under
  their conditions `8 β t² ≤ ε 2^m` and `8 t δ ≤ ε`, but they are not restated), and the
  rounding conditions hold for `meshExponent` and `slotExponent`. ODEs: every instance of the
  released theorem satisfies the certified hypotheses (`ODE.certified_of_instanceOK`), and on a
  mesh the refinement cost is `O(2^{-m})` (`ODE.meshCertificate_le`): for pieces equal to the
  samples the integrated certificates vanish, and the mesh certificate holds whenever the
  quadrature term `2 Λ ∑_q Δ_q² ‖b̃_q‖` is below the budget (inserting breakpoints decreases it)
  and the clock is fine enough. The module `NonVacuity` checks these instances:
  `time_simulation_mesh` applies to the piecewise constant path of the mesh samples with
  `m = meshExponent α T ε M`, through its classical and its integral-sense conjunct
  (`time_simulation_mesh_piecewise_constant`, `time_simulation_mesh_glued`); `slotExponent`
  meets the conditions of the native and binary-data mesh theorems
  (`slotExponent_native_mesh_spec`, `slotExponent_binary_mesh_spec`); the released solver
  guarantee follows from the certified theorem (`ODE.released_time_solver_outcome`); with zero
  forcing and generator pieces equal to the mesh samples, the mesh certificate is the refinement
  cost `Mm h Λ ‖x(0)‖` and meets the budget when `2000 g Mm Λ T ≤ ε 2^m`
  (`ODE.meshCertificate_samples_zero_forcing`, `ODE.meshCertificate_zero_forcing_le`);
  classical piecewise solutions exist for pieces equal to the samples
  (`ODE.exists_mesh_solution`); and for one mesh interval the quadrature term is computed
  (`ODE.meshCertificate_one_interval`, against `ODE.slotCertificate_samples`).
* ODE: the released `InstanceOK` couples the supplied unitaries with a Lipschitz path; the
  released proofs (`GateODE.Time.TParams.outcome`, `GateODE.Time.TParams.prep_certificate`,
  `GateNative.native_time_outcome`, the instance part of
  `GateSynthTrials.native_ode_time_solver_trials`) use the path only through the target facts
  and have no public form for other instances. They are reassembled from the public lemmas for
  instances given by `ODE.CoreOK` and `ODE.TargetOK` (`ODE.outcome_of`, `ODE.native_outcome_of`,
  `ODE.trials_outcome_of`); the counts are taken from the released theorems.
* ODE certificates: the generator certificate is weighted by the energy bound
  `‖x(0)‖ + b_max T` (the released `TimeDependentExtensions.ODEMesh.piecewise_norm_le`); the
  source quadrature is left-endpoint on the slots; on a mesh the forcing sample of slot `k` is
  that of its interval (`b̃_{σ k}`), so the source mass and the loaded forcing directions are
  those of the slot data.
  The mesh samples carry the sample promises on every interval, also on intervals that contain
  no slot point (derived from the data bounds for binary data, `ODE.mesh_promises`).
* The native Hamiltonian counts are assembled from the released circuit lemmas
  (`GateNative.hcirc_valid`, `GateNative.hcirc_nCalls`, `GateNative.hcirc_nGates`,
  `GateNative.card_HW`), since the released `GateNative.native_time_simulation` states them
  together with the path conditions; they coincide with the released counts.
* `regENormedAddMonoid` is a scoped instance of `SparseHamiltonian.GateMesh`: operators on
  registers with a payload form an `ENormedAddMonoid`, which instance search does not reach
  through the `PiLp` norm; it is used to state interval integrability of operator paths (the
  native Hamiltonian endpoints, all native and binary-data ODE endpoints and
  `intervalIntegrable_qlift`). It is the canonical structure of the operator norm, and no other
  instance exists on these types; outside the namespace, state these hypotheses after
  `open scoped SparseHamiltonian.GateMesh`.

**Not formalised.**

* Nonuniform Cayley steps (slot steps `α Δ_r`) and the corresponding boundary circuits; the
  refinement replaces them.
* The branch-dependent meshes and coherent per-label angles of Lemma `ode:lem:gate-select`: as
  in the released time-dependent ODE solvers, the source branches are masked on one common mesh.
* A counted circuit computing the slot-to-sample map from an arbitrary table of `M`
  breakpoints: comparing the slot word with every breakpoint would add a factor `M` (or one
  comparator per breakpoint) to every private call; the map is part of the data presentation.
* Carathéodory solutions of the dissipative equations (integrable generator paths with
  discontinuities inside mesh intervals); the ODE theorems use classical solutions on each
  closed interval.
* The piecewise-propagator guarantee in the Hamiltonian budget forms (integral-sense only), and
  the absolute-constant forms of `hs:eq:gate-total` and `ode:eq:gate-main` (explicit-constant
  budget forms are stated on the uniform slots and on meshes: `binary_time_simulation_budget_mesh`
  and `ODE.binary_ode_time_budget_mesh_trials`).
* On a mesh, a direct comparison of the slot scheme of the dissipative equation with the
  solution: `ODE.meshCertificate` compares through the mesh scheme and keeps the left-endpoint
  quadrature of the mesh, which does not decrease with `m` (for one mesh interval it is
  `Λ (T + h)² ‖b̃‖`, against `Λ T h ‖b̃‖/2` in `ODE.slotCertificate`;
  `ODE.meshCertificate_one_interval`, `ODE.slotCertificate_samples`).
* Restatements of the released native, binary-data and finite-gate-set Lipschitz theorems and
  of the existence conjuncts of the released theorems.
* The construction of the loading and weight-preparation circuits (hypotheses, as in the
  released theorems); the cases `T = 0` and zero bounds, which the released public conditions
  exclude (see the released library `ZeroTimeGateODE`); lower bounds.

**Provenance.** This library is new, written against the released package: it imports
`GateEfficientTimeDependent`, `TimeDependentExtensions`, `IntegrablePathSimulation`,
`GateEfficientNative`, `GateEfficientBinaryTime`, `GateEfficientSynthesis`,
`ODELowerBoundExtensions`, `GateEfficientODE`, `GateEfficientBinaryODETime`,
`GateEfficientSynthesisTrials` and `GateEfficientODEBudget` and changes none of them. The
statement guides of `GateEfficientTimeDependent` and `GateEfficientBinaryTime` predate this
library and list nonuniform meshes as not formalised, that of `GateEfficientBinaryODETime`
lists the regularity and sample certificates of the generator path and nonuniform meshes, that
of `IntegrablePathSimulation` states that the gate-level time-dependent theorems keep their
classical hypotheses, and those of `IntegrablePathSimulation` and `TimeDependentExtensions` list
the gate costs of the time slots as not formalised; these entries are superseded here, except
for nonuniform Cayley steps and the branch-dependent meshes of Lemma `ode:lem:gate-select`.
-/

set_option autoImplicit false
