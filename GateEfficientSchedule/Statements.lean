import GateEfficientSchedule.Native
import GateEfficientSchedule.Abstract

/-!
# Theorem `hs:thm:gates` and Lemma `hs:lem:abstract` with the manuscript's filter schedule, slot
count and error allocation: paper-to-Lean entry point

Theorem `hs:thm:gates` of the accompanying paper (gate-efficient sparse simulation, manuscript
line 3408) fixes the schedule

* `W = αTν`, `b = 32Q`, `k = ⌈4W/Q + log₂(4096/ε)⌉`, `d = k(b - 1)` (equation
  `hs:eq:gate-schedule`, line 3381), with the integer `Q = ⌈max{1, γ√s}⌉` of `hs:eq:params`
  (line 2444);
* `M` the least power of two at least `max{2, 4αT, (αT)^{3/2}/√(3ε)}`, `m = log₂ M`,
  `r = ⌈log₂(2d+2)⌉` (equation `hs:eq:gate-clocks`, line 3389);

and its proof allocates the error as follows (lines 3636-3660): the choice of `M` makes the
Cayley discretisation error at most `ε/4`, the schedule gives filter error `δ = ε/8`, so "the full
output error after amplification is therefore at most `ε/2` before gate approximation"; "give
each private call error `ξ = ε/(24d)`. Their total contribution is at most `ε/4`"; the remaining
known rotations are approximated "with total operator error at most `ε/4`". For the
time-dependent setting the theorem uses "the same circuit" on a uniform mesh of `M = 2^m ≥ 2`
slots satisfying `hs:eq:timegrid` (line 3059): `M ≥ max{1, 4αT, 6βT²/ε, (ΛT)^{3/2}/√ε}`, which
"makes each of the three summed contributions" of `hs:eq:timedisc` (line 3051), the Cayley error
`Λ³Δ³/12`, the freezing error `βΔ²/2` and the sample error `δ_val Δ` summed over the slots, "at
most `ε/12`". The proof of Lemma `hs:lem:abstract` (the general boundary-resolvent simulation
lemma, line 2506) uses the same allocation: "Take `δ = ε/8` in `hs:eq:kchoice`. Together with the
`ε/4` discretisation error, this gives ideal-gate error at most `ε/2`", with at most
`6(32Q - 1)⌈4W/Q + log₂(4096/ε)⌉` calls (equation `hs:eq:explicitcount`, line 2799).

The released gate-level endpoints use the formal schedule `SharpFilterSchedule.depth` at the filter
accuracy `ε/3` (`k_Lean = 1 + ⌈4W/Q + 2 log(3/ε)⌉`, `d_Lean = k_Lean(⌈32Q⌉ - 1)`; neither schedule
dominates the other for all `ε`), the slot count `steps(τ, ε/3)` of the released Cayley estimate
with the constant `1` in place of `1/12`, and, for time-dependent Hamiltonians, the released
freezing estimate with the constant `1` in place of `1/2`; the released form of the lemma,
`GateRemarks.abstract_simulation`, runs the released circuit and bounds the count by
`3840 (W + Q log(1/ε))`. This library proves the theorem and the lemma with the manuscript's
schedule, constants and allocation, and leaves the released definitions and endpoints unchanged.

No result from another paper is used. The released libraries are unchanged. Manuscript lines
refer to `sparse_quantum_algorithms.tex` (v24); the labels are the stable references. Every
theorem of the library is axiom-audited in `GateEfficientSchedule/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateSchedule` and are named relative to it below. Released declarations are
named relative to `SparseHamiltonian` (for example `GateCircuit.Sim.simCircuit`,
`SharpFilterSchedule.depth`), and so are those of the library `GateEfficientSelective` of the
same release (for example `GateSelective.selBudget`).

**Notation.** `τ = αT` is the normalised time and `q̄ = ν` the boundary moment bound of the
released clock hypotheses (`‖R₁ J‖ ≤ b`, `b² ≤ q̄/2`, `q̄ ≤ Q`), so the clock budget is
`W = τ q̄`; `L_Q = ⌈32Q⌉` is the released filter length (`SharpFilterSchedule.length`), equal to
`32Q` for the manuscript's integer `Q`; `w = τ/2^m` is the Cayley step.

**What was already released (cited, not redone).** The clock analysis
`SharpClockSimulation.exists_precise_implementation` and its slot-dependent form
`TimeDependent.exists_precise_implementationV`, the resolvent filter bound
`GlobalFilter.global_filter_norm_le` (generic in the filter length and depth),
`FilterDecay.filter_norm_le_clock_scale`, `FilterDepth.decay_le_of_log_depth`,
`SharpFilterSchedule.log_prefactor_ratio_le`, the smoothing, reuse and amplification layers
(`AmplifiedSmoothing.implementation_isometry`, `AmplifiedSmoothing.implementation_error`,
`GateBlockTransfer.amplified_error_le`), the gate-level circuit `GateCircuit.Sim.ampI` with its
counts, validity and agreement (`ampI_counts`, `ampI_valid`, `amp_agrees`,
`GateCircuit.SlotSim.ampT_agrees`), the Cayley contraction lemmas of `CayleyApproximation` and
`CayleyTransfer`, the propagator layer of `TimeDependent` (`SolvesOn`, `propagator_telescope`,
`exists_solvesOn_of_lipschitz`). From the library `GateEfficientSelective` of the same release:
the selective compiler and the supplied-circuit macros (`GateSelective.selBudget`,
`GateSelective.hcircP`, `GateSelective.privSel`). For Lemma `hs:lem:abstract`: the compressed
second moment in the Loewner order (`GateRemarks.second_moment_iff`), the exchange of `D` and `D†`
for negative times (`GateRemarks.flipDs`, `run_flipDs`, `nPriv_flipDs`, `nUJ_flipDs`,
`nGates_flipDs`, `valid_flipDs`), the interface of `D†` for `-h` (`GateRemarks.transfer_unitary`,
`transfer_right`, `transfer_left`, `transfer_norm`, `transfer_boundary`, `transfer_endpoint`) and
`GateRemarks.exponent_nonneg`, `GateRemarks.exponent_neg`.

**Admissible depths** (module `Depth`). `Admissible Q W δ k`: `k ≥ 1`, the filter decay
`prefactor(Q, W) (1/4)^k ≤ δ` and the smoothing slack `6W ≤ k(L_Q - 1)`. These are the only
properties of the depth used by the released clock analysis:

* `sharp_admissible`: the released depth is admissible;
* `exists_precise_implementation_k`: for every admissible `k` the actual amplified
  implementation of the clock transducer with depth `k` (`implementationK`) is an isometry
  within `2δ` of the clean output preparation (`outputK`, degree `k(L_Q - 1)`) applied to the
  Cayley power (complete output).

**The manuscript's depth** (module `Manuscript`).

* `depthMs Q W ε = ⌈4W/Q + log₂(4096/ε)⌉` and `degreeMs Q W ε = depthMs Q W ε · (L_Q - 1)`;
  `degreeMs_natCast`: `d = k(32Q - 1)` for natural `Q`, the printed formula; `degreeMs_of_nat`:
  `d = k(b - 1)` whenever `32Q = b` is natural.
* `depthMs_admissible`: for `Q ≥ 1`, `W ≥ 0` and `0 < ε ≤ 1`, the manuscript's `k` is admissible
  at the filter accuracy `ε/8`.
* `degreeMs_le`: `d ≤ 128W + 32Q(log₂(4096/ε) + 1)`.

**The sharp Cayley error** (module `Cayley`). For a skew-adjoint `X` and a right inverse `R` of
`1 - X/2` (no spectral theorem; every complex Hilbert space):

* `skew_half_inverse_norm_le_one`: `‖R‖ ≤ 1`;
* `cayley_exp_error_sharp`: `‖(1 + X/2)R - exp X‖ ≤ ‖X‖³/12` (two mean value inequalities with
  moving bounds for `f(s) = (1 + sX/2) - exp(sX)(1 - sX/2)`, `f''(s) = (s/2) exp(sX) X³`);
* `cayley_power_exp_error_sharp`, `hamiltonian_cayley_error_sharp`: `T` steps err by at most
  `T‖X‖³/12`, respectively `T w³/12` for a self-adjoint contraction `H` (the released
  `CayleyApproximation.hamiltonian_cayley_error` has `T w³`).

**The exact-gate circuit for every admissible depth** (module `Circuit`).
`simCircuitK a m τ Q k` is the released circuit `ampI` with `2^m` slots, the filter of depth `k`
(`fDegK`, `labWtK`, `labLenK`) and the reuse register `simRK Q k = ⌈log₂(2d+2)⌉`.

* `amp_error_k`: the ideal amplified circuit is within `2δf + δc` of `exp(-iτH)` on clean
  inputs, for an admissible depth at accuracy `δf`, `w ≤ 1/4` and `2^m w³/12 ≤ δc`;
* `gate_efficient_simulation_k`: valid elementary instructions, exactly `6d` private Cayley calls
  and `12d` calls of `U_J` or `U_J†`, at most `200(d+1)(a+m+r+1)` elementary gates on
  `2a + 3m + 6r + 3` qubit wires, `2d + 2 ≤ 2^r ≤ 4(d+1)`, full output within `2δf + δc` of
  `exp(-iτH)`.

**The manuscript's schedule, exact gates** (module `Endpoint`).

* `meshMs τ ε = max{2, 4τ, √(τ³/(3ε))}` (`√(τ³/(3ε)) = τ^{3/2}/√(3ε)`), `slotMs τ ε` its
  power-of-two exponent; `slotMs_spec`: `2^m ≥ meshMs` and `2^m` is the least such power of two
  (`m ≥ 1`); `mesh_budget`: `w ≤ 1/4` and `2^m w³/12 ≤ ε/4`.
* `simCircuitMs a τ Q q̄ ε = simCircuitK a (slotMs τ ε) τ Q (depthMs Q (τq̄) ε)`.
* `gate_efficient_simulation_ms` (Theorem `hs:thm:gates` before finite-set synthesis, with
  `hs:eq:gate-known`): under the clock hypotheses of the released analysis for the private
  Cayley operation `D` and `J = U_J ι₀`, with `τ ≥ 0`, `Q ≥ 1`, `0 < ε ≤ 1`: valid elementary
  instructions; exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`,
  `d = degreeMs Q (τq̄) ε`; at most `200(d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3`
  qubits; full output on clean inputs within `ε/2` of `exp(-iτH)` (filter `2·ε/8`, Cayley
  `ε/4`); `d ≤ 128τq̄ + 32Q(log₂(4096/ε) + 1)`; `m` and `r` as in `hs:eq:gate-clocks`.

**Lemma `hs:lem:abstract` with the manuscript's schedule** (module `Abstract`).

* `absCircuitMs a α t Q ν ε`: `simCircuitMs` for the time `α|t|` and `q̄ = ν`, with `D` and `D†`
  exchanged for `t < 0` (`GateRemarks.flipDs`), as in the released `GateRemarks.absCircuit`.
* `logb_4096_eq`: `log₂(4096/ε) = 12 + log(1/ε)/log 2`; `degreeMs_cost_le`: for `Q ≥ 1`, `W ≥ 0`
  and `0 < ε ≤ 1/2`, `6d ≤ 3880 (W + Q log(1/ε))` (the form of `hs:eq:abstractcost`; the
  released schedule gives `3840`).
* `abstract_simulation_ms`: under the hypotheses of the released
  `GateRemarks.abstract_simulation` (unitaries `U_J`, `D`, the two-sided inverse `R₁` of `1 - D`,
  `h` self-adjoint with `‖h‖ ≤ 1`, the interface `hs:eq:interface` for `J = U_J ι₀` with the
  compressed second moment `J† R₁† R₁ J ≤ (ν/2) 1` in the Loewner order, `‖R₁‖ ≤ Q`, `1 ≤ Q`,
  `0 < ν ≤ Q`, `α > 0`, every real `t`, `0 < ε ≤ 1/2`): valid instructions; exactly `6d` private
  calls and `12d` calls of `U_J` or `U_J†`, `d = degreeMs Q (α|t|ν) ε`, at most
  `3880 (W + Q log(1/ε))` and `7760 (W + Q log(1/ε))` for `W = α|t|ν`; at most
  `200(d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubits; full output on clean inputs
  within `ε/2` of `exp(-it(αh))` (filter `2·ε/8`, Cayley `ε/4`);
  `d ≤ 128W + 32Q(log₂(4096/ε) + 1)`; `2^m` the least power of two at least
  `max{2, 4α|t|, √((α|t|)³/(3ε))}` (it enters neither `d` nor its bound); `2d + 2 ≤ 2^r ≤ 4(d+1)`.
* `abstract_simulation_ms_explicit` (equation `hs:eq:explicitcount`): at an integer `Q ≥ 1`,
  exactly `6(32Q - 1)⌈4W/Q + log₂(4096/ε)⌉` private calls and `12(32Q - 1)⌈4W/Q + log₂(4096/ε)⌉`
  calls of `U_J` or `U_J†`, with full-output error at most `ε/2`.

**Over a finite gate set with the manuscript's allocation** (modules `Selective`, `Native`).
`selSimMs` compiles the circuit with the supplied finite-set controlled private circuit `pc`
(`GateSelective.hcircP`) selectively with the synthesis budget `ε/4` (`GateSelective.selBudget`).

* `sim_supplied_ms`: before synthesis, exactly `6d` times the calls of `pc`,
  `nGatesN(simPMs ∅) + 6d|pc|` gates with `nGatesN(simPMs ∅) ≤ 200(d+1)(a+m+r+1) + 84dC_J`,
  full output within `ε/2 + 6dξ`.
* `sel_simulation_ms` (equations `hs:eq:gate-Gzero`, `hs:eq:gate-total`): under the synthesis
  hypothesis `GateSynth.Synthesis 𝒢 X L` with `L ζ ≤ c₁ log(1/ζ) + c₀`, an adjoint-closed `𝒢`, a
  valid `pc` over `𝒢` within `ξ` of the enable-controlled private operation on clean work wires
  and `24dξ ≤ ε`: valid gates of `𝒢` and primitive calls; exactly `6d` times the calls of `pc`;
  at most `G₀ = 200(d+1)(a+m+r+1) + 84dC_J` synthesised gate occurrences, whatever `pc`; at most
  `6d|pc| + G₀(c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates; `|S| + (2a + 3m + 6r + 3) +
  (|Z| + bT + bP + A + 3) + |X|` qubits; full output, every qubit outside the system clean,
  within `ε` of `exp(-iτH)` (`ε/2 + 6dξ + ε/4`); `d = k(L_Q - 1)`, its bound, and `2^m` the
  manuscript's slot count. `sel_simulation_ms_signed`: every real time, by the literal
  reverse-adjoint of the compiled circuit for `|t|`.
* `sel_simulation_ms_native`: the same for the selectively compiled native private circuit
  `GateSelective.privSel hS η nd ar` (`ξ = η + 4ζ`), with exactly `12d` times the calls of the
  compute circuit `V`.

**The time-dependent part with the manuscript's constants** (modules `TimeClock`, `TimeMesh`,
`TimeCircuit`, `SelectiveTime`, `Native`).

* `exists_precise_implementationV_k`, `filter_precisionV_k`: the slot-dependent clock for every
  admissible depth.
* `cayley_step_sharp`, `cayley_evolution_error_sharp`: a Cayley step of a self-adjoint `H` with
  `‖H‖ ≤ λ` is a contraction within `(wλ)³/12` of `exp(-iwH)`; `n` steps err by `n(wλ)³/12`.
* `duhamel_step_sharp`, `mesh_error_sharp`: with the moving bound `‖H(u) - H̃‖ ≤ β(u-a) + δ`,
  one interval errs by `β(b-a)²/2 + δ(b-a)`, and the uniform mesh by `βt²/(2M) + tδ`
  (equation `hs:eq:timedisc` without the Cayley term; the released `TimeDependent.mesh_error`
  has `βt²/M`).
* `simCircuitTK`, `ampT_error_k`, `simulationT_k`, `propagator_error_k`: the slot-selected circuit
  with depth `k`, within `2δf + δc + βt²/(2·2^m) + tδ` of every propagator.
* `timegridMs α Λ β t ε = max{1, 4αt, 6βt²/ε, √((Λt)³/ε)}` (equation `hs:eq:timegrid`);
  `timegrid_budget`: `w ≤ 1/4`, Cayley error `≤ ε/12`, freezing error `≤ ε/12`.
* `gate_efficient_time_simulation_ms`: for the slot-selected private operations `D j` with the
  clock promises for `H̃_j/α`, `‖H̃_j‖ ≤ Λ ≤ α`, a `β`-Lipschitz Hermitian path with
  `‖H(jt/2^m) - H̃_j‖ ≤ δ`, `2^m ≥ timegridMs` and `12tδ ≤ ε`: the counts above with
  `d = degreeMs Q (αtq̄) ε`, a propagator exists, and for every propagator `U` the full output
  is within `ε/2` of `U(t)` (filter `ε/4`, Cayley `ε/12`, freezing `ε/12`, samples `ε/12`).
* `sel_time_simulation_ms`, `sel_time_simulation_ms_native`: the finite-gate-set forms
  (supplied slot-selected private circuit, `24dξ ≤ ε`, synthesis `ε/4`), within `ε` of `U(t)`.

**Scope.** Only the gate-level endpoints for supplied unitaries, supplied finite-set private
circuits and the native data, and Lemma `hs:lem:abstract`, are given with the manuscript's schedule;
the isometry, scalar and binary-data instances of the released lemma
(`GateRemarks.abstract_simulation_isometry`, `abstract_simulation_scalar`,
`abstract_simulation_binary`) keep the released schedule, and so does Lemma `ode:lem:gate-select`
(the released depth and subdivision condition replace `ode:eq:gate-select-schedule`, line 4806, and
the first three conditions of `ode:eq:gate-select-mesh`). The binary-data and
bit-budget endpoints (`GateBinary.binary_simulation`, `GateBitBudget.binary_simulation_bits`,
their finite-gate-set and time-dependent forms) keep the released schedule; equation
`hs:eq:gate-binary` is asymptotic and holds for either schedule. The circuit wires carry all
`2^m` slots for time-independent Hamiltonians too, as in the released circuit.
-/
