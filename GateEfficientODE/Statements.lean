import GateEfficientODE.Theorem
import GateEfficientODE.Time.Theorem

/-!
# Gate-efficient dissipative ODE: paper-to-Lean entry point

The exact-gate part of Theorem `ode:thm:gates` (gate-efficient dissipative
equations) of the accompanying paper, with the analytic LCHS grid of
`ode:eq:grid` and `ode:eq:gate-grid-size`, is formalized in two cases.

* Constant coefficients: `SparseHamiltonian.GateODE.solver` in
  `GateEfficientODE/Theorem.lean`, with the complete protocol
  `SparseHamiltonian.GateODE.Params.protocol` and the instance guarantee
  `SparseHamiltonian.GateODE.Params.Outcome`. This case is described first.
* Time-dependent coefficients on a uniform mesh of `2^m` slots:
  `SparseHamiltonian.GateODE.Time.solver` in `GateEfficientODE/Time/Theorem.lean`,
  with the protocol `SparseHamiltonian.GateODE.Time.TParams.protocol` and the
  guarantee `SparseHamiltonian.GateODE.Time.TParams.Outcome`; see the section
  *Time-dependent coefficients* below.

**Equation.** `x' = A x + b` on `[0, T]` with `A = -(L + iH)` (`gen`), `H` and
`L` self-adjoint, `L` positive semidefinite (`Re ⟪w, L w⟫ ≥ 0`), on a
finite-dimensional system space `P`; the target is
`x(T) = ODEConstantForcing.solution A x0 b T` (`Params.target`).

**Access model** (`Model/Instr`). Qubit wires carry the system payload. The
instructions are

* elementary gates: one-qubit unitaries with at most three literal controls,
  all off the target (`OInstr.Valid`);
* calls of `U_J` or `U_J†` on the `a` ancilla qubits of the released
  simulator and the system, with at most one control;
* calls of the label-selected private Cayley operation or its inverse: one
  call applies the supplied unitary `D z` on every configuration whose solver
  wires carry the joint label `z = ((ini, node word), LCHS word)` (coherent
  selection, counted once);
* calls of the supplied source interfaces `J false = J₀` (initial state) and
  `J true = J_b` (forcing), or their inverses, on the sector `ini`;
* the public payload reflection `1 - 2 |v⟩⟨v|` about the seed `v`, with at
  most one control, counted separately.

A circuit is read as a released multi-oracle program whose labels are its
instructions (`Params.program`), so the weights `wGate`, `wPriv`, `wUJ`,
`wSrc c` and `wSeed` count gates and calls exactly, forward and inverse
alike.

**Public data** (`Params`, hypotheses `PublicOK`): `a`, the clock constants
`Q ≥ 1` and `0 ≤ qbar ≤ Q`, `T > 0`, norm bounds `λH, λD ≥ 0` with
`λH + R λD > 0`, the normalisation bound `g ≥ 1`, the precision
`0 < ε ≤ 1/2`, and source norms `r₀, rb ≥ 0` with mass `B = r₀ + T rb > 0`.
Derived: `ν = ε / (10000 g)`, the LCHS radius `R = 4 log (20000 g / ε)`, the
common simulation time `τ = T (λH + R λD)`, the released simulator
`simCircuit a τ Q qbar ν` with filter degree `d` on `2a + 3m + 6r + 3` wires,
the analytic Gaussian LCHS grid `AnalyticLCHS` with growth constant
`D = T λD`: `K = ⌈R / stepBound⌉`, `stepBound = π / (D/2 + log (512/ν))`,
step `h = R / K`, `J = 2K + 1` nodes `n h` (`|n| ≤ K`) and coefficients
`h · kernel w (n h)` of the released Gaussian kernel, `l = ⌈log₂ (J + 2)⌉`, and
`k = ⌈log₂ ⌈T (λH + λD) / ν⌉⌉`.

**Instance hypotheses** (`InstanceOK`): `U_J` and every `D z` are unitary and
satisfy the clock promises of the released gate-level simulator
(`ClockPromise`, as in `hs:thm:gates`) for the branch Hamiltonian
`H_z = (dur s / τ)(H + k_w L)` of label `z = (s, w)`, where `dur s` is `T` for
the initial sector and `i T / 2^k` for node `i`, and `k_w` is the LCHS node;
`H, L` self-adjoint with `‖H‖ ≤ λH`, `‖L‖ ≤ λD`, `L ≥ 0`; the source interfaces
are unitary, `‖x0‖ = r₀`, `‖b‖ = rb`, and `J₀ v`, `J_b v` are the directions of
`x0` and `b` when these are nonzero; `x(T) ≠ 0` and `B ≤ g ‖x(T)‖`.

**Guarantees** (`solver`). The protocol `Params.protocol p v` depends only on
the public data and the seed. Every trial circuit consists of valid
elementary instructions, and in every history, including four failures, the
protocol uses at most

* `40 g · prepGates + 20 g · reflGates` elementary gates, where
  `prepGates = 200 (d+1)(a+m+r+1) + 2 (k+1) + 3 · 2^l (2l+1)` and
  `reflGates = 6 (2a + 3m + 6r + 4 + k + l) + 4`; simplified
  (`Params.gate_count`): `9000 g ((d+1)(a+m+r+1) + (k+1) + (J+2)(l+1))`, and
  with the grid bound substituted (`Params.gate_count_grid`):
  `9000 g ((d+1)(a+m+r+1) + (k+1) + (R (T λD + 2 log (512/ν)) / π + 5)(l+1))`;
* `240 g d` private Cayley calls and `480 g d` calls of `U_J` or `U_J†`;
* `40 g` calls of each source interface and `20 g` seed reflections;

on `4a + 6m + 12r + 2k + 2l + 8` qubit wires besides the system, with
`d ≤ 128 (τ qbar + Q (1 + log (3/ν)))`, `steps ≤ 2^m < 2 steps`,
`2d + 2 ≤ 2^r ≤ 4 (d+1)`, `J + 2 ≤ 2^l < 2 (J + 2)`,
`J ≤ R (T λD + 2 log (512/ν)) / π + 3` (with `R = 4 log (20000 g/ε)` and
`512/ν = 5120000 g/ε`, `Params.J_le_log`), `T (λH + λD) ≤ ν 2^k` and
`2^k < 2 (⌈T (λH + λD)/ν⌉ + 1)`. With `ℓ = log (g/ε)` the grid has
`J = O(ℓ (T λD + ℓ))` labels; when `λD` is the row-norm bound `√(2s) η_D` this
is the paper's `J_k = O(√s T η_D ℓ + ℓ² + 1) = O(q ℓ)`. For every
instance satisfying `InstanceOK` (`Outcome`): every trial circuit is unitary;
the mean herald probability over the trial counts is at least `1/4`; every
trial with nonzero success component has direction error at most `ε/500` up to
a phase; four attempts succeed with probability at least `175/256 > 2/3`;
and, conditioned on success, the output is a density operator within spectral
trace distance `ε` of `x(T) / ‖x(T)‖`.

**Proof map.** Module paths are relative to `GateEfficientODE/`.

* Exponential convergence of the trapezoidal rule on the real line for
  functions holomorphic on a strip with a Cauchy envelope, by Poisson
  summation (Mathlib) and horizontal contour shifts: `Grid/Strip`
  (`StripQuadrature.integral_shift`, `fourier_norm_le`), `Grid/Trapezoid`
  (`trapezoid_error`, `trapezoid_error_op`, `cauchy_sum_le`).
* The analytic LCHS grid: the complex Gaussian kernel on `|Im k| ≤ 1/2`, the
  growth `‖exp (-i u (H + z L))‖ ≤ exp (u λD Im z)` above the axis, the grid
  size, node, mass and error bounds: `Grid/Table`
  (`AnalyticLCHS.evolution_norm_le_exp`, `gridSize_le`, `nodes_abs_le`,
  `mass_le`, `table_error`, `table_certificate`).

* Instruction model, label-selected private calls, embedding of the released
  simulator and the coherent block estimate: `Model/Exposure`, `Model/Instr`
  (`run_map_embI`, `run_isUnitary`, `toProgram_eval`, `toProgram_cost`),
  `Model/Block` (`localOp_branch_error`).
* Rotation trees and uniformly controlled diagonals with AND chains on a
  clean pool: `Gadgets/Uniform` (`prepT_agrees`, `prepT_length_le`,
  `phaseT_agrees`, `phaseT_length`).
* Wires, labels, zero-test and seed reflections, the trial circuits, their
  validity and exact counts: `Circuit/Wires`, `Circuit/Reflect`,
  `Circuit/Trial`, `Circuit/Counts` (`trialC_counts`, `trialC_valid`).
* Agreement of the trial circuits with the released amplification of the
  actual preparation on clean inputs: `Circuit/Agree` (`prepC_agrees`,
  `trialC_seed`).
* Padded LCHS words, source input and output identification, coherent
  selection within `ν` of the branch evolutions, finite LCHS and the source
  quadrature: `Analysis/Words` (`coeffW_mass`), `Analysis/Input`,
  `Analysis/Select` (`select_error`), `Analysis/Table` (`lchs_error`,
  `quadrature_error`).
* The released actual-source certificate and the randomized trial bounds:
  `Analysis/Certificate` (`prep_certificate`, `trial_bounds`).
* The four-attempt protocol, worst-case counts, success and conditional
  output: `Protocol` (`protocol_worst`, `outcome`); public sizes and the main
  theorem: `Theorem`.

**Formalization choices.**

* Gates are exact: arbitrary one-qubit unitaries with at most three
  controls, as in `hs:thm:gates`. Multi-controlled operations use AND chains
  on a pool of clean flags. Rotation angles are not synthesised over a finite
  gate set.
* The coefficient register uses the analytic grid: the integrand
  `k ↦ kernel w k • exp (-i u (H + k L))` of the released Gaussian kernel is
  holomorphic on `|Im k| ≤ 1/2`, with Cauchy envelope
  `exp (3/2 + T λD/2) / (π (1/4 + (Re k)²))`, so the trapezoidal error is at
  most `4 exp (3/2 + T λD/2) / (exp (π/h) - 1) ≤ ν/8`. The discrete Gaussian tail
  beyond `R` and the full-line LCHS residual `exp (1 - w) ≤ 7ν/8` complete the
  budget `2ν`; the coefficient mass is at most `e (1 + 1/64) < 3`. The step
  constant `512` replaces the paper's `64 e^{3/2} / 15`, whose kernel bounds
  are Low–Somma's. The amplitudes and phases cost at most
  `3 · 2^l (2l + 1) = O(J log J)` gates by an explicit rotation tree and a
  uniformly controlled diagonal.
* Sources use `2^k` left-endpoint quadrature nodes; the source register is
  prepared by one rotation and Hadamards, and the forcing interface is called
  once per preparation for all nodes.
* The label-selected private Cayley operation is a supplied unitary family
  with the clock promises of the released simulator for every branch;
  its construction from sparse access (entry decoding and public arithmetic)
  and the gate costs of the source interfaces are not counted here.
* Not formalised: finite-gate-set synthesis, entry decoding and arithmetic,
  workspace of the supplied source circuits, the general-generator extension
  and lower bounds. Time-dependent coefficients are covered by the section
  below.

## Time-dependent coefficients

**Equation.** `x' = -G(u) x + b(u)` on `[0, T]` for an accretive generator
path `G` (`Re ⟪w, G(u) w⟫ ≥ 0`), `βG`-Lipschitz on `[0, T]`, and a
`βb`-Lipschitz forcing with `‖b(u)‖ ≤ bmax`; `x` is any solution
(`TimeDependentODE.SolvesODE`). The interval is divided into `2^m` slots of
length `T / 2^m`. The generator enters through represented slot samples
`G_r = L_r + i H_r` (`Time.gens`) with `H_r, L_r` self-adjoint,
`L_r ≥ 0`, `‖H_r‖ ≤ λH`, `‖L_r‖ ≤ λD` and `‖G(rT/2^m) - G_r‖ ≤ δG`, and the
forcing through samples `b_r` with `‖b(rT/2^m) - b_r‖ ≤ δb`. The exact target
of the circuit is the left-endpoint exponential recurrence
`y_{r+1} = exp (-(T/2^m) G_r)(y_r + (T/2^m) b_r)`, `y_0 = x(0)`
(`Time.TParams.target`); it is within the certified error
`Time.TParams.discretisation` of `x(T)`, which with exact samples equals
`T² / 2^m · (βG (‖x(0)‖ + bmax T) + βb + (λH + λD) bmax)`
(`discretisation_exact_samples`).

**Access model** (`Time/Model`). The instruction syntax is that of the
constant-coefficient solver; the supplied unitaries `TOracles` are read as
follows. A private call applies `D z r` on every configuration whose solver
wires carry the joint label `z` and whose slot wires (the `m` address wires
of the released simulator) carry the slot `r` (label- and slot-selected,
counted once). A loading call applies `J s` on every configuration whose
source wires carry the source label `s = (ini, q)`: the initial direction on
`(false, 0)` and the direction of the forcing sample `b_q` on `(true, q)`. A
weight-preparation call applies the supplied unitary matrix `Wp` to the
`1 + m` source-label wires. Gates, `U_J` and seed reflections are as before.
The weights `wGate`, `wPriv`, `wUJ`, `wLoad`, `wPrep` and `wSeed` count
gates and calls exactly, forward and inverse alike.

**Masked branches.** The source label `s` starts at slot `start s` (`0` for
the initial label, `q` for `(true, q)`); its slot durations are
`dur s r = (T/2^m) · [start s ≤ r]`, and the source vector is `x(0)` on
`(false, 0)` and `(T/2^m) b_q` on `(true, q)` (`zsrc`), of total mass
`B = ‖x(0)‖ + (T/2^m) Σ_q ‖b_q‖` (`mass`). With `τ = T (λH + R λD)` the
private operation of the joint label `z = (s, w)` at slot `r` must satisfy the
clock promise of the released gate-level simulator for the normalised slot
Hamiltonian `H_{z,r} = (T [start s ≤ r] / τ)(H_r + k_w L_r)` (`branchH`), and
the slot-selected simulator `GateCircuit.SlotSim.simCircuitT` of the library
`GateEfficientTimeDependent`, with step `τ / 2^m` per slot, is within `ν` of
the ordered product of the slot evolutions `exp (-i dur s r (H_r + k_w L_r))`
(`GateCircuit.SlotSim.simulationT`, `select_error`).

**Public data** (`Time.TParams`, hypotheses `Time.TParams.PublicOK`): `a`,
`Q ≥ 1`, `0 ≤ qbar ≤ Q`, `T > 0`, `λH, λD ≥ 0` with `λH + R λD > 0`,
`g ≥ 1`, `0 < ε ≤ 1/2`, and the mesh exponent `m` with the mesh condition
`steps τ (ν/3) ≤ 2^m` of the released simulator (implied by
`simM τ ν ≤ m`, `Time.TParams.mesh_of_le`). Internally the solver uses the
ratio `2g` and the accuracy `ε/2`: `ν = ε / (40000 g)`,
`R = 4 log (80000 g / ε)`, the analytic Gaussian grid with growth constant
`T λD` on `J + 2` padded labels and `l = ⌈log₂ (J + 2)⌉` wires.

**Instance hypotheses** (`Time.TParams.InstanceOK`): `U_J`, every `D z r`
(`r < 2^m`), every `J s` and `Wp` unitary, the clock promises above, the
weight promise `Wp |0⟩ = Σ_s sqrt (‖z_s‖ / B) |s⟩` (`WpPromise`), the loading
directions, the represented and sampled data above, `x(T) ≠ 0`,
`B ≤ g ‖x(T)‖`, and the discretisation budget
`discretisation ≤ ε B / (2000 g)`.

**Guarantees** (`Time.solver`). The protocol depends only on the public data
(including `m`) and the seed. Every trial circuit consists of valid
elementary instructions, and in every history, including four failures, the
protocol uses at most

* `80 g · prepGates + 40 g · reflGates` elementary gates, where
  `prepGates = 200 (d+1)(a+m+r+1) + 3 · 2^l (2l+1)` and
  `reflGates = 6 (2a + 4m + 6r + 4 + l) + 4`; simplified
  (`Time.TParams.gate_count`): `18000 g ((d+1)(a+m+r+1) + (J+2)(l+1))`;
* `480 g d` slot-selected private calls and `960 g d` calls of `U_J` or
  `U_J†`;
* `80 g` loading calls, `160 g` weight-preparation calls and `40 g` seed
  reflections;

on `4a + 8m + 12r + 2l + 8` qubit wires besides the system, with
`d ≤ 128 (τ qbar + Q (1 + log (3/ν)))`, `2d + 2 ≤ 2^r ≤ 4 (d+1)`,
`J + 2 ≤ 2^l < 2 (J + 2)` and `J ≤ R (T λD + 2 log (512/ν)) / π + 3`
(with `512/ν = 20480000 g/ε`, `Time.TParams.J_le_log`). For every instance
satisfying `InstanceOK` (`Time.TParams.Outcome`): every trial circuit is
unitary; the mean herald probability is at least `1/4`; every trial with
nonzero success component has direction error at most `ε/500` against
`x(T)` up to a phase; four attempts succeed with probability at least
`175/256 > 2/3`; and, conditioned on success, the output is a density
operator within trace distance `ε` of `x(T) / ‖x(T)‖`.

**Proof map** (time-dependent case; module paths relative to
`GateEfficientODE/`).

* Slot-selected semantics of the released simulator instructions, agreement
  with the released semantics on lists without private calls, the masked
  LCU, amplification and its error against the ordered slot evolutions
  (exact Cayley transfer per slot and the released precise implementation):
  the library `GateEfficientTimeDependent` (`SlotSim`: `runT_eq_run`,
  `select_blockT`; `SlotError`: `ampT_error`, `simulationT`; `Theorem`:
  `simCircuitT_public`).
* The time-dependent instruction semantics and programs: `Time/Model`
  (`trun_map_embI`, `trun_isUnitary`, `ttoProgram_eval`, `ttoProgram_cost`).
* Trial circuits, validity and exact counts, agreement with the released
  amplification: `Time/Trial`, `Time/Counts` (`trialC_counts`,
  `trialC_valid`), `Time/Agree` (`prepC_agrees`, `trialC_seed`).
* Padded words, the weight promise and source input, the coherent selection:
  `Time/Words`, `Time/Input` (`mass_eq`, `inMap_eq_input`), `Time/Select`
  (`branch_block`, `select_error`).
* Growth of ordered product families above the real axis, the LCHS error
  for every source label, the exact source sum and the discretisation:
  `Time/Table` (`productFamily_norm_le_exp`, `lchs_error`, `source_sum`,
  `target_norm_le`, `discretisation_error`).
* The certificate for the discretised target with ratio `2g` and accuracy
  `ε/2`, retargeting to `x(T)`, and the trial bounds: `Time/Certificate`
  (`target_facts`, `prep_certificate`, `trial_bounds`).
* The protocol, worst-case counts, success and conditional output:
  `Time/Protocol` (`protocol_worst`, `outcome`); public sizes and the main
  theorem: `Time/Theorem`.

**Formalization choices** (time-dependent case).

* All branches use one uniform mesh of `2^m` slots: a forcing branch is
  masked (identity) on the slots before its start, as in the released
  `ode:thm:time` formalization, so every branch has the same simulation
  time `τ` and the same step `τ / 2^m`.
* Forcing nodes are the left endpoints `rT/2^m` with weights `T/2^m`. The
  source label is prepared by one call of the supplied weight preparation
  `Wp` (forward and inverse once per preparation), and the loading `J` is
  called once per preparation for all labels; their gate costs are not
  counted here.
* The mesh is public. Its fineness enters only through the simulator's
  mesh condition and the instance's discretisation budget; with exact
  samples the budget is a lower bound `2^m ≥ 2000 g T² (…) / (ε B)`.
-/
