import GateEfficientSelect.NonVacuity
import GateEfficientSelect.ODE.Native
import GateEfficientSelect.ODE.Left
import GateEfficientSelect.ODE.NonVacuity

/-!
# Lemma `ode:lem:gate-select` on branch-dependent meshes: paper-to-Lean entry point

Lemma `ode:lem:gate-select` of the accompanying paper (gate-efficient coherent selection) selects,
coherently from a label `z` that specifies a frequency `|k_z| ≤ R` and a start time `0 ≤ v_z ≤ T`,
the propagator of `H(t) + k_z D(t)` from `v_z` to `T`: the controlled direct sum
`ode:eq:gate-select-target` has a clean-input implementation with full-output error at most `δ`, at
most `6d` private Cayley calls and no factor equal to the number of source labels or time slots in
its gate count. In its proof every branch has its own mesh: "For fixed `z`, choose `M` equal time
steps of length `u_z/M`", with the sample addresses `v_z + r u_z/M`. The released libraries
formalise the single-label case (`GateCircuit.SlotSim.gate_efficient_time_simulation`, used for the
time-dependent gate-level simulation, Theorem `hs:thm:time` with the circuit of `hs:thm:gates`) and,
for the time-dependent part of Theorem `ode:thm:gates`, mask every source branch on one common mesh
instead of using the branch-dependent meshes of Lemma `ode:lem:gate-select`. This library formalises
the branch-dependent meshes in an exact-gate form in which the step of each branch is folded into
its private operation (see *Formalisation choices*):

* the lemma's exact-gate conclusion for an arbitrary label register, against the exact
  propagators of the branch paths (`gate_select`);
* the time-dependent part of Theorem `ode:thm:gates` with branch-dependent meshes and a positive
  source quadrature under the source certificate `ode:eq:gate-source-certificates`,
  for the released protocol, with exact gates (`ODE.solverB`) and natively
  (`ODE.native_ode_time_solverB`), and the certificate for the left-endpoint quadrature from the
  Lipschitz bounds (`ODE.quad_leftEndpoint`).

No result from another paper is used. The released libraries are unchanged. References to the
manuscript use its labels. Every theorem of the library is axiom-audited in
`GateEfficientSelect/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateSelect` (the differential-equation part in
`SparseHamiltonian.GateSelect.ODE`) and are named relative to it below. Released declarations
are named relative to `SparseHamiltonian` (for example `GateCircuit.SlotSim.simCircuitT`,
`GateODE.ClockPromise`, `GateODE.Time.TParams`, `GateNative.native_ode_time_solver`), except
those of the library `TimeDependentExtensions`, which are named in full.

**Notation.** In `gate_select` the error `ε` is the lemma's `δ`, the bound `δ` is a uniform bound
on the sample errors, `2^m` is `M`, `α T` is the common normalised time, `βH + R βD` plays the
role of `L_*`, and `d = GateCircuit.Sim.fDeg Q (α T) qbar (ε/2)` is the package's own filter degree.
In the differential-equation endpoints `B = p.mass` is the quadrature normalisation `B_m` of the
paper, the budget `B ≤ g ‖x(T)‖` is stated with `B_m` (the paper's `B/‖x(T)‖ ≤ ḡ` and
`B_m ≤ 2B` give it with `g = 2ḡ`, as in the released solvers), and the certificate bound `κ`
plays the role of `ν B`.

**What was already released (cited, not redone).**

* The single-label case: `GateCircuit.SlotSim.gate_efficient_time_simulation` (the released
  circuit of `hs:thm:gates` with a slot-selected private Cayley operation, error against every
  propagator of a Lipschitz Hermitian path) with `GateCircuit.SlotSim.simulationT` (error against
  the ordered product of the slot exponentials) and `GateCircuit.SlotSim.simCircuitT_public`
  (validity and counts from the public numbers).
* Label selection with branch durations folded into the private operation, for constant
  coefficients: `GateODE.Params.branchH` (`(dur s / τ)(H + k_w L)`) and
  `GateODE.Params.select_error`, with the block estimate `GateODE.localOp_branch_error`; from
  binary sparse oracles the private operations of these rescaled branch Hamiltonians are
  constructed, with clock constants that do not depend on the label (`GateEfficientBinaryODE`).
* The time-dependent solvers on one common mesh with masked source branches:
  `GateODE.Time.solver` (exact gates, normalised slot Hamiltonian
  `GateODE.Time.TParams.branchH = (T [start s ≤ r] / τ)(H_r + k_w L_r)` and the left-endpoint
  recurrence as exact target), `GateNative.native_ode_time_solver`, and the binary-data,
  finite-gate-set, budget and certificate forms built on them.
* In the query model, coherent selection of durations and of windows at mesh points on one
  common slot grid: `TimeDependentExtensions.Coherent.coherent_select`,
  `TimeDependentExtensions.Coherent.coherent_windows`.

**Lemma `ode:lem:gate-select`** (`gate_select`, modules `Model`, `Branch`, `Lemma`).

* Model. Labels are the configurations `z : Cfg L` of an arbitrary finite set `L` of label
  wires beside the simulator wires (`SW a m r K L`). The circuit is the released instruction
  list `GateCircuit.SlotSim.simCircuitT a (α T) Q qbar (ε/2) m` for the common normalised time
  `α T`, read with a label- and slot-selected private call (`evalS`, `runS`): an elementary gate
  is the renamed elementary gate of the whole register (`evalS_gate`), a `U_J` call acts as
  released, and one private call applies `D z j` on every configuration whose label wires carry
  `z` and whose slot wires carry `j`. On every label it acts as the released slot-selected
  simulator of that label (`runS_eq`). `selE` is the clean-input space (a label and a payload,
  every simulator wire clear), an isometry (`selE_isometry`).
* Branches. `branchPath Hp Dp k v z t = H(v z + t) + k_z D(v z + t)` on `[0, T - v z]`; its
  propagator at `T - v z` is the time-ordered exponential of `ode:eq:gate-select-target`. Branch
  `z` runs on its own uniform mesh of `2^m` slots of length `(T - v z)/2^m` with the sample
  addresses `v z + j (T - v z)/2^m`.
* Hypotheses: `T > 0`, `α > 0`, `Q ≥ 1`, `qbar ≤ Q`, `0 < ε ≤ 1`, Lipschitz bounds `βH, βD ≥ 0`
  of the Hermitian paths `H`, `D` on `[0, T]`, `|k z| ≤ R`, `0 ≤ v z ≤ T`; unitary `U_J` and
  `D z j`; Hermitian represented samples `X z j` with `‖X z j‖ ≤ α` and the sample errors
  `‖H(addr) + k_z D(addr) - X z j‖ ≤ δ` at the branch addresses; the clock promise of the
  released simulator (`GateODE.ClockPromise`, as in `hs:thm:gates`) for `U_J`, `D z j` and the
  rescaled normalised sample `((T - v z)/(α T)) X z j`; and the public conditions
  `steps (α T) (ε/6) ≤ 2^m` (subdivision of the Cayley steps), `4 (βH + R βD) T² ≤ ε 2^m`
  (freezing) and `4 T δ ≤ ε` (samples).
* Guarantees: valid elementary instructions; exactly `6d` private calls and `12d` calls of `U_J`
  or `U_J†`; at most `200 (d+1)(a+m+r+1)` elementary gates; `2a + 3m + 6r + 3` simulator wires
  besides the label wires; `d ≤ 128 (α T qbar + Q (1 + log (6/ε)))` and
  `2d + 2 ≤ 2^r ≤ 4 (d+1)`. No count depends on the label register, and `2^m` enters only
  through `m`. Every branch path has a propagator, and for every family of propagators `U z`
  with `U z 0 = 1` the circuit is within `ε` of `∑_z |z⟩⟨z| ⊗ U z (T - v z)` on the clean-input
  space, with the full output compared (an untouched reference may be part of the system).
* `gate_select_inverse`: the inverse instruction list runs as the adjoint of the circuit and
  has the same validity and counts ("The inverse is the adjoint of the actual circuit and has
  the same resource bounds").
* Per branch: `branch_block` (within `ε` of the ordered product of the branch slot exponentials
  `exp (-i (u/2^m) X j)`), `branch_propagator` (within `ε + β u² / 2^m + u δ` of every
  propagator), `branch_error` (one label under the lemma's hypotheses); `select_error` combines
  the branches.

**Theorem `ode:thm:gates`, time-dependent part, on branch-dependent meshes** (`ODE.solverB`,
`ODE.native_ode_time_solverB`, modules `ODE/*`).

* Protocol: the released `GateODE.Time.TParams.protocol p v` for released public data `p` with
  `GateODE.Time.TParams.PublicOK p`, so validity, worst-case counts (`80 g · prepGates +
  40 g · reflGates` gates, `480 g d` private calls, `960 g d` calls of `U_J` or `U_J†`, `80 g`
  loading, `160 g` weight-preparation calls, `40 g` seed reflections), register and degree bounds
  are the released ones (taken from `GateODE.Time.solver`).
* Branches: the source label `s = (ini, q)` starts at `ODE.startB v s` (`0` for the initial
  labels, a node `v q ∈ [0, T]` for the forcing label `(true, q)`, `q < 2^m`) and runs for
  `ODE.durB v s = T - startB v s` on its own mesh with the addresses `ODE.addrB v s r`. The
  private operation of the joint label `z = (s, w)` at slot `r` carries the clock promise for
  the rescaled normalised slot Hamiltonian `ODE.branchHB = (durB s / τ)(Hb s r + k_w Lb s r)`,
  `τ = T (λH + R λD)`, for represented branch samples `Hb s r`, `Lb s r` (self-adjoint,
  `‖Hb‖ ≤ λH`, `‖Lb‖ ≤ λD`, `Lb ≥ 0`) with `‖G(addrB s r) - (Lb s r + i Hb s r)‖ ≤ δG` for an
  accretive `βG`-Lipschitz generator path.
* Source quadrature: weights `wq q ≥ 0` and forcing vectors `fv q`; the source vector of the
  forcing label `(true, q)` is `w_q f_q` (`ODE.zsrc_bsW`, through `ODE.bsW` in the released
  source format) and `B = ‖x(0)‖ + ∑_q w_q ‖f_q‖` (`ODE.mass_bsW`); the released
  weight-preparation promise and loading of the directions of `x(0)` and of every `f_q` with
  `w_q ≠ 0` ("Terms of zero weight are omitted").
* Certificate (`ODE.BInstanceOK`): a solution `x` of `x' = -G(u) x + b(u)` on `[0, T]` with
  `x(T) ≠ 0` and `B ≤ g ‖x(T)‖`; homogeneous solutions `y_s` of `y' = -G(u) y` on
  `[startB s, T]` with `y_s(startB s) = z_s` (informally `y_s(T) = U(T, v_s) z_s` for the
  propagator `U` of the paper, which is not a Lean object here), which exist
  (`ODE.exists_branch_solution`); the source certificate `‖x(T) - ∑_s y_s(T)‖ ≤ κ`; and the
  budget `κ + T (βG T / 2^m + δG) B ≤ ε B / (2000 g)`. With `f_q = b(v_q)` the source certificate
  is the first certificate of `ode:eq:gate-source-certificates`; as in the paper it is a
  hypothesis, and the solution and the forcing enter the proof of `ODE.solverB` only through
  `x(0)`, `x(T)` and this certificate (the field `solves` records that `x` solves the forced
  equation; `ODE.quad_leftEndpoint` uses it, `ODE.solverB` does not).
* Left-endpoint quadrature (`ODE.quad_leftEndpoint`, the sufficient positive quadrature of the
  proof of Theorem `ode:thm:gates`): for the nodes `ODE.vLeft q = q T / 2^m`, the weights
  `ODE.wLeft q = T / 2^m` and the forcing samples `b̃_q` of the released solver, the certificate
  holds for every solution `x` of the forced equation with a `βb`-Lipschitz forcing bounded by
  `bmax`, `‖b(q T/2^m) - b̃_q‖ ≤ δb`, and the samples of the initial branch, with
  `κ = discretisation + T (βG T / 2^m + δG) B` (`GateODE.Time.TParams.discretisation` the
  released certified error of the left-endpoint recurrence). Here the number of nodes is the
  number `2^m` of slots, and the bound is cruder than the paper's
  `T² [√s (η_D + η_H) b_* + L_b]/(2m)`: with the budget
  of `ODE.BInstanceOK` the generator terms are paid twice,
  `discretisation + 2 T (βG T / 2^m + δG) B ≤ ε B / (2000 g)`, which is stricter than the
  condition of the released masked solver for the same quadrature.
* Guarantee: the released `GateODE.Time.TParams.Outcome` for `x(T)`: success probability at
  least `175/256 > 2/3`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global
  phase, and a conditional output density operator within trace distance `ε` of `x(T)/‖x(T)‖`.
  Natively (`ODE.native_ode_time_solverB`): the released native protocol, counts and wires, and
  under `ODE.BInstanceOK` for the ideal oracles with the released error budget
  `24 d ζ + 3 ζs ≤ ν` the released `GateNative.NOutcome`.
* Every one of the `2^(m+1)` source labels carries branch samples, clock promises and a branch
  solution: the initial labels `(false, w)` with `w ≠ 0` have the source vector `0` and the start
  `0` (the samples of the initial label serve), and padding nodes of weight `0` may be put at
  `v q = T` (a branch of duration `0`, the zero normalised Hamiltonian).

**Non-vacuity.** For the lemma (module `NonVacuity`): `clock_scalar` (with `U_J = 1`, the scalar
operation `cayleyScalar s • 1`, `cayleyScalar s = (i s - 1)/(1 + i s)` of modulus one, carries the
clock promise for `s • 1`, `|s| ≤ 1`, `Q = qbar = 1`); `nv_all_hyps` (every hypothesis of
`gate_select` holds at once for one label wire with the labels `(v, k) = (0, 0)` and `(1/2, 1)`,
`H(t) = t · 1`, `D(t) = (1/4) · 1`, samples with error `1/16` on `m = 4` slot wires, `T = 1`,
`α = 2`, `R = 1`, `δ = 1/16` and `ε = 1/2`, on every system and for every number of ancilla
qubits); `nv_select` (`gate_select` applies to them). For the solver (module `ODE/NonVacuity`):
`ODE.nv_instance` (every condition of `ODE.BInstanceOK` holds for `x' = 1` on `[0, 1]`,
`x(0) = 0`, with the node `1/3` of weight `1`, whose branch addresses `1/3`, `2/3` are not points
of the common mesh, the public data `ODE.nvP` with `m = 1`, and explicit unitaries, among them a
permutation matrix as weight preparation), `ODE.nvB_outcome` (`ODE.outcomeB`, the instance
clause of `ODE.solverB`, applies to them); the generator of this witness is zero, so its branch
samples and clock promises hold trivially and the branch meshes are not exercised by the
dynamics.

**Proof map** (module paths relative to `GateEfficientSelect/`).

* `Model`: `runS_eq` (induction with `GateCircuit.localOp_comp`), `runS_invList`
  (`GateCircuit.SlotSim.runT_invList`), `runS_isUnitary`, `labCfg`, `selE`, `select_error`
  (`GateODE.localOp_branch_error`).
* `Branch`: `clock_family`, `qbar_nonneg_of_clock`, `exp_branch_step` (one simulator step
  `τ/2^m` of `(u/τ) X` is the step `u/2^m` of `X`), `branch_block`
  (`GateCircuit.SlotSim.simulationT`), `branch_propagator` (`TimeDependent.mesh_error` on clamped
  samples).
* `Lemma`: `branchPath_selfAdjoint`, `branchPath_lipschitz`, `branch_budget`, `branch_error`,
  `gate_select` (`GateCircuit.SlotSim.simCircuitT_public`, `SharpFilterSchedule.degree_le`,
  `TimeDependent.exists_solvesOn_of_lipschitz`), `gate_select_inverse`.
* `ODE/Branch`: the branch data, `ODE.exp_branchHB`, `ODE.evolution_branchHB`
  (`TimeDependentODE.GaussianLCHS.productFamily_ofReal`), `ODE.branch_blockB` (`branch_block`),
  `ODE.select_errorB` (`GateODE.Time.TParams.select_error_of_blocks`).
* `ODE/Table`: `ODE.lchs_errorB` (`GateODE.AnalyticLCHS.table_certificate` with
  `GateODE.Time.productFamily_norm_le_exp` and the branch durations summing to
  `durB s ≤ T`), `ODE.propB_norm_le`, `ODE.targetB_norm_le`.
* `ODE/Disc`: `ODE.solvesODE_shift`, `ODE.propB_eq`, `ODE.branch_disc`
  (`TimeDependentODE.mesh_error` without forcing on the shifted interval,
  `TimeDependentODE.recurrence_eq_sum`), `ODE.target_errorB`.
* `ODE/Certificate`: `ODE.BInstanceOK`, `ODE.target_factsB`
  (`TimeDependentODE.Sampling.target_budget`), `ODE.prep_certificateB`
  (`ODEActualSourceError.actual_source_certificate`), `ODE.trial_boundsB` (the released
  `GateODE.Time.TParams.decoded_eq`, the agreement and counts of the released trial circuits,
  `ODEGroverActual.randomized_certificate`).
* `ODE/Theorem`: `ODE.exists_branch_solution` (`TimeDependentODE.exists_solvesODE`),
  `ODE.outcomeB` (the bounded four-attempt protocol, as `GateODE.Time.TParams.outcome`),
  `ODE.solverB`.
* `ODE/Native`: `ODE.native_time_outcomeB`, `ODE.native_ode_time_solverB` (as
  `GateNative.native_time_outcome` with `GateNative.oprep_approx`,
  `GateNative.native_trial_bounds`, `GateNative.noutcome_of_bounds`).
* `ODE/Left`: `ODE.maskedPropagator_eq_shift`, `ODE.homog_disc` (`TimeDependentODE.mesh_error`
  on `[a, c]`), `ODE.quad_leftEndpoint` (the released `GateODE.Time.TParams.discretisation_error`
  and `GateODE.Time.TParams.source_sum`, and `ODE.homog_disc` for every masked propagator).
* `NonVacuity`: `cayleyScalar_norm`, `isUnitary_smul_one`, `clock_scalar`, `nv_sample_eq`,
  `nv_steps` (`steps 2 (1/12) ≤ 16`), `nv_all_hyps`, `nv_select`.
* `ODE/NonVacuity`: `ODE.permMat_unitary`, `ODE.nvP_ok` (`steps (1/100) (ν/3) ≤ 2`),
  `ODE.nv_mass`, `ODE.nv_zsrc`, `ODE.nv_instance`, `ODE.nvB_outcome`.

**Formalisation choices.**

* Sample positivity (a formal restriction): the time-dependent ODE solvers assume `Lb ≥ 0` for every
  represented sample, the hypothesis of the formal versions of Theorem `ode:thm:time`, which that
  theorem of the manuscript does not make (it asks of the represented samples only the uniform
  moment and norm promises; see `TimeDependentODE/Statements.lean`). `RepresentedSampleODE` lifts it
  for the query-level mesh solvers and the common-mesh gate solver; the conformance endpoints
  `ManuscriptConformance.ode_thm_time`, `ode_thm_gates_time_cert` and
  `ode_thm_gates_time_decoder_cert` hold for represented samples of any sign. The manuscript's
  theorems are not changed.
* The step `u_z/2^m` of branch `z` enters through the rescaled normalised sample `(u_z/(α T)) X`
  of its private operation, simulated with the common step `α T/2^m`, rather than through the
  boundary rotation parameter `c_z = (1 - w_z/2)/(1 + w_z/2)`, `w_z = α u_z/2^m`, of the proof.
  Both give the same Cayley step of the branch (`exp_branch_step` at the level of the slot
  exponentials); here the boundary rotations, the circuit and its counts do not depend on the
  label, as for the constant-coefficient released solver (`GateODE.Params.branchH`); the
  released masked solver uses the same mechanism with the slot-dependent scale
  `T [start ≤ r] / τ`. Consequently the per-label work is part of the hypothesis on the private
  operations: the clock promise is required for the rescaled sample, which the paper's private
  operation `C₀(k_z, ·)` (normalised by `α` alone) satisfies only for `u_z = T`; that the
  rescaled operations can be realised (for example by multiplying the decoded value by `u_z/T`
  in the angle arithmetic) with clock constants `Q`, `qbar` independent of the label is
  assumed, not derived (the released binary-data constant-coefficient solver derives it for
  its branch durations).
* The package's own filter degree `d = GateCircuit.Sim.fDeg Q (α T) qbar (ε/2)` and mesh
  condition (the released subdivision condition and the freezing condition
  `4 (βH + R βD) T² ≤ ε 2^m`) replace the schedule `ode:eq:gate-select-schedule` and the mesh
  condition `ode:eq:gate-select-mesh`; the error budget is `ε/2` for the simulation, `ε/4` for
  freezing and `ε/4` for the samples, and the sample errors are bounded uniformly by `δ` (the lemma
  allows an integrated certificate).
* The differential-equation endpoints keep the released protocol, so the source label has
  `m` bits: a quadrature with at most `2^m` nodes is padded with zero weights, and one with more
  nodes needs a larger `m` (a finer mesh of every branch, which keeps the mesh conditions). They
  use the per-branch block `branch_block` of the lemma's proof, not `gate_select` itself: the
  exact target is that of the ordered products of the branch slot propagators, with LCHS applied
  to the ordered product families as in the released solver, and each branch is compared with
  its homogeneous solution by discretising the dissipative generator on the branch mesh
  (`ODE.branch_disc`), in place of the lemma's Hamiltonian freezing.

**Not formalised.**

* The arithmetic part of the lemma: the coherent computation of the branch addresses and scales
  from the label (for a power-of-two source mesh the integer addresses `T (iM + (m-i)r)/(mM)` on
  a grid of `mM` points), the time-indexed binary sparse oracles on that grid, the gate count
  `ode:eq:gate-select-gates` and the work space `A_sel`. The binary-data time-dependent solver
  (`GateBinaryODETime`) and its finite-gate-set, budget and certificate forms keep the masked
  common mesh.
* The paper's construction with label-dependent boundary rotations `R(c_z^M)`,
  `B_in(c_z^{2^j})`, `B_out(c_z^{2^j})` computed coherently from the label by repeated squaring
  (the coherent per-label angles), and its Hölder bound for `R`.
* The source certificate for quadratures other than the left-endpoint one (the paper bounds the
  quadrature error through the Lipschitz constant of `v ↦ U(T, v) b(v)`, which needs the Duhamel
  formula for the dissipative propagator), and the comparison `B_m ≤ 2B` with the continuous
  source mass.
* Integrated sample-error certificates and nonuniform meshes of the branches; finite-gate-set
  synthesis of the branch-dependent native solver.

**Provenance.** New library, written against the released package: it imports
`GateEfficientODE`, `GateEfficientTimeDependent` and `GateEfficientNative` (with their
dependencies) and changes none of them. The statement guides of `GateEfficientMesh` and
`GateEfficientBinaryODETime` and the README list the branch-dependent meshes of
`ode:lem:gate-select` as not formalised; the meshes are formalised here in the form stated
above, while the coherent per-label angles of the lemma's proof, also listed there, remain
outside.
-/
