import GateEfficientNative.Corollaries

/-!
# Native gate-efficient algorithms: paper-to-Lean entry point

This library completes the gate analyses of Theorems `hs:thm:gates` and
`ode:thm:gates` of the accompanying paper on top of the exact-gate
libraries `GateEfficientHamiltonian`, `GateEfficientTimeDependent` and
`GateEfficientODE`: every supplied oracle of those circuits is replaced by a
native implementation, and the error of the implementation is propagated
through the circuits in the paper's full-output convention.
References to the manuscript use its labels.

* Hamiltonian simulation: `SparseHamiltonian.GateNative.native_simulation`
  (constant `H`), `native_simulation_signed` (every real time),
  `native_time_simulation` (time-dependent `H`), with the counts from the
  public data alone (`nativeSim_counts`) and the sparse form of
  `hs:eq:gate-binary` (`native_sparse_counts`), in
  `GateEfficientNative/Hamiltonian/Theorem.lean` and
  `GateEfficientNative/Corollaries.lean`.
* Dissipative ODEs: `SparseHamiltonian.GateNative.native_ode_solver`
  (constant coefficients, `GateEfficientNative/ODE/Constant.lean`) and
  `native_ode_time_solver` (time-dependent coefficients,
  `GateEfficientNative/ODE/Time.lean`), with the explicit worst-case gate
  counts underlying `ode:eq:gate-main` (`native_ode_gate_count`,
  `native_ode_time_gate_count`).

All names below are in the namespace `SparseHamiltonian.GateNative` unless
stated otherwise.

**Gate model** (`Model/Instr`). A native circuit acts on qubit wires `V` with
a payload Hilbert space `R` (`Reg V R`). Its instructions (`NInstr`) are

* elementary gates: one-qubit unitaries with at most three literal
  controls, all off the target (`NInstr.Valid`, `GateOK 3`), the gate model
  of the released gate-level libraries; one gate counts one;
* calls of a primitive oracle `prim j : Reg Y R →L[ℂ] Reg Y R` or its
  inverse, placed on wires `pos : Y ↪ V`; one call counts one.

`nrun prim is` is the operator of a circuit (the head acts first),
`nGatesN is` its number of elementary gates and `nCallsN q is` its number of
calls of the oracles `j` with `q j`, forward and inverse alike. The
user-selected convention is that one-qubit unitaries with up to three
controls are elementary; they are not synthesised over a finite gate set.

**Full-output convention** (`Model/Approx`, `Model/Flatten`). For a circuit
`C` on `B ⊕ X` (work wires `X`) and an operator `O` on `B`,
`ApproxOn CleanX C (liftB O) δ` states `‖C ψ - (O ⊗ 1) ψ‖ ≤ δ ‖ψ‖` for every
`ψ` supported on clean work wires; with the clean embedding `cleanEmb` this is
`‖C ∘ cleanEmb - cleanEmb ∘ O‖ ≤ δ` (`norm_sub_cleanEmb_le`): every residual
work-wire state counts, and no global phase is allowed. A released register
`Reg W (Reg S R)` with a qubit system `S` and an untouched reference `R` is
identified with `Reg (W ⊕ S) R` (`flat`, `conj`).

**The native private Cayley operation** (`Native/*`). On an edge with
represented value `z` the private Cayley operation acts on the orientation
qubit by `D_edge(z) = ((|z|² - 1) I + 2 i [[0, z], [z̄, 0]]) / (1 + |z|²)`
(`edgeMat`, equation `hs:eq:edge`), which equals
`-R_z(-φ) R_x(2θ) R_z(φ)` with `θ = 2 arctan |z|` and `φ = arg z`
(`edgeMat_eq_angMat`, `angMat_eq_rot`). The public data (`NativeOp`) are a
compute circuit `V` of elementary gates and primitive calls on the selection
wires `Sel`, the private register (ancillas and system) and scratch `Z`, the
orientation wire `o`, and a decoder `dec` of the represented entry; the
public arithmetic (`Arith`) is a gate circuit with `A` work wires that writes a
`bT`-bit word `θ̃` and a `bP`-bit word `φ̃`.

* Public hypotheses: `NativeOp.Public` (`V` valid, `dec` independent of the
  orientation wire) and `ArithOK ar o dec ζ`: the arithmetic consists of
  classical controlled NOT gates with at most three controls; on clean
  arithmetic wires it writes the words and restores its work wires; the
  words do not depend on the orientation wire; and `|θ(θ̃) - 2 arctan |z|| ≤ ζ`,
  `|φ(φ̃) - arg z - 2πk| ≤ ζ` for some integer `k` when `z ≠ 0`
  (`thetaVal`, `phiVal`: binary fractions of `π` and `2π`). This is the
  decoding and arithmetic hypothesis behind `G_C`, `A_C` of `hs:thm:gates`.
* Instance hypothesis: `NativeOK prim nd Dsel`: `V† R_val V` acts as the
  selected private operation `Dsel` on clean scratch, where `R_val` is the
  edge rotation of the decoded entry on the orientation wire (the native
  form `D₀ = F† O_val† R_val O_val F` of the paper).
* Implementation (`privMacro`): `V`, the arithmetic, the bit-controlled
  rotations `-R_z(-φ̃) R_x(2θ̃) R_z(φ̃)` under the enable wire (`rotGates`,
  `2 bP + bT + 1` gates with at most two controls), the inverse arithmetic
  and `V†`: `G_C = 2 nGatesN V + 2 |circ| + 2 bP + bT + 1` gates
  (`privGates`), `2 nCallsN V` calls, and the work wires `Z`, the two words
  and `A` arithmetic wires. Its error (`privMacro_approx`): within `4ζ` of
  the enable-controlled selected operation in the full-output convention,
  for the macro and for its literal inverse.

**Native macros** (`Hamiltonian/Layout`, `Hamiltonian/Macro`,
`Hamiltonian/Approx`, `Hamiltonian/Circuit`). Every released instruction is
replaced by a macro (`hmacro`): a gate by itself; a sector-controlled call of
`U_J` by the `C_J` elementary gates `UJg` of `U_J`, each with the sector wire
as an additional control (a gate that already has three controls uses an AND
chain on three clean flags, at most 7 gates per gate); a sector-controlled
private call by `privMacro`, enabled by the sector wire and selected by the
selection wires. The macro of every instruction is within its error weight
(`4ζ` for a private call, `0` otherwise) of the lifted released instruction
(`hmacro_approx`), and the errors add along the circuit (`hcirc_approx`,
`hcirc_error`).

## Hamiltonian simulation

`native_simulation`: the native circuit `nativeSim a τ Q qbar ε UJg nd ar` is
the released circuit `GateCircuit.Sim.simCircuit a τ Q qbar (ε/2)` with
native macros; it depends only on the public data. Hypotheses: unitary
primitive oracles; `U_J` given by its gates `UJg` (each `GateOK 3`); public
`nd` and `ArithOK` at accuracy `ζ ≥ 0`; a unitary private operation `D` with
`NativeOK prim nd D`; the clock promises of the released analysis for `D`
and `J = U_J ι₀` (`(1 - D) R1 = R1 (1 - D) = 1`, `‖R1‖ ≤ Q`,
`J† R1 J = (1 + iH)/2` with `H` self-adjoint and `‖H‖ ≤ 1`,
`‖R1 J‖ ≤ b`, `b² ≤ qbar/2`, `qbar ≤ Q`); `τ ≥ 0`, `Q ≥ 1`, `0 < ε ≤ 1`;
and the arithmetic budget `48 d ζ ≤ ε`, `d = fDeg Q τ qbar (ε/2)`.
Conclusions: every instruction is valid; for every set of primitive oracles
the circuit makes exactly `12 d` times the calls of `V`; it uses at most
`200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` elementary gates on
`|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3)` qubits; and

`‖nrun prim (nativeSim …) ∘ sysEmb io - sysEmb io ∘ exp(-iτH)‖ ≤ ε`,

where `sysEmb io` puts the system state on the system qubits with every other
qubit zero and the reference `R` untouched; also
`d ≤ 128 (τ qbar + Q (1 + log (6/ε)))`, `steps ≤ 2^m < 2 steps`,
`2d + 2 ≤ 2^r ≤ 4 (d+1)`. The released circuit at accuracy `ε/2` and `6d`
native private calls at accuracy `4ζ ≤ ε/(12d)` each give `ε`; this is twice
the paper's `ξ = ε/(24d)`, since no budget is reserved for finite-set
synthesis.

`native_simulation_signed`: every real time `t`; for `t < 0` the literal
inverse circuit, with the same counts and error against `exp(-itH)`.

`native_time_simulation`: time-dependent `H` on `2^m` slots (the released
slot circuit for accuracy `ε/2`, filter parameter `ε/4`, with native macros)
with the slot-selected private operations `D k` given natively by one compute
circuit on the slot wires
(`NativeOK prim nd (selOp (fun w => D (wordEquivFin m w)))`),
the clock promises at every slot, the mesh conditions
`steps (α t) (ε/12) ≤ 2^m`, `8 β t² ≤ ε 2^m`, `8 t δ ≤ ε` and
`48 d ζ ≤ ε`: the same counts, and full-output error at most `ε` against
`U(t)` for every propagator `U` of the path (which exists).

`nativeSim_counts`: the counts depend only on the public data.
`native_sparse_counts` (equation `hs:eq:gate-binary`): for sparsity `s ≥ 1`,
norm bound `η ≥ 0`, time `t ≥ 0` and `0 < ε ≤ 1/2`, with
`q = √s ηt + √(s ηt log(1/ε)) + log(1/ε)`, the released precision budget
chooses `γ`, hence `Q`, `qbar` and the rescaled time `τ = η √s t/γ ≤ √s q`,
such that `d ≤ 4608 q`, `2^m < 2 (2 + 4τ + √(6τ³/ε))`,
`2^r ≤ 4 (4608 q + 1)`, and for all native data the circuit makes at most
`55296 q` times the calls of `V` and uses at most
`200 (4608 q + 1) (G_C + C_J + a + m + r + 1)` elementary gates. With per-call
costs `G_C + C_J + a` polynomial in the data bit length, `log (N+1)` and
`log (1/ζ)` (a hypothesis on the decoding, the arithmetic and `U_J`), this is
`q · poly(b_data, log (N+1), log ((q+1)/ε))`, using `s ≤ N` and
`ζ = ε/(48d)`.

## Dissipative ODEs

The native register (`HWO`, `NW`, `TNW`) consists of the released solver
wires, the system qubits `S`, the scratch, word and arithmetic wires of the
private implementation, three flags for the controlled `U_J` gates, the
source scratch `Zs`, and one flag and a pool of clean wires for the native
zero tests. The reflections of the amplification test every non-system wire
other than the native flag and pool for zero exactly (multi-controlled gates
with AND chains on the native pool, `ODE/Grover`); the flag and the pool stay
clean because no preparation instruction touches them (`Model/Touch`). The
seed is the all-zero state (`seedV`, `sN`) and success is heralded by the
clean non-system wires (`goodN`).

`native_ode_solver` (constant coefficients, public data `GateODE.Params`
with `PublicOK`): the native protocol
`nprotocol (nprepC p UJg nd ar srcC) g` is the released four-attempt
wrapper around the native trial circuits, where `nprepC` is the released
preparation with native macros: `U_J` by its gates, the label-selected
private calls by `privMacro` on the label wires, and the controlled source
interfaces `J₀`, `J_b` by supplied native circuits `srcC false`,
`srcC true` on the control, the system and `Zs` (the hypothesis `G_src`,
`A_src`). Public conclusions: valid trials; one preparation uses at most
`prepGates + 84 d C_J + 6 d G_C + |srcC 0| + |srcC 1|` gates and at most
`12 d calls(V) + calls(srcC 0) + calls(srcC 1)` calls of every set of
primitive oracles; in every history (including four failures) the protocol
uses at most `40 g` times these, plus `20 g (4 n + 3)` gates for the zero
tests (`n` counts every wire except the native flag and pool, the system
qubits included); and the qubit count. Instance
conclusions: for unitary primitive oracles, `NativeOK prim nd` for the
label-selected family `D z`, source circuits within `ζs` of the controlled
interfaces (`srcIdeal`), the released instance conditions
(`GateODE.Params.InstanceOK`) for `(U_J, D, J)` and the error budget
`24 d ζ + 2 ζs ≤ ν`, the native protocol satisfies `NOutcome`: unitary
trials, mean success at least `1/4`, direction error at most `ε/500` up to
a phase for every successful trial, success probability at least
`175/256 > 2/3`, and a conditional output density operator within trace
distance `ε` of `x(T)/‖x(T)‖`.

`native_ode_time_solver` (time-dependent coefficients, public data
`GateODE.Time.TParams` with `PublicOK`): the same structure with the label-
and slot-selected private calls (`tlabFam`, selection wires `TSel`: the
label wires and the slot wires), a loading circuit `loadC` within `ζs` of the
selected loading `J s` (`loadIdeal`) and a weight-preparation circuit `wpC`
within `ζs` of `Wp`; one preparation uses at most
`prepGates + 84 d C_J + 6 d G_C + |loadC| + 2 |wpC|` gates; the protocol has
ratio `2g`; the error budget is `24 d ζ + 3 ζs ≤ ν`; and `NOutcome` holds
against `x(T)` under the released instance conditions
(`GateODE.Time.TParams.InstanceOK`; their sample positivity `L_r ≥ 0` is the
formal restriction stated in `TimeDependentODE/Statements.lean`; `RepresentedSampleODE` lifts it for
the query-level mesh solvers and the common-mesh gate solver; the conformance endpoints
`ManuscriptConformance.ode_thm_time`, `ode_thm_gates_time_cert` and
`ode_thm_gates_time_decoder_cert` hold for represented samples of any sign).

`native_ode_gate_count`, `native_ode_time_gate_count` (the explicit counts
underlying equation `ode:eq:gate-main`): in every history the native
protocols use at most
`9000 g [(d+1)(a+m+r+1+C_J+G_C) + (k+1) + (J+2)(l+1) + G_src + A]` and
`18000 g [(d+1)(a+m+r+1+C_J+G_C) + (J+2)(l+1) + G_src + A]` elementary gates,
where `A = |S| + |Zs| + |Z| + bT + bP + A_ar`; the public sizes `d`, `m`, `r`,
`l` and `J` are bounded by the released size lemmas (for example
`GateODE.Params.degree_bound`, `GateODE.Params.sim_sizes`,
`GateODE.Params.l_bounds`, `GateODE.Params.J_le_log`). The qubit counts of
`native_ode_solver` and `native_ode_time_solver` are the explicit form of
`ode:eq:gate-space`.

**Proof map.** Module paths are relative to `GateEfficientNative/`.

* Native instructions, runs, inverses, renaming and counts: `Model/Instr`.
* The full-output calculus (`ApproxOn`, telescoping, adjoints, lifting
  through exposed operators): `Model/Approx`; flattening of register
  payloads and clean work wires: `Model/Flatten`; wires never touched by a
  circuit: `Model/Touch`.
* The edge rotation, its angle form and the angle-error bound: `Native/Edge`
  (`edgeMat_eq_angMat`, `angMat_eq_rot`, `frob2_angMat_sub_le`); the
  bit-controlled rotation circuit: `Native/Rotation` (`gRun_rotGates`);
  the native private operation and its `4ζ` error: `Native/Private`
  (`privMacro_approx`); selection and lifting: `Native/Lift`.
* Macros, their errors and counts, and the Hamiltonian theorems:
  `Hamiltonian/*` (`hmacro_approx`, `hcirc_error`, `hcirc_nGates`,
  `native_simulation`; negative times through the literal inverse:
  `err_neg`).
* ODE macros and the native preparation error (`ODE/Macro`:
  `oprep_approx`); native zero tests and trials (`ODE/Grover`: `trialN_seed`);
  the enlarged vector error `9νB` and the trial bounds (`ODE/Certificate`:
  `trial_bounds_of_vec`, `native_trial_bounds`); the protocol
  (`ODE/Protocol`: `nprotocol_worst`, `noutcome`); the solvers:
  `ODE/Constant`, `ODE/Time`.
* Public counts and the sparse form of the gate count: `Corollaries`.

**Formalization choices.**

* Elementary gates are one-qubit unitaries with at most three controls; the
  rotation angles of the native private operation are exact binary
  fractions of `π` and `2π`, so no finite-gate-set synthesis is formalised.
  The decoding and the reversible angle arithmetic are public circuits
  whose correctness at accuracy `ζ` is a hypothesis (`ArithOK`), and the
  native identity `NativeOK` relates the supplied private operation to the
  compute circuit; the rotations and their errors are proved.
* The released circuits are reused: the Hamiltonian circuits for accuracy
  `ε/2` (filter parameter `ε/4` for the time-dependent circuit) and the ODE
  preparations as released, with the vector error enlarged from `6νB` to
  `9νB` (`output_certificate9`), which still gives the released amplitude
  interval and direction error.
* The ODE reflections test all non-system qubits other than the native flag
  and pool, including the work qubits of the private implementation and of
  the source circuits, exactly; the native preparation never changes the
  native flag and pool (`Model/Touch`).
* `regIsTopologicalRing` (a scoped instance of `SparseHamiltonian.GateNative`)
  records that the operators on a qubit register with a payload form a
  topological ring, so that `NormedSpace.exp` can be stated on
  `Reg S R →L[ℂ] Reg S R`; Mathlib's instance search does not reach it
  through the `PiLp` norm. It is a proposition, so the exponential is the
  usual operator exponential.
* Not formalised: finite-gate-set synthesis, the construction of the compute
  circuit and of the arithmetic from a concrete data format (they are
  hypotheses), the construction of the source circuits (hypotheses with
  their gate counts), and classical circuit-generation costs.
-/
