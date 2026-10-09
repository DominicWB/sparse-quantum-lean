import GateEfficientBinarySelect.NonVacuity

/-!
# Coherent selection from binary data and Theorem `ode:thm:gates` on branch-dependent meshes:
paper-to-Lean entry point

Lemma `ode:lem:gate-select` of the accompanying paper (gate-efficient coherent selection,
manuscript line 4554) selects, coherently from a label `z` that specifies a frequency
`|k_z| ≤ R` and a start time `0 ≤ v_z ≤ T`, the propagator of `H(t) + k_z D(t)` from `v_z` to
`T`. In its proof every branch has its own mesh with the sample addresses `v_z + r u_z/M`
(line 4610), and the represented samples there must have a "certified total operator-norm
error, integrated over the selected interval, [of] at most `δ/16`" (lines 4574-4577). For
efficiently decoded binary entries the lemma claims the additional gate count
`G_sel(δ) = d poly(b_data, log(N+1), log M, log((d+1)/δ))` (`ode:eq:gate-select-gates`, line
4591) and a reusable work space `A_sel(δ)` without the leading factor `d` (line 4597); for a
power-of-two source mesh the sample address is an integer address on a uniform grid, "computed
by multiplication and addition" (lines 4657-4665). Theorem `ode:thm:gates` (line 4751) allows a
positive source quadrature whose nodes "are computed coherently from their labels" (line 4737);
its word budget `𝔟` (`ode:eq:gate-word-budget`, line 4763) contains a term `log(m+1)` for the
`m` nodes, and it bounds the gates and qubits by `ode:eq:gate-main` and `ode:eq:gate-space`
(lines 4773-4776), with the per-trial claim "every successful trial has Euclidean error at most
`ε`, up to a global phase" (line 4784).

The released libraries formalise the lemma with exact gates under a uniform sample bound and
with the clock promise for the rescaled samples as a hypothesis (`GateEfficientSelect`), the
time-dependent part of the theorem on these meshes with exact gates and natively, for a general
positive quadrature and for the sufficient left-endpoint one (`GateEfficientSelect`,
`GateEfficientQuadrature`), and the binary-data, finite-gate-set and budget forms of the
time-dependent solver on one common mesh with masked source branches only
(`GateEfficientBinaryODETime`, `GateEfficientSynthesisTrials`, `GateEfficientODEBudget`,
`GateEfficientBitBudget`). This library proves:

* the lemma under the integrated sample-error certificate `δ/16` and the mesh condition
  `M ≥ 8 L_* T²/δ` of the paper, with exact gates (`gate_select_certified`), and under integrated
  slot certificates of merely integrable branch paths (`gate_select_integral`);
* the lemma with native private calls (`native_gate_select`, with the inverse
  `native_gate_select_inverse`) and, for time-indexed binary sparse data, the labels of the
  dissipative solver and the power-of-two source mesh of the proof, with the rescaled private
  operations constructed and their clock promises proved with clock constants that do not
  depend on the label, with exact gates (`binary_gate_select`), and natively also with the
  arithmetic constructed (the branch address is computed coherently from the label and the slot
  index, and the branch scale from the label, by a register program) and with explicit `G_sel`
  and `A_sel` (`binary_native_gate_select`, `select_gates_words`, `select_gates_bits`, and for
  the circuit itself at `δ = 4ν`, `ν` the accuracy parameter of the solver,
  `binary_select_lemma_words`, `binary_select_lemma_bits`);
* the time-dependent part of Theorem `ode:thm:gates` from time-indexed binary sparse data on
  these meshes, for positive source quadratures whose nodes are the `2^m` dyadic nodes `u T/2^m`
  of the power-of-two source mesh (one node per slot of a branch; any weights `w_u ≥ 0`, so any
  quadrature with nodes on a dyadic grid of at most `2^m` points): natively
  (`binary_select_solver` for any such weights, `binary_select_solverL` for the left-endpoint
  weights), over a finite gate set (`binary_select_solver_synth`, `binary_select_solverL_synth`,
  and with the per-trial claim `binary_select_solver_trials`, `binary_select_solverL_trials`),
  and equations `ode:eq:gate-main` and `ode:eq:gate-space` with explicit constants in the query
  shape `q*`, in the register words and in `𝔟` (`binary_select_budget`,
  `binary_select_budget_words`, `binary_select_budget_bits`), also over a finite gate set with
  the per-trial claim (`binary_select_budget_trials`, `binary_select_budget_trials_bits`).

Source nodes computed by other coherent arithmetic (non-dyadic nodes, or more nodes than slots
per branch without refining the branches) are not covered; see *Not formalised*. No result from
another paper is used. The released libraries are unchanged. Manuscript lines refer to
`sparse_quantum_algorithms.tex` (v21); the labels are the stable references. Every theorem of the
library is axiom-audited in `GateEfficientBinarySelect/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateBinarySelect` and are named relative to it below. Released declarations
are named relative to `SparseHamiltonian` (for example `GateSelect.gate_select`,
`GateBinaryODETime.PubT`, `GateQuad.LInstanceOK`), except those of the library
`TimeDependentExtensions`, which are named in full.

**Notation.** In the generic lemmas the paper's accuracy `δ` is `ε`, in the binary-data ones it
is `δ`. `M = 2^m` is the number of slots of every branch, `τ = α T` the common normalised time,
`βH + R βD` plays the role of `L_*`, and `d = GateCircuit.Sim.fDeg Q τ q̄ (ε/2)` (exact gates)
or `fDeg Q τ q̄ (ε/4)` (native) is the released filter degree, with the reuse register
`r = GateCircuit.Sim.simR …` (`2d + 2 ≤ 2^r ≤ 4 (d+1)`). For binary data the public data are
`q : GateBinaryODETime.PubT` (system qubits `k_x`, slot bits `σ`, stored bits `b`, decoder scale
`c₀`, energy bounds `η_H`, `η_D`, Cayley rescaling `γ`, time `T`, amplification bound `g`,
accuracy `ε`, mesh bits `m`, arithmetic accuracy `ζ`) with the released parameters `q.params`
(`λ_H = √(4s) η_H/γ`, `λ_D = √(4s) η_D/γ`, frequency bound `R`, `τ = T (λ_H + R λ_D)`,
`ν = ε/(40000 g)`, the solver's degree `q.params.d = fDeg Q τ q̄ ν` and reuse register
`q.params.r`) and the released conditions `PubT.OK` (including the released mesh condition
`steps τ (ν/3) ≤ 2^m`). The source label `(ini, u)` of the released protocol carries the sector
bit `ini`, set on the forcing labels `(true, u)`, and the node word `u` of `m` bits; the branch
of `(true, u)` starts at the dyadic node `v_u = u T/2^m` (`GateQuad.vQ`), that of an initial
label at `0`, so the start is `u' T/2^m` with `u' = (ini ? u : 0)`. The paper's `m` nodes are
`2^m` nodes here and its grid of `mM` points has `2^(2m)` points; the time-indexed binary data
`D : Data (X × Fin (2^(2m))) …` give the samples `M_g = D.matrix (x, g)` at the grid times
`g T/2^(2m)`. `q* = GateODEBudget.qOf s T η_H η_D (2g) (ε/2)` is the query shape and
`ℓ = log(1/ν)`.

**What was already released (cited, not redone).**

* Lemma `ode:lem:gate-select` with exact gates: `GateSelect.gate_select` (uniform sample bound
  `δ` with `4 T δ ≤ ε`, freezing `4 L_* T² ≤ ε 2^m`, the clock promise for the rescaled sample
  `((T - v_z)/τ) X_{z,r}` assumed), its model `GateSelect.runS`, `GateSelect.selE`,
  `GateSelect.branchPath`, the branch estimates `GateSelect.branch_block`,
  `GateSelect.branch_propagator`, `GateSelect.select_error`, the inverse
  `GateSelect.gate_select_inverse`, and the scalar clock witness `GateSelect.clock_scalar`.
* The solver on branch-dependent meshes: `GateSelect.ODE.solverB`,
  `GateSelect.ODE.native_ode_time_solverB` (the released native protocol, with the gates of
  `U_J`, a label- and slot-selected native private operation, its native identity and arithmetic,
  and the instance conditions `GateSelect.ODE.BInstanceOK` as hypotheses), the preparation
  certificate `GateSelect.ODE.prep_certificateB`, the permutation matrices
  `GateSelect.ODE.permMat_unitary`; the sufficient left-endpoint quadrature
  `GateQuad.LInstanceOK`, `GateQuad.solverL`, `GateQuad.native_time_outcomeL`.
* Binary data on the common mesh: `GateBinaryODETime.PubT` with `PubT.params`, `PubT.OK`,
  `PubT.UJg` (`GateBinaryODE.hadUJ4`), the time-indexed oracles `GateBinary.primsT` and the
  slot-selected primitives `GateBinary.slotPrim`, the transfer `GateBinaryODETime.nativeOK_slot2`;
  from the constant-coefficient library the four-sector Cayley action `GateBinaryODE.act4`, the
  compute circuit `GateBinaryODE.computeV4`, the decoder `GateBinaryODE.decO`, the arithmetic
  `GateBinaryODE.odeArith`, the decoder hypothesis `GateBinaryODE.DecOK`, the native identity
  `GateBinaryODE.nativeOK4`, the register programs of `GateEfficientBinary` on
  `GateBinaryODE.RO` with the multiplication chain `GateBinaryODE.chain`, and the lifts
  `GateBinary.qlift`, `GateBinaryODE.mLift`.
* The native and synthesis layers: `GateNative.hcirc` with `GateNative.hcirc_valid`,
  `GateNative.hcirc_nGates`, `GateNative.hcirc_error`, `GateNative.card_HW`, the protocol
  `GateNative.nprotocol`, `GateNative.NOutcome`, `GateNative.native_ode_time_gate_count`, the
  literal inverse `GateNative.ninv` with `GateNative.nrun_ninv`; `GateSynth.sprotocol`,
  `GateSynth.soutcome`, `GateSynthTrials.synthPrep`, `GateSynthTrials.synthPrep_approx`,
  `GateSynthTrials.native_trial_bounds10`, `GateSynthTrials.native_ode_time_solver_trials`.
* The budgets on the common mesh: `GateODEBudget.binary_ode_time_sizes` (`d ≤ 4096 q*`,
  `J ≤ 60 q* ℓ`, …, for `γ = GateODEBudget.gammaOf T η_H η_D (2g) (ε/2)`),
  `GateODEBudget.binary_ode_time_budget`, `GateODEBudget.binary_ode_time_budget_trials`,
  `GateBitBudget.bitB`, `GateBitBudget.HasBits`, `GateBitBudget.wordsT_le`,
  `GateBitBudget.binary_ode_time_budget_bits`, `GateBitBudget.binary_ode_time_budget_trials_bits`
  and the witnesses `GateBitBudget.withChoiceT`, `GateBitBudget.pointPubT`,
  `GateBitBudget.pointData`.
* The uniform clock `GateMesh.slotMesh` with `GateMesh.isMesh_slotMesh` and the slot estimate
  `GateMesh.slot_error_integral` for integral-sense propagators
  `IntegrablePathSimulation.Propagator.IsPropagator`, and
  `TimeDependentExtensions.integral_le_of_lipschitz'`.

**Lemma `ode:lem:gate-select` under the integrated certificate** (module `Certified`).

* `sampleErr Hp Dp k v X T m z = ∑_{r < 2^m} (u_z/2^m) ‖H(a_r) + k_z D(a_r) - X_{z,r}‖`,
  `a_r = v_z + r u_z/2^m`, `u_z = T - v_z`: the represented-sample error of label `z` integrated
  over `[v_z, T]` (at most `u_z δ` under a uniform bound `δ`, `sampleErr_le_of_uniform`).
* `gate_select_certified`: the hypotheses of the released `GateSelect.gate_select` with the
  uniform sample bound replaced by `sampleErr z ≤ ε/16` for every label and the freezing
  condition by `8 (βH + R βD) T² ≤ ε 2^m` (the condition `M ≥ 8 L_* T²/δ` of
  `ode:eq:gate-select-mesh`; the other three are replaced by the released subdivision condition
  `steps τ (ε/6) ≤ 2^m`). Guarantees: the released circuit `simCircuitT a τ Q q̄ (ε/2) m` with
  valid instructions, exactly `6d` private calls and `12d` calls of `U_J` or `U_J†`, at most
  `200 (d+1)(a+m+r+1)` elementary gates, `2a + 3m + 6r + 3 + |L|` wires,
  `d ≤ 128 (τ q̄ + Q (1 + log(6/ε)))`, `2d + 2 ≤ 2^r ≤ 4 (d+1)`; propagators of the branch paths
  exist, and for every family `U z` of them the circuit is within `ε` of
  `∑_z |z⟩⟨z| ⊗ U z (T - v_z)` on the clean-input space `selE`, with the full output compared.
* `gate_select_integral`: for any branch paths `h z` self-adjoint almost everywhere and
  interval integrable on `[0, u_z]`, integral-sense propagators `U z` and slot certificates
  `∑_r ∫_{slot r} ‖h z t - X_{z,r}‖ dt ≤ ε/2`, the same error bound, without a Lipschitz
  bound.
* Per branch: `slot_cert_le` (for a `β`-Lipschitz path the slot certificate is at most
  `β u²/(2 · 2^m)` plus the integrated sample error), `branch_slot_error`, `branch_error_cert`
  (one branch within `ε/2 + L_* u_z²/(2 · 2^m) + sampleErr z`).

**Lemma `ode:lem:gate-select` with native private calls** (module `SelectNative`).

* `native_gate_select`: the released circuit at accuracy `ε/4` with every instruction replaced
  by its native macro (`nativeSel a m τ Q q̄ ε UJg nd ar = GateNative.hcirc …`): `U_J` by its
  gates `UJg` (`GateOK 3`), every label- and slot-selected private call by `V† R V` for the
  compute circuit `V` of `nd` (public, selection wires the label and slot wires `selSW`) and the
  arithmetic `ar` (`ArithOK` at accuracy `ζ ≥ 0`). Hypotheses: unitary primitive oracles,
  `NativeOK` for the selected family `selFam D`, unitary `D z j` with the clock promises, the
  conditions of `gate_select_certified` at accuracy `ε/2` (`steps τ (ε/12) ≤ 2^m`,
  `16 L_* T² ≤ ε 2^m`, `sampleErr z ≤ ε/32`) and `48 d ζ ≤ ε`. Guarantees: valid instructions;
  exactly `12 d` times the primitive calls of `V` of every kind; at most
  `200 (d+1)(a+m+r+1) + 84 d |UJg| + 6 d (2 |V| + 2 |arith| + 2 bP + bT + 1)` elementary gates;
  `|S| + (2a + 3m + 6r + 3 + |L|) + (|Z| + bT + bP + A + 3)` qubits; the degree and register
  bounds; and error at most `ε` on the clean-input space `selN` (labels, payload, every
  simulator and work wire clear). The label register `L` is arbitrary here.
* `native_gate_select_inverse`: for a valid circuit `nativeSel …` (the first conclusion of
  `native_gate_select`), the literal inverse `GateNative.ninv (nativeSel …)` runs as the adjoint
  and has the same validity, gates and calls of every kind.

**Lemma `ode:lem:gate-select` from binary data** (modules `Address`, `Computed`, `Native`,
`Identity`, `Clock`, `SelectBinary`).

* Labels: the label wires `LabW m l` of the released solver (source sector, node word `u`, LCHS
  word `w`); `kOf q z = ν_w` (the LCHS node, `|k_z| ≤ R`, `kOf_abs_le`), `vOf q z = u' T/2^m`
  (`vOf_eq`, `vOf_mem`). The sample addresses of branch `z` are the grid points
  `v_z + j (T - v_z)/2^m = addrN · T/2^(2m)`, `addrN = 2^m u' + j (2^m - u') < 2^(2m)`
  (`addr_eq`, `addrN_lt`).
* The private operation `DOf q D en x z j = privFamB …`: the released four-sector Cayley action
  of the lifted grid sample at the address of slot `j` of branch `z`, at the LCHS node of `w` and
  the Cayley parameter `γ (2^m - u')/2^m` (the branch scale `u_z/T` times `γ`); the represented
  sample `XOf q D en x z j = H_g + k_z L_g`, the lifted Hamiltonian and dissipative parts of the
  grid sample (`HbB`, `LbB`).
* `binary_gate_select` (exact gates): for the public data `q` with `PubT.OK`, time-indexed
  binary data with the slot range and row and column energies at most `η_H²`, `η_D²` of every
  grid sample, Hermitian `βH`-, `βD`-Lipschitz paths `H`, `D` on `[0, T]`, `0 < δ ≤ 1`,
  `steps τ (δ/6) ≤ 2^m`, `8 (βH + R βD) T² ≤ δ 2^m` and `sampleErr z ≤ δ/16` for these samples:
  for the released circuit with the private operations `DOf`, valid instructions, exactly `6d`
  private calls and `12d` calls of `U_J` or `U_J†`, at most `200 (d+1)(a+m+r+1)` gates, the
  degree bound, the existence of the branch propagators and error at most `δ` on `selE` (the
  wire count and register bounds of `gate_select_certified` are not restated). Unitarity,
  self-adjointness, `‖X_{z,j}‖ ≤ λ_H + R λ_D` and the clock promises with the label-independent
  constants `Q = width(4s, γ)`, `q̄ = moment γ` for the rescaled samples are proved
  (`select_hyps`, `clockB`).
* `binary_native_gate_select` (native): the circuit `nativeSel` with the private operation
  `ndQ q` (the address program and the time-indexed compute circuit) and the arithmetic `arQ q`
  (the branch scale from the duration word `2^m - u'`), under the decoder `c₀ · gauss`,
  `steps τ (δ/12) ≤ 2^m`, `16 (βH + R βD) T² ≤ δ 2^m`, `sampleErr z ≤ δ/32` and `48 d ζ ≤ δ`:
  valid instructions; exactly `12 d` times `2 + 2 + 2` calls of the row-location, column-location
  and value oracles; at most `200 (d+1)(a+m+r+1) + G_sel` gates with
  `G_sel = 84 d (σ+3) + 6 d G_C`, `G_C = 2 (|apG| + 28 k_x + 2) + 2 |arith| + 2 bP + bT + 1`;
  `k_x + (2(k_x+3) + 3m + 6r + 3 + (1+m+l)) + A_sel` qubits with
  `A_sel = |ZA| + 6 k_x + 4 b + bT + bP + A_arith + 3`; the degree bound; error at most `δ` on
  `selN` for every family of propagators of the branch paths. The inverse:
  `native_gate_select_inverse` with these data.
* Equation `ode:eq:gate-select-gates`, arithmetic form: `select_gates_words`
  (`G_sel ≤ 393500 d (𝔴+1)³` and `A_sel ≤ 4096 (𝔴+1)³ + 3` for every `d`, `𝔴 = wordsB q` the
  register words, which contain the solver's reuse register `r` but no factor `d`) and
  `select_gates_bits` (`G_sel ≤ 11·10¹² d (𝔟+1)³`, `A_sel ≤ 2·10¹¹ (𝔟+1)³ + 3` under the
  bit-length hypotheses of the budget in `𝔟`). Here `|apG| ≤ 13 (2m+14)(m+5)` (`length_apG`,
  `card_apG_le`) and `|ZA| ≤ 897 (m+1)²` (`card_ZA`, `card_ZA_le`); `|arith|`, `bT`, `bP`,
  `A_arith` are those of the released arithmetic (`arQ_counts`).
* The construction: `addrOps` (module `Address`, a single-assignment program on words of width
  `2m + 14`: `2u'`, `-2u'` whose bits are the duration word, the multiplication chain with the
  slot digits, and `4 addrN`; `addrOK`, `v_md`, `md_word`, `n1_word`, `length_addrG`);
  `nativeOK_slotR` and `nativeOK_computed` (module `Computed`: primitive calls reading only the
  address part of the context, and selection by a computed context); `odeOpB`, `odeArB`,
  `inpB` (module `Native`); `decOK_B`, `nativeOK_B` (module `Identity`: the native identity of
  `privFamB` from `GateBinaryODE.nativeOK4` at every context word); `clockB` (module `Clock`).

**Equation `ode:eq:gate-select-gates` for the circuit itself** (module `SelectCost`).

* `binary_select_lemma_words`: at `δ = 4ν` the circuit of `binary_native_gate_select` has the
  degree `d = q.params.d` and the reuse register `q.params.r` of the solver, its subdivision
  condition is the released mesh condition and `48 d ζ ≤ 4ν` follows from `98304 q* ζ ≤ ν` with
  the public rescaling. Under `16 (βH + R βD) T² ≤ 4ν 2^m` and `sampleErr z ≤ ν/8`: exactly
  `12 d` times `2 + 2 + 2` oracle calls, at most `394300 (d+1)(𝔴+1)³` elementary gates (the
  released circuit and `G_sel` together) on at most `4200 (𝔴+1)³` qubits, `d ≤ 4096 q*`, and
  error at most `4ν` on `selN`.
* `binary_select_lemma_bits`: the same with at most `11·10¹² (d+1)(𝔟+1)³` gates and
  `2·10¹¹ (𝔟+1)³` qubits, under the bit-length hypotheses and `ζ ≥ ν/(196608 q*)` (with
  `98304 q* ζ ≤ ν`, an admissible interval of arithmetic accuracies).

**Theorem `ode:thm:gates`, time-dependent part, from binary data on branch-dependent meshes**
(modules `Pub`, `Solver`, `Synth`).

* Protocol: the released native protocol of `GateSelect.ODE.native_ode_time_solverB` with
  `U_J = q.UJg`, the private operation `ndQ q` and the arithmetic `arQ q`, so the native
  preparation `prepQ q loadC wpC` depends only on `q` and the valid loading and
  weight-preparation circuits `loadC`, `wpC`. `binary_select_counts`: valid trials, at most
  `prepGates + 84 d (σ+3) + 6 d G_C + |loadC| + 2 |wpC|` gates per preparation, at most `24 d`
  calls of each sampled-time oracle besides the source calls, in every history at most
  `80 g N + 40 g (4 (|W| + |XW| + |Zs| + k_x) + 3)` gates and `80 g` times the calls of the
  preparation, and the register `k_x + 2 (|W| + (|ZA| + 6 k_x + 4 b + bT + bP + A + 3) + |Zs|) +
  k_x + 1`. `binary_select_gate_count`: the explicit worst-case gate count.
* `RestB` (module `Pub`): the conditions of `GateSelect.ODE.BInstanceOK` other than the selection
  conditions, for the dyadic nodes and arbitrary weights `w_u ≥ 0`: unitary loading `Jl` of the
  normalised initial and forcing vectors (forcing labels of weight zero omitted), the
  weight-preparation matrix `Wp` with the amplitudes `√(‖z_s‖/B)`, a solution `x` of
  `x' = -G(u) x + b(u)` for an accretive `βG`-Lipschitz generator path within `δG` of the lifted
  grid samples at the branch addresses only (`G(addrN s r · T/2^(2m))` against `M̂` at the grid
  point `addrN s r`), homogeneous branch solutions `y_s` from the branch starts with the source
  vectors `w_u f_u`, the source certificate `‖x(T) - ∑_s y_s(T)‖ ≤ κ` (the first certificate of
  `ode:eq:gate-source-certificates`, a hypothesis as in the paper), `x(T) ≠ 0`,
  `B ≤ g ‖x(T)‖` and `κ + T (βG T/2^m + δG) B ≤ ε B/(2000 g)`. `RestL`: the same for the
  left-endpoint weights `T/2^m` with the certificate of `GateEfficientQuadrature` (`‖G‖ ≤ Λ`, an
  `L`-Lipschitz forcing, forcing samples `‖f_u‖ ≤ b_s` within `δb` of `b(u T/2^m)`, and the
  budget `(Λ b_s + L) T²/2^(m+1) + T δb + T (βG T/2^m + δG) B_m ≤ ε B_m/(2000 g)`), with the
  `n = 2^m` nodes of the released `GateQuad.LInstanceOK` (which allows any `n ≤ 2^m`).
  `instanceB`, `instanceL`: the released instance conditions from these, the energy bounds and
  the accretivity of every grid sample.
* `binary_select_solver`: for every input whose grid samples have row and column energies at
  most `η_H²`, `η_D²` and accretive dissipative parts, loading and weight-preparation circuits
  within `ζs` of `Jl`, `Wp`, `24 d ζ + 3 ζs ≤ ν` and `RestB`: `GateNative.NOutcome` (success
  probability at least `175/256 ≥ 2/3`, every successful trial within `ε/500` of `x(T)/‖x(T)‖`
  up to a global phase, conditional output within trace distance `ε`).
  `binary_select_solverL`: the same under `RestL`.
* Finite gate sets (`GateSynth.Synthesis 𝒢 Xa len`): `binary_select_solver_synth` (every trial
  synthesised at accuracy `ε/200`: valid gates of `𝒢`, the counts, and `GateSynth.SOutcome`,
  success at least `2/3` and conditional output within `ε`) with `binary_select_solverL_synth`
  (`SOutcome` under `RestL`); `binary_select_solver_trials` (only the preparation synthesised,
  at accuracy `ν/3`; with `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢` every gate is a gate of `𝒢`;
  the counts and `NOutcome`, the per-trial claim) with `binary_select_solverL_trials`
  (`NOutcome` under `RestL`); `native_time_trials_outcomeB` is the per-trial outcome for any
  native data.

**Equations `ode:eq:gate-main` and `ode:eq:gate-space`** (modules `Budget`, `BudgetBits`,
`BudgetTrials`), for the public rescaling `γ = GateODEBudget.gammaOf T η_H η_D (2g) (ε/2)`.

* `binary_select_budget`: at most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src
  + A]` gates (`G_src = |loadC| + 2 |wpC|`, `A = k_x + |Zs| + |ZA| + 6 k_x + 4 b + bT + bP +
  A_arith`), at most `7864320 g q*` calls of each sampled-time oracle besides `80 g` times the
  source calls, the register `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|ZA| + bT + bP + A_arith) +
  2 |Zs| + 47`, and `NOutcome` under `RestB` and `98304 q* ζ + 3 ζs ≤ ν`.
* `binary_select_budget_words`: at most `6·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` gates and
  `10000 (𝔴+1)³ + 2 |Zs|` qubits.
* `binary_select_budget_bits`: with `ζ ≥ ν/(196608 q*)`, `b ≤ b_data` and `c₀`, `T`, `η_H`,
  `η_D` of bit length `b_data` (`GateBitBudget.HasBits`), and
  `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε = b_data + log₂(N+1) + log₂(M+1) + log₂(2^m+1) +
  log₂((q* g + 1)/ε)`: at most `2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates and
  `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits, with `𝔴 + ℓ ≤ 300 (𝔟+1)` (`wordsB_le`).
* `binary_select_budget_trials` (in `q*` and the preparation bound `prepBoundB`, with
  `len ζ ≤ c₁ log(1/ζ) + c₀`) and `binary_select_budget_trials_bits` (in `𝔟`: at most
  `80 g (2·10¹⁸ q* (𝔟+1)³ + G_src)(c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
  40 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` and
  `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits): the synthesised protocol with the per-trial claim
  and `NOutcome`.

**Non-vacuity** (module `NonVacuity`).

* The integrated certificate is strictly weaker than the uniform bound: on the explicit data of
  `GateSelect.nv_all_hyps` with represented samples exact except at the first slot of every
  branch, where the error is `1/4`, every hypothesis of `gate_select_certified` holds at
  `ε = 1/2` (`nvc_sampleErr_le`: the integrated error is at most `1/64 ≤ ε/16`) and its
  conclusion follows (`nvc_select`), while for no `ε < 1` does a uniform bound `δ` with
  `4 T δ ≤ ε` exist (`nvc_not_uniform`), so the released `GateSelect.gate_select` does not apply.
* `nv_binary_gate_select`, `nv_binary_native_gate_select`: the public data
  `nvq = GateBitBudget.withChoiceT GateBitBudget.pointPubT` (`PubT.OK` with the coarsest
  admissible mesh, `nvq_m_pos`), the one-point time-indexed binary data `GateBitBudget.pointData`
  on the grid of `2^(2m)` points, the zero paths and `δ = 2ν` (exact gates), `δ = 4ν` (native,
  the budget `48 d ζ ≤ δ` by `nv_zeta`) satisfy every hypothesis of `binary_gate_select` and
  `binary_native_gate_select`, whose error bounds then hold; `nv_select_lemma`: for some
  `b_data` every hypothesis of `binary_select_lemma_words` and `binary_select_lemma_bits` holds
  for them, and the native selection circuit at `δ = 4ν` has at most `394300 (d+1)(𝔴+1)³`
  gates for the register words `𝔴` of the witness.
* `nv_restB`, `nv_instanceB`: for the same data, `x' = seedV` on `[0, 1]` with `x(0) = 0`, the
  zero generator path and the quadrature with the single node `T/2^m` of weight `1` (a forcing
  branch that starts off `0`), with the permutation matrix exchanging the zero word and the word
  of the forcing label as weight preparation, every condition of `RestB` holds, hence every
  condition of the released `GateSelect.ODE.BInstanceOK` for the private operations constructed
  from the binary data.
* `nvh_restB`, `nv_select_outcome`: for the homogeneous problem `x' = 0` with `x(0) = seedV`,
  zero weights and empty loading and weight-preparation circuits (the loading `1` and the
  identity weight preparation, `ζs = 0`), every antecedent of the guarantee of
  `binary_select_solver` holds, and the native protocol has the guarantees `NOutcome`;
  `nvh_restL`, `nv_select_outcomeL`: the same for `binary_select_solverL`, with the
  left-endpoint weights and zero forcing samples.
* `select_all_hyps`: the same public data and binary data with empty circuits satisfy every
  hypothesis of `binary_select_budget_bits` for some `b_data`, and its gate bound holds.
* The witnesses of the binary-data statements have zero generator data, so their energy bounds
  and sample errors are trivial; their clock promises and native identities are given by the
  general `clockB` and `nativeOK_B`, and the address program and the label-dependent Cayley
  parameter are exercised only by the general proofs (`addr_eq`, `clockB`, `nativeOK_B`).

**Proof map.**

* `Certified`: `slot_cert_le` (`TimeDependentExtensions.integral_le_of_lipschitz'` on the slots
  of `GateMesh.slotMesh`), `branch_slot_error` (the released `GateSelect.branch_block`),
  `branch_error_cert` (`GateMesh.slot_error_integral`), `gate_select_certified` (the released
  `GateSelect.select_error` and `GateCircuit.SlotSim.simCircuitT_public`),
  `gate_select_integral` (`GateSelect.select_error` and `GateMesh.slot_error_integral`).
* `SelectNative`: `selRel`, `selSW`, `embW`, `selFam`, `prodOps_evalSel_embW` (the selected
  native semantics of the embedded simulator is `GateSelect.runS`), `hcirc_error_gen` (the
  released `GateNative.hcirc_error` on an isometric embedding of a direct sum), `nativeSel`,
  `selN`, `native_gate_select`, `native_gate_select_inverse`.
* `Address`: the address program and its values; `Computed`: the two transfers of `NativeOK`;
  `Native`: the native data; `Identity`: `decOK_B`, `startW`, `addrN`, `privFamB`,
  `nativeOK_B`; `Clock`: `HbB`, `LbB`, `gensB_eq`, `startB_vQ`, `durB_vQ`, `addrB_vQ`, `clockB`.
* `SelectBinary`: `kOf`, `vOf`, `DOf`, `XOf`, `select_hyps`, `binary_gate_select`,
  `binary_native_gate_select` (from `gate_select_certified` and `native_gate_select`).
  `SelectCost`: `binary_select_lemma_words`, `binary_select_lemma_bits` (from
  `binary_native_gate_select`, `select_gates_words`, `wordsB_le` and
  `GateODEBudget.binary_ode_time_sizes`).
* `Pub`: `layQ`, `kapQ`, `ndQ`, `arQ`, `prepQ`, `arQ_ok`, `nativeOKQ`, `selectB`, `RestB`,
  `sampleG_addr`, `instanceB`, `RestL`, `instanceL`. `Solver`: `binary_select_counts`,
  `binary_select_solver`, `binary_select_solverL` (from the released
  `GateSelect.ODE.native_ode_time_solverB` and `GateQuad.native_time_outcomeL`),
  `binary_select_gate_count` (`GateNative.native_ode_time_gate_count`). `Synth`:
  `native_time_trials_outcomeB` (the released `GateSelect.ODE.prep_certificateB` with
  `GateSynthTrials.synthPrep_approx` and `GateSynthTrials.native_trial_bounds10`) and the four
  finite-gate-set solvers.
* `Budget`: `card_ZA_le`, `card_apG_le`, `wordsB`, `binary_select_arith_words`,
  `select_gates_words`, `binary_select_budget` (`GateODEBudget.binary_ode_time_sizes`),
  `words_gate_arithB`, `binary_select_budget_words`. `BudgetBits`: `wordsB_le`,
  `select_gates_bits`, `binary_select_budget_bits`. `BudgetTrials`: `prepBoundB`,
  `binary_select_budget_trials`, `prepBoundB_le`, `log_factorB_le`, `testedB_le`,
  `binary_select_budget_trials_bits`.

**Formalisation choices.**

* The branch step `u_z/M` is carried by the private operation, as in the released
  `GateEfficientSelect`: the Cayley parameter of the private operation of branch `z` is
  `γ (2^m - u')/2^m`, computed by the released angle arithmetic from the duration word
  `2^m - u'`, so that the private operation carries the clock promise for the rescaled sample
  `((T - v_z)/τ) X_{z,r}` with the label-independent constants `Q = width(4s, γ)` and
  `q̄ = moment γ`. The boundary rotations, the circuit and all its counts are those of the
  released simulator and do not depend on the label; this is the route of the released
  constant-coefficient solver from binary data, and it replaces the label-dependent boundary
  rotations `R(c_z^M)`, `B_in(c_z^{2^j})`, `B_out(c_z^{2^j})` of the proof.
* The source mesh is the power-of-two mesh of the proof with `2^m` nodes `u T/2^m`, the same
  `m` as the slot exponent of every branch (the source label of the released protocol has `m`
  bits): a quadrature with nodes on a coarser dyadic mesh uses zero weights, and one with more
  nodes needs a larger `m`, which refines every branch and keeps the mesh conditions. The
  address `2^m u' + r (2^m - u')` and the duration word are computed by one single-assignment
  register program on words of `2m + 14` bits with at most `13 (2m+14)(m+5)` gates; there is no
  source-time table. The decoder scale `κ = γ √(4s) c₀/(2^(m+F+10) ρ)` of the branch operation
  carries the factor `2^(-m)` of the duration word, which costs `m` further bits of `𝔟`.
* The binary-data lemma is stated for the label wires of the dissipative solver (source sector,
  node word and LCHS word), whose frequencies and start times are computed by the released
  LCHS arithmetic and the address program; the generic native lemma `native_gate_select` covers
  any label register, with the native identity of the private operations as a hypothesis.
* Error budgets. Exact gates: `ε/2` for the released circuit, `ε/16` for freezing
  (`L_* u_z²/(2M) ≤ ε/16` from `M ≥ 8 L_* T²/ε`) and `ε/16` for the integrated sample error, as
  in the proof (`δ/16` each); the released degree and subdivision condition replace the schedule
  `ode:eq:gate-select-schedule` and the conditions `M ≥ 2, 4 α T, 2 (α T)^{3/2}/√δ`. Native:
  `ε/2` for the exact-gate lemma at accuracy `ε/2` (hence `ε/32` for the certificate and
  `16 L_* T² ≤ ε M`) and `ε/2` for the `6 d` private calls at `4 ζ` each (`48 d ζ ≤ ε`).
* The integrated sample error of `gate_select_certified` is the slot-weighted sum of the errors
  at the sample addresses; `gate_select_integral` takes the integrals of the path errors over the
  slots instead, for integrable paths without a Lipschitz bound. For binary data the
  represented samples are the lifted grid samples `H_g + k_z L_g` themselves.
* `G_sel` and `A_sel` are the gates and work wires that the native selection circuit adds to the
  released simulator (`select_gates_words`, `select_gates_bits`); the bounds for the whole circuit
  are `binary_select_lemma_words` and `binary_select_lemma_bits`, stated at `δ = 4ν`, where the
  reuse register is that of the solver (one of the register words) and the degree is the
  solver's `d ≤ 4096 q*`, which enters as the factor `d + 1`.
* The binary-data solvers keep the instance format of the released
  `GateSelect.ODE.BInstanceOK`: the generator path is compared with the lifted samples at the
  branch addresses by a uniform bound `δG` (field `sampleG` of `RestB`, `RestL`), with the
  discretisation term `T (βG T/2^m + δG) B` of the released budget; the integrated sample-error
  certificate is proved for the lemma (the Hamiltonian selection), not for the generator samples
  of the dissipative solvers. The row and column energy bounds and the accretivity are required
  of every grid sample, the promise on the time-indexed data as in the released binary-data
  solvers, although only the samples at the branch addresses are read. The source certificate
  is a hypothesis for general weights and proved for the left-endpoint weights, and the loading
  and weight-preparation circuits are hypotheses with their accuracy `ζs`.
* `𝔟` is the released `GateBitBudget.bitB` with `M = 2^m` time slots and `2^m` source nodes, so
  `log(m+1)` of `ode:eq:gate-word-budget` is `log₂(2^m+1) = log₂(M+1)`; the absolute
  constants of `ode:eq:gate-main` and `ode:eq:gate-space` are explicit.

**Not formalised.**

* Source nodes other than the dyadic nodes `u T/2^m` (for example nodes computed by other
  coherent arithmetic, with their time-address rounding in the represented-sample error, as the
  proof allows), and a number of nodes independent of the number `2^m` of slots per branch
  without refining the branches.
* The label-dependent boundary rotations of the proof with their coherent arithmetic (repeated
  squaring of `c_z`, the Hölder bound `‖R(x) - R(y)‖ ≤ C √|x - y|`, disabling the branch
  `u_z = 0`): the rescaled private operations replace them.
* An integrated sample-error certificate for the generator samples of the dissipative solvers
  (they keep the uniform bound `δG` of the released instance conditions), and energy bounds
  required only at the branch addresses.
* Bounds on the whole native selection circuit from binary data at accuracies other than
  `δ = 4ν` (for other `δ` the degree and the reuse register are not those of the solver, and
  only the arithmetic forms `select_gates_words`, `select_gates_bits` of `G_sel` and `A_sel` with
  a free degree are stated).
* The error of the inverse circuit (its counts and its semantics as the adjoint are proved, for
  the native circuit in `native_gate_select_inverse` and with exact gates in the released
  `GateSelect.gate_select_inverse`).
* The construction of the loading and weight-preparation circuits, which remain hypotheses as in
  the released solvers; non-binary entry decoding (the generic `native_gate_select` assumes the
  native identity); lower bounds.

**Provenance.** New library, written against the released package: it imports
`GateEfficientSelect`, `GateEfficientQuadrature`, `GateEfficientMesh`,
`GateEfficientBinaryODETime`, `GateEfficientBinaryODE`, `GateEfficientBinary`,
`GateEfficientHamiltonian`, `GateEfficientNative`, `GateEfficientSynthesis`,
`GateEfficientSynthesisTrials`, `GateEfficientODEBudget` and `GateEfficientBitBudget` (with their
dependencies) and changes none of them. The statement guides of `GateEfficientSelect` (the
arithmetic part of the lemma, integrated sample-error certificates, finite-gate-set synthesis
of the branch-dependent solver), `GateEfficientQuadrature` (the binary-data and finite-gate-set
solvers on branch-dependent meshes and the arithmetic of the lemma) and `GateEfficientMesh` (the
branch-dependent meshes of the binary-data solvers) list these items as not formalised; they are
formalised here in the form stated above, except for the label-dependent boundary rotations,
non-dyadic source nodes and integrated certificates for the generator samples of the solvers.
-/
