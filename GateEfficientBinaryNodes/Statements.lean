import GateEfficientBinaryNodes.NonVacuity

/-!
# Constant-forcing source preparation, integrated generator-sample certificates and computed
source nodes for Theorem `ode:thm:gates`: paper-to-Lean entry point

Theorem `ode:thm:gates` of the accompanying paper (gate-efficient dissipative equations) solves the
time-dependent dissipative problem from a positive source quadrature, whose "nodes `v_i` and weights
`w_i ≥ 0`" satisfy the certificates eq. `ode:eq:gate-source-certificates` and whose "nodes can be
computed coherently from their labels at polynomial cost". Its proof uses the branch-dependent
meshes of Lemma `ode:lem:gate-select`, whose represented samples "must satisfy the common moment
bounds" at the addresses `v_z + r u_z/M` read by a branch, with "certified total operator-norm
error, integrated over the selected interval, … at most `δ/16`", and "for other efficiently computed
nodes, any time-address rounding is included in the stated represented-sample error". For constant
forcing the proof prepares the sources with "one rotation between the initial and forcing sectors
and `log₂ m` Hadamard gates, and the forcing state is loaded by the same controlled circuit on every
forcing label", so that `G_src(ν) = G_{x₀}(cν) + G_b(cν) + poly(b_data, log(m+1), log(1/ν))`
(equation `ode:eq:gate-constant-source`).

The released libraries formalise the time-dependent part of the theorem from time-indexed binary
data on the branch-dependent meshes with the `2^m` dyadic nodes `u T/2^m` only, with a uniform
bound `δG` on every represented generator sample at the branch addresses and the energy bounds
of every grid sample (`GateEfficientBinarySelect`), and for the time-dependent solvers they take
the loading and weight-preparation circuits of the sources as hypotheses; the constant-coefficient
solver already prepares its sources with one rotation and Hadamard gates
(`GateODE.Params.srcPrep`, in its own source format). This library proves:

* **the integrated sample-error certificate** for the generator samples of the solvers on
  branch-dependent meshes, for any native data (`native_time_outcomeBI`,
  `native_ode_time_solverBI`, `native_time_trials_outcomeBI`, `BInstanceOKI`, `LInstanceOKI`)
  and from time-indexed binary data with the energy bounds and the accretivity required only of
  the samples the branches read (`binary_select_solverI`, `binary_select_solverLI`, their
  finite-gate-set forms `…_synth`, `…_trials`); a uniform bound `δG` gives the certificate with
  `δI = T δG` and the released budget (`BInstanceOK.toI`, `sampleErrQ_le_of_uniform`);
* **the source preparation for constant forcing** (equation `ode:eq:gate-constant-source`) for
  the time-dependent solvers: the weight preparation is constructed (`wpConst`, one rotation and
  `m` Hadamard gates controlled by the sector wire) and the loading is the two supplied
  controlled loading circuits, the same on every forcing label (`loadConst`), with
  `G_src = |srcC false| + |srcC true| + 2 (m+1)` (`const_source_counts`), for the released
  common-mesh solver (`binary_ode_time_solver_const`, `binary_ode_time_solver_const_synth`) and
  for the solver on branch-dependent meshes with the integrated certificate
  (`binary_select_solverLI_const`, `…_synth`, `…_trials`), with the counts
  (`binary_ode_time_const_counts`, `binary_select_const_counts`);
* **Theorem `ode:thm:gates` with coherently computed source nodes**: the nodes
  `v_u = word u · T/2^μ` of any node program (classical reversible gates computing `μ`-bit node
  words from the labels, `NodeProg.OK`, its gates counted), the time addresses computed
  coherently from the node words (`addrGN`), the samples read on a data grid of `2^nd ≤ 2^(μ+m)`
  points with the time-address rounding charged to the integrated represented-sample error
  (`sampleErrNQ`), natively (`binary_nodes_solver`, `binary_nodes_counts`,
  `binary_nodes_gate_count`), over a finite gate set as a partial formalisation, under this
  package's format hypotheses, of the finite-set statement of Theorem `ode:thm:gates`
  (`binary_nodes_solver_synth`, `binary_nodes_solver_trials`, with `binary_nodes_synth_counts`,
  `binary_nodes_trials_counts`), and equations `ode:eq:gate-main` and `ode:eq:gate-space` in the
  query shape `q*`, in the register words and in `𝔟` (`binary_nodes_budget`,
  `binary_nodes_budget_words`, `binary_nodes_budget_bits`), also over a finite gate set (partial
  formalisation, under this package's format hypotheses, of the same finite-set statement) with
  the per-trial claim
  (`binary_nodes_budget_trials`, `binary_nodes_budget_trials_bits`).

No result from another paper is used. The released libraries are unchanged. References to the
manuscript use its labels. Every theorem of the library is axiom-audited in
`GateEfficientBinaryNodes/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateBinaryNodes` and are named relative to it below. Released declarations are
named relative to `SparseHamiltonian` (for example `GateSelect.ODE.BInstanceOK`,
`GateBinaryODETime.PubT`, `GateBinarySelect.prepQ`).

**Notation.** The public data are `q : GateBinaryODETime.PubT` with the released parameters
`q.params` and conditions `PubT.OK` (system qubits `k_x`, slot bits `σ`, stored bits `b`,
decoder scale `c₀`, energy bounds `η_H`, `η_D`, Cayley rescaling `γ`, time `T`, amplification
bound `g`, accuracy `ε`, mesh bits `m`, arithmetic accuracy `ζ`; `ν = ε/(40000 g)`, degree `d`,
reuse register `r`). `M = 2^m` is the number of slots of every branch and the number of node
labels: the source label `(ini, u)` of the released protocol carries the sector bit `ini` and an
`m`-bit node index `u`; the branch of `(true, u)` starts at the node `v_u`, that of an initial
label at `0`, and `u_s = T - v_s` is its duration. `B = ‖x₀‖ + ∑_u w_u ‖f_u‖` is the source mass,
`q* = GateODEBudget.qOf s T η_H η_D (2g) (ε/2)` the query shape, `ℓ = log(1/ν)`, and
`𝔟 = GateBitBudget.bitB b_data (2^k_x) (2^m) (2^m) q* g ε` the word budget of
`ode:eq:gate-word-budget`.

**What was already released (cited, not redone).**

* The solver on branch-dependent meshes: `GateSelect.ODE.native_ode_time_solverB`,
  `GateSelect.ODE.prep_certificateB`, `GateSelect.ODE.target_factsB`,
  `GateSelect.ODE.BInstanceOK`, the source format `GateSelect.ODE.bsW`,
  `GateODE.Time.TParams.srcAmp`, `GateODE.Time.TParams.zsrc`; the left-endpoint quadrature
  `GateQuad.vQ`, `GateQuad.wQ`, `GateQuad.LInstanceOK`, `GateQuad.native_time_outcomeL` and its
  source certificate, the sufficient node counts `GateQuad.nodes_sufficient`,
  `GateQuad.exists_pow_two_nodes`, `GateQuad.paper_quadrature`, `GateQuad.budget_disc_paper`.
* The constant-coefficient source preparation `GateODE.Params.srcPrep` (one rotation and
  uncontrolled Hadamard gates on `2^k` left-endpoint nodes, every label `(false, w)` of the
  initial sector of duration `T`) and the count of the loading circuits of
  `GateBinaryODE.binary_ode_solver`.
* The binary-data solvers: `GateBinaryODETime.binary_ode_time_solver` (common mesh, uniform
  `δG`), `GateBinarySelect.binary_select_solver`, `binary_select_solverL`, their counts and
  finite-gate-set forms, the native data `GateBinarySelect.ndQ`, `arQ`, `prepQ`, the address
  program `GateBinarySelect.addrOps`, the transfers `GateBinarySelect.nativeOK_slotR`,
  `nativeOK_computed`, the released four-sector Cayley action, compute circuit, decoder and
  arithmetic of `GateBinaryODE`, and the register programs of `GateEfficientBinary`.
* The native and synthesis layers: `GateNative.nprotocol`, `GateNative.NOutcome`,
  `GateNative.native_ode_time_gate_count`, `GateNative.srcIdeal`, `GateNative.loadIdeal`;
  `GateSynth.sprotocol`, `GateSynth.soutcome`, `GateSynthTrials.synthPrep`,
  `GateSynthTrials.native_ode_time_solver_trials`, `GateSynthTrials.native_trial_bounds10`.
* The budgets: `GateODEBudget.binary_ode_time_sizes`, `GateODEBudget.arith_words`,
  `GateBitBudget.kap_words` and the word lemmas of `GateEfficientBitBudget`,
  `GateBinarySelect.binary_select_budget_bits`, `GateBinarySelect.binary_select_budget_trials_bits`.
* The one-step estimate `TimeDependentODE.step_error` and the target budget
  `TimeDependentODE.Sampling.target_budget`.

**The integrated certificate** (modules `Core`, `Integrated`, `SelectIntegrated`).

* `Core`: the released chain on branch-dependent meshes with the three target facts of
  `GateSelect.ODE.target_factsB` as hypotheses (`BCore`, `TFacts`, `target_facts_of_error`,
  `prep_certificateC`, `native_time_outcomeC`, `native_time_trials_outcomeC`).
* `sampleErrB p v Hb Lb G s = (u_s/2^m) ∑_{r < 2^m} ‖G(v_s + r u_s/2^m) - (L + i H)_{s,r}‖`:
  the represented-sample error of the branch of `s`, integrated over `[v_s, T]`
  (`sampleErrB_le_of_uniform`: at most `T δG` under a uniform bound). `homog_discI`,
  `branch_discI`: a branch is within `(βG u_s²/2^m + sampleErrB s) ‖z_s‖` of its homogeneous
  solution (the released one-step estimate, slot by slot); `target_errorBI`: the exact target is
  within `κ + (βG T²/2^m + δI) B` of `x(T)`.
* `BInstanceOKI`: the conditions of `GateSelect.ODE.BInstanceOK` with the uniform sample bound
  replaced by `sampleErrB s ≤ δI` for every branch and the budget by
  `κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`; `BInstanceOK.toI`: every released instance is one with
  `δI = T δG` and the same budget. `native_time_outcomeBI`, `native_ode_time_solverBI` (the
  released counts with the guarantee), `native_time_trials_outcomeBI`: the guarantees `NOutcome`
  of the released native protocol and of the protocol on the synthesised preparation for every
  such instance. `LInstanceOKI`, `LInstanceOKI.toBI`: the left-endpoint quadrature.
* From binary data on the grid of `2^(2m)` points (`SelectIntegrated`): `SampleOK D x η_H η_D g`
  collects the row and column energy bounds and the accretivity of the sample at the grid point
  `g`; `selectBA` derives the selection conditions (unitarity, clock promises with the
  label-independent constants, `‖H‖ ≤ λ_H`, `‖L‖ ≤ λ_D`, `L ≥ 0`) from `SampleOK` at the branch
  addresses `addrF s r` only; `sampleErrQ` is the integrated error at these addresses
  (`sampleErrB_Q`); `RestBI`, `RestLI` are the released `RestB`, `RestL` with the integrated
  certificate. `binary_select_solverI`, `binary_select_solverLI`: the released protocol
  `GateBinarySelect.prepQ q loadC wpC` has the guarantees `NOutcome`;
  `binary_select_solverI_synth`, `binary_select_solverLI_synth` (`GateSynth.SOutcome`),
  `binary_select_solverI_trials`, `binary_select_solverLI_trials` (`NOutcome` with the
  synthesised preparation). The protocols and counts are the released ones.

**Constant forcing** (modules `Const`, `ConstSolver`).

* `wpGates m r₀ r_b T`: the rotation `rotC √(r₀/B) √(T r_b/B)` on the sector wire and the Hadamard
  gate on each of the `m` node wires controlled by the sector wire, `B = srcB r₀ r_b T = r₀ + T r_b`
  (`length_wpGates`: `m + 1` gates; `wpGates_ok`); `WpConst` its matrix (`WpConst_unitary`,
  `WpConst_col`), whose first column is the released weight promise for `r₀ = ‖x₀‖`, `r_b = ‖b‖`
  and the forcing samples `b` on all `2^m` nodes with the weights `T/2^m` (`WpConst_srcAmp`,
  `mass_const`: `B_m = B`). `wpConst`: the circuit on the weight-preparation register
  (`nrun_wpConst`: exact; `wpConst_counts`: `m + 1` gates, no call).
* `loadConst srcC`: the supplied loading circuits `srcC false` (initial state) and `srcC true`
  (forcing state), each controlled by the sector wire (`GateNative.srcIdeal`), placed on the
  source-label register; `loadConst_approx`: within `ζ₀ + ζ₁` of the selected loading with the
  same loading on every forcing label (`JlC`); `const_source_counts`:
  `|loadC| + 2 |wpC| = |srcC false| + |srcC true| + 2 (m + 1)` and the calls of the two supplied
  circuits.
* `RestConst` (common mesh: the released `PubT.Rest` for constant forcing with norms `r₀`, `r_b`);
  `binary_ode_time_const_counts`, `binary_ode_time_solver_const`,
  `binary_ode_time_solver_const_synth`: the released common-mesh protocol with these source
  circuits, `G_src = |srcC false| + |srcC true| + 2 (m+1)` in its worst-case gate count, and the
  guarantees under `24 d ζ + 3 (ζ₀ + ζ₁) ≤ ν`.
* `RestLIConst` (branch-dependent meshes, left-endpoint weights, integrated certificate, source
  certificate `Λ r_b T²/2^(m+1)` for `‖G‖ ≤ Λ`), `RestLIConst.toLI`; `binary_select_const_counts`,
  `binary_select_solverLI_const`, `binary_select_solverLI_const_synth`,
  `binary_select_solverLI_const_trials`.

**Computed source nodes** (modules `NodeAddr`, `NodeNative`, `NodeIdentity`, `NodeClock`,
`NodePub`, `NodeSolver`).

* `NodeProg m μ Zn` (gates on the `m` node-index wires, the node register of `μ` wires and a
  scratch `Zn`, and the node words `word u`), `NodeProg.OK`: proper gates with at most three
  controls writing `word u` into the clean node register and returning the scratch clean. The
  nodes are `vN p μ N u = word u · T/2^μ` (`vN_mem`).
* `addrGN` (module `NodeAddr`): one single-assignment register program on words of `μ + m + 14`
  bits computing the address `A = 2^m ν' + r (2^μ - ν') < 2^(μ+m)` of slot `r` of the branch of a
  label with start word `ν' = (ini ? word u : 0)` and the duration word `2^μ - ν'`
  (`addrOKN`, `mdN_word`, `n1N_word`, `n1N_dv`; at most `13 (μ + m + 14)(m + 5)` gates,
  `length_addrGN`, `card_addrGT_le`: at most `910 (μ + m + 1)²`).
* `odeOpN`, `odeArN` (module `NodeNative`): the node program, the address program, the released
  compute circuit with every primitive call reading the top `nd` bits of the address
  (`addrBitN`), and the released arithmetic with `μ` duration bits; `odeOpN_public`,
  `odeOpN_nGates` (`|N| + |addrGT| + 28 k + 2` gates), `odeOpN_nCalls` (two calls of each oracle),
  `odeArN_ok`, `apGN_run` (the programs XOR the node word and the register file into the clean
  scratch).
* `privFamN` (module `NodeIdentity`): the label- and slot-selected private family, the released
  four-sector Cayley action of the lifted sample at the data grid point
  `addrFN s r = ⌊A / 2^(μ+m-nd)⌋` with the Cayley parameter `γ (2^μ - ν')/2^μ`;
  `nativeOK_N`: its native identity; `decOK_N`: the decoder hypothesis at every context word.
* Module `NodeClock`: `startB_vN`, `durB_vN`, `addrB_vN` (the branch geometry of
  `GateSelect.ODE` on the computed nodes: start `ν' T/2^μ`, duration `(2^μ - ν') T/2^μ`,
  addresses `A T/2^(μ+m)`), `HbN`, `LbN`, `gensN_eq` (the represented slot generator is the
  lifted sample at `addrFN`), `clockN` (the clock promises from `SampleOK` at the read sample).
* Module `NodePub`: the native data `ndQN`, `arQN`, `prepQN q μ nd N loadC wpC` (depending only on
  the public data, the node program and the source circuits), `nativeOKQN`, `selectN`,
  `sampleErrNQ` (the integrated error of the lifted samples at the rounded grid points against
  the generator path at the exact addresses, slot length `(2^μ - ν') T/2^(μ+m)`,
  `sampleErrB_NQ`), `RestN` (positive quadrature with the computed nodes and arbitrary weights
  `w_u ≥ 0`, loading, weight preparation, path, integrated certificate `sampleErrNQ s ≤ δI`,
  branch solutions, source certificate `κ`, budget `κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`),
  `instanceN`: `BInstanceOKI` from `SampleOK` at the read samples and `RestN`.
* Module `NodeSolver`: `binary_nodes_counts` (valid trials; at most
  `prepGates + 84 d (σ+3) + 6 d G_C + |loadC| + 2 |wpC|` gates per preparation with
  `G_C = 2 (|N| + |addrGT| + 28 k + 2) + 2 |arith| + 2 bP + bT + 1`; at most `24 d` calls of each
  sampled-time oracle besides the source calls; the worst-case protocol counts and the register
  `k + 2 (|W| + (|Z_N| + 6k + 4b + bT + bP + A + 3) + |Zs|) + k + 1`,
  `|Z_N| = μ + |Zn| + 1 + 2 (μ+m+14) + (4m+62)(μ+m+14)`), `binary_nodes_gate_count` (at most
  `18000 g [(d+1)(a + m + r + 1 + C_J + G_C) + (J+2)(l+1) + G_src + A]` gates),
  `binary_nodes_solver` (`NOutcome` for every input with `SampleOK` at the read samples, source
  circuits within `ζs` of `Jl`, `Wp`, `24 d ζ + 3 ζs ≤ ν` and `RestN`), `binary_nodes_synth_counts`
  with `binary_nodes_solver_synth` (every trial synthesised: valid gates of `𝒢`, counts,
  `SOutcome`), `binary_nodes_trials_counts` with `binary_nodes_solver_trials` (the preparation
  synthesised, every gate in `𝒢` under `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, counts, `NOutcome`
  with the per-trial claim).

**Equations `ode:eq:gate-main` and `ode:eq:gate-space` for computed nodes** (modules
`NodeBudget`, `NodeBits`), with the public rescaling
`γ = GateODEBudget.gammaOf T η_H η_D (2g) (ε/2)`.

* `binary_nodes_budget`: at most `73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]`
  gates, at most `7864320 g q*` calls of each sampled-time oracle besides `80 g` times the source
  calls, the register `22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (|Z_N| + bT + bP + A) + 2 |Zs| + 47`;
  `binary_nodes_budget_solver`: `NOutcome` under `RestN` and `98304 q* ζ + 3 ζs ≤ ν`.
* `wordsN q μ` (the released register words with the node precision `μ` and the decoder scale
  `kapQN` with `2^(μ+F+10)`), `binary_nodes_arith_words` (per-call gates without the node program
  at most `65536 (𝔴+1)³`, added wires without the node scratch at most `4096 (𝔴+1)³`),
  `binary_nodes_budget_words`: at most `6·10¹² g [q* ((𝔴 + ℓ + 1)³ + |N|) + G_src + |Zs| + |Zn|]`
  gates and `10000 (𝔴+1)³ + 2 |Zs| + 2 |Zn|` qubits.
* `bitN b_data q μ = 𝔟 + μ`, `wordsN_le` (`𝔴 + ℓ ≤ 300 (𝔟 + μ + 1)` under `ζ ≥ ν/(196608 q*)`,
  `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`), `binary_nodes_budget_bits`:
  at most `2·10²⁰ g [q* ((𝔟+μ+1)³ + |N|) + G_src + |Zs| + |Zn|]` gates and
  `3·10¹¹ (𝔟+μ+1)³ + 2 |Zs| + 2 |Zn|` qubits.
* Over a finite gate set: `prepBoundN` (`B = 819400 q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) +
  G_src`), `binary_nodes_budget_trials` (validity and gate-set membership, `N_P ≤ B`, at most
  `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates of `𝒢`, the calls, the register
  `44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (|Z_N| + bT + bP + A) + 4 |Zs| + 2 |Xa| + 95`),
  `binary_nodes_budget_solver_trials` (`NOutcome` under `98304 q* ζ + 3 ζs ≤ ν`),
  `prepBoundN_le` (`B ≤ 2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) + G_src`), `log_factorN_le`
  (`log((B+1)/(ν/3)) ≤ 64 (𝔟+μ+1) + log(G_src+1) + log(|N|+1)`), `testedN_le`,
  `binary_nodes_budget_trials_bits` (at most
  `80 g (2·10¹⁸ q* ((𝔟+μ+1)³ + |N|) + G_src)(c₁ (64 (𝔟+μ+1) + log(G_src+1) + log(|N|+1)) + c₀) +
  40 g (4 (3·10¹¹ (𝔟+μ+1)³ + 2 |Zn| + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` and
  `7·10¹¹ (𝔟+μ+1)³ + 4 |Zn| + 4 |Zs| + 2 |Xa|` qubits).

**Non-vacuity** (module `NonVacuity`).

* Node programs: `copyProg m` (`m` CNOT gates, `copyProg_length`; node words `u`, `copyProg_ok`)
  computes the released dyadic nodes (`vN_copy : vN p m (copyProg m) = GateQuad.vQ p M`);
  `midProg m` (a NOT gate and `m` CNOT gates, `midProg_length`; node words `2u + 1` of `m + 1`
  bits, `midProg_ok`) computes the midpoints (`vN_mid`: `(2u + 1) T/2^(m+1)`).
* `sampleErrNQ_le_of_uniform`: a uniform bound `δG` at the read samples gives
  `sampleErrNQ s ≤ T δG`. No explicit data are given on which the integrated certificate of
  the solvers holds and no admissible uniform bound does; for the certificate of Lemma
  `ode:lem:gate-select` on `H + k D` this is the released `GateBinarySelect.nvc_not_uniform`.
* `nvh_restN`, `nv_nodes_outcome`: for the public data `GateBinarySelect.nvq` (`PubT.OK` with the
  coarsest admissible mesh), the one-point data on the grid of `2^(2m)` points and every node
  program with `μ ≥ m` and `NodeProg.OK`, the homogeneous witness satisfies `RestN`, every
  hypothesis of `binary_nodes_solver` holds with empty source circuits, and the native protocol
  has the guarantees `NOutcome`; `nv_copy_outcome`, `nv_mid_outcome` for the two programs
  (for the midpoint program the data grid is coarser than the address grid, so the addresses are
  rounded). `nvMF_restN`, `nvMF_node`, `nvMF_instanceN`: the forcing witness of the released
  `GateBinarySelect.nv_restB` with its forcing node at the midpoint `3T/2^(m+1)` satisfies
  `RestN`, and hence `BInstanceOKI` with the clock promises proved.
* `nodes_all_hyps`: the same public and binary data, the copy program and empty source circuits
  satisfy every hypothesis of `binary_nodes_budget_bits` for some `b_data`, and its gate bound
  holds.
* Constant forcing: `nvc_restLIConst`, `nv_const_outcome` (`x' = seedV`, `x(0) = 0`, `r₀ = 0`,
  `r_b = 1`, the zero path, empty supplied loading circuits: every hypothesis of
  `binary_select_solverLI_const` holds and the protocol with the constructed `wpConst` has the
  guarantees `NOutcome`); `nvc_restConst`, `nv_const_common_outcome` (the common-mesh solver
  `binary_ode_time_solver_const` with `x(0) = seedV`, `b = 0`, `r₀ = 1`, `r_b = 0`; a nonzero
  forcing would need a mesh finer than the coarsest admissible one of `nvq`, because the
  released common-mesh budget contains `T (T/2^m)(λ_H + λ_D) r_b`).
* The integrated certificate from binary data: `nvh_restBI`, `nv_selectI_outcome` (the
  homogeneous witness satisfies `RestBI`, and `binary_select_solverI` gives `NOutcome` for the
  released protocol); `RestLI` is covered through `nvc_restLIConst` and `RestLIConst.toLI`.
* The witnesses have zero generator data, so their energy bounds and sample errors are trivial,
  and `r₀ r_b = 0`, so the rotation of the weight preparation does not mix the two sectors; the
  clock promises, the native identities, the address program and the weight preparation are
  exercised by the general proofs (`clockN`, `nativeOK_N`, `addrOKN`, `WpConst_srcAmp`).

**Proof map.**

* `Core`, `Integrated`: as above; `homog_discI` iterates `TimeDependentODE.step_error` over the
  slots, `target_factsBI` combines `target_errorBI` with `target_facts_of_error`.
* `SelectIntegrated`: `clockBA`, `selectBA` (the released `GateBinarySelect.clockB` argument at
  one sample), `instanceBI`, `instanceLI`, the six solvers (from `native_time_outcomeBI`,
  `native_time_trials_outcomeBI`, `GateSynth.soutcome`).
* `Const`: `wpGates_ok`, `prod_MxW`, `gRun_wp_zero`, `matOf`, `WpConst_col`, `WpConst_srcAmp`,
  `loadConst_approx` (the placement of `GateNative.srcIdeal`, `place_srcIdeal`, `srcIdealL_comp`).
  `ConstSolver`: from `GateBinaryODETime.binary_ode_time_solver`,
  `GateBinarySelect.binary_select_counts` and `binary_select_solverLI`.
* `NodeAddr`: `opsN3`, `chainN`, `opMdN`, `addrOpsN`, `addrOKN` and the register values
  (`vN_ax1`, `vN_n1`, `vN_z1`, `vN_acc`, `vN_md`). `NodeNative`: `apGN`, `fN`, `apGN_run`, `ndAN`,
  `odeOpN`. `NodeIdentity`: `decOK_N`, `nativeOK_N` (`GateBinarySelect.nativeOK_slotR`,
  `GateBinarySelect.nativeOK_computed` with `apGN_run`). `NodeClock`, `NodePub`, `NodeSolver`:
  as above, from `native_time_outcomeBI`, `native_ode_time_solverBI`,
  `native_time_trials_outcomeBI`, `GateNative.native_ode_time_gate_count`,
  `GateSynthTrials.native_ode_time_solver_trials` and `GateSynth.soutcome`.
* `NodeBudget`, `NodeBits`: `card_addrGT_le`, `card_ZAN_le`, `binary_nodes_arith_words`
  (`GateODEBudget.arith_words` with `μ` duration bits), `words_gate_arithN`, `wordsN_le`
  (`GateBitBudget.kap_words` with the exponent `μ + F + 10`), `card_XW_ZN`.

**Formalisation choices.**

* Sample positivity (a formal restriction): the time-dependent ODE solvers assume accretive
  dissipative parts of the represented samples the branches read, the hypothesis of the formal
  versions of Theorem `ode:thm:time`, which that theorem of the manuscript does not make (it asks of
  the represented samples only the uniform moment and norm promises; see
  `TimeDependentODE/Statements.lean`). `RepresentedSampleODE` lifts it for the query-level mesh
  solvers and the common-mesh gate solver; the conformance endpoints
  `ManuscriptConformance.ode_thm_time`, `ode_thm_gates_time_cert` and
  `ode_thm_gates_time_decoder_cert` hold for represented samples of any sign. The manuscript's
  theorems are not changed.
* The integrated certificate is the slot-weighted sum of the errors of the represented samples
  at the sample addresses (the integral over `[v_s, T]` of the piecewise-constant error); the
  variation of the generator path within a slot is charged to the Lipschitz term
  `βG u_s²/2^m`, which with `u_s ≤ T` gives the released discretisation term `βG T²/2^m` of the
  budget, so that the released budget `T (βG T/2^m + δG) B` is recovered with `δI = T δG`.
  As in the released solvers, the certificate concerns the generator samples `L + i H` against
  the path `G`, with the solver's budget `ε B/(2000 g)`, not the samples `H + k D` of the lemma
  with `δ/16`; the lemma's certificate at `k = 0` and `k = ±R` implies it up to a constant.
* The energy bounds are required at the samples the branches read (`SampleOK` at `addrF s r`,
  respectively `addrFN s r`); the selection conditions at slots beyond `2^m` concern the
  identity and are trivial.
* Constant forcing: the Hadamard gates of the weight preparation are controlled by the sector
  wire, so that the labels `(false, w)`, `w ≠ 0`, stay empty, as the released source format
  (`GateSelect.ODE.bsW`, `GateODE.Time.TParams.srcAmp`) requires; the rotation is one exact
  elementary gate (its finite-gate-set cost is that of the released synthesis). The supplied
  loading circuits are counted by their gates and enter with their accuracies `ζ₀`, `ζ₁`
  (`G_{x₀}(cν)`, `G_b(cν)` of the paper with `3 (ζ₀ + ζ₁) ≤ ν - 24 d ζ`); the weight
  preparation is exact, so the conditions `RestConst`, `RestLIConst` take the norms
  `r₀ = ‖x₀‖`, `r_b = ‖b‖` exactly (an approximate rotation is covered by the general solvers
  with a weight-preparation circuit within `ζs`). The left-endpoint certificate
  `Λ r_b T²/2^(m+1)` is the released one of `GateEfficientQuadrature` with `L = δb = 0`; the
  budget condition of `RestLIConst` is the admissibility condition of the mesh.
* Computed nodes: the node labels are the `2^m` labels of the released protocol, one per slot of
  a branch (`M = 2^m`); a quadrature with fewer nodes uses zero weights, one with more nodes
  needs a larger `m' > m`, which refines every branch (the discretisation term `βG T²/2^m` only
  decreases), adds `m' - m` label and slot bits and refines the address and data grids. The
  node words have `μ` bits (`v_u = word u · T/2^μ`, so the nodes lie in `[0, T)`; a quadrature
  node off this grid, including a node at `T` with its zero-duration branch, is rounded to a
  `μ`-bit node, and that rounding belongs to the source certificate `κ`, not to the sample
  error);
  the address program computes the exact branch addresses on the grid of `2^(μ+m)` points, and
  the data are sampled on a grid of `2^nd` points, `nd ≤ μ + m`, at the top `nd` bits of the
  address: the represented sample of a slot is the sample at the rounded time
  `⌊A/2^(μ+m-nd)⌋ T/2^nd`, and the rounding is part of `sampleErrNQ` (compared with the path at
  the exact address), as the proof allows. The node program is an explicit hypothesis with its
  gates and scratch counted (`|N|`, `|Zn|`), as the paper's "polynomial cost"; in the budgets
  `|N|` enters multiplied by `q*` (one copy per private call) and `μ` enters the register words
  (`bitN = 𝔟 + μ`; `μ ≤ b_data` gives `bitN ≤ 2 𝔟`).
* The decoder scale `κ = γ √(4s) c₀/(2^(μ+F+10) ρ)` of the branch operation carries the factor
  `2^(-μ)` of the duration word, which costs `μ` further bits of the decoder words.

**Not formalised.**

* The source certificate `κ` of a general positive quadrature (the first certificate of
  `ode:eq:gate-source-certificates`) and the loading and weight-preparation circuits of general
  forcing remain hypotheses, as in the paper; for constant forcing the loading circuits of `x₀`
  and `b` are supplied (`G_{x₀}`, `G_b`).
* Polynomial-cost bounds for particular node families other than the copy and midpoint
  programs (`m` and `m + 1` gates; the node program and its counts are hypotheses), a number of
  source nodes independent of the number `2^m` of slots per branch without refining the
  branches, and nodes at `T` (zero-duration branches, which the proof disables) other than by
  rounding them into `κ`.
* The integrated certificate for the generator samples of the common-mesh solver
  `GateBinaryODETime.binary_ode_time_solver` (its masked branches keep the released uniform
  bound; `binary_ode_time_solver_const` inherits it).
* An explicit example in which the integrated certificate of the binary-data solvers holds and
  no admissible uniform bound does (the strictness is shown for the certificate of Lemma
  `ode:lem:gate-select` by the released `GateBinarySelect.nvc_not_uniform`).
* The sufficient constant-forcing mesh `m ≤ 2 max{1, T² √s (η_D + η_H) ‖b‖/(2νB)}` of the proof of
  Theorem `ode:thm:gates` is not connected to `RestConst`, `RestLIConst`; its left-endpoint form
  with a Lipschitz bound `L_b = 0` is the released `GateQuad.nodes_sufficient`,
  `GateQuad.exists_pow_two_nodes` and `GateQuad.budget_disc_paper`.
* Lower bounds.

**Provenance.** New library, written against the released package: it imports
`GateEfficientBinarySelect` (with its dependencies `GateEfficientSelect`,
`GateEfficientQuadrature`, `GateEfficientBinaryODETime`, `GateEfficientBinaryODE`,
`GateEfficientBinary`, `GateEfficientNative`, `GateEfficientSynthesis`,
`GateEfficientSynthesisTrials`, `GateEfficientODEBudget`, `GateEfficientBitBudget`) and changes
none of them. The statement guide of `GateEfficientBinarySelect` lists as not formalised the
non-dyadic source nodes, the integrated certificate for the generator samples of the
dissipative solvers and energy bounds required only at the branch addresses; they are
formalised here in the form stated above.
-/
