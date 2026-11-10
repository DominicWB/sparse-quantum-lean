import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import ManuscriptConformance.Hamiltonian
import ManuscriptConformance.HamiltonianLower
import ManuscriptConformance.LinearSystemUpper
import ManuscriptConformance.LinearSystemLower
import ManuscriptConformance.LinearSystemSeparate
import ManuscriptConformance.ODEUpper
import ManuscriptConformance.ODELower
import ManuscriptConformance.ODELowerAdaptive
import ManuscriptConformance.ODETime
import ManuscriptConformance.ODEGeneral
import ManuscriptConformance.Appendix
import ManuscriptConformance.GateDefs
import ManuscriptConformance.GateMain
import ManuscriptConformance.GateHamiltonian
import ManuscriptConformance.GateODE
import ManuscriptConformance.GateODETime
import ManuscriptConformance.GateProps
import ManuscriptConformance.GateGeneralDefs
import ManuscriptConformance.GateGeneral
import ManuscriptConformance.GateDecoderDefs
import ManuscriptConformance.GateDecoder
import ManuscriptConformance.GateMainDecoder
import ManuscriptConformance.GateDecoderTables
import ManuscriptConformance.GateDecoderBinary
import ManuscriptConformance.GateODEGeneral
import ManuscriptConformance.GateODETimeGeneral
import ManuscriptConformance.GateODEDecoder
import ManuscriptConformance.GateODETimeCert
import ManuscriptConformance.GateODETimeCertValid
import ManuscriptConformance.ActualRuns
import ManuscriptConformance.BranchCertificates
import ManuscriptConformance.SourceExecutions
import ManuscriptConformance.EntrywiseCayley
import ManuscriptConformance.SourceExecutionsMore
import ManuscriptConformance.GateODETimeCertFinite
import ManuscriptConformance.GateDecoderTiny
import ManuscriptConformance.TaggedPairEntry
import ManuscriptConformance.TaggedPairSimulation
import ManuscriptConformance.WriterAccess
import ManuscriptConformance.WriterEndpoints
import ManuscriptConformance.WriterProtocols
import ManuscriptConformance.WriterProtocolEndpoints
import ManuscriptConformance.WriterSeparate
import ManuscriptConformance.GatePropsSelective
import ManuscriptConformance.GatePropsKnown
import ManuscriptConformance.WriterTimeEndpoints
import ManuscriptConformance.WriterGeneralEndpoint
import ManuscriptConformance.WriterTimeVariants
import ManuscriptConformance.ApproxRuns
import ManuscriptConformance.WriterGateAccess
import ManuscriptConformance.WriterGates
import ManuscriptConformance.WriterGatesDecoder
import ManuscriptConformance.WriterODEGates
import ManuscriptConformance.WriterODETimeGates
import ManuscriptConformance.WriterODECert
import ManuscriptConformance.WriterODESources
import ManuscriptConformance.WriterGeneralZero
import ManuscriptConformance.WriterDecoderAccess
import ManuscriptConformance.WriterDecoderODE
import ManuscriptConformance.WriterDecoderCert
import ManuscriptConformance.WriterDecoderSources
import ManuscriptConformance.WriterBranchCerts
import ManuscriptConformance.WriterGateVariants
import ManuscriptConformance.PrepColumn
import ManuscriptConformance.PrepLoader
import ManuscriptConformance.SourceLoaderColumns
import ManuscriptConformance.MeshLoaderColumns
import ManuscriptConformance.RobustLoaderColumns
import ManuscriptConformance.DysonLoaderColumns
import ManuscriptConformance.DysonLoaderActual
import ManuscriptConformance.TimeLoaderColumns
import ManuscriptConformance.TimeLoaderRuns
import ManuscriptConformance.TimeLoaderBranch
import ManuscriptConformance.LoaderApprox
import ManuscriptConformance.TimeLoaderApprox
import ManuscriptConformance.TimeLoaderBranchApprox

set_option autoImplicit false

/-!
# Manuscript conformance: the headline results as stated in the manuscript

This library restates the headline results of the manuscript with the assumptions the manuscript
permits, except where the summary table below records another hypothesis, and proves each
statement from the endpoints of the other
libraries of the package. Where the package needs more than the manuscript states, the extra
hypothesis is a named predicate `formal_…` (listed below, with the review item it records); the
manuscript's own external results and computational assumptions are named `ext_…` and `comp_…`.
Where a theorem uses another hypothesis of the package or proves less than the manuscript states,
the summary table below records it.
Every theorem is axiom-audited in `ManuscriptConformance/Audit.lean`. All declarations are in the
namespace `ManuscriptConformance`; names of other libraries are qualified by their namespace, given
relative to `SparseHamiltonian` for the libraries inside it (`GateSynth.synthBudget` is
`SparseHamiltonian.GateSynth.synthBudget`).

## Conventions

* **`O(·)`.** A bound `O(f)` is `∃ C, 0 < C ∧ …` with the constant chosen before every input and
  instance (the constants are explicit in the docstrings). In the gate theorems over a finite gate
  set the query counts have explicit absolute constants, and the gate and qubit constants depend on
  the gate set (and on the arithmetic assumption).
* **Uniformity.** One protocol or circuit, fixed before the instance, serves every instance: the
  quantifier order is "public data, then protocol, then instance", and the protocol depends only on
  the public data. In the gate-level ODE theorems the supplied source circuits are part of the
  public data: the protocol depends on them, and serves the instances whose sources they prepare
  (review item K below).
* **Error notions.** `FullOutputError` (eq. `hs:eq:fullerror`): the error of a circuit on the isometric
  encoding of every normalised input, all work registers included; `cleanInputError`: the same for
  a supplied operation on its registers and a temporary work register in its clean state (the
  temporary-work convention, eq. `access:eq:full-output`); `ReferenceOutputError`: the same
  with an untouched finite reference of any dimension; `HeraldedOutput`: success probability at
  least `2/3` and conditional output within trace distance `ε` (`TraceDistanceLE`); `RunsClose`:
  the conditional output is some mixture of unit vectors, each within Euclidean distance `ε` up
  to a global phase (a property of the density operator alone, which need not identify the actual
  runs: `runsClose_diagnostic`); `TrialsClose`, `HistoriesClose` (`ActualRuns`): every actual
  trial of the protocol with nonzero amplitude, and every successful history, outputs a state
  within `ε` up to a global phase.
* **Value oracle.** The package's convention is an additive value oracle: it adds the stored word
  to its target register, `z ↦ z + w_ij` in the additive group of the words
  (`NativeSparseBlockEncoding.oracles`, the table of `NativeSparseBlockEncoding.Data`; XOR on the
  bit strings of the gate theorems, `GateBinary.prims`), and it stores a word on every pair of
  index words, the words of invalid pairs being arbitrary (`GeneralSparseAccess.QData` for general
  sizes). The manuscript gives XOR-writing as an example of a reversible writer (eq.
  `access:eq:value`). A writer specified only on clean targets (`W |a, 0⟩ = c_a |a, w_a⟩`, any
  phases) is covered for `hs:thm:main`, `hs:thm:optimal`, `hs:thm:two-norm`, `qls:thm:main` and
  `ode:thm:main` (`hs_thm_main_writer`, `hs_thm_optimal_writer`, `hs_thm_two_norm_writer`,
  `qls_thm_main_writer`, `ode_thm_main_writer`: writer, adder and inverse writer on one clean
  scratch register, two writer calls per value call; see *A writer on clean targets* below), for
  `ode:thm:time`, `ode:thm:general` and `qls:cor:separate` (`qls_cor_separate_writer`), and, with
  a writer specified on the clean inputs of valid index pairs only, for the general-size gate
  theorems `hs:thm:gates` and `gate:thm:main`
  (`hs_thm_gates_general_writer`, `gate_thm_main_general_writer`, `hs_thm_gates_decoder_writer`,
  `gate_thm_main_decoder_writer`) and for the general-size forms of `ode:thm:gates` with the decoder
  `c₀(X + iY)` (`ode_thm_gates_general_writer`, `ode_thm_gates_time_general_writer`,
  `ode_thm_gates_time_cert_writer`, `ode_thm_gates_time_cert_valid_writer`) and with binary entry
  decoding (`ode_thm_gates_decoder_writer`, `ode_thm_gates_time_decoder_writer`,
  `ode_thm_gates_time_decoder_cert_writer`, `ode_thm_gates_time_decoder_cert_valid_writer`; see *A
  writer at the gate level* below); the other theorems keep the additive convention.
* **Gate model** (`GateDefs`). Circuits are lists of native instructions on qubit wires: one-qubit
  gates with at most three literal controls (so arbitrary single-qubit gates), or over a finite gate
  set `𝒢` gates of `𝒢` (`GateSynth.GateOf`), and calls of the supplied primitive oracles, counted
  separately. `cleanAlong` is the manuscript's clean embedding `ψ ⊗ |0⟩`.

## Summary

| Result | Theorems | Status | Formal restrictions and notes |
|---|---|---|---|
| `hs:thm:main` | `hs_thm_main`, `hs_thm_main_spectral`, `hs_thm_main_zero` | as stated | none; the spectral and zero forms here and `hs_thm_time_zero` state the full-output error without the untouched reference |
| `hs:thm:time` | `hs_thm_time`, `hs_thm_time_mesh_exists`, `hs_thm_time_zero` | as stated | the mesh, which the manuscript leaves to the proof, has `4 s η T ≤ M`, `9 β T² ≤ ε M` and `9 (√s η T)³ ≤ ε M²`, met by every large `M` (`hs_thm_time_mesh_exists`); these imply eq. `hs:eq:timegrid`, and coarser meshes admitted by that equation are not covered |
| `hs:thm:optimal` | `hs_thm_optimal`, `hs_thm_optimal_theta` | as stated | none; `hs_thm_optimal_theta` states the `Θ` at `η = 1` and `t = τ > 0`, with its lower half for single unitary programs (`NativeSignedFactor.Simulates`; other classes of algorithm: the row of `hsl:thm:main`); for general `η` and either sign of `t` it follows from `OptimalLowerBounds.two_norm_theta` at `m = 1`, `c = sign(t) η`, with `hs_thm_optimal` |
| `hs:thm:two-norm` | `hs_thm_two_norm` | as stated | none |
| `gate:thm:main` | `gate_thm_main`, `gate_thm_main_general`, `gate_thm_main_decoder`, `gate_thm_main_decoder_tiny`, `gate_thm_main_decoder_tables`, `gate_thm_main_general_of_decoder`, `gate_thm_main_general_writer`, `gate_thm_main_decoder_writer`, `gate_thm_main_decoder_tiny_writer`, `gate_thm_main_decoder_tables_writer`, `gate_thm_main_general_of_decoder_writer` | finite gate set; general sizes `N`, `s ≤ N` with locators prescribed on valid list inputs only (`gate_thm_main_general`, B); general sizes and any public decoder of the stored words (`gate_thm_main_decoder`, B2; for stored words of bounded width with no arithmetic hypothesis, `gate_thm_main_decoder_tables`; under the hypotheses of `gate_thm_main_general`, `gate_thm_main_general_of_decoder`); the value oracle a writer specified on the clean inputs of valid index pairs only, with the same bounds (`gate_thm_main_general_writer`, `gate_thm_main_decoder_writer` and the variants `…_tiny_writer`, `…_tables_writer`, `gate_thm_main_general_of_decoder_writer`, B4) | `formal_binaryInput` (B) for `gate_thm_main`; `formal_binaryDecoder` (B2) for `gate_thm_main_general`, with `comp_clipArith` at the scales of the padded construction (`genClipBeta`, `genClipScale`); none for `gate_thm_main_decoder`, with the arithmetic of the decoder `comp_rotArith` (at the rescalings `κ ∈ [1/η, √(2s)/η]` of the construction), `comp_signedArithV`, `comp_clipArithV` (the last at the scales of the padded construction) |
| `hs:cor:unitary` | `hs_cor_unitary`, `hs_cor_unitary_inexact`, `hs_cor_unitary_theta` | as stated | none for the upper bounds; the lower half of `hs_cor_unitary_theta` is for unitary programs over the entry oracle of `UnitaryImplementationExtensions.General` (the entry call with spectators, any `γ`) that implement every search permutation within operator-norm error `ε` on an isometric encoding; for algorithms with measurements inside a run, over the same oracle `UnitaryEntryOracle.oracle` (any parameters), with per-input trace-distance accuracy `ε₀` and a factor that vanishes at `ε₀ = 1/2`: `DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured` and `DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured_heralded`; in operator norm and up to `ε₀ = 1/2`: `MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm` and `MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint` |
| `hs:cor:unitary-optimal` | `hs_cor_unitary_optimal`, `hs_cor_unitary_optimal_inexact` | as stated | none; the constant-error order `Θ(√N)` is `hs_cor_unitary_theta`, whose lower bound is in the entry-oracle model of `UnitaryImplementationExtensions.General` |
| `hs:thm:gates` | `hs_thm_gates`, `hs_thm_gates_general`, `hs_thm_gates_decoder`, `hs_thm_gates_decoder_tiny`, `hs_thm_gates_decoder_tables`, `hs_thm_gates_general_of_decoder`, `hs_thm_gates_general_writer`, `hs_thm_gates_decoder_writer`, `hs_thm_gates_decoder_tiny_writer`, `hs_thm_gates_decoder_tables_writer`, `hs_thm_gates_general_of_decoder_writer` | finite gate set; binary conclusion `hs:eq:gate-binary` (gates and queries); general sizes as above (`hs_thm_gates_general`, B); general sizes and any public decoder (`hs_thm_gates_decoder`, B2; for stored words of bounded width with no arithmetic hypothesis, `hs_thm_gates_decoder_tables`; under the hypotheses of `hs_thm_gates_general`, `hs_thm_gates_general_of_decoder`); the value oracle a writer specified on the clean inputs of valid index pairs only, with the same bounds (`hs_thm_gates_general_writer`, `hs_thm_gates_decoder_writer` and the variants `…_tiny_writer`, `…_tables_writer`, `hs_thm_gates_general_of_decoder_writer`, B4) | `formal_binaryInput` (B) for `hs_thm_gates`; `formal_binaryDecoder` (B2) for `hs_thm_gates_general`; none for `hs_thm_gates_decoder`, with the angle arithmetic of the decoder `comp_rotArith` at the rescalings `κ ∈ [1/η, √(2s)/η]`; the explicit accounting of eqs. `hs:eq:gate-known`, `hs:eq:gate-Gzero` and `hs:eq:gate-total` is in the library `SparseGateAccounting` (`SparseGateAccounting.sparse_known_gates`, `sparse_gate_total`, `sparse_gate_total_signed`), on `GeneralSparseAccess.QData` with any public decoder, for a supplied private circuit (`PrivOK`), and with the private circuit constructed from the angle arithmetic `comp_rotArith` of the decoder and its promise derived in `SparseGateAccounting.sparse_gate_constructed` (B2; module `SparseGateAccounting.Native`), with `s' = 2^⌈log₂ s⌉` in place of `s` in the schedule, and with the original `s` in the schedule for a supplied boundary circuit preparing the boundary state of the `s` original slots (`SparseGateAccounting.UJPrep`, met by the Hadamard gates when `s` is a power of two; the uniform-range circuit itself is not constructed) in `SparseGateAccounting.sparse_gate_original` (module `SparseGateAccounting.Original`), the two finite-set theorems over a gate set with `GateSynthTrials.AdjClosed 𝒢`; the query-order sentence is not restated with it |
| `hsl:thm:main` | `hsl_thm_main` | as stated | single programs, uncontrolled calls; adaptive algorithms: `AdaptiveHamiltonianLowerBound.main_exists_tree`; measured algorithms: `DeferredMeasurementLowerBounds.Corollaries.main_exists_measured` |
| `hsl:cor:power` | `hsl_cor_power` | single programs, uncontrolled calls | no adaptive or measured form is stated, so the manuscript's adaptive and randomised algorithms are not covered |
| `hsl:prop:two-norm` | `hsl_prop_two_norm` | as stated | single programs, uncontrolled calls; adaptive protocols: `OptimalLowerBounds.two_norm_main_max_tree`; measured algorithms: `OptimalLowerBounds.two_norm_main_max_measured` |
| `ode:thm:main` | `ode_thm_main`, `ode_thm_main_actual` | as stated; every actual successful trial and every successful history within `ε` (`ode_thm_main_actual`; `ode_thm_main` states the mixture form `RunsClose`) | each preparation is an exact unitary on the data register; a circuit that restores temporary work only on its prepared input is not of this form |
| `ode:lem:tags` | `ode_lem_tags_rule`, `ode_lem_tags_rule_simulation`; `ODETaggedMoments.native_moment_certificate`, `ODETaggedMoments.native_lchs_moment_certificate`, `ODENativeCayley.program`, `ODENativeCayley.program_intertwines`, `ODEFixedTaggedQuery.query_certificate` | the moment bounds with `p = 2s`, also at the known boundary (`ODEFixedTaggedMoments.native_moment_certificate`), for every Hermitian `K` on `supp(G) ∪ supp(G†)`; the circuit conclusion (known `J`, constant sparse-query cost of `C_0`) for every `K` computed by a public rule `f i j (G i j) (G j i)` (`ode_lem_tags_rule`: `24` native calls, `ODETaggedPairEntry.program`; `K_k = H + kD` is the rule `lchsRule k`, and `ODENativeCayley.program` is literally its instance, `program_lchsRule`), and the baseline simulation of `exp(-i t K)` from it (`ode_lem_tags_rule_simulation`, Eq. `ode:eq:hs`) | the support and Hermiticity of `K` are asked of the rule (`f i j 0 0 = 0`, `f j i v u = star (f i j u v)`); the rule's arithmetic is exact (a scalar function in the gate table, as for `K_k`), no gate count is given for it |
| `ode:thm:time` | `ode_thm_time`, `ode_thm_time_approx`, `ode_thm_time_clock`, `ode_thm_time_actual`, `ode_thm_time_approx_runs`, `ode_thm_time_branch`, `ode_thm_time_approx_branch`, `ode_thm_time_actual_branch`, `ode_thm_time_columns`, `ode_thm_time_actual_columns`, `ode_thm_time_branch_columns`, `ode_thm_time_actual_branch_columns`, `ode_thm_time_columns_approx`, `ode_thm_time_branch_columns_approx` | mixed-output conclusion (D), and for exact source preparations every actual successful trial and history within `ε` (`ode_thm_time_actual`); for approximate source preparations every history whose trial has success probability at least `p₀` within `ε/500 + 2η/√p₀`, the others of weight at most `6 p₀` (`ode_thm_time_approx_runs`); represented samples of any sign (A); integrable pieces and mild solutions, no continuity (J); preparations on temporary work registers with clean-input errors (C); certificates on the opposite branches `K_{±k}` of the same samples in place of the generator and dissipative certificates (`…_branch`); for exact source preparations a loader specified only on its clean columns, also with every actual successful trial and history within `ε` (`ode_thm_time_columns`, `ode_thm_time_actual_columns`, and from branch certificates `ode_thm_time_branch_columns`, `ode_thm_time_actual_branch_columns`; handover item D1, exact case), and approximately, within `δ` of a label-controlled reference on the clean subspace (`ode_thm_time_columns_approx`, from branch certificates `ode_thm_time_branch_columns_approx`) | `formal_classicalPropagator` (J: generator breakpoints on the mesh, so a jump of the generator inside a mesh cell is not covered); label-controlled loading, a hypothesis of the package: the supplied loader acts on the data register as the unitary `J x a` for each label `a`, and in `ode_thm_time_approx` it is within `δ` of such a loader (`CleanWorkODE.ctrlL`), so a loader specified only on clean inputs, as in eq. `ode:eq:source-interface-preparation`, is not covered by these forms except `ode_thm_time_columns`, `ode_thm_time_actual_columns` and their branch forms, for exact preparations (it is also for the general-source solvers with exact preparations, on the uniform mesh, `GeneralSourceODE.solver_columns`, on a mesh, `GeneralSourceExtensions.Mesh.mesh_solver_columns`, `mesh_solver_integral_columns`, and with represented samples of any sign, `RepresentedSampleODE.robust_mesh_solver_columns`, `robust_solver_integral_columns`: paragraph *The column of the preparation*); `1 ≤ ḡ` (implied) and `1 ≤ c_q` (harmless up to absolute constants) stated |
| `ode:lem:block` | `GeneralODE.NativeBlock.exists_native_block` | this package's normalisation `8√2 Λ`; the manuscript has `2πΛ` | for every truncation order `N ≥ 1` (not the dimension), a selected block within `2ε + 4^{-N}/2` of `A/(8√2 Λ)`, with at most `1327104 (√(2s)·2N + √(2s·2N·ℓ) + ℓ)` queries, `ℓ = log(2/ε)`; the general solver runs on this normalisation (`m = ⌈8√2 ΛT⌉` steps) |
| `ode:thm:general` | `ode_thm_general`, `ode_thm_general_zero`, `ode_thm_general_writer`, `ode_thm_general_zero_writer` | conditional on `ext_blockSolver`; with a writer specified only on clean targets (`ode_thm_general_writer`, `ode_thm_general_zero_writer`, B4) | the hypothesis `ext_blockSolver` has at most `c κ log(2/δ)` calls and success at least `q₀`, where the proof of the theorem has polylogarithmic factors; each preparation is an exact unitary on the data register; otherwise none (`1 ≤ C̄`, `1 ≤ ḡ_path` stated, as the manuscript's bounds satisfy) |
| `ode:lem:gate-select` | `GateSelect.gate_select`, `GateSelect.gate_select_inverse`, `GateBinarySelect.gate_select_certified`, `GateBinarySelect.native_gate_select`, `GateBinarySelect.native_gate_select_inverse`, `GateBinarySelect.binary_gate_select`, `GateBinarySelect.binary_native_gate_select`, `GateBinarySelect.select_gates_bits`, `GateBinarySelect.binary_select_lemma_bits` | `T > 0`; exact gates for arbitrary labels, with the clock promises of the private operations as hypotheses; native gate model, no finite-set form of the lemma itself; the clock promises and the arithmetic constructed only from time-indexed binary data, for the labels of the solver | the package's filter degree `GateCircuit.Sim.fDeg` and subdivision condition `steps τ (δ/6) ≤ 2^m` in place of eq. `ode:eq:gate-select-schedule` and the first three bounds of eq. `ode:eq:gate-select-mesh` (for the solver's circuit `steps τ (ν'/3) ≤ 2^m`, `ν'` the precision of its private simulation, whose coarsest solution is `odeMesh`); in the native model the sample certificate `δ/32` in place of `δ/16`, with `16 L_* T² ≤ δ 2^m`, `steps τ (δ/12) ≤ 2^m` and `48 d ζ ≤ δ`; from binary data only the solver's dyadic labels (`GateNative.LabW`, `GateBinarySelect.kOf`, `GateBinarySelect.vOf`: `v_z = u' T/2^m`, `k_z` the LCHS node of the word `w`), `N = 2^{k_x}`, `s = 2^σ`, decoder `c₀(X + iY)`, and `4s` in place of the lemma's `p = 2s` (`Q = width(4s, γ)`, `λ_H = √(4s) η_H/γ`) |
| `ode:thm:gates`, constant | `ode_thm_gates`, `ode_thm_gates_general`, `ode_thm_gates_decoder`, `ode_thm_gates_sources`, `ode_thm_gates_decoder_sources`, `ode_thm_gates_general_writer`, `ode_thm_gates_general_sources_writer`, `ode_thm_gates_decoder_writer`, `ode_thm_gates_decoder_sources_writer` | native gate model, every `T ≥ 0`; for general sizes, with the decoder `c₀(X + iY)` or with binary entry decoding, also with a value writer specified on valid clean inputs only (`ode_thm_gates_general_writer`, `ode_thm_gates_decoder_writer`, B4); supplied native source circuits, charged by their gates and calls, with at most `40 ḡ` executions of each in every history counted on the annotated macro expansion of the protocol (`ode_thm_gates_sources`, `ode_thm_gates_decoder_sources`; no source-preparation oracle, K), each within `ν` (E); general sizes `N`, `s ≤ N` with locators prescribed on valid list inputs only (`ode_thm_gates_general`, B); general sizes and every decoder with an exact binary entry decoding, its cost in the polynomial of the gate bound and its wires in the qubit bound (`ode_thm_gates_decoder`, B2) | `formal_binaryInput` (B) for `ode_thm_gates`; `formal_binaryDecoder` (B2) for `ode_thm_gates_general`; for `ode_thm_gates_decoder` the binary entry decoding read as exact (`BinaryEntryDecoding`: values on the grid `c₀ (ℤ + iℤ)`, other decoders through the represented matrix); `formal_nondegenerate`; finite-set forms only under this package's format hypotheses: `GateSynth.native_ode_solver_synth` (native data, the source circuits synthesised too, `T > 0` and a positive energy scale, concluding success probability at least `2/3` and conditional trace distance, without the per-run bound), `GateSelective.binary_ode_budget_sel` (the binary format `N = 2^{k_x}`, `s = 2^σ`, decoder `c₀(X + iY)`, with `T > 0`, `η_H + η_D > 0`, over a gate set with `GateSynthTrials.AdjClosed 𝒢` and `GateSynthTrials.zeroTestKinds ⊆ 𝒢`, which `GateSynthTrials.extra_hyps` meets over an enlarged set, the counts then over that set) |
| `ode:thm:gates`, time-dependent | `ode_thm_gates_time`, `ode_thm_gates_time_general`, `ode_thm_gates_time_decoder`, `ode_thm_gates_time_cert`, `ode_thm_gates_time_decoder_cert`, `ode_thm_gates_time_cert_valid`, `ode_thm_gates_time_decoder_cert_valid`, `gate_select_sample_certificate`, `ode_thm_gates_time_cert_branch`, `ode_thm_gates_time_decoder_cert_branch`, `ode_thm_gates_time_cert_valid_branch`, `ode_thm_gates_time_decoder_cert_valid_branch`, `ode_thm_gates_time_cert_sources`, `ode_thm_gates_time_decoder_cert_sources`, `ode_thm_gates_time_cert_finite`, `ode_thm_gates_time_general_writer`, `ode_thm_gates_time_cert_writer`, `ode_thm_gates_time_cert_valid_writer`, `ode_thm_gates_time_general_sources_writer`, `ode_thm_gates_time_cert_sources_writer`, `ode_thm_gates_time_decoder_writer`, `ode_thm_gates_time_decoder_cert_writer`, `ode_thm_gates_time_decoder_cert_valid_writer`, `ode_thm_gates_time_decoder_sources_writer`, `ode_thm_gates_time_decoder_cert_sources_writer`, `ode_thm_gates_time_cert_branch_writer`, `ode_thm_gates_time_decoder_cert_branch_writer`, `ode_thm_gates_time_cert_valid_branch_writer`, `ode_thm_gates_time_decoder_cert_valid_branch_writer` | native gate model, uniform mesh, every `T ≥ 0`; for general sizes, with the decoder `c₀(X + iY)` or with binary entry decoding, also with a time-indexed value writer specified on valid clean inputs only (`ode_thm_gates_time_general_writer`, `ode_thm_gates_time_cert_writer`, `ode_thm_gates_time_cert_valid_writer`, `ode_thm_gates_time_decoder_writer`, `ode_thm_gates_time_decoder_cert_writer`, `ode_thm_gates_time_decoder_cert_valid_writer`, B4; their branch-certificate forms `…_branch_writer`); source circuits as above, each within `ν` (E), with at most `160 ḡ` executions of the loading circuit and `320 ḡ` of the weight-preparation circuit in every history (`…_sources`); sample certificates on the opposite branches `K_{±k}` of the same samples (`…_branch`); represented samples of any sign (A); general sizes as above (`ode_thm_gates_time_general`, B); general sizes and every decoder with an exact binary entry decoding (`ode_thm_gates_time_decoder`, B2); the manuscript's source certificates and a sample certificate for the uniform mesh of the slots (the mesh of the initial branch of `ode:lem:gate-select`), bounded through Lipschitz bounds and sample errors of the pieces and of their Hermitian parts (`ode_thm_gates_time_cert`, `ode_thm_gates_time_decoder_cert`, `gate_select_sample_certificate`, G), on the index register or for a problem on `ℂ^N` (`ode_thm_gates_time_cert_valid`, `ode_thm_gates_time_decoder_cert_valid`); over a finite gate set with the selective compiler (supplied circuits over the gate set retained verbatim, F), under the certificates, for time-indexed binary data with the sources at the slot times, with at most `80 ḡ` loadings and `160 ḡ` weight preparations in every history (`ode_thm_gates_time_cert_finite`) | `formal_binaryInput` (B) for `ode_thm_gates_time`; `formal_binaryDecoder` (B2) for `ode_thm_gates_time_general` and `ode_thm_gates_time_cert`; for `ode_thm_gates_time_decoder` and `ode_thm_gates_time_decoder_cert` the binary entry decoding read as exact (`BinaryEntryDecoding`, as above); `formal_gbarOne`; `formal_uniformMesh` (G; `formal_uniformMeshG` on the index register for `ode_thm_gates_time_general` and `ode_thm_gates_time_decoder`), not for `ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert`, which take `formal_classicalPropagator` (J), source quadrature nodes at the slot times and the formal solver's dissipative sample budget (`R ΔD ≤ ν'/6` at its radius `R`, where the lemma's certificate at `δ = ν` gives `R_ms ΔD ≤ ν'` at the manuscript's radius `R_ms`, `R ≤ 2.3 R_ms`); this package's conditions on the mesh and on `δ`: the time slots are one mesh `M = 2^m` with `m ≥ odeMesh …` or `m ≥ odeMeshG …` (at `2ḡ` in the certificate forms), the package's coarsest admissible exponents, not the `M` of the lemma, and the lemma's conditions give both sample budgets at `δ = ν/16` (a calculation not formalised in this package), where the manuscript takes `δ = ν`; finite-set forms only under this package's format hypotheses: `GateSynth.native_ode_time_solver_synth` (native data, the source circuits synthesised too, `T > 0`, a positive energy scale and `GateODE.Time.TParams.InstanceOK`, with accretive samples, concluding success probability at least `2/3` and conditional trace distance, without the per-run bound), `GateSelective.binary_ode_time_budget_sel` (the binary format above, accretive samples and `GateBinaryODETime.PubT.Rest`: a classical solution, a Lipschitz generator and forcing, the explicit discretisation budget), `GateBinarySelect.binary_select_budget_trials_bits` (the same format, branch-dependent meshes, dyadic source nodes, accretive samples and `GateBinarySelect.RestB`: nonnegative weights, a classical solution, a Lipschitz generator, sample bounds at the branch addresses, branch solutions with a quadrature error bound, the explicit discretisation budget); both binary forms over a gate set with `GateSynthTrials.AdjClosed 𝒢` and `GateSynthTrials.zeroTestKinds ⊆ 𝒢`, as above; with represented samples of any sign under the certificates, `ode_thm_gates_time_cert_finite` (`MeshCertificateODE.binary_ode_time_cert_sel`): the public record of time-indexed binary data (`PubT`, power-of-two sizes, exact binary entries) with `T > 0` and `η_H + η_D > 0`, the gate kinds of the exact zero tests in the gate set and an adjoint-closed gate set, the supplied synthesis of length `c₁ log(1/ζ) + c₀` |
| `odel:thm:combined` | `odel_thm_combined`, `odel_thm_combined_adaptive` | as stated | `odel_thm_combined`: single circuit programs over the coherent sampled-time access with forward and inverse calls, no controlled calls, no adaptivity; `odel_thm_combined_adaptive`: adaptive solvers (classical decision trees of fresh measured runs ending in a heralded protocol) over the same access and its call forms (plain, inverse, controlled and controlled-inverse calls), accuracy in the observable form of trace distance; one control qubit per call; measurements inside a run with the post-measurement state kept are not in the class (covered by `DeferredMeasurementLowerBounds.Corollaries.combined_measured`, with `DeferredMeasurementLowerBounds.Corollaries.joint_witness_measured` and `DeferredMeasurementLowerBounds.Corollaries.precision_terms_witness_measured` for the witnesses of the first and of the last two terms) |
| `odel:thm:joint` | `odel_thm_joint`, `odel_thm_joint_adaptive` | as stated | `odel_thm_joint`: single circuit programs over the coherent sampled-time access with forward and inverse calls, no controlled calls, no adaptivity; `odel_thm_joint_adaptive`: adaptive solvers (classical decision trees of fresh measured runs ending in a heralded protocol) over the same access and its call forms (plain, inverse, controlled and controlled-inverse calls), accuracy in the observable form of trace distance; one control qubit per call; measurements inside a run with the post-measurement state kept are not in the class (covered by `DeferredMeasurementLowerBounds.Corollaries.joint_witness_measured`) |
| `odel:rem:homogeneous` | `odel_rem_homogeneous`, `odel_rem_homogeneous_adaptive` | as stated | `odel_rem_homogeneous`: single circuit programs over the coherent sampled-time access with forward and inverse calls, no controlled calls, no adaptivity; `odel_rem_homogeneous_adaptive`: adaptive solvers (classical decision trees of fresh measured runs ending in a heralded protocol) over the same access and its call forms (plain, inverse, controlled and controlled-inverse calls), accuracy in the observable form of trace distance; one control qubit per call; measurements inside a run with the post-measurement state kept are not in the class (covered with the same bound by `DeferredMeasurementLowerBounds.Corollaries.measuredForces_of_treeForces` from the adaptive form) |
| `odel:thm:psd` | `odel_thm_psd`, `odel_thm_psd_adaptive` | as stated | `odel_thm_psd`: single circuit programs over the coherent sampled-time access with forward and inverse calls, no controlled calls, no adaptivity; `odel_thm_psd_adaptive`: adaptive solvers (classical decision trees of fresh measured runs ending in a heralded protocol) over the same access and its call forms (plain, inverse, controlled and controlled-inverse calls), accuracy in the observable form of trace distance; one control qubit per call; measurements inside a run with the post-measurement state kept are not in the class (covered with the same bound by `DeferredMeasurementLowerBounds.Corollaries.measuredForces_of_treeForces` from the adaptive form) |
| `odel:lem:dyson` | `DysonFullClass.full_single`, `DysonFullClass.full_actual`, `DysonFullClass.full_approx`, `DysonFullClass.full_bound` | the input class of `ode_thm_time`, with its two hypotheses of the package; certificates on two opposite branches through the coverage theorems of the next row | a classical propagator on each closed mesh cell and label-controlled loading (`DysonFullClass.FullValidAt`), hypotheses of the package: a jump of the generator inside a cell is not covered; a loader specified only on its clean columns is covered in the exact case for the trial-family certificate, the single-program and the separate-primitive forms (`DysonFullClass.full_dyson_columns`, `full_single_columns`, `full_actual_columns`: paragraph *The column of the preparation*), not for the approximate-preparation form `full_approx` |
| `odel:lem:dyson` (coverage) | `fullValidAt_of_branch_raw`, `fullValidAt_of_branch_clipped`, `fullValid_of_branch_raw` | the full-class validity relation of `DysonFullClass` from certificates on the opposite branches `K_{±k}` of the represented samples: `2 s E_G ≤ log(1 + δ_m)` through `E_G ≤ (1 + 1/k)(E₊ + E₋)/2` (raw samples), or `E_G ≤ log(1 + δ_m)` on the clipped samples | the factor `2s` of the clipping step and `z = s η T` of `DysonFullClass` kept |
| `qls:thm:main` | `qls_thm_main` | as stated | none |
| `qls:cor:separate` | `qls_cor_separate`, `qls_cor_separate_writer` | conditional on `ext_separateSolver` (`SparseLinearSystems.Separate.SeparateSolver`); the native input conventions, primitives and weights of `qls_thm_main`; matrix and preparation costs worst-case on every completed history; with a writer specified only on clean targets (`qls_cor_separate_writer`: the same protocol with every value call replaced by writer, adder and inverse writer on one clean scratch register, fixed before the instance, with the same success probability and conditional output, at most twice the matrix calls, constant `2 C_A`, and the same preparation calls, constant `C_b`) | the hypothesis `ext_separateSolver` is a single-trial interface for general (not necessarily Hermitian) block-input systems, stronger than the statement of Gao–Ji–Liu's theorem (success `2/3` by repeated measurement) and intended to follow from its proof (one Hermitian-input run, their Hermitian reduction and lower-sector selection): one circuit with a fixed isometric output selector, chosen before the oracle pair, at most `cM κ log(2/δ)` block-encoding and `cb (1 + κ/η)` preparation calls, heralded success at least `q₀` and direction error `δ`, for estimates `η` of `‖M⁻¹β‖` in the relaxed interval `[3/8, 5/2]`, the block encoding relative to a public isometric encoding of the system space; it is not proved in this package, and it is used at the universe levels of the instance; the protocol is a fixed-length repetition (`ODERepeatProtocol.Protocol`) of `⌈6/q₀⌉` single trials over its own register layout `Separate.sepOracle`, where the manuscript runs the measured solver five times and `qls_thm_main` uses `Protocol.Tree` over `Step.physOracle`; the preparation bound is stated only under the estimate promise; the cost of obtaining `ν̂` is not counted |
| `qls:prop:chebyshev` | `qls_prop_chebyshev` | as stated | none |
| `qls:lem:entry` | `qls_lem_entry` | as stated, for every Hermitian `s`-sparse `H` with `‖H‖ ≤ 1` (the row and column energies derived from the spectral bound; `J† K² J ≤ 1` in the Loewner order; the Cayley transform of every real multiple `γK`, with its inverse as the literal adjoint program, `6` calls of each sparse primitive) | none |
| `qlsl:thm:main` | `qlsl_thm_main` | as stated | adaptive protocols of fresh measured runs with classical branching; measurements inside a run with the post-measurement state kept are not in the class (covered for the same hard family by `DeferredMeasurementLowerBounds.Corollaries.lower_bound_measured`) |
| `opt:thm:signed` | `opt_thm_signed`, `opt_thm_signed_identity` | as stated | none |
| remark after `opt:thm:signed` | `gate_prop_signed`, `gate_prop_signed_native` | native-model form of the additional-gate and workspace bounds, before finite-set synthesis; finite mesh, exact weights | as for `gate:prop:signed`: designated flag qubits (`wKnown`) and exact rotations with the real clock weights, not the rounded coefficient preparation of the remark |
| `opt:thm:weights` | `opt_thm_weights` | as stated | none |
| `opt:prop:core` | `opt_prop_core` | as stated | none |
| `hs:lem:abstract` | `GateRemarks.abstract_simulation`, `GateRemarks.abstract_simulation_isometry`, `PrivateSpaceAbstract.abstract_simulation_finite`, `PrivateSpaceAbstract.oracleOp_padUnitary`, `PrivateSpaceAbstract.oracleOp_padUnitary_adjoint`, `PrivateSpaceAbstract.abstract_simulation_zero` | every finite-dimensional private space through isometric padding for a nonzero system; controlled padded-call and adjoint operator factorisations through the range-flagged original unitary and a known reflection; the zero system by the empty circuit | counts in the padded-unitary circuit; the factorisation gives the abstract query-model reduction, not an instruction-list translation with a separate original-oracle count; no elementary-gate or wire bound for an arbitrary embedding and range reflection; `U_J` is chosen after the data; any real `Q ≥ 1` |
| `gate:prop:finite` | `gate_prop_finite`, `gate_prop_finite_sel`, `gate_prop_finite_sel_native`, `sel_transfer` | native gate model (no synthesis term); over a finite gate set with a supplied finite-set controlled private circuit (B3: the supplied circuit charged linearly, `n_P G_C`, its work wires reused, the inverse calls its literal reverse-adjoint, the other exact gates synthesised with budget `ε/4`: `n_P G_C + G_known (c₁ log((G_known+1)/(ε/4)) + c₀ + 1)` gates, error `ε`) and with the native private operation compiled selectively | sector-controlled oracle calls (`SecOK`); for `gate_prop_finite` a native private operation of the compute–rotate–uncompute form, the bounded-regime form (I); known gates and wires counted from the supplied circuit, without the bounds through `R` of eqs. `gate:eq:budgets` and `gate:eq:explicit-space` |
| `gate:prop:signed` | `gate_prop_signed`, `gate_prop_signed_native`, `gate_prop_signed_sel`, `gate_prop_signed_sel_native`, `sel_signed_transfer`, `gate_prop_signed_known`, `gate_prop_signed_known_sel`, `gate_prop_signed_known_conv` | abstract factor; native gate model with native factors (explicit-gates form, `R = n`); over a finite gate set with a supplied finite-set circuit for the unconditional factor, charged linearly (B3), and with the native factor compiled selectively; for a general known `Π` and `Z` through a conversion to designated flag qubits (`Converts`), with the conversion built from supplied gates and charged (`convFactor`, `converts_of_gates`) | the circuits run on the wire-defined factor interface `wKnown` (H): a general known `Π` and `Z` enter through a supplied conversion (its gates `Cg` over `𝒢` and the preparation gates `Eg` with their exact promises), whose synthesis from a description of `Π` and `Z` is not formalised; `ε ≤ 1/64`; exact rotations with the real clock weights, not the rounded coefficients of eq. `gate:eq:round`; the finite-set forms by the selective construction (the supplied factor circuit retained), not by the coefficient rounding of the manuscript; the native factor in the package's compute–local-factor–uncompute form (`FactorOp.Public`, `FactorNativeOK`, `FactorArithOK`) |
| `gate:prop:core` | `gate_prop_core`, `gate_prop_core_native`, `gate_prop_core_sel`, `gate_prop_core_sel_native` | abstract private operation; native gate model with the factor-conjugated native private call (explicit-gates form, `R = 2d`); over a finite gate set with a supplied finite-set private circuit, charged linearly (B3: `6d G_C + G_known (c₁ log((G_known+1)/δ) + c₀ + 1)` gates, `G_known ≤ 200(d+1)(a+m+r+1) + 84 d C_J`, error `ε + 6dξ + δ`), and with the native private call compiled selectively | the native private call in the package's form `GateOptimalBinary.ClipNative` (native factor and rotation with their public conditions and native identities, the queries per call an input); exact rotations with the real weights of the signed smoothing |
| `hs:cor:hybrid` | — | not formalised | it relies on major results of other papers |
| value oracle, eq. `access:eq:value` | `NativeSparseBlockEncoding.Data`, `NativeSparseBlockEncoding.oracles`, `GateBinary.prims`, `GeneralSparseAccess.QData`; `WriterAccess.writerOracles`, `hs_thm_main_writer`, `hs_thm_optimal_writer`, `hs_thm_two_norm_writer`, `qls_thm_main_writer`, `qls_cor_separate_writer`, `ode_thm_main_writer`, `ode_thm_time_writer`, `ode_thm_time_actual_writer`, `ode_thm_time_approx_writer`, `ode_thm_general_writer`, `ode_thm_general_zero_writer`; `GeneralSparseAccess.QData.Writer`, `hs_thm_gates_general_writer`, `gate_thm_main_general_writer`, `hs_thm_gates_decoder_writer`, `gate_thm_main_decoder_writer`, `GeneralDecoderODE.implOK_implDPW` | additive on every pair of `k`-bit index words, in every theorem over these data; a writer specified only on clean targets for `hs:thm:main`, `hs:thm:optimal`, `hs:thm:two-norm`, `qls:thm:main`, `qls:cor:separate`, `ode:thm:main`, `ode:thm:general`, and a time-indexed one for `ode:thm:time`; a writer specified only on the clean inputs of valid index pairs for the general-size gate theorems `hs:thm:gates`, `gate:thm:main`, `ode:thm:gates` | the package's convention: `z ↦ z + w_ij`, XOR on bit strings, with a stored word on every pair of index words; a writer specified only on clean targets is covered for those eight results (the released circuits and protocols with two writer calls per value call; for `ode:thm:time` the time address an input register of the writer and the locators), and a writer specified only on the clean inputs of valid index pairs for the four general-size gate theorems of `hs:thm:gates`, `gate:thm:main` and the general-size forms of `ode:thm:gates` with the decoder `c₀(X + iY)` or with binary entry decoding (constant and time-dependent coefficients, the certificate and source-execution forms; the writer and its inverse in the places of the two XOR calls of the padded value oracle, the copy masked by the validity flag: the same bounds; on an invalid pair the inverse call undoes the writer, so no routing to a valid address is needed; with binary entry decoding the inverse writer in the place of the second supplied value call of every decoded value call, which on an invalid pair undoes the first decoded call around the masked copy), not for the other ODE and linear-system endpoints (the manuscript stores words for the valid pairs and gives XOR-writing as an example of a reversible writer) |

"As stated" means: the manuscript's hypotheses (or weaker ones), its conclusion (or a stronger
one), and its quantifier order, within the conventions above, in particular the additive value
oracle (last row of the table).
Any other status, and any restriction in the last column, says how the package's statement differs
from the manuscript's, in particular where it proves less.

## The named hypotheses

**Formal restrictions** (extra hypotheses of the package):

* `formal_binaryInput` (review item B, `GateDefs`): the binary sparse format of the gate
  endpoints: `N = 2^k`, `s = 2^{s_b}` slots on the low index words, entries `c₀(X + iY)` with
  two's complement components. The manuscript allows general sizes and any efficiently decoded
  encoding. General sizes are covered by `gate_thm_main_general`, `hs_thm_gates_general`,
  `ode_thm_gates_general` and `ode_thm_gates_time_general`, general sizes and general decoders by
  `gate_thm_main_decoder`, `hs_thm_gates_decoder`, `ode_thm_gates_decoder` and
  `ode_thm_gates_time_decoder` (below).
* `formal_binaryDecoder` (review item B2, `GateGeneral`): the stored words of sparse data of
  general size are pairs of `b`-bit two's complement words read by the public decoder
  `c₀(X + iY)`; the manuscript allows any efficiently decoded encoding. It is a hypothesis of
  `gate_thm_main_general`, `hs_thm_gates_general`, `ode_thm_gates_general`,
  `ode_thm_gates_time_general` and `ode_thm_gates_time_cert` only: `gate_thm_main_decoder` and
  `hs_thm_gates_decoder` take any public decoder, `ode_thm_gates_decoder`,
  `ode_thm_gates_time_decoder` and `ode_thm_gates_time_decoder_cert` every decoder with an exact
  binary entry decoding (below).
* `formal_classicalPropagator` (review item J, `ODETime`): the propagator of the generator
  pieces of `ode_thm_time` (and of `ode_thm_gates_time_cert`, `ode_thm_gates_time_decoder_cert`)
  is classical on every closed mesh interval, so a jump of the generator
  lies at a mesh point (the manuscript's known breakpoints); the manuscript's more general
  certificates also admit generators discontinuous at unknown points, with Carathéodory
  propagators.
* `formal_uniformMesh` (review item G, `GateODETime`): the package's uniform-mesh conditions for the
  time-dependent gate solver; besides the manuscript's assumptions it fixes the source quadrature to
  the left-point rule on the data mesh, takes the amplification bound on the discrete mass
  (`B_m ≤ ḡ ‖x(T)‖`), and uses the package's explicit discretisation certificate (at the sample
  error `3 δ_G`, with the branch budget `6 R' T δ_G ≤ ν'` of the represented samples), with uniform
  generator sample bounds at the slot times and a Lipschitz bound, sample errors and a norm bound
  for the forcing in place of the manuscript's sample and source certificates.
  `formal_uniformMeshG` (`GateODETimeGeneral`) is the same on the `k`-qubit index register of sparse
  access of general size, with the generator path within `δ_G` of the lifts of the samples extended
  by zero to the index words `≥ N`, for the released public parameters of the padded problem (the
  `λ` term of the discretisation condition that of `2^⌈log₂ s⌉` slots, up to `√2` larger than for
  `s` slots). Neither is a hypothesis of `ode_thm_gates_time_cert` and
  `ode_thm_gates_time_decoder_cert`, which take the manuscript's certificates (below).
* `formal_nondegenerate`, `formal_gbarOne` (`GateDefs`): `ḡ ≥ 1` (and `B > 0` for constant
  coefficients); both hold for every admissible instance, so they exclude only public data without
  an admissible instance.

**Represented samples of any sign** (review item A, resolved). The time-dependent endpoints
`ode_thm_time`, `ode_thm_time_approx`, `ode_thm_gates_time`, `ode_thm_gates_time_general` and
their decoder and certificate forms ask dissipativity of the true generator path only, as the
manuscript does: the represented samples may have dissipative parts of any sign
(`RepresentedSampleODE`; the analysis runs on positive repairs of the samples, the circuits on the
samples). Their sampling certificates bound the dissipative part of the represented-sample
contribution to the manuscript's branch certificate (the proof of Theorem `ode:thm:time`, after eq.
`ode:eq:timedisc`): `6 R (ΔD + ΔR) ≤ ν` on a mesh, where `R ΔD` bounds the dissipative part of the
integrated branch sample error `∑_r ∫ ‖K̃_{k,r} - K_k(u)‖ du ≤ ΔH + R ΔD`, `|k| ≤ R` (`ΔH`, `ΔD` the
integrated sample errors of the Hamiltonian and dissipative parts), and `6 R' T δ_G ≤ ν'` on
the uniform mesh of the gate solver, where `R' T δ_G` bounds the dissipative part of
`∑_r h_r ‖K̃_{k,r} - K_k(t_r)‖`, `|k| ≤ R'` (`6 R ΔD ≤ ν'` in the certificate form, below).

**Integrable pieces and mild solutions** (review item J: resolved for the forcing; the generator's
breakpoints lie on the mesh). `ode_thm_time` and `ode_thm_time_approx` assume neither continuity
of the generator and forcing pieces nor a classical solution: the solution need only be mild
(`RepresentedSampleODE.MildSolution`: an integrable propagated forcing `v ↦ U(T, v) b_r(v)`, as the
certificate on the propagated vector integral presupposes, and Duhamel's formula for `x(T)`), so
the forcing may jump inside a mesh interval, and the generator pieces need only be integrable
(`RepresentedSampleODE.RegularPieces`, as the integrated sample errors presuppose), with a
classical propagator on each closed mesh interval (`formal_classicalPropagator`). Classical
solutions of bounded pieces with an integrable propagated forcing are mild
(`RepresentedSampleODE.MildSolution.of_solves`).

**Source circuits within `ν`** (review item E, resolved). `ode_thm_gates`, `ode_thm_gates_time`,
`ode_thm_gates_general`, `ode_thm_gates_time_general` and their decoder and certificate forms ask
each supplied source circuit to be
within `ν = ε/(10⁴ ḡ)` of its ideal form on clean scratch, which the manuscript's combined
implementation error `ν` of `P_w`, the loading and `P_w†` implies (`G_src(ν)`, before Theorem
`ode:thm:gates`; for constant forcing `G_src(ν) = G_{x₀}(cν) + G_b(cν) + …`, eq.
`ode:eq:gate-constant-source`). The protocols and counts are the released ones (for the general
sizes, through `GeneralSparseODE`); `SourceAccuracyODE` certifies them for such circuits, with every
successful trial within `ε/250` (constant coefficients) or `ε/100` (time-dependent) of the
normalised solution. For constant coefficients the formal vector error is at most `18 ν B`, within
the manuscript's `19 ν B` (eq. `ode:eq:gate-vector-error`); for time-dependent coefficients the
formal analysis bounds it by `45 ν' B_m` against the discretised target, whose direction is within
`ε/1000` of that of the solution (`ν'` the precision of the solver's private simulation). The
certificate forms (`ode_thm_gates_time_cert`, `ode_thm_gates_time_decoder_cert`) are certified by
`MeshCertificateODE` instead, with source circuits within `ν = 8 ν'` (`ν'` at the amplification
bound `2ḡ`, source budget `25 ν'`) and vector error at most `81 ν' B_m`.

**Clean-input preparation errors** (review item C, resolved). `ode_thm_time_approx` lets the
supplied `P_w` and `U_load` use a temporary work register and bounds only their clean-input
operator errors (`cleanInputError`: the temporary-work convention, eq. `access:eq:full-output`), as
Section `ode:sec:time` does before Theorem `ode:thm:time`; the exact preparations are `P` and the
label-controlled loader `∑_a |a⟩⟨a| ⊗ L(a)` with unitary completions `L(a)`; neither need be supplied, the label-controlled form is a
hypothesis of this package, and `formal_prepNorm` is removed. Eq.
`ode:eq:source-interface-preparation` specifies the loader on clean inputs, with arbitrary unitary
completions on unused labels; a supplied loader close only to a label-mixing unitary completion is
not covered. The protocol is the package's trial family
with every fixed gate acting as the identity on the work register, heralded on the output flag and a
clean work register (`CleanWorkODE`): every supplied call keeps its clean-input error with the
remaining registers as spectators (`CleanWorkODE.liftAct_clean`,
`CleanWorkODE.sourcePhysical_clean`), the errors add along every trial, inverse calls included
(`CleanWorkODE.eval_workRecast_clean`), and four fresh trials keep the released guarantees
(`CleanWorkODE.work_certificate`).

**Sparse access of general size** (review item B: general sizes resolved for `gate:thm:main`,
`hs:thm:gates` and `ode:thm:gates`). `gate_thm_main_general` and `hs_thm_gates_general` take the
manuscript's sparse access (Section `hs:sec:control`) for an `N × N` matrix with `s`-sparse lists,
`1 ≤ s ≤ N` (`SparseHamiltonian.GeneralSparseAccess.QData`), on index registers of `k = ⌈log₂ N⌉`
qubits (`2^k < 2N ≤ 2^{k+1}`), with locators that are unitary on their full registers and prescribed
on the valid list inputs only (Section `hs:sec:control`, after eq. `access:eq:locator`), and a value
oracle that XOR-writes a stored word on every pair of index words (the manuscript gives XOR-writing
as an example, eq. `access:eq:value`). The conclusion is the full-output error against the evolution
of the matrix extended by zero to the index words `≥ N`
(`SparseHamiltonian.GeneralSparseAccess.QData.padMat`), on the clean embedding of the index
register; the counts are in `N` and `s`, the query counts with absolute constants. The
circuit is that of the binary theorem at accuracy `ε/2` for the padded data (`k + 1`-bit index
words with a marker, `2^⌈log₂ s⌉ < 2s` slots), with every padded oracle call implemented from the
supplied oracles (`SparseHamiltonian.GeneralSparseAccess.implP`: the locator tests `[i < N]`,
`[a < s]` and the value-oracle test `[i < N] ∧ [j < N]` (cf. Section `hs:sec:gates`, before eq.
`hs:eq:gate-schedule`) by comparisons on clean borrow wires, the supplied locator controlled on a
clear marker with a reference by `access:lem:control`, three calls; the value oracle with a validity
flag, two calls) and the implementation gates synthesised over the gate set (`genCirc`). The
manuscript instead treats non-power-of-two `s` by a uniform-range preparation and invalid labels by
validity tests inside the circuit (Section `hs:sec:gates`, before eq. `hs:eq:gate-schedule`).
`comp_signedArith`, `comp_clipArith` are asked at the index width `k`, and `comp_clipArith` at the
scales of the padded construction: the clipping parameter at accuracy `ε/2` (`genClipBeta`) and the
Cayley scale at sparsity `2^⌈log₂ s⌉` and accuracy `ε/2` (`genClipScale`). The decoder is
`c0 (X + iY)` (`formal_binaryDecoder`, B2).

`ode_thm_gates_general` and `ode_thm_gates_time_general` (`ode:thm:gates`, constant and
time-dependent coefficients, every `T ≥ 0`) take the same sparse access (time-indexed in the
time-dependent case: the sample of slot `r` is `D.matrix (x, r)`, the oracles of the samples
selected coherently by the slot wires, `SparseHamiltonian.GeneralSparseODE.primsTG`). The protocol
is the package's four-attempt protocol of the binary theorem on the padded data
(`SparseHamiltonian.GeneralSparseODE.GPub.prep`, `GPubT.prep`, library `GeneralSparseODE`), with
every call of the padded oracles in the private operation replaced by its implementation from the
supplied oracles (`implP`, on clean ancillas added to the private scratch: at most three supplied
calls of the same kind and `implG k b = 30 (k + 1) + 4 b` gates per padded call) and the source
circuits of the `k`-qubit index register on the low wires of the padded system register. The
conclusions are those of the binary theorems with the counts in `N` and `s` (the padded word
budget is within `+3` of the manuscript's `𝔟` in the constant case and within `+5` in the
time-dependent case, whose solver runs at the internal ratio `2ḡ` and accuracy `ε/2`; the padded
query shape is at most `2`, resp. `6`, times `q`), and the output is the normalised solution on the
index register with the marker qubit clean (`cleanAlong Fin.castSuccEmb`): the solution of
`x' = -A x + b` for `A` the matrix extended by zero to the index words `≥ N`
(`SparseHamiltonian.GeneralSparseODE.padLift`, the matrix on the valid index words and zero
elsewhere: `padLift_eq`). For sources on `ℂ^N` (`validEmb`, the basis vector of `i` to that of the
index word `binW k i`) the target is the clean embedding of `validEmb` of the normalised solution
on `ℂ^N` (`solution_padLift_validEmb`; time-dependent: `solves_validLift`, `accretive_validLift`,
`norm_validLift_sub_le`, `norm_validLift_sub_padLift_le` for the lifted generator path), and a
source component on an invalid index word evolves freely (`solution_padLift_invalid`), so the
theorems also cover such sources. The time-dependent instance conditions are those of the released
public parameters of the padded problem (`formal_uniformMeshG`). The decoder is `c₀(X + iY)`
(`formal_binaryDecoder`, B2); `ode_thm_gates_decoder` and `ode_thm_gates_time_decoder` take every
decoder with an exact binary entry decoding (below).

**General decoders** (review item B2: resolved for `gate:thm:main`, `hs:thm:gates` and
`ode:thm:gates`).
`gate_thm_main_decoder` and `hs_thm_gates_decoder` take the sparse access of general size above
with any public decoder `val` of the stored words in place of the decoder `c₀(X + iY)`, and ask the
computational assumptions of the manuscript (the paragraph before Theorem `gate:thm:main` and the
assumptions before eq. `hs:eq:gate-binary`) for the decoder `val`: reversible word arithmetic on the
value word writing the local rotation parameters of the construction to accuracy `ξ` with gates and
work wires at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` (`comp_rotArith` for the angles of the
rotation of the bounded regime and of `hs:thm:gates`, at the rescalings `κ ∈ [1/η, √(2s)/η]` of the
construction; `comp_signedArithV` for the factor of the signed-factor regime; `comp_clipArithV` for
the factor and the rotation of the clipped regime, at the scales of the padded construction). The
circuit is that of the binary theorems for the decoder of the data (`hs_gates_dataDec`,
`gate_main_dataDec`, from the native operations of the library `GeneralDecoder` decoding with the
decoder of the data) at accuracy `ε/2` for the padded data with a validity decoder
(`SparseHamiltonian.GeneralSparseAccess.QData.padDataE`: the supplied word of the low index words
on every pair, decoded as `val w` on a pair of valid index words and as `0` otherwise), with the
padded oracles implemented from the supplied ones (`implPE`: the padded locators of `implP`, one
supplied value call) and the implementation gates synthesised over the gate set (`genCircE`). On an
invalid pair the returned word is the XOR-written word of the low index words, which `QData`
stores on every pair of index words (the manuscript prescribes the words of the valid pairs and
gives XOR-writing as an example, eq. `access:eq:value`). The arithmetic of the padded data computes
the validity of the pair of index words on the index wires, runs the arithmetic of `val`, copies the
angle and phase words under the validity and uncomputes (`GeneralDecoder` `RotWordArith.flagLift`,
`WordArith.flagLiftG`), so on an invalid pair the local operations are selected by the validity
of the pair (Section `hs:sec:gates`, before eq. `hs:eq:gate-schedule`, for `hs:thm:gates`; the
paragraph after the proof of Lemma `hs:lem:boundary` for `gate:thm:main`: "a known fixed action
independently of the returned value word"): the rotation of `hs:thm:gates` and of the
bounded regime, the factors and the phase of the clipped rotation are those of the zero entry
independently of the returned word; with the branch bit `g` set, the angle word of the clipped
rotation is the word of the arithmetic for the returned word, within `ξ` of the angle
`2 arctan(2q [f])` of the zero entry (as `|y(1, f, c₁, c₂)| = 2q [f]` for every entry), so that
action is fixed up to the accuracy `ξ`, which the error bound absorbs. The query counts are those
of `gate_thm_main_general` and `hs_thm_gates_general` (`288·10¹² Q_μ` and `6635520 q`).

**Tiny entries without their phase** (`GateDecoderTiny`). Through `RotWordArith.phi` the assumption
`comp_rotArith` asks the phase word of `arg (val w)` for every word with `val w ≠ 0`, however small.
`hs_thm_gates_decoder_tiny` and `gate_thm_main_decoder_tiny` ask the arithmetic assumptions for the
thresholded decoder `dropVal small val` instead (`0` on the words selected by a public test `small`
that only selects entries of modulus at most `τ` and does not separate an entry from its conjugate;
the arithmetic decides the test reversibly on the stored word and returns the parameters of the zero
entry there, so no phase word is asked for a selected word, `dropVal_phi_vacuous`). The same circuit
on the original data then has full-output error at most `ε + |t| s τ` against the evolution of the
original matrix: the access with the thresholded decoder (`QData.dropTiny`, the same table,
locators and oracles, `dropTiny_prims`) keeps every promise of the instance, and its padded matrix is
within `s τ` of that of the data in operator norm on the original locator lists
(`padMat_dropTiny_sub`). With `small = false` the thresholded decoder is `val` (`dropVal_false`).
The threshold is global (`s τ |t|` in the evolution); the local per-rotation tolerance of the
manuscript's argument (`D(0)` where `‖D(a) - D(0)‖` is within the local tolerance) would need the
weaker phase premise inside `GateNative.ArithOK`, which is not changed here.

The two theorems extend the general-size theorems, with other constants `C` and `K`
(`GateDecoderBinary`): for the decoder `c₀(X + iY)` the hypotheses of `hs_thm_gates_general` imply
those of `hs_thm_gates_decoder` at `c_A = 2·10⁷`, `d_A = 3` (`comp_rotArith_binary`: the CORDIC
arithmetic of the package on the value word, for `c₀`, `η` of bit length `b_data`), and the
hypotheses of `gate_thm_main_general` with constants `c_A`, `d_A` imply those of
`gate_thm_main_decoder` at `max(c_A, 2·10⁷)`, `max(d_A, 3)` (with `comp_signedArithV_binary`,
`comp_clipArithV_binary` from `comp_signedArith`, `comp_clipArith`, and the monotonicity lemmas
`comp_rotArith_cmono`, `comp_signedArithV_cmono`, `comp_clipArithV_cmono`,
`comp_rotArith_dmono`, `comp_signedArithV_dmono`, `comp_clipArithV_dmono`);
`hs_thm_gates_general_of_decoder` and `gate_thm_main_general_of_decoder` state the conclusions of
the decoder theorems under the hypotheses of the general-size theorems (the gate exponent of
`hs_thm_gates_general`, `4`, is not restated). The form and the accuracy of the assumptions can be met for every
decoder: by reversible lookup tables (`GateDecoderTables`; `GeneralDecoder.Tables`) they hold with
`c_A = tableConst b = 2^{2b+8} (b + 1)` and `d_A = 1` (`comp_rotArith_tables`,
`comp_signedArithV_tables`, `comp_clipArithV_tables`), so for stored words of `2b` bits with
`b ≤ b₀` the two theorems hold with no arithmetic hypothesis (`hs_thm_gates_decoder_tables`,
`gate_thm_main_decoder_tables`, with gate constants exponential in `b₀`); the polynomial bound with
constants independent of `b` is the computational content of the assumptions.

`ode_thm_gates_decoder` and `ode_thm_gates_time_decoder` (`GateODEDecoder`, library
`GeneralDecoderODE`) take the sparse access of general size with a decoder `val` and, as the formal
reading of its "efficient binary entry decoding" (Section `ode:sec:gates`, Theorem `ode:thm:gates`),
an exact binary entry decoding: a reversible circuit `dc` of controlled NOT gates with at most three
controls (`GeneralDecoderODE.BinDecode b b' A`) that writes, from every stored word, two `b'`-bit
two's complement components on clean wires and restores its `A` work wires, and is exact for the
decoder, `val w = c₀ (X + iY)` (`BinaryEntryDecoding`, `b' > 0`, `c₀ > 0`). The represented entries
then lie on the grid `c₀ (ℤ + iℤ)`; exactness on every stored word is harmless (the oracles do not
depend on `val`), and a decoder with other values, or a decoding to the requested accuracy only, is
not covered: the theorems apply to the rounded decoder, whose values define the represented matrix
(Section `hs:sec:control`, after eq. `access:eq:value`). The bit bound `b_data` of `comp_bits`
bounds the decoded components (`b' ≤ b_data`) and the public parameters; the stored words enter
through the cost and the wires of the decoding (for the manuscript's `b_data`, which also bounds the
stored words, the theorems apply with `max(b_data, b')`). The protocol is that of
`ode_thm_gates_general` and `ode_thm_gates_time_general` for the decoded data (`QData.decData`: the
same matrix and locators, the stored words replaced by their decoded words read by `c₀(X + iY)`),
with every padded call implemented by `implP` of the decoded data and every decoded value call in it
by two supplied value calls around the decoding circuit, the copy of the decoded word into the
value wires and the decoding backwards (`GeneralDecoderODE.implDec`, `implDP`: at most six supplied
calls of the same kind and `implG k b' + 3 (2 |dc| + 2b')` gates per padded call, on clean
ancillas in the private scratch). The bounds carry the decoding cost `cost dc = |dc| + 2b + 2b' + A`
(gates and wires) in the polynomial of the gate bound and its wires `wires dc = 2b + 2b' + A` in the
qubit bound: at most `C ḡ [q ((𝔟+1)³ + cost dc) + G_src + A_src]` gates and
`C (𝔟+1)³ + C A_src + C wires dc` qubits, and the query counts of the general-size theorems (in the
library bounds twice the constants of `GeneralSparseODE`: at most six supplied calls per padded call
in place of three). The decoder `c₀(X + iY)` has the copy of the stored word as a binary entry
decoding (`binaryEntryDecoding_copy`: `2b` gates, cost `6b + A`), so the decoder theorems apply
under the hypotheses of the general-size theorems, with their own protocol and constants; every
decoder whose values are binary entries has the lookup-table decoding (`exists_binaryEntryDecoding`,
at most `2^{2b} · 2b' (4b + 1)` gates).

**The manuscript's certificates** (review item G: resolved for the time-dependent `ode:thm:gates`
on sparse access of general size, except the placement of the source nodes and a constant factor,
below `14`, in the dissipative sample budget).
`ode_thm_gates_time_cert` and `ode_thm_gates_time_decoder_cert` (`GateODETimeCert`, library
`MeshCertificateODE`) state the time-dependent theorems of general size (with the decoder
`c₀(X + iY)`, resp. a decoder with an exact binary entry decoding) under the manuscript's
certificates (eq. `ode:eq:gate-source-certificates` and the represented-sample certificates of
Lemma `ode:lem:gate-select`) in place of `formal_uniformMeshG`. The generator is given by pieces
`G_r` on the closed intervals of the uniform mesh `t_r = r T / M` of the `M = 2^m` slots (`m` at
least the coarsest admissible exponent of the padded problem at the amplification bound `2ḡ`),
accretive (the true path dissipative) and integrable, with their propagator `U`
(`formal_classicalPropagator`), and the solution `x` is mild, `B = ‖x₀‖ + ∫ ‖b‖`. The source is a
positive quadrature with nodes at the slot times `t_r`, `r < M`: the source vector `b̃_r` of slot
`r` enters with weight `T/M`, so for `T > 0` weights `w_r ≥ 0` are the case
`(T/M) b̃_r = w_r b(t_r)` (the node `T` is not a slot time), prepared with the
amplitudes `√(‖x₀‖/B_m)`, `√(w_r ‖b(t_r)‖/B_m)` (`MeshCertificateODE.quadAmp`) and the directions of
`x₀` and `b(t_r)`; its certificates are those of eq. `ode:eq:gate-source-certificates`:
`‖x(T) - U(T, 0) x₀ - ∑_r w_r U(T, t_r) b(t_r)‖ ≤ ζ B` (`MeshCertificateODE.quadSum`),
`B_m ≤ 2B` (`MeshCertificateODE.quadMass`), `B ≤ ḡ ‖x(T)‖` and `x(T) ≠ 0`. The sample certificate
for the same uniform mesh bounds the integrated sample error `ΔG = ∑_r ∫ ‖G_r(u) - G̃_r‖ du` of the
represented samples on the index register (`MeshCertificateODE.sampleErr`) and its dissipative
part `ΔD` (`MeshCertificateODE.dissErr`): `ζ + 2 (ΔG + 2 ΔD) ≤ ε/(2000 ḡ)` and `6 R ΔD ≤ ν'`, the
budgets of `ode_thm_time` with `c_q = 2` (`R`, `ν'` the radius and precision of `ode:thm:time` at
`2ḡ`, `R = 4 log(16/ν)`, `ν' = ν/8`); for `ζ = ν` the first asks `ΔG + 2 ΔD ≤ 2ν`. The uniform
mesh of the slots is the mesh of the initial branch in Lemma `ode:lem:gate-select`, and Lipschitz
bounds give the two errors: `gate_select_sample_certificate` (`ΔG ≤ β T²/(2M) + (T/M) ∑_r δ_r` for
`β`-Lipschitz pieces with left-endpoint sample errors `δ_r`, and
`ΔD ≤ β_D T²/(2M) + (T/M) ∑_r δ^D_r` for their Hermitian parts). The lemma's conditions at
`δ = ν` (`L_* ≥ Lip(H) + R_ms Lip(D)`, `M ≥ 8 L_* T²/δ`, integrated error at most `δ/16` of the
represented samples on every branch `H + kD`, `|k| ≤ R_ms`, for the manuscript's frequency radius
`R_ms = 2 + 2 log((1 + 1/(2π))/ν)`, eq. `ode:eq:nu`) give the first budget (`ΔG ≤ 3ν/16`) and, from
the branches `k = ±R_ms`, `R_ms ΔD ≤ ν/8 = ν'`. The second budget is the branch budget of the
formal solver, whose analysis keeps the branch evolutions of the represented samples within `ν'/3`
of those of their positive repairs; it asks `R ΔD ≤ ν'/6` at the radius `R` of the formal solver,
`2 R_ms < R ≤ 2.3 R_ms` (as `ν ≤ 5·10⁻⁵`), so the lemma's conditions give it at a `δ` finer by the
factor `6R/R_ms < 14`, in particular at `δ = ν/16`, which gives both budgets. This `δ` and the mesh
exponent `m ≥ odeMeshG …` of the theorems are this package's conditions; the manuscript chooses `d`
and `M` from the lemma at `δ = ν`. The protocol is that of `ode_thm_gates_time_general`, resp.
`ode_thm_gates_time_decoder`, for the public data with the amplification bound `2ḡ` (the solver
needs `B_m ≤ 2ḡ ‖x(T)‖`; internal ratio `4ḡ`), fixed before the instance; the bounds are those of
the two theorems with the manuscript's `q` and `𝔟` at `ḡ` and the constants `108 C₀`
(`odeShape_two_le`, `bitB_two_le`), with source circuits within `ν = ε/(10⁴ ḡ)`
(`odePubT_zeta2`). The analysis compares the discretised target of the solver, the exponential
left-endpoint recurrence of the represented samples, with the quadrature sum through `ΔG`
(`MeshCertificateODE.quad_target_error`), on the positive repairs of the samples with the path
negativity bounds of the slots, whose negativity mass is `ΔD`. Not covered: quadrature nodes other
than the slot times. The manuscript's nodes are computed coherently from their labels, and its
selection lemma propagates each branch on its own uniform mesh `v_z + r u_z/M`; the formal solver
propagates every branch on the common mesh of the slots, with the samples of the slot-indexed
oracles (a quadrature on a coarser power-of-two mesh is the case of zero weights off its nodes).
Branch-dependent meshes and coherently computed nodes are formalised for time-indexed binary data
under their own instance conditions (`GateEfficientSelect`, `GateEfficientBinarySelect`,
`GateEfficientBinaryNodes`), not in these theorems. The two theorems are stated on the index
register, for the matrix extended by zero to the index words `≥ N`;
`ode_thm_gates_time_cert_valid` and `ode_thm_gates_time_decoder_cert_valid` (`GateODETimeCertValid`)
state their guarantees for a problem on `ℂ^N`, with the same protocols: generator pieces, forcing,
mild solution, propagator and source vectors on `ℂ^N`, the certificates on `ℂ^N` with the sample
errors against the samples `matrixOperator (D.matrix (x, r))`, and the loading preparing the
embedded directions `validEmb (x₀/‖x₀‖)`, `validEmb (b_r/‖b_r‖)`, against the embedding
`validEmb (x(T)/‖x(T)‖)` with the marker clean. They apply the index-register theorems to the lifted
problem (`MeshCertificateODE.Valid`: `validLift ∘ G_r`, the embedded vectors and the lifted
propagator `liftV N k U`), whose certificate-form conditions follow from those on `ℂ^N`
(`isMeshPropagator_liftV`, `mild_liftV`, `quadSum_liftV`, `meshScale_validEmb`,
`quadMass_validEmb`, `quadAmp_validEmb`, `sampleErr_padLift_le`, `dissErr_padLift_le`).

**The finite gate set under the certificates** (`GateODETimeCertFinite`, libraries
`MeshCertificateODE` and `GateEfficientSelective`). `ode_thm_gates_time_cert_finite` states the
time-dependent Theorem `ode:thm:gates` over a finite gate set `𝒢` under the certificate-form
conditions `MeshCertificateODE.CertRest` (represented samples of either sign, accretive integrable
pieces with their propagator, the source certificate at the slot times and the sample budgets) for
time-indexed binary data (`GateBinaryODETime.PubT`: power-of-two sizes, exact binary entries
`c₀ (X + iY)`, the uniform mesh `M = 2^m` of the slots, the sources at the slot times), stated for
the public record `q` with `q.OK` (`T > 0` and `η_H + η_D > 0`; the zero branches are not covered)
and protocol parameter `2ḡ`, `ḡ = q.g`, not in the manuscript's parameters. The protocol is fixed
before the instance: the native preparation compiled by the selective compiler
(`GateSelective.selPrep` with the budget `ν'/3`: the gates of `𝒢` and every call kept, the supplied
loading and weight-preparation circuits over `𝒢` retained verbatim, the other gates synthesised by
the supplied synthesis of length at most `c₁ log(1/ζ) + c₀`), the exact zero tests (their gate kinds
assumed in `𝒢`, `zeroTestKinds ⊆ 𝒢`) and the literal reverse-adjoint of the compiled preparation
(`AdjClosed 𝒢`). Its guarantees (success at least `2/3`, conditional trace distance `ε`, every
successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase) are derived from the
certificate of the actual compiled preparation (`MeshCertificateODE.cert_time_outcome_of`: the
selected-vector error and the amplitude from `cert_prep_certificate` and `cert_target_facts'`, the
synthesis error charged on the actual preparation; the two bounds are stated for the compiled
preparation in `MeshCertificateODE.cert_time_sel_prep_bounds`), for supplied circuits within `ζ_s`
with `98304 q* ζ + 3 ζ_s ≤ ν'`. The resources are those of
`GateSelective.binary_ode_time_budget_sel`, in `𝔟` (`q* = qOf s T η_H η_D (2ḡ) (ε/2)`, `𝔟` the bit
budget `bitB`): at most `2·10¹⁸ q* (𝔟+1)³` synthesised occurrences per preparation; at most
`80 ḡ (G_load + 2 G_wp + K (64 c₁ (𝔟+1) + c₀ + 1)) + 40 ḡ (4 n + 3)` gates with
`K = 2·10¹⁸ q* (𝔟+1)³` and `n = 3·10¹¹ (𝔟+1)³ + 2|Z_s| + |X_a|`, the supplied circuits linear and
outside the synthesis logarithm; at most `7864320 ḡ q*` calls of each selected matrix-oracle kind
plus `80 ḡ (Q_load + 2 Q_wp)`; and `7·10¹¹ (𝔟+1)³ + 4|Z_s| + 2|X_a|` qubits. The source executions
are counted on the annotated selective expansion (`binary_time_sel_sources`, annotation `sbAnnot`):
at most `80 ḡ` loadings and `160 ḡ` weight preparations in every history, the calls and gates the
propagation part (the compiled protocol with empty source circuits) plus the executions times the
supplied costs.

**Lemma `ode:lem:tags` for an arbitrary supported `K`** (`TaggedPairEntry`, `TaggedPairSimulation`;
handover item D4). `ODENativeCayley.program` computes the tagged entry of `K_k = H + kD` only. The
modules replace that scalar arithmetic by a public rule `f : n → n → ℂ → ℂ → ℂ`, the matrix being
`pairMatrix f G` with entry `f i j (G i j) (G j i)` (`K` computable from `G_ij`, `G_ji` and known
data); the original locators, the tag routing, the four value queries with their uncomputation and
the native control compilation are unchanged. `ode_lem_tags_rule`: for a rule with `f i j 0 0 = 0`
(so `K` vanishes outside `supp(G) ∪ supp(G†)`, `pairMatrix_support`) and `f j i v u = star (f i j u v)`
(so `K = K†`, `pairMatrix_isHermitian`) and row and column norms of `K` at most `ρ > 0`, the moment
bounds of `ode:eq:moments` with `p = 2s` hold at the known boundary, the action is the Cayley action
of `γ C₀`, the fixed program `ODETaggedPairEntry.program D f γ ρ` (`6` row, `6` column and `12`
value calls, chosen before the instance) implements it exactly on the clean encoding
`ODENativeCayley.clean D` (independent of the instance, of `f` and of `γ`, `ρ`), and its literal
adjoint implements the inverse at the same counts. `ode_lem_tags_rule_simulation` chooses one public
rescaling `γ` from `2s`, `ρ t` and `ε` for every admissible rule and gives the actual native program
for `exp(-i t K)` with full-output error `ε` and at most
`663552 (√(2s) ρ t + √(2s ρ t log(2/ε)) + log(2/ε))` original calls (the `72`-call active layer
`activeProgram`, `ODEFixedTaggedQuery.query_certificate` with its query hypothesis discharged).
`pairMatrix_lchsRule` and `program_lchsRule` identify `K_k` and the released circuit as the instance
`f = lchsRule k`. The rule is applied exactly in the gate table, like the LCHS entry; its arithmetic
cost is not counted (as for the released `K_k` circuit, whose counts are query counts).

**A writer on clean targets** (`WriterAccess`, `WriterProtocols`, `WriterEndpoints`,
`WriterProtocolEndpoints`; handover item B4). Section `hs:sec:control` lets the value oracle be any
reversible writer of the stored word into a clean target, with its supplied inverse.
`WriterAccess.writerOracles D W` has the supplied locators and a supplied unitary writer `W x` on
the address and target registers, specified only by `W x |a, 0⟩ = c x a |a, w_a⟩`
(`w_a = D.table x a`, any phases `c x a`) and arbitrary elsewhere. `circuits_intertwines`: writer,
a fixed adder of the scratch word into the value target, and the literal inverse writer, on one
extra scratch register, act on every state with a clean scratch register exactly as the additive
lookup and return the scratch register to its clean word (the phases cancel; arbitrary dirty value
targets and flags are allowed); the locator calls keep the scratch register as a spectator. The
converted workspace of each theorem is its released physical workspace with one more register
holding a value word (`single0`: the scratch register in its zero word); `Impl` records an
implementation of a family of calls on this encoding and passes through the fixed register layers
of the physical families (`Impl.fconj`, `Impl.fdiag`, `FImplH.masked`), every converted call being
a primitive call under one fixed unital star-algebra homomorphism `Φ`; further supplied calls (the
source preparations) act with the scratch register a spectator (`FImplH.extra`); measured
protocols are moved by compiling every circuit and encoding every seed and output isometry, with
the same Born probabilities, success mass and conditional output (`encodeProtocol_*`,
`encodeTree_*`). `hs_thm_main_writer`, `hs_thm_optimal_writer`, `hs_thm_two_norm_writer`: the
circuit of `hs_thm_main`, `hs_thm_optimal`, `hs_thm_two_norm` with every value call replaced is
fixed before the instance, makes exactly the locator calls of the released circuit and two writer
calls per value call (at most twice the calls, so the constants `2C`), acts as the released circuit
on the clean scratch register, and has the same full-output error, also with an untouched
reference. `qls_thm_main_writer`, `ode_thm_main_writer`: the protocols of `qls_thm_main` and
`ode_thm_main` so converted have the success probability and conditional output of the released
protocols on every instance (hence their guarantees), at most twice the worst-case matrix calls
(locator and writer calls) and the same worst-case source calls. `qls_cor_separate_writer`
(module `WriterSeparate`): the same for the protocol of `qls_cor_separate` over
`Separate.sepOracle`, conditional on `ext_separateSolver`, with the implementation of the
physical calls on the clean scratch register (`Impl`) and the converted protocol
(`encodeProtocol`) in the statement: constants `2 C_A` and `C_b`, both bounds on every completed
history, the preparation bound under the estimate promise. `ode_thm_time_writer` (module
`WriterTimeEndpoints`): the same for the protocol of `ode_thm_time` on time-indexed data, with a
writer `W (x, r)` for every sample and the time-indexed primitive calls `timeWriterOracles` (the
time address an input register of the locators and the writer); the coherent sampled-time query
reads a different instance in every branch of its label register, and its layer
(`Impl.flabel`, `FImplH.label`) maps the converted calls through the blockwise homomorphism
`ampHom` (`homOf_time`: the branch-dependent primitive calls are the time-indexed ones under a fixed
unital star-algebra homomorphism). `ode_thm_general_writer` (module `WriterGeneralEndpoint`): the
same for the protocol of `ode_thm_general` (the same reduced output); the Taylor history calls the
native block encoding on `K` fresh copies of its register, so the converted call on copy `i` is a
primitive call under a fixed homomorphism `Φ i` determined by the copy (`Impl.fhomL`, `powHom`),
and every other register layer is a homomorphism layer (`Impl.fhom`, `ampHom_single0`); the case
`T = 0` (`ode_thm_general_zero`, direct preparation of the initial state) likewise
(`ode_thm_general_zero_writer`, module `WriterGeneralZero`: no matrix query, no forcing call and at
most `40` calls of the initial-state preparation in every history). The
selected outputs of the trials are unchanged by the conversion, so the per-run properties transfer
(`trialsClose_encode`, `historiesClose_encode`; module `WriterTimeVariants`):
`ode_thm_time_actual_writer` adds `TrialsClose` and `HistoriesClose` for the converted trials of
`ode_thm_time_actual`, and every other endpoint over the same oracles (the branch-certificate forms)
converts through `fimplH_meshActual` and these lemmas. `ode_thm_time_approx_writer`: the same for
the approximate source preparations on clean work registers of `ode_thm_time_approx`
(`fimplH_workActual`: the matrix calls with the work register a spectator). Not covered: the other
ODE and linear-system endpoints (general-source, mesh-certificate); the ODE gate theorems are
converted for a writer at the gate level (below).

**A writer at the gate level** (`WriterGateAccess`, `WriterGates`, `WriterGatesDecoder`; handover
item B4). `GeneralSparseAccess.QData.Writer D`: a unitary `W x` on the edge register and the value
wires of the gate model, specified only on the clean inputs of the valid index pairs,
`W x |i, j, 0⟩ = c x i j |i, j, w_ij⟩` for `i, j < N` (`w_ij` the stored word of `D`, any phases),
arbitrary on invalid index words and dirty targets; `Writer.prims` has the supplied locators and the
writer (an inverse call is its literal adjoint). The padded value oracle of the general-size gate
theorems writes the stored word into a clean scratch register, copies it into the value wires
controlled by the validity flag of the pair (the public zero word otherwise) and uncomputes it
(`implVal`, two XOR calls); `implValW` has the same gates with the writer and its inverse in the
places of the two XOR calls (`implPW`: with the locator implementations of `implP`). On a valid pair
the phases cancel (`wmid_valid`); on an invalid pair the copy does not read the writer's wires and
the inverse call undoes the writer whatever it did (`wmid_invalid`), so no controlled access to the
writer and no routing of invalid index words to a valid address are needed; `implOKW`: on clean
ancillas the implementations act as the padded primitives. The four theorems
`hs_thm_gates_general_writer`, `gate_thm_main_general_writer` (binary decoder `c₀(X + iY)`, padded
data `padData`) and `hs_thm_gates_decoder_writer`, `gate_thm_main_decoder_writer` (any public
decoder; padded data `padDataEW`, the padded data `padDataE` with the all-zero word on invalid pairs,
which the validity decoder ignores: the same matrix, decoder, locators and arithmetic assumptions)
have the hypotheses, constants and bounds of `hs_thm_gates_general`, `gate_thm_main_general`,
`hs_thm_gates_decoder`, `gate_thm_main_decoder` (writer calls counted with the locator calls among
the primitive sparse queries); the circuit is fixed before the writer and the instance, and the
error clause holds for every writer with the specification. The general-size ODE gate solvers call
the padded oracles through the same implementation (`GeneralSparseODE.GPub.nd`, `GPubT.nd`), so
`GPub.prepW`, `GPubT.prepW` (the private operation through `implPW`; for time-dependent
coefficients the coherent sampled-time primitives `primsTGW Wr x` of a writer of every sample) give
`ode_thm_gates_general_writer`, `ode_thm_gates_time_general_writer`,
`ode_thm_gates_time_cert_writer` and `ode_thm_gates_time_cert_valid_writer` (modules
`WriterODEGates`, `WriterODETimeGates`, `WriterODECert`), with the constants, bounds and guarantees
of the released forms, the source circuits calling the primitives of the writer model, and the
source-execution forms `ode_thm_gates_general_sources_writer`,
`ode_thm_gates_time_general_sources_writer` (`WriterODESources`). The decoder forms of
`ode:thm:gates` call the padded oracles of the decoded data through the composite
`GeneralDecoderODE.implDP`, every decoded value call of the padded value oracle a supplied value
call into clean stored-word ancillas, the decoding, the copy of the decoded word, the decoding
backwards and a second supplied value call (`implDec`), which reads the stored word of every pair.
`implDPW` (module `WriterDecoderAccess`) has the inverse writer in the place of the second supplied
call: the same gates and kinds of calls (`nGatesN_implDPW_le`, `kindOK_implDPW`). A decoded value
call through the writer acts on a valid pair as the decoded XOR on any target (`decW_valid`) and is
an involution of the whole register (`decW_invol`); the two decoded calls of the padded value oracle
surround the copy masked by the validity flag, so on an invalid pair the second undoes the first
(`cmid_invalid`), and on clean ancillas `implDPW` acts as the padded oracles of the decoded data for
every writer with the specification (`implOK_implDPW`). This gives `ode_thm_gates_decoder_writer`,
`ode_thm_gates_time_decoder_writer` (module `WriterDecoderODE`; protocols
`GeneralDecoderODE.prepDW`, `prepTDW`), `ode_thm_gates_time_decoder_cert_writer`,
`ode_thm_gates_time_decoder_cert_valid_writer` (`WriterDecoderCert`) and the source-execution forms
`ode_thm_gates_decoder_sources_writer`, `ode_thm_gates_time_decoder_sources_writer`,
`ode_thm_gates_time_decoder_cert_sources_writer` and, for the certificate form with the decoder
`c₀(X + iY)`, `ode_thm_gates_time_cert_sources_writer` (`WriterDecoderSources`), with the hypotheses,
constants, bounds and guarantees of the released forms; the branch-certificate forms
`ode_thm_gates_time_cert_branch_writer`, `ode_thm_gates_time_decoder_cert_branch_writer`,
`ode_thm_gates_time_cert_valid_branch_writer`, `ode_thm_gates_time_decoder_cert_valid_branch_writer`
(`WriterBranchCerts`) follow from the writer certificate forms as the released ones from theirs
(`gate_budgets_of_branch`). The binary-format endpoints (`formal_binaryInput`), the finite-gate-set
form `ode_thm_gates_time_cert_finite` keep the XOR value oracle. The `tiny`, `tables` and
`of_decoder` variants of the Hamiltonian gate theorems apply the writer forms as the released ones
apply theirs (`hs_thm_gates_decoder_tiny_writer`, `gate_thm_main_decoder_tiny_writer`,
`hs_thm_gates_decoder_tables_writer`, `gate_thm_main_decoder_tables_writer`,
`hs_thm_gates_general_of_decoder_writer`, `gate_thm_main_general_of_decoder_writer`; module
`WriterGateVariants`; a writer of `D` is a writer of the thresholded data `D.dropTiny small`,
`QData.Writer.dropTiny`).

**The column of the preparation** (`PrepColumn`; handover item D1, the amplification part). The
trials of the native four-attempt protocol `GateNative.nprotocol` are the preparation followed by
amplification steps with its literal inverse; on the clean reflection wire they are the actual
Grover trials of the preparation, which depend on it only through its column on the seed
(`U (1 - 2|sN⟩⟨sN|) U† = 1 - 2|U sN⟩⟨U sN|`). So two native preparations, unitary and preserving
the clean reflection wire, with the same column have the same trial outputs
(`GateNative.trialN_seed_congr`), the same success mass and conditional output
(`GateNative.nprotocol_law_congr`, from `ODERepeatProtocol.fourTrials_law_congr`), and the released
guarantee `WOutcome` and `HeraldedOutput` transfer between them
(`SourceAccuracyODE.WOutcome.of_column`, `heraldedOutput_of_column`), for any primitives and
circuits. For the time-dependent native preparations (module `PrepLoader`; the logical preparation
`Wp · LCHS · LOAD · SELECT · PHASE · LCHS⁻¹ · Wp⁻¹`, in the zero case `Wp · LOAD · Wp⁻¹`) the column
depends on the loading circuit only through its label columns `|c⟩|0⟩_S|0⟩_{Zs}`, the loading call
being the only one and acting after the weight preparation and the rotation tree, when the weight
preparation leaves its scratch clean on the clean input (`hwp`; `wpScratch_of_exact`, the exact
case of the released source hypothesis): `tnprepC_column_congr`, `tzprepC_column_congr`,
`GeneralSparseODE.GPubT.prep_column_congr`, `GeneralDecoderODE.prepTI_column_congr`. So the
released guarantee `WOutcome` of a loading circuit holds for every valid loading circuit with the
same label columns (`GPubT.wOutcome_of_loader_columns`, `prepTI_wOutcome_of_loader_columns`,
`SourceAccuracyODE.WOutcome.of_loader_columns`), in the exact case of D1. Approximate weight
preparations and completions and the constant-coefficient preparation (two controlled source calls
in sequence, the second acting on the output of the first) are not covered, and the loading
hypotheses of the endpoints (label-controlled loaders on clean work) are unchanged. For the
uniform-mesh general-source solver `GeneralSourceODE.solver` (`ode:thm:time` with the source
interface; module `SourceLoaderColumns`) the loading oracle may be any unitary `Lo` on the whole
branch register (source label, LCHS label and data), specified only on the clean columns
`|a, τ⟩|seed⟩` of the labels with nonzero source vectors (`Lo |a, τ⟩|seed⟩ = |a, τ⟩|x(0)/‖x(0)‖⟩`,
resp. `|a, τ⟩|b(v_i)/‖b(v_i)‖⟩`, the phases of the released convention) and not assumed to preserve
the labels elsewhere: `GeneralSourceODE.solver_columns` (`OutcomeColumns`) gives the guarantee of
`GeneralSourceODE.Outcome` (success at least `2/3`, conditional trace distance at most `ε`, the same
matrix-query bound and at most `40 g'` calls of each of `P_w`, `Lo` and `P_w†`, inverse calls
included) for one public trial family over `P_w`, `Lo`, `P_w†`. The trials call `Lo` and its
inverse; after `P_w` the seed branch state is a combination of clean columns of positive weight
(`Weights.act_seedInput`, `Weights.clean_congr`), and the trials depend on the preparation only
through its seed column (`Compiled.program_seed_congr`, `Compiled.amplified_seed_congr`,
`Native.publicTrialsS_seed_congr`), so the certificate of the released proof for a label-controlled
family with the same columns transfers (`Oracles.columns_certificate`,
`propagated_solver_public`). The same holds on a public mesh with breakpoints, the clock on `N`
slots and the integrated sample error (module `MeshLoaderColumns`):
`GeneralSourceExtensions.Mesh.mesh_solver_columns` (`MeshOutcomeColumns`, the guarantee of
`Mesh.mesh_solver`) and, for continuous pieces with the certificate on the propagated vector
integral, `mesh_solver_integral_columns` (that of `Mesh.mesh_solver_integral`), through
`MeshOracles.columns_certificate` and `Mesh.mesh_propagated_solver_public`; and with represented
samples of any sign (module `RobustLoaderColumns`):
`RepresentedSampleODE.robust_mesh_solver_columns` and `robust_solver_integral_columns` (the
guarantees of `robust_mesh_solver` and `robust_solver_integral`, through
`robust_propagated_solver_public`). For the full-class Dyson solver of `odel:lem:dyson` (module
`DysonLoaderColumns`), `DysonFullClass.full_dyson_columns` (`FullValidColumns`, `fullOracleL`) gives
the released complete certificate of `full_dyson` (cutoff `chosenIterations g'`, `g' = c_q ḡ e^z`,
shape `K/589824`, accuracy `ε`) for one public trial family over the native calls of the original
access and the counted interfaces with `Lo`: the compiled amplified trials depend on the interfaces
only through the seed column, with the same counts (`compiledTrials_seed_congr`,
`trialCertificate_of_seed`), so the certificate of the released proof for the label-controlled
family `columnLoader Lo` transfers (`herald_certificate_columns`). With the amplification shape
(`full_dyson_shape_columns`, from `compiledTrials_shape`), the single-program and separate-primitive
forms follow as in the released proofs (module `DysonLoaderActual`): `full_single_columns`
(`FullSingleOutcomeColumns`: one heralded program with at most `dysonBound z (c_q ḡ) ε` matrix
queries and at most `40 g'` calls of each counted interface) and `full_actual_columns`
(`ActualCertificate` of the four-attempt protocol over the separate primitives `P_w`, `Lo`, `P_w†`,
with at most `40 g'` calls of each). For the conformance theorem of `ode:thm:time` (module
`TimeLoaderColumns`; it is built on the approximate-preparation solver with `δ = 0`), the zero cores
of the represented-sample solver (`RepresentedSampleODE.robust_zero_core_public`, from
`mesh_zero_time_core_public` and `mesh_zero_generator_core_public`) and its propagated core have the
same public trial family, so the column transfer applies for every `T ≥ 0`
(`RobustPublicOutcome.columns`, `robust_solver_nonneg_columns`). With integrable pieces, mild
solutions and the sampling budgets of `ode:thm:time` (`robust_solver_nonneg_regular_columns`,
`RegularOutcomeColumns`) this gives `ode_thm_time_columns`: the statement of `ode_thm_time` for the
protocol over `P_w`, `Lo`, `P_w†`, with the same constant. The accuracy of every actual successful
trial and history (`TrialsClose`, `HistoriesClose`) holds for the same protocol (module
`TimeLoaderRuns`: `ode_thm_time_actual_columns`, the statement of `ode_thm_time_actual`): the trials
agree with those of the label-controlled family on the public seed
(`MeshOracles.columns_seed_eval`), and `TrialsClose` depends only on the outputs on the seed
(`trialsClose_congr_seed`, `MeshOracles.columns_trialsClose`). The branch-certificate forms follow
from these as the released ones do (module `TimeLoaderBranch`: `ode_thm_time_branch_columns`,
`ode_thm_time_actual_branch_columns`). Approximate completions are stable (module `LoaderApprox`):
the `j`-th amplified trial moves by at most `(4j + 1) δ` when the prepared vector moves by `δ`
(`ODEGroverActual.trial_sub_le`), and the four-attempt protocol uses its trials only on the seed
(`perturbed_four_seed`, `approx_certificate_seed`). So a unitary loader `Lo` within `δ` of `loader
J` on the seed branch state after `P_w`, and arbitrary elsewhere, keeps the guarantee of the public
mesh trial family of `J`: success at least `2/3`, conditional trace distance at most `ε` and the
released counts, under `20 g δ ≤ 1/400` and `20 g δ ≤ ε/20`
(`MeshOracles.columns_approx_certificate`, through `Compiled.program_seed_dev` and
`MeshNative.publicTrialsS_seed_dev`). With a label-controlled reference `J` fixed with the public
data (not implemented) and `Lo` within `δ` of `loader J` on the clean subspace
(`Weights.CleanClose`), this gives the endpoint
`RepresentedSampleODE.robust_solver_nonneg_regular_columns_approx` and the conformance theorem
`ode_thm_time_columns_approx` (module `TimeLoaderApprox`), under `40 c_q ḡ δ ≤ min(1/400, ε/20)`.
Its branch-certificate form is `ode_thm_time_branch_columns_approx` (module
`TimeLoaderBranchApprox`). The approximate-preparation forms (`ode_thm_time_approx`,
`ode_thm_time_approx_branch`, the forms on temporary work registers and
`DysonFullClass.full_approx`) keep the label-controlled loader.

**External results** (theorem parameters, not reproved): `ext_singleQubitSynthesis`,
`ext_singleQubitLength` (single-qubit synthesis of length `O(log(1/ζ))`, Ref. KMM2013),
`ext_controlDecomposition` (exact decomposition of the controlled one-qubit gates),
`ext_blockSolver` (the block-input linear-system solver of the proof of `ode:thm:general`), and
`ext_separateSolver` (the solver of Gao, Ji and Liu with separate matrix and preparation query
bounds, `SparseLinearSystems.Separate.SeparateSolver`, used by `qls:cor:separate`).

**Computational assumptions** (Section `gate:sec:result`): `comp_bits` (the stored components have
at most `b_data` bits and the listed public parameters have `b_data`-bit fixed-point descriptions,
`GateBitBudget.HasBits`), `comp_signedArith`, `comp_clipArith` (polynomial-cost reversible
scalar arithmetic of the signed-factor and clipped constructions of `gate:thm:main`, at the public
scales of the construction: for `gate_thm_main_general` those of the construction on the padded
data, `genClipBeta`, `genClipScale`); for general decoders (`GateDecoder`, `GateMainDecoder`), the
arithmetic of the decoder on the value word, `comp_rotArith` (at the rescalings
`κ ∈ [1/η, √(2s)/η]`), `comp_signedArithV`, `comp_clipArithV` (met for every decoder by lookup
tables, `GateDecoderTables`, and implied for the decoder `c₀(X + iY)` by the hypotheses of the
general-size theorems, `GateDecoderBinary`), and on the base wires of the native operations for the
decoder of the data, `comp_decArith`, `comp_signedArithD`, `comp_clipArithD` (which follow for the
padded data from the assumptions on the value word: `comp_decArith_padDataE`,
`comp_signedArithD_padDataE`, `comp_clipArithD_padDataE`).

**Conclusion forms and coverage.** Review item D: the time-dependent general-source endpoints give
the heralded mixed-output guarantee (`HeraldedOutput`). For exact source preparations
`ode_thm_time_actual` adds, for the same protocol and counts, the accuracy of every actual
successful trial and history (`TrialsClose`, `HistoriesClose`), as `ode_thm_main_actual` does for
`ode:thm:main`; `RunsClose` (a decomposition of the conditional density) does not express it
(`runsClose_diagnostic`). For approximate source preparations a rare successful branch may be
inaccurate while the conditional state is accurate, so the
statement for every successful run does not hold; `ode_thm_time_approx_runs` (module `ApproxRuns`)
gives for the protocol of `ode_thm_time_approx` the history-resolved form that does: the
conditional output is the ensemble of the actual successful histories, every trial whose success
probability is at least `p₀ > η²` (`η = 60 c_q ḡ δ`, the per-trial perturbation of the released
proof) has direction error at most `ε/500 + 2 η/√p₀` up to a phase, and the other histories carry
conditional weight at most `6 p₀` (`lowWeight_le`). Review item F: the package's finite-gate-set synthesis
(`GateSynth.synthBudget`) multiplies every native gate, those of supplied source circuits and of
native private calls included, by the synthesis length, where the manuscript's `G_src(ν)` and
`G_P(ξ)` are already finite-set counts; `ode_thm_gates`, `ode_thm_gates_time`,
`ode_thm_gates_general`, `ode_thm_gates_time_general`, `ode_thm_gates_decoder`,
`ode_thm_gates_time_decoder`, `ode_thm_gates_time_cert`, `ode_thm_gates_time_decoder_cert`,
`gate_prop_finite`,
`gate_prop_signed_native` and `gate_prop_core_native` are therefore stated in the native gate model
(arbitrary single-qubit gates), where no synthesis term arises. The finite-set forms of the three
Appendix D propositions with the supplied subcircuit charged at its actual linear cost are
`gate_prop_finite_sel`, `gate_prop_signed_sel` and `gate_prop_core_sel` (item B3, module
`GatePropsSelective`: the generic transfers `sel_transfer` for sector-controlled circuits and
`sel_signed_transfer` for unconditional factor calls, with the supplied private or factor circuit
retained, its inverse its literal reverse-adjoint, its work wires reused, and only the remaining
exact gates synthesised), with the native data compiled selectively once in
`gate_prop_finite_sel_native`, `gate_prop_signed_sel_native` and `gate_prop_core_sel_native`. Finite-set forms of Theorem
`ode:thm:gates` hold only under this package's format hypotheses (native data:
`GateSynth.native_ode_solver_synth`, `GateSynth.native_ode_time_solver_synth`; the binary format
`N = 2^{k_x}`, `s = 2^σ`, decoder `c₀(X + iY)`, with `T > 0`, `η_H + η_D > 0`, and `G_src` linear:
`GateSelective.binary_ode_budget_sel`, `GateSelective.binary_ode_time_budget_sel`); for the
time-dependent theorem on time-indexed binary data, `ode_thm_gates_time_cert_finite` (below) gives
the finite-gate-set form under the certificates, with the supplied circuits retained verbatim. The
general accounting of
`hs:thm:gates` for arbitrary implementations of the private operation is proved in the package
only for an abstract operation given by its clock promises
(`GateCircuit.Sim.gate_efficient_simulation`; over a finite gate set, with a supplied private
circuit, `GateSchedule.sel_simulation_ms` and `GateSchedule.sel_simulation_ms_signed`; on sparse
access of general size with any public decoder, `SparseGateAccounting.sparse_gate_total`, with
`s' = 2^⌈log₂ s⌉` in place of `s` and the supplied circuit a hypothesis; with the circuit
constructed from the decoder's angle arithmetic and its promise derived,
`SparseGateAccounting.sparse_gate_constructed`; with the original `s` in the schedule for a supplied
boundary circuit of the `s` original slots, `SparseGateAccounting.sparse_gate_original`). `hs_thm_gates_decoder`
takes the native route (`GeneralDecoder.binary_simulationD`) and gives eq. `hs:eq:gate-binary`,
without the work-qubit count of eq. `hs:eq:gate-total`.
Review item H: the factor interface of `gate_prop_signed` and `gate_prop_signed_native` is the
wire-defined `wKnown` (success projection and sign reflection on qubits of the factor's ancillas,
the form of the stable local factor of Section `gate:sec:native`), where Section `gate:sec:signed`
allows any known projection `Π` and reflection `Z`; `gate_prop_signed_native` takes the native
factor in the package's compute–local-factor–uncompute form. A general known `Π` and `Z` reach
these circuits through a conversion (module `GatePropsKnown`): a unitary `C` of the ancilla space
with `C E = U_J ι₀`, `C Π C† = [wire f = 1]` and `C Z C† = (-1)^{wire z}` (`Converts`) leaves the
signed compression, the weight and the Hamiltonian unchanged (`ham_conj`, `Converts.ham`), so
`gate_prop_signed_known` and `gate_prop_signed_known_sel` simulate `exp(-i t λ C_K)` of the general
interface; `gate_prop_signed_known_conv` builds the conversion from supplied gates (`Eg` preparing
the initialised input, `Cg` over `𝒢` converting) and charges it: `U_C† · fc · U_C` per factor call
(`convFactor_approx`, `n_P (|fc| + 2 |Cg|)` retained gates) and `C_J = |Eg| + |Cg|` boundary gates.
The synthesis of `Eg` and `Cg` from a description of `Π` and `Z` is not formalised. Review item I: `gate_prop_finite`
requires every oracle call, boundary calls included, to be controlled by the sector wire (`SecOK`)
and the private operation to be a native operation of the package's compute–rotate–uncompute form
with its public conditions (`NativeOp.Public`, `NativeOK`, `ArithOK`): the form of the
bounded-regime circuit. The signed circuit, whose factor calls are unconditional, and the clipped
circuit, whose private operation is factor-conjugated (`D = U_f† C U_f`, Section
`gate:sec:native`), have their own native forms, `gate_prop_signed_native` and
`gate_prop_core_native`. The circuits of `gate_prop_signed` and `gate_prop_core` use exact rotations
with the real weights of the query proof; the rounded coefficients of eq. `gate:eq:round` and the
rounded coefficient preparation of the remark after Theorem `opt:thm:signed` are not formalised.
Review item K: the gate-level ODE theorems take the source preparations as
supplied native circuits that may call only the matrix primitives; the native model has no
separate source-preparation oracle, so one protocol serves the instances whose sources the supplied
circuits prepare, and the manuscript's supplied source-preparation calls (before Theorem
`ode:thm:gates`) are not modelled as oracle calls. Their number is the number of executions of
the supplied circuits, counted on the annotated macro expansion of the protocol
(`SourceExecutions`: `ode_thm_gates_sources`, `ode_thm_gates_decoder_sources`,
`ode_thm_gates_time_cert_sources`, `ode_thm_gates_time_decoder_cert_sources`;
`SourceExecutionsMore`: `ode_thm_gates_general_sources`, `ode_thm_gates_time_sources`,
`ode_thm_gates_time_general_sources`, `ode_thm_gates_time_decoder_sources`).

**Conditions stated explicitly.** `ode_thm_time` assumes `1 ≤ ḡ` (on a dissipative path
`‖x(T)‖ ≤ B`, as in the remark `g ≥ 1` after Theorem `ode:thm:main`) and `1 ≤ c_q` (harmless up to
absolute constants: for `c_q < 1` the theorem applies with `c_q = 1`, the mass condition being
monotone in `c_q`, with a certificate budget finer by the factor `c_q`); `ode_thm_general` assumes
`1 ≤ C̄` and `1 ≤ ḡ_path` (`C_A ≥ 1` and `g_path ≥ 1` by their definitions before Theorem
`ode:thm:general`). The conditions on `ḡ`, `C̄` and `ḡ_path` hold for every admissible instance.

## Strengthened statements

* **Actual runs** (`ActualRuns`). `TrialsClose t x target ε`: every trial of the public trial
  family `t` whose amplitude is nonzero outputs a unit vector within Euclidean distance `ε` of
  `target` up to a global phase; `HistoriesClose`: the conditional density of the four-attempt
  protocol is the ensemble of the actual trial outputs with the first-success weights, and every
  successful history of positive weight has nonzero amplitude and output within `ε`.
  `ode_thm_main_actual` (`ode:thm:main`) and `ode_thm_time_actual` (`ode:thm:time`, exact source
  preparations, zero time and a known zero generator included) state them for the trial family of
  the same protocol, with the success, trace-distance and count conclusions of `ode_thm_main` and
  `ode_thm_time`. `runsClose_diagnostic`: `diag(0.99, 0.01)` satisfies `RunsClose` for
  `|0⟩` and `ε = 1/5` through an alternative decomposition, while its branch `|1⟩` of positive
  weight is not within `1/5` of `|0⟩` up to any phase. Not extended to approximate preparations.
* **Branch certificates** (`BranchCertificates`). For the same represented samples `G̃` on the same
  mesh and `k > 0`: `ΔH = (ΔK₊ + ΔK₋)/2`, `ΔD = (ΔK₊ - ΔK₋)/(2k)`, `E_D ≤ (E₊ + E₋)/(2k)` and
  `E_G ≤ (1 + 1/k)(E₊ + E₋)/2` (no commutation or positivity; nonuniform meshes), composed into
  `ode_thm_time`, `ode_thm_time_approx`, `ode_thm_time_actual` (keeping the refinement error), the
  four time-dependent gate certificate endpoints (at the selected `k` and the formal solver's
  radius, with the constants documented in the module), and the coverage of `DysonFullClass`
  (raw and clipped routes); a non-accretive represented sample is accepted
  (`nonaccretive_branch_accepted`).
* **Source executions** (`SourceExecutions`). The native preparations are macro expansions of
  labelled released programs; the annotated expansion (`constAnnot`, `constAnnotI`, `timeAnnot`)
  evaluates to the same flattened native preparation and trials and records every execution of a
  supplied source circuit or its literal inverse. Along every history of the protocols of
  `ode_thm_gates`, `ode_thm_gates_decoder`, `ode_thm_gates_time_cert` and
  `ode_thm_gates_time_decoder_cert`: the source executions (at most `40 ḡ` of each circuit, resp.
  `160 ḡ` loadings and `320 ḡ` weight preparations), the calls as propagation calls (at most
  `C ḡ q`, zero in the zero case) plus the executions times the calls of each circuit, the total
  calls, and the gates as propagation gates plus the executions times the gates of each circuit
  (`ode_thm_gates_sources`, `ode_thm_gates_decoder_sources`, `ode_thm_gates_time_cert_sources`,
  `ode_thm_gates_time_decoder_cert_sources`). The same for the four other native gate endpoints
  (`SourceExecutionsMore`, annotations `constAnnotI`, `btimeAnnot` for the uniform-mesh
  preparation `btprepC`, and `timeAnnot`): `ode_thm_gates_general_sources` (at most `40 ḡ`
  executions of each circuit), `ode_thm_gates_time_sources`, `ode_thm_gates_time_general_sources`
  and `ode_thm_gates_time_decoder_sources` (protocol parameter `2ḡ`: at most `80 ḡ` loadings and
  `160 ḡ` weight preparations).
* **Finite gate set under the certificates** (`GateODETimeCertFinite`).
  `ode_thm_gates_time_cert_finite`: the finite-set protocol of
  `GateSelective.binary_ode_time_budget_sel` (selective compiler, supplied circuits over the gate
  set retained verbatim, exact zero tests in the gate set, literal reverse-adjoint) has the
  guarantees of `ode:thm:gates` under the certificate-form conditions `CertRest` for time-indexed
  binary data, derived from the certificate of the actual compiled preparation, with its gates,
  calls, qubits and source executions (at most `80 ḡ` loadings and `160 ḡ` weight preparations);
  the selective annotation `selAnnot` carries the source tags through the compiler
  (`aflat_selAnnot`, `nexec_selAnnot`, `aerase_selAnnot`, `nSynN_aflat_aerase`).
* **Sparse Cayley representation** (`EntrywiseCayley`). `qls_lem_entry`: Lemma `qls:lem:entry`
  for every Hermitian `s`-sparse `H` with `‖H‖ ≤ 1`, bundled from the arbitrary-`H` constructions
  of `SparseHamiltonian.FixedNativeCayleySimulation` and `SparseHamiltonian.NativeCayleyProgram`:
  the input-independent isometry `J` (no matrix query), the self-adjoint generator `K` with
  `J† K J = H/√s`, `J† K² J ≤ 1` and `‖K‖ ≤ √s` (the row and column energies derived from the
  spectral bound, `energies_of_norm_le_one`), and for every real `γ` the Cayley unitary
  `(γK + i)(γK - i)⁻¹` with an explicit two-sided inverse of `γK - i`, implemented on a fixed
  clean encoding by an eighteen-query native program and its inverse by the literal adjoint
  program (`6` calls of each sparse primitive).
* **Centred averaging** (`ChebyshevLinearSystemFinite.CentredAveraging`, Remark
  `qls:rem:averaging` and the comparison of Remark `qls:rem:constants`). For a polynomial `f` of
  degree at most `d` with nonnegative coefficients summing to one, `W^{-⌊d/2⌋} f(W)` has the error
  relative to `P` and the selected norm of `f(W)` and is the exact success block of the released
  signed-step run of `⌈d/2⌉` steps with an explicit coefficient seed (`54` matrix-oracle and `2`
  source calls per step, its literal adjoint program the adjoint); composed with the step counts,
  the Chebyshev test and final runs make fewer than `1/1400` of the calls of the forward
  conservative averaging runs of `q_av` and `k q_av` steps, and the same holds for the prescribed
  budgets with the numbers of tests and attempts fixed; the centred averaging counts are compared
  separately (`700 d^fin_σ(1/100) < ⌈q_av/2⌉`, `centred_test_ratio`, and
  `700 d^fin_σ(δ) < ⌈k q_av/2⌉`, `centred_final_ratio`; derived here, not claims of the
  manuscript).
* **Direct audits.** `SparseHamiltonian.ControlledLookup.controlled_two_queries`, its clean
  correctness theorems `circuit_clean` and `circuit_clean_apply`, and
  `SparseHamiltonian.NativeControlledOracle.three_query_control`, `three_query_inverse_control`
  and `certificate` have guarded audits in `SparseHamiltonian/Audit.lean`, with the axiom reports
  determined by compiling (Lemma `access:lem:control`).
-/
