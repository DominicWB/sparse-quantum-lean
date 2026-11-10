import ChebyshevLinearSystemFinite.Alloc
import ChebyshevLinearSystemFinite.CentredAveraging

set_option autoImplicit false

/-!
# Theorem `qls:thm:main` with finite gates and explicit constants: paper-to-Lean entry point

Theorem 8.1 (`qls:thm:main`) of the accompanying paper with the finite-gate allowance of the
paragraph "Finite-gate accuracy" of Section `part:qls` (equations `qls:eq:finitedegree` and
`qls:eq:bernoulli` and the allocation paragraph after it), and the explicit constants of Remark
`qls:rem:constants` (equation `qls:eq:testconstant`). The released exact-gate proof
`ChebyshevLinearSystem.main` (library `ChebyshevLinearSystem`) is unchanged. The endpoints are
`main_amp`, `main`, `main_uniform`, `main_uniform_sharp`, `main_alloc`, `main_exact`,
`main_improved` and `main_improved_exists` (`ChebyshevLinearSystemFinite/Main.lean`,
`ChebyshevLinearSystemFinite/Alloc.lean`). No result from another paper is used. Unqualified names
below are in the namespace `ChebyshevLinearSystemFinite`; `Endpoint`, `Step`, `Protocol` and
`LogicalWalk` refer to the namespaces `SparseLinearSystems.*` of the released library and
`Estimator` to `SparseLinearSystems.Protocol.Estimator`; `MultiOracleCircuit`, `OracleCircuit`,
`EncodedLabeledProgram`, `NativeSparseBlockEncoding` and `ODEMixedOutput` refer to
`SparseHamiltonian.*`, and `ChebyshevLinearSystem`, `ChebyshevFilter` to the released libraries of
these names. References to the manuscript use its labels.

**Access model and promise.** Those of `ChebyshevLinearSystem.main`:
`D : NativeSparseBlockEncoding.Data X n Z s` (an `s`-sparse `A_x` for every unknown input,
exact finite-word entries, padded injective in-place locators with full unitary extensions),
the state preparation `Ub x` with public reference state `sv`, the physical oracle family
`Step.physOracle D Ub T` (the three native primitives and the controlled `U_b`), the weights
`Step.wMat` and `Step.wSrc` (every call counted, inverse calls included), and the promise
`Endpoint.Promise D κ x` (`‖A_x‖ ≤ 1`, `A_x` invertible, `‖A_x⁻¹‖ ≤ κ`), with `κ ≥ 1`,
unitary `U_b` and `‖sv‖ = 1`. Public instance-independent gates are free.

**The finite-degree protocol** (`Algorithm.lean`, `Degree.lean`). The released Chebyshev
protocol with the degrees of equation `qls:eq:finitedegree`, `d^fin_ξ(δ) = d_ξ(δ) + 1`
(`finDegree`):

* a test of candidate `r` at stage `j` (`testRunF`): the LCU circuit of
  `d^fin_j = d_{σ_j}(1/100) + 1` signed walk steps (`dTestF`) of the filter at
  `b(σ_j)`, seed `ψ ⊗ J e`, coefficient flag;
* a final attempt at the estimate `r` (`finalRunF`, a `Protocol.TestRun` whose flag is the
  output isometry): `d^fin_fin = d_0(ε/1000) + 1` signed steps (`dFinF`) at `σ = 0`, the filter
  at `b(1/κ)`;
* one counter register of `T + 1` values, `T = 2 (d^fin_fin + Σ_{j ≤ m} d^fin_j)` (`TcF`).

`implAlgorithm κ ε test fin` is the released classical control (`Estimator.algorithm`: the
`m = ⌈log₂ ⌈κ⌉⌉` stages, five candidates, `n_j = ⌈4 log(2/ζ_j)/t²⌉` fresh runs per candidate,
the thresholds and the clipping) run with the implemented tests `test j r` and at most `1000`
fresh implemented final attempts `fin r` (`repeatLeaf`). `algorithmF` is the protocol with the
ideal runs (exact gates).

**The model of approximate known gates** (`GateApprox.lean`, `Runs.lean`).

* `GateApprox p q e` for programs `p q : MultiOracleCircuit.Program O`: `q` makes exactly the
  oracle calls of `p` (same labels, directions and order); every fixed gate `U` of `p` is
  replaced by an arbitrary query-free program (a finite circuit of known unitary gates) whose
  unitary is within `e_U` of `U` in operator norm; `e` bounds the sum of the `e_U`. Then
  `‖q(x) - p(x)‖ ≤ e` for every input (`GateApprox.eval_sub_le`, telescoping) and the weighted
  costs agree for every weighting (`GateApprox.cost_eq`).
* `RunApprox t t' e` for runs `t t' : Protocol.TestRun O F` (circuit, unit seed, flag
  isometry): the circuit of `t'` is a `GateApprox` of that of `t` within `e_C`, the seed within
  `e_ψ`, the flag within `e_F` (operator norm), `e_C + e_ψ + e_F ≤ e`. Then the unnormalised
  success vectors `F† C_x ψ` (`amp`) differ by at most `e` (`RunApprox.amp_sub_le`), so `e`
  bounds the manuscript's `e`, and the success probabilities differ by at most `2e`
  (`RunApprox.probability_sub_le`).
* `AmpApprox P t t' e`, the manuscript's hypothesis itself: `t'` has the weighted cost of `t`
  for every weighting of the labels (`AmpApprox.cost_eq`), and on every input satisfying `P`
  the success vectors differ by at most `e` (`AmpApprox.amp_sub_le`), so the success
  probabilities differ there by at most `2e` (`AmpApprox.probability_sub_le`, from
  `probability_sub_le_of_amp`). Nothing is assumed about how the known gates, the seed or the
  flag are approximated. `RunApprox.ampApprox`: a `RunApprox` within `e` is an `AmpApprox`
  within `e` for every `P`.

**Accuracy requirements** (`Degree.lean`), with `δ₀ = sech(2 d^fin artanh b)` (`delta0`, the
residual amplitude `resid` at the finite degree; `delta0_le`: `δ₀ ≤ δ/(1 + 2χ²) < δ`;
`delta0_le_sharp`: `δ₀ ≤ δ/(1 + 2(1 - δ)χ)`, from `resid_succ_le_sharp`):

* tests: `e_test(s, j) = (δ² - δ₀(σ_j)²)/2` at `δ = 1/100` (`eTest`), with
  `eTest s j ≥ 1/(9·10⁶ s 4^j)` (`eTest_ge`), `eTest s j ≥ 1/(825000 √s 2^j)`
  (`eTest_ge_sharp`), `eTest s (Endpoint.stageOf κ j) ≥ 1/(3.6·10⁷ s κ²)` (`eTest_ge_uniform`)
  and `eTest s (Endpoint.stageOf κ j) ≥ 1/(1.65·10⁶ √s κ)` (`eTest_ge_uniform_sharp`);
* final attempts: `e_fin(s, κ, ε) = δ - δ₀` at `δ = ε/1000`, gap `1/κ` (`eFin`), with
  `eFin s κ ε ≥ ε/(9·10⁵ s κ²)` (`eFin_ge`) and `eFin s κ ε ≥ ε/(41250 √s κ)`
  (`eFin_ge_sharp`).

**Guarantees** (for `0 < ε ≤ 1/10`; all constants explicit absolute numbers, no logarithm of
`s` or `κ`, no extra power of `log(1/ε)`):

* `main_amp` (the manuscript's hypothesis): for all
  `test : ℕ → ℝ → Protocol.TestRun (Step.physOracle D Ub (TcF s κ ε)) (LogicalWalk.PrivO n)`
  and `fin : ℝ → Protocol.TestRun (Step.physOracle D Ub (TcF s κ ε)) (EuclideanSpace ℂ n)`
  with, for `P = Endpoint.Promise D κ`,
  `∀ j r, AmpApprox P (testRunF D Ub sv κ ε j r) (test j r) (eTest s (Endpoint.stageOf κ j))`
  and `∀ r, AmpApprox P (finalRunF D Ub sv κ ε r) (fin r) (eFin s κ ε)` (only the tests of the
  stages `1, …, m` are ever run): every transcript of
  `implAlgorithm κ ε test fin` makes at most `2.7·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and
  `10⁹ √s κ log(1/ε)` calls of the controlled `U_b` or its inverse (`27 * 10 ^ 9`, `10 ^ 9` in
  Lean); for every input satisfying the promise every run is unitary, the heralded success
  probability is at least `2/3`, and the conditional output is a density operator within trace
  distance `ε` (`ODEMixedOutput.hermitianTraceDistance`) of `|x⟩⟨x|`,
  `|x⟩ = A⁻¹ b/‖A⁻¹ b‖` (`Endpoint.solutionState`).
* `main`: the conclusions of `main_amp` for all `test` and `fin` with
  `∀ j r, RunApprox (testRunF D Ub sv κ ε j r) (test j r) (eTest s (Endpoint.stageOf κ j))`
  and `∀ r, RunApprox (finalRunF D Ub sv κ ε r) (fin r) (eFin s κ ε)`: the special case of
  `main_amp` in which the error budget is split into the approximate known gates, the seed and
  the flag (`RunApprox.ampApprox`).
* `main_uniform`: the conclusions of `main` with the requirements `1/(3.6·10⁷ s κ²)` for every
  test and `ε/(9·10⁵ s κ²)` for every final attempt; `main_uniform_sharp`: with the sharper
  requirements `1/(1.65·10⁶ √s κ)` and `ε/(41250 √s κ)` (`165 * 10 ^ 4`, `41250` in Lean).
* `main_alloc` (the manuscript's allocation): for one implementation `st` of the signed steps,
  `GateApprox (ChebyshevLinearSystem.signedStepProg D Ub sv (TcF s κ ε) l) (st l) ρ` for every
  signed label `l`, with `ρ ≤ ε/(10¹⁰ s √s κ³ log(1/ε))`, and coefficient preparations `St j`
  (stage `j`) and `Sf` (final), isometries within `η ≤ ε/(10⁷ s κ²)` of the ideal coefficient
  seeds `ChebyshevLinearSystem.seedT` and unprepared by their adjoints (the walk seed `J e`, the
  clean encoding and the output isometry exact): the conclusions of `main` for
  `allocAlgorithm D Ub sv κ ε st St hSt Sf hSf`.
* `main_exact`: the conclusions of `main` for `algorithmF` (exact gates, finite degrees).
* `main_improved`: the released exact-gate algorithm `ChebyshevLinearSystem.algorithm` with
  at most `2.7·10¹⁰ √s κ log(1/ε)` matrix-oracle and `10⁹ √s κ log(1/ε)` source calls
  (released `ChebyshevLinearSystem.main`: `4.4·10¹⁰`, `1.7·10⁹`) and the released guarantees;
  `main_improved_exists`: its existential form (one register size and one protocol, chosen
  before every unknown input).

**Remark `qls:rem:constants`** (`Constants.lean`), with `y = g/√s ∈ (0, 1]`,
`h₀ = arcosh 100`:

* `finDegree_hundred_le`: `d^fin_σ(1/100) ≤ ((h₀/2) √((165/4)² + 1) + 2)/y` (equation
  `qls:eq:testconstant`, via `arsinh u ≥ u/√(1 + u²)`, `div_sqrt_le_arsinh_chi`);
  `testconstant_lt`: `(h₀/2) √((165/4)² + 1) + 2 < 112`; `finDegree_hundred_lt`:
  `d^fin_σ(1/100) < 112/y`;
* `finDegree_le_kStages`: `d^fin_σ(δ) ≤ k d^fin_σ(1/100)` for `0 < δ ≤ 1/100`,
  `k = ⌈log(1/δ)/log 100⌉` (`kStages`; `cosh_pow_le`: `cosh(k a) ≥ cosh(a)^k`,
  `arcosh_le_kStages`);
* `qAv_ge`: the averaging budget `q_av = ⌈51200π/y⌉ - 1` (`qAv`) is at least
  `(51200π - 1)/y`; `averaging_ratio`: `1400 d^fin_σ(1/100) < q_av`;
  `averaging_ratio_final`: `1400 d^fin_σ(δ) < k q_av`.

**Centred averaging and the query comparison** (`CentredAveraging.lean`, namespace
`ChebyshevLinearSystemFinite.CentredAveraging`; Remark `qls:rem:averaging` and the comparison
paragraph of Remark `qls:rem:constants`). For a real polynomial `p` of degree at most `d` with
nonnegative coefficients and `p(1) = 1` (`polyOp p W = f(W)`), `m = ⌊d/2⌋` (`lowHalf`) and
`c = ⌈d/2⌉` (`highHalf`):

* `centred_sub_eq`, `norm_centred_sub_apply`, `norm_centred_apply`, `opNorm_centred_sub`: for a
  unitary `W` and `W P = P`, `W^{-m} f(W) - P = W^{-m}(f(W) - P)`, with the same error on every
  vector, the same operator-norm error and the same selected norm; `centred_filter_error`: for the
  averaging filter `f_N(W)^k` and the fixed-space projector, the error `(N b)^{-k} ‖x‖` and
  equation `qls:eq:filterprobability` of the centred filter;
* `centred_sum`: `W^{-m} f(W) = ∑_{|z| ≤ c} a_{z+m} W^z` (exponents in `[-m, d - m] ⊆ [-c, c]`;
  for odd `d` the branch `-c` carries weight zero, `centCoeff_neg_highHalf`);
  `centSeedT_isometry`, `centT_compression`: on the released counter register (`2c ≤ T`) the
  centred coefficient seed is an isometry and the `c` signed steps compress to `W^{-m} f(W)`;
* `centred_run`, `centred_test_amplitude`: the released signed-step run
  `ChebyshevLinearSystem.runPhys … c` on the physical oracle family has success block
  `W_{σ,r}(x)^{-m} f(W_{σ,r}(x))` on every input, its literal adjoint program the adjoint block,
  and both make `54 c` matrix-oracle and `2 c` source calls; `centred_run_zero` (`d = 0`: no step,
  identity block); `centred_averaging_run`: the averaging filter `f_N(W)^k` with
  `⌈k (N - 1)/2⌉` signed steps;
* the comparison, with `n_av = ⌈100π/ω⌉`, `ω = g/(512√s)` (`nAv`, `qAv_eq`: `q_av = n_av - 1`):
  `step_costs` (a forward and a signed step both make `54` matrix-oracle and `2` source calls),
  `test_query_comparison` (`1400` times the calls of the Chebyshev run of `d^fin_σ(1/100)` signed
  steps are fewer than those of the forward run of `q_av` steps), `final_query_comparison` (the
  repeated stage: `d^fin_σ(δ)` against `k q_av`, `δ ≤ 1/100`), `walkStepsAv`, `walkSteps_ratio`,
  `budget_query_comparison` (the prescribed budgets with the numbers of tests and attempts of
  `walkStepsF`), and `averaging_schedules` (the forward run of `k q_av` steps, the centred run of
  `⌈k q_av/2⌉` signed steps and a Chebyshev run, with their exact amplitudes and counts). The
  comparison concerns the stated conservative forward averaging schedule only;
  `centred_test_ratio` (`700 d^fin_σ(1/100) < ⌈q_av/2⌉`) and `centred_final_ratio`
  (`700 d^fin_σ(δ) < ⌈k q_av/2⌉` and `700 d^fin_σ(δ) < k ⌈q_av/2⌉` for `0 < δ ≤ 1/100`) are
  derived here, not claims of the manuscript.

**Intermediate results.**

* `impl_bernoulli` (equation `qls:eq:bernoulli`): an implemented test whose success vector is
  within `e_test` of the ideal one has `|p_F - p_ξ(r)| ≤ δ₀² + 2e_test = 10⁻⁴`,
  `p_ξ(r) = ‖P_{ξ_j,r} J e‖²`; `impl_test_bounds`: hence
  `1/(2(1 + q²)) - 10⁻⁴ ≤ p_F ≤ 1/(1 + q²) + 10⁻⁴`, `q = ρ_j/r`.
* `impl_final_amp`: an implemented final attempt whose decoded amplitude is within `e_fin` of
  the ideal one is within `δ₀ + e_fin = ε/1000` of the decoded exact projection `c A⁻¹ b`
  (`final_fact_deg`); `impl_final_good`: so at a good estimate `1000` attempts succeed with
  probability at least `97/100` and output a state within `ε/50`.
* `impl_correctness`: for one input, from these bounds on the success vectors at that input,
  success at least `2/3` and conditional trace distance at most `ε`.
* `algorithm_bad_le_tol`: the released estimator analysis with the two-sided tolerance.
* Costs: `impl_worstCost` (at most the calls of the ideal finite-degree runs, when every
  implemented run has their weighted cost), `walkStepsF_le` (`≤ 4.9·10⁸ √s κ log(1/ε)` signed
  steps), `impl_matrix_queries`, `impl_source_queries`, `algorithm_matrix_queries_sharp`,
  `algorithm_source_queries_sharp`.
* Allocation: `allocRun_approx` (signed steps within `ρ` and a coefficient preparation within
  `η` give `RunApprox ... (d ρ + 2η)`), `allocTest_approx`, `allocFinal_approx`,
  `alloc_test_arith`, `alloc_final_arith`.

**Proof map.** Module paths are relative to `ChebyshevLinearSystemFinite/`.

* `GateApprox`: `GateApprox` and `GateApprox.refl`, `mono`, `cost_eq`, `count_eq`,
  `adjoint`, `eval_sub_le` (with the released `OracleCircuit.product_error_le`),
  `eval_apply_sub_le`, `nonneg`, `GateApprox.compile`.
* `Runs`: `amp`, `probability_sub_le_of_amp`, `RunApprox` and its lemmas, `AmpApprox` and its
  lemmas, `RunApprox.ampApprox`; `repeatLeaf` (the released `Protocol.single` leaf) and
  `repeatLeaf_successMass`, `repeatLeaf_leafDir`, `repeatLeaf_spec`, `repeatLeaf_worstCost`.
* `Estimator`: `reject_inv_tol`, `last_accepts_tol`, `candidates_le_tol`, `stages_le_tol`,
  `algorithm_bad_le_tol` (with the released `Estimator.count_step`, `Estimator.accept_good`).
* `Degree`: `resid`, `augDegree_resid` (`d_σ(sech(2D arsinh χ)) = D`), `resid_succ_le`,
  `resid_succ_le_sharp`, `finDegree`, `delta0`, `delta0_le`, `delta0_le_sharp`, `delta0_lt`,
  `dTestF`, `dFinF`, `TcF`, `eTest`, `eFin` and their bounds (`eTest_ge`, `eTest_ge_sharp`,
  `eFin_ge`, `eFin_ge_sharp`).
* `Facts`: `filter_proj_deg`, `test_fact_deg`, `final_fact_deg` (the released
  `ChebyshevFilter.augmented_final_fact` at `δ = resid`).
* `Algorithm`: `implAlgorithm`, `testRunF`, `finalRunF`, `algorithmF`, `testRunF_amp`,
  `finalRunF_amp` (the released `ChebyshevLinearSystem.test_amplitude` and
  `ChebyshevLinearSystem.final_amplitude`).
* `Correctness`: `testRunF_bounds`, `impl_test_bounds`, `impl_bernoulli`, `impl_final_amp`,
  `impl_final_good` (the released `ChebyshevLinearSystem.final_good_arith`),
  `impl_correctness` (the released `Protocol.Tree.successMass_ge`,
  `Protocol.Tree.output_guarantee`).
* `Constants`: Remark `qls:rem:constants`, `dTestF_lt` (`d^fin_j < 112 √s 2^j`), `kStages_le`,
  `dFinF_le` (`d^fin_fin ≤ 168 √s κ log(1/ε)`).
* `Cost`: `reps_le_sharp`, `two_pow_stageOf_le`, `eTest_ge_uniform`, `eTest_ge_uniform_sharp`,
  `walkStepsF`, `walkStepsF_le`, `walkStepsC_le_walkStepsF`, the query counts.
* `Main`: `main_amp`, `main`, `main_uniform`, `main_uniform_sharp`, `main_exact`,
  `main_improved`, `main_improved_exists`.
* `Alloc`: `allocRun`, `allocRun_approx`, `allocTest`, `allocFinal`, `allocAlgorithm`,
  `main_alloc`.
* `CentredAveraging`: centred averaging and the query comparison, as above.

Every theorem of the library is axiom-audited in `ChebyshevLinearSystemFinite/Audit.lean`.

**Formalisation choices and deviations from the paper.**

* Known gates are modelled syntactically in `main` (`RunApprox`, `GateApprox`): an implemented
  circuit has the same query skeleton as the ideal one, and each fixed gate (of the released
  step programs, of the native Cayley and source programs, of the signed-step reversal gates
  and of the run layer) is replaced by any finite circuit of known gates. No structure is
  imposed on the replacements: the manuscript's prescriptions (reverse rotations as actual
  adjoints of the forward circuits, reflections as preparation · exact basis reflection ·
  actual adjoint preparation, so that both directions stay inverses of one implemented unitary)
  are special cases, not hypotheses; the analysis uses only operator-norm closeness. In the
  released signed step the reverse direction is `Y W Y` with fixed gates `Y` (chiral symmetry,
  `ChebyshevLinearSystem.flip_WwO`), so the manuscript's reverse rotations have no separate
  counterpart.
* The hypothesis of `main_amp` is the manuscript's `e` itself, a bound on the change of the
  unnormalised success vector on the inputs satisfying the promise, together with the weighted
  costs of the ideal runs (`AmpApprox`). `main` is the special case in which the error budget is
  split into the approximate known gates (`GateApprox`), the seed and the flag: `RunApprox` asks
  for these errors to add up to the allowance, which bounds the change of the success vector
  (`RunApprox.amp_sub_le`, `RunApprox.ampApprox`). In both, the implemented runs act on the
  registers of the ideal runs (no additional synthesis ancillas).
* Seeds and flags are modelled as public unit vectors and isometries within Euclidean and
  operator-norm distance of the ideal ones (`RunApprox`); the manuscript's coefficient-state
  preparation within `η_c`, unprepared by its actual adjoint, is the special case `allocRun`
  (seed and flag each within `η_c`). The remark that the coefficient distribution changes by at
  most `2η_c` in total variation is not used.
* The test allowance enters as the manuscript's two-sided bound `|p_F - p_ξ(r)| ≤ 10⁻⁴`; the
  released estimator analysis assumed the one-sided bound `p_ξ(r) ≤ p_F` of exact gates and is
  re-proved with the two-sided tolerance (`algorithm_bad_le_tol`); the thresholds, margins and
  classical control are unchanged (`0.2299 + 0.0001 = 0.23`, `0.2499 - 0.0099 ≥ 0.22`).
* As in the released proof the tests use the public lower bound `g = σ_j ≤ g_{σ_j}` and the final
  filter `g = 1/κ`, so `y = σ_j/√s` and `y = 1/(κ√s)` in equation `qls:eq:testconstant`; the
  final degree is bounded through `d^fin(δ) ≤ k d^fin(1/100)` (`dFinF_le`, constant `168`).
* The explicit accuracy requirements of `eTest_ge`, `eFin_ge`, `main_uniform` and `main_alloc`
  are sufficient conditions derived from `δ₀ ≤ δ/(1 + 2χ²)` (`delta0_le`, a relative margin of
  at least `2χ²/(1 + 2χ²)` from the one extra degree), so they scale as `1/(s 4^j)`,
  `1/(s κ²)` and `ε/(s κ²)`. The relative margin is in fact at least of order `2χ`:
  `δ₀ ≤ δ/(1 + 2(1 - δ)χ)` (`delta0_le_sharp`, `resid_succ_le_sharp`:
  `cosh(x + 2 arsinh χ) ≥ (1 + 2(1 - δ)χ) cosh x` when `cosh x ≥ 1/δ`). This gives the
  requirements of `eTest_ge_sharp`, `eFin_ge_sharp`, `eTest_ge_uniform_sharp` and
  `main_uniform_sharp`, which scale as `1/(√s 2^j)`, `1/(√s κ)` and `ε/(√s κ)`, larger by
  factors of order `√s 2^j` and `√s κ`. None of these is optimised, and `main_alloc` keeps the
  requirements derived from `delta0_le`.
* The constants: `d^fin_j < 112 √s 2^j` and `d^fin_fin ≤ 168 √s κ log(1/ε)`; the repetition
  count is the released one (the elementary tail bound `P(|S/n - p| ≥ t) ≤ 2 exp(-n t²/4)` with
  `t = 0.0099`, not Hoeffding's inequality), bounded more sharply by
  `n_j ≤ 204062 log(1/ε) + 28290 (m - j)`; at most `4.9·10⁸ √s κ log(1/ε)` signed steps, `54`
  matrix-oracle and `2` source calls each.
* The averaging comparison of Remark `qls:rem:constants` concerns the averaging schedule with
  the angle bound `ω = g/(512√s)` and `N = ⌈100π/ω⌉` named in the remark (`qAv`), as a
  statement about the prescribed step budgets; the released averaging-filter proof of
  `SparseLinearSystems` uses `N = ⌈100/b⌉` instead.

**Not formalised.** Hoeffding's inequality and the repetition count `⌈log(2/ζ)/(2·0.0099²)⌉` of
equation `qls:eq:hoeffding`, gate synthesis itself (the number of elementary gates needed to
reach a given accuracy, and approximations that use additional ancilla qubits; only the
accuracies of replacements on the registers of the run are modelled), the transfer of the
averaging comparison of Remark `qls:rem:constants` to matrix-query budgets, gate and workspace
counts, and classical circuit-generation costs. The matching lower bound (`qlsl:thm:main`) is
formalised in the separate library `LinearSystemLowerBound`.

**Provenance.** A new library written against the released package; it reuses the released
access model, walk, circuit layer, protocol, estimator, endpoint lemmas and Chebyshev runs of
`SparseLinearSystems`, `ChebyshevFilter` and `ChebyshevLinearSystem`. No released Lean module
was changed. It covers the items "the finite-gate allowance of equation `qls:eq:finitedegree`"
and "the explicit constants of Remark `qls:rem:constants`" listed as not formalised in
`ChebyshevLinearSystem/Statements.lean`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/
