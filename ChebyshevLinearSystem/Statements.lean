import ChebyshevLinearSystem.Main

set_option autoImplicit false

/-!
# Theorem `qls:thm:main` with the positive Chebyshev filter: paper-to-Lean entry point

Theorem 8.1 (`qls:thm:main`) of the accompanying paper, end to end with the paper's own
filter: the positive Chebyshev filter of Proposition `qls:prop:chebyshev`, implemented by the
normalisation-one LCU circuit of signed walk steps (Lemma `qls:lem:signedwalk`), with the
degrees of equation `qls:eq:filtercost`. The released proof `SparseLinearSystems.Endpoint.main`
(library `SparseLinearSystems`) uses the averaging filter of Remark `qls:rem:averaging` with
forward walk steps and is unchanged. The endpoints are `ChebyshevLinearSystem.main` and its
existential form `ChebyshevLinearSystem.main_exists` (`ChebyshevLinearSystem/Main.lean`). No
result from another paper is used. Unqualified names below are in the namespace
`ChebyshevLinearSystem`; `Endpoint`, `Facts`, `Step`, `Protocol`, `LogicalWalk` and
`Augmented` refer to the namespaces `SparseLinearSystems.*` of the released library, and
`NativeSparseBlockEncoding`, `ODEMixedOutput` and `EncodedLabeledProgram` to
`SparseHamiltonian.*`. References to the manuscript use its labels.

**Access model.** That of the released theorem. `D : NativeSparseBlockEncoding.Data X n Z s`
supplies, for every unknown input `x : X`, an `N × N` matrix `A_x` with at most `s ≥ 1`
nonzero entries per row and column, exact finite-word entries, and padded injective in-place
row and column locators with full unitary extensions. `Facts.Aop D x` is `A_x` as an operator
on `EuclideanSpace ℂ n` (spectral norm). `Ub x` is the supplied state-preparation circuit and
`sv` the public reference state, `b = U_b sv`. The physical oracle family is the released
`Step.physOracle D Ub T`: the three native primitives with all other registers as spectators,
and `U_b` controlled by a workspace bit. `Step.wMat` counts every native matrix-oracle call
and `Step.wSrc` every call of the controlled `U_b`; inverse calls are counted. Public
instance-independent gates are free.

**Promise** (equation `qls:eq:promise`). `Endpoint.Promise D κ x`: `‖A_x‖ ≤ 1`, `A_x` is
invertible and `‖A_x⁻¹‖ ≤ κ`. In addition `κ ≥ 1`, every `U_b` is unitary and `‖sv‖ = 1`.

**Algorithm.** `algorithm D Ub sv κ ε` is one bounded adaptive protocol
(`Protocol.Tree (Step.physOracle D Ub (Tc s κ ε)) (LogicalWalk.PrivO n) (EuclideanSpace ℂ n)`),
uniform over all unknown inputs; its circuits, seeds, flags and classical decisions are
determined by `s`, `κ`, `ε` and the instance-independent part of the access model. It is the
released estimator protocol (`Protocol.Estimator.algorithm`, as in `Endpoint.algorithm`) with
Chebyshev test runs and final leaves: the geometric norm estimator for
`m = ⌈log₂ ⌈κ⌉⌉` stages (`Endpoint.stagesM`) with `σ_j = 2^{-j}` (`Endpoint.sig`), five
candidates per stage and `n_j = ⌈4 log(2/ζ_j)/t²⌉` fresh runs per candidate (`Endpoint.reps`),
then at most `1000` fresh final attempts, stopping at the first heralded success. The filters
are Chebyshev filters `F_{b,d}(W) = ∑_{|j| ≤ d} p_j W^j` (`ChebyshevFilter.filterOp`):

* a test of candidate `r` at stage `j` (`testRun`) runs `F_{b,d}(W_{σ_j,r})` with
  `b = b(σ_j) = χ/√(1 + χ²)`, `χ = 4σ_j/(165√s)` (`Augmented.bLow`) and the degree
  `d_j = ⌈arcosh(100)/(2 arsinh χ)⌉` (`dTest`, `ChebyshevFilter.augDegree` at `δ = 1/100`)
  on the seed `J e`, and measures the coefficient flag;
* a final attempt at the estimate `r` (`finalLeaf`) runs `F_{b,d}(W_{0,r})` with `b = b(1/κ)`
  and `d = ⌈arcosh(1000/ε)/(2 arsinh(4/(165√s κ)))⌉` (`dFin`, `δ = ε/1000`), and decodes the
  walk boundary and the solution coordinates.

Every filter is the LCU circuit of `d` signed steps on one counter register of `T + 1` values,
`T = 2 (d_fin + ∑_{j ≤ m} d_j)` (`Tc`): the coefficient seed `∑_j √p_{j-d} |j⟩ ⊗ v`
(`seedT`), the signed steps (`runPhys`), and the flag `E (ψ ⊗ ·)` (`testFlag`,
`finalOutput`). Its success block is exactly `F_{b,d}(W_{σ,r}(x))` (`run_success_block`).

**Guarantees** (`main`, for `0 < ε ≤ 1/10`):

* every transcript, including every failure branch, makes at most
  `4.4·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and at most `1.7·10⁹ √s κ log(1/ε)` calls of
  the controlled `U_b` and its inverse (`44 * 10 ^ 9`, `17 * 10 ^ 8` in Lean);
* for every input satisfying the promise, every run is unitary, the heralded success
  probability is at least `2/3`, and the output conditioned on success is a positive
  trace-one operator `ρ` with `½ ‖ρ - |x⟩⟨x|‖₁ ≤ ε`, `|x⟩ = A⁻¹ b / ‖A⁻¹ b‖`
  (`Endpoint.solutionState`).

`main_exists`: there are a register size `T` and one protocol
`P : Protocol.Tree (Step.physOracle D Ub T) (LogicalWalk.PrivO n) (EuclideanSpace ℂ n)`,
chosen before every unknown input, with the same guarantees. The trace distance is
`ODEMixedOutput.hermitianTraceDistance`, half the sum of the absolute eigenvalues of the
Hermitian difference. All constants are explicit absolute numbers; there is no logarithm of
`s` or `κ` and no extra power of `log(1/ε)`. The released averaging-filter proof gives
`4·10¹²` and `2·10¹¹`.

**Intermediate results.**

* Lemma `qls:lem:signedwalk` for the released walk (`signed_walk_step`): for every direction
  register `dir : Fin (T + 1) → Option Bool` the program `signedStepProg D Ub sv T (σ, r, dir)`
  over `Step.physOracle D Ub T` acts, exactly on the clean subspace `Step.E D T`, as
  `W_{σ,r}(x)`, `W_{σ,r}(x)†` or `1` on each counter value (`ChebyshevFilter.dirOp`), for every
  input; its weighted cost equals that of the forward step `Step.stepProg` for every weighting
  of the physical labels: `54` matrix-oracle calls and `2` source calls. The controls are
  fixed gates.
* The chiral symmetry of the walk: the fixed involution `Z = parPriv` satisfies
  `Z K_{σ,r}(x) Z = -K_{σ,r}(x)` for every input (`parPriv_Kw`; the padding branch of `K` is
  `0`), hence, with the fixed gate `Y = Z R` (`flipO`: `Z` transported to the opaque copy as
  `parO`, `R` the reflection gate of `Step.stepProg`), `Y W_{σ,r}(x) Y = W_{σ,r}(x)†`
  (`flip_WwO`).
* The LCU circuit of Proposition `qls:prop:chebyshev` as a physical program for the released
  walk (`chebyshev_run`): for `2d ≤ T` and `b ∈ (-1, 1)` the flag `testFlag D b T d` is an
  isometry (normalisation one), the success block of the run `runPhys D Ub sv T σ r d` of `d`
  signed steps is exactly `F_{b,d}(W_{σ,r}(x))` on every input (`run_success_block`), and the
  run makes `54 d` matrix-oracle and `2 d` source calls. The decoded test amplitude is
  `F_{b,d}(W) J e` (`test_amplitude`) and the decoded final amplitude `S† J† F_{b,d}(W) J e`
  (`final_amplitude`).
* For the augmented walk under the hypotheses of the released gap theorem `Facts.gapO`
  (`0 < g ≤ g_σ`, `r ≥ 1/8`, `0 < δ < 1`), the run of degree `d_σ(δ)` at `b(g)` has success
  block within `δ` of the eigenvalue-one projector `P_{σ,r}` (`augmented_run`, from
  `ChebyshevFilter.augmented_filter`).

**Proof map.** Module paths are relative to `ChebyshevLinearSystem/`.

* `Chiral`: `Cayley(-K) = Cayley(K)†` (`cayley_neg`), conjugation by an anticommuting
  involution (`cayley_chiral`), reversal of `W = R C` (`walk_reverse`); the orientation
  parity anticommutes with the native generator because the edge generator exchanges the
  orientations and the locators act orientation-wise (`parOr_entryGenerator`,
  `parOr_block`, `parOr_generator`); `T₁`, `T₂(β)` are off-diagonal (`parPub_T1`,
  `parPub_T2`); `parPriv_Kw`; the opaque walk as a Cayley walk (`WwO_walk`, from the released
  `Augmented.conj_walk`); `flip_WwO`.
* `SignedStep`: the signed logical oracle (`signedLog`), the reversal gate on inverse branches
  (`flipGate`), the operator identity (`signed_eq`), the program (`signedStepProg`), its
  action from the released `Step.stepProg_intertwines` (`signedStepProg_intertwines`), its
  cost (`signedStepProg_cost`, `signedStepProg_cost_mat`, `signedStepProg_cost_src`), and
  `signed_walk_step`.
* `Register`: Proposition `qls:prop:chebyshev`'s LCU circuit on the padded register: powers
  `j - d` (`powT`), directions (`dirT`), the seed (`seedT`, `seedT_isometry`), the signed
  steps (`signedStepsT`, `signedStepsT_eq`) and the compression (`lcuT_compression`); the
  case `T = 2d` is `ChebyshevFilter`'s circuit (`seedT_two_mul`, `signedStepsT_two_mul`).
* `Run`: logical runs (`runLog`), physical runs via the released
  `EncodedLabeledProgram.compile` (`runPhys`, `runPhys_intertwines`), seeds and flags
  (`seedVec`, `testFlag`, `finalOutput` and their norms), `run_success_block`,
  `chebyshev_run`, `test_amplitude`, `final_amplitude`, costs.
* `Algorithm`: degrees and register (`dTest`, `dFin`, `Tc`, `test_fits`, `final_fits`,
  `bLow_mem`), `augmented_run`, `testRun`, `finalCircuit`, `finalLeaf`, `algorithm`, and the
  semantics of the runs (`testRun_probability`, `finalAmp_eq`, `finalLeaf_spec`).
* Equations `qls:eq:probability`, `qls:eq:filterprobability` and `qls:eq:bernoulli`:
  `Correctness` (`test_bounds`, from `ChebyshevFilter.augmented_test_fact` at `δ = 1/100`).
  Equations `qls:eq:normladder` to `qls:eq:estimatebound`: the released `Endpoint.rho_ladder`
  and `Protocol.Estimator.algorithm_bad_le`.
* Equations `qls:eq:qrange`, `qls:eq:finalprob` and the final error: `Correctness`
  (`final_good_arith`, `finalLeaf_good`, from `ChebyshevFilter.augmented_final_fact` at
  `δ = ε/1000`).
* Success, mixture and conditional trace distance: `Correctness` (`correctness`, with the
  released `Protocol.Tree.successMass_ge` and `Protocol.Tree.output_guarantee`).
* Equations `qls:eq:filtercost`, `qls:eq:geometriccost` and `qls:eq:main`: `Cost`
  (`dTest_le`, `dFin_le`, `walkStepsC_le`, `algorithm_worstCost`,
  `algorithm_matrix_queries`, `algorithm_source_queries`).
* `Main`: `main`, `main_exists`.

Every theorem of the library is axiom-audited in `ChebyshevLinearSystem/Audit.lean`.

**Formalisation choices and deviations from the paper.** These change constants or proof
routes only, not the stated bounds.

* Lemma `qls:lem:signedwalk` is proved through the chiral symmetry rather than the common
  conjugator `D = V† C V` of equation `qls:eq:commonconjugator`. The released circuit layer
  factors the walk as `R · A_sp · F_a · V · F_b · V†` (`LogicalWalk.WwO_factor`), where the
  sparse factor `A_sp` is the compiled native Cayley program and its internal common
  conjugator is not exposed. The signed step is the released forward step (`Step.stepProg`)
  on all active counter values, preceded and followed by the fixed gate `Y = Z R` on the
  inverse-step values; it makes the same oracle calls as one forward step, and its controls
  are fixed gates, as stated in the lemma. Equation `qls:eq:signedstep` itself is not used.
* The chiral symmetry needs the fourth branch of the released generator `LogicalWalk.Kw` to
  be `0` (`Augmented.walkK`). Equation `qls:eq:composition` puts the padding term
  `P_pad/(8√s)` there; the released walk acts on spaces without unused basis states, so that
  term vanishes (module note of `SparseLinearSystems/Augmented/Walk.lean`; unused physical
  states lie outside the clean encoding `Step.E`). No involution anticommutes with a nonzero
  `P_pad ⪰ 0`, so this route needs the padding branch to vanish.
* All runs share one counter register of `T + 1` values (the physical oracle family depends on
  `T`): a degree-`d` filter uses register value `j` with power `j - d`, and the values
  `j > 2d` carry seed weight zero. The LCU circuit uses exactly `d` signed steps (the
  proposition says at most `d`).
* The tests use the public lower bound `g = σ_j ≤ g_{σ_j}` in the filter parameter
  `b(σ_j)`, as the released proof; the final filter uses `g = 1/κ = g_0`.
* The final preparation is one Chebyshev filter with target `δ = ε/1000`, as in the
  manuscript (the released proof uses `100^{-k} ≤ ε/1000` with `k` powers of the averaging
  filter).
* Kept from the released proof: exact gates (the test tolerance `10⁻⁴ = δ²` comes from the
  filter alone), the elementary tail bound `P(|S/n - p| ≥ t) ≤ 2 exp(-n t²/4)` instead of
  Hoeffding's inequality (`t = 0.0099`), the failure budget `ζ_j = (ε/5000) 2^{j-m}` per test,
  clipping to `[1, 4κ]` with the fallback `2r`, and `1000` final attempts (success at least
  `97/100` from a good estimate).
* The degrees are bounded through `ChebyshevFilter.augDegree_le`
  (`d_σ(δ) ≤ 23 √s log(2/δ) / g`): `d_j ≤ 128 √s 2^j` and `d_fin ≤ 111 √s κ log(1/ε)`, so
  every transcript makes at most `8.1·10⁸ √s κ log(1/ε)` signed steps (`walkStepsC_le`).

**Not formalised.** The finite-gate allowance of equation `qls:eq:finitedegree`, Hoeffding's
inequality, the explicit constants of Remark `qls:rem:constants` (in particular the degree
constant `112`), the literal common-conjugator form `qls:eq:signedstep` of the signed step for
the released walk, the reversal for a walk with a padding term, gate and workspace counts, and
classical circuit-generation costs. The matching lower bound (`qlsl:thm:main`) is formalised in
the separate library `LinearSystemLowerBound`.

**Provenance.** A new library written against the released package; it reuses the released
access model, walk, circuit layer, protocol, estimator analysis and endpoint lemmas of
`SparseLinearSystems` and the filter facts of `ChebyshevFilter`. No released Lean module was
changed. It covers the item "Theorem `qls:thm:main` with the Chebyshev filter" listed as not
formalised in `ChebyshevFilter/Statements.lean`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/
