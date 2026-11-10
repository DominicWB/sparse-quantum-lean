import SparseLowerBounds.Hamiltonian.ReleaseForm

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Hamiltonian-simulation query lower bounds: paper-to-Lean entry point

Theorem `hsl:thm:main` of the accompanying paper (the Hamiltonian-simulation query lower bound,
Section `part:hsl`) is formalized in `SparseLowerBounds/Hamiltonian/Theorem.lean`: eq. `hsl:eq:main`
is `SparseLowerBounds.Hamiltonian.main_max` (max form) and `main_exists` (family form), assembled
from the per-family theorems `time_main`, `mixed_main`, `precision_main` (spectator register) and
`time_main_native`, `mixed_main_native`, `precision_main_native`; the instance properties are
`hard_instances`. Corollary `hsl:cor:power` is `cor_power` and `cor_power_not_uniform` in
`Hamiltonian/Power.lean`. Lemma `odel:lem:herald` is `Hamiltonian/Herald.lean`. The lower bounds
under the release's endpoint error (the correctness notion of
`ImprovedSparseHamiltonian.simulation_log_one`) are in `Hamiltonian/ReleaseForm.lean`. The lemmas:
`hsl:lem:search` is `SparseLowerBounds.SearchWeight.search_lemma` (average correlation) and
`search_lemma_worst`; `hsl:lem:mixed` is `Hamiltonian.mixed_general`; `hsl:lem:precision` is
`Hamiltonian.precision_general`, through the Fourier-degree bound `BitDegree.le_two_mul_count`. All
declarations named below without a namespace are in `SparseLowerBounds.Hamiltonian`.
References to the manuscript use its labels.

**Access model** (Section `hsl:sec:main` and the chain construction of Section `part:hsl`). The
matrix oracles are the release's native sparse primitives. The hard data are
`SparseHamiltonian.NativeSparseBlockEncoding.Data X N (Word B) s`, built by the one-bit word-table
builder `bitData` (`Hamiltonian/DataBuilder.lean`). The unknown input is `j : Fin n → Fin (2^μ)`
(`n` one-hot strings of length `m = 2^μ`) for the time and mixed families and `x : Fin n → Bool` for
the precision family. `NativeSparseBlockEncoding.oracles D` consists of the in-place row locator,
the in-place column locator (each a full permutation unitary) and the value oracle, which adds the
exact entry word. The `*_native` theorems use `oracles D`; the others use `specOracles Ω D`, the
same primitives acting on every copy of an untouched spectator register `ℂ^Ω` that the algorithm may
use as workspace.

* Value queries cost two Boolean queries: query the one membership bit the
  entry depends on, add the word selected by that bit (a fixed gate), unquery
  (`Query/PhaseCircuit.lean`: `PhaseCircuit.circuit_intertwines`,
  `PhaseCircuit.implementsOn_circuit`; `Hamiltonian/Compile.lean`:
  `implementsOn_bitData`, `implementsOn_bitData_spec`; specialised in
  `Hamiltonian/Native.lean`: `implementsOn_searchData(_spec)`,
  `implementsOn_scalarData(_spec)`). The Boolean oracle is
  `oneHotOracle P` (search families) or `bitOracle P` (precision family).
* Locators are free. Location lists and their full in-place extensions are literally constant in the
  input (`HardInstance.locators_const`), so both location oracles are fixed gates of cost 0
  (`hardCost`), as the paper allows (Section `hsl:sec:main`: "allowing all location operations,
  known gates and state preparation for free").
* Inverse queries are counted. `p.labelCount .value` (written `Q`) counts
  value queries, inverses included, and `p.count` all queries. The release
  value oracle is additive, so `EncodedMultiOracle.compile` replaces an
  inverse value query by the adjoint of the two-query circuit, again two
  Boolean queries; `p.cost hardCost = 2 Q` (`cost_hardCost`,
  `native_bound_of_cost`).
* Controlled calls (Section `hsl:sec:main`: inverses and the controls of Lemma
  `access:lem:control`). `MultiOracleCircuit.Program` has no controlled primitive. A controlled
  location call is a fixed gate. A controlled value call is one spectator value call between fixed
  controlled swaps that, on the inactive branch, route the word register to a dummy `Word B`
  register held in the uniform superposition, which every shift leaves invariant (the release's
  `NativeControlledOracle.referenceSwap` pattern). So the spectator forms, with spectator
  `Ω × Fin 2 × Word B`, apply at cost 1 per controlled value call. This reduction is documented in
  the module docstring of `Hamiltonian/Theorem.lean`; there is no Lean lemma for it.

**Algorithm.** A non-adaptive `SparseHamiltonian.MultiOracleCircuit.Program`
`p` over that family (fixed unitaries, labelled queries, inverse queries,
sequencing), uniform over all inputs, run on an input-independent seed `φ₀`
with `‖φ₀‖ ≤ 1`, and read through an isometry
`e : K →L[ℂ] SysGarb S G` (`e† ∘L e = 1`) into system ⊗ garbage, where the
system is `EuclideanSpace ℂ S` (`S = SearchIndex n μ s` or `ScalarIndex n s`)
and the garbage `G` is any Hilbert space. The precision theorems need neither
`‖φ₀‖ ≤ 1` nor the isometry hypothesis (the heralded ones keep `e† ∘L e = 1`).

**Accuracy** (eq. `hsl:eq:accuracy`). The target is
`ψ_X = evolve (D.matrix x) τ ψ_in`, where `evolve H τ` is by definition the
release's `NormedSpace.exp ((-Complex.I * τ) • SparseStateOverlap.matrixOperator H)`
and `ψ_in = (|r₀⟩ + |v₀⟩)/√2` is the known input of eq. `hsl:eq:readout`
(`searchInput`, `scalarInput`). `Readout.Accurate e (p.eval x φ₀) ψ_X ε` is
the observable form of trace distance at most `ε`: for every self-adjoint
`M` with `‖M‖ ≤ 1`, `|⟪Φ, e† (M ⊗ 1_G) e Φ⟫ - ⟪ψ_X, M ψ_X⟫| ≤ 2ε`; it allows
mixed outputs. An operator-norm error at most `ε` implies it (Section `hsl:sec:main`):
`accurate_of_endpoint` reads the output through the constructed
isometry `endpointReadout ι i₀` (`endpointReadout_isometry`), and
`accurate_of_endpoint_program` (`Hamiltonian/ReleaseForm.lean`) applies this
to programs. The `*_endpoint` theorems assume exactly the release's
hypothesis `‖p.eval x ∘L ι - ι ∘L exp(-iτ H_x)‖ ≤ ε` for an isometric input
encoding `ι` (seed `ι ψ_in`). Heralded accuracy (Lemma `odel:lem:herald`) is
`Readout.HeraldedAccurate e herald (p.eval x φ₀) ψ_X ε` (conditional trace
distance multiplied through by the success probability, no division) with
`IsStarProjection herald` and success `2/3 ≤ ‖herald (p.eval x φ₀)‖²`.

**Hypotheses.** `HSRange τ s ε`: exactly `τ ≥ 1`, `s ≥ 32` and
`0 < ε ≤ 1/64` (Theorem `hsl:thm:main`); `L = hsL ε = log(1/ε)`,
`h = hsH τ ε = log(e + L/τ)`, `r = hsR τ ε = L/h` (eq. `hsl:eq:parameters`).
The mixed theorems also assume `L ≥ 64τ` and `s ≥ 64n/τ`, the precision
theorems `L ≥ 64τ`, where `n = precN τ ε = ⌊r/4⌋` (eq. `hsl:eq:nchoice`);
`main_max` and `main_exists` use the mixed and precision algorithms only in
those ranges (for `L < 64τ` the time bound absorbs the rest).

**Hard families** (`Hamiltonian/Instance.lean`, `Hamiltonian/HardData.lean`,
`Hamiltonian/HardDataScalar.lean`). `m = 2^{hsMu s}` is the largest power of
two at most `s/2` (eq. `hsl:eq:mrange`). Every core chain `H` is completed to
`fullMatrix H s = H ⊕ diag(0, 1) ⊕ 2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ` (isolated zero-energy
reference vertex `refZero`, isolated energy-one vertex `refOne`, known dense
padding block), and the chain weights are the exact dyadic roundings
`b'_k = N_k/2^F` of `Hamiltonian/Rounding.lean`.

* Time family `timeData τ s hs` (Lemma `hsl:lem:time`): the search-decorated spin
  chain (`searchHam`, eq. `hsl:eq:dressed`) with `n = timeN τ =
  max{1, ⌊2τ/π⌋}` clock steps and weights `c b_k`, `c = timeC τ =
  min{1, πn/(2τ)}`; the forward edges carry the search gadgets `U_{j k}` of
  eq. `hsl:eq:gadget`.
* Mixed family `mixedMainData τ ε s hs` (Lemma `hsl:lem:mixed`): the same chain
  with `n = precN τ ε` and `c = 1`.
* Precision family `precisionMainData τ ε s hs` (Lemma `hsl:lem:precision`): the signed
  scalar chain (`scalarHam`), edge `k` carrying `(-1)^{x_k}`, with
  `n = precN τ ε`.

`hard_instances` proves `HardInstance` for all three (Theorem `hsl:thm:main`): real symmetric (hence
Hermitian); operator norm exactly one; maximum row and column Euclidean norms exactly one (all at
most one, attained at `refOne`); maximum row and column sparsity exactly `s`; exact finite-word
dyadic entries (`D.scale = 1`, position-independent decode `wordDecode B z = valMinAbs z / 2^B`,
every entry `v/2^B` with `-2^B < v ≤ 2^B`); input-independent location lists and locator extensions;
and dimension at most `4 s (τ + r + 1)`. `hard_data_meet_release_hypotheses`: the families satisfy
the hypotheses of `simulation_log_one` with `η = 1`, and `release_upper` is the release's upper
bound on every `HardInstance`.

**Guarantees** (`Q = p.labelCount .value`; each bound also holds for
`p.count`, except the conditional second precision bound, which is on `Q`).

* `time_main` (eq. `hsl:eq:timelower`): `c_T √s τ ≤ Q`,
  `c_T = cT = log 2/(192π)`.
* `mixed_main` (eq. `hsl:eq:mixrbound`):
  `(log 2/(384√2)) √(sτr) ≤ Q`.
* `precision_main` (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): `r/32 ≤ Q`, and `√(sτr)/(64√2) ≤ Q`
  when `s < 64n/τ`.
* `main_max` (eq. `hsl:eq:main`): for any three
  algorithms (spectator form), accurate on the time, mixed and precision
  families respectively, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`,
  `c₀ = c0 = log 2/(4096π)`; `main_max_native` (`Hamiltonian/NativeMax.lean`):
  the same without a spectator register.
* `main_exists`: equivalently, one of the three concrete families, chosen by
  the parameters, forces every accurate algorithm (any spectator, any
  garbage) to make at least `c₀ (√s τ + √(sτr) + r)` value queries.
* `fixedtime_sum` (eq. `hsl:eq:fixedtime`): the algebraic
  form of the sum at `τ = 1`.
* Any 2-query-implementable family (Boolean cost `p.cost w`, for any unitary
  labelled family `O` whose labels are `EncodedOracle.ImplementsOn` the
  Boolean oracle on a fixed isometric encoding with `w l` queries):
  `time_general` (`(log 2/48) n √m ≤ p.cost w` and `2 c_T √s τ ≤ p.cost w`),
  `mixed_general` (Lemma `hsl:lem:mixed`: `(log 2/48) √(mnτ) ≤ p.cost w`, so
  `Q ≥ (log 2/96) √(mnτ)`, eq. `hsl:eq:mixedlower`), `precision_general`
  (Lemma `hsl:lem:precision`: `n/2 ≤ p.cost w`, so `Q ≥ n/4`,
  eq. `hsl:eq:precisionlower`); their native corollaries at arbitrary family
  parameters are `time_native`, `time_spec`, `mixed_native`, `mixed_spec`,
  `precision_native`, `precision_spec` (`Hamiltonian/Native.lean`).
* Lemma `odel:lem:herald` (`Hamiltonian/Herald.lean`), same
  constants: `time_herald`, `mixed_herald`, `precision_herald` (spectator),
  `time_herald_native`, `mixed_herald_native`, `precision_herald_native`,
  `time_herald_general`, `mixed_herald_general`, `precision_herald_general`
  (Boolean cost) and the combined `main_max_herald`.
* Endpoint form (`Hamiltonian/ReleaseForm.lean`): `time_endpoint`,
  `mixed_endpoint`, `precision_endpoint`, their `*_native` versions and
  `main_max_endpoint`.
* Corollary `hsl:cor:power` (`Hamiltonian/Power.lean`):
  `power_separation`, `cor_power`, `cor_power_not_uniform` (see the
  formalization choices for the thresholds).

**Proof map.** Module paths are relative to `SparseLowerBounds/`.

* Lemma `hsl:lem:search`: `Query.SearchWeight` (weight
  `w = P_u + a² P_v + a R`, `wInv`, `conj_Z`, `norm_conj_Z_le`:
  `‖w⁻¹ Z w⁻¹‖ ≤ a⁻²`; `norm_conj_D_le`: `‖w D_b w⁻¹‖ ≤ 1 + 12a/√m`;
  `search_final`, `search_lemma`, `search_lemma_worst`), on the generic
  adversary `Adversary.program_correlation_le`.
* The gadget, eq. `hsl:eq:gadget`: `Hamiltonian.Gadget`
  (`LinearSystems.gadget` reused; `gadget_mulVec_alt`: `U_x v = (-1)^j v`
  on the alternating vector).
* The spin chain, eqs. `hsl:eq:spin`, `hsl:eq:spinamp`: `Hamiltonian.SpinChain` (`norm_spinMatrix`:
  `‖B_n‖ = 1`; `norm_pathMatrix_le`: Schur test with the positive vector `√binom(n,k)`;
  `endAmp_scaled`: `⟨n|e^{-iτaB_n}|0⟩ = (-i)^n sin(aτ/n)^n` from the explicit solution
  `spinSolution` and `evolve_apply_eq_of_hasDerivAt`; `norm_pathMatrix_sub_le`: row sums).
* Decorated chains and parity amplitudes, eqs. `hsl:eq:dressed`, `hsl:eq:parityamp` (the chain
  construction of Section `part:hsl` and Lemma `hsl:lem:precision`): `Hamiltonian.Chains`
  (`searchGauge`, `searchChain_amp`, `signGauge`, `scalarChain_amp`, `norm_searchChain`,
  `norm_scalarChain`).
* Dyadic rounding, eqs. `hsl:eq:round`, `hsl:eq:roundevolution`: `Hamiltonian.Rounding`
  (`chainNum_lt`, `chainWeight_le`, `chainWeight_pos`, `norm_endAmp_chainWeight_sub_le`, by
  Duhamel's inequality `HamiltonianStability.evolution_error_le` and row sums).
* The hard Hamiltonians (the chain construction of Section `part:hsl` and the end of the proof of
  Theorem `hsl:thm:main`): `Hamiltonian.Instance` (`fullMatrix`, `searchHam`, `scalarHam`,
  `searchHam_props`, `scalarHam_props`, `card_searchIndex`, `card_scalarIndex`).
* The readout, eq. `hsl:eq:readout`: `Hamiltonian.Amplitude`
  (`readout_expectation`; `search_corr`, `scalar_corr`: parity-corrected
  ideal expectation at least `7A/8`) and `Hamiltonian.Accuracy`
  (`corr_of_accurate`: accuracy moves it by at most `2ε`).
* Sparse access with exact words and public locators (the chain construction of Section `part:hsl`):
  `Hamiltonian.DataBuilder` (`Word`, `wordDecode`, `BitTable`, `bitData`),
  `Hamiltonian.HardDataEntries`, `Hamiltonian.HardDataScalar` (`scalarData`),
  `Hamiltonian.HardData` (`searchData`, `timeData`, `mixedMainData`,
  `precisionMainData`).
* Two Boolean queries per value call (the chain construction of Section `part:hsl`):
  `Query.PhaseCircuit`, `Hamiltonian.Compile`, `Hamiltonian.Native`, with `Query.Ancilla` and
  `Query.Reduction` (`exists_boolean_program_inner`).
* Lemma `hsl:lem:mixed` and the time bound (Lemma `hsl:lem:mixed` and Lemma `hsl:lem:time`):
  `Hamiltonian.SearchFamily` (`search_cost_of_corr`, `time_corr`,
  `mixed_corr`, `time_general`, `mixed_general`).
* Lemma `hsl:lem:precision`, the Fourier/bit-degree
  argument: `Query.BitDegree` (`program_mem_degLE`: state degree at most `q`;
  `inner_mem_degLE`: expectation degree at most `2q`;
  `sum_bitParity_mul_eq_zero`: parity is orthogonal to degree below `n`;
  `le_two_mul_count`: `n ≤ 2q`) and `Hamiltonian.PrecisionFamily`
  (`precision_cost_of_corr`, `precision_corr_pos`, `precision_general`).
* Parameters and numerics, eqs. `hsl:eq:parameters`, `hsl:eq:mrange`,
  `hsl:eq:nchoice`, `hsl:eq:nrange`, `hsl:eq:precisionchoice`,
  `hsl:eq:rbound`, `hsl:eq:mixrbound`, `hsl:eq:failedmix`,
  `hsl:eq:timelower`: `Hamiltonian.Parameters`,
  `Hamiltonian.Numerics` (`time_final`, `precN_range`, `sixteen_eps_le`,
  `rbound`, `mixrbound`, `failedmix`).
* Assembly (proof of Theorem `hsl:thm:main`): `Hamiltonian.Assembly` (`sum_le_of_small_L`,
  `third_cT_mul_sum_le`, `c0_le`, `three_mul_c0_le`, `assembly`).
* The theorem, corollary, heralded extension and endpoint form:
  `Hamiltonian.Theorem`, `Hamiltonian.Power`, `Hamiltonian.Herald`,
  `Hamiltonian.ReleaseForm`; the combined bound without a spectator register:
  `Hamiltonian.NativeMax` (`main_max_native`).

Proof-only lemmas live in `Helpers/SearchWeight`, `Helpers/SpinChain`,
`Helpers/Chains` (namespaces `SparseLowerBounds.Helpers.*`) and
`Helpers/HsInstance` (namespace `SparseLowerBounds.Hamiltonian.HsInstance`).
Every theorem of the library, helpers included, and every field of the Prop
structures `HSRange` and `HardInstance` is axiom-audited in
`SparseLowerBounds/Audit.lean`.

**Formalization choices.** The paper's constants are proved as stated:
`c₀ = log 2/(4096π)` in eq. `hsl:eq:main`, `c_T = log 2/(192π)`,
`log 2/(384√2)`, `1/(64√2)`, `r/32`, and in the lemmas `log 2/96` and `n/4`
for value queries (`log 2/48` and `n/2` for the Boolean cost `2Q`). There is
no constant deviation. The other choices:

* Combined statement. The three terms of eq. `hsl:eq:main` are witnessed by different families, so
  `hsl:thm:main` is stated in max form, `main_max` ("For three nonnegative numbers, that maximum
  is at least one third of their sum", `assembly`, a statement about three arbitrary reals), with
  the equivalent family form `main_exists`; the same max form is used for the heralded
  (`main_max_herald`) and endpoint (`main_max_endpoint`) versions and for programs without a
  spectator register (`main_max_native`).
* The precision lemma is proved for `n ≥ 1` (the paper states `n ≥ 2`;
  `precision_general`), which is stronger; the mixed lemma keeps `n ≥ 2`.
* The heralded extension is stated at the main parameters only (where
  `A ≥ (τ/(2n))^n ≥ 16ε`, `sixteen_eps_le`), exactly as Lemma
  `odel:lem:herald`; the stand-alone family lemmas are unheralded.
* The dimension bound `O(s(τ + r + 1))` is made explicit as
  `Fintype.card ≤ 4 s (τ + r + 1)` (`hard_instances`).
* Native and spectator forms; controlled value calls are covered by the
  spectator reduction described above (documented, no Lean lemma).
* The bridge from the release simulator's physical oracle is formalized in
  `Hamiltonian/ReleaseAccess`, `ReleaseBridge` and `ReleaseTheta`: see
  "Release simulator" below.
* Corollary `hsl:cor:power` quantifies over all thresholds: for every
  `p < 1/2`, `k`, `C`, `L₀` and `s₀` there is `(s, ε)` with
  `HSRange 1 s ε`, `L ≥ L₀` and `s ≥ s₀` at which every accurate algorithm
  on the mixed family makes more than `C (√s L^p + L) (log s)^k` value
  queries (`cor_power`), so no bound `O(√s L^p + L)` with a fixed
  `polylog(s)` factor holds eventually in `L` and `s`
  (`cor_power_not_uniform`). The threshold `s₀` is arbitrary. The witness is
  `L = N`, `ε = e^{-N}`, `s = N²` (`power_params`) for an integer
  `N ≥ max(64, ⌈L₀⌉, s₀)` beyond an explicit constant (`power_asymptotic`), so
  `s = L²` exactly, the paper's `s = ⌈L²⌉` at integer `L` (proof of Corollary `hsl:cor:power`);
  `L ≥ 64` and `64 n ≤ s` there, so the mixed family applies at `τ = 1`.

Further choices, documented in the module docstrings:

* `evolve H τ` is by definition the release's
  `NormedSpace.exp ((-Complex.I * τ) • SparseStateOverlap.matrixOperator H)`.
* Words are `Word B = ZMod (2^{B+1})` with decode `valMinAbs z / 2^B` (range
  `(-1, 1]`) and scale `1`. Rounded numerators are capped at `2^F - 1`, so
  the unrepresentable entry `-1` (possible for `n = 1`, `b_0 = 1`) never
  occurs; the rounding error stays at most `2^{-F}`.
* Rounding precision `δ = min{a/(2√n), A/(16τ)}` (eq. `hsl:eq:round`, using
  `b_k ≥ 1/√n`).
* Padding exponent `⌈log₂ s⌉ = Nat.clog 2 s`; the locator slots are the
  padding block; the locator extensions are fixed permutations from
  `Equiv.extendSubtype`. The search families need `s ≥ 2m` and are padded to
  dimension `(n+1)m + 2 + s`, the scalar family to `n + 3 + s`.
* The general family lemmas bound the Boolean cost `p.cost w`; the native
  corollaries bound `Q = p.labelCount .value` (location calls free) and
  `p.count`.
* Deliberate strengthenings (weaker hypotheses, hence stronger theorems):
  `search_lemma` bounds the average correlation over uniformly random hidden
  positions (`search_lemma_worst` is the worst-case corollary) and does not
  assume `β₀ ≤ 1`; the precision lemma uses arbitrarily small positive
  correlation (Lemma `hsl:lem:precision`) and needs no norm hypothesis on the seed, the
  observable or the readout; the main-parameter bound
  `(τ/(2n))^n ≥ e^{-L/4} ≥ 8ε` of the proof of Theorem `hsl:thm:main` is
  proved with `16ε`, the
  form used by Lemma `odel:lem:herald`.

**Release simulator.** The release's algorithm (`release_upper`, from
`ImprovedSparseHamiltonian.simulation_log_one`) is a program over
`ImprovedSparseHamiltonian.oracle D γ 1 τ ε` on `ImprovedSparseHamiltonian.Physical`.
`Hamiltonian/ReleaseAccess` proves that every label of that oracle family is implementable on the
hard Boolean oracle at cost `hardCost` (2 per native value call, 0 for input-independent parts) for
the three hard families; `Hamiltonian/ReleaseBridge` gives the lower bounds for every program over
it under the release's endpoint error (`time_release`, `mixed_release`, `precision_release`,
`main_max_release`, `main_max_release_cost`); and `Hamiltonian/ReleaseTheta` brackets the release
simulator itself (`release_theta`, `release_theta_exists`, `release_theta_bracket`):
`c₀ (√s τ + √(sτr) + r)` is at most the worst of the three per-family value counts, and each release
count is at most `995328 (√s τ + √(sτL) + L)`, which `release_shape_eq`/`release_shape_le` relate to
the same shape up to the factor `h` (`√h` on the mixed term, `h` on the additive term, Section
`hsl:sec:main`). Choices: lower bounds on `Q = labelCount .value`, also on the weighted cost and
`p.count`, upper bound on `p.count`; arbitrary physical schedule in the bridge, the release's own
schedule in the bracket; the bracket quantifies over every program satisfying `simulation_log_one`'s
conclusion (`ReleaseSimulates`), with existence from `release_theta_exists`; heralded release forms
omitted (the release simulator is unheralded).

**Not formalized.**

* Adaptive algorithms (classical trees of measured runs) for Hamiltonian
  simulation; the theorems here cover non-adaptive programs, the class of
  `simulation_log_one`.
* The unitary `Ω(√N)` search bound, the padding of the three families to a common dimension or a
  qubit register (Section `hsl:sec:main` and the end of the proof of Theorem `hsl:thm:main`), the
  structural limitation of parity-amplitude reductions (Section `part:hsl`), and gate, workspace and
  classical circuit-generation costs.
-/
end
