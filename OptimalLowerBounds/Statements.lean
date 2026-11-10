import OptimalLowerBounds.Access
import OptimalLowerBounds.Optimal
import OptimalLowerBounds.Embedding
import OptimalLowerBounds.Enlarge
import OptimalLowerBounds.TwoNorm
import OptimalLowerBounds.Denominator
import OptimalLowerBounds.AdaptiveAccess
import OptimalLowerBounds.Adaptive
import OptimalLowerBounds.Measured

set_option autoImplicit false

/-!
# Lower bounds for the improved-precision simulations: paper-to-Lean entry point

The manuscript adds three lower-bound results to the Hamiltonian-simulation lower bound
`hsl:thm:main` (formalised in the released library
`SparseLowerBounds`, statement guide `SparseLowerBounds/Hamiltonian/Statements.lean`):

1. the `Θ` statement of Theorem `hs:thm:optimal` (eq. `hs:eq:optimal-theta`; after Theorem
   `hsl:thm:main`, "Theorem `hs:thm:optimal` matches it term by term") and "the stronger lower bound
   `Ω(√(sτL))` cannot hold uniformly";
2. Proposition `hsl:prop:two-norm` (Section `twonorml:sec:lower`), a matching lower bound with a
   maximum-entry promise: the matching lower bound of Theorem `hs:thm:two-norm` "is established on
   the aligned parameter families of Proposition `hsl:prop:two-norm`";
3. the paragraphs after the proof of Proposition `hsl:prop:two-norm` ("its precision denominator
   must contain this time scale, rather than `η|t|`").

Section 4 proves their forms for adaptive protocols and for algorithms with measurements inside a
run, with controlled and inverse oracle calls. The manuscript states no separate result for these:
its lower bounds reduce to `hsl:thm:main`, which covers them ("Purification and deferred measurement
include adaptive and randomised algorithms", proof of Lemma `hsl:lem:precision`; access with
inverses and the controls of Lemma `access:lem:control`).

No result from another paper is used. References to the manuscript use its labels.
Every theorem of the library and every field of the `Prop` structure `TwoNormInstance` is
axiom-audited in `OptimalLowerBounds/Audit.lean`.

**Naming convention.** In the Lean statements of sections 2 and 4 about the enlarged families the
variable `s` is the base sparsity `s₀` of `hsl:thm:main`; the enlarged families have sparsity
`s * m`. All declarations are in the namespace `OptimalLowerBounds`; names below are relative to
it, except the names of other libraries, which are fully qualified. `HSRange`,
`hsL`, `hsH`, `hsR`, `precN`, `c0`, `cT`, `timeData`, `mixedMainData`, `precisionMainData`,
`searchHam`, `scalarHam`, `searchInput`, `scalarInput`, `evolve`, `HardInstance`, `hardCost`,
`specOracles` are in `SparseLowerBounds.Hamiltonian` (or `SparseLowerBounds`), `Simulates`,
`physOracle` are `NativeSignedFactor.Simulates`, `NativeSignedFactor.physOracle`, and
`valueWeight` is `AdaptiveHamiltonianLowerBound.Access.valueWeight`.

## Access model and accuracy

As for `hsl:thm:main`: the hidden input is read only through the native sparse primitives of
`SparseHamiltonian.NativeSparseBlockEncoding.Data` (in-place row and column locators and the
reversible value oracle, inverses counted); `Q = p.labelCount .value` counts value calls and
location calls are free, as the manuscript allows (they are input-independent). A value call costs
two Boolean queries to the hidden bits (`hardCost`). Three program models are covered here, and
the adaptive and measured models in section 4:

* the **spectator form**, programs over `specOracles Ω D` (the primitives on every copy of an
  untouched register `ℂ^Ω`; for unitary programs, controlled value calls reduce to it, as
  documented for `hsl:thm:main`; section 4 covers them directly), and the **native form**,
  programs over `oracles D`, both with the
  trace-distance accuracy `SparseLowerBounds.Readout.Accurate` of eq. `hsl:eq:accuracy` (mixed
  outputs allowed, no postselection);
* the **common form** of the improved-precision upper bounds, `Simulates (physOracle D) H t ε q`
  (a known isometric input, one program over `CoherentQuerySchedule.oracle (physOracle D)`,
  unitary on every instance, at most `q` calls counting adjoints, full-output error `ε`).

`Access`: every label of a family with a Boolean access certificate
(`SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess`, cost `hardCost`) obeys the three per-family
bounds of `hsl:thm:main` (`time_of_access`, `mixed_of_access`, `precision_of_access`) and their max
form (`main_max_of_access`). The common form is certified from the native primitives
(`physAccess`, `commonAccess`; `timeCommonAccess`, `mixedCommonAccess`, `precisionCommonAccess`):
each label is one native call inside spectators and fixed relabellings.

## 1. Theorem `hs:thm:optimal`: the worst-case query complexity

`simulationCost D t ε` is the infimum of the query bounds `q` with
`Simulates (physOracle D) H t ε q` (one program for every instance of `D`: the worst case over the
instances).

* `time_common`, `mixed_common`, `precision_common`: the per-family bounds for every common-form
  program with endpoint error `ε` (eqs. `hsl:eq:timelower`, `hsl:eq:mixrbound`, `hsl:eq:rbound`,
  `hsl:eq:failedmix`);
* `main_max_simulates`: `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)` for any common-form
  simulations of the three hard families of `hsl:thm:main` at time `τ`;
* `optimal_on_hard`: the hard families (row and column norms exactly one) meet the hypotheses of
  `OptimalSparseSimulation.optimal_simulation` with `η = 1`, `t = τ`, so each is simulated with at
  most `2·10¹² (√s τ + √(sτr) + r)` queries (`bound_eq`, `rb_eq_hsR`: the precision parameters
  agree);
* **`optimal_theta`** (`hs:eq:optimal-theta`): for `τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`,
  `c₀ S ≤ max(simulationCost_T, simulationCost_M, simulationCost_P) ≤ 2·10¹² S`,
  `S = √s τ + √(sτr) + r`, `r = L/log(e + L/τ)`, `c₀ = log 2/(4096π)`;
* **`not_uniform_sqrt`** (Section `part:hsl`): for every `c > 0` there are `τ = 1`, `s`, `ε` in the
  range of `hsl:thm:main` at which every Hermitian data with row and column norms at most one (in
  particular each hard family) is simulated with fewer than `c √(sτL)` queries (`bound_lt_sqrt`:
  `s = N²`, `ε = e^{-N}`).

## 2. Proposition `hsl:prop:two-norm`

**The families** (`Embedding`, `Enlarge`). `enlargeData` builds `c H ⊗ 𝟙𝟙ᵀ` from one-bit native
data (`SparseLowerBounds.Hamiltonian.bitData`): the enlarged address `((i, a), (j, b))` reads the
word of `(i, j)` (`enlargeTable`), the lists are `(loc i k, b)` (`enlargeLoc`), and the public
decoder multiplies by `c` (`enlargeMatrix`, `enlargeData_matrix`). The native primitives are those
of the unscaled enlargement (`oracles_enlargeData`), so each value call costs two Boolean queries
of the same hidden bits (`implementsOn_enlargeData`, `implementsOn_enlargeData_spec`).
`timeTwo θ s₀ _ m _ c _`, `mixedTwo`, `precisionTwo` enlarge the three hard families of
`hsl:thm:main` at sparsity `s₀` and time `θ`; `μ = |c|`, `η = |c|√m`, and `c m t = θ` fixes the
sign of `c` by that of `t` (`exists_coeff`: every `μ > 0`, `t ≠ 0`).

* `two_instances` (statement of the proposition): `TwoNormInstance D c m`, i.e. real symmetric,
  entries of modulus at most `μ` with equality somewhere, row and column Euclidean norms at most
  `η` with equality somewhere, maximum row and column sparsity exactly `s = s₀ m`, exact words
  `c v/2^B` with the position-independent decoder `z ↦ c · valMinAbs z/2^B`, input-independent
  locators (`enlargeData_twoNormInstance`); for a dyadic `c = M/2^p` every entry is the dyadic
  `(M v)/2^{B+p}` (`TwoNormInstance.dyadic_entries`);
* `evolve_enlarge` (eq. `twonorml:eq:embedded-evolution`): `e^{-itH_X} V ψ = V e^{-iθ H⁰_X} ψ`,
  `V ψ = ψ ⊗ u_m` (`embedU`, `matrixOperator_enlarge_comp`, `exp_comp_eq_comp_exp`);
  `accurate_of_embedU`: discarding the ancilla preserves trace-distance accuracy;
* `two_shape_eq` (eq. `twonorml:eq:scaling`): `√s η|t| + √(sμ|t| r_μ) + r_μ =
  √s₀ θ + √(s₀ θ r_μ) + r_μ`;
* **`two_norm_main_max`** (spectator form), **`two_norm_main_max_native`** (native form) and
  **`two_norm_main_max_simulates`** (common form) (eq. `twonorml:eq:lower`): for any three
  algorithms accurate on the three enlarged families for `e^{-itH_X}(ψ_in ⊗ u_m)`,
  `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)` with `r_μ = L/log(e + L/θ)`,
  `θ = η²|t|/μ`; the per-family forms are `time_two_of_access`, `mixed_two_of_access`,
  `precision_two_of_access`, the general max form `two_norm_max_of_access`;
* `two_opNorm`, `eta_lt_opNorm_bound` (Section `twonorml:sec:lower`): the enlarged Hamiltonians have
  operator norm at least `μ m` (`norm_enlarge_ge`), which exceeds `η = μ√m` for `m ≥ 2`.

**The matching upper bound** (the paragraph before Proposition `hsl:prop:two-norm`).
`two_on_aligned_of`, `two_on_aligned`: every `TwoNormInstance` meets the hypotheses of
`TwoNormSimulation.two_norm_simulation` (`μ ≤ η ≤ √s μ`, `η²|t|/μ = θ ≥ 1`), so it is simulated with
at most `2·10¹² S'` queries; **`two_norm_theta`**:
`c₀ S' ≤ max(simulationCost_T, simulationCost_M, simulationCost_P) ≤ 2·10¹² S'`,
`S' = √s η|t| + √(sμ|t| r_μ) + r_μ`, on the aligned families.

## 3. The logarithmic denominator must also change

With `m = 4^k` (`denomM`), `μ = 2^{-k} = m^{-1/2}` (`denomMu`), `θ = 2^k = √m` (`denomTheta`),
`L = √m log m` (`denomL`), `ε = e^{-L}` (`denomEps`), `s = 2m`, `η = t = 1`
(`denom_params`, eq. `twonorml:eq:counterexample-parameters`), `denomData k` is the signed scalar
chain of Lemma `hsl:lem:precision` (sparsity two) of length `n = ⌊r_μ/4⌋` at time `θ`, enlarged
(`denom_instance`).

* `wrongShape s η μ t ε = √s η|t| + √(sμ|t| r̃) + r̃` with the old `r̃ = L/log(e + L/(η|t|))`;
  for `k ≥ 1`, `wrong_r_bounds`: `2^k/2 ≤ r̃ ≤ 2^{k+1}` (`r̃ = Θ(√m)`), and `wrongShape_le`: at
  most `6·2^k` (eq. `twonorml:eq:wrong-denominator`);
* `denom_rmu`: `r_μ = √m log m/log(e + log m)`; `denom_lower`
  (eq. `twonorml:eq:necessary-denominator`): for `k ≥ 47` every accurate algorithm makes at least
  `r_μ/32` value queries (`precision_scalar_of_access`, Lemma `hsl:lem:precision` at any sparsity);
* **`wrong_denominator`** (spectator form) and **`wrong_denominator_simulates`** (common form):
  for every `C` and every `k ≥ max(47, ⌈(384 C)² + 3⌉)` more than
  `C (√s η|t| + √(sμ|t| r̃) + r̃)` queries are needed (`wrong_lt_rmu`, `wrong_lt_of_lower`);
* `denom_simulates`: for `k ≥ 2`, `hs:thm:two-norm` simulates `denomData k` with
  `2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` queries (`two_on_aligned_of`): the corrected precision
  parameter works where the old one fails, and the lower bounds are not vacuous.

## 4. Adaptive protocols and measured algorithms

The lower bounds of sections 1-3 in the native and common access models (eq. `hsl:eq:main` over
the common oracle in max form, Proposition `hsl:prop:two-norm` in max form and per family, and the
denominator statements) also hold, with the same constants, for algorithms that measure and
branch, over every admissible native access (modules `AdaptiveAccess`, `Adaptive`, `Measured`);
the statements over arbitrary certified (`PhaseAccess`) families are not extended (see Scope).
Two models of the package are used:

* **adaptive protocols** `SparseLinearSystems.Protocol.Tree O F E` (fresh measured runs with
  classical branching on the outcomes, random trial labels and repeated trials, a heralded
  output; the model of `AdaptiveHamiltonianLowerBound`);
* **measured algorithms** `DeferredMeasurementLowerBounds.Model.Measured O E` (oracle calls,
  forward or inverse; input-independent instruments with finitely many outcomes in the middle of a
  run, followed by the classically chosen continuation of the observed outcome; heralded output;
  rejection), on one persistent workspace, from a unit initial vector.

Both models fix no register layout; both need a finite-dimensional output space `E`.

**Access.** Every label is admissible for the data
(`AdaptiveHamiltonianLowerBound.Access.Admissible`): a native call (in a fixed isometric layout of
the workspace as a finite direct sum of copies of the native query space, every copy applies the
identity, one native query or its inverse; weight at least one) or an input-independent unitary
(any weight). This includes spectators, masks, controlled and inverse calls and coherent choices
of the native query; a workspace that carries a native call is finite-dimensional. Named
instances: `admissible_callFamily` (the plain, inverse, controlled and controlled-inverse forms
`AdaptiveODELowerBound.Access.callFamily` of admissible labels are admissible with the weight of
their label; `formOp_eq_fiber`, `nativeCall_formBranch`); `admissible_common` and
`admissible_common_calls` (for data with input-independent locators, the common oracle of the
upper bounds and its call forms, from the normal form `common_normal_form`: one native call
inside spectators and fixed relabellings, `physWrap`, `isWrap_physWrap`, `physOracle_eq_wrap`).
The enlarged data have one-bit entries (`hardAccess_searchTwo`, `hardAccess_scalarTwo`,
`hardAccess_timeTwo`, `hardAccess_mixedTwo`, `hardAccess_precisionTwo`, `hardAccess_denomData`),
so admissible labels have search-weight growth and the weight method of
`AdaptiveHamiltonianLowerBound` applies.

**Accuracy and count.** Success probability at least `2/3` on every input, and conditional output
`ε`-accurate in trace distance (`AdaptiveHamiltonianLowerBound.DensityAccurate`, the observable
form of eq. `hsl:eq:accuracy` for mixed outputs) for `e^{-itH_X}(ψ_in ⊗ u_m)`, read through an
isometry into system ⊗ any garbage. `densityAccurate_of_embedU` (with `outObs_regroup`) discards
the ancilla from a mixed output, and `densityAccurate_search_of_two`,
`densityAccurate_scalar_of_two` turn accuracy on an enlarged family into accuracy on the original
family at time `θ = c m t`. The count is the worst-case weighted number of calls `worstCost w` over
all transcripts, inverse calls included; with `valueWeight` it counts value calls. A measured
algorithm is deferred (`DeferredMeasurementLowerBounds.Corollaries.deferred_admissible`): an
adaptive protocol over admissible labels with the same success mass, an equally accurate output
(the records join the garbage) and no larger worst-case count.

* Adaptive protocols: the per-family bounds `time_two_tree`, `mixed_two_tree`,
  `precision_two_tree` and the max form **`two_norm_main_max_tree`** (eq. `twonorml:eq:lower`,
  `c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ) ≤ max(Q_T, Q_M, Q_P)`);
* measured algorithms: the per-family bounds `time_two_measured`, `mixed_two_measured`,
  `precision_two_measured` and the max form **`two_norm_main_max_measured`** (admissible labels);
  **`two_norm_main_max_measured_calls`** (the four call forms of the native primitives with
  spectators, value forms counted) and **`two_norm_main_max_measured_common`** (the common oracle,
  value calls counted);
* **`main_max_measured_common`**: eq. `hsl:eq:main` for measured algorithms over the common oracle
  of the original families (the lower half of `hs:thm:optimal` in its own query model, value calls
  counted);
* the denominator paragraph: `precision_scalar_tree` (Lemma `hsl:lem:precision` for adaptive
  protocols at any sparsity), `denom_lower_tree`, **`wrong_denominator_tree`** (adaptive
  protocols), `denom_lower_measured`, **`wrong_denominator_measured`** (admissible labels) and
  **`wrong_denominator_measured_common`** (common oracle), with `wrong_lt_of_lower`;
* non-vacuity and the brackets: a common-form simulation is a measured algorithm over the common
  oracle with success probability one, density accuracy and worst-case value-call count at most
  its query bound (`measured_of_simulates`, `measured_on_aligned_of`, `measured_on_aligned`).
  **`optimal_measured_theta`** and **`two_norm_measured_theta`**: the released simulations of
  `hs:thm:optimal` (resp. `hs:thm:two-norm`) are measured algorithms over the common oracle of the
  original (resp. aligned enlarged) families that meet every hypothesis of
  `main_max_measured_common` (resp. `two_norm_main_max_measured_common`) and make at most
  `2·10¹² S` (resp. `2·10¹² S'`) value calls in the worst case, while the lower bound
  `c₀ S ≤ max(Q_T, Q_M, Q_P)` (resp. `c₀ S'`) holds for them and for every other accurate
  measured algorithm over admissible labels; `denom_measured` for `denomData k`, `k ≥ 2`.

## Scope and differences from the manuscript

* The bounds are stated in max form over the three families, as for `hsl:thm:main` ("We need not
  find one matrix on which all three mechanisms are simultaneously difficult"); the constants are
  those of `hsl:thm:main` (`c₀ = log 2/(4096π)`), also for the enlarged families: the
  multiplication by the public `μ` is in the decoder, so an enlarged value call is one original
  value call (the manuscript's "at most two old value queries", with which "the reduction has
  constant query overhead", is not needed).
* `μ` is any positive real (the bound does not use dyadicity); exact dyadic entries for dyadic `μ`
  are `TwoNormInstance.dyadic_entries`. Negative times use the coefficient `c = -μ`
  (`exists_coeff`), the manuscript's negated Hamiltonians.
* "Worst-case sparse-query complexity" is formalised as `simulationCost` in the common form for the
  `Θ` brackets of unitary programs (`optimal_theta`, `two_norm_theta`, all queries counted), as
  lower bounds on every program for the spectator and native forms, and, for measured algorithms
  (section 4), as the universal lower bound together with released measured algorithms meeting it
  up to the constant (`optimal_measured_theta`, `two_norm_measured_theta`, value calls counted);
  no infimum over measured algorithms is defined.
* The counterexample uses the padded signed chain at sparsity two (`scalarHam n 2 θ`), so
  `s = 2m` exactly; the numerics of `hsl:thm:main` (`precN_range`, `sixteen_eps_le`, `rbound`)
  are invoked with the sparsity parameter `32` of `HSRange`, which they do not use.
* The operator-norm remark is formalised as the lower bound `μ m ≤ ‖H_X‖`.
* Section 4: the adaptive bounds use the weight method of `AdaptiveHamiltonianLowerBound`, which
  needs the operator structure of admissible labels; the statements over arbitrary certified
  families (`PhaseAccess`: `time_of_access`, …, `two_norm_max_of_access`,
  `precision_scalar_of_access`, `denom_lower` and their per-family forms) are for unitary programs
  only. As in `DeferredMeasurementLowerBounds`, the worst case is over all transcripts, including
  those of probability zero; replacing every subtree reached with probability zero on every input
  by a rejection changes no success mass and no output, so the bounds also hold for the worst
  case over the transcripts of positive probability (not formalised).
* Section 4: a native call needs a fixed isometric identification of the workspace with a finite
  direct sum of copies of the native query space, so a workspace that carries native calls is
  finite-dimensional; relating other register layouts, such as qubit registers, to this form is a
  padding argument that is not formalised (as in `AdaptiveHamiltonianLowerBound`). Both models
  need a finite-dimensional output space; embedding an adaptive protocol as a measured algorithm
  (`DeferredMeasurementLowerBounds.Model.ofTree`) needs a finite-dimensional workspace.
* Section 4, not restated: family forms, in which one family chosen by the parameters bounds
  every algorithm (they follow from the max forms by contradiction, as
  `AdaptiveHamiltonianLowerBound.main_exists_tree`); per-family measured bounds for the original
  families (from `deferred_admissible` with `AdaptiveHamiltonianLowerBound.time_tree`, …); and
  forms over named access families that follow from the stated forms with the admissibility
  lemmas: measured forms over the call forms of the common oracle (`admissible_common_calls` with
  `two_norm_main_max_measured`), per-family measured bounds over the common oracle for the
  enlarged families (`admissible_common` with `time_two_measured`, …), tree forms over the named
  access families, and call-form and common-oracle forms of the adaptive-protocol denominator
  statements.
* Covered by the released libraries, not restated here: the constant-error `Θ(√N)` of Corollary
  `hs:cor:unitary-optimal` (`UnitaryImplementationExtensions`), the structural limitation of
  parity-amplitude reductions (Section `part:hsl`; `LowerBoundRemarks.ParityAmplitude`) and
  Corollary `hsl:cor:power` (`SparseLowerBounds.Hamiltonian.cor_power`).
-/
