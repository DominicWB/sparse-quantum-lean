import AdaptiveHamiltonianLowerBound.Theorem

/-!
# Hamiltonian-simulation lower bound for adaptive algorithms: paper-to-Lean entry point

Theorem `hsl:thm:main` of the accompanying paper (Section `part:hsl`) is formalised in the library
`SparseLowerBounds` for non-adaptive programs. This library proves it for **adaptive algorithms**:
the released adaptive protocols of the linear-system lower bound, with any admissible oracle labels.
No result from another paper is used, and the libraries `SparseLowerBounds` and
`LinearSystemLowerBound` are only imported. All declarations below are in the namespace
`AdaptiveHamiltonianLowerBound`.

* Eq. `hsl:eq:main`: `main_max_tree` (max form) and `main_exists_tree` (family form), from
  the per-family theorems `time_tree`, `mixed_tree`, `precision_tree`. The instance
  properties of the hard families (real symmetric, operator norm and maximum row and column
  norms exactly one, sparsity exactly `s`, exact dyadic entries, input-independent locators,
  dimension at most `4 s (τ + r + 1)`) are `SparseLowerBounds.Hamiltonian.hard_instances`.
  Since the accuracy hypothesis is heralded, these theorems are also Lemma
  `odel:lem:herald` for adaptive algorithms.
* Lemma `hsl:lem:search` for adaptive protocols: `search_tree_cost` (average correlation)
  and `search_tree_cost_worst`; the counting step of Lemma `hsl:lem:precision`, by the weight
  method: `precision_tree_cost`; the family bounds for any labels with search-weight growth:
  `time_tree_general`, `mixed_tree_general`, `precision_tree_general`.
* The non-adaptive theorem as a special case: `main_max_programs` (programs with admissible
  labels, which includes controlled calls) and `main_max_spec_programs` (the released
  spectator form, count `labelCount .value`), both for unit seeds.

References to the manuscript use its labels.

**Algorithm model.** `SparseLinearSystems.Protocol.Tree O F E` (the model of Theorem
`qls:thm:main` and of `LinearSystemLowerBound`): a finite classical decision tree of fresh
measured runs (`TestRun`: a program over the labelled oracle family `O` on a public unit seed,
then the two-outcome measurement of a flag isometry `F → K`), branching on the outcomes, with
a final protocol of fresh trials (uniformly random trial labels, repeated trials) that heralds
its output through an output isometry `E → K`. The workspace `K` is any Hilbert space, the
output space `E` is finite-dimensional, the label type `L` is arbitrary. A native call needs a
fixed isometric identification of `K` with a finite direct sum of copies of the native space
(the native space tensored with the other registers), so workspaces that carry native calls
are finite-dimensional; relating other register layouts, such as qubit registers, to this
form is a padding argument that is not formalised. Each fresh run ends in one two-outcome
measurement; measurements with more outcomes, and measurements inside a run followed by
classically controlled operations, are not part of the model (see below).

**Access model.** Every label must be admissible for the hard data `D`
(`Access.Admissible D (O l) (w l)`): either a native call (`Access.NativeCall`: in a fixed
isometric layout `K ≃ ⊕_{σ ∈ S} NSpace`, every spectator branch applies the identity, one
native query of `D` or the inverse of one — spectators, controlled and masked calls, inverses
and coherent choices of the native query; weight at least one), or an input-independent
unitary (any weight). For inputs `Fin n → Fin m` this is the admissibility of the linear-system
lower bound (`Access.admissible_iff_native`). The data are the released hard families
`SparseLowerBounds.Hamiltonian.timeData`, `mixedMainData` (inputs `Fin n → Fin m`,
`m = 2^{hsMu s}`) and `precisionMainData` (inputs `Fin n → Bool`). The released primitives
`NativeSparseBlockEncoding.oracles D` and `specOracles Ω D` are admissible with the weight
`Access.valueWeight` (value `1`, locations `0`: `Access.admissible_oracles`,
`Access.admissible_specOracles`). The count is `T.worstCost w`, the maximum over all
transcripts of the weighted number of calls, every fresh run counted; with `valueWeight` it is
the worst-case number of value queries (locations free, Section `hsl:sec:main`).

**Accuracy.** On every input `x`: success probability `2/3 ≤ T.successMass x`, and the
conditional output `T.conditionalDensity x`, read through an isometry
`e : E →L[ℂ] SysGarb S G` into system ⊗ garbage (`e† ∘L e = 1`, any garbage Hilbert space
`G`), is `ε`-accurate for `ψ_x = evolve (D.matrix x) τ ψ_in` (`ψ_in = searchInput`,
`scalarInput`): `DensityAccurate e ρ ψ ε` says
`|Re tr(e† (M ⊗ 1) e ρ) - Re⟪ψ, M ψ⟫| ≤ 2ε` for every self-adjoint `M` with `‖M‖ ≤ 1`, the
observable form of trace distance at most `ε` of the reduced output (eq. `hsl:eq:accuracy`);
for pure outputs it is the released `Readout.Accurate` (`densityAccurate_pure_iff`). An
unheralded algorithm is the case of success probability one.

**Hypotheses.** `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`); for the mixed family
also `L ≥ 64τ` and `s ≥ 64n/τ`, for the precision family `L ≥ 64τ`, where `n = precN τ ε`
(eq. `hsl:eq:nchoice`); `main_max_tree` and `main_exists_tree` use those families only in
these ranges, as the paper.

**Guarantees** (`Q = T.worstCost w`).

* `time_tree` (eq. `hsl:eq:timelower`): `c_T √s τ ≤ Q`, `c_T = log 2/(192π)`.
* `mixed_tree` (eq. `hsl:eq:mixrbound`): `(log 2/(384√2)) √(sτr) ≤ Q`.
* `precision_tree` (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): `r/32 ≤ Q`, and
  `√(sτr)/(64√2) ≤ Q` when `s < 64n/τ`.
* `main_max_tree` (eq. `hsl:eq:main`): for any three adaptive algorithms, accurate on the
  time, mixed and precision families respectively,
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, `c₀ = log 2/(4096π)`.
* `main_exists_tree`: one of the three families, chosen by the parameters, forces every
  accurate adaptive algorithm to have `Q ≥ c₀ (√s τ + √(sτr) + r)`.
* `time_tree_general`, `mixed_tree_general`, `precision_tree_general`: for any unitary
  labels with search-weight growth (`SearchGrowth`; for the precision family along `toBits`),
  `Q ≥ (log 2/48) n √m` (time family), `Q ≥ (log 2/48) √(mnτ)` (mixed family, `L ≥ 64τ` and
  `s ≥ 64n/τ`) and `Q ≥ n/2` (precision family, `L ≥ 64τ`).

**Proof map.** Module paths are relative to `AdaptiveHamiltonianLowerBound/`.

* `Model/Reindex`: programs, runs, trials, protocols and trees along a map of inputs, with the
  same success mass, outputs and worst-case cost (`Reindex.tree`).
* `Model/Single`: a program as a tree with one fresh trial (`Single.tree`).
* `Weight/Kernel`: weight growth for any invertible Hermitian one-coordinate weight `a` with
  row sums one (`WGrowth`, closed under products, block diagonals, layouts and circuits), the
  kernel potential `wpot` (`wpot_run`, `wpot_split`), the parity bound with
  `μ ≥ ‖a⁻¹ Z a⁻¹‖` (`wparity_bound`) and the tree bound `wtree_xor`.
* `Weight/Search`: the search weight `W_a = P_u + a² P_v + a R` (Lemma `hsl:lem:search`):
  `‖W_a D_b W_a⁻¹ - D_b‖ ≤ 4√2 a/√m + 4a²/m` (`norm_conj_reflect_sub_le`), single-bit calls
  `‖W_a Ô η‖ ≤ λ ‖W_a η‖` with `λ = 1 + 4√2 a/√m + 4a²/m` (`norm_act_w_joint_bitOp`,
  `wgrowth_bit`), `‖W_a⁻¹ Z W_a⁻¹‖ ≤ a⁻²` and `search_tree_xor`; `λ ≤ 1 + 12a/√m` for
  `a ≤ √m` (`searchLam_le_twelve`) and `λ ≤ 7a²` for `m = 2` (`searchLam_two_le`).
* `Access/Native`: admissibility over any input type and the growth `(λ²)^w` of admissible
  labels along a map of inputs (`wgrowth_admissible`: value queries are one-bit translations
  on every address block, `wgrowth_lookup`).
* `Access/HardData`: the one-bit tables of the hard families (`bitTable_value_bit`,
  `hardAccess_timeData`, `hardAccess_mixedMainData`, `hardAccess_precisionMainData` along
  `toBits`) and the admissibility of the released primitives.
* `Readout`: `DensityAccurate`, the heralded correlation `(2/3)(a₀ - 2ε)`
  (`tree_correlation`, eq. `odel:eq:heraldcorr`) and the signs (`parity_eq_parSign`,
  `bitParity_toBits`).
* `Cost`: `SearchGrowth`, `search_tree_cost` and `search_tree_cost_worst` (weight
  `a = 2β₀^{-1/(2n)}`, `search_final`) and `precision_tree_cost` (`m = 2`, `a → ∞`).
* `Families`, `Theorem`: the family bounds and the assembly (`SparseLowerBounds.Hamiltonian`'s
  `time_final`, `mixrbound`, `rbound`, `failedmix`, `assembly`).

Every theorem of the library is axiom-audited in `AdaptiveHamiltonianLowerBound/Audit.lean`.

**Formalisation choices.**

* Adaptivity is handled as in the linear-system lower bound: a positive semidefinite Gram
  kernel is carried through the protocol (the coordinate-free form of the paper's
  purification), with the weight `W_a` of Lemma `hsl:lem:search` in place of `2I - P`; a heralded
  failure contributes no output, the random-bit convention of eq. `odel:eq:heraldcorr`.
* A value query is estimated directly: on every address block it is a translation of the value
  register that depends on one bit, so it costs one growth factor `λ²`. The paper simulates it
  by two Boolean queries, so the general bounds here are twice the paper's value-query bounds
  (`log 2/48` for `log 2/96`, `n/2` for `n/4`), and the paper's constants, including `c₀`,
  follow. There is no constant deviation in the main theorems.
* The precision family (Lemma `hsl:lem:precision`) is handled with the same weight method instead of
  the Fourier-degree argument of Lemma `hsl:lem:precision`: each input bit is a one-hot string of
  length two (`toBits j k = [j k = 1]`), the search weight with `m = 2` has `‖w⁻¹ Z w⁻¹‖ ≤ a⁻²` and
  per-call growth `λ² ≤ 49a⁴`, so a positive parity correlation forces `a^{4Q-2n}` to stay bounded
  below as `a → ∞`, that is `Q ≥ n/2`.
* The correlations are those of the heralded proof (Lemma `odel:lem:herald`): `≥ 1/4` (time),
  `≥ A/2` with `A ≥ 16ε` (mixed, main parameters), `> 0` (precision, main parameters).
* Native-call layouts are indexed by `S : Type`, as in the linear-system library; the
  spectator type of `main_max_spec_programs` is in `Type`.
* The non-adaptive special cases need unit seeds and finite-dimensional workspaces (the trial
  seeds of the tree model are unit vectors and its outputs live in finite-dimensional spaces);
  the released non-adaptive theorems remain, with their weaker hypotheses.

**Not formalised.**

* Measurements inside a single run followed by classically controlled operations, and
  measurements with more than two outcomes. They can be deferred in the usual way; since a
  native call may apply different queries on different branches and is counted once, this
  does not increase the worst-case count. The reduction is not formalised, as for the
  linear-system lower bound.
* Workspaces that are not a direct sum of copies of the native space (padding).
* The further items listed as not formalised in `SparseLowerBounds/Hamiltonian/Statements.lean`
  (the unitary `Ω(√N)` search bound, the padding of the three families to a common dimension,
  the structural limitation of parity-amplitude reductions, gate, workspace and classical
  costs).
-/
