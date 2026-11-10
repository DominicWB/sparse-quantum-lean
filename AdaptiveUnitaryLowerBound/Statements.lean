import AdaptiveUnitaryLowerBound.Entry
import AdaptiveUnitaryLowerBound.Lookup
import AdaptiveUnitaryLowerBound.NonVacuity

set_option autoImplicit false

/-!
# The unitary `Ω(√N)` lower bound for adaptive algorithms: paper-to-Lean entry point

Corollary `hs:cor:unitary` of the manuscript ends: "the constant-error worst-case complexity is
`Θ(√N)`". Its lower half is stated with the reduction to unstructured search (proof of Corollary
`hs:cor:unitary`), and the corollary counts inverse calls (Corollary `hs:cor:unitary`). The lower
half is formalised in `UnitaryImplementationExtensions.LowerBound` for non-adaptive unitary query
circuits. This library proves it for **adaptive algorithms** (the protocols
`SparseLinearSystems.Protocol.Tree`, with heralded or unheralded output) and for **controlled and
controlled-inverse calls**, the convention of the manuscript's lower-bound sections (access with
inverses and the controls of Lemma `access:lem:control`, Section `hsl:sec:main`; "Purification and
deferred measurement include adaptive and randomised algorithms", proof of Lemma
`hsl:lem:precision`). All declarations below are in the namespace `AdaptiveUnitaryLowerBound`.

* Labels implemented by the released entry oracle of the search family:
  `Theorem.implementation_count_ge_tree` (adaptive),
  `Theorem.implementation_count_ge_calls_tree` (adaptive, call forms),
  `Theorem.implementation_count_ge_program` (one program, trace-distance accuracy),
  `Theorem.implementation_count_ge_program_of_error` and
  `Theorem.implementation_count_ge_calls_program_of_error` (one program, the manuscript's
  operator-norm error, eq. `hs:eq:unitaryerror`).
* The entry oracle itself as the only oracle: `Entry.heralded_tree`, `Entry.unheralded_tree`,
  `Entry.heralded_calls_tree`, `Entry.unheralded_calls_tree`, `Entry.calls_program_of_error`.
* The ordinary entry lookup with any payload: `Lookup.entry_count_ge_tree`,
  `Lookup.entry_count_ge_calls_tree`, `Lookup.entry_count_ge_program_of_error`,
  `Lookup.entry_count_ge_calls_program_of_error`.
* Unstructured search for adaptive protocols: `Kernel.tree_search_count_ge`,
  `Kernel.tree_search_count_ge_of_gap`, `Accuracy.tree_search_count_ge_of_accurate`, and the
  operator-norm program form `Theorem.program_search_count_ge_of_error`.
* Non-vacuity, the released constant-error circuit as an adaptive protocol:
  `NonVacuity.released_tree`, `NonVacuity.released_calls_bounds`.

**Algorithms.** A labelled unitary family `O : L → Fin N → W →L[ℂ] W`, every label `l`
implemented on an isometric encoding `Enc` by at most `w l` calls of the oracle
(`EncodedOracle.ImplementsOn`; inverse calls included, fixed unitaries and input-independent
labels free), and any adaptive protocol `T : Tree O F E` over `O`; the cost is the worst-case
weighted count `T.worstCost w` over all transcripts. With the call family
`AdaptiveODELowerBound.Access.callFamily O` every label is also available in its inverse,
controlled and controlled-inverse forms, each at the weight of the label (cost
`T.worstCost (fun c => w c.1)`). The oracles are the released entry oracle
`UnitaryEntryOracle.oracle (searchData N) γ η t ε` for all parameters and the ordinary entry
lookup `LookupControlledGate.oracle (searchTable N)` with an arbitrary untouched payload; both
are Boolean phase oracles of the marked strings (`Oracles.entry_oracle_eq_phase_marked`,
`Oracles.lookup_eq_phase_marked`). The workspace `W` embeds isometrically into the space of
the oracle (`Enc`): over the released entry oracle it is a subspace of
`UnitaryEntryOracle.Physical (Fin N) (ZMod 2) γ η t ε`, as in the released bound; the entry
lookup carries an arbitrary payload. The protocol bounds and
`Theorem.implementation_count_ge_program` need finite-dimensional workspace and output spaces
(lossless purification); the operator-norm program forms need none.

**Accuracy.** The package's adaptive notion: on every instance `m` success has probability at
least `s₀ > 0` (`T.successMass m`), and the conditional output, read through an isometry
`e : E → ℂ^N ⊗ G`, is `ε₀`-accurate in trace distance
(`AdaptiveHamiltonianLowerBound.DensityAccurate`) for `U_m |0⟩ = |m⟩`, the action of the
search unitary `UnitaryImplementationExtensions.SearchFamily.searchMatrix N m` on the input of
the reduction. Heralded means `s₀ = 2/3`, unheralded `s₀ = 1`. The `_program_of_error`
forms use the manuscript's operator-norm error `‖p.eval m ∘L J - J ∘L U_m‖ ≤ ε₀` on an
isometry `J` directly; `Theorem.implementation_count_ge_program` uses trace-distance accuracy
of one program on a unit seed (`Readout.Accurate`).

**Guarantees** (`N ≥ 2`).

* `Theorem.implementation_count_ge_tree`, `Theorem.implementation_count_ge_calls_tree`,
  `Lookup.entry_count_ge_tree`, `Lookup.entry_count_ge_calls_tree`: for `ε₀ ≤ 1/2`,
  `(s₀ (1 - 2ε₀))² √(N - 1) ≤ 4 Q`, positive for `ε₀ < 1/2`, with `Q = T.worstCost w`
  (`Q = T.worstCost (fun c => w c.1)` for the call forms).
* `Entry.heralded_tree`, `Entry.heralded_calls_tree`: `(1 - 2ε₀)² √(N - 1) ≤ 9 Q`;
  `Entry.unheralded_tree`, `Entry.unheralded_calls_tree`: `(1 - 2ε₀)² √(N - 1) ≤ 4 Q`, with
  `Q = T.worstCost (fun _ => 1)` the number of entry calls.
* `Theorem.implementation_count_ge_program`: the bound with `s₀ = 1` for one program over `O`
  on a unit seed with accurate output (`Readout.Accurate`).
* `Theorem.implementation_count_ge_program_of_error`,
  `Theorem.implementation_count_ge_calls_program_of_error`, `Entry.calls_program_of_error`,
  `Lookup.entry_count_ge_program_of_error`, `Lookup.entry_count_ge_calls_program_of_error`:
  operator-norm error `ε₀ ≤ 1` gives `(1 - 2ε₀ √(1 - ε₀²/4)) √(N - 1) ≤ 2 Q` with
  `Q = p.cost w` (resp. `p.cost (fun c => w c.1)`, `p.cost (fun _ => 1)`), the constant of
  `UnitaryImplementationExtensions.LowerBound.implementation_count_ge`, positive on the
  corollary's whole range `0 < ε ≤ 1/2`.
* `NonVacuity.released_tree`, `NonVacuity.released_calls_bounds` (non-vacuity): the released
  constant-error circuit of `SparseHamiltonian.UnitaryImplementation.implementation`, run once
  as an adaptive protocol (`NonVacuity.single_hyps`), meets every hypothesis of
  `Entry.unheralded_tree` and `Entry.heralded_tree` at `ε₀ = 1/4`, and, lifted to the plain
  call forms with a clean control qubit (`NonVacuity.released_calls`), those of
  `Entry.unheralded_calls_tree`, `Entry.heralded_calls_tree` and
  `Entry.calls_program_of_error`; it makes at most `queryConstant · √N` entry calls, so both
  halves of `Θ(√N)` hold for adaptive protocols in one oracle model.

**Proof map.** Module paths are relative to `AdaptiveUnitaryLowerBound/`.

* `Oracles`: the entry oracle and the entry lookup as phase oracles of the marked strings, and
  the transfer of `ImplementsOn` to phase queries.
* `Observable`: the pair observable `D_{m,m'} = |m⟩⟨m| - |m'⟩⟨m'|`.
* `Kernel`: the search bound for trees from the positive-weight adversary of
  `AdaptiveODELowerBound.Adversary` with the Schur certificate `Search.schurCert`
  (`λ = √(N - 1)`); `treeKernel_re_le_of_gap` turns a correlation gap into a kernel bound.
* `Correlation`, `Accuracy`: the heralded correlation `s₀ b` (`tree_bias_of_mass`), the pair
  gap `2 s₀ (1 - 2ε₀)` (`pair_gap`) and the search bound for accurate outputs.
* `Theorem`, `Entry`, `Lookup`: the instances for the three oracle models, with the call forms
  from `AdaptiveODELowerBound.Access.callFamily`, and the operator-norm program forms through
  `Kernel.tree_search_count_ge` applied to `AdaptiveHamiltonianLowerBound.Single.tree` with
  `UnitaryImplementationExtensions.Search.norm_inner_le_of_near`.
* `NonVacuity`: `single_hyps` from `AdaptiveHamiltonianLowerBound.Single.tree`,
  `SparseLowerBounds.Hamiltonian.accurate_of_endpoint` and
  `AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff`; `released` from
  `SparseHamiltonian.UnitaryImplementation.implementation`; the call forms through the released
  `TimeDependentHamiltonianLowerBound.plainLift` and `TimeDependentHamiltonianLowerBound.boolEmbed`
  (`count_plainLift`, `plain_calls`).

Every theorem of the library is axiom-audited in `AdaptiveUnitaryLowerBound/Audit.lean`.

**Formalisation choices.**

* Accuracy for protocols is trace-distance accuracy at the single reduction input `|0⟩`, the
  package's adaptive notion; the protocols have no input register and prepare an approximation
  of `U_m |0⟩` from public seeds (an algorithm that implements `U_m` gives one, `|0⟩` being a
  known state). Operator-norm error `ε` of a unitary program gives `ε`-accuracy
  there by composing `SparseLowerBounds.Hamiltonian.accurate_of_endpoint` with
  `AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff` (not stated as a separate theorem),
  which reaches `ε < 1/2` through the protocol bounds; the program forms take operator-norm
  error directly and cover `0 < ε ≤ 1/2`.
* Constants: `(s₀ (1 - 2ε₀))² √(N - 1) ≤ 4 Q` for protocols, from pairwise correlation gaps;
  the bound is empty at `ε₀ = 1/2`, where the gap vanishes. The success threshold `s₀` is a
  parameter (`2/3` gives the constant `9`, `1` the constant `4`).
* Per-label `EncodedOracle.ImplementsOn` is the access notion, as in the adaptive bounds of
  `AdaptiveODELowerBound.Adversary`; `UnitaryImplementationExtensions.LowerBound` states the
  non-adaptive bound for programs over the oracle itself, the one-label case with the identity
  encoding (`Entry.entryOracles`). The entry oracle is a Boolean phase oracle, hence its own
  inverse, so inverse calls are plain calls.
* `Kernel.tree_search_count_ge` (kernel form) and `Kernel.tree_search_count_ge_of_gap` (gap
  form, with a contraction that may depend on the pair) generalise the two-answer bound
  `AdaptiveODELowerBound.Adversary.tree_decision_count_ge` to `N`-outcome search;
  `Correlation.tree_bias_of_mass` generalises `AdaptiveHamiltonianLowerBound.tree_bias_general`
  (the case `s₀ = 2/3`) to any `s₀ > 0`.
* The instance `[NeZero N]` is kept alongside `2 ≤ N` for the input `0 : Fin N`, as in
  `UnitaryImplementationExtensions.LowerBound.implementation_count_ge`.

**Not formalised.**

* The endpoint `ε₀ = 1/2` of trace-distance accuracy, for protocols and for
  `Theorem.implementation_count_ge_program`: pairwise kernels give nothing there (the output
  `(|m⟩⟨m| + |m'⟩⟨m'|)/2` is within `1/2` of both targets), and for `N = 2` a query-free
  protocol with maximally mixed output meets the hypotheses, so a bound would need `N ≥ 3` and
  a global search argument. For unitary programs with operator-norm error the endpoint is
  covered.
* Operator-norm error for adaptive protocols, which has no natural meaning for mixed or
  heralded outputs, and a bridge from a pure-output norm error `ε` to trace-distance accuracy
  `ε √(1 - ε²/4)`.
* Circuit-size, workspace and classical circuit-generation costs.
* Measurements inside a run: the protocols `Tree` measure only flags at the end of fresh runs;
  algorithms with measurements inside a run are treated in `DeferredMeasurementLowerBounds`.

**Provenance.** No result from another paper is used; the search bound is derived from the
package's positive-weight adversary for trees. The released libraries `SparseHamiltonian`,
`SparseODE`, `SparseLinearSystems`, `SparseLowerBounds`, `LinearSystemLowerBound`,
`ODELowerBoundExtensions`, `AdaptiveHamiltonianLowerBound`, `AdaptiveODELowerBound`,
`UnitaryImplementationExtensions` and (for `NonVacuity`) `TimeDependentHamiltonianLowerBound`
are only imported; no released module is changed.
`UnitaryImplementationExtensions/Statements.lean` predates this library and lists lower bounds
against adaptive or controlled-call algorithms as outside it; they are proved here. Algorithms
with measurements inside a run are treated in `DeferredMeasurementLowerBounds`
(`DeferredMeasurementLowerBounds.Corollaries.entry_count_ge_measured`,
`DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured`; not imported
here). References to the manuscript use its labels.
-/
