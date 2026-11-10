import MeasuredUnitaryLowerBound.Endpoint.Calls
import MeasuredUnitaryLowerBound.NonVacuity
import MeasuredUnitaryLowerBound.OperatorNorm.NonVacuity

set_option autoImplicit false

/-!
# The unitary `Ω(√N)` lower bound at trace-distance error `1/2`: paper-to-Lean entry point

Corollary `hs:cor:unitary` of the manuscript allows any error `0 < ε ≤ 1/2` and ends: "the
constant-error worst-case complexity is `Θ(√N)`". Its lower half is the reduction to unstructured
search (proof of Corollary `hs:cor:unitary`: `U_m |0⟩ = |m⟩`), and the corollary counts inverse
calls (Corollary `hs:cor:unitary`). The lower-bound setting of the manuscript gives access with
inverses and the controls of Lemma `access:lem:control` (Section `hsl:sec:main`), and the closing
sentence of the proof of `hsl:lem:precision` covers "Purification and deferred measurement include
adaptive and randomised algorithms" (proof of Lemma `hsl:lem:precision`).
`AdaptiveUnitaryLowerBound` and `DeferredMeasurementLowerBounds` prove the lower half for adaptive
and measured algorithms at every fixed trace-distance error `ε₀ < 1/2`; their factors `(1 - 2ε₀)²`
and `1 - 2 √(ε₀ (1 - ε₀))` vanish at `ε₀ = 1/2`. This library proves it on the whole range
`ε₀ ≤ 1/2`, endpoint included, for adaptive protocols (heralded or not), for algorithms with
measurements inside a run, and for both with controlled and controlled-inverse calls. It also states
the manuscript's operator-norm error `‖A_U - U‖ ≤ ε` (eq. `hs:eq:unitaryerror`) for measured
algorithms, through a purification of their output, with the sharp per-input trace distance
`ε √(1 - ε²/4)` (`OperatorNorm`). All declarations below are in the namespace
`MeasuredUnitaryLowerBound`.

**Paper-to-Lean map.** Namespaces and files (relative to `MeasuredUnitaryLowerBound/`):
`Global` is `Global/Sum.lean`, `Global/Kernel.lean` and `Global/Reads.lean`; `Reading` is
`Reading.lean`; `Adaptive` is `Endpoint/Tree.lean` and `Endpoint/Entry.lean`; `Deferred` is
`Endpoint/Measured.lean`; `Calls` is `Endpoint/Calls.lean`; `NonVacuity` is `NonVacuity.lean`;
`OperatorNorm` is the directory `OperatorNorm/` (`Sharp`, `Notion`, `Accuracy`, `Programs`,
`Deferred`, `Bound`, `CallsBound`, `ProgramBound`, `NonVacuity`).

* Adaptive protocols over labels implemented by the released entry oracle of the search family:
  `Adaptive.implementation_count_ge_tree_endpoint`,
  `Adaptive.implementation_count_ge_calls_tree_endpoint` (call forms) and
  `Adaptive.implementation_count_ge_program_endpoint` (one program on a unit seed).
* The ordinary entry lookup with any payload: `Adaptive.entry_count_ge_tree_endpoint`,
  `Adaptive.entry_count_ge_calls_tree_endpoint`.
* The released entry oracle as the only oracle, at `ε₀ = 1/2`:
  `Adaptive.unheralded_tree_half`, `Adaptive.heralded_tree_half`,
  `Adaptive.unheralded_calls_tree_half`, `Adaptive.heralded_calls_tree_half`, and the `√N`
  forms `Adaptive.unheralded_tree_sqrt`, `Adaptive.heralded_tree_sqrt`,
  `Adaptive.unheralded_calls_tree_sqrt`, `Adaptive.heralded_calls_tree_sqrt`
  (through `Adaptive.sqrt_le_of_half`).
* Measured algorithms (`DeferredMeasurementLowerBounds.Model.Measured`):
  `Deferred.implementation_count_ge_measured_endpoint`,
  `Deferred.entry_count_ge_measured_endpoint`, `Deferred.implementation_count_ge_measured_half`,
  `Deferred.implementation_count_ge_measured_sqrt`.
* Measured algorithms over the four call forms:
  `Calls.implementation_count_ge_measured_calls_endpoint`,
  `Calls.implementation_count_ge_measured_calls_half`,
  `Calls.implementation_count_ge_measured_calls_sqrt`.
* Unstructured search: `Adaptive.tree_search_count_ge_endpoint`,
  `Deferred.search_count_ge_measured_endpoint`, `Calls.search_count_ge_measured_calls_endpoint`,
  and the readout forms `Global.tree_count_ge_of_reads`, `Global.program_count_ge_of_reads`.
* Non-vacuity: `NonVacuity.released_tree_half`, `NonVacuity.released_calls_tree_half`,
  `NonVacuity.released_measured_half`, `NonVacuity.released_measured_calls_half`.
* Operator-norm error for measured algorithms (`hs:cor:unitary`, range `0 < ε ≤ 1/2` in Corollary
  `hs:cor:unitary`; measured algorithms by purification and deferred measurement, proof of Lemma
  `hsl:lem:precision`): the notion `OperatorNorm.NormImplements`; the sharp passage to trace
  distance `OperatorNorm.abs_re_inner_sub_le_sharp`, `OperatorNorm.accurate_of_endpoint_sharp`,
  `OperatorNorm.densityAccurate_of_normImplements` (eq. `hs:eq:unitaryerror`); the bounds
  `OperatorNorm.implementation_count_ge_measured_norm`, `OperatorNorm.entry_count_ge_measured_norm`,
  `OperatorNorm.implementation_count_ge_measured_norm_half`,
  `OperatorNorm.implementation_count_ge_measured_norm_sqrt`; over the four call forms (with inverses
  and the controls of Lemma `access:lem:control`, Section `hsl:sec:main`)
  `OperatorNorm.implementation_count_ge_measured_calls_norm` and its `_half` and `_sqrt` forms;
  containment of the unitary programs of the corollary `OperatorNorm.normImplements_runAll`,
  `OperatorNorm.normImplements_of_deferred`, `OperatorNorm.implementation_count_ge_program_norm`,
  `OperatorNorm.implementation_count_ge_calls_program_norm` (through
  `OperatorNorm.global_of_pairwise`); non-vacuity `OperatorNorm.released_measured_norm`,
  `OperatorNorm.released_measured_calls_norm`.

**Algorithms.** Adaptive protocols `SparseLinearSystems.Protocol.Tree` over a labelled unitary
family `O : L → Fin N → W →L[ℂ] W`, every label implemented on an isometric encoding by at most
`w l` calls of the oracle (`EncodedOracle.ImplementsOn`, inverse calls included), on
finite-dimensional workspace and output spaces, with cost the worst-case weighted count
`T.worstCost w` over all transcripts; with `AdaptiveODELowerBound.Access.callFamily` every label
is also available in its inverse, controlled and controlled-inverse forms at the weight of the
label (cost `T.worstCost (fun c => w c.1)`). Measured algorithms
`DeferredMeasurementLowerBounds.Model.Measured O E` (measurements, resets and classical control
inside a run) run on the input `J |0⟩` of an isometric encoding `J`, with cost the worst-case
number of oracle calls `M.worstCost (fun _ => 1)`; over `callFamily O` each call form counts
once. The oracles are the released entry oracle
`UnitaryEntryOracle.oracle (searchData N) γ η t ε` for all parameters and the ordinary entry
lookup `LookupControlledGate.oracle (searchTable N)` with any payload.

**Accuracy.** On every instance `m` success has probability at least `s₀ > 0` (`p₀ > 0` for
measured algorithms), and the conditional output, read through an isometry
`e : E → ℂ^N ⊗ G`, is within trace distance `ε₀` of `U_m |0⟩ = |m⟩`
(`AdaptiveHamiltonianLowerBound.DensityAccurate`). The `_half` forms take `ε₀ = 1/2`, with
success probability one (unheralded and measured forms) or at least `2/3` (heralded forms); the
measured `_half` forms ask accuracy for every unit input `ψ` with target `U_m ψ` (an
implementation of `U_m`) and use `ψ = |0⟩`. The operator-norm forms ask
`OperatorNorm.NormImplements M J e m U_m ε₀` for every `m`: some finite Kraus family `A_r` of
the output on the encoded inputs `J ψ` (`successDensity = ∑_r |A_r ψ⟩⟨A_r ψ|`) succeeds with
probability `‖ψ‖²`, and its read dilation `ψ ↦ (e (A_r ψ))_r` is within operator norm `ε₀` of
`U_m ⊗ γ` for a unit garbage vector `γ` over the records.

**Quantifiers.** `N ≥ 2` with `[NeZero N]`, all parameters `γ η t ε` of the released entry
oracle, every algorithm of the class, every isometric readout `e`, every `ε₀ ≤ 1/2` and every
`s₀ > 0` (`p₀ > 0`).

**Guarantees** (`Q` the cost above).

* Tree, program and plain measured forms: `(s₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) Q`.
* Measured call forms: `(p₀ (N (1 - ε₀) - 1))² ≤ 32 (N - 1) √(N - 1) Q`.
* At `ε₀ = 1/2`: `(N - 2)² ≤ 16 (N - 1) √(N - 1) Q` (unheralded trees, call-form trees and
  plain measured algorithms), `(N - 2)² ≤ 36 (N - 1) √(N - 1) Q` (heralded trees, `s₀ = 2/3`)
  and `(N - 2)² ≤ 128 (N - 1) √(N - 1) Q` (measured call forms).
* For `N ≥ 3`: `√(N - 1) ≤ 64 Q` (unheralded trees, unheralded call-form trees, plain measured
  algorithms), `√(N - 1) ≤ 144 Q` (heralded trees, heralded call-form trees) and
  `√(N - 1) ≤ 512 Q` (measured call forms); `Adaptive.sqrt_le_of_half` turns
  `(N - 2)² ≤ C (N - 1) √(N - 1) Q` into `√(N - 1) ≤ 4 C Q`, which gives the remaining
  combinations (heralded measured algorithms, the entry lookup) from the endpoint forms.
* Operator norm (`s = ε₀ √(1 - ε₀²/4)`, `ε₀ ≤ 1/2`, success probability one):
  `(N (1 - s) - 1)² ≤ 4 (N - 1) √(N - 1) Q` (measured algorithms, the entry lookup, and unitary
  programs with `Q = p.cost 1`), with `32` over the call forms; at `ε₀ = 1/2`, `s = √15/8`;
  for `N ≥ 3`, `√(N - 1) ≤ 64 Q` (`512` over the call forms). Since `s ≤ √15/8 < 1/2`, these
  bounds are not empty at `N = 2`.
* Non-vacuity: the released constant-error circuit of
  `SparseHamiltonian.UnitaryImplementation.implementation` meets the hypotheses of the `_half`
  forms in each class (trees, call-form trees, measured algorithms, measured call forms) and
  makes at most `queryConstant · √N` entry calls, so both halves of `Θ(√N)` hold in one oracle
  model. Run and output in full, it implements every `U_m` within operator-norm error `1/4`, so
  it also meets the hypotheses of the operator-norm forms (`OperatorNorm.released_measured_norm`,
  `OperatorNorm.released_measured_calls_norm`).

**Proof map.** `Global.Sum` → `Global.Kernel` → `Global.Reads` → `Reading` →
`Endpoint.Tree`, `Endpoint.Entry` → `Endpoint.Measured` → `Endpoint.Calls` → `NonVacuity`;
`OperatorNorm.Sharp` → `OperatorNorm.Notion` → `OperatorNorm.Accuracy`, `OperatorNorm.Programs`,
`OperatorNorm.Deferred` → `OperatorNorm.Bound` → `OperatorNorm.CallsBound` →
`OperatorNorm.ProgramBound` → `OperatorNorm.NonVacuity`.

* `Global.Sum`: Cauchy-Schwarz over the ordered pairs (`sq_sum_adversary_le`) and the real
  inequality `N b² ≤ 2 (N - 1) ∑_{x ≠ x'} (1 - k(x, x'))` from summed gaps (`sum_le_of_gaps`).
* `Global.Kernel`: the summed adversary progress `∑_{x ≠ x'} (1 - Re κ_T) ≤ 2 √(N - 1) N Q`
  (`adversary_deficit_le`, from `AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le`
  with the Schur certificate `UnitaryImplementationExtensions.Search.schurCert`) and the kernel
  form of the bound (`tree_count_ge_of_kernel_gaps`).
* `Global.Reads`: summed pair gaps of readout effects (`sum_pair_gaps`, `pair_gap_eq`) and the
  readout forms for trees (`AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap`) and for
  one program (`SparseLowerBounds.PositiveAdversary.norm_inner_le_of_gap`).
* `Reading`: the read effects `outObs e |y⟩⟨y|` sum to the identity, their read values
  `DeferredMeasurementLowerBounds.Corollaries.readProb` sum to the trace of the output (the
  success probability; through `DeferredMeasurementLowerBounds.Model.ofTree` for trees), and an
  accurate output gives `N r(x, x) - ∑_y r(x, y) ≥ s₀ (N (1 - ε₀) - 1)`.
* `Endpoint.Tree`, `Endpoint.Entry`: the instances for the released entry oracle, the entry
  lookup and the call forms, as in `AdaptiveUnitaryLowerBound.Theorem`,
  `AdaptiveUnitaryLowerBound.Lookup` and `AdaptiveUnitaryLowerBound.Entry`.
* `Endpoint.Measured`: the deferral compiled into one program over the controlled spectated
  phase oracle, as in
  `DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_sharp`, then
  `Global.program_count_ge_of_reads`.
* `Endpoint.Calls`: the deferral compiled into controlled calls
  (`DeferredMeasurementLowerBounds.Access.ctrlTreeOf`, `worstCost_ctrlTreeOf`), the labels as
  phase queries (`implementsOn_ctrlTarget`), then `Adaptive.tree_search_count_ge_endpoint`.
* `NonVacuity`: `AdaptiveUnitaryLowerBound.NonVacuity.released`, `released_tree`,
  `released_calls` and `single_hyps`; the measured algorithms are the released circuit followed
  by the trivial output, accurate by `SparseLowerBounds.Hamiltonian.accurate_of_endpoint`;
  `densityAccurate_mono` passes from `1/4` to `1/2`.
* `OperatorNorm.Sharp`: for vectors `a`, `b` of norm at most one with `‖a - b‖ ≤ ε`, `ε² ≤ 2`,
  and a self-adjoint contraction `L`, `|Re⟪a, L a⟫ - Re⟪b, L b⟫| ≤ 2 ε √(1 - ε²/4)`
  (parallelogram law, `norm_add_sq_le`), the observable form of
  `UnitaryImplementationExtensions.Search.norm_sub_proj_le`; the constants, with
  `sharp_lt_half` from `UnitaryImplementationExtensions.Search.near_factor_pos`.
* `OperatorNorm.Accuracy`: the trace of the output is the success probability
  (`DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity`), so the read dilation
  is a unit vector; output and target correlations are expectations in the dilation
  (`corr_outObs_sum_pure`, `inner_garbageTensor_lift`, `inner_tensor_liftObs`), compared by
  `abs_re_inner_sub_le_sharp`.
* `OperatorNorm.Programs`, `OperatorNorm.Deferred`: a unitary program run and output in full
  (`runAll`, read through `SparseLowerBounds.Hamiltonian.endpointReadout`) and the decoded
  deferred unitary (`DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude`) satisfy the
  notion.
* `OperatorNorm.Bound`, `OperatorNorm.CallsBound`: the trace-distance endpoint bounds
  `Deferred.implementation_count_ge_measured_endpoint`,
  `Deferred.entry_count_ge_measured_endpoint` and
  `Calls.implementation_count_ge_measured_calls_endpoint` with `p₀ = 1` and trace distance
  `ε₀ √(1 - ε₀²/4)`; no new adversary argument.
* `OperatorNorm.ProgramBound`: the entry-oracle program form through `normImplements_runAll`;
  the call-form program form from the pairwise bound
  `AdaptiveUnitaryLowerBound.Entry.calls_program_of_error` through `global_of_pairwise`
  (`0 ≤ s ≤ √15/8` gives `(1 - s)² ≤ 16 (1 - 2s)`, and `0 ≤ N (1 - s) - 1 ≤ (N - 1)(1 - s)`).
* `OperatorNorm.NonVacuity`: `AdaptiveUnitaryLowerBound.NonVacuity.released`, `released_calls`
  and `normImplements_runAll`.

Every theorem of the library is axiom-audited in `MeasuredUnitaryLowerBound/Audit.lean`.

**Formalisation choices.**

* Error measure. The manuscript's error is the operator norm `‖A_U - U‖ ≤ ε`
  (`hs:eq:unitaryerror`); the accuracy here is trace distance
  (`DensityAccurate`), the package's notion for adaptive, heralded and measured outputs, for
  which an operator norm has no natural meaning. For a unitary program, operator-norm error `ε`
  gives trace distance at most `ε` (`SparseLowerBounds.Hamiltonian.accurate_of_endpoint` with
  `AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff`), so the trace-distance bounds
  contain the operator-norm endpoint; for unitary programs that endpoint is already covered by
  `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error`. The new content
  is the trace-distance endpoint `ε₀ = 1/2` for adaptive, heralded and measured algorithms,
  the measured and adaptive form of the manuscript's range `0 < ε ≤ 1/2`.
* Setting. Adaptive algorithms, measurements inside a run, inverses and coherent controls come from
  the lower-bound setting of the manuscript (Section `hsl:sec:main`) and from the closing sentence
  of the proof of `hsl:lem:precision`, not from the text of the corollary itself.
* `N = 2`. The bounds are empty at `N = 2`, and must be: a protocol without queries whose
  output is maximally mixed is within trace distance `1/2` of both targets. In operator norm
  `U_0 = 1` and `U_1 = X` are at distance `2`, so this obstruction is specific to trace
  distance. The `√N` forms need `N ≥ 3`.
* Route. Pairwise kernels give nothing at `ε₀ = 1/2` (the output `(|m⟩⟨m| + |m'⟩⟨m'|)/2` is
  within `1/2` of both targets), so the bounds use pair gaps summed over the ordered pairs with
  Cauchy-Schwarz and the package's summed adversary progress, not a hybrid argument with a
  reference run. On the whole range the bound scales as `(s₀ (N (1 - ε₀) - 1))²`, that is as
  `(1 - ε₀)²` for large `N`, against `(1 - 2ε₀)²` in the pairwise bounds.
* Success thresholds. Heralded means `s₀ = 2/3`; the unheralded and implementation forms ask
  success probability one. The heralded measured forms drop the released condition
  `p₀ (1 - ε₀) ≥ 1/2` and need only `p₀ > 0`.
* Constants are explicit: `4` in general, `16` and `36` at `ε₀ = 1/2`, `64` and `144` in the
  `√N` forms. For the measured call forms the compilation costs a factor `2 · 4 = 8`
  (`worstCost_ctrlTreeOf`, four counted call forms), giving `32`, `128` and `512`; the
  single-label conjugation saving is not used.
* Finite dimension. Trees need finite-dimensional workspace and output spaces (lossless
  purification). The plain measured forms are compiled into one program
  (`DeferredMeasurementLowerBounds.Access.compiledProgram`) and need only a finite-dimensional
  output; the measured call forms go through an adaptive protocol and need a finite-dimensional
  oracle space, which the released entry oracle has.
* The read values are `DeferredMeasurementLowerBounds.Corollaries.readProb`, the heralded joint
  read probability. `Global.tree_count_ge_of_kernel_gaps` keeps `Re κ_T ≤ 1` as a hypothesis,
  since its module assumes no finite dimension; `Global.tree_count_ge_of_reads` derives it.
* `MeasuredUnitaryLowerBound.Calls.fintypeCallForm` is a `Fintype` instance for
  `AdaptiveODELowerBound.Access.CallForm`, which the package does not provide. It is scoped to
  the namespace `MeasuredUnitaryLowerBound.Calls` and used only inside proofs there; no public
  statement depends on it.
* The additive lemmas for `liftObs` and `outObs` and the isometric form `Reading.outObs_one`
  (`outObs e 1 = 1` for `e† e = 1`) are stated in `Reading`: the package proves only the
  `e† ∘L e` form, inside `DysonSingleProgram`, which this library does not import.
* `Reading.outObsHom` (the additive map `outObs e`) is a definition and, like the definitions
  of `AdaptiveUnitaryLowerBound`, is not audited; the additivity it carries
  (`Reading.outObs_add`) is.
* `[NeZero N]` is kept alongside `2 ≤ N` for the input `0 : Fin N`, as in the bounds lifted.
* Operator-norm notion for measured algorithms. A measured algorithm implements an instrument,
  not an operator; `OperatorNorm.NormImplements` is the operator-norm error of some purification
  (the Kraus family is existential, so the notion depends only on the output; the garbage may
  depend on the instance but not on the input). It asks success with probability `‖ψ‖²` on the
  encoded inputs, as for the unitary circuit `A_U` of the corollary; without it a contraction
  within `ε` of `U ⊗ γ` bounds the conditional trace distance only by `ε`. Algorithms that
  reject (success probability below one on some unit input) are outside the notion; for them
  the heralded trace-distance bounds (`Deferred.implementation_count_ge_measured_endpoint` with
  `p₀ > 0`) apply.
* The sharp constant `ε √(1 - ε²/4)` is derived, not stated in the manuscript.
  `OperatorNorm.abs_re_inner_sub_le_sharp` needs only `ε² ≤ 2` (the monotone range of
  `d √(4 - d²)`); `OperatorNorm.accurate_of_endpoint_sharp` keeps the hypotheses of
  `SparseLowerBounds.Hamiltonian.accurate_of_endpoint` and adds `ε² ≤ 2`. The constant lemmas are
  stated on `0 ≤ ε ≤ 1/2`, which contains the manuscript's `0 < ε ≤ 1/2` (Corollary
  `hs:cor:unitary`); the bounds take `ε₀ ≤ 1/2`, although the proof works whenever
  `ε₀ √(1 - ε₀²/4) ≤ 1/2`.
* Containment. Every unitary program with the package's error `‖p.eval x ∘L J - J ∘L U‖ ≤ ε`,
  run and output in full, satisfies the notion with one Kraus map and garbage `J |i₀⟩`
  (`OperatorNorm.normImplements_runAll`); the program forms present containment and
  non-vacuity, not new program content. The call-form program bound is a corollary of the
  pairwise bound `AdaptiveUnitaryLowerBound.Entry.calls_program_of_error`; the entry-oracle
  global form goes through the measured route and complements
  `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error`.
* `N = 2` in operator norm: since `ε₀ √(1 - ε₀²/4) ≤ √15/8 < 1/2`, the operator-norm bounds
  force at least one call at `N = 2`, as they must (`U_0 = 1` and `U_1 = X` are at
  operator-norm distance `2`); the `√N` forms take `N ≥ 3`. Constants: `4` (plain and entry
  lookup), `32` (call forms), `64` and `512` in the `√N` forms.
* Untouched reference (Corollary `hs:cor:unitary`): for linear maps between possibly different
  spaces, `‖T ⊗ 1‖ ≤ ‖T‖` with entangled inputs over a finite reference is the package's
  `SparseHamiltonian.FiniteReferenceLift.norm_lift_le` (with `norm_error_le` and
  `normalized_error_le`), cited, not restated. Only the input `|0⟩` of the reduction is used in
  the bounds, although the hypothesis is the full operator-norm statement, as in the manuscript.
* The plain operator-norm forms use the oracle family of `Endpoint/Measured.lean`, the call
  forms `AdaptiveUnitaryLowerBound.Entry.entryOracles`, as in `Endpoint/Calls.lean`; inverse
  calls count as forward calls and each of the four call forms counts once. The output space
  must be finite dimensional, as in the trace-distance measured bounds.

**Not formalised.**

* Operator-norm error for adaptive `Protocol.Tree` algorithms (trees start from a seed and
  have no input slot; they reach the measured model only through
  `DeferredMeasurementLowerBounds.Model.ofTree`). The operator-norm form for measured algorithms
  and the sharp passage to trace distance `ε √(1 - ε²/4)` are proved (`OperatorNorm`).
* A heralded operator-norm variant (success probability below one), and the wider error range
  `ε₀ √(1 - ε₀²/4) ≤ 1/2` beyond `ε₀ ≤ 1/2`.
* Running a measured algorithm next to an untouched reference register (the linear-map fact is
  `SparseHamiltonian.FiniteReferenceLift.norm_lift_le`).
* A formal comparison of `OperatorNorm.implementation_count_ge_program_norm` with
  `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error` (the pairwise
  bound implies it at every `N` when `ε₀ √(1 - ε₀²/4) ≤ √2 - 1`; the call-form comparison is
  `OperatorNorm.global_of_pairwise`).
* Circuit-size, workspace and classical circuit-generation costs.

**Provenance.** No result from another paper is used; the search bound is derived from the package's
positive-weight adversary for trees. The released libraries `AdaptiveHamiltonianLowerBound`,
`AdaptiveODELowerBound`, `AdaptiveUnitaryLowerBound`, `DeferredMeasurementLowerBounds` and
`UnitaryImplementationExtensions` (with their dependencies) are only imported; no released module is
changed. Of the items listed as not formalised in `DeferredMeasurementLowerBounds/Statements.lean`
and `AdaptiveUnitaryLowerBound/Statements.lean`, the trace-distance endpoint `ε₀ = 1/2` and the
named measured forms over the call family are proved here. The operator-norm endpoint is covered for
unitary programs by `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error`,
and for measured algorithms, with the sharp trace distance, by `OperatorNorm`; the statement guide
of `DeferredMeasurementLowerBounds` predates `OperatorNorm`. References to the manuscript use its
labels.
-/
