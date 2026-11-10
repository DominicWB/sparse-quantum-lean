import SparseLinearSystems.Endpoint.Main
import SparseLinearSystems.Separate.Main

/-!
# Sparse linear systems: paper-to-Lean entry point

Theorem 8.1 (`qls:thm:main`) of the accompanying paper is formalized by
`SparseLinearSystems.Endpoint.main`, with the existential form
`SparseLinearSystems.Endpoint.main_exists`; both are in
`SparseLinearSystems/Endpoint/Main.lean`.
References to the manuscript use its labels.

**Access model.** The sparse data are those of the Hamiltonian and ODE
libraries: `SparseHamiltonian.NativeSparseBlockEncoding.Data X n Z s` supplies,
for every unknown input `x : X`, an `N × N` matrix `A_x` with at most `s ≥ 1`
nonzero entries per row and column, exact finite-word entries, and padded
injective in-place row and column locators with full unitary extensions.
`Facts.Aop D x` is `A_x` as an operator on `EuclideanSpace ℂ n`, so its
norm is the spectral norm. `Ub x` is the supplied state-preparation circuit
and `sv` the public reference state, `b = U_b sv`. The physical oracle family
`Step.physOracle` consists of the three native primitives, applied with all
other registers as spectators, and the source preparation `U_b` controlled by
a workspace bit. `Step.wMat` counts every native matrix-oracle call and
`Step.wSrc` every call of the controlled `U_b`; inverse calls are counted.
Public instance-independent gates are free.

**Promise** (equation `qls:eq:promise`). `Endpoint.Promise D κ x` states
`‖A_x‖ ≤ 1`, that `A_x` is invertible and `‖A_x⁻¹‖ ≤ κ`. In addition `κ ≥ 1`,
every `U_b` is unitary and `‖sv‖ = 1`.

**Algorithm.** `Endpoint.algorithm D Ub sv κ ε` is one bounded adaptive
protocol (`Protocol.Tree`), uniform over all unknown inputs. Its circuits,
seeds, flags and classical decisions are public: they are determined by `s`,
`κ`, `ε` and the instance-independent part of the access model. It runs the
geometric norm estimator for `m = ⌈log₂ ⌈κ⌉⌉` stages and then at most `1000`
fresh final attempts, stopping at the first heralded success.

**Guarantees** (`Endpoint.main`, for `0 < ε ≤ 1/10`):

* every transcript, including every failure branch, makes at most
  `4·10¹² √s κ log(1/ε)` matrix-oracle calls and at most
  `2·10¹¹ √s κ log(1/ε)` calls of the controlled `U_b` and its inverse;
* for every input satisfying the promise, every run is unitary, the heralded
  success probability is at least `2/3`, and the output conditioned on success
  is a positive trace-one operator `ρ` with
  `½ ‖ρ - |x⟩⟨x|‖₁ ≤ ε`, `|x⟩ = A⁻¹ b / ‖A⁻¹ b‖` (`Endpoint.solutionState`).

The trace distance is `ODEMixedOutput.hermitianTraceDistance`, half the sum of
the absolute eigenvalues of the Hermitian difference. All constants are
explicit absolute numbers. There is no logarithm of `s` or `κ` and no extra
power of `log(1/ε)`.

**Proof map.** Module paths are relative to `SparseLinearSystems/`; declarations
are named within their namespaces.

* Lemma `qls:lem:walk` (kernel walk and phase gap): `WalkGap`
  (`Hyp.fixed_lift`, `Hyp.tangent_gap`, `Hyp.chord_gap`).
* Lemma `qls:lem:entry` and the augmented walk, equations
  `qls:eq:composition` to `qls:eq:augsine`: `Sparse.SplitBoundary`,
  `Sparse.SparseBranch`, `Augmented.Walk` (`augmented_hyp`,
  `augmented_chord_gap`).
* Equations `qls:eq:probability`, `qls:eq:finalprob`:
  `Augmented.Probability`, `Augmented.Solution`, `Augmented.Analysis`.
* Remark `qls:rem:averaging` and equation `qls:eq:filterprobability`:
  `Spectral.UnitaryFilter`.
* Coherent walk steps (`qls:eq:commonconjugator`): `Circuit.LogicalWalk`
  (`Ww_factor`), `Circuit.Step` (`stepProg_intertwines`: `54` matrix-oracle
  calls and `2` source calls per walk step), `Circuit.Run`.
* Equations `qls:eq:bernoulli`, `qls:eq:hoeffding`: `Circuit.Facts`
  (`test_fact`) and `Statistics.BinomialTail`.
* Equations `qls:eq:normladder`, `qls:eq:candidates`,
  `qls:eq:estimatebound`: `Augmented.NormLadder`, `Protocol.Estimator`
  (`algorithm_bad_le`), `Endpoint.Correctness` (`rho_ladder`, `test_bounds`).
* Equations `qls:eq:qrange`, `qls:eq:finalprob` and the final error:
  `Circuit.Facts` (`final_fact`), `Endpoint.Correctness` (`finalLeaf_good`).
* Success, mixture and conditional trace distance: `Protocol.Tree`
  (`successMass_ge`, `output_guarantee`), `Endpoint.Correctness`
  (`correctness`).
* Equations `qls:eq:geometriccost` and `qls:eq:main`: `Endpoint.Cost`
  (`walkSteps_le`, `algorithm_matrix_queries`, `algorithm_source_queries`).

**Formalization choices.** These change constants only, not the stated bounds.

* The filter is the averaging filter `f_N(W)^k` of Remark
  `qls:rem:averaging`, with `N = ⌈100 / b⌉`, rather than the positive
  Chebyshev filter of Proposition `qls:prop:chebyshev`. It is implemented by
  forward walk steps controlled by one counter register, so signed steps
  (Lemma `qls:lem:signedwalk`) are not needed.
* Gates are exact. The finite-gate allowance of equation
  `qls:eq:finitedegree` is not modelled; the test tolerance `10⁻⁴` of equation
  `qls:eq:bernoulli` comes from the filter error alone.
* Repeated tests use the elementary bound
  `P(|S/n - p| ≥ t) ≤ 2 exp(-n t²/4)` instead of Hoeffding's inequality, so
  `n_j = ⌈4 log(2/ζ_j) / t²⌉` with `t = 0.0099`.
* Each of the five tests at stage `j` has failure budget
  `ζ_j = (ε/5000) 2^{j-m}`, matching the manuscript's combined budget.
  If no candidate is accepted, the clipped value `2r` of the last candidate is
  used as the fallback estimate.
* The final preparation uses `σ = 0`, `N = ⌈100 / b(1/κ)⌉`,
  `k = ⌈log₁₀₀ ⌈1000/ε⌉⌉` and `1000` attempts. At a good estimate one attempt
  succeeds with probability at least `0.0349`, and the leaf with at least
  `97/100`.

**Corollary `qls:cor:separate`** (conditional). `Separate.main` gives, for
the same access model, a public `κ ≥ 1`, `0 < ε ≤ 1/10` and a public scalar
`ν̂` with `ν/2 ≤ ν̂ ≤ 2ν` (`ν = ‖A⁻¹ b‖`), one protocol over
`Separate.sepOracle` with worst-case matrix cost at most `C_A √s κ log(1/ε)`
on every input and, on every valid input, worst-case `U_b` cost at most
`C_b κ/ν`, success at least `2/3` and conditional trace distance at most `ε`.
It is conditional on the hypothesis `Separate.SeparateSolver cM cb q₀`, a
uniform single-trial block-input solver interface representing the solver of
Gao, Ji and Liu; it is stronger than the statement of their theorem, is
intended to follow from its proof, and is not formalised here. Proof map:
`Separate.Algebra` (walk identity `(I - W) R₀ J u = (i/α) J H u`, trivial
fixed space, `‖B v‖ ≥ t*/√(1 + t*²) ‖v‖`), `Separate.Bounds` (`κ_B = 4√s κ`,
the enlarged solution and its norm, the transferred estimate
`ν̂_B = (9/8) √s ν̂` in `[3/8, 5/2] ‖y‖`, the decoder `T`),
`Separate.Registers` and `Separate.Native` (the exact block encoding
`lcu (R̃ D̃₀)` of `B`, the preparation of `J (b, 0)`, separate costs `54/0`
and `0/1`), `Separate.Decode` (herald routing, selected vector `T (out† ψ)`,
success and error transfer), `Separate.Main` (repetition and costs).

Outside this formalization: the matching lower bound (`qlsl:thm:main`), gate
and workspace counts, classical circuit-generation costs, and the external
solver theorem used by Corollary `qls:cor:separate`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/
