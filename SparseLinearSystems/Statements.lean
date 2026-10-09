import SparseLinearSystems.Endpoint.Main

/-!
# Sparse linear systems: paper-to-Lean entry point

Theorem 8.1 (`qls:thm:main`) of the accompanying paper is formalized by
`SparseLinearSystems.Endpoint.main`, with the existential form
`SparseLinearSystems.Endpoint.main_exists`; both are in
`SparseLinearSystems/Endpoint/Main.lean`.

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

Outside this formalization: the matching lower bound (`qlsl:thm:main`), gate
and workspace counts, and classical circuit-generation costs.
-/
