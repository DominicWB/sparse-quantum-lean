import QLSHoeffding.Main
import QLSHoeffding.Constants

set_option autoImplicit false

/-!
# Theorem `qls:thm:main` with Hoeffding's inequality and the repetition count of equation
`qls:eq:hoeffding`: paper-to-Lean entry point

The probability tests of the linear-system algorithm (Section `qls`) use Hoeffding's inequality:
"independent repetitions and Hoeffding's inequality give an empirical frequency `p̂` with
`|p̂ - p_F| ≤ 0.0099`, except with probability `ζ`, after `n_rep = ⌈log(2/ζ)/(2(0.0099)²)⌉`
repetitions" (equation `qls:eq:hoeffding`), and "give the five tests at stage `j` a combined failure
budget `ζ_j = (ε/1000) 2^{j-m}`"; Remark `qls:rem:constants` quotes "the remaining repetition count
of about `5102 log(10/ζ_j)` per stage test".

The released proofs of Theorem `qls:thm:main` (`SparseLinearSystems.Endpoint.main`,
`ChebyshevLinearSystem.main`, `ChebyshevLinearSystemFinite.main`) use the elementary binomial
tail bound `2 exp(-n t²/4)` for `t ≤ 2` (`SparseLinearSystems.BinomialTail.two_sided`,
`two_sided_le_of_count`) with the count `⌈4 log(2/ζ)/t²⌉` (`SparseLinearSystems.Endpoint.reps`),
eight times the count of
`qls:eq:hoeffding`, at the per-test budget `Endpoint.zeta κ ε j = (ε/5000) 2^{j-m}`. This library
proves Hoeffding's inequality for the binomial law and the third (finite-degree) proof of the
theorem with the manuscript's count; the released proofs are unchanged.

No result from another paper is used. The released libraries are unchanged. References to the
manuscript use its labels. Every theorem of the library is axiom-audited in
`QLSHoeffding/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace `QLSHoeffding` and
are named relative to it below. `Endpoint`, `Protocol` and `BinomialTail` refer to the
namespaces `SparseLinearSystems.*` of the released library and `Estimator` to
`SparseLinearSystems.Protocol.Estimator`, and unqualified released names of the finite-degree
proof to `ChebyshevLinearSystemFinite`.

**Hoeffding's inequality for the binomial law** (module `Hoeffding`). For `0 ≤ p ≤ 1`, with
`binom n p c` the binomial probabilities:

* `log_mgf_le` (Hoeffding's lemma for a Bernoulli variable):
  `log(1 - p + p e^θ) ≤ pθ + θ²/8` for every real `θ`, by calculus: the gap
  `θ²/8 - log(1 - p + p e^θ) + pθ` vanishes with its derivative at `0` and has a monotone
  derivative (`gap_nonneg`, `slope_monotone`, `tilt_mul_le`);
* `mgf_le_sharp`: `Σ_c binom n p c e^{θc} ≤ exp(n(pθ + θ²/8))`;
* `upper_tail_sharp`, `lower_tail_sharp`, `two_sided_sharp`: the mass of `|c - np| ≥ nt` is at most
  `exp(-2nt²)` on each side and `2 exp(-2nt²)` in total, for every `t ≥ 0`;
* `two_sided_le_of_count_sharp`: `n ≥ log(2/ζ)/(2t²)` gives inaccurate mass at most `ζ`.

**The estimator for every repetition schedule meeting its tail budget** (module `Estimator`).
`TailOK n t ζ`: for every `p ∈ [0, 1]` the counts with `|c - np| ≥ nt` have binomial mass at most
`ζ`. `tailOK_hoeffding` (Hoeffding's count) and `tailOK_released` (the released count) meet it.
`count_step_tail`, `candidates_le_tail`, `stages_le_tail` and `algorithm_bad_le_tail` are the
released stage, stages and union-bound analysis of the norm estimator
(`Estimator.algorithm_bad_le`, `ChebyshevLinearSystemFinite.algorithm_bad_le_tol`, with the
two-sided tolerance `1/(2(1+q²)) - 10⁻⁴ ≤ p ≤ 1/(1+q²) + 10⁻⁴` of equation `qls:eq:bernoulli`)
with `TailOK` in place of the count.

**The schedule** (modules `Schedule`, `Constants`).

* `zetaMs κ ε j = (ε/1000) 2^{j-m}`, the manuscript's stage budget; `zeta_eq_zetaMs`: the released
  per-test budget is `Endpoint.zeta κ ε j = zetaMs κ ε j / 5`, so the allocation agrees with the
  manuscript's (five tests per stage);
* `repsH κ ε j = ⌈log(2/ζ)/(2t²)⌉` at `ζ = Endpoint.zeta κ ε j` and `t = Estimator.tAcc = 0.0099`;
  `repsH_eq_ms`: `repsH κ ε j = ⌈log(10/ζ_j)/(2 · 0.0099²)⌉`, exactly `qls:eq:hoeffding` at the
  per-test budget `ζ_j/5` (`1/(2 · 0.0099²) ≈ 5101.5`, the "about `5102 log(10/ζ_j)`" of
  Remark `qls:rem:constants`);
* `repsH_tailOK`: the counts meet the tail budgets; `repsH_le`:
  `n_j ≤ 25509 log(1/ε) + 3537 (m - j)` for `0 < ε ≤ 1/10`.
* `repsH_bracket` (module `Constants`): `5101 log(10/ζ_j) ≤ n_j ≤ 5102 log(10/ζ_j)` for
  `0 < ε ≤ 1` and every stage `j`, the count quoted in Remark `qls:rem:constants`
  (`zetaMs_le`: `ζ_j ≤ ε/1000`; `four_log_two_le_log_ten_div_zetaMs`: `log(10/ζ_j) ≥ 4 log 2`, so
  the ceiling adds less than `0.48 log(10/ζ_j)`).

**The protocol and the theorem** (modules `Algorithm`, `Cost`, `Main`). `implAlgorithmH κ ε test fin`
is the finite-degree Chebyshev protocol `ChebyshevLinearSystemFinite.implAlgorithm` (the degrees
of equation `qls:eq:finitedegree`, the released classical control: `m = ⌈log₂ ⌈κ⌉⌉` stages, five
candidates per stage, the thresholds and the clipping, at most `1000` final attempts) with the
counts `repsH`; `algorithmFH` is its exact-gate instance.

* `impl_correctnessH`: for every implementation whose tests and final attempts change the success
  vector at the input by at most the manuscript's allowances `e_test`, `e_fin`: unitary runs,
  success probability at least `2/3`, conditional output within trace distance `ε` of the
  normalised solution.
* `walkStepsH_le`, `impl_worstCostH`, `impl_matrix_queriesH`, `impl_source_queriesH`: at most
  `6.2·10⁷ √s κ log(1/ε)` signed walk steps, hence at most `3.4·10⁹ √s κ log(1/ε)` matrix-oracle
  calls and `1.25·10⁸ √s κ log(1/ε)` source calls in every transcript (the released counts give
  `2.7·10¹⁰` and `10⁹`).
* `main_ampH`, `mainH` (Theorem `qls:thm:main` with the repetition count of
  `qls:eq:hoeffding`, with approximate known gates in the sense of
  `ChebyshevLinearSystemFinite.AmpApprox`, respectively `RunApprox`), `main_exactH`,
  `main_exactH_exists` (exact gates): for `κ ≥ 1` and `0 < ε ≤ 1/10`, the access model, promise
  and oracle family of `ChebyshevLinearSystemFinite.main`, worst-case counts as above, and for
  every input satisfying the promise, unitary runs, success probability at least `2/3` and
  conditional trace distance at most `ε`.

**Scope.** The first two released proofs (the averaging filter of Remark `qls:rem:averaging` and
the exact-degree Chebyshev filter) keep the released count. Their classical control is the same
`Estimator.algorithm`, whose analysis `algorithm_bad_le_tail` covers every test run within the
tolerance of `qls:eq:bernoulli`, but their endpoints are not restated with the count of
`qls:eq:hoeffding`.
-/
