import ChebyshevFilter.Proposition

/-!
# Positive Chebyshev filtering: paper-to-Lean entry point

Proposition `qls:prop:chebyshev` of the accompanying paper (positive Chebyshev filtering in
the linear-system algorithm, equations `qls:eq:chebdegree` to `qls:eq:chebpositive`), Lemma
`qls:lem:signedwalk` and the degree `qls:eq:filtercost` for the augmented walk. The released
proof of Theorem `qls:thm:main` (library `SparseLinearSystems`) uses the averaging filter of
Remark `qls:rem:averaging` with forward walk steps instead, and is unchanged. No result from
another paper is used. All declarations below are in the namespace `ChebyshevFilter`.
References to the manuscript use its labels.

* Proposition `qls:prop:chebyshev`: `chebyshev_filter`.
* Eq. `qls:eq:chebpositive`: `shifted_taylor`, and positivity `shifted_mem_cone`.
* Eqs. `qls:eq:chebdegree`, `qls:eq:chebfilter`: `lam`, `chebDegree`, `filterFun`,
  `filterCoeff`, `laurent_eq`.
* Eq. `qls:eq:cheberror`: `filterFun_zero`, `norm_filterOp_sub_fixedProj_le`, with
  `filterNorm_eq_cosh` and `inv_filterNorm_chebDegree_le` (the residual amplitude
  `sech(2d artanh b) ≤ δ`).
* The normalisation-one LCU circuit with `d` signed walk steps: `seed_isometry`,
  `signedSteps_full`, `lcu_compression`.
* Lemma `qls:lem:signedwalk` (eq. `qls:eq:signedstep`): `signedProg_eval`,
  `signedProg_cost`; with the proposition: `chebyshev_filter_program`.
* Eq. `qls:eq:augsine` (`artanh b_σ = arsinh χ_σ`) and eq. `qls:eq:filtercost`:
  `artanh_bLow`, `augDegree`, `augDegree_eq`, `augDegree_le`, `augmented_filter`.
* Eq. `qls:eq:filterprobability` for the Chebyshev filter: `norm_filterOp_apply_sq`,
  `filterOp_probability_bounds`; the probability tests at `δ = 1/100` and the final
  projection for the augmented walk: `augmented_test_fact`, `augmented_final_fact`.

**Model.** `W : V →L[ℂ] V` is unitary (`SparseLinearSystems.UnitaryFilter.Unitary`:
`W† W = W W† = 1`) on a finite-dimensional complex Hilbert space `V`, and `P = fixedProj W`
is the orthogonal projection onto the eigenvalue-one space `ker(W - 1)`. Negative powers are
`W^{-k} = (W†)^k` (`wpow`), and `F_{b,d}(W) = ∑_{j=-d}^{d} p_j W^j` (`filterOp`).

The LCU circuit acts on the coefficient register `ℂ^{2d+1} ⊗ V` (`Reg d V`; register value
`j` carries the power `j - d`). The seed is the isometry `v ↦ ∑_j √p_{j-d} |j⟩ ⊗ v` (`seed`,
the released `WeightedClock.boundary`). Signed step `l` (`signedStep`) applies `W` on the
branches with `j - d ≥ l`, `W†` on those with `j - d ≤ -l`, and `1` on the others. The
success block of a circuit `U` on the register is `seed† U seed`.

For Lemma `qls:lem:signedwalk` the walk has the conjugated form of eq.
`qls:eq:commonconjugator`, `W(x) = R V(x)† C V(x)` (`conjWalk`): `V` is a
`MultiOracleCircuit.Program` over any named oracles (for example matrix and
state-preparation oracles), and `R`, `C` are input-independent unitaries. A forward step is
the program `R · V† · C · V` (`forwardProg`). On a register `ℂ^ι ⊗ K` with a direction for
each register value (`dir : ι → Option Bool`: `W`, `W†` or inactive), the signed step
(`signedProg`) is a program over the same named oracles acting on the payload, with the
register as a spectator (`spectator`, `lift`); its fixed gates are block diagonal in the
register. Costs are `Program.cost w`, for any weights `w` of the oracle labels.

**Hypotheses.** `0 < b < 1`; every eigenvalue `e^{iθ} ≠ 1` of `W` has `|sin(θ/2)| ≥ b`
(`chebyshev_filter`; it implies `|z - 1| ≥ 2b` for every eigenvalue `z ≠ 1`, the form used
by the released files and by the other theorems here, `gap_of_phase`); `0 < δ < 1`. For the
program form, the oracles are unitary and the gap holds on every input.

**Guarantees** (`d = chebDegree b δ = ⌈arcosh(1/δ) / (2 artanh b)⌉`, `λ = b²/(1 - b²)`).

* `chebyshev_filter`: the Laurent coefficients `p_j = filterCoeff b d j` are nonnegative,
  vanish outside `[-d, d]` and sum to one;
  `∑_j p_j e^{ijθ} = T_d((1 + λ) cos θ + λ) / T_d(1 + 2λ)` for every real `θ`;
  `F_{b,d}(1) = 1`; `‖F_{b,d}(W) - P‖ ≤ δ`; `F_{b,d}(W) v = F_{b,d}(e^{iθ}) v` for every
  eigenvector `W v = e^{iθ} v`; the seed is an isometry (normalisation one); and the `d`
  signed steps have success block exactly `F_{b,d}(W)`.
* `norm_filterOp_sub_le`: `‖F_{b,d}(W) - P‖ ≤ 1 / T_d(1 + 2λ) = sech(2 d artanh b)` for
  every `d`.
* `chebyshev_filter_program`: for `W(x) = R V(x)† C V(x)`, the program `lcuProg` of `d`
  signed steps has success block `F_{b,d}(W(x))` on every input, within `δ` of `P(x)`, and
  its cost is `d` times the cost of one forward step, for every weighting of the labels.
* `signedProg_eval`, `signedProg_cost`: the signed step acts as `W`, `W†` and `1` on the
  forward, inverse and inactive branches, and makes exactly the calls of one forward step,
  label by label.
* `augmented_filter`: for the walk `W_{σ,r}` of the released linear-system circuit
  (`LogicalWalk.WwO`), under the hypotheses of the released gap theorem `Facts.gapO`
  (any public `0 < g ≤ g_σ`): `‖F(W_{σ,r}) - P_{σ,r}‖ ≤ δ` for the filter at
  `b = χ/√(1 + χ²)`, `χ = 4g/(165√s)` (`Augmented.bLow`, `Augmented.chi`; `b_σ` at
  `g = g_σ`), of degree `d_σ(δ) = ⌈arcosh(1/δ) / (2 arsinh(4g/(165√s)))⌉` (`augDegree`,
  equal to `chebDegree b δ`); the LCU circuit with `d_σ(δ)` signed steps has this success
  block; and `d_σ(δ) ≤ 23 √s log(2/δ) / g`.
* `augmented_test_fact`, `augmented_final_fact`: the released `Facts.test_fact` and
  `Facts.final_fact` with the Chebyshev filter (degree `d_σ(1/100)`, respectively
  `d_0(δ)` at `g = 1/κ`) in place of the averaging filter: test probabilities in
  `[1/(2(1 + q²)), 1/(1 + q²) + 10⁻⁴]`, and a decoded final amplitude within `δ` of
  `c A⁻¹ b` with `1/(r (1 + μ)(1 + q²)) ≤ c ≤ 1/(r (1 + q²))`.

**Proof map.** Module paths are relative to `ChebyshevFilter/`.

* `Cone`: nonnegative Chebyshev combinations as an `ℝ≥0`-submodule (`cone`), closed under
  products (`T_m T_n = (T_{m+n} + T_{|m-n|})/2`) and containing `(x + 1)^k` and `T_d^{(k)}`
  (Mathlib's `T_iterate_derivative_mem_span_T`); coefficients in Mathlib's Chebyshev basis
  (`chebCoeff`).
* `Positivity`: Taylor expansion at a polynomial increment (`comp_X_add`), eq.
  `qls:eq:chebpositive` (`shifted_taylor`) and positivity (`shifted_mem_cone`).
* `Degree`: `1 + 2λ = cosh(2 artanh b)`, `T_d(1 + 2λ) = cosh(2 d artanh b)`, the degree,
  and the affine argument in `[-1, 1]`.
* `Laurent`: the Laurent coefficients, their sum, and the Laurent form from
  `T_m(cos θ) = cos(mθ)`.
* `Operator`: `W^m + W†^m = 2 T_m(1 - t/2)` on eigenvectors of the defect `(W - 1)†(W - 1)`
  (`sum_pow_apply_eigen`), the diagonal form of `F(W) - P` in the defect eigenbasis, the error
  bounds, spectral orthogonality, eigenvectors of `W` and the eigenphase hypothesis.
* `Circuit`: the coefficient register, the signed steps, the seed and the compression.
* `SignedWalk`: Lemma `qls:lem:signedwalk` and the LCU program.
* `Augmented`: `artanh b ≥ b` (from the series of `log((1 + b)/(1 - b))`),
  `arcosh y ≤ log(2y)`, the augmented degree and its bound, and the walk `WwO`.
* `Facts`: the probability tests and the final projection.
* `Proposition`: the assembled statements.

Every theorem of the library is axiom-audited in `ChebyshevFilter/Audit.lean`.

**Formalisation choices.**

* The filter is given by its Laurent coefficients. The Chebyshev coefficients `c_m` of
  `T_d(x + λ(x + 1))` are read off in Mathlib's Chebyshev basis, and
  `p_0 = c_0 / T_d(1 + 2λ)`, `p_{±m} = c_m / (2 T_d(1 + 2λ))`. `laurent_eq` proves that these
  are the coefficients of the manuscript's `F_{b,d}(e^{iθ})`, and `filterOp_apply_eigen` that
  `F_{b,d}(W)` acts on every eigenvector of `W` by the value of `F_{b,d}` at its eigenvalue.
* The spectral theorem is used for the self-adjoint defect `(W - 1)†(W - 1) = 2 - W - W†`
  rather than for `W`: on its eigenvectors `W^m + W†^m = 2 T_m(1 - t/2)`, the operator form of
  `2 cos(mθ) = 2 T_m(cos θ)` with `t = |e^{iθ} - 1|² = 2 - 2 cos θ`.
* The LCU circuit uses exactly `d` signed steps (the proposition says at most `d`). The seed
  is an isometry from the payload rather than a state preparation followed by a projection,
  as in the released counter filter (`SparseLinearSystems/Circuit/CounterFilter.lean`).
* In Lemma `qls:lem:signedwalk` the reflection `R` may be any unitary; `R_-` applies `R†`,
  which is `R` for the reflection `I - 2JJ†` of the manuscript. The direction register is any
  finite register with one direction per register value. `V` and `V†` act on the payload
  with the register as a spectator, as queries in larger registers are placed in the released
  circuit layer.
* `augDegree_le` makes `d_σ(δ) = O((√s/g) log(2/δ))` explicit with the constant `23`, for
  `s ≥ 1` and `0 < g ≤ 1`.

**Not formalised.**

* Theorem `qls:thm:main` with the Chebyshev filter: the released end-to-end proof (protocol,
  costs and correctness) keeps the averaging filter and forward steps. The filter-level facts
  of the analysis are proved here for the Chebyshev filter (`augmented_test_fact`,
  `augmented_final_fact`), and Lemma `qls:lem:signedwalk` is proved for any walk of the form
  `R V† C V`. The released circuit layer factors the augmented walk as
  `R · A_sp · F_a · V · F_b · V†` around a native Cayley program (`LogicalWalk.Ww_factor`,
  `LogicalWalk.WwO_factor`, compiled in `SparseLinearSystems/Circuit/Step.lean`), and is
  not brought into that form here.
* The finite-gate allowance of eq. `qls:eq:finitedegree`, the explicit constants of Remark
  `qls:rem:constants`, and the centred implementation of positive polynomials in Remark
  `qls:rem:averaging`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/
