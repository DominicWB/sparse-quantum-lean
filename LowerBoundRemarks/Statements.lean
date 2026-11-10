import LowerBoundRemarks.ParityAmplitude
import LowerBoundRemarks.LinearSystemPadding
import LowerBoundRemarks.HamiltonianPadding

/-!
# Remarks after the lower-bound theorems: paper-to-Lean entry point

Three remarks of the accompanying paper on its query lower bounds are formalised here: the
structural remark on parity-amplitude reductions after Corollary `hsl:cor:power` in Section
`part:hsl`; the remark after Theorem `qlsl:thm:main` on padding the hard linear systems to any
larger dimension; and the padding of the three hard Hamiltonian-simulation families to a common
dimension, the last clause of Theorem `hsl:thm:main` ("with further known padding allowed") with the
end of its proof ("Further known zero padding equalises dimensions or accommodates a qubit
register") and the remark after it ("We need not find one matrix on which all three mechanisms are
simultaneously difficult"). The statement
files of `SparseLowerBounds` and `AdaptiveHamiltonianLowerBound` (parity remark, Hamiltonian
padding) and of `LinearSystemLowerBound` (linear-system padding) list these remarks as not
formalised there; those libraries are unchanged. No result from another paper is used. References to
the manuscript use its labels. Declarations are named relative to the namespace
given with each item and paragraph below (one namespace per module of `LowerBoundRemarks/`);
declarations of the released lower-bound libraries are named relative to `LinearSystemLowerBound`
and `SparseLowerBounds.Hamiltonian`, as in their statement files.

* Parity-amplitude reductions (Section `part:hsl`; namespace `LowerBoundRemarks.ParityAmplitude`,
  module `ParityAmplitude.lean`): `moment_eq_zero` (`E_X[σ(X) H_X^k] = 0` for `k < n`) and
  `exp_correlation_le` (`‖E_X[σ(X) e^{-iτ H_X}]‖ ≤ e^τ τ^n/n!`), with the series form
  `exp_correlation_le_tsum`, the matrix form `matrix_exp_correlation_le` and the `hsl` parity
  forms `hsl_moment_eq_zero` and `hsl_exp_correlation_le`.
* Padding the hard linear systems (remark after Theorem `qlsl:thm:main`; namespace
  `LowerBoundRemarks.LinearSystemPadding`, module `LinearSystemPadding.lean`): `padFamily_promise`
  and the other properties of `padFamily`; the lower bounds `pad_lower_bound` (constant
  `1/3072`), `pad_lower_bound_sharp` (`1/1536`) and `pad_lower_bound_sharp_clean`; in a
  prescribed dimension, `common_dimension` and `lower_bound_common_dimension`.
* Padding the hard Hamiltonian-simulation families (the last clause of Theorem `hsl:thm:main` and
  the end of its proof; namespace `LowerBoundRemarks.HamiltonianPadding`, module
  `HamiltonianPadding.lean`): `main_max_pad`, `main_exists_pad`, `hard_instances_pad` and
  `third_sum_le_max`; in one common dimension, `main_max_common_dimension` and
  `main_exists_common_dimension`.

**Parity-amplitude reductions** (namespace `LowerBoundRemarks.ParityAmplitude`).

* Setting. Blocks form a finite type `B`, `n = Fintype.card B`; block `b` takes values in a finite
  type `Ω b`; inputs `X : ∀ b, Ω b` are uniformly distributed,
  `E_X[f X] = (Fintype.card (∀ b, Ω b) : ℂ)⁻¹ • ∑ X, f X`. Per-block signs `σ b : Ω b → ℝ` are
  balanced, `∑ ω, σ b ω = 0`, and `parity σ X = ∏ b, σ b (X b)`. `H` maps inputs into a `ℂ`-algebra
  `A`. "every entry [of `H_X`] is linear in the membership bits of independent blocks" is
  `IsBlockAffine H`, `H X = H₀ + ∑ b, F b (X b)`; it is equivalent to
  `H X = H₀ + ∑_b ∑_z [X b = z] G b z` (`isBlockAffine_iff_membership`) and, for matrices, to every
  entry being `c₀ + ∑_{b,z} c_{b,z} [X b = z]` (`isBlockAffine_iff_entries`).
* `moment_eq_zero`: for balanced signs and block-affine `H`,
  `∑ X, (parity σ X : ℂ) • H X ^ k = 0` for every `k < n`; `expect_moment_eq_zero` is the
  expectation form and `moment_eq_zero_membership` the literal membership-bit form.
* `exp_correlation_le_tsum` and `exp_correlation_le`: if moreover `|σ b ω| ≤ 1`, `A` is a
  complete normed `ℂ`-algebra with `‖1‖ = 1`, `‖H X‖ ≤ 1` for every `X` and `0 ≤ τ`, then
  `‖E_X[σ(X) exp((-i τ) • H X)]‖ ≤ ∑' k, (if n ≤ k then τ^k/k! else 0) ≤ e^τ τ^n/n!`
  (`tsum_tail_le`); `exp_correlation_le_membership` is the literal membership-bit form.
* `matrix_exp_correlation_le`: the same bound, under the same hypotheses on `σ` and `τ`, for
  square complex matrices with spectral (`ℓ²`-operator) norm at most one whose entries are affine
  in the membership bits, with the matrix exponential: the bound of the remark (its moment
  identity is `moment_eq_zero`).
* `hsl_moment_eq_zero`, `hsl_exp_correlation_le`: the parity `σ(X) = (-1)^{j_1 + ⋯ + j_n}` of
  `n` hidden positions `j_b ∈ Fin m`, `m` even (balanced by `sum_hslSign`), averaged over the
  `m^n` inputs; the precision family has `m = 2`, the search families a power of two.
* Proof. The functions of the input that depend on at most `j` blocks (Mathlib's `DependsOn`)
  span `blockSpan j`; block-affine maps lie in `blockSpan 1` (`IsBlockAffine.mem_blockSpan`),
  products add block degrees (`mul_mem_blockSpan`, `pow_mem_blockSpan`), and a function of fewer
  than `n` blocks has zero correlation with the parity, by the involution `swapAt`
  (`sum_smul_eq_zero_of_update_eq`, `sum_parity_smul_eq_zero_of_dependsOn`,
  `sum_parity_smul_eq_zero_of_mem`). In the exponential series the terms `k < n` vanish and the
  others are bounded by `τ^k/k!` (`norm_average_le`, `tsum_tail_le`).

**Padding the hard linear systems** (namespace `LowerBoundRemarks.LinearSystemPadding`). The hard
family of `LinearSystemLowerBound` is `A_X = family κ ε s X` on `Ind κ ε s` (dimension `4nm`,
`n = npar κ ε`, `m = mpar s`), with right-hand side `b = rhsVec κ ε s` and normalised solutions
`x_A = target κ ε s X`. Let `P` be any finite type (the padding register).

* The padded family. `emb I P` is the isometric extension by zero `ι v = v ⊕ 0`;
  `padFamily κ ε s P X = A_X ⊕ I_P` (`Matrix.fromBlocks A_X 0 0 1`) on `Ind κ ε s ⊕ P`;
  `padRhs κ ε s P = ι b`; `padTarget κ ε s P X = A'⁻¹ b' / ‖A'⁻¹ b'‖` for `A' = A_X ⊕ I_P` and
  `b' = ι b`.
* Properties, for `κ ≥ 32` and `s ≥ 5` where needed: `padFamily_promise` (`‖A'‖ ≤ 1`, `A'`
  invertible, `‖A'⁻¹‖ ≤ κ`; generic form `block_promise` for any bound `c ≥ 1`),
  `padFamily_real_symm`, `padFamily_indefinite`, `padFamily_sparse` (row and column `a` are
  supported in the input-independent set `padSupport κ ε s P a` of at most `s` indices),
  `padFamily_dimension` (`|Ind ⊕ P| = 4nm + |P| > s κ ln(1/ε)/32`), `padRhs_apply`,
  `padRhs_norm`, `padSolution_eq` (`A'⁻¹ b' = ι (A_X⁻¹ b)`), `padTarget_eq` (`x_{A'} = ι x_A`)
  and `padTarget_norm`.
* `pad_lower_bound_sharp`: the hypotheses of `LinearSystemLowerBound.lower_bound_sharp` with
  `Ind κ ε s ⊕ P` in place of `Ind κ ε s` and `padTarget` in place of `target`: `κ ≥ 32`,
  `s ≥ 5`, `0 < ε ≤ 1/64`; native data `D` on `Ind κ ε s ⊕ P` with `D.matrix = padFamily κ ε s P`,
  input-independent row and column location oracles and `D.table x α = enc α (D.matrix x α.1 α.2)`
  for a fixed `enc`; oracle labels `l` with weights `w l` that are all admissible for `D`
  (`Native.Admissible`: a native call of weight at least one, or an input-independent unitary);
  an adaptive protocol `T : SparseLinearSystems.Protocol.Tree O F E` whose finite-dimensional
  output space `E` is identified with `ℂ^{Ind ⊕ P}` ⊗ garbage `ℂ^G` by a fixed isometry `V`; and,
  for every input, success probability at least `2/3` and reduced conditional output within
  spectral trace distance `ε` of `|x_{A'}⟩⟨x_{A'}|`. Conclusion:
  `κ √s ln(1/ε) / 1536 < T.worstCost w`, the weighted count maximised over all transcripts.
  `pad_lower_bound` gives `κ √s ln(1/ε) / 3072`, the paper's constant;
  `pad_lower_bound_sharp_clean` is the case of a clean output, `E = ℂ^{Ind ⊕ P}`.
* Proof. `bound_of_access` is the counting step `LinearSystemLowerBound.lower_bound_of_bias` for
  native data on any index type satisfying `Native.HardAccess` (input-independent locators, table
  entries that are fixed functions of at most one input bit); `padAccess` gives `HardAccess` for
  the padded data (`padFamily_bitDetermined`); the padded decoder `padDecoder = ι ∘ M ∘ ι†` is a
  contraction (`padDecoder_norm_le`) with the signed correlation of the unpadded decoder
  (`inner_padDecoder`, `padTarget_correlation`).
* Non-vacuity. `exists_pad_access` and `exists_pad_hardAccess` construct such data, with fixed
  permutation locators covering the row and column supports (`coverData`) and a word code in
  `ZMod 8` with one more value for the identity entry (`padEnc`, `padDec`,
  `padFamily_entry_cases`).
* A prescribed dimension. For `|Ind κ ε s| ≤ Nd`, padding by
  `PadReg κ ε s Nd = Fin (Nd - |Ind κ ε s|)` gives dimension exactly `Nd` (`padReg_card`), and
  every `Nd ≥ s κ ln(1/ε)` qualifies (`card_ind_le`). `common_dimension`: exact dimension,
  promise, supports of at most `s` indices and data with input-independent locators and an
  entry-determined table; `lower_bound_common_dimension`: exact dimension and the bound of
  `pad_lower_bound_sharp`.

**Padding the hard Hamiltonian-simulation families** (namespace
`LowerBoundRemarks.HamiltonianPadding`; the model, the parameters and the families are those of
`SparseLowerBounds/Hamiltonian/Statements.lean`: `HSRange τ s ε` is `τ ≥ 1`, `s ≥ 32` and
`0 < ε ≤ 1/64`, `L = hsL ε`, `r = hsR τ ε`, `n = precN τ ε`, `c₀ = c0 = log 2/(4096π)`). Let `P`
be any finite type.

* Known zero padding. `padMat P H = H ⊕ 0_P` (`Matrix.fromBlocks H 0 0 0`); the word table
  `padTable T P` keeps the original block and reads no bit, with word `0`, elsewhere; the
  location lists `padLoc` keep the original lists and give padding rows the slot list (fixed and
  injective); `padBitData` is the one-bit builder `bitData` applied to these. The padded hard
  families are `timePadData τ s hs P`, `mixedPadData τ ε s hs P` and
  `precisionPadData τ ε s hs P`: `timeData`, `mixedMainData` and `precisionMainData` padded by
  `P` (through `padSearchData` and `padScalarData`), with the known input `ψ_in ⊕ 0`
  (`HsInstance.inlOp _ P ψ_in`) and the targets
  `e^{-iτ(H_X ⊕ 0)} (ψ_in ⊕ 0) = (e^{-iτ H_X} ψ_in) ⊕ 0` (`evolve_padMat`).
* Algorithms are those of `time_main`: non-adaptive programs over the native primitives of the
  padded data with an untouched spectator register (`specOracles Ω`), run on an
  input-independent seed `φ₀` and read through `e` into `ℂ^{N ⊕ P}` ⊗ garbage `G`, and
  `ε`-accurate (`Readout.Accurate`) for the padded targets on every input. As in `main_max`,
  `‖φ₀‖ ≤ 1` and the isometry `e† ∘L e = 1` are assumed for the time and mixed families only.
  `Q = p.labelCount .value` counts value queries.
* `time_main_pad`, `mixed_main_pad`, `precision_main_pad`: for every padding `P`, under
  `HSRange τ s ε` (and `L ≥ 64τ`, `s ≥ 64n/τ` for the mixed family, `L ≥ 64τ` for the precision
  family), the bounds of `time_main`, `mixed_main` and `precision_main` with the same constants.
  `time_pad_spec`, `mixed_pad_spec` and `precision_pad_spec` are `time_spec`, `mixed_spec` and
  `precision_spec` for the padded families; the last two are Lemmas `hsl:lem:mixed` and
  `hsl:lem:precision` for padded families at arbitrary family parameters.
* `main_max_pad` (eq. `hsl:eq:main`): for any paddings `PT`, `PM`, `PP` and any three
  algorithms, accurate for the padded time, mixed and precision families respectively,
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`. `main_exists_pad`: one of the three padded
  families forces every accurate algorithm (seed of norm at most one, isometric readout) to make
  at least `mainBound τ ε s = c₀ (√s τ + √(sτr) + r)` value queries (`ForcesQueries`). Unlike
  `main_exists`, `ForcesQueries` assumes the seed bound and the isometric readout for the
  precision family as well, so that disjunct is slightly weaker.
* `hard_instances_pad`: the three padded families satisfy `HardInstance` (real symmetric,
  operator norm and maximum row and column Euclidean norms exactly one, maximum row and column
  sparsity exactly `s`, exact dyadic words with position-independent decode, input-independent
  locators) and have dimension at most `4 s (τ + r + 1) + |P|`.
* `third_sum_le_max`: if `A ≤ Q_T`, `B ≤ Q_M` and `C ≤ Q_P`, then
  `(A + B + C)/3 ≤ max(Q_T, Q_M, Q_P)`: the maximum of three nonnegative lower bounds is at least a
  third of their sum.
* One common dimension. `PadTo S Nd = Fin (Nd - |S|)`, and `|S ⊕ PadTo S Nd| = Nd` when
  `|S| ≤ Nd` (`card_padTo`); every `Nd ≥ 4 s (τ + r + 1)` is at least the three dimensions
  (`card_le_of_dim`). For every `Nd` at least the three dimensions (for instance a large enough
  power of two), `main_max_common_dimension` and `main_exists_common_dimension`: the three
  families padded by `PadTo _ Nd` all have dimension exactly `Nd` and obey the max form and the
  family form of eq. `hsl:eq:main`, so the worst case in dimension `Nd` obeys eq. `hsl:eq:main`.
* Proof. Every primitive of the padded data is again a `hardCost` program over the Boolean oracle
  of the same hidden bits: two Boolean queries per value call, locators free
  (`implementsOn_padBitData_spec`, `implementsOn_padSearchData_spec`,
  `implementsOn_padScalarData_spec`). The isometry `padReadout P G i₀` keeps the original
  coordinates and moves the padding coordinates into the garbage, at the system state `i₀`
  (`padReadout_isometry`, `padReadout_comp_isometry`); a Hermitian contraction `M` is measured
  through it as the Hermitian contraction `M ⊕ M_{i₀ i₀} 1_P` (`outObs_padReadout`,
  `isSelfAdjoint_blockObs`, `norm_blockObs_le`), which has the same expectation on `ψ ⊕ 0` as `M`
  on `ψ`, so accuracy for a padded target is accuracy for the original target with the same `ε`
  (`accurate_padReadout`, `accurate_pad_evolve`). The generic lemmas `time_general`,
  `mixed_general` and `precision_general` of `SparseLowerBounds` then apply with the readout
  `padReadout P G refZero ∘L e`, and `assembly` combines the three bounds. Padding keeps
  `HardInstance` (`padBitData_hardInstance`, `padSearchData_hardInstance`,
  `padScalarData_hardInstance`), since norm one and sparsity `s` are attained on the original
  block.

Every theorem of the library is axiom-audited in `LowerBoundRemarks/Audit.lean`.

**Formalisation choices.**

* The parity remark is formalised for any block-affine family with arbitrary balanced per-block
  signs, in any complete normed `ℂ`-algebra with `‖1‖ = 1`; the `hsl` parity and matrices with
  the spectral norm are special cases. It is not applied in Lean to the hard families of
  `SparseLowerBounds`.
* The linear systems are padded by an identity block, `A_X ⊕ I`, with the right-hand side
  extended by zero, as in the remark; the Hamiltonian families are padded by known zeros,
  `H_X ⊕ 0`, as in the proof of Theorem `hsl:thm:main`. In both cases the
  padding block is known: its entries do not depend on the input.
* The padded linear-system bounds are proved from the counting step for an arbitrary index type
  and the access conditions `HardAccess`, with the constants of `lower_bound_sharp` and
  `lower_bound`; the padded Hamiltonian bounds are reduced to the generic lemmas of
  `SparseLowerBounds` through the readout `padReadout`, with the constants of `time_main`,
  `mixed_main`, `precision_main` and `main_max`.

**Not formalised.** The parity remark is a structural statement, not a lower bound: it does not
exclude different reductions or different readouts, and it does not show that the remaining
logarithmic gap of Theorem `hsl:thm:main` is unavoidable. For the padded linear systems, the
readout forms `lower_bound_readout` and `lower_bound_sharp_readout`, the actual condition number
`family_cond` and the matching upper bound `upper_meets_lower` are not restated. For the padded
Hamiltonian families only the non-adaptive spectator form is restated: the forms without a
spectator register (`*_main_native`, `main_max_native`), the heralded forms of Lemma
`odel:lem:herald`, the endpoint forms and the adaptive form
`AdaptiveHamiltonianLowerBound.main_max_tree` are not. The padding remarks of the
differential-equation lower bounds (Section `part:odel`) are not treated.
-/
