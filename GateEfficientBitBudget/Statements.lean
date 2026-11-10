import GateEfficientBitBudget.Witness
import GateEfficientBitBudget.NonVacuity
import GateEfficientBitBudget.Synth
import GateEfficientBitBudget.HamiltonianBudget
import GateEfficientBitBudget.SynthHamiltonian

/-!
# The gate budgets in the bit-length parameter `𝔟`: paper-to-Lean entry point

Theorem `hs:thm:gates` of the accompanying paper concludes, for standard efficiently decoded binary
or fixed-point entries and public parameters of bit lengths at most `b_data`,
`G_additional = q poly(b_data, log(N+1), log((q+1)/ε))` (equation `hs:eq:gate-binary`). Theorem
`ode:thm:gates` bounds the complete dissipative solver by
`G_ODE ≤ C ḡ [q P(𝔟) + G_src(ν) + A_src(ν)]` gates and `A_ODE ≤ P(𝔟) + C A_src(ν)` auxiliary qubits
(equations `ode:eq:gate-main`, `ode:eq:gate-space`) in the word budget
`𝔟 = b_data + log(N+1) + log(M+1) + log(m+1) + log((q ḡ+1)/ε)` (equation `ode:eq:gate-word-budget`;
`b_data` bounds the bit lengths of the represented entries and public parameters; the proof reads
these forms off the assembly cost `ode:eq:gate-assembly-cost`). The released libraries
`GateEfficientBinary`, `GateEfficientBinaryTime`, `GateEfficientODEBudget` and
`GateEfficientSynthesis` state the budgets as polynomials in the register words of the
constructions; the guide of `GateEfficientODEBudget` lists the bound of the words of the arithmetic
accuracy, of the LCHS grid spacing and of the decoder scale by `𝔟` as not formalised. This library
fixes a bit-length model of the public parameters, defines `𝔟`, bounds every register word linearly
by `𝔟`, and states the budgets in `𝔟` with explicit constants, keeping every released conclusion
they are derived from. References to the manuscript use its labels.

The released libraries are unchanged; their guides predate this library. Of the items that the
`GateEfficientODEBudget` guide lists as not formalised (and the corresponding remark in the
docstring of `GateEfficientODEBudget/Words.lean`), this library adds the bound of `F`, `n_c` and
the bits of `κ` by `𝔟` (`words_le`, `wordsT_le`) and the comparison of `q*`, `ℓ` for `(2g, ε/2)`
with those for `(g, ε)` (`qOf_two_le`, `logBudget_two`, `bitB_two_le`,
`binary_ode_time_budget_bits_user`). It also states the finite-gate-set budget in `𝔟`
(`binary_ode_budget_trials_bits`) rather than in the words. The `GateEfficientBinary` guide reads
`q · poly(b, log N, log((q+1)/ε), |log c₀|)` off its bounds rather than as a Lean statement;
`binary_simulation_bits` is that statement, with `|log₂ c₀| ≤ b_data` (`HasBits.abs_logb_le`).
No result from another paper is used, except single-qubit synthesis and the decomposition of
controlled gates as the hypothesis `GateSynth.Synthesis` of the finite-gate-set forms. All
declarations below are in the namespace `SparseHamiltonian.GateBitBudget`.

* Bit lengths and the word budget: `HasBits` (`hasBits_iff`, `hasBits_fixed`, `hasBits_int`,
  `exists_hasBits`, `hasBits_zero`, `HasBits.mono`, `HasBits.abs_lt`, `HasBits.lt`,
  `HasBits.one_le_mul_abs`, `HasBits.abs_logb_le`), `bitB` (the paper's `𝔟`), `bitH` (`bitH_eq`),
  `log_le_logb`.
* Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`: `binary_ode_budget_bits`
  (constant coefficients), `binary_ode_time_budget_bits` (time-dependent coefficients) and
  `binary_ode_time_budget_bits_user` (the same with the query shape of the user's `(g, ε)`); the
  key lemmas `words_le`, `words_le_bitB`, `wordsT_le`.
* Equation `hs:eq:gate-binary` in `b_data`, `log(N+1)`, `log((q+1)/ε)`:
  `binary_simulation_bits` (time-independent Hamiltonians), `binary_time_simulation_bits`
  (time-dependent Hamiltonians on `2^m` time slots); `cordicWords`, `cordic_words`,
  `privGates_binary`, `privGates_binaryT`, `cordicWords_le`, `hs_gates_le`, `hs_gatesT_le`.
* Over a finite gate set: `binary_ode_budget_trials_bits`, `binary_ode_time_budget_trials_bits`,
  `binary_simulation_budget_synth_bits`, `binary_time_simulation_budget_synth_bits`.
* Compatibility of the hypotheses: `zetaOf`, `zetaOf_spec`, `withChoice`, `withChoice_spec`,
  `withChoiceT₀`, `withChoiceT`, `withChoiceT_spec`, `hs_zeta_spec`, `hs_zeta_shape_spec`,
  `hs_zeta_shape_specT`; the internal ratio and accuracy of the time-dependent solver:
  `logBudget_two`, `qOf_two_le`, `bitB_two_le`, `time_budget_user`.
* Satisfiability and non-vacuity: `exists_common_bits`, `withChoice_bits`, `withChoiceT_bits`,
  `pointPub`, `pointPub_ok`, `pointPubT₀`, `pointPubT`, `pointPubT_ok`, `bits_witness`,
  `bits_witnessT` (`Witness`); `pointData`, `pointData_range`, `pointData_matrix`,
  `twos_inl_zero`, `twos_inr_zero`, `gauss_zero_word`, `ode_all_hyps`, `ode_time_all_hyps`,
  `hs_all_hyps`, `hsT_all_hyps` (`NonVacuity`).
* The scales and the words: `one_le_mul_eta`, `one_le_mul_theta`, `gam_inv_le`, `gammaOf_inv_le`,
  `logb_inv_gammaOf_le`, `one_le_radius`, `rho_le`, `one_le_mul_rho`, `step_inv_le`,
  `four_div_step_le`, `sqrt_le_self_of_one_le`, `kap_le`, `kap_inv_le` (`Scale`);
  `shape_one_le_X`, `shape_q_le_X`, `shape_div_le_X`, `shape_inv_precision_le`, `shape_ell_le_X`,
  `shape_ell_le_logb`, `logb_X_two_le`, `r_word`, `l_word`, `m_word`, `k_word`, `inv_zeta_le`,
  `F_word`, `nOf_word`, `kap_words` (`Sizes`); `inner_le`, `prepBound_le`, `prepBoundT_le`,
  `log_prep_le`, `log_three_div_le`, `log_q_cube_le`, `log_factor_le`, `log_factorT_le`,
  `tested_le`, `testedT_le` (`SynthWords`); `synth_arith` (`Synth`); `le_shape`,
  `hs_final_arith`, `simM_word`, `simR_word`, `hs_log_le`, `hs_synth_arith`.

**The bit-length model** (`Bits`). `HasBits b x :⇔ ∃ n : ℤ, |n| < 2^(2b) ∧ x = n / 2^b`: the
real public parameter `x` is a signed fixed-point number with `b` integer and `b` fractional bits;
equivalently, `x` is an integer multiple of `2^(-b)` with `|x| < 2^b` (`hasBits_iff`). A
fixed-point word `n / 2^f` with `|n| < 2^(i+f)` (`i` integer and `f` fractional bits, any split
of a word of length `i + f` plus sign) has `HasBits (i + f)` (`hasBits_fixed`), an integer of
`i` bits has `HasBits i` (`hasBits_int`), zero has every bit length, every dyadic rational has
some bit length (`exists_hasBits`), and the bit length is monotone (`HasBits.mono`). The
consequences used are `|x| < 2^b` (`HasBits.abs_lt`, `HasBits.lt`) and, for `x ≠ 0`,
`1 ≤ 2^b |x|` (`HasBits.one_le_mul_abs`), so that `|log₂ |x|| ≤ b` (`HasBits.abs_logb_le`). The
bit-length hypotheses are on exactly those public parameters whose magnitudes enter the register
words other than through `𝔟`: the stored bits `b ≤ b_data` and `HasBits b_data` for the decoder
scale `c₀` (all endpoints) and, for the dissipative solvers, the time `T` and the energy bounds
`η_H`, `η_D` (through `κ` and `log(1/γ)`). The other public data need none. `k_x` and
`s = 2^σ ≤ 2^k_x` enter through `log(N+1)`, the mesh exponent through `log(M+1)`, and `g` and `ε`
through `log((q g + 1)/ε)`. The rescaling `γ` is the public function `gammaOf`, and the arithmetic
accuracy has an explicit lower bound. The norms `r₀`, `r_b`, the source accuracy `ζs` and the
source circuits do not enter the words.

**The word budget** (`bitB`, `bitH`). `bitB bd N M m q g ε = bd + log₂(N+1) + log₂(M+1) +
log₂(m+1) + log₂((q g + 1)/ε)` is equation `ode:eq:gate-word-budget` with base-2 logarithms
(`Real.logb 2`); since `log₂ x = log x / log 2`, the bounds hold in the paper's natural-log `𝔟`
with the constants multiplied by at most `(1/log 2)³ < 3.01` (`(1/log 2)⁴ < 4.34` for the forms
over a finite gate set); the proofs use the converse `log x ≤ log₂ x` for `x ≥ 1`
(`log_le_logb`). `bitH bd N q ε = bd + log₂(N+1) + log₂((q+1)/ε) = bitB bd N 0 0 q 1 ε`
(`bitH_eq`) is the argument of `hs:eq:gate-binary`. In the endpoints `N = 2^k_x` (the padded
dimension of the binary data), `q` is the query shape `q*` of the construction and `ḡ = g`.

**The key lemma** (`words_le`, `words_le_bitB`, `wordsT_le`). For the public data `q : Pub` of
`GateBinaryODE` with the public rescaling `γ = gammaOf T η_H η_D g ε` (the hypothesis `hγ` of
`GateODEBudget.binary_ode_budget`), an arithmetic accuracy `ζ ≥ ν/(196608 q*)`
(`q* = qOf s T η_H η_D g ε`, `ν = ε/(10000 g)`, `ℓ = log(1/ν)`) and the bit-length hypotheses,
the register words `𝔴 = GateODEBudget.words q = k_x + b + m + r + k + l + F + n_c + ⌈log₂ ⌈κ⌉⌉ +
⌈log₂ ⌈1/κ⌉⌉` satisfy `𝔴 + ℓ ≤ 300 (𝔟₀ + 1)`, `𝔟₀ = bitB b_data (2^k_x) 0 0 q* g ε`
(`words_le`), hence `𝔴 + ℓ ≤ 300 (𝔟 + 1)` for `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`
(`words_le_bitB`). With `X = (q* g + 1)/ε` (`q* ≤ X`, `1/ν ≤ 10⁴ X`, `ℓ ≤ 14 + log₂ X`,
`Sizes`): from the released size bounds `r ≤ 15 + log₂ X`, `l ≤ 21 + 2 log₂ X`,
`m ≤ 15 + 2 log₂ X`, `k ≤ 16 + 2 log₂ X`; from `ζ ≥ ν/(196608 q*)` and the LCHS step
`h = R/K ≥ 1/J` (`step_inv_le`, `J ≤ 60 q* ℓ`) the fractional bits `F = ⌈log₂ ⌈4/(ζ h)⌉⌉ ≤
54 + 4 log₂ X` and the CORDIC steps `n_c = nOf(ζ/2) ≤ 38 + 2 log₂ X`; for the decoder scale
`κ = γ √(4s) c₀ / (2^(k+F+10) ρ)`, `ρ = η_H + R η_D`: `⌈log₂ ⌈κ⌉⌉ ≤ 1 + k_x + 2 b_data` and
`⌈log₂ ⌈1/κ⌉⌉ ≤ k + F + 41 + 4 b_data + 2 log₂ X` (`kap_words`), from `κ ≤ 2^(1+k_x+2b_data)`
(`kap_le`; `√s ≤ 2^k_x`, `c₀ < 2^b_data`, `ρ ≥ 2^(-b_data)`) and
`κ⁻¹ ≤ 2^(k+F+10) ρ γ⁻¹ 2^b_data / 2` (`kap_inv_le`) with `ρ ≤ (1 + R) 2^b_data` (`rho_le`) and
the bound of the rescaling `γ⁻¹ ≤ 1 + ℓ/Θ ≤ 2 ℓ 4^b_data` (`gam_inv_le`, `gammaOf_inv_le`,
`Θ = T η_H + T η_D ℓ ≥ T (η_H + η_D) ≥ 4^(-b_data)`, `one_le_mul_theta`), that is
`log₂(1/γ) ≤ 2 b_data + 1 + log₂ ℓ` (`logb_inv_gammaOf_le`). No hypothesis on `γ` is used
besides its public choice. `wordsT_le` is the time-dependent form for `q : PubT` with
`γ = gammaOf T η_H η_D (2g) (ε/2)`, `q* = qOf s T η_H η_D (2g) (ε/2)`, `ν = ε/(40000 g)` and
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` (internal `X` compared by `logb_X_two_le`).

**Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`, constant coefficients**
(`binary_ode_budget_bits`). Hypotheses: `q.OK`, `hγ`, `ν ≤ 196608 q* ζ`, `b ≤ b_data`,
`HasBits b_data c₀`, `HasBits b_data T`, `HasBits b_data η_H`, `HasBits b_data η_D`, and the
binary data `D`, `en`, `hrange`, `hdec` and the valid source circuits `srcC` of
`GateBinaryODE.binary_ode_solver`. With `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε` (`N = 2^k_x`,
the time mesh `M = 2^m` of the released simulator and the `m_src = 2^k` source nodes of the
quadrature register), in every history the native protocol `nprotocol (q.prep srcC) g` uses at
most `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` elementary gates (`G_src = |srcC 0| + |srcC 1|`, `|Zs|`
the source scratch) and its register has at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits: equations
`ode:eq:gate-main` and `ode:eq:gate-space` with `P(x) = 3·10¹¹ (x+1)³`, `C = 10²⁰` and
`A_src = |Zs|`. The conclusion also contains `𝔴 + ℓ ≤ 300 (𝔟+1)` and every conclusion of
`GateODEBudget.binary_ode_budget_words` (`3·10¹² g [q* (𝔴+ℓ+1)³ + G_src + |Zs|]` gates,
`10000 (𝔴+1)³ + 2 |Zs|` qubits) and of `GateODEBudget.binary_ode_budget`: at most
`36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` gates, at most
`3932160 g q*` calls of each matrix oracle besides `40 g` times the calls of the source circuits,
the register size `22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`,
and, for every input and instance as in `binary_ode_solver` with `98304 q* ζ + 2 ζs ≤ ν`, the
guarantees `GateNative.NOutcome` (success probability at least `2/3`, conditional output within
trace distance `ε`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase).

**Time-dependent coefficients** (`binary_ode_time_budget_bits`). Hypotheses: `q.OK` for
`q : PubT` (the mesh condition `steps τ (ν/3) ≤ 2^m` included), `γ = gammaOf T η_H η_D (2g)
(ε/2)`, `ν ≤ 196608 q* ζ` with `q* = qOf s T η_H η_D (2g) (ε/2)`, the bit-length hypotheses, and
the time-indexed binary data and the valid circuits `loadC`, `wpC` of
`GateBinaryODETime.binary_ode_time_solver`. With `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`
(the public time mesh `M = 2^m` and the `2^m` source nodes; the internal `q*` of `(2g, ε/2)` and
the user's `g`, `ε` in the last term): at most `2·10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates
(`G_src = |loadC| + 2 |wpC|`), at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits, `𝔴 + ℓ ≤ 300 (𝔟+1)`
(`𝔴 = wordsT q`, `ℓ = log(40000 g/ε)`), and every conclusion of
`GateODEBudget.binary_ode_time_budget_words` and `GateODEBudget.binary_ode_time_budget`
(`98304 q* ζ + 3 ζs ≤ ν` for the guarantees). By `qOf_two_le` (`q*(2g, ε/2) ≤ 3 q*(g, ε)`),
`logBudget_two` (`ℓ(2g, ε/2) = ℓ(g, ε) + log 4`) and `bitB_two_le` (the internal `q*` raises
`𝔟` by at most `2`), `time_budget_user` turns these bounds into bounds in the query shape
`q* = qOf s T η_H η_D g ε` of the user's `(g, ε)` and its `𝔟`, with the factors `81` (gates) and
`27` (qubits): under the same hypotheses, `binary_ode_time_budget_bits_user` gives at most
`2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` gates and at most `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits.

**Equation `hs:eq:gate-binary`** (`binary_simulation_bits`). For `s ≥ 1`, `τ ≥ 0`,
`0 < ε ≤ 1/2` and `q = √s τ + √(sτ log(1/ε)) + log(1/ε)`, the rescaling `γ ∈ (0, 1]` of
`GateBinary.binary_simulation_budget` (chosen from `s`, `τ`, `ε` before the data; `γ √s ≥ 1`,
`d ≤ 4608 q`, `τ' ≤ √s q`, the released bounds on the simulator words) satisfies: for all binary
sparse data with `s = 2^σ` slots, `k`-bit indices (`N = 2^k`) and `b ≤ b_data` stored bits, every
decoder scale `c₀ > 0` with `HasBits b_data c₀`, every admissible input and every arithmetic
accuracy `ζ ∈ (0, 1]` with `ε/(442368 q) ≤ ζ ≤ ε/(221184 q)` (the upper end is the released
budget; `ζ = ε/(442368 q)` is admissible, `hs_zeta_shape_spec`), the circuit `binarySim` uses at
most `10¹⁵ q (𝔟_H + 1)³` elementary gates with `𝔟_H = bitH b_data (2^k) q ε` (equation
`hs:eq:gate-binary` with the cubic `poly(x) = 10¹⁵ (x+1)³`), the private operation at most
`2·10⁹ (𝔟_H + 1)³` gates, and every conclusion of `binary_simulation_budget` holds (at most
`55296 q` times `2` row, `2` column and `1` value calls, the released gate count
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)`, full-output error at most `ε`). Proof: the
CORDIC counts give `G_C ≤ 57000 (cordicWords + 1)³` (`cordic_words`, `privGates_binary`) for
`cordicWords = k + b + n + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉`, and `cordicWords ≤ 25 (𝔟_H + 1)`
(`cordicWords_le`: `κ = γ √s c₀ ∈ [c₀, 2^k c₀]`, `n ≤ 25 + log₂((q+1)/ε)`); `simM_word` and
`simR_word` bound `m ≤ 5 + 2k + 2 log₂((q+1)/ε)` and `r ≤ 15 + log₂((q+1)/ε)` (`hs_gates_le`).
`binary_time_simulation_bits`: the same for `binary_time_simulation_budget`
(`q = √s t + √(st log(2/ε)) + log(2/ε)`, `0 < ε ≤ 1`, the time-indexed data on `M = 2^m` slots,
the path and mesh hypotheses of the released budget; `ζ = ε/(442368 q)` is admissible,
`hs_zeta_shape_specT`), with at most `10¹⁵ q (𝔟_H + log₂(M+1) + 1)³` gates (`hs_gatesT_le`), the
per-call bound `2·10⁹ (𝔟_H + 1)³`, and every conclusion of `binary_time_simulation_budget`.

**Over a finite gate set.** Under `Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀`
(`c₀, c₁ ≥ 0` the synthesis constants, not the decoder scale `c₀`), `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢` (stated assumptions: `GateSynthTrials.extra_hyps` meets them over
`closeKinds 𝒢₀`, and the gate counts are then over that set), and the hypotheses of
`binary_ode_budget_bits`: `binary_ode_budget_trials_bits` gives
`B = prepBound q srcC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src` (`prepBound_le`), at most
`40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` in every history of the synthesised
protocol `nprotocol (synthPrep hS (ν/3) (q.prep srcC)) g` (the synthesis factor
`log((B+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)`, `log_factor_le`), at most
`7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits, and every conclusion of
`GateODEBudget.binary_ode_budget_trials` (valid gates of `𝒢` in every trial, the released counts,
and with `98304 q* ζ + 2 ζs ≤ ν` the guarantees `NOutcome`, every successful trial included).
`binary_ode_time_budget_trials_bits`: the same for `binary_ode_time_budget_trials` (`80 g`,
`40 g`, `prepBoundT`, `3 ζs`). `binary_simulation_budget_synth_bits` (from
`GateSynth.binary_simulation_budget_synth`, synthesis accuracy `ε' ∈ (0, 1]`, the hypotheses of
`binary_simulation_bits`): at most `10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε')) + c₀)` gates of
`𝒢` (`hs_log_le`, `hs_synth_arith`), with every released conclusion (validity, gate kinds, calls,
the released gate count, full-output error at most `ε + ε'`); this is `hs:eq:gate-binary` after
synthesis, a polynomial of degree `4` in `𝔟_H` and `log(1/ε')`.
`binary_time_simulation_budget_synth_bits`: the same with `𝔟_H + log₂(M+1)`.

**Compatibility and satisfiability of the hypotheses.** `zetaOf ν q* = ν/(196608 q*)` has
`0 < ζ ≤ 1`, `ν ≤ 196608 q* ζ` and `98304 q* ζ = ν/2`, so the released budget
`98304 q* ζ + 2 ζs ≤ ν` holds exactly for `ζs ≤ ν/4` (`ζs ≤ ν/6` with `3 ζs`) (`zetaOf_spec`).
`withChoice_spec`: for public data with `Pub.OK`, the data `withChoice q` (`γ = gammaOf …`,
`ζ = zetaOf ν q*`, all else unchanged) satisfy `Pub.OK`, `hγ` and `ν ≤ 196608 q* ζ`;
`withChoiceT_spec`: the same for `PubT` with the coarsest admissible mesh, the least exponent
`m = simM τ ν` with `steps τ (ν/3) ≤ 2^m` (`withChoiceT`), so that the mesh condition of
`PubT.OK` holds (any finer power-of-two mesh is admissible as well and enters through
`log₂(M+1)`). The bit-length hypotheses concern `b`, `c₀`, `T`, `η_H`, `η_D`, which these choices
leave unchanged; finitely many dyadic rationals and `b` have a common bit length `b_data ≥ b`
(`exists_common_bits`, from `exists_hasBits`). Hence for public data with `Pub.OK` (`PubT.OK`) and
dyadic `c₀`, `T`, `η_H`, `η_D` the data `withChoice q` (`withChoiceT q`) satisfy every hypothesis
of `binary_ode_budget_bits` (`binary_ode_time_budget_bits`) on the public parameters for some
`b_data` (`withChoice_bits`, `withChoiceT_bits`), and the explicit public data `pointPub`,
`pointPubT` (`k_x = σ = 0`, `b = 1`, `c₀ = T = η_H = g = 1`, `η_D = 0`, `ε = 1/2`) with these
choices satisfy all of them jointly (`bits_witness`, `bits_witnessT`). The remaining hypotheses
(the binary data `D`, `en`, `hrange`, `hdec` and the valid source circuits) are those of the
released endpoints, which the public choices do not affect. One-point data meets them together
with the explicit public data: `k_x = σ = 0`, every entry the zero word, `en` the identity, empty
source circuits (`pointData`; `ode_all_hyps`, `ode_time_all_hyps` state every hypothesis of
`binary_ode_budget_bits`, `binary_ode_time_budget_bits` for these data, together with the gate
bound of the endpoint). For `hs:eq:gate-binary`, a dyadic `c₀` and `b` have a common bit length
(`exists_common_bits b [c₀]`), and `ζ = ε/(442368 q)` is admissible because `q ≥ log 2 > 1/2`
(`hs_zeta_spec`, `hs_zeta_shape_spec`, `hs_zeta_shape_specT`). For `s = 1`, `τ = t = 0`,
`ε = 1/2`, the one-point data with `b = 1`, `c₀ = 1` (zero matrix) and, for time-dependent
Hamiltonians, the zero path with `β = δ = 0` and the least admissible mesh meet every hypothesis
of `binary_simulation_bits` and `binary_time_simulation_bits` at once (`hs_all_hyps`,
`hsT_all_hyps`, with the gate bounds of the endpoints).

**Proof map.** `Bits` (bit lengths, `𝔟`, word estimates `clog_le_mul_pow`, `nat_le_mul_pow`,
`nat_le_logb`, `cube_le`, `budget_mono`) → `Scale` (the rescaling, the energy, time and sector
scales, the LCHS step, the decoder scale) → `Sizes` (the words from `X`) → `Constant`
(`words_le` from `GateODEBudget.binary_ode_sizes`; `binary_ode_budget_bits` from
`GateODEBudget.binary_ode_budget_words` and `GateODEBudget.binary_ode_budget`; the choices) →
`Time` (`wordsT_le` from `binary_ode_time_sizes`; `binary_ode_time_budget_bits` from
`binary_ode_time_budget_words` and `binary_ode_time_budget`; the internal ratio;
`binary_ode_time_budget_bits_user`) → `Witness` (the explicit public data and satisfiability,
from `withChoice_spec`, `withChoiceT_spec`, `Sim.simM_spec`); `Hamiltonian`, `HamiltonianGates`
(from `GateBinary.cordicArith_counts`, `GateBinary.params_fields`, `GateODEBudget.arith_poly`,
`computeV_nGates`, `computeVT_nGates`) → `HamiltonianBudget` (`binary_simulation_budget`,
`binary_time_simulation_budget`) → `NonVacuity` (the endpoints applied to one-point data);
`SynthWords`, `Synth` (`GateODEBudget.binary_ode_budget_trials`,
`GateODEBudget.binary_ode_time_budget_trials`, `binary_arith_words`, `binary_time_arith_words`)
and `SynthHamiltonian` (`GateSynth.binary_simulation_budget_synth`,
`GateSynth.binary_time_simulation_budget_synth`).

**Formalisation choices and deviations from the paper.**

* Bit lengths are fixed-point bit lengths (`HasBits`): `|log₂ |x|| ≤ b` for a nonzero parameter
  of bit length `b`. The released arithmetic holds the decoder scale `κ` in fixed point, with
  `⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` bits. For floating-point public parameters this is polynomial in
  the exponent values, not in the word lengths, so floating-point formats are not covered (the
  paper's polynomial-cost assumption on the arithmetic holds here for fixed-point parameters).
  The entries are the released format, two `b`-bit two's complement words with one public scale;
  other fixed-point entry formats need another decoder.
* `𝔟` uses base-2 logarithms; in the paper's `𝔟` the bounds hold with the constants multiplied
  by at most `(1/log 2)³ < 3.01` (`(1/log 2)⁴ < 4.34` over a finite gate set).
* The arithmetic accuracy is a free public parameter of the released solvers, bounded only above;
  the endpoints take any `ζ ≥ ν/(196608 q*)` (respectively `ζ ≥ ε/(442368 q)`) besides the
  released budget, and `zetaOf` (respectively `ε/(442368 q)`) is an explicit admissible choice.
* The released rescaling `γ = min(1, √(Θ/ℓ))` has no floor `p^(-1/2)`; `log(1/γ)` is bounded by
  the bit lengths of `T`, `η_H`, `η_D` and `log ℓ` (`gammaOf_inv_le`) instead of `log(2s)/2`.
* Constant coefficients: `M = 2^m` is the time mesh of the released simulator (`simM τ ν`) and
  `m_src = 2^k` the source nodes of the quadrature register; both are `poly(q*/ν)` for constant
  coefficients, and the key lemma `words_le` holds without the terms `log(M+1)`, `log(m+1)`.
  Time-dependent coefficients: `M = 2^m` is the public mesh (which also carries the regularity of
  the path) and the source quadrature uses the same `2^m` nodes; `q*` is that of the internal
  `(2g, ε/2)` of the released solver, and `binary_ode_time_budget_bits_user` restates the bounds
  with the `q*` of `(g, ε)` (factors `81` and `27`).
* The constants are explicit and generous (`300`, `10²⁰`, `2·10²⁰`, `2·10²²`, `3·10¹¹`,
  `9·10¹²`, `7·10¹¹`, `10¹⁵`, `2·10⁹`, `2·10¹⁸`, `64`, `36`); the polynomial is cubic because of
  the released CORDIC counts (register width `2 n² + …` times `n + 1` steps).
* The time-dependent form of `hs:eq:gate-binary` is not displayed in the paper; the Lean form adds
  `log₂(M+1)` for the `m` slot wires, which enter the released gate count linearly.
* Over a finite gate set the synthesis factor multiplies the whole native preparation, the source
  circuits included, as in the released finite-gate-set budgets; it is bounded by
  `64 (𝔟+1) + log(G_src+1)`.

Every theorem of the library is axiom-audited in `GateEfficientBitBudget/Audit.lean`.

**Not formalised.** Floating-point parameter formats; the source certificates, the construction
of the source circuits and their costs `G_src(ν)`, `A_src(ν)` (they remain the parameters
`G_src`, `|Zs|` of the bounds; the absorption of source costs polynomial in `𝔟` into
`q poly(𝔟)` is not a Lean statement); the cases `T = 0` and `η_H + η_D = 0`, which the released
public conditions exclude; the qubit count of `hs:thm:gates` in `𝔟` (the released budget
`binary_simulation_budget` states gates and calls only); `𝔟` forms of the finite-gate-set solvers
with every trial synthesised (`GateBinaryODE.binary_ode_solver_synth`,
`GateBinaryODETime.binary_ode_time_solver_synth`); `𝔟` forms of the native constructions whose
arithmetic is a hypothesis (`GateEfficientNative`); equations `ode:eq:gate-select-gates` and
`ode:eq:gate-constant-source` as separate statements; single-qubit synthesis and the decomposition
of controlled gates (the hypothesis `GateSynth.Synthesis`).

**Provenance.** New library; it reuses without change `GateEfficientODEBudget` (`words`,
`wordsT`, `gammaOf`, `qOf`, `thetaOf`, `gam`, `gam_cases`, `ShapeOK`, `pub_shapeOK`,
`pubT_shapeOK`, `sqrt_four_mul`, `binary_ode_sizes`, `binary_ode_time_sizes`, `binary_ode_budget`,
`binary_ode_time_budget`, `binary_ode_budget_words`, `binary_ode_time_budget_words`,
`binary_arith_words`, `binary_time_arith_words`, `arith_poly`, `wordOf_le`, `prepBound`,
`prepBoundT`, `binary_ode_budget_trials`, `binary_ode_time_budget_trials`),
`GateEfficientBinaryODE` (`Pub`, `fOf`, `hStep`, `hStep_pos`, `kapOf`) and
`GateEfficientBinaryODETime` (`PubT`, `gridP`, `kapT`), `GateEfficientODE`
(`AnalyticLCHS.step`, `halfCount`, `gridSize`, `halfCount_pos`; `Params`, `Time.TParams`),
`GateEfficientHamiltonian` (`GateCircuit.Sim.simM`, `simM_spec`), `GateEfficientNative`
(`privGates`, `nprotocol`, `NOutcome`), `GateEfficientBinary` (`binary_simulation_budget`,
`cordicArith_counts`, `params_fields`, `computeV_nGates`, `Cordic.nOf`, `Cordic.wordOf`,
`Cordic.g2Of`, `Cordic.lkOf`, `binarySim`, `twos`, `gauss`, `lowWord`), `GateEfficientBinaryTime`
(`binary_time_simulation_budget`, `computeVT_nGates`, `binaryTimeSim`), `GateEfficientSynthesis`
(`binary_simulation_budget_synth`, `binary_time_simulation_budget_synth`, `Synthesis`),
`GateEfficientSynthesisTrials` (through the trials budgets), `SparseODE.ImprovedODEQueryBudget`
(`logBudget`, `precision`, `radius`, `radius_le`, `logBudget_ge_one`, `precision_pos`,
`precision_le_one_ten_thousandth`), `SparseODE.ODEGaussianParametersContinuation2`
(`ODEGaussianParameters.radius_ge_four`), `SparseHamiltonian.ImprovedPrecisionBudget` (`shape`,
`targetLog_ge_half`) and `SparseHamiltonian.NativeSparseBlockEncoding` (`Data`).
-/
