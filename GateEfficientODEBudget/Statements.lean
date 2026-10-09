import GateEfficientODEBudget.Synth
import GateEfficientODEBudget.Words

/-!
# The asymptotic gate budget of the dissipative solvers: paper-to-Lean entry point

Theorem `ode:thm:gates` of the accompanying paper bounds the complete dissipative solver by
`G_ODE ≤ C ḡ [q P(𝔟) + G_src(ν) + A_src(ν)]` non-matrix-oracle gates (equation
`ode:eq:gate-main`) and `A_ODE ≤ P(𝔟) + C A_src(ν)` auxiliary qubits (equation
`ode:eq:gate-space`), with `O(ḡ q)` matrix queries and `O(ḡ)` source-preparation calls, where
`ν = ε/(10⁴ ḡ)`, `ℓ = log(1/ν)`, `Θ = T η_H + T η_D ℓ` and `q = √s Θ + √(sΘℓ) + ℓ` (equation
`ode:eq:gate-q`). The released solvers from binary data (`GateBinaryODE.binary_ode_solver`,
`GateBinaryODETime.binary_ode_time_solver`) count their gates through the filter degree `d`, the
LCHS grid `J` and the register words (`GateBinaryODE.binary_ode_gate_count`,
`GateBinaryODETime.binary_ode_time_gate_count`), with the Cayley rescaling `γ` a free public
datum. This library chooses `γ` from the public data before the data, proves `d = O(q)`,
`J = O(q ℓ)` and that the words `m`, `r`, `k`, `l` are `O(log(q/ν))`, and states the resulting
budgets with explicit absolute constants: before synthesis, as a polynomial in the register
words, and over a finite gate set with the per-trial claim (through
`GateEfficientSynthesisTrials`). The released libraries are unchanged. No result from another
paper is used, except single-qubit synthesis and the decomposition of controlled gates as the
hypothesis `GateSynth.Synthesis` of the finite-gate-set form. All declarations below are in the
namespace `SparseHamiltonian.GateODEBudget`.

* The public rescaling and the size bounds: `gam`, `thetaOf`, `qOf`, `gammaOf`, `ShapeOK`
  (`ShapeOK.tau_le`, `ShapeOK.width_mul_le`, `ShapeOK.degree_shape_le`, `ShapeOK.lamD_le`,
  `ShapeOK.lam_le`, `ShapeOK.grid_le`, `steps_le`); the sizes of the binary solvers:
  `binary_ode_sizes`, `binary_ode_time_sizes` (`pub_shapeOK`, `pubT_shapeOK`).
* Equation `ode:eq:gate-main` before synthesis: `binary_ode_budget` (constant coefficients),
  `binary_ode_time_budget` (time-dependent coefficients).
* The same as a polynomial in the register words: `words`, `wordsT`, `binary_arith_words`,
  `binary_time_arith_words`, `binary_ode_budget_words`, `binary_ode_time_budget_words`.
* Over a finite gate set, with the per-trial claim: `binary_ode_budget_trials`,
  `binary_ode_time_budget_trials` (`prepBound`, `prepBoundT`).
* Arithmetic: `gate_budget_arith`, `gate_budget_arith'`, `call_budget_arith`,
  `prep_budget_arith`, `prep_budget_arith'`, `arith_poly`, `arith_words`, `words_gate_arith`,
  `clog_two_add_two_le`, `wordOf_le`, `card_XW_SZ4`, `card_SX`.

**The public rescaling** (`Shape`). `ℓ = log(10000 g/ε) = log(1/ν)`
(`ImprovedODEQueryBudget.logBudget`), `Θ = thetaOf T η_H η_D g ε = T η_H + T η_D ℓ` and
`q* = qOf s T η_H η_D g ε = √s Θ + √(sΘℓ) + ℓ` (`ImprovedODEQueryBudget.queryShape`), which is
`q` of equation `ode:eq:gate-q` with `s = 2^σ` the padded slot count of the binary data. The
rescaling is `γ = gammaOf T η_H η_D g ε = min(1, √(Θ/ℓ))`: a function of `T`, `η_H`, `η_D`, `g`
and `ε` only, so it is chosen before the binary data, the input, the source circuits and the
instance (the endpoint hypothesis `hγ : q.γ = gammaOf …`). In the two regimes
(`gam_cases`) `γ = 1` (`ℓ ≤ Θ`) or `Θ/γ = γℓ = √(Θℓ)`; hence for `ShapeOK` (the public
positivity conditions) the common simulation time `τ = T √(4s) (η_H + R η_D)/γ` is at most
`16 q*` (`tau_le`), `width(4s, γ) (1 + log(3/ν)) ≤ 16 q*` (`width_mul_le`), so the released degree
bound `d ≤ 128 (τ q̄ + Q (1 + log(3/ν)))` gives `d ≤ 4096 q*` (`degree_shape_le`),
`T λ_D ≤ 2 q*/ℓ` (`lamD_le`), `T (λ_H + λ_D) ≤ 2 q*` (`lam_le`), the released LCHS grid bound is at
most `60 q* ℓ` (`grid_le`), and the released simulator schedule has at most
`2 + 64 q* + √(12288 q*³/ν)` steps (`steps_le`).

**The sizes** (`binary_ode_sizes`; hypotheses `q.OK`, `hγ`): `τ ≤ 16 q*`, `d ≤ 4096 q*`,
`2^m < 2 (2 + 64 q* + √(12288 q*³/ν))`, `2^r ≤ 4 (4096 q* + 1)`, `J ≤ 60 q* ℓ`,
`2^l < 2 (60 q* ℓ + 2)` and `2^k < 2 (2 q*/ν + 2)` (`k` the quadrature bits): the degree is
`O(q*)` and the words `m`, `r`, `l`, `k` are `O(log(q*/ν))`. `binary_ode_time_sizes`
(`q : GateBinaryODETime.PubT`, `hγ : q.γ = gammaOf T η_H η_D (2g) (ε/2)`, `q*` and `ℓ` with
`(2g, ε/2)`, the internal ratio and accuracy of the released time-dependent solver): the same
bounds for `τ`, `d`, `r`, `J`, `l`, and the finest admissible mesh `simM τ ν` of the released
simulator has `2^simM < 2 (2 + 64 q* + √(12288 q*³/ν))` slots; the mesh exponent `m` is a public
choice with `steps τ (ν/3) ≤ 2^m` (`PubT.OK`), which also carries the regularity of the generator
path, as the mesh `M` of the paper.

**Equation `ode:eq:gate-main` before synthesis** (`binary_ode_budget`; hypotheses `q.OK`, `hγ`,
the binary data `D`, `en`, `hrange`, `hdec` and the valid source circuits `srcC` of
`binary_ode_solver`). In every history the native protocol `nprotocol (q.prep srcC) g`

* uses at most `36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]`
  elementary gates, `G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one private
  call, `G_src = |srcC 0| + |srcC 1|`, `A = k_x + |Zs| + (6 k_x + 4 b) + bT + bP + A_arith`;
* makes at most `3932160 g q*` calls of each matrix oracle besides `40 g` times the calls of the
  source circuits (`O(ḡ q)` matrix queries, `O(ḡ)` source calls);

its register has `22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`
qubits; and for every input and instance as in `binary_ode_solver` with the arithmetic budget
`98304 q* ζ + 2 ζs ≤ ν` (which implies the released `24 d ζ + 2 ζs ≤ ν`) it has the guarantees
`GateNative.NOutcome`: success probability at least `2/3`, conditional output within trace
distance `ε`, and every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase.
`binary_ode_time_budget` (hypotheses `q.OK`, `hγ`, the time-indexed binary data and the valid
circuits `loadC`, `wpC` of `binary_ode_time_solver`): at most
`73746000 g [q* (G_C + k_x + σ + m + r + ℓ (l+1) + 8) + G_src + A]` gates
(`G_src = |loadC| + 2 |wpC|`), at most `7864320 g q*` calls of each coherent sampled-time oracle
besides `80 g` times the calls of `loadC` and twice those of `wpC`,
`22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47` qubits, and the
guarantees of `binary_ode_time_solver` with `98304 q* ζ + 3 ζs ≤ ν`.

**The budget as a polynomial in the words** (`Words`). `words q = k_x + b + m + r + k + l + F +
n_c + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` (`F` the fractional bits of the LCHS step, `n_c` the CORDIC steps
for the accuracy `ζ/2`, `κ` the decoder scale); `wordsT q` is the same without `k`. From the
released counts `Pub.ar_counts` and `PubT.ar_counts`: `G_C ≤ 65536 (𝔴+1)³`,
`A_arith ≤ 4096 (𝔴+1)³` and `bT, bP ≤ 5 (𝔴+1)` (`binary_arith_words`,
`binary_time_arith_words`). With the hypotheses of `binary_ode_budget` (respectively
`binary_ode_time_budget`) the native protocol uses at most
`3·10¹² g [q* (𝔴 + ℓ + 1)³ + G_src + |Zs|]` (respectively `6·10¹²`) elementary gates in every
history and its register has at most `10000 (𝔴+1)³ + 2 |Zs|` qubits
(`binary_ode_budget_words`, `binary_ode_time_budget_words`): equations `ode:eq:gate-main` and
`ode:eq:gate-space` with `P(x) = C (x + 1)³` in the word parameter `𝔴 + ℓ` and `A_src = |Zs|`.

**Over a finite gate set** (`Synth`; hypotheses `hS : GateSynth.Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` (`c₀, c₁ ≥ 0`), `AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢`, and
those of `binary_ode_budget`; the two gate-set hypotheses are without loss of generality,
`GateSynthTrials.extra_hyps`). With `B = prepBound q srcC`
`= 819400 q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src` (`prep_budget_arith`) and the
synthesised preparation `P = GateSynthTrials.synthPrep hS (ν/3) (q.prep srcC)`,
`binary_ode_budget_trials`: every instruction of every trial `trialN P j` is valid and every gate
is a gate of `𝒢`; one native preparation has at most `B` gates; in every history the synthesised
protocol `nprotocol P g` (only the preparation synthesised, its inverse the exact adjoint, the
zero tests and the sign exact) uses at most `40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n + 3)`
gates of `𝒢`,
`n = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`, and the
calls of `binary_ode_budget`; its register has
`44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95` qubits; and
with `98304 q* ζ + 2 ζs ≤ ν` it has the guarantees `NOutcome`, every successful trial within
`ε/500` of the normalised solution up to a global phase. `binary_ode_time_budget_trials`: the
same with `80 g`, `40 g`, `16 m` and no `k` in `n`, `32 m` and no `k` in the qubits,
`B = prepBoundT q loadC wpC` (without `k`, `G_src = |loadC| + 2 |wpC|`), and the budget
`98304 q* ζ + 3 ζs ≤ ν`.

**Proof map.** `Shape` (rescaling, `d = O(q)`, grid, schedule) → `Constant` (`binary_ode_sizes`
from the released `Params.degree_bound`, `sim_sizes`, `J_le`, `l_bounds`, `k_bounds`;
`binary_ode_budget` from the released `binary_ode_gate_count`, `binary_ode_counts`,
`binary_ode_solver`) → `Time` (the same from `TParams.degree_bound`, `simM_spec`, `r_bounds`,
`J_le`, `l_bounds`, `binary_ode_time_gate_count`, `binary_ode_time_counts`,
`binary_ode_time_solver`) → `Words` (`Pub.ar_counts`, `PubT.ar_counts`, `binary_ode_budget`,
`binary_ode_time_budget`) and `Synth` (`GateSynthTrials.binary_ode_solver_trials`,
`GateSynthTrials.binary_ode_time_solver_trials`, `GateSynth.gates_log_le`).

**Formalisation choices and deviations from the paper.**

* The rescaling is `γ = min(1, √(Θ/ℓ))`, chosen before the data. The paper optimises
  `γ = min{1, max{p^{-1/2}, √(ρT/log(2/ν))}}` once (Lemma `ode:lem:gate-select`, after
  `ode:eq:tradeoff`); here `ρT ∈ [Θ, 8Θ]` (`ImprovedODEQueryBudget.effectiveTime_le`) and
  `log(2/ν) ≤ 2ℓ` change only constants, and the floor `p^{-1/2}` is dropped: the size bounds do
  not need it, but in the paper it bounds `log(1/γ)` by `log(2s)/2`. Any `0 < γ ≤ 1` is allowed
  by the released solvers, so the choice is an extra public hypothesis `hγ`, not a change of the
  solvers.
* The constants are explicit and generous (`C = 36873000`, `73746000`, `3·10¹²`, `6·10¹²`,
  `819400`); the arithmetic budget `98304 q* ζ` replaces `24 d ζ`, so that `ζ` can be chosen
  from `q*` and `ν` before the degree is computed.
* The time-dependent solver works internally with `(2g, ε/2)`; its `q*` and `ℓ` are those of
  `(2g, ε/2)`, which exceed those of `(g, ε)` by at most constant factors (`ℓ` grows by `log 4`;
  an elementary estimate, not stated in Lean).
* Over a finite gate set the logarithmic synthesis factor multiplies the whole native preparation,
  the source circuits included (`B` contains `G_src`), since every gate of the preparation is
  synthesised; the paper's form treats `G_src(ν)` as a finite-gate count.
* The polynomial `P` is evaluated at the words `𝔴` of the construction, not at the paper's
  `𝔟 = b_data + log(N+1) + log(M+1) + log(m+1) + log((q ḡ+1)/ε)`: `k_x = log₂ N`, `b ≤ b_data`
  and `m`, `r`, `k`, `l` are `O(log(q*/ν))` (`binary_ode_sizes`), but `F = ⌈log₂ ⌈4/(ζ h)⌉⌉`,
  `n_c = ⌈log₂ ⌈16/ζ⌉⌉ + 2` and the bits of `κ = γ √(4s) c₀/(2^(k+F+10) ρ)` are not bounded in
  Lean. In the paper they are `O(𝔟)`: the arithmetic accuracy is fixed by the error budget, so
  `log(1/ζ) = O(log((q ḡ+1)/ε))`; `log(1/h) = O(log q*)` (`ShapeOK.lamD_le`); `c₀`, `T`, `η_H`,
  `η_D` are public parameters, whose bit lengths `b_data` includes, and
  `|log ρ| ≤ |log(η_H+η_D)| + log R`; and the paper's `γ ≥ p^{-1/2}` gives
  `log(1/γ) ≤ log(2s)/2`. In Lean the public parameters are real numbers, `ζ` is a free public
  parameter bounded only above (by `98304 q* ζ + 2 ζs ≤ ν`), and `γ = min(1, √(Θ/ℓ))` has no
  lower bound in terms of `s`.

Every theorem of the library is axiom-audited in `GateEfficientODEBudget/Audit.lean`.

**Not formalised.** A bound of the words `F`, `n_c`, `⌈log₂ ⌈κ⌉⌉` and `⌈log₂ ⌈1/κ⌉⌉` by the
paper's `𝔟` (it needs the bit lengths of the public parameters `c₀`, `T`, `η_H`, `η_D`, a lower
bound on `ζ` and, for the rescaling used here, `log(1/γ)`; see above); the source certificates,
the construction of the source circuits and their costs `G_src(ν)`, `A_src(ν)`; the cases
`T = 0` and `η_H + η_D = 0`, which the released public conditions exclude; single-qubit
synthesis and the decomposition of controlled gates (the hypothesis `GateSynth.Synthesis`); the
comparison of `q*`, `ℓ` for `(2g, ε/2)` with those for `(g, ε)`; a word form of the
finite-gate-set budget.

**Provenance.** New library; it reuses without change `SparseODE.ImprovedODEQueryBudget`
(`theta`, `queryShape`, `logBudget`, `radius`, `effectiveTime_le`), the modules
`SparseHamiltonian.CayleyClockInterface` (`width`, `moment`) and `SparseHamiltonian.TimeSchedule`
(`steps`), `GateEfficientHamiltonian` (`GateCircuit.Sim.simM`, `GateCircuit.Sim.simM_spec`),
`GateEfficientODE` (the released size lemmas), `GateEfficientNative` (`nprotocol`, `NOutcome`),
`GateEfficientBinary` (`Cordic.nOf`, `Cordic.wordOf`, `Cordic.g2Of`, `Cordic.lkOf`),
`GateEfficientBinaryODE` and `GateEfficientBinaryODETime` (public data, counts, gate counts,
solvers, arithmetic counts), `GateEfficientSynthesis` (`Synthesis`, `gates_log_le`) and
`GateEfficientSynthesisTrials` (the solvers over a finite gate set with exact reflections).
-/
