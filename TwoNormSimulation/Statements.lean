import TwoNormSimulation.TwoNorm

set_option autoImplicit false

/-!
# Theorem `hs:thm:two-norm`: paper-to-Lean entry point

Section `hs:sec:optimal` of the manuscript states Theorem `hs:thm:two-norm`: with a supplied entry
bound `‖H‖_max ≤ μ`, row and column Euclidean norms at most `η`, `μ ≤ η ≤ √s μ` (eq.
`hs:eq:two-norm-promises`), `θ = η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`, "there is a finite unitary circuit
with error at most `ε`, including all work-register outputs, using [eq. `hs:eq:two-norm-bound`]
primitive sparse queries, with absolute constants; the guarantee includes an untouched
reference"; eq. `hs:eq:two-norm-bound` is `O(√s η|t| + √(sμ|t| r_μ) + r_μ)` with
`r_μ = L/log(e + μL/(η²|t|))`, `L = log(1/ε)`. It is proved in
Appendix B (`twonorm:sec:proof`). This library proves the theorem with the explicit
constant `2·10¹²`. The matching lower bound (Proposition `hsl:prop:two-norm`) is not part of this
library; it is `OptimalLowerBounds.two_norm_main_max`, with the bracket on the aligned families
`OptimalLowerBounds.two_norm_theta`, and for adaptive and measured algorithms
`OptimalLowerBounds.two_norm_main_max_tree`, `OptimalLowerBounds.two_norm_main_max_measured` and
`OptimalLowerBounds.two_norm_measured_theta`.

No result from another paper is used. This library reuses the baseline Cayley simulation of Theorem
`hs:thm:main` (`SparseHamiltonian`), the native signed factor (`NativeSignedFactor`), the large-sparsity core
(`LargeSparsityCore`, whose parameters take a real moment parameter and whose modules
`NativeTwoNorm` and `NativeTwoNormCore` carry the entry scale `μ`), and the common query form of
`OptimalSparseSimulation`. References to the manuscript use its labels. Every
theorem of the library is axiom-audited in `TwoNormSimulation/Audit.lean`.

**Naming convention.** All declarations are in the namespace `TwoNormSimulation`; names below are
relative to it, except the names of other libraries, which are fully qualified. `Simulates` and
`physOracle` are `NativeSignedFactor.Simulates` and `NativeSignedFactor.physOracle`.

## The statement

The sparse data and the query model are those of Theorem `hs:thm:optimal`
(`OptimalSparseSimulation/Statements.lean`): the data
`SparseHamiltonian.NativeSparseBlockEncoding.Data X n Z s`, and programs in the common form
`Simulates (physOracle D) H t ε q` (a known isometric input, one program whose only oracle calls
are the native primitives with spectator registers, unitary for every instance, at most `q` calls
counting adjoints, full-output error at most `ε`).

**Theorem** (`two_norm_simulation`). Let `H(x) = D.matrix x` be Hermitian with row and column
Euclidean norms at most `η` and entries of modulus at most `μ` for every instance, with
`μ ≤ η ≤ √s μ` (`hs:eq:two-norm-promises`), and let `t` be a real time with `θ = η²|t|/μ ≥ 1` and
`0 < ε ≤ 1/64`. Then

`Simulates (physOracle D) H t ε (2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ))`,

with `L = log(1/ε)`, `h_μ = log(e + L/θ)` and `r_μ = L/h_μ` (`hs:eq:two-norm-parameters`; in Lean
`r_μ = SignedFactorSimulation.rb θ ε`, and the bound is `bound s η μ t ε`). The program is the same
for all instances; negative times are included. `two_norm_simulation_with_reference` adds an
untouched finite reference.

## The proof

With `σ = sμ²/η² ≥ 1` (`sigma`, `one_le_sigma`) and `θ = η²|t|/μ` (`thetaT`): `√σ θ = √s η|t|`
(`sqrt_sigma_mul_theta`) and `σθ = sμ|t|` (`sigma_mul_theta`) (`hs:eq:two-norm-rescaling`). The
three regimes of the proof of Theorem `hs:thm:two-norm` (Appendix B):

* *Bounded precision logarithm* (module `Bounded`; the paragraph "Bounded `h`: the baseline"). The
  baseline generator `K₀`, built from `H/η`, has norm at most `√s μ/η = √σ` when the entries are at
  most `μ` (`generator_norm_le_entry`), while its boundary moments are unchanged. the baseline
  Cayley simulation with the schedule `(σ, θ)` (`query_certificate_sigma`,
  `exists_normalized_simulation`; the clock width `⌈max{1, γ√σ}⌉` and the public optimisation of `γ`
  of the baseline, `SparseHamiltonian.ImprovedPrecisionBudget.exists_rescaling_for_precision`) gives
  at most `497664 (√σ θ + √(σθ ℓ) + ℓ)` native calls with `ℓ = log(2/ε)`, for every sign of `t`
  (`bounded_simulation`). For `h_μ < 10⁴`, `L = h_μ r_μ` gives
  `√σ θ + √(σθ ℓ) + ℓ ≤ 1.2·10⁴ (√σ θ + √(σθ r_μ) + r_μ)` (`bounded_shape_le`, with `targetLog_le`:
  `ℓ ≤ (7/6) L`; module `Regimes`).
* *The signed-factor regime* (the paragraph "Large `h` with `τ_ent ≤ Lh`"). For `h_μ ≥ 10⁴` and
  `σθ < L h_μ`, the native signed factor with entry scale `κ = μ`
  (`NativeSignedFactor.native_signed_simulation`, `T = sμ|t| = σθ`, `b = √s η|t| = √σ θ`) and the
  comparison `OptimalSparseSimulation.signed_bound` at `(σ, θ)` give at most
  `48·10¹⁰ · 4 (√(σθ r_μ) + r_μ)` calls.
* *The clipped-transducer regime* (the paragraph "Large `h` with `τ_ent ≥ Lh`"). For `h_μ ≥ 10⁴` and
  `σθ ≥ L h_μ`, the joint representation clipped at `μ`
  (`LargeSparsityCore.Native.compression_of_entry`: `J†KJ = H/α`, `α = sμ/q`; the moments with the
  factor `η²/μ²`, `LargeSparsityCore.Native.norm_K_input_sq_le_ratio` and its companions) satisfies
  the hypotheses of the abstract core with the moment parameter `σ`
  (`LargeSparsityCore.Native.coreData_two`), and the core gives at most `6972480 √(σθ r_μ)` native
  calls (`LargeSparsityCore.Native.core_simulation_two`).

*Combination* (module `TwoNorm`). The signed-factor theorem is already in the common form. The
bounded and the clipped constructions act on their own workspaces and are moved to the common form
by fixed changes of coordinates (`OptimalSparseSimulation.simulates_of_spectatorForm`,
`OptimalSparseSimulation.cayleyActive_form`): the bounded one inside `bounded_simulation`, after
the alignment of input and output with one Boolean spectator, the clipped one in
`two_norm_simulation`.

## Scope and differences from the manuscript

* Only query complexity is claimed here; the gate-level implementation (Theorem `gate:thm:main`) is
  the library `GateOptimalPrecision`. The constant `2·10¹²` is explicit, and
  the threshold on `h_μ` is the `10⁴` of the large-sparsity core.
* In the bounded regime the rescaling `γ` is the public optimum of the baseline for the
  parameters `(σ, θ)` rather than the explicit `γ = min{1, max{σ^{-1/2}, √(θ/L)}}`, and the
  precision term is `ℓ = log(2/ε)`; both give the bound `O(√s η|t| + √(sμ|t| L) + L)`.
* The clipped regime uses the parameter choices, the exact known gates and the error split of the
  large-sparsity core (`LargeSparsityCore/Statements.lean`) with `(σ, θ)` in place of `(s, τ)`, in
  place of the manuscript's `Q₀ = ⌈max{1, 2q/h}⌉`, `B₀ = 32Q₀` and the gate-approximation budget.
* The row and value index types `n` and `Z` are taken in `Type` (for the common form).
* `μ > 0` is not a hypothesis: it follows from `θ ≥ 1`. The cases `t = 0` and a known zero
  Hamiltonian (no queries) are not part of the statement.
-/
