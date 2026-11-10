# Extent of the Lean formalisation

Detailed result coverage, model assumptions and validation information for
`sparse-quantum-lean` version `0.1.0-rc30`.
See the [project README](../README.md) for installation, build commands,
authorship and citation information. Source paths in prose and code spans are
relative to the repository root; the links below resolve from this document.

## Contents

- [Results and scope](#results-and-scope)
  - [Theorem correspondence](#theorem-correspondence)
  - [Hamiltonian and unitary endpoints](#hamiltonian-and-unitary-endpoints)
  - [Solver and gate endpoints](#solver-and-gate-endpoints)
  - [Lower bounds and Dyson constructions](#lower-bounds-and-dyson-constructions)
  - [Linear-system filters and time-dependent extensions](#linear-system-filters-and-time-dependent-extensions)
  - [Separate matrix and preparation query bounds](#separate-matrix-and-preparation-query-bounds)
  - [Native gates, arithmetic and synthesis](#native-gates-arithmetic-and-synthesis)
  - [Explicit schedules and improved-precision bounds](#explicit-schedules-and-improved-precision-bounds)
  - [Statement guides](#statement-guides)
  - [Scope qualifications and library relationships](#scope-qualifications-and-library-relationships)
- [Validation and audits](#validation-and-audits)
- [Model and trusted base](#model-and-trusted-base)

## Results and scope

**Manuscript conformance.** The library
[`ManuscriptConformance`](../ManuscriptConformance/Statements.lean) restates the headline results of
the manuscript with the assumptions the manuscript permits, except where the summary table records
another hypothesis, and proves each
from the endpoints listed below: one or a few theorems per result, with a summary table of their
status. Extra hypotheses of the package are named predicates `formal_…` (the binary data format
of the gate endpoints, the classical propagator of the time-dependent generator pieces, the
uniform-mesh model of the time-dependent gate-level ODE solver (not needed in its form with the
manuscript's certificates), and the nondegeneracy conditions `ḡ ≥ 1`, `B > 0`); the manuscript's
external results and computational assumptions are named `ext_…` and `comp_…`.
Where a restatement uses a hypothesis not named `formal_…`, `ext_…` or `comp_…`, or proves less
than the manuscript states, `ManuscriptConformance/Statements.lean` records it in the summary
table.

### Theorem correspondence

| Paper result | Lean declaration | Source |
|---|---|---|
| Time-independent Hamiltonian simulation, Theorem 2.1 (`hs:thm:main`) | `SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one` | [Hamiltonian endpoint](../SparseHamiltonian/ManuscriptPrecision.lean) |
| Controlled reversible access, Lemma 3.1 (`access:lem:control`): from a supplied unitary `F` with inverse access and a known basis input `x₀` with `F\|x₀⟩ = \|y₀⟩` (phase one, `y₀` unknown), a controlled `F` and a controlled `F†` from three calls of `F` or `F†` on the clean subspace; a controlled value lookup from two value calls; audited directly in `SparseHamiltonian/Audit.lean` | `SparseHamiltonian.NativeControlledOracle.three_query_control`, `SparseHamiltonian.NativeControlledOracle.three_query_inverse_control`, `SparseHamiltonian.ControlledLookup.controlled_two_queries` | [Controlled native calls](../SparseHamiltonian/NativeControlledOracle.lean) |
| Finite clock weights for optimal-precision simulation, Theorem A.2 (`opt:thm:weights`): for real `q ≥ 1` and integer `M ≥ 1`, explicit real weights `λ_1, …, λ_n` with `n ≤ 27qM`, `∑ \|λ_j\| ≤ 3000` and exact moments `∑_j λ_j Ces_j(e^{-qMξ} R^k ξ^m) = δ_{m0}` for `0 ≤ m ≤ k < M` | `OptimalPrecision.exists_clock_weights`, `OptimalPrecision.clockWeight`, `OptimalPrecision.clockLength_le`, `OptimalPrecision.sum_abs_clockWeight_le`, `OptimalPrecision.clock_moments` | [Clock weights](../OptimalPrecision/Weights/Theorem.lean) |
| Operator tail estimate, Lemma A.3 (`opt:lem:tail`): for any weights with these three properties and bounded operators `0 ⪯ D ⪯ δI`, `-D ⪯ C ⪯ D` on a complex Hilbert space, `δ ≥ 0`, `‖∑_j λ_j Ces_j(F) - e^{-iq²MC}‖ ≤ 2·3001·(e²·27²b/M)^M` for `M ≥ 2·27²b`, `b = q²Mδ`, with the transfer `F = e^{-qMΩ}` of `opt:eq:continuum` | `OptimalPrecision.Tail.tail_estimate`, `OptimalPrecision.Tail.Fop`, `OptimalPrecision.Tail.Omega` | [Tail estimate](../OptimalPrecision/Tail/Lemma.lean) |
| Simulation with indefinite factors, Theorem A.1 (`opt:thm:signed`): for `H = λB†ZB`, `B = ΠU_BE`, `D = B†B ⪯ δI`, `λ > 0`, `0 < δ ≤ 1`, every `t` and `0 < ε ≤ 1/64`, with `T = λ\|t\|`, `b = Tδ` and `r_b = log(1/ε)/log(e + log(1/ε)/b)`, a known isometric input and a program whose only oracle is the factor query `I ⊗ U_B` (with its adjoint), with `0` queries if `b ≤ ε` and at most `4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` otherwise, and full-output error at most `ε` | `SignedFactorSimulation.signed_factor_simulation`, `SignedFactorSimulation.signed_factor_simulation_uniform`, `SignedFactorSimulation.Known`, `SignedFactorSimulation.rb` | [Signed-factor theorem](../SignedFactorSimulation/Theorem.lean) |
| Native sparse factor and simulation with it (`opt:sec:native`, `opt:eq:native-factor`, `opt:eq:whole-factor`): a factor unitary from the native row locator, column locator and value oracle with `12` native calls and a known factor structure, with `B†ZB = H/(sη)` and `B†B = D_H/(sη) ⪯ s^{-1/2}I`; for Hermitian `H` with row and column Euclidean norms at most `η`, every `t` and `0 < ε ≤ 1/64`, with `τ = η\|t\|`, `T = sτ`, `b = √s τ`, a known isometric input and a program over the native oracles with spectator registers (with adjoints), with `0` queries if `b ≤ ε` and at most `48·10¹⁰ (√(Tb) + √(T r_b) + r_b)` otherwise, and full-output error at most `ε` | `NativeSignedFactor.native_signed_simulation_eta`, `NativeSignedFactor.native_signed_simulation`, `NativeSignedFactor.phys_ham`, `NativeSignedFactor.phys_Dop_eq`, `NativeSignedFactor.phys_Dop_le_eta`, `NativeSignedFactor.Simulates` | [Native-factor simulation](../NativeSignedFactor/Simulation.lean) |
| Large-sparsity core, Proposition A.5 (`opt:prop:core`, `opt:sec:core`, `opt:eq:core-degree`): for Hermitian `H` with row and column Euclidean norms at most `η` and `τ = η\|t\|` with `τ ≥ 1`, `0 < ε ≤ 1/64`, `h = log(e + L/τ) ≥ 10⁴` and `sτ ≥ Lh` (`L = log(1/ε)`, `r = L/h`), a known isometric input and a program over the native oracles with spectator registers (with adjoints), with at most `6972480 √(sτr)` native queries and full-output error at most `ε` for `e^{-itH}` | `LargeSparsityCore.Native.core_simulation`, `LargeSparsityCore.Native.core_native`, `LargeSparsityCore.Core.core_query`, `LargeSparsityCore.Native.compression`, `LargeSparsityCore.Parameters.Regime.degree_le_sqrt` | [Large-sparsity core](../LargeSparsityCore/NativeCore.lean) |
| Optimal time-independent sparse simulation, Theorem 4.3 (`hs:thm:optimal`), upper bound (`hs:eq:optimal-bound`, `opt:eq:regime-comparison`): for Hermitian `H` with row and column Euclidean norms at most `η`, every `t` with `τ = η\|t\| ≥ 1` and `0 < ε ≤ 1/64`, with `L = log(1/ε)`, `h = log(e + L/τ)` and `r = L/h`, a known isometric input and a program over the native oracles with spectator registers (with adjoints), with at most `2·10¹² (√s τ + √(sτr) + r)` native queries and full-output error at most `ε` for `e^{-itH}`, also on inputs entangled with an untouched reference | `OptimalSparseSimulation.optimal_simulation`, `OptimalSparseSimulation.optimal_simulation_with_reference` | [Optimal simulation](../OptimalSparseSimulation/Optimal.lean) |
| Refined precision for unitary implementation, Corollary 4.7 (`hs:cor:unitary-optimal`), upper bound: exact entries, or entries within `ε/(πN)` of the intended unitary, `0 < ε ≤ 1/2`, at most `5·10¹³ (√(N ρ_ε) + ρ_ε)` entry-oracle queries (inverse calls counted, no location oracle), `ρ_ε = ℓ/log(e + ℓ)`, `ℓ = log(1/ε)`, full-output error at most `ε`, also with an untouched reference | `OptimalSparseSimulation.unitary_optimal`, `OptimalSparseSimulation.unitary_optimal_inexact`, `OptimalSparseSimulation.unitary_optimal_with_reference`, `OptimalSparseSimulation.unitary_optimal_inexact_with_reference` | [Refined unitary implementation](../OptimalSparseSimulation/Unitary.lean) |
| Two-norm time-independent sparse simulation, Theorem 4.4 (`hs:thm:two-norm`, `hs:eq:two-norm-bound`, Appendix B): for Hermitian `H` with row and column Euclidean norms at most `η`, entries of modulus at most `μ`, `μ ≤ η ≤ √s μ`, every `t` with `θ = η²\|t\|/μ ≥ 1` and `0 < ε ≤ 1/64`, with `L = log(1/ε)` and `r_μ = L/log(e + L/θ)`, a known isometric input and a program over the native oracles with spectator registers (with adjoints), with at most `2·10¹² (√s η\|t\| + √(sμ\|t\| r_μ) + r_μ)` native queries and full-output error at most `ε` for `e^{-itH}`, also with an untouched reference | `TwoNormSimulation.two_norm_simulation`, `TwoNormSimulation.two_norm_simulation_with_reference`, `TwoNormSimulation.bounded_simulation`, `LargeSparsityCore.Native.core_simulation_two` | [Two-norm simulation](../TwoNormSimulation/TwoNorm.lean) |
| Worst-case query complexity of time-independent sparse simulation, the `Θ` statement of Theorem 4.3 (`hs:thm:optimal`, `hs:eq:optimal-theta`): for `τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`, on the hard families of `hsl:thm:main` (row and column norms exactly one) and in the common query form of the upper bound, `c₀ S ≤` the largest of the three families' query complexities `≤ 2·10¹² S`, `S = √s τ + √(sτr) + r`, `c₀ = log 2/(4096π)`; `Ω(√(sτL))` cannot hold uniformly | `OptimalLowerBounds.optimal_theta`, `OptimalLowerBounds.main_max_simulates`, `OptimalLowerBounds.optimal_on_hard`, `OptimalLowerBounds.not_uniform_sqrt` | [Optimal `Θ` bracket](../OptimalLowerBounds/Optimal.lean) |
| Lower bound with a maximum-entry promise, Proposition 5.7 (`hsl:prop:two-norm`, `twonorml:eq:lower`): the hard families of `hsl:thm:main` enlarged to `μ H⁰ ⊗ 𝟙𝟙ᵀ` (real symmetric, exact words, maximum sparsity exactly `s = m s₀`, maximum entry magnitude exactly `μ`, row and column Euclidean norms exactly `η = μ√m`, public locators; operator norm at least `μ m`), every `t` with `θ = η²\|t\|/μ ≥ 1`; for algorithms over the native primitives (with or without spectator registers) accurate in trace distance on `e^{-itH}(ψ_in ⊗ u_m)`, and for common-form simulations, `max(Q_T, Q_M, Q_P) ≥ c₀ (√s η\|t\| + √(sμ\|t\| r_μ) + r_μ)`; with Theorem `hs:thm:two-norm`, `Θ` on these aligned families | `OptimalLowerBounds.two_norm_main_max`, `OptimalLowerBounds.two_norm_main_max_native`, `OptimalLowerBounds.two_norm_main_max_simulates`, `OptimalLowerBounds.two_instances`, `OptimalLowerBounds.two_norm_theta`, `OptimalLowerBounds.two_opNorm` | [Two-norm lower bound](../OptimalLowerBounds/TwoNorm.lean) |
| The logarithmic denominator must also change (`twonorml:eq:counterexample-parameters`, `twonorml:eq:wrong-denominator`, `twonorml:eq:necessary-denominator`): at `m = 4^k`, `s = 2m`, `η = t = 1`, `μ = m^{-1/2}`, `L = √m log m`, the bound with the old precision parameter `r̃ = L/log(e + L/(η\|t\|))` is at most `6√m` while for `k ≥ 47` every accurate algorithm needs at least `r_μ/32` queries, `r_μ = √m log m/log(e + log m)`; for every `C`, more than `C` times the old bound for all `k ≥ max(47, ⌈(384 C)² + 3⌉)`; the corrected bound of `hs:thm:two-norm` holds | `OptimalLowerBounds.wrong_denominator`, `OptimalLowerBounds.wrong_denominator_simulates`, `OptimalLowerBounds.wrongShape_le`, `OptimalLowerBounds.wrong_r_bounds`, `OptimalLowerBounds.denom_lower`, `OptimalLowerBounds.denom_simulates` | [Denominator obstruction](../OptimalLowerBounds/Denominator.lean) |
| The lower bounds of `OptimalLowerBounds` for adaptive protocols and for algorithms with measurements inside a run (input-independent instruments with classical continuations on one persistent workspace), with controlled and inverse oracle calls (every native call admissible for the data, in particular the plain, inverse, controlled and controlled-inverse forms of the native primitives and, for public locators, the common oracle of the upper bounds): success probability at least `2/3`, conditional output `ε`-accurate in trace distance (mixed outputs), worst-case weighted number of calls over all transcripts; Proposition `hsl:prop:two-norm` with the same constant `c₀`, the lower half of `hs:thm:optimal` in its common query model and the denominator obstruction; the released common-form simulations are measured algorithms with success probability one and at most `2·10¹² S` value calls (`2·10¹² S'` on the aligned two-norm families), so over the common oracle the lower bound `c₀ S` (resp. `c₀ S'`) on the worst-case number of value calls is attained up to the constant | `OptimalLowerBounds.two_norm_main_max_measured`, `OptimalLowerBounds.two_norm_main_max_tree`, `OptimalLowerBounds.two_norm_main_max_measured_calls`, `OptimalLowerBounds.two_norm_main_max_measured_common`, `OptimalLowerBounds.main_max_measured_common`, `OptimalLowerBounds.wrong_denominator_measured`, `OptimalLowerBounds.optimal_measured_theta`, `OptimalLowerBounds.two_norm_measured_theta`, `OptimalLowerBounds.admissible_callFamily`, `OptimalLowerBounds.admissible_common` | [Measured lower bounds](../OptimalLowerBounds/Measured.lean) |
| Gate-efficient improved-precision simulation, Theorem 4.5 (`gate:thm:main`) and its single-norm case (exact gates): for `0 < μ ≤ η ≤ √s μ`, `θ = η²\|t\|/μ ≥ 1`, `0 < ε ≤ 1/64` and self-adjoint `H`, with the private operation of each regime given on a gate register (`BoundedIface`, `SignedIface`, `ClippedIface`, each required only in its regime), a valid unitary circuit with at most `2·10¹¹ Q_μ` private and `2·10¹¹ Q_μ` boundary calls, at most `10¹³ (Q_μ + 1)(a + m + r + 1)` elementary gates on at most `2a + 3m + 6r + 5` auxiliary qubits, `2^m ≤ 10³⁶ (Q_μ + 1)⁴/ε`, `2^r ≤ 10⁸ (Q_μ + 1)` and full-output error at most `ε` for `e^{-itH}`, `Q_μ = √s η\|t\| + √(sμ\|t\| r_μ) + r_μ`; the single-norm case at `μ = η` | `GateOptimalPrecision.gate_optimal_simulation`, `GateOptimalPrecision.gate_optimal_simulation_single`, `GateOptimalPrecision.GateClaims` | [Gate-level optimal precision](../GateOptimalPrecision/Main.lean) |
| The same with native private calls: every sector-controlled private call replaced by the compute–rotate–uncompute macro of the baseline gate theorem, every factor call by the native factor of Section D.4 (`gate:sec:native`: compute, arithmetic, the local gates of `U(c)`, inverse arithmetic, uncompute) and every boundary call by its gates under the sector wire; with the native identities and the arithmetic accuracy `ζ` as hypotheses (angle accuracy for the edge rotation; the threshold or magnitude accuracy `ζ²` and phase accuracy `ζ` for the factor), at most `2·10¹¹ Q_μ` times the primitive calls of one native private call, at most `10¹³ (Q_μ + 1)(a + m + r + 1) + 2·10¹¹ Q_μ G` elementary gates (`G` the gates of one native boundary and private call) and full-output error at most `ε + 2·10¹¹ Q_μ ζ'` (`ζ' = 4ζ` or `3ζ`; the telescoping of Proposition D.3, `gate:prop:finite`, without finite-set synthesis), at most `ε` for the construction at `ε/2` with `32·10¹¹ Q_μ ζ ≤ ε` | `GateOptimalPrecision.gate_optimal_native`, `GateOptimalPrecision.gate_optimal_native_total`, `GateOptimalPrecision.gate_optimal_native_single`, `GateOptimalPrecision.NativeClaims`, `GateOptimalPrecision.native_transfer`, `GateOptimalPrecision.signed_transfer` | [Native optimal precision](../GateOptimalPrecision/NativeMain.lean) |
| The same from binary sparse oracles (`k`-bit indices, `s = 2^{s_b}` slots, two's complement entries with decoder `c₀(X + iY)`; Hermitian `H` with row and column Euclidean norms at most `η` and entries of modulus at most `μ`): the interfaces `BoundedIface`, `SignedIface`, `ClippedIface` and the native identities `NativeOK`, `FactorNativeOK` of the three regimes constructed from the oracles (the clipped private Cayley unitary as `D = U_f† C U_f`, a native factor and a native rotation, `6ξ + 4ζ` per call); per private call `10`, `10` or `30` row, column and value calls and an explicit gate cost, the scratch of `6k + 2b` qubits and the arithmetic wires; with the CORDIC angle arithmetic of the bounded regime proved (explicit cost bound) and the scalar arithmetic of the signed and clipped regimes as hypotheses required only in their own regimes, met at every accuracy by reversible lookup tables (gate counts exponential in `b`; with these tables no arithmetic hypothesis remains), full-output error `ε + 2·10¹¹ Q_μ ζ'` (`ζ' = 4ζ`, `3ξ` or `6ξ + 4ζ`), at most `ε` at `ε/2` with `8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε`; over a finite gate set with single-qubit synthesis and the decomposition of controlled gates as hypotheses (synthesis budget `ε'`): gates of the set only, the same primitive calls, at most `N L(ε'/(N+1))` gates, and with a logarithmic synthesis length at most `G_N (c₁ log((G_N + 1)/ε') + c₀)` for the native gate bound `G_N`, and error `ε + ε'` | `GateOptimalBinary.gate_optimal_binary`, `GateOptimalBinary.gate_optimal_binary_total`, `GateOptimalBinary.gate_optimal_binary_synth`, `GateOptimalBinary.gate_optimal_binary_tables`, `GateOptimalBinary.factorWordArith_exists`, `GateOptimalBinary.clipArith_exists`, `GateOptimalBinary.SynthClaims.gates_log`, `GateOptimalBinary.bdNativeCost_le`, `GateOptimalBinary.boundedIface`, `GateOptimalBinary.signedIface`, `GateOptimalBinary.clippedIface`, `GateOptimalBinary.boundedNative`, `GateOptimalBinary.signedNative`, `GateOptimalBinary.clipNative`, `GateOptimalBinary.gate_optimal_native_clip` | [Binary optimal precision](../GateOptimalBinary/Main.lean) |
| The same for sparse access of general size (`gate:thm:main` and `hs:thm:gates` with the sparse access of Section `hs:sec:control`): an `N × N` matrix with `s`-sparse lists, `1 ≤ s ≤ N`, on index registers of `k = ⌈log₂ N⌉` qubits, locators unitary on their full registers and prescribed on the valid list inputs only, the value oracle XOR-writing a stored word on every pair of index words; the padded data (`k + 1`-bit index words with a marker, `2^⌈log₂ s⌉` slots on the low words) in the binary format for the decoder `c₀(X + iY)`, the padded oracles implemented from the supplied ones on shared clean ancillas (the validity tests by comparisons on clean borrow wires, the supplied locators controlled on a clear marker with a reference by `access:lem:control`, three calls each, the value oracle with a validity flag, two calls; at most `30(k + 1) + 4b` gates each), every call of a circuit of the padded data replaced by its implementation (exact on clean ancillas) and the implementation gates synthesised over the gate set; full-output error against the evolution of the matrix extended by zero to the index words `≥ N`, counts in `N` and `s` (at most `288·10¹² Q_μ` and `6635520 q` primitive queries), decoder `c₀(X + iY)` | `ManuscriptConformance.gate_thm_main_general`, `ManuscriptConformance.hs_thm_gates_general`, `SparseHamiltonian.GeneralSparseAccess.implOK`, `SparseHamiltonian.GeneralSparseAccess.kindOK_implP`, `SparseHamiltonian.GeneralSparseAccess.nGatesN_implP_le`, `SparseHamiltonian.GeneralSparseAccess.nrun_subst_cleanEmb`, `SparseHamiltonian.GeneralSparseAccess.keepC_error`, `SparseHamiltonian.GeneralSparseAccess.QData.padData_matrix`, `ManuscriptConformance.genCirc_error` | [Sparse access of general size](../GeneralSparseAccess/Statements.lean) |
| The same for general decoders (`gate:thm:main` and `hs:thm:gates` for any efficiently decoded encoding, review item B2): sparse access of general size as above with any public decoder `val` of the stored words in place of `c₀(X + iY)`; the native operations of `hs:thm:gates` and of the three regimes of `gate:thm:main` decoding with the decoder of the data (which may depend on the edge), with their native identities and the binary endpoints for any decoder; the padded data with a validity decoder (the supplied word of the low index words on every pair, decoded as `val w` on a pair of valid index words and as `0` otherwise) with its primitives implemented from the supplied ones (the padded locators, one supplied value call); the arithmetic of the padded data from word arithmetic of `val` on the value word: the validity of the pair computed on the index wires, the angle and phase words copied under it (so on an invalid pair the local operations are those of the zero entry: the rotations, the factors and the clipped phase independently of the returned word; with the branch bit set the clipped angle word is that of the arithmetic, within the accuracy `ξ` of the zero-entry angle `2 arctan(2q [f])`) and uncomputed, at most `3c + 10k + 23` gates and work wires for a word arithmetic of cost `c`; with the computational assumptions on the arithmetic of `val` (`comp_rotArith`, `comp_signedArithV`, `comp_clipArithV`: gates and work at most `c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at accuracy `ξ`, the angles at the rescalings `κ ∈ [1/η, √(2s)/η]` of the construction) and no assumption on the encoding: the counts and errors of the general-size theorems (at most `288·10¹² Q_μ` and `6635520 q` primitive queries); for the decoder `c₀(X + iY)` the hypotheses of the general-size theorems imply these assumptions (the CORDIC arithmetic on the value word for the angles), so the decoder theorems extend them with other constants; the form and accuracy of these assumptions met for every decoder by reversible lookup tables (`c_A = 2^{2b+8}(b + 1)`, `d_A = 1`), so for stored words of bounded width with no arithmetic hypothesis (gate constants exponential in the width) | `ManuscriptConformance.gate_thm_main_decoder`, `ManuscriptConformance.hs_thm_gates_decoder`, `ManuscriptConformance.gate_main_dataDec`, `ManuscriptConformance.hs_gates_dataDec`, `ManuscriptConformance.gate_thm_main_decoder_tables`, `ManuscriptConformance.hs_thm_gates_decoder_tables`, `ManuscriptConformance.comp_clipArithV_tables`, `ManuscriptConformance.comp_rotArith_binary`, `ManuscriptConformance.gate_thm_main_general_of_decoder`, `SparseHamiltonian.GeneralDecoder.sparse_nativeOKD`, `SparseHamiltonian.GeneralDecoder.sgFOD_native`, `SparseHamiltonian.GeneralDecoder.clFOD_native`, `SparseHamiltonian.GeneralDecoder.clNDD_native`, `SparseHamiltonian.GeneralDecoder.gate_optimal_binaryD_synth`, `SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_ok`, `SparseHamiltonian.GeneralDecoder.flagLiftG_factorOK`, `SparseHamiltonian.GeneralDecoder.flagLiftG_rotOK`, `SparseHamiltonian.GeneralDecoder.clipWordArith_exists`, `SparseHamiltonian.GeneralSparseAccess.QData.padDataE_matrix`, `SparseHamiltonian.GeneralSparseAccess.implOKE` | [General decoders](../GeneralDecoder/Statements.lean) |
| Value access by a reversible writer specified on clean targets (Section `hs:sec:control`, eq. `access:eq:value`, handover item B4): a supplied unitary writer with `W \|a, 0⟩ = c_a \|a, w_a⟩` (any phases, arbitrary elsewhere) implements the additive lookup with two writer calls on one clean scratch register (writer, adder, inverse writer; the phases cancel), and Theorems `hs:thm:main`, `hs:thm:optimal`, `hs:thm:two-norm`, `qls:thm:main` and `ode:thm:main` hold for it, on the released workspace with one more value-word register: the released circuits and protocols with every value call so replaced are fixed before the instance, make the same locator and source calls and two writer calls per value call, and have the same full-output errors (also with an untouched reference), success probabilities and conditional outputs; Theorem `ode:thm:time` likewise for time-indexed data with a writer for every sample, the time address an input register of the locators and the writer (the coherent sampled-time query reads a different instance in each branch, converted through the blockwise homomorphism `ampHom`); Theorem `ode:thm:general` likewise, the converted call on each of the `K` copies of the Taylor history a primitive call under a fixed homomorphism determined by the copy; Corollary `qls:cor:separate` likewise, conditional on `ext_separateSolver` (constants `2 C_A` and `C_b`, both bounds on every completed history); the per-run accuracy of every actual successful trial and history (`TrialsClose`, `HistoriesClose`) carries over (`ode_thm_time_actual_writer`), and approximate source preparations on clean work registers are covered (`ode_thm_time_approx_writer`); Theorems `hs:thm:gates` and `gate:thm:main` for sparse access of general size (binary decoder or any public decoder, and their `tiny`, `tables` and `of_decoder` variants) hold, with the hypotheses, constants and bounds of the released theorems, for a writer on the edge register and the value wires specified only on the clean inputs of valid index pairs, `W \|i, j, 0⟩ = c_ij \|i, j, w_ij⟩` for `i, j < N` (any phases, any unitary action elsewhere): the writer and its inverse take the places of the two XOR calls of the padded value oracle, whose copy of the scratch word is masked by the validity flag, so on an invalid pair the inverse call undoes the writer and no routing to a valid address is needed; likewise the general-size forms of Theorem `ode:thm:gates` with the decoder `c₀(X + iY)` and with binary entry decoding (constant and time-dependent coefficients, the certificate, branch-certificate and source-execution forms), the private operation of the padded solvers calling the locators and the writer through the same implementation (with binary entry decoding, the inverse writer in the place of the second supplied value call of every decoded value call: a decoded call through the writer is an involution, so on an invalid pair the second decoded call around the masked copy undoes the first), with the constants, bounds and guarantees of the released forms; Theorem `ode:thm:general` at `T = 0` likewise with a writer on clean targets; not for the other ODE and linear-system endpoints | `ManuscriptConformance.hs_thm_main_writer`, `ManuscriptConformance.hs_thm_optimal_writer`, `ManuscriptConformance.hs_thm_two_norm_writer`, `ManuscriptConformance.qls_thm_main_writer`, `ManuscriptConformance.qls_cor_separate_writer`, `ManuscriptConformance.ode_thm_main_writer`, `ManuscriptConformance.ode_thm_time_writer`, `ManuscriptConformance.ode_thm_general_writer`, `ManuscriptConformance.ode_thm_time_actual_writer`, `ManuscriptConformance.ode_thm_time_approx_writer`, `SparseHamiltonian.WriterAccess.Impl.fhom`, `SparseHamiltonian.WriterAccess.FImplH.label`, `SparseHamiltonian.WriterAccess.ampHom_diagonal`, `SparseHamiltonian.WriterAccess.circuits_intertwines`, `SparseHamiltonian.WriterAccess.transfer`, `SparseHamiltonian.WriterAccess.encodeTree_conditionalDensity`, `ManuscriptConformance.hs_thm_gates_general_writer`, `ManuscriptConformance.gate_thm_main_general_writer`, `ManuscriptConformance.hs_thm_gates_decoder_writer`, `ManuscriptConformance.gate_thm_main_decoder_writer`, `SparseHamiltonian.GeneralSparseAccess.QData.Writer`, `SparseHamiltonian.GeneralSparseAccess.implOKW`, `SparseHamiltonian.GeneralSparseAccess.wmid_invalid`, `ManuscriptConformance.ode_thm_gates_general_writer`, `ManuscriptConformance.ode_thm_gates_time_general_writer`, `ManuscriptConformance.ode_thm_gates_time_cert_writer`, `ManuscriptConformance.ode_thm_gates_time_cert_valid_writer`, `ManuscriptConformance.ode_thm_gates_general_sources_writer`, `ManuscriptConformance.ode_thm_gates_time_general_sources_writer`, `ManuscriptConformance.ode_thm_general_zero_writer`, `SparseHamiltonian.GeneralDecoderODE.decW_invol`, `SparseHamiltonian.GeneralDecoderODE.cmid_invalid`, `SparseHamiltonian.GeneralDecoderODE.implOK_implDPW`, `ManuscriptConformance.ode_thm_gates_decoder_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_writer`, `ManuscriptConformance.ode_thm_gates_decoder_sources_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_sources_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_sources_writer`, `ManuscriptConformance.ode_thm_gates_time_cert_sources_writer`, `ManuscriptConformance.ode_thm_gates_time_cert_branch_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_branch_writer`, `ManuscriptConformance.ode_thm_gates_time_cert_valid_branch_writer`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_branch_writer`, `ManuscriptConformance.hs_thm_gates_decoder_tiny_writer`, `ManuscriptConformance.gate_thm_main_decoder_tiny_writer`, `ManuscriptConformance.hs_thm_gates_decoder_tables_writer`, `ManuscriptConformance.gate_thm_main_decoder_tables_writer`, `ManuscriptConformance.hs_thm_gates_general_of_decoder_writer`, `ManuscriptConformance.gate_thm_main_general_of_decoder_writer` | [Writer access](../ManuscriptConformance/WriterAccess.lean), [layers and protocols](../ManuscriptConformance/WriterProtocols.lean), [Hamiltonian endpoints](../ManuscriptConformance/WriterEndpoints.lean), [protocol endpoints](../ManuscriptConformance/WriterProtocolEndpoints.lean), [separate-query endpoint](../ManuscriptConformance/WriterSeparate.lean), [time-dependent endpoint](../ManuscriptConformance/WriterTimeEndpoints.lean), [general endpoint](../ManuscriptConformance/WriterGeneralEndpoint.lean), [per-run forms](../ManuscriptConformance/WriterTimeVariants.lean), [gate-level access](../ManuscriptConformance/WriterGateAccess.lean), [gate theorems](../ManuscriptConformance/WriterGates.lean), [gate theorems with a decoder](../ManuscriptConformance/WriterGatesDecoder.lean), [ODE gate theorems](../ManuscriptConformance/WriterODEGates.lean), [time-dependent ODE gate theorems](../ManuscriptConformance/WriterODETimeGates.lean), [certificate forms](../ManuscriptConformance/WriterODECert.lean), [source executions](../ManuscriptConformance/WriterODESources.lean), [zero-time general endpoint](../ManuscriptConformance/WriterGeneralZero.lean), [decoded access](../ManuscriptConformance/WriterDecoderAccess.lean), [decoder ODE gate theorems](../ManuscriptConformance/WriterDecoderODE.lean), [decoder certificate forms](../ManuscriptConformance/WriterDecoderCert.lean), [decoder source executions](../ManuscriptConformance/WriterDecoderSources.lean), [branch-certificate forms](../ManuscriptConformance/WriterBranchCerts.lean), [gate-theorem variants](../ManuscriptConformance/WriterGateVariants.lean) |
| Tiny decoded entries without their phase (`gate:thm:main` and `hs:thm:gates` for general decoders, follow-up 4a): the arithmetic assumptions are asked for the thresholded decoder `dropVal small val` (`0` on the words selected by a public test that only selects entries of modulus at most `τ` and does not separate an entry from its conjugate, decided reversibly on the stored word), so no phase word is asked for a selected word, however small and whatever its phase; the same circuit on the original data has full-output error at most `ε + \|t\| s τ` against the evolution of the original matrix (the thresholded padded matrix is within `s τ` in operator norm, on the original locator lists); with an empty test the old assumption is recovered. The threshold is global, not the local per-rotation tolerance of the manuscript's argument | `ManuscriptConformance.hs_thm_gates_decoder_tiny`, `ManuscriptConformance.gate_thm_main_decoder_tiny`, `ManuscriptConformance.fullOutputError_dropTiny`, `SparseHamiltonian.GeneralSparseAccess.QData.dropTiny`, `SparseHamiltonian.GeneralSparseAccess.QData.padMat_dropTiny_sub`, `ManuscriptConformance.dropVal_phi_vacuous` | [Tiny entries](../ManuscriptConformance/GateDecoderTiny.lean) |
| The same for the gate-level dissipative solvers (`ode:thm:gates`, constant and time-dependent coefficients, every `T ≥ 0`, review item B): the released solvers on the padded data of sparse access of general size as above (time-indexed for time-dependent coefficients, the oracles of the samples selected coherently by the slot wires), with every padded call of the private operation replaced by its implementation from the supplied oracles (at most three supplied calls of the same kind and `30 (k+1) + 4 b` gates per padded call, on clean ancillas added to the private scratch), the source circuits of the `k`-qubit index register on the low wires of the padded system register, and the instance conditions and the outcome transferred along the marker embedding of the index register; the counts of the binary theorems in `N` and `s` (the padded word budget within `+3`, resp. `+5`, of `𝔟`, the padded query shape at most `2`, resp. `6`, times `q`; at most three times the released supplied calls), the output the normalised solution on the index register with the marker qubit clean, for the matrix extended by zero to the index words `≥ N` (for sources on `ℂ^N` the embedding of the solution on `ℂ^N`, a source component on an invalid index word evolving freely; the time-dependent conditions for the public parameters of the padded problem); decoder `c₀(X + iY)` | `ManuscriptConformance.ode_thm_gates_general`, `ManuscriptConformance.ode_thm_gates_time_general`, `SparseHamiltonian.GeneralSparseODE.general_ode_outcome`, `SparseHamiltonian.GeneralSparseODE.general_ode_budget`, `SparseHamiltonian.GeneralSparseODE.general_time_outcome`, `SparseHamiltonian.GeneralSparseODE.general_time_budget`, `SparseHamiltonian.GeneralSparseODE.nativeOK_substOp`, `SparseHamiltonian.GeneralSparseODE.nativeOK_substSlot`, `SparseHamiltonian.GeneralSparseODE.RobustRestG.padded`, `SparseHamiltonian.GeneralSparseODE.padLift_eq`, `SparseHamiltonian.GeneralSparseODE.solution_padLift_validEmb`, `SparseHamiltonian.GeneralSparseODE.solves_validLift` | [General-size ODE gate solvers](../GeneralSparseODE/Statements.lean) |
| The same for every decoder of the stored words with an exact binary entry decoding, so with values on the grid `c₀ (ℤ + iℤ)` (`ode:thm:gates`, constant and time-dependent coefficients, every `T ≥ 0`, review item B2): the solvers above on the decoded data (the matrix and the locators of the access, the stored words replaced by the decoded binary entries read by `c₀(X + iY)`), with every decoded value call implemented by two supplied value calls around the reversible decoding circuit, the copy of the decoded word and the decoding backwards (at most six supplied calls of the same kind and `30 (k+1) + 4 b' + 3 (2 |dc| + 2 b')` gates per padded call, on clean ancillas in the private scratch); the decoding cost `|dc| + 2b + 2b' + A` (gates and wires) in the polynomial of the gate bound and its wires `2b + 2b' + A` in the qubit bound, the decoded components of `b' ≤ b_data` bits; for the decoder `c₀(X + iY)` the copy of the stored word, for every decoder with binary entries a lookup-table decoding | `ManuscriptConformance.ode_thm_gates_decoder`, `ManuscriptConformance.ode_thm_gates_time_decoder`, `ManuscriptConformance.binaryEntryDecoding_copy`, `ManuscriptConformance.exists_binaryEntryDecoding`, `SparseHamiltonian.GeneralDecoderODE.decoder_ode_outcome`, `SparseHamiltonian.GeneralDecoderODE.decoder_ode_budget`, `SparseHamiltonian.GeneralDecoderODE.decoder_time_outcome`, `SparseHamiltonian.GeneralDecoderODE.decoder_time_budget`, `SparseHamiltonian.GeneralDecoderODE.implOK_implDP`, `SparseHamiltonian.GeneralDecoderODE.implDec_ok` | [ODE gate solvers with binary entry decoding](../GeneralDecoderODE/Statements.lean) |
| The same under the manuscript's certificates (`ode:thm:gates`, time-dependent coefficients, every `T ≥ 0`, review item G): the general-size and decoder solvers above for the public data with the amplification bound `2ḡ`, on every instance with a positive source quadrature at the slot times `r T/M` and the certificates of eq. `ode:eq:gate-source-certificates` against the exact propagator (`‖x(T) − U(T,0) x₀ − ∑_r w_r U(T,t_r) b(t_r)‖ ≤ ζ B`, `B_m ≤ 2B`, `B ≤ ḡ ‖x(T)‖`) and a sample certificate for the uniform mesh of the slots (the integrated sample error `ΔG` of the represented samples and its dissipative part `ΔD`: `ζ + 2 (ΔG + 2 ΔD) ≤ ε/(2000 ḡ)`, `6 R ΔD ≤ ν'`), which Lipschitz bounds as in `ode:lem:gate-select` bound (`ΔG ≤ β T²/(2M) + (T/M) ∑_r δ_r`, and `ΔD ≤ β_D T²/(2M) + (T/M) ∑_r δ^D_r` for the Hermitian parts; the lemma's conditions at `δ = ν` give the first budget, and the second at a `δ` finer by a factor below `14`, so `δ = ν/16` gives both; this `δ` and the mesh exponent `m ≥ odeMeshG …` are this package's conditions, where the manuscript chooses `M` from the lemma at `δ = ν`); represented samples of any sign, integrable generator pieces with a classical propagator on each closed mesh interval, mild solutions; on the index register or for a problem on `ℂ^N` (the loading preparing the embedded directions, the output the embedding of the normalised solution); source nodes off the slot times not covered | `ManuscriptConformance.ode_thm_gates_time_cert`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert`, `ManuscriptConformance.ode_thm_gates_time_cert_valid`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid`, `ManuscriptConformance.gate_select_sample_certificate`, `SparseHamiltonian.MeshCertificateODE.general_time_cert_outcome`, `SparseHamiltonian.MeshCertificateODE.decoder_time_cert_outcome`, `SparseHamiltonian.MeshCertificateODE.cert_native_time_outcome`, `SparseHamiltonian.MeshCertificateODE.quad_target_error`, `SparseHamiltonian.MeshCertificateODE.sampleErr_umesh_le_of_lipschitz` | [ODE gate solvers under the manuscript's certificates](../MeshCertificateODE/Statements.lean) |
| Accuracy of every actual successful run (`ode:thm:main`; `ode:thm:time` with exact source preparations, zero time and a known zero generator included): for the trial family of the same protocol, every trial of nonzero amplitude outputs a unit vector within Euclidean distance `ε` of `x(T)/‖x(T)‖` up to a global phase (`TrialsClose`), and the conditional density is the ensemble of the actual trial outputs over the successful histories, each within `ε` (`HistoriesClose`), with the success, trace-distance and count conclusions of the endpoints; the density-only predicate `RunsClose` does not imply it (`diag(0.99, 0.01)`, `runsClose_diagnostic`); for approximate source preparations on clean work registers the history-resolved form: every trial whose success probability is at least `p₀ > η²` (`η = 60 c_q ḡ δ`) within `ε/500 + 2η/√p₀` up to a phase, the other histories of conditional weight at most `6 p₀` (`ode_thm_time_approx_runs`); for exact source preparations also with a loader specified only on its clean columns (`ode_thm_time_actual_columns`, handover item D1) | `ManuscriptConformance.ode_thm_main_actual`, `ManuscriptConformance.ode_thm_time_actual`, `ManuscriptConformance.ode_thm_time_actual_columns`, `ManuscriptConformance.TrialsClose`, `ManuscriptConformance.HistoriesClose`, `ManuscriptConformance.runsClose_diagnostic`, `ManuscriptConformance.ode_thm_time_approx_runs`, `ManuscriptConformance.lowWeight_le` | [Actual runs](../ManuscriptConformance/ActualRuns.lean), [approximate sources](../ManuscriptConformance/ApproxRuns.lean), [clean-column loader](../ManuscriptConformance/TimeLoaderRuns.lean) |
| Certificates on the opposite branches `K_{±k} = H ± kD` of the same represented samples on a common mesh (proof of `odel:lem:dyson`; `ode:thm:time`, `ode:thm:gates`): `ΔH = (ΔK₊ + ΔK₋)/2`, `ΔD = (ΔK₊ − ΔK₋)/(2k)`, `E_D ≤ (E₊ + E₋)/(2k)`, `E_G ≤ (1 + 1/k)(E₊ + E₋)/2` for `k > 0` (no commutation or positivity; nonuniform meshes), composed into the time-dependent endpoints (refinement error kept), the time-dependent gate certificate endpoints (selected `k`, formal solver radius) and the full-class Dyson coverage (`2s E_G ≤ log(1 + δ_m)`); a non-accretive represented sample is accepted; with exact preparations also for a loader specified only on its clean columns (`ode_thm_time_branch_columns`, `ode_thm_time_actual_branch_columns`, handover item D1) | `ManuscriptConformance.ode_thm_time_branch`, `ManuscriptConformance.ode_thm_time_approx_branch`, `ManuscriptConformance.ode_thm_time_actual_branch`, `ManuscriptConformance.ode_thm_gates_time_cert_branch`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_branch`, `ManuscriptConformance.ode_thm_gates_time_cert_valid_branch`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_valid_branch`, `ManuscriptConformance.fullValidAt_of_branch_raw`, `ManuscriptConformance.fullValidAt_of_branch_clipped`, `ManuscriptConformance.nonaccretive_branch_accepted`, `ManuscriptConformance.ode_thm_time_branch_columns`, `ManuscriptConformance.ode_thm_time_actual_branch_columns` | [Branch certificates](../ManuscriptConformance/BranchCertificates.lean), [clean-column loader](../ManuscriptConformance/TimeLoaderBranch.lean) |
| Source executions after native macro expansion (`ode:thm:gates`): an annotated expansion of the labelled released program that evaluates to the actual native preparation and trials; along every history of the protocols, at most `40 ḡ` executions of each source circuit (constant coefficients, binary data and binary entry decoder) or `160 ḡ` loadings and `320 ḡ` weight preparations (time-dependent certificate endpoints), at most `40 ḡ` executions of each circuit for general sizes and at most `80 ḡ` loadings and `160 ḡ` weight preparations for the uniform-mesh, general-size and decoder time-dependent endpoints, the calls as propagation calls (at most `C ḡ q`, none at zero time or for a known zero generator) plus the executions times the calls inside each supplied circuit, and the gates as propagation gates plus the executions times the supplied gates | `ManuscriptConformance.ode_thm_gates_sources`, `ManuscriptConformance.ode_thm_gates_decoder_sources`, `ManuscriptConformance.ode_thm_gates_time_cert_sources`, `ManuscriptConformance.ode_thm_gates_time_decoder_cert_sources`, `ManuscriptConformance.ode_thm_gates_general_sources`, `ManuscriptConformance.ode_thm_gates_time_sources`, `ManuscriptConformance.ode_thm_gates_time_general_sources`, `ManuscriptConformance.ode_thm_gates_time_decoder_sources`, `ManuscriptConformance.aflat_atrial`, `ManuscriptConformance.nhistory_calls` | [Source executions](../ManuscriptConformance/SourceExecutions.lean), [remaining endpoints](../ManuscriptConformance/SourceExecutionsMore.lean) |
| The native protocol depends only on the column of its preparation (handover item D1, the amplification part): the trials of the native four-attempt protocol (the preparation, then the good reflection, the literal inverse preparation, the seed reflection, the preparation and a sign) depend on the preparation only through its action on the seed, so two native preparations, unitary and preserving the clean reflection wire, with the same column have the same trial outputs, success mass and conditional output, and the released guarantee `WOutcome` (per-trial directions included) and `HeraldedOutput` transfer between them; for the time-dependent native preparations (the general-size, decoder and writer solvers included) the column depends on the loading circuit only through its label columns `\|c⟩\|0⟩\|0⟩` when the weight preparation leaves its scratch clean on the clean input (the exact case), so `WOutcome` holds for every valid loading circuit with the label columns of one that has it; approximate weight preparations and completions and the constant-coefficient preparation are not covered, and the loading hypotheses of the endpoints are unchanged; for the general-source ODE solvers with exact preparations (`ode:thm:time` with the source interface, on the uniform mesh, on a mesh with breakpoints, and with represented samples of any sign) the loader may be any unitary specified only on its clean columns of positive weight, with the guarantees and counts of `GeneralSourceODE.solver`, `Mesh.mesh_solver`, `Mesh.mesh_solver_integral`, `robust_mesh_solver` and `robust_solver_integral`, and for the full-class Dyson solver of `odel:lem:dyson` with the complete certificate of `full_dyson` and the guarantees and counts of `full_single` and `full_actual`; the conformance theorem of `ode:thm:time` has the same form for every `T ≥ 0` (`ode_thm_time_columns`), with every actual successful trial and history within `ε` (`ode_thm_time_actual_columns`), and from branch certificates (`ode_thm_time_branch_columns`, `ode_thm_time_actual_branch_columns`); approximate completions: a loader within `δ` of a label-controlled one on the seed branch state after `P_w` keeps the guarantee of the public mesh trial family, with conditional trace distance `ε` under `20 g δ ≤ min(1/400, ε/20)`, since the `j`-th trial moves by at most `(4j + 1) δ` (`columns_approx_certificate`, `trial_sub_le`), and the conformance theorem of `ode:thm:time` with a loader within `δ` of a label-controlled reference on the clean subspace (`ode_thm_time_columns_approx`, `40 c_q ḡ δ ≤ min(1/400, ε/20)`; from branch certificates `ode_thm_time_branch_columns_approx`) | `SparseHamiltonian.ODERepeatProtocol.fourTrials_law_congr`, `SparseHamiltonian.GateNative.trialN_seed_congr`, `SparseHamiltonian.GateNative.nprotocol_law_congr`, `SparseHamiltonian.SourceAccuracyODE.WOutcome.of_column`, `ManuscriptConformance.heraldedOutput_of_column`, `SparseHamiltonian.GateNative.tnprepC_column_congr`, `SparseHamiltonian.GateNative.tzprepC_column_congr`, `SparseHamiltonian.GateNative.wpScratch_of_exact`, `SparseHamiltonian.GeneralSparseODE.GPubT.wOutcome_of_loader_columns`, `SparseHamiltonian.GeneralDecoderODE.prepTI_wOutcome_of_loader_columns`, `SparseHamiltonian.SourceAccuracyODE.WOutcome.of_loader_columns`, `SparseHamiltonian.GeneralSourceODE.solver_columns`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_columns`, `SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_columns`, `DysonFullClass.full_dyson_columns`, `DysonFullClass.full_actual_columns`, `ManuscriptConformance.ode_thm_time_columns`, `ManuscriptConformance.ode_thm_time_actual_columns`, `ManuscriptConformance.ode_thm_time_branch_columns`, `SparseHamiltonian.GeneralSourceExtensions.MeshOracles.columns_approx_certificate`, `SparseHamiltonian.ODEGroverActual.trial_sub_le`, `ManuscriptConformance.ode_thm_time_columns_approx`, `ManuscriptConformance.ode_thm_time_branch_columns_approx` | [preparation column](../ManuscriptConformance/PrepColumn.lean), [loader columns](../ManuscriptConformance/PrepLoader.lean), [clean-column loader](../ManuscriptConformance/SourceLoaderColumns.lean), [on a mesh](../ManuscriptConformance/MeshLoaderColumns.lean), [samples of any sign](../ManuscriptConformance/RobustLoaderColumns.lean), [Dyson full class](../ManuscriptConformance/DysonLoaderColumns.lean), [Dyson single program](../ManuscriptConformance/DysonLoaderActual.lean), [`ode:thm:time`](../ManuscriptConformance/TimeLoaderColumns.lean), [actual runs](../ManuscriptConformance/TimeLoaderRuns.lean), [branch certificates](../ManuscriptConformance/TimeLoaderBranch.lean), [approximate completions](../ManuscriptConformance/LoaderApprox.lean), [approximate columns](../ManuscriptConformance/TimeLoaderApprox.lean), [branch certificates with approximate columns](../ManuscriptConformance/TimeLoaderBranchApprox.lean) |
| The time-dependent `ode:thm:gates` over a finite gate set under the manuscript's certificates (time-indexed binary data with exact binary entries on the uniform mesh, the sources at the slot times; `T > 0` and `η_H + η_D > 0`, stated for the public record `PubT`): the finite-set protocol of `binary_ode_time_budget_sel` (the native preparation compiled selectively with the budget `ν'/3`, the supplied loading and weight-preparation circuits over the gate set retained verbatim, the exact zero tests with their gate kinds assumed in the gate set, the literal reverse-adjoint of the compiled preparation) has success at least `2/3`, conditional trace distance `ε` and every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase under the certificate-form conditions (represented samples of either sign), derived from the certificate of the actual compiled preparation; at most `80 ḡ (G_load + 2 G_wp + 2·10¹⁸ q* (𝔟+1)³ (64 c₁ (𝔟+1) + c₀ + 1)) + 40 ḡ (4 (3·10¹¹ (𝔟+1)³ + 2\|Z_s\| + \|X_a\|) + 3)` gates, `7864320 ḡ q*` calls of each selected matrix-oracle kind plus `80 ḡ (Q_load + 2 Q_wp)`, `7·10¹¹ (𝔟+1)³ + 4\|Z_s\| + 2\|X_a\|` qubits, and at most `80 ḡ` loadings and `160 ḡ` weight preparations in every history | `ManuscriptConformance.ode_thm_gates_time_cert_finite`, `ManuscriptConformance.binary_time_sel_sources`, `SparseHamiltonian.MeshCertificateODE.binary_ode_time_cert_sel`, `SparseHamiltonian.MeshCertificateODE.cert_time_outcome_of`, `SparseHamiltonian.MeshCertificateODE.cert_time_prep_bounds`, `SparseHamiltonian.MeshCertificateODE.cert_time_sel_outcome`, `SparseHamiltonian.MeshCertificateODE.cert_time_sel_prep_bounds` | [Finite gate set under the certificates](../ManuscriptConformance/GateODETimeCertFinite.lean), [certificate argument](../MeshCertificateODE/Selective.lean) |
| Centred averaging (`qls:rem:averaging`) and the query comparison of `qls:rem:constants`: for a polynomial `f` of degree at most `d` with nonnegative coefficients summing to one and a unitary `W` with `W P = P`, `W^{-⌊d/2⌋} f(W) - P = W^{-⌊d/2⌋}(f(W) - P)` (same error and selected norm); the released signed-step run of `⌈d/2⌉` steps with an explicit coefficient seed has success block exactly `W^{-⌊d/2⌋} f(W)` on every input and its literal adjoint the adjoint, with `54` matrix-oracle and `2` source calls per step; the actual Chebyshev runs of `d^fin_σ(1/100)` and `d^fin_σ(δ)` signed steps make fewer than `1/1400` of the calls of the forward conservative averaging runs of `q_av` and `k q_av` steps, and the prescribed budgets compare the same way with the numbers of tests and attempts fixed; the centred counts are compared separately (`700 d^fin_σ(1/100) < ⌈q_av/2⌉`, `700 d^fin_σ(δ) < ⌈k q_av/2⌉`; derived here, not claims of the manuscript) | `ChebyshevLinearSystemFinite.CentredAveraging.centred_sub_eq`, `ChebyshevLinearSystemFinite.CentredAveraging.centred_run`, `ChebyshevLinearSystemFinite.CentredAveraging.centred_averaging_run`, `ChebyshevLinearSystemFinite.CentredAveraging.test_query_comparison`, `ChebyshevLinearSystemFinite.CentredAveraging.final_query_comparison`, `ChebyshevLinearSystemFinite.CentredAveraging.budget_query_comparison`, `ChebyshevLinearSystemFinite.CentredAveraging.averaging_schedules`, `ChebyshevLinearSystemFinite.CentredAveraging.centred_test_ratio`, `ChebyshevLinearSystemFinite.CentredAveraging.centred_final_ratio` | [Centred averaging](../ChebyshevLinearSystemFinite/CentredAveraging.lean) |
| Lemma D.2 (`gate:lem:reuse`, compiled signed reuse) and Propositions D.4 and D.5 (`gate:prop:signed`, `gate:prop:core`): the LCU block `A₀⁻¹ ∑_j w_j Ces_j(F)` of the released reuse circuit `lcuI`; the signed-factor gate circuit (unconditional calls of `U_B` and `U_B†`, three phase gates per private call, an attenuation flag and `3⁸` amplification calls) with at most `4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` factor calls and full-output error `ε`, also with native factors (full-output error `ε + 3ζ nPriv`, `signed_native_simulation`); the clipped-transducer gate circuit on a finer mesh with exactly `6d` private calls; all before finite-set synthesis, with the success projection and sign reflection on designated flag qubits (`wKnown`) in place of a general `Π` and `Z`, the native private call of the clipped circuit in the form `GateOptimalBinary.ClipNative`, and exact rotations with the real weights, not the rounded coefficients of eq. `gate:eq:round` (the remark after `opt:thm:signed` included) | `GateOptimalPrecision.lcuI_ces_pad`, `GateOptimalPrecision.signed_gate_simulation`, `GateOptimalPrecision.signed_native_simulation`, `GateOptimalPrecision.clipped_gate_simulation` | [Signed-factor gate bound](../GateOptimalPrecision/SignedTheorem.lean) |
| Propositions D.3–D.5 (`gate:prop:finite`, `gate:prop:signed`, `gate:prop:core`) over a finite gate set with a supplied finite-set private circuit (item B3 of the v2.8 additions): the released circuit with every private call replaced by the supplied controlled private circuit (sector-controlled calls) or the supplied factor circuit (the unconditional factor calls of the signed circuit), the inverse calls by its literal reverse-adjoint, its work wires reused across calls, every boundary call by the controlled gates of `U_J`, and only the remaining exact gates synthesised: exactly `n_P` copies of its calls, at most `n_P G_C + G_known (c₁ log((G_known+1)/δ) + c₀ + 1)` gates with `G_known` the known gates of the released circuit, the qubit count, and full-output error `ε₀ + n_P ξ + δ` (error `ε` for `gate:prop:finite` with `n_P ≤ c_*R`, `ξ ≤ ε/(4c_*R)`, `δ = ε/4`); the native private operation, the native factor and the factor-conjugated private call of the clipped circuit compiled selectively once (within `η + ξ`); the designated-flag factor interface `wKnown` and exact weights as for the native forms | `ManuscriptConformance.sel_transfer`, `ManuscriptConformance.sel_signed_transfer`, `ManuscriptConformance.gate_prop_finite_sel`, `ManuscriptConformance.gate_prop_signed_sel`, `ManuscriptConformance.gate_prop_core_sel`, `ManuscriptConformance.gate_prop_finite_sel_native`, `ManuscriptConformance.gate_prop_signed_sel_native`, `ManuscriptConformance.gate_prop_core_sel_native`, `ManuscriptConformance.pcSel_spec`, `ManuscriptConformance.pcSel_unc` | [Finite-set propositions](../ManuscriptConformance/GatePropsSelective.lean) |
| Proposition D.4 (`gate:prop:signed`) for a general known success projection `Π` and sign reflection `Z` (Section `gate:sec:signed`; item B3 of the v2.8 additions): a conversion `C` to designated flag qubits (`C E = U_J ι₀`, `C Π C† = [wire f = 1]`, `C Z C† = (-1)^{wire z}`) leaves the signed compression, the weight and the Hamiltonian `λ C_K` unchanged, so the signed circuit with the converted boundary and factor simulates `exp(-i t λ C_K)` of the general interface, with exact gates and over a finite gate set; with the conversion built from supplied gates (`Eg` preparing the initialised input, `Cg` over `𝒢` converting) and charged: `U_C† · fc · U_C` per factor call (within `ξ` of `U_C U U_C†` when `fc` is within `ξ` of `U`; `n_P (|fc| + 2|Cg|)` retained gates, the calls of `n_P` copies of `fc`) and `C_J = |Eg| + |Cg|` boundary gates, full-output error `ε + n_P ξ + δ`; the synthesis of `Eg`, `Cg` from a description of `Π`, `Z` not formalised | `ManuscriptConformance.ham_conj`, `ManuscriptConformance.Converts.ham`, `ManuscriptConformance.gate_prop_signed_known`, `ManuscriptConformance.gate_prop_signed_known_sel`, `ManuscriptConformance.convFactor_approx`, `ManuscriptConformance.converts_of_gates`, `ManuscriptConformance.gate_prop_signed_known_conv` | [General known interface](../ManuscriptConformance/GatePropsKnown.lean) |
| Boundary compression, Lemma D.1 (`hs:lem:boundary`, `gate:eq:dyadic`): the released dyadic factorisation of the chronological boundary network and its gate count | `SparseHamiltonian.GateCircuit.Dyadic.chron_eq_compressed`, `SparseHamiltonian.GateCircuit.Sim.net_agrees`, `SparseHamiltonian.GateCircuit.Sim.netGates_length` | [Dyadic network](../GateEfficientHamiltonian/Circuit/Dyadic.lean) |
| Native factors and controls, Section D.4 (`gate:sec:native`): the stable three-qubit factor `U(c) = A_φ(R_u ⊗ I)A_φ†` (five gates, the exact action on clean inputs, `‖U(c) - I‖ ≤ 1 - √(1-u) + √u ≤ 2√u` on all inputs, error at most `3ξ` from magnitude accuracy `ξ²` and phase accuracy `ξ`) and its `2 b_P + b_T + 4` gates from an angle and a phase word; the clipping, Cayley and correction-phase identities of the joint private operation; the five-query controlled locator (exactly the controlled `U` on clean work wires for every `U` with `U\|x_*⟩ = \|y_*⟩`, at most `12w` gates, at most `16w` from zero work wires, the reversed circuit controlling `U†`) | `GateOptimalPrecision.uMat_action`, `GateOptimalPrecision.uMat_gates`, `GateOptimalPrecision.norm_uMat_sub_one_le`, `GateOptimalPrecision.norm_uMat_sub_le_of_accuracy`, `GateOptimalPrecision.gRun_locGates`, `GateOptimalPrecision.norm_uImpl_sub_le`, `GateOptimalPrecision.edgeMat_cayley`, `GateOptimalPrecision.hMat_edgeMat_hMat`, `GateOptimalPrecision.ctrlLoc_agrees`, `GateOptimalPrecision.ctrlLoc0_agrees` | [Controlled locator](../GateOptimalPrecision/ControlledLocator.lean) |
| Constant-error unitary implementation, Corollary 4.6 (`hs:cor:unitary`) | `SparseHamiltonian.UnitaryImplementation.implementation` | [Unitary endpoint](../SparseHamiltonian/UnitaryImplementation.lean) |
| Unitary implementation at every precision `0 < ε ≤ 1/2`, exact entries (`hs:cor:unitary`, with the additive term `ℓ` of `hs:thm:main` in place of `ℓ/log(e + ℓ/N)`) | `SparseHamiltonian.UnitaryPrecision.implementation`, `SparseHamiltonian.UnitaryPrecision.implementation_with_reference`, `SparseHamiltonian.UnitaryPrecision.implementation_two_term` | [Unitary precision endpoint](../UnitaryImplementationPrecision/Exact.lean) |
| The same with entries within `ε/(πN)` of the intended unitary, also as one circuit for every such unitary (`hs:cor:unitary`, inexact entries) | `SparseHamiltonian.UnitaryPrecision.implementation_inexact`, `SparseHamiltonian.UnitaryPrecision.implementation_inexact_uniform`, `SparseHamiltonian.UnitaryPrecision.implementation_inexact_two_term` | [Inexact-entry unitary endpoint](../UnitaryImplementationPrecision/Inexact.lean) |
| The bound `O(√(Nℓ) + ℓ/log(e + ℓ/N))` of Corollary 4.6 (`hs:cor:unitary`, eq. `hs:eq:unitarybound`), exact and inexact entries, also with an untouched reference: at most `5·10¹³ (√(Nℓ) + ℓ/log(e + ℓ/N))` entry-oracle calls (inverse calls counted, no location oracle), `ℓ = log(1/ε)`, from the circuits of Corollary 4.7 (`ρ_ε ≤ ℓ` and `ρ_ε ≤ ℓ/log(e + ℓ/N)`) | `OptimalSparseSimulation.unitary_bound`, `OptimalSparseSimulation.unitary_bound_inexact`, `OptimalSparseSimulation.unitary_bound_with_reference`, `OptimalSparseSimulation.unitary_bound_inexact_with_reference` | [Unitary bound](../OptimalSparseSimulation/UnitaryBound.lean) |
| Query lower bound `Ω(√N)` and worst-case query complexity `Θ(√N)` of unitary implementation at fixed error, for unitary query circuits over the entry oracle and its inverse, on the search family `(U_m)_{jk} = [j + k = m mod N]` (`hs:cor:unitary`, last sentence) | `UnitaryImplementationExtensions.LowerBound.entry_count_ge`, `UnitaryImplementationExtensions.LowerBound.implementation_count_ge`, `UnitaryImplementationExtensions.LowerBound.theta`, `UnitaryImplementationExtensions.LowerBound.theta_of_error` | [Unitary lower bound](../UnitaryImplementationExtensions/LowerBound.lean) |
| Query lower bound `Ω(√N)` of unitary implementation at fixed error for adaptive algorithms with heralded or unheralded output (trace-distance error below `1/2`), and for adaptive algorithms and unitary query circuits with inverse, controlled and controlled-inverse entry calls; with the released circuit, both halves of `Θ(√N)` for adaptive algorithms in one oracle model (`hs:cor:unitary`, last sentence) | `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_tree`, `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_calls_tree`, `AdaptiveUnitaryLowerBound.Entry.heralded_tree`, `AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_calls_program_of_error`, `AdaptiveUnitaryLowerBound.NonVacuity.released_tree` | [Adaptive unitary lower bound](../AdaptiveUnitaryLowerBound/Theorem.lean) |
| Query lower bound `Ω(√N)` of unitary implementation at trace-distance error `ε₀ = 1/2` (the trace-distance form, for adaptive and measured algorithms, of the endpoint of the manuscript's operator-norm range `0 < ε ≤ 1/2`), for adaptive algorithms with heralded or unheralded output and for algorithms with measurements inside a run, also with inverse, controlled and controlled-inverse entry calls: `(s₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) Q` (`32` for the measured call forms) for every `ε₀ ≤ 1/2`, and `√(N - 1) ≤ 64 Q` (unheralded; `512` for the measured call forms) at `ε₀ = 1/2` for `N ≥ 3`; with the released circuit, both halves of `Θ(√N)` in each class (`hs:cor:unitary`, last sentence) | `MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_tree_endpoint`, `MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_calls_tree_endpoint`, `MeasuredUnitaryLowerBound.Adaptive.unheralded_tree_sqrt`, `MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint`, `MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_endpoint`, `MeasuredUnitaryLowerBound.NonVacuity.released_measured_half` | [Trace-distance endpoint](../MeasuredUnitaryLowerBound/Endpoint/Tree.lean) |
| Query lower bound `Ω(√N)` of unitary implementation with the manuscript's operator-norm error `ε₀ ≤ 1/2` for algorithms with measurements inside a run (operator-norm error of a purification of the output, success with probability one), also with inverse, controlled and controlled-inverse entry calls, with the sharp per-input trace distance `s = ε₀ √(1 - ε₀²/4) ≤ √15/8`: `(N (1 - s) - 1)² ≤ 4 (N - 1) √(N - 1) Q` (`32` for the call forms) and `√(N - 1) ≤ 64 Q` (`512`) for `N ≥ 3`; unitary programs are contained, and the released circuit meets the hypotheses (`hs:cor:unitary`, `hs:eq:unitaryerror`) | `MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm`, `MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm`, `MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm_sqrt`, `MeasuredUnitaryLowerBound.OperatorNorm.densityAccurate_of_normImplements`, `MeasuredUnitaryLowerBound.OperatorNorm.normImplements_runAll`, `MeasuredUnitaryLowerBound.OperatorNorm.released_measured_norm` | [Operator-norm measured bound](../MeasuredUnitaryLowerBound/OperatorNorm/Bound.lean) |
| Second proof of the upper bounds of `hs:cor:unitary` at every precision, with exact and with inexact entries (two-term constants, target family part of the data) | `UnitaryImplementationExtensions.General.implementation`, `UnitaryImplementationExtensions.Inexact.implementation` | [Inexact unitary endpoint](../UnitaryImplementationExtensions/Inexact.lean) |
| Constant-coefficient dissipative ODE, Theorem 6.1 (`ode:thm:main`), with the per-run Euclidean guarantee for every actual trial with a nonzero success branch | `SparseHamiltonian.ODECompleteEndpoint.solver`, `ManuscriptConformance.ode_thm_main_actual` | [Complete ODE endpoint](../SparseODE/ODECompleteSuccess.lean) |
| Two tagged copies of the original support, Lemma 6.2 (`ode:lem:tags`): for Hermitian `K` supported on `supp(G) ∪ supp(G†)` with row and column norms at most `ρ`, the moment bounds with `p = 2s` from the original locators, without a locator for the support union; the lemma's circuit conclusion (known `J`, constant sparse-query cost of `C_0`: `24` native calls, `6` row, `6` column and `12` value calls, and the literal adjoint for the inverse) for every `K` computed by a public rule `f i j (G i j) (G j i)` that vanishes on two zero entries and is conjugate symmetric, and from it the baseline simulation of `exp(-i t K)` (Eq. `ode:eq:hs`, one public rescaling for all such rules); the branches `K_k = H + kD` are the rule `lchsRule k`, whose circuit is the released one | `ManuscriptConformance.ode_lem_tags_rule`, `ManuscriptConformance.ode_lem_tags_rule_simulation`, `SparseHamiltonian.ODETaggedPairEntry.program_intertwines`, `SparseHamiltonian.ODETaggedPairEntry.program_lchsRule`, `SparseHamiltonian.ODETaggedMoments.native_moment_certificate`, `SparseHamiltonian.ODETaggedMoments.native_lchs_moment_certificate`, `SparseHamiltonian.ODEFixedTaggedQuery.query_certificate`, `SparseHamiltonian.ODENativeCayley.program_intertwines` | [Tagged moments](../SparseODE/ODETaggedMoments.lean), [arbitrary rule](../ManuscriptConformance/TaggedPairEntry.lean), [simulation](../ManuscriptConformance/TaggedPairSimulation.lean) |
| Optimal sparse-query linear-system algorithm, Theorem 8.1 (`qls:thm:main`) | `SparseLinearSystems.Endpoint.main` | [Linear-system endpoint](../SparseLinearSystems/Endpoint/Main.lean) |
| Separate matrix and preparation query bounds, Corollary `qls:cor:separate`, conditional on a stated uniform block-input solver interface representing Gao–Ji–Liu's result (`ext_separateSolver`, `SparseLinearSystems.Separate.SeparateSolver`; the external solver theorem is not formalised in this package): one protocol, fixed before the instance, with at most `C_A √s κ log(1/ε)` matrix queries on every completed history and, on every valid input with `ν/2 ≤ ν̂ ≤ 2ν`, at most `C_b κ/ν` preparation calls on every completed history, success at least `2/3` and conditional trace distance at most `ε`; with a writer value oracle specified only on clean targets, the same protocol with every value call replaced by writer, adder and inverse writer on one clean scratch register, fixed before the instance, with the same success probability and conditional output, at most twice the matrix calls (constant `2 C_A`) and the same preparation calls (constant `C_b`) | `ManuscriptConformance.qls_cor_separate`, `ManuscriptConformance.qls_cor_separate_writer`, `SparseLinearSystems.Separate.main`, `SparseLinearSystems.Separate.SeparateSolver` | [Separate-query endpoint](../SparseLinearSystems/Separate/Main.lean), [solver interface](../SparseLinearSystems/Separate/SolverInterface.lean), [conformance](../ManuscriptConformance/LinearSystemSeparate.lean), [writer form](../ManuscriptConformance/WriterSeparate.lean) |
| Sparse Cayley representation and the kernel walk, Lemmas 8.2 and 8.3 (`qls:lem:entry`, `qls:lem:walk`): Lemma 8.2 for a general Hermitian `s`-sparse `H` with `‖H‖ ≤ 1` given by native sparse oracles (`ManuscriptConformance.qls_lem_entry`, `EntrywiseCayley`, bundled from the arbitrary-`H` constructions of `FixedNativeCayleySimulation` and `NativeCayleyProgram`: the boundary isometry `J`, built from the public slot data alone, and the clean encoding, both fixed for every input; for every input the self-adjoint edge generator `K`, and when `H` is Hermitian with `‖H‖ ≤ 1` (the row and column energy bounds derived from it) `J† K J = H/√s`, `J† K² J ≤ 1` in the Loewner order, `‖K J‖ ≤ 1` and `‖K‖ ≤ √s`; for every real `γ` the Cayley unitary of `γ K`, implemented on the clean encoding by an eighteen-query native circuit, six calls of each native primitive, and its inverse by the literal adjoint program); `branchProps` gives the operator conclusions of Lemma 8.2 for the operator `H₀` of the augmented walk (the off-diagonal lift of `Z ⊗ B`, `B = [[0, A], [A†, 0]]`) | `ManuscriptConformance.qls_lem_entry`, `SparseLinearSystems.SparseBranch.branchProps`, `SparseLinearSystems.WalkGap.Hyp.fixed_lift`, `SparseLinearSystems.WalkGap.Hyp.tangent_gap`, `SparseLinearSystems.WalkGap.Hyp.chord_gap` | [Kernel walk](../SparseLinearSystems/WalkGap.lean) |
| Gate-efficient sparse simulation, exact gates, Theorem 4.8 (`hs:thm:gates`) | `SparseHamiltonian.GateCircuit.Sim.gate_efficient_simulation` | [Gate-level endpoint](../GateEfficientHamiltonian/Circuit/Theorem.lean) |
| Time-dependent Hamiltonian simulation, uniform mesh, Theorem 4.1 (`hs:thm:time`) | `SparseHamiltonian.TimeDependent.simulation` | [Time-dependent endpoint](../TimeDependentHamiltonian/Theorem.lean) |
| Gate counts for time-dependent simulation, uniform mesh, exact gates (`hs:thm:time` with the circuit of `hs:thm:gates`) | `SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation` | [Time-dependent gate-level endpoint](../GateEfficientTimeDependent/Theorem.lean) |
| Time-dependent dissipative ODE, uniform mesh, Theorem 6.3 (`ode:thm:time`), with the left-endpoint source rule and public source norms; formally also with positive semidefinite dissipative parts of the represented samples, which the manuscript does not assume ("Formal restriction (sample positivity)" below) | `SparseHamiltonian.TimeDependentODE.solver` | [Time-dependent ODE endpoint](../TimeDependentODE/Theorem.lean) |
| Time-dependent dissipative ODE with the general source interface, Theorem 6.3 (`ode:thm:time`, eqs. `ode:eq:source-interface-mass`, `ode:eq:source-interface-preparation`): public nodes `v_i ∈ [0, T]` and complex coefficients `ω_i`, a supplied weight preparation `P_w` with amplitudes `√(‖z_a‖/B_q)` and a controlled data loader `U_load`, `B_q ≤ c_q B`, and the propagated quadrature certificate `‖∫₀ᵀ U(T, v) b(v) dv - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B`; success probability at least `2/3`, conditional trace distance `ε`, at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `40 g'` calls of each of `P_w`, `U_load` and `P_w†`, `g' = 2 c_q ḡ`; also on the two composite source interfaces with the certificate stated for the solution (`propagated_solver`), related through Duhamel's formula; formally also with positive semidefinite dissipative parts of the represented samples (not assumed in the manuscript); the same guarantees and counts with the loader specified only on its clean columns `\|a, τ⟩\|seed⟩` of the labels with nonzero source vectors (any unitary on the whole branch register, not assumed to preserve the labels elsewhere; `40 g'` calls of each of `P_w`, the loader and `P_w†`; handover item D1, exact case) | `SparseHamiltonian.GeneralSourceODE.solver`, `SparseHamiltonian.GeneralSourceODE.propagated_solver`, `SparseHamiltonian.GeneralSourceODE.duhamel`, `SparseHamiltonian.GeneralSourceODE.exists_isPropagator`, `SparseHamiltonian.GeneralSourceODE.solver_columns`, `SparseHamiltonian.GeneralSourceODE.Oracles.columns_certificate` | [General-source ODE endpoint](../GeneralSourceODE/Theorem.lean), [clean-column loader](../ManuscriptConformance/SourceLoaderColumns.lean) |
| Time-dependent dissipative ODE with the general source interface at zero time or with a known zero generator, and for every `T ≥ 0` (`ode:thm:time` with the degenerate branches `T = 0` and `η_H + R η_D = 0` of `ode:thm:main`): the identity SELECT and no matrix query in the zero cases, the released guarantees in every case; formally also with positive semidefinite dissipative parts of the represented samples | `SparseHamiltonian.GeneralSourceExtensions.zero_solver`, `SparseHamiltonian.GeneralSourceExtensions.solver_nonneg`, `SparseHamiltonian.GeneralSourceExtensions.zero_propagated_solver` | [General-source zero cases](../GeneralSourceExtensions/Zero.lean) |
| The same with approximately implemented preparations (eq. `ode:eq:source-interface-preparation` up to operator-norm errors): supplied unitaries `P_w`, `U_load` within `δ` of exact preparations, which may depend on the instance and are not supplied, with `30 g' δ ≤ 1/400` and `30 g' δ ≤ ε/20`; success probability at least `2/3`, conditional trace distance `ε` and the released counts, also for every `T ≥ 0` | `SparseHamiltonian.GeneralSourceExtensions.approx_solver`, `SparseHamiltonian.GeneralSourceExtensions.approx_solver_nonneg`, `SparseHamiltonian.GeneralSourceExtensions.approx_certificate` | [Approximate preparations](../GeneralSourceExtensions/Approx/Theorem.lean) |
| The same on nonuniform meshes with breakpoints and integrated certificates: one generator and one forcing piece and one represented sample per mesh interval, a clock of `N` uniform slots, the integrated sample error `∑_r ∫ ‖G_r - G̃_r‖` and the refinement term `s Λ ∑_r \|c_r T/N - Δ_r\|` in the budget (`Λ` the bound on the decoded entries, `c_r` the slots of interval `r`; at most `s Λ M T/N`, zero on the uniform mesh with `N = qM`), supplied node values, and the certificate on the propagated source sum or, for continuous pieces, on the propagated vector integral (Duhamel's formula on the mesh); combined with approximate preparations and every `T ≥ 0`; on the uniform mesh with `N = M` slots the mesh endpoint gives `GeneralSourceODE.solver` itself and the combined endpoint the statement of `approx_solver_nonneg` itself (the `M`-slot workspace is definitionally the released one); formally also with positive semidefinite dissipative parts of the represented samples (without them in `RepresentedSampleODE`, next row); with exact preparations also with the loader specified only on its clean columns of positive weight, with the guarantees and counts of `mesh_solver` and `mesh_solver_integral` (handover item D1, exact case) | `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_integral`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_nonneg`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_integral`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.solver_of_mesh`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.approx_solver_nonneg_of_mesh`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_uniform`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_uniform`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_duhamel`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.exists_isMeshPropagator`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_columns`, `SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_integral_columns` | [General-source mesh endpoints](../GeneralSourceExtensions/Mesh/Integral.lean), [clean-column loader on a mesh](../ManuscriptConformance/MeshLoaderColumns.lean) |
| The same with represented samples of any sign (proof of `ode:thm:time`, the represented samples after Eq. `ode:eq:timedisc`: only the true path is dissipative): the analysis runs on the positive repairs `(‖D̃‖/(‖D̃‖ + κ))(D̃ + κ)` of the dissipative parts `D̃_r` of the samples (`Re ⟨w, G̃_r w⟩ ≥ -κ_r ‖w‖²`), the circuits on the samples; the released public tables, SELECT programs, query bounds and source-call counts, under the budgets `ζ + c_q (ΔG + 2 Λ_κ + 2 ΔR) ≤ ε/(2000 ḡ)` and `6 R (Λ_κ + ΔR) ≤ ν` (`Λ_κ = ∑_r (t_{r+1} - t_r) κ_r`), with the negativity bounds of the true path `ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε/(2000 ḡ)` and `6 R (ΔD + ΔR) ≤ ν` (`ΔD = ∑_r ∫ ‖Herm(G_r - G̃_r)‖ ≤ ΔG`; the second budget bounds the dissipative part `R ΔD` of the integrated branch sample error `∑_r ∫ ‖K̃_{k,r} - K_k(u)‖ du ≤ ΔH + R ΔD`, `\|k\| ≤ R`); and the time-dependent gate-level solver from binary data for every `T ≥ 0` with the discretisation budget at the sample error `3 δ_G` and the branch budget `6 R' T δ_G ≤ ν'` (`R`, `ν` the LCHS radius and precision of the ratio `2 c_q ḡ` on a mesh, `R'`, `ν'` those of `2 ḡ` in the gate solver); on a mesh also for integrable generator pieces and mild solutions (an integrable propagated forcing `v ↦ U(T, v) b_r(v)` and Duhamel's formula for `x(T)`), without continuity or a classical solution (the propagator of the generator pieces classical on every closed piece), classical solutions of bounded pieces with an integrable propagated forcing being mild by Duhamel's formula; with exact preparations, every actual trial with a nonzero success branch within Euclidean distance `ε` of `x(T)/‖x(T)‖` up to a global phase (the per-run form of `ode:thm:time`); with exact preparations also with the loader specified only on its clean columns of positive weight, with the guarantees and counts of `robust_mesh_solver` and `robust_solver_integral`, and for every `T ≥ 0` with integrable pieces and mild solutions, in the statement of `ode_thm_time` (handover item D1, exact case) | `SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_regular`, `SparseHamiltonian.RepresentedSampleODE.MildSolution.of_solves`, `SparseHamiltonian.RepresentedSampleODE.mesh_duhamel_bounded`, `SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_path`, `SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_integral`, `SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_nonneg`, `SparseHamiltonian.RepresentedSampleODE.robust_propagated_solver`, `SparseHamiltonian.RepresentedSampleODE.robust_zero_core`, `SparseHamiltonian.RepresentedSampleODE.repair_nonneg`, `SparseHamiltonian.RepresentedSampleODE.GateTime.robust_binary_time_outcome_nonneg`, `SparseHamiltonian.RepresentedSampleODE.GateTime.robust_native_time_outcome`, `SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_columns`, `SparseHamiltonian.RepresentedSampleODE.robust_solver_integral_columns`, `SparseHamiltonian.RepresentedSampleODE.robust_solver_nonneg_regular_columns`, `ManuscriptConformance.ode_thm_time_columns` | [Represented samples of any sign](../RepresentedSampleODE/Statements.lean), [clean-column loader](../ManuscriptConformance/RobustLoaderColumns.lean), [Theorem `ode:thm:time`](../ManuscriptConformance/TimeLoaderColumns.lean) |
| The same with preparations on temporary work registers (`ode:thm:time` with finite implementations, the paragraph after Eq. `ode:eq:source-interface-preparation`, whose clean-input operator errors are those of the full-output convention of Eq. `access:eq:full-output`): a supplied `P_w` on the label register and a temporary work register, a supplied `U_load` on the label, data and work registers and `P_w†` its adjoint, `P_w` and `U_load` each within `δ` of an exact preparation (`P`, and `∑_a \|a⟩⟨a\| ⊗ L(a)` with unitary completions `L(a)`; neither is supplied) on a clean work register, with the represented samples of any sign, integrable pieces and mild solutions of `RepresentedSampleODE`; the released trial family with every fixed gate the identity on the work register, heralded on a clean work register: success at least `2/3`, conditional trace distance `ε`, the released counts and budgets; the label-controlled loader and the classical propagator on each closed mesh cell are this package's hypotheses, so a loader specified only on clean inputs and a jump of the generator inside a cell are not covered | `SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_regular`, `SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg`, `SparseHamiltonian.CleanWorkODE.work_certificate`, `SparseHamiltonian.CleanWorkODE.eval_workRecast_clean`, `SparseHamiltonian.CleanWorkODE.actualOracleW_clean`, `SparseHamiltonian.CleanWorkODE.liftAct_clean` | [Preparations on temporary work registers](../CleanWorkODE/Statements.lean) |
| Gate-efficient dissipative ODE with source circuits within `ν` (`ode:thm:gates`, whose `G_src(ν)` asks a combined implementation error `ν = ε/(10⁴ ḡ)` of `P_w`, the loading and `P_w†`, the paragraph before Theorem `ode:thm:gates`): the released native protocols for constant coefficients and, with represented samples of any sign, for time-dependent coefficients, from binary data and for every `T ≥ 0`, under the source budgets `98304 q* ζ + 2 ζ_s ≤ 4 ν` and `98304 q* ζ + 3 ζ_s ≤ 13 ν'` (`ν' = ν/4`; `q*` the package's query parameter, for time-dependent coefficients at the internal ratio `2ḡ` and accuracy `ε/2`), so that with the package's arithmetic accuracy `98304 q* ζ ≤ ν/2` (resp. `ν'/2`) each source circuit within `ν` suffices (the released analysis asks `ν/4` and `ν/24`); success at least `2/3`, every successful trial within `ε/250` (constant) or `ε/100` (time-dependent) of the normalised solution up to a global phase and the conditional output within the same trace distance (`WOutcome`, from any relative vector error `ρ ≤ 1/4`), with the released counts | `SparseHamiltonian.SourceAccuracyODE.binary_ode_outcome_nonneg`, `SparseHamiltonian.SourceAccuracyODE.binary_time_outcome_nonneg`, `SparseHamiltonian.SourceAccuracyODE.native_ode_outcome`, `SparseHamiltonian.SourceAccuracyODE.native_time_outcome`, `SparseHamiltonian.SourceAccuracyODE.woutcome_of_vec`, `SparseHamiltonian.SourceAccuracyODE.woutcome_of_bounds` | [Source circuits within ν](../SourceAccuracyODE/Statements.lean) |
| Gate-efficient dissipative ODE, constant coefficients, exact gates, Theorem 6.7 (`ode:thm:gates`) | `SparseHamiltonian.GateODE.solver` | [Gate-level ODE endpoint](../GateEfficientODE/Theorem.lean) |
| Gate-efficient dissipative ODE, time-dependent coefficients, uniform mesh, exact gates (`ode:thm:gates`); formally with `L_r ≥ 0` for every represented sample | `SparseHamiltonian.GateODE.Time.solver` | [Time-dependent gate-level ODE endpoint](../GateEfficientODE/Time/Theorem.lean) |
| General constant-coefficient ODE, Theorem 6.5 (`ode:thm:general`) with Lemma 6.4 (`ode:lem:block`, in this package's normalisation `8√2 Λ`; the manuscript has `2πΛ`), pure-output block-input linear-system solver as a hypothesis | `SparseHamiltonian.GeneralODE.general`, `SparseHamiltonian.GeneralODE.NativeBlock.exists_native_block` | [General ODE endpoint](../GeneralODE/Theorem.lean) |
| General constant-coefficient ODE from a mixed-output block-input linear-system solver, Theorem 6.5 (`ode:thm:general`, eq. `ode:eq:history-solver-tolerance`): the solver need only reach conditional output trace distance `δ_LS = ε/(4096 g²)` with possibly mixed output; success probability at least `175/256`, conditional trace distance `ε` after the work register is discarded, and for a solver with `c κ log(2/δ)` calls at most `227776401506304000 · c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` matrix queries | `SparseHamiltonian.MixedOutputODE.general`, `SparseHamiltonian.MixedOutputODE.general_of_block`, `SparseHamiltonian.MixedOutputODE.general_query_bound` | [Mixed-output general ODE](../MixedOutputODE/Theorem.lean) |
| General constant-coefficient ODE at `T = 0` (direct preparation of the initial state) and for every `T ≥ 0` (`ode:thm:general`), block-input linear-system solver as a hypothesis for `T > 0` | `SparseHamiltonian.GeneralODE.general_zero`, `SparseHamiltonian.GeneralODE.general_nonneg` | [Zero-time general ODE](../GeneralODEZeroTime/Theorem.lean) |
| Zero time or a zero norm bound in time-independent simulation: identity circuit, no query, exact; Theorem 2.1 for every `η ≥ 0` (remark in `hs:thm:main`) | `SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_zero`, `SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_log_one_nonneg` | [Zero-time Hamiltonian](../ZeroTimeRemarks/Hamiltonian.lean) |
| Zero time or a known zero Hamiltonian in time-dependent simulation, on uniform and nonuniform meshes and for time-indexed block encodings, for every `T ≥ 0` and every norm bound `η ≥ 0` (`α ≥ 0`) (remark in `hs:thm:time`; `hs:eq:blockadditive`) | `SparseHamiltonian.ZeroTimeRemarks.TimeUniform.simulation_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.TimeMesh.simulation_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.TimeBlock.simulation_nonneg` | [Zero-time time-dependent simulation](../ZeroTimeRemarks/TimeUniform.lean) |
| Empty circuit at zero time in the gate-level simulations, exact and native gates (remarks in `hs:thm:gates` and, for the time-dependent circuits, `hs:thm:time`) | `SparseHamiltonian.ZeroTimeRemarks.Gates.simulation_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.Gates.time_simulation_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.Gates.native_simulation_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.Gates.native_simulation_signed_zero`, `SparseHamiltonian.ZeroTimeRemarks.Gates.native_time_simulation_nonneg` | [Zero-time gate circuits](../ZeroTimeRemarks/Gates.lean) |
| Zero time or a known zero generator in the dissipative ODE solvers, with no matrix query in the native oracle family of the positive case; the solvers for every `T ≥ 0` (remark after `ode:thm:main`; `ode:thm:time`) | `SparseHamiltonian.ZeroTimeRemarks.ODEConstant.solver_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.ODETime.solver_nonneg`, `SparseHamiltonian.ZeroTimeRemarks.ODEMesh.solver_nonneg` | [Zero-time ODE solvers](../ZeroTimeRemarks/ODEConstant.lean) |
| Zero time or a known zero generator in the gate-level dissipative ODE solvers: direct source assembly, with no `U_J` or private call (exact gates), exactly the calls of the supplied source circuits (native implementations) and no sparse-oracle call beyond them (binary data) (remark in `ode:thm:gates`) | `SparseHamiltonian.ZeroTimeGateODE.exact_ode_solver_zero`, `SparseHamiltonian.ZeroTimeGateODE.exact_ode_time_solver_zero`, `SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_zero`, `SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_zero`, `SparseHamiltonian.ZeroTimeGateODE.binary_zero_no_matrix_calls` | [Zero-time native gate-level ODE](../ZeroTimeGateODE/Constant.lean) |
| The gate-level dissipative ODE solvers for every `T ≥ 0`: exact gates, native implementations, binary and time-indexed binary sparse oracles, and over a finite gate set with the per-trial claim (`ode:thm:gates` with its zero-time remark) | `SparseHamiltonian.ZeroTimeGateODE.exact_ode_solver_nonneg`, `SparseHamiltonian.ZeroTimeGateODE.exact_ode_time_solver_nonneg`, `SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_nonneg`, `SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_nonneg`, `SparseHamiltonian.ZeroTimeGateODE.binary_ode_solver_nonneg`, `SparseHamiltonian.ZeroTimeGateODE.binary_ode_time_solver_nonneg`, `SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_nonneg_trials`, `SparseHamiltonian.ZeroTimeGateODE.binary_ode_solver_nonneg_trials` | [Combined zero-time gate-level ODE](../ZeroTimeGateODE/Combined.lean) |
| Matching linear-system query lower bound, Theorem 9.1 (`qlsl:thm:main`) | `LinearSystemLowerBound.lower_bound` | [Lower-bound endpoint](../LinearSystemLowerBound/Theorem.lean) |
| Elementary XOR lower bound, Lemma 9.2 (`qlsl:lem:xor`) | `LinearSystemLowerBound.Boolean.xor_lemma` | [XOR lemma](../LinearSystemLowerBound/XorLemma.lean) |
| Hamiltonian-simulation query lower bound, Theorem 5.1 (`hsl:thm:main`) | `SparseLowerBounds.Hamiltonian.main_max` | [Hamiltonian lower-bound endpoint](../SparseLowerBounds/Hamiltonian/Theorem.lean) |
| Small-correlation search parity, the mixed family and the time family, Lemmas 5.2, 5.3 and 5.5 (`hsl:lem:search`, `hsl:lem:mixed`, `hsl:lem:time`) | `SparseLowerBounds.SearchWeight.search_lemma`, `SparseLowerBounds.SearchWeight.search_lemma_worst`, `SparseLowerBounds.Hamiltonian.mixed_general`, `SparseLowerBounds.Hamiltonian.time_main`, `SparseLowerBounds.Hamiltonian.time_main_native` | [Search weight](../SparseLowerBounds/Query/SearchWeight.lean) |
| Precision lower bound of the signed scalar chain, Lemma 5.4 (`hsl:lem:precision`): every program simulating the chain for `0 < τ ≤ n` within `ε ≤ (τ/(2n))^n/8` makes at least `n/4` queries (`n ≥ 1` suffices) | `SparseLowerBounds.Hamiltonian.precision_general`, `SparseLowerBounds.Hamiltonian.precision_native`, `SparseLowerBounds.Hamiltonian.precision_spec` | [Precision family](../SparseLowerBounds/Hamiltonian/PrecisionFamily.lean) |
| No uniform `O(√s L^p + L)` bound for `p < 1/2`, Corollary 5.6 (`hsl:cor:power`) | `SparseLowerBounds.Hamiltonian.cor_power_not_uniform` | [Power corollary](../SparseLowerBounds/Hamiltonian/Power.lean) |
| Heralded transfer, Lemma 7.5 (`odel:lem:herald`) | `SparseLowerBounds.Hamiltonian.main_max_herald` | [Heralded transfer](../SparseLowerBounds/Hamiltonian/Herald.lean) |
| Dissipative-ODE query lower bound, Theorem 7.1 (`odel:thm:combined`) | `SparseLowerBounds.ODE.combined` | [ODE lower-bound endpoint](../SparseLowerBounds/ODE/Theorem.lean) |
| Outer adversary bound, Lemma 7.2 (`odel:lem:outer`) | `SparseLowerBounds.ODE.outer_count_ge` | [Outer adversary](../SparseLowerBounds/ODE/JointAdversary.lean) |
| Inhomogeneous time-dependent ODE lower bound, Theorem 7.3 (`odel:thm:joint`) | `SparseLowerBounds.ODE.joint_witness` | [Joint ODE lower bound](../SparseLowerBounds/ODE/JointTheorem.lean) |
| Heralded transfer in the ODE model, Lemma 7.5 (`odel:lem:herald`, eq. `odel:eq:hsbound`) | `SparseLowerBounds.ODE.herald_witness` | [ODE precision families](../SparseLowerBounds/ODE/Precision.lean) |
| Constant-coefficient positive semidefinite ODE precision lower bound, Theorem 7.6 (`odel:thm:psd`) | `ODELowerBoundExtensions.Psd.psd` | [PSD ODE lower bound](../ODELowerBoundExtensions/Psd/Theorem.lean) |
| Source-free variant of the joint ODE lower bound, Proposition 7.4 (`odel:rem:homogeneous`) | `ODELowerBoundExtensions.Homogeneous.hom_witness` | [Homogeneous ODE lower bound](../ODELowerBoundExtensions/Homogeneous/Theorem.lean) |
| Dissipative-ODE lower bound with maximum sparsity exactly `s`, in one common dimension or on a qubit register (padding remarks of Theorems 7.3 and 7.1, `odel:thm:joint` and `odel:thm:combined`) | `ODELowerBoundExtensions.Padding.combined_common_dimension` | [ODE padding](../ODELowerBoundExtensions/Padding/Combined.lean) |
| Dissipative-ODE lower bound for retry protocols over the released ODE solver's oracle, Theorem 7.1 (`odel:thm:combined`) | `ODELowerBoundExtensions.Release.combined_max_release` | [ODE release bridge](../ODELowerBoundExtensions/Release/Bridge.lean) |
| Two-sided bracket for the released ODE solver on the hard families, Theorem 7.1 (`odel:thm:combined` with `odel:eq:upper`) | `ODELowerBoundExtensions.Release.release_theta_bracket` | [ODE release bracket](../ODELowerBoundExtensions/Release/Theta.lean) |
| Fixed-parameter precision obstruction: a truncated Dyson-series ODE solver with `O(ḡ e^z (1 + z + L_g/log(e + L_g/z)))` matrix queries, Lemma 7.7 (`odel:lem:dyson`, eq. `odel:eq:dyson`), with the source access of the released time-dependent solver (public norms of the initial state and of one forcing sample per cell, positive cell quadrature) in place of the general source interface | `ODELowerBoundExtensions.Dyson.dyson` | [Dyson ODE solver](../ODELowerBoundExtensions/Dyson/Theorem.lean) |
| No uniform `ḡ √s τ log(ḡ/ε)` ODE lower bound for retry protocols at fixed `s`, `τ`, `ḡ` (eq. `odel:eq:fixed` and its consequence) | `ODELowerBoundExtensions.Dyson.no_retry_witnesses` | [Dyson solver on the lower-bound class](../ODELowerBoundExtensions/Dyson/Family/Retry.lean) |
| Fixed-parameter precision obstruction as one heralded program in the solver class of the ODE lower bounds (four attempts with coherent amplification cutoffs and a first-success readout), with at most `16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))` calls, Lemma 7.7 (`odel:lem:dyson`, eq. `odel:eq:dyson`), with the source access of the released time-dependent solver (public norms of the initial state and of one forcing sample per cell, positive cell quadrature) in place of the general source interface | `DysonSingleProgram.solver_dyson`, `DysonSingleProgram.exists_solver_of_shape`, `DysonSingleProgram.solver_dyson_joint` | [Single-program Dyson solver](../DysonSingleProgram/Theorem.lean) |
| No uniform `ḡ √s τ log(ḡ/ε)` ODE lower bound for single heralded programs or adaptive solvers at fixed `s`, `τ`, `ḡ` (eq. `odel:eq:fixed` and its consequence) | `DysonSingleProgram.solver_fixed`, `DysonSingleProgram.no_witnesses`, `DysonSingleProgram.no_tree_witnesses` | [Single-program fixed-parameter obstruction](../DysonSingleProgram/Fixed.lean) |
| Fixed-parameter precision obstruction as one heralded program on its general certified-mesh access with source preparation (mesh, cell-to-sample map and source norms public; coherent amplification cutoffs and a first-success readout), with at most `16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))` matrix queries, also on the released time-dependent class, and eq. `odel:eq:fixed` with its consequence for these programs, Lemma 7.7 (`odel:lem:dyson`), with the source access of the released time-dependent solver (public norms of the initial state and of one forcing sample per cell, positive cell quadrature) in place of the general source interface | `DysonGeneralAccess.Dyson.single_dyson`, `DysonGeneralAccess.Dyson.single_release_class`, `DysonGeneralAccess.Dyson.single_fixed`, `DysonGeneralAccess.Dyson.single_no_uniform` | [General-access Dyson program](../DysonGeneralAccess/Theorem.lean) |
| Lemma 7.7 (`odel:lem:dyson`, eq. `odel:eq:dyson`) on the input class of Theorem 6.3 (`ode:thm:time`), with this package's label-controlled loading and a classical propagator on each closed mesh cell: represented samples of either sign (radially clipped to the entry bound `η`, `z = s η T`), source nodes anywhere in `[0, T]` with complex weights, hidden source norms, the integrated certificate on the represented generator; one heralded program with at most `16000 c_q ḡ e^z (1 + z + L/log(e + L/z))` matrix queries and `40 c_q ḡ e^z` calls of each source interface, the four-attempt protocols over the separate primitives `P_w`, `U_load`, `P_w†` and with approximate preparations on temporary work registers, and eq. `odel:eq:fixed` with its consequence on this class; with exact preparations also the complete certificate of the trial family, the single heralded program and the four-attempt protocol over `P_w`, `Lo`, `P_w†`, with the loader specified only on its clean columns of positive weight (handover item D1, exact case) | `DysonFullClass.full_single`, `DysonFullClass.full_actual`, `DysonFullClass.full_approx`, `DysonFullClass.full_bound`, `DysonFullClass.full_fixed`, `DysonFullClass.full_no_uniform`, `DysonFullClass.full_dyson_columns`, `DysonFullClass.full_single_columns`, `DysonFullClass.full_actual_columns` | [Full-class Dyson comparison](../DysonFullClass/Statements.lean), [clean-column loader](../ManuscriptConformance/DysonLoaderColumns.lean), [single program and separate primitives](../ManuscriptConformance/DysonLoaderActual.lean) |
| Dissipative-ODE query lower bound for adaptive solvers with inverse and controlled calls, Theorem 7.1 (`odel:thm:combined`) | `AdaptiveODELowerBound.combined_tree`, `AdaptiveODELowerBound.combined_max_tree` | [Adaptive ODE lower-bound endpoint](../AdaptiveODELowerBound/Theorem.lean) |
| Outer adversary, joint and source-free ODE lower bounds for adaptive solvers, Lemma 7.2, Theorem 7.3 and Proposition 7.4 (`odel:lem:outer`, `odel:thm:joint`, `odel:rem:homogeneous`) | `AdaptiveODELowerBound.Joint.outer_count_ge_tree`, `AdaptiveODELowerBound.Joint.joint_witness_tree`, `AdaptiveODELowerBound.Joint.hom_witness_tree` | [Adaptive joint ODE lower bound](../AdaptiveODELowerBound/Joint/Families.lean) |
| Heralded transfer and positive semidefinite precision lower bound for adaptive solvers, Lemma 7.5 and Theorem 7.6 (`odel:lem:herald`, `odel:thm:psd`) | `AdaptiveODELowerBound.herald_witness_tree`, `AdaptiveODELowerBound.Psd.psd_tree` | [Adaptive PSD ODE lower bound](../AdaptiveODELowerBound/Psd/Theorem.lean) |
| Padded ODE families for adaptive solvers, with maximum sparsity exactly `s`, in one common dimension or on a qubit register (padding remarks of Theorems 7.3 and 7.1) | `AdaptiveODELowerBound.Padding.combined_common_dimension_tree`, `AdaptiveODELowerBound.Padding.combined_qubit_register_tree` | [Adaptive ODE padding](../AdaptiveODELowerBound/Padding/Combined.lean) |
| Dissipative-ODE lower bound for adaptive solvers over the released ODE solver's oracle, Theorem 7.1 (`odel:thm:combined`) | `AdaptiveODELowerBound.Release.combined_max_release_tree` | [Adaptive ODE release bridge](../AdaptiveODELowerBound/Release/Bridge.lean) |
| A value call, its inverse and its controlled forms cost at most the Boolean membership queries of the call, two per value call and none per location call (Section `odel:sec:main`) | `AdaptiveODELowerBound.Access.implementsOn_callFamily`, `AdaptiveODELowerBound.Access.implementsOn_calls_joint`, `AdaptiveODELowerBound.Access.implementsOn_calls_hom`, `AdaptiveODELowerBound.Access.admissible_callFamily_spec` | [Call forms](../AdaptiveODELowerBound/Access/Control.lean) |
| ODE lower bounds for adaptive solvers and retry protocols over the released constant-coefficient ODE solver's oracle, on the `g = 1` Hamiltonian families, Lemma 7.5 (`odel:lem:herald`; applied to `ode:thm:main`) | `ConstantODELowerBound.Herald.herald_max_const_tree`, `ConstantODELowerBound.Herald.herald_max_const_retry` | [Constant-coefficient ODE lower bound](../ConstantODELowerBound/Herald.lean) |
| The same on the positive semidefinite families, Theorem 7.6 (`odel:thm:psd`; applied to `ode:thm:main`) | `ConstantODELowerBound.Psd.psd_max_const_tree`, `ConstantODELowerBound.Psd.psd_max_const_retry` | [Constant-coefficient PSD ODE lower bound](../ConstantODELowerBound/Psd.lean) |
| The released constant-coefficient ODE solver as an algorithm over its oracle, and lower and released upper bounds at its runs on those families (`ode:thm:main` with `odel:lem:herald` and `odel:thm:psd`) | `ConstantODELowerBound.Solver.constProtocol_of_certificate`, `ConstantODELowerBound.Solver.exists_constProtocol`, `ConstantODELowerBound.Runs.herald_const_bounds`, `ConstantODELowerBound.Runs.psd_const_bounds`, `ConstantODELowerBound.Instances.herald_const_bracket` | [Constant-coefficient ODE runs](../ConstantODELowerBound/Runs.lean) |
| Positive semidefinite ODE precision lower bound for adaptive solvers over both released ODE solvers' physical oracles, with inverse, controlled and controlled-inverse calls, Theorem 7.6 (`odel:thm:psd`) | `PhysicalODELowerBound.Mesh.psd_mesh`, `PhysicalODELowerBound.Const.psd_const` | [Physical-oracle PSD ODE lower bound](../PhysicalODELowerBound/Mesh/Psd.lean) |
| Inhomogeneous time-dependent and source-free ODE lower bounds for adaptive solvers over the released general-mesh ODE solver's physical oracle with controlled calls, Theorem 7.3 and Proposition 7.4 (`odel:thm:joint`, `odel:rem:homogeneous`), and the padded joint families | `PhysicalODELowerBound.Mesh.joint_witness_mesh`, `PhysicalODELowerBound.Mesh.hom_witness_mesh`, `PhysicalODELowerBound.Mesh.joint_common_dimension_mesh` | [Physical-oracle joint ODE lower bound](../PhysicalODELowerBound/Mesh/Joint.lean) |
| Dissipative-ODE query lower bound for adaptive solvers over the released general-mesh ODE solver's physical oracle with controlled calls, in family form, padded, in one common dimension or on a qubit register, Theorem 7.1 (`odel:thm:combined`) | `PhysicalODELowerBound.Mesh.combined_mesh`, `PhysicalODELowerBound.Mesh.combined_common_dimension_mesh`, `PhysicalODELowerBound.Mesh.combined_qubit_register_mesh` | [Physical-oracle ODE lower bound](../PhysicalODELowerBound/Mesh/Combined.lean) |
| ODE lower bounds on the `g = 1` Hamiltonian families for adaptive solvers over both released ODE solvers' physical oracles with controlled calls, with known zero padding, and over the constant-coefficient solver's oracle in one common dimension or on a qubit register, Lemma 7.5 (`odel:lem:herald`, eq. `odel:eq:hsbound`) | `PhysicalODELowerBound.Mesh.herald_witness_mesh`, `PhysicalODELowerBound.Const.herald_witness_const`, `PhysicalODELowerBound.Const.herald_common_dimension_const`, `PhysicalODELowerBound.Const.herald_qubit_register_const` | [Constant-coefficient physical-oracle ODE lower bound](../PhysicalODELowerBound/Const/Herald.lean) |
| Controlled and controlled-inverse calls of the released general-mesh ODE solver's physical oracle cost at most the Boolean membership queries of the call's label, and the call forms of both released ODE solvers' physical oracles have the label's search-weight growth (Section `odel:sec:main`) | `PhysicalODELowerBound.Access.implementsOn_mesh_calls`, `PhysicalODELowerBound.Access.searchGrowth_mesh_calls`, `PhysicalODELowerBound.Const.searchGrowth_const_calls` | [Physical-oracle controlled calls](../PhysicalODELowerBound/Access/MeshBoolean.lean) |
| Deferral of measurements (purification and deferred measurement in the proofs of `hsl:lem:precision` and `qlsl:lem:xor`): every measured algorithm over unitary oracle labels (calls and input-independent instruments with finitely many outcomes on one workspace: mid-run and multi-outcome measurements, classical control, randomness, resets of finite-dimensional registers) is one unitary program over record-selected calls with the same success probability and, the records discarded, the same output, with at most its worst-case number of counted calls over all transcripts; the adaptive protocols of the package are measured algorithms on finite-dimensional workspaces | `DeferredMeasurementLowerBounds.Deferral.deferral`, `DeferredMeasurementLowerBounds.Model.ofTree`, `DeferredMeasurementLowerBounds.Model.successMass_ofTree`, `DeferredMeasurementLowerBounds.Model.worstCost_ofTree`, `DeferredMeasurementLowerBounds.NonVacuity.deferral_midRun` | [Deferral theorem](../DeferredMeasurementLowerBounds/Deferral/Theorem.lean) |
| Hamiltonian-simulation (also for the class of `hs:thm:time` over its coherent sampled-time oracles), linear-system and dissipative-ODE query lower bounds for algorithms with measurements inside a run, with the constants of the adaptive forms, Theorems 5.1, 9.1 and 7.1 (`hsl:thm:main`, `qlsl:thm:main`, `odel:thm:combined`) | `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`, `DeferredMeasurementLowerBounds.Corollaries.main_max_measured_access`, `DeferredMeasurementLowerBounds.Corollaries.lower_bound_sharp_measured`, `DeferredMeasurementLowerBounds.Corollaries.combined_measured`, `DeferredMeasurementLowerBounds.Corollaries.measuredForces_of_treeForces`, `DeferredMeasurementLowerBounds.NonVacuity.released_linear_system_measured` | [Deferred-measurement statement guide](../DeferredMeasurementLowerBounds/Statements.lean) |
| Query lower bound `Ω(√N)` of unitary implementation at every fixed error `ε₀ < 1/2`, for algorithms with measurements inside a run over the entry oracle and its inverse that succeed with probability one with output within trace distance `ε₀` of `U_m ψ` for every input `ψ`: `(1 - 2√(ε₀(1 - ε₀))) √(N - 1) ≤ 2Q` (`hs:cor:unitary`, last sentence) | `DeferredMeasurementLowerBounds.Corollaries.entry_count_ge_measured`, `DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured`, `DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured_heralded`, `DeferredMeasurementLowerBounds.NonVacuity.released_unitary_measured` | [Measured unitary lower bound](../DeferredMeasurementLowerBounds/Corollaries/Unitary.lean) |
| Dissipative-ODE lower bounds for algorithms with measurements inside a run over the released general-mesh ODE solver's physical oracle and its call forms (plain, inverse, controlled and controlled-inverse calls), with the constants of the adaptive forms, with the padded joint, combined and `g = 1` families and the joint and combined families in one common dimension or on a qubit register, Theorems 7.1, 7.3 and 7.6, Proposition 7.4 and Lemma 7.5 (`odel:thm:combined`, `odel:thm:joint`, `odel:rem:homogeneous`, `odel:lem:herald`, `odel:thm:psd`; applied to `ode:thm:time`, Section `odel:sec:main`) | `ReleasedODESolverLowerBounds.Mesh.measuredMeshForces_of_meshForces`, `ReleasedODESolverLowerBounds.Mesh.combined_max_release_measured_mesh`, `ReleasedODESolverLowerBounds.Mesh.combined_common_dimension_measured_mesh`, `ReleasedODESolverLowerBounds.Mesh.joint_witness_measured_mesh`, `ReleasedODESolverLowerBounds.Mesh.hom_witness_measured_mesh`, `ReleasedODESolverLowerBounds.Mesh.herald_witness_measured_mesh`, `ReleasedODESolverLowerBounds.Mesh.psd_measured_mesh` | [Measured general-mesh ODE lower bounds](../ReleasedODESolverLowerBounds/Mesh/Corollaries.lean) |
| The same over the released constant-coefficient ODE solver's physical oracle and its call forms, on the `g = 1` families also padded, in one common dimension or on a qubit register, and on the positive semidefinite families, Lemma 7.5 and Theorem 7.6 (`odel:lem:herald`, eq. `odel:eq:hsbound`, `odel:thm:psd`; applied to `ode:thm:main`) | `ReleasedODESolverLowerBounds.Const.measuredConstForces_of_constForces`, `ReleasedODESolverLowerBounds.Const.herald_max_release_measured_const`, `ReleasedODESolverLowerBounds.Const.psd_max_release_measured_const`, `ReleasedODESolverLowerBounds.Const.herald_common_dimension_measured_const` | [Measured constant-coefficient ODE lower bounds](../ReleasedODESolverLowerBounds/Const/Corollaries.lean) |
| Runs of the released general-mesh ODE solver on the positive semidefinite and homogeneous families at split bounds `(η_H, η_D)`, with lower and released upper bounds side by side, and runs of both released ODE solvers as measured algorithms with the same worst-case counts (on a family with an input, all of whose inputs are solvable) (`ode:thm:time` with `odel:thm:psd` and `odel:rem:homogeneous`) | `ReleasedODESolverLowerBounds.Runs.exists_meshProtocol`, `ReleasedODESolverLowerBounds.Runs.psd_meshRun_bracket`, `ReleasedODESolverLowerBounds.Runs.hom_meshRun_bracket`, `ReleasedODESolverLowerBounds.Runs.MeshRun.exists_measuredSolver`, `ReleasedODESolverLowerBounds.Runs.constRun_exists_measuredSolver` | [Released general-mesh ODE runs](../ReleasedODESolverLowerBounds/Runs/Instances.lean) |
| Parity-amplitude reductions (remark in Section 5, after `hsl:cor:power`) | `LowerBoundRemarks.ParityAmplitude.matrix_exp_correlation_le` | [Parity remark](../LowerBoundRemarks/ParityAmplitude.lean) |
| Padding the Hamiltonian-simulation hard families to a common dimension (last clause of `hsl:thm:main` and the end of its proof) | `LowerBoundRemarks.HamiltonianPadding.main_max_common_dimension` | [Hamiltonian padding](../LowerBoundRemarks/HamiltonianPadding.lean) |
| Padding the hard linear systems to any larger dimension (remark after `qlsl:thm:main`) | `LowerBoundRemarks.LinearSystemPadding.lower_bound_common_dimension` | [Linear-system padding](../LowerBoundRemarks/LinearSystemPadding.lean) |
| Gate-efficient sparse simulation with native oracle implementations, before finite-set synthesis (`hs:thm:gates`) | `SparseHamiltonian.GateNative.native_simulation` | [Native gate-level endpoint](../GateEfficientNative/Hamiltonian/Theorem.lean) |
| Sparse form of the native gate count, before finite-set synthesis (`hs:eq:gate-binary`) | `SparseHamiltonian.GateNative.native_sparse_counts` | [Native gate-level corollaries](../GateEfficientNative/Corollaries.lean) |
| Gate-efficient sparse simulation from binary sparse oracles, with constructed entry decoding, angle arithmetic, compute circuit and `U_J`, before finite-set synthesis (`hs:thm:gates`, time-independent) | `SparseHamiltonian.GateBinary.binary_simulation` | [Binary-data gate-level endpoint](../GateEfficientBinary/Sparse/Simulation.lean) |
| Gate budget from binary sparse oracles, before finite-set synthesis (`hs:eq:gate-binary`) | `SparseHamiltonian.GateBinary.binary_simulation_budget` | [Binary-data gate budget](../GateEfficientBinary/Sparse/Budget.lean) |
| Gate-efficient time-dependent sparse simulation from time-indexed binary sparse oracles, uniform mesh, before finite-set synthesis (`hs:thm:time` with the circuit of `hs:thm:gates`) | `SparseHamiltonian.GateBinary.binary_time_simulation` | [Time-dependent binary-data gate-level endpoint](../GateEfficientBinaryTime/Simulation.lean) |
| Gate budget from time-indexed binary sparse oracles, uniform mesh, with the rescaled sparse parameters of `hs:thm:time`, before finite-set synthesis (`hs:thm:time` with the circuit of `hs:thm:gates`) | `SparseHamiltonian.GateBinary.binary_time_simulation_budget` | [Time-dependent binary-data gate budget](../GateEfficientBinaryTime/Budget.lean) |
| Gate-efficient dissipative ODE with native oracle implementations, constant coefficients (`ode:thm:gates`) | `SparseHamiltonian.GateNative.native_ode_solver` | [Native gate-level ODE endpoint](../GateEfficientNative/ODE/Constant.lean) |
| Gate-efficient dissipative ODE with native oracle implementations, time-dependent coefficients, uniform mesh (`ode:thm:gates`) | `SparseHamiltonian.GateNative.native_ode_time_solver` | [Native time-dependent gate-level ODE endpoint](../GateEfficientNative/ODE/Time.lean) |
| Gate-efficient dissipative ODE from binary sparse oracles, constant coefficients, with constructed `U_J`, compute circuit, entry decoding, angle arithmetic and clock promises, before finite-set synthesis (`ode:thm:gates`; explicit worst-case gate count underlying `ode:eq:gate-main`) | `SparseHamiltonian.GateBinaryODE.binary_ode_solver`, `SparseHamiltonian.GateBinaryODE.binary_ode_counts`, `SparseHamiltonian.GateBinaryODE.binary_ode_gate_count` | [Binary-data gate-level ODE endpoint](../GateEfficientBinaryODE/Solver.lean) |
| Gate-efficient dissipative ODE from binary sparse oracles over a finite gate set, constant coefficients, synthesis as a hypothesis (`ode:thm:gates`, without its per-trial claim) | `SparseHamiltonian.GateBinaryODE.binary_ode_solver_synth` | [Finite-gate-set binary-data ODE endpoint](../GateEfficientBinaryODE/Synth.lean) |
| Gate-efficient dissipative ODE from time-indexed binary sparse oracles, time-dependent coefficients on a uniform mesh, with constructed `U_J`, compute circuit, entry decoding, angle arithmetic (with a slot comparator for the masked source branches) and clock promises at every label and slot, before finite-set synthesis (`ode:thm:gates`, time-dependent part; explicit worst-case gate count underlying `ode:eq:gate-main`) | `SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver`, `SparseHamiltonian.GateBinaryODETime.binary_ode_time_counts`, `SparseHamiltonian.GateBinaryODETime.binary_ode_time_gate_count` | [Time-dependent binary-data gate-level ODE endpoint](../GateEfficientBinaryODETime/Solver.lean) |
| Gate-efficient dissipative ODE from time-indexed binary sparse oracles over a finite gate set, time-dependent coefficients, synthesis as a hypothesis (`ode:thm:gates`, time-dependent part, without its per-trial claim) | `SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver_synth` | [Finite-gate-set time-dependent binary-data ODE endpoint](../GateEfficientBinaryODETime/Synth.lean) |
| Gate-efficient dissipative ODE over a finite gate set with the per-trial claim, native implementations, constant and time-dependent coefficients; only the preparation synthesised, exact zero tests and actual inverse, with synthesis, an adjoint-closed gate set and the zero-test gates as hypotheses (`ode:thm:gates`) | `SparseHamiltonian.GateSynthTrials.native_ode_solver_trials`, `SparseHamiltonian.GateSynthTrials.native_ode_time_solver_trials` | [Synthesised-trial ODE endpoints](../GateEfficientSynthesisTrials/Solver.lean) |
| The same from binary and time-indexed binary sparse oracles (`ode:thm:gates`) | `SparseHamiltonian.GateSynthTrials.binary_ode_solver_trials`, `SparseHamiltonian.GateSynthTrials.binary_ode_time_solver_trials` | [Synthesised-trial binary-data ODE endpoints](../GateEfficientSynthesisTrials/Binary.lean) |
| Asymptotic gate, call and qubit budgets of the dissipative solvers from binary and time-indexed binary sparse oracles with the public rescaling (`ode:eq:gate-main`, `ode:eq:gate-space`; `d ≤ 4096 q`, `J ≤ 60 q ℓ`) | `SparseHamiltonian.GateODEBudget.binary_ode_budget`, `SparseHamiltonian.GateODEBudget.binary_ode_time_budget`, `SparseHamiltonian.GateODEBudget.binary_ode_sizes`, `SparseHamiltonian.GateODEBudget.binary_ode_time_sizes` | [Binary-data ODE budget](../GateEfficientODEBudget/Constant.lean) |
| The same as a cubic polynomial in the register words, and over a finite gate set with the per-trial claim | `SparseHamiltonian.GateODEBudget.binary_ode_budget_words`, `SparseHamiltonian.GateODEBudget.binary_ode_time_budget_words`, `SparseHamiltonian.GateODEBudget.binary_ode_budget_trials`, `SparseHamiltonian.GateODEBudget.binary_ode_time_budget_trials` | [Word form](../GateEfficientODEBudget/Words.lean) |
| `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget `𝔟` of `ode:eq:gate-word-budget` for the dissipative solvers from binary and time-indexed binary sparse oracles, for fixed-point public parameters of bit length at most `b_data` (`P(x) = 3·10¹¹ (x+1)³`, `C = 10²⁰`; register words at most `300 (𝔟+1)`) | `SparseHamiltonian.GateBitBudget.binary_ode_budget_bits`, `SparseHamiltonian.GateBitBudget.binary_ode_time_budget_bits`, `SparseHamiltonian.GateBitBudget.binary_ode_time_budget_bits_user`, `SparseHamiltonian.GateBitBudget.words_le`, `SparseHamiltonian.GateBitBudget.wordsT_le` | [Bit-length ODE budget](../GateEfficientBitBudget/Constant.lean) |
| The same over a finite gate set with the per-trial claim | `SparseHamiltonian.GateBitBudget.binary_ode_budget_trials_bits`, `SparseHamiltonian.GateBitBudget.binary_ode_time_budget_trials_bits` | [Bit-length ODE budget over a finite gate set](../GateEfficientBitBudget/Synth.lean) |
| `hs:eq:gate-binary` in `b_data`, `log(N+1)` and `log((Q_base+1)/ε)` from binary sparse oracles, and from time-indexed binary sparse oracles with `q = √s t + √(st log(2/ε)) + log(2/ε)` in place of `Q_base` and `log₂(M+1)` added (`poly(x) = 10¹⁵ (x+1)³`) | `SparseHamiltonian.GateBitBudget.binary_simulation_bits`, `SparseHamiltonian.GateBitBudget.binary_time_simulation_bits` | [Bit-length Hamiltonian budget](../GateEfficientBitBudget/HamiltonianBudget.lean) |
| `hs:eq:gate-binary` in the bit lengths after finite-set synthesis, synthesis as a hypothesis | `SparseHamiltonian.GateBitBudget.binary_simulation_budget_synth_bits`, `SparseHamiltonian.GateBitBudget.binary_time_simulation_budget_synth_bits` | [Bit-length Hamiltonian budget after synthesis](../GateEfficientBitBudget/SynthHamiltonian.lean) |
| Gate-efficient sparse simulation over a finite gate set, native oracle implementations, time-independent, every real time and time-dependent on a uniform mesh, with single-qubit synthesis and the decomposition of controlled gates as hypotheses (`hs:thm:gates`; the time-dependent form is `hs:thm:time` with the circuit of `hs:thm:gates`, beyond the paper) | `SparseHamiltonian.GateSynth.native_simulation_synth`, `SparseHamiltonian.GateSynth.native_simulation_signed_synth`, `SparseHamiltonian.GateSynth.native_time_simulation_synth` | [Finite-gate-set native endpoints](../GateEfficientSynthesis/Hamiltonian.lean) |
| Gate-efficient sparse simulation over a finite gate set from binary and time-indexed binary sparse oracles, synthesis as a hypothesis (`hs:thm:gates`; from time-indexed data `hs:thm:time` with the circuit of `hs:thm:gates`, beyond the paper) | `SparseHamiltonian.GateSynth.binary_simulation_synth`, `SparseHamiltonian.GateSynth.binary_time_simulation_synth` | [Finite-gate-set binary-data endpoints](../GateEfficientSynthesis/Binary.lean) |
| Gate budgets over a finite gate set from binary and time-indexed binary sparse oracles, synthesis as a hypothesis (bounds of the form of `hs:eq:gate-total`, with the private calls synthesised too; `hs:eq:gate-binary` after synthesis) | `SparseHamiltonian.GateSynth.binary_simulation_budget_synth`, `SparseHamiltonian.GateSynth.binary_time_simulation_budget_synth` | [Finite-gate-set binary-data budgets](../GateEfficientSynthesis/Binary.lean) |
| Gate-efficient dissipative ODE over a finite gate set, constant and time-dependent coefficients, synthesis as a hypothesis (a partial formalisation, under this package's format hypotheses, of the finite-set statement of `ode:thm:gates`, without its per-trial claim) | `SparseHamiltonian.GateSynth.native_ode_solver_synth`, `SparseHamiltonian.GateSynth.native_ode_time_solver_synth` | [Finite-gate-set ODE endpoints](../GateEfficientSynthesis/ODESolver.lean) |
| The synthesis hypothesis from single-qubit synthesis and the decomposition of controlled gates | `SparseHamiltonian.GateSynth.Synthesis.of_parts`, `SparseHamiltonian.GateSynth.of_parts_len_le` | [Synthesis hypothesis](../GateEfficientSynthesis/Parts.lean) |
| Selective finite-gate-set synthesis: the gates of supplied circuits over the gate set retained verbatim, only the other exact gates synthesised, at most `N_keep + K L(δ/(K+1))` gates for `K` synthesised occurrences and error `δ`, every primitive call kept, literal reverse-adjoints over an adjoint-closed gate set | `SparseHamiltonian.GateSelective.selBudget_spec`, `SparseHamiltonian.GateSelective.selBudget_approxOn`, `SparseHamiltonian.GateSelective.selBudget_gates_log`, `SparseHamiltonian.GateSelective.selC_retained`, `SparseHamiltonian.GateSelective.selC_inv_gateOf` | [Selective compiler](../GateEfficientSelective/Compiler.lean) |
| Gate-efficient sparse simulation over a finite gate set with a supplied finite-set circuit for the controlled private Cayley operation, its inverse the literal reverse-adjoint (`hs:thm:gates`, `hs:eq:gate-Gzero`, `hs:eq:gate-total`): exactly `6d` times its calls, at most `6d G_C + G₀(c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates with `G₀ = 200(d+1)(a+m+r+1) + 84 d C_J` independent of the supplied circuit, the `2a + 3m + 6r + 3` circuit wires and the `\|Z\| + bT + bP + A + 3` private and work wires of the supplied circuit besides the system and the synthesis ancillas, full-output error `ε`; every real time and, beyond the paper, time-dependent on a uniform mesh (`hs:thm:time` with this circuit); the circuit from the native data | `SparseHamiltonian.GateSelective.sel_simulation`, `SparseHamiltonian.GateSelective.sel_simulation_signed`, `SparseHamiltonian.GateSelective.sel_time_simulation`, `SparseHamiltonian.GateSelective.sel_simulation_native`, `SparseHamiltonian.GateSelective.privSel_spec` | [Selective Hamiltonian endpoints](../GateEfficientSelective/HamSim.lean) |
| Gate-efficient dissipative ODE over a finite gate set with the supplied source circuits retained (`ode:thm:gates`, `ode:eq:gate-main`, `ode:eq:gate-space`): `G_src` linear and outside every logarithm, `A_src` through the zero tests and the register, with the per-trial claim; natively for constant and time-dependent coefficients and on branch-dependent meshes with a positive source quadrature, and from binary data in `𝔟` (for constant coefficients at most `40g(G_src + 2·10¹⁸q*(𝔟+1)³(64c₁(𝔟+1)+c₀+1)) + 20g(4(3·10¹¹(𝔟+1)³ + 2\|Zs\| + \|Xa\|) + 3)` gates and `7·10¹¹(𝔟+1)³ + 4\|Zs\| + 2\|Xa\|` qubits; `80g`, `40g` for time-dependent coefficients; `𝔟 + μ` and the node-program gates for computed source nodes) | `SparseHamiltonian.GateSelective.native_ode_solver_sel`, `SparseHamiltonian.GateSelective.native_ode_time_solver_sel`, `SparseHamiltonian.GateSelective.native_time_sel_outcomeB`, `SparseHamiltonian.GateSelective.binary_ode_budget_sel`, `SparseHamiltonian.GateSelective.binary_ode_time_budget_sel`, `SparseHamiltonian.GateSelective.binary_nodes_budget_sel` | [Selective ODE budgets](../GateEfficientSelective/ODEBudget.lean) |
| Gate-efficient sparse simulation with the manuscript's schedule (`hs:thm:gates` with `hs:eq:gate-schedule` and `hs:eq:gate-clocks`): `k = ⌈4W/Q + log₂(4096/ε)⌉`, `d = k(b_av - 1)`, `b_av = 32Q`, for integer `Q` (`k(⌈32Q⌉ - 1)` in general), `M = 2^{m_slot}` the least power of two at least `max{2, 4αT, (αT)^{3/2}/√(3ε)}`, filter error `ε/8` and Cayley error `ε/4` (the sharp local error `w³/12`); exactly `6d` private calls, full-output error `ε/2` with exact gates and `ε` over a finite gate set with `ξ = ε/(24d)` and synthesis `ε/4`; beyond the paper, the time-dependent form (`hs:thm:time` with this circuit) on the mesh `hs:eq:timegrid` with the constants of `hs:eq:timedisc`; Lemma `hs:lem:abstract` for every real time with exactly the `6(32Q - 1)⌈4W/Q + log₂(4096/ε)⌉` calls of `hs:eq:explicitcount` (at most `3880 (W + Q log(1/ε))`) and full-output error `ε/2` | `SparseHamiltonian.GateSchedule.gate_efficient_simulation_ms`, `SparseHamiltonian.GateSchedule.abstract_simulation_ms`, `SparseHamiltonian.GateSchedule.abstract_simulation_ms_explicit`, `SparseHamiltonian.GateSchedule.sel_simulation_ms`, `SparseHamiltonian.GateSchedule.sel_simulation_ms_native`, `SparseHamiltonian.GateSchedule.gate_efficient_time_simulation_ms`, `SparseHamiltonian.GateSchedule.sel_time_simulation_ms`, `SparseHamiltonian.GateSchedule.depthMs_admissible`, `SparseHamiltonian.GateSchedule.hamiltonian_cayley_error_sharp` | [Manuscript schedule](../GateEfficientSchedule/Endpoint.lean) |
| The explicit accounting of `hs:thm:gates` (eqs. `hs:eq:gate-known`, `hs:eq:gate-Gzero`, `hs:eq:gate-total`, the manuscript's schedule) on sparse access of general size with any public decoder, with the controlled private circuit constructed (item B2 of the v2.8 additions): the native private operation of the normalised padded data with every padded oracle call implemented from the supplied oracles, its native implementation with an arithmetic of the padded data, compiled selectively once over the gate set; its promise derived from the native identity of the padded data, the oracle implementation and the arithmetic interface `comp_rotArith` of the decoder (no clock or Cayley correctness assumed); exactly `6d` private calls, `12 d` times the at most `3(2 + 2 + 1)` calls of the compute circuit, the private gates `G_C ≤ G_P(1 + c₁ log((G_P+1)/δ) + c₀)` with `G_P = 2\|V'\| + 2\|arith\| + 2b_P + b_T + 1`, the known gates `G₀` and their synthesis, the qubit count with the `k + 1` system wires separate, full-output error `ε` with an untouched reference, one circuit fixed before the instance; the schedule has `s' = 2^⌈log₂ s⌉` in place of `s` with the Hadamard boundary circuit, and the original `s` (`α = η√s/γ`, `Q = ⌈max{1, γ√s}⌉`, `d`, `m`, `r`, `ξ = ε/(24d)` at `s`) with a supplied boundary circuit preparing the boundary state of the `s` original slots (`UJPrep`, its `C_J` gates charged; the uniform-range circuit is not constructed) on the padded data restricted to the original slots | `SparseHamiltonian.SparseGateAccounting.sparse_gate_original`, `SparseHamiltonian.SparseGateAccounting.sparse_gate_original_signed`, `SparseHamiltonian.SparseGateAccounting.sparse_gate_total_s`, `SparseHamiltonian.SparseGateAccounting.R1bin_boundary_of`, `SparseHamiltonian.SparseGateAccounting.padUJ_prep`, `SparseHamiltonian.SparseGateAccounting.sparse_gate_constructed`, `SparseHamiltonian.SparseGateAccounting.sparse_gate_native`, `SparseHamiltonian.SparseGateAccounting.sparse_gate_native_signed`, `SparseHamiltonian.SparseGateAccounting.privCirc_privOK`, `SparseHamiltonian.SparseGateAccounting.privCirc_spec`, `SparseHamiltonian.SparseGateAccounting.exists_arith`, `SparseHamiltonian.SparseGateAccounting.sparse_gate_total` | [Sparse gate accounting](../SparseGateAccounting/Statements.lean) |
| Gate-efficient time-dependent sparse simulation under the integrated sample-error certificate on the uniform slots, against the propagators of integrable Hermitian paths and of piecewise paths: exact gates, native implementations, time-indexed binary sparse oracles (also with the rescaled sparse parameters) and finite gate sets (`hs:thm:time` with the circuit of `hs:thm:gates`, beyond the paper, with the certificate of the paragraph after `hs:thm:time`) | `SparseHamiltonian.GateMesh.time_simulation_certified`, `SparseHamiltonian.GateMesh.native_time_simulation_certified`, `SparseHamiltonian.GateMesh.binary_time_simulation_certified`, `SparseHamiltonian.GateMesh.binary_time_simulation_budget_certified`, `SparseHamiltonian.GateMesh.binary_time_simulation_budget_certified_synth` | [Certified time-dependent gate-level endpoints](../GateEfficientMesh/Exact.lean) |
| The same on nonuniform meshes with breakpoints, by uniform refinement of the clock, beyond the paper, which gives no time-dependent gate theorem for Hamiltonian simulation (slot `k` reads the samples of the interval containing `kT/2^m`; rounding condition `4 M α T ≤ ε 2^m`, for native implementations `8 M α T ≤ ε 2^m`, for binary data `8 M τ' ≤ ε 2^m` with the rescaled time `τ'`) | `SparseHamiltonian.GateMesh.time_simulation_mesh`, `SparseHamiltonian.GateMesh.native_time_simulation_mesh`, `SparseHamiltonian.GateMesh.binary_time_simulation_mesh`, `SparseHamiltonian.GateMesh.binary_time_simulation_budget_mesh`, `SparseHamiltonian.GateMesh.binary_time_simulation_mesh_synth` | [Mesh time-dependent gate-level endpoints](../GateEfficientMesh/BinaryMesh.lean) |
| Gate-efficient dissipative ODE, time-dependent coefficients, under an integrated certificate on the uniform slots (`ode:thm:gates`: "a certificate for the same uniform meshes suffices"), and on nonuniform meshes with breakpoints by uniform refinement of the clock | `SparseHamiltonian.GateMesh.ODE.ode_time_solver_certified`, `SparseHamiltonian.GateMesh.ODE.ode_time_solver_mesh`, `SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified`, `SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified`, `SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh` | [Certified gate-level ODE endpoints](../GateEfficientMesh/ODE/Exact.lean) |
| The same over a finite gate set with the per-trial claim, also with the explicit budget of `ode:eq:gate-main` and `ode:eq:gate-space` | `SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified_trials`, `SparseHamiltonian.GateMesh.ODE.binary_ode_time_budget_certified_trials`, `SparseHamiltonian.GateMesh.ODE.binary_ode_time_budget_mesh_trials` | [Finite-gate-set certified ODE endpoints](../GateEfficientMesh/ODE/Trials.lean) |
| Gate-efficient coherent selection on branch-dependent meshes, exact gates (`ode:lem:gate-select`): for an arbitrary label register, with start times `v_z ∈ [0, T]` and frequencies `k_z ∈ [-R, R]`, the released slot-selected circuit for the common normalised time `αT`, whose private operation for label `z` carries the step `(T - v_z)/2^m` of the mesh of branch `z`, makes exactly `6d` private calls and `12d` calls of `U_J` or `U_J†` with at most `200 (d+1)(a+m+r+1)` gates, no count depending on the labels, and is within `ε` of the controlled direct sum of the propagators of `H(v_z + t) + k_z D(v_z + t)` over `[0, T - v_z]`; the inverse with the same counts; explicit data meeting every hypothesis; for `T > 0`, with the package's filter degree `fDeg` and subdivision condition `steps τ (ε/6) ≤ 2^m` in place of eq. `ode:eq:gate-select-schedule` and the first three bounds of eq. `ode:eq:gate-select-mesh`, and with the clock promises of the private operations as hypotheses | `SparseHamiltonian.GateSelect.gate_select`, `SparseHamiltonian.GateSelect.gate_select_inverse`, `SparseHamiltonian.GateSelect.nv_select` | [Coherent selection on branch-dependent meshes](../GateEfficientSelect/Lemma.lean) |
| Gate-efficient dissipative ODE, time-dependent coefficients, on branch-dependent meshes with a positive source quadrature, exact gates and native implementations (`ode:thm:gates`, time-dependent part, under the source certificate of `ode:eq:gate-source-certificates`): the released protocol, counts and outcome, every forcing branch on its own mesh of `2^m` slots from its node to `T`; the certificate for the left-endpoint nodes from Lipschitz bounds; explicit data meeting every hypothesis | `SparseHamiltonian.GateSelect.ODE.solverB`, `SparseHamiltonian.GateSelect.ODE.native_ode_time_solverB`, `SparseHamiltonian.GateSelect.ODE.quad_leftEndpoint`, `SparseHamiltonian.GateSelect.ODE.nvB_outcome` | [Branch-dependent ODE endpoint](../GateEfficientSelect/ODE/Theorem.lean) |
| The sufficient positive source quadrature of the proof of `ode:thm:gates` for time-dependent forcing: with `m ≥ max{1, T² C_b/(2νB)}` left-endpoint nodes and `C_b = Λ b_* + L_b`, the source certificate of `ode:eq:gate-source-certificates` is at most `νB` and the quadrature mass `B_m` is within `T² L_b/(2m) ≤ νB` of `B`, so `(1 - ν)B ≤ B_m ≤ (1 + ν)B` and `0 < B_m ≤ 2B`; the Lipschitz bound `C_b` of `v ↦ U(T, v) b(v)` with homogeneous solutions; the solver on branch-dependent meshes with this quadrature, exact gates and native implementations, with the budget fields from the paper's parameters; both constants attained for a zero generator and a ramp forcing; explicit data meeting every hypothesis | `SparseHamiltonian.GateQuad.paper_quadrature`, `SparseHamiltonian.GateQuad.cert_left`, `SparseHamiltonian.GateQuad.flow_lipschitz`, `SparseHamiltonian.GateQuad.solverL`, `SparseHamiltonian.GateQuad.native_time_outcomeL`, `SparseHamiltonian.GateQuad.budget_disc_paper`, `SparseHamiltonian.GateQuad.sharp_cert`, `SparseHamiltonian.GateQuad.nvL_outcome` | [Sufficient source quadrature](../GateEfficientQuadrature/Paper.lean) |
| Coherent selection from binary data (`ode:lem:gate-select` with `ode:eq:gate-select-gates`) and the time-dependent part of `ode:thm:gates` from time-indexed binary sparse oracles on branch-dependent meshes: the lemma under the paper's integrated sample-error certificate `δ/16` and mesh condition `8 L_* T² ≤ δ M` with exact gates, natively under `δ/32` and `16 L_* T² ≤ δ M`; for binary data and the dyadic labels of the dissipative solver (`Q = width(4s, γ)`, so `4s` in place of the lemma's `p = 2s`) the branch address `v_z + r u_z/M` and the branch scale computed from the label and the slot index by a register program, the clock promises proved with label-independent constants, `G_sel ≤ 393500 d (𝔴+1)³` and `A_sel ≤ 4096 (𝔴+1)³ + 3`, and the whole selection circuit at `δ = 4ν` within `11·10¹² (d+1)(𝔟+1)³` gates; the native, finite-gate-set and per-trial solvers for positive source quadratures on the `2^m` dyadic nodes, with `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`; explicit data meeting every hypothesis, where the uniform sample bound fails | `SparseHamiltonian.GateBinarySelect.gate_select_certified`, `SparseHamiltonian.GateBinarySelect.native_gate_select`, `SparseHamiltonian.GateBinarySelect.binary_native_gate_select`, `SparseHamiltonian.GateBinarySelect.binary_select_lemma_bits`, `SparseHamiltonian.GateBinarySelect.binary_select_solver`, `SparseHamiltonian.GateBinarySelect.binary_select_solver_trials`, `SparseHamiltonian.GateBinarySelect.binary_select_budget_bits`, `SparseHamiltonian.GateBinarySelect.nv_select_outcome` | [Binary coherent selection](../GateEfficientBinarySelect/SelectBinary.lean) |
| The time-dependent part of `ode:thm:gates` from time-indexed binary sparse oracles with coherently computed source nodes: the nodes `word u · T/2^μ` of any node program (classical reversible gates computing `μ`-bit node words from the labels, its gates counted), the branch addresses computed from the node words, the samples read on a data grid of `2^nd ≤ 2^(μ+m)` points with the time-address rounding in the integrated represented-sample error, energy bounds only at the samples read; native, finite-gate-set and per-trial solvers, and `ode:eq:gate-main`, `ode:eq:gate-space` in `q*`, the register words and `𝔟 + μ`; the copy (dyadic) and midpoint node programs and explicit data meeting every hypothesis | `SparseHamiltonian.GateBinaryNodes.binary_nodes_solver`, `SparseHamiltonian.GateBinaryNodes.binary_nodes_counts`, `SparseHamiltonian.GateBinaryNodes.binary_nodes_solver_trials`, `SparseHamiltonian.GateBinaryNodes.binary_nodes_budget`, `SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_bits`, `SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_trials_bits`, `SparseHamiltonian.GateBinaryNodes.nv_nodes_outcome` | [Computed source nodes](../GateEfficientBinaryNodes/NodeSolver.lean) |
| The constant-forcing source preparation of `ode:thm:gates` (`ode:eq:gate-constant-source`) for the time-dependent solvers (the constant-coefficient solver already has it): one rotation and `m` controlled Hadamard gates prepare the weights of the `2^m` left-endpoint nodes, the supplied initial and forcing loading circuits are used once each, `G_src = G_{x₀} + G_b + 2(m+1)`, for the released common-mesh solver and for the solver on branch-dependent meshes; the integrated sample-error certificate for the generator samples of the solvers on branch-dependent meshes (`κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`), natively and from binary data with energy bounds only at the samples read | `SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const`, `SparseHamiltonian.GateBinaryNodes.binary_ode_time_solver_const`, `SparseHamiltonian.GateBinaryNodes.const_source_counts`, `SparseHamiltonian.GateBinaryNodes.WpConst_srcAmp`, `SparseHamiltonian.GateBinaryNodes.native_time_outcomeBI`, `SparseHamiltonian.GateBinaryNodes.binary_select_solverI`, `SparseHamiltonian.GateBinaryNodes.nv_const_outcome` | [Constant forcing](../GateEfficientBinaryNodes/ConstSolver.lean) |
| General boundary-resolvent simulation lemma for every real time in the exact-gate model, with the compressed second moment in the Loewner order and at most `6 d ≤ 3840 (α\|t\|ν + Q log(1/ε))` calls of `D` or `D†` (`hs:lem:abstract`, `hs:eq:interface`, `hs:eq:abstractcost`); every known isometry of a finite-dimensional system; for every finite-dimensional private space, in calls of the padded unitary, `SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_finite`; instances from scalar data and from binary sparse oracles; with the manuscript's schedule, exactly the count of `hs:eq:explicitcount`, at most `3880 (α\|t\|ν + Q log(1/ε))`, and error `ε/2` | `SparseHamiltonian.GateRemarks.abstract_simulation`, `SparseHamiltonian.GateSchedule.abstract_simulation_ms_explicit`, `SparseHamiltonian.GateRemarks.abstract_simulation_isometry`, `SparseHamiltonian.GateRemarks.second_moment_iff`, `SparseHamiltonian.GateRemarks.abstract_simulation_scalar`, `SparseHamiltonian.GateRemarks.interface_binary` | [Boundary-resolvent lemma](../GateEfficientRemarks/Abstract.lean) |
| Lemma `hs:lem:abstract` for any private space, completed (review item B1): every call of the padded private unitary `V D₀ V† - (1 - V V†)`, under any literal controls, is one call of `D₀` or `D₀†` under the range flag of `V` (`V D₀ V† + (1 - V V†)`) after the known reflection about the range of `V`, which makes no call (an operator identity for the query theorem; no gate count is claimed for an arbitrary `V`); for a zero system the empty circuit, with no call and no gate, is exact | `SparseHamiltonian.PrivateSpaceAbstract.oracleOp_padUnitary`, `SparseHamiltonian.PrivateSpaceAbstract.oracleOp_padUnitary_adjoint`, `SparseHamiltonian.PrivateSpaceAbstract.padUnitary_eq_flagCall`, `SparseHamiltonian.PrivateSpaceAbstract.flagCall_unitary`, `SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_zero` | [Padded call](../PrivateSpaceAbstract/Flag.lean) |
| Auxiliary-qubit count of `hs:eq:gate-total` in `b_data`, `log(N+1)` and `log((Q_base+1)/ε)` from binary sparse oracles, and from time-indexed binary sparse oracles with `q = √s t + √(st log(2/ε)) + log(2/ε)` in place of `Q_base` and `log₂(M+1)` added, with the gate bounds of `hs:eq:gate-binary` for the same circuits, before and after synthesis (at most `4·10⁶ (𝔟_H+1)³` qubits, system qubits included; cubic, since the released CORDIC workspace has at least `12 n³` qubits) | `SparseHamiltonian.GateRemarks.binary_simulation_bits_qubits`, `SparseHamiltonian.GateRemarks.binary_time_simulation_bits_qubits`, `SparseHamiltonian.GateRemarks.binary_simulation_budget_synth_bits_qubits`, `SparseHamiltonian.GateRemarks.binary_time_simulation_budget_synth_bits_qubits`, `SparseHamiltonian.GateRemarks.binArith_A_ge` | [Bit-length qubit counts](../GateEfficientRemarks/Qubits.lean) |
| The empty circuit at zero time from binary and time-indexed binary sparse oracles, with every released hypothesis and conclusion (remarks in `hs:thm:gates` and, for the time-dependent circuits, `hs:thm:time`) | `SparseHamiltonian.GateRemarks.binary_simulation_nonneg`, `SparseHamiltonian.GateRemarks.binary_simulation_budget_nonneg`, `SparseHamiltonian.GateRemarks.binary_time_simulation_nonneg`, `SparseHamiltonian.GateRemarks.binary_time_simulation_budget_nonneg` | [Zero-time binary-data circuits](../GateEfficientRemarks/ZeroBinary.lean) |
| The same over a finite gate set, native implementations and binary sparse oracles, synthesis as a hypothesis (remarks in `hs:thm:gates` and, for the time-dependent circuits, `hs:thm:time`) | `SparseHamiltonian.GateRemarks.native_simulation_synth_nonneg`, `SparseHamiltonian.GateRemarks.native_simulation_signed_synth_zero`, `SparseHamiltonian.GateRemarks.native_time_simulation_synth_nonneg`, `SparseHamiltonian.GateRemarks.binary_simulation_synth_nonneg`, `SparseHamiltonian.GateRemarks.binary_time_simulation_synth_nonneg`, `SparseHamiltonian.GateRemarks.binary_simulation_budget_synth_nonneg`, `SparseHamiltonian.GateRemarks.binary_time_simulation_budget_synth_nonneg` | [Zero-time finite-gate-set circuits](../GateEfficientRemarks/ZeroSynth.lean) |
| Gate-efficient sparse simulation from binary sparse oracles for every real time (`hs:thm:gates` under the assumptions of `hs:thm:main`): for `t < 0` the literal inverse of the released circuit for `-t`, with inverse oracle calls, the released counts for `-t` and the same full-output error against `e^{-itĤ}`, before and after synthesis, in the bit lengths with the qubit count, and with the empty circuit at `t = 0`; at `t = -1` for a nonzero Hamiltonian every hypothesis at once, while the released circuit for `-t` is at least `‖(e^{-itĤ} - e^{itĤ}) ψ‖ - ε` from `e^{-itĤ}` | `SparseHamiltonian.GateSigned.binary_simulation_signed`, `SparseHamiltonian.GateSigned.binary_simulation_bits_qubits_signed`, `SparseHamiltonian.GateSigned.binary_simulation_budget_synth_bits_qubits_signed`, `SparseHamiltonian.GateSigned.binary_simulation_signed_zero`, `SparseHamiltonian.GateSigned.hs_signed_all_hyps`, `SparseHamiltonian.GateSigned.binarySim_error_ge` | [Signed-time binary-data circuits](../GateEfficientSigned/Binary.lean) |
| Source gate and work costs polynomial in `𝔟` give the total gate bound `ḡ q poly(𝔟)` (remark in `ode:thm:gates`): at most `10²⁰ (1+2c) g q* (𝔟+1)^max(j,3)` gates (twice that, with the internal `q*`, for time-dependent coefficients) and `(3·10¹¹+2c) (𝔟+1)^max(j,3)` qubits for the solvers from binary and time-indexed binary sparse oracles, also over a finite gate set with the per-trial claim and for every `T ≥ 0` | `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_poly`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_user`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_poly`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_poly`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_poly_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_user_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_poly_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_poly_nonneg` | [Polynomial source costs](../GateEfficientRemarks/ODE/Poly.lean) |
| Zero time or a known zero generator over a finite gate set with every trial synthesised, native and binary-data solvers, and these solvers for every `T ≥ 0` (remark in `ode:thm:gates`) | `SparseHamiltonian.GateRemarks.ODE.native_ode_solver_synth_zero`, `SparseHamiltonian.GateRemarks.ODE.native_ode_time_solver_synth_zero`, `SparseHamiltonian.GateRemarks.ODE.native_ode_solver_synth_nonneg`, `SparseHamiltonian.GateRemarks.ODE.native_ode_time_solver_synth_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_solver_synth_zero`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_solver_synth_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_solver_synth_zero`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_solver_synth_nonneg` | [Zero case, every trial synthesised](../GateEfficientRemarks/ODE/SynthZero.lean) |
| Zero time or a known zero generator: `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` with the constants of the general case on the register of the direct source assembly, for every `b_data`, also over a finite gate set with the per-trial claim; explicit data meeting every hypothesis | `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_zero`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_zero`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_zero`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_zero`, `SparseHamiltonian.GateRemarks.ODE.zero_instance_all_hyps`, `SparseHamiltonian.GateRemarks.ODE.zero_instance_outcome` | [Zero-case budgets in 𝔟](../GateEfficientRemarks/ODE/ZeroBudget.lean) |
| The budgets in `𝔟` of the binary-data ODE solvers on their registers for every `T ≥ 0`, with every conclusion of the released budgets (in the zero case for a Cayley rescaling of bit length `b_data`) | `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_nonneg`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_zero_released`, `SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_zero_released`, `SparseHamiltonian.GateRemarks.ODE.zero_words_le`, `SparseHamiltonian.GateRemarks.ODE.zero_wordsT_le` | [Budgets in 𝔟 for every T ≥ 0](../GateEfficientRemarks/ODE/ZeroReleased.lean) |
| Hamiltonian-simulation query lower bound for adaptive algorithms, Theorem 5.1 (`hsl:thm:main`) | `AdaptiveHamiltonianLowerBound.main_max_tree` | [Adaptive Hamiltonian lower-bound endpoint](../AdaptiveHamiltonianLowerBound/Theorem.lean) |
| Positive Chebyshev filtering (`qls:prop:chebyshev`) | `ChebyshevFilter.chebyshev_filter` | [Chebyshev filter](../ChebyshevFilter/Proposition.lean) |
| Coherent choice of walk direction (`qls:lem:signedwalk`) for the Chebyshev LCU circuit, for walks `R V† C V`, and for the released walk through a chiral symmetry | `ChebyshevFilter.chebyshev_filter_program`, `ChebyshevLinearSystem.signed_walk_step` | [Chebyshev filter](../ChebyshevFilter/Proposition.lean) |
| Chebyshev filter degree for the augmented walk (`qls:eq:filtercost`) | `ChebyshevFilter.augmented_filter` | [Augmented-walk filter](../ChebyshevFilter/Augmented.lean) |
| Optimal sparse-query linear-system algorithm with the positive Chebyshev filter and signed walk steps, Theorem 8.1 (`qls:thm:main` with `qls:prop:chebyshev` and `qls:lem:signedwalk`) | `ChebyshevLinearSystem.main` | [Chebyshev linear-system endpoint](../ChebyshevLinearSystem/Main.lean) |
| Optimal sparse-query linear-system algorithm with approximately implemented known gates and the degrees `d + 1`, Theorem 8.1 (`qls:thm:main` with `qls:eq:finitedegree`, `qls:eq:bernoulli`), and the explicit constants of `qls:rem:constants` | `ChebyshevLinearSystemFinite.main_amp`, `ChebyshevLinearSystemFinite.main`, `ChebyshevLinearSystemFinite.main_alloc`, `ChebyshevLinearSystemFinite.finDegree_hundred_lt` | [Finite-gate linear-system endpoint](../ChebyshevLinearSystemFinite/Main.lean) |
| Optimal sparse-query linear-system algorithm with Hoeffding's inequality and the repetition count `⌈log(10/ζ_j)/(2·0.0099²)⌉` of `qls:eq:hoeffding` at the stage budget `ζ_j = (ε/1000) 2^{j-m}`, finite degrees and approximately implemented known gates (`qls:thm:main`): at most `3.4·10⁹ √s κ log(1/ε)` matrix-oracle and `1.25·10⁸ √s κ log(1/ε)` source calls; `5101 log(10/ζ_j) ≤ n_j ≤ 5102 log(10/ζ_j)` (`qls:rem:constants`) | `QLSHoeffding.mainH`, `QLSHoeffding.main_ampH`, `QLSHoeffding.main_exactH`, `QLSHoeffding.two_sided_sharp`, `QLSHoeffding.repsH_eq_ms`, `QLSHoeffding.repsH_bracket` | [Hoeffding schedule](../QLSHoeffding/Main.lean) |
| Time-dependent Hamiltonian simulation on nonuniform meshes, with breakpoints and integrated sample-error certificates (generalisations after `hs:thm:time`) | `TimeDependentExtensions.Hamiltonian.simulation` | [Mesh Hamiltonian endpoint](../TimeDependentExtensions/Hamiltonian/Theorem.lean) |
| Piecewise Lipschitz paths with one-sided samples (after `hs:thm:time`) | `TimeDependentExtensions.Hamiltonian.simulation_lipschitz` | [Mesh Hamiltonian corollaries](../TimeDependentExtensions/Hamiltonian/Corollaries.lean) |
| Time-dependent dissipative ODE on nonuniform meshes, with breakpoints, integrated certificates and the certified left-endpoint source quadrature (proof of `ode:thm:time`; the general source interface is `GeneralSourceODE`, on meshes `GeneralSourceExtensions`); formally also with positive semidefinite dissipative parts of the represented samples | `TimeDependentExtensions.ODE.solver` | [Mesh ODE endpoint](../TimeDependentExtensions/ODE/Theorem.lean) |
| Piecewise Lipschitz generators and forcing (proof of `ode:thm:time`; formally also with positive semidefinite dissipative parts of the represented samples) | `TimeDependentExtensions.ODE.solver_lipschitz` | [Mesh ODE corollaries](../TimeDependentExtensions/ODE/Corollaries.lean) |
| Time-indexed block encodings (`hs:eq:blockspecial`, `hs:eq:blockadditive`) | `TimeDependentExtensions.BlockEncoding.simulation` | [Block-encoding endpoint](../TimeDependentExtensions/BlockEncoding/Theorem.lean) |
| Coherent selection of durations and start times (after `hs:thm:time`) | `TimeDependentExtensions.Coherent.coherent_select`, `TimeDependentExtensions.Coherent.coherent_windows` | [Coherent parameters](../TimeDependentExtensions/Coherent/Theorem.lean) |
| Propagators of integrable Hermitian paths (Carathéodory sense): existence, uniqueness, unitarity and the integrated sample-error certificate (after `hs:thm:time`) | `IntegrablePathSimulation.Propagator.existsUnique_isPropagator`, `IntegrablePathSimulation.Propagator.IsPropagator.isUnitary`, `IntegrablePathSimulation.Propagator.IsPropagator.refined_error` | [Integrable-path propagators](../IntegrablePathSimulation/Propagator/Duhamel.lean) |
| Time-dependent Hamiltonian simulation for integrable Hermitian paths, against the Dyson series and with an untouched reference, with coherent windows and time-indexed block encodings (after `hs:thm:time`) | `IntegrablePathSimulation.Hamiltonian.simulation`, `IntegrablePathSimulation.Hamiltonian.simulation_dyson`, `IntegrablePathSimulation.Coherent.coherent_windows`, `IntegrablePathSimulation.BlockEncoding.simulation` | [Integrable-path Hamiltonian endpoint](../IntegrablePathSimulation/Hamiltonian/Theorem.lean) |
| Hamiltonian-simulation query lower bound for the time-dependent class of `hs:thm:time` on uniform meshes, on nonuniform meshes and for integrable paths, whose constant hard paths belong to each class (remark after `hs:thm:time`; `hsl:thm:main`) | `TimeDependentHamiltonianLowerBound.uniform_class_max`, `TimeDependentHamiltonianLowerBound.mesh_class_max`, `TimeDependentHamiltonianLowerBound.integrable_class_max` | [Time-dependent lower bound](../TimeDependentHamiltonianLowerBound/ClassBound.lean) |
| The same for programs over the released time-dependent oracle families meeting the error criterion on the constant paths (`hsl:thm:main`) | `TimeDependentHamiltonianLowerBound.main_max_uniform`, `TimeDependentHamiltonianLowerBound.main_max_mesh`, `TimeDependentHamiltonianLowerBound.main_max_integrable` | [Time-dependent release forms](../TimeDependentHamiltonianLowerBound/Release.lean) |
| The same for adaptive algorithms over the coherent sampled-time access, with inverse and controlled calls, or over the released time-dependent oracle families (`hsl:thm:main`) | `TimeDependentHamiltonianLowerBound.main_max_tree_access`, `TimeDependentHamiltonianLowerBound.main_max_tree_calls`, `TimeDependentHamiltonianLowerBound.main_max_tree_uniform`, `TimeDependentHamiltonianLowerBound.main_max_tree_mesh` | [Time-dependent adaptive lower bound](../TimeDependentHamiltonianLowerBound/Trees.lean) |
| Two-sided bracket for the released time-dependent simulators on the constant hard families (`hsl:thm:main` with `hsl:eq:upper`) | `TimeDependentHamiltonianLowerBound.uniform_theta_bracket`, `TimeDependentHamiltonianLowerBound.mesh_theta_bracket` | [Time-dependent bracket](../TimeDependentHamiltonianLowerBound/Theta.lean) |
| Hamiltonian-simulation query lower bound for the time-dependent class in the time-indexed block-encoding model, in calls of a Hermitian block encoding of the constant hard paths with `α_BE = sη` (released aligned family, the controlled time-indexed oracle itself, or all call forms; error criterion of the released block-encoding theorem), with the reduction constant `8` (extension of `hsl:thm:main` and the remark after `hs:thm:time` to the time-indexed block-encoding model of `hs:eq:blockspecial`; the manuscript derives only the upper bound `hs:eq:blockadditive` there) | `TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block`, `TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_primitive`, `TimeDependentLowerBoundExtensions.BlockEncoding.main_max_calls_block` | [Block-encoding lower bound](../TimeDependentLowerBoundExtensions/BlockEncoding/Bound.lean) |
| The same under the error criterion of the integrable-path block-encoding theorem (same extension, reduction constant `8`) | `TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_integrable` | [Integrable-path block-encoding lower bound](../TimeDependentLowerBoundExtensions/BlockEncoding/Integrable.lean) |
| The same with coherent selection of known durations and start times, for programs and adaptive algorithms over the released selection family and its call forms (`hsl:thm:main`) | `TimeDependentLowerBoundExtensions.Coherent.main_max_select`, `TimeDependentLowerBoundExtensions.Coherent.main_max_windows`, `TimeDependentLowerBoundExtensions.Coherent.main_max_tree_select`, `TimeDependentLowerBoundExtensions.Coherent.main_max_calls_select` | [Coherent-selection lower bound](../TimeDependentLowerBoundExtensions/Coherent/Bound.lean) |
| The same with coherent selection of windows under the error criterion of the integrable-path coherent-windows theorem (`hsl:thm:main`) | `TimeDependentLowerBoundExtensions.Coherent.main_max_windows_integrable` | [Integrable-path coherent-selection lower bound](../TimeDependentLowerBoundExtensions/Coherent/Integrable.lean) |
| The same for programs and adaptive algorithms over all call forms (plain, inverse, controlled, controlled inverse) of the released uniform-mesh, general-mesh and integrable-path oracle families (`hsl:thm:main`) | `TimeDependentLowerBoundExtensions.Calls.main_max_calls_uniform`, `TimeDependentLowerBoundExtensions.Calls.main_max_calls_mesh`, `TimeDependentLowerBoundExtensions.Calls.main_max_calls_integrable`, `TimeDependentLowerBoundExtensions.Calls.main_max_tree_calls_uniform`, `TimeDependentLowerBoundExtensions.Calls.main_max_tree_calls_mesh` | [Call-form lower bound](../TimeDependentLowerBoundExtensions/Calls/Bound.lean) |
| The same for slot-selected gate-level time-dependent circuits, in private-operation calls, conditional on each private operation being realised exactly by a program with at most `q` value calls of the native sparse queries (`NativeRealization`, shown for single call forms with `q = 1`) (`hsl:thm:main`) | `TimeDependentLowerBoundExtensions.Gate.main_max_gate`, `TimeDependentLowerBoundExtensions.Gate.main_max_gate_uniform`, `TimeDependentLowerBoundExtensions.Gate.nativeRealization_call` | [Gate-level lower bound](../TimeDependentLowerBoundExtensions/Gate/Bound.lean) |
| The same with each private operation realised within operator-norm error `ξ` by a program with at most `q` value calls (`ApproxRealization`, the gate model of the manuscript with a fixed primitive-oracle cost; implied by a realisation of the controlled operation within `ξ`), when the ideal circuit's endpoint error plus `nPriv · ξ` is at most `ε` (`hsl:thm:main`) | `TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_tolerant`, `TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_uniform_tolerant`, `TimeDependentLowerBoundExtensions.Tolerant.approxRealization_zero_iff`, `TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_controlled`, `TimeDependentLowerBoundExtensions.Tolerant.approxRealization_call` | [Gate-level lower bound within ξ](../TimeDependentLowerBoundExtensions/Tolerant/Bound.lean) |
| The same for the class of piecewise Lipschitz paths with breakpoints (the error criterion of the released piecewise Lipschitz theorem), for programs over the released general-mesh family and its call forms; the released simulators meet the hypotheses (`hsl:thm:main`, remark after `hs:thm:time`) | `TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_max`, `TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_max_calls`, `TimeDependentLowerBoundExtensions.Tolerant.simulation_lipschitz_guarantee`, `TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_nonvacuous` | [Piecewise Lipschitz lower bound](../TimeDependentLowerBoundExtensions/Tolerant/LipschitzBound.lean) |
| The same for algorithms with measurements inside a run over the released uniform-mesh, general-mesh and integrable-path, selection and block-encoding oracle families and their call forms (worst-case value calls; `8` times block-encoding calls); the released simulators, run as measured algorithms, meet the hypotheses on constant data (`hsl:thm:main`) | `TimeDependentLowerBoundExtensions.Measured.main_max_measured_uniform`, `TimeDependentLowerBoundExtensions.Measured.main_max_measured_mesh`, `TimeDependentLowerBoundExtensions.Measured.main_max_measured_select`, `TimeDependentLowerBoundExtensions.Measured.main_max_measured_block`, `TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_block`, `TimeDependentLowerBoundExtensions.Measured.released_block_measured` | [Measured time-dependent lower bound](../TimeDependentLowerBoundExtensions/Measured/Block.lean) |

### Hamiltonian and unitary endpoints

The Hamiltonian theorem constructs a primitive-oracle circuit and bounds its
query count and full-output operator-norm error. The unitary theorem gives
error at most `1/4` using `O(sqrt(N))` original entry-oracle calls.
The complete ODE endpoint runs at most four fresh trials, with heralded
success probability at least `175/256 > 2/3`. Its conditional mixed output
has trace distance at most `ε` from the normalised actual solution, with
worst-case bounds on matrix and source-preparation queries.

The library `UnitaryImplementationPrecision` proves Corollary `hs:cor:unitary`
at every precision `0 < ε ≤ 1/2`, through Theorem `hs:thm:main` and without
results from other papers, in the access model of the unitary theorem: one
entry oracle with spectators (no location oracle), its clean encoding, and
counts that include inverse calls; at `ε = 1/4` the oracle, workspace and
encoding are literally the released ones. For exact entries, one program fixed
before the instance makes at most `497664 π (√N + √(N ℓ) + ℓ)` entry-oracle
calls, `ℓ = log(1/ε)`, and its full output is within `ε` of `U`, also on inputs
entangled with an untouched reference (`UnitaryPrecision.implementation`). For
an entry table without the unitarity promise (`UnitaryPrecision.Table`) whose
represented entries are within `ε/(πN)` of those of a unitary `U`, the
dilation of the represented matrix is simulated with `η = 2` to error `ε/2`;
Schur's bound on the common locators and Duhamel's bound give full-output
error at most `ε` against `U` with at most `995328 π (√N + √(N ℓ) + ℓ)` table
calls (`implementation_inexact`), and one circuit, built from the table and
`ε` alone, serves every unitary within `ε/(πN)` of the represented entries
(`implementation_inexact_uniform`). The additive term is the `ℓ` of
`hs:thm:main` instead of the paper's `ℓ/log(e + ℓ/N)`, which needs
`hs:cor:hybrid`: for `ℓ ≤ N` the count is `O(√(Nℓ))`, as in the paper
(`three_term_le_root`), and for `ℓ > N` it exceeds the paper's bound by at
most the factor `log(e + ℓ/N)` (`two_term_le_hybrid`). The paper's bound itself
is obtained from Corollary `hs:cor:unitary-optimal` instead
(`OptimalSparseSimulation.unitary_bound`, `unitary_bound_inexact`).

The library `UnitaryImplementationExtensions` proves the lower half of the last
sentence of `hs:cor:unitary`, without results from other papers. The hard
family is `(U_m)_{jk} = [j + k = m mod N]` (`SearchFamily.searchMatrix`,
unitary, `U_m |0⟩ = |m⟩`) with one-bit entries; its reversible entry lookup is
exactly a Boolean phase oracle, also after the released spectator lift
(`PhaseBridge.lookup_eq_phase`, `LiftPhase.oracle_eq_phase`), so one entry query
is one search query. By the package's positive-weight adversary, every unitary
query circuit over the entry lookup (with any untouched workspace) or over the
released entry oracle (for any parameters), inverse calls counted and fixed
gates free, that implements every `U_m` on one isometric encoding with error
`ε₀ ≤ 1` makes at least `(1 - 2ε₀√(1 - ε₀²/4)) √(N - 1)/2` calls
(`UnitaryImplementationExtensions.LowerBound.entry_count_ge`,
`implementation_count_ge`); this is positive for `ε₀ ≤ 1/2`, and at `ε₀ = 1/4`
it gives `√N ≤ 4√2 · count`. With the released circuit this is `Θ(√N)` in one
oracle model (`LowerBound.theta`), and at every fixed `ε` with the
general-precision circuits (`theta_of_error`, `theta_inexact`). The oracle is
that of `UnitaryImplementationPrecision` (equal by `rfl` for equal tables), so
the bound applies to its circuits as well. The library also proves the upper
bounds again, independently (`General.implementation`, `Inexact.implementation`,
with the target family part of the data), with two-term constants about 1.2
times those of `UnitaryPrecision`. Adaptive algorithms (classical trees of
measured runs) and controlled entry queries are covered by the library
`AdaptiveUnitaryLowerBound` (adaptive algorithms at trace-distance error below
`1/2`), algorithms with measurements inside a run by
`DeferredMeasurementLowerBounds`, and the endpoint `1/2` of trace-distance error
for both, and the operator-norm form for measured algorithms, by
`MeasuredUnitaryLowerBound`.

The library `AdaptiveUnitaryLowerBound` proves the lower half of the last
sentence of `hs:cor:unitary` for adaptive protocols
(`SparseLinearSystems.Protocol.Tree`, heralded or unheralded) and for the
inverse, controlled and controlled-inverse forms of every call
(`AdaptiveODELowerBound.Access.callFamily`), again without results from other
papers. For `N ≥ 2`, let every label be implemented on an isometric encoding by
at most `w l` calls of the released entry oracle of the search family (or of the
ordinary entry lookup with any payload), inverse calls counted, on a
finite-dimensional workspace. Every adaptive protocol `T` over these labels with
finite-dimensional output that succeeds with probability at least `s₀ > 0` on
every instance `m` and whose conditional output, read through an isometry, is
within trace distance `ε₀ ≤ 1/2` of `U_m |0⟩ = |m⟩` satisfies
`(s₀ (1 - 2ε₀))² √(N - 1) ≤ 4 T.worstCost w`
(`Theorem.implementation_count_ge_tree`, `Lookup.entry_count_ge_tree`), and over
the call forms, each at the weight of its label, the same with
`T.worstCost (fun c => w c.1)` (`Theorem.implementation_count_ge_calls_tree`,
`Lookup.entry_count_ge_calls_tree`). With the entry oracle as the only oracle
this is `(1 - 2ε₀)² √(N - 1) ≤ 9 Q` heralded and `≤ 4 Q` unheralded, `Q` the
worst-case number of entry calls (`Entry.heralded_tree`, `Entry.unheralded_tree`
and their `_calls_tree` forms). The bound is positive for `ε₀ < 1/2`. Single
programs with operator-norm error `ε₀ ≤ 1`, over weighted labels or their call
forms and on any workspace, keep the non-adaptive bound
`(1 - 2ε₀ √(1 - ε₀²/4)) √(N - 1) ≤ 2 Q`
(`Theorem.implementation_count_ge_program_of_error`,
`Theorem.implementation_count_ge_calls_program_of_error`,
`Entry.calls_program_of_error`, `Lookup.entry_count_ge_program_of_error`,
`Lookup.entry_count_ge_calls_program_of_error`). The released constant-error
circuit of `UnitaryImplementation`, run once as an adaptive protocol, meets these
hypotheses at `ε₀ = 1/4`, also over the call forms, with at most
`queryConstant · √N` entry calls, so both halves of `Θ(√N)` hold for adaptive
protocols in one oracle model (`NonVacuity.released_tree`,
`NonVacuity.released_calls_bounds`).

The library `MeasuredUnitaryLowerBound` proves this lower half at the endpoint
`ε₀ = 1/2` of trace-distance error, where the factors `(1 - 2ε₀)²` and
`1 - 2√(ε₀(1 - ε₀))` of the pairwise bounds vanish, again without results from
other papers. Under the hypotheses of `Theorem.implementation_count_ge_tree`
(`N ≥ 2`, success probability at least `s₀ > 0`, conditional output within
trace distance `ε₀ ≤ 1/2` of `U_m |0⟩`), every adaptive protocol satisfies
`(s₀ (N (1 - ε₀) - 1))² ≤ 4 (N - 1) √(N - 1) T.worstCost w`
(`Adaptive.implementation_count_ge_tree_endpoint`, with the forms over the call
family, for one program on a unit seed and over the entry lookup). The same
holds for every algorithm with measurements inside a run
(`DeferredMeasurementLowerBounds.Model.Measured`) on the input `J |0⟩` of an
isometric encoding, with success probability at least `p₀ > 0` and `Q` its
worst-case number of entry calls
(`Deferred.implementation_count_ge_measured_endpoint`), and with `32` in place
of `4` over the four call forms
(`Calls.implementation_count_ge_measured_calls_endpoint`). At `ε₀ = 1/2` this
gives `(N - 2)² ≤ 16 (N - 1) √(N - 1) Q` (`36` heralded, `128` for the measured
call forms) and, for `N ≥ 3`, `√(N - 1) ≤ 64 Q` (`144` heralded, `512` for the
measured call forms). The bounds are empty at `N = 2`, as they must be: a
query-free protocol with maximally mixed output is within trace distance `1/2`
of both targets. The proof sums the pair gaps of the readout effects over all
ordered pairs and combines them by Cauchy-Schwarz with the package's summed
adversary progress. The released constant-error circuit meets the hypotheses
of the `ε₀ = 1/2` forms in each class with at most `queryConstant · √N` entry
calls (`NonVacuity.released_tree_half`, `released_calls_tree_half`,
`released_measured_half`, `released_measured_calls_half`).

The same library states the manuscript's operator-norm error
`‖A_U - U‖ ≤ ε` (`hs:eq:unitaryerror`) for algorithms with measurements inside a
run: `OperatorNorm.NormImplements` asks that some purification of the output
on the encoded inputs succeed with probability one and be within operator norm
`ε₀` of `U ⊗ γ` for a unit garbage vector `γ`. Such an algorithm is within
trace distance `s = ε₀ √(1 - ε₀²/4)` of `U ψ` on every unit input
(`OperatorNorm.densityAccurate_of_normImplements`), and `s ≤ √15/8 < 1/2` for
`ε₀ ≤ 1/2`, so `(N (1 - s) - 1)² ≤ 4 (N - 1) √(N - 1) Q`
(`OperatorNorm.implementation_count_ge_measured_norm`, also for the entry
lookup), with `32` over the four call forms
(`OperatorNorm.implementation_count_ge_measured_calls_norm`), and
`√(N - 1) ≤ 64 Q` (`512`) for `N ≥ 3`. Unlike the trace-distance endpoint these
bounds are not empty at `N = 2`. Unitary programs with operator-norm error
`ε₀`, run and output in full, satisfy the notion
(`OperatorNorm.normImplements_runAll`), and the released circuit meets the
hypotheses (`OperatorNorm.released_measured_norm`,
`OperatorNorm.released_measured_calls_norm`).

### Solver and gate endpoints

The linear-system endpoint is one bounded adaptive protocol for all inputs with
`‖A‖ ≤ 1`, `‖A⁻¹‖ ≤ κ`: a geometric solution-norm estimator followed by at most
1000 final attempts. Every transcript makes at most `4·10¹² √s κ log(1/ε)`
matrix-oracle calls and `2·10¹¹ √s κ log(1/ε)` calls of the controlled `U_b` or
its inverse, for `0 < ε ≤ 1/10`. Success has probability at least `2/3`, and the
conditional output has trace distance at most `ε` from `A⁻¹b/‖A⁻¹b‖`.

The gate-level endpoint is one explicit circuit of elementary gates (one-qubit
unitaries with at most three controls) and sector-controlled calls of the
supplied unitaries `U_J` and private Cayley operation `D`, fixed before the
oracles. Under the clock hypotheses of the Hamiltonian analysis for
`J = U_J ι₀`, it makes exactly `6d` private Cayley calls and `12d` calls of
`U_J` or `U_J†`, uses at most `200 (d+1)(a+m+r+1)` elementary gates on
`2a + 3m + 6r + 3` qubits besides the system, and its full output on clean
inputs is within `ε` of `exp(-iτH)`; here `d ≤ 128 (τ q̄ + Q (1 + log(3/ε)))`
is the filter degree, `2^m` the number of time slots and `2^r ≤ 4(d+1)`.

The time-dependent endpoint uses coherent sampled-time oracles
`∑_r |r⟩⟨r| ⊗ O_r`, built from the native primitives of represented samples
`H̃_r` on a uniform mesh of `M` intervals. One program and one clean encoding
make at most `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))` queries, `τ = η t`,
independently of `M` and of the Lipschitz constant `β` of the Hermitian path
`H(u)`. Its full output is within `ε` of every propagator of the path, given
`‖H(r t/M) - H̃_r‖ ≤ δ` with `t δ ≤ ε/12` and explicit mesh conditions; the
propagator is shown to exist.

The time-dependent gate-level endpoint gives gate counts for this simulation.
The released gate-level circuit, with `2^m` time slots, calls a slot-selected
private Cayley operation that applies the supplied `D_k` on the configurations
whose slot wires carry `k`; `D_k` carries the clock promise for the
normalised sample `H̃_k / α`. The circuit is fixed by public numbers before
the oracles. For a `β`-Lipschitz Hermitian path with
`‖H(k t/2^m) - H̃_k‖ ≤ δ`, `4 t δ ≤ ε`, `4 β t² ≤ ε 2^m` and
`steps (α t) (ε/6) ≤ 2^m`, it makes exactly `6d` private calls and `12d`
calls of `U_J` or `U_J†`, uses at most `200 (d+1)(a+m+r+1)` elementary gates
on `2a + 3m + 6r + 3` qubits besides the system, and its full output on clean
inputs is within `ε` of every propagator of the path. With the rescaled
sparse parameters of `hs:thm:time`,
`d ≤ 4608 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, `τ = η t`, so neither the
number of slots nor `β` multiplies the number of calls, and they enter the
gate count only through `m`. The manuscript states `hs:thm:gates` for
time-independent Hamiltonians; this is the single-label case of
`ode:lem:gate-select`.

The time-dependent ODE endpoint solves `x' = -G(u) x + b(u)` with accretive
`G(u)`, using the same coherent sampled-time access to represented generator
samples `G̃_r` and a forcing-preparation interface that is coherent in the
quadrature label. One public trial family, fixed before the matrix input, the
paths, the solution and both source directions, satisfies the complete ODE
certificate for `x(T)`: success at least `2/3`, conditional trace distance at
most `ε`, at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and
`40 g'` calls of each source interface, `g' = 2g`, the bound of the
constant-coefficient endpoint. The source mass is the left-endpoint quadrature
`B = ‖x(0)‖ + (T/M) ∑ ‖b̃_r‖`, with `B ≤ g ‖x(T)‖`; Lipschitz and sample-error
bounds certify the time discretisation through the public budget
`discretisation ≤ ε B / (2000 g)`. Neither `M` nor the regularity constants
enter the query counts.

**Formal restriction (sample positivity).** The formal versions of Theorem
`ode:thm:time` (`TimeDependentODE`, `GeneralSourceODE`, `GeneralSourceExtensions`,
`TimeDependentExtensions` and the time-dependent forms of `ZeroTimeRemarks`)
assume that the dissipative
part `(G̃_r + G̃_r†)/2` of every represented generator sample is positive
semidefinite. The manuscript's theorem does not: it assumes the exact generator
path accretive and asks of the represented samples only the uniform moment and
norm promises. The released circuit propagates every LCHS branch by the
represented samples, and the formal proofs of these libraries apply the LCHS
identity to these sampled propagators, which needs every sample dissipative;
they prove the theorem for dissipative samples, which include samples that are
exact values of the path. The released time-dependent gate-level ODE theorems (the time-dependent part of
`ode:thm:gates`) assume `L_r ≥ 0` for every represented sample in the same way,
and the input class of the truncated Dyson-series solvers of `odel:lem:dyson`
in `ODELowerBoundExtensions`, `DysonSingleProgram` and `DysonGeneralAccess`
assumes the used samples accretive (`DysonFullClass` proves the lemma on the
input class of `ode:thm:time` without this hypothesis, under this package's label-controlled
loading and a classical propagator on each closed mesh cell). The restriction is stated in
[the time-dependent ODE statement guide](../TimeDependentODE/Statements.lean) and
in the guides of the libraries that make the hypothesis. The library
`RepresentedSampleODE` removes it for the mesh endpoints of
`GeneralSourceExtensions` and for the time-dependent gate-level solver from
binary data, which the conformance theorems `ode_thm_time`,
`ode_thm_time_approx` and `ode_thm_gates_time` use: the analysis runs on the
positive repairs `(‖D̃‖/(‖D̃‖ + κ))(D̃ + κ)` of the represented dissipative parts
`D̃` with negativity bounds `κ` (from the true path, `κ_r` the average of
`‖Herm(G_r - G̃_r)‖` on a mesh interval, `κ = δ_G` on the uniform mesh), and the
budgets acquire the dissipative part of the represented-sample term of the
manuscript's branch certificate: on a mesh `R ΔD`, `ΔD = ∑_r ∫ ‖Herm(G_r - G̃_r)‖`,
in the integrated form `∑_r ∫ ‖K̃_{k,r} - K_k(u)‖ du ≤ ΔH + R ΔD` (`ΔH` the
integrated sample error of the Hamiltonian parts), and `R' T δ_G` on the uniform
mesh of the gate solver. On a mesh these theorems take the mild solution
(Duhamel's formula), which asks of the forcing only that the propagated forcing
`v ↦ U(T, v) b(v)` be integrable; the propagator of the generator pieces is
classical on every closed mesh interval (`formal_classicalPropagator` in the
conformance theorems).

The library `GeneralSourceODE` proves the same theorem with the source access
of the manuscript's Theorem `ode:thm:time` (eqs. `ode:eq:source-interface-mass`
and `ode:eq:source-interface-preparation`) in place of the left-endpoint rule
with public source norms. The input supplies public nodes `v_i ∈ [0, T]`,
complex coefficients `ω_i` (their phases are a public gate), a weight
preparation `P_w` with amplitudes `√(‖z_a‖/B_q)` on the labels of the initial
state and of the nodes, `z = (x(0), ω_i b(v_i))`, and a data loader `U_load`
that prepares the corresponding directions; only the bounds `B_q ≤ c_q B` and
`B ≤ ḡ ‖x(T)‖` enter, not `B_q` or the source norms. Under the mesh conditions
of the released solver at `g = c_q ḡ`, the certified propagated quadrature
`‖∫₀ᵀ U(T, v) b(v) dv - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B` and
`ζ + c_q T (β_G T/M + δ_G) ≤ ε/(2000 ḡ)`, four fresh trials of one public
trial family succeed with probability at least `2/3` and have conditional
trace distance at most `ε` (`Oracles.ActualCertificate`), with at most
`1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `40 g'` calls of each
of `P_w`, `U_load` and `P_w†`, `g' = 2 c_q ḡ`
(`SparseHamiltonian.GeneralSourceODE.solver`); neither `M` nor the number of
nodes enters the counts. The propagator `U(T, v)` of the dissipative equation
is a Lean object here (`IsPropagator`, existence `exists_isPropagator`), and
Duhamel's formula (`duhamel`) identifies the certificate with the one stated
for the solution, which `propagated_solver` uses on the two composite source
interfaces `phase ∘ U_load ∘ (P_w ⊗ 1)` and `P_w† ⊗ 1`. Here the preparations
are exact, the matrix samples are on a uniform mesh, `T > 0` and
`η_H + R η_D > 0`, and, as in the released solver, every sample has a positive
semidefinite dissipative part (the formal restriction above).

The library `GeneralSourceExtensions` proves the variants of this theorem that
`GeneralSourceODE` leaves out, separately and combined. In the degenerate
branches `T = 0` and `η_H + R η_D = 0` of `ode:thm:main`, every branch product
is the identity and the released compiler with the identity SELECT gives the
released guarantees with no matrix query; `solver_nonneg` holds for every
`T ≥ 0`, with matrix-query budget `0` in these cases (`zero_solver`). With
approximately implemented preparations, the supplied `P_w` and `U_load` are
arbitrary unitaries within `δ` in operator norm of exact preparations, which
may depend on the instance and are not supplied. The released trial family
for the input type of exact preparation instances, run on the supplied
oracles, moves by at most `30 g' δ` per trial, and for `30 g' δ ≤ 1/400` and
`30 g' δ ≤ ε/20` four fresh trials succeed with probability at least `2/3`,
with conditional trace distance at most `ε` and the released counts
(`approx_solver`). On a nonuniform mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` with one
generator piece, one forcing piece and one represented sample per interval
(breakpoints at the mesh points), the clock runs on `N` uniform slots and the
budget is `ζ + c_q (ΔG + ΔR) ≤ ε/(2000 ḡ)`, with the integrated sample error
`ΔG = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r - G̃_r‖` and the refinement term
`ΔR = s Λ ∑_r |c_r T/N - Δ_r|` (`Mesh.mesh_solver`). Here `Λ` bounds the
decoded entries of the sparse data, interval `r` of length `Δ_r` has `c_r`
slots, and `ΔR`, the rounding of the interval lengths to whole slots, is at
most `s Λ M T/N` and vanishes when the mesh points lie on the slot grid. The
certificate is stated on the propagated source sum or, for continuous pieces,
on the propagated vector integral `∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv`,
which Duhamel's formula on the mesh identifies (`Mesh.mesh_duhamel`,
`Mesh.mesh_solver_integral`). `Mesh.mesh_approx_solver_nonneg_integral`
combines the three variants. On the uniform mesh with `N = q M` slots the
refinement term vanishes, the sample error is at most the released
`T (β_G T/M + δ_G)`, and every instance of the uniform theorems is an instance
of the mesh endpoints (`Mesh.uniform_instance`), so the mesh endpoint and the
combined endpoint give the guarantees of `GeneralSourceODE.solver` and
`approx_solver_nonneg` for all their instances on the actual oracles of the
`qM`-slot workspace (`Mesh.mesh_solver_uniform`,
`Mesh.mesh_approx_solver_nonneg_uniform`). For `q = 1` this workspace is
definitionally the released one, and the mesh endpoints give the released
statements themselves (`Mesh.solver_of_mesh`,
`Mesh.approx_solver_nonneg_of_mesh`). The positivity restriction above applies
to all of them; gate and workspace costs are not formalised.

The gate-level ODE endpoint solves `x' = -(L + iH) x + b` with `L ≥ 0` by one
explicit protocol of elementary gates, fixed before the instance: a joint
source/LCHS label register with an explicit rotation-tree preparation and
diagonal phases, the released gate-level simulator with a label-selected
private Cayley operation, the supplied source interfaces `J₀`, `J_b`, and
counted seed reflections, amplified and repeated at most four times. Under the
clock promises of `hs:thm:gates` for every branch Hamiltonian, success has
probability at least `175/256 > 2/3` and the conditional output is within
trace distance `ε` of `x(T)/‖x(T)‖`. Every history uses at most
`9000 g ((d+1)(a+m+r+1) + (k+1) + (J+2)(l+1))` elementary gates on
`4a + 6m + 12r + 2k + 2l + 8` qubits, `240 g d` private calls, `480 g d` calls
of `U_J` or `U_J†`, `40 g` calls of each source interface and `20 g` seed
reflections. Here `d` is the filter degree of the simulator for the common
time `τ = T (λH + R λD)`, `2^k` the number of source quadrature nodes, and `J`
the size of the analytic LCHS grid (`2^l < 2 (J+2)`): the trapezoidal rule for
the Gaussian LCHS integrand converges exponentially in the inverse step, so
`J ≤ R (T λD + 2 log (512/ν)) / π + 3 = O(ℓ (T λD + ℓ))`, with
`R = 4 log (20000 g/ε)`, `ν = ε/(10000 g)` and `ℓ = log (g/ε)`.

The time-dependent gate-level ODE endpoint solves `x' = -G(u) x + b(u)` with
accretive, Lipschitz `G(u)` on a public uniform mesh of `2^m` slots, by one
explicit protocol of the same kind. Every source and LCHS branch is masked on
the common mesh, so all branches share the simulation time
`τ = T (λH + R λD)`; a slot-selected private Cayley operation `D z r` serves
the represented sample `G̃_r = L̃_r + i H̃_r` of slot `r`, the source label is
prepared by one call of a supplied weight preparation `Wp`, and a supplied
loading `J` places `x(0)` and the forcing samples `b̃_q`. With the internal
ratio `2g` and accuracy `ε/2`, and under the discretisation budget of the
time-dependent ODE endpoint, success has probability at least `175/256` and
the conditional output is within trace distance `ε` of `x(T)/‖x(T)‖`. Every
history uses at most `18000 g ((d+1)(a+m+r+1) + (J+2)(l+1))` elementary gates
on `4a + 8m + 12r + 2l + 8` qubits, `480 g d` private calls, `960 g d` calls
of `U_J` or `U_J†`, `80 g` loading calls, `160 g` weight-preparation calls and
`40 g` seed reflections, with `J = O(ℓ (T λD + ℓ))` as above.

The general ODE endpoint solves `x' = A x + b` for an arbitrary sparse
generator `A = -M` with a known spectral bound `‖A‖ ≤ Λ`; no dissipativity or
normality is assumed. The near-optimal block-input linear-system solver (Costa
et al.; Dalzell) is the explicit hypothesis `BlockSolver f q₀`: `f(κ, δ)` calls
of a block encoding and a preparation give a decoded output of squared norm at
least `q₀` within direction error `δ`. From the native sparse queries, Lemma
`ode:lem:block` (this package's normalisation `8√2 Λ`; the manuscript has `2πΛ`)
builds a block encoding of `A/(8√2 Λ)` with
`O(√s log(1/ε))` queries; a block-encoded Taylor history with `m = ⌈8√2 ΛT⌉`
steps, `m` final copies and the `φ₁` source term in a source column is solved
with `κ = O(C̄ m)`, decoded at the final copies and amplified. One protocol,
fixed before the input, succeeds with probability at least `175/256` and has
conditional trace distance at most `ε` from `x(T)/‖x(T)‖` whenever
`‖e^{tA}‖ ≤ C̄` and `‖x(t)‖ ≤ g ‖x(T)‖` on `[0, T]`. Every history makes at
most `40 (5g/√q₀) f(κ, δ) · 3K · 1327104 · shape` native matrix queries and
`40 (5g/√q₀) · 3 f(κ, δ)` calls of each source interface; for
`f = c κ log(2/δ)` this is at most
`159443481054412800 · c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` matrix queries with
`𝓛 = 1 + log((1 + ΛT) C̄ g/ε)`, the paper's `Õ(√s ḡ C̄ (1 + ΛT))`
(`SparseHamiltonian.GeneralODE.Complexity.general_query_bound`). The bound
`ḡ_B` of the paper is not needed.

The library `MixedOutputODE` proves Theorem `ode:thm:general` from the solver
guarantee that the manuscript actually requests (eq.
`ode:eq:history-solver-tolerance`): a block-input linear-system solver whose
output, possibly mixed, need only be within conditional trace distance
`δ_LS = ε/(4096 g²)` of the normalised solution (`MixedBlockSolver f q₀`; the
work register holds the solver's work and measurement records, and nothing is
assumed about it). With the access model, public data and instance hypotheses
of `GeneralODE.general`, one protocol, chosen before the input, succeeds with
probability at least `175/256` and, after the work register is discarded, has
conditional trace distance at most `ε` from `x(T)/‖x(T)‖`
(`SparseHamiltonian.MixedOutputODE.general`); for `f = c κ log(2/δ)` it makes
at most `227776401506304000 · c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` matrix queries and
`26292000 · c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of each source
(`general_query_bound`). The pure-output hypothesis of `GeneralODE` implies the
mixed-output one (`mixed_of_block`, `general_of_block`). The selection
constants are weaker than the manuscript's (`MixedOutputODE/Statements.lean`),
and the case `T = 0` is `GeneralODEZeroTime`.

The library `GeneralODEZeroTime` adds the case `T = 0` of `ode:thm:general`,
direct preparation of the initial state, in the same physical oracle model
(`SparseHamiltonian.GeneralODE.general_zero`): one protocol, fixed before the
input, calls the initial-state interface once on the seed inside the released
amplification wrapper. Every history makes no matrix query, no call of the
forcing interface and at most `40` initial-state calls; success has
probability at least `175/256`, and the conditional output is within trace
distance `ε` of `x₀/‖x₀‖` for every `ε ≥ 0`. No `BlockSolver` hypothesis and
no norm bound is needed at `T = 0`. `general_nonneg` states `ode:thm:general`
for every `T ≥ 0` under the hypotheses of `general`, including
`BlockSolver f q₀`, which is used only for `T > 0`, with the budgets of
`general` for `T > 0`.

The library `ZeroTimeRemarks` formalises the zero-time clauses of `hs:thm:main`,
`hs:thm:time` and `hs:thm:gates` and the remark after `ode:thm:main` (inherited
by `ode:thm:time`)
that zero time or a known zero Hamiltonian or generator needs no matrix
queries, each in the oracle family, clean encoding, cost weights and output
guarantee of the released endpoint, together with forms of these endpoints for
every time and every norm bound. For `hs:thm:main` the identity program over
the oracles of `simulation_log_one` makes no query and is exact when `t = 0` or
`η = 0` (`ZeroTimeRemarks.Hamiltonian.simulation_zero`);
`Hamiltonian.simulation_log_one_nonneg` states the theorem for every `η ≥ 0`
with at most `if t = 0 ∨ η = 0 then 0 else 995328 q` queries,
`q = √s τ + √(s τ log(1/ε)) + log(1/ε)`. The time-dependent forms
(`TimeUniform`, `TimeMesh`, `TimeBlock`) do the same for every `T ≥ 0` and
`η ≥ 0` (`α ≥ 0` for time-indexed block encodings; on uniform and general
meshes also with an untouched reference); a known zero
Hamiltonian is the public bound `η = 0`, which forces the represented samples
to vanish, and the identity program then has the certified discretisation
error, at most `ε`. The gate-level forms use the empty circuit on the released
wires at zero time, with no gate and no call and error exactly `0`. For
`ode:thm:main` and `ode:thm:time` the released trial family with the identity
program as SELECT gives, in the native oracle family of the positive case and
with the released seed, flag and complete certificate, a protocol that makes
no matrix query in any history when `T = 0` or `η_H + R η_D = 0`
(`ODEConstant.solver_nonneg`, `ODETime.solver_nonneg`, `ODEMesh.solver_nonneg`,
with the matrix-query budget `if … then 0 else` the released bound). The source
assembly and the source-call bounds are the released ones; at `T = 0` the
forcing preparation is still called, with zero amplitude.

The library `ZeroTimeGateODE` formalises the remark of `ode:thm:gates` that
at `T = 0` and for a known zero generator direct source assembly suffices, with
no propagator query (matrix queries inside the supplied source circuits still
count), without results from other papers; the released gate-level
endpoints assume `T > 0` and `λ_H + R λ_D > 0` (`η_H + η_D > 0` for binary
data) and embed the released simulator as SELECT. Direct source assembly is a
new preparation: the source rotation `srcRot T r₀ r_b` on the source-label
wire, the supplied source circuits controlled on it and the inverse rotation
(`zprepC`; for time-dependent coefficients the weight preparation, the loading
circuit and the inverse weight preparation, `tzprepC`), with no LCHS register,
simulator, private operation, `U_J` or arithmetic; its exact-gate forms
(`zprepE`, `tzprepE`) run in the released instruction model. Its successful
amplitude `‖x(T)‖/B` lies in `[1/g, 1]` and can exceed the range of the
released amplification theorem; `randomized_certificate_full` removes its
hypothesis `a ≤ 1/2`, so the released four-attempt protocols, cutoffs and
guarantees are reused unchanged. With native implementations
(`native_ode_solver_zero`, `native_ode_time_solver_zero`) every history makes
at most `40 g` times (time-dependent coefficients: `80 g` times) the calls of
one preparation, which are exactly those of the supplied circuits, and the
protocol meets `GateNative.NOutcome` against `x₀ + T b` (time-dependent
coefficients: `x(T)`, through the released discretisation budget) with
`2ζs ≤ ν` (`3ζs ≤ ν`) and no condition on `U_J`, the private operations or the
arithmetic; with exact gates (`exact_ode_solver_zero`,
`exact_ode_time_solver_zero`) no history calls `U_J` or a private Cayley
operation. The `*_nonneg` forms state the exact-gate, native and binary-data
endpoints, and the finite-gate-set endpoints with the per-trial claim, for
every `T ≥ 0`, with circuits and counts
`if <zero case> then <direct source assembly> else <released>` and every
released size conclusion; from binary data the protocols make no sparse-oracle
call in the zero case beyond those of the source circuits
(`binary_zero_no_matrix_calls`, `binary_time_zero_no_matrix_calls`). At
`T = 0` the forcing circuit is still applied, with weight zero.

### Lower bounds and Dyson constructions

The linear-system lower bound uses no result from another paper. For `κ ≥ 32`,
an integer `s ≥ 5` and `0 < ε ≤ 1/64`, the hard family consists of real
symmetric, indefinite matrices `A_X` (Hermitian dilations of open-clock
matrices built from dense gadgets whose entries depend on one hidden bit each)
with `‖A_X‖ ≤ 1`, `‖A_X⁻¹‖ ≤ κ`, at most `s` input-independent possible
nonzero positions in every row and column, dimension `N` with
`s κ ln(1/ε)/32 < N ≤ (s - 1) κ ln(1/ε)`, actual condition number
`κ/16 < ‖A_X‖ ‖A_X⁻¹‖ ≤ κ` (the upper dimension bound and the lower
condition-number bound are proved through the copy of this family in the
`SparseLowerBounds` library, `LinearSystemLowerBound/Bridge.lean`), and a
fixed unit right-hand side `b`. Take any native sparse data for these matrices
with input-independent location oracles and a value oracle that encodes the
entries. Every adaptive protocol whose oracle calls are native queries or
their inverses in fixed layouts (so also controlled versions, spectators and
coherent choices among queries), or input-independent unitaries, and which on
every input succeeds with probability at least `2/3` and outputs, conditional
on success, a state whose reduced state on the output register (the output may
be entangled with any finite garbage register) is within trace distance `ε` of
`A_X⁻¹b/‖A_X⁻¹b‖`, makes more than `κ √s ln(1/ε)/1536` native queries in the
worst case (`LinearSystemLowerBound.lower_bound_sharp`; `lower_bound` states
the paper's `1/3072`; the `*_readout` forms read the output through any fixed
linear map of norm at most one, such as an isometry, so the output register
may have any dimension, as for qubits; relating accuracy on a larger register
to this form is a channel argument that is not formalised). The location
oracles are input-independent, so calls of them alone may be left uncounted
and the bound holds for value queries alone. Adaptivity through fresh measured
runs and classical branching is covered directly; measurements inside a run
followed by classically controlled operations are covered by the usual
deferral of measurements, which keeps the worst-case count and is
formalised in `DeferredMeasurementLowerBounds` (`Deferral.deferral`,
`Corollaries.lower_bound_sharp_measured`). The released algorithm of the
linear-system endpoint satisfies
these hypotheses on the hard family, so its worst-case count `Q` obeys
`κ √s ln(1/ε)/1536 < Q ≤ 4·10¹² √s κ ln(1/ε)`
(`LinearSystemLowerBound.upper_meets_lower`).

The Hamiltonian-simulation lower bound is an external development, included as
the library `SparseLowerBounds`; it uses no result from another paper. For
`τ ≥ 1`, an integer `s ≥ 32` and `0 < ε ≤ 1/64`, with `L = ln(1/ε)`,
`h = ln(e + L/τ)` and `r = L/h`, it constructs three hard families of real
symmetric sparse Hamiltonians (spin chains decorated with search gadgets for
the time and mixed families, a signed chain for the precision family) with
operator norm and maximum row and column norms exactly one, sparsity exactly
`s`, exact dyadic entries, input-independent location oracles and dimension at
most `4 s (τ + r + 1)`. Consider non-adaptive programs over the released
native primitives of a family, inverses included, with or without a spectator
register, run on an input-independent seed and read through a fixed isometry
into system and garbage registers, whose output on every input is within trace
distance `ε` of `e^{-iτH_X} ψ_in` (in observable form, which allows mixed
outputs). For any three such programs on the three families,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` value queries with
`c₀ = log 2/(4096π)` (`SparseLowerBounds.Hamiltonian.main_max` with spectator
registers, `main_max_native` without; by `main_exists`, one of the three
families forces this bound on every accurate program with a spectator
register); location queries are free. The combined bound also holds with a
success flag of probability at least `2/3` and conditional accuracy
(`odel:lem:herald`, `main_max_herald`), under the released endpoint error
(`main_max_endpoint`), and for every program over the released simulator's
oracle family (`main_max_release`). For the released simulator on the hard
families, `c₀ S ≤ max Q ≤ max count ≤ 995328 h S` with `S = √s τ + √(sτr) + r`
(`release_theta_bracket`). In that library controlled value calls are covered by
a documented reduction to the spectator form, without a Lean lemma; the
adaptive library below covers them directly.

The library `AdaptiveHamiltonianLowerBound` proves `hsl:thm:main` for adaptive
algorithms, again without results from other papers. The algorithms are the
adaptive protocols of the linear-system endpoint (fresh measured runs with
classical branching, then fresh trials with uniformly random labels and
repeats, and a heralded output), and every oracle label is admissible for the
hard data as in the linear-system lower bound: a native call in a fixed
layout of the workspace as copies of the native query space (spectators,
controlled and masked calls, inverses and coherent choices of the native
query), counted with weight at least one, or an input-independent unitary.
If such an algorithm succeeds on every input with probability at least `2/3`
and its conditional output, read through a fixed isometry into system and
garbage registers, is within trace distance
`ε` of `e^{-iτH_X} ψ_in` (observable form), then for any three such algorithms
on the time, mixed and precision families
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, where `Q` is the worst-case
weighted number of calls over all transcripts
(`AdaptiveHamiltonianLowerBound.main_max_tree`; family form
`main_exists_tree`); with the weight that counts value calls only, `Q` is the
worst-case number of value queries. The proof carries a positive semidefinite
kernel through the protocol, as in the linear-system lower bound, with the
paper's search weight; a value call costs one growth factor instead of two
Boolean queries, and the precision family is treated with the same weight
method on one-hot strings of length two instead of the Fourier-degree
argument. As for the linear-system lower bound, measurements inside a run
followed by classically controlled operations (and measurements with more
than two outcomes) are covered by the usual deferral of measurements, which is
formalised in `DeferredMeasurementLowerBounds` (`Corollaries.main_max_measured`;
for the time-dependent class `Corollaries.main_max_measured_access`). A
non-adaptive program with a unit seed is the special case of
one fresh trial: `main_max_programs` covers programs with controlled calls, and
`main_max_spec_programs` gives the released spectator form for unit seeds and
an isometric readout.

The dissipative-ODE lower bounds (library `ODELowerBounds`, modules
`SparseLowerBounds/ODE`) are an external development of the same origin as the
Hamiltonian lower bound, added here; they use no result from another paper. A
family of the time-dependent dissipative class `x' = A(t) x + b(t)`,
`-A = D + iH`, `D ⪰ 0`, has public piecewise-constant stages whose generators
are read through the released coherent sampled-time native oracles
`∑ |i,k⟩⟨i,k| ⊗ O_l(x,k)`, public sources and a public initial state; the
class asks for row and column norms at most one, `T = τ` and a solution with
`x(T) ≠ 0` and `B ≤ ḡ ‖x(T)‖`, `B = ‖x₀‖ + ∫ ‖b‖`. A solver is a non-adaptive
program over this access with any spectator register, a seed of norm at most
one, an isometric readout into system and garbage registers and a herald, with
success probability at least `2/3` on every input and conditional accuracy `ε`
(observable form of trace distance) for `x(T)/‖x(T)‖`. For an integer
`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2` and `0 < ε ≤ 1/64`, one of three families forces
every solver to make at least `c (ḡ √s τ + √(sτr) + r)` value queries,
`c = log 2/(8192π)` (`SparseLowerBounds.ODE.combined`; max form
`combined_max`): the joint family of `odel:thm:joint` (inhomogeneous and
time-dependent, `D = 0`, `g = √M ∈ [ḡ/√2, ḡ]`), which alone forces
`ḡ √s τ/400` (`joint_witness`, from the adversary bound `outer_count_ge` of
`odel:lem:outer`), and the mixed and precision families of the Hamiltonian
lower bound read as homogeneous ODEs with `g = 1` (`mixed_forces`,
`precision_forces`, `precision_forces_sqrt`; one of them witnesses
`c₀ (√(sτr) + r)`, `precision_terms_witness`). With the time family, these
`g = 1` families give eq. `odel:eq:hsbound` in the ODE model
(`herald_witness`). Controlled calls are covered by a documented reduction
without a Lean lemma (the adaptive ODE lower-bound library below proves it,
`AdaptiveODELowerBound.Access.implementsOn_callFamily`), and that library states
no matching ODE upper bound (the extensions library below states the bracket).

The library `LowerBoundRemarks` formalises three remarks on these lower
bounds, again without results from other papers. If every entry of `H_X` is
affine in the membership bits of `n` independent uniformly random input blocks
and `σ(X)` is a balanced block parity, then `E_X[σ(X) H_X^k] = 0` for `k < n`
(`LowerBoundRemarks.ParityAmplitude.moment_eq_zero`) and, for signs bounded by
one, `‖H_X‖ ≤ 1` and `τ ≥ 0`, `‖E_X[σ(X) e^{-iτH_X}]‖ ≤ e^τ τ^n/n!`
(`matrix_exp_correlation_le`; the parity-amplitude remark). The hard linear
systems padded to `A_X ⊕ I`, with the right-hand side extended by zero, keep
the promise and the bound `κ √s ln(1/ε)/1536` in any larger dimension
(`LinearSystemPadding.pad_lower_bound_sharp`, `lower_bound_common_dimension`),
and the three hard Hamiltonian families padded by known zeros keep their
instance properties (`hard_instances_pad`) and, in one common dimension,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` for the non-adaptive spectator
form (`HamiltonianPadding.main_max_common_dimension`, family form
`main_exists_common_dimension`).

The library `ODELowerBoundExtensions` extends the ODE lower bounds, again
without results from other papers. For `s ≥ 32`, `τ ≥ 1` and `L ≥ 64τ`, one of
two homogeneous constant-coefficient families with `D_X ⪰ 0`, `‖D_X‖ = 1`,
`T = τ` and `1 ≤ g ≤ √2` forces every heralded solver to make at least
`log 2/(3072√2) (√(sτr) + r)` value queries (`ODELowerBoundExtensions.Psd.psd`,
max form `psd_max`; Theorem `odel:thm:psd`). For `τ ≥ 20(1 + log ḡ)` the
source-free variant of the joint family, with one dissipative stage, forces
`ḡ √s τ/500` with `g = Θ(ḡ)` (`Homogeneous.hom_witness`, `hom_g_theta`;
Proposition `odel:rem:homogeneous`). Padded by known zeros, and with a dense
block of dyadic entries for the joint family, the three hard families of
`odel:thm:combined` have maximum sparsity exactly `s` and keep the combined
bound in every common dimension at least their three dimensions (for example
every `Nd ≥ 3 ḡ² s` with `Nd ≥ 4 s (τ + r + 1)`), in particular on every large
enough qubit register (`Padding.combined_common_dimension`,
`combined_qubit_register`). These three results are stated for single heralded
programs (`SparseLowerBounds.ODE.Solver`). The class of solvers is widened to
the release's bounded retry protocols (`ODERepeatProtocol.Protocol`: a random
circuit label and a fresh seed per attempt, the first heralded success decoded),
which contain every `Solver`; `odel:thm:combined` holds for them with the same
constant (`Release.combined_retry`, `combined_max_retry`) and over the physical
oracle of the released general-mesh solver `TimeDependentExtensions.ODE.solver`
with public source interfaces (`Release.combined_max_release`, the analogue of
`main_max_release`). For release runs of that solver on the three hard families,
`c S ≤ max Q ≤ 2548039680 ḡ (√s τ + √(sτℓ) + ℓ) ≤ 7644119040 ℓ S` with
`S = ḡ √s τ + √(sτr) + r`, `c = log 2/(8192π)` and `ℓ = log(40000 ḡ/ε)`
(`Release.release_theta`; such runs exist, `release_theta_bracket`), and on the
joint family alone, for `τ ≥ ℓ`, `ḡ √s τ/400 ≤ Q_J ≤ 7644119040 ḡ √s τ`
(`joint_release_theta`): upper and lower bounds agree within one factor `ℓ` up
to constants, and up to a constant on the joint family. Lemma `odel:lem:dyson`
is proved outright, with the source access of the released time-dependent solver
(public norms of the initial state and of one forcing sample per mesh cell,
unitary direction interfaces and the positive cell quadrature) in place of the
general source interface of eqs. `ode:eq:source-interface-mass` and
`ode:eq:source-interface-preparation` used in the manuscript's proof: under the
coherent time access, certified time discretisation and this source preparation,
a truncated Dyson series on a six-query block encoding of the sampled generator
gives one public four-attempt trial family satisfying the released complete
certificate with at most `16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))` matrix
queries, `z = s Λ T` (`Λ` the public entry bound of the data, `Λ = η` on the
lower-bound class) and `L_g = log(4000 ḡ/ε)`
(`ODELowerBoundExtensions.Dyson.dyson`; it covers the released solver's input
class, `dyson_release_class`). On the ODE lower-bound class it gives retry
solvers with `O(log(1/ε)/log log(1/ε))` queries at fixed `s`, `τ`, `ḡ` (eq.
`odel:eq:fixed`, `Dyson.retry_fixed`), so no family of the class witnesses
`c ḡ √s τ log(ḡ/ε)` against retry protocols for small `ε`
(`Dyson.no_retry_witnesses`).

The library `DysonSingleProgram` proves Lemma `odel:lem:dyson` on the ODE
lower-bound class as one heralded program of the single-program solver class
`SparseLowerBounds.ODE.Solver`, again without results from other papers. For
`η > 0`, `T > 0`, `ḡ ≥ 1` and `0 < ε ≤ 1`, every family of `InClass η ḡ` has a
solver over its own access `F.access ι` whose program makes at most
`16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))` calls, inverse calls included,
`z = s η T`, `L_g = log(4000 ḡ/ε)` (`DysonSingleProgram.solver_dyson`, with the
hypotheses and bound of `Dyson.retrySolver_dyson`). The program
(`exists_solver_of_shape`, `fourAttempts`) runs the four attempts of the
released Dyson trials on separate registers: each attempt holds its uniformly
random amplification cutoff coherently in a label register, controlling only
the fixed reflections (no oracle call is controlled), and is then parked by a
fixed basis permutation; the herald is the OR of the four success flags, and a
fixed, query-free readout isometry decodes the first heralded attempt. It
reproduces the released four-attempt law exactly (`Parallel.Stage.good_four`)
at four times the largest-cutoff count, the released worst case. The
amplitude-amplification shape of the released trials, hidden by the released
existential statements, is re-proved with them (`Explicit.dyson_grover`,
`Explicit.family_dyson_grover`, with the bound `Explicit.bound_le_dysonBound`).
The joint hard family of `odel:thm:joint` meets the hypotheses, and its single
program makes between `ḡ √s τ/400` and the bound above calls
(`solver_dyson_joint`). At fixed `s`, `τ`, `ḡ` single programs therefore reach
`O(log(1/ε)/log log(1/ε))` calls (eq. `odel:eq:fixed`, `solver_fixed`), and for
every `c > 0` and all small `ε` no family of the class witnesses
`c ḡ √s τ log(ḡ/ε)` for single programs (`no_witnesses`, which implies the
released `Dyson.no_retry_witnesses`) or for adaptive solvers
(`no_tree_witnesses`).

The library `DysonGeneralAccess` proves Lemma `odel:lem:dyson` as one heralded
program on its general certified-mesh access with source preparation (the
released access `ODELowerBoundExtensions.Dyson.oracle`, with the source access
of the released time-dependent solver), again without results
from other papers. The class `Model.HeraldedSolver` has the fields of
`SparseLowerBounds.ODE.Solver` with the access and a valid-instance relation
as parameters; `Solver` is its specialisation (`Model.ofSolver`,
`Model.toSolver`). The mesh, its cell-to-sample map and the source norms stay
public parameters of the access, as the manuscript selects the mesh classically
from the public certificate. Under the hypotheses of `Dyson.dyson` there is one
heralded program over the access with a spectator register that solves every
instance meeting the premises of the released outcome (`Dyson.Valid`) with
success probability at least `2/3`, conditional accuracy `ε` and at most
`16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))` matrix queries, inverse calls
included, `L_g = log(4000 ḡ/ε)` (`Dyson.single_dyson`); source calls are not
counted. The program (`Core.single`) is the four-attempt construction of
`DysonSingleProgram` over any unitary access whose trial family has the
amplification shape and the released complete certificate; its success equals
the success mass of the released four-trial wrapper (`Core.single_success`).
The released time-dependent class is covered (`Dyson.single_release_class`),
eq. `odel:eq:fixed` and its consequence hold for these programs
(`Dyson.single_fixed`, `Dyson.single_no_uniform`), and the theorem
`DysonSingleProgram.solver_dyson` is re-derived from the general construction
(`Family.solver_dyson_of_core`).

The library `AdaptiveODELowerBound` proves the dissipative-ODE lower bounds for
adaptive solvers, again without results from other papers; the released ODE
lower-bound libraries are unchanged. A solver (`AdaptiveODELowerBound.Model.TreeSolver`)
is an adaptive protocol of the linear-system endpoint (fresh measured runs with
classical branching, then fresh trials with uniformly random labels and a
heralded output) over the sampled-time access of the class or over its call
forms (each label as a call, its inverse, its controlled form
`|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l` and the controlled inverse), with any branch
register, an isometric readout into system and garbage registers, success
probability at least `2/3` on every input and conditional output within trace
distance `ε` of `x(T)/‖x(T)‖` (observable form); the count is the worst-case
number of value calls over all transcripts, every run, attempt, inverse and
controlled call included, and it also bounds the number of all calls. With the
released families, ranges and constants, for `s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2` and
`0 < ε ≤ 1/64` one of the joint, mixed and precision families forces
`c (ḡ √s τ + √(sτr) + r)` value calls, `c = log 2/(8192π)`
(`AdaptiveODELowerBound.combined_tree`; max forms `combined_max_tree`,
`combined_max_cost_tree`); the joint family alone forces `ḡ √s τ/400`
(`Joint.joint_witness_tree`, from a positive-weight adversary for protocol trees,
`Joint.outer_count_ge_tree`), its source-free variant `ḡ √s τ/500`
(`Joint.hom_witness_tree`), one of the `g = 1` families
`c₀ (√s τ + √(sτr) + r)` (`herald_witness_tree`) and one of the positive
semidefinite families `log 2/(3072√2) (√(sτr) + r)` (`Psd.psd_tree`, by the
weight method of the adaptive Hamiltonian lower bound). The padded families keep
these bounds in every common dimension and on qubit registers
(`Padding.combined_common_dimension_tree`, `combined_qubit_register_tree`), and
adaptive solvers over the physical oracle of the released general-mesh solver
with public source interfaces obey the max form for value and matrix counts
(`Release.combined_max_release_tree`). That an inverse or controlled value call
costs at most two Boolean membership queries, and a location call none, is a
Lean lemma (`Access.implementsOn_callFamily`), so controlled calls are no longer
covered only by a documented reduction. Retry protocols are the trees without
measured runs (`Model.retryToTree`), so the positive semidefinite, source-free
and padded bounds also hold for them (`psd_retry`, `hom_witness_retry`,
`combined_common_dimension_retry`, …). As for the adaptive Hamiltonian lower
bound, measurements inside a run followed by classically controlled operations
are covered by the deferral of measurements, formalised for the sampled-time
access and its call forms in `DeferredMeasurementLowerBounds`
(`Corollaries.combined_measured`, `measuredForces_of_treeForces`), and over the
released physical oracles in `ReleasedODESolverLowerBounds` below; controlled
calls of the released physical oracle and the constant-coefficient released
solver of `ode:thm:main` are covered by the libraries `PhysicalODELowerBound`
and `ConstantODELowerBound` below.

The library `ConstantODELowerBound` applies these lower bounds to the released
constant-coefficient solver `SparseHamiltonian.ODECompleteEndpoint.solver` of
`ode:thm:main`, again without results from other papers, on the hard families
that are constant-coefficient equations. On a one-stage family the solver runs
on the stage-0 data `ConstantODELowerBound.Oracle.constData F` and calls the
released physical oracle on these data (`Oracle.constOracle`), every matrix
label of which is one native call in a fixed isometric layout
(`Normal.physicalOracle_normal_form`). For adaptive solvers and retry protocols
over this oracle (any branch register, mesh size, slot count and degree,
public source interfaces, inverse calls counted), on `HSRange` the time, mixed
and precision families with `g = 1` force `c₀ (√s τ + √(sτr) + r)` value calls
and matrix calls in max form, `c₀ = log 2/(4096π)` (`Herald.herald_max_const_tree`,
`herald_max_const_retry`; Lemma `odel:lem:herald`), and on `PsdRange` the two
positive semidefinite families force `log 2/(3072√2) (√(sτr) + r)`
(`Psd.psd_max_const_tree`, `psd_max_const_retry`; Theorem `odel:thm:psd`).
Every certificate family of the released solver's positive-time branch on
these data gives a released protocol over that oracle
(`Solver.constProtocol_of_certificate`), and the solver takes that branch
under its hypotheses (`Solver.exists_constProtocol`); with public source
interfaces preparing `x₀/‖x₀‖` and `b/‖b‖` from a unit seed it is a run
(`Runs.ConstRun`). For runs on the `g = 1` families
`c₀ S ≤ max Q ≤ 1274019840 ḡ (√s τ + √(sτℓ) + ℓ)` with
`S = √s τ + √(sτr) + r` and `ℓ = log(10⁴ ḡ/ε)` (`Runs.herald_const_bounds`;
such runs exist for `ḡ ≥ 1`, `Instances.herald_const_bracket`), and on the
positive semidefinite families the lower bound and the released bound
`1274019840 ḡ (√s τ ℓ + √(s τ ℓ²) + ℓ)` hold side by side
(`Runs.psd_const_bounds`; runs exist for `ḡ ≥ √2`). The joint `ḡ √s τ` term
is not claimed for constant-coefficient equations, as in the manuscript.

The library `PhysicalODELowerBound` states the ODE lower bounds over the
physical oracles of both released ODE solvers and over their call forms (plain,
inverse, controlled and controlled-inverse calls of every label), again without
results from other papers. `Mesh.MeshForces F ε b` says that every adaptive
solver of `F` over the general-mesh solver's oracle (any placement, spectator
index, slot count, degree and public source interfaces) or over its call forms
makes at least `b` value calls and `b` matrix calls in the worst case;
`Const.ConstForces` is the same over the constant-coefficient solver's oracle.
In family form, on `PsdRange` and for `ḡ ≥ √2` one of the two positive
semidefinite families witnesses `log 2/(3072√2) (√(sτr) + r)` over either oracle
(`Mesh.psd_mesh`, `Const.psd_const`; Theorem `odel:thm:psd`); on `HSRange` and
for `ḡ ≥ 1` one of the `g = 1` families witnesses `c₀ (√s τ + √(sτr) + r)` over
either oracle, also with known zero padding, and in one common dimension or on a
qubit register over the constant-coefficient oracle (`Mesh.herald_witness_mesh`,
`Const.herald_witness_const`, `Const.herald_common_dimension_const`,
`Const.herald_qubit_register_const`); over the general-mesh oracle the joint
family witnesses `ḡ √s τ/400` (`Mesh.joint_witness_mesh`, padded
`Mesh.joint_witness_pad_mesh`), the source-free variant `ḡ √s τ/500`
(`Mesh.hom_witness_mesh`; Proposition `odel:rem:homogeneous`), and on
`CombinedRange` one of the joint, mixed and precision families witnesses
`c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)`, also padded, in one common
dimension and on a qubit register (`Mesh.combined_mesh`,
`Mesh.combined_common_dimension_mesh`, `Mesh.combined_qubit_register_mesh`). The
time-dependent families are stated over the general-mesh oracle only. Every call
form of a label of the general-mesh solver's oracle is implemented by the
Boolean membership queries of its label (for a family with a Boolean certificate
of its sampled-time access), two per value call
(`Access.implementsOn_mesh_calls`), and every call form of a label of either
oracle has its label's search-weight growth (`Access.searchGrowth_mesh_calls`,
`Const.searchGrowth_const_calls`). Retry protocols, every released protocol of
the general-mesh solver at any parameters and the runs of the
constant-coefficient solver are covered (`Mesh.MeshForces.retry`,
`Mesh.MeshForces.releaseProtocol`, `Const.ConstForces.retry`,
`Const.ConstForces.constRun`; `releaseRun` for the general-mesh runs on families
with `D = 0`), and the max forms of `AdaptiveODELowerBound` and
`ConstantODELowerBound` are restated with identical statements
(`Mesh.combined_max_release_tree_of_mesh`,
`Const.herald_max_const_tree_of_const`, `Const.psd_max_const_tree_of_const`).

The library `DeferredMeasurementLowerBounds` formalises the deferral of
measurements behind the lower-bound sections ("Purification and deferred
measurement include adaptive and randomised algorithms"; "after coherent
purification and padding to their worst-case query count"), again without
results from other papers. A measured algorithm (`Model.Measured`) is a finite
tree of oracle calls, forward or inverse, and input-independent instruments with
finitely many outcomes on one persistent workspace of any dimension, each
instrument followed by a classically chosen continuation (multi-outcome and
generalised measurements in the middle of a run, randomness, known unitaries,
classical control and resets of finite-dimensional registers), ending in a
heralded output through an isometry or in rejection. It starts from an
input-independent unit vector, and its cost is the worst case over all
transcripts, including those of probability zero, as for the adaptive protocols
of the package, which are measured algorithms on finite-dimensional workspaces
(`Model.ofTree`, with the same success probability, output and worst-case cost).
For every choice of counted labels, every measured algorithm over unitary labels
is one unitary program over the record-selected calls `Σ_r |r⟩⟨r| ⊗ O(π r)` of
its labels and known unitaries, with the same success mass and, after discarding
the record registers, the same heralded output, making at most the measured
algorithm's worst-case number of counted calls (`Deferral.deferral`; for a
measurement inside a run followed by a classically controlled call,
`NonVacuity.deferral_midRun`). A record-selected call of admissible native
labels is one native call, and a record-selected call of the phase oracle or of
the sampled-time value call is one controlled call (an inverse value call is a
value call conjugated by the known negation of the value register), so no
constant is lost: `hsl:thm:main` (`Corollaries.main_max_measured`,
`main_exists_measured`; for the class of `hs:thm:time` over the coherent
sampled-time access and its call forms `main_max_measured_access`,
`main_max_measured_calls`), `qlsl:thm:main` (`lower_bound_sharp_measured`,
`lower_bound_measured`) and `odel:thm:combined` with its witness sentences
(`combined_measured`, `combined_max_measured`, `joint_witness_measured`,
`precision_terms_witness_measured`) hold for measured algorithms with the
constants and hypotheses of the adaptive forms, and measured and tree forcing
are equivalent for the ODE families (`measuredForces_of_treeForces`,
`treeForces_of_measuredForces`). Measured algorithms over the entry oracle of
the search family and its inverse that implement every `U_m` with success
probability one and per-input trace distance `ε₀ ≤ 1/2` make at least
`(1 - 2√(ε₀(1 - ε₀))) √(N - 1)/2` entry calls (`entry_count_ge_measured`,
`implementation_count_ge_measured`, with heralded forms), which is `Ω(√N)` for
every fixed `ε₀ < 1/2`. The released linear-system algorithm and the released
unitary circuits, as measured algorithms, meet these hypotheses
(`NonVacuity.released_linear_system_measured`, with worst-case count between
`κ √s ln(1/ε)/1536` and `4·10¹² √s κ ln(1/ε)`, and
`NonVacuity.released_unitary_measured`). General single-label controlled access
loses at most a factor `2` when one label is counted (none when its inverse is a
known conjugation) and at most `2 · #{counted labels}` in general
(`Access.worstCost_ctrlTree`, `Access.worstCost_ctrlTree_conj`,
`Access.worstCost_ctrlTreeOf`); no corollary uses this access.

The library `ReleasedODESolverLowerBounds` states the ODE lower bounds for
algorithms with measurements inside a run over the physical oracles of both
released ODE solvers (Section `odel:sec:main`: "the lower bounds apply to the
upper bounds of the preceding section"), again without results from other
papers. A measured solver
(`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver`) over either oracle
or over its call forms is deferred; its record-selected calls become controlled
calls of the oracle lifted to the record register, and this lift is absorbed
into the same released oracle with an enlarged spectator index by an isometry
(`Access.exists_absorb`, `Transport.Absorbs`), which
`PhysicalODELowerBound.Mesh.MeshForces` and
`PhysicalODELowerBound.Const.ConstForces` cover since they quantify over every
spectator index. An inverse value call is a value call conjugated by the known
negation of the value register, and source calls are known gates of the public
sources, so no constant is lost: forcing over an oracle implies forcing for
measured solvers with the same bound, and conversely on a nonempty input set
(`Mesh.measuredMeshForces_of_meshForces`,
`Const.measuredConstForces_of_constForces`,
`Mesh.meshForces_of_measuredMeshForces`,
`Const.constForces_of_measuredConstForces`). Hence over the general-mesh oracle,
on `CombinedRange` one of the joint, mixed and precision families witnesses
`c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)`, for measured solvers, also
padded, in one common dimension and on a qubit register, and in max form at
named measured solvers (`Mesh.combined_measured_mesh`,
`Mesh.combined_common_dimension_measured_mesh`,
`Mesh.combined_qubit_register_measured_mesh`,
`Mesh.combined_max_release_measured_mesh`), and the joint and source-free
families witness `ḡ √s τ/400` and `ḡ √s τ/500`
(`Mesh.joint_witness_measured_mesh`, `Mesh.hom_witness_measured_mesh`); over
either oracle, on `HSRange` and for `ḡ ≥ 1` one of the `g = 1` families
witnesses `c₀ (√s τ + √(sτr) + r)`, and on `PsdRange` and for `ḡ ≥ √2` one of
the positive semidefinite families witnesses `log 2/(3072√2) (√(sτr) + r)`
(`Mesh.herald_witness_measured_mesh`, `Mesh.psd_measured_mesh`,
`Const.herald_max_release_measured_const`,
`Const.psd_max_release_measured_const`, with padded, common-dimension and
qubit-register forms of the `g = 1` families in `Const.Padded`). The
time-dependent families are stated over the general-mesh oracle only. Runs of
the released general-mesh solver on the positive semidefinite and homogeneous
families are certified by the solver at `Θ = τ η_H + τ η_D ℓ ≥ τℓ` rather than
at the `Θ = τ` fixed by `ODELowerBoundExtensions.Release.ReleaseRun`. They are
given as runs at split bounds (`Runs.MeshRun F τ ḡ ε η_H η_D`, with `ReleaseRun`
the case `(1, 0)` in both directions, `Runs.MeshRun.ofReleaseRun`,
`Runs.MeshRun.toReleaseRun`), which the solver yields under its hypotheses
(`Runs.exists_meshProtocol`; the package's `exists_releaseProtocol` is its case
`(1, 0)`, `Runs.exists_releaseProtocol_of_meshProtocol`). With
`ℓ = log(40000 ḡ/ε)` and `queryShape(s, u, ℓ) = √s u + √(s u ℓ) + ℓ`, on
`PsdRange` and for `ḡ ≥ √2` runs `(0, 1)` on the two positive semidefinite
families satisfy
`log 2/(3072√2) (√(sτr) + r) ≤ max Q_matrix ≤ 1274019840 · 2ḡ · queryShape(s, τℓ, ℓ)`
for the maximum of their matrix counts (`Runs.psd_meshRun_bracket`), and on
`HomRange` a run `(1, 1)` on the source-free family satisfies
`ḡ √s τ/500 ≤ Q_value ≤ Q_matrix ≤ 1274019840 · 2ḡ · queryShape(s, τ + τℓ, ℓ)`
for its value count and its matrix count (`Runs.hom_meshRun_bracket`,
`Runs.MeshRun.valueQueries_le`). Every run of either released solver, on a
family with an input, all of whose inputs are solvable, is a measured solver
with the same worst-case counts (`Runs.MeshRun.exists_measuredSolver`,
`Runs.constRun_exists_measuredSolver`), so the measured bounds constrain the
released solvers themselves.

### Linear-system filters and time-dependent extensions

The library `ChebyshevFilter` proves Proposition `qls:prop:chebyshev`, which the
released proof of `qls:thm:main` replaces by the averaging filter of Remark
`qls:rem:averaging` (that proof is unchanged). For a unitary `W` on a
finite-dimensional Hilbert space whose eigenvalues `e^{iθ} ≠ 1` have
`|sin(θ/2)| ≥ b`, `0 < b < 1`, and for `0 < δ < 1`, take `λ = b²/(1 - b²)` and
`d = ⌈arcosh(1/δ)/(2 artanh b)⌉`. The Laurent coefficients `p_j` of
`F(e^{iθ}) = T_d((1 + λ) cos θ + λ)/T_d(1 + 2λ)` are nonnegative, supported on
`-d, …, d` and sum to one, `F(1) = 1`, and `F(W) = ∑ p_j W^j` is within `δ` of
the eigenvalue-one projector in operator norm; the normalisation-one LCU
circuit with `d` signed walk steps has success block exactly `F(W)`
(`ChebyshevFilter.chebyshev_filter`). For a walk `R V† C V` with known `R`, `C`
and an oracle program `V`, a signed step makes exactly the oracle calls of a
forward step (Lemma `qls:lem:signedwalk`), so the circuit costs `d` forward
steps (`chebyshev_filter_program`). For the augmented walk of the
linear-system algorithm and any public `0 < g ≤ g_ξ`,
`d_ξ(δ) = ⌈arcosh(1/δ)/(2 arsinh(4g/(165√s)))⌉` gives error at most `δ` and
`d_ξ(δ) ≤ 23 √s log(2/δ)/g` (`augmented_filter`), and the filter-level
test-probability and final-amplitude facts of the analysis hold with this
filter (`augmented_test_fact`, `augmented_final_fact`). Lemma
`qls:lem:signedwalk` is proved there for walks of the form `R V† C V`.

The library `ChebyshevLinearSystem` proves Theorem `qls:thm:main` end to end
with this filter (`ChebyshevLinearSystem.main`, existential form
`main_exists`). The access model, physical oracle family, cost weights, promise
and guarantees are those of `SparseLinearSystems.Endpoint.main`, and so are the
norm estimator and the `1000` final attempts; every test and final attempt is
the normalisation-one LCU circuit of `d` signed steps of the released walk on
one shared counter register, with `d_j = d_{ξ_j}(1/100)` at `b(ξ_j)` for the
tests and `d_0(ε/1000)` at `b(1/κ)` for the final filter. Lemma
`qls:lem:signedwalk` is proved for the released walk through a chiral symmetry
instead of the form `R V† C V`: a fixed involution `Z` satisfies `Z K Z = -K`
(the padding branch of the released generator is zero), so the fixed gate
`Y = Z R` gives `Y W Y = W†`, and the signed step is the released forward step
on the active counter values between two applications of `Y` on the inverse
ones, with the same `54` matrix-oracle and `2` source calls
(`ChebyshevLinearSystem.signed_walk_step`). Every transcript makes at most
`4.4·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and `1.7·10⁹ √s κ log(1/ε)` calls
of the controlled `U_b` or its inverse, against `4·10¹²` and `2·10¹¹` with the
averaging filter.

The library `ChebyshevLinearSystemFinite` adds the finite-gate allowance of
`qls:eq:finitedegree` and the explicit constants of Remark `qls:rem:constants`.
Its protocol is that of `ChebyshevLinearSystem` with the degrees `d + 1`; the
access model, oracle family, cost weights, promise, norm estimator and final
attempts are unchanged. For every implementation whose runs make the same
oracle calls and whose unnormalised success vectors move by at most
`(10⁻⁴ - δ₀²)/2` in each test and `ε/1000 - δ₀` in each final attempt, with
`δ₀ = sech(2 d^fin artanh b)`, the guarantees of Theorem `qls:thm:main` hold
with at most `2.7·10¹⁰ √s κ log(1/ε)` matrix-oracle calls and
`10⁹ √s κ log(1/ε)` calls of the controlled `U_b` or its inverse
(`ChebyshevLinearSystemFinite.main_amp`). `main` is the special case in which
every known gate is replaced by any query-free circuit and the seed and the
flag or output isometry by nearby ones, the errors adding up to the allowances
(`GateApprox`, `RunApprox`); `main_uniform_sharp` gives explicit uniform
requirements (`1/(1.65·10⁶ √s κ)` per test, `ε/(41250 √s κ)` per final
attempt) and `main_alloc` the manuscript's allocation over signed steps and
coefficient preparations. The estimator analysis is re-proved with the
two-sided test tolerance `|p_F - p_ξ(r)| ≤ 10⁻⁴`. Remark `qls:rem:constants` is
formalised as `d^fin_ξ(1/100) < 112/y`, `d^fin_ξ(δ) ≤ k d^fin_ξ(1/100)` and
`1400 d^fin < q_av` (`finDegree_hundred_lt`, `finDegree_le_kStages`,
`averaging_ratio`, `averaging_ratio_final`), and the exact-gate Chebyshev
algorithm meets the same query bounds (`main_improved`). Centring the averaging
filter of Remark `qls:rem:averaging` keeps its error relative to `P` and its
selected norm, and the released signed-step run of `⌈d/2⌉` steps with an
explicit coefficient seed implements `W^{-⌊d/2⌋} f(W)` exactly
(`CentredAveraging.centred_run`); composed with the equal per-step counts
(`54` matrix-oracle and `2` source calls), the Chebyshev test and final runs
make fewer than `1/1400` of the calls of the forward conservative averaging runs
of `q_av` and `k q_av` steps (`test_query_comparison`,
`final_query_comparison`, `budget_query_comparison`); the centred counts are
stated separately (`averaging_schedules`; `centred_test_ratio`,
`centred_final_ratio`: `700 d^fin_ξ(1/100) < ⌈q_av/2⌉`,
`700 d^fin_ξ(δ) < ⌈k q_av/2⌉`).

The library `TimeDependentExtensions` proves the generalisations stated after
`hs:thm:time` and in the proof of `ode:thm:time`, without results from other
papers. A mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` may be nonuniform, and the path is one
piece per mesh interval, so breakpoints at mesh points are allowed; the
propagator or solution solves each piece on its closed interval, with one-sided
derivatives at the mesh points, and the one-sided sample of interval `r` is the
value of its piece at `t_r`. The clock runs on `N` uniform slots, and slot `k`
reads the sample of the interval containing `k T/N` through a slot-to-sample
map in the clean encoding, so the primitive sampled-time queries and the query
bounds are those of the released theorems; the bounds depend on neither `M`,
`N` nor the regularity of the path. For Hamiltonians (`TimeDependentExtensions.Hamiltonian.simulation`),
under `4 s η T ≤ N`, `9 (√s η T)³ ≤ ε N²` and `9 M √s η T ≤ ε N`, one program
with at most `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))` queries, `τ = η T`,
and one clean encoding are within `ε` of every propagator of every path with
Hermitian, interval-integrable pieces whose integrated sample errors
`∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du` are at most `ε/9`; for
`β_r`-Lipschitz pieces with `‖H_r(t_r) - H̃_r‖ ≤ δ_r` the certificate
`∑_r (β_r Δ_r²/2 + δ_r Δ_r) ≤ ε/9` suffices and the propagator exists
(`simulation_lipschitz`); `simulation_with_reference` adds an untouched
reference register. For ODEs (`TimeDependentExtensions.ODE.solver`), the
released complete certificate of `ode:thm:time` holds on any mesh with the
source mass `B = ‖x(0)‖ + ∑_q Δ_q ‖b̃_q‖` of the nonuniform left-endpoint
quadrature, under the certified budget
`(‖x(0)‖ + b_max T) ∑_r ∫ ‖G_r - G̃_r‖ + ∑_r ∫ ‖b_r - b̃_r‖ + publicError ≤ ε B/(2000 g)`,
where `publicError = s Λ (∑_q Δ_q² ‖b̃_q‖/2 + M (T/N) B)` covers the
quadrature and the refinement (`publicError_le` bounds it on meshes of step at
most `h`); `solver_lipschitz` covers Lipschitz pieces with one-sided samples.
For time-indexed block encodings, Hermitian unitaries `O_r` with
`J† O_r J = H̃_r/α` give the moment interface with `Q = ν = 1`
(`hs:eq:blockspecial`; `BlockEncoding.resolvent_boundary`, `resolvent_moment`,
`endpoint_norm_le`) and a simulation with at most `2304 (α T + 1 + log(3/ε))`
controlled time-indexed queries, inverses included (`hs:eq:blockadditive`;
`BlockEncoding.simulation`). Coherent selection of public durations
(`Coherent.coherent_select`) and of windows `[t_{a_i}, t_{b_i}]`, that is start
times and durations at mesh points (`Coherent.coherent_windows`), uses one
oracle family and one clean encoding fixed by the largest duration `T`; for each
public table a program with at most `663552 (√(2s) η T + √(2s η T ℓ) + ℓ)`
queries, `ℓ = log(2/ε)` (`ℓ = log(6/ε)` for windows), is within `ε` of the
coherently selected evolutions. The paper's nonuniform Cayley steps are
replaced by this refinement, which costs `M (T/N) Λ` and gives the extra slot
condition. Propagators and solutions are classical, so every discontinuity of
the path must be a mesh point; Carathéodory propagators of integrable
Hamiltonian paths are added by the library `IntegrablePathSimulation`, and
Carathéodory solutions of ODEs with integrable generators are not formalised
(the mild solutions of `RepresentedSampleODE` allow merely integrable forcing,
with classical propagators on the mesh pieces).

The library `IntegrablePathSimulation` proves the time-dependent Hamiltonian
theorems for integrable Hermitian paths (the remark after `hs:thm:time` that a
certified bound on the integrated sample errors suffices), without results from
other papers. A propagator (`IntegrablePathSimulation.Propagator.IsPropagator H U T`)
solves `U(s) = 1 + ∫_0^s (-i) H(u) U(u) du` on `[0, T]` with an
interval-integrable integrand; for every interval-integrable path it exists
(Dyson series) and is unique on `[0, T]` (`existsUnique_isPropagator`), it is
unitary when `H` is self-adjoint at almost every time
(`IsPropagator.isUnitary`), and it is within
`∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du` of the mesh product
(`IsPropagator.mesh_error_integral`, `IsPropagator.refined_error`). With the
released oracle families, encodings, slot conditions and counts,
`IntegrablePathSimulation.Hamiltonian.simulation` (also `simulation_dyson`,
`simulation_with_reference`) is within `ε` of every such propagator of every
path that is Hermitian almost everywhere and interval integrable with
certificate at most `ε/9`; `Coherent.coherent_windows` and
`BlockEncoding.simulation` extend the coherent windows and the time-indexed
block encodings likewise. Every piecewise propagator with interval-integrable
pieces is a propagator of the glued path (`Propagator.isPropagator_glue`), and
the released theorems follow with unchanged statements
(`Hamiltonian.simulation_piecewise`, `Coherent.coherent_windows_piecewise`,
`BlockEncoding.simulation_piecewise`). Discontinuities of the path need not be
mesh points; the uniform-mesh and ODE theorems keep their classical
hypotheses, and the gate-level time-dependent theorems are extended to
integrable paths by the library `GateEfficientMesh`.

The library `TimeDependentHamiltonianLowerBound` proves the remark after
`hs:thm:time` that the lower bound of `hsl:thm:main` applies to the
time-dependent class, on uniform meshes, on nonuniform meshes and for
integrable paths, without results from other papers. Constant time-indexed
data `constData D M` repeat a time-independent instance in all `M` samples. On
such data the released coherent sampled-time oracle is the native Cayley-layout
oracle with an untouched time register (`sampledOracle_constData`, by `rfl`),
the bare coherent access `∑_{(i,r)} |i, r⟩⟨i, r| ⊗ O_l(x, r)` is the native
access with the spectator `ι × Fin M` (`coherentAccess_constData`), and every
label of the physical oracle families of the released uniform-mesh and
general-mesh simulators is `U⁻¹ (1_Ω ⊗ O_l(x)) U` for one fixed isometric
identification `U` (`aligned_normal_form`). The predicates `UniformHyp`,
`MeshHyp`, `MeshPath` and `IntegrablePath` bundle exactly the hypotheses of
`TimeDependent.simulation`, `TimeDependentExtensions.Hamiltonian.simulation` and
`IntegrablePathSimulation.Hamiltonian.simulation`, and the three hard families
with constant paths belong to these classes with `η = 1`, `t = τ` and
`β = δ_val = 0` (`uniform_class_members`, `mesh_class_members`,
`meshPath_const`, `integrablePath_const`). Every classical, piecewise or
integral-sense propagator of a constant path is `exp(-iτH)` at `τ`, so the
released error criteria on the constant paths are the endpoint error of the
released lower bounds. For any three programs over the released time-dependent
oracle families of the constant time, mixed and precision data (any schedule
and number of samples, any isometric encoding) that meet the released
guarantee for every path of the class,
`c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` value queries, inverses
included, and the same for the numbers of all calls (`uniform_class_max`,
`mesh_class_max`, `integrable_class_max`; with the criterion on the constant
paths only, `main_max_uniform`, `main_max_mesh`, `main_max_integrable`). The
same holds for adaptive algorithms over the coherent sampled-time access, with inverse and controlled calls, or over the
released families (`main_max_tree_access`, `main_max_tree_calls`,
`main_max_tree_uniform`, `main_max_tree_mesh`). On the constant hard families
the released time-dependent simulators satisfy
`c₀ S ≤ max Q ≤ max count ≤ 995328 h S` (`uniform_theta_bracket`,
`mesh_theta_bracket`), and they meet the hypotheses of the class statements
(`uniform_class_nonvacuous`, `mesh_class_nonvacuous`,
`integrable_class_nonvacuous`) and, run as single trials, those of the adaptive
forms (`single_tree_hyps`, `access_of_uniform`, `calls_of_access`). The hard
instances are constant in time; time-indexed block encodings, coherent
parameter selection, the piecewise Lipschitz corollary, the gate-level
time-dependent theorems and controlled calls of the released physical families
are not covered there.

The library `TimeDependentLowerBoundExtensions` carries the lower bound of
`hsl:thm:main` for the time-dependent classes, with the same constant hard
paths, into four further settings, without results from other papers. In the
time-indexed block-encoding model the hard instances are supplied through the
package's Hermitian dilation `beOp D x` of the released six-query block
encoding, with boundary `beJ D` and normalisation `beAlpha D = s · scale`, so
that `α_BE J† O_r J = H_x` exactly (`blockSample_beOp`), the normalisation
`α_BE = sη` of a standard sparse block encoding. For any three programs over
the released aligned block-encoding families of these encodings (any samples,
slots and schedule) with isometric encodings that meet the error criterion of
the released block-encoding theorem (`BECriterion`), of its integrable-path
form (`BEIntegrableCriterion`) or the endpoint error,
`c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)` block-encoding calls,
inverses included (`main_max_block`, `main_max_block_integrable`,
`main_max_block_endpoint`); the same holds over the controlled time-indexed
oracle itself and over all call forms of the aligned family
(`main_max_block_primitive`, `main_max_calls_block`). The factor `8` (at most
`16` Boolean queries per call) is a constant of the reduction; the manuscript
derives only the upper bound `hs:eq:blockadditive` in this model. With
coherent selection of known durations or start times, programs over the
released selection family whose branch `i₀` has total duration (window length)
`τ` satisfy `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` value calls and
calls (`Coherent.main_max_select`, `Coherent.main_max_windows`,
`Coherent.main_max_windows_integrable`), and the same holds for adaptive
algorithms and over all call forms of that family
(`Coherent.main_max_tree_select`, `Coherent.main_max_calls_select`,
`Coherent.main_max_calls_windows`, `Coherent.main_max_tree_calls_select`). Over
all call forms of the released uniform-mesh, general-mesh and integrable-path
families each value call counts once (`Calls.main_max_calls_uniform`,
`Calls.main_max_calls_mesh`, `Calls.main_max_calls_integrable`,
`Calls.main_max_tree_calls_uniform`, `Calls.main_max_tree_calls_mesh`). For the
package's slot-selected gate-level circuits, whose instance enters only through
the private operation, the bound is
`c₀ (√s τ + √(sτr) + r) ≤ q · max(nPriv_T, nPriv_M, nPriv_P)` private calls
(`Gate.main_max_gate`, `Gate.main_max_gate_uniform`) when each private
operation is realised exactly by a program with at most `q` value calls over
the call forms of the native sparse queries (`NativeRealization`, the exact
form of the fixed primitive-oracle cost per private operation of the
manuscript's gate model); this hypothesis holds with `q = 1` for every single
call form (`Gate.nativeRealization_call`). The released simulators meet the
block-encoding and selection criteria on these families
(`BlockEncoding.exists_beProgram`, `Coherent.exists_selectProgram`,
`Coherent.exists_windowsProgram`); the integrable-path criteria are the
conclusions of the released integrable-path theorems, which supply such
programs directly (not restated). When each private operation is only realised
within operator-norm error `ξ` (`Tolerant.ApproxRealization`, the gate model
of the manuscript; a realisation of the controlled operation within `ξ` gives
one, `Tolerant.approxRealization_of_controlled`), the same bound holds whenever
the endpoint error of the ideal circuit plus `nPriv · ξ` is at most `ε`
(`Tolerant.main_max_gate_tolerant`, `Tolerant.main_max_gate_uniform_tolerant`);
the exact forms are the case `ξ = 0`. For the class of piecewise Lipschitz
paths with breakpoints (`Tolerant.LipschitzPath`, the error criterion of
`TimeDependentExtensions.Hamiltonian.simulation_lipschitz`) the bound holds for
programs over the released general-mesh family and its call forms
(`Tolerant.lipschitz_class_max`, `Tolerant.lipschitz_class_max_calls`). For
algorithms with measurements inside a run over the released uniform-mesh,
general-mesh and integrable-path, selection and block-encoding families and
their call forms, success at least `2/3` and accuracy `hsl:eq:accuracy`
against the constant path give the bound in worst-case value calls
(`Measured.main_max_measured_uniform`, `Measured.main_max_measured_mesh`,
`Measured.main_max_measured_select` and their call forms) and with the factor
`8` in block-encoding calls (`Measured.main_max_measured_block`,
`Measured.main_max_measured_block_primitive`,
`Measured.main_max_measured_calls_block`); block-encoding calls are compiled
into masked native calls before the deferral of measurements. The released
uniform-mesh, general-mesh, integrable-path, duration-selection and
block-encoding simulators, run as measured algorithms on constant data, meet
these hypotheses (`Measured.released_uniform_measured` to
`Measured.released_block_measured`).

### Separate matrix and preparation query bounds

The sparse reduction, norm-estimate transfer, decoding, finite success
amplification and separate native query accounting for Corollary
`qls:cor:separate` are formalised conditional on a stated uniform block-input
solver interface representing Gao–Ji–Liu's result. The external solver theorem
is not formalised in this package. The endpoints
`ManuscriptConformance.qls_cor_separate` and
`ManuscriptConformance.qls_cor_separate_writer` cover additive value access
and reversible writing on clean targets, respectively. Both follow from
`SparseLinearSystems.Separate.main` (`SparseLinearSystems/Separate/`),
through `ManuscriptConformance/LinearSystemSeparate.lean` and, for the
writer form, `ManuscriptConformance/WriterSeparate.lean`.

**Statement.** The native input conventions of `qls_thm_main`: sparse data `D`
with `s ≥ 1` slots, a unitary `U_b` with a known unit seed, `κ ≥ 1`,
`0 < ε ≤ 1/10`, and a public scalar `ν̂`. The hypothesis is
`ext_separateSolver : SeparateSolver cM cb q₀` with `cM ≥ 0`, `cb > 0`,
`q₀ > 0`. The constants are `C_A = 54 N (12 cM + 1)` and `C_b = (73/9) N cb`,
`N = ⌈6/q₀⌉` (`constA`, `constB`), chosen before every input. One protocol
(`Separate.protocol`, at most `N` fresh trials over `Separate.sepOracle`: the
three native primitives and the controlled `U_b`, with the weights `Step.wMat`
and `Step.wSrc` of `qls_thm_main`), fixed before the instance, has at most
`C_A √s κ log(1/ε)` matrix queries on every completed history, for every
input. On every input with `‖A‖ ≤ 1`, `A` invertible, `‖A⁻¹‖ ≤ κ` and
`ν/2 ≤ ν̂ ≤ 2ν`, `ν = ‖A⁻¹ b‖`, it has at most `C_b κ/ν` calls of `U_b` and
`U_b†` on every completed history, success probability at least `2/3`, and
conditional output a density operator within trace distance `ε` of
`A⁻¹b/‖A⁻¹b‖`. The preparation bound is inside the valid-instance quantifier;
`1 ≤ ν ≤ κ` is derived from the promises. `ν̂` is a classical input; the cost
of obtaining it is not counted (the protocol uses `max(ν̂, 1/2)`, equal to `ν̂`
on every valid instance, to keep the solver's estimate positive).

**The interface** (`Separate/SolverInterface.lean`). `SeparateSolver cM cb q₀`
is a `def … : Prop` passed as a theorem argument, never an axiom. For all
finite-dimensional system spaces `E`, register spaces `G`, public isometries
`ι : E → G`, unit seeds `r₀ ∈ G` and public `κ ≥ 2`, `0 < δ < 1/2`, `η > 0`,
there are one circuit `S` and one isometric output selector `out`, chosen
before the oracle pair, with at most `cM κ log(2/δ)` block-encoding calls and
at most `cb (1 + κ/η)` preparation calls (`S.labelCount`; inverse calls are
counted), such that for every unitary `U` and `P` with `P r₀ = ι β`,
`‖β‖ = 1`, `‖v‖ ≤ κ ‖M v‖` for `M = ι† U ι`, and every `y` with `M y = β` and
`(3/8) ‖y‖ ≤ η ≤ (5/2) ‖y‖`, the selected vector `a = out† S ψ₀` has
`‖a‖² ≥ q₀` and direction within `δ` of that of `y`, up to a phase. `M` need
not be Hermitian. This single-circuit, fixed-selector form is stronger than
the statement of Theorem 5.7 of Gao, Ji and Liu (arXiv:2609.33686), whose
success probability `2/3` comes from repeated measurements. It is intended
to follow from their proof: one Hermitian-input run with constant acceptance
probability, their Hermitian reduction for a general block-encoded matrix and
the selection of the lower system sector, before any outer repetition. That
derivation is not formalised; the proof here uses only `q₀ > 0`. The block
encoding is relative to a public isometric encoding of `E` in `G` (a
projected encoding; the product encoding
`v ↦ v ⊗ |a₀⟩` of `GeneralODE.Solver.BlockSolver` is a special case). The
axiom audits of the endpoint list only the standard axioms; that does not
discharge this hypothesis.

**Reduction** (`Separate/Algebra.lean`, `Separate/Bounds.lean`). General
matrices are covered directly. The public split boundary `J`, the edge
generator `K` and `α = √s` satisfy the hypotheses of Lemma `qls:lem:walk` for
the dilation `H = [[0, A], [A†, 0]]` with `μ = 1`, `k₀ = √s` (`hyp`). With
`D₀ = (K + i)(K - i)⁻¹`, `R₀ = (I + iK)/2`, `W = (I - 2JJ†) D₀`,
`B = (I - W)/2` and `C = (I - D₀)/2`: `(I - W) R₀ J u = (i/α) J H u` for every
`u` (`one_sub_walk_resolvent`); `W` has no nonzero fixed vector on the whole
logical edge space (`walk_fixed_eq_zero`); with the chord gap of Lemma
`qls:lem:walk`, which includes the eigenvalue `-1`,
`t*/√(1 + t*²) ‖v‖ ≤ ‖B v‖` (`enlarged_lower`), hence `‖v‖ ≤ κ_B ‖B v‖` with
`κ_B = 4 √s κ` (`enlarged_inverse`). `y = -2i√s R₀ J (0, z)`, `z = A⁻¹ b`,
solves `B y = J (b, 0)` (`enlarged_solution_eq`), with
`√s ‖z‖ ≤ ‖y‖ ≤ √2 √s ‖z‖`; `T = π₂ J† C` maps `y` to `-i√s z` and is a
contraction (`decode_solution`, `decode_norm_le`); the transferred estimate
`ν̂_B = (9/8) √s ν̂` lies in `[3/8, 5/2] ‖y‖` (`estimate_transfer`); and
`1 + κ_B/ν̂_B ≤ (73/9) κ/ν` (`ratio_bound`).

**Circuits and separate costs** (`Separate/Registers.lean`,
`Separate/Native.lean`). The concrete Cayley action at scale one equals the
Hilbert-space Cayley transform, by uniqueness of inverses (`action_one`), so
the eighteen-call native Cayley circuit implements `D₀` on the clean encoding
(`cay_clean`). `U_B = lcu (R̃ D̃₀)` (Hadamard, `I` or `-U`, Hadamard on a signal
qubit) has selected block exactly `B`, normalisation one, for the public
encoding `|0⟩ ⊗ clean` (`UB_block`, `lcu_block`). `P_b = Φ U_b`, with `Φ` a
fixed unitary extension of the public isometry `nEmb u ↦ clean (J (u, 0))`,
maps the public seed to the encoded `J (b, 0)` (`PB_seed`); the unknown vector
is never prepared by a free gate. The physical letters are `circLcu` (two public
gates and one masked native Cayley circuit: 54 matrix calls and no preparation
call, `circLcu_cost_mat`, `circLcu_cost_src`) and `circP` (one masked
controlled preparation call and a public gate: no matrix call and one
preparation call, `circP_cost_mat`, `circP_cost_src`); they implement the
masked solver oracles exactly through the clean encodings (`circLcu_apply`,
`circP_apply`, `letters_intertwine`). Work registers are handled by exact
intertwining; invertibility is used only on the logical edge space.
`Step.stepProg` is not used.

**Decoding** (`Separate/Decode.lean`). A fixed flag flip, a unitary extension
of the herald routing (the solver's failure component stays in the flag-false
sector, its selected vector `out† ψ` moves to a decoding cell), and the decoder
`lcu D̃₀` on the flag-true cells. The selected vector of a trial is exactly
`T (out† ψ)` (`selected`, `trial_amplitude`): the solver herald, the decoder
signal, the embedding registers and the lower dilation sector form one
selection, and amplitude from a failed solver branch is never accepted. With
`δ = ε/8`, one trial succeeds with probability at least `q₀/3` and its output
direction is within `3δ < ε` of `A⁻¹b/‖A⁻¹b‖` up to a phase
(`decode_success`, through `decode_contraction`).

**Repetition and costs** (`Separate/Main.lean`). `N = ⌈6/q₀⌉` attempts succeed
with probability at least `2/3` by `(1 - p)^N ≤ 1/(1 + N p) ≤ 1/3`
(`repeat_guarantee`); the conditional output is the pure state of the
normalised selected vector (`single_successDensity`), within trace distance
`ε` (`pure_traceDistance`). One trial makes `54 + 54 ·` (block-encoding calls)
matrix queries and (preparation calls) preparation calls (`trial_cost_mat`,
`trial_cost_src`); `log(2/δ) ≤ 3 log(1/ε)` (`log_budget`) and
`√s κ log(1/ε) ≥ 1` absorb the decoder. Every completed history obeys both
budgets (`ODERepeatProtocol.Protocol.History.cost_le_worstCost`).

**Writer form** (`ManuscriptConformance/WriterSeparate.lean`).
`ManuscriptConformance.qls_cor_separate_writer` covers value access by a
reversible writer specified only on clean targets, as in
`qls_thm_main_writer`: a supplied unitary writer `W x` with
`W x |a, 0⟩ = c x a |a, w_a⟩` for the stored words and any phases, arbitrary
elsewhere, with its inverse; it is not assumed to add or XOR into other target
contents. The hypotheses are otherwise those of `qls_cor_separate`, including
`ext_separateSolver`. On the workspace of `Separate.sepOracle` with one more
value-word register (`single0`), every physical call is implemented on the
clean scratch register: a value call applies the writer, adds its stored word
to the target and applies the inverse writer. The phases cancel and the
scratch register returns to zero, at the cost of two writer calls. Locators
and controlled preparation calls leave the scratch register untouched. The
theorem exposes this implementation as `Impl`: its matrix primitives are the
supplied locator and writer oracles acting on the enlarged workspace through
one fixed unital star-algebra homomorphism `Φ`, and its preparation primitives
are those of `Separate.sepOracle` with the scratch register as a spectator.
The converted protocol `A' = encodeProtocol hI A`, fixed before the instance,
has the
success mass and conditional output of the protocol `A` of `qls_cor_separate`
on every instance, at most twice its worst-case matrix calls (locator and
writer calls, `protocol_worstCost_le_mul`, `wcostU_wMat_le`) and the same
worst-case preparation calls (`wcostU_wSrc`). Hence the constants `2 C_A` and
`C_b`, success at least `2/3` and trace distance at most `ε`, with both bounds
on every completed history and the preparation bound under the estimate
promise. The repetition count and the external solver hypothesis are those of
`qls_cor_separate`.

**Formal restrictions.** The solver theorem enters as the hypothesis
`ext_separateSolver` in the single-trial form above; it is not proved. Its
system and register spaces are arbitrary finite-dimensional Hilbert spaces
with a public isometric encoding, and the endpoint uses it at the universe
levels of the instance (`SeparateSolver.{v, max v w}`). The protocol repeats
`N = ⌈6/q₀⌉` single trials, where the manuscript runs the measured solver of
Gao, Ji and Liu five times; both give the corollary's asymptotic bounds. It
is a fixed-length repetition protocol (`ODERepeatProtocol.Protocol`) over its
own register layout `Separate.sepOracle`, with the primitives, labels and
weights of `qls_thm_main`, which uses the adaptive `Protocol.Tree` over
`Step.physOracle`. The preparation bound is stated only under the estimate
promise `ν/2 ≤ ν̂ ≤ 2ν`. The access models are the native additive value
oracle of `qls_thm_main` and, in the writer form, a writer specified on clean
targets. The cost of obtaining `ν̂` is not counted.

### Native gates, arithmetic and synthesis

The native gate-level endpoints complete `hs:thm:gates` and `ode:thm:gates`
before finite-set synthesis: every supplied oracle of the released gate-level
circuits is replaced by a native implementation whose error is propagated in
the full-output convention (every non-system qubit, including every work
qubit, returns clean; no phase freedom). `U_J` is given by its `C_J`
elementary gates. A private Cayley call becomes `V† R_val V` with reversible
angle arithmetic: a public compute circuit `V` of elementary gates and
primitive oracle calls decodes the represented entry `z`, public arithmetic
writes angle words for `2 arctan |z|` and `arg z` within `ζ` (the hypothesis
`ArithOK`, the decoding and arithmetic part of `G_C` and `A_C`), and
bit-controlled rotations `-R_z(-φ̃) R_x(2θ̃) R_z(φ̃)` realise the edge
rotation; the hypothesis `NativeOK` states that `V† R_val V` is the supplied
private operation on clean scratch. One native private call uses
`G_C = 2 G_V + 2 G_arith + 2 bP + bT + 1` gates (`G_V`, `G_arith` the gates of
`V` and of the arithmetic, `bT`, `bP` the angle-word lengths) and is within
`4ζ`. The native simulation circuit (with `d`, `m`, `r` those of the
exact-gate circuit for accuracy `ε/2`) makes exactly `12d` times the
primitive calls of `V`, uses at most `200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C`
elementary gates and is within `ε` of `exp(-iτH)` on the system embedding
when `48 d ζ ≤ ε`; negative times use the literal inverse circuit, and a
time-dependent version uses slot-selected native private operations. With
the rescaled sparse parameters (sparsity `s`, norm bound `η`, time `t`),
`d ≤ 4608 Q_base` for `Q_base = √s ηt + √(s ηt log(1/ε)) + log(1/ε)` and the
gate count is at most `200 (4608 Q_base + 1)(G_C + C_J + a + m + r + 1)` with
`m` and `r`
logarithmic, the pre-synthesis form of `hs:eq:gate-binary`. In the native ODE
protocols the source interfaces are supplied circuits within `ζs` (the
hypothesis behind `G_src` and `A_src`) and the reflections are exact zero
tests on the non-system qubits (the flag and pool used by the tests stay
clean); under the released instance conditions and `24 d ζ + 2 ζs ≤ ν`
(time-dependent: `24 d ζ + 3 ζs ≤ ν`) they keep success probability
`175/256 > 2/3` and trace distance `ε`, with explicit worst-case counts of
gates, primitive calls and qubits: at most
`9000 g [(d+1)(a+m+r+1+C_J+G_C) + (k+1) + (J+2)(l+1) + G_src + A]` gates with
constant coefficients and
`18000 g [(d+1)(a+m+r+1+C_J+G_C) + (J+2)(l+1) + G_src + A]` with
time-dependent coefficients, where `A = |S| + |Zs| + |Z| + bT + bP + A_ar`
counts the system, scratch and arithmetic wires. One-qubit unitaries with at
most three controls count as elementary gates.

The library `GateEfficientBinary` constructs these ingredients for sparse
Hamiltonians given by binary sparse oracles and instantiates `hs:thm:gates`
for time-independent Hamiltonians
(`SparseHamiltonian.GateBinary.binary_simulation`). Indices are `k`-bit words
(dimension `2^k`), each entry is stored as two `b`-bit two's complement words
`X`, `Y` (`b ≥ 1`) with the public decoder `c₀ (X + iY)`, `c₀ > 0`, and the
`s = 2^σ` slots are the index words supported on the lowest `σ` bits; other
dimensions and sparsities are reached by zero padding. The primitive oracles
are the data's row and column location oracles on qubit index registers and an
XOR of the stored bits into `2b` value qubits. The library builds the compute
circuit `V` (`28k` gates and `2` row, `2` column and `1` value calls; each
controlled location call of the paper is realised with uncontrolled calls and
one extra call on a reference register), reversible integer CORDIC arithmetic
for `arg z` and `2 arctan |z|` within `ζ` with explicit gate and wire counts
(`ArithOK`, `cordicArith_ok`), and `U_J` from `σ + 1` Hadamard gates, and
proves `NativeOK` from the oracles (`sparse_nativeOK`); the clock promises are
those of the released query-level analysis, transported to qubits. For a
Hermitian `H` with row and column norms at most one, `τ ≥ 0`, `0 < γ ≤ 1`,
`0 < ε ≤ 1` and `48 d ζ ≤ ε`, the circuit makes exactly `12d` times `2` row,
`2` column and `1` value calls, uses at most
`200 (d+1)(k+m+r+2) + 84 d (σ+1) + 6 d G_C` elementary gates with
`G_C = 56k + 2 G_arith + 2 bP + bT + 1` on explicitly counted qubits, and its
full output is within `ε` of `exp(-iτH)` on the `k` system qubits. For
`0 < ε ≤ 1/2`, the released precision budget chooses `γ` from `s`, `τ` and `ε`
before the data, with `d ≤ 4608 q` and logarithmic `m` and `r`; for
`221184 q ζ ≤ ε` the circuit makes at most `55296 q` times `2` row, `2` column
and `1` value calls and uses at most
`200 (4608 q + 1)(G_C + σ + k + m + r + 3)` gates (`binary_simulation_budget`,
the pre-synthesis form of `hs:eq:gate-binary`), where `G_C` is polynomial in
`b`, `k`, `log(1/ζ)` and `|log(γ √s c₀)|`.

The library `GateEfficientBinaryTime` does the same for time-dependent
Hamiltonians, `hs:thm:time` with the circuit of `hs:thm:gates`, beyond the
paper (`SparseHamiltonian.GateBinary.binary_time_simulation`). Time-indexed
binary data are binary sparse data whose input also carries the time slot. The
primitive oracles are the coherent sampled-time oracles
`∑_w |w⟩⟨w| ⊗ O_j(x, w)` on `m` slot qubits, where `O_j(x, w)` are the binary
oracles of the sample named by the slot word `w`, and the compute circuit is
that of the time-independent case with every call also reading the slot
qubits; a generic transfer (`nativeOK_slot`) turns the native identity of
every sample into that of the slot-selected private operation
(`sparse_nativeOK_time`). For Hermitian samples with row and column norms at
most one, `t ≥ 0`, a Hermitian matrix path `H` on `[0, t]` that is
`β`-Lipschitz in operator norm and within `δ` of the samples at the slot
times, `0 < γ ≤ 1`, `0 < ε ≤ 1`, `0 < ζ ≤ 1`, the mesh conditions of the
native time-dependent theorem with `α = √s/γ` (`steps (√s t/γ) (ε/12) ≤ 2^m`
and `8 β t² ≤ ε 2^m`), the sample-error budget `8 t δ ≤ ε` and the arithmetic
budget `48 d ζ ≤ ε`, the circuit with `2^m` time slots makes exactly `12d`
times `2` row, `2` column and `1` value calls, uses at most
`200 (d+1)(k+m+r+2) + 84 d (σ+1) + 6 d G_C` elementary gates with the same
`G_C` and is within `ε` of every propagator of the path, lifted to the `k`
system qubits. For `0 < ε ≤ 1`, the released time-dependent precision budget
chooses `γ` from `s`, `t` and `ε` before the data, the path and the mesh, with
`d ≤ 4608 q` for `q = √s t + √(s t log(2/ε)) + log(2/ε)`; for `221184 q ζ ≤ ε`
the circuit makes at most `55296 q` times `2` row, `2` column and `1` value
calls and uses at most `200 (4608 q + 1)(G_C + σ + k + m + r + 3)` gates
(`binary_time_simulation_budget`). Neither `β` nor `δ` enters these counts;
`β` only constrains the number of time slots, which enters only through the
`m` slot qubits.

The library `GateEfficientSynthesis` adds the finite-gate-set synthesis step
of `hs:thm:gates` and `ode:thm:gates`. Single-qubit synthesis over a finite
gate set and the decomposition of controlled gates are results from other
papers and enter only as explicit hypotheses: `Synthesis 𝒢 X L` states that
the finite set `𝒢` of gate kinds (control values and a one-qubit matrix) is
such that every one-qubit unitary with at most three controls is approximated
within every `ζ > 0` by at most `L ζ` gates of `𝒢` (placed on distinct wires)
with the clean ancilla wires `X`, in the full-output convention (ancilla
residues and phases included), and `Synthesis.of_parts` derives it from
single-qubit synthesis and an exact decomposition of controlled gates. Every
elementary gate of a native circuit is replaced by its synthesis and every
primitive call is kept; the bound proved for the payload `ℂ` holds for every
payload, and the errors add along the circuit. A synthesis budget `ε'` spent
uniformly (`ε'/(N+1)` per gate for `N` native gates) adds `|X|` qubits and at
most `ε'` to the full-output error and gives at most `N L(ε'/(N+1))` gates,
and at most `G (c₁ log((G+1)/ε') + c₀)` for every `G ≥ N` when
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` with `c₀, c₁ ≥ 0` and `ε' ≤ 1`. This
gives `hs:thm:gates` over a finite gate set for the native circuits
(time-independent and every real time) and the binary-data circuit, and the
same for the time-dependent native and binary-data circuits (`hs:thm:time`
with the circuit of `hs:thm:gates`, beyond the paper). With the rescaling `γ`
of the binary-data budgets, chosen before the gate set, the synthesis budget
and the data, the gate count is at most `G (c₁ log((G+1)/ε') + c₀)` for
`G = 200 (4608 q + 1)(G_C + σ + k + m + r + 3)`: a bound of the form of
`hs:eq:gate-total` in which the gates of the native private calls are
synthesised as well, and, with the logarithmic `m` and `r` of the
time-independent budget, `hs:eq:gate-binary` after synthesis. For
`ode:thm:gates` every trial of the native four-attempt protocol is synthesised
with the budget `ε/200`; its decoded amplitudes move by at most `ε/200`,
which keeps the success probability at least `2/3` and the conditional output
within trace distance `ε` (a perturbation lemma for the four-attempt
protocol), with at most the native bound on primitive calls, the native qubits
and `|X|`, and, for a logarithmic `L`, at most the native gate bound times
`c₁ log((G+1)/(ε/200)) + c₀` gates, `G` the native gate bound of one trial.
The per-trial claim of `ode:thm:gates` (every successful trial within `ε` up to
a global phase) needs the reflections kept exact over the gate set, as in the
paper; here they are synthesised with the rest of each trial, and the library
`GateEfficientSynthesisTrials` below gives the per-trial form.

The library `GateEfficientBinaryODE` gives the constant-coefficient part of
`ode:thm:gates` from binary sparse oracles
(`SparseHamiltonian.GateBinaryODE.binary_ode_solver`). As in the released
query-level solver, the input selects one matrix `M`, here given by the binary
data, slots and primitive oracles of `GateEfficientBinary`, and the ODE is
`x' = -M x + b` with Hamiltonian part `H = (M - M†)/(2i)` and dissipative part
`L = (M + M†)/2`. From the oracles the library constructs `U_J` from `σ + 3`
Hadamard gates, the label-selected private operation with its compute circuit
(`28 k + 2` gates, two calls of each oracle) and native identity, and the
reversible arithmetic; it derives the clock promises of every label and the
norm, self-adjointness and accretivity conditions on the lifted `H` and `L`
from energy bounds and the accretivity of the input. The source circuits (with
their accuracy `ζs` and the budget `24 d ζ + 2 ζs ≤ ν`) and the source and
target conditions of the instance remain hypotheses, as in
`GateNative.native_ode_solver`. The Hamiltonian and dissipative parts of an
LCHS branch are placed in two sectors, so that every value of the edgewise
Cayley gate is a positive multiple `κ ρ_x Z'` of one Gaussian integer `Z'`,
which a single-assignment register program computes from the stored bits and
the label, and whose angles the CORDIC circuit computes; this doubles the
boundary weight to `4s` (`Q = ⌈max(1, γ √(4s))⌉`, `λ_H = √(4s) η_H/γ`,
`λ_D = √(4s) η_D/γ`). The LCHS nodes use a rounded step `round(2^F h)` whose
relative error, at most `ζ/4`, is absorbed in the arithmetic accuracy `ζ`. For
an input whose Hamiltonian and dissipative parts have row and column energies
at most `η_H²` and `η_D²`, with accretive dissipative part, the native protocol
succeeds with probability at least `2/3` with a conditional output within trace
distance `ε` of the normalised solution and every successful trial within
`ε/500` up to a global phase. Its gate, call and qubit counts depend only on
the public data and the source circuits (`binary_ode_counts`), with the
worst-case gate count
`9000 g [(d+1)(k + 3 + m + r + 1 + σ + 3 + G_C) + (k_T + 1) + (J+2)(l+1) + G_src + A]`
(`binary_ode_gate_count`), where `k_T` is the number of node bits,
`G_C = 2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1` the gates of one native
private call, `G_src` the gates of the source circuits and
`A = k + |Zs| + (6 k + 4 b) + bT + bP + A_arith` the system, source-scratch,
private-scratch and arithmetic wires. `binary_ode_solver_synth` gives the
finite-gate-set form under the synthesis hypothesis.

The library `GateEfficientBinaryODETime` gives the time-dependent part of
`ode:thm:gates` from time-indexed binary sparse oracles
(`SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver`). The data are
those of `GateEfficientBinaryTime`: on input `x` the sample of time slot
`r < 2^m` is the matrix `M_r`, read through coherent sampled-time oracles on
the `m` slot qubits, and the `2^m` samples are those of the uniform mesh of
`GateNative.native_ode_time_solver`. From the oracles the library constructs
`U_J` (`σ + 3` Hadamard gates), the label- and slot-selected private
operation, whose compute circuit is that of `GateEfficientBinaryODE` with
every call also reading the slot qubits, with its native identity at every
slot, and the reversible arithmetic. The masking of the source branches on
the common mesh enters as the factor `[start ≤ r]` of the Cayley parameter; a
two-operation slot comparator (at most `52 (m + 14)` gates and
`1 + 64 (m + 14)` work wires) computes it, and the released register program
uses it in place of the branch duration. The library derives the clock
promises at every label and slot and the norm, self-adjointness and
accretivity conditions on the lifted parts of every sample from energy bounds
and the accretivity of every sample. The loading and weight-preparation
circuits (with their accuracy `ζs` and the budget `24 d ζ + 3 ζs ≤ ν`) and the
source, path and target conditions of the instance (`PubT.Rest`) remain
hypotheses, as in `GateNative.native_ode_time_solver`. The native protocol
then succeeds with probability at least `2/3` with a conditional output within
trace distance `ε` of `x(T)/‖x(T)‖` and every successful trial within `ε/500`
up to a global phase. Its gate, call and qubit counts depend only on the
public data and the two source circuits (`binary_ode_time_counts`), with the
worst-case gate count
`18000 g [(d+1)(k + 3 + m + r + 1 + σ + 3 + G_C) + (J+2)(l+1) + G_src + A]`
(`binary_ode_time_gate_count`), where `G_src = |loadC| + 2 |wpC|` and `G_C`
and `A` are as for constant coefficients, the comparator included in the
arithmetic. `binary_ode_time_solver_synth` gives the finite-gate-set form
under the synthesis hypothesis.

The library `GateEfficientSynthesisTrials` gives `ode:thm:gates` over a finite
gate set including its per-trial claim, as in the paper's proof. Only the
native preparation is synthesised (`synthBudget` with the public budget
`ν/3`); the inverse preparation of every amplification step is the literal
adjoint of the synthesised circuit, and the two zero tests and the sign are
the released exact gates, on a trial register with a fresh flag and pool
(`2 (|V| + |X|) + 1` qubits), so that every trial performs exact Grover
iterations on the implemented preparation unitary (`trialN_seed`). Besides
`Synthesis 𝒢 X L` it assumes that `𝒢` is closed under adjoints (`AdjClosed`)
and contains the four kinds of the exact zero tests (`zeroTestKinds`: NOT gates
with two controls of values `(0, 0)` and `(1, 0)`, `diag(-1, 1)` with one
control and the sign `-1`); adding these finitely many kinds and the adjoints
to any synthesising gate set gives both with the same length function
(`GateSynthTrials.extra_hyps`). The protocol then satisfies the native
`NOutcome`: success probability at least `2/3`, conditional output within
trace distance `ε`, and every successful trial within `ε/500` of the
normalised solution up to a global phase. In every history it makes at most
`40 g` times the native calls (`80 g` for time-dependent coefficients) and, for
`L ζ ≤ c₁ log(1/ζ) + c₀`, at most `40 g N (c₁ log(3(N+1)/ν) + c₀) + 20 g (4 n + 3)`
gates of `𝒢` (`native_ode_solver_trials`, `native_ode_time_solver_trials`,
`binary_ode_solver_trials`, `binary_ode_time_solver_trials`).

The library `GateEfficientODEBudget` gives equations `ode:eq:gate-main` and
`ode:eq:gate-space` with explicit constants for the solvers from binary data.
With `ν = ε/(10⁴ g)`, `ℓ = log(1/ν)`, `Θ = T η_H + T η_D ℓ`,
`q = √s Θ + √(sΘℓ) + ℓ` and the public rescaling `γ = min(1, √(Θ/ℓ))`
(hypothesis `hγ`): `τ ≤ 16 q`, `d ≤ 4096 q`, `J ≤ 60 q ℓ` and the register words
`m`, `r`, `k`, `l` are `O(log(q/ν))` (`binary_ode_sizes`); under
`98304 q ζ + 2 ζs ≤ ν` the native protocol keeps its guarantees with at most
`3932160 g q` calls of each matrix oracle besides `40 g` times the source calls
and at most `36873000 g [q (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]`
gates (`binary_ode_budget`), at most `3·10¹² g [q (𝔴 + ℓ + 1)³ + G_src + |Zs|]`
gates on `10⁴ (𝔴 + 1)³ + 2 |Zs|` qubits, with `𝔴` the sum of the register words
(`binary_ode_budget_words`), and, through `GateEfficientSynthesisTrials`, the
same over a finite gate set with the per-trial claim
(`binary_ode_budget_trials`); the time-dependent forms use `(2g, ε/2)` and
doubled constants. The polynomial is evaluated at the word lengths of the
construction; for public parameters of bounded bit length the library
`GateEfficientBitBudget` below bounds these words, those of the arithmetic
accuracy, of the LCHS step and of the decoder scale included, by `𝔟`.

The library `GateEfficientBitBudget` states these budgets, and equation
`hs:eq:gate-binary`, in the paper's bit-length parameter, without results from
other papers. A public parameter has bit length `b` (`HasBits b x`) if
`x = n/2^b` for an integer `|n| < 2^(2b)`; a fixed-point word of `i + f` bits
has bit length `i + f`, and `|log₂ |x|| ≤ b` for `x ≠ 0`. `bitB` is the word
budget `𝔟 = b_data + log₂(N+1) + log₂(M+1) + log₂(m+1) + log₂((q g+1)/ε)` of
`ode:eq:gate-word-budget` with base-2 logarithms (with the paper's natural
logarithms the constants grow by a factor of at most `(1/log 2)³ < 3.01`). If
the stored bits are at most `b_data`, the decoder scale `c₀`, the time `T` and
the energy bounds `η_H`, `η_D` have bit length `b_data`, the rescaling is the
public one and the arithmetic accuracy is at least `ν/(196608 q)`, the register
words of the solvers from binary data, those of the arithmetic accuracy, of the
LCHS step and of the decoder scale included, satisfy `𝔴 + ℓ ≤ 300 (𝔟 + 1)`
(`words_le`, `wordsT_le`), and the native protocol uses at most
`10²⁰ g [q (𝔟+1)³ + G_src + |Zs|]` gates on at most `3·10¹¹ (𝔟+1)³ + 2 |Zs|`
qubits, with every released conclusion kept (`binary_ode_budget_bits`):
equations `ode:eq:gate-main` and `ode:eq:gate-space` with
`P(x) = 3·10¹¹ (x+1)³`, `C = 10²⁰` and `A_src = |Zs|`. For time-dependent
coefficients the gate constant is `2·10²⁰` with the `q` of the solver's internal
`(2g, ε/2)` (`binary_ode_time_budget_bits`), and the constants are `2·10²²` and
`9·10¹²` with the `q` of `(g, ε)` (`binary_ode_time_budget_bits_user`). For
Hamiltonians the binary construction uses at most `10¹⁵ Q_base (𝔟_H + 1)³` gates,
`𝔟_H = b_data + log₂(N+1) + log₂((Q_base+1)/ε)` (`Q_base` the query scale of
`hs:eq:gate-binary`), for an arithmetic accuracy
`ε/(442368 Q_base) ≤ ζ ≤ ε/(221184 Q_base)` (`binary_simulation_bits`; on `2^m` time
slots `binary_time_simulation_bits` adds `log₂(M+1)`, with
`q = √s t + √(st log(2/ε)) + log(2/ε)` in place of `Q_base`). Over a finite gate set
the synthesis factor is at most `64 (𝔟+1) + log(G_src+1)`, respectively
`36 (𝔟_H+1) + log(1/ε')` (`binary_ode_budget_trials_bits`,
`binary_ode_time_budget_trials_bits`, `binary_simulation_budget_synth_bits`,
`binary_time_simulation_budget_synth_bits`). The public choices of the
rescaling and of the arithmetic accuracy are admissible, and all hypotheses
hold together on explicit one-point data (`withChoice_spec`,
`withChoiceT_spec`, `bits_witness`, `ode_all_hyps`, `hs_all_hyps`).
Floating-point public parameters and the costs of the source circuits (the
parameters `G_src`, `|Zs|`) are not covered.

The library `GateEfficientMesh` proves the time-dependent gate-level
simulation (`hs:thm:time` with the circuit of `hs:thm:gates`) and the
time-dependent part of `ode:thm:gates` at gate level under integrated
sample-error certificates on the uniform slots of the released circuits
(the paragraph after `hs:thm:time`; "a certificate for the same uniform
meshes suffices" in `ode:thm:gates`) and, as corollaries beyond the paper,
whose time-dependent gate theorem (`ode:thm:gates`) is stated on uniform
meshes and which gives no time-dependent gate theorem for Hamiltonian
simulation, on nonuniform meshes with breakpoints, with the released
circuits, protocols and counts and without results from other papers.
On the `2^m` uniform slots, the released circuit with slot-selected private
operations for the samples `H̃_k` is within `ε` of `U(t)` for every propagator
`U(s) = 1 - i ∫_0^s H(u) U(u) du` of a path that is Hermitian almost everywhere
and interval integrable, and for every classical propagator with one piece per
slot, whenever `∑_k ∫_{kt/2^m}^{(k+1)t/2^m} ‖H(u) - H̃_k‖ du ≤ ε/2`
(`time_simulation_certified`; `ε/4` for native implementations and binary data);
the subdivision condition is the only condition on `m`, and the released
Lipschitz error bound follows (`time_simulation_lipschitz`). On a mesh
`0 = t_0 ≤ ⋯ ≤ t_M = T`, slot `k` reads the samples of the interval containing
`kT/2^m`, so that the equal-angle boundary circuit is the released one: the
same circuit and counts, with this `m` and without a factor `M`, give error `ε`
under the mesh certificate `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du ≤ ε/4` and
the rounding condition `4 M α T ≤ ε 2^m` (`time_simulation_mesh`, with the
explicit exponent `meshExponent`; `ε/8` and `8 M α T ≤ ε 2^m` for native
implementations, and the same with the rescaled time for binary data, also in
the budget form `binary_time_simulation_budget_mesh`). Binary mesh data are
presented on the clock by re-indexing (`clockData`), whose oracles at slot word
`w` are the released binary oracles of the sample of the interval of `w`
(`primsT_clockData`); this slot-to-sample map is part of the presentation of
the data and is not counted. For dissipative equations,
`ODE.ode_time_solver_certified` gives the released protocol, counts and outcome
for classical piecewise solutions with one accretive generator piece and one
forcing piece per slot under `ODE.slotCertificate ≤ ε B/(2000 g)` (the
generator certificate weighted by `‖x(0)‖ + b_max T`, the forcing certificate
and the left-endpoint quadrature), and every instance of the released theorem
satisfies these hypotheses (`ODE.certified_of_instanceOK`); on a mesh,
`ODE.meshCertificate` adds a refinement cost of order `2^{-m}` and keeps the
left-endpoint source quadrature of the mesh, which does not decrease with `m`
(`ODE.meshCertificate_le`). Native, binary-data and finite-gate-set forms
follow, with the per-trial claim and explicit budgets
(`ODE.binary_ode_time_budget_certified_trials`,
`ODE.binary_ode_time_budget_mesh_trials`), and the module `NonVacuity` checks
that the hypotheses can be met. Nonuniform Cayley steps are not formalised
(the branch-dependent meshes of `ode:lem:gate-select` are formalised in
`GateEfficientSelect`).
Hypotheses on the interval integrability of operator paths on qubit registers
use the scoped instance `GateMesh.regENormedAddMonoid` (after
`open scoped SparseHamiltonian.GateMesh`).

The library `GateEfficientRemarks` formalises statements around `hs:thm:gates`
and `ode:thm:gates` that the other gate-level libraries leave open, without
results from other papers. Lemma `hs:lem:abstract` holds for every real time in
the exact-gate model (`GateRemarks.abstract_simulation`): for unitaries `U_J`,
`D`, the two-sided inverse `R₁` of `1 − D` and `h` self-adjoint with `‖h‖ ≤ 1`
satisfying `hs:eq:interface` for `J = U_J ι₀` (the compressed second moment
`J† R₁† R₁ J ≤ (ν/2) 1` in Mathlib's Loewner order, `‖R₁‖ ≤ Q`, `1 ≤ Q`,
`0 < ν ≤ Q`), the circuit `absCircuit`, fixed by the public numbers, makes
exactly `6 d ≤ 3840 (α|t|ν + Q log(1/ε))` calls of `D` or `D†` and is within
`ε` of `exp(−itαh)`, with a degree bound that does not involve the time slots;
for `t < 0` it is the released circuit with `D` and `D†` exchanged, since
`R₁† = 1 − R₁` gives the interface of `D†` for `−h` (with the manuscript's
schedule, the count `hs:eq:explicitcount` and error `ε/2`:
`GateSchedule.abstract_simulation_ms`). On finite-dimensional
systems every isometry is `U_J ι₀` (`abstract_simulation_isometry`), and the
hypotheses hold for scalar data (`abstract_simulation_scalar`) and for the
operators of the binary-data construction (`interface_binary`). For the
binary-data constructions the register, the `log₂ N` system qubits included,
has at most `4·10⁶ (𝔟_H + 1)³` qubits (`log₂(M+1)` added on `2^m` slots, `|Xa|`
after synthesis), stated with every conclusion of the `GateBitBudget` endpoints
for the same circuits (`binary_simulation_bits_qubits` and its variants); the
cube comes from the released CORDIC workspace, which has at least `12 n³` qubits
for its `n ≥ log₂(1/ε)` steps (`binArith_A_ge`). The remark "at `t = 0` the
identity suffices" (Theorem `hs:thm:gates`) is stated for the binary-data
and finite-gate-set variants of `hs:thm:gates`, with the released hypotheses
and conclusions, counts `if <zero time> then 0 else <released>` and error
exactly `0` at zero time (`binary_simulation_nonneg` and ten more); for
the time-dependent circuits among them (`hs:thm:time` with the circuit of
`hs:thm:gates`, beyond the paper) it is the zero-time remark of `hs:thm:time`.
For `ode:thm:gates` (namespace `GateRemarks.ODE`): if the source gates and the
source scratch are at most `c (𝔟+1)^j`, the budgets in `𝔟` become `ḡ q poly(𝔟)`,
at most `10²⁰ (1+2c) g q* (𝔟+1)^max(j,3)` gates on `(3·10¹¹+2c) (𝔟+1)^max(j,3)`
qubits (`ODE.binary_ode_budget_poly`, with time-dependent, finite-gate-set and
every-`T ≥ 0` forms); a single instance meets these hypotheses with constant
polynomials, so their content is uniformity over a family. For zero time or a
known zero generator, the direct source assembly of `ZeroTimeGateODE` is also
synthesised trial by trial (`ODE.native_ode_solver_synth_zero` and its native,
binary-data and every-`T ≥ 0` forms), and it meets `ode:eq:gate-main` and
`ode:eq:gate-space` in `𝔟` with the constants of the general case: on its own
register for every `b_data` (`ODE.binary_ode_budget_bits_zero`, in fact linearly
in `𝔟`), and on the registers of the general solvers when the Cayley rescaling,
a free public parameter in this case, has bit length `b_data`
(`ODE.binary_ode_budget_bits_zero_released`); this gives the released budgets
in `𝔟`, with all their conclusions, for every `T ≥ 0`
(`ODE.binary_ode_budget_bits_nonneg` and its time-dependent and finite-gate-set
forms). Explicit one-point data meet the zero-case hypotheses jointly, the
antecedents of the guarantees included (`ODE.zero_instance_all_hyps`,
`ODE.zero_instance_outcome`).

The library `GateEfficientSigned` states the time-independent binary-data
endpoints of `hs:thm:gates` for every real time, as the theorem's assumptions
(those of `hs:thm:main`, with `τ = η|t|`) and its construction ("Negative time
uses the adjoint of the constructed circuit") require; the released endpoints
are stated for `τ ≥ 0`. The circuit `GateSigned.binarySimSigned` is the released
`GateBinary.binarySim` for `|t|` if `t ≥ 0` and its literal inverse
`GateNative.ninv` (reversed, every gate conjugate-transposed, every call
replaced by the call of the inverse oracle) if `t < 0`, on the same wires. Under
the hypotheses of each released endpoint for `|t|` it keeps every conclusion for
`|t|` (validity, the call, gate, private-gate and qubit counts, the degree and
register bounds) and its full output is within `ε` of `e^{-itĤ}`
(`GateSigned.binary_simulation_signed`, `binary_simulation_budget_signed`,
`binary_simulation_bits_signed`, `binary_simulation_bits_qubits_signed`); over a
finite gate set the signed circuit is synthesised as it is, within `ε + ε'`
(`binary_simulation_synth_signed`, `binary_simulation_budget_synth_signed`,
`binary_simulation_budget_synth_bits_signed`,
`binary_simulation_budget_synth_bits_qubits_signed`), and with the empty circuit
at `t = 0` the counts are `0` and the error is exactly `0` there
(`binary_simulation_signed_zero` and three more). One-point binary data with the
identity matrix meet every hypothesis at `t = -1` (`hs_signed_all_hyps`), and
there the released circuit for `|t|`, which is at least
`‖e^{-itĤ} ψ - e^{-i|t|Ĥ} ψ‖ - ε` from `e^{-itĤ}` for every unit `ψ`
(`binarySim_error_ge`), misses `e^{-itĤ}` by more than `ε` (on this
one-dimensional system the two evolutions differ by a global phase). The
time-dependent endpoints keep `t ≥ 0`, as `hs:thm:time` does.

The library `GateEfficientSelect` formalises Lemma `ode:lem:gate-select` on the
branch-dependent meshes of its proof ("For fixed `z`, choose `M` equal time
steps of length `u_z/M`"), where the released time-dependent ODE solvers mask
the source branches on one common mesh. Labels are the configurations of an
arbitrary finite register beside the simulator wires. The released instruction
list `GateCircuit.SlotSim.simCircuitT` of the slot-selected simulator for the
common normalised time `αT` is read with a label- and slot-selected private call
(`GateSelect.runS`), whose operation for label `z` at slot `j` carries the
released clock promise for the rescaled sample `((T - v_z)/(αT)) X_{z,j}`; one
step of the circuit is then the step `(T - v_z)/2^m` of the mesh of branch `z`
(`exp_branch_step`). For Hermitian `βH`- and `βD`-Lipschitz paths `H` and `D`,
labels with frequencies `k_z ∈ [-R, R]` and start times `v_z ∈ [0, T]`, and
samples within `δ` of `H + k_z D` at the branch addresses
`v_z + j(T - v_z)/2^m`, under `steps(αT, ε/6) ≤ 2^m`, `4(βH + RβD)T² ≤ ε 2^m`
and `4Tδ ≤ ε`, the circuit makes exactly `6d` private calls and `12d` calls of
`U_J` or `U_J†` and uses at most `200(d+1)(a+m+r+1)` gates, no count depending
on the label register, and on clean inputs its full output is within `ε` of the
controlled direct sum of the propagators of `H(v_z + t) + k_z D(v_z + t)` over
`[0, T - v_z]` (`GateSelect.gate_select`; the inverse in `gate_select_inverse`).
For the time-dependent part of `ode:thm:gates` (namespace `GateSelect.ODE`) the
released protocol runs with the forcing label `(true, q)` started at a node
`v_q ∈ [0, T]`, with weight `w_q ≥ 0` and forcing vector `f_q`, on its own mesh.
For an accretive `β_G`-Lipschitz generator path with branch sample errors at
most `δ_G`, under the paper's source certificate `‖x(T) - ∑_s y_s(T)‖ ≤ κ` for
the homogeneous solutions `y_s` started at the source vectors and the budget
`κ + T(β_G T/2^m + δ_G) B ≤ εB/(2000g)`, `B = ‖x(0)‖ + ∑_q w_q ‖f_q‖`, it gives
the released outcome with the released counts, with exact gates (`ODE.solverB`)
and natively (`ODE.native_ode_time_solverB`); for the left-endpoint nodes the
certificate follows from Lipschitz bounds (`ODE.quad_leftEndpoint`). Explicit
data meet every hypothesis of the lemma (`nv_select`) and of the solver
(`ODE.nvB_outcome`). The clock promise for the rescaled samples is a hypothesis
in place of the boundary rotations `R(c_z^M)` that the proof computes from the
label; this coherent per-label arithmetic, the gate count
`ode:eq:gate-select-gates`, other source quadratures and the binary-data and
finite-gate-set forms on these meshes are not formalised.

The library `GateEfficientQuadrature` formalises the sufficient positive source
quadrature that the proof of `ode:thm:gates` specifies for time-dependent
forcing. For a solution `x` of `x' = -G(u) x + b(u)` on `[0, T]` with accretive
`G(u)`, `‖G(u)‖ ≤ Λ`, `‖b(u)‖ ≤ b_*` and `Lip(b) ≤ L`, `C_b = Λ b_* + L`, and
the left-endpoint quadrature with `n` nodes `qT/n` and weights `T/n`, the source
certificate `‖x(T) - y_0(T) - ∑_q Y_q(T)‖ ≤ C_b T²/(2n)` holds for the solutions
`y_0`, `Y_q` of the homogeneous equation started at `x(0)` and at
`(T/n) b(qT/n)` (the paper's `U(T, 0) x₀` and `(T/n) U(T, v_q) b(v_q)`;
`GateQuad.cert_left`, which also allows sample errors `δ` at the cost `Tδ`). It
is proved by a telescoping energy estimate (`energy_affine`), without the
propagator and the Duhamel formula as Lean objects, and the Lipschitz bound
`C_b` of `v ↦ U(T, v) b(v)` is stated with homogeneous solutions
(`flow_lipschitz`). The quadrature mass `B_n = ‖x(0)‖ + ∑_q (T/n) ‖b(qT/n)‖` is
within `T² L/(2n)` of `B = ‖x(0)‖ + ∫_0^T ‖b‖` (`mass_left`), and with the
paper's number of nodes `n ≥ T² C_b/(2νB)`, `0 < ν < 1`, the certificate is at
most `νB`, `(1 - ν)B ≤ B_n ≤ (1 + ν)B`, `0 < B_n` and `B_n ≤ 2B`
(`paper_quadrature`; `exists_pow_two_nodes` gives a power of two). In the solver
on branch-dependent meshes the certificate holds for every instance with this
quadrature and `n ≤ 2^m` nodes (`quad_left`, `LInstanceOK`; `GateQuad.solverL`
with exact gates and `native_time_outcomeL` natively), and the paper's
`ν = ε/(10⁴ ḡ)` and `B ≤ ḡ ‖x(T)‖`, with the solver's public parameter
`g = 2ḡ`, give the budget fields of that solver when the branch discretisation is at most `ε/(10⁴ g)`
(`budget_disc_paper`). For a zero generator and a ramp forcing both bounds are
attained (`sharp_cert`, `sharp_mass`), and explicit data with an interior node
and sample errors, or with a padding label, meet every hypothesis
(`nvL_outcome`, `nvL1_outcome`; zero generator). Source certificates for other
quadratures remain a hypothesis, as in the paper.

The library `GateEfficientBinarySelect` formalises the arithmetic part of
`ode:lem:gate-select` for time-indexed binary sparse oracles and, on the
branch-dependent meshes of its proof, the binary-data, finite-gate-set and
budget forms of the time-dependent part of `ode:thm:gates`. The lemma holds
under the paper's integrated sample-error certificate: if the represented-sample
errors at the branch addresses, weighted by the slot length, sum to at most
`ε/16` for every label and `8(βH + RβD)T² ≤ ε 2^m` (with the released
subdivision condition and the clock promises), the released circuit is within
`ε` of the controlled direct sum of the branch propagators
(`GateBinarySelect.gate_select_certified`; under integrated slot certificates of
merely integrable branch paths `gate_select_integral`), and explicit data
satisfy it at `ε = 1/2` (`nvc_select`) although for no `ε < 1` does a uniform
sample bound with `4Tδ ≤ ε` exist for them (`nvc_not_uniform`). With native
private calls (`native_gate_select`, the inverse in `native_gate_select_inverse`)
the circuit uses at most
`200(d+1)(a+m+r+1) + 84 d C_J + 6 d (2|V| + 2|arith| + 2bP + bT + 1)` gates. For
time-indexed binary data on the grid of `2^(2m)` times `gT/2^(2m)`, the labels of
the dissipative solver and the `2^m` dyadic source nodes `uT/2^m`, the clock
promises of the rescaled private operations hold with the label-independent
constants `width(4s, γ)` and `moment γ` (`binary_gate_select`), and natively a
single-assignment register program computes the branch address
`2^m u' + r(2^m - u')` from the label and the slot index and the duration word
`2^m - u'` from the label, and the released angle arithmetic takes the branch
scale into the Cayley parameter `γ(2^m - u')/2^m` (`binary_native_gate_select`).
The gates `G_sel = 84 d(σ+3) + 6 d G_C` and work
wires `A_sel` added to the released simulator are at most `393500 d (𝔴+1)³` and
`4096 (𝔴+1)³ + 3` in the register words `𝔴` (`select_gates_words`), and at
`δ = 4ν` the whole selection circuit has at most `394300 (d+1)(𝔴+1)³`, or
`11·10¹² (d+1)(𝔟+1)³`, gates (`binary_select_lemma_words`,
`binary_select_lemma_bits`). The native solver on these meshes from binary data
has the released guarantees for every positive source quadrature on the dyadic
nodes (`binary_select_solver`; `binary_select_solverL` for the left-endpoint
weights), also over a finite gate set with every trial synthesised or with the
per-trial claim (`binary_select_solver_synth`, `binary_select_solver_trials`),
and satisfies `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`, with at most
`2·10²⁰ g[q*(𝔟+1)³ + G_src + |Zs|]` gates and `3·10¹¹(𝔟+1)³ + 2|Zs|` qubits
(`binary_select_budget_bits`; over a finite gate set
`binary_select_budget_trials_bits`). Explicit data meet every hypothesis of the
lemmas and of the solvers' guarantees (`nv_binary_native_gate_select`,
`nv_instanceB`, `nv_select_outcome`; zero generator). The boundary rotations
that the proof computes from the label are replaced by the rescaled private
operations; source nodes off the dyadic grid and integrated certificates for the
generator samples of the solvers are formalised in `GateEfficientBinaryNodes`.

The library `GateEfficientBinaryNodes` completes three parts of the proof of
`ode:thm:gates` that `GateEfficientBinarySelect` left open. First, the generator
samples of the dissipative solvers on branch-dependent meshes satisfy the
integrated sample-error certificate of `ode:lem:gate-select` instead of a
uniform bound: if the slot-weighted sum `sampleErrB s` of the represented-sample
errors at the branch addresses is at most `δI` for every branch and
`κ + (βG T²/2^m + δI) B ≤ ε B/(2000 g)`, the released native protocol and its
synthesised forms have the released guarantees (`native_time_outcomeBI`,
`native_time_trials_outcomeBI`; a uniform bound `δG` gives `δI = T δG` and the
released budget, `BInstanceOK.toI`), and from binary data the energy bounds and
accretivity are needed only at the samples the branches read
(`binary_select_solverI`, `binary_select_solverLI` and their finite-gate-set
forms). Second, for constant forcing (`ode:eq:gate-constant-source`) the
time-dependent solvers get the source preparation that the constant-coefficient
solver already has (`GateODE.Params.srcPrep`): the weight preparation is
constructed, one rotation `rotC √(r₀/B) √(T r_b/B)` and `m` Hadamard gates
controlled by the sector wire (`WpConst_srcAmp`), and the two supplied
controlled loading circuits are used once each, so that
`G_src = |srcC 0| + |srcC 1| + 2(m+1)` (`const_source_counts`), for the released
common-mesh solver (`binary_ode_time_solver_const`) and for the solver on
branch-dependent meshes (`binary_select_solverLI_const`, with finite-gate-set
forms). Third, the time-dependent part of `ode:thm:gates` holds from binary data
for positive source quadratures whose nodes `word u · T/2^μ` are computed
coherently by a node program (`NodeProg.OK`, its `|N|` gates counted): a
register program computes the branch addresses `2^m ν' + r(2^μ - ν')` and
duration words from the node words, every call reads the data grid of
`2^nd ≤ 2^(μ+m)` points at the top `nd` address bits, and the time-address
rounding is part of the integrated represented-sample error
(`binary_nodes_solver`, `binary_nodes_solver_synth`,
`binary_nodes_solver_trials`), with at most
`2·10²⁰ g[q*((𝔟+μ+1)³ + |N|) + G_src + |Zs| + |Zn|]` gates and
`3·10¹¹(𝔟+μ+1)³ + 2|Zs| + 2|Zn|` qubits (`binary_nodes_budget_bits`; over a
finite gate set `binary_nodes_budget_trials_bits`). The copy program computes
the released dyadic nodes and the midpoint program the midpoints
`(u + 1/2)T/2^m`; explicit data meet every hypothesis for every node program
(`nv_nodes_outcome`), for a forcing node at a midpoint (`nvMF_instanceN`) and
for constant forcing (`nv_const_outcome`; zero generator). The node labels are
the `2^m` slots of a branch, so more nodes than slots require a larger `m`; the
nodes lie on the `μ`-bit grid in `[0, T)`, and other quadrature nodes are
rounded to it with the rounding in the source certificate, which, like the
loading circuits, remains a hypothesis for a general quadrature, as in the
paper.

The library `GateEfficientSelective` proves the separated finite-gate-set forms
of `hs:thm:gates` and `ode:thm:gates`, in which supplied finite-set circuits are
charged by their own gate count: equation `hs:eq:gate-total` with `G_C(ξ)`
outside the synthesis logarithm and equations `ode:eq:gate-main` and
`ode:eq:gate-space` with `G_src` and `A_src` linear, for any supplied circuits,
without assuming that their costs are polynomial. Its compiler
(`GateSelective.selBudget`) keeps every gate that is already in the finite gate
set, synthesises the other exact gates with the budget `δ/(K+1)` each on one
reused register of clean ancillas, keeps every primitive call, and is within `δ`
in the full-output convention with at most `N_keep + K L(δ/(K+1))` gates
(`selBudget_spec`, `selBudget_approxOn`, `selBudget_gates_log`). For
Hamiltonians the private Cayley calls are a supplied circuit `pc` over the gate
set within `ξ` of the enable-controlled private operation on clean work wires,
its inverse its literal reverse-adjoint (`hcircP`, `ctrl_inv_approx`); with
`24dξ ≤ ε` the compiled circuit has exactly `6d` times the calls of `pc`,
synthesises at most `G₀ = 200(d+1)(a+m+r+1) + 84 d C_J` gate occurrences
whatever `pc`, has at most `6d|pc| + G₀(c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates
and full-output error `ε` (`sel_simulation`, every real time
`sel_simulation_signed`, time-dependent `sel_time_simulation`), and the native
data give such a circuit (`privSel_spec`, `sel_simulation_native`). For the
dissipative solvers the native preparation is compiled selectively with the
budget `ν/3` and amplified with its literal inverse and the exact zero tests:
the source circuits over the gate set are retained, the synthesised occurrences
are bounded by the preparation with empty source circuits, and in every history
the protocol uses at most
`40g(G_src + K(c₁ log((K+1)/(ν/3)) + c₀ + 1)) + 20g(4n+3)` gates with the
guarantees of the released solvers (`native_ode_solver_sel`,
`native_ode_time_solver_sel` with `80g` and `40g`, on branch-dependent meshes
`native_time_sel_outcomeB`); from binary data this gives `ode:eq:gate-main` and
`ode:eq:gate-space` in `𝔟` with polynomials that do not depend on the source
circuits (for constant coefficients at most `2·10¹⁸q*(𝔟+1)³` synthesised
occurrences per preparation and the factor `64c₁(𝔟+1) + c₀ + 1`,
`binary_ode_budget_sel`; for time-dependent coefficients
`binary_ode_time_budget_sel`; with computed source nodes `(𝔟+μ+1)³ + |N|`
occurrences and the factor `c₁(64(𝔟+μ+1) + log(|N|+1)) + c₀ + 1`,
`binary_nodes_budget_sel`). Under the manuscript's certificates (represented samples of either sign,
`MeshCertificateODE.CertRest`) the time-dependent binary-data protocol has the same guarantees,
derived from the certificate of the actual compiled preparation
(`MeshCertificateODE.binary_ode_time_cert_sel`); its source executions are counted on the
annotated selective expansion (`ManuscriptConformance.ode_thm_gates_time_cert_finite`).

### Explicit schedules and improved-precision bounds

The library `QLSHoeffding` proves Hoeffding's inequality for the binomial law,
`2 exp(-2nt²)` for every `t ≥ 0`, by Hoeffding's lemma for a Bernoulli variable
(`two_sided_sharp`, `log_mgf_le`), and Theorem `qls:thm:main` for the
finite-degree Chebyshev protocol with the repetition count
`⌈log(10/ζ_j)/(2·0.0099²)⌉` of `qls:eq:hoeffding` at the manuscript's stage
budget `ζ_j = (ε/1000) 2^{j-m}` (`repsH_eq_ms`; the released per-test budget is
`ζ_j/5`), with at most `3.4·10⁹ √s κ log(1/ε)` matrix-oracle and
`1.25·10⁸ √s κ log(1/ε)` source calls (`mainH`, `main_ampH`, `main_exactH`); the
released proofs use eight times this count. The count satisfies
`5101 log(10/ζ_j) ≤ n_j ≤ 5102 log(10/ζ_j)` for `0 < ε ≤ 1`, the "about
`5102 log(10/ζ_j)`" of Remark `qls:rem:constants` (`repsH_bracket`).

The library `GateEfficientSchedule` proves Theorem `hs:thm:gates` with the
manuscript's schedule. The released clock simulation holds for every admissible
filter depth (`exists_precise_implementation_k`), and the manuscript's
`k = ⌈4W/Q + log₂(4096/ε)⌉` is admissible at the filter accuracy `ε/8`
(`depthMs_admissible`), with `d = k(b_av - 1)`, `b_av = 32Q`, for the integer `Q` of
`ov:eq:Q` (`degreeMs_natCast`). A Cayley step errs by at most `w³/12` in
every Hilbert space (`hamiltonian_cayley_error_sharp`; the released constant is
`1`), so the least power of two `M ≥ max{2, 4αT, (αT)^{3/2}/√(3ε)}` of
`hs:eq:gate-clocks` gives Cayley error `ε/4`. With exact gates the circuit makes
exactly `6d` private calls and has full-output error `ε/2`
(`gate_efficient_simulation_ms`), and over a finite gate set with `ξ = ε/(24d)`
and synthesis `ε/4` the error is `ε` (`sel_simulation_ms`,
`sel_simulation_ms_native`). Beyond the paper, the time-dependent form
(`hs:thm:time` with this circuit) uses the mesh `hs:eq:timegrid` and the
constants `Λ³Δ³/12`, `βΔ²/2` of `hs:eq:timedisc` (`duhamel_step_sharp`,
`mesh_error_sharp`; the released freezing constant is `1`), with error
`ε/2` before synthesis (`gate_efficient_time_simulation_ms`) and `ε` after
it (`sel_time_simulation_ms`). Lemma `hs:lem:abstract` holds with the same
schedule for every real time: exactly `6(32Q - 1)⌈4W/Q + log₂(4096/ε)⌉`
calls of `D` or `D†` (`hs:eq:explicitcount`, `abstract_simulation_ms_explicit`),
at most `3880 (W + Q log(1/ε))`, and full-output error `ε/2`
(`abstract_simulation_ms`). The binary-data and bit-budget endpoints and Lemma
`ode:lem:gate-select` keep the released schedule; `hs:eq:gate-binary` is
asymptotic.

The library `OptimalPrecision` proves Theorem `opt:thm:weights` and Lemma
`opt:lem:tail` of Appendix A of the manuscript, the
analytic core of Theorem `hs:thm:optimal`, without results from other papers.
For every real `q ≥ 1` and integer `M ≥ 1` the explicit weights
`clockWeight q M` of `opt:eq:weights`, built from the paper's gamma mixtures on
the horizon `clockLength q M = D_* + 1 ≤ 27qM`, satisfy `∑ |λ_j| ≤ 3000` and the
exact moments `∑_j λ_j Ces_j(e^{-qMξ} R^k ξ^m) = δ_{m0}` for `0 ≤ m ≤ k < M`
(`clockLength_le`, `sum_abs_clockWeight_le`, `clock_moments`;
`exists_clock_weights` is the existential form of the theorem). The moments are
proved algebraically: the signed clocks act on the polynomial parts of
exponential polynomials, the extraction rule is a linear functional on power
series in `x = -∂`, and its values follow from partial fractions and the zeros
of `C₁` and `C₂` at `α` and `ᾱ`; the inverse Laplace transform and the
distributional pairing of the paper are not used. The variation bound uses the
orthogonality and eigenrelation of the Laguerre functions, Parseval and
Cauchy–Schwarz, and `∫_0^∞ (tφ + tφ' + φ)² ≤ 6512/(qM)`; its proof gives a total
variation below `600`, and the statement keeps the paper's `3000`. For any
weights with these three properties and bounded operators `0 ⪯ D ⪯ δI`,
`-D ⪯ C ⪯ D` on a complex Hilbert space, the signed clock of the transfer is
within `2·3001·(e²·27²b/M)^M` of `e^{-iq²MC}` when `M ≥ 2·27²b`, `b = q²Mδ`
(`Tail.tail_estimate`, for every `δ ≥ 0`), by the accretivity of `Ω`, the Fejér
contraction, the matching jets (no commutation of `C` and `D`), the Joukowski
bound and Cauchy's estimate.

The library `SignedFactorSimulation` proves Theorem `opt:thm:signed` of
Appendix A at the circuit level, from these two results.
The factor interface is `Known P W` (a known isometry `E`, a success projection
`Π` and a reflection `Z` commuting with `Π`); for supplied unitaries `U_B` with
`D = B†B ⪯ δI`, `B = ΠU_BE`, and `H = λB†ZB`, `signed_factor_simulation` gives,
for every `t` and `0 < ε ≤ 1/64`, a known isometric input `P → ℂ^ι ⊗ W` and a
program whose only oracle is the factor query `I_ι ⊗ U_B` and its adjoint, with
no query if `b ≤ ε` and at most `4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` queries
otherwise (`T = λ|t|`, `b = Tδ`), whose full output is within `ε` of
`e^{-itH}`. The proof builds the three-phase private unitary `U_B† G U_B` and its
generator `Ω` (`Known.omega_eq`), the chronological cascade with transfer
`u(w)^m` (`Known.transfer_cascade_factor`), the finite mesh
(`Known.finite_mesh`), the signed linear combination of reuse circuits with
registers of the size of the factor's register (`cascade_block`), the
controlled private steps from `U_B`, `U_B†` and known phases
(`liftU_conj`, `select_implements`, two queries per layer), eight rounds of
amplification by tripling (`ampIter_block_error`, `amplified_error`), the order
`M = ⌈40000 b + 100000 r_b⌉` with its factorial tail (`tail_bound`) and, for
`T < M`, the attenuation of the factor in the known input
(`Known.atten`); negative time uses the adjoint program.

The library `NativeSignedFactor` supplies the factor of Theorem `opt:thm:signed`
from the native sparse oracles (`opt:sec:native`). The
factor unitary `U_B` (`physProgram`) applies the row and column locators on the
two orientations of the edge register, computes the entry word, applies a
local gate (the success factor `√|c| V(c)†` with failure flag, for the entry
`c = H_e/κ` clipped to the unit disk) and uncomputes the word; with the released
masked calls (Lemma `access:lem:control`) it costs `12` native calls. Its known structure
(`physKnown`: the public slot preparation on both orientations, success flag
`0`, orientation sign) gives `B†ZB = H/(sκ)` (`phys_Cop`, `phys_ham`),
`B†B = D_H/(sκ)` (`phys_Dop_eq`) and `B†B ⪯ η/(√s κ) I` (`phys_Dop_le`) for a
Hermitian `H` with entries of modulus at most `κ` and row and column Euclidean
norms at most `η`. Theorem `opt:thm:signed` with every factor query replaced by
this program (`simulates_of_factor`) gives the native simulation
`native_signed_simulation_eta` (`κ = η`, `T = sτ`, `b = √s τ`, at most
`48·10¹⁰ (√(Tb) + √(T r_b) + r_b)` native queries) and its general-scale form
`native_signed_simulation`.

The library `LargeSparsityCore` proves the bound `O(√(sτr))` of the
large-sparsity core (`opt:sec:core`) in the regime `sτ ≥ Lh` with the explicit
threshold `h ≥ 10⁴` of `opt:eq:core-explicit` (`Parameters.Regime`). The
entries are clipped (`opt:eq:clip`, `β = h`), `H/η = c₁ + c₂`; one unitary frame
(the locators, the value oracle and the local gate of the correction factor)
makes the joint private generator, its Cayley transform and the two isolated
spectral projections diagonal, with the clipped part on a third flag of the
correction factor's register (`Native.Kop`, `Native.Dop`, `Native.spectral`);
the known boundary carries the flag state `(|0⟩ + |2⟩)/√2` and gives
`J†KJ = H/α` with `α = sη/q`, `‖P_± J‖² ≤ h/(2s)`, `‖K P₀ J‖² ≤ 2q²/s` and
`‖KJ‖² ≤ 2q²(1 + h)/s` (`Native.compression`, `opt:eq:joint-moments`,
`opt:eq:isolated-weights`). The product filter `g_{B₀}^m g_p^k` of degree
`d ≤ 21520 √(sτr)` is bounded on the actual finite global private block by
Riesz projections and resolvent bounds on three circles
(`CoreFilter.filter_bound`, `Parameters.Regime.filter_estimate`:
`‖f(D_g)‖ ≤ ε/3`), the released amplified smoothing and Cayley
discretisation give full-output error `ε` (`Core.core_implementation`), and
every active layer costs `54` native calls (`Native.active_implementsOn`), so
that `Native.core_simulation` uses at most `6972480 √(sτr)` native queries.

The library `OptimalSparseSimulation` proves the upper bound of Theorem
`hs:thm:optimal` (the proof of Theorem `hs:thm:optimal`, eq.
`opt:eq:regime-comparison`): for `τ = η|t| ≥ 1` and `0 < ε ≤ 1/64`, at most
`2·10¹² (√s τ + √(sτr) + r)` native queries with full-output error `ε`
(`optimal_simulation`), from the baseline simulation (Theorem `hs:thm:main`) for
`h < 10⁴`, the large-sparsity core for `sτ ≥ Lh` and the native signed factor
for `sτ < Lh` (`bounded_bound`, `signed_bound`). The circuits of the first two
act on their own workspaces and are moved to the common form
`NativeSignedFactor.Simulates (physOracle D)` by fixed changes of coordinates
(`SpectatorForm`, `cayleyActive_form`, `improved_form`). The library also proves
the upper bound of Corollary `hs:cor:unitary-optimal`: for exact entries or
entries within `ε/(πN)` of the intended unitary, at most
`5·10¹³ (√(N ρ_ε) + ρ_ε)` entry-oracle queries with `ρ_ε = ℓ/log(e + ℓ)`
(`unitary_optimal`, `unitary_optimal_inexact`). From these circuits the library
also obtains the bound eq. `hs:eq:unitarybound` of Corollary `hs:cor:unitary`,
at most `5·10¹³ (√(Nℓ) + ℓ/log(e + ℓ/N))` calls (`unitary_bound`,
`unitary_bound_inexact`), since `ρ_ε ≤ ℓ` and `ρ_ε ≤ ℓ/log(e + ℓ/N)`. The lower
bound of `hs:thm:optimal` is in `OptimalLowerBounds`; the constant-error `Θ(√N)`
of `hs:cor:unitary-optimal` is that of Corollary `hs:cor:unitary`
(`UnitaryImplementationExtensions`).

The library `TwoNormSimulation` proves Theorem `hs:thm:two-norm` (Appendix B):
with a supplied entry bound `‖H‖_max ≤ μ`, row and column norms at most `η`,
`μ ≤ η ≤ √s μ` and `θ = η²|t|/μ ≥ 1`, at most
`2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` native queries with full-output error
`ε` (`two_norm_simulation`). With the moment parameter `σ = sμ²/η²`, the three
regimes are the baseline Cayley simulation with the clock width
`⌈max{1, γ√σ}⌉` (`bounded_simulation`), the native signed factor at entry
scale `μ`, and the large-sparsity core clipped at `μ`
(`LargeSparsityCore.Native.core_simulation_two`, with the parameters of
`LargeSparsityCore` now taking a real moment parameter).

The library `OptimalLowerBounds` proves the lower-bound results of the second
version. Theorem `hsl:thm:main` holds for every program over any oracle family
whose labels are implemented by two Boolean queries per value call
(`time_of_access`, `main_max_of_access`), in particular in the common query form
of the upper bounds (`commonAccess`); on its hard families, which meet the
hypotheses of `hs:thm:optimal` with `η = 1`, the worst-case query complexity is
between `c₀ S` and `2·10¹² S`, `S = √s τ + √(sτr) + r` (`optimal_theta`,
`hs:eq:optimal-theta`), and `Ω(√(sτL))` cannot hold uniformly
(`not_uniform_sqrt`). Proposition `hsl:prop:two-norm` enlarges the hard
families to `μ H⁰ ⊗ 𝟙𝟙ᵀ` with the public decoder multiplying by `μ`
(`enlargeData`, `two_instances`), so a value call of an enlarged family is one
call of the original family and the constant `c₀` is unchanged (the
manuscript's words of `μ H⁰` cost two calls, an absolute factor):
`max(Q_T, Q_M, Q_P) ≥ c₀ (√s η|t| + √(sμ|t| r_μ) + r_μ)` for trace-distance
accuracy on `ψ_in ⊗ u_m` (`two_norm_main_max`, `accurate_of_embedU`,
`evolve_enlarge`), with the matching upper bound of `hs:thm:two-norm` on these
aligned families (`two_norm_theta`). At `m = 4^k`, `s = 2m`, `η = t = 1`,
`μ = m^{-1/2}`, `L = √m log m`, the bound with the old precision parameter is
at most `6√m`, while `r_μ/32` queries are needed for `k ≥ 47`
(`wrong_denominator`) and the corrected bound holds (`denom_simulates`). In the
native and common access models (not over arbitrary certified families) these
lower bounds also hold, with the same constants, for adaptive protocols
(`two_norm_main_max_tree`) and for algorithms with measurements inside a run
(`two_norm_main_max_measured`, `main_max_measured_common`,
`wrong_denominator_measured`), with success probability at least `2/3`,
conditional trace-distance accuracy and the worst-case number of calls, over
every admissible native access: the four call forms of admissible labels
(`admissible_callFamily`) and, for public locators, the common oracle of the
upper bounds (`admissible_common`) are admissible, the enlarged data have
one-bit entries (`hardAccess_searchTwo`), discarding the ancilla preserves the
accuracy of a mixed output (`densityAccurate_of_embedU`), and deferral
transfers accuracy and worst-case count (`DeferredMeasurementLowerBounds`). The
released common-form simulations are such measured algorithms, with success
probability one and at most `2·10¹² S` value calls (`2·10¹² S'` on the aligned
two-norm families; `measured_of_simulates`), so over the common oracle the
lower bound on the worst-case number of value calls is attained up to the
constant (`optimal_measured_theta`, `two_norm_measured_theta`).

The library `GateOptimalPrecision` formalises Theorem `gate:thm:main` (Section
`gate:sec:result`, proved in Appendix `gate:sec:proof`) in the released gate
model: for `μ ≤ η ≤ √s μ`, `θ = η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`, each of the
three regimes (the bounded-logarithm Cayley circuit, the signed factor with `3⁸`
amplification calls, the clipped transducer on a finer mesh) gives a valid
unitary circuit with at most `2·10¹¹ Q_μ` private and boundary calls,
`10¹³ (Q_μ + 1)(a + m + r + 1)` elementary gates on `2a + 3m + 6r + 5` auxiliary
qubits, `2^m ≤ 10³⁶ (Q_μ + 1)⁴/ε` and full-output error `ε`,
`Q_μ = √s η|t| + √(sμ|t| r_μ) + r_μ` (`gate_optimal_simulation`,
`gate_optimal_simulation_single`), with the private operation of each regime
given by an interface on the gate register. Replacing every private call by its
native compute–rotate–uncompute macro or by the native factor of Section
`gate:sec:native` (compute, arithmetic, the local gates of `U(c)`, inverse
arithmetic, uncompute) and every boundary call by gates gives the native form,
with full-output error `ε + 2·10¹¹ Q_μ ζ'`, `ζ' = 4ζ` or `3ζ` for arithmetic
accuracy `ζ` (`gate_optimal_native`), and total error `ε` with the construction
at `ε/2` and `32·10¹¹ Q_μ ζ ≤ ε` (`gate_optimal_native_total`). The library also
proves Lemma `gate:lem:reuse` in Cesàro form for the released circuit
(`lcuI_ces_pad`), Propositions `gate:prop:signed` and `gate:prop:core`
(`signed_gate_simulation`, `clipped_gate_simulation`), the stable three-qubit
factor `U(c)` with `‖U(c) - I‖ ≤ 2√u` on all inputs (`uMat_action`,
`norm_uMat_sub_one_le`) and its gates (`gRun_locGates`, `norm_uImpl_sub_le`),
the clipping, Cayley and correction-phase identities (`clip_split`,
`edgeMat_cayley`, `hMat_edgeMat_hMat`) and the five-query controlled locator
(`ctrlLoc_agrees`, `ctrlLoc0_agrees`). The library `GateOptimalBinary` derives
every interface and every native identity of the three regimes from binary
sparse oracles: the bounded generator and its Cayley macro with the CORDIC
arithmetic (`boundedIface`, `boundedNative`), the signed factor `U_B = F† U(c) F`
with its native factor (`signedIface`, `signedNative`), and the clipped joint
representation in the frame `W = A F`, whose private Cayley unitary is
`D = U_f† C U_f`, a native factor and a native rotation within `6ξ + 4ζ`
(`clippedIface`, `clipNative`, `gate_optimal_native_clip`). With the scalar
arithmetic of the signed and clipped regimes as hypotheses, each required only
in its own regime, the native circuit makes `10`, `10` or `30` oracle calls per
private call (`gate_optimal_binary`, `gate_optimal_binary_total`; the clipped
call computes the value word three times, where one computation would make
`10` calls), and with single-qubit synthesis and the decomposition of controlled
gates as hypotheses its synthesis uses only gates of the finite set with error
`ε + ε'` (`gate_optimal_binary_synth`) and, for a logarithmic synthesis length,
the finite-gate-set form of `gate:eq:main-gates` (`SynthClaims.gates_log`).

### Statement guides

The [Hamiltonian statement guide](../SparseHamiltonian/Statements.lean),
[ODE statement guide](../SparseODE/Statements.lean),
[linear-system statement guide](../SparseLinearSystems/Statements.lean),
[gate-level statement guide](../GateEfficientHamiltonian/Statements.lean),
[time-dependent statement guide](../TimeDependentHamiltonian/Statements.lean),
[time-dependent ODE statement guide](../TimeDependentODE/Statements.lean),
[time-dependent gate-level statement guide](../GateEfficientTimeDependent/Statements.lean),
[gate-level ODE statement guide](../GateEfficientODE/Statements.lean),
[general ODE statement guide](../GeneralODE/Statements.lean),
[linear-system lower-bound statement guide](../LinearSystemLowerBound/Statements.lean),
[Hamiltonian lower-bound statement guide](../SparseLowerBounds/Statements.lean),
[native gate-level statement guide](../GateEfficientNative/Statements.lean),
[adaptive Hamiltonian lower-bound statement guide](../AdaptiveHamiltonianLowerBound/Statements.lean),
[Chebyshev filter statement guide](../ChebyshevFilter/Statements.lean),
[time-dependent extensions statement guide](../TimeDependentExtensions/Statements.lean),
[ODE lower-bound statement guide](../SparseLowerBounds/ODE/Statements.lean),
[zero-time general ODE statement guide](../GeneralODEZeroTime/Statements.lean),
[lower-bound remarks statement guide](../LowerBoundRemarks/Statements.lean),
[binary-data gate-level statement guide](../GateEfficientBinary/Statements.lean),
[time-dependent binary-data gate-level statement guide](../GateEfficientBinaryTime/Statements.lean),
[finite-gate-set synthesis statement guide](../GateEfficientSynthesis/Statements.lean),
[binary-data gate-level ODE statement guide](../GateEfficientBinaryODE/Statements.lean),
[ODE lower-bound extensions statement guide](../ODELowerBoundExtensions/Statements.lean),
[time-dependent binary-data gate-level ODE statement guide](../GateEfficientBinaryODETime/Statements.lean),
[Chebyshev linear-system statement guide](../ChebyshevLinearSystem/Statements.lean),
[synthesised-trials statement guide](../GateEfficientSynthesisTrials/Statements.lean),
[binary-data ODE budget statement guide](../GateEfficientODEBudget/Statements.lean),
[finite-gate linear-system statement guide](../ChebyshevLinearSystemFinite/Statements.lean),
[zero-time remarks statement guide](../ZeroTimeRemarks/Statements.lean),
[unitary-precision statement guide](../UnitaryImplementationPrecision/Statements.lean),
[adaptive ODE lower-bound statement guide](../AdaptiveODELowerBound/Statements.lean),
[unitary-implementation extensions statement guide](../UnitaryImplementationExtensions/Statements.lean),
[integrable-path simulation statement guide](../IntegrablePathSimulation/Statements.lean),
[zero-time gate-level ODE statement guide](../ZeroTimeGateODE/Statements.lean),
[time-dependent Hamiltonian lower-bound statement guide](../TimeDependentHamiltonianLowerBound/Statements.lean),
[constant-coefficient ODE lower-bound statement guide](../ConstantODELowerBound/Statements.lean),
[physical-oracle ODE lower-bound statement guide](../PhysicalODELowerBound/Statements.lean),
[single-program Dyson statement guide](../DysonSingleProgram/Statements.lean),
[gate-level mesh statement guide](../GateEfficientMesh/Statements.lean),
[bit-length budget statement guide](../GateEfficientBitBudget/Statements.lean),
[gate-level remarks statement guide](../GateEfficientRemarks/Statements.lean),
[deferred-measurement lower-bound statement guide](../DeferredMeasurementLowerBounds/Statements.lean),
[adaptive unitary lower-bound statement guide](../AdaptiveUnitaryLowerBound/Statements.lean),
[signed-time gate-level statement guide](../GateEfficientSigned/Statements.lean),
[coherent-selection statement guide](../GateEfficientSelect/Statements.lean),
[source-quadrature statement guide](../GateEfficientQuadrature/Statements.lean),
[binary coherent-selection statement guide](../GateEfficientBinarySelect/Statements.lean),
[measured unitary lower-bound statement guide](../MeasuredUnitaryLowerBound/Statements.lean),
[general-access Dyson statement guide](../DysonGeneralAccess/Statements.lean),
[time-dependent lower-bound extensions statement guide](../TimeDependentLowerBoundExtensions/Statements.lean),
[released ODE solver lower-bound statement guide](../ReleasedODESolverLowerBounds/Statements.lean),
[computed source-node statement guide](../GateEfficientBinaryNodes/Statements.lean),
[selective-synthesis statement guide](../GateEfficientSelective/Statements.lean),
[Hoeffding-schedule statement guide](../QLSHoeffding/Statements.lean),
[manuscript-schedule statement guide](../GateEfficientSchedule/Statements.lean),
[optimal-precision statement guide](../OptimalPrecision/Statements.lean),
[signed-factor statement guide](../SignedFactorSimulation/Statements.lean),
[native-factor statement guide](../NativeSignedFactor/Statements.lean),
[large-sparsity core statement guide](../LargeSparsityCore/Statements.lean),
[optimal simulation statement guide](../OptimalSparseSimulation/Statements.lean),
[two-norm statement guide](../TwoNormSimulation/Statements.lean),
[optimal lower-bound statement guide](../OptimalLowerBounds/Statements.lean),
[gate-level optimal-precision statement guide](../GateOptimalPrecision/Statements.lean),
[general-source ODE statement guide](../GeneralSourceODE/Statements.lean),
[mixed-output general ODE statement guide](../MixedOutputODE/Statements.lean),
[binary-data optimal-precision statement guide](../GateOptimalBinary/Statements.lean),
[general-source extensions statement guide](../GeneralSourceExtensions/Statements.lean),
[represented-sample ODE statement guide](../RepresentedSampleODE/Statements.lean),
[source-accuracy ODE statement guide](../SourceAccuracyODE/Statements.lean),
[clean-work ODE statement guide](../CleanWorkODE/Statements.lean),
[general-size sparse access statement guide](../GeneralSparseAccess/Statements.lean),
[general-decoder statement guide](../GeneralDecoder/Statements.lean),
[general-size ODE gate-solver statement guide](../GeneralSparseODE/Statements.lean),
[decoder ODE gate-solver statement guide](../GeneralDecoderODE/Statements.lean),
[mesh-certificate ODE statement guide](../MeshCertificateODE/Statements.lean),
[full-class Dyson statement guide](../DysonFullClass/Statements.lean) and
[manuscript-conformance statement guide](../ManuscriptConformance/Statements.lean)
give the precise bounds and quantifiers; the last seventy-five also list where the
proofs depart from the paper's choices (for example averaging instead of
Chebyshev filtering, exact gates, a Chernoff bound with constant `1/4`, an
exact tree preparation of the uniform pointer states, uniform meshes with
their own constants, the step constant of the analytic LCHS grid in the
gate-level ODE solver, the source column and two-tag block encoding of the
general ODE solver, the direct estimate of value queries in the linear-system
lower bound, the enlarged vector error `9νB` of the native ODE solvers, the
weight method for the precision family against adaptive algorithms, the
uniform refinement of nonuniform meshes instead of nonuniform Cayley steps,
the additive adversary with Schur certificates and the explicit constants of
the ODE lower bound, and the two's complement entry format, the Hadamard `U_J`
and the uncontrolled location calls of the binary-data constructions, the
time slot as part of the input of the time-indexed binary data, the
uniform synthesis budget, with the ODE synthesis error absorbed in the native
accuracy, the two-sector LCHS branches and the rounded LCHS step of the
binary-data ODE solvers, the slot comparator for the masked source branches of
the time-dependent one, the chiral reversal instead of the common
conjugator in the signed walk steps of the Chebyshev linear-system proof, a
fresh flag and pool for the exact zero tests of the synthesised trials, the
rescaling `γ = min(1, √(Θ/ℓ))` of the binary-data ODE budgets, the error
budget split into gates, seed and flag in `ChebyshevLinearSystemFinite.main`,
the public bound `η = 0` for a known zero Hamiltonian or generator, the
released source assembly with the identity as SELECT in the zero-time ODE
cases, the tree adversary and the weight method of the adaptive ODE lower
bounds, the integral-equation reading of `U_H(T, 0)` for integrable
paths, a new direct source-assembly circuit with the forcing circuit at weight
zero at `T = 0` and the released amplification extended to successful
amplitudes up to one at gate level, the constant hard paths in normalised
units `η = 1` of the time-dependent lower bounds, for the released ODE
solvers max forms over the constant-coefficient solver's oracle with one
solver per family and runs at fixed split bounds `η_H`, `η_D` and forcing
predicates over the solvers' physical oracles with their controlled call
forms, the coherent cutoff registers and first-success readout of the
single Dyson program, the slot-to-sample map of the gate-level mesh theorems
as part of the presentation of the data, fixed-point public parameters,
base-2 logarithms and a lower bound on the arithmetic accuracy in the budgets
in `𝔟`, the exchange of `D` and `D†` for negative times in the boundary-resolvent
lemma, the register without work wires of the zero-case budgets and a
rescaling of bit length `b_data` on the released registers in the zero case,
the Halmos dilations on fresh record registers and the aligned record-selected
calls of the deferral of measurements, the pairwise correlation gaps of the
adaptive search bound, the pair gaps summed over all ordered pairs with
Cauchy-Schwarz at the trace-distance endpoint `ε₀ = 1/2`, and the heralded
single-program class over a general access, with the mesh as a public
parameter and success and accuracy required on the valid instances (a promise
class), of the Dyson solver, and the Hermitian dilation of the six-query block
encoding with the reduction constant `8` and the exact native realisation of
private operations in the time-dependent lower bounds, and the absorption of the
record registers of the deferral into the spectator index of the released ODE
solvers' oracles by an isometry and the runs at split bounds of the
general-mesh solver in the measured ODE lower bounds, and the algebraic pairing
on the polynomial parts of exponential polynomials in place of the inverse
Laplace transform in the clock-weight construction of Appendix A, and eight rounds
of amplification by tripling, the attenuation of the factor in the known input
and an explicit constant in the signed-factor theorem, and the sign-qubit form
of the local factor, the clipped entry scale and the three-query masked native
calls of the native factor, and the exact real clock weights with `3⁸`
amplification calls, the uniform constants over the three regimes and the
interfaces and native identities as hypotheses on the gate register of the
gate-level optimal-precision theorems, and the exact preparation instances as
part of the input and the rounding of the mesh intervals to whole clock slots
of the general-source extensions).
Paper labels
identify the results across numbering changes.

### Scope qualifications and library relationships

Not formalised here: the sharper hybrid bound (`hs:cor:hybrid`) and the sharper
block-encoding bound `hs:eq:prioroptimal` of Chen, Gao, Wang and Zhou, which
rely on other papers (the additive term `ℓ/log(e + ℓ/N)` of `hs:cor:unitary` is
obtained from Corollary `hs:cor:unitary-optimal` instead,
`OptimalSparseSimulation.unitary_bound`), Lemma `odel:lem:dyson` in full (`DysonFullClass` proves
the lemma with label-controlled loading and a classical propagator on each closed mesh cell, with
branch certificates through the coverage theorems of `ManuscriptConformance.BranchCertificates`;
a loader specified only on its clean columns is covered in the exact case only
(`DysonFullClass.full_dyson_columns`, `full_single_columns`, `full_actual_columns`), and a jump
inside a cell is not covered), represented samples whose dissipative
parts are not positive semidefinite in the endpoints of `TimeDependentODE`,
`GeneralSourceODE` and `TimeDependentExtensions` (`ode:thm:time` itself admits
them: `ManuscriptConformance.ode_thm_time`, through `RepresentedSampleODE`), a version of
`GeneralODE.general_nonneg` for the mixed-output solver hypothesis,
the normalisation `2πΛ` of Lemma `ode:lem:block`
(`GeneralODE.NativeBlock.exists_native_block` has this package's `8√2 Λ`), Theorem `ode:thm:time`
with a jump of the generator inside a mesh cell or a loader specified only on clean inputs
(`ManuscriptConformance.ode_thm_time` takes a classical propagator on each closed mesh cell and
label-controlled loading, this package's hypotheses), Lemma `ode:lem:gate-select` with the
manuscript's schedule and mesh (`GateEfficientSelect` and `GateEfficientBinarySelect` have `T > 0`,
the package's filter degree `GateCircuit.Sim.fDeg` and subdivision condition, whose coarsest
solution for the solver's circuit is `ManuscriptConformance.odeMesh`, in the native model the
sample certificate `δ/32`, and from binary data the dyadic labels of the solver with `4s` in place
of `p = 2s`), Theorem `ode:thm:gates` over a finite gate set for general data (the conformance
endpoints count native gates; the finite-set forms hold under this package's format hypotheses,
native data or the binary format, with `T > 0` in these forms: `GateSynth.native_ode_solver_synth`,
`GateSynth.native_ode_time_solver_synth`, `GateSelective.binary_ode_budget_sel`,
`GateSelective.binary_ode_time_budget_sel`), and in its conformance endpoints a binary entry
decoding that is not exact (`ManuscriptConformance.BinaryEntryDecoding`), source nodes off the slot
times, sources that are not native circuits, and a mesh other than the endpoint's (`M = 2^m` with
`m ≥ ManuscriptConformance.odeMeshG …`; the lemma's conditions enter at `δ = ν/16`, where the
manuscript takes `δ = ν`), a value oracle that is not additive on every pair of `k`-bit index words
outside the writer endpoints (`NativeSparseBlockEncoding.oracles`, `GeneralSparseAccess.QData`: a
writer specified only on clean targets is covered for `hs:thm:main`, `hs:thm:optimal`,
`hs:thm:two-norm`, `qls:thm:main`, `qls:cor:separate`, `ode:thm:main`, `ode:thm:general` and, with
a time-indexed writer, `ode:thm:time` by `ManuscriptConformance.hs_thm_main_writer` and its seven
companions, and a
writer specified only on the clean inputs of valid index pairs for the general-size gate theorems
`hs:thm:gates` and `gate:thm:main` by `ManuscriptConformance.hs_thm_gates_general_writer` and its
three companions and for the general-size forms of `ode:thm:gates` with the decoder `c₀(X + iY)` or
with binary entry decoding by `ManuscriptConformance.ode_thm_gates_general_writer`,
`ManuscriptConformance.ode_thm_gates_decoder_writer` and their companions, not for the other ODE
and linear-system endpoints; the manuscript gives XOR-writing as an example of a reversible
writer),
operator-norm error for adaptive
algorithms in the `Ω(√N)` bound of `hs:cor:unitary` (the trace-distance bounds
of `MeasuredUnitaryLowerBound` hold up to the endpoint `ε₀ = 1/2` and are empty
at `N = 2`, as trace distance forces; the operator-norm form is stated for
measured algorithms, which have an input slot) and for algorithms that reject
(success probability below one; the heralded trace-distance bounds apply to
them), the operator-norm bound on the wider range `ε₀ √(1 - ε₀²/4) ≤ 1/2`,
measured algorithms run next to an untouched reference register (the linear-map
fact is `SparseHamiltonian.FiniteReferenceLift.norm_lift_le`), a formal
comparison of the operator-norm program bound over the entry oracle with the
pairwise program bound, containment of the adaptive protocols in the measured
model for infinite-dimensional workspaces (an instrument with finitely many
outcomes cannot reset such a workspace; the deferral and the measured lower
bounds hold for workspaces of every dimension), for general single-label
controlled access with several counted labels a bound that charges each aligned
slot only for the labels it uses, a measured form over the aligned sampled
family of the time-dependent simulators with any slot count and degree (the
measured bounds are stated over the native and coherent sampled-time oracles,
over the released oracle families of the time-dependent simulators in
`TimeDependentLowerBoundExtensions`, and over the physical oracles of the
released ODE solvers in `ReleasedODESolverLowerBounds`), a measured non-vacuity
witness for the windows simulators, Carathéodory solutions of ODEs with
integrable generators (the generalisations of `ode:thm:time` use classical
propagators on each mesh interval, and classical solutions except for the mild
solutions of `RepresentedSampleODE`, whose forcing need only be integrable;
Carathéodory propagators of integrable Hamiltonian paths are in
`IntegrablePathSimulation`), the class of piecewise
Lipschitz inputs of `ode:thm:time` in the ODE lower bounds (it is named here
only for the Hamiltonian class), for the lower bound of `hsl:thm:main` on the
time-dependent classes coherent selection of public parameters other than
durations and start times, adaptive algorithms in the block-encoding model
stated by name (they would follow from the measured block-encoding bounds),
block-encoding calls for block encodings of normalisation below `s · scale`, a
`ξ`-tolerant gate-level form whose hypothesis bounds the error of the executed
circuit (the form with the ideal circuit's error plus `nPriv · ξ` is proved),
measured forms of the gate-level bounds, the native gate-level model
`SparseHamiltonian.GateNative`, the realisation of the released simulator's
private operation by sparse queries (`NativeRealization`, or `ApproxRealization`
within `ξ`; the released gate-level library takes it as the hypothesis
`NativeOK`, and the gate-level bounds of `TimeDependentLowerBoundExtensions` are
conditional on it; it is shown for single call forms of the native queries), and
family forms and separate heralded forms over the families of that library
(`TimeDependentHamiltonianLowerBound` proves the bound for the uniform-mesh,
nonuniform-mesh and integrable-path classes, and
`TimeDependentLowerBoundExtensions` in the time-indexed block-encoding model,
with coherent selection of durations and start times, for gate-level circuits
(exactly or within `ξ`), for the piecewise Lipschitz class, over all call forms
of the released families and for measured algorithms over them, all with the
constant hard paths), the lower bound of `hsl:thm:main` with hard instances that
vary in time (which the manuscript does not claim; its hard instances for the
time-dependent classes are time independent), nonuniform Cayley steps at gate
level (`GateEfficientMesh` covers nonuniform meshes by a uniform refinement of
the clock, with the slot-to-sample map as part of the presentation of the data,
and for dissipative equations keeps the left-endpoint source quadrature of the
mesh in its certificate), the coherent per-label angles of `ode:lem:gate-select`
(`GateEfficientSelect` formalises its branch-dependent meshes with exact gates
and natively, with the step of each branch in its private operation and the
source certificate derived only for the left-endpoint quadrature, with the
paper's constants in `GateEfficientQuadrature`; `GateEfficientBinarySelect`
constructs the binary-data arithmetic and the binary-data, finite-gate-set and
budget solvers on these meshes for the dyadic source nodes of the proof, and
`GateEfficientBinaryNodes` for coherently computed source nodes with integrated
certificates for the generator samples), the dissipative propagator `U(T, v)`
and the Duhamel formula as Lean objects at gate level (`GeneralSourceODE` has
both at query level, `IsPropagator` and `duhamel`; `GateEfficientQuadrature`
proves the source certificate of the left-endpoint quadrature directly, with
homogeneous solutions), the block-input linear-system solver used by
`ode:thm:general` for `T > 0` (a hypothesis there), for the constant-coefficient
released ODE solver of `ode:thm:main` the ODE lower bounds whose hard families
are time dependent (`odel:thm:joint`, `odel:rem:homogeneous` and the joint term
of `odel:thm:combined`, which the manuscript does not claim for
constant-coefficient equations, and runs of that solver on such families; the
others are applied to it in `ConstantODELowerBound` and `PhysicalODELowerBound`,
and for measured solvers in `ReleasedODESolverLowerBounds`), common-dimension
and qubit-register forms of the padded `g = 1` families alone over the physical
oracle of the released general-mesh ODE solver (for adaptive or measured
solvers), input-dependent source interfaces in the ODE lower bounds, for the
single program of the Dyson solver of `odel:lem:dyson` on its general
certified-mesh access (`DysonGeneralAccess`) a source-call bound and circuit and
time-register sizes (not claimed by the manuscript, which counts only matrix
queries) and the selection of the mesh inside the program (the manuscript
selects it classically from the public certificate), the literal sorted-label
sampling of that solver (replaced by occupation-number configurations with the
same operator identity), the forms of the padded hard families other than those
stated (for the Hamiltonian families only the non-adaptive spectator form, for
the linear systems not the `*_readout` forms), the forms in `𝔟` of the solvers
that synthesise every trial (also in the zero case of the remark of
`ode:thm:gates` on zero time or a known zero generator), bounds on the registers
of the general binary-data ODE solvers in that zero case without a bit-length
hypothesis on the free rescaling `γ` (`GateEfficientRemarks` proves the remark
with every trial synthesised and with the absolute constants of
`ode:eq:gate-main` and `ode:eq:gate-space`), single-qubit synthesis over a
finite gate set and the decomposition of controlled gates (hypotheses of the
synthesis library for `hs:thm:gates` and `ode:thm:gates`), the explicit accounting of
`hs:thm:gates` (eqs. `hs:eq:gate-known`, `hs:eq:gate-Gzero`, `hs:eq:gate-total`) at the printed
schedule when `s` is not a power of two, as far as the boundary circuit is concerned
(`SparseGateAccounting.sparse_gate_original` keeps the schedule at the original `s` for a supplied
boundary circuit preparing the boundary state of the `s` original slots, the uniform-range
preparation, which is not constructed; with the Hadamard boundary circuit,
`SparseGateAccounting.sparse_gate_constructed` has `s' = 2^⌈log₂ s⌉` in place of `s`; in both the
private circuit is constructed from the decoder's angle arithmetic, with the promise derived), exact
decompositions
of the inverse and zero-test gates over gate sets that do not contain them
(hypotheses of the synthesised-trials library), floating-point public parameters
in the budgets in `𝔟` (`GateEfficientBitBudget` covers fixed-point parameters),
Lemma `hs:lem:abstract` for isometries into infinite-dimensional private spaces
that do not extend to a unitary and with approximately implemented `D₀`, the
construction of the source circuits from concrete data formats (the binary-data
libraries construct the compute circuits, entry decoding and angle arithmetic
for time-independent and time-dependent Hamiltonians and dissipative ODEs; in
the native gate-level library their accuracy and the identity `NativeOK` are
hypotheses and their gate counts are parameters), gate counts for the
linear-system algorithm and the synthesis of its approximately implemented known
gates (only their accuracies are modelled), the literal signed step
`qls:eq:signedstep` for the released walk (Lemma `qls:lem:signedwalk` is proved
for it through a chiral symmetry in `ChebyshevLinearSystem`), and classical
circuit-generation costs. Of the improved-precision results (Section
`hs:sec:optimal` and Appendices A and B), Theorems `opt:thm:weights` and
`opt:thm:signed`, Lemma `opt:lem:tail`, the native sparse factor of
`opt:sec:native`, the large-sparsity core of `opt:sec:core` (Proposition
`opt:prop:core`), Theorem `hs:thm:optimal` with its `Θ` statement, the upper
bound of Corollary `hs:cor:unitary-optimal`, Theorem `hs:thm:two-norm` (Appendix
B), Proposition `hsl:prop:two-norm` and the obstruction for the logarithmic
denominator (also for adaptive and measured algorithms) are formalised
(`OptimalPrecision`, `SignedFactorSimulation`, `NativeSignedFactor`,
`LargeSparsityCore`, `OptimalSparseSimulation`, `TwoNormSimulation`,
`OptimalLowerBounds`); the constant-error `Θ(√N)` of `hs:cor:unitary-optimal` is
that of Corollary `hs:cor:unitary` (`UnitaryImplementationExtensions`). Of the
improved-precision gate results (Section `gate:sec:result` and Appendix
`gate:sec:proof`), Theorem `gate:thm:main` and its single-norm case (with exact
gates and with native private calls), Lemma `gate:lem:reuse`, Propositions
`gate:prop:signed` and `gate:prop:core` and the constructions of Section
`gate:sec:native` are formalised (`GateOptimalPrecision`; Lemma
`hs:lem:boundary` is the released boundary network, and Proposition
`gate:prop:finite` is formalised without finite-set synthesis; the three propositions and the remark
after `opt:thm:signed` are in the native gate model, with sector-controlled calls in
`gate:prop:finite`, the success projection and sign reflection on designated flag qubits instead of a
general `Π` and `Z`, the private call `GateOptimalBinary.ClipNative` of the clipped circuit, and
exact weights rather than rounded coefficients; at proposition level over a finite gate set the
three propositions also hold with a supplied finite-set private or factor circuit charged at its
actual linear cost and the remaining known gates synthesised, `ManuscriptConformance.gate_prop_finite_sel`,
`gate_prop_signed_sel`, `gate_prop_core_sel` and their `_native` forms, by the selective construction
rather than the coefficient rounding of the manuscript; a general known `Π` and `Z` reach the
signed circuit through a supplied conversion to designated flag qubits, charged in the circuit when
it is given by gates, `ManuscriptConformance.gate_prop_signed_known_conv`, its synthesis from a
description of `Π` and `Z` not formalised), and for binary
sparse oracles the gate-register interfaces and native identities of the three
regimes are derived from the oracles and finite-set synthesis is applied with
single-qubit synthesis and the decomposition of controlled gates as hypotheses
(`GateOptimalBinary`; the scalar arithmetic of the signed and clipped regimes,
a hypothesis of the main theorems, is met at every accuracy by reversible
lookup tables, `GateOptimalBinary.gate_optimal_binary_tables`); not formalised
are the external single-qubit synthesis result, a polynomial-cost scalar
arithmetic (the tables have length exponential in `b`), a fused
clipped call with one computation of the value word, the dyadic rounding
of the signed weights and the classical compilation of the tables, and the
Möttönen and one-Grover-round preparations (the released exact tree
preparations are used instead). `SparseODE/Statements.lean` predates the time-dependent
ODE library and still lists `ode:thm:time` as outside that library; it and the
time-dependent and gate-level ODE statement guides also predate the general ODE
library and list `ode:thm:general` as outside their libraries.
`SparseLinearSystems/Statements.lean` predates the lower-bound library and lists
`qlsl:thm:main` as outside it, and the Hamiltonian, ODE, time-dependent and
gate-level ODE statement guides predate the lower-bound libraries and list lower
bounds as outside them. The exact-gate statement guides predate the native
gate-level library and list parts of the gate analyses that it now covers
(approximate private Cayley implementations, entry decoding and arithmetic, the
binary-entry corollary, negative times for time-independent Hamiltonians) as
outside their libraries; the native sparse instantiation of `U_J` and of the
private and slot-selected Cayley operations, which they also list, is
constructed for binary data by the binary-data libraries. The Hamiltonian
lower-bound statement guides predate the adaptive library and list adaptive
algorithms as outside them. The linear-system statement guide predates the
Chebyshev filter library; its note that the proof of `qls:thm:main` uses the
averaging filter, so that signed steps are not needed, still applies. The
time-dependent and time-dependent ODE statement guides predate the
time-dependent extensions library and list nonuniform meshes, breakpoints,
integrated sample-error certificates, coherent parameters and the time-indexed
block-encoding case as outside their libraries. The general ODE statement guide
predates the zero-time library and lists the case `T = 0` as outside it. The
Hamiltonian lower-bound statement guides predate the ODE lower-bound and
lower-bound remarks libraries and list the ODE lower bounds, the padding to a
common dimension and the parity-amplitude remark as outside them; the
linear-system lower-bound guide lists the padding remark as outside it. The
native gate-level statement guide predates the binary-data library and lists the
construction of the compute circuit and of the arithmetic from a concrete data
format as outside its library. The binary-data statement guide predates the
time-dependent binary-data library and lists `hs:thm:time` with the circuit of
`hs:thm:gates` from binary data as outside its library. The exact-gate, native
and binary-data gate-level statement guides predate the synthesis library and
list finite-gate-set synthesis as outside their libraries; the synthesis library
adds it for the native and binary-data circuits, with single-qubit synthesis and
the decomposition of controlled gates as hypotheses. The binary-data,
time-dependent binary-data and synthesis statement guides predate the
binary-data ODE library and list `ode:thm:gates` from binary data as outside
their libraries; the binary-data ODE library adds it for constant coefficients
and the time-dependent binary-data ODE library for time-dependent coefficients,
and the binary-data ODE statement guide predates the latter and lists the
time-dependent part as outside it. The Chebyshev filter statement guide predates
the Chebyshev linear-system library and lists Theorem `qls:thm:main` with the
Chebyshev filter, and Lemma `qls:lem:signedwalk` for the released walk, as
outside it; both are proved there. The synthesis statement guide predates the
synthesised-trials library and lists the per-trial claim of `ode:thm:gates`
after synthesis as outside it; the time-dependent binary-data ODE statement
guide predates the ODE budget library and lists the asymptotic form of
`ode:eq:gate-main` as outside it; the Chebyshev linear-system statement guide
predates the finite-gate linear-system library and lists the finite-gate
allowance and the constants of Remark `qls:rem:constants` as outside it. The
time-dependent extensions, time-dependent ODE and zero-time general ODE
statement guides predate the zero-time remarks library and list the degenerate
cases `T = 0`, `η = 0` and `α = 0`, the zero-time and zero-energy branches, or
the remarks after `hs:thm:time` and `ode:thm:main` as outside their libraries;
the zero-time remarks library adds them (the gate-level remark of
`ode:thm:gates` is added by the zero-time gate-level ODE library).
`SparseLowerBounds/ODE/Statements.lean` predates the ODE lower-bound extensions
library and lists Theorem `odel:thm:psd`, Lemma `odel:lem:dyson` with eq.
`odel:eq:fixed` and its consequence, Proposition `odel:rem:homogeneous`, the
padding remarks of the ODE lower bounds, the comparison with the ODE upper
bounds, the application to the released ODE solvers and adaptive solvers as
outside it; its note, and that of `SparseLowerBounds/ODE/Model.lean`, that there
is no Lean transport between the lower-bound access and the released solvers'
flattenings no longer applies to the general-mesh solver
`TimeDependentExtensions.ODE.solver`
(`ODELowerBoundExtensions.Release.physicalOracle_normal_form`,
`ODELowerBoundExtensions.Dyson.familyLayout_matrix`); the constant-coefficient
solver of `ode:thm:main` is bridged by the later library `ConstantODELowerBound`
(`ConstantODELowerBound.Normal.physicalOracle_normal_form`). The lower-bound
remarks statement guide lists the ODE padding remarks as outside it. The ODE
lower-bound and ODE lower-bound extensions statement guides and
`SparseLowerBounds/ODE/Model.lean` predate the adaptive ODE lower-bound library
and list adaptive solvers, controlled oracle calls (covered there only by a
documented reduction) and the forms of Theorem `odel:thm:psd`, Proposition
`odel:rem:homogeneous` and the padded families beyond single programs as outside
them; the adaptive library proves them over the sampled-time access. The
Hamiltonian statement guide predates the unitary-precision and
unitary-implementation extensions libraries and states `hs:cor:unitary` at error
`1/4` with exact entries; the Hamiltonian and adaptive Hamiltonian lower-bound
guides and the unitary-precision guide list the unitary `Ω(√N)` search bound as
outside them; the extensions library proves it. The time-dependent extensions
statement guide predates the integrable-path simulation library and lists
Carathéodory propagators of general integrable paths as outside it; they are
proved there for Hamiltonian paths, and Carathéodory solutions of ODEs with
integrable generators remain outside. The zero-time remarks, binary-data
gate-level ODE and time-dependent binary-data gate-level ODE statement guides
predate the zero-time gate-level ODE
library and list the gate-level remark of `ode:thm:gates`, or the cases `T = 0`
and `η_H + η_D = 0`, as outside them; that library proves them (the note of the
ODE budget guide on these cases still applies to its budgets). The
time-dependent, time-dependent extensions and integrable-path simulation
statement guides predate the time-dependent Hamiltonian lower-bound library and
list lower bounds for their classes as outside them; that library proves the
lower bound of `hsl:thm:main` for the uniform-mesh, nonuniform-mesh and
integrable-path classes. The ODE lower-bound, ODE lower-bound extensions and
adaptive ODE lower-bound statement guides predate the constant-coefficient ODE
lower-bound library and list the application of the ODE lower bounds to the
constant-coefficient solver of `ode:thm:main` as outside them; it is proved
there for the `g = 1` Hamiltonian and positive semidefinite families (the joint
`ḡ √s τ` term, which the manuscript does not prove for constant-coefficient
equations, is not claimed). The ODE lower-bound extensions and adaptive ODE
lower-bound statement guides predate the physical-oracle ODE lower-bound library
and list controlled calls of the released ODE solvers' physical oracles and the
forms of Theorem `odel:thm:psd`, Proposition `odel:rem:homogeneous` and the
padded families over the general-mesh solver's oracle as outside them; they are
proved there. The ODE lower-bound extensions statement guide (with
`ODELowerBoundExtensions/Dyson/Family/Retry.lean`) predates the single-program
Dyson library and lists a single-program `Solver` form of the Dyson algorithm of
`odel:lem:dyson`, and with it the refutation of a uniform bound for single
programs, as outside it; both are proved there on the ODE lower-bound class. The
time-dependent gate-level and time-dependent binary-data gate-level statement
guides predate the gate-level mesh library and list nonuniform meshes as outside
them, the time-dependent binary-data gate-level ODE statement guide lists the
regularity and sample certificates of the generator path and nonuniform meshes,
the integrable-path simulation statement guide states that the gate-level
time-dependent theorems keep their classical hypotheses, and the integrable-path
simulation and time-dependent extensions statement guides list the gate costs of
the time slots as outside them; the gate-level mesh library proves the
gate-level time-dependent theorems under integrated certificates and, by uniform
refinement of the clock, on nonuniform meshes (nonuniform Cayley steps remain
outside; the branch-dependent meshes of `ode:lem:gate-select` are in the
coherent-selection library). The binary-data ODE budget statement guide (with
`GateEfficientODEBudget/Words.lean`) predates the bit-length budget library and
lists the bound of the words `F`, `n_c` and the bits of `κ` by `𝔟`, the
comparison of `q`, `ℓ` for `(2g, ε/2)` with those for `(g, ε)` and a word form
of the finite-gate-set budget as outside it; the bit-length budget library
proves the first two for fixed-point public parameters and states the
finite-gate-set budget in `𝔟`. The binary-data gate-level statement guide reads
the `𝔟` form of `hs:eq:gate-binary` off its bounds; the bit-length budget
library states it. The statement guides of `GateEfficientBitBudget` (the qubit
count of `hs:thm:gates` in `𝔟` and the absorption of the source costs into
`q poly(𝔟)`), `ZeroTimeRemarks` (the zero-time forms of the binary-data and
finite-gate-set variants of `hs:thm:gates`), `ZeroTimeGateODE` (the forms of its
remark with every trial synthesised and with the absolute constants of
`ode:eq:gate-main` and `ode:eq:gate-space`) and `GateEfficientODEBudget` (the
cases `T = 0` and `η_H + η_D = 0`) predate the gate-level remarks library and
list these items as outside them; that library proves them, within the scope
stated in its guide, and states Lemma `hs:lem:abstract`, which the exact-gate
statement guide cites for nonnegative times, for every real time. The
linear-system, adaptive Hamiltonian, adaptive ODE, time-dependent Hamiltonian,
constant-coefficient ODE and physical-oracle ODE lower-bound statement guides
predate the deferred-measurement lower-bound library and list measurements
inside a run followed by classically controlled operations (and measurements
with more than two outcomes) as outside them; the deferral is proved there, and
the headline lower bounds are stated there for measured algorithms (for the
time-dependent class over the coherent sampled-time access and its call forms;
over the released physical oracles of the ODE solvers they are stated in the
released ODE solver lower-bound library). The unitary-implementation extensions
statement guide predates the adaptive unitary lower-bound library and lists
lower bounds against adaptive or controlled-call algorithms as outside it; they
are proved there. The gate-level remarks statement guide predates the
signed-time gate-level library and lists negative times for the circuits from
binary sparse oracles as outside it; they are proved there. The gate-level mesh
and time-dependent binary-data gate-level ODE statement guides predate the
coherent-selection library and list the branch-dependent meshes of
`ode:lem:gate-select` as outside them; that library formalises them with exact
gates and natively, with the step of each branch in its private operation (the
coherent per-label angles of the lemma's proof remain outside; the binary-data
arithmetic is in `GateEfficientBinarySelect`). The coherent-selection statement
guide predates the source-quadrature library and lists the comparison `B_m ≤ 2B`
with the continuous source mass as outside it; the source-quadrature library
proves it for the left-endpoint quadrature, with the paper's certificate
constant `T² C_b / (2m)`. The coherent-selection and source-quadrature statement
guides predate the binary coherent-selection library and list the binary-data
arithmetic of `ode:lem:gate-select`, integrated sample-error certificates and
the binary-data and finite-gate-set solvers on branch-dependent meshes as
outside them; that library formalises the integrated certificate for the lemma
(not for the generator samples of the solvers), and the arithmetic and the
solvers for the dyadic source nodes of the proof. The binary coherent-selection
statement guide predates the computed source-node library and lists source nodes
off the dyadic grid, integrated certificates for the generator samples of the
solvers and energy bounds only at the branch addresses as outside it; that
library formalises them. The finite-gate-set synthesis, synthesised-trials,
bit-length budget and computed source-node statement guides predate the
selective-synthesis library, in which the supplied private-operation and source
circuits are retained instead of synthesised (the separated forms of
`hs:eq:gate-total`, `ode:eq:gate-main` and `ode:eq:gate-space`). The finite-gate
linear-system statement guide predates the Hoeffding-schedule library and lists
Hoeffding's inequality and the repetition count of `qls:eq:hoeffding` as outside
it; that library formalises them. The gate-level statement guides of the
released Hamiltonian endpoints use the released filter schedule and slot counts;
the manuscript-schedule library gives the schedule of `hs:eq:gate-schedule`,
`hs:eq:gate-clocks` and `hs:eq:timegrid`. The adaptive unitary and
deferred-measurement lower-bound statement guides predate the measured unitary
lower-bound library and list the endpoint `ε₀ = 1/2` of trace-distance accuracy
(and the deferred-measurement guide the named measured forms over the controlled
and controlled-inverse entry calls and a named operator-norm form) as outside
them; they are proved there (the operator-norm form for measured algorithms,
with the sharp trace distance `ε√(1 - ε²/4)`), while operator-norm forms for
adaptive algorithms remain outside. The deferred-measurement lower-bound
statement guide also predates the time-dependent lower-bound extensions library
and lists named measured forms over the released oracle families of the
time-dependent simulators as outside it; they are proved there. The
single-program Dyson statement guide predates the general-access Dyson library
and lists a single-program form for the general certified-mesh class of
`odel:lem:dyson` as outside it; it is proved there. The time-dependent
Hamiltonian lower-bound statement guide predates the time-dependent lower-bound
extensions library and lists time-indexed block encodings, coherent selection of
durations and windows, the gate-level time-dependent theorems and controlled
calls of the released physical families as outside it; they are proved there
(the gate-level forms conditional on `NativeRealization` or, within `ξ`,
`ApproxRealization`), and so is the piecewise Lipschitz corollary for the
Hamiltonian class, while family forms and hard instances that vary in time
remain outside. The physical-oracle ODE lower-bound statement guide predates the
released ODE solver lower-bound library and lists runs of the released
general-mesh solver on the positive semidefinite and homogeneous families as
`ReleaseRun`s as outside it; the released solver certifies such runs at
`Θ = τ η_H + τ η_D ℓ ≥ τℓ` rather than `Θ = τ`, and the runs at split bounds
(`Runs.MeshRun`, which contains `ReleaseRun`) are given in the released ODE
solver lower-bound library, with lower and released upper bounds side by side. The
statement guides of the time-dependent gate-level ODE solvers (`GateEfficientODE`,
`GateEfficientBinaryODETime`, `RepresentedSampleODE`, `SourceAccuracyODE`) predate the
mesh-certificate ODE library and state them under the package's uniform-mesh conditions; that
library proves the guarantees of the native time-dependent protocol and of the general-size and
decoder protocols under the manuscript's source and sample certificates, and gives the
certificate-form instance conditions of the released oracles for time-indexed binary data.

## Validation and audits

The default `lake build` includes both extensions, the linear-system library,
the gate-efficient and time-dependent Hamiltonian libraries, the gate-level
time-dependent simulation library, the time-dependent, gate-efficient and
general ODE libraries, the linear-system and Hamiltonian lower-bound
libraries, the native gate-level library, the adaptive Hamiltonian lower-bound
library, the Chebyshev filter library, the Chebyshev linear-system library,
the time-dependent extensions library,
the ODE lower-bound library, the zero-time general ODE library, the
lower-bound remarks library, the binary-data gate-level library, the
time-dependent binary-data gate-level library, the finite-gate-set synthesis
library, the binary-data gate-level ODE library, the ODE lower-bound
extensions library, the time-dependent binary-data gate-level ODE library, the
synthesised-trials library, the binary-data ODE budget library, the finite-gate
linear-system library, the zero-time remarks library, the unitary-precision
library, the adaptive ODE lower-bound library, the unitary-implementation
extensions library, the integrable-path simulation library, the zero-time
gate-level ODE library, the time-dependent Hamiltonian lower-bound library, the
constant-coefficient ODE lower-bound library, the physical-oracle ODE
lower-bound library, the single-program Dyson library, the gate-level mesh
library, the bit-length budget library, the gate-level remarks library, the
deferred-measurement lower-bound library, the adaptive unitary lower-bound
library, the signed-time gate-level library, the coherent-selection library,
the source-quadrature library, the binary coherent-selection library, the
measured unitary lower-bound library, the general-access Dyson library, the
time-dependent lower-bound extensions library, the released ODE solver
lower-bound library, the computed source-node library, the selective-synthesis
library, the Hoeffding-schedule library, the manuscript-schedule library, the
optimal-precision library, the signed-factor library, the native-factor library,
the large-sparsity core library, the optimal simulation library, the two-norm
simulation library, the optimal lower-bound library, the gate-level
optimal-precision library, the general-source ODE library, the mixed-output
general ODE library, the binary-data optimal-precision library, the
general-source extensions library, the represented-sample ODE library, the
source-accuracy ODE library, the clean-work ODE library, the general-size sparse access
library, the general-decoder library, the general-size ODE gate-solver library, the decoder
ODE gate-solver library, the mesh-certificate ODE library, the full-class Dyson library,
the private-space abstract-simulation library, the sparse gate-accounting library, the
manuscript-conformance library and **14695 checked axiom audits**.
Each fixes Lean's exact axiom report, ignoring message whitespace: exactly
`propext`, `Classical.choice` and `Quot.sound`, except for 28 combinatorial
lemmas of the gate-efficient ODE library, 2 index lemmas of the gate-level
time-dependent library, 6 slot-index lemmas of the general ODE library, 5
elementary lemmas of the linear-system lower-bound library, 19 elementary
lemmas of the Hamiltonian lower-bound library, 27 wire and literal lemmas of
the native gate-level library, a bit-table lemma and a weight lemma of the
adaptive Hamiltonian lower-bound library, 6 slot-index and ring-identity
lemmas of the time-dependent extensions library, 7 graph and locator lemmas of
the ODE lower-bound library, 6 padded-table lemmas of the lower-bound remarks
library, 148 wire, bit-vector and circuit-bookkeeping lemmas of the
binary-data gate-level library, 2 wire lemmas of the time-dependent
binary-data gate-level library, 3 control and placement lemmas of the
synthesis library, 90 wire, bit-vector and register-program lemmas of the
binary-data gate-level ODE library, 8 table, word, index and weight lemmas
of the ODE lower-bound extensions library, 17 wire, configuration,
bit-vector and register-program lemmas of the time-dependent binary-data
gate-level ODE library, an AND-chain lemma of the synthesised-trials
library, 6 degree-half lemmas of the finite-gate linear-system library, 2 index lemmas of the
unitary-precision library, a bit-table
lemma of the unitary-implementation extensions library, two configuration
lemmas and a wire-placement lemma of the zero-time gate-level ODE library,
2 two's complement word lemmas of the bit-length budget library, 4 register
and index lemmas of the deferred-measurement lower-bound library, 2 two's
complement word lemmas of the signed-time gate-level library, 3
label-configuration and index lemmas of the coherent-selection library,
23 layout, wire, XOR-permutation and register lemmas of the binary
coherent-selection library, a call-form instance and lemma of the measured
unitary lower-bound library, a cost lemma of the time-dependent lower-bound
extensions library, 2 call-form selector lemmas and a weight lemma of the
released ODE solver lower-bound library, 24 layout, gate-count, wire,
injectivity, bit-vector and register lemmas of the computed source-node library,
4 wire-map lemmas of the selective-synthesis library, a Laguerre-coefficient
lemma and 2 `ξ`-coefficient lemmas of the optimal-precision library, 2
branch-length lemmas of the signed-factor library, 9 noncommutative ring
identities of the large-sparsity core library and 2 definitional table lemmas
of the optimal lower-bound library and a padded-length lemma, an index lemma, a
control lemma, 2 XOR lemmas and 2 configuration lemmas of the gate-level
optimal-precision library, 30 wire, index and injectivity lemmas of the
binary-data optimal-precision library, 49 wire, layout, word, index and
injectivity lemmas of the general-size sparse access library, 10 wire, word,
layout and injectivity lemmas of the general-decoder library, 5 wire-map and
injectivity lemmas of the general-size ODE gate-solver library, 10 wire, word,
configuration and injectivity lemmas of the decoder ODE gate-solver library and
a bit-vector lemma, a two's complement word lemma, five wire and injectivity
lemmas, a copy-bit lemma and four weight lemmas of the manuscript-conformance
library, whose
reports list a subset of these three axioms (or none).

Warnings remain enabled. Individual audit modules can also be built as Lake
targets by their qualified module names.

The linear-system, both time-dependent, the gate-level time-dependent, the
gate-efficient ODE, the general ODE, the ten lower-bound, the native
gate-level, the Chebyshev filter, both Chebyshev linear-system, the
time-dependent extensions, the zero-time general ODE, the lower-bound remarks,
the four binary-data gate-level, the two synthesis, the ODE budget, the
zero-time remarks, the zero-time gate-level ODE, both unitary-implementation,
the integrable-path simulation, the single-program Dyson, the gate-level mesh,
the bit-length budget, the gate-level remarks, the signed-time gate-level, the
coherent-selection, the source-quadrature, the binary coherent-selection, the
measured unitary lower-bound, the general-access Dyson, the time-dependent
lower-bound extensions, the released ODE solver lower-bound, the computed
source-node, the selective-synthesis, the Hoeffding-schedule, the
manuscript-schedule, the optimal-precision, the signed-factor, the
native-factor, the large-sparsity core, the optimal simulation, the two-norm
simulation, the optimal lower-bound, the gate-level optimal-precision, the
general-source ODE, the mixed-output ODE, the binary-data optimal-precision, the
general-source extensions, the represented-sample ODE, the source-accuracy ODE, the
clean-work ODE, the general-size sparse access, the general-decoder, the general-size ODE
gate-solver, the decoder ODE gate-solver, the mesh-certificate ODE, the manuscript-conformance
and the ODE
lower-bound extensions audits cover every
theorem of
their libraries (except
one private helper theorem of the linear-system library); the ODE lower-bound
audit also covers the proof fields of its model structures, and the ODE
lower-bound extensions, adaptive ODE lower-bound, unitary-implementation
extensions, time-dependent Hamiltonian lower-bound, constant-coefficient ODE
lower-bound, physical-oracle ODE lower-bound, single-program Dyson,
general-access Dyson, deferred-measurement lower-bound, time-dependent
lower-bound extensions, released ODE solver lower-bound, optimal-precision,
signed-factor and optimal lower-bound audits the proof fields of their
structures.

The supplied build record for the proof sources reports a successful complete
default build (5229 jobs, exit code 0, no warnings), including
`qls_cor_separate` and `qls_cor_separate_writer`, followed by a successful
no-change build. The build was incremental: Lake reused compiled dependencies
and modules whose sources and dependencies were unchanged. The record
identifies the source archive by SHA-256
`af0ec48c2b2da58bc2767f603e7953adb6742954fd169090cb279c2c97c68c9e`
and reports that its extracted contents match the built tree.

The present package preserves all Lean commands, declarations, proofs and
axiom guards from that compiled source; subsequent Lean-file edits affect
comments only. Its source hashes have been updated and the packaging checks
pass. This is the supplied compilation evidence, not a new compiler run or a
GitHub CI result for the documentation revision. The published commit should
also pass the repository's CI workflow.

[GitHub Actions](../.github/workflows/lean.yml) runs the Lean build and a separate
packaging check for source hashes, dependency pins, audit coverage and version
consistency. The latter uses `python3 scripts/check_release.py`; **Python is
not required for `lake build`**. Its current-release reference data is in
`scripts/release_manifest.json`. This check does not verify mathematical proofs.

## Model and trusted base

[`NativeSparseBlockEncoding.Data`](../SparseHamiltonian/NativeSparseBlockEncoding.lean)
specifies exact finite-word sparse data, padded injective row/column locators
and their full unitary extensions. Slots embed in the matrix index register;
the decoder is bounded on every word. Public instance-independent gates are
free. Controlled matrix queries are constructed from the primitive interfaces.
[`MultiOracleCircuit.Program`](../SparseHamiltonian/MultiOracleCircuit.lean)
defines circuit semantics; `Program.count` and `Program.cost` count queries.

The ODE model additionally supplies exact source norms and state-preparation
circuits, their inverses, and controls on known initial/forcing branch labels
and the source-sector flag. These calls are counted.
`ODEPrimitiveSourceJoin.TrialCertificate` is the proved output specification,
not an assumed correctness certificate. The program is uniform over unknown
inputs in a public promise family, giving the usual worst-case interpretation.

The linear-system model uses the same sparse data and a supplied
state-preparation circuit `U_b`, called in a form controlled by a workspace
bit; forward and inverse calls are counted. For Theorem `qls:thm:main`, the
algorithm is a finite tree of
fresh measured runs with classical decisions (`SparseLinearSystems.Protocol`),
whose leaves are bounded fresh-trial preparations from the ODE library.
Success probability, conditional output and worst-case cost are defined by
this transcript semantics. The Chebyshev linear-system library uses the same
model, physical oracle family, cost weights and transcript semantics; the
finite-gate linear-system library also lets each fixed gate of a run be
replaced by any query-free program, with operator-norm errors (`GateApprox`).

Corollary `qls:cor:separate` uses the same primitive query labels and weights,
with a fixed-length repetition protocol (`ODERepeatProtocol.Protocol`) over
its own register layout. Its separate query bounds and output guarantees are
conditional on `SeparateSolver` and the supplied factor-two solution-norm
estimate. The writer form preserves the success probability and conditional
output, with at most twice the matrix queries and the same preparation
queries. The [separate-query coverage](#separate-matrix-and-preparation-query-bounds)
above specifies the external interface and all remaining restrictions.

The gate-level model (`GateEfficientHamiltonian/Circuit/Instr.lean`) has qubit
wires carrying an arbitrary Hilbert-space payload. Its instructions are
controlled one-qubit unitaries with at most three controls, and calls of the
supplied unitaries `U_J` and `D` (or their adjoints) on the ancilla wires and
the payload, controlled by one wire; every instruction is counted.
In the time-dependent gate-level model
(`GateEfficientTimeDependent/SlotSim.lean`) a private call is slot-selected:
it applies the supplied `D_k` on every configuration whose slot wires carry
the slot `k`, as one counted call.

The time-dependent model (`TimeDependentHamiltonian/Native/TimeIndexed.lean`)
indexes the native sparse data by the unknown instance and the sampled time.
Each query is one coherent sampled-time primitive, block diagonal in the time
register, and inverse calls are counted. The intended path enters only
through the hypotheses of the theorem and the propagator equation
(`TimeDependentHamiltonian/Continuous/Propagator.lean`).

The time-dependent ODE model (`TimeDependentODE/Native/Source.lean`) uses the
same time-indexed sparse data for the generator samples and the released source
model, except that the forcing interface applies the supplied preparation of
sample `r` on every forcing label `r` as one counted call. The continuous paths
and the solution enter only through the hypotheses of the theorem and the
equation `x' = -G(u) x + b(u)` (`TimeDependentODE/Continuous/Solution.lean`).

The gate-level ODE model (`GateEfficientODE/Model/Instr.lean`) extends the
gate-level model by solver wires, a private Cayley call that applies the
supplied operation `D z` of the joint label `z` carried by the solver wires
(one counted call), controlled calls of the supplied source interfaces and
their inverses, and the public reflection about the seed vector; every
instruction is counted. The instance enters only through the supplied
unitaries and the hypotheses of the theorem. Its time-dependent semantics
(`GateEfficientODE/Time/Model.lean`) keeps the instruction syntax and reads a
private call as `D z r` for the joint label `z` and the slot `r` carried by the
simulator's slot wires, a loading call as the supplied `J s` of the source
label `s`, and a weight-preparation call as the supplied unitary `Wp` on the
source-label wires; each is one counted call.

The general ODE model (`GeneralODE/Theorem.lean`, `physicalOracle`) uses the
released native sparse data and source interfaces. Its oracles are the native
queries on one of `K` copies of the block-encoding register and the two source
interfaces, controlled on the history slot register, each acting on the
workspace of the released native control with all other registers as
spectators; the physical calls are uncontrolled. The block-input
linear-system solver enters only through the hypothesis `BlockSolver f q₀`
(`GeneralODE/Solver/Interface.lean`), whose circuits call the block encoding
and the preparation on masked copies of the oracle register; every call is
counted.

The linear-system lower bound (`LinearSystemLowerBound/Hard/Native.lean`)
uses the protocols of the linear-system endpoint over any workspace and any
oracle family whose labels are admissible (`Native.Admissible`). A native
call identifies the workspace, by a fixed isometry, with a direct sum of
copies of the native query space and applies on each copy the identity, one
native query (row location, column location or value) or its inverse; it is
counted with weight at least one. An input-independent unitary may have any
weight. The data are any `NativeSparseBlockEncoding.Data` with the hard
matrices, input-independent location oracles and a value table that encodes
the entries; `LinearSystemLowerBound.exists_access` constructs such data. A
fixed isometry identifies the output space with the output register and a
finite garbage register, and the output state is the partial trace over the
garbage register (`LinearSystemLowerBound/Weight/PartialTrace.lean`); the
`*_readout` forms read the output into these registers through any fixed
linear map of norm at most one (`LinearSystemLowerBound/Readout.lean`).

The Hamiltonian lower bound (`SparseLowerBounds/Hamiltonian/Theorem.lean`)
uses non-adaptive `MultiOracleCircuit.Program`s over the released native
primitives of the hard data (`NativeSparseBlockEncoding.oracles`), over these
primitives acting on every copy of an untouched spectator register
(`specOracles`), or over the released simulator's oracle family
(`SparseLowerBounds/Hamiltonian/ReleaseBridge.lean`). Accuracy is
`SparseLowerBounds.Readout.Accurate`: for every self-adjoint `M` with
`‖M‖ ≤ 1`, the expectation of `M ⊗ 1` in the output read through a fixed
isometry into system and garbage registers is within `2ε` of its expectation
in the target state; the endpoint and release forms assume instead the
released operator-norm endpoint error, which implies it. Value queries,
inverses included, are counted (`p.labelCount .value`).

The adaptive Hamiltonian lower bound
(`AdaptiveHamiltonianLowerBound/Theorem.lean`) uses the protocols of the
linear-system endpoint, with a finite-dimensional output space, and labels
admissible for the released hard data
(`AdaptiveHamiltonianLowerBound.Access.Admissible`, the linear-system
library's notion stated for any input type, since the precision family has
Boolean inputs); a native call identifies the workspace, by a fixed isometry,
with a direct sum of copies of the native query space. Accuracy is `AdaptiveHamiltonianLowerBound.DensityAccurate`, the
observable form above for the conditional output density, together with
success probability at least `2/3`; the count is the worst-case weighted
number of calls over all transcripts (`T.worstCost w`).

The ODE lower bound (`SparseLowerBounds/ODE/Model.lean`) uses non-adaptive
`MultiOracleCircuit.Program`s over the released coherent sampled-time oracle
(`TimeDependentODE.labelOracle` of the native primitives of stage-indexed data
`NativeSparseBlockEncoding.Data (X × Fin K)`), with an untouched branch
register. A solution must satisfy the released `TimeDependentODE.SolvesODE`
with the constant generator and source of each stage on its closed interval,
and the generators must be `TimeDependentODE.Accretive`. Accuracy is
`SparseLowerBounds.Readout.HeraldedAccurate` (the observable form above,
conditional on a herald projection, multiplied through by the success
probability) for every solution; value queries, inverses included, are counted
(`labelCount .value`), and the bounds also hold for the total count. The
lower-bound remarks use the models of the released lower-bound libraries, the
ODE lower-bound extensions use this model and, for the released ODE solver, its
retry protocols (`ODERepeatProtocol.Protocol`) over the same sampled-time access
or the solver's physical oracle, with worst-case counts over all transcripts
(the Dyson solver of `odel:lem:dyson` uses the release's physical-oracle builder
with the masked coherent sampled-time native access), and
the zero-time general ODE library uses the physical oracle model of the general
ODE library.

The Chebyshev filter library (`ChebyshevFilter/Statements.lean`) states the
filter for any unitary `W` on a finite-dimensional Hilbert space
(`UnitaryFilter.Unitary`), with `W^{-k} = (W†)^k`. Its LCU circuit acts on a
coefficient register `ℂ^{2d+1} ⊗ V`; the seed is the isometry
`v ↦ ∑_j √p_{j-d} |j⟩ ⊗ v`, and the success block of a circuit `U` is
`seed† U seed`. For Lemma `qls:lem:signedwalk` the walk is `R V† C V` with
input-independent unitaries `R`, `C` and a `MultiOracleCircuit.Program` `V`; the
signed steps are programs over the same named oracles acting on the payload,
with the direction register as a spectator, and every call is counted
(`Program.cost`).

The time-dependent extensions library (`TimeDependentExtensions/Statements.lean`)
uses the time-indexed sparse data and source interfaces of the released
time-dependent libraries, with one sample and one forcing label per mesh
interval; a query is one coherent sampled-time primitive, counted once with the
sample in superposition, and inverse calls are counted. The mesh enters only
the clean encoding, which writes the sample of each slot into the time
register. For block encodings the primitive is the controlled time-indexed
oracle `|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v` for supplied Hermitian unitaries `O_r`,
and every call, inverse calls included, is counted. Paths, propagators and
solutions enter only through the hypotheses of the theorems: one piece per mesh
interval, and propagators (`SolvesOn`) and solutions (`SolvesODE`) with a
derivative at every point of each closed interval.

The native gate-level model (`GateEfficientNative/Model/Instr.lean`) has qubit
wires with a Hilbert-space payload. Its instructions are one-qubit unitaries
with at most three controls and calls of primitive oracles (or their
inverses) placed on chosen wires; both are counted. The released registers
with a qubit system are flattened into qubit wires, and errors are measured
on clean work wires (`ApproxOn`, `GateEfficientNative/Model/Approx.lean`). The
instance enters through the primitive oracles, the supplied private
operations, related to the public compute circuit by the hypothesis
`NativeOK`, the supplied source operations, approximated by the source
circuits, and the hypotheses of the theorems. In the binary-data gate-level
library (`GateEfficientBinary/Sparse/Oracles.lean`, `prims`) the primitive
oracles are built from `NativeSparseBlockEncoding.Data` with two's complement
entry words: the full unitary location oracles act on qubit index registers in
the computational basis and the value oracle XORs the stored words into value
qubits (as in the released data model, the column oracle maps `|j, slot k⟩` to
`|colloc j k, j⟩`); the Hamiltonian enters only through these oracles, the
decoder hypothesis and the hypotheses of the theorems. In the time-dependent
binary-data library (`GateEfficientBinaryTime/Oracles.lean`, `primsT`) the
data are indexed by the input and the time slot, and each primitive oracle is
the coherent sampled-time oracle `∑_w |w⟩⟨w| ⊗ O_j(x, w)`: it reads the
circuit's `m` slot qubits and applies the binary primitive oracle of the
sample named by the slot word, as one counted call; the path enters only
through the hypotheses of the theorems and the propagator equation. The
time-dependent binary-data ODE library (`GateEfficientBinaryODETime`) reads the
generator samples on the `2^m` slots of the native solver's uniform mesh
through the same oracles; the generator path, the forcing and the solution
enter through the hypotheses `PubT.Rest`.
The synthesis library (`GateEfficientSynthesis/Hypothesis.lean`) uses the
native gate-level model: a gate set is a set of gate kinds (control values and
a one-qubit matrix), whose gates may be placed on any distinct wires, and the
synthesis results enter only through the hypothesis `Synthesis` (or
`OneQubitSynthesis` and `ControlDecomposition`), an approximation on clean
ancilla wires in the full-output convention for the payload `ℂ`. The
synthesised-trials library uses the same model with an adjoint-closed gate set
that contains the four kinds of the exact zero tests (`AdjClosed`,
`zeroTestKinds`).

The unitary-precision library uses the entry model of the unitary theorem
(`UnitaryEntryData.Data`: an entry table with a fixed bounded decoder whose
represented matrix is unitary; the only unknown primitive is one call of the
table with spectators, and inverse calls are counted) and, for inexact
entries, the same model without the unitarity promise
(`UnitaryPrecision.Table`); the intended unitary enters only through the
hypotheses and the error bound. The zero-time remarks library uses the models
of the released endpoints that it extends.

The adaptive ODE lower-bound library (`AdaptiveODELowerBound/Model/Solver.lean`)
uses the protocols of the linear-system endpoint over the sampled-time access of
the ODE lower bound and over its call forms (each label as a call, its inverse,
its controlled form through the package's identity mask, and the controlled
inverse), with an isometric readout and the observable accuracy
`DensityAccurate`; the count is the worst-case number of value calls over all
transcripts. The unitary-implementation extensions library uses the entry model
of the unitary theorem with the target unitary in the data
(`ApproxData.Data`), which enters only the hypotheses and the error bound; its
lower bounds quantify over all `OracleCircuit.Program`s over the entry oracle and
all isometric encodings. In the integrable-path library the path and its
propagators enter only through the hypotheses of the theorems. The
deferred-measurement lower-bound library uses its own algorithm model
(`DeferredMeasurementLowerBounds/Model/Measured.lean`: oracle calls and
input-independent instruments with finitely many outcomes on one persistent
workspace, with classical continuations and a heralded output) and the access
classes and accuracy notions of the lower bounds that it lifts; the adaptive
unitary lower-bound library uses the protocols of the linear-system endpoint
over labels implemented by the entry oracle, and their call forms, with the
observable accuracy `DensityAccurate`.

The zero-time gate-level ODE library uses the native and exact-gate models of
the released gate-level ODE endpoints; the supplied source-preparation circuits
(for time-dependent coefficients, the loading and weight-preparation circuits)
enter through hypotheses on their accuracy, as in the released theorems. The
time-dependent Hamiltonian lower-bound library uses the programs and isometric
encodings of the Hamiltonian lower bound over the released oracle families of
the time-dependent simulators (any schedule), and the protocols of the adaptive
Hamiltonian lower bound over the coherent sampled-time access (the released
`TimeDependentODE.labelOracle` of the samples, with an untouched branch
register), its call forms or those families, all on constant data
`constData D M`; accuracy is the error criterion of the released theorems on
the constant path, and the count is the number of value calls (for protocols,
the worst case over all transcripts). The time-dependent lower-bound extensions
library uses the same programs, protocols and constant data over the released
block-encoding and selection families and the call forms of the released
families, with the error criteria of the released and integrable-path theorems;
its gate-level forms use the package's slot-selected circuits with the private
operation as the only instance-dependent part.

The constant-coefficient and physical-oracle ODE lower-bound libraries use the
protocols of the adaptive ODE lower-bound library over the physical oracles of
the released ODE solvers (with inverse calls) and over their call forms, with
public source interfaces; source calls weigh `0`. The released ODE solver
lower-bound library uses the measured solvers of the deferred-measurement
lower-bound library over the same oracles and call forms, with the same counts.
The single-program Dyson
library uses the single-program solver class `SparseLowerBounds.ODE.Solver` of
the ODE lower bounds (one program over the class's access, an
input-independent seed, herald projection and isometric readout).

The gate-level mesh library uses the models of the released gate-level
time-dependent endpoints. On a mesh, the slot-selected private call of slot `k`
applies the supplied operation of the mesh interval containing `kT/2^m`, and
binary mesh data are presented on the uniform clock
(`GateEfficientMesh/BinaryMesh.lean`, `clockData`): at slot word `w` each
primitive oracle is the binary primitive oracle of the sample of the mesh
interval of `w`, as one counted call; computing the slot-to-sample map is not
counted. Paths, propagators and solutions enter only through the hypotheses of
the theorems. The bit-length budget library uses the binary-data models; the
bit lengths of the public parameters (`HasBits`,
`GateEfficientBitBudget/Bits.lean`) are hypotheses on the real parameters of
the released statements. The gate-level remarks library uses the models of the
released gate-level endpoints that it extends; its zero-case budgets run the
direct source assembly of the zero-time gate-level ODE library on that library's
native register without simulator, LCHS, private-operation and arithmetic wires
(`GateRemarks.ODE.MinW`), and its other forms on the released registers.

The lower bounds of `OptimalLowerBounds` (`OptimalLowerBounds/Statements.lean`)
use the program models of the Hamiltonian lower bound, over any oracle family
whose labels have Boolean access certificates (`PhaseAccess`, two Boolean
queries per value call), the common form `NativeSignedFactor.Simulates` of the
upper bounds (one program over `CoherentQuerySchedule.oracle (physOracle D)` on
a known isometric input, at most `q` calls counting adjoints, full-output error
`ε`), and the adaptive protocols of the linear-system endpoint and the measured
algorithms of `DeferredMeasurementLowerBounds.Model.Measured` over labels
admissible for the hard or enlarged data, with the worst-case weighted number of
calls over all transcripts (value calls with the weight `valueWeight`); a native
call identifies the workspace, by a fixed isometry, with a finite direct sum of
copies of the native query space. For an enlarged family the accuracy of
programs and of adaptive and measured algorithms is the observable form of
trace distance for `e^{-itH_X}(ψ_in ⊗ u_m)` on the enlarged system; the common
form assumes the full-output error of `Simulates`, which implies it.

The gate-level optimal-precision library (`GateOptimalPrecision/Statements.lean`)
uses the gate-level model and the native gate-level model. The private
operations of its three regimes enter through interfaces on the gate register
(`BoundedIface`, `SignedIface`, `ClippedIface`: a supplied boundary `U_J` and a
supplied private operation or factor `U_B` with the representation and factor
identities of the regime, each required only in its regime), and in the native
form through the native identities `NativeOK` and `FactorNativeOK` (the
supplied compute circuit, the decoded edge rotation or local factor `U(c)` and
the uncompute act as the private operation or `U_B` on clean scratch) and the
scalar accuracies `ArithOK` and `FactorArithOK` of the reversible arithmetic;
the controlled locator uses the native model with one primitive locator on
`w`-bit words and only its prescribed action on one known word.

The binary-data optimal-precision library (`GateOptimalBinary/Statements.lean`)
uses the binary sparse oracles of the binary-data gate-level library (row and
column location oracles on `k`-bit index words and a value oracle writing two
`b`-bit two's complement components, with the slots enumerated by the low index
words) as the primitives of the native model. Its hypotheses are those of the
data and of Theorem `gate:thm:main`, and the scalar arithmetic of the signed and
clipped regimes (`FactorWordArith`, `ClipFactorArith`, `ClipAngleArith`:
reversible circuits of controlled NOT gates with at most three controls writing
the angle and phase words of the decoded scalars to the stated accuracies), each
required only in its own regime and met at every accuracy by the reversible
lookup tables of `GateOptimalBinary/Tables.lean`; over a finite gate set, also
the synthesis hypothesis `SparseHamiltonian.GateSynth.Synthesis` (single-qubit
synthesis and the decomposition of controlled gates, `Synthesis.of_parts`).

The general-source ODE library (`GeneralSourceODE/Statements.lean`) uses the
coherent sampled-time native access of the time-dependent ODE solver on a
uniform matrix mesh, with three counted source labels `P_w`, `U_load` and
`P_w†` (each with its enable control) in place of the released source
interfaces; the supplied preparations are exact unitaries on the label and data
registers, the coefficient phases are a public gate, and every instance carries
its generator path (accretive and `β_G`-Lipschitz, sample errors `δ_G`), a
continuous forcing, a solution, the propagator family `U` of the homogeneous
equation and the certified propagated quadrature. The mixed-output ODE library
(`MixedOutputODE/Statements.lean`) uses the access model and instance
hypotheses of the general ODE library; its solver hypothesis `MixedBlockSolver`
returns a decoded pure state on the solution and work registers, and its
accuracy is the trace distance of the reduced state on the solution register
after the work register is discarded (`ptrace`).

The general-source extensions library (`GeneralSourceExtensions/Statements.lean`)
uses the access model of the general-source ODE library and, on a mesh, the
coherent sampled-time native access on `N` uniform clock slots with one
represented sample per mesh interval (`TimeDependentExtensions.MeshSelect`).
For approximate preparations, the supplied `P_w` and `U_load` are arbitrary
unitary families, and every instance carries exact unitary preparations within
`δ` of them in operator norm, which the algorithm does not receive; on a mesh,
every instance carries its generator and forcing pieces, the node values
`b_i`, the mesh propagator (`IsMeshPropagator`) and the integrated
certificates.

The represented-sample ODE library (`RepresentedSampleODE/Statements.lean`) uses the access
models of the general-source extensions library on a mesh and of the time-dependent gate-level
solver from binary data; its instances carry negativity bounds of the represented samples (on a
mesh, derived from the true path by `pathNegativity`; on the uniform mesh, `δ_G`), and on a mesh the
mild solution (`MildSolution`) with the propagator of the generator pieces
(`Mesh.IsMeshPropagator`).

The source-accuracy ODE library (`SourceAccuracyODE/Statements.lean`) uses the access models of
the native gate-level ODE solvers it certifies: constant coefficients from binary data, and
time-dependent coefficients from time-indexed binary data with represented samples of any sign.

The clean-work ODE library (`CleanWorkODE/Statements.lean`) uses the mesh access model of
`RepresentedSampleODE`, with the supplied `P_w` and `U_load` acting on a temporary work register
adjoined to the source register of the primitive workspace.

The general-size sparse access library (`GeneralSparseAccess/Statements.lean`) uses the native
model of `GateEfficientNative` with the supplied row, column and value oracles of an `N × N`
matrix on `k`-bit index words (`QData.prims`: the locators unitary on the full edge register and
prescribed on the valid list inputs only, the value oracle XOR-ing a stored word), and the binary
sparse oracles of `GateEfficientBinary` for the padded data.

The general-decoder library (`GeneralDecoder/Statements.lean`) uses the native model of
`GateEfficientNative` with the binary sparse oracles of `GateEfficientBinary` and the native data
of `GateOptimalPrecision`, for sparse data with any public decoder
(`NativeSparseBlockEncoding.Data.decode`, which may depend on the edge), and the supplied oracles
of `GeneralSparseAccess` for the padded data with a validity decoder.

The general-size ODE gate-solver library (`GeneralSparseODE/Statements.lean`) uses the native
model of `GateEfficientNative` with the supplied oracles of `GeneralSparseAccess` (for
time-dependent coefficients selected coherently by the slot wires, `GateBinary.slotPrim`), and the
binary and time-indexed binary sparse oracles of `GateEfficientBinary` and `GateEfficientBinaryTime`
for the padded data.

The decoder ODE gate-solver library (`GeneralDecoderODE/Statements.lean`) uses the native model of
`GateEfficientNative` with the supplied oracles of `GeneralSparseAccess` for sparse access with a
decoder that has an exact binary entry decoding, the oracles of its decoded data (`QData.decData`)
implemented from them through the reversible decoding circuit, and the solvers of
`GeneralSparseODE` for the decoded data.

The mesh-certificate ODE library (`MeshCertificateODE/Statements.lean`) uses the models of the
time-dependent gate solvers it certifies (`GateEfficientODE`, `GateEfficientBinaryODETime`,
`GeneralSparseODE`, `GeneralDecoderODE`, and the finite-gate-set solver of
`GateEfficientSelective`), with the generator pieces, their propagator and the solution on the
system register, or on the index register of sparse access of general size.

The manuscript-conformance library (`ManuscriptConformance/Statements.lean`) uses the access
models of the libraries it restates. Its gate-level statements use the native gate model of
`GateEfficientNative` (one-qubit gates with at most three controls, or the gates of a finite gate
set), and its named hypotheses `formal_…`, `ext_…` and `comp_…` are listed in its statement guide.

The logical trusted base is Lean's kernel and the three foundational axioms
listed above. The mathematical assumptions are explicit in the Lean statements.
