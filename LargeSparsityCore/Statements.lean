import LargeSparsityCore.NativeCore
import LargeSparsityCore.NativeTwoNormCore

set_option autoImplicit false

/-!
# The large-sparsity core (`opt:sec:core`): paper-to-Lean entry point

Appendix A of the manuscript proves Theorem `hs:thm:optimal` in the regime `sτ ≥ Lh` by a joint
clipped representation of `H` and a product filter with exact zeros at two isolated private phases
(Section `opt:sec:core`, Proposition `opt:prop:core`): "the original sparse oracles give a
simulation with error on all output registers at most `ε` and query cost `O(√(sτr))`". This library
proves that bound at the circuit level over the native sparse oracles of the released package, with
the explicit threshold `h ≥ 10⁴` of `opt:eq:core-explicit`. It also proves the clipped-transducer
regime of Theorem `hs:thm:two-norm` (Appendix B, the proof of Theorem `hs:thm:two-norm`), at the
entry scale `μ` with the real moment parameter `σ = sμ²/η²` (`Native.core_simulation_two`). The
combination of the regimes (the proof of Theorem `hs:thm:optimal`, eq. `opt:eq:regime-comparison`),
Theorem `hs:thm:optimal` and Corollary `hs:cor:unitary-optimal` are the library
`OptimalSparseSimulation`; Theorem `hs:thm:two-norm` is the library `TwoNormSimulation`.

No result from another paper is used. The released libraries are unchanged; the native oracle model,
the locator and value programs, the masked-call compilation, the active-layer compiler, the
chronological clock, the signed smoothing and its amplification, and the Cayley discretisation of
`SparseHamiltonian`, and the local factor of `NativeSignedFactor` are reused. References to the
manuscript use its labels. Every theorem of the library is axiom-audited in
`LargeSparsityCore/Audit.lean`.

**Naming convention.** All declarations are in the namespace `LargeSparsityCore`; names below are
relative to it, except the fully qualified names of the released libraries.

## The statement

The sparse data are those of the released package,
`SparseHamiltonian.NativeSparseBlockEncoding.Data X n Z s`: for every instance `x`, a matrix
`H = D.matrix x` on `n`, a row locator and a column locator that are arbitrary unitaries with the
in-place, phase-one promise on the `s` listed slots of every row and column, and an additive value
oracle whose word decodes to the entry by a known decoder. The promise `Native.Promise D η x` is
that every row and every column of `H` has Euclidean norm at most `η`.

The regime `Parameters.Regime s τ ε` (module `Parameters`) is: `s ≥ 1`, `τ ≥ 1`,
`0 < ε ≤ 1/64`, `h ≥ 10⁴` and `L h ≤ s τ`, with `L = log(1/ε)`, `h = log(e + L/τ)` and
`r = L/h` (`hs:eq:optimal-parameters`, `opt:eq:core-regime`, `opt:eq:core-explicit`).

**Theorem** (`Native.core_simulation`). Let `H(x) = D.matrix x` be Hermitian with row and column
Euclidean norms at most `η > 0` for every instance, and let `t` be a time with
`Parameters.Regime s (η|t|) ε`. There is a program over the released native oracle family
(`SparseHamiltonian.NativeCayleyActive.oracle`: the row locator, the column locator and the value
oracle, each on its register with spectator registers), with at most `6972480 √(sτr)` calls counting
adjoints, `τ = η|t|`, unitary for every instance, such that

`‖p.eval x ∘ input - input ∘ e^{-itH(x)}‖ ≤ ε`

for every instance, with the same known isometry `input` (`Native.input`; `input† input = 1` is part
of the conclusion) on input and output. The input, the embedding and every gate are chosen before
the instance; the program is the same for all instances `x` of the family `X`. Negative time uses
the inverse program. The embedding `input` is not a plain `|0⟩` initialisation: it contains the
known coherent smoothing preparation and the clean encoding of the native workspace; by the paper's
convention ("Known changes of input or output encoding can be absorbed into surrounding circuits")
this is the full-output error of the paper. `Native.core_native` is the form for `e^{-i(τ/η)H}` with
at most `324 d` calls, and `Parameters.Regime.degree_le_sqrt` gives `d ≤ 21520 √(sτr)`
(`opt:eq:core-degree`).

## The entry-scale form (Appendix B)

The parameters (`Parameters`) and the abstract core (`Core`) take a real parameter `s ≥ 1`: the
sparsity in the theorem above, and the moment parameter `σ = sμ²/η²` in Appendix B ("The
finite-clock resolvent [eq. `opt:eq:global-resolvent`] and spectral enclosures therefore have
exactly the hypotheses used in Appendix `opt:sec:core`, with `s` replaced analytically by `σ` and
`τ` by `θ`"). With a supplied entry bound `‖H‖_max ≤ μ`, the joint representation is clipped at `μ`
(`twonorm:eq:clip`); its compression is `J†KJ = H/α` with `α = sμ/q`
(`Native.compression_of_entry`), and every moment acquires the factor `η²/μ²`
(`Native.norm_Ppl_input_sq_le_ratio`, `Native.norm_Pmi_input_sq_le_ratio`,
`Native.norm_bulk_input_sq_le_ratio`, `Native.norm_K_input_sq_le_ratio`; module `NativeTwoNorm`),
which is the moment parameter `σ` in place of `s` (`Native.coreData_two`; module
`NativeTwoNormCore`). **Theorem** (`Native.core_simulation_two`): in the regime
`Parameters.Regime σ θ ε` with `θ = η²|t|/μ`, `μ, η > 0` and `sμ² = ση²`, for Hermitian `H(x)` with
row and column Euclidean norms at most `η` and entries of modulus at most `μ`, at most
`6972480 √(σθr_μ)` native calls give full-output error at most `ε` for `e^{-itH}` (`σθ = sμ|t|`),
with the known isometric input `Native.inputS D σ θ ε`; `Native.core_native_two` is the form with
`324 d` calls. With `μ = η` these are the statements above.

## The proof

*Parameters* (module `Parameters`). The choice of `opt:sec:core`: `q_* = √(sτ/r)`,
the even integer `p = 2⌈π q_* + 1⌉`, `2q = cot(π/p)` (so `q_* ≤ q ≤ 2q_*`, `2πq ≤ p ≤ 7q`,
`opt:eq:phase-choice`), `k = ⌈4r⌉`, `m = ⌈32hk⌉` (`opt:eq:filter-orders`), `B₀ = ⌈64q/h⌉`,
`ρ₀ = 8/B₀`, `Q₀ = 2q/h`, `ζ = hτ/(100qk)` (`opt:eq:zeta`), `a = sτ/q`, the degree
`d = m(B₀ - 1) + k(p - 1)` and the mesh `N_s` (`steps`). The regime gives all scalar
inequalities (`Regime.*`), among them the filter estimate `‖f(D_g)‖ ≤ ε/3`
(`Regime.filter_estimate`, `opt:eq:filter-small`: the isolated part is at most `2e^{-hk/2}`, the
bulk part at most `e^{-hk/2}`), the catalyst budget `6aν ≤ d` (`Regime.catalyst_le`,
`opt:eq:degree-catalyst`) and `d ≤ 21520 √(sτr)` (`Regime.degree_le_sqrt`).

*The filter* (modules `ProductFilter`, `Scalars`). The product filter `g_{B₀}^m g_p^k`
(`opt:eq:filter`) has nonnegative palindromic coefficients summing to one, so its signed smoothing
has absolute weight two (`ProductFilter.absolute_mass_two`, `opt:eq:smoothing`); `g_p` vanishes at
the isolated phases `λ_± = e^{±2πi/p}` and is at most `ζp(1 + ζ)^p/2` on the circles
`|z - λ_±| = ζ` (`Scalars.norm_geometricAverage_root_le`; for the product filter
`Scalars.norm_filter_root_le`).

*Contour integrals* (modules `Riesz`, `Clusters`, `FilterBound`). Riesz projections and the
Dunford formula on circles (`Riesz.riesz`, `Riesz.dunford`), the spectral clusters of a
finite-dimensional operator (`Clusters.exists_clusters`), and the bound of the product filter of a
contraction from resolvent bounds on the two isolated circles and the bulk circle `|z - 1| = ρ₀`
(`FilterBound.filter_norm_le`): `‖f(T)‖ ≤ 2ζFM + (2/(B₀ρ₀))^m ρ₀ M_b (1 + 2ζM)`.

*The finite-clock resolvent* (modules `GeneralResolvent`, `CayleyBlocks`, `CoreFilter`). The
resolvent of the actual chronological private block `D_g` of the baseline at a general point
(`GeneralResolvent.exists_global_resolvent`, `opt:eq:global-resolvent`, with the exact identity
`opt:eq:real-transfer`, `GeneralResolvent.re_inner_omega`); the resolvent of a Cayley private
operator from its block structure (`CayleyBlocks.Spectral`, `CayleyBlocks.exists_resolvent_bounds`);
and their combination on the three circles, including invertibility in the whole gap region
(`CoreFilter.filter_bound`).

*Smoothing and amplification* (module `Smoothing`). The amplified coherent smoothing of the first
version for an arbitrary coefficient list: an isometry with full-output error `2δ` when the filter
is at most `δ` on `D_g` (`Smoothing.exists_implementation`), and its query certificate with `6dq`
calls when every synchronized active clock layer costs `q` calls
(`Smoothing.implementation_query_certificate`).

*The abstract core* (module `Core`). Under the block structure and the moment bounds of
`opt:eq:joint-moments` and `opt:eq:isolated-weights` (`Core.CoreData`), the amplified clock has
full-output error at most `ε` for `e^{-i a J†KJ}` (`Core.core_implementation`: `2ε/3` from the
filter, `ε/3` from the Cayley discretisation), and the query form `Core.core_query` aligns the
output preparation with the input preparation by a known sign unitary.

*The joint representation* (modules `NativeLocal`, `NativeOperators`, `NativeMoments`). Clipping
(`opt:eq:clip`): `z/η = c₁ + c₂` with `c₁ = (z/η)/(1 + h|z|/η)` (`Native.cclip` with its
argument `β = h`, `h|c₁| ≤ 1`) and the correction `c₂` (`Native.ccorr`, `|c₂| ≤ h|z|²/η²`); both
have the phase of `z` (`Native.phase_ccorr`).
On the released logical native workspace, one unitary frame
`𝒰(x) = G ∘ V(x) ∘ L(x)` (`Native.U`: the locators, the value oracle and the local gate
`NativeSignedFactor.localOp c₂` of the correction factor) makes every private operator diagonal:
`K = 𝒰† Λ_K 𝒰` with eigenvalues `±2q` on the success labels, `0` on failure and `±2q|c₁|` on the
clipped flag (`Native.Kop`, `opt:eq:joint-lift`); `D = 𝒰† λ(Λ_K) 𝒰` (`Native.Dop`); the isolated
projections `P_±` (`Native.Ppl`, `Native.Pmi`). The block structure holds exactly
(`Native.spectral`), `‖R₁P₀‖ ≤ (1 + 2q/h)/2` (`Native.norm_R1_bulk_le`), and `D(x)` is the
evaluation of a six-call logical program (`Native.logicalProgram_eval`). The known boundary
`J` (`Native.Jin`) carries the flag state `(|0⟩ + |2⟩)/√2`; then `J†KJ = H/α` with `α = sη/q`
(`Native.compression`), `‖P_± J‖² ≤ h/(2s)` (`Native.norm_Ppl_input_sq_le`,
`Native.norm_Pmi_input_sq_le`), `‖K P₀ J‖² ≤ 2q²/s` (`Native.norm_bulk_input_sq_le`) and
`‖KJ‖² ≤ 2q²(1 + h)/s` (`Native.norm_K_input_sq_le`).

*Compilation* (module `NativeCore`). `Native.coreData` verifies `Core.CoreData`; the logical
program is compiled to `18` native calls (`Native.physProgram`) and every active layer to `54`
(`Native.active_implementsOn`), which gives `Native.core_native` and `Native.core_simulation`.

## Scope and differences from the manuscript

* Only query complexity is claimed here; the gate-level implementation (Theorem `gate:thm:main`) is
  the library `GateOptimalPrecision`; here the finite mesh, the known coefficient
  preparations and the local gates are exact known gates of the query model, and no error budget
  is spent on approximating them. The errors are `ε/3` for the filter in place of `ε/8`
  (`opt:eq:filter-small`; `Parameters.Regime.filter_estimate` bounds the right-hand side of
  `CoreFilter.filter_bound`), doubled by the amplification, and `ε/3` for the Cayley
  discretisation.
* The signed smoothing uses the released index set, on which the absolute weight is
  exactly two, in place of `∑|ω_j| = 2 - 2a₀` (`opt:eq:smoothing`); the catalyst budget is
  `6aν ≤ d` (as required by the released smoothing) in place of `d > 5W`
  (`opt:eq:degree-catalyst`).
* The explicit constants are those of `opt:eq:core-explicit` (`h ≥ 10⁴`, `C_order = 4`,
  `C_bulk = 32`), with `Q₀ = 2q/h` (so `ρ₀Q₀ ≤ 1/4`), the bulk average `B₀ = ⌈64q/h⌉` and
  `ρ₀ = 8/B₀` in place of `Q₀ = ⌈max{1, 2q/h}⌉`, `B₀ = 32Q₀` and `ρ₀ = 1/(4Q₀)`; both give
  `B₀ρ₀ = 8`. The phase count is `p = 2⌈πq_* + 1⌉` rather than the least eligible even `p`.
  As in the manuscript, `h ≥ 10⁴` is an asymptotic witness, not a practical threshold: it forces
  `L/τ ≥ e^{10⁴} - e`, so the regime contains only extremely small `ε` and extremely large `s`
  (it is nonempty, for example `τ = 1`, `ε = e^{-e^{10⁴}}`, `s = ⌈Lh⌉`).
* The contour consists of three full circles, `|z - λ_±| = ζ` and `|z - 1| = ρ₀`, with Riesz
  projections splitting off the isolated clusters, in place of the inner and outer arcs of
  `opt:eq:bulk-contour`; on the bulk the average is written as `B₀⁻¹(1 - T^{B₀}) S` with
  `(1 - T) S = P_b`, and contractivity bounds `1 - T^{B₀}`.
* The spectral enclosure is the invertibility of `z - D_g` at every point of the gap region, from
  the small-step condition `v (1 + 2(2/ζ + 4Q₀/3)) ≤ 1/2`; the mesh is
  `N_s = 1 + ⌈max{max(4a, √(3a³/ε)), a(2 + 8/ζ + 6Q₀)}⌉`.
* The joint representation uses one edge register with a three-valued flag: the clipped part on
  flag `2`, the correction factor on flags `0, 1` (the failure value zero), in place of a direct
  sum of the clipped orientation space and the correction factor space. The boundary is the
  public slot preparation with the flag state `(|0⟩ + |2⟩)/√2`, so that `J = (J₀, J_c)/√2` with a
  shared edge register. The correction factor uses the local factor `√|c| V(c)†` of
  `NativeSignedFactor`, and the correction entry is clipped to the unit disk (the identity on
  oracle words), so that every value word gives a unitary.
* The private space is the whole logical native workspace (every value word and flag), on which
  the private operators are defined exactly; the invariant clean subspace of the manuscript is not
  needed.
* The catalyst is `ν = (1 + 2q²(1 + h)/s)/2` (`opt:eq:nu-W`), with endpoint `b = √(ν/2)` and the
  bound `max(‖R₁‖, ν)` of the released clock; `ν ≤ 1` (`Parameters.Regime.second_le_one`).
* The oracle model is that of the released native simulation: every native call acts on its register
  with spectator registers, and masked calls use the released three-query construction (`18` native
  calls for the private Cayley operator, `54` for an active layer).
* The constants `21520`, `324` and `6972480` are explicit and are not optimised.
-/
