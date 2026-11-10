import UnitaryImplementationExtensions.LowerBound

set_option autoImplicit false

/-!
# Black-box unitary implementation in full: paper-to-Lean entry point

Corollary `hs:cor:unitary` of the manuscript is formalised in
`SparseHamiltonian.UnitaryImplementation` for exact entries at error `1/4`, and in
`UnitaryImplementationPrecision` (namespace `SparseHamiltonian.UnitaryPrecision`) at every precision
with exact and inexact entries. This library proves the `Ω(√N)` half of the last sentence, "the
constant-error worst-case complexity is `Θ(√N)`", for unitary query circuits over the entry oracle,
and gives a second, independent proof of the upper bounds at every precision and with inexact
entries (inexact entries with entrywise error at most `ε/(πN)`, every precision `0 < ε ≤ 1/2`;
larger two-term constants, target family part of the data). The oracle, encoding and count are those
of `UnitaryPrecision` (equal by `rfl` for equal tables), so the lower bounds also apply to its
circuits. All declarations below are in the namespace `UnitaryImplementationExtensions`.

* Inexact entries (eq. `hs:eq:unitaryerror`, proof of Corollary `hs:cor:unitary`):
  `Inexact.implementation`; with an untouched finite reference, `Inexact.reference_error`; exact
  data as the zero-error case, `Inexact.implementation_ofExact`.
* General precision, exact entries (eq. `hs:eq:unitarybound` without its hybrid term):
  `General.implementation`, `General.reference_error`.
* The lower bound (Corollary `hs:cor:unitary`, reduction sketched in the proof of Corollary
  `hs:cor:unitary`): `LowerBound.entry_count_ge` (programs over the ordinary entry lookup),
  `LowerBound.implementation_count_ge` (programs over the oracle of the upper bound), and the two
  halves together: `LowerBound.theta` (error `1/4`), `LowerBound.theta_of_error` (every fixed
  `0 < ε ≤ 1/2`, exact model) and `LowerBound.theta_inexact` (every fixed `0 < ε ≤ 1/2`, oracle
  model of the inexact circuit).
* Constant-error unstructured search: `Search.count_ge` (overlap form) and
  `Search.search_count_ge` (success-probability form).

**Access model.** `ApproxData.Data X n Z`: the ordinary reversible entry table with a fixed
bounded decoder of `SparseHamiltonian.UnitaryEntryData.Data` (fields `table`, `decode`,
`scale`, `scale_pos`, `decode_bound`), with a unitary `target x` (`target_unitary`) in place of
the unitarity promise on the decoded matrix `represented D x`; exact data is
`ApproxData.ofExact` (`ofExact_represented`). The entry error is a theorem hypothesis,
`‖represented D x i j - target x i j‖ ≤ ε/(π N)`, `N = card n`, exactly `ξ ≤ ε/(πN)`. The
oracle is one ordinary reversible entry query of the table lifted by the released spectator map
(`ApproxOracle.oracle`; on exact data it is `UnitaryEntryOracle.oracle` by `rfl`,
`ApproxOracle.oracle_ofExact`). Location calls are compiled into fixed gates, so only entry
queries, forward or inverse, are counted (`OracleCircuit.Program.count`).

**Guarantees** (`ℓ = log(1/ε)`, `N = card n`).

* `Inexact.implementation`: for `0 < ε ≤ 1/2` and entry error at most `ε/(πN)`, there are
  `γ ∈ (0, 1]` and one oracle program `p` over `Inexact.oracle D γ ε`, fixed before the
  instance, with at most `inexactConstant (√(N ℓ) + ℓ)` queries, such that the clean encoding
  `ι = Inexact.input D γ ε` is isometric and, for every `x`, `p.eval x` is unitary and
  `‖p.eval x ι - ι U_x‖ ≤ ε`, where `U_x` is the operator of the target `D.target x` (not of
  the represented matrix); `inexactConstant = 995328 (π/√log 2 + √(2π) + 2)`.
* `General.implementation`: for exact entries and `0 < ε ≤ 1/2`, the same with
  `exactConstant (√(N ℓ) + ℓ)` queries, `exactConstant = 995328 (π/(2√log 2) + √(π/2) + 1)`.
  At `ε = 1/4` its oracle and encoding are those of the released corollary
  (`General.oracle_quarter`, `General.input_quarter`, by `rfl`).
* `LowerBound.entry_count_ge`, `LowerBound.implementation_count_ge`: for `N ≥ 2` and the search
  family `(U_m)_{jk} = 1[j + k = m mod N]` (`SearchFamily.searchMatrix`, one-bit entries
  `SearchFamily.searchData`), every program that implements every `U_m` on an isometric encoding
  with error `ε₀ ≤ 1` satisfies `(1 - 2 ε₀ √(1 - ε₀²/4)) √(N - 1) ≤ 2 · count`; the factor is
  positive for `0 ≤ ε₀ ≤ 1/2` (`Search.near_factor_pos`).
* `LowerBound.theta`: for `N ≥ 2`, the released circuit has at most `queryConstant · √N` queries
  and error `1/4`, and every program over the same oracle family and every isometric encoding
  with error `1/4` satisfy `√N ≤ 4√2 · count`. `theta_of_error`, `theta_inexact`: at every fixed
  `0 < ε ≤ 1/2`, the upper bounds `exactConstant (√ℓ + ℓ) √N` and
  `inexactConstant (√(N ℓ) + ℓ)`, a positive lower factor and the lower bound in the same oracle
  model.

**Proof map.** Module paths are relative to `UnitaryImplementationExtensions/`.

* `ApproxData`, `ApproxNorm`, `ApproxOracle`: the inexact access model, the Hermitian dilation
  `dilation M = [[0, M], [M†, 0]]` (`dilationMatrix_eq`), its native interface (`toNative`), the
  Schur bound `‖H̃_U - H_U‖ ≤ N ξ` (`dilation_error_le`), `‖H̃_U‖ ≤ 2` once `N ξ ≤ 1`
  (`norm_represented_dilation_le`), and the entry-only reduction (`compile`, `compile_eval`,
  `compile_count_le`).
* `Inexact`: simulation of `H̃_U` with `s = N`, `η = 2`, time `π/2` and error `ε/2`
  (`ImprovedSparseHamiltonian.simulation_spectral_log_one`), Duhamel's bound to `H_U`
  (`simulation_transfer`, `(π/2) N ξ ≤ ε/2`), and the exact identity
  `exp(-i(π/2) H_U) = -i H_U` with the released flag flip and phase correction.
* `General`: the released route with `ImprovedSparseHamiltonian.simulation_log_one` at general
  precision.
* `PhaseBridge`, `LiftPhase`: the one-bit reversible lookup is a Boolean phase oracle
  (`lookup_eq_phase`), unital star-algebra homomorphisms map phase oracles to phase oracles
  (`phase_map`), and the released entry oracle of one-bit data is a phase oracle
  (`oracle_eq_phase`).
* `Search`, `SearchFamily`: the constant-error search bound from the package's positive-weight
  adversary `SparseLowerBounds.PositiveAdversary.count_ge` (`schurCert`, `count_ge`,
  `norm_inner_le_of_near`), and the search family (`searchMatrix_unitary`,
  `searchMatrix_single_zero`: `U_m |0⟩ = |m⟩`, `count_ge_of_outputs`, `count_ge_of_phase`).
* `LowerBound`: the lower bounds and the `Θ(√N)` statements.

Every theorem of the library, and every `Prop`-valued field of `ApproxData.Data`, is
axiom-audited in `UnitaryImplementationExtensions/Audit.lean`.

**Formalisation choices.**

* General `ε`: the bound proved is `C (√(N ℓ) + ℓ)` with explicit constants, from
  `simulation_log_one` and `simulation_spectral_log_one`; the manuscript's additive term
  `ℓ/log(e + ℓ/N)` comes from `hs:cor:hybrid`, which the package does not formalise; the bound
  with that term is `OptimalSparseSimulation.unitary_bound`, from Corollary
  `hs:cor:unitary-optimal`.
* The released corollary is the `ε = 1/4` instance of the general model (`oracle_quarter`,
  `input_quarter`); its constant `queryConstant` is kept, so it is not restated.
  `Inexact.implementation_ofExact` is the zero-error case of the inexact theorem at `η = 2` and
  precision `ε/2`; the sharper exact-entry form is `General.implementation`.
* The upper bounds need only `[Nonempty n]`, weaker than the manuscript's `N ≥ 2`; the lower
  bound needs `N ≥ 2`.
* The inexact native interface (`ApproxData.dilationTable`, `dilationDecode`, `toNative` and
  `ApproxOracle.plainTable`, `flatEntry`, `letter`, `compile`) restates the released one for a
  represented matrix that need not be unitary, since the released declarations are typed on
  exact unitary data; for exact data it agrees with the released one (`dilationTable_ofExact`,
  `dilationDecode_ofExact`, `toNative_ofExact_matrix`), and the oracle is the released one.
  `ApproxData.targetData` packages the target as exact entry data only so that the released
  dilation identities apply to it; it is never used as an oracle.
* The target family is part of the data and the program is quantified after `D`; it is built
  from `table`, `decode`, `scale` and the public parameters only (the oracle and
  `Inexact.input` do not depend on `target`, by `rfl`), so the statement is uniform over the
  instances of the promise family `X`. The query-model reading, one circuit that does not know
  the intended unitary, is the instance in which `X` is the set of admissible pairs (instance,
  unitary within `ε/(πN)`); it is stated directly as
  `SparseHamiltonian.UnitaryPrecision.implementation_inexact_uniform`.
* The hard family is the manuscript's `U_m` with one-bit entries in `ZMod 2` and decoder
  `z ↦ [z = 1]`. Each entry query is exactly one search query, since the one-bit XOR lookup
  equals the phase oracle (proof of Corollary `hs:cor:unitary`).
* The lower bound is stated for every program over the ordinary entry lookup (with an
  arbitrary untouched payload and an arbitrary isometric encoding), for every program over the
  released oracle `UnitaryEntryOracle.oracle (SearchFamily.searchData N) γ η t ε` for all
  parameters, and in Boolean phase form for any projection family whose positions are marked by
  one equality test. The class is `OracleCircuit.Program`, the class of the upper bound:
  non-adaptive unitary query circuits (fixed unitary gates, no intermediate measurement or
  classical control) with forward and inverse entry queries on the oracle's workspace and one
  isometric encoding for input and output.
* The transport to the released oracle is an exact operator identity (`PhaseBridge.phase_map`),
  the exact-identity form of `SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate` (in
  `SparseLowerBounds/Helpers/HsRelease/PhaseAccess.lean`, not imported here), not the
  cost-bounded certificates `SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess`, which are
  built for the release simulator's labels.
* Constant-error search is derived from the positive-weight adversary rather than from Lemma
  `hsl:lem:search`, which is a search-parity correlation bound. The manuscript states the lower
  half with a reduction sketch; it is proved here.
* Unit outputs within `ε₀ ≤ 1` of orthonormal states have overlap at most
  `2 ε₀ √(1 - ε₀²/4)` (`Search.norm_inner_le_of_near`); at `ε₀ = 1/4` the bound is
  `√N ≤ 4√2 · count`.

**Not formalised.**

* Corollary `hs:cor:hybrid`, the manuscript's route to the additive term `ℓ/log(e + ℓ/N)` of eq.
  `hs:eq:unitarybound` (that term is `OptimalSparseSimulation.unitary_bound`, from Corollary
  `hs:cor:unitary-optimal`).
* Lower bounds against adaptive or controlled-call algorithms (classical trees of measured
  runs, heralded success, controlled entry queries).
* A separate lower bound over inexact tables of the hard family (exact tables are admissible
  inexact data, so `theta_inexact` already gives the lower bound in the inexact circuit's oracle
  model).
* The exact range of positivity of the lower-bound factor (it is positive exactly for
  `ε₀ < √(2 - √3)`); only positivity on `0 ≤ ε₀ ≤ 1/2` is proved.
* Gate, workspace and classical circuit-generation costs.

**Provenance.** No result from another paper is used; the manuscript cites the search lower
bound, and it is derived here from the package's positive-weight adversary. The libraries
`SparseHamiltonian`, `SparseLowerBounds` and `GeneralODE` are only imported; no released module
is changed. `SparseHamiltonian/Statements.lean` predates this library and describes Corollary
`hs:cor:unitary` at error `1/4` with exact entries; the Hamiltonian and adaptive Hamiltonian
lower-bound statement guides list the unitary `Ω(√N)` search bound as outside them. Both are
proved here. `UnitaryImplementationPrecision/Statements.lean` lists the lower bound `Ω(√N)` as
not formalised; it is proved here. References to the manuscript use its labels.
-/
