import UnitaryImplementationPrecision.Exact
import UnitaryImplementationPrecision.Uniform

set_option autoImplicit false

/-!
# Corollary `hs:cor:unitary` at every precision and with inexact entries: paper-to-Lean entry point

Corollary `hs:cor:unitary` (black-box unitary implementation, Section `hs:sec:unitary`) of the
accompanying paper implements a unitary `U ∈ ℂ^{N×N}`, `N ≥ 2`, from a reversible entry-value
oracle whose entries are exact or have entrywise absolute error at most `ε/(πN)`: a unitary
circuit `A_U` with `‖A_U - U‖ ≤ ε` for `0 < ε ≤ 1/2`, also on inputs entangled with an
untouched reference, using `O(√(Nℓ) + ℓ/log(e + ℓ/N))` entry-oracle queries, `ℓ = log(1/ε)`,
inverse calls included, and no location oracle. The released
`SparseHamiltonian.UnitaryImplementation.implementation` (library `SparseHamiltonian`) proves the
case of exact entries at the constant error `1/4` with `O(√N)` queries; it is unchanged. This
library proves the corollary for every `0 < ε ≤ 1/2`, with exact and with inexact entries,
through the formalised Theorem `hs:thm:main`
(`SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one`), with the additive term `ℓ`
of that theorem in place of `ℓ/log(e + ℓ/N)` (see **The precision term**). Nothing from outside
the paper is used. Unqualified names below are in the namespace
`SparseHamiltonian.UnitaryPrecision`; qualified names such as `UnitaryEntryData.Data` refer to
`SparseHamiltonian.*`.

* Exact entries: `implementation`, `implementation_with_reference`, `implementation_two_term`;
  also `native_implementation` (before the known locators are compiled away) and
  `reference_error`.
* Inexact entries: `implementation_inexact`, `implementation_inexact_uniform`,
  `implementation_inexact_with_reference`, `implementation_inexact_two_term`; also
  `native_implementation_inexact`, `reference_error_inexact` and the Duhamel step
  `duhamel_step`.
* The inexact entry model: `Table`, `Table.ofData`, `Table.dilationMatrix`, `Table.toNative`,
  `Table.oracle`, `Table.compile`, `Table.comap`, the ghost data `exactData`, and the reading
  of a program over another oracle family, `reindex`.
* The precision term: `sqrt_le_absorb`, `three_term_le_two_term`, `three_term_le_root`,
  `two_term_le_hybrid`.

**Access model, exact entries.** As for `UnitaryImplementation.implementation`:
`D : UnitaryEntryData.Data X n Z` is an ordinary reversible entry table `D.table x` with a fixed
decoder `D.decode`, bounded by `D.scale` and independent of the instance `x`, whose decoded
(represented) matrix `D.matrix x` is unitary for every `x`; `N = card n ≥ 1` and the value
alphabet `Z` is a finite additive group. The only unknown primitive is
`oracle D γ ε = UnitaryEntryOracle.oracle D γ 1 (π/2) ε`: one ordinary call of the table on the
simulator workspace `Physical n Z γ ε`, every other register a spectator
(`UnitaryEntryOracle.flatEntry_eq_original`). A program `p : OracleCircuit.Program (oracle D γ ε)`
consists of fixed unitary gates, independent of `x`, and calls of the oracle or its inverse;
`p.count` counts both. The known row and column locators of the dilation are fixed gates: there
is no location oracle. The fixed clean isometry `input D γ ε` encodes both input and output.

**Access model, inexact entries.** `T : Table X n Z` has exactly the fields of
`UnitaryEntryData.Data` except its unitarity promise: an entry table `T.table`, a fixed decoder
`T.decode` bounded by `T.scale`, and the represented matrix `T.matrix x` (the decoded entries,
`Ũ` in the paper), which may be any matrix. `Table.ofData` forgets the promise of released data,
and for it the dilation, the native interface, the physical oracle and the compiler are the
released ones (`Table.ofData_dilationMatrix`, `Table.toNative_ofData`, `Table.flatEntry_ofData`,
`Table.oracle_ofData`, `Table.letter_ofData`, `Table.compile_ofData`, all by `rfl`). The only
unknown primitive is `inexactOracle T γ ε = Table.oracle T γ 2 (π/2) (ε/2)`: one ordinary call
of the table with spectators (`Table.flatEntry_eq_original`); the clean isometry is
`inexactInput T γ ε`. The intended unitary family `U : X → Matrix n n ℂ` is never queried: it
enters only through `hU`, the promise `hEntry` and the target of the error bound. The
construction uses `T` and the public parameters alone; `implementation_inexact_uniform` states
one circuit, built from `T` and `ε`, that is within `ε` of every unitary whose entries are within
`ε/(π N)` of the represented ones.

**Hypotheses and guarantees.** Below `ℓ = log(1/ε)`, `U_x` is the operator of `D.matrix x`
(exact entries) or of `U x` (inexact entries), and `SparseStateOverlap.matrixOperator` is the
operator of a matrix on `EuclideanSpace ℂ n`.

* `implementation D ε hε hεHalf`: for `0 < ε ≤ 1/2` there are `0 < γ ≤ 1` and one program `p`
  over `oracle D γ ε`, chosen before the instance, with
  `p.count ≤ 497664 π (√N + √(N ℓ) + ℓ)` entry queries, `(input D γ ε)† ∘ input D γ ε = 1`, and
  for every instance `x`: `p.eval x` is unitary on the whole workspace and
  `‖p.eval x ∘ input D γ ε - input D γ ε ∘ U_x‖ ≤ ε`.
* `implementation_with_reference`: the same count, isometry and unitarity, and for the given
  finite reference `R` and every `ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n)` with `‖ψ‖ = 1`
  (arbitrarily entangled), the error of the circuit lifted by `FiniteReferenceLift.lift` (the
  reference untouched) is at most `ε`; the reference does not enter the count.
  `reference_error`: for any circuit with the operator-norm bound, the error is at most `ε ‖ψ‖`
  for every finite `R` and every `ψ`, so the circuit of `implementation` serves every reference.
* `implementation_two_term`: the guarantees of `implementation` with
  `p.count ≤ 497664 π (1 + (log 2)^{-1/2}) (√(N ℓ) + ℓ)`.
* `implementation_inexact T U hU ε hε hεHalf hEntry`: for a family `U` of unitary matrices
  (`hU`), `0 < ε ≤ 1/2`, and `‖T.matrix x i j - U x i j‖ ≤ ε/(π N)` for all `x`, `i`, `j`
  (`hEntry`), there are `0 < γ ≤ 1` and one program `p` over `inexactOracle T γ ε` with
  `p.count ≤ 995328 π (√N + √(N ℓ) + ℓ)` table queries, `inexactInput T γ ε` isometric, and for
  every `x`: `p.eval x` unitary and, with `E = inexactInput T γ ε`,
  `‖p.eval x ∘ E - E ∘ U_x‖ ≤ ε` against the intended unitary `U x` (not the represented
  matrix).
* `implementation_inexact_uniform T ε hε hεHalf`: for `0 < ε ≤ 1/2` there are `0 < γ ≤ 1` and one
  program `p` over `inexactOracle T γ ε`, built from `T` and `ε` alone, with the count of
  `implementation_inexact` and `inexactInput T γ ε` isometric, such that for every instance `x`,
  `p.eval x` is unitary and, for every matrix `V` whose operator is unitary with
  `‖T.matrix x i j - V i j‖ ≤ ε/(π N)` for all `i`, `j`, `‖p.eval x ∘ E - E ∘ V‖ ≤ ε` (with `E`
  as above and `V` read as its operator). This is the query-model reading: the circuit does not
  know the intended unitary.
* `implementation_inexact_with_reference`, `reference_error_inexact`: the reference forms, as for
  exact entries. `implementation_inexact_two_term`: the guarantees of `implementation_inexact`
  with `p.count ≤ 995328 π (1 + (log 2)^{-1/2}) (√(N ℓ) + ℓ)`.

**The precision term.** The paper's bound `hs:eq:unitarybound`,
`O(√(Nℓ) + ℓ/log(e + ℓ/N))`, is Corollary `hs:cor:hybrid` at `τ = π/2`: it chooses between the
bound of Theorem `hs:thm:main` and optimal block-encoding simulation from other papers
(qubitization with the joint time-precision dependence of QSVT). Corollary `hs:cor:hybrid` is
not formalised, so neither is the additive term `ℓ/log(e + ℓ/N)`. The formalised counts are
those of Theorem `hs:thm:main` at `s = N`, `t = π/2` and `η = 1` (exact entries) or `η = 2`
(inexact entries): `O(√N + √(Nℓ) + ℓ)`, with the additive `ℓ` in place of `ℓ/log(e + ℓ/N)`.
Since `ℓ ≥ log 2 > 0`, `√N ≤ (log 2)^{-1/2} √(Nℓ)` (`sqrt_le_absorb`, with `(log 2)^{-1/2}`
written `(√(log 2))⁻¹`) absorbs the first term into `√(Nℓ)` (`three_term_le_two_term`), so the
formalised count is `O(√(Nℓ) + ℓ)` (`implementation_two_term`,
`implementation_inexact_two_term`). For `ℓ ≤ N`, that is `ε ≥ e^{-N}`, `ℓ ≤ √(Nℓ)`, so the
formalised count is `O(√(Nℓ))`, the order of `hs:eq:unitarybound` there (`three_term_le_root`;
for `ℓ ≤ N ≤ s τ` the proof of `hs:cor:hybrid` also uses Theorem `hs:thm:main`); for `ℓ > N` it
exceeds that bound by at most the factor `log(e + ℓ/N)` (`two_term_le_hybrid`). At constant `ε`
it is `O(√N)`, the upper bound in the corollary's `Θ(√N)`.

**Proof map, exact entries** (`Exact.lean`). Theorem `hs:thm:main`
(`ImprovedSparseHamiltonian.simulation_log_one`) is applied to the released native data
`UnitaryEntryData.toNative D` of the dilation `H_U = [[0, U], [U†, 0]]`
(`UnitaryEntryData.dilationMatrix`), with `s = N`, `η = 1`, `t = π/2` and precision `ε`;
Hermiticity and the unit row and column norms are the released
`UnitaryEntryData.dilation_hermitian`, `UnitaryEntryData.dilation_row_energy` and
`UnitaryEntryData.dilation_column_energy`. As `H_U² = 1` (`UnitaryEntryData.dilation_sq`),
`e^{-i(π/2)H_U} = -i H_U` (`UnitaryDilationTransfer.exp_quarter_turn`), and `H_U` maps
`|1⟩ ⊗ ψ` to `|0⟩ ⊗ Uψ` (`UnitaryEntryData.dilation_includeOne`);
`UnitaryDilationTransfer.exists_clean_unitary_program` adds the flag flip and the phase
correction as one fixed alignment gate, without queries (`native_implementation`).
`UnitaryEntryOracle.compile` turns the known locators into fixed gates and each value query into
one entry query between fixed routing gates, preserving the whole operator (`implementation`).
The count `995328 (√N (π/2) + √(N (π/2) ℓ) + ℓ)` of
`ImprovedSparseHamiltonian.simulation_log_one` is at most `497664 π (√N + √(N ℓ) + ℓ)`
(`exact_shape_le`).

**Proof map, inexact entries** (`Table.lean`, `TableOracle.lean`, `Inexact.lean`,
`Uniform.lean`). The dilation `H̃_U = [[0, Ũ], [Ũ†, 0]]` of the represented matrix
(`Table.dilationMatrix`) is Hermitian (`Table.dilation_hermitian`) and vanishes on the diagonal
blocks, so the released known locators list all its nonzero entries (`Table.row_covers`,
`Table.toNative`, sparsity `N`). With `ξ = ε/(π N)`, `N ξ² ≤ 1` (`card_mul_sq_le_one`) and
`energy_le_four` give row and column norms at most `η = 2` (`Table.dilation_row_energy_two`,
`Table.dilation_column_energy_two`, from the unit norms of `U` through the released
`UnitaryEntryData.row_energy` and `UnitaryEntryData.column_energy`). Theorem `hs:thm:main`
(`ImprovedSparseHamiltonian.simulation_log_one`) simulates `H̃_U` for `t = π/2` to error `ε/2`.
The two dilations share the known locators, so `‖H̃_U - H_U‖ ≤ N ξ`
(`Table.dilation_sub_norm_le`, by Schur's bound
`SparseValuePrecision.operator_error_le_of_common_locators` on the opposite blocks
`Table.opposite`), and Duhamel's bound
`‖e^{-i(π/2)H̃_U} - e^{-i(π/2)H_U}‖ ≤ (π/2) N ξ = ε/2` (`Table.dilation_evolution_error_le`,
`duhamel_term_eq_half`; through the released `HamiltonianStability.output_error_le` in
`duhamel_step`) gives error at most `ε` for the true dilation `H_U`. The released transfer with
the true involution `H_U` (`native_implementation_inexact`) and `Table.compile`
(`Table.letter`, `Table.value_routing`, `Table.compile_eval`, `Table.compile_count`) finish as
for exact entries (`implementation_inexact`). The count
`995328 (√N π + √(N π log(2/ε)) + log(2/ε))` is at most `995328 π (√N + √(N ℓ) + ℓ)`
(`inexact_shape_le`, from `log(2/ε) ≤ 2ℓ`). For `implementation_inexact_uniform`,
`implementation_inexact` is applied to the table read on the admissible pairs of an instance and
a unitary within `ε/(π N)` of its represented matrix (`Table.comap`), whose oracle on a pair is
the oracle of `T` on its instance and whose encoding is that of `T`; the same gate sequence read
over the instances of `T` (`reindex`, `reindex_eval`, `reindex_count`) is the uniform circuit.

Every theorem of the library is axiom-audited in `UnitaryImplementationPrecision/Audit.lean`.

**Formalisation choices.**

* The inexact oracle is the released entry model without the unitarity promise (`Table`), so it
  is the same kind of object as the exact one, with represented entries `Ũ`; the released data,
  native interface, physical oracle and compiler are its special case `Table.ofData` (by `rfl`).
* The intended unitary is presented as released data by `exactData U hU`, whose ghost table
  returns the instance and is never queried, so that the released dilation lemmas
  (`UnitaryEntryData.dilation_sq`, `UnitaryEntryData.dilation_includeOne`,
  `UnitaryEntryData.dilation_hermitian`, `UnitaryEntryData.row_energy`,
  `UnitaryEntryData.column_energy`) apply to `H_U`.
* `N ≥ 1` (`Nonempty n`) suffices; the corollary's `N ≥ 2` is not needed for the upper bounds.
* The inexact case simulates at `η = 2` and precision `ε/2`, as in the paper; its constant
  `995328 π` is twice that of the exact case.
* `‖H̃_U - H_U‖ ≤ N ξ` is proved by Schur's bound on the common locators; the paper writes
  `‖H̃_U - H_U‖ = ‖Ũ - U‖ ≤ N ξ`.
* As in `UnitaryImplementation.implementation`, the rescaling `γ` of the simulator is part of
  the construction (it fixes the workspace; the construction chooses it from `N`, `η |t|` and
  the precision only) and the width bound `1 ≤ γ √N` of
  `ImprovedSparseHamiltonian.simulation_log_one` is dropped.
* In `implementation_with_reference` and `implementation_inexact_with_reference` the reference
  `R` is fixed before the circuit, as in the released
  `ImprovedSparseHamiltonian.simulation_with_reference_log_one`; `reference_error` and
  `reference_error_inexact` hold for every reference.

**Not formalised.** The sharper additive term `ℓ/log(e + ℓ/N)` of `hs:eq:unitarybound` for
`ℓ > N`, which needs Corollary `hs:cor:hybrid` (optimal block-encoding simulation from other
papers); the lower bound `Ω(√N)` at constant error (the reduction from unstructured search in
the proof of Corollary `hs:cor:unitary`); gate counts.
-/
