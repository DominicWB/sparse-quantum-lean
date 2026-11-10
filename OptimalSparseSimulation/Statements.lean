import OptimalSparseSimulation.UnitaryBound

set_option autoImplicit false

/-!
# Theorem `hs:thm:optimal` and Corollary `hs:cor:unitary-optimal`: paper-to-Lean entry point

Section `hs:sec:optimal` of the manuscript states Theorem `hs:thm:optimal`: for `τ = η|t| ≥ 1` and
`0 < ε ≤ 1/64`, a unitary circuit achieves error at most `ε`, including all work-register outputs,
with the number of primitive sparse queries of eq. `hs:eq:optimal-bound`, and the guarantee
includes an untouched reference; eq. `hs:eq:optimal-bound` is `O(√s τ + √(sτr) + r)` with
`r = L/log(e + L/τ)`, `L = log(1/ε)`. Its upper bound is proved at the end of Appendix A (the proof
of Theorem `hs:thm:optimal`, eq. `opt:eq:regime-comparison`) by combining three constructions. This
library proves that upper bound with the explicit constant `2·10¹²`, and the upper bound of
Corollary `hs:cor:unitary-optimal` with the constant `5·10¹³`, from which it also obtains the bound
of Corollary `hs:cor:unitary` (eq. `hs:eq:unitarybound`). The matching lower bounds are not part of
this library: the `Θ` statement of `hs:thm:optimal` for `s ≥ 32` (Theorem `hsl:thm:main` against
this upper bound) is `OptimalLowerBounds.optimal_theta` (for measured algorithms over the same
oracle family, `OptimalLowerBounds.optimal_measured_theta`), and the constant-error `Θ(√N)` of the
corollary is that of Corollary `hs:cor:unitary` (`UnitaryImplementationExtensions`).

No result from another paper is used. The released libraries are unchanged; this library reuses
Theorem `hs:thm:main` of `SparseHamiltonian`, the native signed factor of `NativeSignedFactor`, the
quantity `r_b` of `SignedFactorSimulation`, the large-sparsity core of `LargeSparsityCore` and the
entry-oracle model of `UnitaryImplementationPrecision`. References to the manuscript use its
labels. Every theorem of the library is axiom-audited in
`OptimalSparseSimulation/Audit.lean`.

**Naming convention.** All declarations are in the namespace `OptimalSparseSimulation`; names
below are relative to it, except the names of the released libraries, which are fully qualified.
`Simulates` and `physOracle` are `NativeSignedFactor.Simulates` and
`NativeSignedFactor.physOracle`.

## The common query model

The sparse data are those of the released package,
`SparseHamiltonian.NativeSparseBlockEncoding.Data X n Z s`: for every instance `x`, a matrix
`H = D.matrix x` on `n`, a row locator and a column locator that are arbitrary unitaries with the
in-place, phase-one promise on the `s` listed slots of every row and column (the slot lists are
injective and cover every nonzero entry), and an additive value oracle whose word decodes to the
entry by a known decoder. The physical native call `NativeSignedFactor.physOracle D l x` is the
original primitive `l` (row locator, column locator or value oracle) on its register, with every
other register a spectator.

`NativeSignedFactor.Simulates (physOracle D) H t ε q` (released with the native signed factor)
states: there are a finite type `ι`, a known isometry `inp : ℂ^n → ℂ^ι ⊗ W` and a program whose
only oracle calls are calls `physOracle D l x` on every block of `ℂ^ι ⊗ W`
(`SparseHamiltonian.CoherentQuerySchedule.oracle`: the block register is a spectator), with at
most `q` calls counting adjoints, unitary for every instance, and with
`‖p.eval x ∘ inp - inp ∘ e^{-itH(x)}‖ ≤ ε` for every instance, with the same known isometry on
input and output. `Implements O V ε q` is the same statement for an arbitrary target `V x`
(`simulates_iff`).

The baseline simulation and the large-sparsity core act on their own workspaces.
`SpectatorForm O O'` (module `Spectator`) says that a family `O'` is `O` with a spectator register
up to one fixed linear isometric equivalence `e` (independent of the label and the instance):
`e O'(l, x) e⁻¹ = 1 ⊗ O(l, x)`. Programs over such a family move to the common form with the same
count, unitarity and error (`implements_of_spectatorForm`, `simulates_of_spectatorForm`). The
oracle of the active Cayley layers, used by the large-sparsity core, is of this form
(`cayleyActive_form`: unfolded, it is the physical native call, flattened by the fixed
`SparseHamiltonian.NativeDilationLayout.layout` and extended by the native-control spectators on
every active label, `cayleyActive_eq`), and so is the oracle of the baseline simulation,
which adds one alignment spectator (`improved_form`).

## The statement of Theorem `hs:thm:optimal`

**Theorem** (`optimal_simulation`). Let `H(x) = D.matrix x` be Hermitian with row and column
Euclidean norms at most `η` for every instance, let `t` be a real time with `τ = η|t| ≥ 1`, and let
`0 < ε ≤ 1/64`. Then

`Simulates (physOracle D) H t ε (2·10¹² (√s τ + √(sτr) + r))`,

with `L = log(1/ε)`, `h = log(e + L/τ)` and `r = L/h` (`hs:eq:optimal-parameters`; in Lean
`r = SignedFactorSimulation.rb τ ε = L/log(e + L/τ)`, `rval_eq_rb`, and the bound is `bound s τ ε`).
The input and the program may depend on the family `D` but not on the instance `x`: the same
circuit serves every instance of `X` (for `X` the whole promise class this is the statement of the
paper); negative times are included.
`optimal_simulation_with_reference` gives the same circuit on normalised inputs entangled with an
untouched finite reference.

## The statement of Corollary `hs:cor:unitary-optimal`

The entry-oracle model is that of Corollary `hs:cor:unitary`
(`UnitaryImplementationPrecision`): a reversible entry table `T` with a known bounded decoder whose
represented matrix `T.matrix x` is within `ε/(πN)` of an intended unitary family `U` in every
entry, `N = card n` (inexact entries), or released exact data `D` with unitary `D.matrix x`. The
oracle `entryOracle T ι` is one ordinary call of the table
(`SparseHamiltonian.UnitaryPrecision.Table.flatEntry`, the original table call with spectators by
`SparseHamiltonian.UnitaryPrecision.Table.flatEntry_eq_original`) with the spectators of the
common form.

**Corollary** (`unitary_optimal_inexact`, `unitary_optimal`). For `0 < ε ≤ 1/2` there are a known
isometric input and one program whose only oracle calls are calls of `entryOracle` (no location
oracle), unitary for every instance, with full-output error at most `ε` against `U x`
(respectively `D.matrix x`) and at most `5·10¹³ (√(N ρ_ε) + ρ_ε)` calls, inverse calls counted,
with `ℓ = log(1/ε)` and `ρ_ε = ℓ/log(e + ℓ)` (`rho`, the precision quotient in the proof of
Corollary `hs:cor:unitary-optimal`; `hs:eq:unitary-optimal-bound`).
`unitary_optimal_inexact_with_reference` and `unitary_optimal_with_reference` add an untouched
finite reference.

**Corollary `hs:cor:unitary`, eq. `hs:eq:unitarybound`** (module `UnitaryBound`:
`unitary_bound_inexact`, `unitary_bound`). The circuits of Corollary `hs:cor:unitary-optimal`
make at most `5·10¹³ (√(Nℓ) + ℓ/log(e + ℓ/N))` calls (`hybridTerm`, `count_le_unitary_shape`),
since `ρ_ε ≤ ℓ` (`rho_le_log`) and `ρ_ε ≤ ℓ/log(e + ℓ/N)` (`rho_le_hybrid`, from `ℓ/N ≤ ℓ`);
`unitary_bound_inexact_with_reference` and `unitary_bound_with_reference` add an untouched finite
reference. The manuscript proves eq. `hs:eq:unitarybound` through Corollary `hs:cor:hybrid`, which
is not formalised. The lower bound `Ω(√N)` of Corollary `hs:cor:unitary` is in
`UnitaryImplementationExtensions`.

## The proof

*Regimes* (module `Regimes`, the proof of Theorem `hs:thm:optimal`, eq. `opt:eq:regime-comparison`).
With the threshold `h ≥ 10⁴` of the core:

* `h < 10⁴`: Theorem `hs:thm:main`
  (`SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one`) uses at most
  `995328 (√s τ + √(sτL) + L)` calls, and `L = hr` gives
  `√s τ + √(sτL) + L ≤ 10⁴ (√s τ + √(sτr) + r)` (`bounded_bound`).
* `h ≥ 10⁴` and `sτ ≥ Lh`: the large-sparsity core (`LargeSparsityCore.Native.core_simulation`)
  uses at most `6972480 √(sτr)` calls.
* `h ≥ 10⁴` and `sτ < Lh`: the native signed factor
  (`NativeSignedFactor.native_signed_simulation_eta`, Theorem `opt:thm:signed` with `T = sτ` and
  `b = √s τ`) uses at most `48·10¹⁰ (√(Tb) + √(T r_b) + r_b)` calls. With `x = L/τ`,
  `x ≥ e^h/2` gives `h³ ≤ x`, so `b ≤ r` (`b_le_r`), and `h e^{h/2} ≤ x` gives
  `L/b ≥ √(x/h) ≥ e^{h/4}`, so `log(e + L/b) ≥ h/4` and `r_b ≤ 4r` (`quarter_le_log`, `rb_le`;
  `opt:eq:regime-comparison`). Hence `√(Tb) + √(T r_b) + r_b ≤ 4 (√(sτr) + r)`
  (`signed_bound`).

*Combination* (module `Optimal`). The three cases, with the first two moved to the common form
(`improved_form`, `cayleyActive_form`), give `optimal_simulation`.

*The corollary* (module `Unitary`). Theorem `hs:thm:optimal` is applied to the represented
dilation `H̃_U = [[0, Ũ], [Ũ†, 0]]` (`SparseHamiltonian.UnitaryPrecision.Table.toNative`:
sparsity `N`, the known locators, row and column norms at most `η = 2`) with `t = π/2` (so
`τ = π`) and precision `δ = min(ε/2, 1/64)` (`delta`). Duhamel's bound
(`SparseHamiltonian.UnitaryPrecision.duhamel_step`) gives error at most `ε` for the true dilation
`H_U`; the released transfer
(`SparseHamiltonian.UnitaryDilationTransfer.exists_clean_unitary_program`) adds the flag flip and
the phase correction; the result is moved back to the common form; and `compile` replaces the
known locators by fixed gates and each value query by one entry query between fixed routing gates
(`SparseHamiltonian.UnitaryPrecision.Table.value_routing`), without adding calls
(`compile_count_le`). The budget
(`unitary_budget`): `ρ_ε ≥ 1/2`, `ℓ ≤ log(1/δ) ≤ 7ℓ` and `log(e + log(1/δ)/π) ≥ log(e + ℓ)/3`, so
`r ≤ 21 ρ_ε` and `2·10¹² (√N π + √(Nπr) + r) ≤ 5·10¹³ (√(N ρ_ε) + ρ_ε)`.

## Scope and differences from the manuscript

* Only query complexity is claimed here; the gate-level implementation (Theorem `gate:thm:main`) is
  the library `GateOptimalPrecision` (for Theorem `hs:thm:optimal`). The constants are explicit:
  `2·10¹²` in Theorem `hs:thm:optimal` and `5·10¹³` in the corollary.
* The threshold on `h` is the explicit `10⁴` of the core (`opt:eq:core-explicit`); for `h < 10⁴`
  the baseline bound has the required order, as in the manuscript.
* The row and value index types `n` and `Z` are taken in `Type`, so that the spectator types of the
  common form are types of the first universe (the predicate `Simulates` quantifies over
  `ι : Type`). The instance family `X` is arbitrary.
* The circuits of the three regimes act on different physical workspaces; the statement puts all
  of them in the single form `Simulates (physOracle D)` by fixed changes of coordinates, which is
  how "primitive sparse-oracle queries" is made precise. The known input `inp` contains the known
  preparations of each construction (by the paper's convention, known changes of encoding are
  absorbed into the surrounding query-free operations).
* In the corollary, the exact case is derived from the inexact case with zero entry error, so both
  use `η = 2` and `δ = min(ε/2, 1/64)` (the manuscript uses `η = 1` for exact entries). The
  sparsity is any `N ≥ 1`; the manuscript assumes `N ≥ 2`.
* `η > 0` is not a hypothesis: it follows from `η|t| ≥ 1`.
-/
