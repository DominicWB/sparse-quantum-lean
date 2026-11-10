import SparseLowerBounds.Hamiltonian.ReleaseTheta
import SparseLowerBounds.Hamiltonian.NativeMax
import SparseLowerBounds.LinearSystems.Instance

/-!
# Hamiltonian-simulation query lower bounds: paper-to-Lean entry point

Theorem `hsl:thm:main` (the Hamiltonian-simulation query lower bound), its lemmas
`hsl:lem:search`, `hsl:lem:mixed` and `hsl:lem:precision`, Corollary `hsl:cor:power` and Lemma
`odel:lem:herald` (heralded transfer) of the accompanying paper are formalised here, together
with the comparison with the released simulator.  No result from another paper is used.  The
detailed statement guide, with the model, the hard families, the hypotheses and the
formalisation choices, is `SparseLowerBounds/Hamiltonian/Statements.lean`.  Declarations named
below without a namespace are in `SparseLowerBounds.Hamiltonian`.

* Theorem `hsl:thm:main`, eq. `hsl:eq:main` (`Hamiltonian/Theorem.lean`): `main_max` — for any
  three algorithms with spectator registers that are `ε`-accurate on the time, mixed and
  precision families, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` with `c₀ = log 2/(4096π)`,
  `L = ln(1/ε)`, `h = ln(e + L/τ)`, `r = L/h` — the equivalent family form `main_exists` (one
  of the three families forces the bound on every accurate algorithm), and the same bound
  without a spectator register, `main_max_native` (`Hamiltonian/NativeMax.lean`); the
  per-family bounds `time_main`, `mixed_main`, `precision_main` (with a spectator register)
  and `*_main_native` (without); the instance properties `hard_instances` (real symmetric,
  operator norm and maximum row and column norms exactly one, sparsity exactly `s`, exact
  dyadic entries, input-independent locators, dimension at most `4 s (τ + r + 1)`).
* Lemma `hsl:lem:search`: `SparseLowerBounds.SearchWeight.search_lemma` and
  `SparseLowerBounds.SearchWeight.search_lemma_worst`; Lemma `hsl:lem:mixed`: `mixed_general`;
  Lemma `hsl:lem:precision`: `precision_general`, through
  `SparseLowerBounds.BitDegree.le_two_mul_count`.
* Corollary `hsl:cor:power` (`Hamiltonian/Power.lean`): `cor_power` and
  `cor_power_not_uniform`.
* Lemma `odel:lem:herald` (`Hamiltonian/Herald.lean`): `time_herald`, `mixed_herald`,
  `precision_herald`, their `*_native` and `*_general` forms, and `main_max_herald`.
* The released simulator: the bounds under the released endpoint error (`main_max_endpoint`,
  `Hamiltonian/ReleaseForm.lean`), for every program over the released simulator's oracle
  family (`main_max_release`, `Hamiltonian/ReleaseBridge.lean`), and the bracket
  `c₀ S ≤ max Q ≤ max count ≤ 995328 h S` with `S = √s τ + √(sτr) + r` for the released
  simulator on the hard families (`release_theta`, `release_theta_bracket`,
  `Hamiltonian/ReleaseTheta.lean`).
* The hard linear-system matrix of Theorem `qlsl:thm:main`
  (`SparseLowerBounds.LinearSystems.hardMatrix`, `LinearSystems/Instance.lean`), with its
  actual condition number `R/4 < ‖A‖ ‖A⁻¹‖` for `n ≥ R/2`
  (`SparseLowerBounds.LinearSystems.quarter_lt_cond`) and the dimension bounds
  `s κ L/32 ≤ N ≤ (s - 1) κ L` (`SparseLowerBounds.LinearSystems.dim_bounds`,
  `LinearSystems/Parameters.lean`).  Theorem `qlsl:thm:main` itself is formalised in the
  `LinearSystemLowerBound` library, which uses these two facts
  (`LinearSystemLowerBound.family_cond`, `LinearSystemLowerBound.family_dimension_sharp`).

**Model** (details in `Hamiltonian/Statements.lean`).  Algorithms are non-adaptive
`SparseHamiltonian.MultiOracleCircuit.Program`s over the released native sparse primitives of
a hard family (in-place row and column location oracles and the value oracle, inverses
included), with or without an untouched spectator register, run on an input-independent seed
and read through a fixed isometry into system ⊗ garbage.  Accuracy is trace distance at most
`ε` from `e^{-iτH_X} ψ_in` in observable form (`SparseLowerBounds.Readout.Accurate`), which
allows mixed outputs; an operator-norm (endpoint) error at most `ε` implies it.
`Q = p.labelCount .value` counts value queries, inverses included; location queries are free,
since the locators of the hard families are input-independent.  Controlled value calls are covered
by a documented reduction to the spectator form (no Lean lemma).

**Not formalised.**  Adaptive algorithms for Hamiltonian simulation (the theorems cover
non-adaptive programs, the class of the released simulator); padding the three families to a
common dimension; the structural remark on parity-amplitude reductions; gate, workspace and
classical costs; the ODE lower bounds of Section `part:odel` other than Lemma
`odel:lem:herald`.

**Provenance.** This library is an external development, included with its statements and proofs. It
was split into modules (`SparseLowerBounds.Imports` collects the external imports),
`set_option linter.unusedSectionVars false` was replaced by `omit … in`, `private` was removed so
that every theorem can be audited, linter warnings were fixed, and process notes were removed from
the documentation. Of its linear-system part, only the shared Boolean-query layer (`Query/`,
`Adaptive/Access.lean`) and the hard matrix (`LinearSystems/`) are included; its own linear-system
lower-bound theorems are not. The module `Hamiltonian/NativeMax.lean` was added in this package.
References to the manuscript use its labels.

**Audits.**  `SparseLowerBounds/Audit.lean` fixes the exact axiom report of every theorem of
the library and of every field of the `Prop` structures `HSRange`, `HardInstance` and
`LinearSystems.HardRange`.
-/
