import SparseODE.ImprovedSparseODE
import SparseODE.ODEOperationalBounds
import SparseODE.ODECompleteSuccess

/-!
# Constant-coefficient dissipative ODE: paper-to-Lean entry point

Theorem 6.1 (`ode:thm:main`) of the accompanying paper is formalized by
`SparseHamiltonian.ODECompleteEndpoint.solver`, with the nonempty-family form
`SparseHamiltonian.ODECompleteEndpoint.solver_of_nonempty_promise`.
Their full statements are in `SparseODE/ODECompleteSuccess.lean` and build
on the trial-family theorem `SparseHamiltonian.ImprovedSparseODE.solver`.
The existing `SparseHamiltonian.*` declaration namespaces are preserved.

For the equation `x' = A x + b`, the sparse data encodes `M = -A`.
The Hermitian part of `M` is positive semidefinite. Source norms are exact
public inputs. Initial and forcing preparation circuits, their inverses,
and the specified controls on known source/sector labels are supplied.

The concrete trial family has mean success probability at least `1/4` under
uniform trial selection. Each nonzero successful output has normalized vector
error at most `ε / 500`, up to phase. Matrix queries are at most
`318504960 * g * (sqrt(s) * Θ + sqrt(s * Θ * ℓ) + ℓ)` per trial, with at most
`10 * g` calls to each supplied source interface (including inverse calls).
`SparseHamiltonian.ODEOperationalBounds` exposes the operational consequences
and the common-energy specialization of equation `ode:eq:simple`.

The complete endpoint runs at most four fresh trials and stops at the first
successful herald. Its success probability is at least `175/256 > 2/3`.
After conditioning on success and discarding the classical trial labels,
the output density operator is positive, has trace one, and has spectral
trace distance at most `ε` from the normalized actual solution.
The worst-case matrix-query count is at most
`1274019840 * g * (sqrt(s) * Θ + sqrt(s * Θ * ℓ) + ℓ)`, with at most
`40 * g` calls to each supplied source interface, including inverses.

The time-dependent extension (`ode:thm:time`), general-generator extension
(`ode:thm:general`) and all lower bounds are outside this formalization, as are
gate and workspace bounds. The linear-system algorithm (`qls:thm:main`) is
formalized separately in the `SparseLinearSystems` library.
-/
