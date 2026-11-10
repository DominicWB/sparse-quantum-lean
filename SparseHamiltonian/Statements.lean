import SparseHamiltonian.ManuscriptPrecision
import SparseHamiltonian.UnitaryImplementation

/-!
# Hamiltonian simulation: paper-to-Lean entry point

Theorem 2.1 (`hs:thm:main`) of the accompanying paper is formalized by
`SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one`.
The declaration, including its full quantifiers and concrete circuit, is in
`SparseHamiltonian/ManuscriptPrecision.lean`.

For row and column Euclidean bounds `η > 0`, time `t`, and `0 < ε ≤ 1/2`,
the primitive query bound is
`995328 * (sqrt(s) * (η * |t|) + sqrt(s * (η * |t|) * log(1/ε)) + log(1/ε))`.
One input-independent circuit and one common clean embedding serve every
unknown instance in the specified oracle family. The error is an operator
norm bound on the entire output isometry, including its workspace.

`simulation_spectral_log_one` derives the energy promises from a spectral-norm bound;
`simulation_with_reference_log_one` includes any finite untouched entangled reference.
The zero-time and zero-energy cases are supplied separately by
`SparseHamiltonian.ImprovedZeroSimulation`.

The exact-entry, error-`1/4` instance of Corollary `hs:cor:unitary` is
`SparseHamiltonian.UnitaryImplementation.implementation`, in
`SparseHamiltonian/UnitaryImplementation.lean`. It constructs a clean circuit
with full-output operator-norm error at most `1/4`, using at most
`UnitaryImplementation.queryConstant * sqrt(N)` original entry-oracle calls
(including inverse calls). Its reference-stability theorem is
`SparseHamiltonian.UnitaryImplementation.reference_error`. The full corollary
(every `0 < ε ≤ 1/2`, exact entries or entries within `ε/(πN)`, the bound
`hs:eq:unitarybound` and the constant-error `Θ(√N)`) is proved in the libraries
`UnitaryImplementationPrecision`, `UnitaryImplementationExtensions` and
`OptimalSparseSimulation`.

The formal construction uses exact known gates and allocates the error as `ε/3` to the Cayley
mesh (`ImprovedNativeSimulation.slots`) and `ε/3` to the filter schedule
(`ImprovedNativeSimulation.degree`), in place of the paper's mesh error `ε/4`, filter tolerance
`ε/8` with amplified error `ε/4`, and `ε/2` left for the approximation of known gates.

No gate complexity, classical circuit-generation cost, lower bound,
time-dependent extension (`hs:thm:time`, Theorem 4.1), or sharper
precision-only hybrid corollary (`hs:cor:hybrid`, Corollary 4.2) is asserted
by these endpoints. The LaTeX labels identify the results across revisions of the manuscript.
-/
