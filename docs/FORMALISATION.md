# Formalisation guide

This guide describes the scope and assumptions of package **0.1.0-rc6**.
The accompanying paper is *Root-sparsity scaling for Hamiltonian simulation,
differential equations and linear-system solvers*.
Paper labels below are stable references; theorem numbers and manuscript line
numbers in individual source comments can refer to earlier manuscript versions.

The author confirmed successful compilation of this revised package on
9 October 2026 with Lean 4.32.1 and Mathlib v4.32.1, including
`GateEfficientSchedule/Abstract.lean`, `QLSHoeffding/Constants.lean` and all
10,055 axiom audits. This records the local build; GitHub Actions status is
reported separately. The release-documentation update changes no Lean sources
or build settings.

## Principal results

The theorem declarations, including all hypotheses, are authoritative.
`Statements.lean` files explain their correspondence with the paper and give
the more detailed implementation and proof maps.

| Paper result | Principal Lean endpoint or guide |
|---|---|
| Time-independent Hamiltonian simulation (`hs:thm:main`) | `SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one`, in [ManuscriptPrecision.lean](../SparseHamiltonian/ManuscriptPrecision.lean) |
| Time-dependent Hamiltonian simulation (`hs:thm:time`) | `SparseHamiltonian.TimeDependent.simulation`; [uniform-mesh guide](../TimeDependentHamiltonian/Statements.lean), [general meshes](../TimeDependentExtensions/Statements.lean), [integrable paths](../IntegrablePathSimulation/Statements.lean) |
| Constant-error unitary implementation (`hs:cor:unitary`) | `SparseHamiltonian.UnitaryImplementation.implementation`, in [UnitaryImplementation.lean](../SparseHamiltonian/UnitaryImplementation.lean); [precision extensions](../UnitaryImplementationPrecision/Statements.lean) |
| Gate-efficient Hamiltonian simulation (`hs:thm:gates`) | `SparseHamiltonian.GateSchedule.gate_efficient_simulation_ms` and `sel_simulation_ms`; [manuscript-schedule guide](../GateEfficientSchedule/Statements.lean), [binary-data guide](../GateEfficientBinary/Statements.lean) |
| Abstract boundary-resolvent simulation (`hs:lem:abstract`, `hs:eq:explicitcount`) | `SparseHamiltonian.GateSchedule.abstract_simulation_ms` and `abstract_simulation_ms_explicit`; [manuscript-schedule lemma](../GateEfficientSchedule/Abstract.lean) |
| Constant-coefficient dissipative ODE (`ode:thm:main`) | `SparseHamiltonian.ODECompleteEndpoint.solver`, in [ODECompleteSuccess.lean](../SparseODE/ODECompleteSuccess.lean) |
| Time-dependent dissipative ODE (`ode:thm:time`) | `SparseHamiltonian.TimeDependentODE.solver`; [uniform-mesh guide](../TimeDependentODE/Statements.lean), [general-mesh guide](../TimeDependentExtensions/Statements.lean) |
| Gate-efficient dissipative ODE (`ode:thm:gates`) | `SparseHamiltonian.GateSelective.binary_ode_budget_sel` and `binary_ode_time_budget_sel`; [selective-synthesis guide](../GateEfficientSelective/Statements.lean), [source-node guide](../GateEfficientBinaryNodes/Statements.lean) |
| General constant-coefficient ODE (`ode:thm:general`), conditional on a block-input solver | `SparseHamiltonian.GeneralODE.general`; [general-ODE guide](../GeneralODE/Statements.lean) |
| Sparse linear-system algorithm (`qls:thm:main`) | `QLSHoeffding.main_exactH` and `main_exactH_exists`; [Hoeffding-schedule guide](../QLSHoeffding/Statements.lean) |
| Hamiltonian query lower bound (`hsl:thm:main`) | `SparseLowerBounds.Hamiltonian.main_max`; [lower-bound guide](../SparseLowerBounds/Hamiltonian/Statements.lean) |
| Dissipative-ODE query lower bounds (`odel:thm:combined`, `odel:thm:joint`, `odel:thm:psd`) | `SparseLowerBounds.ODE.combined`, `SparseLowerBounds.ODE.joint_witness`, `ODELowerBoundExtensions.Psd.psd`; [base guide](../SparseLowerBounds/ODE/Statements.lean), [extensions](../ODELowerBoundExtensions/Statements.lean) |
| Linear-system query lower bound (`qlsl:thm:main`) | `LinearSystemLowerBound.lower_bound`; [guide](../LinearSystemLowerBound/Statements.lean) |

The upper bounds construct circuits or finite protocols and prove their
correctness and resource counts. The complete ODE and linear-system
endpoints include heralded success probability at least `2/3` and a bound on
the trace distance of the conditional mixed output. Worst-case protocol
costs include unsuccessful histories, rather than counting only a successful
trial.

## Access and output conventions

The query model uses exact finite-word sparse data with injective padded row
and column locators and their full unitary extensions. The slot register
embeds into the matrix-index register, and the public decoder is bounded on
every word. See [NativeSparseBlockEncoding.Data](../SparseHamiltonian/NativeSparseBlockEncoding.lean).
The precise row/column norm, Hermiticity, dissipativity and representation
promises remain hypotheses of each applicable theorem.

A primitive matrix query is an application of a row locator, column locator
or value oracle, or its inverse. Query-only bounds allow input-independent
unitaries at no query cost. Gate-level bounds additionally count elementary
gates and workspace. Controlled uses of opaque matrix oracles are not free:
the native implementations construct the required controls from the stated
primitive access. Time-dependent access is coherent in the sampled-time
register and allows time-varying supports.

Algorithms are selected using public parameters and a promise family before
the unknown instance is supplied. The resulting guarantee is uniform over
instances in that family.

Hamiltonian implementation error uses the full-output convention on clean
inputs: it counts residual work-register amplitudes and phases, with the
ideal work registers returned to zero. Reference-system versions retain an
untouched spectator register where stated. Heralded ODE and linear-system
outputs are compared as conditional density operators after discarding the
protocol's classical labels and auxiliary output registers.

## Exact gates and finite-set synthesis

The exact-gate circuit model permits one-qubit unitaries with at most three
literal controls on distinct wires. Generic circuit theorems also take
boundary and private operations as supplied unitaries; subsequent native
and binary libraries implement these operations and count their primitive
queries and additional elementary gates.

The finite-gate results assume `GateSynth.Synthesis`: a specified finite gate
set approximates each such elementary unitary, for every positive error
`zeta`, using at most `L zeta` gates and a fixed clean ancillary register.
Logarithmic synthesis-cost conclusions additionally assume
`L zeta <= c1 * log(1/zeta) + c0` on the stated accuracy range.
See [the synthesis hypothesis](../GateEfficientSynthesis/Hypothesis.lean).
This package does not prove a particular Clifford+T synthesis algorithm.

Where required, the finite gate set must be closed under adjoints and contain
the elementary gates used by the exact zero tests. Approximation is in the
full-output convention. The package proves how the local errors compose;
the inverse of an implemented circuit is its actual reverse-adjoint circuit.

[Selective synthesis](../GateEfficientSelective/Statements.lean) retains gates
already in the finite set. Thus supplied private-circuit costs enter the
Hamiltonian bound linearly, outside the synthesis logarithm, and supplied
source-preparation costs enter the ODE bound linearly. These endpoints are
the reference for `hs:eq:gate-total`, `ode:eq:gate-main` and
`ode:eq:gate-space`; the older compiler remains available with its more
conservative counts.

## Sources and reversible arithmetic

ODE query endpoints receive source norms and state-preparation interfaces
for the initial and forcing vectors, with their specified controls and
inverses. These calls are counted. General time-dependent forcing also
requires coherent, phase-consistent source loading, weight preparation and
the stated source-quadrature and normalisation certificates. Gate endpoints
use actual supplied source circuits with specified errors, gate costs and
workspace. They do not assert efficient state preparation for arbitrary
classically described vectors. For constant forcing, the source-weight
preparation is constructed from a rotation and Hadamard gates; the initial
and forcing-state loaders are still supplied.

The linear-system model similarly supplies preparation of the right-hand
side, with the required controlled forward and inverse access. The
algorithm's uses of that interface are counted.

Generic [native theorems](../GateEfficientNative/Statements.lean) accept a
compute circuit, a decoding identity (`NativeOK`) and reversible angle
arithmetic (`ArithOK`). The arithmetic writes approximations to
`2 * arctan(abs(z))` and `arg(z)`, preserves the relevant inputs and returns
its scratch register to zero. Its gates, errors and workspace are counted.

The [binary-data construction](../GateEfficientBinary/Statements.lean)
proves these identities for its concrete sparse-oracle circuits and proves
the required arithmetic using reversible operations and CORDIC. This is
more than a supplied arithmetic-cost hypothesis. The concrete representation
uses two's-complement real and imaginary entry words with a known positive
scale, binary matrix indices and power-of-two locator-slot registers with
the specified slot embedding. The theorems assume this representation;
they should not be read as a separate proved conversion from every possible
matrix or locator encoding.

[Bit-budget results](../GateEfficientBitBudget/Statements.lean) make the
fixed-point size assumptions on the public scales and parameters explicit
and bound the actual register words by the paper's bit-length parameters.
For general source-node rules, a reversible node program with its own
correctness and cost can be supplied; standard dyadic address calculations
are constructed. See [computed source nodes](../GateEfficientBinaryNodes/Statements.lean).

## Schedules and current scope

[GateEfficientSchedule](../GateEfficientSchedule/Statements.lean) proves
general exact-gate, supplied-private-circuit and native endpoints with the
paper's literal filter schedule, slot bound and error allocation. It also
proves the sharper Cayley and freezing-error constants used there.
The abstract simulation lemma now has the manuscript's schedule for every
real time: at integer `Q >= 1`, it makes exactly
`6(32Q - 1) ceil(4W/Q + log2(4096/epsilon))` private calls, with full-output
error at most `epsilon/2`. Its bound is `3880 (W + Q log(1/epsilon))`
for `0 < epsilon <= 1/2`; calls to the boundary unitary are counted separately.

The final binary-data and bit-budget specialisations retain the earlier
schedule, as do the isometry, scalar and binary-data specialisations of the
earlier abstract lemma. The ODE SELECT lemma (`ode:lem:gate-select`) also
uses the earlier depth and subdivision condition: the literal formula
`ode:eq:gate-select-schedule` and the first three mesh conditions of
`ode:eq:gate-select-mesh` are not formalised in that form. These results have
the same asymptotic complexity, without adopting every numerical choice
from the manuscript.

[QLSHoeffding](../QLSHoeffding/Statements.lean) proves the sharp binomial
tail bound and incorporates the paper's repetition count into the complete
finite-degree Chebyshev solver. The new
[constants module](../QLSHoeffding/Constants.lean) proves
`5101 log(10/zeta_j) <= n_j <= 5102 log(10/zeta_j)` for `0 < epsilon <= 1`,
matching the repetition-count estimate in `qls:rem:constants`. Earlier
averaging-filter and Chebyshev endpoints remain available with their larger
repetition counts.

The principal limits of the formalisation are:

- The refined hybrid precision bound (`hs:cor:hybrid`), its external
  block-encoding ingredient (`hs:eq:prioroptimal`), and hence the refined
  additive term in the unitary-implementation corollary are not formalised.
  The unitary precision endpoints have the additive term `ell` instead of
  `ell / log(e + ell/N)`; the constant-error root-dimension result is covered.
- The general, potentially non-dissipative constant-coefficient ODE result
  is conditional on `BlockSolver`. Its history-system construction,
  implementation and reduction are proved, but the assumed block-input
  linear-system solver is not constructed here. See its
  [precise interface](../GeneralODE/Solver/Interface.lean).
- The finite-gate, source-preparation and representation assumptions above
  remain part of the applicable theorem statements.
- Lower-bound extensions distinguish unitary programs, adaptive protocols
  and measured algorithms, their oracle call forms, and their error
  criteria. A theorem in one model does not automatically claim every
  stronger model. The relevant statement guides specify the exact scope.

## Further statement guides

Source comments in earlier libraries describe those libraries at the time
they were written. In particular, an older guide saying an extension is
"outside this formalisation" does not describe the whole rc6 package.
Use the newer guides below and the preceding scope summary together with
the actual theorem declarations.

| Topic | Guides |
|---|---|
| Exact and native Hamiltonian circuits | [exact](../GateEfficientHamiltonian/Statements.lean), [time-dependent](../GateEfficientTimeDependent/Statements.lean), [native](../GateEfficientNative/Statements.lean), [signed time](../GateEfficientSigned/Statements.lean) |
| Binary Hamiltonian circuits | [constant](../GateEfficientBinary/Statements.lean), [time-dependent](../GateEfficientBinaryTime/Statements.lean), [bit budgets](../GateEfficientBitBudget/Statements.lean) |
| ODE circuits and budgets | [exact](../GateEfficientODE/Statements.lean), [binary](../GateEfficientBinaryODE/Statements.lean), [binary time-dependent](../GateEfficientBinaryODETime/Statements.lean), [budgets](../GateEfficientODEBudget/Statements.lean), [selective synthesis](../GateEfficientSelective/Statements.lean) |
| Meshes, SELECT and source quadrature | [meshes](../GateEfficientMesh/Statements.lean), [SELECT](../GateEfficientSelect/Statements.lean), [binary SELECT](../GateEfficientBinarySelect/Statements.lean), [quadrature](../GateEfficientQuadrature/Statements.lean), [nodes](../GateEfficientBinaryNodes/Statements.lean) |
| Synthesis and zero-time cases | [synthesis](../GateEfficientSynthesis/Statements.lean), [trials](../GateEfficientSynthesisTrials/Statements.lean), [gate remarks](../GateEfficientRemarks/Statements.lean), [zero time](../ZeroTimeRemarks/Statements.lean), [zero-time ODE gates](../ZeroTimeGateODE/Statements.lean), [general ODE](../GeneralODEZeroTime/Statements.lean) |
| Linear-system algorithms | [averaging](../SparseLinearSystems/Statements.lean), [Chebyshev filter](../ChebyshevFilter/Statements.lean), [Chebyshev solver](../ChebyshevLinearSystem/Statements.lean), [finite degrees](../ChebyshevLinearSystemFinite/Statements.lean), [Hoeffding schedule](../QLSHoeffding/Statements.lean) |
| Unitary implementation and lower bounds | [extensions](../UnitaryImplementationExtensions/Statements.lean), [precision](../UnitaryImplementationPrecision/Statements.lean), [adaptive](../AdaptiveUnitaryLowerBound/Statements.lean), [measured](../MeasuredUnitaryLowerBound/Statements.lean) |
| Hamiltonian lower-bound extensions | [adaptive](../AdaptiveHamiltonianLowerBound/Statements.lean), [time-dependent](../TimeDependentHamiltonianLowerBound/Statements.lean), [further time-dependent forms](../TimeDependentLowerBoundExtensions/Statements.lean) |
| ODE lower-bound extensions | [constant coefficients](../ConstantODELowerBound/Statements.lean), [adaptive](../AdaptiveODELowerBound/Statements.lean), [physical oracles](../PhysicalODELowerBound/Statements.lean), [released solvers](../ReleasedODESolverLowerBounds/Statements.lean) |
| Measured models and precision obstructions | [deferred measurement](../DeferredMeasurementLowerBounds/Statements.lean), [lower-bound remarks](../LowerBoundRemarks/Statements.lean), [single-program Dyson solver](../DysonSingleProgram/Statements.lean), [general Dyson access](../DysonGeneralAccess/Statements.lean) |

## Logical assumptions and checks

The audit modules contain 10,055 strict `#guard_msgs` checks of
axiom reports. Their allowed foundational axioms are `propext`,
`Classical.choice` and `Quot.sound`; some declarations depend on only a
subset. Mathematical hypotheses such as `Synthesis` and `BlockSolver` are
explicit theorem arguments, not added logical axioms.

The package checker verifies source hashes, dependency pins, audit coverage,
version consistency and prohibited proof shortcuts. It is a packaging and
hygiene check, separate from Lean's kernel checking during `lake build`.
See the [README](../README.md) for the build commands.
