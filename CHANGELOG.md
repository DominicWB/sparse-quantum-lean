# Changelog

## 0.1.0-rc6 — 2026-10-09

- Extended the project to 55 libraries and 10,055 strict axiom audits.
- Added time-dependent Hamiltonian and dissipative ODE query algorithms,
  certified-mesh extensions, and exact-gate and finite-gate-set implementations
  with gate and workspace bounds.
- Added concrete binary-data decoding, reversible arithmetic, routing,
  coherent selection and source-node constructions.
- Added the sparse linear-system algorithm, Chebyshev filtering and the
  Hoeffding repetition schedule used in the manuscript. The latest addition
  proves the explicit `5101 log(10/zeta_j)` to `5102 log(10/zeta_j)` bracket
  for the repetition count (`QLSHoeffding/Constants.lean`).
- Added Hamiltonian, ODE, linear-system and unitary-implementation lower
  bounds, including adaptive and measured variants in their stated models.
- Extended unitary implementation to general precision and certified inexact
  entries, with the additive precision term documented in the README.
- Added selective synthesis, retaining supplied private and source circuit
  costs outside synthesis logarithms, and Hamiltonian circuit endpoints with
  the manuscript's explicit filter and discretisation schedules. The latest
  addition gives the abstract simulation lemma for every real time with the
  manuscript's explicit call count (`GateEfficientSchedule/Abstract.lean`).
- Included the general constant-coefficient ODE construction conditional on
  the stated block-input linear-system solver interface.
- The maintainer confirmed successful compilation of the revised rc6
  package on 9 October 2026, including both new modules and all 10,055 audits.
- Shortened release documentation, added a formalisation guide and repository
  citation metadata. This documentation cleanup preserves every Lean source,
  audit, dependency pin, build target, checker and source hash from the supplied
  revision.

## 0.1.0-rc5 — 2026-10-02

- Included constant-error `O(sqrt(N))` unitary implementation and the complete
  constant-coefficient ODE success and conditional mixed-output guarantee.
- Included the Hamiltonian `log(1/epsilon)` endpoint corollaries on
  `0 < epsilon <= 1/2`, with 588 strict axiom audits in the default build.

## 0.1.0-rc4 — 2026-10-02

- Added the Hamiltonian `log(1/epsilon)` corollaries, including spectral-norm
  and entangled-reference versions, and updated the theorem map and audits.

## 0.1.0-rc3 — 2026-10-01

- Introduced the current-release source manifest and simplified the packaging
  checker and release instructions.
