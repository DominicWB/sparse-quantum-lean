# Root-sparsity quantum algorithms in Lean

[![Lean CI](https://github.com/DominicWB/sparse-quantum-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/DominicWB/sparse-quantum-lean/actions/workflows/lean.yml)

Formal proofs accompanying [*Root-sparsity scaling for Hamiltonian simulation,
differential equations and linear-system solvers*](https://arxiv.org/abs/2610.02939),
by Dominic W. Berry, Abhishek Rawat, Sophia Simon and Guang Hao Low.

**Toolchain:** Lean 4.32.1 and Mathlib v4.32.1. **Package:** 0.1.0-rc6.

## Build

Install [Elan](https://github.com/leanprover/elan), then run from the directory
containing `lakefile.toml`:

```sh
lake exe cache get
lake build
```

The first command downloads precompiled Mathlib dependencies. The default build
checks all 55 libraries, including all 10,055 strict axiom audits. Keep `.lake`
between builds to reuse compiled modules. Use the supplied dependency manifest;
`lake update` is not needed.

To retain the build output and exit code in PowerShell:

```powershell
lake build 2>&1 | Tee-Object build.log
$buildExit = $LASTEXITCODE
"Lake exit code: $buildExit" | Tee-Object -FilePath build.log -Append
```

The maintainer confirmed successful compilation of this revised rc6 package
on 9 October 2026, including the two latest proof modules and all 10,055
axiom audits. The badge links to the separate GitHub CI results. This
release-documentation update leaves all Lean sources and build settings unchanged.

## Main results

The links below lead to theorem guides or endpoint source files. Paper labels
identify results independently of section numbering.

| Result | Lean entry point |
|---|---|
| Time-independent Hamiltonian queries (`hs:thm:main`) | [ManuscriptPrecision](SparseHamiltonian/ManuscriptPrecision.lean) |
| Time-dependent Hamiltonian queries (`hs:thm:time`) | [TimeDependentHamiltonian](TimeDependentHamiltonian/Statements.lean) |
| Dissipative ODE queries and complete success/output guarantee (`ode:thm:main`) | [ODECompleteSuccess](SparseODE/ODECompleteSuccess.lean) |
| Time-dependent dissipative ODEs (`ode:thm:time`) | [TimeDependentODE](TimeDependentODE/Statements.lean) |
| Hamiltonian gates, workspace and abstract simulation with the manuscript schedule (`hs:thm:gates`, `hs:lem:abstract`) | [GateEfficientSchedule](GateEfficientSchedule/Statements.lean) |
| Hamiltonian and ODE finite-set gates with supplied circuit costs separated (`hs:thm:gates`, `ode:thm:gates`) | [GateEfficientSelective](GateEfficientSelective/Statements.lean) |
| Linear-system queries with the manuscript's repetition schedule (`qls:thm:main`) | [QLSHoeffding](QLSHoeffding/Statements.lean) |
| Hamiltonian and ODE query lower bounds (`hsl:thm:main`, `odel:thm:combined`) | [SparseLowerBounds](SparseLowerBounds/Statements.lean) |
| Linear-system query lower bound (`qlsl:thm:main`) | [LinearSystemLowerBound](LinearSystemLowerBound/Statements.lean) |
| Unitary implementation (`hs:cor:unitary`, precision qualification below) | [Upper bounds](UnitaryImplementationPrecision/Statements.lean), [constant-error lower bound](UnitaryImplementationExtensions/Statements.lean) |
| General constant-coefficient ODEs, conditional (`ode:thm:general`) | [GeneralODE](GeneralODE/Statements.lean) |

See the [formalisation guide](docs/FORMALISATION.md) for further variants,
precise declarations, access models and links to the individual statement guides.

### Scope and assumptions

- The refined hybrid precision bound (`hs:cor:hybrid`) is not formalised.
  General-precision unitary implementation has query bound
  `O(sqrt(N ell) + ell)`, where `ell = log(1/epsilon)`, rather than the
  manuscript's refined additive term. Exact and certified inexact entries
  are covered, as is the constant-error `Theta(sqrt(N))` bound.
- The positive-time general, possibly non-dissipative ODE theorem assumes
  a block-input linear-system solver satisfying `BlockSolver`. Constructing
  that solver remains outside this package.
- Finite-gate-set results use an explicit synthesis hypothesis. Input and
  source preparations are supplied interfaces with counted calls; their
  gate and workspace costs remain explicit. Concrete binary-data libraries
  construct and verify the relevant decoding, reversible arithmetic and
  sparse-oracle routing. Generic interfaces permit other implementations.
- The general Hamiltonian circuit endpoints and abstract simulation lemma
  use the manuscript's explicit schedule. Binary-data and bit-budget
  specialisations, and the ODE SELECT lemma (`ode:lem:gate-select`), retain
  alternative schedules with the same asymptotic bounds. Their theorem
  statements record the exact hypotheses and constants.

## Access model and verification

The native sparse model uses reversible value queries and injective in-place
row/column locators with inverses. List slots embed in the matrix index
register, so `s` is at most the dimension; the decoder is bounded on every
word. Controlled sparse queries are constructed from these primitives.
Time-dependent queries act coherently on a sampled-time register. ODE and
linear-system inputs include the specified controlled source preparations
and inverses; their calls are counted.

The chosen algorithm is uniform over unknown inputs in a stated promise
family. Circuit error includes work registers; the ODE and linear-system
endpoints also prove heralded success, conditional mixed-output accuracy and
worst-case query bounds. Gate costs exclude operations internal to the
supplied matrix oracles and retain the costs of supplied source circuits.

Lean checks the theorem statements under their explicit hypotheses. Strict
`#guard_msgs (whitespace := lax)` assertions check the axiom reports against
fixed expected lists, each a subset of `propext`, `Classical.choice` and
`Quot.sound`. The package excludes `sorry`, new axioms, `native_decide`,
`unsafe` and `implemented_by`.

A separate optional packaging check verifies source hashes, dependency pins,
audit coverage and version consistency:

```sh
python3 scripts/check_release.py
```

Python is not required by `lake build`. The packaging check supplements Lean's
proof checking. [CI](.github/workflows/lean.yml) runs both and retains build logs.

## Citation and licence

The repository is [DominicWB/sparse-quantum-lean](https://github.com/DominicWB/sparse-quantum-lean).
Please cite the associated paper and identify the software version and commit
used. Machine-readable software metadata is in [CITATION.cff](CITATION.cff).
Source code is licensed under [Apache 2.0](LICENSE); dependencies retain their
own licences, and the paper is distributed separately.

See [CHANGELOG.md](CHANGELOG.md) for release changes.
