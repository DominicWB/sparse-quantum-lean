# Root-sparsity quantum algorithms in Lean

Formal proofs accompanying **Root-sparsity scaling for Hamiltonian simulation,
differential equations and linear-system solvers**, by Dominic W. Berry,
Abhishek S. Rawat, Sophia Simon and Guang Hao Low.

**Software authors:** Dominic W. Berry and Abhishek S. Rawat.  
**Toolchain:** Lean 4.32.1 and Mathlib v4.32.1. **Package:** 0.1.0-rc30.

## Build

Install [Elan](https://github.com/leanprover/elan), then run from the directory
containing `lakefile.toml`:

```sh
lake exe cache get
lake build
```

The default build includes all 79 libraries and their axiom audits. The
supplied `lean-toolchain` and `lake-manifest.json` pin the toolchain and
dependencies. Keep the manifest unchanged; `lake update` is not required.
Keep `.lake` between builds to reuse compiled modules.

## Theorem coverage

The project formalises results on:

- Hamiltonian simulation, including time-dependent, optimal-precision and
  two-norm query bounds, unitary implementation, and gate-efficient variants.
- Dissipative differential equations, including source preparation, heralded
  output guarantees, time-dependent and general-source variants, and gate
  bounds under explicit arithmetic and synthesis assumptions.
- Quantum linear-system solving and general constant-coefficient differential
  equations, the latter using an external block-input linear-system solver;
  separate matrix and preparation query bounds (Corollary `qls:cor:separate`)
  conditional on a stated interface for the external solver of Gao, Ji and
  Liu, which is not formalised here.
- Query lower bounds, including adaptive algorithms and intermediate
  measurements on the stated hard families.

**[Detailed formalisation coverage](docs/FORMALISATION.md)** explains the
correspondence with the manuscript, exact theorem names, oracle models,
resource accounting, additional hypotheses and remaining restrictions. It
is the extended companion to the manuscript's short Lean appendix.

The [manuscript correspondence table](ManuscriptConformance/Statements.lean)
and each library's `Statements.lean` give the source-level statement guides.
Coverage is subject to those explicit hypotheses; some formal schedules,
constants and input formats differ from the manuscript.

## Verification

The package contains 1,866 Lean source files and **14695 checked axiom audits**.
The audit modules use strict `#guard_msgs` to check that the reported axioms
are `propext`, `Classical.choice` and `Quot.sound`, or specified subsets.
Warnings remain enabled.

The proofs and axiom audits, including the separate-query corollary and its
writer form, have a recorded successful complete build. See the
[validation details](docs/FORMALISATION.md#validation-and-audits) for the
scope of that evidence.

[GitHub Actions](.github/workflows/lean.yml) builds the proofs and runs the
supplementary packaging check:

```sh
python3 scripts/check_release.py
```

That check validates source hashes, dependency pins, audit inventories and
version consistency. It does not compile proofs. Python is not required for
`lake build`.

## Citation and licence

Use [CITATION.cff](CITATION.cff) or the supplied
[BibTeX entry](CITATION.bib), and identify the release or commit used.
The repository is <https://github.com/DominicWB/sparse-quantum-lean>.

Source code is licensed under [Apache 2.0](LICENSE). Dependencies retain
their own licences; the paper is distributed separately.
