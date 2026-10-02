# Root-sparsity quantum algorithms in Lean

Formal proofs accompanying **Root-sparsity scaling for Hamiltonian simulation,
differential equations and linear-system solvers**, by Dominic W. Berry,
Abhishek Rawat, Sophia Simon and Guang Hao Low.

**Toolchain:** Lean 4.32.1 and Mathlib v4.32.1. **Package:** 0.1.0-rc5.

## Scope

|Paper result|Lean declaration|Source|
|-|-|-|
|Time-independent Hamiltonian simulation, Theorem 4.1 (`hs:thm:main`)|`SparseHamiltonian.ImprovedSparseHamiltonian.simulation\_log\_one`|[Hamiltonian endpoint](SparseHamiltonian/ManuscriptPrecision.lean)|
|Constant-error unitary implementation (`hs:cor:unitary`)|`SparseHamiltonian.UnitaryImplementation.implementation`|[Unitary endpoint](SparseHamiltonian/UnitaryImplementation.lean)|
|Constant-coefficient dissipative ODE, Theorem 6.1 (`ode:thm:main`)|`SparseHamiltonian.ODECompleteEndpoint.solver`|[Complete ODE endpoint](SparseODE/ODECompleteSuccess.lean)|

The Hamiltonian theorem constructs a primitive-oracle circuit and bounds its
query count and full-output operator-norm error. The unitary theorem gives
error at most `1/4` using `O(sqrt(N))` original entry-oracle calls.
The complete ODE endpoint runs at most four fresh trials, with heralded
success probability at least `175/256 > 2/3`. Its conditional mixed output
has trace distance at most `ε` from the normalised actual solution, with
worst-case bounds on matrix and source-preparation queries.

The [Hamiltonian statement guide](SparseHamiltonian/Statements.lean) and
[ODE statement guide](SparseODE/Statements.lean) give the precise bounds and
quantifiers. Paper labels identify the results across numbering changes.

Not formalised here: the time-dependent Hamiltonian extension (`hs:thm:time`),
the sharper hybrid bound (`hs:cor:hybrid`), time-dependent or general-generator
ODEs, linear-system solvers, lower bounds, gate/workspace or classical
circuit-generation costs. The unfinished gate-efficient Hamiltonian
development is not included.

## Build

Install [Elan](https://github.com/leanprover/elan), then run in this directory:

```sh
lake exe cache get
lake build
```

The toolchain and dependency commits are pinned. Use the supplied manifest;
there is no need to run `lake update`. Keep `.lake` between builds to reuse
compiled modules.

To retain a build log and exit code in PowerShell:

```powershell
lake build 2>\&1 | Tee-Object build.log
$buildExit = $LASTEXITCODE
"Lake exit code: $buildExit" | Tee-Object -FilePath build.log -Append
```

The default `lake build` includes both extensions and **588 checked axiom audits**.
Each requires exactly
`propext`, `Classical.choice` and `Quot.sound`, ignoring message whitespace.
Warnings remain enabled. The audit targets can also be built separately:

```sh
lake build SparseHamiltonian.Audit
lake build SparseODE.Audit
```

The full rc5 package, including the extension proofs, the Hamiltonian log(1/ε)

corollaries and all 588 checked axiom audits, compiled successfully with Lean

4.32.1 and Mathlib v4.32.1 on 2 October 2026 (Lake exit code 0).

## Model and trusted base

[`NativeSparseBlockEncoding.Data`](SparseHamiltonian/NativeSparseBlockEncoding.lean)
specifies exact finite-word sparse data, padded injective row/column locators
and their full unitary extensions. Slots embed in the matrix index register;
the decoder is bounded on every word. Public instance-independent gates are
free. Controlled matrix queries are constructed from the primitive interfaces.
[`MultiOracleCircuit.Program`](SparseHamiltonian/MultiOracleCircuit.lean)
defines circuit semantics; `Program.count` and `Program.cost` count queries.

The ODE model additionally supplies exact source norms and state-preparation
circuits, their inverses, and controls on known initial/forcing branch labels
and the source-sector flag. These calls are counted.
`ODEPrimitiveSourceJoin.TrialCertificate` is the proved output specification,
not an assumed correctness certificate. The program is uniform over unknown
inputs in a public promise family, giving the usual worst-case interpretation.

The logical trusted base is Lean's kernel and the three foundational axioms
listed above. The mathematical assumptions are explicit in the Lean statements.

## Citation and licence

Citation metadata is in [CITATION.cff](CITATION.cff). Source code is licensed
under [Apache 2.0](LICENSE); dependencies retain their own licences. The paper
is distributed separately. Maintainer publication steps are in [RELEASE.md](RELEASE.md).

