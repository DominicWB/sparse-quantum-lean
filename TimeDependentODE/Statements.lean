import TimeDependentODE.Corollaries

/-!
# Time-dependent dissipative ODE: paper-to-Lean entry point

Theorem `ode:thm:time` (time-dependent generators and forcing) of the
accompanying paper is formalized for uniform meshes by
`SparseHamiltonian.TimeDependentODE.solver` in `TimeDependentODE/Theorem.lean`,
with the uniform statement `SparseHamiltonian.TimeDependentODE.Outcome`.
The constant-coefficient endpoint `ode:thm:main` is the released
`SparseHamiltonian.ODECompleteEndpoint.solver` (library `SparseODE`); its
statement file predates this extension.

**Equation and access model.** The equation is `x' = -G(u) x + b(u)` on
`[0, T]`; the generator `G(u)` is accretive (`Accretive`: `Re ⟪v, G v⟫ ≥ 0`),
that is, `A = -G` is dissipative. The represented samples are released native
sparse data `D : NativeSparseBlockEncoding.Data (X × Fin M) n Z s`, indexed by
the unknown instance `x : X` and the sample `r < M` of the uniform mesh
`t_r = r T / M`; `D.matrix (x, r)` is `G̃_r`. A matrix query applies one
coherent sampled-time primitive `∑_r |r⟩⟨r| ⊗ O_r`, where `O_r` is the
released row-locator, column-locator or value oracle of sample `r` with its
full unitary extension (`labelOracle`, `oracle`, `NativeSource.matrixOracle`);
one call counts once with `r` in superposition, and inverse calls are
counted. The source interfaces are the supplied unitaries `J₀ x` (initial
state, controlled on the initial source label) and `Jb x r` (forcing sample
`r`, applied coherently on every forcing label `some r` as one call). The
complete primitive oracle family is `NativeSource.physicalOracle D d J₀ Jb`
(matrix labels `Sum.inl`, source labels `Sum.inr`).

**Hypotheses** of `solver`, all public:

* `0 ≤ η_H`, `0 ≤ η_D`, `0 < T`, `1 ≤ g`, `0 < ε ≤ 1` and `0 < M`;
* every sample has Hermitian imaginary and real parts with row and column
  Euclidean norms at most `η_H` and `η_D`, and a positive semidefinite real
  part; the sparsity bound `s` is part of the data;
* with `g' = 2 g`, `ε' = ε / 2`, `R = radius g ε = 4 log (20000 g' / ε')` and
  `ν = precision g ε = ε' / (10000 g')`: `ρ = η_H + R η_D > 0` and the mesh
  conditions `8 s ρ T ≤ M` and `3 (√(2s) ρ T)³ ≤ ν M²`;
* public source norms `r₀ ≥ 0` and `rb r ≥ 0` with positive source mass
  `B = r₀ + (T / M) ∑ rb r` (`PublicSource.mass`), unitary source interfaces
  and a unit seed.

For every instance `x`, after the circuit has been selected, the guarantee
holds under the following instance hypotheses: the generator path `G` is
accretive and `β_G`-Lipschitz in operator norm on `[0, T]`, with sample
errors `‖G(t_r) - G̃_r‖ ≤ δ_G`; the forcing path `b` is bounded by `b_max`
and `β_b`-Lipschitz, with forcing samples `b̃_r`, `‖b(t_r) - b̃_r‖ ≤ δ_b`;
`x(·)` is any solution on `[0, T]` (`SolvesODE`); `‖x(0)‖ = r₀`,
`‖b̃_r‖ = rb r`, and the source interfaces prepare the directions of `x(0)`
and of every nonzero `b̃_r` from the seed; `x(T) ≠ 0` and `B ≤ g ‖x(T)‖`;
and the certified discretisation error
`T ((β_G T/M + δ_G)(r₀ + b_max T) + β_b T/M + δ_b + (T/M) s D.scale (b_max + δ_b))`
(`Sampling.discretisation`) is at most `ε B / (2000 g)`.

**Guarantees.** There are a filter degree `d`, a clean source encoding `E`
and one trial family `q` over the primitive oracle family, all depending only
on public data, such that every `q j` is unitary and, for every valid
instance, the released complete certificate `ODECompleteTrial.Certificate`
holds for the target `x(T)` with the public seed and output flag:

* four bounded attempts succeed with probability at least `2/3` (also
  `175/256`);
* conditioned on success, the output density operator is positive with trace
  one and spectral trace distance at most `ε` from `x(T) / ‖x(T)‖`;
* every history makes at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix
  queries, `Θ = T η_H + T η_D ℓ`, `ℓ = log (10000 g' / ε')`, and at most
  `40 g'` calls to each source interface (`80 g'` in total), including
  inverse calls. Neither `M` nor the regularity constants enter the counts.

`TimeDependentODE/Corollaries.lean` adds `meshSize` and `mesh_conditions`
(an explicit admissible mesh; every larger `M` is admissible) and
`discretisation_eq` (sample-error term plus a term decaying as `1 / M`).
Solutions exist for Lipschitz paths: `exists_solvesODE_of_lipschitz`.

**Proof map.** Module paths are relative to `TimeDependentODE/`.

* Gaussian LCHS for every entire family that is contractive on the closed
  lower half-plane, by contour integration around the pole `-i`:
  `LCHS/GaussianIntegrands`, `LCHS/GaussianResidue`, `LCHS/GaussianContour`,
  `LCHS/GaussianFull` (`GaussianLCHS.full_line_error`,
  `GaussianLCHS.truncated_error`).
* Ordered products of the complex-frequency slot evolutions and one public
  Gaussian table for all of them (Low–Somma's formula with time ordering):
  `LCHS/Products` (`productFamily_norm_le_one`, `productFamily_neg_I`,
  `productFamily_lipschitz`), `LCHS/Table` (`table_certificate`).
* The coherent sampled-time native layer of the tagged Cayley construction,
  `72` queries per active layer independent of `M`: `Native/Layer`
  (`labelOracle`, `cayleyProgram_intertwines`, `valid`, `implementsOn`).
* The chronological clock of `hs:thm:time` with the tagged moment interface
  at every sample (`ODEJointCayley`), and the Cayley error `M (√(2s) ρ T / M)³`:
  `Native/Simulation` (`Select.select_core`), `Native/Select`
  (`Select.exists_native_select`, `Select.select`).
* Label-dependent forcing interface, source-loaded SELECT, counted
  amplification and primitive compilation: `Source/Controls`,
  `Source/Compiled`, `Source/Counted`, `Source/Primitive`, `Source/Public`,
  with native coordinates and validity derived from sparse access:
  `Native/Source` (`NativeSource.matrix_valid`,
  `NativeSource.coefficient_trial_certificate`).
* Continuous problem: energy bound and existence (`Continuous/Solution`,
  `Continuous/Existence`), the exponential left-endpoint scheme and its
  certified mesh error, and the masked-propagator form of the recurrence
  (`Continuous/Discretisation`: `mesh_error`, `recurrence_eq_sum`).
* Public source coefficients, sampled generators and branch identification,
  discretised target and its relative budget: `Solver/Coefficients`,
  `Solver/Families` (`Sampling.family_neg_I`,
  `Sampling.branchEvolution_eq_family`), `Solver/Target`
  (`Sampling.discretisation_error`, `Sampling.target_budget`).
* Assembly with the released actual-source certificate, query conversion and
  complete endpoint: `Theorem` (`retarget`, `solver`).

**Formalization choices.**

* The mesh is uniform and the source quadrature is the left-endpoint rule:
  the source register loads `x(0)` and `(T/M) b̃_q`, and the forcing term
  `q` is propagated from slot `q` on. The source mass `B` is the
  corresponding quadrature of `‖x(0)‖ + ∫ ‖b‖`.
* The scheme is `y_{r+1} = exp(-(T/M) G̃_r)(y_r + (T/M) b̃_r)`; its certified
  error uses operator-norm Lipschitz bounds of the paths and the public bound
  `‖G̃_r‖ ≤ s D.scale`. The discretised target, not `x(T)`, is the LCHS and
  source-certificate target; half of the ratio budget and half of the
  direction error are reserved for the transfer to `x(T)` (`g' = 2 g`,
  `ε' = ε / 2`).
* `8 s ρ T ≤ M` gives the clock condition `w ≤ 1/4` for every admissible
  rescaling; `3 (√(2s) ρ T)³ ≤ ν M²` bounds the accumulated Cayley error by
  `ν / 3`.
* Not formalised: nonuniform meshes, breakpoints of piecewise Lipschitz
  inputs, integrated sample-error certificates, the zero-time and zero-energy
  degenerate branches of `ode:thm:main`, the general-generator extension
  `ode:thm:general`, gate and workspace costs, and lower bounds.
-/
