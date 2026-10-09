import IntegrablePathSimulation.Hamiltonian.Corollaries
import IntegrablePathSimulation.Coherent.Corollaries
import IntegrablePathSimulation.BlockEncoding.Theorem
import IntegrablePathSimulation.Propagator.Released

set_option autoImplicit false

/-!
# Time-dependent simulation of integrable Hermitian paths: paper-to-Lean entry point

Theorem `hs:thm:time` of the manuscript (lines 1414-1445) compares the circuit with the
time-ordered exponential `U_H(T, 0)` (eq. `hs:eq:timeerror`, lines 1431-1435). The paragraph
"Regularity and coherent parameters" after its proof (lines 1618-1632) states, at lines
1622-1626: "More generally, for an integrable Hermitian path it suffices to have a certified
bound on the sum of the integrated sample errors `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - H̃_r‖ du`. All
uses of regularity are confined to this classical error certificate." The library
`TimeDependentExtensions` proves the integrated certificate for classical piecewise
propagators. This library defines propagators of merely integrable paths (in the sense of
Carathéodory), proves their existence, uniqueness and unitarity and the unitary Duhamel
estimate, and proves the released time-dependent Hamiltonian theorems for such paths, with the
released theorems as corollaries. All declarations below are in the namespace
`IntegrablePathSimulation`.

* Propagators (`Propagator.SolvesIntegralOn`, `Propagator.IsPropagator`): existence and
  uniqueness `Propagator.existsUnique_isPropagator`, the Dyson series
  `Propagator.picardSeries` (`isPropagator_picardSeries`), unitarity
  `Propagator.IsPropagator.isUnitary`.
* The integrated sample-error certificate (eq. `hs:eq:timedisc`, line 1595, and lines
  1622-1626): `Propagator.IsPropagator.mesh_error_integral`,
  `Propagator.IsPropagator.refined_error`, `Propagator.SolvesIntegralOn.duhamel`,
  `Propagator.SolvesIntegralOn.window_error`.
* Theorem `hs:thm:time` for integrable paths: `Hamiltonian.simulation`; against the Dyson
  series `Hamiltonian.simulation_dyson`; with an untouched reference (lines 1442-1443)
  `Hamiltonian.simulation_with_reference`.
* Coherent start times and durations (lines 1627-1632): `Coherent.coherent_windows`.
* Time-indexed block encodings (eq. `hs:eq:blockadditive`, lines 1640-1660):
  `BlockEncoding.simulation`.
* Containment of the released statements: `Propagator.isPropagator_glue`,
  `Propagator.isPropagator_of_solvesOn`, and the released theorems with unchanged statements,
  `Hamiltonian.simulation_piecewise` (`TimeDependentExtensions.Hamiltonian.simulation`),
  `Hamiltonian.simulation_classical` (`TimeDependentExtensions.Hamiltonian.simulation_path`),
  `Coherent.coherent_windows_piecewise`, `BlockEncoding.simulation_piecewise`,
  `Propagator.duhamel_integral_of_solvesOn`, `Propagator.mesh_error_integral_piecewise` and
  `Propagator.refined_error_piecewise`.

**Propagators.** `Propagator.SolvesIntegralOn H U a b`: `u ↦ H u * U u` is interval integrable
on `[a, b]` and `U s = U a + ∫_a^s (-i) H(u) U(u) du` for `s ∈ [a, b]` (a Bochner integral in
`P →L[ℂ] P`, `P` any complex Hilbert space). `Propagator.IsPropagator H U T`: `U 0 = 1` and
`SolvesIntegralOn H U 0 T`. The integrand is the derivative of the released classical
`SolvesOn`.

**Hypotheses** (those of the released theorems that are lifted). `Hamiltonian.simulation`:
`0 < M`, `0 < η`, `0 < T`, `0 < ε ≤ 1/2`, `0 < N`, `IsMesh t M T`, `4 s η T ≤ N`,
`9 (√s η T)³ ≤ ε N²`, `9 M √s η T ≤ ε N`, and Hermitian samples `D.matrix (x, r)` with row and
column norms at most `η`. `Coherent.coherent_windows`: `0 < ε ≤ 1`, `8 s η T ≤ N`,
`9 (√(2s) η T)³ ≤ ε N²`, `3 M √s η T ≤ ε N`. `BlockEncoding.simulation`: `0 < ε ≤ 1`,
`0 < α`, Hermitian unitaries `O_r`, an isometric `J`, `4 α T ≤ N`, `9 (α T)³ ≤ ε N²`,
`9 M α T ≤ ε N`.

**Guarantees** (`τ = η T`).

* `Propagator.existsUnique_isPropagator`: for `0 ≤ T` and `H` interval integrable on `[0, T]`,
  a propagator exists and any two agree on `[0, T]`.
* `Propagator.IsPropagator.isUnitary`: if `H` is self-adjoint at almost every time of `[0, T]`
  and interval integrable, `U s` is unitary for every `s ∈ [0, T]`.
* `Propagator.IsPropagator.refined_error`: `‖U T - refinedEvolution‖ ≤
  ∑_r ∫_{t_r}^{t_{r+1}} ‖H u - H̃_r‖ du + M (T/N) Λ`.
* `Hamiltonian.simulation`: there are `γ ∈ (0, 1]` with `1 ≤ γ √s` and one program `p` over
  `TimeDependentExtensions.Hamiltonian.oracle D N γ η T ε` with at most
  `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))` queries such that, with the isometric encoding
  `ι = TimeDependentExtensions.Hamiltonian.input D hM t N γ η T ε`, for every `x`, `p.eval x` is
  unitary and `‖p.eval x ι - ι U T‖ ≤ ε` for every path `H` on `[0, T]` that is Hermitian at
  almost every time and interval integrable, with
  `∑_r ∫_{t_r}^{t_{r+1}} ‖H(u) - D.matrix (x, r)‖ du ≤ ε/9`, and every propagator `U` of `H`.
* `Coherent.coherent_windows`: coherent windows `[t_{a_i}, t_{b_i}]` of one integrable path with
  certificate at most `ε/3` and count `663552 · shape (2s) (η T) (log (6/ε))`; the branch
  evolutions are integral-sense solutions from the identity at `t_{a_i}`.
* `BlockEncoding.simulation`: certificate at most `ε/9` against `H̃_r = α J† O_r J` and count
  `2304 (α T + 1 + log(3/ε))` controlled time-indexed calls, inverses included.

**Proof map.** Module paths are relative to `IntegrablePathSimulation/`.

* `Calculus/Absolute`, `Calculus/Product`: absolute continuity and the product rule for
  integral equations (`mul_eq_add_integral`, `integral_mul_primitive_pow`).
* `Calculus/Gronwall`: Grönwall's inequality in integral form with an integrable coefficient
  (`le_mul_exp_of_le_add_integral`, `eq_zero_of_norm_le_integral`).
* `Propagator/Basic`, `Propagator/Existence`, `Propagator/Uniqueness`, `Propagator/Unitary`:
  the definitions; Picard terms bounded by `(∫‖H‖)ⁿ/n!` (`norm_picardTerm_le`); uniqueness by
  Grönwall; `U* U` conserved by the product rule and `U U* = 1` by Grönwall.
* `Propagator/Duhamel`: the unitary Duhamel estimate and the integrated certificate.
* `Propagator/Classical`, `Propagator/Released`: classical and piecewise propagators are
  propagators of the glued path (`pieceIndex`, `glue`, `glue_ae_eq`, `solvesIntegralOn_glue`),
  and the released mesh estimates as corollaries (`sum_integral_glue`, `ae_star_glue`).
* `Hamiltonian/Theorem`, `Coherent/Theorem`, `BlockEncoding/Theorem`: the released proofs with
  the classical estimates replaced by the integral-sense ones; `Hamiltonian/Corollaries`,
  `Coherent/Corollaries`: the released statements and the Dyson-series and reference forms.

Every theorem of the library is axiom-audited in `IntegrablePathSimulation/Audit.lean`.

**Formalisation choices.**

* `U_H(T, 0)` of an integrable path is read as the solution of the integral equation
  (Carathéodory sense). Integrability of `u ↦ H u * U u` is part of the definition: without it
  a non-integrable `H` would admit the solution `U ≡ 1`. Continuity and absolute continuity of
  `U` are derived. `Hamiltonian.simulation_dyson` states the theorem against the Dyson series
  `Propagator.picardSeries` with no propagator supplied.
* The Hermitian hypothesis holds at almost every time of `[0, T]`, weaker than the pointwise
  form of the released theorems, which is recovered with `ae_of_all`. Interval integrability of
  `H` on `[0, T]` is a separate hypothesis. No sparsity or norm promise is placed on `H(u)`,
  only on the samples, as in the package. Integrability is Bochner interval integrability in the
  operator norm (for matrices, equivalent to entrywise Lebesgue integrability); the Hermitian
  condition holds almost everywhere, so the path may be changed on a null set
  (`SolvesIntegralOn.congr_ae`).
* The hypotheses, budgets and constants are those of the released theorems that are lifted
  (`T > 0`, `η > 0`, the slot conditions with refinement, certificate `ε/9` or `ε/3`), not the
  manuscript's `ε/12` budget on a uniform mesh.
* One path `H` on `[0, T]` replaces the pieces. A piecewise path enters by gluing:
  `pieceIndex t M u` is the last `r ≤ M - 1` with `t r ≤ u`, and the glued path equals each
  piece on `[t_r, t_{r+1})`, hence almost everywhere, so the certificates agree.
* Containment needs interval-integrable pieces, which the released theorems already assume, so
  the corollaries keep the released statements unchanged (the duplication is intentional).
  Without integrability containment fails: `U = exp(-iφ)` with `φ(u) = u² sin(1/u²)` satisfies
  `SolvesOn`, but `φ'` is not integrable near `0`; this is documented, not proved.
* Unitarity holds in any complex Hilbert space and is stated with the released
  `OracleCircuit.IsUnitary`; the simulation theorems are stated on `EuclideanSpace ℂ n`.
* Uniqueness is existence plus agreement on `Icc 0 T`; uniqueness among all functions
  `ℝ → (P →L[ℂ] P)` would fail, since values outside `[0, T]` are unconstrained.
* Coherent windows use one path on `[0, T]`; each branch evolution solves the integral equation
  on its window from the identity at `t_{a_i}`, and the contraction bound used by the Duhamel
  estimate comes from the conservation law `SolvesIntegralOn.star_mul_self` (`V* V = 1`); window
  solutions exist, e.g. `V(s) = U(s) U(t_{a_i})*` for a propagator `U` (not stated as a lemma).
  The released `TimeDependentExtensions.Coherent.window_error`, stated for an arbitrary monotone
  `t`, is generalised by `SolvesIntegralOn.window_error` and recovered at the level of
  `coherent_windows_piecewise`.
* Only `U_H(·, 0)` is formalised, from the identity at `0`; the Duhamel estimate is stated on
  arbitrary subintervals and mesh windows.

**Not formalised.**

* Carathéodory solutions of ODEs with integrable generators. The manuscript uses the
  integrated certificate for general generators only inside the proof of Lemma
  `odel:lem:dyson`; the ODE solvers of the package keep classical piecewise solutions.
* The two-parameter propagator `U_H(t, s)` and its group law.
* Coherent selection of public parameters other than durations and start times at mesh points
  (lines 1627-1628).
* The lower bound of Theorem `hsl:thm:main` for this class (lines 1635-1638).
* Gate and workspace costs of the additional time slots (lines 1634-1635).
* Zero time or a known zero Hamiltonian (line 1444); nonuniform Cayley steps without
  refinement.
* The uniform-mesh theorem `SparseHamiltonian.TimeDependent.simulation`, the gate-level
  time-dependent theorems and the ODE solvers keep their classical (Lipschitz or piecewise
  classical) hypotheses; only the general-mesh query theorems for Hamiltonians are lifted.

**Provenance.** No result from another paper is used. The libraries `TimeDependentExtensions`,
`TimeDependentHamiltonian` and `SparseHamiltonian` are only imported; no released module is
changed. `TimeDependentExtensions/Statements.lean` predates this library: its sentence that
Carathéodory propagators and solutions of general integrable paths are not formalised is
superseded here for Hamiltonian paths, and still applies to ODE solutions. Line numbers in this
guide refer to the manuscript used by this library; the module docstrings of the imported
libraries cite another manuscript version, and the paper labels are the stable references.
-/
