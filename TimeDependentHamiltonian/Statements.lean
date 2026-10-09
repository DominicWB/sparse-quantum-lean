import TimeDependentHamiltonian.Corollaries

/-!
# Time-dependent Hamiltonian simulation: paper-to-Lean entry point

Theorem `hs:thm:time` (time-dependent Hamiltonian simulation) of the
accompanying paper is formalized for uniform meshes by
`SparseHamiltonian.TimeDependent.simulation` in
`TimeDependentHamiltonian/Theorem.lean`.

**Access model.** The represented samples are released native sparse data
`D : NativeSparseBlockEncoding.Data (X × Fin M) n Z s`, indexed by the unknown
instance `x : X` and the sampled time `r < M`; `D.matrix (x, r)` is `H̃_r`.
A query applies one coherent sampled-time primitive `∑_r |r⟩⟨r| ⊗ O_r`
(equation `hs:eq:timeaccess`), where `O_r` is the released row-locator,
column-locator or value oracle of sample `r`, with its full unitary extension
(`timeOracle`, `Sampled.oracle`, `oracle`). One call counts once even when `r`
is in superposition, and inverse calls are counted. The location lists, their
order and padding may vary with `r`. The oracles act on a fixed workspace
determined by `n`, `Z`, `M` and the filter degree, and `input D hM γ η t ε`
is the fixed clean encoding of the system `EuclideanSpace ℂ n` in it. Both
depend only on public data, not on the instance.

**Hypotheses** of `simulation`:

* `0 < η`, `0 ≤ t`, `0 ≤ β`, `0 < ε ≤ 1/2` and `0 < M`;
* every sample is Hermitian with row and column Euclidean norms at most `η`;
  the sparsity bound `s` is part of the data;
* the path `Hpath x u` is Hermitian for `u ∈ [0, t]` and obeys the
  operator-norm Lipschitz bound `‖H(u) - H(v)‖ ≤ β |u - v|` there; no
  sparsity or norm promise is needed for the path;
* the sample errors on the uniform mesh obey `‖H(r t / M) - H̃_r‖ ≤ δ` and
  `t δ ≤ ε / 12`;
* the mesh conditions `4 s η t ≤ M`, `9 β t² ≤ ε M` and
  `9 (√s η t)³ ≤ ε M²`.

**Guarantees.** For some `γ` with `0 < γ ≤ 1` and `γ √s ≥ 1`, the rescaling
of equation `hs:eq:timeparams`, there is one program `p` over
`oracle D γ η t ε`, uniform over the unknown instances, such that

* `p` makes at most `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))` queries,
  `τ = η t`, including inverse calls (the constant of the released
  `hs:thm:main` endpoint); neither `M` nor `β` enters the count;
* the clean encoding `ι = input D hM γ η t ε` satisfies `ι† ι = 1`;
* for every instance `x`, `p.eval x` is unitary and
  `‖p.eval x ∘ ι - ι ∘ U(t)‖ ≤ ε` for every propagator `U` of the path, that
  is, every solution of `U' = -i H(u) U` on `[0, t]` with `U(0) = 1`
  (`SolvesOn`). This is equation `hs:eq:timeerror` for the complete output,
  including every work register.

`TimeDependentHamiltonian/Corollaries.lean` adds `simulation_propagator`
(the propagator exists, by the Picard–Lindelöf theorem, so the guarantee is
not vacuous), `simulation_with_reference` (inputs entangled with an untouched
finite reference), `meshSize` and `meshSize_spec` (an explicit admissible
mesh; every larger `M` is also admissible), `input_isometry` and
`zero_certificate` (for zero time or a zero path, the identity program over
the same oracles makes no queries and is exact).

**Proof map.** Module paths are relative to `TimeDependentHamiltonian/`.

* Coherent sampled-time oracles and lifted programs, equation
  `hs:eq:timeaccess`: `Native/TimeIndexed` (`timeIndexed`, `timeOracle`,
  `liftProgram_eval`, `sampledProgram`); the phase-fixed reference at one
  sampled time: `timeOracle_valid`, `sampledOracle_valid`.
* Exact sparse Cayley unitaries and clock promises for every sample, with a
  common boundary isometry and common `Q` and `ν` (equation
  `hs:eq:interface`): the released `FixedNativeCayleySimulation` at each
  `(x, r)` (`Sampled.actions`, `Sampled.sampled_core`).
* The chronological transducer with slot-dependent private operations and
  its catalyst, equations `hs:eq:timecayley` and `hs:eq:timecatalyst`:
  `Chronology/Colligation` (`privateV`, `exitV`, `colligation_energy`,
  `colligation_public`, `colligation_private`, `stackedV_norm_sq_le`,
  `exitV_identity`).
* The global resolvent for different local unitaries, equations
  `hs:eq:timelocal` to `hs:eq:timeresolvent`: `Chronology/Varying`
  (`orderedProduct_norm_le`, `resolvent_two_sided_inverse`,
  `exists_resolvent`) and `Chronology/Colligation`
  (`exists_privateV_resolvent`, `filter_precisionV`), from the released local
  certificates `GlobalResolvent.exists_local_clock_certificate`.
* Filter, finite reuse, LCU and amplification with target `U_C`:
  `Chronology/Simulation` (`exists_precise_implementationV`, `layerV_factor`,
  `implementationV_query_certificate`), with the released generic smoothing
  and amplification modules.
* Controlled sampled access through the complete query register, with `54`
  queries per active layer independent of `M`: `Native/Encoding`
  (`cleanInputV`, `clean_implementsOnV`, `Sampled.implementsOn`).
* Native simulation of the ordered product of sampled exponentials, with the
  Cayley error `M (√s τ / M)³`: `Native/Simulation`
  (`Sampled.exists_sampled_simulation`).
* Discretisation against the path, equation `hs:eq:timedisc`:
  `Continuous/Propagator` (`duhamel_step`, `propagator_telescope`,
  `mesh_error`); existence of the propagator: `Continuous/Existence`.
* Rescaling by `η`, the choice of `γ` (equation `hs:eq:gammaopt` with
  `τ = η t`) and the error budget: `Theorem` (`sampledEvolution_normalize`,
  `step_le_quarter`, `count_le_shape`, `simulation`).

**Formalization choices.**

* The mesh is uniform, `t_r = r t / M`. The boundary rotations are then
  common to all slots and only the private Cayley unitaries vary. The mesh
  is part of the oracle family, so the mesh conditions are hypotheses.
* `4 s η t ≤ M` gives the clock condition `w ≤ 1/4` for every admissible
  `γ`, since `α = η √s / γ ≤ η s`; the paper's condition `4 α T ≤ M` depends
  on `γ`. The other two conditions differ from equation `hs:eq:timegrid`
  (`6 β T² ≤ ε M` and `(Λ T)³ ≤ ε M²`, `Λ = √s η`) only in their constants:
  the per-interval estimates used here are `β Δ²` (Duhamel in mean-value
  form) and the released Cayley bound, which has no factor `1/12`.
* Error budget: `2ε/3` for the amplified filter with tolerance `ε/3`, `ε/9`
  for the Cayley steps, `ε/9` for freezing and `ε/12` for sample values, in
  total `35ε/36`. Gates are exact in the query model, so no part of `ε` is
  reserved for gate approximation.
* The propagator is any solution of the Schrödinger equation on `[0, t]`,
  with one-sided derivatives at the endpoints; the time-ordered exponential
  is not constructed separately.
* Not formalised: nonuniform meshes, piecewise Lipschitz paths with
  breakpoints, integrated sample-error certificates, coherent selection of
  public parameters, the time-indexed block-encoding special case (equations
  `hs:eq:blockspecial` and `hs:eq:blockadditive`), the hybrid bound
  `hs:cor:hybrid`, gate and workspace costs, and lower bounds.
-/
