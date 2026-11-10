import GeneralSourceExtensions.Mesh.Integral
import GeneralSourceExtensions.Mesh.Uniform

/-!
# Extensions of the general source interface: paper-to-Lean entry point

The released library `GeneralSourceODE` formalizes Theorem `ode:thm:time` (Section
`ode:sec:time`) with the source access of eqs. `ode:eq:source-interface-mass` and
`ode:eq:source-interface-preparation` (`SparseHamiltonian.GeneralSourceODE.solver`) on the
uniform mesh `t_r = r T / M`, with exactly implemented preparations, for `T > 0` and
`ρ = η_H + R η_D > 0`. This library removes the three restrictions, separately and together: it
covers the degenerate branches `T = 0` and `ρ = 0`, approximately implemented preparations with
operator-norm errors, and nonuniform meshes with breakpoints and integrated certificates.
References to the manuscript use its labels. The notation is that of
`GeneralSourceODE/Statements.lean`: `g' = 2 c_q ḡ`, `Θ = T η_H + T η_D ℓ`,
`ℓ = log (10000 g' / (ε / 2))`, `R = TimeDependentODE.radius (c_q ḡ) ε` and
`ν = TimeDependentODE.precision (c_q ḡ) ε`. Declaration names are relative to
`SparseHamiltonian.GeneralSourceExtensions`.

**Degenerate cases** (`Zero.lean`). If `T = 0` or the public energy bounds give `ρ = 0`, every
branch product of the coherent SELECT is the identity: at `T = 0` every public duration of every
source label vanishes (`durationTable_eq_zero`), and with `ρ = 0` every represented sample
vanishes. The identity program is then an exact SELECT for the released clean encoding at the
rescaling `γ = 1` (as in `ZeroTimeRemarks`), and the released compiler and four-attempt protocol
make no matrix query (`trial_matrix_cost`, `zero_core`).

* `zero_solver`: in the zero cases, `BudgetOutcome … 0`, that is, the released outcome over the
  actual oracles (`GeneralSourceODE.Outcome`) with no matrix query in any history. The mesh
  conditions and the column promises are not needed.
* `solver_nonneg`: under the hypotheses of `GeneralSourceODE.solver` with `0 ≤ T` in place of
  `0 < T` and without `ρ > 0`, `BudgetOutcome` holds with the matrix-query budget
  `Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`.
* `zero_propagated_solver`: the zero cases on the two counted composite interfaces
  (`PropagatedBudgetOutcome … 0`).

**Approximate preparations** (`Approx/`). The supplied `P_w` and `U_load` are arbitrary unitary
families. An instance comes with exact unitary preparations `P` and `L a` that act as `P_w` and
`U_load` act in `GeneralSourceODE.solver` (`GeneralSourceODE.Compiled.WeightPrep` for `P`; `L`
loads `x(0) / ‖x(0)‖` and `b(v_i) / ‖b(v_i)‖` from the seed). They are not supplied to the
algorithm and may depend on the whole instance. The instance hypotheses are

  `‖P_w(x) - P‖ ≤ δ`, `‖U_load(x, a) - L a‖ ≤ δ` for every label `a`,
  `30 g' δ ≤ 1/400`, `30 g' δ ≤ ε / 20`,

together with the other instance hypotheses of `GeneralSourceODE.Outcome`, stated for `P` and
`L`.

* `approx_solver`: under the hypotheses of `GeneralSourceODE.solver`, one public trial family over
  the coherent sampled-time matrix oracle and the supplied `P_w`, `U_load` and `P_w†` satisfies
  `ApproxOutcome`. For every such instance, four fresh trials satisfy `ApproxCertificate`: the
  success probability is at least `2/3`, the conditional output is a density operator within
  trace distance `ε` of `x(T) / ‖x(T)‖`, and every history makes at most
  `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `40 g'` calls of each of `P_w`,
  `U_load` and `P_w†`.
* `approx_solver_nonneg`: the same for every `T ≥ 0` and without `ρ > 0`, with the matrix-query
  budget of `solver_nonneg` (`ApproxBudgetOutcome`).

The family is the released one built for the input type `Inst X n m` of exact preparation
instances, with the sparse data read through the input projection (`pullback`, whose public
tables are those of `D`), and run on the supplied oracles (`recast`, `cost_recast`). Each
embedded supplied call is within `δ` of the exact one (`actualOracle_dev`, from `norm_act_le`,
`norm_loader_sub_le` and `norm_sourcePhysical_sub_le`). Each trial makes at most `10 g'` calls of
each supplied operation, so it moves by at most `30 g' δ` in operator norm
(`eval_recast_sub_le`). The released trial certificate has mean Born success at least `1/4` and
phase-free direction error `ε / 500`; for the moved trials, the four-attempt protocol succeeds
with probability at least `2/3` and has conditional trace distance at most
`6 ε / 500 + 360 g' δ ≤ ε` (`perturbed_four`, from `GateSynth.perturb_four`;
`approx_certificate`).

**Meshes with breakpoints and integrated certificates** (`Mesh/`). The equation is posed on a
mesh `0 = t_0 ≤ ⋯ ≤ t_M = T` (`TimeDependentExtensions.IsMesh`) with one generator piece `G_r`
and one forcing piece `b_r` per interval: `x' = -G_r x + b_r` on `[t_r, t_{r+1}]`, with one-sided
derivatives at the mesh points, so the pieces may jump there. There is one represented sample
`G̃_r = D.matrix (x, r)` per interval. The clock runs on `N` uniform slots of length `T / N`;
slot `k` reads the sample of the interval containing `k T / N` (`TimeDependentExtensions.pieceOf`,
with the coherent SELECT of `TimeDependentExtensions.MeshSelect`), so for `T > 0` interval `r`
has `c_r` slots with `|c_r T / N - Δ_r| < T / N`, `Δ_r = t_{r+1} - t_r`. A source label with
start time `t₀` (`0` for `x(0)`, `v_i` for node `i`) has the public SELECT entry
`T · meshWidth t₀ t r / (t_{r+1} - t_r)` on sample `r` (`Mesh.meshDurations`), the part of
interval `r` after `t₀` rescaled to the slots, so the SELECT circuit is public. The nodes need
not be mesh points. The source vectors are `x(0)` and `ω_i b_i` for node values `b_i` supplied
with the instance (`b(v_i)` in the manuscript), and the source scale is
`B = ‖x(0)‖ + ∑_r ∫_{t_r}^{t_{r+1}} ‖b_r‖` (`Mesh.meshScale`). The Lipschitz constant and the
pointwise sample errors of the released theorem are replaced by an integrated sample-error
certificate and a refinement term,

  `ΔG = ∑_r ∫_{t_r}^{t_{r+1}} ‖G_r(u) - G̃_r‖ du` (`Mesh.sampleError`),
  `ΔR = s Λ ∑_r |c_r T / N - Δ_r|` with `Λ = D.scale` (`Mesh.refinementError`),

the second the rounding of the interval lengths to whole slots (`Mesh.roundingError`): at most
`s Λ M T / N` (`Mesh.refinementError_le`), and zero when the mesh points lie on the slot grid
(`Mesh.roundingError_eq_zero_of_grid`), as on the uniform mesh with `N = q M`
(`Mesh.refinementError_uniform`).

The hypotheses of `Mesh.mesh_solver` are those of `GeneralSourceODE.solver` with the slot count
`N` in the clock conditions (`8 s ρ T ≤ N`, `3 (√(2s) ρ T)³ ≤ ν N²`), together with
`IsMesh t M T` and `0 < N`. For every instance: the pieces are accretive and interval-integrable
and `x(·)` solves them; `U t₀ w` is the homogeneous solution with value `w` at `t₀`
(`Mesh.IsMeshPropagator`); `P_w` and `U_load` prepare the weights and directions of `x(0)` and
`ω_i b_i`; `B_q ≤ c_q B`; `‖x(T) - U(T, 0) x(0) - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B`; `x(T) ≠ 0` and
`B ≤ ḡ ‖x(T)‖`; and `ζ + c_q (ΔG + ΔR) ≤ ε / (2000 ḡ)`.

* `Mesh.mesh_solver`: one public trial family over the actual oracles of the `N`-slot workspace
  (`MeshOracles.actualOracle`) satisfies `Mesh.MeshOutcome`: four fresh trials have the released
  guarantees (`GeneralSourceODE.Oracles.ActualCertificate`). Neither `M`, `N`, `m`, the mesh nor
  the certificates enter the counts.
* `Mesh.mesh_solver_integral`: the same with the manuscript's certificate on the propagated vector
  integral, `‖∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B`, for pieces
  continuous on their closed intervals (`Mesh.MeshIntegralOutcome`). Duhamel's formula on the
  mesh (`Mesh.mesh_duhamel`) identifies the two certificates.
* `Mesh.mesh_solver_nonneg`: every `T ≥ 0`, without `ρ > 0`, with the matrix-query budget of
  `solver_nonneg` (`Mesh.MeshBudgetOutcome`).
* `Mesh.mesh_propagated_solver`: the version on the two counted composite interfaces
  (`Mesh.MeshPropagatedOutcome`, concluding `ODECompleteTrial.Certificate`).

**The combined endpoints.** `Mesh.mesh_approx_solver_nonneg` covers meshes, approximate
preparations and every `T ≥ 0` together, with the matrix-query budget of `solver_nonneg`
(`Mesh.MeshApproxBudgetOutcome`). `Mesh.mesh_approx_solver_nonneg_integral` is the same for
continuous pieces with the certificate on the propagated vector integral
(`Mesh.MeshApproxIntegralOutcome`).

**Non-vacuity** (`Mesh/Corollaries.lean`). `Mesh.exists_isMeshPropagator`: pieces continuous on
their closed intervals have a mesh propagator, from every start time and every initial value.
`Mesh.sampleError_le_of_lipschitz`: `β_r`-Lipschitz pieces with left-endpoint sample errors `δ_r`
have `ΔG ≤ ∑_r (β_r Δ_r² / 2 + δ_r Δ_r)`, `Δ_r = t_{r+1} - t_r`.

**The uniform theorems from the mesh endpoints** (`Mesh/Uniform.lean`). On the uniform mesh
`t_r = r T / M` (`Mesh.isMesh_uniform`) with `N = q M` slots, `q > 0`, a `β_G`-Lipschitz path with
sample errors `δ_G` has `ΔG + ΔR ≤ T (β_G T / M + δ_G)`, the budget term of the released theorem
(`Mesh.uniform_budget_le`), and every instance of the released theorem is an instance of the mesh
endpoints for the constant pieces `G_r = G`, `b_r = b` and the node values `b(v_i)`, with the same
source scale and, by Duhamel's formula, the certificate on the propagated source sum
(`Mesh.uniform_instance`). The released clock conditions on `M` give those on `q M`
(`Mesh.clock_conditions_mul`). Hence `Mesh.mesh_solver_uniform` derives the guarantees of
`GeneralSourceODE.solver` for all its instances from `Mesh.mesh_solver`
(`Mesh.UniformOutcome`), and `Mesh.mesh_approx_solver_nonneg_uniform` derives those of
`approx_solver_nonneg` from the combined endpoint `Mesh.mesh_approx_solver_nonneg`
(`Mesh.UniformApproxBudgetOutcome`), on the actual oracles of the `q M`-slot workspace. At
`q = 1` this workspace is, definitionally, the released one (`Mesh.actualOracle_eq_released`), and
the two outcomes are `GeneralSourceODE.Outcome` and `ApproxBudgetOutcome`
(`Mesh.uniformOutcome_eq`, `Mesh.uniformApproxBudgetOutcome_eq`). So the mesh endpoint gives the
released theorem itself (`Mesh.solver_of_mesh`, the conclusion of `GeneralSourceODE.solver` under
its hypotheses), and the combined endpoint gives the statement of `approx_solver_nonneg` itself
(`Mesh.approx_solver_nonneg_of_mesh`), which with `δ = 0` also covers exact preparations, with
success at least `2/3`.

**Proof map.** Module paths are relative to `GeneralSourceExtensions/`.

* Zero cases: `Zero` (`durationTable_eq_zero`, `trial_matrix_cost`, `zero_core`,
  `budget_of_trial`, `actual_of_trial`) and `Mesh/Zero` (`Mesh.meshDurations_eq_zero`,
  `Mesh.mesh_zero_core`).
* Recast programs and the perturbed protocol: `Approx/Recast` (`recast`, `eval_recast_sub_le`,
  `perturbed_four`, `approx_certificate`). Norms of the embedded supplied operations:
  `Approx/Norms`. Exact preparation instances: `Approx/Pullback` (`pullback`, `Inst`,
  `actualOracle_pullback_matrix`, `actualOracle_dev`). Assembly: `Approx/Theorem`
  (`approx_build`).
* Mesh durations, the product family of a public table, mesh propagators, the node error and the
  refinement into slots: `Mesh/Durations` (`Mesh.meshWidth`, `Mesh.meshDurations`,
  `Mesh.tableFamily`, `Mesh.IsMeshPropagator`, `Mesh.node_error_nat`, `Mesh.refined_sub_le`).
* The `N`-slot native layer and its actual oracles: `Mesh/Native` (`MeshNative.matrix_valid`,
  `MeshNative.trial_certificate`) and `Mesh/Oracles` (`MeshOracles.actualOracle`,
  `MeshOracles.implementation_eval`, `MeshOracles.actualTrials`).
* Branch and target errors and the two-interface solver: `Mesh/Theorem` (`Mesh.branch_error`,
  `Mesh.mesh_target_error`, `Mesh.mesh_propagated_solver`). The actual oracles: `Mesh/Actual`
  (`Mesh.mesh_actual_build`). Approximate preparations on a mesh: `Mesh/Approx`
  (`Mesh.mesh_approx_build`).
* Uniqueness, linearity and the cocycle law of mesh propagators, and Duhamel's formula on the
  mesh: `Mesh/Duhamel` (`Mesh.SolvesFrom.unique`, `Mesh.IsMeshPropagator.cocycle`,
  `Mesh.piece_duhamel`, `Mesh.mesh_duhamel`). The integral certificates: `Mesh/Integral`.
* The uniform mesh: `Mesh/Uniform` (`Mesh.uniform_budget_le`, `Mesh.uniform_instance`,
  `Mesh.actualOracle_eq_released`, `Mesh.solver_of_mesh`, `Mesh.approx_solver_nonneg_of_mesh`).

**Formalization choices.**

* As in `GeneralSourceODE`, every represented sample must have a positive semidefinite
  dissipative part (hypothesis `hPSD`), because the circuit applies the LCHS formula to the
  sampled propagators. This is a restriction of the formal theorems, stated in
  `TimeDependentODE/Statements.lean`; the manuscript's theorem is not changed. The certified
  branch error is first-order (`Mesh.branch_error`), in place of eq. `ode:eq:timedisc`.
* The zero cases are decided from public data (`T` and the public energy bounds), so the trial
  family stays public: it is the identity-SELECT family in the zero cases and the released family
  otherwise.
* The preparation errors are operator-norm errors of the supplied operations, uniform over the
  labels. The matrix oracle, the public phases and the seed are exact. The success constant
  `175/256` of the exact theorem becomes `2/3`.
* On a mesh, `N` is a public parameter of the circuit. It enters the clock conditions and the
  refinement term `ΔR`, which a large `N` makes small without changing the counts, and which
  vanishes when the mesh points lie on the slot grid. The node values `b_i` are supplied because
  `b(v_i)` is not determined by the pieces at a breakpoint; the certificate ties them to the
  solution.
* The mesh endpoints use the `N`-slot workspace of the coherent SELECT on `N` slots; for `N = M`
  it is the released workspace of `GeneralSourceODE`, so that on the uniform mesh with `N = M`
  the released statements follow literally (`Mesh.solver_of_mesh`,
  `Mesh.approx_solver_nonneg_of_mesh`). A larger `N = q M` gives the same guarantees on a longer
  clock (`Mesh.mesh_solver_uniform`, `Mesh.mesh_approx_solver_nonneg_uniform`).
* The mesh propagator is a hypothesis of the instance, as `IsPropagator` is in `GeneralSourceODE`;
  `Mesh.exists_isMeshPropagator` shows that it exists for pieces continuous on their closed
  intervals.
* Not formalised: errors of the matrix oracles (the samples are released sparse data), gate and
  workspace costs.
-/
