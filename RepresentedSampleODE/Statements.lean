import RepresentedSampleODE.Repair
import RepresentedSampleODE.Family
import RepresentedSampleODE.Target
import RepresentedSampleODE.Theorem
import RepresentedSampleODE.Zero
import RepresentedSampleODE.Actual
import RepresentedSampleODE.Approx
import RepresentedSampleODE.Integral
import RepresentedSampleODE.Duhamel
import RepresentedSampleODE.Regular
import RepresentedSampleODE.Gate.Certificate
import RepresentedSampleODE.Gate.Native
import RepresentedSampleODE.Gate.Binary

/-!
# Represented samples of any sign: statement guide

The time-dependent dissipative ODE solvers of `GeneralSourceExtensions.Mesh` (Theorem
`ode:thm:time` with the general source interface on a mesh) and the time-dependent gate solver
(`GateODE.Time`, from binary data `GateRemarks.ODE.binary_ode_time_budget_bits_nonneg`) require
every *represented* sample `G̃_r = D.matrix (x, r)` to have a positive semidefinite dissipative
part. The manuscript (proof of `ode:thm:time`) applies the LCHS formula to the true dissipative path
and asks of the represented branches only the moment and norm promises and certified approximation
errors. This library proves the solvers without the positivity of the represented samples; only the
true path is dissipative.

## The method

* **Positive repair** (`Repair`). For a self-adjoint `A` with `Re ⟨w, A w⟩ ≥ -κ ‖w‖²`, the
  operator `repair A κ = (‖A‖/(‖A‖ + κ)) (A + κ)` is positive semidefinite, `‖repair A κ‖ ≤ ‖A‖`,
  and `‖repair A κ - A‖ ≤ 2 min(κ, ‖A‖)`. It serves the analysis only; the circuits keep the
  represented samples.
* **The repaired family** (`Family`). The Gaussian LCHS product family of a source label with the
  repaired dissipative parts is entire, contractive on the closed lower half-plane and has the
  public Lipschitz constant of the represented family, so the released public Gaussian table
  applies to it (`TimeDependentODE.GaussianLCHS.table_certificate`). At the public nodes
  `|k| ≤ R` the represented SELECT branches differ from the repaired branches by at most
  `2 R (Λ_κ + ΔR)` (`tableFamily_sub_robustFamily`), `Λ_κ = ∑_r (t_{r+1} - t_r) κ_r`
  (`negativity`).
* **The repaired target** (`Target`). The repaired generators `repair D̃_r κ_r + i H̃_r` are
  accretive and within `2 κ_r` of the samples; the repaired target is within
  `(ΔG + 2 Λ_κ + 2 ΔR) B_q` of the propagated source sum (`robust_target_error`).
* **The solver** (`Theorem`). The public SELECT program and Gaussian table are those of the
  released solver; the per-label targets of the actual-source certificate are the branch sums
  corrected by the repaired-family table error, and the quadrature step absorbs the branch
  difference: `robust_propagated_solver`, under `RobustBudget`:
  `ζ + c_q (ΔG + 2 Λ_κ + 2 ΔR) ≤ ε / (2000 ḡ)` and `6 R (Λ_κ + ΔR) ≤ ν`
  (`R = radius (c_q ḡ) ε`, `ν = precision (c_q ḡ) ε`). For positive samples one may take `κ = 0`;
  the budgets are then those of the released solver with the rounding term doubled and the branch
  budget `6 R ΔR ≤ ν` (both void on the uniform mesh with `N = qM`, where `ΔR = 0`).

## Endpoints

* `robust_zero_core` (`Zero`): the identity SELECT when `T = 0` or `η_H + R η_D = 0`
  (`mesh_zero_time_core`: at `T = 0` without positivity; `mesh_zero_generator_core`: the released
  zero core; both for `ZeroTrialOutcome`, without the classical solution, which no core proof
  uses);
* `robust_mesh_solver`, `robust_mesh_solver_nonneg` (`Actual`): over the actual oracles `P_w`,
  `U_load`, `P_w†`, with the released query bounds;
* `robust_approx_solver_nonneg` (`Approx`): with approximately implemented preparations, every
  `T ≥ 0`;
* `robust_solver_integral`, `robust_approx_solver_nonneg_integral` (`Integral`): with the
  certificate on the propagated vector integral for continuous pieces;
* `robust_approx_solver_nonneg_path` (`Integral`): the same with negativity bounds from the true
  path, `κ_r` the average of `‖Herm(G_r(u) - G̃_r)‖` over interval `r` (`pathNegativity`), whose
  negativity mass is the dissipative sample error `ΔD = ∑_r ∫ ‖Herm(G_r - G̃_r)‖ ≤ ΔG`
  (`dissipativeError`): budgets `ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε / (2000 ḡ)` and
  `6 R (ΔD + ΔR) ≤ ν`. The branch budget bounds the dissipative part `R ΔD` of the integrated
  branch sample error `∑_r ∫ ‖K̃_{k,r} - K_k(u)‖ du ≤ ΔH + R ΔD`, `|k| ≤ R` (`ΔH` the integrated
  sample error of the Hamiltonian parts; the integrated form of the manuscript's represented-sample
  contribution after eq. `ode:eq:timedisc`).
* `robust_approx_solver_nonneg_regular` (`Regular`): the same for integrable generator pieces
  (`RegularPieces`) and mild solutions (`MildSolution`: an integrable propagated forcing
  `v ↦ U(T, v) b_r(v)` on every mesh interval and Duhamel's formula
  `x(T) = U(T, 0) x(0) + ∑_r ∫ U(T, v) b_r(v) dv`), without continuity or a classical solution, with
  the propagator classical on every closed piece (`Mesh.IsMeshPropagator`); classical solutions of
  bounded pieces with an integrable propagated forcing are mild (`MildSolution.of_solves`, by
  Duhamel's formula
  `mesh_duhamel_bounded`, `Duhamel`: the Duhamel function `v ↦ U(T, v) x(v)` is continuous with
  right derivative `U(T, v) b(v)`), in particular for continuous pieces
  (`MildSolution.of_continuous`, `RegularPieces.of_continuous`).

## The gate-level solver (`Gate`)

On the uniform mesh of the gate solver the path is accretive and within `δ_G` of the samples at
the slot times, so `Re ⟨w, L_r w⟩ ≥ -δ_G ‖w‖²` without further hypotheses
(`GateTime.negativity_of_sample`), and the analysis runs on the repairs `repair L_r δ_G`:

* `GateTime.RobustInstanceOK` (`Gate/Certificate`): the released instance conditions
  `GateODE.Time.TParams.InstanceOK` without `psd`, with the discretisation budget at the sample
  error `3 δ_G` and the branch budget `6 R T δ_G ≤ ν` (it bounds the dissipative part `R T δ_G` of
  the represented-sample contribution `∑_r h_r ‖K̃_{k,r} - K_k(t_r)‖` to the manuscript's branch
  error budget after eq. `ode:eq:timedisc`);
  `GateTime.robust_prep_certificate`: the released actual-source certificate for the repaired
  target;
* `GateTime.robust_native_time_outcome` (`Gate/Native`): the guarantees of the released native
  protocol for one instance;
* `GateTime.robust_binary_time_outcome_nonneg` (`Gate/Binary`): the guarantees of the released
  protocol `btprepC q loadC wpC` from time-indexed binary data, every `T ≥ 0`, under
  `GateTime.RobustRest` (the released `PubT.Rest` with the two budgets: `RobustRest.of_rest`,
  `RobustRest.toRest`) and the energy bounds of the samples.

The public trial families, the query bounds and the source-call counts are those of the released
endpoints; only the instance conditions change.
-/
