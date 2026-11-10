import ConstantODELowerBound.Runs
import DeferredMeasurementLowerBounds.Corollaries.ODESolver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Runs of the released constant-coefficient solver as measured solvers

Manuscript Theorem `ode:thm:main` and Section `odel:sec:main` ("the lower bounds apply to the upper
bounds of the preceding section").

* `constRun_exists_measuredSolver`: every run of the released constant-coefficient solver
  (`ConstantODELowerBound.Runs.ConstRun`, any split bounds `η_H`, `η_D`) is a measured solver over
  the constant-coefficient physical oracle with the same worst-case value and matrix counts
  (`ConstantODELowerBound.Runs.ConstRun.toTreeSolver` read by
  `DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.ofTreeSolver`), so the measured lower
  bounds of `ReleasedODESolverLowerBounds.Const` constrain the released solver itself.
-/

namespace ReleasedODESolverLowerBounds.Runs

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ConstantODELowerBound.Oracle (constOracle)
open ConstantODELowerBound.Solver (RunIndex runMesh)
open ConstantODELowerBound.Runs (ConstRun)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

/-- **Every run of the released constant-coefficient solver is a measured solver over the
constant-coefficient physical oracle with the same worst-case counts** (on a family with an
input, all of whose inputs are solvable). -/
theorem constRun_exists_measuredSolver {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] [Nonempty X] {s : ℕ} {F : Family X N Z 1 s}
    {τ gbar ε etaH etaD : ℝ} (A : ConstRun F τ gbar ε etaH etaD)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    ∃ M : MeasuredSolver F
        (constOracle F (RunIndex F τ gbar ε) (runMesh F τ gbar ε) A.slots A.degree A.J₀ A.Jb)
        (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) ε,
      M.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) = A.valueQueries ∧
        M.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = A.matrixQueries := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨φ, hφ⟩ := DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos
    (A.toTreeSolver hsol).tree x (by linarith [(A.toTreeSolver hsol).success x])
  refine ⟨MeasuredSolver.ofTreeSolver
    (ConstantODELowerBound.Oracle.constOracle_unitary F _ _ _ _ A.sources_public)
    (A.toTreeSolver hsol) φ hφ, ?_, ?_⟩ <;>
  · rw [MeasuredSolver.ofTreeSolver, DeferredMeasurementLowerBounds.Model.worstCost_ofTree,
      ConstRun.toTreeSolver, ConstantODELowerBound.Protocol.ConstProtocol.worstCost_toTreeSolver]
    rfl

end

end ReleasedODESolverLowerBounds.Runs
