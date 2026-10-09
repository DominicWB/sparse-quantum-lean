import ReleasedODESolverLowerBounds.Mesh.Model

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Adaptive forcing from measured forcing over the general-mesh physical oracle

Adaptive solvers on the finite-dimensional physical workspace are measured solvers
(`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.ofTreeSolver`), so measured forcing
implies adaptive forcing with the same bound for a family with an input.
-/

namespace ReleasedODESolverLowerBounds.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)
open AdaptiveODELowerBound.Access (callFamily)
open AdaptiveODELowerBound.Model (TreeSolver)
open DeferredMeasurementLowerBounds.Deferral (DRec DOut)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)
open PhysicalODELowerBound.Mesh (MeshForces MeshWitnesses MeshCost)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z]
  {K s : ℕ}

/-- **Measured forcing implies adaptive forcing with the same bound**, for a family with an
input: adaptive solvers on the finite-dimensional physical workspace are measured solvers. -/
theorem meshForces_of_measuredMeshForces [Nonempty X] {F : Family X N Z K s} {ε b : ℝ}
    (h : MeasuredMeshForces F ε b) : MeshForces F ε b := by
  obtain ⟨x⟩ := ‹Nonempty X›
  refine ⟨?_, ?_⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hU := TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
    obtain ⟨φ, hφ⟩ := DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos A.tree
      x (by linarith [A.success x])
    have hA := h.1 M σ ι Nsl d J₀ Jb hJ E G
      (MeasuredSolver.ofTreeSolver (O := meshOracle F σ ι Nsl d J₀ Jb) hU A φ hφ)
    simpa only [MeasuredSolver.ofTreeSolver, DeferredMeasurementLowerBounds.Model.worstCost_ofTree]
      using hA
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hU := TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
    obtain ⟨φ, hφ⟩ := DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos A.tree
      x (by linarith [A.success x])
    have hA := h.2 M σ ι Nsl d J₀ Jb hJ E G
      (MeasuredSolver.ofTreeSolver (O := callFamily (meshOracle F σ ι Nsl d J₀ Jb))
        (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary hU c x) A φ hφ)
    simpa only [MeasuredSolver.ofTreeSolver, DeferredMeasurementLowerBounds.Model.worstCost_ofTree]
      using hA

end

end ReleasedODESolverLowerBounds.Mesh
