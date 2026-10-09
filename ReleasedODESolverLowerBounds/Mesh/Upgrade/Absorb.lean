import ReleasedODESolverLowerBounds.Mesh.Model
import ReleasedODESolverLowerBounds.Access.MeshForm
import ReleasedODESolverLowerBounds.Transport.Call

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Record absorption for the general-mesh physical oracle

The record register of a deferral is absorbed into the spectator index of the general-mesh
physical oracle (`ReleasedODESolverLowerBounds.Access.meshOracle_absorb`), in the form
`ReleasedODESolverLowerBounds.Transport.Absorbs` used by the compilation of measured solvers.
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

/-- **The record register of a deferral is absorbed into the spectator index** of the
general-mesh physical oracle. -/
theorem meshAbsorbs (F : Family X N Z K s) {M : ℕ} (σ : Fin M → Fin K) (ι J : Type) [Fintype ι]
    [DecidableEq ι] [Fintype J] [DecidableEq J] (Nsl d : ℕ) (J₀ : X → SysOp N)
    (Jb : X → Fin M → SysOp N) :
    Nonempty (Transport.Absorbs (meshOracle F σ ι Nsl d J₀ Jb)
      (meshOracle F σ (J × ι) Nsl d J₀ Jb) J) := by
  obtain ⟨Vm, hiso, hint⟩ := Access.meshOracle_absorb F σ ι J Nsl d J₀ Jb
  exact ⟨⟨Vm, hiso, hint⟩⟩

end

end ReleasedODESolverLowerBounds.Mesh
