import ReleasedODESolverLowerBounds.Mesh.Upgrade.Cost
import ReleasedODESolverLowerBounds.Mesh.Upgrade.Converse

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# From adaptive to measured solvers over the general-mesh physical oracle

Manuscript lines 2363-2364 (proof of Lemma `hsl:lem:precision`: "Randomised or adaptive
algorithms are covered by purification and deferred measurement") and Section `odel:sec:main`,
lines 3669-3681 (the lower bounds apply to Theorems `ode:thm:main` and `ode:thm:time`).

A measured solver over `meshOracle F σ ι N d J₀ J_b` (or over its call forms) is deferred, its
record-selected calls are compiled into controlled calls of the spectator lift
`1_{DRec} ⊗ meshOracle F σ ι` (`1_{DRec × Bool} ⊗ …` for the call forms), and the spectator
lift is absorbed into the physical oracle with the larger spectator index `DRec × ι`
(`Access.meshOracle_absorb`); the inverse value call is a conjugated value call
(`Access.meshOracle_valueConj`) and the source calls are known operations
(`ODELowerBoundExtensions.Release.physicalOracle_inr_const`). The result is an adaptive solver
over the call forms of `meshOracle F σ (DRec × ι)` with the same success and accuracy and at most
the measured solver's worst-case number of value calls (`exists_meshTree_plain`,
`exists_meshTree_call`). Hence:

* `measuredMeshForces_of_meshForces`: **forcing on adaptive solvers implies forcing on measured
  solvers with the same bound**, so every `PhysicalODELowerBound.Mesh.MeshWitnesses` is a
  `MeasuredMeshWitnesses` (`measuredMeshWitnesses_of_meshWitnesses`);
* `meshForces_of_measuredMeshForces`: conversely (adaptive solvers on the finite-dimensional
  physical workspace are measured solvers,
  `DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.ofTreeSolver`), for a
  family with an input;
* `MeasuredMeshCost.exists_meshCost_le`: every realised measured count is at least a realised
  adaptive count (`PhysicalODELowerBound.Mesh.MeshCost`), so the max forms transfer.
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

/-- **Adaptive witnesses over the general-mesh physical oracle are measured witnesses of the same
bound.** -/
theorem measuredMeshWitnesses_of_meshWitnesses {F : Family X N Z K s} {τ gbar ε b : ℝ}
    (h : MeshWitnesses F τ gbar ε b) : MeasuredMeshWitnesses F τ gbar ε b :=
  ⟨h.inClass, h.time_eq, measuredMeshForces_of_meshForces h.forces⟩

end

end ReleasedODESolverLowerBounds.Mesh
