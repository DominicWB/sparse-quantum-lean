import ReleasedODESolverLowerBounds.Mesh.Upgrade.Plain
import ReleasedODESolverLowerBounds.Mesh.Upgrade.Call

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Measured counts and forcing from adaptive counts over the general-mesh physical oracle

Every realised measured value count over the general-mesh physical oracle is at least a realised
adaptive value count, and forcing on adaptive solvers implies forcing on measured solvers with the
same bound (the matrix count is at least the value count).
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

/-- **Every realised measured value count is at least a realised adaptive value count** on the
general-mesh physical oracle. -/
theorem MeasuredMeshCost.exists_meshCost_le {F : Family X N Z K s} {ε q : ℝ}
    (hq : MeasuredMeshCost F ε q) : ∃ q', MeshCost F ε q' ∧ q' ≤ q := by
  rcases hq with
    ⟨M, σ, ι, _, _, Nsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨M, σ, ι, _, _, Nsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩
  · obtain ⟨T, hT⟩ := exists_meshTree_plain hJ A
    exact ⟨_, Or.inr ⟨M, σ, DRec A.alg × ι, inferInstance, inferInstance, Nsl, d, J₀, Jb, hJ,
      EuclideanSpace ℂ (Fin 1), Joint (DOut A.alg) E, Joint (DOut A.alg) G, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, T, rfl⟩, by exact_mod_cast hT⟩
  · obtain ⟨T, hT⟩ := exists_meshTree_call hJ A
    exact ⟨_, Or.inr ⟨M, σ, (DRec A.alg × Bool) × ι, inferInstance, inferInstance, Nsl, d, J₀,
      Jb, hJ, EuclideanSpace ℂ (Fin 1), Joint (DOut A.alg) E, Joint (DOut A.alg) G,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, T, rfl⟩, by exact_mod_cast hT⟩

/-- **Forcing on adaptive solvers over the general-mesh physical oracle implies forcing on measured
solvers with the same bound** (purification and deferred measurement, proof of Lemma
`hsl:lem:precision`). The value count is transported; the matrix count follows from it, the matrix
count being at least the value count
(`DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono`).
-/
theorem measuredMeshForces_of_meshForces {F : Family X N Z K s} {ε b : ℝ}
    (h : MeshForces F ε b) : MeasuredMeshForces F ε b := by
  refine ⟨?_, ?_⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A
    obtain ⟨T, hT⟩ := exists_meshTree_plain hJ A
    have hb := (h.2 M σ (DRec A.alg × ι) Nsl d J₀ Jb hJ (EuclideanSpace ℂ (Fin 1))
      (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) T).1
    have hv : b ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) :=
      hb.trans (by exact_mod_cast hT)
    have hm := A.alg.worstCost_mono ODELowerBoundExtensions.Release.matrixWeight_value_le
    exact ⟨hv, hv.trans (by exact_mod_cast hm)⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A
    obtain ⟨T, hT⟩ := exists_meshTree_call hJ A
    have hb := (h.2 M σ ((DRec A.alg × Bool) × ι) Nsl d J₀ Jb hJ (EuclideanSpace ℂ (Fin 1))
      (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) T).1
    have hv : b ≤ A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) :=
      hb.trans (by exact_mod_cast hT)
    have hm := A.alg.worstCost_mono
      (fun c => ODELowerBoundExtensions.Release.matrixWeight_value_le c.1)
    exact ⟨hv, hv.trans (by exact_mod_cast hm)⟩

end

end ReleasedODESolverLowerBounds.Mesh
