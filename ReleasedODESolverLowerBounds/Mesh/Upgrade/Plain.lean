import ReleasedODESolverLowerBounds.Mesh.Upgrade.Absorb

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Deferred measured solvers over the general-mesh physical oracle

A measured solver over the general-mesh physical oracle is an adaptive solver over the call forms
of the physical oracle with spectator index `DRec × ι`, with at most its worst-case number of
value calls (`ReleasedODESolverLowerBounds.Transport.exists_treeSolver_plain`).
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

variable {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 10000000 in
/-- **A measured solver over the general-mesh physical oracle is an adaptive solver over the
call forms of the physical oracle with spectator index `DRec × ι`**, with at most its worst-case
number of value calls. -/
theorem exists_meshTree_plain {F : Family X N Z K s} {ε : ℝ} {M : ℕ} {σ : Fin M → Fin K}
    {ι : Type} [Fintype ι] [DecidableEq ι] {Nsl d : ℕ} {J₀ : X → SysOp N}
    {Jb : X → Fin M → SysOp N} (hJ : PublicSources J₀ Jb)
    (A : MeasuredSolver F (meshOracle F σ ι Nsl d J₀ Jb) E G ε) :
    ∃ T : TreeSolver F (callFamily (meshOracle F σ (DRec A.alg × ι) Nsl d J₀ Jb))
        (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) ε,
      T.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ≤
        A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
  have hB : ∀ l x, IsUnitary (meshOracle F σ ι Nsl d J₀ Jb l x) :=
    TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
  have hB' : ∀ l x, IsUnitary (meshOracle F σ (DRec A.alg × ι) Nsl d J₀ Jb l x) :=
    TimeDependentExtensions.MeshSource.physicalOracle_unitary (ι := DRec A.alg × ι)
      (ODELowerBoundExtensions.Release.stageData F.data σ) Nsl d J₀ Jb hJ.initial_unitary
      hJ.forcing_unitary
  have hsrc : ∀ b x x', meshOracle F σ ι Nsl d J₀ Jb (Sum.inr b) x =
      meshOracle F σ ι Nsl d J₀ Jb (Sum.inr b) x' :=
    ODELowerBoundExtensions.Release.physicalOracle_inr_const
      (ODELowerBoundExtensions.Release.stageData F.data σ) ι Nsl d hJ
  have Nc := Classical.choice (Access.meshOracle_valueConj F σ ι Nsl d J₀ Jb)
  have hAb : Transport.Absorbs (meshOracle F σ ι Nsl d J₀ Jb)
      (meshOracle F σ (DRec A.alg × ι) Nsl d J₀ Jb) (DRec A.alg) :=
    Classical.choice (meshAbsorbs F σ ι (DRec A.alg) Nsl d J₀ Jb)
  obtain ⟨T, hT⟩ := Transport.exists_treeSolver_plain (B := meshOracle F σ ι Nsl d J₀ Jb)
    (B' := meshOracle F σ (DRec A.alg × ι) Nsl d J₀ Jb) hB hB' hsrc Nc A hAb
  rw [countWeight_value] at hT
  exact ⟨T, hT⟩

end

end ReleasedODESolverLowerBounds.Mesh
