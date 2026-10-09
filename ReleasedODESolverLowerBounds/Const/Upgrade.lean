import ReleasedODESolverLowerBounds.Const.Model
import ReleasedODESolverLowerBounds.Mesh.Model
import ReleasedODESolverLowerBounds.Access.ConstForm
import ReleasedODESolverLowerBounds.Transport.Call

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# From adaptive to measured solvers over the constant-coefficient physical oracle

Manuscript line 2364 (purification and deferred measurement) and Section `odel:sec:main`, lines
3669-3681; Theorem `ode:thm:main` (line 2584).

As for the general-mesh oracle (`ReleasedODESolverLowerBounds.Mesh`): a measured solver over
`constOracle F ι N_m T_sl d J₀ J_b` or its call forms is deferred and compiled into an adaptive
solver over the call forms of `constOracle F (DRec × ι)` (respectively `(DRec × Bool) × ι`)
with the same success and accuracy and at most its worst-case number of value calls
(`exists_constTree_plain`, `exists_constTree_call`), through `Access.constOracle_absorb`,
`Access.constOracle_valueConj` and the input independence of the public source labels
(`ConstantODELowerBound.Normal.physicalOracle_inr_const`); value calls are counted by
`Mesh.countWeight_value`.

* `measuredConstForces_of_constForces`, `measuredConstWitnesses_of_constWitnesses`: forcing on
  adaptive solvers implies forcing on measured solvers with the same bound.
* `constForces_of_measuredConstForces`: the converse, for a family with an input.
* `MeasuredConstCost.exists_constCost_le`: every realised measured count is at least a realised
  adaptive count (`PhysicalODELowerBound.Const.ConstCost`).
-/

namespace ReleasedODESolverLowerBounds.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle (constOracle PublicConstSources)
open AdaptiveODELowerBound.Access (callFamily)
open AdaptiveODELowerBound.Model (TreeSolver)
open DeferredMeasurementLowerBounds.Deferral (DRec DOut)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)
open PhysicalODELowerBound.Const (ConstForces ConstWitnesses ConstCost)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The record register of a deferral is absorbed into the branch register** of the
constant-coefficient physical oracle. -/
theorem constAbsorbs (F : Family X N Z 1 s) (ι J : Type) [Fintype ι] [DecidableEq ι] [Fintype J]
    [DecidableEq J] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N) :
    Nonempty (Transport.Absorbs (constOracle F ι Nm Tsl d J₀ Jb)
      (constOracle F (J × ι) Nm Tsl d J₀ Jb) J) := by
  obtain ⟨Vm, hiso, hint⟩ := Access.constOracle_absorb F ι J Nm Tsl d J₀ Jb
  exact ⟨⟨Vm, hiso, hint⟩⟩

variable {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

set_option maxHeartbeats 1600000 in
/-- **A measured solver over the constant-coefficient physical oracle is an adaptive solver over
the call forms of the oracle with branch register `DRec × ι`**, with at most its worst-case
number of value calls. -/
theorem exists_constTree_plain {F : Family X N Z 1 s} {ε : ℝ} {ι : Type} [Fintype ι]
    [DecidableEq ι] {Nm Tsl d : ℕ} {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb)
    (A : MeasuredSolver F (constOracle F ι Nm Tsl d J₀ Jb) E G ε) :
    ∃ T : TreeSolver F (callFamily (constOracle F (DRec A.alg × ι) Nm Tsl d J₀ Jb))
        (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) ε,
      T.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ≤
        A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
  have hB : ∀ l x, IsUnitary (constOracle F ι Nm Tsl d J₀ Jb l x) :=
    ConstantODELowerBound.Oracle.constOracle_unitary F ι Nm Tsl d hJ
  have hB' : ∀ l x, IsUnitary (constOracle F (DRec A.alg × ι) Nm Tsl d J₀ Jb l x) :=
    ConstantODELowerBound.Oracle.constOracle_unitary F (DRec A.alg × ι) Nm Tsl d hJ
  have hsrc : ∀ b x x', constOracle F ι Nm Tsl d J₀ Jb (Sum.inr b) x =
      constOracle F ι Nm Tsl d J₀ Jb (Sum.inr b) x' := fun b x x' =>
    ConstantODELowerBound.Normal.physicalOracle_inr_const
      (ConstantODELowerBound.Oracle.constData F) ι Nm Tsl d hJ b x x'
  have Nc := Classical.choice (Access.constOracle_valueConj F ι Nm Tsl d J₀ Jb)
  have hAb := Classical.choice (constAbsorbs F ι (DRec A.alg) Nm Tsl d J₀ Jb)
  obtain ⟨T, hT⟩ := Transport.exists_treeSolver_plain hB hB' hsrc Nc A hAb
  refine ⟨T, ?_⟩
  simpa only [Mesh.countWeight_value] using hT

set_option maxHeartbeats 10000000 in
/-- **A measured solver over the call forms of the constant-coefficient physical oracle is an
adaptive solver over the call forms of the oracle with branch register `(DRec × Bool) × ι`**,
with at most its worst-case number of value calls in any form. -/
theorem exists_constTree_call {F : Family X N Z 1 s} {ε : ℝ} {ι : Type} [Fintype ι]
    [DecidableEq ι] {Nm Tsl d : ℕ} {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb)
    (A : MeasuredSolver F (callFamily (constOracle F ι Nm Tsl d J₀ Jb)) E G ε) :
    ∃ T : TreeSolver F (callFamily (constOracle F ((DRec A.alg × Bool) × ι) Nm Tsl d J₀ Jb))
        (EuclideanSpace ℂ (Fin 1)) (Joint (DOut A.alg) E) (Joint (DOut A.alg) G) ε,
      T.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ≤
        A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) := by
  have hB : ∀ l x, IsUnitary (constOracle F ι Nm Tsl d J₀ Jb l x) :=
    ConstantODELowerBound.Oracle.constOracle_unitary F ι Nm Tsl d hJ
  have hB' : ∀ l x, IsUnitary (constOracle F ((DRec A.alg × Bool) × ι) Nm Tsl d J₀ Jb l x) :=
    ConstantODELowerBound.Oracle.constOracle_unitary F ((DRec A.alg × Bool) × ι) Nm Tsl d hJ
  have hsrc : ∀ b x x', constOracle F ι Nm Tsl d J₀ Jb (Sum.inr b) x =
      constOracle F ι Nm Tsl d J₀ Jb (Sum.inr b) x' := fun b x x' =>
    ConstantODELowerBound.Normal.physicalOracle_inr_const
      (ConstantODELowerBound.Oracle.constData F) ι Nm Tsl d hJ b x x'
  have Nc := Classical.choice (Access.constOracle_valueConj F ι Nm Tsl d J₀ Jb)
  have hAb := Classical.choice (constAbsorbs F ι (DRec A.alg × Bool) Nm Tsl d J₀ Jb)
  obtain ⟨T, hT⟩ := Transport.exists_treeSolver_call (B := constOracle F ι Nm Tsl d J₀ Jb)
    (B' := constOracle F ((DRec A.alg × Bool) × ι) Nm Tsl d J₀ Jb) (l₀ := Query.value)
    hB hB' hsrc Nc A hAb
  refine ⟨T, ?_⟩
  simpa only [Mesh.countWeight_value] using hT

/-- **Every realised measured value count is at least a realised adaptive value count** on the
constant-coefficient physical oracle. -/
theorem MeasuredConstCost.exists_constCost_le {F : Family X N Z 1 s} {ε q : ℝ}
    (hq : MeasuredConstCost F ε q) : ∃ q', ConstCost F ε q' ∧ q' ≤ q := by
  rcases hq with ⟨ι, _, _, Nm, Tsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨ι, _, _, Nm, Tsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩
  · obtain ⟨T, hT⟩ := exists_constTree_plain hJ A
    exact ⟨_, Or.inr ⟨DRec A.alg × ι, inferInstance, inferInstance, Nm, Tsl, d, J₀, Jb, hJ,
      EuclideanSpace ℂ (Fin 1), Joint (DOut A.alg) E, Joint (DOut A.alg) G, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, T, rfl⟩, by exact_mod_cast hT⟩
  · obtain ⟨T, hT⟩ := exists_constTree_call hJ A
    exact ⟨_, Or.inr ⟨(DRec A.alg × Bool) × ι, inferInstance, inferInstance, Nm, Tsl, d, J₀,
      Jb, hJ, EuclideanSpace ℂ (Fin 1), Joint (DOut A.alg) E, Joint (DOut A.alg) G,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, T, rfl⟩, by exact_mod_cast hT⟩

/-- **Forcing on adaptive solvers over the constant-coefficient physical oracle implies forcing
on measured solvers with the same bound.** -/
theorem measuredConstForces_of_constForces {F : Family X N Z 1 s} {ε b : ℝ}
    (h : ConstForces F ε b) : MeasuredConstForces F ε b := by
  have hw := ODELowerBoundExtensions.Release.matrixWeight_value_le
  refine ⟨?_, ?_⟩
  · intro ι _ _ Nm Tsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A
    obtain ⟨T, hT⟩ := exists_constTree_plain hJ A
    have hv : b ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) :=
      (h.2 _ Nm Tsl d J₀ Jb hJ _ _ _ T).1.trans (by exact_mod_cast hT)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono A.alg hw
  · intro ι _ _ Nm Tsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A
    obtain ⟨T, hT⟩ := exists_constTree_call hJ A
    have hv : b ≤ A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) :=
      (h.2 _ Nm Tsl d J₀ Jb hJ _ _ _ T).1.trans (by exact_mod_cast hT)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono A.alg
      (fun c => hw c.1)

/-- **Measured forcing implies adaptive forcing with the same bound**, for a family with an
input. -/
theorem constForces_of_measuredConstForces [Nonempty X] {F : Family X N Z 1 s} {ε b : ℝ}
    (h : MeasuredConstForces F ε b) : ConstForces F ε b := by
  obtain ⟨x⟩ := ‹Nonempty X›
  constructor
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨φ, hφ⟩ := DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos
      A.tree x (by linarith [A.success x])
    have hA := h.1 ι Nm Tsl d J₀ Jb hJ E G (MeasuredSolver.ofTreeSolver
      (ConstantODELowerBound.Oracle.constOracle_unitary F ι Nm Tsl d hJ) A φ hφ)
    simpa only [MeasuredSolver.ofTreeSolver, DeferredMeasurementLowerBounds.Model.worstCost_ofTree]
      using hA
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨φ, hφ⟩ := DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos
      A.tree x (by linarith [A.success x])
    have hA := h.2 ι Nm Tsl d J₀ Jb hJ E G (MeasuredSolver.ofTreeSolver
      (fun c x => AdaptiveODELowerBound.Access.callFamily_unitary
        (ConstantODELowerBound.Oracle.constOracle_unitary F ι Nm Tsl d hJ) c x) A φ hφ)
    simpa only [MeasuredSolver.ofTreeSolver, DeferredMeasurementLowerBounds.Model.worstCost_ofTree]
      using hA

/-- **Adaptive witnesses over the constant-coefficient physical oracle are measured witnesses of
the same bound.** -/
theorem measuredConstWitnesses_of_constWitnesses {F : Family X N Z 1 s} {τ gbar ε b : ℝ}
    (h : ConstWitnesses F τ gbar ε b) : MeasuredConstWitnesses F τ gbar ε b :=
  ⟨h.inClass, h.time_eq, measuredConstForces_of_constForces h.forces⟩

end

end ReleasedODESolverLowerBounds.Const
