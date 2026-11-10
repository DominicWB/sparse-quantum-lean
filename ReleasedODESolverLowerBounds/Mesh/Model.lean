import PhysicalODELowerBound.Mesh.Model
import DeferredMeasurementLowerBounds.Corollaries.ODESolver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Measured solvers over the general-mesh physical oracle

Manuscript Section `odel:sec:main` (access with inverses and controls, success flag of probability
at least `2/3` on every input, conditional trace distance `ε`, worst-case query bound; "the lower
bounds apply to the upper bounds of the preceding section") and the end of the proof of Lemma
`hsl:lem:precision` ("Purification and deferred measurement include adaptive and randomised
algorithms").

The measured solvers (`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver`: mid-run and
multi-outcome measurements, classical control, randomness and resets of finite-dimensional
registers) here call the physical oracle of the released general-mesh solver
(`ODELowerBoundExtensions.Release.meshOracle F σ ι N d J₀ J_b`, any placement, spectator index,
slot count, degree and public source interfaces), in the two access shapes of
`PhysicalODELowerBound.Mesh.MeshForces`: the oracle itself (with inverse calls) and its call
forms `AdaptiveODELowerBound.Access.callFamily` (plain, inverse, controlled and
controlled-inverse calls). The value count is `ODESourceQueryBudget.matrixWeight valueWeight`,
the matrix count `matrixWeight (fun _ => 1)`, inverse calls counted, in the worst case over all
transcripts (`DeferredMeasurementLowerBounds.Model.Measured.worstCost`).

* `MeasuredMeshForces F ε b`: every such measured solver, in both access shapes, makes at least
  `b` value calls and at least `b` matrix calls. It has the shape of
  `PhysicalODELowerBound.Mesh.MeshForces` with measured solvers in place of adaptive ones.
* `MeasuredMeshWitnesses F τ ḡ ε b`: `F` is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and
  measured-forces `b`.
* `MeasuredMeshCost F ε q`: `q` is the worst-case value count of some measured solver over the
  physical oracle or its call forms; `MeasuredMeshForces.le_cost`.
* `countWeight_value`: the counted weight of the value label is the value count (used for the
  general-mesh and the constant-coefficient physical oracles alike).
-/

namespace ReleasedODESolverLowerBounds.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)
open AdaptiveODELowerBound.Access (callFamily)
open DeferredMeasurementLowerBounds.Model (countWeight)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- The counted weight of the value label is the value count `matrixWeight valueWeight`. -/
theorem countWeight_value :
    countWeight (· = (Sum.inl Query.value : Query ⊕ Bool)) =
      ODESourceQueryBudget.matrixWeight valueWeight := by
  funext l
  rcases l with q | b
  · cases q <;> simp [countWeight, ODESourceQueryBudget.matrixWeight, valueWeight]
  · simp [countWeight, ODESourceQueryBudget.matrixWeight]

/-- **`F` forces `b` on measured solvers over the general-mesh physical oracle at accuracy `ε`**:
every measured solver over `meshOracle F σ ι N d J₀ J_b` (any placement `σ`, spectator index `ι`,
slot count `N`, degree `d`, public source interfaces, output and garbage spaces), and every
measured solver over its call forms, makes at least `b` value calls and at least `b` matrix
calls in the worst case over all transcripts. -/
def MeasuredMeshForces (F : Family X N Z K s) (ε b : ℝ) : Prop :=
  (∀ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N), PublicSources J₀ Jb →
    ∀ (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : MeasuredSolver F (meshOracle F σ ι Nsl d J₀ Jb) E G ε),
      b ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
        b ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
  (∀ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N), PublicSources J₀ Jb →
    ∀ (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : MeasuredSolver F (callFamily (meshOracle F σ ι Nsl d J₀ Jb)) E G ε),
      b ≤ A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ∧
        b ≤ A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight (fun _ => 1) c.1))

/-- **`F` witnesses `b` on measured solvers over the general-mesh physical oracle** for the
parameters `(τ, ḡ, ε)`: `F` is in the class with `η = 1`, `T = τ` and `g ≤ ḡ`, and
measured-forces `b` at accuracy `ε`. -/
structure MeasuredMeshWitnesses (F : Family X N Z K s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : MeasuredMeshForces F ε b

/-- **A realised worst-case value count of a measured solver over the general-mesh physical
oracle**: `q` is the worst-case value count of some measured solver of `F` at accuracy `ε` over
the physical oracle (any placement, spectator index, slot count, degree and public source
interfaces) or over its call forms. -/
def MeasuredMeshCost (F : Family X N Z K s) (ε q : ℝ) : Prop :=
  (∃ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) (_ : PublicSources J₀ Jb) (E G : Type)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G) (A : MeasuredSolver F (meshOracle F σ ι Nsl d J₀ Jb) E G ε),
      q = A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) ∨
  (∃ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) (_ : PublicSources J₀ Jb) (E G : Type)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G)
      (A : MeasuredSolver F (callFamily (meshOracle F σ ι Nsl d J₀ Jb)) E G ε),
      q = A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1))

/-- The worst-case value count of a measured solver over the physical oracle is a realised
measured count. -/
theorem MeasuredMeshCost.of_measured {F : Family X N Z K s} {ε : ℝ} {M : ℕ} (σ : Fin M → Fin K)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N}
    {Jb : X → Fin M → SysOp N} (hJ : PublicSources J₀ Jb) {E G : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : MeasuredSolver F (meshOracle F σ ι Nsl d J₀ Jb) E G ε) :
    MeasuredMeshCost F ε (A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) := by
  exact Or.inl ⟨M, σ, ι, inferInstance, inferInstance, Nsl, d, J₀, Jb, hJ, E, G, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, A, rfl⟩

/-- Measured forcing is a lower bound on every realised measured value count. -/
theorem MeasuredMeshForces.le_cost {F : Family X N Z K s} {ε b : ℝ} (h : MeasuredMeshForces F ε b)
    {q : ℝ} (hq : MeasuredMeshCost F ε q) : b ≤ q := by
  rcases hq with
    ⟨M, σ, ι, _, _, Nsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨M, σ, ι, _, _, Nsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩
  · exact (h.1 M σ ι Nsl d J₀ Jb hJ E G A).1
  · exact (h.2 M σ ι Nsl d J₀ Jb hJ E G A).1

/-- A measured witness of `b` witnesses every smaller bound. -/
theorem MeasuredMeshWitnesses.mono {F : Family X N Z K s} {τ gbar ε b b' : ℝ}
    (hW : MeasuredMeshWitnesses F τ gbar ε b) (hb : b' ≤ b) :
    MeasuredMeshWitnesses F τ gbar ε b' := by
  refine ⟨hW.inClass, hW.time_eq, ⟨?_, ?_⟩⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.1 M σ ι Nsl d J₀ Jb hJ E G A
    exact ⟨hb.trans h1, hb.trans h2⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.2 M σ ι Nsl d J₀ Jb hJ E G A
    exact ⟨hb.trans h1, hb.trans h2⟩

end

end ReleasedODESolverLowerBounds.Mesh
